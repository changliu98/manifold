use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::x86::types::{Address, Node, Symbol};
use ascent::ascent_par;
use ascent::lattice::set::Set;

// A may-reaching frame write at one CFG point.  The interval belongs inside
// the lattice value, never in its key.  `Write` retains both the physical write
// interval and the query cell whose reaching state it represents; otherwise a
// one-byte update would erase a preceding wide initializer for every disjoint
// subcell query in the same object.  The recursive relation still has exactly
// one row per (function, CFG point), with the per-query facts joined in its Set.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FrameWriteOrigin {
    Unwritten(i64, usize),
    Unknown(Address, i64, usize),
    Write(Address, i64, usize, i64, usize),
}

pub(crate) fn frame_intervals_overlap(
    write_ofs: i64,
    write_width: usize,
    cell_ofs: i64,
    pointer_width: i64,
) -> Option<bool> {
    let write_width = i64::try_from(write_width).ok()?;
    if write_width <= 0 || pointer_width <= 0 {
        return None;
    }
    let write_end = write_ofs.checked_add(write_width)?;
    let cell_end = cell_ofs.checked_add(pointer_width)?;
    Some(write_ofs < cell_end && cell_ofs < write_end)
}

/// Whether one exact byte interval fully contains another.  These are frame
/// coordinates, not program points: the comparisons describe physical bytes
/// inside one recovered stack frame and never stand in for CFG reachability.
pub(crate) fn frame_interval_contains(
    outer_ofs: i64,
    outer_width: usize,
    inner_ofs: i64,
    inner_width: usize,
) -> bool {
    let (Ok(outer_width), Ok(inner_width)) =
        (i64::try_from(outer_width), i64::try_from(inner_width))
    else {
        return false;
    };
    if outer_width <= 0 || inner_width <= 0 {
        return false;
    }
    let (Some(outer_end), Some(inner_end)) = (
        outer_ofs.checked_add(outer_width),
        inner_ofs.checked_add(inner_width),
    ) else {
        return false;
    };
    outer_ofs <= inner_ofs && inner_end <= outer_end
}

fn exact_stack_byte_interval(offset: i64, width: usize) -> bool {
    let Ok(width) = i64::try_from(width) else {
        return false;
    };
    width > 0 && offset.checked_add(width).is_some()
}

fn is_x86_stack_pointer_name(name: &str) -> bool {
    matches!(name, "RSP" | "ESP" | "SP" | "SPL")
}

fn is_x86_frame_pointer_name(name: &str) -> bool {
    matches!(name, "RBP" | "EBP" | "BP" | "BPL")
}

fn x86_gpr_view_width(reg: &str) -> Option<i64> {
    match reg {
        "RAX" | "RBX" | "RCX" | "RDX" | "RSI" | "RDI" | "RBP" | "RSP" | "R8" | "R9" | "R10"
        | "R11" | "R12" | "R13" | "R14" | "R15" => Some(8),
        "EAX" | "EBX" | "ECX" | "EDX" | "ESI" | "EDI" | "EBP" | "ESP" | "R8D" | "R9D" | "R10D"
        | "R11D" | "R12D" | "R13D" | "R14D" | "R15D" => Some(4),
        "AX" | "BX" | "CX" | "DX" | "SI" | "DI" | "BP" | "SP" | "R8W" | "R9W" | "R10W" | "R11W"
        | "R12W" | "R13W" | "R14W" | "R15W" => Some(2),
        "AL" | "BL" | "CL" | "DL" | "AH" | "BH" | "CH" | "DH" | "SIL" | "DIL" | "BPL" | "SPL"
        | "R8B" | "R9B" | "R10B" | "R11B" | "R12B" | "R13B" | "R14B" | "R15B" => Some(1),
        _ => None,
    }
}

/// Whether this state member belongs to one exact tracked query cell.  Query
/// identity is byte-layout metadata, not a reachability approximation; the
/// member reached the current point only through the CFG lattice above.
pub(crate) fn frame_origin_tracks(
    origin: &FrameWriteOrigin,
    cell_ofs: i64,
    cell_width: usize,
) -> bool {
    let (tracked_ofs, tracked_width) = match origin {
        FrameWriteOrigin::Unwritten(ofs, width)
        | FrameWriteOrigin::Unknown(_, ofs, width)
        | FrameWriteOrigin::Write(_, _, _, ofs, width) => (*ofs, *width),
    };
    tracked_ofs == cell_ofs && tracked_width == cell_width
}

fn frame_origin_cell_overlaps(
    origin: &FrameWriteOrigin,
    write_ofs: i64,
    write_width: usize,
) -> bool {
    let (cell_ofs, cell_width) = match origin {
        FrameWriteOrigin::Unwritten(ofs, width)
        | FrameWriteOrigin::Unknown(_, ofs, width)
        | FrameWriteOrigin::Write(_, _, _, ofs, width) => (*ofs, *width),
    };
    let Ok(write_width) = i64::try_from(write_width) else {
        return true;
    };
    frame_intervals_overlap(cell_ofs, cell_width, write_ofs, write_width).unwrap_or(true)
}

ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct FrameWritePassProgram;

    relation abi_pointer_size(i64);
    relation call_targets_noreturn(Node);
    relation code_in_block(Address, Address);
    relation decoded_memory_write_unknown(Address, &'static str);
    relation decoded_stack_read_bytes(Address, Symbol, i64, usize);
    relation decoded_stack_write_bytes(Address, Symbol, i64, usize);
    relation decoded_stack_write_unresolved(Address, Symbol);
    relation ddisasm_cfg_edge(Address, Address, Symbol);
    relation function_has_ltl_body(Address);
    relation function_has_uncovered_block(Address);
    relation function_unknown_terminal(Address, Node);
    relation function_unresolved_control(Address, Node);
    relation instr_in_function(Node, Address);
    relation next(Address, Address);
    relation op_indirect(Symbol, &'static str, &'static str, &'static str, i64, i64, usize);
    relation op_register(Symbol, &'static str);
    relation plea(Address, Symbol, Symbol);
    relation pmov(Address, Symbol, Symbol);
    relation settled_block_dom_set(Address, Address, Set<Address>);
    relation settled_sp_frame_shift(Address, Address, i64);

    // Normalize decoder-proven operand roles only from the final SP state
    // published by FrameCoordinatePass. A known zero is evidence; absence or
    // an ambiguous final Set publishes no shift and becomes an explicit veto.
    relation frame_stack_write_bytes(Address, Address, i64, usize);
    relation frame_stack_read_bytes(Address, Address, i64, usize);
    relation unnormalized_frame_stack_write(Address, Address);

    frame_stack_write_bytes(*func, *addr, ofs, *width) <--
        decoded_stack_write_bytes(addr, base, raw_ofs, width),
        if is_x86_stack_pointer_name(base),
        abi_pointer_size(pointer_width),
        if x86_gpr_view_width(base) == Some(*pointer_width),
        instr_in_function(addr, func),
        settled_sp_frame_shift(func, addr, depth),
        if *width > 0,
        !decoded_memory_write_unknown(addr, _),
        if let Some(ofs) = raw_ofs.checked_sub(*depth),
        if exact_stack_byte_interval(ofs, *width);

    frame_stack_read_bytes(*func, *addr, ofs, *width) <--
        decoded_stack_read_bytes(addr, base, raw_ofs, width),
        if is_x86_stack_pointer_name(base),
        abi_pointer_size(pointer_width),
        if x86_gpr_view_width(base) == Some(*pointer_width),
        instr_in_function(addr, func),
        settled_sp_frame_shift(func, addr, depth),
        if *width > 0,
        if let Some(ofs) = raw_ofs.checked_sub(*depth),
        if exact_stack_byte_interval(ofs, *width);

    unnormalized_frame_stack_write(*func, *addr) <--
        decoded_stack_write_bytes(addr, base, _, _),
        if is_x86_stack_pointer_name(base),
        abi_pointer_size(pointer_width),
        if x86_gpr_view_width(base) == Some(*pointer_width),
        instr_in_function(addr, func),
        !settled_sp_frame_shift(func, addr, _);
    unnormalized_frame_stack_write(*func, *addr) <--
        decoded_stack_write_bytes(addr, base, _, width),
        if is_x86_stack_pointer_name(base),
        abi_pointer_size(pointer_width),
        if x86_gpr_view_width(base) == Some(*pointer_width),
        instr_in_function(addr, func),
        if *width == 0;
    unnormalized_frame_stack_write(*func, *addr) <--
        decoded_stack_write_bytes(addr, base, _, _),
        if is_x86_stack_pointer_name(base),
        abi_pointer_size(pointer_width),
        if x86_gpr_view_width(base) != Some(*pointer_width),
        instr_in_function(addr, func);
    // BP is not a function-wide frame identity: it can be observed before the
    // setup, on a non-dominated arm, or after a clobber, and its displacement
    // lives in a different coordinate from post-allocation SP. Until a settled
    // point-keyed BP coordinate is available, every BP write is opaque and BP
    // reads/LEAs are deliberately ineligible for MUST Slot provenance.
    unnormalized_frame_stack_write(*func, *addr) <--
        decoded_stack_write_bytes(addr, base, _, _),
        if is_x86_frame_pointer_name(base),
        instr_in_function(addr, func);
    unnormalized_frame_stack_write(*func, *addr) <--
        decoded_stack_write_bytes(addr, base, _, _),
        if is_x86_stack_pointer_name(base),
        abi_pointer_size(pointer_width),
        if x86_gpr_view_width(base) == Some(*pointer_width),
        instr_in_function(addr, func),
        decoded_memory_write_unknown(addr, _);
    unnormalized_frame_stack_write(*func, *addr) <--
        decoded_stack_write_bytes(addr, base, raw_ofs, _),
        if is_x86_stack_pointer_name(base),
        abi_pointer_size(pointer_width),
        if x86_gpr_view_width(base) == Some(*pointer_width),
        instr_in_function(addr, func),
        settled_sp_frame_shift(func, addr, depth),
        if raw_ofs.checked_sub(*depth).is_none();
    unnormalized_frame_stack_write(*func, *addr) <--
        decoded_stack_write_bytes(addr, base, raw_ofs, width),
        if is_x86_stack_pointer_name(base),
        abi_pointer_size(pointer_width),
        if x86_gpr_view_width(base) == Some(*pointer_width),
        instr_in_function(addr, func),
        settled_sp_frame_shift(func, addr, depth),
        if let Some(ofs) = raw_ofs.checked_sub(*depth),
        if !exact_stack_byte_interval(ofs, *width);
    unnormalized_frame_stack_write(*func, *addr) <--
        decoded_stack_write_unresolved(addr, base),
        if is_x86_stack_pointer_name(base),
        instr_in_function(addr, func);
    unnormalized_frame_stack_write(*func, *addr) <--
        decoded_stack_write_unresolved(addr, base),
        if is_x86_frame_pointer_name(base),
        instr_in_function(addr, func);

    #[local] relation exact_frame_stack_lea_member(Address, Address, i64);
    exact_frame_stack_lea_member(*func, *addr, ofs) <--
        plea(addr, _, memory),
        op_indirect(memory, _, base, index, _, raw_ofs, _),
        if is_x86_stack_pointer_name(base),
        if *index == "NONE" || index.is_empty(),
        abi_pointer_size(pointer_width),
        if x86_gpr_view_width(base) == Some(*pointer_width),
        instr_in_function(addr, func),
        settled_sp_frame_shift(func, addr, depth),
        if let Some(ofs) = raw_ofs.checked_sub(*depth);

    // Compilers commonly materialize the current frame base with a plain
    // full-width `mov %sp, %gpr`.  AsmPass intentionally raises that machine
    // move to the same Ainstack(0) address expression as an LEA; publish the
    // matching exact frame coordinate here so RTL can retain its stack-object
    // identity.  Partial-register moves are not pointer materializations.
    exact_frame_stack_lea_member(*func, *addr, ofs) <--
        pmov(addr, dst, src),
        op_register(dst, dst_name),
        op_register(src, src_name),
        if is_x86_stack_pointer_name(src_name),
        abi_pointer_size(pointer_width),
        if x86_gpr_view_width(src_name) == Some(*pointer_width),
        if x86_gpr_view_width(dst_name) == Some(*pointer_width),
        instr_in_function(addr, func),
        settled_sp_frame_shift(func, addr, depth),
        if let Some(ofs) = 0_i64.checked_sub(*depth);
    #[local] relation exact_frame_stack_lea_conflict(Address, Address);
    exact_frame_stack_lea_conflict(*func, *addr) <--
        exact_frame_stack_lea_member(func, addr, left),
        exact_frame_stack_lea_member(func, addr, right),
        if left != right;

    // Point-local frame-coordinate authority.  This fact depends only on the
    // decoded full-width stack base and the settled SP state at this
    // instruction.  An unrelated uncovered arm may veto whole-function MUST
    // provenance later, but it cannot turn this machine address into an
    // absolute integer.
    relation exact_frame_stack_lea(Address, Address, i64);
    exact_frame_stack_lea(*func, *addr, *ofs) <--
        exact_frame_stack_lea_member(func, addr, ofs),
        !exact_frame_stack_lea_conflict(func, addr);

    // Consume the already-settled dominator summary as the structural
    // reachable-block authority. Besides excluding disconnected decode
    // fragments, this schedules the two large point-state passes serially
    // instead of evaluating both lattices in one memory-heavy stage.
    #[local] relation reachable_frame_node(Address, Address);
    reachable_frame_node(*func, *node) <--
        instr_in_function(node, func),
        code_in_block(node, block),
        settled_block_dom_set(func, block, _);

    // Instruction CFG only. Numeric address or node order never participates
    // in reaching-write state.
    #[local] relation cfg_step(Address, Address);
    cfg_step(*src, *dst) <--
        next(src, dst),
        code_in_block(src, block),
        code_in_block(dst, block),
        !call_targets_noreturn(src);
    cfg_step(*src, *dst) <--
        ddisasm_cfg_edge(src, dst, edge_type),
        if *edge_type != "call" && *edge_type != "indirect" && *edge_type != "indirect_call",
        !call_targets_noreturn(src);

    // Pointer reads remain the provenance queries this pass was introduced
    // for.  Add a narrow query only when some exact write in the same frame
    // physically contains it; the lattice will still decide structurally
    // whether that write reaches the read.  This avoids multiplying every CFG
    // point by unrelated byte reads on large functions.  Escaped-only objects
    // have their own object proof in RTL and do not need a write-state cell.
    #[local] relation tracked_frame_cell(Address, i64, usize);
    tracked_frame_cell(*func, *ofs, *width) <--
        frame_stack_read_bytes(func, _, ofs, width),
        abi_pointer_size(pointer_width),
        if i64::try_from(*width).ok() == Some(*pointer_width);

    tracked_frame_cell(*func, *read_ofs, *read_width) <--
        frame_stack_read_bytes(func, _, read_ofs, read_width),
        frame_stack_write_bytes(func, _, write_ofs, write_width),
        if (*write_ofs, *write_width) != (*read_ofs, *read_width),
        if frame_interval_contains(*write_ofs, *write_width, *read_ofs, *read_width);

    #[local] relation node_has_cfg_predecessor(Address, Address);
    node_has_cfg_predecessor(*func, *node) <--
        cfg_step(pred, node),
        reachable_frame_node(func, pred),
        reachable_frame_node(func, node);

    // x86 has one explicit data-memory destination, but keep that decoder
    // contract explicit.  If two distinct normalized write roles ever appear
    // at one instruction, treating either one as the unique transfer would be
    // unsound; collapse the whole instruction to an unknown frame write.
    #[local] relation ambiguous_frame_stack_write(Address, Address);
    ambiguous_frame_stack_write(*func, *write) <--
        frame_stack_write_bytes(func, write, ofs_a, width_a),
        frame_stack_write_bytes(func, write, ofs_b, width_b),
        if (*ofs_a, *width_a) != (*ofs_b, *width_b);

    #[local] relation opaque_frame_stack_write(Address, Address);
    opaque_frame_stack_write(func, write) <--
        unnormalized_frame_stack_write(func, write);
    opaque_frame_stack_write(func, write) <--
        ambiguous_frame_stack_write(func, write);

    // Exactly one lattice row per (function, CFG point).  The set can contain
    // write facts for several frame intervals, but no interval participates in
    // the recursive key.  Storage is O(CFG points * may-reaching write facts),
    // with no pairwise point reachability and no historical lattice snapshots.
    #[local] lattice frame_write_in(Address, Address, Set<FrameWriteOrigin>);
    #[local] lattice frame_write_out(Address, Address, Set<FrameWriteOrigin>);

    frame_write_in(*func, *root, Set::singleton(FrameWriteOrigin::Unwritten(*cell_ofs, *cell_width))) <--
        reachable_frame_node(func, root),
        tracked_frame_cell(func, cell_ofs, cell_width),
        !node_has_cfg_predecessor(func, root);

    frame_write_in(*func, *entry, Set::singleton(FrameWriteOrigin::Unwritten(*cell_ofs, *cell_width))) <--
        reachable_frame_node(func, entry),
        if func == entry,
        tracked_frame_cell(func, cell_ofs, cell_width);

    frame_write_in(*func, *succ, state.clone()) <--
        frame_write_out(func, node, state),
        cfg_step(node, succ),
        reachable_frame_node(func, node),
        reachable_frame_node(func, succ);

    // Ordinary instructions preserve every reaching interval.
    frame_write_out(*func, *node, Set::singleton(*origin)) <--
        frame_write_in(func, node, state),
        for origin in state.0.iter(),
        !frame_stack_write_bytes(func, node, _, _),
        !opaque_frame_stack_write(func, node);

    // A unique exact write updates only the tracked query cells it overlaps.
    // Test the member's query interval, not the preceding physical writer's
    // interval: a wide initializer may reach several disjoint narrow queries.
    frame_write_out(*func, *write, Set::singleton(*origin)) <--
        frame_write_in(func, write, state),
        for origin in state.0.iter(),
        frame_stack_write_bytes(func, write, write_ofs, write_width),
        !opaque_frame_stack_write(func, write),
        if !frame_origin_cell_overlaps(origin, *write_ofs, *write_width);

    frame_write_out(
        *func,
        *write,
        Set::singleton(FrameWriteOrigin::Write(
            *write,
            *write_ofs,
            *write_width,
            *cell_ofs,
            *cell_width,
        )),
    ) <--
        frame_write_in(func, write, _),
        frame_stack_write_bytes(func, write, write_ofs, write_width),
        !opaque_frame_stack_write(func, write),
        tracked_frame_cell(func, cell_ofs, cell_width),
        if let Ok(cell_width_i64) = i64::try_from(*cell_width),
        if matches!(frame_intervals_overlap(*write_ofs, *write_width, *cell_ofs, cell_width_i64), Some(true));

    // An indexed/dynamic/ambiguous write may replace any tracked cell. Give
    // each cell its own interval-bearing Unknown value, so a later exact write
    // can restore that cell without erasing uncertainty for disjoint cells.
    frame_write_out(*func, *write, Set::singleton(FrameWriteOrigin::Unknown(*write, *cell_ofs, *cell_width))) <--
        frame_write_in(func, write, _),
        opaque_frame_stack_write(func, write),
        tracked_frame_cell(func, cell_ofs, cell_width);
}

pub struct FrameWritePass;

impl IRPass for FrameWritePass {
    fn name(&self) -> &'static str {
        "frame_write_state"
    }

    fn run(&self, db: &mut DecompileDB) {
        let mut prog = FrameWritePassProgram::default();
        prog.swap_db_fields(db);
        prog.run();

        // Read only settled lattice rows. Publishing an ordinary relation from
        // inside the recursive SCC would retain transient, incomplete states.
        let mut read_cells: std::collections::BTreeMap<(Address, Address), Vec<(i64, usize)>> =
            std::collections::BTreeMap::new();
        for (func, node, ofs, width) in prog.frame_stack_read_bytes.iter() {
            read_cells
                .entry((*func, *node))
                .or_default()
                .push((*ofs, *width));
        }
        for cells in read_cells.values_mut() {
            cells.sort_unstable();
            cells.dedup();
        }
        let reads: std::collections::HashSet<(Address, Address)> = prog
            .frame_stack_read_bytes
            .iter()
            .map(|(func, node, _, _)| (*func, *node))
            .collect();
        let mut settled: Vec<(Address, Address, Set<FrameWriteOrigin>)> = prog
            .frame_write_in
            .iter()
            .filter_map(|row| {
                let row = row.read().expect("frame-write lattice row lock poisoned");
                reads
                    .contains(&(row.0, row.1))
                    .then(|| (row.0, row.1, row.2.clone()))
            })
            .collect();
        settled.sort_by_key(|(func, node, _)| (*func, *node));

        // Project a unique, covering physical writer only after the lattice is
        // settled.  This keeps aggregation/negation out of RTL's large SCC and
        // gives later passes an O(number of reads) storage-provenance input,
        // never a pairwise reachability relation.
        let mut storage_origins = Vec::new();
        for (func, read, state) in &settled {
            let Some(cells) = read_cells.get(&(*func, *read)) else {
                continue;
            };
            for &(read_ofs, read_width) in cells {
                let mut origins = state
                    .0
                    .iter()
                    .filter(|origin| frame_origin_tracks(origin, read_ofs, read_width));
                let Some(origin) = origins.next() else {
                    continue;
                };
                if origins.next().is_some() {
                    continue;
                }
                let FrameWriteOrigin::Write(write, write_ofs, write_width, _, _) = origin else {
                    continue;
                };
                if frame_interval_contains(*write_ofs, *write_width, read_ofs, read_width) {
                    storage_origins.push((
                        *func,
                        *read,
                        read_ofs,
                        read_width,
                        *write,
                        *write_ofs,
                        *write_width,
                    ));
                }
            }
        }
        storage_origins.sort_unstable();
        storage_origins.dedup();

        if db.measure_rule_times {
            let pass_name = "FrameWritePassProgram".to_string();
            let summary = format!(
                "=== Rule Times ===\n{}\n\n=== Relation Sizes ===\n{}",
                prog.scc_times_summary(),
                prog.relation_sizes_summary(),
            );
            eprintln!(
                "[RULE_TIMES] pass {}\n{}\n[/RULE_TIMES]",
                pass_name, summary
            );
            db.rule_time_reports.push((pass_name, summary));
        }

        prog.swap_db_fields(db);
        let relation = ascent::boxcar::Vec::new();
        for fact in settled {
            relation.push(fact);
        }
        db.rel_set("settled_frame_write_state", relation);
        let relation = ascent::boxcar::Vec::new();
        for fact in storage_origins {
            relation.push(fact);
        }
        db.rel_set("settled_frame_storage_origin", relation);
    }

    fn inputs(&self) -> &'static [&'static str] {
        FrameWritePassProgram::inputs_only()
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "exact_frame_stack_lea",
            "frame_stack_read_bytes",
            "frame_stack_write_bytes",
            "settled_frame_storage_origin",
            "settled_frame_write_state",
            "unnormalized_frame_stack_write",
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::{frame_interval_contains, frame_origin_tracks, FrameWriteOrigin, FrameWritePass};
    use crate::decompile::elevator::DecompileDB;
    use crate::decompile::passes::pass::IRPass;
    use ascent::lattice::set::Set;

    fn settled_at(db: &DecompileDB, func: u64, reload: u64, slot: i64) -> Set<FrameWriteOrigin> {
        settled_at_width(db, func, reload, slot, 8)
    }

    fn settled_at_width(
        db: &DecompileDB,
        func: u64,
        reload: u64,
        slot: i64,
        width: usize,
    ) -> Set<FrameWriteOrigin> {
        let state = db
            .rel_iter::<(u64, u64, Set<FrameWriteOrigin>)>("settled_frame_write_state")
            .find_map(|(owner, node, state)| {
                (*owner == func && *node == reload).then(|| state.clone())
            })
            .expect("reload must have one settled reaching-write state");
        Set(state
            .0
            .into_iter()
            .filter(|origin| frame_origin_tracks(origin, slot, width))
            .collect())
    }

    #[test]
    fn narrow_read_retains_its_structurally_covering_wide_write() {
        let func = 0x8000_u64;
        let write = 0x8010_u64;
        let read = 0x8020_u64;
        let mut db = DecompileDB::default();
        db.rel_push("abi_pointer_size", (8_i64,));
        for node in [func, write, read] {
            db.rel_push("instr_in_function", (node, func));
            db.rel_push("code_in_block", (node, node));
            db.rel_push("settled_sp_frame_shift", (func, node, 0_i64));
            db.rel_push("settled_block_dom_set", (func, node, Set::singleton(node)));
        }
        db.rel_push("ddisasm_cfg_edge", (func, write, "branch"));
        db.rel_push("ddisasm_cfg_edge", (write, read, "branch"));
        db.rel_push("decoded_stack_write_bytes", (write, "RSP", 4_i64, 4_usize));
        db.rel_push("decoded_stack_read_bytes", (read, "RSP", 5_i64, 1_usize));

        FrameWritePass.run(&mut db);

        assert_eq!(
            settled_at_width(&db, func, read, 5, 1).0,
            std::collections::BTreeSet::from([FrameWriteOrigin::Write(write, 4, 4, 5, 1)])
        );
        assert!(frame_interval_contains(4, 4, 5, 1));
        assert!(!frame_interval_contains(4, 1, 4, 4));
    }

    #[test]
    fn partial_and_dynamic_writes_replace_pointer_spills_but_disjoint_writes_do_not() {
        let func = 0x1000_u64;
        let entry = func;
        let spill = 0x1010_u64;
        let disjoint = 0x1020_u64;
        let reload = 0x1030_u64;

        let mut disjoint_db = DecompileDB::default();
        disjoint_db.rel_push("abi_pointer_size", (8_i64,));
        for node in [entry, spill, disjoint, reload] {
            disjoint_db.rel_push("instr_in_function", (node, func));
            disjoint_db.rel_push("code_in_block", (node, node));
            disjoint_db.rel_push("settled_sp_frame_shift", (func, node, 0_i64));
            disjoint_db.rel_push("settled_block_dom_set", (func, node, Set::singleton(node)));
        }
        disjoint_db.rel_push("ddisasm_cfg_edge", (entry, spill, "branch"));
        disjoint_db.rel_push("ddisasm_cfg_edge", (spill, disjoint, "branch"));
        disjoint_db.rel_push("ddisasm_cfg_edge", (disjoint, reload, "branch"));
        disjoint_db.rel_push("decoded_stack_read_bytes", (reload, "RSP", 0_i64, 8_usize));
        disjoint_db.rel_push("decoded_stack_write_bytes", (spill, "RSP", 0_i64, 8_usize));
        disjoint_db.rel_push(
            "decoded_stack_write_bytes",
            (disjoint, "RSP", 8_i64, 1_usize),
        );
        FrameWritePass.run(&mut disjoint_db);
        assert_eq!(
            settled_at(&disjoint_db, func, reload, 0).0,
            std::collections::BTreeSet::from([FrameWriteOrigin::Write(spill, 0, 8, 0, 8)])
        );

        for dynamic in [false, true] {
            let mut db = DecompileDB::default();
            let overwrite = 0x1040_u64;
            db.rel_push("abi_pointer_size", (8_i64,));
            for node in [entry, spill, overwrite, reload] {
                db.rel_push("instr_in_function", (node, func));
                db.rel_push("code_in_block", (node, node));
                db.rel_push("settled_sp_frame_shift", (func, node, 0_i64));
                db.rel_push("settled_block_dom_set", (func, node, Set::singleton(node)));
            }
            db.rel_push("ddisasm_cfg_edge", (entry, spill, "branch"));
            db.rel_push("ddisasm_cfg_edge", (spill, overwrite, "branch"));
            db.rel_push("ddisasm_cfg_edge", (overwrite, reload, "branch"));
            db.rel_push("decoded_stack_read_bytes", (reload, "RSP", 0_i64, 8_usize));
            db.rel_push("decoded_stack_write_bytes", (spill, "RSP", 0_i64, 8_usize));
            if dynamic {
                db.rel_push("decoded_stack_write_unresolved", (overwrite, "RSP"));
            } else {
                db.rel_push(
                    "decoded_stack_write_bytes",
                    (overwrite, "RSP", 1_i64, 1_usize),
                );
            }
            FrameWritePass.run(&mut db);
            assert_eq!(
                settled_at(&db, func, reload, 0).0,
                std::collections::BTreeSet::from([if dynamic {
                    FrameWriteOrigin::Unknown(overwrite, 0, 8)
                } else {
                    FrameWriteOrigin::Write(overwrite, 1, 1, 0, 8)
                }])
            );
        }
    }

    #[test]
    fn unwritten_join_arm_remains_explicit_unknown() {
        let func = 0x2000_u64;
        let entry = func;
        let spill = 0x2010_u64;
        let untouched = 0x2020_u64;
        let reload = 0x2030_u64;
        let mut db = DecompileDB::default();
        db.rel_push("abi_pointer_size", (8_i64,));
        for node in [entry, spill, untouched, reload] {
            db.rel_push("instr_in_function", (node, func));
            db.rel_push("code_in_block", (node, node));
            db.rel_push("settled_sp_frame_shift", (func, node, 0_i64));
            db.rel_push("settled_block_dom_set", (func, node, Set::singleton(node)));
        }
        for edge in [
            (entry, spill, "branch"),
            (entry, untouched, "branch"),
            (spill, reload, "branch"),
            (untouched, reload, "branch"),
        ] {
            db.rel_push("ddisasm_cfg_edge", edge);
        }
        db.rel_push("decoded_stack_read_bytes", (reload, "RSP", 24_i64, 8_usize));
        db.rel_push("decoded_stack_write_bytes", (spill, "RSP", 24_i64, 8_usize));
        FrameWritePass.run(&mut db);
        assert_eq!(
            settled_at(&db, func, reload, 24).0,
            std::collections::BTreeSet::from([
                FrameWriteOrigin::Unwritten(24, 8),
                FrameWriteOrigin::Write(spill, 24, 8, 24, 8),
            ])
        );
    }

    #[test]
    fn narrow_write_does_not_erase_a_disjoint_subcell_query() {
        let func = 0x2800_u64;
        let wide_write = 0x2810_u64;
        let byte_rmw = 0x2820_u64;
        let word_read = 0x2830_u64;
        let mut db = DecompileDB::default();
        db.rel_push("abi_pointer_size", (8_i64,));
        for node in [func, wide_write, byte_rmw, word_read] {
            db.rel_push("instr_in_function", (node, func));
            db.rel_push("code_in_block", (node, node));
            db.rel_push("settled_sp_frame_shift", (func, node, 0_i64));
            db.rel_push("settled_block_dom_set", (func, node, Set::singleton(node)));
        }
        for edge in [
            (func, wide_write),
            (wide_write, byte_rmw),
            (byte_rmw, word_read),
        ] {
            db.rel_push("ddisasm_cfg_edge", (edge.0, edge.1, "branch"));
        }
        db.rel_push(
            "decoded_stack_write_bytes",
            (wide_write, "RSP", -8_i64, 8_usize),
        );
        db.rel_push(
            "decoded_stack_read_bytes",
            (byte_rmw, "RSP", -8_i64, 1_usize),
        );
        db.rel_push(
            "decoded_stack_write_bytes",
            (byte_rmw, "RSP", -8_i64, 1_usize),
        );
        db.rel_push(
            "decoded_stack_read_bytes",
            (word_read, "RSP", -6_i64, 2_usize),
        );

        FrameWritePass.run(&mut db);

        assert_eq!(
            settled_at_width(&db, func, word_read, -6, 2).0,
            std::collections::BTreeSet::from([FrameWriteOrigin::Write(wide_write, -8, 8, -6, 2,)])
        );
        assert!(db
            .rel_iter::<(u64, u64, i64, usize, u64, i64, usize)>("settled_frame_storage_origin")
            .any(|fact| fact == &(func, word_read, -6, 2, wide_write, -8, 8)));
    }

    #[test]
    fn exact_coordinates_require_settled_sp_state_and_unindexed_stack_bases() {
        let func = 0x3000_u64;
        let setup = 0x3010_u64;
        let known_write = 0x3020_u64;
        let missing_write = 0x3030_u64;
        let indexed_write = 0x3040_u64;
        let known_lea = 0x3050_u64;
        let missing_lea = 0x3060_u64;
        let bp_write = 0x3070_u64;
        let esp_write = 0x3080_u64;
        let esp_lea = 0x3090_u64;
        let known_mov = 0x30a0_u64;
        let missing_mov = 0x30b0_u64;
        let narrow_mov = 0x30c0_u64;
        let mut db = DecompileDB::default();

        db.rel_push("abi_pointer_size", (8_i64,));
        for node in [
            func,
            setup,
            known_write,
            missing_write,
            indexed_write,
            known_lea,
            missing_lea,
            bp_write,
            esp_write,
            esp_lea,
            known_mov,
            missing_mov,
            narrow_mov,
        ] {
            db.rel_push("instr_in_function", (node, func));
            db.rel_push("code_in_block", (node, node));
            db.rel_push("settled_block_dom_set", (func, node, Set::singleton(node)));
        }
        for node in [known_write, indexed_write, known_lea, known_mov, narrow_mov] {
            db.rel_push("settled_sp_frame_shift", (func, node, 8_i64));
        }
        db.rel_push("settled_sp_frame_shift", (func, esp_write, 8_i64));
        db.rel_push("settled_sp_frame_shift", (func, esp_lea, 8_i64));
        db.rel_push("function_has_ltl_body", (func,));

        db.rel_push(
            "decoded_stack_write_bytes",
            (known_write, "RSP", 24_i64, 8_usize),
        );
        db.rel_push(
            "decoded_stack_write_bytes",
            (missing_write, "RSP", 32_i64, 8_usize),
        );
        db.rel_push("decoded_stack_write_unresolved", (indexed_write, "RSP"));
        db.rel_push(
            "decoded_stack_write_bytes",
            (bp_write, "RBP", -16_i64, 8_usize),
        );
        db.rel_push(
            "decoded_stack_write_bytes",
            (esp_write, "ESP", 24_i64, 8_usize),
        );

        for (node, dst, memory, raw_ofs) in [
            (known_lea, "known_dst", "known_mem", 24_i64),
            (missing_lea, "missing_dst", "missing_mem", 24_i64),
            (esp_lea, "esp_dst", "esp_mem", 24_i64),
        ] {
            db.rel_push("plea", (node, dst, memory));
            db.rel_push(
                "op_indirect",
                (
                    memory,
                    "",
                    if node == esp_lea { "ESP" } else { "RSP" },
                    "NONE",
                    1_i64,
                    raw_ofs,
                    8_usize,
                ),
            );
        }
        for (node, dst, dst_name, src, src_name) in [
            (known_mov, "known_mov_dst", "RDI", "known_mov_src", "RSP"),
            (
                missing_mov,
                "missing_mov_dst",
                "RDI",
                "missing_mov_src",
                "RSP",
            ),
            (narrow_mov, "narrow_mov_dst", "EDI", "narrow_mov_src", "ESP"),
        ] {
            db.rel_push("pmov", (node, dst, src));
            db.rel_push("op_register", (dst, dst_name));
            db.rel_push("op_register", (src, src_name));
        }

        FrameWritePass.run(&mut db);

        let writes: std::collections::BTreeSet<_> = db
            .rel_iter::<(u64, u64, i64, usize)>("frame_stack_write_bytes")
            .copied()
            .collect();
        assert!(writes.contains(&(func, known_write, 16, 8)));
        assert!(!writes.iter().any(|(_, node, _, _)| *node == bp_write));
        assert!(!writes.iter().any(|(_, node, _, _)| *node == esp_write));
        assert!(!writes.iter().any(|(_, node, _, _)| *node == missing_write));
        let unresolved: std::collections::BTreeSet<_> = db
            .rel_iter::<(u64, u64)>("unnormalized_frame_stack_write")
            .copied()
            .collect();
        assert!(unresolved.contains(&(func, missing_write)));
        assert!(unresolved.contains(&(func, indexed_write)));
        assert!(unresolved.contains(&(func, bp_write)));
        assert!(unresolved.contains(&(func, esp_write)));
        let exact_leas: std::collections::BTreeSet<_> = db
            .rel_iter::<(u64, u64, i64)>("exact_frame_stack_lea")
            .copied()
            .collect();
        assert!(exact_leas.contains(&(func, known_lea, 16)));
        assert!(exact_leas.contains(&(func, known_mov, -8)));
        assert!(!exact_leas.iter().any(|(_, node, _)| *node == missing_lea));
        assert!(!exact_leas.iter().any(|(_, node, _)| *node == esp_lea));
        assert!(!exact_leas.iter().any(|(_, node, _)| *node == missing_mov));
        assert!(!exact_leas.iter().any(|(_, node, _)| *node == narrow_mov));
    }

    #[test]
    fn point_local_stack_lea_survives_unrelated_body_incompleteness() {
        let func = 0x4000_u64;
        let lea = 0x4010_u64;
        let unresolved = 0x4020_u64;
        let mut db = DecompileDB::default();

        db.rel_push("abi_pointer_size", (8_i64,));
        db.rel_push("instr_in_function", (lea, func));
        db.rel_push("settled_sp_frame_shift", (func, lea, 8_i64));
        db.rel_push("function_has_ltl_body", (func,));
        db.rel_push("function_unresolved_control", (func, unresolved));
        db.rel_push("plea", (lea, "point_dst", "point_mem"));
        db.rel_push(
            "op_indirect",
            ("point_mem", "", "RSP", "NONE", 1_i64, 40_i64, 8_usize),
        );

        FrameWritePass.run(&mut db);

        assert!(db
            .rel_iter::<(u64, u64, i64)>("exact_frame_stack_lea")
            .any(|fact| fact == &(func, lea, 32)));
    }
}
