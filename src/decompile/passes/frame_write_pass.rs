use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::x86::types::{Address, Node, Symbol};
use ascent::ascent_par;
use ascent::lattice::set::Set;

// A may-reaching frame write at one CFG point.  The interval belongs inside
// the lattice value, never in its key: keying the recursive state by both node
// and pointer cell materializes a node x cell product and can become quadratic
// in large functions.  `Unwritten` and `Unknown` retain the queried interval so
// an exact later write can replace only the cells that it actually covers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FrameWriteOrigin {
    Unwritten(i64, usize),
    Unknown(Address, i64, usize),
    Write(Address, i64, usize),
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
        "RSP" | "RBP" => Some(8),
        "ESP" | "EBP" => Some(4),
        "SP" | "BP" => Some(2),
        "SPL" | "BPL" => Some(1),
        _ => None,
    }
}

pub(crate) fn frame_origin_overlaps(
    origin: &FrameWriteOrigin,
    cell_ofs: i64,
    cell_width: usize,
) -> bool {
    let (origin_ofs, origin_width) = match origin {
        FrameWriteOrigin::Unwritten(ofs, width)
        | FrameWriteOrigin::Unknown(_, ofs, width)
        | FrameWriteOrigin::Write(_, ofs, width) => (*ofs, *width),
    };
    let Ok(cell_width) = i64::try_from(cell_width) else {
        return true;
    };
    // Invalid intervals are never evidence for a MUST spill. Treat them as
    // overlapping so they survive to the reload and veto provenance.
    frame_intervals_overlap(origin_ofs, origin_width, cell_ofs, cell_width).unwrap_or(true)
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
    relation plea(Address, Symbol, Symbol);
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
    #[local] relation exact_frame_stack_lea_conflict(Address, Address);
    exact_frame_stack_lea_conflict(*func, *addr) <--
        exact_frame_stack_lea_member(func, addr, left),
        exact_frame_stack_lea_member(func, addr, right),
        if left != right;

    relation exact_frame_stack_lea(Address, Address, i64);
    exact_frame_stack_lea(*func, *addr, *ofs) <--
        exact_frame_stack_lea_member(func, addr, ofs),
        function_has_ltl_body(func),
        !function_has_uncovered_block(func),
        !function_unknown_terminal(func, _),
        !function_unresolved_control(func, _),
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

    #[local] relation tracked_pointer_cell(Address, i64, usize);
    tracked_pointer_cell(*func, *ofs, *width) <--
        frame_stack_read_bytes(func, _, ofs, width),
        abi_pointer_size(pointer_width),
        if i64::try_from(*width).ok() == Some(*pointer_width);

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
        tracked_pointer_cell(func, cell_ofs, cell_width),
        !node_has_cfg_predecessor(func, root);

    frame_write_in(*func, *func, Set::singleton(FrameWriteOrigin::Unwritten(*cell_ofs, *cell_width))) <--
        reachable_frame_node(func, func),
        tracked_pointer_cell(func, cell_ofs, cell_width);

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

    // A unique exact write kills only origins whose intervals overlap it.
    frame_write_out(*func, *write, Set::singleton(*origin)) <--
        frame_write_in(func, write, state),
        for origin in state.0.iter(),
        frame_stack_write_bytes(func, write, write_ofs, write_width),
        !opaque_frame_stack_write(func, write),
        if !frame_origin_overlaps(origin, *write_ofs, *write_width);

    frame_write_out(*func, *write, Set::singleton(FrameWriteOrigin::Write(*write, *write_ofs, *write_width))) <--
        frame_write_in(func, write, _),
        frame_stack_write_bytes(func, write, write_ofs, write_width),
        !opaque_frame_stack_write(func, write),
        tracked_pointer_cell(func, cell_ofs, cell_width),
        if let Ok(cell_width) = i64::try_from(*cell_width),
        if matches!(frame_intervals_overlap(*write_ofs, *write_width, *cell_ofs, cell_width), Some(true));

    // An indexed/dynamic/ambiguous write may replace any tracked cell. Give
    // each cell its own interval-bearing Unknown value, so a later exact write
    // can restore that cell without erasing uncertainty for disjoint cells.
    frame_write_out(*func, *write, Set::singleton(FrameWriteOrigin::Unknown(*write, *cell_ofs, *cell_width))) <--
        frame_write_in(func, write, _),
        opaque_frame_stack_write(func, write),
        tracked_pointer_cell(func, cell_ofs, cell_width);
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
        let pointer_widths: std::collections::HashSet<usize> = prog
            .abi_pointer_size
            .iter()
            .filter_map(|(width,)| usize::try_from(*width).ok())
            .collect();
        let reads: std::collections::HashSet<(Address, Address)> = prog
            .frame_stack_read_bytes
            .iter()
            .filter(|(_, _, _, width)| pointer_widths.contains(width))
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
    }

    fn inputs(&self) -> &'static [&'static str] {
        FrameWritePassProgram::inputs_only()
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "exact_frame_stack_lea",
            "frame_stack_read_bytes",
            "frame_stack_write_bytes",
            "settled_frame_write_state",
            "unnormalized_frame_stack_write",
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::{frame_origin_overlaps, FrameWriteOrigin, FrameWritePass};
    use crate::decompile::elevator::DecompileDB;
    use crate::decompile::passes::pass::IRPass;
    use ascent::lattice::set::Set;

    fn settled_at(db: &DecompileDB, func: u64, reload: u64, slot: i64) -> Set<FrameWriteOrigin> {
        let state = db
            .rel_iter::<(u64, u64, Set<FrameWriteOrigin>)>("settled_frame_write_state")
            .find_map(|(owner, node, state)| {
                (*owner == func && *node == reload).then(|| state.clone())
            })
            .expect("reload must have one settled reaching-write state");
        Set(state
            .0
            .into_iter()
            .filter(|origin| frame_origin_overlaps(origin, slot, 8))
            .collect())
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
            std::collections::BTreeSet::from([FrameWriteOrigin::Write(spill, 0, 8)])
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
                    FrameWriteOrigin::Write(overwrite, 1, 1)
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
                FrameWriteOrigin::Write(spill, 24, 8),
            ])
        );
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
        ] {
            db.rel_push("instr_in_function", (node, func));
            db.rel_push("code_in_block", (node, node));
            db.rel_push("settled_block_dom_set", (func, node, Set::singleton(node)));
        }
        for node in [known_write, indexed_write, known_lea] {
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
        assert!(!exact_leas.iter().any(|(_, node, _)| *node == missing_lea));
        assert!(!exact_leas.iter().any(|(_, node, _)| *node == esp_lea));
    }
}
