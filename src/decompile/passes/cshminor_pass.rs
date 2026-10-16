use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::{declare_io_from, run_pass};

use crate::decompile::passes::cminor_pass::*;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::mreg::Mreg;
use crate::x86::op::{Addressing, Comparison, Condition, Operation};
use crate::x86::types::*;
use ascent::ascent_par;
use ascent::lattice::set::Set;
use ascent::Dual;

fn unique_external_cfg_entry(
    implementation_nodes: &std::collections::HashSet<Node>,
    cfg_edges: &[(Node, Node)],
) -> Option<Node> {
    let entries: std::collections::HashSet<Node> = cfg_edges
        .iter()
        .filter_map(|&(src, dst)| {
            (implementation_nodes.contains(&dst) && !implementation_nodes.contains(&src))
                .then_some(dst)
        })
        .collect();
    (entries.len() == 1).then(|| *entries.iter().next().unwrap())
}

fn collect_dense_node_targets<'a>(
    inp: impl Iterator<Item = (&'a usize, &'a Node)>,
) -> impl Iterator<Item = Arc<Vec<Node>>> {
    let mut pairs: Vec<(usize, Node)> = inp.map(|(idx, node)| (*idx, *node)).collect();
    pairs.sort();
    pairs.dedup();
    let conflict = pairs.windows(2).any(|pair| pair[0].0 == pair[1].0);
    let dense = !conflict
        && pairs
            .iter()
            .enumerate()
            .all(|(expected, (actual, _))| expected == *actual);
    dense
        .then(|| Arc::new(pairs.into_iter().map(|(_, node)| node).collect()))
        .into_iter()
}

fn compute_canonical_stack_slot_locals(
    rows: impl IntoIterator<Item = (Address, Address, i64, RTLReg)>,
) -> Vec<(Address, i64, RTLReg)> {
    let mut grouped =
        std::collections::BTreeMap::<(Address, i64), std::collections::BTreeSet<RTLReg>>::new();
    for (func, _node, ofs, local) in rows {
        grouped.entry((func, ofs)).or_default().insert(local);
    }
    grouped
        .into_iter()
        .map(|((func, ofs), locals)| {
            (
                func,
                ofs,
                *locals.iter().next().expect("nonempty stack-local set"),
            )
        })
        .collect()
}

// Helper: add node n to a Set<Node>, returning new Set
fn dom_set_with_self(strict: &Set<Node>, n: Node) -> Set<Node> {
    let mut s = strict.0.clone();
    s.insert(n);
    Set(s)
}

// Substitute every Evar(old) with Evar(new) inside a Csharpminor expression.
fn cond_subst_var_in_expr(expr: &CsharpminorExpr, old: RTLReg, new: RTLReg) -> CsharpminorExpr {
    match expr {
        CsharpminorExpr::Evar(r) if *r == old => CsharpminorExpr::Evar(new),
        CsharpminorExpr::Eunop(op, inner) => CsharpminorExpr::Eunop(
            op.clone(),
            Box::new(cond_subst_var_in_expr(inner, old, new)),
        ),
        CsharpminorExpr::Ebinop(op, l, r) => CsharpminorExpr::Ebinop(
            op.clone(),
            Box::new(cond_subst_var_in_expr(l, old, new)),
            Box::new(cond_subst_var_in_expr(r, old, new)),
        ),
        CsharpminorExpr::Eload(chunk, addr) => {
            CsharpminorExpr::Eload(*chunk, Box::new(cond_subst_var_in_expr(addr, old, new)))
        }
        CsharpminorExpr::Econdition(c, t, f) => CsharpminorExpr::Econdition(
            Box::new(cond_subst_var_in_expr(c, old, new)),
            Box::new(cond_subst_var_in_expr(t, old, new)),
            Box::new(cond_subst_var_in_expr(f, old, new)),
        ),
        _ => expr.clone(),
    }
}

fn cond_subst_exprs(args: &[CsharpminorExpr], old: RTLReg, new: RTLReg) -> Vec<CsharpminorExpr> {
    args.iter()
        .map(|e| cond_subst_var_in_expr(e, old, new))
        .collect()
}

const ARITH_LOAD_SYNTH_NODE_BIT: u64 = 1u64 << 62;

/// All fixed, post-RTL evidence required to reinterpret one memory-source
/// arithmetic operand as a physical frame load.  Keeping the full proof in one
/// value lets the Datalog layer reject any disagreement before changing the
/// generic Cminor conversion.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct PostRtlArithLoadClaim {
    function: Address,
    real_node: Node,
    operation: Operation,
    chunk: MemoryChunk,
    raw_displacement: i64,
    destination_mreg: Mreg,
    result: RTLReg,
    read_offset: i64,
    read_width: usize,
    base_offset: i64,
    owner: RTLReg,
    extent: i64,
    address_is_64bit: bool,
}

/// Replace only the exact owner operand emitted by RTL's memory-source
/// arithmetic expansion.  The finalized RTL shape is checked in Datalog; this
/// helper independently checks the Cminor operation/result shape so a later IR
/// change fails closed instead of rewriting the wrong variable occurrence.
fn post_rtl_arith_load_stmt(
    destination: RTLReg,
    expr: &CminorExpr,
    claim: &PostRtlArithLoadClaim,
) -> Option<CsharpminorStmt> {
    let CminorExpr::Ebinop(binop, lhs, rhs) = expr else {
        return None;
    };
    let expected_binop = binop_from_operation(&claim.operation)?;
    if *binop != expected_binop
        || destination != claim.result
        || *lhs != claim.result
        || *rhs != claim.owner
        || claim.result == claim.owner
    {
        return None;
    }

    let delta = claim.read_offset.checked_sub(claim.base_offset)?;
    if delta < 0 {
        return None;
    }
    let owner_address = CsharpminorExpr::Eaddrof(ident_from_reg(claim.owner));
    let address = if delta == 0 {
        owner_address
    } else if claim.address_is_64bit {
        CsharpminorExpr::Ebinop(
            CminorBinop::Oaddl,
            Box::new(owner_address),
            Box::new(CsharpminorExpr::Econst(Constant::Olongconst(delta))),
        )
    } else {
        CsharpminorExpr::Ebinop(
            CminorBinop::Oadd,
            Box::new(owner_address),
            Box::new(CsharpminorExpr::Econst(Constant::Ointconst(delta))),
        )
    };
    let loaded = CsharpminorExpr::Eload(claim.chunk, Box::new(address));
    Some(CsharpminorStmt::Sset(
        destination,
        CsharpminorExpr::Ebinop(
            binop.clone(),
            Box::new(CsharpminorExpr::Evar(claim.result)),
            Box::new(loaded),
        ),
    ))
}

/// Split an immediate equality comparison into the register/register
/// condition and Cminor binary operator that preserve its width/signedness.
/// Only equality is admitted: ordering unrelated C objects is not a portable
/// reconstruction of the linked image's numeric address order.
fn symbolic_pointer_comparison(condition: &Condition) -> Option<(Condition, CminorBinop, i64)> {
    let equality =
        |comparison: &Comparison| matches!(comparison, Comparison::Ceq | Comparison::Cne);
    match condition {
        Condition::Ccompimm(comparison, immediate) if equality(comparison) => Some((
            Condition::Ccomp(*comparison),
            CminorBinop::Ocmp(*comparison),
            *immediate,
        )),
        Condition::Ccompuimm(comparison, immediate) if equality(comparison) => Some((
            Condition::Ccompu(*comparison),
            CminorBinop::Ocmpu(*comparison),
            *immediate,
        )),
        Condition::Ccomplimm(comparison, immediate) if equality(comparison) => Some((
            Condition::Ccompl(*comparison),
            CminorBinop::Ocmpl(*comparison),
            *immediate,
        )),
        Condition::Ccompluimm(comparison, immediate) if equality(comparison) => Some((
            Condition::Ccomplu(*comparison),
            CminorBinop::Ocmplu(*comparison),
            *immediate,
        )),
        _ => None,
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Copy)]
pub enum LoopType {
    PreTested,
    PostTested,
    MidTested,
    Infinite,
}
use either::Either;

ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct CshminorPassProgram;


    relation cminor_stmt(Node, CminorStmt);
    relation trim_jump_table_impl(Node);
    relation abi_pointer_size(i64);

    // Memory addressing is performed at the target pointer width.  Emitting
    // both Oadd and Oaddl candidates on LP64 let selection choose a compiling
    // but truncating `(unsigned int)base + index` expression.  Keep the old
    // two-width fallback only for isolated relation tests that omit ABI facts.
    #[local] relation csharp_address_is_64bit(bool);
    csharp_address_is_64bit(true) <--
        abi_pointer_size(size),
        if *size >= 8;
    csharp_address_is_64bit(false) <--
        abi_pointer_size(size),
        if *size < 8;
    csharp_address_is_64bit(false) <-- !abi_pointer_size(_);
    csharp_address_is_64bit(true) <-- !abi_pointer_size(_);

    #[local] relation active_cminor_stmt(Node, CminorStmt);
    active_cminor_stmt(node, stmt.clone()) <--
        cminor_stmt(node, stmt),
        !trim_jump_table_impl(node);
    active_cminor_stmt(node, stmt.clone()) <--
        cminor_stmt(node, stmt),
        trim_jump_table_impl(node),
        if matches!(stmt, CminorStmt::Sjumptable(_, _));

    relation instr_in_function(Node, Address);
    // Exact evidence needed to reinterpret a linked absolute immediate as an
    // address constant after Cminor has embedded it in a Condition.
    relation raw_image_addresses_are_absolute(bool);
    relation data_section_range(Address, Address);
    relation base_ident_to_symbol(Ident, Symbol);
    relation interior_to_base_ident(Ident, Ident, i64);
    relation must_be_ptr(RTLReg);
    relation global_var_ref(Ident);
    relation rtl_succ(Node, Node);
    relation rtl_expansion_edge(Node, Node);
    #[local] relation rtl_expansion_member(Node);
    rtl_expansion_member(src) <-- rtl_expansion_edge(src, _);
    rtl_expansion_member(dst) <-- rtl_expansion_edge(_, dst);
    #[local] relation rtl_optimized_expansion_edge(Node, Node);
    rtl_optimized_expansion_edge(src, dst) <--
        rtl_succ(src, dst),
        rtl_expansion_member(src);
    rtl_optimized_expansion_edge(src, dst) <--
        rtl_succ(src, dst),
        rtl_expansion_member(dst);
    relation cminor_fallthrough(Node, Node);
    relation emit_function(Address, Symbol, Node);
    // Post-optimizer semantic entry.  Keep this distinct from emit_function's
    // raw machine entry, which remains necessary for ABI/register recovery.
    relation rtl_function_entry(Address, Node);
    relation emit_function_param(Address, RTLReg);
    relation next(Address, Address);
    relation idom(Address, Node, Node);
    relation stack_var(Address, Address, i64, RTLReg);
    relation func_stacksz(Address, Address, Symbol, u64);
    relation known_func_param_pointee_size(Symbol, usize, usize);
    relation canonical_stack_slot_local(Address, i64, RTLReg);
    // rtl_pass export: the single escaped canonical local per (func, offset), used to resolve synthetic-only stack loads that have no per-node stack_var.
    relation slot_escaped_canonical(Address, i64, RTLReg);
    // Canonical scalar local for each exact field belonging to a wider escaped
    // region.  At the region base this is the same backing-owner authority the
    // final C layout consumes when it constructs one byte buffer.
    relation slot_escaped_region_canonical(Address, i64, RTLReg);
    // rtl_pass export: a conflict-free physical owner for a frame read that
    // begins inside a wider reaching write or escaped object.
    relation frame_read_storage_owner(Address, Address, i64, i64, RTLReg);
    // Reads/stores that must preserve byte-addressed access through that owner
    // rather than collapsing to the owner's scalar SSA value.
    relation frame_read_storage_access_owner(Address, Address, i64, i64, RTLReg);
    relation frame_write_storage_owner(Address, Address, i64, i64, RTLReg);
    // Fixed post-RTL evidence for memory-source arithmetic whose stack operand
    // was initially represented by the canonical slot value.  This pass runs
    // after RTL and its storage/extent analyses have settled, so consuming the
    // complete relations here cannot feed a candidate-selection cycle back
    // into RTL.
    relation arith_load_op(Address, Operation, MemoryChunk, Mreg, i64, Mreg);
    relation frame_stack_read_bytes(Address, Address, i64, usize);
    relation escaped_stack_region_extent(Address, i64, i64);
    relation escaped_stack_region_field(Address, i64, i64, MemoryChunk);
    relation escaped_stack_region_caller_field(Address, i64, i64, MemoryChunk);
    // Exact fixed-size external ABI objects (for example struct stat).  These
    // remain byte-addressed even when the caller reads the first field at the
    // object's base.
    relation external_stack_object_extent(Address, i64, i64);
    // Post-RTL exact external object certificate: function, frame base,
    // emitted local, byte extent.  Cminor has already joined the named call
    // argument to the unique SSA result of Oaddrstack, so no earlier alias
    // reconstruction is needed.
    relation external_stack_object_local(Address, i64, RTLReg, i64);
    relation reg_rtl(Node, Mreg, RTLReg);
    relation rtl_inst(Node, RTLInst);
    // Noreturn recognition inputs: the always-noreturn symbol set, single-def constants for resolving an error-family status arg, and function_noreturn for user-defined wrappers.
    relation is_known_noreturn_function(Symbol);
    relation single_def_const(RTLReg, Constant);
    relation function_noreturn(Address);
    relation symbol_resolved_addr(Symbol, Address);
    // Memory-indirect call/tail transfer: rtl_pass surfaces the load addressing
    // so we can inline the function-pointer load into the callee expression
    // (renders as `(*(base + disp))(args)`).
    relation call_through_memory_load(Node, RTLReg, MemoryChunk, Addressing, Args);
    // signature_pass: the function returns void, so a loop exit flowing to its return stays a plain break; used to gate loop_exit_to_return to value-returning functions only.
    relation emit_function_void_candidate(Address);


    relation stmt_can_fallthrough(Node);
    relation csh_next(Node, Node);
    relation cminor_succ(Node, Node);
    relation func_entry_node(Address, Node);
    relation pred(Address, Node, Node);

    #[local] relation csh_frame_size_member(Address, i64);
    csh_frame_size_member(*func, frame_size) <--
        func_stacksz(func, _, _, size),
        if let Ok(frame_size) = i64::try_from(*size),
        if frame_size > 0;

    #[local] relation csh_frame_size_conflict(Address);
    csh_frame_size_conflict(func) <--
        csh_frame_size_member(func, left),
        csh_frame_size_member(func, right),
        if left != right;

    #[local] relation csh_local_frame_size(Address, i64);
    csh_local_frame_size(func, *size) <--
        csh_frame_size_member(func, size),
        !csh_frame_size_conflict(func);

    #[local] relation external_stack_object_local_candidate(
        Address, i64, RTLReg, i64, Symbol, usize
    );
    external_stack_object_local_candidate(*func, *base, *owner, extent, *name, *pos) <--
        active_cminor_stmt(call, ?CminorStmt::Scall(_, _, Either::Right(Either::Right(name)), args)),
        known_func_param_pointee_size(name, pos, bytes),
        if let Some(argument) = args.get(*pos),
        active_cminor_stmt(lea, ?CminorStmt::Sassign(address, CminorExpr::Econst(Constant::Oaddrstack(base)))),
        if address == argument,
        instr_in_function(call, func),
        instr_in_function(lea, func),
        stack_var(func, lea, base, owner),
        csh_local_frame_size(func, frame_size),
        if let Ok(extent) = i64::try_from(*bytes),
        if extent > 0 && extent <= (1 << 20),
        if let Some(end) = base.checked_add(extent),
        if *base >= 0 && end <= *frame_size;

    // A pointer-width select can pass either a caller-provided object or a
    // local fallback to a fixed-layout external out-parameter.  The external
    // call may therefore write the complete ABI object into every stack arm.
    // Recover each explicit Oaddrstack arm structurally; condition operands
    // begin at position two and cannot be storage origins.
    #[local] relation external_stack_object_selected_local_candidate(
        Address, i64, RTLReg, i64, Symbol, usize
    );

    // A Cminor register copy commonly separates the select from its call use.
    // Reject a copied destination if any active alternative gives it a
    // different definition.  Keeping this as one conflict relation avoids a
    // large transitive auxiliary program while retaining the exact real-world
    // handoff produced by Cminor.
    #[local] relation cminor_copy_destination_conflict(RTLReg);
    cminor_copy_destination_conflict(*destination) <--
        active_cminor_stmt(_, ?CminorStmt::Sassign(destination, CminorExpr::Evar(left))),
        active_cminor_stmt(_, ?CminorStmt::Sassign(other, CminorExpr::Evar(right))),
        if destination == other && left != right;
    cminor_copy_destination_conflict(*destination) <--
        active_cminor_stmt(_, ?CminorStmt::Sassign(destination, CminorExpr::Evar(_))),
        active_cminor_stmt(_, ?CminorStmt::Sassign(other, expression)),
        if destination == other,
        if !matches!(expression, CminorExpr::Evar(_));
    cminor_copy_destination_conflict(*destination) <--
        active_cminor_stmt(_, ?CminorStmt::Sassign(destination, CminorExpr::Evar(_))),
        active_cminor_stmt(_, ?CminorStmt::Scall(Some(other), _, _, _)),
        if destination == other;
    cminor_copy_destination_conflict(*destination) <--
        active_cminor_stmt(_, ?CminorStmt::Sassign(destination, CminorExpr::Evar(_))),
        active_cminor_stmt(_, ?CminorStmt::Sbuiltin(Some(other), _, _, _)),
        if destination == other;

    external_stack_object_selected_local_candidate(
        *func, *base, *owner, extent, *name, *pos
    ) <--
        active_cminor_stmt(call, ?CminorStmt::Scall(_, _, Either::Right(Either::Right(name)), call_args)),
        known_func_param_pointee_size(name, pos, bytes),
        if let Some(argument) = call_args.get(*pos),
        active_cminor_stmt(select, ?CminorStmt::Sassign(selected, CminorExpr::Eop(Operation::Osel(_, typ), select_args))),
        if selected == argument,
        abi_pointer_size(pointer_width),
        if crate::decompile::passes::rtl_pass::typ_is_pointer_width(typ, *pointer_width),
        for (arm_position, address) in select_args.iter().enumerate(),
        if arm_position < 2,
        active_cminor_stmt(lea, ?CminorStmt::Sassign(address_value, CminorExpr::Econst(Constant::Oaddrstack(base)))),
        if address_value == address,
        instr_in_function(call, func),
        instr_in_function(select, func),
        instr_in_function(lea, func),
        stack_var(func, lea, base, owner),
        csh_local_frame_size(func, frame_size),
        if let Ok(extent) = i64::try_from(*bytes),
        if extent > 0 && extent <= (1 << 20),
        if let Some(end) = base.checked_add(extent),
        if *base >= 0 && end <= *frame_size;

    external_stack_object_selected_local_candidate(
        *func, *base, *owner, extent, *name, *pos
    ) <--
        active_cminor_stmt(call, ?CminorStmt::Scall(_, _, Either::Right(Either::Right(name)), call_args)),
        known_func_param_pointee_size(name, pos, bytes),
        if let Some(argument) = call_args.get(*pos),
        active_cminor_stmt(copy, ?CminorStmt::Sassign(copied, CminorExpr::Evar(copy_source))),
        if copied == argument,
        !cminor_copy_destination_conflict(copied),
        active_cminor_stmt(select, ?CminorStmt::Sassign(selected, CminorExpr::Eop(Operation::Osel(_, typ), select_args))),
        if copy_source == selected,
        abi_pointer_size(pointer_width),
        if crate::decompile::passes::rtl_pass::typ_is_pointer_width(typ, *pointer_width),
        for (arm_position, address) in select_args.iter().enumerate(),
        if arm_position < 2,
        active_cminor_stmt(lea, ?CminorStmt::Sassign(address_value, CminorExpr::Econst(Constant::Oaddrstack(base)))),
        if address_value == address,
        instr_in_function(call, func),
        instr_in_function(copy, func),
        instr_in_function(select, func),
        instr_in_function(lea, func),
        stack_var(func, lea, base, owner),
        csh_local_frame_size(func, frame_size),
        if let Ok(extent) = i64::try_from(*bytes),
        if extent > 0 && extent <= (1 << 20),
        if let Some(end) = base.checked_add(extent),
        if *base >= 0 && end <= *frame_size;

    external_stack_object_local_candidate(func, base, owner, extent, name, pos) <--
        external_stack_object_selected_local_candidate(func, base, owner, extent, name, pos);

    #[local] relation external_stack_object_adjacent_peer(Address, i64, RTLReg, i64, Symbol, usize);
    external_stack_object_adjacent_peer(
        *func, *base, *owner, *extent, *name, *pos
    ) <--
        external_stack_object_local_candidate(func, base, owner, extent, name, pos),
        external_stack_object_local_candidate(func, peer_base, peer_owner, peer_extent, peer_name, peer_pos),
        if owner != peer_owner && extent == peer_extent && name == peer_name && pos == peer_pos,
        if base.checked_add(*extent) == Some(*peer_base)
            || peer_base.checked_add(*peer_extent) == Some(*base);

    #[local] relation external_stack_object_local_conflict(Address, i64, RTLReg, i64);
    external_stack_object_local_conflict(*func, *base, *owner, *extent) <--
        external_stack_object_local_candidate(func, base, owner, extent, _, _),
        stack_var(func, _, other_offset, owner),
        if let Some(end) = base.checked_add(*extent),
        if *other_offset < *base || *other_offset >= end;

    external_stack_object_local_conflict(*func, *base, *owner, *extent) <--
        external_stack_object_local_candidate(func, base, owner, extent, _, _),
        escaped_stack_region_field(func, base, field_offset, chunk),
        let width = crate::decompile::analysis::struct_recovery_pass::chunk_byte_size(chunk) as i64,
        if *field_offset < 0 || field_offset.checked_add(width).is_none_or(|end| end > *extent);

    external_stack_object_local_conflict(*func, *base, *owner, *extent) <--
        external_stack_object_local_candidate(func, base, owner, extent, _, _),
        escaped_stack_region_caller_field(func, base, field_offset, chunk),
        let width = crate::decompile::analysis::struct_recovery_pass::chunk_byte_size(chunk) as i64,
        if *field_offset < 0 || field_offset.checked_add(width).is_none_or(|end| end > *extent);

    external_stack_object_local(func, base, owner, extent),
    external_stack_object_extent(func, base, extent) <--
        external_stack_object_adjacent_peer(func, base, owner, extent, _, _),
        !external_stack_object_local_conflict(func, base, owner, extent);

    external_stack_object_local(func, base, owner, extent),
    external_stack_object_extent(func, base, extent) <--
        external_stack_object_selected_local_candidate(func, base, owner, extent, _, _),
        !external_stack_object_local_conflict(func, base, owner, extent);

    // A call whose callee never returns gets no cminor_succ edge, so its dead tail drops: an always-noreturn symbol, or an error-family symbol with a nonzero constant status arg.
    relation call_node_noreturn(Node);
    call_node_noreturn(*node) <--
        active_cminor_stmt(node, ?CminorStmt::Scall(_, _, Either::Right(Either::Right(name)), _)),
        if crate::abi::is_always_noreturn(name);
    // (2) error-family: join arg 0's register to a single-definition nonzero int constant.
    call_node_noreturn(*node) <--
        active_cminor_stmt(node, ?CminorStmt::Scall(_, _, Either::Right(Either::Right(name)), args)),
        if crate::abi::is_status_noreturn_callee(name),
        single_def_const(status_reg, cst),
        if args.first() == Some(status_reg),
        if matches!(cst, Constant::Ointconst(n) | Constant::Olongconst(n) if *n != 0);
    // (3) user-defined noreturn wrapper called by direct address (die/usage/...).
    call_node_noreturn(*node) <--
        active_cminor_stmt(node, ?CminorStmt::Scall(_, _, Either::Right(Either::Left(addr)), _)),
        function_noreturn(addr);
    // (4) user-defined noreturn wrapper called by symbol that resolves to its entry.
    call_node_noreturn(*node) <--
        active_cminor_stmt(node, ?CminorStmt::Scall(_, _, Either::Right(Either::Right(name)), _)),
        symbol_resolved_addr(name, addr),
        function_noreturn(addr);

    stmt_can_fallthrough(node) <--
        active_cminor_stmt(node, stmt),
        !call_node_noreturn(node),
        if !matches!(stmt,
            CminorStmt::Sjump(_) |
            CminorStmt::Sbranch(_, _, _, _) |
            CminorStmt::Sifthenelse(_, _, _, _) |
            CminorStmt::Sreturn(_) |
            CminorStmt::Stailcall(_, _, _) |
            CminorStmt::Sjumptable(_, _));

    // Walk `next` chain to first cminor node (transitive closure)
    #[local] relation next_to_cminor(Node, Node);
    next_to_cminor(a, b) <-- next(a, b), active_cminor_stmt(b, _);
    next_to_cminor(a, c) <-- next(a, b), !active_cminor_stmt(b, _), next_to_cminor(b, c);

    // Canonical control target used by both emitted Csharp statements and
    // loop metadata.  Branch opcodes and other trimmed instructions can sit
    // at a raw target; following the explicit instruction-next chain keeps
    // the statement CFG and every downstream structural fact in the same
    // node space.  The last rule preserves a genuinely unresolved target so
    // generation remains total instead of silently deleting the branch.
    #[local] relation control_target(Node);
    control_target(*target) <-- active_cminor_stmt(_, ?CminorStmt::Sjump(target));
    control_target(*ifso) <-- active_cminor_stmt(_, ?CminorStmt::Sbranch(_, _, ifso, _));
    control_target(*ifnot) <-- active_cminor_stmt(_, ?CminorStmt::Sbranch(_, _, _, ifnot));
    control_target(*ifso) <-- active_cminor_stmt(_, ?CminorStmt::Sifthenelse(_, _, ifso, _));
    control_target(*ifnot) <-- active_cminor_stmt(_, ?CminorStmt::Sifthenelse(_, _, _, ifnot));

    #[local] relation resolved_control_target(Node, Node);
    resolved_control_target(*target, *target) <--
        control_target(target),
        active_cminor_stmt(target, _);
    resolved_control_target(*target, resolved) <--
        control_target(target),
        !active_cminor_stmt(target, _),
        next_to_cminor(target, resolved);
    resolved_control_target(*target, *target) <--
        control_target(target),
        !active_cminor_stmt(target, _),
        !next_to_cminor(target, _);

    // Jump-table metadata names raw instruction targets, which may have been
    // eliminated before Cminor. Preserve each case index while following the
    // explicit instruction-next chain to its first live statement.
    #[local] relation resolved_jumptable_target(Node, usize, Node);
    resolved_jumptable_target(*node, idx, *target) <--
        active_cminor_stmt(node, ?CminorStmt::Sjumptable(_, targets)),
        for (idx, target) in targets.iter().enumerate(),
        active_cminor_stmt(target, _);
    resolved_jumptable_target(*node, idx, resolved) <--
        active_cminor_stmt(node, ?CminorStmt::Sjumptable(_, targets)),
        for (idx, target) in targets.iter().enumerate(),
        !active_cminor_stmt(target, _),
        next_to_cminor(*target, resolved);

    #[local] relation resolved_jumptable_targets(Node, Arc<Vec<Node>>);
    resolved_jumptable_targets(node, resolved) <--
        active_cminor_stmt(node, ?CminorStmt::Sjumptable(_, _)),
        agg resolved = collect_dense_node_targets(idx, target) in resolved_jumptable_target(node, idx, target);

    // Natural fallthrough via `next` chain
    cminor_fallthrough(node, next_cminor) <--
        active_cminor_stmt(node, _),
        stmt_can_fallthrough(node),
        next_to_cminor(node, next_cminor);

    csh_next(node, next_node) <--
        stmt_can_fallthrough(node),
        cminor_fallthrough(node, next_node);

    // Direct branch targets (target IS a cminor node)
    cminor_succ(*node, *target) <-- active_cminor_stmt(node, ?CminorStmt::Sjump(target)), active_cminor_stmt(target, _);
    cminor_succ(*node, *ifso) <-- active_cminor_stmt(node, ?CminorStmt::Sbranch(_, _, ifso, _)), active_cminor_stmt(ifso, _);
    cminor_succ(*node, *ifnot) <-- active_cminor_stmt(node, ?CminorStmt::Sbranch(_, _, _, ifnot)), active_cminor_stmt(ifnot, _);
    cminor_succ(*node, *ifso) <-- active_cminor_stmt(node, ?CminorStmt::Sifthenelse(_, _, ifso, _)), active_cminor_stmt(ifso, _);
    cminor_succ(*node, *ifnot) <-- active_cminor_stmt(node, ?CminorStmt::Sifthenelse(_, _, _, ifnot)), active_cminor_stmt(ifnot, _);
    cminor_succ(*node, target) <-- active_cminor_stmt(node, ?CminorStmt::Sjumptable(_, targets)), for target in targets.iter(), active_cminor_stmt(target, _);

    // Resolved branch targets (non-cminor target -> nearest cminor via `next`)
    cminor_succ(*node, resolved) <-- active_cminor_stmt(node, ?CminorStmt::Sjump(target)), !active_cminor_stmt(target, _), next_to_cminor(*target, resolved);
    cminor_succ(*node, resolved) <-- active_cminor_stmt(node, ?CminorStmt::Sbranch(_, _, ifso, _)), !active_cminor_stmt(ifso, _), next_to_cminor(*ifso, resolved);
    cminor_succ(*node, resolved) <-- active_cminor_stmt(node, ?CminorStmt::Sbranch(_, _, _, ifnot)), !active_cminor_stmt(ifnot, _), next_to_cminor(*ifnot, resolved);
    cminor_succ(*node, resolved) <-- active_cminor_stmt(node, ?CminorStmt::Sifthenelse(_, _, ifso, _)), !active_cminor_stmt(ifso, _), next_to_cminor(*ifso, resolved);
    cminor_succ(*node, resolved) <-- active_cminor_stmt(node, ?CminorStmt::Sifthenelse(_, _, _, ifnot)), !active_cminor_stmt(ifnot, _), next_to_cminor(*ifnot, resolved);
    cminor_succ(*node, resolved) <-- active_cminor_stmt(node, ?CminorStmt::Sjumptable(_, targets)), for target in targets.iter(), !active_cminor_stmt(target, _), next_to_cminor(*target, resolved);

    // synth_rerouted guards against re-fabricating the rtl_edge_negated-killed fallthrough for synth-carrying nodes (bits 62/63), which would give an unconditional stmt two successors and detach synth stores from their if-arms.
    #[local] relation synth_rerouted(Node);
    synth_rerouted(*node) <--
        rtl_succ(node, dst),
        if (*dst & (3u64 << 62)) != 0,
        active_cminor_stmt(dst, _);
    synth_rerouted(*node) <--
        rtl_optimized_expansion_edge(node, dst),
        active_cminor_stmt(dst, _);

    // Fallthrough suppressed when a synth chain carries the real flow; bridge rules below provide node -> synth -> ... -> next instead.
    cminor_succ(node, next) <--
        csh_next(node, next),
        !synth_rerouted(node),
        active_cminor_stmt(node, _),
        active_cminor_stmt(next, _);

    // Synth-node successor: synthetic nodes lack next entries, so bridge via rtl_succ, which drives the join one tuple per CFG edge; scanning active_cminor_stmt twice was an O(n^2) self-join (36s).
    cminor_succ(*node, *dst) <--
        rtl_succ(node, dst),
        if (*node & (3u64 << 62)) != 0,
        active_cminor_stmt(node, _),
        active_cminor_stmt(dst, _);

    // Synth chain exiting to a trimmed address resolves via `next`, so suppressing the bypass edge above cannot strand the chain.
    cminor_succ(*node, resolved) <--
        rtl_succ(node, dst),
        if (*node & (3u64 << 62)) != 0,
        active_cminor_stmt(node, _),
        !active_cminor_stmt(dst, _),
        next_to_cminor(*dst, resolved);

    // The predecessor of a synth node needs an explicit cminor_succ; `next` skips synth, leaving it unreachable from its real-address predecessor.
    cminor_succ(*node, *dst) <--
        rtl_succ(node, dst),
        if (*dst & (3u64 << 62)) != 0,
        active_cminor_stmt(node, _),
        active_cminor_stmt(dst, _);

    // Arbitrary-length expansions use their explicit semantic edges.  These
    // two rules subsume both entering and traversing the chain without using
    // node-id magnitude as a control-flow predicate.
    cminor_succ(*node, *dst) <--
        rtl_optimized_expansion_edge(node, dst),
        active_cminor_stmt(node, _),
        active_cminor_stmt(dst, _);
    cminor_succ(*node, resolved) <--
        rtl_optimized_expansion_edge(node, dst),
        active_cminor_stmt(node, _),
        !active_cminor_stmt(dst, _),
        next_to_cminor(*dst, resolved);


    // Prefer the optimizer-normalized entry.  The emit_function fallback keeps
    // isolated pass tests and partial pipelines total, but is disabled for a
    // function as soon as the optimizer publishes its authoritative entry.
    #[local] relation semantic_function_entry(Address, Node);
    semantic_function_entry(func, entry) <-- rtl_function_entry(func, entry);
    semantic_function_entry(func, entry) <-- emit_function(func, _, entry), !rtl_function_entry(func, _);

    // A semantic entry may still point at a statement trimmed by jump-table
    // cleanup; follow `next` only in that residual case.  Crucially, an entry
    // removed by RTL nop collapse is already retargeted through rtl_succ, so
    // raw `next` can no longer bypass its synthetic expansion.
    func_entry_node(func, entry) <--
        semantic_function_entry(func, entry),
        active_cminor_stmt(entry, _);

    func_entry_node(func, resolved) <--
        semantic_function_entry(func, entry),
        !active_cminor_stmt(entry, _),
        next_to_cminor(entry, resolved);


    pred(func, to_node, from_node) <--
        cminor_succ(from_node, to_node),
        instr_in_function(from_node, func),
        instr_in_function(to_node, func);


    // Lattice-based dom: intersection of pred dom-sets via Dual<Set<Node>>; replaces the path_avoiding O(V^2) computation (~115 MB on /bin/ls).
    #[local] lattice strict_dom_set(Address, Node, Dual<Set<Node>>);
    lattice dom_set(Address, Node, Dual<Set<Node>>);

    // Cooper-Harvey-Kennedy dom: dom_set(n) = strict_dom_set(n) U {n}; strict_dom_set(n) = intersect dom_set(p) over preds; entry seed = {entry}.

    // Entry case: dom_set = {entry}.
    dom_set(func, entry, Dual(Set::singleton(*entry))) <--
        func_entry_node(func, entry);

    // Non-entry case: strict_dom_set accumulates intersection of preds' dom_sets
    strict_dom_set(func, n, Dual(p_doms_dual.0.clone())) <--
        cminor_succ(p, n),
        instr_in_function(n, func),
        instr_in_function(p, func),
        dom_set(func, p, p_doms_dual),
        !func_entry_node(func, n);

    // dom_set = strict union {n}.
    dom_set(func, n, Dual(dom_set_with_self(&strict_dual.0, *n))) <--
        strict_dom_set(func, n, strict_dual),
        !func_entry_node(func, n);

    // A reachable node's dominators form a chain, and idom(n)'s set is exactly
    // dom(n) without n. Derive the exported tree edge directly from the two
    // point-keyed lattice values instead of materializing an O(V^2) dom relation.
    idom(func, n, *d) <--
        dom_set(func, n, doms_dual),
        for d in doms_dual.0.iter(),
        if d != n,
        dom_set(func, d, parent_doms_dual),
        if doms_dual.0.iter().all(|candidate| candidate == n || parent_doms_dual.0.contains(candidate)),
        if parent_doms_dual.0.iter().all(|candidate| doms_dual.0.contains(candidate));


    relation csharp_stmt_candidate(Node, CsharpminorStmt);

    // Enumerate only immediates that actually participate in a one-register
    // equality comparison whose operand is already known to be a pointer.
    // This is also the provenance that binds `immediate` for the range check
    // below; scanning arbitrary integer constants would conflate ordinary
    // integers with linked image addresses.
    #[local] relation pointer_comparison_immediate(i64);
    pointer_comparison_immediate(immediate) <--
        active_cminor_stmt(_, ?CminorStmt::Sassign(_, expr)),
        if let CminorExpr::Eop(Operation::Ocmp(condition), args) = expr,
        if args.len() == 1,
        let source = args[0],
        must_be_ptr(source),
        if let Some((_, _, immediate)) = symbolic_pointer_comparison(condition);
    pointer_comparison_immediate(immediate) <--
        active_cminor_stmt(_, ?CminorStmt::Sifthenelse(condition, regs, _, _)),
        if regs.len() == 1,
        let source = regs[0],
        must_be_ptr(source),
        if let Some((_, _, immediate)) = symbolic_pointer_comparison(condition);
    pointer_comparison_immediate(immediate) <--
        active_cminor_stmt(_, ?CminorStmt::Sbranch(condition, regs, _, _)),
        if regs.len() == 1,
        let source = regs[0],
        must_be_ptr(source),
        if let Some((_, _, immediate)) = symbolic_pointer_comparison(condition);

    #[local] relation absolute_data_immediate(i64);
    absolute_data_immediate(immediate) <--
        pointer_comparison_immediate(immediate),
        raw_image_addresses_are_absolute(raw_absolute),
        if *raw_absolute,
        if *immediate > 0,
        let address = *immediate as Address,
        data_section_range(start, end),
        if address >= *start && address < *end;

    // Prefer the exact physical owner of an interior coordinate.  The exact
    // synthetic name is only a fallback when no owner relation exists.
    #[local] relation symbolic_data_address_candidate(i64, Ident, i64);
    symbolic_data_address_candidate(immediate, *owner, *offset) <--
        absolute_data_immediate(immediate),
        let interior = *immediate as Ident,
        interior_to_base_ident(interior, owner, offset);
    symbolic_data_address_candidate(immediate, exact, 0) <--
        absolute_data_immediate(immediate),
        let exact = *immediate as Ident,
        base_ident_to_symbol(exact, _),
        !interior_to_base_ident(exact, _, _);

    #[local] relation symbolic_data_address_conflict(i64);
    symbolic_data_address_conflict(immediate) <--
        symbolic_data_address_candidate(immediate, owner_a, offset_a),
        symbolic_data_address_candidate(immediate, owner_b, offset_b),
        if owner_a != owner_b || offset_a != offset_b;

    #[local] relation symbolic_data_address(i64, Ident, i64);
    symbolic_data_address(immediate, owner, offset) <--
        symbolic_data_address_candidate(immediate, owner, offset),
        !symbolic_data_address_conflict(immediate);

    // Cminor's immediate Condition cannot itself carry Oaddrsymbol.  Once the
    // compared value is a hard pointer and the immediate has one exact image
    // owner, replace only that numeric expression with an address expression.
    // The marker suppresses the generic numeric conversion of this same
    // candidate; unrelated supersets at the node remain available.
    #[local] relation symbolic_pointer_assign(Node, CminorExpr, CsharpminorExpr);
    symbolic_pointer_assign(node, expr.clone(), converted) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(_, expr)),
        if let CminorExpr::Eop(Operation::Ocmp(condition), args) = expr,
        if args.len() == 1,
        let source = args[0],
        must_be_ptr(source),
        if let Some((_register_condition, binop, immediate)) = symbolic_pointer_comparison(condition),
        symbolic_data_address(immediate, owner, offset),
        let converted = CsharpminorExpr::Ebinop(
            binop.clone(),
            Box::new(CsharpminorExpr::Evar(source)),
            Box::new(CsharpminorExpr::Econst(Constant::Oaddrsymbol(*owner, *offset))),
        );

    #[local] relation symbolic_pointer_branch(Node, Condition, Args, Condition, Arc<Vec<CsharpminorExpr>>);
    symbolic_pointer_branch(node, condition.clone(), regs.clone(), register_condition, converted_args) <--
        active_cminor_stmt(node, ?CminorStmt::Sifthenelse(condition, regs, _, _)),
        if regs.len() == 1,
        let source = regs[0],
        must_be_ptr(source),
        if let Some((register_condition, _binop, immediate)) = symbolic_pointer_comparison(condition),
        symbolic_data_address(immediate, owner, offset),
        let converted_args = Arc::new(vec![
            CsharpminorExpr::Evar(source),
            CsharpminorExpr::Econst(Constant::Oaddrsymbol(*owner, *offset)),
        ]);

    // A symbolic compare can be the only reference to the target object.  Its
    // owner still needs one file-scope declaration for Oaddrsymbol to name.
    global_var_ref(*owner) <--
        symbolic_pointer_assign(_, _, converted),
        if let CsharpminorExpr::Ebinop(_, _, right) = converted,
        if let CsharpminorExpr::Econst(Constant::Oaddrsymbol(owner, _)) = right.as_ref();
    global_var_ref(*owner) <--
        symbolic_pointer_branch(_, _, _, _, converted_args),
        if let Some(CsharpminorExpr::Econst(Constant::Oaddrsymbol(owner, _))) = converted_args.get(1);
    symbolic_pointer_branch(node, condition.clone(), regs.clone(), register_condition, converted_args) <--
        active_cminor_stmt(node, ?CminorStmt::Sbranch(condition, regs, _, _)),
        if regs.len() == 1,
        let source = regs[0],
        must_be_ptr(source),
        if let Some((register_condition, _binop, immediate)) = symbolic_pointer_comparison(condition),
        symbolic_data_address(immediate, owner, offset),
        let converted_args = Arc::new(vec![
            CsharpminorExpr::Evar(source),
            CsharpminorExpr::Econst(Constant::Oaddrsymbol(*owner, *offset)),
        ]);

    // Track nodes where a stack address was resolved to Eaddrof via stack_var.
    #[local] relation stack_addr_resolved(Node);

    #[local] relation frame_read_has_storage_access_owner(Node);
    frame_read_has_storage_access_owner(*node) <--
        frame_read_storage_access_owner(_, node, _, _, _);

    #[local] relation frame_write_has_storage_owner(Node);
    frame_write_has_storage_owner(*node) <-- frame_write_storage_owner(_, node, _, _, _);

    // Per-function stack offset -> canonical local, so a memory operand materialized only at cminor (a CMP's [rsp+ofs]) resolves to the slot's local instead of a bare *(const).
    #[local] relation stack_local_at(Address, i64, RTLReg);
    stack_local_at(func, ofs, reg) <-- stack_var(func, _, ofs, reg);

    // Resolve Eop(Olea(Ainstack(ofs)), []) -> Eaddrof(var_ident) when stack_var maps the offset.
    csharp_stmt_candidate(node, stmt), stack_addr_resolved(node) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, CminorExpr::Eop(op, args))),
        if let Operation::Olea(Addressing::Ainstack(ofs)) = op,
        if args.is_empty(),
        instr_in_function(node, func_start),
        stack_var(func_start, node, *ofs, stack_rtl),
        let var_ident = ident_from_reg(*stack_rtl),
        let stmt = CsharpminorStmt::Sset(*dst, CsharpminorExpr::Eaddrof(var_ident));

    // Resolve Eop(Oleal(Ainstack(ofs)), []) -> Eaddrof(var_ident) when stack_var maps the offset.
    csharp_stmt_candidate(node, stmt), stack_addr_resolved(node) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, CminorExpr::Eop(op, args))),
        if let Operation::Oleal(Addressing::Ainstack(ofs)) = op,
        if args.is_empty(),
        instr_in_function(node, func_start),
        stack_var(func_start, node, *ofs, stack_rtl),
        let var_ident = ident_from_reg(*stack_rtl),
        let stmt = CsharpminorStmt::Sset(*dst, CsharpminorExpr::Eaddrof(var_ident));

    // Resolve Econst(Oaddrstack(ofs)) -> Eaddrof(var_ident) when stack_var maps the offset. This handles the case where cminor_pass already converted Olea(Ainstack) to Oaddrstack.
    csharp_stmt_candidate(node, stmt), stack_addr_resolved(node) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, CminorExpr::Econst(Constant::Oaddrstack(ofs)))),
        instr_in_function(node, func_start),
        stack_var(func_start, node, *ofs, stack_rtl),
        let var_ident = ident_from_reg(*stack_rtl),
        let stmt = CsharpminorStmt::Sset(*dst, CsharpminorExpr::Eaddrof(var_ident));

    csharp_stmt_candidate(node, stmt), stack_addr_resolved(node) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, CminorExpr::Eop(op, args))),
        if let Operation::Olea(Addressing::Ainstack(ofs)) = op,
        if args.is_empty(),
        instr_in_function(node, func_start),
        !stack_var(func_start, node, *ofs, _),
        canonical_stack_slot_local(func_start, *ofs, stack_rtl),
        let var_ident = ident_from_reg(*stack_rtl),
        let stmt = CsharpminorStmt::Sset(*dst, CsharpminorExpr::Eaddrof(var_ident));

    csharp_stmt_candidate(node, stmt), stack_addr_resolved(node) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, CminorExpr::Eop(op, args))),
        if let Operation::Oleal(Addressing::Ainstack(ofs)) = op,
        if args.is_empty(),
        instr_in_function(node, func_start),
        !stack_var(func_start, node, *ofs, _),
        canonical_stack_slot_local(func_start, *ofs, stack_rtl),
        let var_ident = ident_from_reg(*stack_rtl),
        let stmt = CsharpminorStmt::Sset(*dst, CsharpminorExpr::Eaddrof(var_ident));

    // A later LEA of the same physical slot can lack a point-local stack_var
    // even though another modeled access already names the physical storage.
    // Multiple SSA locals at one byte offset are lifetime variants of that one
    // frame cell; the finalized pre-pass uses the same deterministic minimum
    // owner policy as slot_escaped_canonical.
    csharp_stmt_candidate(node, stmt), stack_addr_resolved(node) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, CminorExpr::Econst(Constant::Oaddrstack(ofs)))),
        instr_in_function(node, func_start),
        !stack_var(func_start, node, *ofs, _),
        canonical_stack_slot_local(func_start, *ofs, stack_rtl),
        let var_ident = ident_from_reg(*stack_rtl),
        let stmt = CsharpminorStmt::Sset(*dst, CsharpminorExpr::Eaddrof(var_ident));

    // A narrow read can start inside a wider scalar/object, or at its base with
    // a smaller width.  Use RTL's structural owner handoff and retain the byte
    // delta from that object.  Without this rule the generic Ainstack
    // conversion either treats the displacement as an absolute integer or
    // widens the read to the owner's scalar value.
    csharp_stmt_candidate(node, stmt), stack_addr_resolved(node) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, CminorExpr::Eload(chunk, addr, args))),
        if let Addressing::Ainstack(ofs) = addr,
        if args.is_empty(),
        instr_in_function(node, func_start),
        frame_read_storage_access_owner(func_start, node, *ofs, base_ofs, owner_rtl),
        if let Some(delta) = ofs.checked_sub(*base_ofs),
        let owner_ident = ident_from_reg(*owner_rtl),
        let addr_expr = if delta == 0 {
            CsharpminorExpr::Eaddrof(owner_ident)
        } else {
            CsharpminorExpr::Ebinop(
                CminorBinop::Oaddl,
                Box::new(CsharpminorExpr::Eaddrof(owner_ident)),
                Box::new(CsharpminorExpr::Econst(Constant::Olongconst(delta))),
            )
        },
        let stmt = CsharpminorStmt::Sset(
            *dst,
            CsharpminorExpr::Eload(*chunk, Box::new(addr_expr)),
        );

    // A fixed external out-parameter is one physical byte region.  Resolve
    // every contained load through its base owner before copy propagation can
    // replace distinct load temporaries with the same scalar local.  Select
    // the nearest containing exact base when ABI objects overlap.
    #[local] relation exact_external_frame_read_candidate(
        Address, Node, i64, i64, i64, RTLReg, MemoryChunk
    );
    exact_external_frame_read_candidate(
        *func_start, *node, *ofs, *base_ofs, *extent, *owner_rtl, *chunk
    ) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(_, CminorExpr::Eload(chunk, addr, args))),
        if let Addressing::Ainstack(ofs) = addr,
        if args.is_empty(),
        instr_in_function(node, func_start),
        external_stack_object_local(func_start, base_ofs, owner_rtl, extent),
        if *extent > 0,
        let width = crate::decompile::analysis::struct_recovery_pass::chunk_byte_size(chunk) as i64,
        if width > 0,
        if let Some(read_end) = ofs.checked_add(width),
        if let Some(region_end) = base_ofs.checked_add(*extent),
        if *ofs >= *base_ofs && read_end <= region_end;

    #[local] relation exact_external_frame_read_shadowed(Address, Node, i64);
    exact_external_frame_read_shadowed(func, node, base) <--
        exact_external_frame_read_candidate(func, node, _, base, _, _, _),
        exact_external_frame_read_candidate(func, node, _, closer, _, _, _),
        if closer > base;

    csharp_stmt_candidate(node, stmt), stack_addr_resolved(node) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, CminorExpr::Eload(chunk, addr, args))),
        if let Addressing::Ainstack(ofs) = addr,
        if args.is_empty(),
        exact_external_frame_read_candidate(func_start, node, ofs, base_ofs, _, owner_rtl, chunk),
        !exact_external_frame_read_shadowed(func_start, node, base_ofs),
        if let Some(delta) = ofs.checked_sub(*base_ofs),
        let owner_ident = ident_from_reg(*owner_rtl),
        let addr_expr = if delta == 0 {
            CsharpminorExpr::Eaddrof(owner_ident)
        } else {
            CsharpminorExpr::Ebinop(
                CminorBinop::Oaddl,
                Box::new(CsharpminorExpr::Eaddrof(owner_ident)),
                Box::new(CsharpminorExpr::Econst(Constant::Olongconst(delta))),
            )
        },
        let stmt = CsharpminorStmt::Sset(
            *dst,
            CsharpminorExpr::Eload(*chunk, Box::new(addr_expr)),
        );

    // Resolve an untracked stack Eload to the function's local for that offset; an address-escaped
    // slot uses rtl_pass's single slot_escaped_canonical, not the multi-valued fallback.  That slot
    // is memory a callee may have written, so it is read through its address, the way Csharpminor
    // reads every stack-allocated variable.  Reading it as Evar(owner) holds only while the owner
    // stays a scalar of this width, and Clight may back it wider (an opaque escaped buffer sized
    // to its frame gap, an ABI out-parameter object): Evar then names the array, which decays to
    // its address, and `strip(base)` received `&base`.
    csharp_stmt_candidate(node, stmt), stack_addr_resolved(node) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, CminorExpr::Eload(chunk, addr, args))),
        if let Addressing::Ainstack(ofs) = addr,
        if args.is_empty(),
        instr_in_function(node, func_start),
        slot_escaped_canonical(func_start, *ofs, stack_rtl),
        !frame_read_has_storage_access_owner(node),
        let stmt = CsharpminorStmt::Sset(
            *dst,
            CsharpminorExpr::Eload(
                *chunk,
                Box::new(CsharpminorExpr::Eaddrof(ident_from_reg(*stack_rtl))),
            ),
        );

    csharp_stmt_candidate(node, stmt), stack_addr_resolved(node) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, CminorExpr::Eload(_chunk, addr, args))),
        if let Addressing::Ainstack(ofs) = addr,
        if args.is_empty(),
        instr_in_function(node, func_start),
        !slot_escaped_canonical(func_start, *ofs, _),
        !frame_read_has_storage_access_owner(node),
        stack_local_at(func_start, *ofs, stack_rtl),
        let stmt = CsharpminorStmt::Sset(*dst, CsharpminorExpr::Evar(*stack_rtl));

    // Upper half of a wide XMM/YMM spill: bind an untracked base+8 offset to the base slot's local, gated on no def at ofs with a tracked local 8 bytes below.
    csharp_stmt_candidate(node, stmt), stack_addr_resolved(node) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, CminorExpr::Eload(_chunk, addr, args))),
        if let Addressing::Ainstack(ofs) = addr,
        if args.is_empty(),
        instr_in_function(node, func_start),
        !slot_escaped_canonical(func_start, *ofs, _),
        !frame_read_has_storage_access_owner(node),
        !stack_local_at(func_start, *ofs, _),
        stack_local_at(func_start, *ofs - 8, stack_rtl),
        let stmt = CsharpminorStmt::Sset(*dst, CsharpminorExpr::Evar(*stack_rtl));

    // RTL expands `op reg,[sp+ofs]` into an Inop at the real node and one
    // synthetic Iop whose second value operand is the canonical stack slot.
    // If that slot later becomes an escaped byte-array owner, treating the
    // operand as Evar(owner) changes an integer load into the owner's address.
    // Recover the machine load here, after every ownership/extent relation has
    // settled.  Every field which could change the rewrite participates in the
    // claim; any disagreement vetoes the transformation.
    #[local] relation post_rtl_arith_load_claim(Node, PostRtlArithLoadClaim);
    post_rtl_arith_load_claim(synthetic, claim) <--
        arith_load_op(real, operation, chunk, base_mreg, raw_displacement, destination_mreg),
        if *base_mreg == Mreg::SP,
        instr_in_function(real, function),
        reg_rtl(real, *destination_mreg, result),
        frame_stack_read_bytes(function, real, read_offset, read_width),
        if *read_width == crate::decompile::analysis::struct_recovery_pass::chunk_byte_size(chunk),
        escaped_stack_region_extent(function, base_offset, extent),
        slot_escaped_region_canonical(function, base_offset, owner),
        if let Ok(read_width_i64) = i64::try_from(*read_width),
        if *extent > read_width_i64,
        if let Some(read_end) = read_offset.checked_add(read_width_i64),
        if let Some(region_end) = base_offset.checked_add(*extent),
        if *read_offset >= *base_offset && read_end <= region_end,
        csharp_address_is_64bit(address_is_64bit),
        let synthetic = *real | ARITH_LOAD_SYNTH_NODE_BIT,
        let claim = PostRtlArithLoadClaim {
            function: *function,
            real_node: *real,
            operation: operation.clone(),
            chunk: *chunk,
            raw_displacement: *raw_displacement,
            destination_mreg: *destination_mreg,
            result: *result,
            read_offset: *read_offset,
            read_width: *read_width,
            base_offset: *base_offset,
            owner: *owner,
            extent: *extent,
            address_is_64bit: *address_is_64bit,
        };

    #[local] relation post_rtl_arith_load_claim_conflict(Node);
    post_rtl_arith_load_claim_conflict(*node) <--
        post_rtl_arith_load_claim(node, left),
        post_rtl_arith_load_claim(node, right),
        if left != right;

    #[local] relation post_rtl_arith_load_rewrite_candidate(Node, CsharpminorStmt);
    post_rtl_arith_load_rewrite_candidate(*node, stmt) <--
        post_rtl_arith_load_claim(node, claim),
        !post_rtl_arith_load_claim_conflict(node),
        rtl_inst(node, ?RTLInst::Iop(seen_operation, args, result)),
        if seen_operation == &claim.operation,
        if args.as_slice() == [claim.result, claim.owner] && *result == claim.result,
        active_cminor_stmt(node, ?CminorStmt::Sassign(destination, expr)),
        if let Some(stmt) = post_rtl_arith_load_stmt(*destination, expr, claim);

    #[local] relation post_rtl_arith_load_rewrite_conflict(Node);
    post_rtl_arith_load_rewrite_conflict(*node) <--
        post_rtl_arith_load_rewrite_candidate(node, left),
        post_rtl_arith_load_rewrite_candidate(node, right),
        if left != right;

    #[local] relation post_rtl_arith_load_rewrite(Node, CsharpminorStmt);
    post_rtl_arith_load_rewrite(*node, stmt.clone()) <--
        post_rtl_arith_load_rewrite_candidate(node, stmt),
        !post_rtl_arith_load_rewrite_conflict(node);

    #[local] relation post_rtl_arith_load_rewritten(Node);
    post_rtl_arith_load_rewritten(node) <-- post_rtl_arith_load_rewrite(node, _);

    csharp_stmt_candidate(*node, stmt.clone()) <--
        post_rtl_arith_load_rewrite(node, stmt);

    csharp_stmt_candidate(node, CsharpminorStmt::Sset(*dst, converted.clone())) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        symbolic_pointer_assign(node, expr, converted);

    // Generic Sassign -> Sset conversion (skipped when stack_addr_resolved or
    // an exact symbolic pointer immediate handles this same expression).
    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        !stack_addr_resolved(node),
        !symbolic_pointer_assign(node, expr, _),
        !post_rtl_arith_load_rewritten(node),
        csharp_address_is_64bit(is_64bit),
        if let Some(converted) = csharp_expr_from_cminor_sized(expr, *is_64bit),
        let stmt = CsharpminorStmt::Sset(*dst, converted);

    csharp_stmt_candidate(node, CsharpminorStmt::Snop) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        !stack_addr_resolved(node),
        !symbolic_pointer_assign(node, expr, _),
        !post_rtl_arith_load_rewritten(node),
        csharp_address_is_64bit(is_64bit),
        if csharp_expr_from_cminor_sized(expr, *is_64bit).is_none();

    // Synthetic narrow frame stores use the same physical owner as their
    // paired load.  Resolve the normalized frame coordinate before the generic
    // addressing conversion can turn it into a literal pointer.
    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sstore(chunk, addr, args, src)),
        if let Addressing::Ainstack(ofs) = addr,
        if args.is_empty(),
        instr_in_function(node, func_start),
        frame_write_storage_owner(func_start, node, *ofs, base_ofs, owner_rtl),
        if let Some(delta) = ofs.checked_sub(*base_ofs),
        let owner_ident = ident_from_reg(*owner_rtl),
        let addr_expr = if delta == 0 {
            CsharpminorExpr::Eaddrof(owner_ident)
        } else {
            CsharpminorExpr::Ebinop(
                CminorBinop::Oaddl,
                Box::new(CsharpminorExpr::Eaddrof(owner_ident)),
                Box::new(CsharpminorExpr::Econst(Constant::Olongconst(delta))),
            )
        },
        let stmt = CsharpminorStmt::Sstore(
            *chunk,
            addr_expr,
            CsharpminorExpr::Evar(*src),
        );

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sstore(chunk, addr, args, src)),
        !frame_write_has_storage_owner(node),
        csharp_address_is_64bit(is_64bit),
        if let Some(addr_expr) = addressing_to_csharp_expr_sized(addr, args.as_slice(), *is_64bit),
        let value_expr = CsharpminorExpr::Evar(*src),
        let stmt = CsharpminorStmt::Sstore(chunk.clone(), addr_expr, value_expr);

    csharp_stmt_candidate(node, CsharpminorStmt::Snop) <--
        active_cminor_stmt(node, ?CminorStmt::Sstore(chunk, addr, args, src)),
        !frame_write_has_storage_owner(node),
        csharp_address_is_64bit(is_64bit),
        if addressing_to_csharp_expr_sized(addr, args.as_slice(), *is_64bit).is_none();

    // Default Scall conversion (callee is a plain register reference).
    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Scall(dst, sig, func, args)),
        !call_through_memory_load(node, _, _, _, _),
        let converted_func = match func.clone() {
            Either::Left(reg) => Either::Left(CsharpminorExpr::Evar(reg)),
            Either::Right(id) => Either::Right(id),
        },
        let call_args = args.iter().map(|r| CsharpminorExpr::Evar(*r)).collect(),
        let stmt = CsharpminorStmt::Scall(dst.clone(), sig.clone(), converted_func, call_args);

    // Memory-indirect call: render callee as the load expression `(*(base + disp))` so the function pointer slot is dereferenced explicitly in the C output.
    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Scall(dst, sig, _, args)),
        call_through_memory_load(node, _temp, chunk, addressing, load_args),
        csharp_address_is_64bit(is_64bit),
        if let Some(addr_expr) = addressing_to_csharp_expr_sized(addressing, load_args.as_slice(), *is_64bit),
        let converted_func = Either::Left(CsharpminorExpr::Eload(*chunk, Box::new(addr_expr))),
        let call_args = args.iter().map(|r| CsharpminorExpr::Evar(*r)).collect(),
        let stmt = CsharpminorStmt::Scall(dst.clone(), sig.clone(), converted_func, call_args);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Stailcall(sig, func, args)),
        !call_through_memory_load(node, _, _, _, _),
        let converted_func = match func.clone() {
            Either::Left(reg) => Either::Left(CsharpminorExpr::Evar(reg)),
            Either::Right(id) => Either::Right(id),
        },
        let call_args = args.iter().map(|r| CsharpminorExpr::Evar(*r)).collect(),
        let stmt = CsharpminorStmt::Stailcall(sig.clone(), converted_func, call_args);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Stailcall(sig, _, args)),
        call_through_memory_load(node, _temp, chunk, addressing, load_args),
        csharp_address_is_64bit(is_64bit),
        if let Some(addr_expr) = addressing_to_csharp_expr_sized(addressing, load_args.as_slice(), *is_64bit),
        let converted_func = Either::Left(CsharpminorExpr::Eload(*chunk, Box::new(addr_expr))),
        let call_args = args.iter().map(|r| CsharpminorExpr::Evar(*r)).collect(),
        let stmt = CsharpminorStmt::Stailcall(sig.clone(), converted_func, call_args);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sbuiltin(dst, name, args, res)),
        let converted_args = args.iter().map(csharp_builtin_arg_from).collect(),
        let converted_res = csharp_builtin_arg_from(&res),
        let stmt = CsharpminorStmt::Sbuiltin(dst.clone(), name.clone(), converted_args, converted_res);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sbranch(cond, regs, ifso, ifnot)),
        !symbolic_pointer_branch(node, cond, regs, _, _),
        resolved_control_target(ifso, live_ifso),
        resolved_control_target(ifnot, live_ifnot),
        let converted_args = regs
            .iter()
            .map(|r| CsharpminorExpr::Evar(*r))
            .collect::<Vec<CsharpminorExpr>>(),
        let stmt = CsharpminorStmt::Scond(cond.clone(), converted_args, *live_ifso, *live_ifnot);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sbranch(cond, regs, ifso, ifnot)),
        symbolic_pointer_branch(node, cond, regs, register_condition, converted_args),
        resolved_control_target(ifso, live_ifso),
        resolved_control_target(ifnot, live_ifnot),
        let stmt = CsharpminorStmt::Scond(register_condition.clone(), converted_args.as_ref().clone(), *live_ifso, *live_ifnot);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sifthenelse(cond, regs, ifso, ifnot)),
        !symbolic_pointer_branch(node, cond, regs, _, _),
        resolved_control_target(ifso, live_ifso),
        resolved_control_target(ifnot, live_ifnot),
        let converted_args = regs.iter().map(|r| CsharpminorExpr::Evar(*r)).collect(),
        let stmt = CsharpminorStmt::Scond(cond.clone(), converted_args, *live_ifso, *live_ifnot);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sifthenelse(cond, regs, ifso, ifnot)),
        symbolic_pointer_branch(node, cond, regs, register_condition, converted_args),
        resolved_control_target(ifso, live_ifso),
        resolved_control_target(ifnot, live_ifnot),
        let stmt = CsharpminorStmt::Scond(register_condition.clone(), converted_args.as_ref().clone(), *live_ifso, *live_ifnot);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sjumptable(reg, _)),
        resolved_jumptable_targets(node, targets),
        let stmt = CsharpminorStmt::Sjumptable(CsharpminorExpr::Evar(*reg), targets.clone());

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sreturn(result)),
        let converted = CsharpminorExpr::Evar(*result),
        let stmt = CsharpminorStmt::Sreturn(converted);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Snop),
        let stmt = CsharpminorStmt::Snop;

    // Drop unreachable bare Sjumps: the structurer reads such an orphan goto as a loop back-edge, making the loop span everything between its label and the dead jump.
    relation cminor_node_has_pred(Node);
    cminor_node_has_pred(*n) <-- cminor_succ(_, n);

    csharp_stmt_candidate(node, CsharpminorStmt::Sjump(*live_target)) <--
        active_cminor_stmt(node, ?CminorStmt::Sjump(target)),
        resolved_control_target(target, live_target),
        cminor_node_has_pred(node);



    relation func_exit_node(Address, Node);

    func_exit_node(func, node) <--
        csharp_stmt_candidate(node, ?CsharpminorStmt::Sreturn(_)),
        instr_in_function(node, func);

    func_exit_node(func, node) <--
        csharp_stmt_candidate(node, ?CsharpminorStmt::Stailcall(_, _, _)),
        instr_in_function(node, func);


    relation loop_back_edge(Address, Node, Node);
    relation loop_head(Address, Node);

    loop_back_edge(func, latch, header) <--
        cminor_succ(latch, header),
        instr_in_function(latch, func),
        dom_set(func, latch, latch_doms),
        if latch_doms.0.contains(header);

    loop_head(func, header) <--
        loop_back_edge(func, _, header);


    // The natural loop body (reverse-from-latch, dominance-filtered), kept as a STABLE seed the abort-region rule reads without feeding back, so folding cannot cascade.
    relation loop_body_core(Address, Node, Node);

    loop_body_core(func, header, header) <--
        loop_back_edge(func, _, header);

    loop_body_core(func, header, latch) <--
        loop_back_edge(func, latch, header);

    loop_body_core(func, header, p) <--
        loop_body_core(func, header, node),
        pred(func, node, p),
        dom_set(func, p, p_doms),
        if p_doms.0.contains(header),
        if *p != *header;

    // n reaches a function return along the CFG; this is what separates a loop's normal exit continuation from an in-loop abort arm that only hits a noreturn sink.
    relation reaches_return(Node);
    reaches_return(n) <-- func_exit_node(_, n);
    reaches_return(p) <-- cminor_succ(p, n), reaches_return(n);

    // Require at least one exit that reaches a return, or a wholly-noreturn function would fold its post-loop tail into an inner loop.
    relation loop_has_returning_exit(Address, Node);
    loop_has_returning_exit(func, header) <--
        loop_body_core(func, header, b),
        cminor_succ(b, t),
        !loop_body_core(func, header, t),
        reaches_return(t);

    // Candidate in-loop noreturn abort region: entered from the body via an
    // exit edge whose target never reaches a return, then grown forward inside
    // the header's dominance region.  This is one unary membership set per
    // loop, rather than a reachability relation keyed by every entry.
    #[local] relation loop_abort_candidate(Address, Node, Node);
    loop_abort_candidate(func, header, t) <--
        loop_has_returning_exit(func, header),
        loop_body_core(func, header, b),
        cminor_succ(b, t),
        !loop_body_core(func, header, t),
        !reaches_return(t),
        dom_set(func, t, t_doms),
        if t_doms.0.contains(header);
    loop_abort_candidate(func, header, n) <--
        loop_abort_candidate(func, header, m),
        cminor_succ(m, n),
        !loop_body_core(func, header, n),
        !reaches_return(n),
        dom_set(func, n, n_doms),
        if n_doms.0.contains(header);

    // Raw CFG predecessors are intentional here: a predecessor attributed to
    // another function or fragment is still a side entry and must prevent the
    // shared landing pad from being moved into this loop.
    #[local] relation loop_abort_external_entry(Address, Node, Node);
    loop_abort_external_entry(func, header, n) <--
        loop_abort_candidate(func, header, n),
        cminor_succ(p, n),
        !loop_body_core(func, header, p),
        !loop_abort_candidate(func, header, p);

    // First carry outside-entry taint forward so a merge reached by a clean
    // sibling is visible.  Then walk backward from every tainted node to all
    // candidate ancestors that can feed it, and forward once more from those
    // ancestors.  The result taints every candidate descendant of those
    // ancestors
    // without pairing every entry with every reachable node; disconnected
    // loop-owned components remain valid.
    #[local] relation loop_abort_external_taint(Address, Node, Node);
    loop_abort_external_taint(func, header, n) <--
        loop_abort_external_entry(func, header, n);
    loop_abort_external_taint(func, header, n) <--
        loop_abort_external_taint(func, header, p),
        cminor_succ(p, n),
        loop_abort_candidate(func, header, n);

    #[local] relation loop_abort_unsafe_ancestor(Address, Node, Node);
    loop_abort_unsafe_ancestor(func, header, n) <--
        loop_abort_external_taint(func, header, n);
    loop_abort_unsafe_ancestor(func, header, p) <--
        loop_abort_unsafe_ancestor(func, header, n),
        cminor_succ(p, n),
        loop_abort_candidate(func, header, p);

    #[local] relation loop_abort_unsafe_region(Address, Node, Node);
    loop_abort_unsafe_region(func, header, n) <--
        loop_abort_unsafe_ancestor(func, header, n);
    loop_abort_unsafe_region(func, header, n) <--
        loop_abort_unsafe_region(func, header, p),
        cminor_succ(p, n),
        loop_abort_candidate(func, header, n);

    relation loop_abort_region(Address, Node, Node);
    loop_abort_region(func, header, n) <--
        loop_abort_candidate(func, header, n),
        !loop_abort_unsafe_region(func, header, n);

    relation loop_body(Address, Node, Node);
    loop_body(func, header, n) <--
        loop_body_core(func, header, n);
    loop_body(func, header, n) <--
        loop_abort_region(func, header, n);

    // CF-2/O-6 (removed 2026-06-10): SCC-body-extension was provably empty for recognized loops, and headerless-SCC creation regressed goto_per_func by 11%; reviving it needs emission costs cut first.


    relation loop_nesting_via_idom(Address, Node, Node);
    relation directly_nested_dom(Address, Node, Node);
    relation intermediate_loop_dom(Address, Node, Node);
    relation immediate_loop_parent(Address, Node, Node);

    loop_nesting_via_idom(func, outer, inner) <--
        loop_head(func, outer),
        loop_head(func, inner),
        dom_set(func, inner, inner_doms),
        if inner_doms.0.contains(outer),
        loop_body(func, outer, inner),
        if *outer != *inner;

    directly_nested_dom(func, outer, inner) <--
        loop_nesting_via_idom(func, outer, inner),
        !intermediate_loop_dom(func, outer, inner);

    intermediate_loop_dom(func, outer, inner) <--
        loop_nesting_via_idom(func, outer, mid),
        loop_nesting_via_idom(func, mid, inner);

    immediate_loop_parent(func, inner, outer) <--
        directly_nested_dom(func, outer, inner);


    relation innermost_loop(Address, Node, Node);
    relation node_in_nested_inner_loop(Address, Node, Node);

    innermost_loop(func, node, header) <--
        loop_body(func, header, node),
        !node_in_nested_inner_loop(func, header, node);

    node_in_nested_inner_loop(func, outer, node) <--
        directly_nested_dom(func, outer, inner),
        loop_body(func, inner, node),
        if *node != *inner;


    relation loop_exit_edge(Address, Node, Node, Node);
    relation loop_exit_branch(Address, Node, Node, Condition, Arc<Vec<CsharpminorExpr>>, Node, Node, bool);
    relation loop_jumptable_exit(Address, Node, Node, Node);
    relation loop_exit_count(Address, Node, usize);
    relation loop_has_exit(Address, Node);
    relation exit_at_header(Address, Node);
    relation exit_at_latch(Address, Node, Node);

    loop_exit_edge(func, header, from_node, to_node) <--
        loop_body(func, header, from_node),
        cminor_succ(from_node, to_node),
        !loop_body(func, header, to_node);

    // Substitute dst->src for a loop-exit comparison reading a copy that is eliminated downstream, using the copy at the branch's unique predecessor where v == src provably holds.
    relation cond_other_pred(Node, Node);
    cond_other_pred(n, p) <--
        cminor_succ(p, n),
        cminor_succ(p2, n),
        if p2 != p;

    relation cond_read_copy(Node, RTLReg, RTLReg);
    cond_read_copy(*branch_node, *v, *w) <--
        csharp_stmt_candidate(branch_node, ?CsharpminorStmt::Scond(_, _, _, _)),
        cminor_succ(pred, branch_node),
        !cond_other_pred(branch_node, pred),
        csharp_stmt_candidate(pred, ?CsharpminorStmt::Sset(v, src_expr)),
        if let CsharpminorExpr::Evar(w) = src_expr;

    loop_exit_branch(func, header, branch_node, cond.clone(), Arc::new(args.clone()), *ifso, *ifnot, false) <--
        loop_body(func, header, branch_node),
        csharp_stmt_candidate(branch_node, ?CsharpminorStmt::Scond(cond, args, ifso, ifnot)),
        !loop_body(func, header, *ifso),
        loop_body(func, header, *ifnot),
        !cond_read_copy(branch_node, _, _);

    loop_exit_branch(func, header, branch_node, cond.clone(), Arc::new(cond_subst_exprs(args, *v, *w)), *ifso, *ifnot, false) <--
        loop_body(func, header, branch_node),
        csharp_stmt_candidate(branch_node, ?CsharpminorStmt::Scond(cond, args, ifso, ifnot)),
        !loop_body(func, header, *ifso),
        loop_body(func, header, *ifnot),
        cond_read_copy(branch_node, v, w);

    loop_exit_branch(func, header, branch_node, cond.clone(), Arc::new(args.clone()), *ifnot, *ifso, true) <--
        loop_body(func, header, branch_node),
        csharp_stmt_candidate(branch_node, ?CsharpminorStmt::Scond(cond, args, ifso, ifnot)),
        loop_body(func, header, *ifso),
        !loop_body(func, header, *ifnot),
        !cond_read_copy(branch_node, _, _);

    loop_exit_branch(func, header, branch_node, cond.clone(), Arc::new(cond_subst_exprs(args, *v, *w)), *ifnot, *ifso, true) <--
        loop_body(func, header, branch_node),
        csharp_stmt_candidate(branch_node, ?CsharpminorStmt::Scond(cond, args, ifso, ifnot)),
        loop_body(func, header, *ifso),
        !loop_body(func, header, *ifnot),
        cond_read_copy(branch_node, v, w);

    loop_jumptable_exit(func, header, branch_node, *target) <--
        loop_body(func, header, branch_node),
        csharp_stmt_candidate(branch_node, ?CsharpminorStmt::Sjumptable(_, targets)),
        for target in targets.iter(),
        !loop_body(func, header, *target);

    relation loop_unconditional_exit(Address, Node, Node);

    loop_unconditional_exit(func, header, node) <--
        loop_exit_edge(func, header, node, _),
        !loop_exit_branch(func, header, node, _, _, _, _, _),
        !loop_jumptable_exit(func, header, node, _);

    loop_exit_count(func, header, count) <--
        loop_head(func, header),
        agg count = ascent::aggregators::count() in loop_exit_branch(func, header, _, _, _, _, _, _);

    loop_has_exit(func, header) <--
        loop_exit_count(func, header, count),
        if *count > 0;

    loop_has_exit(func, header) <--
        loop_jumptable_exit(func, header, _, _);

    loop_has_exit(func, header) <--
        loop_exit_edge(func, header, _, _);

    exit_at_header(func, header) <--
        loop_exit_branch(func, header, node, _, _, _, _, _),
        if *node == *header;

    exit_at_header(func, header) <--
        loop_unconditional_exit(func, header, node),
        if *node == *header;

    exit_at_latch(func, header, latch) <--
        loop_back_edge(func, latch, header),
        loop_exit_branch(func, header, latch, _, _, _, _, _),
        if *latch != *header;

    exit_at_latch(func, header, latch) <--
        loop_back_edge(func, latch, header),
        loop_unconditional_exit(func, header, latch),
        if *latch != *header;


    relation loop_type(Address, Node, LoopType);
    relation primary_exit_node(Address, Node, Node);

    loop_type(func, header, LoopType::Infinite) <--
        loop_head(func, header),
        !loop_has_exit(func, header);

    loop_type(func, header, LoopType::PreTested) <--
        loop_head(func, header),
        exit_at_header(func, header);

    loop_type(func, header, LoopType::PostTested) <--
        loop_head(func, header),
        exit_at_latch(func, header, _),
        !exit_at_header(func, header);

    loop_type(func, header, LoopType::MidTested) <--
        loop_head(func, header),
        loop_has_exit(func, header),
        !exit_at_header(func, header),
        !exit_at_latch(func, header, _);

    primary_exit_node(func, header, header) <--
        loop_type(func, header, LoopType::PreTested);

    primary_exit_node(func, header, latch) <--
        loop_type(func, header, LoopType::PostTested),
        exit_at_latch(func, header, latch);

    primary_exit_node(func, header, exit_node) <--
        loop_type(func, header, LoopType::MidTested),
        loop_exit_count(func, header, 1),
        loop_exit_branch(func, header, exit_node, _, _, _, _, _);


    relation loop_self_modify(Address, Node, Node, RTLReg);
    relation loop_increment(Address, Node, Node, RTLReg);
    relation exit_condition_uses_reg(Address, Node, RTLReg);
    relation induction_var(Address, Node, RTLReg);
    relation has_induction_var(Address, Node);

    loop_self_modify(func, header, node, dst) <--
        loop_body(func, header, node),
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        if crate::decompile::passes::clight_pass::extract_self_modifying_reg(dst, expr).is_some();

    loop_increment(func, header, node, dst) <--
        loop_body(func, header, node),
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        if let CminorExpr::Ebinop(op, arg1, arg2) = expr,
        if crate::decompile::passes::clight_pass::is_increment_decrement_op(op),
        if *arg1 == *dst || *arg2 == *dst;

    exit_condition_uses_reg(func, header, reg) <--
        primary_exit_node(func, header, exit_node),
        loop_exit_branch(func, header, exit_node, _, args, _, _, _),
        let vars = crate::decompile::passes::clight_pass::extract_vars_from_csharp_exprs(args.as_slice()),
        for reg in vars;

    induction_var(func, header, reg) <--
        loop_self_modify(func, header, _, reg),
        exit_condition_uses_reg(func, header, reg);

    induction_var(func, header, reg) <--
        loop_increment(func, header, _, reg),
        exit_condition_uses_reg(func, header, reg);

    has_induction_var(func, header) <--
        induction_var(func, header, _);


    relation body_stmt(Address, Node, Node);
    relation body_stmt_count(Address, Node, usize);
    relation has_substantial_body(Address, Node);
    relation step_node(Address, Node, Node, RTLReg);
    relation valid_loop(Address, Node);

    body_stmt(func, header, node) <--
        loop_body(func, header, node),
        active_cminor_stmt(node, stmt),
        if !crate::decompile::passes::clight_pass::is_trivial_cminor_stmt(stmt),
        if *node != *header;

    body_stmt_count(func, header, count) <--
        loop_head(func, header),
        agg count = ascent::aggregators::count() in body_stmt(func, header, _);

    has_substantial_body(func, header) <--
        body_stmt_count(func, header, count),
        if *count >= 1;

    step_node(func, header, step, ind_var) <--
        induction_var(func, header, ind_var),
        loop_increment(func, header, step, ind_var);

    valid_loop(func, header) <--
        has_induction_var(func, header),
        loop_has_exit(func, header);

    valid_loop(func, header) <--
        has_substantial_body(func, header),
        loop_has_exit(func, header);

    valid_loop(func, header) <--
        loop_type(func, header, LoopType::Infinite),
        has_substantial_body(func, header);

    valid_loop(func, header) <--
        loop_back_edge(func, _, header),
        body_stmt_count(func, header, count),
        if *count >= 1,
        loop_has_exit(func, header);


    relation emit_loop_body(Address, Node, Node);
    relation emit_loop_exit(Address, Node, Node, Condition, Arc<Vec<CsharpminorExpr>>, Node, Node);
    relation trim_step(Address, Node, Node);
    // A non-primary loop exit flowing to a function return rather than post-loop code: a valueless break would drop the returned value, so select tail-duplicates value_node and the return into it.
    relation loop_exit_to_return(Address, Node, Node, Node, Node);
    // node flows to a function return (ret_node) through zero or more pure jump nodes (no intervening assignment, branch, or side effect), so a value-set-then-`jmp epilogue` exit is recognized as a return even with the jump on its own node between them.
    relation returns_after(Address, Node, Node);
    // Any loop exit flowing to a function return, with the per-loop count: a genuine early-return defect needs >=2, while a single return exit must keep its exit as the loop condition.
    relation loop_return_exit_any(Address, Node, Node);
    relation loop_return_exit_count(Address, Node, usize);
    relation node_owned_by_loop(Address, Node, Node);

    emit_loop_body(func, header, body_node) <--
        valid_loop(func, header),
        loop_body(func, header, body_node);

    emit_loop_exit(func, header, branch_node, cond.clone(), args.clone(), *exit_target, *continue_target) <--
        valid_loop(func, header),
        loop_exit_branch(func, header, branch_node, cond, args, exit_target, continue_target, _);

    trim_step(func, header, step) <--
        step_node(func, header, step, _);

    returns_after(func, node, node) <--
        func_exit_node(func, node);

    returns_after(func, node, ret_node) <--
        returns_after(func, succ, ret_node),
        cminor_succ(node, succ),
        active_cminor_stmt(node, ?CminorStmt::Sjump(_)),
        instr_in_function(node, func);

    loop_return_exit_any(func, header, exit_node) <--
        loop_exit_branch(func, header, exit_node, _, _, exit_target, _, _),
        active_cminor_stmt(exit_target, ?CminorStmt::Sassign(_, _)),
        cminor_succ(exit_target, succ),
        returns_after(func, succ, _);

    loop_return_exit_any(func, header, exit_node) <--
        loop_exit_branch(func, header, exit_node, _, _, exit_target, _, _),
        func_exit_node(func, exit_target);

    loop_return_exit_count(func, header, c) <--
        loop_head(func, header),
        agg c = ascent::aggregators::count() in loop_return_exit_any(func, header, _);

    // A non-primary return-exit tail-duplicates its return unconditionally, since a valueless break would fall through to whatever the layout places after the loop and drop the value.
    loop_exit_to_return(func, header, exit_node, exit_target, ret_node) <--
        loop_exit_branch(func, header, exit_node, _, _, exit_target, _, _),
        !emit_function_void_candidate(func),
        !primary_exit_node(func, header, exit_node),
        !loop_body(func, header, exit_target),
        active_cminor_stmt(exit_target, ?CminorStmt::Sassign(_, _)),
        cminor_succ(exit_target, succ),
        returns_after(func, succ, ret_node),
        pred(func, exit_target, exit_node);

    // 0-hop: the exit target is itself the function return (value computed inline at the exit).
    loop_exit_to_return(func, header, exit_node, exit_target, exit_target) <--
        loop_exit_branch(func, header, exit_node, _, _, exit_target, _, _),
        !emit_function_void_candidate(func),
        !primary_exit_node(func, header, exit_node),
        !loop_body(func, header, exit_target),
        func_exit_node(func, exit_target),
        pred(func, exit_target, exit_node);

    // The primary return-exit tail-duplicates only when a second distinct return-exit exists; as the sole return-exit it stays the loop condition.
    loop_exit_to_return(func, header, exit_node, exit_target, ret_node) <--
        loop_exit_branch(func, header, exit_node, _, _, exit_target, _, _),
        !emit_function_void_candidate(func),
        primary_exit_node(func, header, exit_node),
        !loop_body(func, header, exit_target),
        active_cminor_stmt(exit_target, ?CminorStmt::Sassign(_, _)),
        cminor_succ(exit_target, succ),
        returns_after(func, succ, ret_node),
        pred(func, exit_target, exit_node),
        loop_return_exit_count(func, header, c),
        if *c >= 2;

    loop_exit_to_return(func, header, exit_node, exit_target, exit_target) <--
        loop_exit_branch(func, header, exit_node, _, _, exit_target, _, _),
        !emit_function_void_candidate(func),
        primary_exit_node(func, header, exit_node),
        !loop_body(func, header, exit_target),
        func_exit_node(func, exit_target),
        pred(func, exit_target, exit_node),
        loop_return_exit_count(func, header, c),
        if *c >= 2;

    node_owned_by_loop(func, node, header) <--
        innermost_loop(func, node, header),
        valid_loop(func, header),
        !loop_head(func, node);

    node_owned_by_loop(func, node, parent) <--
        loop_head(func, node),
        valid_loop(func, node),
        immediate_loop_parent(func, node, parent);


    relation ternary_true_assignment(Address, Node, RTLReg, CsharpminorExpr, Node);
    relation ternary_false_assignment(Address, Node, RTLReg, CsharpminorExpr, Node);
    relation valid_ternary(Address, Node, RTLReg, CsharpminorExpr, CsharpminorExpr, Node);

    ternary_true_assignment(func, branch, var, expr.clone(), merge) <--
        csharp_stmt_candidate(branch, ?CsharpminorStmt::Scond(_, _, ifso, _)),
        instr_in_function(branch, func),
        csharp_stmt_candidate(ifso, ?CsharpminorStmt::Sset(var, expr)),
        cminor_succ(ifso, merge);

    ternary_false_assignment(func, branch, var, expr.clone(), merge) <--
        csharp_stmt_candidate(branch, ?CsharpminorStmt::Scond(_, _, _, ifnot)),
        instr_in_function(branch, func),
        csharp_stmt_candidate(ifnot, ?CsharpminorStmt::Sset(var, expr)),
        cminor_succ(ifnot, merge);

    valid_ternary(func, branch, var, true_expr.clone(), false_expr.clone(), merge) <--
        ternary_true_assignment(func, branch, var, true_expr, merge),
        ternary_false_assignment(func, branch, var, false_expr, merge),
        !valid_loop(func, branch),
        !node_owned_by_loop(func, branch, _);

}

pub struct CshminorPass;

impl CshminorPass {
    fn prepare_internal_struct_stack_objects(db: &mut DecompileDB) {
        const MAX_OBJECT_BYTES: usize = 1 << 20;

        let mut struct_sizes: HashMap<usize, HashSet<usize>> = HashMap::new();
        for &(struct_id, _, bytes) in db.rel_iter::<(usize, usize, usize)>("emit_struct_def") {
            if bytes > 0 && bytes <= MAX_OBJECT_BYTES {
                struct_sizes.entry(struct_id).or_default().insert(bytes);
            }
        }
        let exact_struct_sizes: HashMap<usize, usize> = struct_sizes
            .into_iter()
            .filter_map(|(struct_id, sizes)| {
                (sizes.len() == 1).then(|| (struct_id, *sizes.iter().next().unwrap()))
            })
            .collect();

        let mut param_sizes: HashMap<(Address, usize), HashSet<usize>> = HashMap::new();
        for &(callee, position, struct_id) in
            db.rel_iter::<(Address, usize, usize)>("func_param_struct_type_candidate")
        {
            if let Some(&bytes) = exact_struct_sizes.get(&struct_id) {
                param_sizes
                    .entry((callee, position))
                    .or_default()
                    .insert(bytes);
            }
        }
        let exact_param_sizes: HashMap<(Address, usize), usize> = param_sizes
            .into_iter()
            .filter_map(|(key, sizes)| {
                (sizes.len() == 1).then(|| (key, *sizes.iter().next().unwrap()))
            })
            .collect();
        let mut stack_addresses: HashMap<RTLReg, Vec<(Node, i64)>> = HashMap::new();
        let mut calls: Vec<(Node, Address, Args)> = Vec::new();
        for (node, statement) in db.rel_iter::<(Node, CminorStmt)>("cminor_stmt") {
            match statement {
                CminorStmt::Sassign(
                    destination,
                    CminorExpr::Econst(Constant::Oaddrstack(base)),
                ) => {
                    stack_addresses
                        .entry(*destination)
                        .or_default()
                        .push((*node, *base));
                }
                CminorStmt::Scall(_, _, Either::Right(Either::Left(callee)), arguments) => {
                    calls.push((*node, *callee, arguments.clone()))
                }
                _ => {}
            }
        }

        let mut node_functions: HashMap<Node, HashSet<Address>> = HashMap::new();
        for &(node, function) in db.rel_iter::<(Node, Address)>("instr_in_function") {
            node_functions.entry(node).or_default().insert(function);
        }
        let stack_vars: Vec<(Address, Node, i64, RTLReg)> = db
            .rel_iter::<(Address, Node, i64, RTLReg)>("stack_var")
            .copied()
            .collect();
        let mut frame_sizes: HashMap<Address, HashSet<i64>> = HashMap::new();
        for &(function, _, _, bytes) in
            db.rel_iter::<(Address, Address, Symbol, u64)>("func_stacksz")
        {
            if let Ok(bytes) = i64::try_from(bytes) {
                if bytes > 0 {
                    frame_sizes.entry(function).or_default().insert(bytes);
                }
            }
        }
        let exact_frame_sizes: HashMap<Address, i64> = frame_sizes
            .into_iter()
            .filter_map(|(function, sizes)| {
                (sizes.len() == 1).then(|| (function, *sizes.iter().next().unwrap()))
            })
            .collect();

        let mut candidates: HashMap<(Address, i64), HashSet<(RTLReg, i64)>> = HashMap::new();
        for (call, callee, arguments) in calls {
            let Some(call_functions) = node_functions.get(&call) else {
                continue;
            };
            for (&(candidate_callee, position), &bytes) in &exact_param_sizes {
                if candidate_callee != callee {
                    continue;
                }
                let Some(argument) = arguments.get(position) else {
                    continue;
                };
                let Some(addresses) = stack_addresses.get(argument) else {
                    continue;
                };
                let Ok(extent) = i64::try_from(bytes) else {
                    continue;
                };
                for &(lea, base) in addresses {
                    let Some(lea_functions) = node_functions.get(&lea) else {
                        continue;
                    };
                    for &function in call_functions.intersection(lea_functions) {
                        let Some(&frame_size) = exact_frame_sizes.get(&function) else {
                            continue;
                        };
                        let Some(end) = base.checked_add(extent) else {
                            continue;
                        };
                        if base < 0 || end > frame_size {
                            continue;
                        }
                        let owners: HashSet<RTLReg> = stack_vars
                            .iter()
                            .filter_map(|&(owner_func, owner_node, offset, owner)| {
                                (owner_func == function && owner_node == lea && offset == base)
                                    .then_some(owner)
                            })
                            .collect();
                        if owners.len() != 1 {
                            continue;
                        }
                        candidates
                            .entry((function, base))
                            .or_default()
                            .insert((*owners.iter().next().unwrap(), extent));
                    }
                }
            }
        }

        // Some post-RTL contracts prove a complete physical region without a
        // source-level struct classification: an initialized span, an
        // endpoint-bounded pointer walk. Fixed external ABI objects already
        // have a direct Cminor ownership path; re-projecting all of them here
        // shrinks conservative alias regions and changes unrelated lifetimes.
        // Materialize only those independently inspectable sources after
        // Cminor has established the final stack-address spelling.  The generic
        // escaped_stack_region_extent union also contains field and frame-gap
        // lower bounds, so consuming it here changed lifetime-overlaid locals
        // and regressed behavior.
        let mut projected_region_extents: HashMap<(Address, i64), i64> = HashMap::new();
        for &(function, base, extent) in
            db.rel_iter::<(Address, i64, i64)>("initialized_stack_region_extent")
        {
            if extent <= 0 || extent > MAX_OBJECT_BYTES as i64 {
                continue;
            }
            projected_region_extents
                .entry((function, base))
                .and_modify(|current| *current = (*current).max(extent))
                .or_insert(extent);
        }
        for &(function, low, high) in
            db.rel_iter::<(Address, i64, i64)>("stack_pointer_walk_region")
        {
            let Some(extent) = high.checked_sub(low) else {
                continue;
            };
            if extent <= 0 || extent > MAX_OBJECT_BYTES as i64 {
                continue;
            }
            projected_region_extents
                .entry((function, low))
                .and_modify(|current| *current = (*current).max(extent))
                .or_insert(extent);
        }

        let mut canonical_base_locals: HashMap<(Address, i64), HashSet<RTLReg>> = HashMap::new();
        for &(function, base, local) in
            db.rel_iter::<(Address, i64, RTLReg)>("canonical_stack_slot_local")
        {
            canonical_base_locals
                .entry((function, base))
                .or_default()
                .insert(local);
        }
        // Focused pass fixtures can invoke this helper without first running
        // prepare_canonical_stack_slot_locals.  Preserve the production rule's
        // fail-closed behavior by accepting the raw stack mapping only when it
        // names one owner at the base.
        let mut raw_base_locals: HashMap<(Address, i64), HashSet<RTLReg>> = HashMap::new();
        for &(function, _, base, local) in &stack_vars {
            raw_base_locals
                .entry((function, base))
                .or_default()
                .insert(local);
        }
        for (key, locals) in raw_base_locals {
            canonical_base_locals.entry(key).or_insert(locals);
        }
        for ((function, base), extent) in projected_region_extents {
            let Some(owners) = canonical_base_locals.get(&(function, base)) else {
                continue;
            };
            if owners.len() != 1 {
                continue;
            }
            let owner = *owners.iter().next().unwrap();
            candidates
                .entry((function, base))
                .or_default()
                .insert((owner, extent));
        }

        let escaped_fields: Vec<(Address, i64, i64, MemoryChunk)> = db
            .rel_iter::<(Address, i64, i64, MemoryChunk)>("escaped_stack_region_field")
            .copied()
            .chain(
                db.rel_iter::<(Address, i64, i64, MemoryChunk)>(
                    "escaped_stack_region_caller_field",
                )
                .copied(),
            )
            .collect();
        let existing_locals: HashSet<(Address, i64, RTLReg, i64)> = db
            .rel_iter::<(Address, i64, RTLReg, i64)>("external_stack_object_local")
            .copied()
            .collect();
        let existing_extents: HashSet<(Address, i64, i64)> = db
            .rel_iter::<(Address, i64, i64)>("external_stack_object_extent")
            .copied()
            .collect();

        let mut rows = Vec::new();
        for ((function, base), layouts) in candidates {
            let owners: HashSet<RTLReg> = layouts.iter().map(|(owner, _)| *owner).collect();
            if owners.len() != 1 {
                continue;
            }
            let owner = *owners.iter().next().unwrap();
            // Every row is a storage lower bound for this same physical owner.
            // The widest one satisfies all observed accesses; choosing a
            // smaller struct candidate would recreate the overflow this bridge
            // is intended to prevent.
            let Some(extent) = layouts.iter().map(|(_, extent)| *extent).max() else {
                continue;
            };
            let Some(end) = base.checked_add(extent) else {
                continue;
            };
            let shared_owner_outside =
                stack_vars
                    .iter()
                    .any(|&(owner_func, _, other_offset, other_owner)| {
                        owner_func == function
                            && other_owner == owner
                            && (other_offset < base || other_offset >= end)
                    });
            let field_outside =
                escaped_fields
                    .iter()
                    .any(|&(field_func, field_base, field_offset, chunk)| {
                        if field_func != function || field_base != base {
                            return false;
                        }
                        let width =
                            crate::decompile::analysis::struct_recovery_pass::chunk_byte_size(
                                &chunk,
                            ) as i64;
                        field_offset < 0
                            || field_offset
                                .checked_add(width)
                                .is_none_or(|field_end| field_end > extent)
                    });
            if !shared_owner_outside && !field_outside {
                rows.push((function, base, owner, extent));
            }
        }
        rows.sort_unstable();
        rows.dedup();
        for (function, base, owner, extent) in rows {
            if !existing_locals.contains(&(function, base, owner, extent)) {
                db.rel_push(
                    "external_stack_object_local",
                    (function, base, owner, extent),
                );
            }
            if !existing_extents.contains(&(function, base, extent)) {
                db.rel_push("external_stack_object_extent", (function, base, extent));
            }
        }
    }

    fn prepare_canonical_stack_slot_locals(db: &mut DecompileDB) {
        let rows = compute_canonical_stack_slot_locals(
            db.rel_iter::<(Address, Address, i64, RTLReg)>("stack_var")
                .copied(),
        );
        let relation = ascent::boxcar::Vec::new();
        for row in rows {
            relation.push(row);
        }
        db.rel_set("canonical_stack_slot_local", relation);
    }

    fn prepare_jump_tables(db: &mut DecompileDB) {
        if db
            .rel_iter::<(Node, usize, Node)>("jump_table_target")
            .next()
            .is_none()
        {
            return;
        }

        let mut tables: HashMap<Node, Vec<(usize, Node)>> = HashMap::new();
        for &(jmp, idx, target) in db.rel_iter::<(Node, usize, Node)>("jump_table_target") {
            tables.entry(jmp).or_default().push((idx, target));
        }
        for targets in tables.values_mut() {
            targets.sort_by_key(|(idx, _)| *idx);
        }

        let mut impls: HashMap<Node, Vec<Node>> = HashMap::new();
        for &(impl_addr, jmp_addr) in db.rel_iter::<(Node, Node)>("jump_table_impl") {
            impls.entry(jmp_addr).or_default().push(impl_addr);
        }

        let rtl_edges: Vec<(Node, Node)> =
            db.rel_iter::<(Node, Node)>("rtl_succ").copied().collect();
        let mut materialized_impl_set = std::collections::HashSet::new();

        // Sort jump-table nodes and pick lowest RTLReg discriminant for determinism.
        let mut jmp_nodes: Vec<Node> = tables.keys().copied().collect();
        jmp_nodes.sort();
        for jmp_node in jmp_nodes {
            // RTL already preserved the actual dispatch use and its reaching
            // index computation. Reconstructing it from an earlier comparison
            // would replace that value with its pre-mask/pre-adjustment input.
            if db.rel_iter::<(Node, CminorStmt)>("cminor_stmt")
                .any(|(node, stmt)| *node == jmp_node && matches!(stmt, CminorStmt::Sjumptable(..)))
            {
                continue;
            }
            let targets = &tables[&jmp_node];
            let impl_nodes = match impls.get(&jmp_node) {
                Some(v) => v,
                None => continue,
            };
            let impl_set_local: std::collections::HashSet<Node> = impl_nodes
                .iter()
                .copied()
                .chain(std::iter::once(jmp_node))
                .collect();
            // RTL optimization can bypass transparent address-calculation
            // nodes, so numeric instruction order does not identify the live
            // entry of a jump-table implementation. Collapse the region only
            // when the CFG has one structural entry from outside it.
            let Some(entry) = unique_external_cfg_entry(&impl_set_local, &rtl_edges) else {
                continue;
            };

            let ordered_targets: Vec<Node> = targets.iter().map(|(_, t)| *t).collect();

            // Pick smallest RTLReg across plausible discriminants for deterministic output.
            let mut candidates: Vec<RTLReg> = Vec::new();
            for (_node, stmt) in db.rel_iter::<(Node, CminorStmt)>("cminor_stmt") {
                match stmt {
                    CminorStmt::Sbranch(_, args, ifso, ifnot)
                    | CminorStmt::Sifthenelse(_, args, ifso, ifnot) => {
                        if (impl_set_local.contains(ifso) || impl_set_local.contains(ifnot))
                            && args.len() == 1
                        {
                            candidates.push(args[0]);
                        }
                    }
                    _ => {}
                }
            }

            if candidates.is_empty() {
                let cmp_addrs: Vec<Node> = db
                    .rel_iter::<(Node, Node)>("jump_table_cmp")
                    .filter(|(j, _)| *j == jmp_node)
                    .map(|(_, a)| *a)
                    .collect();
                let index_regs: Vec<&'static str> = db
                    .rel_iter::<(Node, &'static str)>("jump_table_index_reg")
                    .filter(|(j, _)| *j == jmp_node)
                    .map(|(_, r)| *r)
                    .collect();
                for &cmp_addr in &cmp_addrs {
                    for &idx_name in &index_regs {
                        let mreg = Mreg::x86(idx_name);
                        for &(addr, ref reg, rtl_reg) in
                            db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl")
                        {
                            if addr == cmp_addr && *reg == mreg {
                                candidates.push(rtl_reg);
                            }
                        }
                    }
                }
            }

            candidates.sort();
            candidates.dedup();
            let reg = match candidates.into_iter().next() {
                Some(r) => r,
                None => continue,
            };

            db.rel_push(
                "cminor_stmt",
                (
                    entry,
                    CminorStmt::Sjumptable(reg, Arc::new(ordered_targets)),
                ),
            );
            materialized_impl_set.extend(impl_set_local);
        }

        let mut impl_nodes_sorted: Vec<Node> = materialized_impl_set.into_iter().collect();
        impl_nodes_sorted.sort();
        for node in impl_nodes_sorted {
            db.rel_push("trim_jump_table_impl", (node,));
        }
    }
}

impl IRPass for CshminorPass {
    fn name(&self) -> &'static str {
        "cshminor"
    }

    fn run(&self, db: &mut DecompileDB) {
        Self::prepare_jump_tables(db);
        Self::prepare_canonical_stack_slot_locals(db);
        Self::prepare_internal_struct_stack_objects(db);

        run_pass!(db, CshminorPassProgram);
    }

    fn extra_reads(&self) -> &'static [&'static str] {
        &[
            "jump_table_target",
            "jump_table_impl",
            "jump_table_cmp",
            "jump_table_index_reg",
            "reg_rtl",
            "stack_var",
            "func_param_struct_type_candidate",
            "emit_struct_def",
            "initialized_stack_region_extent",
            "stack_pointer_walk_region",
        ]
    }

    declare_io_from!(CshminorPassProgram);
}

#[cfg(test)]
mod tests {
    use super::{
        compute_canonical_stack_slot_locals, ident_from_reg, unique_external_cfg_entry,
        CshminorPass, CshminorPassProgram,
    };
    use crate::decompile::elevator::DecompileDB;
    use crate::mreg::Mreg;
    use crate::x86::op::{Addressing, Comparison, Condition, Operation};
    use crate::x86::types::{
        CminorBinop, CminorExpr, CminorStmt, Constant, CsharpminorExpr, CsharpminorStmt,
        MemoryChunk, RTLInst, Typ,
    };
    use either::Either;
    use std::collections::HashSet;
    use std::sync::Arc;

    fn synthetic_ids<const N: usize>() -> [u64; N] {
        std::array::from_fn(|index| index as u64 + 1)
    }

    fn on_large_stack(test: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .stack_size(128 * 1024 * 1024)
            .spawn(test)
            .unwrap()
            .join()
            .unwrap();
    }

    fn post_rtl_arith_load_fixture(
        read_offset: i64,
        read_width: usize,
        base_offset: i64,
        extent: i64,
        owner: u64,
    ) -> (CshminorPassProgram, u64, u64, u64) {
        let real = 0x4510;
        let synthetic = real | super::ARITH_LOAD_SYNTH_NODE_BIT;
        let result = 0x9100;
        let mut prog = CshminorPassProgram::default();
        prog.abi_pointer_size.push((8,));
        prog.arith_load_op.push((
            real,
            Operation::Oadd,
            MemoryChunk::MInt32,
            Mreg::SP,
            read_offset,
            Mreg::R8,
        ));
        prog.reg_rtl.push((real, Mreg::R8, result));
        prog.frame_stack_read_bytes
            .push((FUNC, real, read_offset, read_width));
        prog.escaped_stack_region_extent
            .push((FUNC, base_offset, extent));
        prog.slot_escaped_region_canonical
            .push((FUNC, base_offset, owner));
        prog.rtl_inst.push((
            synthetic,
            RTLInst::Iop(Operation::Oadd, Arc::new(vec![result, owner]), result),
        ));
        prog.cminor_stmt.push((
            synthetic,
            CminorStmt::Sassign(result, CminorExpr::Ebinop(CminorBinop::Oadd, result, owner)),
        ));
        for node in [real, synthetic] {
            prog.instr_in_function.push((node, FUNC));
        }
        (prog, real, synthetic, result)
    }

    fn assert_generic_arith_owner_candidate(
        prog: &CshminorPassProgram,
        synthetic: u64,
        result: u64,
        owner: u64,
    ) {
        assert!(!prog
            .post_rtl_arith_load_rewritten
            .iter()
            .any(|(node,)| *node == synthetic));
        let candidates: Vec<_> = prog
            .csharp_stmt_candidate
            .iter()
            .filter_map(|(node, stmt)| (*node == synthetic).then_some(stmt))
            .collect();
        assert_eq!(candidates.len(), 1, "{candidates:?}");
        assert!(matches!(
            candidates[0],
            CsharpminorStmt::Sset(
                destination,
                CsharpminorExpr::Ebinop(CminorBinop::Oadd, lhs, rhs),
            ) if *destination == result
                && matches!(lhs.as_ref(), CsharpminorExpr::Evar(reg) if *reg == result)
                && matches!(rhs.as_ref(), CsharpminorExpr::Evar(reg) if *reg == owner)
        ));
    }

    #[test]
    fn memory_addresses_use_the_target_pointer_width_exclusively() {
        let [load, store, base, index, destination, source] = synthetic_ids();
        let mut lp64 = CshminorPassProgram::default();
        lp64.abi_pointer_size.push((8,));
        lp64.cminor_stmt.push((
            load,
            CminorStmt::Sassign(
                destination,
                CminorExpr::Eload(
                    MemoryChunk::MInt8Unsigned,
                    Addressing::Aindexed2(0),
                    Arc::new(vec![base, index]),
                ),
            ),
        ));
        lp64.cminor_stmt.push((
            store,
            CminorStmt::Sstore(
                MemoryChunk::MInt8Unsigned,
                Addressing::Aindexed2(0),
                Arc::new(vec![base, index]),
                source,
            ),
        ));

        lp64.run();

        let load_candidates: Vec<_> = lp64
            .csharp_stmt_candidate
            .iter()
            .filter(|(node, _)| *node == load)
            .collect();
        assert_eq!(load_candidates.len(), 1, "{load_candidates:?}");
        assert!(matches!(
            &load_candidates[0].1,
            CsharpminorStmt::Sset(
                got_destination,
                CsharpminorExpr::Eload(_, address),
            ) if *got_destination == destination
                && matches!(
                    address.as_ref(),
                    CsharpminorExpr::Ebinop(CminorBinop::Oaddl, left, right)
                        if matches!(left.as_ref(), CsharpminorExpr::Evar(reg) if *reg == base)
                            && matches!(right.as_ref(), CsharpminorExpr::Evar(reg) if *reg == index)
                )
        ));

        let store_candidates: Vec<_> = lp64
            .csharp_stmt_candidate
            .iter()
            .filter(|(node, _)| *node == store)
            .collect();
        assert_eq!(store_candidates.len(), 1, "{store_candidates:?}");
        assert!(matches!(
            &store_candidates[0].1,
            CsharpminorStmt::Sstore(_, CsharpminorExpr::Ebinop(CminorBinop::Oaddl, _, _), value)
                if matches!(value, CsharpminorExpr::Evar(reg) if *reg == source)
        ));

        let mut ilp32 = CshminorPassProgram::default();
        ilp32.abi_pointer_size.push((4,));
        ilp32.cminor_stmt.push((
            load,
            CminorStmt::Sassign(
                destination,
                CminorExpr::Eload(
                    MemoryChunk::MInt8Unsigned,
                    Addressing::Aindexed2(0),
                    Arc::new(vec![base, index]),
                ),
            ),
        ));
        ilp32.run();
        let ilp32_candidates: Vec<_> = ilp32
            .csharp_stmt_candidate
            .iter()
            .filter(|(node, _)| *node == load)
            .collect();
        assert_eq!(ilp32_candidates.len(), 1, "{ilp32_candidates:?}");
        assert!(matches!(
            &ilp32_candidates[0].1,
            CsharpminorStmt::Sset(
                _,
                CsharpminorExpr::Eload(_, address),
            ) if matches!(
                address.as_ref(),
                CsharpminorExpr::Ebinop(CminorBinop::Oadd, _, _)
            )
        ));
    }

    #[test]
    fn later_addrstack_reuses_the_final_canonical_slot_local() {
        let [func, owner_site, use_site, dst, local, other] = synthetic_ids();
        let statement = CminorStmt::Sassign(dst, CminorExpr::Econst(Constant::Oaddrstack(12)));

        let mut unique = CshminorPassProgram::default();
        unique.cminor_stmt.push((use_site, statement.clone()));
        unique.instr_in_function.push((use_site, func));
        unique.stack_var.push((func, owner_site, 12, local));
        let unique_rows = compute_canonical_stack_slot_locals([(func, owner_site, 12, local)]);
        assert_eq!(unique_rows, vec![(func, 12, local)]);
        unique.canonical_stack_slot_local.extend(unique_rows);
        let op_site = use_site + 20;
        let op_dst = dst + 20;
        unique.cminor_stmt.push((
            op_site,
            CminorStmt::Sassign(
                op_dst,
                CminorExpr::Eop(
                    Operation::Oleal(Addressing::Ainstack(12)),
                    Arc::new(Vec::new()),
                ),
            ),
        ));
        unique.instr_in_function.push((op_site, func));
        unique.run();
        assert!(unique.csharp_stmt_candidate.iter().any(|fact| {
            fact == &(
                use_site,
                CsharpminorStmt::Sset(dst, CsharpminorExpr::Eaddrof(ident_from_reg(local))),
            )
        }));
        assert!(unique.csharp_stmt_candidate.iter().any(|fact| {
            fact == &(
                op_site,
                CsharpminorStmt::Sset(op_dst, CsharpminorExpr::Eaddrof(ident_from_reg(local))),
            )
        }));

        let mut conflicting = CshminorPassProgram::default();
        conflicting.cminor_stmt.push((use_site, statement));
        conflicting.instr_in_function.push((use_site, func));
        conflicting.stack_var.extend([
            (func, owner_site, 12, local),
            (func, owner_site + 10, 12, other),
        ]);
        let conflict_rows = compute_canonical_stack_slot_locals([
            (func, owner_site, 12, local),
            (func, owner_site + 10, 12, other),
        ]);
        assert_eq!(conflict_rows, vec![(func, 12, local.min(other))]);
        conflicting.canonical_stack_slot_local.extend(conflict_rows);
        conflicting.run();
        assert!(conflicting
            .csharp_stmt_candidate
            .iter()
            .any(|(node, stmt)| {
                *node == use_site
                    && matches!(
                        stmt,
                        CsharpminorStmt::Sset(reg, CsharpminorExpr::Eaddrof(owner))
                            if *reg == dst && *owner == ident_from_reg(local.min(other))
                    )
            }));
    }

    fn seed_interior_pointer_address(
        prog: &mut CshminorPassProgram,
        pointer_reg: u64,
        owner: u64,
        interior: u64,
        hard_pointer: bool,
        raw_absolute: bool,
    ) {
        prog.raw_image_addresses_are_absolute.push((raw_absolute,));
        prog.data_section_range.push((owner, owner + 0x100));
        prog.base_ident_to_symbol
            .push((owner as usize, "global_words"));
        prog.base_ident_to_symbol
            .push((interior as usize, "SUB_interior"));
        prog.interior_to_base_ident.push((
            interior as usize,
            owner as usize,
            (interior - owner) as i64,
        ));
        if hard_pointer {
            prog.must_be_ptr.push((pointer_reg,));
        }
    }

    #[test]
    fn hard_pointer_equality_uses_the_interior_owners_symbolic_address() {
        let [node, pointer, result] = synthetic_ids();
        let owner = 0x4000;
        let interior = owner + 8;
        let mut prog = CshminorPassProgram::default();
        prog.cminor_stmt.push((
            node,
            CminorStmt::Sassign(
                result,
                CminorExpr::Eop(
                    Operation::Ocmp(Condition::Ccomplimm(Comparison::Ceq, interior as i64)),
                    Arc::new(vec![pointer]),
                ),
            ),
        ));
        seed_interior_pointer_address(&mut prog, pointer, owner, interior, true, true);

        prog.run();

        let candidates: Vec<_> = prog
            .csharp_stmt_candidate
            .iter()
            .filter_map(|(candidate_node, stmt)| (*candidate_node == node).then_some(stmt))
            .collect();
        assert_eq!(candidates.len(), 1);
        assert!(matches!(
            candidates[0],
            CsharpminorStmt::Sset(
                dst,
                CsharpminorExpr::Ebinop(
                    CminorBinop::Ocmpl(Comparison::Ceq),
                    left,
                    right,
                ),
            ) if *dst == result
                && matches!(left.as_ref(), CsharpminorExpr::Evar(reg) if *reg == pointer)
                && matches!(
                    right.as_ref(),
                    CsharpminorExpr::Econst(Constant::Oaddrsymbol(ident, 8))
                        if *ident == owner as usize
                )
        ));
        assert!(prog
            .global_var_ref
            .iter()
            .any(|(ident,)| *ident == owner as usize));
    }

    #[test]
    fn integer_equality_that_matches_an_address_stays_numeric() {
        let [node, integer, result] = synthetic_ids();
        let owner = 0x4000;
        let interior = owner + 8;
        let mut prog = CshminorPassProgram::default();
        prog.cminor_stmt.push((
            node,
            CminorStmt::Sassign(
                result,
                CminorExpr::Eop(
                    Operation::Ocmp(Condition::Ccomplimm(Comparison::Ceq, interior as i64)),
                    Arc::new(vec![integer]),
                ),
            ),
        ));
        seed_interior_pointer_address(&mut prog, integer, owner, interior, false, true);

        prog.run();

        assert!(prog
            .csharp_stmt_candidate
            .iter()
            .any(|(candidate_node, stmt)| {
                *candidate_node == node
                    && matches!(
                        stmt,
                        CsharpminorStmt::Sset(
                            _,
                            CsharpminorExpr::Ebinop(_, _, right),
                        ) if matches!(
                            right.as_ref(),
                            CsharpminorExpr::Econst(Constant::Olongconst(value))
                                if *value == interior as i64
                        )
                    )
            }));
        assert!(!prog.csharp_stmt_candidate.iter().any(|(candidate_node, stmt)| {
            *candidate_node == node
                && matches!(
                    stmt,
                    CsharpminorStmt::Sset(
                        _,
                        CsharpminorExpr::Ebinop(
                            _,
                            _,
                            right,
                        ),
                    ) if matches!(right.as_ref(), CsharpminorExpr::Econst(Constant::Oaddrsymbol(..)))
                )
        }));
        assert!(!prog
            .global_var_ref
            .iter()
            .any(|(ident,)| *ident == owner as usize));
    }

    #[test]
    fn relocatable_image_offset_cannot_masquerade_as_an_absolute_pointer() {
        let [node, pointer, result] = synthetic_ids();
        let owner = 0x4000;
        let interior = owner + 8;
        let mut prog = CshminorPassProgram::default();
        prog.cminor_stmt.push((
            node,
            CminorStmt::Sassign(
                result,
                CminorExpr::Eop(
                    Operation::Ocmp(Condition::Ccomplimm(Comparison::Ceq, interior as i64)),
                    Arc::new(vec![pointer]),
                ),
            ),
        ));
        seed_interior_pointer_address(&mut prog, pointer, owner, interior, true, false);

        prog.run();

        assert!(!prog.csharp_stmt_candidate.iter().any(|(candidate_node, stmt)| {
            *candidate_node == node
                && matches!(
                    stmt,
                    CsharpminorStmt::Sset(
                        _,
                        CsharpminorExpr::Ebinop(_, _, right),
                    ) if matches!(right.as_ref(), CsharpminorExpr::Econst(Constant::Oaddrsymbol(..)))
                )
        }));
        assert!(prog
            .csharp_stmt_candidate
            .iter()
            .any(|(candidate_node, stmt)| {
                *candidate_node == node
                    && matches!(
                        stmt,
                        CsharpminorStmt::Sset(
                            _,
                            CsharpminorExpr::Ebinop(_, _, right),
                        ) if matches!(
                            right.as_ref(),
                            CsharpminorExpr::Econst(Constant::Olongconst(value))
                                if *value == interior as i64
                        )
                    )
            }));
    }

    #[test]
    fn symbolic_pointer_branch_keeps_both_cfg_targets() {
        let [branch, pointer, ifso, ifnot] = synthetic_ids();
        let owner = 0x4000;
        let interior = owner + 8;
        let mut prog = CshminorPassProgram::default();
        prog.cminor_stmt.push((
            branch,
            CminorStmt::Sifthenelse(
                Condition::Ccompluimm(Comparison::Cne, interior as i64),
                Arc::new(vec![pointer]),
                ifso,
                ifnot,
            ),
        ));
        prog.cminor_stmt.push((ifso, CminorStmt::Snop));
        prog.cminor_stmt.push((ifnot, CminorStmt::Snop));
        seed_interior_pointer_address(&mut prog, pointer, owner, interior, true, true);

        prog.run();

        assert!(prog
            .csharp_stmt_candidate
            .iter()
            .any(|(candidate_node, stmt)| {
                *candidate_node == branch
                    && matches!(
                        stmt,
                        CsharpminorStmt::Scond(
                            Condition::Ccomplu(Comparison::Cne),
                            args,
                            live_ifso,
                            live_ifnot,
                        ) if *live_ifso == ifso
                            && *live_ifnot == ifnot
                            && matches!(
                                args.as_slice(),
                                [
                                    CsharpminorExpr::Evar(reg),
                                    CsharpminorExpr::Econst(Constant::Oaddrsymbol(ident, 8)),
                                ] if *reg == pointer && *ident == owner as usize
                            )
                    )
            }));
        assert!(prog
            .global_var_ref
            .iter()
            .any(|(ident,)| *ident == owner as usize));
    }

    const FUNC: u64 = 0x1000;
    const HEADER: u64 = 0x1010;
    const CORE_EXIT: u64 = 0x1020;
    const ABORT_ENTRY: u64 = 0x2000;
    const ABORT_SINK: u64 = 0x2010;
    const OUTSIDE_PRED: u64 = 0x3000;
    const CLEAN_ENTRY: u64 = 0x4000;
    const CLEAN_SINK: u64 = 0x4010;
    const SIBLING_ENTRY: u64 = 0x5000;

    fn abort_candidate() -> CshminorPassProgram {
        let mut prog = CshminorPassProgram::default();
        prog.loop_body_core.push((FUNC, HEADER, CORE_EXIT));
        prog.loop_abort_candidate.push((FUNC, HEADER, ABORT_ENTRY));
        prog.loop_abort_candidate.push((FUNC, HEADER, ABORT_SINK));
        prog.cminor_succ.push((ABORT_ENTRY, ABORT_SINK));
        prog.cminor_succ.push((CORE_EXIT, ABORT_ENTRY));
        prog
    }

    #[test]
    fn jump_table_entry_comes_from_cfg_not_node_order() {
        let implementation_nodes = HashSet::from([0x100, 0x200, 0x300]);
        let edges = vec![(0x50, 0x200), (0x200, 0x300)];

        assert_eq!(
            unique_external_cfg_entry(&implementation_nodes, &edges),
            Some(0x200)
        );

        let ambiguous_edges = vec![(0x50, 0x200), (0x60, 0x100)];
        assert_eq!(
            unique_external_cfg_entry(&implementation_nodes, &ambiguous_edges),
            None
        );
    }

    #[test]
    fn retargeted_expansion_tail_survives_nop_collapse() {
        let tail = 0x900;
        let collapsed = 0x100;
        let live = 0x700;
        let mut prog = CshminorPassProgram::default();
        prog.cminor_stmt
            .extend([(tail, CminorStmt::Snop), (live, CminorStmt::Snop)]);
        prog.rtl_expansion_edge.push((tail, collapsed));
        prog.rtl_succ.push((tail, live));

        prog.run();

        assert!(prog.cminor_succ.iter().any(|fact| fact == &(tail, live)));
        assert!(!prog
            .cminor_succ
            .iter()
            .any(|fact| fact == &(tail, collapsed)));
    }

    #[test]
    fn optimized_entry_does_not_follow_raw_next_around_expansion() {
        let raw_entry = 0x900;
        let expansion_stage = 0x700;
        let live = 0x100;
        let mut prog = CshminorPassProgram::default();

        prog.emit_function
            .push((FUNC, "entry_expansion", raw_entry));
        prog.rtl_function_entry.push((FUNC, expansion_stage));
        prog.cminor_stmt.extend([
            (expansion_stage, CminorStmt::Snop),
            (live, CminorStmt::Sreturn(0)),
        ]);
        prog.rtl_expansion_edge.push((raw_entry, expansion_stage));
        prog.rtl_succ.push((expansion_stage, live));
        // The raw instruction stream skips the synthetic semantic stage.
        prog.next.push((raw_entry, live));

        prog.run();

        assert!(prog
            .func_entry_node
            .iter()
            .any(|fact| fact == &(FUNC, expansion_stage)));
        assert!(!prog
            .func_entry_node
            .iter()
            .any(|fact| fact == &(FUNC, live)));
        assert!(prog
            .cminor_succ
            .iter()
            .any(|fact| fact == &(expansion_stage, live)));
    }

    #[test]
    fn jump_table_cases_resolve_to_live_cminor_targets() {
        const SWITCH: u64 = 0x10;
        const RAW_CASE: u64 = 0x20;
        const LIVE_CASE: u64 = 0x30;
        const DISCRIMINANT: u64 = 7;

        let mut prog = CshminorPassProgram::default();
        prog.cminor_stmt.push((
            SWITCH,
            CminorStmt::Sjumptable(DISCRIMINANT, Arc::new(vec![RAW_CASE])),
        ));
        prog.cminor_stmt.push((LIVE_CASE, CminorStmt::Snop));
        prog.next.push((RAW_CASE, LIVE_CASE));

        prog.run();

        assert!(prog.csharp_stmt_candidate.iter().any(|(node, stmt)| {
            *node == SWITCH
                && matches!(
                    stmt,
                    CsharpminorStmt::Sjumptable(_, targets)
                        if targets.as_slice() == [LIVE_CASE]
                )
        }));
    }

    #[test]
    fn memory_tailcall_inlines_the_function_pointer_load() {
        let [node, target, base, arg] = synthetic_ids();
        let mut prog = CshminorPassProgram::default();
        prog.abi_pointer_size.push((8,));
        prog.cminor_stmt.push((
            node,
            CminorStmt::Stailcall(None, Either::Left(target), Arc::new(vec![arg])),
        ));
        prog.call_through_memory_load.push((
            node,
            target,
            MemoryChunk::MInt64,
            Addressing::Aindexed(24),
            Arc::new(vec![base]),
        ));

        prog.run();

        let candidates: Vec<_> = prog
            .csharp_stmt_candidate
            .iter()
            .filter_map(|(candidate_node, stmt)| (*candidate_node == node).then_some(stmt))
            .collect();
        assert_eq!(candidates.len(), 1);
        assert!(matches!(
            candidates[0],
            CsharpminorStmt::Stailcall(
                _,
                Either::Left(CsharpminorExpr::Eload(MemoryChunk::MInt64, address)),
                args
            ) if matches!(address.as_ref(), CsharpminorExpr::Ebinop(_, _, _))
                && matches!(args.as_slice(), [CsharpminorExpr::Evar(value)] if *value == arg)
        ));
    }

    #[test]
    fn post_rtl_arith_load_rewrites_exact_owner_at_zero_and_nonzero_delta() {
        on_large_stack(|| {
            for (read_offset, base_offset, expected_delta) in [(4_i64, 4_i64, 0_i64), (8, 4, 4)] {
                let owner = 0x9000;
                let (mut prog, _real, synthetic, result) =
                    post_rtl_arith_load_fixture(read_offset, 4, base_offset, 12, owner);
                prog.run();

                assert!(prog
                    .post_rtl_arith_load_rewritten
                    .iter()
                    .any(|(node,)| *node == synthetic));
                let candidates: Vec<_> = prog
                    .csharp_stmt_candidate
                    .iter()
                    .filter_map(|(node, stmt)| (*node == synthetic).then_some(stmt))
                    .collect();
                assert_eq!(candidates.len(), 1, "{candidates:?}");
                assert!(matches!(
                    candidates[0],
                    CsharpminorStmt::Sset(
                        destination,
                        CsharpminorExpr::Ebinop(
                            CminorBinop::Oadd,
                            lhs,
                            loaded,
                        ),
                    ) if *destination == result
                        && matches!(lhs.as_ref(), CsharpminorExpr::Evar(reg) if *reg == result)
                        && matches!(
                            loaded.as_ref(),
                            CsharpminorExpr::Eload(MemoryChunk::MInt32, address)
                                if if expected_delta == 0 {
                                    matches!(
                                        address.as_ref(),
                                        CsharpminorExpr::Eaddrof(ident)
                                            if *ident == ident_from_reg(owner)
                                    )
                                } else {
                                    matches!(
                                        address.as_ref(),
                                        CsharpminorExpr::Ebinop(
                                            CminorBinop::Oaddl,
                                            base,
                                            delta,
                                        ) if matches!(
                                            base.as_ref(),
                                            CsharpminorExpr::Eaddrof(ident)
                                                if *ident == ident_from_reg(owner)
                                        ) && matches!(
                                            delta.as_ref(),
                                            CsharpminorExpr::Econst(Constant::Olongconst(value))
                                                if *value == expected_delta
                                        )
                                    )
                                }
                        )
                ));
            }
        });
    }

    #[test]
    fn post_rtl_arith_load_rejects_scalar_width_mismatch_and_noncontainment() {
        on_large_stack(|| {
            let owner = 0x9000;
            for (read_offset, read_width, base_offset, extent) in [
                // A scalar-sized object keeps the established scalar SSA route.
                (4_i64, 4_usize, 4_i64, 4_i64),
                // The decoder width must agree exactly with the machine chunk.
                (4, 8, 4, 12),
                // A larger extent is insufficient when the read crosses its end.
                (12, 4, 4, 8),
            ] {
                let (mut prog, _real, synthetic, result) = post_rtl_arith_load_fixture(
                    read_offset,
                    read_width,
                    base_offset,
                    extent,
                    owner,
                );
                prog.run();
                assert_generic_arith_owner_candidate(&prog, synthetic, result, owner);
            }
        });
    }

    #[test]
    fn post_rtl_arith_load_rejects_ambiguous_owner_or_operation() {
        on_large_stack(|| {
            let owner = 0x9000;
            let other_owner = 0x9010;

            let (mut owners, _real, synthetic, result) =
                post_rtl_arith_load_fixture(4, 4, 4, 12, owner);
            owners
                .slot_escaped_region_canonical
                .push((FUNC, 4, other_owner));
            owners.run();
            assert!(owners
                .post_rtl_arith_load_claim_conflict
                .iter()
                .any(|(node,)| *node == synthetic));
            assert_generic_arith_owner_candidate(&owners, synthetic, result, owner);

            let (mut operations, real, synthetic, result) =
                post_rtl_arith_load_fixture(4, 4, 4, 12, owner);
            operations.arith_load_op.push((
                real,
                Operation::Osub,
                MemoryChunk::MInt32,
                Mreg::SP,
                4,
                Mreg::R8,
            ));
            operations.run();
            assert!(operations
                .post_rtl_arith_load_claim_conflict
                .iter()
                .any(|(node,)| *node == synthetic));
            assert_generic_arith_owner_candidate(&operations, synthetic, result, owner);
        });
    }

    #[test]
    fn named_cminor_out_param_publishes_exact_local_object() {
        let [lea, call, address, owner, peer_lea, peer_call, peer_address, peer_owner] =
            synthetic_ids();
        let base = 0;
        let peer_base = 144;
        let mut prog = CshminorPassProgram::default();
        for (lea_node, call_node, address_reg, local, offset) in [
            (lea, call, address, owner, base),
            (peer_lea, peer_call, peer_address, peer_owner, peer_base),
        ] {
            prog.cminor_stmt.push((
                lea_node,
                CminorStmt::Sassign(
                    address_reg,
                    CminorExpr::Econst(Constant::Oaddrstack(offset)),
                ),
            ));
            prog.cminor_stmt.push((
                call_node,
                CminorStmt::Scall(
                    None,
                    None,
                    Either::Right(Either::Right("stat")),
                    Arc::new(vec![0xdead, address_reg]),
                ),
            ));
            prog.instr_in_function
                .extend([(lea_node, FUNC), (call_node, FUNC)]);
            prog.stack_var.push((FUNC, lea_node, offset, local));
        }
        prog.func_stacksz.push((FUNC, peer_call + 1, "caller", 360));
        prog.known_func_param_pointee_size.push(("stat", 1, 144));

        prog.run();

        assert!(prog
            .external_stack_object_local
            .iter()
            .any(|fact| fact == &(FUNC, base, owner, 144)));
        assert!(prog
            .external_stack_object_local
            .iter()
            .any(|fact| fact == &(FUNC, peer_base, peer_owner, 144)));
        assert!(prog
            .external_stack_object_extent
            .iter()
            .any(|fact| fact == &(FUNC, base, 144)));
    }

    #[test]
    fn selected_stack_arm_publishes_fixed_external_object() {
        let [lea, select, copy, call, address, selected, copied, owner, incoming, condition] =
            synthetic_ids();
        let base = 32_i64;
        let mut prog = CshminorPassProgram::default();
        prog.abi_pointer_size.push((8,));
        prog.cminor_stmt.extend([
            (
                lea,
                CminorStmt::Sassign(address, CminorExpr::Econst(Constant::Oaddrstack(base))),
            ),
            (
                select,
                CminorStmt::Sassign(
                    selected,
                    CminorExpr::Eop(
                        Operation::Osel(Condition::Ccomplimm(Comparison::Cne, 0), Typ::Tany64),
                        Arc::new(vec![incoming, address, condition]),
                    ),
                ),
            ),
            (
                copy,
                CminorStmt::Sassign(copied, CminorExpr::Evar(selected)),
            ),
            (
                call,
                CminorStmt::Scall(
                    None,
                    None,
                    Either::Right(Either::Right("strtoumax")),
                    Arc::new(vec![incoming, copied, condition]),
                ),
            ),
        ]);
        prog.instr_in_function
            .extend([(lea, FUNC), (select, FUNC), (copy, FUNC), (call, FUNC)]);
        prog.stack_var.push((FUNC, lea, base, owner));
        prog.func_stacksz.push((FUNC, call + 1, "caller", 64));
        prog.known_func_param_pointee_size.push(("strtoumax", 1, 8));

        prog.run();

        assert!(prog
            .external_stack_object_selected_local_candidate
            .iter()
            .any(|fact| fact == &(FUNC, base, owner, 8, "strtoumax", 1)));
        assert!(prog
            .external_stack_object_local
            .iter()
            .any(|fact| fact == &(FUNC, base, owner, 8)));
        assert!(prog
            .external_stack_object_extent
            .iter()
            .any(|fact| fact == &(FUNC, base, 8)));
    }

    #[test]
    fn internal_struct_parameter_sizes_exact_caller_local() {
        let [lea, call, address, owner] = synthetic_ids();
        let callee = 0x9000;
        let struct_id: usize = 0x1234;
        let base = 16_i64;
        let mut db = DecompileDB::default();
        for row in [
            (
                lea,
                CminorStmt::Sassign(address, CminorExpr::Econst(Constant::Oaddrstack(base))),
            ),
            (
                call,
                CminorStmt::Scall(
                    None,
                    None,
                    Either::Right(Either::Left(callee)),
                    Arc::new(vec![address]),
                ),
            ),
        ] {
            db.rel_push("cminor_stmt", row);
        }
        db.rel_push("instr_in_function", (lea, FUNC));
        db.rel_push("instr_in_function", (call, FUNC));
        db.rel_push("stack_var", (FUNC, lea, base, owner));
        db.rel_push("func_stacksz", (FUNC, call + 1, "caller", 64_u64));
        db.rel_push(
            "func_param_struct_type_candidate",
            (callee, 0_usize, struct_id),
        );
        db.rel_push("emit_struct_def", (struct_id, 3_usize, 21_usize));

        CshminorPass::prepare_internal_struct_stack_objects(&mut db);

        assert!(db
            .rel_iter::<(u64, i64, u64, i64)>("external_stack_object_local")
            .any(|fact| fact == &(FUNC, base, owner, 21)));
        assert!(db
            .rel_iter::<(u64, i64, i64)>("external_stack_object_extent")
            .any(|fact| fact == &(FUNC, base, 21)));
    }

    #[test]
    fn post_rtl_internal_field_projection_does_not_claim_whole_object() {
        let [lea, owner] = synthetic_ids();
        let base = 16_i64;
        let mut db = DecompileDB::default();
        db.rel_push("stack_var", (FUNC, lea, base, owner));
        db.rel_push("func_stacksz", (FUNC, lea + 1, "caller", 64_u64));
        // A visible internal access is a useful field lower bound, but does not
        // prove the complete object or the lifetime of overlaid caller slots.
        db.rel_push(
            "escaped_stack_region_field",
            (FUNC, base, 20_i64, MemoryChunk::MAny64),
        );
        db.rel_push("escaped_stack_region_extent", (FUNC, base, 28_i64));

        CshminorPass::prepare_internal_struct_stack_objects(&mut db);

        assert!(!db
            .rel_iter::<(u64, i64, u64, i64)>("external_stack_object_local")
            .any(|fact| fact.0 == FUNC && fact.1 == base));
        assert!(!db
            .rel_iter::<(u64, i64, i64)>("external_stack_object_extent")
            .any(|fact| fact.0 == FUNC && fact.1 == base));
    }

    #[test]
    fn independently_proven_region_sizes_caller_without_enumerated_fields() {
        let [lea, owner] = synthetic_ids();
        let base = 32_i64;
        let mut db = DecompileDB::default();
        db.rel_push("stack_var", (FUNC, lea, base, owner));
        db.rel_push("func_stacksz", (FUNC, lea + 1, "caller", 512_u64));
        db.rel_push("initialized_stack_region_extent", (FUNC, base, 257_i64));

        CshminorPass::prepare_internal_struct_stack_objects(&mut db);

        assert!(db
            .rel_iter::<(u64, i64, u64, i64)>("external_stack_object_local")
            .any(|fact| fact == &(FUNC, base, owner, 257)));
    }

    #[test]
    fn copied_select_argument_rejects_a_noncopy_redefinition() {
        let [copy, redefine, source, destination] = synthetic_ids();
        let mut prog = CshminorPassProgram::default();
        prog.cminor_stmt.extend([
            (
                copy,
                CminorStmt::Sassign(destination, CminorExpr::Evar(source)),
            ),
            (
                redefine,
                CminorStmt::Sassign(destination, CminorExpr::Econst(Constant::Olongconst(0))),
            ),
        ]);

        prog.run();

        assert!(prog
            .cminor_copy_destination_conflict
            .iter()
            .any(|fact| fact.0 == destination));
    }

    #[test]
    fn named_cminor_out_param_rejects_a_wider_shared_local() {
        let [lea, call, address, owner, distant, peer_lea, peer_call, peer_address, peer_owner] =
            synthetic_ids();
        let base = 0;
        let peer_base = 144;
        let mut prog = CshminorPassProgram::default();
        for (lea_node, call_node, address_reg, local, offset) in [
            (lea, call, address, owner, base),
            (peer_lea, peer_call, peer_address, peer_owner, peer_base),
        ] {
            prog.cminor_stmt.push((
                lea_node,
                CminorStmt::Sassign(
                    address_reg,
                    CminorExpr::Econst(Constant::Oaddrstack(offset)),
                ),
            ));
            prog.cminor_stmt.push((
                call_node,
                CminorStmt::Scall(
                    None,
                    None,
                    Either::Right(Either::Right("stat")),
                    Arc::new(vec![0xdead, address_reg]),
                ),
            ));
            prog.instr_in_function
                .extend([(lea_node, FUNC), (call_node, FUNC)]);
            prog.stack_var.push((FUNC, lea_node, offset, local));
        }
        prog.stack_var.extend([(FUNC, distant, base + 1024, owner)]);
        prog.func_stacksz
            .push((FUNC, peer_call + 1, "caller", 2048));
        prog.known_func_param_pointee_size.push(("stat", 1, 144));
        prog.escaped_stack_region_caller_field
            .push((FUNC, base, 1024, MemoryChunk::MAny64));

        prog.run();

        assert!(prog
            .external_stack_object_local_conflict
            .iter()
            .any(|fact| fact == &(FUNC, base, owner, 144)));
        assert!(!prog
            .external_stack_object_local
            .iter()
            .any(|fact| fact.0 == FUNC && fact.2 == owner));
    }

    #[test]
    fn fixed_external_object_reads_preserve_base_relative_byte_offsets() {
        let [base_read, interior_read, base_dst, interior_dst, owner] = synthetic_ids();
        let base = 144;
        let mut prog = CshminorPassProgram::default();
        for (node, offset, destination) in [
            (base_read, base, base_dst),
            (interior_read, base + 8, interior_dst),
        ] {
            prog.cminor_stmt.push((
                node,
                CminorStmt::Sassign(
                    destination,
                    CminorExpr::Eload(
                        MemoryChunk::MInt64,
                        Addressing::Ainstack(offset),
                        Arc::new(vec![]),
                    ),
                ),
            ));
            prog.instr_in_function.push((node, FUNC));
        }
        prog.external_stack_object_local
            .push((FUNC, base, owner, 144));

        prog.run();

        for (node, destination, expected_delta) in [
            (base_read, base_dst, 0_i64),
            (interior_read, interior_dst, 8_i64),
        ] {
            assert!(prog.csharp_stmt_candidate.iter().any(|(candidate, stmt)| {
                *candidate == node
                    && matches!(
                        stmt,
                        CsharpminorStmt::Sset(
                            value,
                            CsharpminorExpr::Eload(MemoryChunk::MInt64, address),
                        ) if *value == destination
                            && if expected_delta == 0 {
                                matches!(
                                    address.as_ref(),
                                    CsharpminorExpr::Eaddrof(ident)
                                        if *ident == ident_from_reg(owner)
                                )
                            } else {
                                matches!(
                                    address.as_ref(),
                                    CsharpminorExpr::Ebinop(
                                        CminorBinop::Oaddl,
                                        base_address,
                                        delta,
                                    ) if matches!(
                                        base_address.as_ref(),
                                        CsharpminorExpr::Eaddrof(ident)
                                            if *ident == ident_from_reg(owner)
                                    ) && matches!(
                                        delta.as_ref(),
                                        CsharpminorExpr::Econst(Constant::Olongconst(value))
                                            if *value == expected_delta
                                    )
                                )
                            }
                    )
            }));
        }
    }

    #[test]
    fn interior_frame_read_uses_its_structural_storage_owner() {
        let [node, dst, owner, stale_exact_local] = synthetic_ids();
        let mut prog = CshminorPassProgram::default();
        prog.cminor_stmt.push((
            node,
            CminorStmt::Sassign(
                dst,
                CminorExpr::Eload(
                    MemoryChunk::MInt8Unsigned,
                    Addressing::Ainstack(5),
                    Arc::new(vec![]),
                ),
            ),
        ));
        prog.instr_in_function.push((node, FUNC));
        prog.stack_var.push((FUNC, node, 5, stale_exact_local));
        prog.frame_read_storage_owner
            .push((FUNC, node, 5, 4, owner));
        prog.frame_read_storage_access_owner
            .push((FUNC, node, 5, 4, owner));

        prog.run();

        assert!(prog.csharp_stmt_candidate.iter().any(|(candidate, stmt)| {
            *candidate == node
                && matches!(
                    stmt,
                    CsharpminorStmt::Sset(
                        value,
                        CsharpminorExpr::Eload(
                            MemoryChunk::MInt8Unsigned,
                            address,
                        ),
                    ) if *value == dst
                        && matches!(
                            address.as_ref(),
                            CsharpminorExpr::Ebinop(
                                CminorBinop::Oaddl,
                                base,
                                offset,
                            ) if matches!(
                                base.as_ref(),
                                CsharpminorExpr::Eaddrof(ident)
                                    if *ident == ident_from_reg(owner)
                            ) && matches!(
                                offset.as_ref(),
                                CsharpminorExpr::Econst(Constant::Olongconst(1))
                            )
                        )
                )
        }));
        assert!(!prog.csharp_stmt_candidate.iter().any(|(candidate, stmt)| {
            *candidate == node
                && matches!(
                    stmt,
                    CsharpminorStmt::Sset(value, CsharpminorExpr::Evar(stale))
                        if *value == dst && *stale == stale_exact_local
                )
        }));
    }

    #[test]
    fn full_width_owned_base_reload_keeps_the_memory_read_operation() {
        let [node, dst, owner] = synthetic_ids();
        let mut prog = CshminorPassProgram::default();
        prog.cminor_stmt.push((node, CminorStmt::Sassign(dst,
            CminorExpr::Eload(MemoryChunk::MAny64, Addressing::Ainstack(8), Arc::new(vec![])))));
        prog.instr_in_function.push((node, FUNC));
        prog.stack_var.push((FUNC, node, 8, owner));
        prog.frame_read_storage_access_owner.push((FUNC, node, 8, 8, owner));
        prog.run();
        let reads: Vec<_> = prog.csharp_stmt_candidate.iter()
            .filter(|(candidate, _)| *candidate == node).collect();
        assert_eq!(reads.len(), 1);
        assert!(matches!(&reads[0].1,
            CsharpminorStmt::Sset(value, CsharpminorExpr::Eload(MemoryChunk::MAny64, address))
                if *value == dst && matches!(address.as_ref(), CsharpminorExpr::Eaddrof(id)
                    if *id == ident_from_reg(owner))));
    }

    #[test]
    fn escaped_slot_read_goes_through_the_owner_address() {
        // A callee may have written the escaped slot, and Clight may back its owner wider than
        // this read, where Evar(owner) would name the array instead of loading the value.
        let [node, dst, owner] = synthetic_ids();
        let mut prog = CshminorPassProgram::default();
        prog.cminor_stmt.push((node, CminorStmt::Sassign(dst,
            CminorExpr::Eload(MemoryChunk::MAny64, Addressing::Ainstack(0), Arc::new(vec![])))));
        prog.instr_in_function.push((node, FUNC));
        prog.slot_escaped_canonical.push((FUNC, 0, owner));
        prog.run();
        let reads: Vec<_> = prog.csharp_stmt_candidate.iter()
            .filter(|(candidate, _)| *candidate == node).collect();
        assert_eq!(reads.len(), 1);
        assert!(matches!(&reads[0].1,
            CsharpminorStmt::Sset(value, CsharpminorExpr::Eload(MemoryChunk::MAny64, address))
                if *value == dst && matches!(address.as_ref(), CsharpminorExpr::Eaddrof(id)
                    if *id == ident_from_reg(owner))));
    }

    #[test]
    fn narrow_frame_load_and_store_keep_their_physical_owner_at_zero_and_nonzero_delta() {
        let [read, store, dst, src, owner] = synthetic_ids();
        let mut prog = CshminorPassProgram::default();
        prog.cminor_stmt.push((
            read,
            CminorStmt::Sassign(
                dst,
                CminorExpr::Eload(
                    MemoryChunk::MInt8Unsigned,
                    Addressing::Ainstack(4),
                    Arc::new(vec![]),
                ),
            ),
        ));
        // Deliberately provide an exact scalar local too: the structural
        // storage access must win because this is a byte read of its base.
        prog.stack_var.push((FUNC, read, 4, owner));
        prog.slot_escaped_canonical.push((FUNC, 4, owner));
        prog.frame_read_storage_access_owner
            .push((FUNC, read, 4, 4, owner));

        prog.cminor_stmt.push((
            store,
            CminorStmt::Sstore(
                MemoryChunk::MInt16Unsigned,
                Addressing::Ainstack(6),
                Arc::new(vec![]),
                src,
            ),
        ));
        prog.frame_write_storage_owner
            .push((FUNC, store, 6, 4, owner));
        for node in [read, store] {
            prog.instr_in_function.push((node, FUNC));
        }

        prog.run();

        let read_candidates: Vec<_> = prog
            .csharp_stmt_candidate
            .iter()
            .filter_map(|(node, stmt)| (*node == read).then_some(stmt))
            .collect();
        assert_eq!(read_candidates.len(), 1);
        assert!(matches!(
            read_candidates[0],
            CsharpminorStmt::Sset(
                value,
                CsharpminorExpr::Eload(MemoryChunk::MInt8Unsigned, address),
            ) if *value == dst
                && matches!(
                    address.as_ref(),
                    CsharpminorExpr::Eaddrof(ident) if *ident == ident_from_reg(owner)
                )
        ));

        let store_candidates: Vec<_> = prog
            .csharp_stmt_candidate
            .iter()
            .filter_map(|(node, stmt)| (*node == store).then_some(stmt))
            .collect();
        assert_eq!(store_candidates.len(), 1);
        assert!(matches!(
            store_candidates[0],
            CsharpminorStmt::Sstore(
                MemoryChunk::MInt16Unsigned,
                CsharpminorExpr::Ebinop(CminorBinop::Oaddl, base, offset),
                CsharpminorExpr::Evar(value),
            ) if matches!(
                    base.as_ref(),
                    CsharpminorExpr::Eaddrof(ident) if *ident == ident_from_reg(owner)
                )
                && matches!(
                    offset.as_ref(),
                    CsharpminorExpr::Econst(Constant::Olongconst(2))
                )
                && *value == src
        ));
    }

    #[test]
    fn branch_statement_and_metadata_share_live_control_targets() {
        let [branch, raw_true, live_true, live_false] = synthetic_ids();

        let mut prog = CshminorPassProgram::default();
        prog.cminor_stmt.push((
            branch,
            CminorStmt::Sifthenelse(
                Condition::Ccompimm(Comparison::Ceq, 0),
                Arc::new(vec![7]),
                raw_true,
                live_false,
            ),
        ));
        prog.cminor_stmt.push((live_true, CminorStmt::Snop));
        prog.cminor_stmt.push((live_false, CminorStmt::Snop));
        prog.next.push((raw_true, live_true));

        prog.run();

        assert!(prog.csharp_stmt_candidate.iter().any(|(node, stmt)| {
            *node == branch
                && matches!(
                    stmt,
                    CsharpminorStmt::Scond(_, _, ifso, ifnot)
                        if *ifso == live_true && *ifnot == live_false
                )
        }));
    }

    #[test]
    fn conditional_successors_do_not_gain_an_address_order_fallthrough() {
        const BRANCH: u64 = 0x10;
        const IF_SO: u64 = 0x80;
        const IF_NOT: u64 = 0x20;
        const ADDRESS_NEXT: u64 = 0x18;

        let mut prog = CshminorPassProgram::default();
        prog.cminor_stmt.push((
            BRANCH,
            CminorStmt::Sifthenelse(
                Condition::Ccompimm(Comparison::Ceq, 0),
                Arc::new(vec![1]),
                IF_SO,
                IF_NOT,
            ),
        ));
        for node in [IF_SO, IF_NOT, ADDRESS_NEXT] {
            prog.cminor_stmt.push((node, CminorStmt::Snop));
        }
        // The instruction-next relation is layout metadata. Both semantic
        // successors of Sifthenelse are explicit in the statement.
        prog.next.push((BRANCH, ADDRESS_NEXT));

        prog.run();

        let successors: HashSet<u64> = prog
            .cminor_succ
            .iter()
            .filter_map(|(src, dst)| (*src == BRANCH).then_some(*dst))
            .collect();
        assert_eq!(successors, HashSet::from([IF_SO, IF_NOT]));
    }

    #[test]
    fn exclusively_loop_owned_abort_tail_is_folded() {
        on_large_stack(|| {
            let mut prog = abort_candidate();

            prog.run();

            assert!(!prog
                .loop_abort_unsafe_region
                .iter()
                .any(|fact| fact == &(FUNC, HEADER, ABORT_ENTRY)));
            assert!(prog
                .loop_abort_region
                .iter()
                .any(|fact| fact == &(FUNC, HEADER, ABORT_ENTRY)));
            assert!(prog
                .loop_abort_region
                .iter()
                .any(|fact| fact == &(FUNC, HEADER, ABORT_SINK)));
        });
    }

    #[test]
    fn externally_shared_abort_entry_is_not_folded() {
        on_large_stack(|| {
            let mut prog = abort_candidate();
            prog.cminor_succ.push((OUTSIDE_PRED, ABORT_ENTRY));

            prog.run();

            assert!(prog
                .loop_abort_external_entry
                .iter()
                .any(|fact| fact == &(FUNC, HEADER, ABORT_ENTRY)));
            assert!(prog
                .loop_abort_unsafe_region
                .iter()
                .any(|fact| fact == &(FUNC, HEADER, ABORT_ENTRY)));
            assert!(!prog
                .loop_abort_region
                .iter()
                .any(|(func, header, _)| *func == FUNC && *header == HEADER));
        });
    }

    #[test]
    fn external_entry_into_descendant_rejects_whole_abort_region() {
        on_large_stack(|| {
            let mut prog = abort_candidate();
            prog.cminor_succ.push((OUTSIDE_PRED, ABORT_SINK));

            prog.run();

            assert!(prog
                .loop_abort_external_entry
                .iter()
                .any(|fact| fact == &(FUNC, HEADER, ABORT_SINK)));
            assert!(prog
                .loop_abort_unsafe_region
                .iter()
                .any(|fact| fact == &(FUNC, HEADER, ABORT_ENTRY)));
            assert!(!prog
                .loop_abort_region
                .iter()
                .any(|(func, header, _)| *func == FUNC && *header == HEADER));
        });
    }

    #[test]
    fn shared_component_does_not_reject_disconnected_owned_abort() {
        on_large_stack(|| {
            let mut prog = abort_candidate();
            prog.cminor_succ.push((OUTSIDE_PRED, ABORT_SINK));
            prog.loop_abort_candidate.push((FUNC, HEADER, CLEAN_ENTRY));
            prog.loop_abort_candidate.push((FUNC, HEADER, CLEAN_SINK));
            prog.cminor_succ.push((CORE_EXIT, CLEAN_ENTRY));
            prog.cminor_succ.push((CLEAN_ENTRY, CLEAN_SINK));

            prog.run();

            assert!(!prog
                .loop_abort_region
                .iter()
                .any(|fact| fact == &(FUNC, HEADER, ABORT_ENTRY)));
            assert!(prog
                .loop_abort_region
                .iter()
                .any(|fact| fact == &(FUNC, HEADER, CLEAN_ENTRY)));
            assert!(prog
                .loop_abort_region
                .iter()
                .any(|fact| fact == &(FUNC, HEADER, CLEAN_SINK)));
        });
    }

    #[test]
    fn external_entry_taints_clean_sibling_through_shared_tail() {
        on_large_stack(|| {
            let mut prog = abort_candidate();
            prog.loop_abort_candidate
                .push((FUNC, HEADER, SIBLING_ENTRY));
            prog.cminor_succ.push((CORE_EXIT, SIBLING_ENTRY));
            prog.cminor_succ.push((SIBLING_ENTRY, ABORT_SINK));
            prog.cminor_succ.push((OUTSIDE_PRED, SIBLING_ENTRY));

            prog.run();

            assert!(prog
                .loop_abort_external_taint
                .iter()
                .any(|fact| fact == &(FUNC, HEADER, ABORT_SINK)));
            assert!(prog
                .loop_abort_unsafe_region
                .iter()
                .any(|fact| fact == &(FUNC, HEADER, ABORT_ENTRY)));
            assert!(!prog
                .loop_abort_region
                .iter()
                .any(|(func, header, _)| *func == FUNC && *header == HEADER));
        });
    }

    #[test]
    fn nonmonotonic_cfg_derives_idom_and_back_edge_from_dom_sets() {
        const ENTRY: u64 = 0x3000;
        const LEFT: u64 = 0x9000;
        const RIGHT: u64 = 0x2000;
        const LOOP_HEADER: u64 = 0x8000;
        const LATCH: u64 = 0x1000;

        // The latch-to-header edge increases numerically, and the diamond's
        // arms are deliberately out of address order. Dominance must therefore
        // come only from the CFG lattice, never from Node magnitude.
        let mut prog = CshminorPassProgram::default();
        prog.func_entry_node.push((FUNC, ENTRY));
        for node in [ENTRY, LEFT, RIGHT, LOOP_HEADER, LATCH] {
            prog.instr_in_function.push((node, FUNC));
        }
        for edge in [
            (ENTRY, LEFT),
            (ENTRY, RIGHT),
            (LEFT, LOOP_HEADER),
            (RIGHT, LOOP_HEADER),
            (LOOP_HEADER, LATCH),
            (LATCH, LOOP_HEADER),
        ] {
            prog.cminor_succ.push(edge);
        }

        prog.run();

        for expected in [
            (FUNC, LEFT, ENTRY),
            (FUNC, RIGHT, ENTRY),
            (FUNC, LOOP_HEADER, ENTRY),
            (FUNC, LATCH, LOOP_HEADER),
        ] {
            assert!(
                prog.idom.iter().any(|fact| fact == &expected),
                "missing structural idom {expected:?}"
            );
        }
        assert!(prog
            .loop_back_edge
            .iter()
            .any(|fact| fact == &(FUNC, LATCH, LOOP_HEADER)));
    }
}
