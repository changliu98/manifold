use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::{declare_io_from, run_pass};

use crate::decompile::passes::cminor_pass::*;
use std::collections::HashMap;
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
    // rtl_pass export: the single escaped canonical local per (func, offset), used to resolve synthetic-only stack loads that have no per-node stack_var.
    relation slot_escaped_canonical(Address, i64, RTLReg);
    // rtl_pass export: a conflict-free physical owner for a frame read that
    // begins inside a wider reaching write or escaped object.
    relation frame_read_storage_owner(Address, Address, i64, i64, RTLReg);
    // Reads/stores that must preserve byte-addressed access through that owner
    // rather than collapsing to the owner's scalar SSA value.
    relation frame_read_storage_access_owner(Address, Address, i64, i64, RTLReg);
    relation frame_write_storage_owner(Address, Address, i64, i64, RTLReg);
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

    // Resolve an untracked stack Eload to the function's local for that offset; an address-escaped slot uses rtl_pass's single slot_escaped_canonical, not the multi-valued fallback.
    csharp_stmt_candidate(node, stmt), stack_addr_resolved(node) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, CminorExpr::Eload(_chunk, addr, args))),
        if let Addressing::Ainstack(ofs) = addr,
        if args.is_empty(),
        instr_in_function(node, func_start),
        slot_escaped_canonical(func_start, *ofs, stack_rtl),
        let stmt = CsharpminorStmt::Sset(*dst, CsharpminorExpr::Evar(*stack_rtl));

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

    csharp_stmt_candidate(node, CsharpminorStmt::Sset(*dst, converted.clone())) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        symbolic_pointer_assign(node, expr, converted);

    // Generic Sassign -> Sset conversion (skipped when stack_addr_resolved or
    // an exact symbolic pointer immediate handles this same expression).
    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        !stack_addr_resolved(node),
        !symbolic_pointer_assign(node, expr, _),
        if let Some(converted) = csharp_expr_from_cminor(expr),
        let stmt = CsharpminorStmt::Sset(*dst, converted);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        !stack_addr_resolved(node),
        !symbolic_pointer_assign(node, expr, _),
        if let Some(converted) = csharp_expr_from_cminor_sized(expr, true),
        let stmt = CsharpminorStmt::Sset(*dst, converted);

    csharp_stmt_candidate(node, CsharpminorStmt::Snop) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        !stack_addr_resolved(node),
        !symbolic_pointer_assign(node, expr, _),
        if csharp_expr_from_cminor(expr).is_none();

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
        if let Some(addr_expr) = addressing_to_csharp_expr(addr, args.as_slice()),
        let value_expr = CsharpminorExpr::Evar(*src),
        let stmt = CsharpminorStmt::Sstore(chunk.clone(), addr_expr, value_expr);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sstore(chunk, addr, args, src)),
        !frame_write_has_storage_owner(node),
        if let Some(addr_expr) = addressing_to_csharp_expr_sized(addr, args.as_slice(), true),
        let value_expr = CsharpminorExpr::Evar(*src),
        let stmt = CsharpminorStmt::Sstore(chunk.clone(), addr_expr, value_expr);

    csharp_stmt_candidate(node, CsharpminorStmt::Snop) <--
        active_cminor_stmt(node, ?CminorStmt::Sstore(chunk, addr, args, src)),
        !frame_write_has_storage_owner(node),
        if addressing_to_csharp_expr(addr, args.as_slice()).is_none();

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
        if let Some(addr_expr) = addressing_to_csharp_expr_sized(addressing, load_args.as_slice(), true),
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
        if let Some(addr_expr) = addressing_to_csharp_expr_sized(addressing, load_args.as_slice(), true),
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

        run_pass!(db, CshminorPassProgram);
    }

    fn extra_reads(&self) -> &'static [&'static str] {
        &[
            "jump_table_target",
            "jump_table_impl",
            "jump_table_cmp",
            "jump_table_index_reg",
            "reg_rtl",
        ]
    }

    declare_io_from!(CshminorPassProgram);
}

#[cfg(test)]
mod tests {
    use super::{ident_from_reg, unique_external_cfg_entry, CshminorPassProgram};
    use crate::x86::op::{Addressing, Comparison, Condition, Operation};
    use crate::x86::types::{
        CminorBinop, CminorExpr, CminorStmt, Constant, CsharpminorExpr, CsharpminorStmt,
        MemoryChunk,
    };
    use either::Either;
    use std::collections::HashSet;
    use std::sync::Arc;

    fn synthetic_ids<const N: usize>() -> [u64; N] {
        std::array::from_fn(|index| index as u64 + 1)
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
    }

    #[test]
    fn externally_shared_abort_entry_is_not_folded() {
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
    }

    #[test]
    fn external_entry_into_descendant_rejects_whole_abort_region() {
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
    }

    #[test]
    fn shared_component_does_not_reject_disconnected_owned_abort() {
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
    }

    #[test]
    fn external_entry_taints_clean_sibling_through_shared_tail() {
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
