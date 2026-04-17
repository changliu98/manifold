

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::{declare_io_from, run_pass};

use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use crate::decompile::passes::cminor_pass::*;

use crate::x86::mach::Mreg;
use crate::x86::op::{Addressing, Condition, Operation};
use crate::x86::types::*;
use ascent::ascent_par;


#[derive(Clone, Debug, PartialEq, Eq, Hash, Copy)]
pub enum ExitType {
    Primary,
    EarlyBreak,
    #[allow(dead_code)]
    LateBreak,
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
    relation rtl_succ(Node, Node);
    relation cminor_fallthrough(Node, Node);
    relation emit_function(Address, Symbol, Node);
    relation emit_function_param(Address, RTLReg);
    relation next(Address, Address);
    relation emit_var_type_candidate(RTLReg, XType);
    relation idom(Address, Node, Node);
    relation stack_var(Address, Address, i64, RTLReg);


    relation stmt_can_fallthrough(Node);
    relation csh_next(Node, Node);
    relation cminor_succ(Node, Node);
    relation func_entry_node(Address, Node);
    relation pred(Address, Node, Node);

    stmt_can_fallthrough(node) <--
        active_cminor_stmt(node, stmt),
        if !matches!(stmt,
            CminorStmt::Sjump(_) |
            CminorStmt::Sreturn(_) |
            CminorStmt::Stailcall(_, _, _));

    // Walk `next` chain to first cminor node (transitive closure)
    #[local] relation next_to_cminor(Node, Node);
    next_to_cminor(a, b) <-- next(a, b), active_cminor_stmt(b, _);
    next_to_cminor(a, c) <-- next(a, b), !active_cminor_stmt(b, _), next_to_cminor(b, c);

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

    // Fallthrough as successor
    cminor_succ(node, next) <--
        csh_next(node, next),
        active_cminor_stmt(node, _),
        active_cminor_stmt(next, _);


    func_entry_node(func, entry) <--
        emit_function(func, _, entry);


    pred(func, to_node, from_node) <--
        cminor_succ(from_node, to_node),
        instr_in_function(from_node, func),
        instr_in_function(to_node, func);


    relation pred_count(Address, Node, usize);
    relation reachable_from_entry(Address, Node);
    relation path_avoiding(Address, Node, Node);
    relation dom(Address, Node, Node);
    relation not_idom(Address, Node, Node);
    relation dom_depth(Address, Node, usize);
    relation dom_children(Address, Node, Node);
    relation dom_tree_root(Address, Node);

    pred_count(func, node, count) <--
        instr_in_function(node, func),
        agg count = ascent::aggregators::count() in pred(func, node, _);

    reachable_from_entry(func, n) <-- func_entry_node(func, n);
    reachable_from_entry(func, y) <-- reachable_from_entry(func, x), cminor_succ(x, y), instr_in_function(y, func);

    // path_avoiding(func, n, d): n reachable from entry without passing through d
    path_avoiding(func, entry, d) <--
        func_entry_node(func, entry),
        reachable_from_entry(func, d),
        if entry != d;
    path_avoiding(func, n, d) <--
        path_avoiding(func, m, d),
        cminor_succ(m, n),
        instr_in_function(n, func),
        if n != d;

    // d dominates n iff no path from entry to n avoids d
    dom(func, n, n) <--
        reachable_from_entry(func, n);
    dom(func, n, d) <--
        reachable_from_entry(func, n),
        reachable_from_entry(func, d),
        !path_avoiding(func, n, d);

    // Immediate dominator: closest strict dominator
    not_idom(func, n, d) <--
        dom(func, n, d),
        dom(func, n, mid),
        dom(func, mid, d),
        if mid != n,
        if mid != d;
    idom(func, n, d) <--
        dom(func, n, d),
        !not_idom(func, n, d),
        if n != d;

    dom_depth(func, entry, 0) <--
        func_entry_node(func, entry);

    dom_depth(func, node, depth + 1) <--
        idom(func, node, idom_node),
        dom_depth(func, idom_node, depth);

    dom_children(func, parent, child) <--
        idom(func, child, parent);

    dom_tree_root(func, entry) <--
        func_entry_node(func, entry);


    relation csharp_stmt_candidate(Node, CsharpminorStmt);
    relation has_csharp_stmt_candidate(Node);

    // Track nodes where a stack address was resolved to Eaddrof via stack_var.
    #[local] relation stack_addr_resolved(Node);

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

    // Resolve Econst(Oaddrstack(ofs)) -> Eaddrof(var_ident) when stack_var maps the offset.
    // This handles the case where cminor_pass already converted Olea(Ainstack) to Oaddrstack.
    csharp_stmt_candidate(node, stmt), stack_addr_resolved(node) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, CminorExpr::Econst(Constant::Oaddrstack(ofs)))),
        instr_in_function(node, func_start),
        stack_var(func_start, node, *ofs, stack_rtl),
        let var_ident = ident_from_reg(*stack_rtl),
        let stmt = CsharpminorStmt::Sset(*dst, CsharpminorExpr::Eaddrof(var_ident));

    // Generic Sassign -> Sset conversion (skipped when stack_addr_resolved handles the node).
    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        !stack_addr_resolved(node),
        if let Some(converted) = csharp_expr_from_cminor(expr),
        let stmt = CsharpminorStmt::Sset(*dst, converted);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        !stack_addr_resolved(node),
        if let Some(converted) = csharp_expr_from_cminor_sized(expr, true),
        let stmt = CsharpminorStmt::Sset(*dst, converted);

    // Divergence: shlimm -> mulimm (CompCert compiles mul-by-power-of-2 as shl)
    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        if let CminorExpr::Eop(op, args) = expr,
        if args.len() == 1,
        if let Operation::Oshlimm(n) = op,
        if (1..=3).contains(n),
        let mul_val = 1i64 << *n,
        let converted = CsharpminorExpr::Ebinop(
            CminorBinop::Omul,
            Box::new(CsharpminorExpr::Evar(args[0])),
            Box::new(CsharpminorExpr::Econst(Constant::Ointconst(mul_val))),
        ),
        let stmt = CsharpminorStmt::Sset(*dst, converted);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        if let CminorExpr::Eop(op, args) = expr,
        if args.len() == 1,
        if let Operation::Oshllimm(n) = op,
        if (1..=3).contains(n),
        let mul_val = 1i64 << *n,
        let converted = CsharpminorExpr::Ebinop(
            CminorBinop::Omull,
            Box::new(CsharpminorExpr::Evar(args[0])),
            Box::new(CsharpminorExpr::Econst(Constant::Olongconst(mul_val))),
        ),
        let stmt = CsharpminorStmt::Sset(*dst, converted);

    csharp_stmt_candidate(node, CsharpminorStmt::Snop) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        !stack_addr_resolved(node),
        if csharp_expr_from_cminor(expr).is_none();

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sstore(chunk, addr, args, src)),
        if let Some(addr_expr) = addressing_to_csharp_expr(addr, args.as_slice()),
        let value_expr = CsharpminorExpr::Evar(*src),
        let stmt = CsharpminorStmt::Sstore(chunk.clone(), addr_expr, value_expr);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sstore(chunk, addr, args, src)),
        if let Some(addr_expr) = addressing_to_csharp_expr_sized(addr, args.as_slice(), true),
        let value_expr = CsharpminorExpr::Evar(*src),
        let stmt = CsharpminorStmt::Sstore(chunk.clone(), addr_expr, value_expr);

    csharp_stmt_candidate(node, CsharpminorStmt::Snop) <--
        active_cminor_stmt(node, ?CminorStmt::Sstore(chunk, addr, args, src)),
        if addressing_to_csharp_expr(addr, args.as_slice()).is_none();

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Scall(dst, sig, func, args)),
        let converted_func = match func.clone() {
            Either::Left(reg) => Either::Left(CsharpminorExpr::Evar(reg)),
            Either::Right(id) => Either::Right(id),
        },
        let call_args = args.iter().map(|r| CsharpminorExpr::Evar(*r)).collect(),
        let stmt = CsharpminorStmt::Scall(dst.clone(), sig.clone(), converted_func, call_args);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Stailcall(sig, func, args)),
        let converted_func = match func.clone() {
            Either::Left(reg) => Either::Left(CsharpminorExpr::Evar(reg)),
            Either::Right(id) => Either::Right(id),
        },
        let call_args = args.iter().map(|r| CsharpminorExpr::Evar(*r)).collect(),
        let stmt = CsharpminorStmt::Stailcall(sig.clone(), converted_func, call_args);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sbuiltin(dst, name, args, res)),
        let converted_args = args.iter().map(csharp_builtin_arg_from).collect(),
        let converted_res = csharp_builtin_arg_from(&res),
        let stmt = CsharpminorStmt::Sbuiltin(dst.clone(), name.clone(), converted_args, converted_res);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sbranch(cond, regs, ifso, ifnot)),
        let converted_args = regs
            .iter()
            .map(|r| CsharpminorExpr::Evar(*r))
            .collect::<Vec<CsharpminorExpr>>(),
        let stmt = CsharpminorStmt::Scond(cond.clone(), converted_args, *ifso, *ifnot);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sifthenelse(cond, regs, ifso, ifnot)),
        let converted_args = regs.iter().map(|r| CsharpminorExpr::Evar(*r)).collect(),
        let stmt = CsharpminorStmt::Scond(cond.clone(), converted_args, *ifso, *ifnot);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sjumptable(reg, targets)),
        let stmt = CsharpminorStmt::Sjumptable(CsharpminorExpr::Evar(*reg), targets.clone());

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sreturn(result)),
        let converted = CsharpminorExpr::Evar(*result),
        let stmt = CsharpminorStmt::Sreturn(converted);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Snop),
        let stmt = CsharpminorStmt::Snop;

    csharp_stmt_candidate(node, CsharpminorStmt::Sjump(*target)) <--
        active_cminor_stmt(node, ?CminorStmt::Sjump(target));

    has_csharp_stmt_candidate(node) <-- csharp_stmt_candidate(node, _);


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
        dom(func, latch, header);

    loop_head(func, header) <--
        loop_back_edge(func, _, header);


    relation loop_body(Address, Node, Node);

    loop_body(func, header, header) <--
        loop_back_edge(func, _, header);

    loop_body(func, header, latch) <--
        loop_back_edge(func, latch, header);

    loop_body(func, header, p) <--
        loop_body(func, header, node),
        pred(func, node, p),
        dom(func, p, header),
        if *p != *header;


    relation loop_nesting_via_idom(Address, Node, Node);
    relation directly_nested_dom(Address, Node, Node);
    relation intermediate_loop_dom(Address, Node, Node);
    relation immediate_loop_parent(Address, Node, Node);

    loop_nesting_via_idom(func, outer, inner) <--
        loop_head(func, outer),
        loop_head(func, inner),
        dom(func, inner, outer),
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


    relation enclosing_loops(Address, Node, Node);
    relation loop_depth(Address, Node, usize);

    enclosing_loops(func, node, header) <--
        loop_head(func, header),
        loop_body(func, header, node);

    loop_depth(func, node, depth) <--
        instr_in_function(node, func),
        agg depth = ascent::aggregators::count() in enclosing_loops(func, node, _);


    relation reducible_loop(Address, Node);
    relation has_side_entry(Address, Node);
    relation irreducible_loop(Address, Node);
    relation loop_preheader(Address, Node, Node);
    relation exit_dominated_by_header(Address, Node, Node);

    reducible_loop(func, header) <--
        loop_head(func, header),
        !has_side_entry(func, header);

    has_side_entry(func, header) <--
        loop_body(func, header, body_node),
        pred(func, body_node, external),
        !loop_body(func, header, external),
        if *body_node != *header;

    irreducible_loop(func, header) <--
        loop_head(func, header),
        has_side_entry(func, header);

    loop_preheader(func, header, preheader) <--
        loop_head(func, header),
        idom(func, header, preheader),
        !loop_body(func, header, preheader);

    exit_dominated_by_header(func, header, exit_target) <--
        loop_exit_edge(func, header, _, exit_target),
        dom(func, exit_target, header);


    relation nested_loop(Address, Node, Node);
    relation directly_nested(Address, Node, Node);
    relation intermediate_nesting(Address, Node, Node);
    relation innermost_loop(Address, Node, Node);
    relation node_in_nested_inner_loop(Address, Node, Node);

    nested_loop(func, outer, inner) <--
        loop_head(func, outer),
        loop_head(func, inner),
        if *outer != *inner,
        loop_body(func, outer, inner),
        !loop_body(func, inner, outer);

    directly_nested(func, outer, inner) <--
        nested_loop(func, outer, inner),
        !intermediate_nesting(func, outer, inner);

    intermediate_nesting(func, outer, inner) <--
        nested_loop(func, outer, mid),
        nested_loop(func, mid, inner);

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

    loop_exit_branch(func, header, branch_node, cond.clone(), Arc::new(args.clone()), *ifso, *ifnot, false) <--
        loop_body(func, header, branch_node),
        csharp_stmt_candidate(branch_node, ?CsharpminorStmt::Scond(cond, args, ifso, ifnot)),
        !loop_body(func, header, *ifso),
        loop_body(func, header, *ifnot);

    loop_exit_branch(func, header, branch_node, cond.clone(), Arc::new(args.clone()), *ifnot, *ifso, true) <--
        loop_body(func, header, branch_node),
        csharp_stmt_candidate(branch_node, ?CsharpminorStmt::Scond(cond, args, ifso, ifnot)),
        loop_body(func, header, *ifso),
        !loop_body(func, header, *ifnot);

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
    relation exit_type(Address, Node, Node, ExitType);

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

    exit_type(func, header, exit_node, ExitType::Primary) <--
        primary_exit_node(func, header, exit_node);

    exit_type(func, header, exit_node, ExitType::EarlyBreak) <--
        loop_exit_branch(func, header, exit_node, _, _, _, _, _),
        !primary_exit_node(func, header, exit_node);


    relation loop_defines_reg(Address, Node, Node, RTLReg);
    relation loop_uses_reg(Address, Node, RTLReg);
    relation loop_self_modify(Address, Node, Node, RTLReg);
    relation loop_increment(Address, Node, Node, RTLReg);
    relation exit_condition_uses_reg(Address, Node, RTLReg);
    relation induction_var(Address, Node, RTLReg);
    relation has_induction_var(Address, Node);

    loop_defines_reg(func, header, node, dst) <--
        loop_body(func, header, node),
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, _));

    loop_uses_reg(func, header, reg) <--
        loop_body(func, header, node),
        active_cminor_stmt(node, ?CminorStmt::Sassign(_, expr)),
        let vars = crate::decompile::passes::clight_pass::extract_vars_from_cminor_exprs(&[expr.clone()]),
        for reg in vars;

    loop_uses_reg(func, header, reg) <--
        loop_body(func, header, node),
        active_cminor_stmt(node, ?CminorStmt::Sstore(_, _, args, src)),
        let mut all_vars = args.to_vec(),
        let _ = all_vars.push(*src),
        for reg in all_vars;

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
    relation has_step_node(Address, Node);
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

    has_step_node(func, header) <--
        step_node(func, header, _, _);

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


    #[local] relation valid_loop_body(Address, Node, Node);

    valid_loop_body(func, header, node) <--
        loop_body(func, header, node),
        valid_loop(func, header);

    relation emit_loop_body(Address, Node, Node);
    relation emit_loop_exit(Address, Node, Node, Condition, Arc<Vec<CsharpminorExpr>>, Node, Node);
    relation trim_step(Address, Node, Node);
    relation loop_continue_cond(Address, Node, ClightExpr);
    relation emit_break_stmt(Address, Node, Node, ClightStmt);
    relation node_owned_by_loop(Address, Node, Node);

    emit_loop_body(func, header, body_node) <--
        valid_loop(func, header),
        loop_body(func, header, body_node);

    emit_loop_exit(func, header, branch_node, cond.clone(), args.clone(), *exit_target, *continue_target) <--
        valid_loop(func, header),
        loop_exit_branch(func, header, branch_node, cond, args, exit_target, continue_target, _);

    trim_step(func, header, step) <--
        step_node(func, header, step, _);

    loop_continue_cond(func, header, continue_cond) <--
        valid_loop(func, header),
        primary_exit_node(func, header, exit_node),
        loop_exit_branch(func, header, exit_node, cond, args, _, _, false),
        agg all_var_types = crate::decompile::passes::clight_pass::collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = crate::decompile::passes::clight_pass::extract_vars_from_csharp_exprs(args.as_slice()),
        let var_types = crate::decompile::passes::clight_pass::filter_and_build_multi_var_type_map(&all_var_types, &vars_used),
        let inverted_cond = crate::decompile::passes::clight_pass::invert_condition(&cond),
        if let Some(continue_cond) = crate::decompile::passes::clight_pass::clight_condition_expr_with_types(&inverted_cond, args.as_slice(), &var_types);

    loop_continue_cond(func, header, continue_cond) <--
        valid_loop(func, header),
        primary_exit_node(func, header, exit_node),
        loop_exit_branch(func, header, exit_node, cond, args, _, _, true),
        agg all_var_types = crate::decompile::passes::clight_pass::collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = crate::decompile::passes::clight_pass::extract_vars_from_csharp_exprs(args.as_slice()),
        let var_types = crate::decompile::passes::clight_pass::filter_and_build_multi_var_type_map(&all_var_types, &vars_used),
        if let Some(continue_cond) = crate::decompile::passes::clight_pass::clight_condition_expr_with_types(&cond, args.as_slice(), &var_types);

    emit_break_stmt(func, header, exit_node, break_stmt) <--
        valid_loop(func, header),
        loop_exit_branch(func, header, exit_node, cond, args, _, _, inverted),
        !primary_exit_node(func, header, exit_node),
        agg all_var_types = crate::decompile::passes::clight_pass::collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = crate::decompile::passes::clight_pass::extract_vars_from_csharp_exprs(args.as_slice()),
        let var_types = crate::decompile::passes::clight_pass::filter_and_build_multi_var_type_map(&all_var_types, &vars_used),
        let break_cond_raw = if *inverted {
            crate::decompile::passes::clight_pass::invert_condition(&cond)
        } else {
            cond.clone()
        },
        if let Some(break_cond) = crate::decompile::passes::clight_pass::clight_condition_expr_with_types(&break_cond_raw, args.as_slice(), &var_types),
        let break_stmt = ClightStmt::Sifthenelse(
            break_cond,
            Box::new(ClightStmt::Sbreak),
            Box::new(ClightStmt::Sskip),
        );

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
        if db.rel_iter::<(Node, usize, Node)>("jump_table_target").next().is_none() {
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

        let mut impl_set = std::collections::HashSet::new();
        for &(impl_addr, _) in db.rel_iter::<(Node, Node)>("jump_table_impl") {
            impl_set.insert(impl_addr);
        }

        // Sort jump-table nodes and pick lowest RTLReg discriminant for determinism.
        let mut jmp_nodes: Vec<Node> = tables.keys().copied().collect();
        jmp_nodes.sort();
        for jmp_node in jmp_nodes {
            let targets = &tables[&jmp_node];
            let impl_nodes = match impls.get(&jmp_node) {
                Some(v) => v,
                None => continue,
            };
            let entry = match impl_nodes.iter().min() {
                Some(&e) => e,
                None => continue,
            };
            let impl_set_local: std::collections::HashSet<Node> = impl_nodes.iter().copied()
                .chain(std::iter::once(jmp_node))
                .collect();

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
                        let mreg = Mreg::from(idx_name);
                        for &(addr, ref reg, rtl_reg) in db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl") {
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

            db.rel_push("cminor_stmt", (entry, CminorStmt::Sjumptable(reg, Arc::new(ordered_targets))));
        }

        let mut impl_nodes_sorted: Vec<Node> = impl_set.into_iter().collect();
        impl_nodes_sorted.sort();
        for node in impl_nodes_sorted {
            db.rel_push("trim_jump_table_impl", (node,));
        }
    }
}

impl IRPass for CshminorPass {
    fn name(&self) -> &'static str { "cshminor" }

    fn run(&self, db: &mut DecompileDB) {
        Self::prepare_jump_tables(db);

        run_pass!(db, CshminorPassProgram);
    }

    declare_io_from!(CshminorPassProgram);
}
