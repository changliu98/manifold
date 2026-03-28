

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::{declare_io_from, run_pass};

use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use crate::decompile::passes::cminor_pass::*;

use crate::x86::mach::Mreg;
use crate::x86::op::Condition;
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
    relation jump_table_impl_suppress(Node);

    #[local] relation active_cminor_stmt(Node, CminorStmt);
    active_cminor_stmt(node, stmt.clone()) <--
        cminor_stmt(node, stmt),
        !jump_table_impl_suppress(node);
    active_cminor_stmt(node, stmt.clone()) <--
        cminor_stmt(node, stmt),
        jump_table_impl_suppress(node),
        if matches!(stmt, CminorStmt::Sjumptable(_, _));

    relation instr_in_function(Node, Address);
    relation rtl_succ(Node, Node);
    relation cminor_fallthrough(Node, Node);
    relation emit_function(Address, Symbol, Node);
    relation emit_function_param(Address, RTLReg);
    relation next(Address, Address);
    relation emit_var_type_candidate(RTLReg, XType);
    relation idom(Address, Node, Node);
    relation pdom(Address, Node, Node);


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

    csh_next(node, next_node) <--
        stmt_can_fallthrough(node),
        cminor_fallthrough(node, next_node);

    cminor_succ(*node, *target) <-- active_cminor_stmt(node, ?CminorStmt::Sjump(target));
    cminor_succ(*node, *ifso) <-- active_cminor_stmt(node, ?CminorStmt::Sbranch(_, _, ifso, _));
    cminor_succ(*node, *ifnot) <-- active_cminor_stmt(node, ?CminorStmt::Sbranch(_, _, _, ifnot));
    cminor_succ(*node, *ifso) <-- active_cminor_stmt(node, ?CminorStmt::Sifthenelse(_, _, ifso, _));
    cminor_succ(*node, *ifnot) <-- active_cminor_stmt(node, ?CminorStmt::Sifthenelse(_, _, _, ifnot));
    cminor_succ(*node, target) <-- active_cminor_stmt(node, ?CminorStmt::Sjumptable(_, targets)), for target in targets.iter();
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

    dom(func, n, n) <--
        reachable_from_entry(func, n);

    dom(func, n, d) <--
        idom(func, n, mid),
        dom(func, mid, d);

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

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        if let Some(converted) = csharp_expr_from_cminor(expr),
        let stmt = CsharpminorStmt::Sset(*dst, converted);

    csharp_stmt_candidate(node, stmt) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        if let Some(converted) = csharp_expr_from_cminor_sized(expr, true),
        let stmt = CsharpminorStmt::Sset(*dst, converted);

    csharp_stmt_candidate(node, CsharpminorStmt::Snop) <--
        active_cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
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

    relation suppress_goto_to(Node);
    relation suppress_node_in_loop(Address, Node, Node);
    relation emit_loop_body(Address, Node, Node);
    relation emit_loop_exit(Address, Node, Node, Condition, Arc<Vec<CsharpminorExpr>>, Node, Node);
    relation suppress_step(Address, Node, Node);
    relation loop_continue_cond(Address, Node, ClightExpr);
    relation emit_break_stmt(Address, Node, Node, ClightStmt);
    relation node_owned_by_loop(Address, Node, Node);

    suppress_goto_to(header) <--
        valid_loop(_, header);

    suppress_node_in_loop(func, header, node) <--
        node_owned_by_loop(func, node, header);

    suppress_node_in_loop(func, header, header) <--
        valid_loop(func, header);

    emit_loop_body(func, header, body_node) <--
        valid_loop(func, header),
        loop_body(func, header, body_node);

    emit_loop_exit(func, header, branch_node, cond.clone(), args.clone(), *exit_target, *continue_target) <--
        valid_loop(func, header),
        loop_exit_branch(func, header, branch_node, cond, args, exit_target, continue_target, _);

    suppress_step(func, header, step) <--
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
        !node_owned_by_ifthenelse(func, node, _),
        !loop_head(func, node);

    node_owned_by_loop(func, node, parent) <--
        loop_head(func, node),
        valid_loop(func, node),
        immediate_loop_parent(func, node, parent),
        !node_owned_by_ifthenelse(func, node, _);


    relation ifthenelse_branch_point(Address, Node, Node, Node);
    #[local] relation ifthenelse_merge_candidate(Address, Node, Node);
    #[local] relation ifthenelse_earlier_merge_candidate(Address, Node, Node);
    #[local] relation ifso_fallthrough(Address, Node, Node);
    relation ifthenelse_merge_point(Address, Node, Node);
    relation valid_ifthenelse(Address, Node);
    relation if_only_block(Address, Node, Node);
    relation emit_if_only_block(Address, Node);
    relation ifthenelse_if_branch(Address, Node, Node);
    relation ifthenelse_else_branch(Address, Node, Node);
    relation emit_ifthenelse_body(Address, Node, Node, bool);
    relation suppress_node_in_ifthenelse(Address, Node, Node);

    ifthenelse_branch_point(func, node, *ifso, *ifnot) <--
        csharp_stmt_candidate(node, ?CsharpminorStmt::Scond(_, _, ifso, ifnot)),
        instr_in_function(node, func),
        !valid_loop(func, node),
        !valid_loop_body(func, _, node),
        if *ifso != *ifnot;

    ifthenelse_branch_point(func, node, *ifso, *ifnot) <--
        csharp_stmt_candidate(node, ?CsharpminorStmt::Scond(_, _, ifso, ifnot)),
        instr_in_function(node, func),
        !valid_loop(func, node),
        valid_loop_body(func, header, node),
        loop_body(func, header, *ifso),
        loop_body(func, header, *ifnot),
        if *ifso != *ifnot;


    // --- Merge candidates: collect all possible merge points ---

    // Candidate 1: postdominator
    ifthenelse_merge_candidate(func, branch, merge) <--
        ifthenelse_branch_point(func, branch, _, _),
        pdom(func, branch, merge),
        if *merge != *branch;

    // Candidate 2: common one-hop successor of both targets
    ifthenelse_merge_candidate(func, branch, succ_node) <--
        ifthenelse_branch_point(func, branch, ifso, ifnot),
        cminor_succ(ifso, succ_node),
        cminor_succ(ifnot, succ_node);

    // Candidate 3: ifso falls through to ifnot (diamond pattern)
    ifthenelse_merge_candidate(func, branch, ifnot) <--
        ifthenelse_branch_point(func, branch, ifso, ifnot),
        cminor_succ(ifso, ifnot),
        instr_in_function(ifnot, func);

    // Candidate 4: ifnot falls through to ifso
    ifthenelse_merge_candidate(func, branch, ifso) <--
        ifthenelse_branch_point(func, branch, ifso, ifnot),
        cminor_succ(ifnot, ifso),
        instr_in_function(ifso, func);

    // Candidate 5: sequential continuation -- walk cminor_fallthrough from ifso to the next branch point as merge candidate (fixes conditional chains with shared noreturn else-target).
    ifso_fallthrough(func, branch, *ifso) <--
        ifthenelse_branch_point(func, branch, ifso, _);

    ifso_fallthrough(func, branch, next) <--
        ifso_fallthrough(func, branch, node),
        cminor_fallthrough(node, next),
        instr_in_function(next, func),
        !ifthenelse_branch_point(func, next, _, _);

    ifthenelse_merge_candidate(func, branch, bp) <--
        ifso_fallthrough(func, branch, node),
        cminor_fallthrough(node, bp),
        ifthenelse_branch_point(func, bp, _, _),
        instr_in_function(bp, func),
        if *bp != *branch;

    // --- Selection: pick the closest merge candidate ---
    ifthenelse_earlier_merge_candidate(func, branch, merge) <--
        ifthenelse_merge_candidate(func, branch, merge),
        ifthenelse_merge_candidate(func, branch, closer),
        if *closer > *branch,
        if *closer < *merge;

    ifthenelse_merge_point(func, branch, merge) <--
        ifthenelse_merge_candidate(func, branch, merge),
        if *merge > *branch,
        !ifthenelse_earlier_merge_candidate(func, branch, merge);

    valid_ifthenelse(func, branch) <--
        ifthenelse_branch_point(func, branch, _, _),
        ifthenelse_merge_point(func, branch, _);

    if_only_block(func, branch, merge) <--
        valid_ifthenelse(func, branch),
        ifthenelse_branch_point(func, branch, _, ifnot),
        ifthenelse_merge_point(func, branch, merge),
        if *ifnot == *merge;

    emit_if_only_block(func, branch) <--
        if_only_block(func, branch, _);

    ifthenelse_if_branch(func, branch, ifso) <--
        ifthenelse_branch_point(func, branch, ifso, _),
        ifthenelse_merge_point(func, branch, merge),
        if *ifso != *merge;

    ifthenelse_if_branch(func, branch, next) <--
        ifthenelse_if_branch(func, branch, node),
        cminor_succ(node, next),
        ifthenelse_merge_point(func, branch, merge),
        instr_in_function(next, func),
        if *next != *merge,
        if *next != *branch;

    ifthenelse_else_branch(func, branch, ifnot) <--
        ifthenelse_branch_point(func, branch, _, ifnot),
        ifthenelse_merge_point(func, branch, merge),
        if *ifnot != *merge;

    ifthenelse_else_branch(func, branch, next) <--
        ifthenelse_else_branch(func, branch, node),
        cminor_succ(node, next),
        ifthenelse_merge_point(func, branch, merge),
        instr_in_function(next, func),
        if *next != *merge,
        if *next != *branch;

    emit_ifthenelse_body(func, branch, node, true) <--
        valid_ifthenelse(func, branch),
        ifthenelse_if_branch(func, branch, node);

    emit_ifthenelse_body(func, branch, node, false) <--
        valid_ifthenelse(func, branch),
        ifthenelse_else_branch(func, branch, node),
        !ifthenelse_if_branch(func, branch, node);

    suppress_node_in_ifthenelse(func, branch, node) <--
        emit_ifthenelse_body(func, branch, node, _),
        valid_ifthenelse(func, branch),
        if *node != *branch;


    relation ifthenelse_inside_loop(Address, Node, Node);
    relation node_owned_by_ifthenelse(Address, Node, Node);

    ifthenelse_inside_loop(func, branch, loop_head) <--
        valid_ifthenelse(func, branch),
        suppress_node_in_loop(func, loop_head, branch);

    node_owned_by_ifthenelse(func, node, branch) <--
        emit_ifthenelse_body(func, branch, node, _),
        valid_ifthenelse(func, branch),
        if *node != *branch;



    relation ternary_true_assignment(Address, Node, RTLReg, CsharpminorExpr, Node);
    relation ternary_false_assignment(Address, Node, RTLReg, CsharpminorExpr, Node);
    relation valid_ternary(Address, Node, RTLReg, CsharpminorExpr, CsharpminorExpr, Node);
    relation suppress_for_ternary(Node);
    relation emit_ternary(Address, Node, RTLReg);

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
        !suppress_node_in_loop(func, _, branch);

    suppress_for_ternary(ifso) <--
        valid_ternary(func, branch, _, _, _, _),
        csharp_stmt_candidate(branch, ?CsharpminorStmt::Scond(_, _, ifso, _)),
        instr_in_function(ifso, func);
    suppress_for_ternary(ifnot) <--
        valid_ternary(func, branch, _, _, _, _),
        csharp_stmt_candidate(branch, ?CsharpminorStmt::Scond(_, _, _, ifnot)),
        instr_in_function(ifnot, func);

    emit_ternary(func, branch, var) <--
        valid_ternary(func, branch, var, _, _, _);


    relation short_circuit_and(Address, Node, Node, Node, Node);
    relation short_circuit_or(Address, Node, Node, Node, Node);
    relation suppress_for_short_circuit(Node);
    relation emit_short_circuit_and(Address, Node, Node);
    relation emit_short_circuit_or(Address, Node, Node);

    short_circuit_and(func, branch1, branch2, final_true, final_false) <--
        csharp_stmt_candidate(branch1, ?CsharpminorStmt::Scond(_, _, ifso1, ifnot1)),
        instr_in_function(branch1, func),
        csharp_stmt_candidate(branch2, ?CsharpminorStmt::Scond(_, _, ifso2, ifnot2)),
        if *ifso1 == *branch2,
        if *ifnot1 == *ifnot2,
        let final_true = *ifso2,
        let final_false = *ifnot2,
        !valid_loop(func, branch1),
        !valid_ternary(func, branch1, _, _, _, _);

    short_circuit_or(func, branch1, branch2, final_true, final_false) <--
        csharp_stmt_candidate(branch1, ?CsharpminorStmt::Scond(_, _, ifso1, ifnot1)),
        instr_in_function(branch1, func),
        csharp_stmt_candidate(branch2, ?CsharpminorStmt::Scond(_, _, ifso2, ifnot2)),
        if *ifnot1 == *branch2,
        if *ifso1 == *ifso2,
        let final_true = *ifso1,
        let final_false = *ifnot2,
        !valid_loop(func, branch1),
        !valid_ternary(func, branch1, _, _, _, _);

    suppress_for_short_circuit(branch2) <--
        short_circuit_and(_, _, branch2, _, _);
    suppress_for_short_circuit(branch2) <--
        short_circuit_or(_, _, branch2, _, _);

    emit_short_circuit_and(func, branch1, branch2) <--
        short_circuit_and(func, branch1, branch2, _, _);

    emit_short_circuit_or(func, branch1, branch2) <--
        short_circuit_or(func, branch1, branch2, _, _);
}

fn lengauer_tarjan(
    succs: &[Vec<usize>],
    preds: &[Vec<usize>],
    entry_idx: usize,
    n: usize,
) -> Option<Vec<(usize, usize)>> {
    if n <= 1 {
        return Some(Vec::new());
    }

    let mut dfnum = vec![u32::MAX; n];
    let mut vertex: Vec<usize> = Vec::with_capacity(n);
    let mut dfs_parent = vec![usize::MAX; n];

    {
        let mut stack: Vec<(usize, usize)> = Vec::new();
        dfnum[entry_idx] = 0;
        vertex.push(entry_idx);
        stack.push((entry_idx, 0));

        while let Some((node, child_ptr)) = stack.last_mut() {
            let node_val = *node;
            if *child_ptr < succs[node_val].len() {
                let succ = succs[node_val][*child_ptr];
                *child_ptr += 1;
                if dfnum[succ] == u32::MAX {
                    dfs_parent[succ] = node_val;
                    dfnum[succ] = vertex.len() as u32;
                    vertex.push(succ);
                    stack.push((succ, 0));
                }
            } else {
                stack.pop();
            }
        }
    }

    let dfs_count = vertex.len();
    if dfs_count <= 1 {
        return Some(Vec::new());
    }

    let mut semi = vec![0u32; n];
    let mut idom_arr = vec![usize::MAX; n];
    let mut ancestor = vec![usize::MAX; n];
    let mut label = (0..n).collect::<Vec<_>>();
    let mut bucket: Vec<Vec<usize>> = vec![Vec::new(); n];

    for i in 0..dfs_count {
        semi[vertex[i]] = i as u32;
    }

    fn eval(v: usize, ancestor: &mut [usize], label: &mut [usize], semi: &[u32]) -> usize {
        if ancestor[v] == usize::MAX {
            return v;
        }
        let mut chain = Vec::new();
        let mut u = v;
        while ancestor[u] != usize::MAX && ancestor[ancestor[u]] != usize::MAX {
            chain.push(u);
            u = ancestor[u];
        }
        for &node in chain.iter().rev() {
            let a = ancestor[node];
            if semi[label[a]] < semi[label[node]] {
                label[node] = label[a];
            }
            ancestor[node] = ancestor[u];
        }
        label[v]
    }

    for i in (1..dfs_count).rev() {
        let w = vertex[i];
        let p = dfs_parent[w];

        let mut s = dfnum[w];
        for &v in &preds[w] {
            if dfnum[v] == u32::MAX {
                continue;
            }
            let s_prime = if dfnum[v] <= dfnum[w] {
                dfnum[v]
            } else {
                semi[eval(v, &mut ancestor, &mut label, &semi)]
            };
            s = s.min(s_prime);
        }
        semi[w] = s;
        bucket[vertex[s as usize]].push(w);
        ancestor[w] = p;

        for v in std::mem::take(&mut bucket[p]) {
            let u = eval(v, &mut ancestor, &mut label, &semi);
            idom_arr[v] = if semi[u] < semi[v] { u } else { p };
        }
    }

    for i in 1..dfs_count {
        let w = vertex[i];
        if idom_arr[w] != usize::MAX && idom_arr[w] != vertex[semi[w] as usize] {
            idom_arr[w] = idom_arr[idom_arr[w]];
        }
    }

    let mut result = Vec::with_capacity(dfs_count);
    for i in 1..dfs_count {
        let w = vertex[i];
        if idom_arr[w] < n {
            result.push((w, idom_arr[w]));
        }
    }

    Some(result)
}

pub struct CshminorPass;

impl CshminorPass {
    fn prepare_dominators(db: &mut DecompileDB) {
        let mut func_nodes: HashMap<u64, HashSet<u64>> = HashMap::new();
        let mut func_entry: HashMap<u64, u64> = HashMap::new();

        let mut node_to_func: HashMap<u64, u64> = HashMap::new();
        for &(node, func) in db.rel_iter::<(Node, Address)>("instr_in_function") {
            node_to_func.insert(node, func);
        }

        for &(node, ref _stmt) in db.rel_iter::<(Node, CminorStmt)>("cminor_stmt") {
            if let Some(&func) = node_to_func.get(&node) {
                func_nodes.entry(func).or_default().insert(node);
            }
        }

        for &(func, _, entry) in db.rel_iter::<(Address, Symbol, Node)>("emit_function") {
            func_entry.insert(func, entry);
        }

        let mut succs_map: HashMap<u64, Vec<u64>> = HashMap::new();

        let cminor_nodes: HashSet<u64> = db.rel_iter::<(Node, CminorStmt)>("cminor_stmt").map(|&(n, _)| n).collect();

        let mut sorted_func_cminor: HashMap<u64, Vec<u64>> = HashMap::new();
        for (&func, nodes) in &func_nodes {
            let mut sorted: Vec<u64> = nodes.iter().copied().collect();
            sorted.sort_unstable();
            sorted_func_cminor.insert(func, sorted);
        }

        let resolve_target = |target: u64, func: u64| -> Option<u64> {
            if cminor_nodes.contains(&target) {
                return Some(target);
            }
            if let Some(sorted) = sorted_func_cminor.get(&func) {
                match sorted.binary_search(&target) {
                    Ok(_) => Some(target),
                    Err(pos) => {
                        if pos < sorted.len() {
                            Some(sorted[pos])
                        } else {
                            None
                        }
                    }
                }
            } else {
                None
            }
        };


        for &(node, ref stmt) in db.rel_iter::<(Node, CminorStmt)>("cminor_stmt") {
            let targets: Vec<u64> = match stmt {
                CminorStmt::Sjump(target) => vec![*target],
                CminorStmt::Sbranch(_, _, ifso, ifnot) => vec![*ifso, *ifnot],
                CminorStmt::Sifthenelse(_, _, ifso, ifnot) => vec![*ifso, *ifnot],
                CminorStmt::Sjumptable(_, targets) => targets.to_vec(),
                _ => vec![],
            };
            let func = node_to_func.get(&node).copied().unwrap_or(0);
            for t in targets {
                if let Some(resolved) = resolve_target(t, func) {
                    succs_map.entry(node).or_default().push(resolved);
                }
            }
        }

        let non_fallthrough: HashSet<u64> = db.rel_iter::<(Node, CminorStmt)>("cminor_stmt")
            .filter(|&&(_, ref stmt)| matches!(stmt,
                CminorStmt::Sjump(_) | CminorStmt::Sreturn(_) | CminorStmt::Stailcall(_, _, _)))
            .map(|&(node, _)| node)
            .collect();

        // Collect synthetic-node fallthrough edges (from cminor_pass via rtl_succ)
        let synthetic_ft: HashSet<(u64, u64)> = db.rel_iter::<(Node, Node)>("cminor_fallthrough")
            .map(|&(a, b)| (a, b))
            .collect();
        let has_synthetic_ft: HashSet<u64> = synthetic_ft.iter().map(|&(a, _)| a).collect();

        for &(src, dst) in &synthetic_ft {
            succs_map.entry(src).or_default().push(dst);
        }

        // Address-sorted fallthrough for non-synthetic nodes
        for (&_func, sorted) in &sorted_func_cminor {
            for i in 0..sorted.len().saturating_sub(1) {
                let node = sorted[i];
                if non_fallthrough.contains(&node) { continue; }
                if has_synthetic_ft.contains(&node) { continue; }
                let next_cminor = sorted[i + 1];
                if next_cminor & (1u64 << 62) != 0 { continue; }
                succs_map.entry(node).or_default().push(next_cminor);
                db.rel_push("cminor_fallthrough", (node, next_cminor));
            }
        }

        let mut resolved_edges: Vec<(u64, u64)> = Vec::new();
        for &(node, ref stmt) in db.rel_iter::<(Node, CminorStmt)>("cminor_stmt") {
            let targets: Vec<u64> = match stmt {
                CminorStmt::Sjump(target) => vec![*target],
                CminorStmt::Sbranch(_, _, ifso, ifnot) => vec![*ifso, *ifnot],
                CminorStmt::Sifthenelse(_, _, ifso, ifnot) => vec![*ifso, *ifnot],
                CminorStmt::Sjumptable(_, targets) => targets.to_vec(),
                _ => vec![],
            };
            let func = node_to_func.get(&node).copied().unwrap_or(0);
            for t in targets {
                if !cminor_nodes.contains(&t) {
                    if let Some(resolved) = resolve_target(t, func) {
                        if resolved != t {
                            resolved_edges.push((node, resolved));
                        }
                    }
                }
            }
        }
        for (from, to) in resolved_edges {
            db.rel_push("cminor_succ", (from, to));
        }

        for (&func, nodes) in &func_nodes {
            let entry = match func_entry.get(&func) {
                Some(&e) => e,
                None => continue,
            };

            if !nodes.contains(&entry) {
                continue;
            }

            let node_vec: Vec<u64> = nodes.iter().copied().collect();
            let n = node_vec.len();
            let mut node_to_idx: HashMap<u64, usize> = HashMap::with_capacity(n);
            for (i, &node) in node_vec.iter().enumerate() {
                node_to_idx.insert(node, i);
            }

            let mut fwd_succs: Vec<Vec<usize>> = vec![Vec::new(); n];
            let mut fwd_preds: Vec<Vec<usize>> = vec![Vec::new(); n];

            for &node in nodes {
                if let Some(targets) = succs_map.get(&node) {
                    if let Some(&from_idx) = node_to_idx.get(&node) {
                        for &target in targets {
                            if let Some(&to_idx) = node_to_idx.get(&target) {
                                fwd_succs[from_idx].push(to_idx);
                                fwd_preds[to_idx].push(from_idx);
                            }
                        }
                    }
                }
            }

            for s in fwd_succs.iter_mut() { s.sort_unstable(); s.dedup(); }
            for p in fwd_preds.iter_mut() { p.sort_unstable(); p.dedup(); }

            let entry_idx = node_to_idx[&entry];
            if let Some(idom_map) = lengauer_tarjan(&fwd_succs, &fwd_preds, entry_idx, n) {
                for (node_idx, idom_idx) in idom_map {
                    db.rel_push("idom", (func, node_vec[node_idx], node_vec[idom_idx]));
                }
            }

            let mut exit_indices: Vec<usize> = Vec::new();
            for &(node, ref stmt) in db.rel_iter::<(Node, CminorStmt)>("cminor_stmt") {
                if nodes.contains(&node) {
                    if matches!(stmt, CminorStmt::Sreturn(_) | CminorStmt::Stailcall(_, _, _)) {
                        if let Some(&idx) = node_to_idx.get(&node) {
                            exit_indices.push(idx);
                        }
                    }
                }
            }

            // For non-returning functions (e.g., exit()/abort()), use leaf nodes as fallback exit points
            if exit_indices.is_empty() {
                for idx in 0..n {
                    if fwd_succs[idx].is_empty() {
                        exit_indices.push(idx);
                    }
                }
            }

            if !exit_indices.is_empty() {
                let vn = n + 1;
                let virtual_exit = n;
                let mut rev_succs: Vec<Vec<usize>> = vec![Vec::new(); vn];
                let mut rev_preds: Vec<Vec<usize>> = vec![Vec::new(); vn];

                for from_idx in 0..n {
                    for &to_idx in &fwd_succs[from_idx] {
                        rev_succs[to_idx].push(from_idx);
                        rev_preds[from_idx].push(to_idx);
                    }
                }

                for &exit_idx in &exit_indices {
                    rev_succs[virtual_exit].push(exit_idx);
                    rev_preds[exit_idx].push(virtual_exit);
                }

                for s in rev_succs.iter_mut() { s.sort_unstable(); s.dedup(); }
                for p in rev_preds.iter_mut() { p.sort_unstable(); p.dedup(); }

                if let Some(ipdom_map) = lengauer_tarjan(&rev_succs, &rev_preds, virtual_exit, vn) {
                    for (node_idx, ipdom_idx) in ipdom_map {
                        if node_idx < n && ipdom_idx < n {
                            db.rel_push("pdom", (func, node_vec[node_idx], node_vec[ipdom_idx]));
                        }
                    }
                }
            }
        }
    }

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

        for (jmp_node, targets) in &tables {
            let impl_nodes = match impls.get(jmp_node) {
                Some(v) => v,
                None => continue,
            };
            let entry = match impl_nodes.iter().min() {
                Some(&e) => e,
                None => continue,
            };

            let ordered_targets: Vec<Node> = targets.iter().map(|(_, t)| *t).collect();

            let mut discriminant: Option<RTLReg> = None;
            for (_node, stmt) in db.rel_iter::<(Node, CminorStmt)>("cminor_stmt") {
                match stmt {
                    CminorStmt::Sbranch(_, args, ifso, ifnot) => {
                        if (*ifso == entry || *ifnot == entry) && args.len() == 1 {
                            discriminant = Some(args[0]);
                            break;
                        }
                    }
                    CminorStmt::Sifthenelse(_, args, ifso, ifnot) => {
                        if (*ifso == entry || *ifnot == entry) && args.len() == 1 {
                            discriminant = Some(args[0]);
                            break;
                        }
                    }
                    _ => {}
                }
            }

            if discriminant.is_none() {
                if let Some(&(_, cmp_addr)) = db.rel_iter::<(Node, Node)>("jump_table_cmp").find(|(j, _)| *j == *jmp_node) {
                    if let Some(&(_, index_reg_name)) = db.rel_iter::<(Node, &'static str)>("jump_table_index_reg").find(|(j, _)| *j == *jmp_node) {
                        let mreg = Mreg::from(index_reg_name);
                        for &(addr, ref reg, rtl_reg) in db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl") {
                            if addr == cmp_addr && *reg == mreg {
                                discriminant = Some(rtl_reg);
                                break;
                            }
                        }
                    }
                }
            }

            let reg = match discriminant {
                Some(r) => r,
                None => continue,
            };

            db.rel_push("cminor_stmt", (entry, CminorStmt::Sjumptable(reg, Arc::new(ordered_targets))));
        }

        for &node in &impl_set {
            db.rel_push("jump_table_impl_suppress", (node,));
        }
    }
}

impl IRPass for CshminorPass {
    fn name(&self) -> &'static str { "cshminor" }

    fn run(&self, db: &mut DecompileDB) {
        Self::prepare_jump_tables(db);
        Self::prepare_dominators(db);

        run_pass!(db, CshminorPassProgram);
    }

    declare_io_from!(CshminorPassProgram);
}
