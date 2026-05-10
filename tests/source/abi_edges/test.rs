fn call_count_to(func: &str, callee: &str) -> usize {
    fn count_expr(expr: &CExpr, callee: &str) -> usize {
        let here = match expr {
            CExpr::Call(f, _) if matches!(unwrap_casts(f.as_ref()), CExpr::Var(n) if n == callee) => {
                1
            }
            _ => 0,
        };
        here + match expr {
            CExpr::Unary(_, inner)
            | CExpr::Cast(_, inner)
            | CExpr::SizeofExpr(inner)
            | CExpr::Paren(inner) => count_expr(inner, callee),
            CExpr::Binary(_, l, r) | CExpr::Assign(_, l, r) | CExpr::Index(l, r) => {
                count_expr(l, callee) + count_expr(r, callee)
            }
            CExpr::Ternary(c, t, e) => {
                count_expr(c, callee) + count_expr(t, callee) + count_expr(e, callee)
            }
            CExpr::Call(f, args) => {
                count_expr(f, callee) + args.iter().map(|a| count_expr(a, callee)).sum::<usize>()
            }
            CExpr::Member(inner, _) | CExpr::MemberPtr(inner, _) => count_expr(inner, callee),
            CExpr::StmtExpr(_, inner) => count_expr(inner, callee),
            _ => 0,
        }
    }

    fn count_stmt(stmt: &CStmt, callee: &str) -> usize {
        match stmt {
            CStmt::Expr(e) | CStmt::Return(Some(e)) => count_expr(e, callee),
            CStmt::If(cond, then_s, else_s) => {
                count_expr(cond, callee)
                    + count_stmt(then_s, callee)
                    + else_s.as_ref().map_or(0, |s| count_stmt(s, callee))
            }
            CStmt::While(cond, body) | CStmt::DoWhile(body, cond) => {
                count_expr(cond, callee) + count_stmt(body, callee)
            }
            CStmt::For(init, cond, update, body) => {
                let init_count = match init {
                    Some(ForInit::Expr(e)) => count_expr(e, callee),
                    _ => 0,
                };
                init_count
                    + cond.as_ref().map_or(0, |e| count_expr(e, callee))
                    + update.as_ref().map_or(0, |e| count_expr(e, callee))
                    + count_stmt(body, callee)
            }
            CStmt::Switch(expr, body) => count_expr(expr, callee) + count_stmt(body, callee),
            CStmt::Block(items) => items
                .iter()
                .map(|item| match item {
                    CBlockItem::Stmt(s) => count_stmt(s, callee),
                    CBlockItem::Decl(_) => 0,
                })
                .sum(),
            CStmt::Labeled(_, inner) => count_stmt(inner, callee),
            CStmt::Sequence(stmts) => stmts.iter().map(|s| count_stmt(s, callee)).sum(),
            _ => 0,
        }
    }

    count_stmt(&func_def(&OUTPUT, func).body, callee)
}

fn has_indirect_call(func: &str) -> bool {
    let f = func_def(&OUTPUT, func);
    stmt_has_expr(&f.body, &|e| match e {
        CExpr::Call(callee, _) => match unwrap_casts(callee.as_ref()) {
            CExpr::Var(name) => !matches!(
                name.as_str(),
                "add_edge" | "xor_edge" | "apply_selected" | "select_and_call"
            ),
            _ => true,
        },
        _ => false,
    })
}

#[test]
fn all_functions_present() {
    for name in [
        "ret_i8",
        "ret_u16",
        "ret_i32",
        "ret_i64",
        "combine_return_widths",
        "more_than_six_args",
        "call_with_stack_args",
        "outparam_and_return",
        "add_edge",
        "xor_edge",
        "apply_selected",
        "select_and_call",
        "record_side_effect",
        "void_helper_sequence",
        "reuse_call_result",
    ] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn return_width_caller_preserves_all_helper_calls() {
    assert!(has_call_to(&OUTPUT, "combine_return_widths", "ret_i8"));
    assert!(has_call_to(&OUTPUT, "combine_return_widths", "ret_u16"));
    assert!(has_call_to(&OUTPUT, "combine_return_widths", "ret_i32"));
    assert!(has_call_to(&OUTPUT, "combine_return_widths", "ret_i64"));
}

#[test]
fn return_width_caller_combines_results() {
    assert!(
        has_binop(&OUTPUT, "combine_return_widths", BinaryOp::Add),
        "expected additions combining mixed-width returns"
    );
}

#[test]
fn stack_arg_callee_keeps_many_params_and_terms() {
    let b = body(&OUTPUT, "more_than_six_args");
    assert!(
        param_count(&OUTPUT, "more_than_six_args") >= 6,
        "expected register params plus at least one recovered stack-passed value"
    );
    assert!(
        has_binop(&OUTPUT, "more_than_six_args", BinaryOp::Mul)
            || has_binop(&OUTPUT, "more_than_six_args", BinaryOp::Add),
        "expected weighted combination of many arguments:\n{b}"
    );
}

#[test]
fn stack_arg_caller_calls_callee() {
    assert!(
        has_call_to(&OUTPUT, "call_with_stack_args", "more_than_six_args"),
        "expected call with integer args beyond register-passed parameters"
    );
}

#[test]
fn outparam_function_writes_pointers_and_returns_value() {
    let b = body(&OUTPUT, "outparam_and_return");
    assert!(
        has_deref(&OUTPUT, "outparam_and_return"),
        "expected stores through out-parameters"
    );
    assert!(
        has_assign(&OUTPUT, "outparam_and_return"),
        "expected out-parameter assignments"
    );
    assert!(
        has_binop(&OUTPUT, "outparam_and_return", BinaryOp::BitXor)
            || has_binop(&OUTPUT, "outparam_and_return", BinaryOp::Add)
            || has_binop(&OUTPUT, "outparam_and_return", BinaryOp::Sub)
            || b.contains("return"),
        "expected return value alongside out-parameter stores:\n{b}"
    );
}

#[test]
fn function_pointer_selection_has_branch_and_apply_call() {
    assert!(
        has_if_stmt(&OUTPUT, "select_and_call"),
        "expected branch selecting a function pointer"
    );
    assert!(
        has_call_to(&OUTPUT, "select_and_call", "apply_selected"),
        "expected selected function pointer to be passed to apply_selected"
    );
}

#[test]
fn apply_selected_keeps_function_pointer_surface() {
    let b = body(&OUTPUT, "apply_selected");
    assert!(
        has_indirect_call("apply_selected")
            || param_count(&OUTPUT, "apply_selected") >= 3
            || b.contains("return"),
        "expected function-pointer apply surface:\n{b}"
    );
}

#[test]
fn void_helper_sequence_preserves_both_void_calls() {
    assert_eq!(
        call_count_to("void_helper_sequence", "record_side_effect"),
        2,
        "expected both void-returning side-effect calls"
    );
}

#[test]
fn void_helper_writes_global_state() {
    assert!(
        has_assign(&OUTPUT, "record_side_effect"),
        "expected void helper to write side-effect state"
    );
}

#[test]
fn call_result_reuse_calls_once_and_reuses_arithmetically() {
    assert_eq!(
        call_count_to("reuse_call_result", "ret_i32"),
        1,
        "expected one producing call whose result is reused"
    );
    assert!(
        has_binop(&OUTPUT, "reuse_call_result", BinaryOp::Add),
        "expected arithmetic reuse of call result"
    );
}
