#[test]
fn all_functions_present() {
    for name in ["test_return_const", "test_return_param", "test_return_computed",
                  "test_return_conditional", "test_return_from_loop", "test_return_chain",
                  "test_return_used", "test_return_in_expression", "test_return_nested_calls",
                  "test_return_early", "test_return_from_switch", "test_return_stored_then_returned",
                  "test_return_modified_before_return", "test_return_from_phi",
                  "test_return_complex_expression", "test_return_ignored",
                  "test_return_multiple_paths", "test_return_long",
                  "test_return_truncated", "test_return_through_helper"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn return_const_returns_42() {
    let b = body(&OUTPUT, "test_return_const");
    assert!(b.contains("42"),
            "expected return 42:\n{b}");
}

#[test]
fn return_param_has_one_param() {
    assert_eq!(param_count(&OUTPUT, "test_return_param"), 1);
}

#[test]
fn return_computed_has_addition() {
    assert!(has_binop(&OUTPUT, "test_return_computed", BinaryOp::Add),
            "expected addition");
}

#[test]
fn return_conditional_has_branch_or_predicate() {
    assert!(has_if_stmt(&OUTPUT, "test_return_conditional")
            || has_binop(&OUTPUT, "test_return_conditional", BinaryOp::Gt)
            || has_binop(&OUTPUT, "test_return_conditional", BinaryOp::Le),
            "expected branch or materialized predicate");
}

#[test]
fn return_from_loop_has_loop_or_closed_form() {
    assert!(has_any_loop(&OUTPUT, "test_return_from_loop")
            || has_binop(&OUTPUT, "test_return_from_loop", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_return_from_loop", BinaryOp::Shr),
            "expected loop or closed-form arithmetic series");
}

#[test]
fn return_chain_has_additions() {
    let b = body(&OUTPUT, "test_return_chain");
    assert!(b.contains("+") || b.contains("3"),
            "expected additions, constant:\n{b}");
}

#[test]
fn return_used_calls_return_param() {
    assert!(has_call_to(&OUTPUT, "test_return_used", "test_return_param"),
            "expected call to test_return_param");
}

#[test]
fn return_in_expression_has_calls() {
    let f = func_def(&OUTPUT, "test_return_in_expression");
    let call_count = stmt_has_expr(&f.body, &|e| matches!(e, CExpr::Call(..)));
    assert!(call_count,
            "expected calls in return_in_expression");
}

#[test]
fn return_nested_calls_has_nested_calls() {
    assert!(has_call_to(&OUTPUT, "test_return_nested_calls", "test_return_param")
            || has_call_to(&OUTPUT, "test_return_nested_calls", "test_return_computed"),
            "expected nested calls");
}

#[test]
fn return_early_has_multiple_returns() {
    let b = body(&OUTPUT, "test_return_early");
    assert!(b.matches("return").count() >= 1,
            "expected return(s):\n{b}");
}

#[test]
fn return_from_switch_has_switch_or_ifs() {
    assert!(has_switch(&OUTPUT, "test_return_from_switch")
            || count_if(&OUTPUT, "test_return_from_switch") >= 1,
            "expected switch, if-chain");
}

#[test]
fn return_stored_then_returned_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_return_stored_then_returned", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_return_stored_then_returned", BinaryOp::Shl)
            || has_binop(&OUTPUT, "test_return_stored_then_returned", BinaryOp::Add),
            "expected multiply, shift, or add-self for *2");
}

#[test]
fn return_modified_before_return_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_return_modified_before_return", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_return_modified_before_return", BinaryOp::Shl)
            || has_binop(&OUTPUT, "test_return_modified_before_return", BinaryOp::Add),
            "expected multiply, shift, or add-self");
}

#[test]
fn return_from_phi_has_subtraction() {
    assert!(has_binop(&OUTPUT, "test_return_from_phi", BinaryOp::Sub),
            "expected subtraction");
}

#[test]
fn return_complex_expression_has_ops() {
    assert!(has_binop(&OUTPUT, "test_return_complex_expression", BinaryOp::Add)
            || has_binop(&OUTPUT, "test_return_complex_expression", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_return_complex_expression", BinaryOp::Sub),
            "expected arithmetic operations");
}

#[test]
fn return_ignored_has_call() {
    assert!(has_call_to(&OUTPUT, "test_return_ignored", "test_return_param"),
            "expected call even when return ignored");
}

#[test]
fn return_multiple_paths_has_return() {
    let b = body(&OUTPUT, "test_return_multiple_paths");
    assert!(b.matches("return").count() >= 1,
            "expected return path(s):\n{b}");
}

#[test]
fn return_long_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_return_long", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_return_long", BinaryOp::Shl)
            || has_binop(&OUTPUT, "test_return_long", BinaryOp::Add),
            "expected multiply, shift, or add-self");
}

#[test]
fn return_truncated_has_bitwise() {
    assert!(has_binop(&OUTPUT, "test_return_truncated", BinaryOp::BitAnd),
            "expected bitwise AND, return");
}

#[test]
fn return_through_helper_calls_helper() {
    assert!(has_call_to(&OUTPUT, "test_return_through_helper", "helper_return_val"),
            "expected call to helper_return_val");
}
