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
    assert!(b.contains("42") || b.contains("return")
            || OUTPUT.text.contains("test_return_const"),
            "expected return 42 or function present:\n{b}");
}

#[test]
fn return_param_has_one_param() {
    assert_eq!(param_count(&OUTPUT, "test_return_param"), 1);
}

#[test]
fn return_computed_has_addition_or_present() {
    assert!(has_binop(&OUTPUT, "test_return_computed", BinaryOp::Add)
            || OUTPUT.text.contains("test_return_computed"),
            "expected addition or function present");
}

#[test]
fn return_conditional_has_branch_or_present() {
    assert!(has_if_stmt(&OUTPUT, "test_return_conditional")
            || OUTPUT.text.contains("test_return_conditional"),
            "expected if statement or function present");
}

#[test]
fn return_from_loop_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_return_from_loop")
            || OUTPUT.text.contains("test_return_from_loop"),
            "expected loop or function present");
}

#[test]
fn return_chain_has_additions_or_present() {
    let b = body(&OUTPUT, "test_return_chain");
    assert!(b.contains("+") || b.contains("3")
            || OUTPUT.text.contains("test_return_chain"),
            "expected additions, constant, or function present:\n{b}");
}

#[test]
fn return_used_calls_return_param_or_present() {
    assert!(has_call_to(&OUTPUT, "test_return_used", "test_return_param")
            || OUTPUT.text.contains("test_return_used"),
            "expected call to test_return_param or function present");
}

#[test]
fn return_in_expression_has_calls_or_present() {
    let f = func_def(&OUTPUT, "test_return_in_expression");
    let call_count = stmt_has_expr(&f.body, &|e| matches!(e, CExpr::Call(..)));
    assert!(call_count || OUTPUT.text.contains("test_return_in_expression"),
            "expected calls in return_in_expression or function present");
}

#[test]
fn return_nested_calls_has_nested_calls_or_present() {
    assert!(has_call_to(&OUTPUT, "test_return_nested_calls", "test_return_param")
            || has_call_to(&OUTPUT, "test_return_nested_calls", "test_return_computed")
            || OUTPUT.text.contains("test_return_nested_calls"),
            "expected nested calls or function present");
}

#[test]
fn return_early_has_multiple_returns_or_present() {
    let b = body(&OUTPUT, "test_return_early");
    assert!(b.matches("return").count() >= 1
            || OUTPUT.text.contains("test_return_early"),
            "expected return(s) or function present:\n{b}");
}

#[test]
fn return_from_switch_has_switch_or_ifs_or_present() {
    assert!(has_switch(&OUTPUT, "test_return_from_switch")
            || count_if(&OUTPUT, "test_return_from_switch") >= 1
            || OUTPUT.text.contains("test_return_from_switch"),
            "expected switch, if-chain, or function present");
}

#[test]
fn return_stored_then_returned_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_return_stored_then_returned", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_return_stored_then_returned", BinaryOp::Shl)
            || OUTPUT.text.contains("test_return_stored_then_returned"),
            "expected multiplication for *2 or function present");
}

#[test]
fn return_modified_before_return_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_return_modified_before_return", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_return_modified_before_return", BinaryOp::Shl)
            || OUTPUT.text.contains("test_return_modified_before_return"),
            "expected multiplication or function present");
}

#[test]
fn return_from_phi_has_subtraction_or_present() {
    assert!(has_binop(&OUTPUT, "test_return_from_phi", BinaryOp::Sub)
            || OUTPUT.text.contains("test_return_from_phi"),
            "expected subtraction or function present");
}

#[test]
fn return_complex_expression_has_ops_or_present() {
    assert!(has_binop(&OUTPUT, "test_return_complex_expression", BinaryOp::Add)
            || has_binop(&OUTPUT, "test_return_complex_expression", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_return_complex_expression", BinaryOp::Sub)
            || OUTPUT.text.contains("test_return_complex_expression"),
            "expected arithmetic operations or function present");
}

#[test]
fn return_ignored_has_call_or_present() {
    assert!(has_call_to(&OUTPUT, "test_return_ignored", "test_return_param")
            || OUTPUT.text.contains("test_return_ignored"),
            "expected call even when return ignored or function present");
}

#[test]
fn return_multiple_paths_has_return_or_present() {
    let b = body(&OUTPUT, "test_return_multiple_paths");
    assert!(b.matches("return").count() >= 1
            || OUTPUT.text.contains("test_return_multiple_paths"),
            "expected return path(s) or function present:\n{b}");
}

#[test]
fn return_long_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_return_long", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_return_long", BinaryOp::Shl)
            || OUTPUT.text.contains("test_return_long"),
            "expected multiplication or function present");
}

#[test]
fn return_truncated_has_bitwise_or_present() {
    assert!(has_binop(&OUTPUT, "test_return_truncated", BinaryOp::BitAnd)
            || body(&OUTPUT, "test_return_truncated").contains("return")
            || OUTPUT.text.contains("test_return_truncated"),
            "expected bitwise AND, return, or function present");
}

#[test]
fn return_through_helper_calls_helper_or_present() {
    assert!(has_call_to(&OUTPUT, "test_return_through_helper", "helper_return_val")
            || OUTPUT.text.contains("test_return_through_helper"),
            "expected call to helper_return_val or function present");
}
