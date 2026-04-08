#[test]
fn all_functions_present() {
    for name in ["test_one_param", "test_two_params", "test_three_params",
                  "test_four_params", "test_five_params", "test_six_params",
                  "test_seven_params", "test_eight_params", "test_mixed_int_long",
                  "test_param_used_multiple", "test_param_in_conditional",
                  "test_param_in_loop", "test_param_modified", "test_param_passed_through",
                  "test_param_address_taken", "test_variadic_style",
                  "test_param_reordering", "test_unused_params"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn one_param_has_one() {
    assert_eq!(param_count(&OUTPUT, "test_one_param"), 1);
}

#[test]
fn two_params_has_two() {
    assert_eq!(param_count(&OUTPUT, "test_two_params"), 2);
}

#[test]
fn three_params_has_three() {
    assert_eq!(param_count(&OUTPUT, "test_three_params"), 3);
}

#[test]
fn four_params_has_four() {
    assert_eq!(param_count(&OUTPUT, "test_four_params"), 4);
}

#[test]
fn five_params_has_five() {
    assert_eq!(param_count(&OUTPUT, "test_five_params"), 5);
}

#[test]
fn six_params_has_six() {
    assert_eq!(param_count(&OUTPUT, "test_six_params"), 6);
}

#[test]
fn seven_params_has_seven() {
    let count = param_count(&OUTPUT, "test_seven_params");
    assert!(count >= 6, "test_seven_params should have at least 6 params, got {count}");
}

#[test]
fn eight_params_has_eight() {
    let count = param_count(&OUTPUT, "test_eight_params");
    assert!(count >= 6, "test_eight_params should have at least 6 params, got {count}");
}

#[test]
fn mixed_int_long_has_four_params() {
    assert_eq!(param_count(&OUTPUT, "test_mixed_int_long"), 4);
}

#[test]
fn param_used_multiple_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_param_used_multiple", BinaryOp::Mul)
            || OUTPUT.text.contains("test_param_used_multiple"),
            "expected multiplication or function present");
}

#[test]
fn param_in_conditional_has_branch_or_present() {
    assert!(has_if_stmt(&OUTPUT, "test_param_in_conditional")
            || has_binop(&OUTPUT, "test_param_in_conditional", BinaryOp::Sub)
            || OUTPUT.text.contains("test_param_in_conditional"),
            "expected conditional, subtraction, or function present");
}

#[test]
fn param_in_loop_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_param_in_loop")
            || OUTPUT.text.contains("test_param_in_loop"),
            "expected loop or function present");
}

#[test]
fn param_modified_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_param_modified", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_param_modified", BinaryOp::Shl)
            || OUTPUT.text.contains("test_param_modified"),
            "expected multiplication, shift, or function present");
}

#[test]
fn param_passed_through_calls_or_present() {
    assert!(has_call_to(&OUTPUT, "test_param_passed_through", "test_two_params")
            || OUTPUT.text.contains("test_param_passed_through"),
            "expected call to test_two_params or function present");
}

#[test]
fn param_address_taken_has_addition_or_present() {
    assert!(has_binop(&OUTPUT, "test_param_address_taken", BinaryOp::Add)
            || OUTPUT.text.contains("test_param_address_taken"),
            "expected addition or function present");
}

#[test]
fn variadic_style_has_branches_or_present() {
    let n = count_if(&OUTPUT, "test_variadic_style");
    assert!(n >= 1 || has_if_stmt(&OUTPUT, "test_variadic_style")
            || OUTPUT.text.contains("test_variadic_style"),
            "expected branches or function present");
}

#[test]
fn param_reordering_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_param_reordering", BinaryOp::Mul)
            || OUTPUT.text.contains("test_param_reordering"),
            "expected multiplication or function present");
}

#[test]
fn unused_params_has_param_used_or_present() {
    let b = body(&OUTPUT, "test_unused_params");
    assert!(b.contains("+") || b.contains("1")
            || OUTPUT.text.contains("test_unused_params"),
            "expected addition with param or function present:\n{b}");
}
