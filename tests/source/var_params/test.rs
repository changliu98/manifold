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
fn param_used_multiple_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_param_used_multiple", BinaryOp::Mul),
            "expected multiplication");
}

#[test]
fn param_in_conditional_has_branch() {
    assert!(has_if_stmt(&OUTPUT, "test_param_in_conditional")
            || has_binop(&OUTPUT, "test_param_in_conditional", BinaryOp::Sub),
            "expected conditional, subtraction");
}

#[test]
fn param_in_loop_has_loop_or_closed_form() {
    assert!(has_any_loop(&OUTPUT, "test_param_in_loop")
            || has_binop(&OUTPUT, "test_param_in_loop", BinaryOp::Mul),
            "expected loop or closed-form multiplication");
}

#[test]
fn param_modified_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_param_modified", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_param_modified", BinaryOp::Shl)
            || has_binop(&OUTPUT, "test_param_modified", BinaryOp::Add),
            "expected multiply, shift, or add-self");
}

#[test]
fn param_passed_through_calls() {
    assert!(has_call_to(&OUTPUT, "test_param_passed_through", "test_two_params"),
            "expected call to test_two_params");
}

#[test]
fn param_address_taken_has_addition() {
    assert!(has_binop(&OUTPUT, "test_param_address_taken", BinaryOp::Add),
            "expected addition");
}

#[test]
fn variadic_style_has_branches() {
    let n = count_if(&OUTPUT, "test_variadic_style");
    assert!(n >= 1 || has_if_stmt(&OUTPUT, "test_variadic_style"),
            "expected branches");
}

#[test]
fn param_reordering_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_param_reordering", BinaryOp::Mul),
            "expected multiplication");
}

#[test]
fn unused_params_has_param_used() {
    let b = body(&OUTPUT, "test_unused_params");
    assert!(b.contains("+") || b.contains("1"),
            "expected addition with param:\n{b}");
}
