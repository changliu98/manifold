#[test]
fn all_functions_present() {
    for name in ["test_six_args", "test_seven_args", "test_mixed_types",
                  "test_pass_through", "test_void_return", "test_chain"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn six_args_has_params() {
    assert!(has_binop(&OUTPUT, "test_six_args", BinaryOp::Add), "expected addition of params");
}

#[test]
fn pass_through_calls_six_args() {
    assert!(has_call_to(&OUTPUT, "test_pass_through", "test_six_args"),
            "expected call to test_six_args");
}

#[test]
fn chain_calls_both() {
    assert!(has_call_to(&OUTPUT, "test_chain", "test_void_return"),
            "expected call to test_void_return");
    assert!(has_call_to(&OUTPUT, "test_chain", "test_six_args"),
            "expected call to test_six_args");
}

#[test]
fn seven_args_present_with_params() {
    let b = body(&OUTPUT, "test_seven_args");
    assert!(b.contains("return"), "expected return:\n{b}");
}

#[test]
fn mixed_types_has_multiple_additive_steps() {
    let b = body(&OUTPUT, "test_mixed_types");
    assert!(b.matches("+").count() >= 3, "expected additive combination across mixed-width args:\n{b}");
}

#[test]
fn void_return_returns_zero() {
    let b = body(&OUTPUT, "test_void_return");
    assert!(b.contains("return 0;"), "expected explicit zero return for helper thunk:\n{b}");
}
