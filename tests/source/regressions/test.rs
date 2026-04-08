#[test]
fn all_functions_present() {
    for name in ["add_op", "xor_op", "guard", "test_early_return_ladder",
                  "test_nested_if_chain", "dispatch", "test_indirect_dispatch",
                  "test_switch_fallthrough", "test_nested_loop_break_continue",
                  "test_struct_pointer_alias"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn regression_early_return_ladder() {
    let b = body(&OUTPUT, "test_early_return_ladder");
    assert!(b.matches("return").count() >= 3, "expected 3+ returns:\n{b}");
}

#[test]
fn regression_nested_if_chain() {
    assert!(count_if(&OUTPUT, "test_nested_if_chain") >= 3, "expected 3+ ifs");
}

#[test]
fn regression_switch_fallthrough() {
    assert!(has_switch(&OUTPUT, "test_switch_fallthrough"), "expected switch");
    let b = body(&OUTPUT, "test_switch_fallthrough");
    assert!(b.matches("case ").count() >= 3, "expected 3+ cases:\n{b}");
}

#[test]
fn regression_nested_loop_break_continue() {
    let b = body(&OUTPUT, "test_nested_loop_break_continue");
    assert!(!b.contains("goto test_nested_loop_break_continue;"),
            "self-goto indicates failed loop structuring:\n{b}");
}

#[test]
fn regression_struct_pointer_alias() {
    assert!(has_field_access(&OUTPUT, "test_struct_pointer_alias", "left"),
            "expected field access to 'left'");
}

#[test]
fn regression_dispatch_has_switch_and_loop() {
    assert!(has_any_loop(&OUTPUT, "dispatch"), "expected dispatcher loop");
    assert!(has_switch(&OUTPUT, "dispatch"), "expected dispatcher switch");
}

#[test]
fn regression_dispatch_has_indirect_call() {
    assert!(has_deref(&OUTPUT, "dispatch"),
            "expected indirect call through recovered dispatch target");
}

#[test]
fn regression_indirect_dispatch_calls_dispatch() {
    assert!(has_call_to(&OUTPUT, "test_indirect_dispatch", "dispatch"),
            "expected wrapper to call dispatch");
}
