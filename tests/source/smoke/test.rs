#[test]
fn all_functions_present() {
    for name in ["helper_add", "test_if_no_else", "test_while_loop",
                  "test_for_loop", "test_do_while", "test_call", "test_switch"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn if_no_else_has_if() {
    assert!(has_if_stmt(&OUTPUT, "test_if_no_else"), "expected if");
}

#[test]
fn while_loop_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_while_loop"), "expected loop");
}

#[test]
fn for_loop_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_for_loop"), "expected loop");
}

#[test]
fn do_while_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_do_while"), "expected loop");
}

#[test]
fn call_references_helper() {
    assert!(has_call_to(&OUTPUT, "test_call", "helper_add"), "expected call to helper_add");
}

#[test]
fn switch_has_cases() {
    assert!(has_switch(&OUTPUT, "test_switch") || count_if(&OUTPUT, "test_switch") >= 3,
            "expected switch or if-chain");
}
