#[test]
fn all_functions_present() {
    for name in ["test_if_in_while", "test_while_in_while", "test_for_with_break",
                  "test_for_with_continue", "test_complex_condition",
                  "test_loop_with_two_exits"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn if_in_while_has_loop_and_if() {
    assert!(has_any_loop(&OUTPUT, "test_if_in_while"), "expected loop");
    assert!(has_if_stmt(&OUTPUT, "test_if_in_while"), "expected if inside loop");
}

#[test]
fn while_in_while_has_nested_loops() {
    let b = body(&OUTPUT, "test_while_in_while");
    let loop_count = b.matches("while").count() + b.matches("for").count();
    assert!(loop_count >= 2, "expected 2+ loop keywords, found {loop_count}:\n{b}");
}

#[test]
fn for_with_break_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_for_with_break"), "expected loop");
}

#[test]
fn for_with_continue_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_for_with_continue"), "expected loop");
}

#[test]
fn complex_condition_has_branches() {
    assert!(has_if_stmt(&OUTPUT, "test_complex_condition")
            || body(&OUTPUT, "test_complex_condition").matches("return").count() >= 2,
            "expected branches");
}

#[test]
fn loop_with_two_exits_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_loop_with_two_exits"), "expected loop");
}
