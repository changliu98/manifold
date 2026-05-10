#[test]
fn all_functions_present() {
    for name in [
        "multi_continue_loop",
        "nested_loop_early_return",
        "switch_negative_default_loop",
        "post_test_guard_loop",
        "if_switch_composition",
    ] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn multi_continue_loop_has_loop_and_multiple_branches() {
    let b = body(&OUTPUT, "multi_continue_loop");
    assert!(
        has_any_loop(&OUTPUT, "multi_continue_loop"),
        "expected loop:\n{b}"
    );
    assert!(
        count_if(&OUTPUT, "multi_continue_loop") >= 1
            || has_continue_stmt(&OUTPUT, "multi_continue_loop")
            || b.contains("goto "),
        "expected recovered branch, continue, or goto edge:\n{b}"
    );
}

#[test]
fn multi_continue_loop_preserves_exit_side_effect() {
    let b = body(&OUTPUT, "multi_continue_loop");
    assert!(
        b.contains("sink") && b.contains("return"),
        "expected loop result side effect and return:\n{b}"
    );
}

#[test]
fn nested_loop_early_return_has_nested_loops() {
    assert!(
        count_loops(&OUTPUT, "nested_loop_early_return") >= 2,
        "expected nested loops"
    );
}

#[test]
fn nested_loop_early_return_keeps_explicit_return() {
    let b = body(&OUTPUT, "nested_loop_early_return");
    assert!(
        b.contains("return"),
        "expected explicit return from nested-loop search:\n{b}"
    );
}

#[test]
fn switch_negative_default_loop_has_loop_and_dispatch() {
    let b = body(&OUTPUT, "switch_negative_default_loop");
    assert!(
        has_any_loop(&OUTPUT, "switch_negative_default_loop"),
        "expected loop:\n{b}"
    );
    assert!(
        has_switch(&OUTPUT, "switch_negative_default_loop")
            || count_if(&OUTPUT, "switch_negative_default_loop") >= 1
            || b.contains("case ")
            || b.contains("continue")
            || b.contains("goto "),
        "expected switch, branch, or goto dispatch:\n{b}"
    );
}

#[test]
fn switch_negative_default_loop_keeps_result_return() {
    let b = body(&OUTPUT, "switch_negative_default_loop");
    assert!(
        b.contains("return"),
        "expected loop dispatch result return:\n{b}"
    );
}

#[test]
fn post_test_guard_loop_has_loop_and_guard() {
    assert!(
        has_any_loop(&OUTPUT, "post_test_guard_loop"),
        "expected post-test loop"
    );
    assert!(
        has_if_stmt(&OUTPUT, "post_test_guard_loop"),
        "expected entry or break guard"
    );
}

#[test]
fn post_test_guard_loop_has_explicit_return() {
    let b = body(&OUTPUT, "post_test_guard_loop");
    assert!(
        b.contains("return"),
        "expected explicit post-test loop return:\n{b}"
    );
}

#[test]
fn if_switch_composition_has_if_and_dispatch() {
    assert!(
        has_if_stmt(&OUTPUT, "if_switch_composition"),
        "expected outer if composition"
    );
    assert!(
        has_switch(&OUTPUT, "if_switch_composition")
            || count_if(&OUTPUT, "if_switch_composition") >= 3,
        "expected switch or equivalent dispatch"
    );
}

#[test]
fn if_switch_composition_has_explicit_return() {
    let b = body(&OUTPUT, "if_switch_composition");
    assert!(
        b.contains("return"),
        "expected explicit if/switch result return:\n{b}"
    );
}
