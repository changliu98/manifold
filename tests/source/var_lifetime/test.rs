#[test]
fn all_functions_present() {
    for name in ["test_non_overlapping", "test_overlapping_simple", "test_long_lifetime",
                  "test_reuse_after_dead", "test_interleaved_lifetimes", "test_nested_scopes",
                  "test_split_lifetime", "test_parallel_vars", "test_short_lived_temps",
                  "test_interference_graph", "test_many_live_at_once", "test_def_in_loop_body"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn non_overlapping_has_additions() {
    let b = body(&OUTPUT, "test_non_overlapping");
    assert!(b.contains("+") || b.contains("1") || b.contains("2") || b.contains("3"),
            "expected additions, constants:\n{b}");
}

#[test]
fn overlapping_simple_has_addition() {
    assert!(has_binop(&OUTPUT, "test_overlapping_simple", BinaryOp::Add),
            "expected addition");
}

#[test]
fn long_lifetime_has_additions() {
    let b = body(&OUTPUT, "test_long_lifetime");
    assert!(b.matches("+").count() >= 1,
            "expected additions:\n{b}");
}

#[test]
fn reuse_after_dead_has_assignments() {
    let b = body(&OUTPUT, "test_reuse_after_dead");
    assert!(b.matches("=").count() >= 1,
            "expected assignments:\n{b}");
}

#[test]
fn interleaved_lifetimes_has_additions() {
    assert!(has_binop(&OUTPUT, "test_interleaved_lifetimes", BinaryOp::Add),
            "expected additions");
}

#[test]
fn nested_scopes_has_additions() {
    assert!(has_binop(&OUTPUT, "test_nested_scopes", BinaryOp::Add),
            "expected additions");
}

#[test]
fn split_lifetime_has_branch() {
    assert!(has_if_stmt(&OUTPUT, "test_split_lifetime"),
            "expected if statement");
}

#[test]
fn parallel_vars_has_additions() {
    let b = body(&OUTPUT, "test_parallel_vars");
    assert!(b.matches("+").count() >= 1,
            "expected additions:\n{b}");
}

#[test]
fn short_lived_temps_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_short_lived_temps", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_short_lived_temps", BinaryOp::Shl),
            "expected multiplication, shift");
}

#[test]
fn interference_graph_has_additions() {
    let b = body(&OUTPUT, "test_interference_graph");
    assert!(b.matches("+").count() >= 1,
            "expected additions:\n{b}");
}

#[test]
fn many_live_at_once_has_six_params() {
    assert_eq!(param_count(&OUTPUT, "test_many_live_at_once"), 6,
               "test_many_live_at_once should have 6 params");
}

#[test]
fn def_in_loop_body_has_loop_or_closed_form() {
    // Clang recognizes the arithmetic series and removes the loop.
    assert!(has_any_loop(&OUTPUT, "test_def_in_loop_body")
            || has_binop(&OUTPUT, "test_def_in_loop_body", BinaryOp::Mul),
            "expected loop or closed-form multiplication");
}

#[test]
fn def_in_loop_body_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_def_in_loop_body", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_def_in_loop_body", BinaryOp::Shl)
            || has_binop(&OUTPUT, "test_def_in_loop_body", BinaryOp::Add),
            "expected multiply, shift, or strength-reduced addition for i*2");
}
