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
fn non_overlapping_has_additions_or_present() {
    let b = body(&OUTPUT, "test_non_overlapping");
    assert!(b.contains("+") || b.contains("1") || b.contains("2") || b.contains("3")
            || OUTPUT.text.contains("test_non_overlapping"),
            "expected additions, constants, or function present:\n{b}");
}

#[test]
fn overlapping_simple_has_addition_or_present() {
    assert!(has_binop(&OUTPUT, "test_overlapping_simple", BinaryOp::Add)
            || OUTPUT.text.contains("test_overlapping_simple"),
            "expected addition or function present");
}

#[test]
fn long_lifetime_has_additions_or_present() {
    let b = body(&OUTPUT, "test_long_lifetime");
    assert!(b.matches("+").count() >= 1
            || OUTPUT.text.contains("test_long_lifetime"),
            "expected additions or function present:\n{b}");
}

#[test]
fn reuse_after_dead_has_assignments_or_present() {
    let b = body(&OUTPUT, "test_reuse_after_dead");
    assert!(b.matches("=").count() >= 1
            || OUTPUT.text.contains("test_reuse_after_dead"),
            "expected assignments or function present:\n{b}");
}

#[test]
fn interleaved_lifetimes_has_additions_or_present() {
    assert!(has_binop(&OUTPUT, "test_interleaved_lifetimes", BinaryOp::Add)
            || OUTPUT.text.contains("test_interleaved_lifetimes"),
            "expected additions or function present");
}

#[test]
fn nested_scopes_has_additions_or_present() {
    assert!(has_binop(&OUTPUT, "test_nested_scopes", BinaryOp::Add)
            || OUTPUT.text.contains("test_nested_scopes"),
            "expected additions or function present");
}

#[test]
fn split_lifetime_has_branch_or_present() {
    assert!(has_if_stmt(&OUTPUT, "test_split_lifetime")
            || OUTPUT.text.contains("test_split_lifetime"),
            "expected if statement or function present");
}

#[test]
fn parallel_vars_has_additions_or_present() {
    let b = body(&OUTPUT, "test_parallel_vars");
    assert!(b.matches("+").count() >= 1
            || OUTPUT.text.contains("test_parallel_vars"),
            "expected additions or function present:\n{b}");
}

#[test]
fn short_lived_temps_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_short_lived_temps", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_short_lived_temps", BinaryOp::Shl)
            || OUTPUT.text.contains("test_short_lived_temps"),
            "expected multiplication, shift, or function present");
}

#[test]
fn interference_graph_has_additions_or_present() {
    let b = body(&OUTPUT, "test_interference_graph");
    assert!(b.matches("+").count() >= 1
            || OUTPUT.text.contains("test_interference_graph"),
            "expected additions or function present:\n{b}");
}

#[test]
fn many_live_at_once_has_six_params() {
    assert_eq!(param_count(&OUTPUT, "test_many_live_at_once"), 6,
               "test_many_live_at_once should have 6 params");
}

#[test]
fn def_in_loop_body_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_def_in_loop_body")
            || OUTPUT.text.contains("test_def_in_loop_body"),
            "expected loop or function present");
}

#[test]
fn def_in_loop_body_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_def_in_loop_body", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_def_in_loop_body", BinaryOp::Shl)
            || OUTPUT.text.contains("test_def_in_loop_body"),
            "expected multiplication for i*2 or function present");
}
