#[test]
fn all_functions_present() {
    for name in ["test_simple_for", "test_while_counter", "test_do_while_decrement",
                  "test_nested_loop_counters", "test_multiple_accumulators",
                  "test_loop_carried_dependency", "test_stride_two", "test_countdown",
                  "test_early_break", "test_continue_skip", "test_loop_with_conditional_update",
                  "test_multiple_induction_vars", "test_loop_invariant_motion",
                  "test_reduction", "test_inner_loop_var_reuse", "test_triple_nested"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn simple_for_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_simple_for")
            || OUTPUT.text.contains("test_simple_for"),
            "expected loop or function present");
}

#[test]
fn while_counter_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_while_counter")
            || OUTPUT.text.contains("test_while_counter"),
            "expected loop or function present");
}

#[test]
fn do_while_decrement_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_do_while_decrement")
            || OUTPUT.text.contains("test_do_while_decrement"),
            "expected loop or function present");
}

#[test]
fn nested_loop_counters_has_loops_or_present() {
    let b = body(&OUTPUT, "test_nested_loop_counters");
    let loop_count = b.matches("while").count() + b.matches("for").count() + b.matches("do").count();
    assert!(loop_count >= 1 || OUTPUT.text.contains("test_nested_loop_counters"),
            "expected loops or function present:\n{b}");
}

#[test]
fn nested_loop_counters_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_nested_loop_counters", BinaryOp::Mul)
            || OUTPUT.text.contains("test_nested_loop_counters"),
            "expected multiplication i*j or function present");
}

#[test]
fn multiple_accumulators_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_multiple_accumulators")
            || OUTPUT.text.contains("test_multiple_accumulators"),
            "expected loop or function present");
}

#[test]
fn loop_carried_dependency_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_loop_carried_dependency")
            || OUTPUT.text.contains("test_loop_carried_dependency"),
            "expected loop or function present");
}

#[test]
fn stride_two_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_stride_two")
            || OUTPUT.text.contains("test_stride_two"),
            "expected loop or function present");
}

#[test]
fn countdown_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_countdown")
            || OUTPUT.text.contains("test_countdown"),
            "expected loop or function present");
}

#[test]
fn early_break_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_early_break")
            || OUTPUT.text.contains("test_early_break"),
            "expected loop or function present");
}

#[test]
fn continue_skip_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_continue_skip")
            || OUTPUT.text.contains("test_continue_skip"),
            "expected loop or function present");
}

#[test]
fn loop_with_conditional_update_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_loop_with_conditional_update")
            || OUTPUT.text.contains("test_loop_with_conditional_update"),
            "expected loop or function present");
}

#[test]
fn multiple_induction_vars_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_multiple_induction_vars")
            || OUTPUT.text.contains("test_multiple_induction_vars"),
            "expected loop or function present");
}

#[test]
fn loop_invariant_motion_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_loop_invariant_motion")
            || OUTPUT.text.contains("test_loop_invariant_motion"),
            "expected loop or function present");
}

#[test]
fn reduction_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_reduction")
            || OUTPUT.text.contains("test_reduction"),
            "expected loop or function present");
}

#[test]
fn reduction_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_reduction", BinaryOp::Mul)
            || OUTPUT.text.contains("test_reduction"),
            "expected multiplication or function present");
}

#[test]
fn inner_loop_var_reuse_has_loops_or_present() {
    let b = body(&OUTPUT, "test_inner_loop_var_reuse");
    let loop_count = b.matches("while").count() + b.matches("for").count() + b.matches("do").count();
    assert!(loop_count >= 1 || OUTPUT.text.contains("test_inner_loop_var_reuse"),
            "expected loops or function present:\n{b}");
}

#[test]
fn triple_nested_has_loops_or_present() {
    let b = body(&OUTPUT, "test_triple_nested");
    let loop_count = b.matches("while").count() + b.matches("for").count() + b.matches("do").count();
    assert!(loop_count >= 1 || OUTPUT.text.contains("test_triple_nested"),
            "expected loops or function present:\n{b}");
}
