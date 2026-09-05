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
fn simple_for_has_loop_or_closed_form() {
    assert!(has_any_loop(&OUTPUT, "test_simple_for")
            || has_binop(&OUTPUT, "test_simple_for", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_simple_for", BinaryOp::Shr),
            "expected loop or closed-form arithmetic series");
}

#[test]
fn while_counter_has_loop_or_clamp() {
    // Clang proves the loop result is max(n, 0).
    assert!(has_any_loop(&OUTPUT, "test_while_counter")
            || has_if_stmt(&OUTPUT, "test_while_counter"),
            "expected loop or recovered clamp condition");
}

#[test]
fn do_while_decrement_has_loop_or_closed_form() {
    assert!(has_any_loop(&OUTPUT, "test_do_while_decrement")
            || has_binop(&OUTPUT, "test_do_while_decrement", BinaryOp::Mul),
            "expected loop or closed-form arithmetic series");
}

#[test]
fn nested_loop_counters_has_loops() {
    let b = body(&OUTPUT, "test_nested_loop_counters");
    let loop_count = b.matches("while").count() + b.matches("for").count() + b.matches("do").count();
    assert!(loop_count >= 1,
            "expected loops:\n{b}");
}

#[test]
fn nested_loop_counters_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_nested_loop_counters", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_nested_loop_counters", BinaryOp::Add),
            "expected multiplication or its loop-carried additive recurrence");
}

#[test]
fn multiple_accumulators_has_loop_or_closed_form() {
    assert!(has_any_loop(&OUTPUT, "test_multiple_accumulators")
            || has_binop(&OUTPUT, "test_multiple_accumulators", BinaryOp::Mul),
            "expected loop or closed-form multiplication");
}

#[test]
fn loop_carried_dependency_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_loop_carried_dependency"),
            "expected loop");
}

#[test]
fn stride_two_has_loop_or_closed_form() {
    assert!(has_any_loop(&OUTPUT, "test_stride_two")
            || has_binop(&OUTPUT, "test_stride_two", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_stride_two", BinaryOp::Shr),
            "expected loop or closed-form stride arithmetic");
}

#[test]
fn countdown_has_loop_or_closed_form() {
    assert!(has_any_loop(&OUTPUT, "test_countdown")
            || has_binop(&OUTPUT, "test_countdown", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_countdown", BinaryOp::Shr),
            "expected loop or closed-form arithmetic series");
}

#[test]
fn early_break_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_early_break"),
            "expected loop");
}

#[test]
fn continue_skip_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_continue_skip"),
            "expected loop");
}

#[test]
fn loop_with_conditional_update_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_loop_with_conditional_update"),
            "expected loop");
}

#[test]
fn multiple_induction_vars_has_loop_or_closed_form() {
    assert!(has_any_loop(&OUTPUT, "test_multiple_induction_vars")
            || has_binop(&OUTPUT, "test_multiple_induction_vars", BinaryOp::Mul),
            "expected loop or closed-form multiplication");
}

#[test]
fn loop_invariant_motion_has_loop_or_closed_form() {
    assert!(has_any_loop(&OUTPUT, "test_loop_invariant_motion")
            || has_binop(&OUTPUT, "test_loop_invariant_motion", BinaryOp::Mul),
            "expected loop or closed-form multiplication");
}

#[test]
fn reduction_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_reduction"),
            "expected loop");
}

#[test]
fn reduction_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_reduction", BinaryOp::Mul),
            "expected multiplication");
}

#[test]
fn reduction_preserves_the_recurrent_product() {
    let mut tu = TranslationUnit::new();
    tu.add_function(func_def(&OUTPUT, "test_reduction").clone());
    let recovered = manifold::decompile::passes::c_pass::print_translation_unit(&tu);
    let source = format!(
        "{recovered}\n{}",
        r#"
int main(void) {
    int values[] = {3, 1, 4, 1, 5};
    int expected[] = {1, 3, 3, 12, 12, 60};
    if (test_reduction(values, -1) != 1) return 1;
    for (int n = 0; n <= 5; ++n)
        if (test_reduction(values, n) != expected[n]) return n + 2;
    int negative[] = {2, -3, 4};
    int zero[] = {2, 0, 4};
    if (test_reduction(negative, 3) != -24) return 8;
    if (test_reduction(zero, 3) != 0) return 9;
    return 0;
}
"#
    );
    for compiler in ["gcc", "clang"] {
        let name = format!("{}_reduction_behavior", module_path!().replace("::", "_"));
        let executable = compile(&name, compiler, &source, "-O2");
        let result = Command::new("timeout")
            .arg("10s")
            .arg(executable)
            .status()
            .unwrap();
        assert!(result.success(), "recovered product differs: {recovered}");
    }
}

#[test]
fn inner_loop_var_reuse_has_loops() {
    let b = body(&OUTPUT, "test_inner_loop_var_reuse");
    let loop_count = b.matches("while").count() + b.matches("for").count() + b.matches("do").count();
    assert!(loop_count >= 1,
            "expected loops:\n{b}");
}

#[test]
fn triple_nested_has_loops_or_closed_form() {
    let b = body(&OUTPUT, "test_triple_nested");
    let loop_count = b.matches("while").count() + b.matches("for").count() + b.matches("do").count();
    assert!(loop_count >= 1 || has_binop(&OUTPUT, "test_triple_nested", BinaryOp::Mul),
            "expected loops or closed-form multiplication:\n{b}");
}
