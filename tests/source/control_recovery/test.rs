#[test]
fn all_functions_present() {
    for name in [
        "if_else_basic",
        "if_else_ladder",
        "nested_if_else",
        "guard_chain",
        "while_counter",
        "while_break_continue",
        "do_while_increment",
        "for_accumulate",
        "for_break_on_target",
        "for_continue_skip_negative",
        "nested_for_sum",
        "mixed_loop_nesting",
        "infinite_loop_break",
        "loop_multi_exit",
        "switch_dense",
        "switch_sparse",
        "switch_fallthrough",
        "switch_in_loop",
        "switch_under_if",
        "if_inside_switch",
        "complex_control_mesh",
    ] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn if_else_basic_has_if() {
    assert!(has_if_stmt(&OUTPUT, "if_else_basic"), "expected if statement");
}

#[test]
fn if_else_ladder_has_multiple_branches() {
    assert!(count_if(&OUTPUT, "if_else_ladder") >= 3
            || has_switch(&OUTPUT, "if_else_ladder"),
            "expected if-else ladder");
}

#[test]
fn nested_if_else_has_nested_branches() {
    assert!(count_if(&OUTPUT, "nested_if_else") >= 2, "expected nested if statements");
}

#[test]
fn guard_chain_has_many_guards() {
    assert!(count_if(&OUTPUT, "guard_chain") >= 3, "expected multiple guard checks");
}

#[test]
fn guard_chain_has_many_returns() {
    let b = body(&OUTPUT, "guard_chain");
    assert!(b.matches("return").count() >= 4, "expected multiple early returns:\n{b}");
}

#[test]
fn while_counter_has_loop() {
    assert!(has_any_loop(&OUTPUT, "while_counter"), "expected while loop");
}

#[test]
fn while_break_continue_has_loop_and_conditions() {
    assert!(has_any_loop(&OUTPUT, "while_break_continue"), "expected loop");
    assert!(has_if_stmt(&OUTPUT, "while_break_continue")
            || has_break_stmt(&OUTPUT, "while_break_continue")
            || has_continue_stmt(&OUTPUT, "while_break_continue"),
            "expected break/continue-style branching");
}

#[test]
fn do_while_increment_has_loop() {
    assert!(has_any_loop(&OUTPUT, "do_while_increment"), "expected loop");
}

#[test]
fn for_accumulate_has_loop() {
    assert!(has_any_loop(&OUTPUT, "for_accumulate"), "expected loop");
}

#[test]
fn for_break_on_target_has_loop_and_if() {
    assert!(has_any_loop(&OUTPUT, "for_break_on_target"), "expected loop");
    assert!(has_if_stmt(&OUTPUT, "for_break_on_target"), "expected branch for target match");
}

#[test]
fn for_continue_skip_negative_has_loop() {
    assert!(has_any_loop(&OUTPUT, "for_continue_skip_negative"), "expected loop");
}

#[test]
fn nested_for_sum_has_nested_loops() {
    assert!(count_loops(&OUTPUT, "nested_for_sum") >= 2, "expected nested loops");
}

#[test]
fn mixed_loop_nesting_has_nested_loops() {
    assert!(count_loops(&OUTPUT, "mixed_loop_nesting") >= 2, "expected mixed nested loops");
}

#[test]
fn infinite_loop_break_has_loop_and_if() {
    assert!(has_any_loop(&OUTPUT, "infinite_loop_break"), "expected loop");
    assert!(has_if_stmt(&OUTPUT, "infinite_loop_break"), "expected break condition");
}

#[test]
fn loop_multi_exit_has_explicit_exit() {
    let b = body(&OUTPUT, "loop_multi_exit");
    assert!(b.contains("return"), "expected explicit exit:\n{b}");
}

#[test]
fn switch_dense_has_dispatch() {
    let b = body(&OUTPUT, "switch_dense");
    assert!(has_switch(&OUTPUT, "switch_dense")
            || count_if(&OUTPUT, "switch_dense") >= 2
            || b.contains("return"),
            "expected dispatch-like control flow:\n{b}");
}

#[test]
fn switch_sparse_has_dispatch() {
    assert!(has_switch(&OUTPUT, "switch_sparse")
            || count_if(&OUTPUT, "switch_sparse") >= 4,
            "expected sparse switch dispatch");
}

#[test]
fn switch_fallthrough_has_dispatch() {
    let b = body(&OUTPUT, "switch_fallthrough");
    assert!(has_switch(&OUTPUT, "switch_fallthrough")
            || count_if(&OUTPUT, "switch_fallthrough") >= 2
            || b.contains("return"),
            "expected fallthrough-style dispatch:\n{b}");
}

#[test]
fn switch_in_loop_has_loop_and_dispatch() {
    let b = body(&OUTPUT, "switch_in_loop");
    assert!(has_any_loop(&OUTPUT, "switch_in_loop"), "expected outer loop");
    assert!(has_switch(&OUTPUT, "switch_in_loop")
            || count_if(&OUTPUT, "switch_in_loop") >= 1
            || b.contains("goto ")
            || b.contains("return"),
            "expected dispatch inside loop:\n{b}");
}

#[test]
fn switch_under_if_has_if_and_dispatch() {
    assert!(has_if_stmt(&OUTPUT, "switch_under_if"), "expected enclosing if");
    assert!(has_switch(&OUTPUT, "switch_under_if")
            || count_if(&OUTPUT, "switch_under_if") >= 2,
            "expected switch or equivalent branch chain");
}

#[test]
fn if_inside_switch_has_switch_or_if_chain() {
    assert!(has_switch(&OUTPUT, "if_inside_switch")
            || count_if(&OUTPUT, "if_inside_switch") >= 2,
            "expected switch with inner conditionals");
}

#[test]
fn if_inside_switch_has_inner_if() {
    assert!(has_if_stmt(&OUTPUT, "if_inside_switch"), "expected if statements in switch arms");
}

#[test]
fn complex_control_mesh_has_early_exit() {
    let b = body(&OUTPUT, "complex_control_mesh");
    assert!(b.matches("return").count() >= 1, "expected at least one explicit return:\n{b}");
}
