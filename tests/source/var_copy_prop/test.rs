#[test]
fn all_functions_present() {
    for name in ["test_simple_copy", "test_chain_copy", "test_copy_with_use",
                  "test_dead_store_simple", "test_dead_store_chain", "test_partial_dead",
                  "test_copy_across_branch", "test_copy_to_multiple", "test_copy_from_param",
                  "test_swap_pattern", "test_copy_in_loop", "test_redundant_reload",
                  "test_copy_then_modify", "test_dead_in_branch"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn simple_copy_returns() {
    let b = body(&OUTPUT, "test_simple_copy");
    assert!(b.contains("return"),
            "expected return:\n{b}");
}

#[test]
fn chain_copy_returns() {
    let b = body(&OUTPUT, "test_chain_copy");
    assert!(b.contains("return"),
            "expected return:\n{b}");
}

#[test]
fn copy_with_use_has_addition() {
    assert!(has_binop(&OUTPUT, "test_copy_with_use", BinaryOp::Add)
            || has_binop(&OUTPUT, "test_copy_with_use", BinaryOp::Shl),
            "expected addition, shift for doubling");
}

#[test]
fn dead_store_simple_assignment() {
    let b = body(&OUTPUT, "test_dead_store_simple");
    let assigns = b.matches("=").count();
    assert!(assigns <= 10,
            "expected assignments:\n{b}");
}

#[test]
fn partial_dead_has_addition() {
    assert!(has_binop(&OUTPUT, "test_partial_dead", BinaryOp::Add),
            "expected addition in partial_dead");
}

#[test]
fn copy_across_branch_has_branch() {
    assert!(has_if_stmt(&OUTPUT, "test_copy_across_branch"),
            "expected if statement");
}

#[test]
fn copy_to_multiple_has_additions() {
    assert!(has_binop(&OUTPUT, "test_copy_to_multiple", BinaryOp::Add),
            "expected addition in copy_to_multiple");
}

#[test]
fn copy_from_param_has_two_params() {
    assert_eq!(param_count(&OUTPUT, "test_copy_from_param"), 2,
               "copy_from_param should have 2 params");
}

#[test]
fn swap_pattern_has_addition() {
    assert!(has_binop(&OUTPUT, "test_swap_pattern", BinaryOp::Add),
            "expected addition in swap_pattern");
}

#[test]
fn copy_in_loop_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_copy_in_loop"),
            "expected loop");
}

#[test]
fn redundant_reload_has_return() {
    let b = body(&OUTPUT, "test_redundant_reload");
    assert!(b.contains("return"),
            "expected return:\n{b}");
}

#[test]
fn copy_then_modify_has_addition() {
    assert!(has_binop(&OUTPUT, "test_copy_then_modify", BinaryOp::Add),
            "expected addition in copy_then_modify");
}

#[test]
fn dead_in_branch_has_branch() {
    // Both compilers can materialize this two-value branch with SETcc plus
    // arithmetic.  Require the recovered predicate when no statement branch
    // survives in the binary.
    assert!(has_if_stmt(&OUTPUT, "test_dead_in_branch")
            || has_binop(&OUTPUT, "test_dead_in_branch", BinaryOp::Gt)
            || has_binop(&OUTPUT, "test_dead_in_branch", BinaryOp::Le),
            "expected branch or materialized branch predicate");
}
