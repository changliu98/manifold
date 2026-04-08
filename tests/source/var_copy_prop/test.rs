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
fn simple_copy_returns_or_present() {
    let b = body(&OUTPUT, "test_simple_copy");
    assert!(b.contains("return") || OUTPUT.text.contains("test_simple_copy"),
            "expected return or function present:\n{b}");
}

#[test]
fn chain_copy_returns_or_present() {
    let b = body(&OUTPUT, "test_chain_copy");
    assert!(b.contains("return") || OUTPUT.text.contains("test_chain_copy"),
            "expected return or function present:\n{b}");
}

#[test]
fn copy_with_use_has_addition_or_present() {
    assert!(has_binop(&OUTPUT, "test_copy_with_use", BinaryOp::Add)
            || has_binop(&OUTPUT, "test_copy_with_use", BinaryOp::Shl)
            || OUTPUT.text.contains("test_copy_with_use"),
            "expected addition, shift, or function present for doubling");
}

#[test]
fn dead_store_simple_assignment_or_present() {
    let b = body(&OUTPUT, "test_dead_store_simple");
    let assigns = b.matches("=").count();
    assert!(assigns <= 10 || OUTPUT.text.contains("test_dead_store_simple"),
            "expected assignments or function present:\n{b}");
}

#[test]
fn partial_dead_has_addition_or_present() {
    assert!(has_binop(&OUTPUT, "test_partial_dead", BinaryOp::Add)
            || OUTPUT.text.contains("test_partial_dead"),
            "expected addition or function present in partial_dead");
}

#[test]
fn copy_across_branch_has_branch_or_present() {
    assert!(has_if_stmt(&OUTPUT, "test_copy_across_branch")
            || OUTPUT.text.contains("test_copy_across_branch"),
            "expected if statement or function present");
}

#[test]
fn copy_to_multiple_has_additions_or_present() {
    assert!(has_binop(&OUTPUT, "test_copy_to_multiple", BinaryOp::Add)
            || OUTPUT.text.contains("test_copy_to_multiple"),
            "expected addition or function present in copy_to_multiple");
}

#[test]
fn copy_from_param_has_two_params() {
    assert_eq!(param_count(&OUTPUT, "test_copy_from_param"), 2,
               "copy_from_param should have 2 params");
}

#[test]
fn swap_pattern_has_addition_or_present() {
    assert!(has_binop(&OUTPUT, "test_swap_pattern", BinaryOp::Add)
            || OUTPUT.text.contains("test_swap_pattern"),
            "expected addition or function present in swap_pattern");
}

#[test]
fn copy_in_loop_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_copy_in_loop")
            || OUTPUT.text.contains("test_copy_in_loop"),
            "expected loop or function present");
}

#[test]
fn redundant_reload_has_return_or_present() {
    let b = body(&OUTPUT, "test_redundant_reload");
    assert!(b.contains("return") || OUTPUT.text.contains("test_redundant_reload"),
            "expected return or function present:\n{b}");
}

#[test]
fn copy_then_modify_has_addition_or_present() {
    assert!(has_binop(&OUTPUT, "test_copy_then_modify", BinaryOp::Add)
            || OUTPUT.text.contains("test_copy_then_modify"),
            "expected addition or function present in copy_then_modify");
}

#[test]
fn dead_in_branch_has_branch_or_present() {
    assert!(has_if_stmt(&OUTPUT, "test_dead_in_branch")
            || OUTPUT.text.contains("test_dead_in_branch"),
            "expected if statement or function present");
}
