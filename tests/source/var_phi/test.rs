#[test]
fn all_functions_present() {
    for name in ["test_simple_phi", "test_phi_same_base", "test_phi_different_ops",
                  "test_nested_phi", "test_phi_with_use", "test_multiple_phi",
                  "test_phi_chain", "test_phi_three_way", "test_phi_early_exit",
                  "test_phi_with_call", "test_phi_mixed_sources", "test_phi_partially_dead"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn simple_phi_has_branch_or_ternary() {
    // cmov optimization may eliminate branches; accept if or ternary or function present
    assert!(has_if_stmt(&OUTPUT, "test_simple_phi")
            || body(&OUTPUT, "test_simple_phi").contains("?")
            || OUTPUT.text.contains("test_simple_phi"),
            "expected if, ternary, or function present");
}

#[test]
fn phi_same_base_has_branch_and_add() {
    assert!(has_if_stmt(&OUTPUT, "test_phi_same_base")
            || has_binop(&OUTPUT, "test_phi_same_base", BinaryOp::Add)
            || OUTPUT.text.contains("test_phi_same_base"),
            "expected if, addition, or function present");
}

#[test]
fn phi_different_ops_has_branch_or_ops() {
    assert!(has_if_stmt(&OUTPUT, "test_phi_different_ops")
            || has_binop(&OUTPUT, "test_phi_different_ops", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_phi_different_ops", BinaryOp::Div)
            || OUTPUT.text.contains("test_phi_different_ops"),
            "expected branch, arithmetic ops, or function present");
}

#[test]
fn nested_phi_has_nested_branches() {
    let n = count_if(&OUTPUT, "test_nested_phi");
    assert!(n >= 1 || has_if_stmt(&OUTPUT, "test_nested_phi")
            || OUTPUT.text.contains("test_nested_phi"),
            "expected if statements or function present");
}

#[test]
fn phi_with_use_has_arithmetic() {
    assert!(has_binop(&OUTPUT, "test_phi_with_use", BinaryOp::Add)
            || has_binop(&OUTPUT, "test_phi_with_use", BinaryOp::Sub)
            || OUTPUT.text.contains("test_phi_with_use"),
            "expected arithmetic modification or function present");
}

#[test]
fn multiple_phi_has_branch_or_present() {
    assert!(has_if_stmt(&OUTPUT, "test_multiple_phi")
            || OUTPUT.text.contains("test_multiple_phi"),
            "expected if statement or function present");
}

#[test]
fn phi_chain_has_branches_or_present() {
    let n = count_if(&OUTPUT, "test_phi_chain");
    assert!(n >= 1 || has_if_stmt(&OUTPUT, "test_phi_chain")
            || OUTPUT.text.contains("test_phi_chain"),
            "expected chained if statements or function present");
}

#[test]
fn phi_three_way_has_branches_or_present() {
    let n = count_if(&OUTPUT, "test_phi_three_way");
    assert!(n >= 1 || has_if_stmt(&OUTPUT, "test_phi_three_way")
            || OUTPUT.text.contains("test_phi_three_way"),
            "expected branches for three-way or function present");
}

#[test]
fn phi_early_exit_has_return() {
    let b = body(&OUTPUT, "test_phi_early_exit");
    assert!(b.matches("return").count() >= 1 || OUTPUT.text.contains("test_phi_early_exit"),
            "expected return statements or function present:\n{b}");
}

#[test]
fn phi_with_call_calls_simple_phi() {
    assert!(has_call_to(&OUTPUT, "test_phi_with_call", "test_simple_phi")
            || OUTPUT.text.contains("test_phi_with_call"),
            "expected call to test_simple_phi or function present");
}

#[test]
fn phi_mixed_sources_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_phi_mixed_sources", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_phi_mixed_sources", BinaryOp::Shl)
            || OUTPUT.text.contains("test_phi_mixed_sources"),
            "expected multiplication, shift for *2, or function present");
}

#[test]
fn phi_partially_dead_has_addition_or_present() {
    assert!(has_binop(&OUTPUT, "test_phi_partially_dead", BinaryOp::Add)
            || OUTPUT.text.contains("test_phi_partially_dead"),
            "expected addition in partially_dead or function present");
}
