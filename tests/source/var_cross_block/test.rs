#[test]
fn all_functions_present() {
    for name in ["test_def_in_pred", "test_use_in_succ", "test_live_across_loop",
                  "test_multiple_preds", "test_multiple_succs", "test_diamond_cfg",
                  "test_loop_back_edge", "test_nested_cfg", "test_early_return",
                  "test_switch_cfg", "test_break_in_loop", "test_complex_cfg",
                  "test_critical_edge", "test_backedge_live_var"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn def_in_pred_has_branch() {
    assert!(has_if_stmt(&OUTPUT, "test_def_in_pred"),
            "expected if statement");
}

#[test]
fn use_in_succ_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_use_in_succ", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_use_in_succ", BinaryOp::Shl),
            "expected multiplication, shift");
}

#[test]
fn live_across_loop_has_loop_or_closed_form() {
    // Clang folds the constant-add loop to 10*n + 10.
    assert!(has_any_loop(&OUTPUT, "test_live_across_loop")
            || has_binop(&OUTPUT, "test_live_across_loop", BinaryOp::Mul),
            "expected loop or closed-form multiplication");
}

#[test]
fn multiple_preds_has_branches() {
    let n = count_if(&OUTPUT, "test_multiple_preds");
    assert!(n >= 1 || has_if_stmt(&OUTPUT, "test_multiple_preds"),
            "expected branches");
}

#[test]
fn multiple_succs_has_returns() {
    let b = body(&OUTPUT, "test_multiple_succs");
    assert!(b.matches("return").count() >= 1,
            "expected returns:\n{b}");
}

#[test]
fn diamond_cfg_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_diamond_cfg", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_diamond_cfg", BinaryOp::Shl)
            || has_binop(&OUTPUT, "test_diamond_cfg", BinaryOp::Add),
            "expected multiply, shift, or add-self for *2");
}

#[test]
fn loop_back_edge_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_loop_back_edge"),
            "expected loop");
}

#[test]
fn nested_cfg_has_branches() {
    let n = count_if(&OUTPUT, "test_nested_cfg");
    assert!(n >= 1 || has_if_stmt(&OUTPUT, "test_nested_cfg"),
            "expected nested branches");
}

#[test]
fn early_return_has_returns() {
    let b = body(&OUTPUT, "test_early_return");
    assert!(b.matches("return").count() >= 1,
            "expected returns:\n{b}");
}

#[test]
fn switch_cfg_has_switch_or_ifs() {
    assert!(has_switch(&OUTPUT, "test_switch_cfg")
            || count_if(&OUTPUT, "test_switch_cfg") >= 1,
            "expected switch, if-chain");
}

#[test]
fn break_in_loop_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_break_in_loop"),
            "expected loop");
}

#[test]
fn complex_cfg_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_complex_cfg", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_complex_cfg", BinaryOp::Shl)
            || has_binop(&OUTPUT, "test_complex_cfg", BinaryOp::Add),
            "expected multiply, shift, or add-self for *2");
}

#[test]
fn critical_edge_has_addition() {
    assert!(has_binop(&OUTPUT, "test_critical_edge", BinaryOp::Add),
            "expected addition");
}

#[test]
fn backedge_live_var_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_backedge_live_var"),
            "expected loop");
}
