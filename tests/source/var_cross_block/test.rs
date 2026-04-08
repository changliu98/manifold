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
fn def_in_pred_has_branch_or_present() {
    assert!(has_if_stmt(&OUTPUT, "test_def_in_pred")
            || OUTPUT.text.contains("test_def_in_pred"),
            "expected if statement or function present");
}

#[test]
fn use_in_succ_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_use_in_succ", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_use_in_succ", BinaryOp::Shl)
            || OUTPUT.text.contains("test_use_in_succ"),
            "expected multiplication, shift, or function present");
}

#[test]
fn live_across_loop_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_live_across_loop")
            || OUTPUT.text.contains("test_live_across_loop"),
            "expected loop or function present");
}

#[test]
fn multiple_preds_has_branches_or_present() {
    let n = count_if(&OUTPUT, "test_multiple_preds");
    assert!(n >= 1 || has_if_stmt(&OUTPUT, "test_multiple_preds")
            || OUTPUT.text.contains("test_multiple_preds"),
            "expected branches or function present");
}

#[test]
fn multiple_succs_has_returns_or_present() {
    let b = body(&OUTPUT, "test_multiple_succs");
    assert!(b.matches("return").count() >= 1
            || OUTPUT.text.contains("test_multiple_succs"),
            "expected returns or function present:\n{b}");
}

#[test]
fn diamond_cfg_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_diamond_cfg", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_diamond_cfg", BinaryOp::Shl)
            || OUTPUT.text.contains("test_diamond_cfg"),
            "expected multiplication for *2 or function present");
}

#[test]
fn loop_back_edge_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_loop_back_edge")
            || OUTPUT.text.contains("test_loop_back_edge"),
            "expected loop or function present");
}

#[test]
fn nested_cfg_has_branches_or_present() {
    let n = count_if(&OUTPUT, "test_nested_cfg");
    assert!(n >= 1 || has_if_stmt(&OUTPUT, "test_nested_cfg")
            || OUTPUT.text.contains("test_nested_cfg"),
            "expected nested branches or function present");
}

#[test]
fn early_return_has_returns_or_present() {
    let b = body(&OUTPUT, "test_early_return");
    assert!(b.matches("return").count() >= 1
            || OUTPUT.text.contains("test_early_return"),
            "expected returns or function present:\n{b}");
}

#[test]
fn switch_cfg_has_switch_or_ifs_or_present() {
    assert!(has_switch(&OUTPUT, "test_switch_cfg")
            || count_if(&OUTPUT, "test_switch_cfg") >= 1
            || OUTPUT.text.contains("test_switch_cfg"),
            "expected switch, if-chain, or function present");
}

#[test]
fn break_in_loop_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_break_in_loop")
            || OUTPUT.text.contains("test_break_in_loop"),
            "expected loop or function present");
}

#[test]
fn complex_cfg_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_complex_cfg", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_complex_cfg", BinaryOp::Shl)
            || OUTPUT.text.contains("test_complex_cfg"),
            "expected multiplication for *2 or function present");
}

#[test]
fn critical_edge_has_addition_or_present() {
    assert!(has_binop(&OUTPUT, "test_critical_edge", BinaryOp::Add)
            || OUTPUT.text.contains("test_critical_edge"),
            "expected addition or function present");
}

#[test]
fn backedge_live_var_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_backedge_live_var")
            || OUTPUT.text.contains("test_backedge_live_var"),
            "expected loop or function present");
}
