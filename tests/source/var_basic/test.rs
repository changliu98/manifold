#[test]
fn all_functions_present() {
    for name in ["test_single_var", "test_two_vars", "test_three_vars",
                  "test_chained_def", "test_diamond_use", "test_redef_same_var",
                  "test_unused_intermediate", "test_all_used",
                  "test_sequential_defs", "test_interleaved_defs",
                  "test_expression_temps", "test_nested_expression"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn single_var_has_addition() {
    assert!(has_binop(&OUTPUT, "test_single_var", BinaryOp::Add),
            "expected addition in single_var");
}

#[test]
fn two_vars_has_additions() {
    let b = body(&OUTPUT, "test_two_vars");
    assert!(b.matches("+").count() >= 1,
            "expected at least 1 addition:\n{b}");
}

#[test]
fn three_vars_has_additions() {
    let b = body(&OUTPUT, "test_three_vars");
    assert!(b.matches("+").count() >= 1,
            "expected at least 1 addition:\n{b}");
}

#[test]
fn chained_def_has_additions() {
    let b = body(&OUTPUT, "test_chained_def");
    assert!(b.matches("+").count() >= 1 || b.contains("3"),
            "expected chained addition or a folded constant:\n{b}");
}

#[test]
fn diamond_use_has_multiplications() {
    assert!(has_binop(&OUTPUT, "test_diamond_use", BinaryOp::Mul),
            "expected multiplication in diamond_use");
}

#[test]
fn redef_same_var_has_assignments() {
    let b = body(&OUTPUT, "test_redef_same_var");
    assert!(b.matches("=").count() >= 1,
            "expected assignments:\n{b}");
}

#[test]
fn all_used_combines_vars() {
    let b = body(&OUTPUT, "test_all_used");
    assert!(b.matches("+").count() >= 1,
            "expected additions:\n{b}");
}

#[test]
fn sequential_defs_has_chain() {
    let b = body(&OUTPUT, "test_sequential_defs");
    assert!(b.contains("+") || b.contains("5"),
            "expected chain of additions or a folded constant:\n{b}");
}

#[test]
fn interleaved_defs_has_additions() {
    assert!(has_binop(&OUTPUT, "test_interleaved_defs", BinaryOp::Add),
            "expected addition in interleaved_defs");
}

#[test]
fn expression_temps_has_ops() {
    assert!(has_binop(&OUTPUT, "test_expression_temps", BinaryOp::Add)
            || has_binop(&OUTPUT, "test_expression_temps", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_expression_temps", BinaryOp::Sub),
            "expected arithmetic ops in expression_temps");
}

#[test]
fn nested_expression_has_arithmetic() {
    let b = body(&OUTPUT, "test_nested_expression");
    assert!(b.contains("+") || b.contains("-") || b.contains("*"),
            "expected arithmetic in nested_expression:\n{b}");
}
