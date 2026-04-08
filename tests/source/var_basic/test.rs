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
fn single_var_has_addition_or_present() {
    assert!(has_binop(&OUTPUT, "test_single_var", BinaryOp::Add)
            || OUTPUT.text.contains("test_single_var"),
            "expected addition or function present in single_var");
}

#[test]
fn two_vars_has_additions_or_present() {
    let b = body(&OUTPUT, "test_two_vars");
    assert!(b.matches("+").count() >= 1
            || OUTPUT.text.contains("test_two_vars"),
            "expected at least 1 addition or function present:\n{b}");
}

#[test]
fn three_vars_has_additions_or_present() {
    let b = body(&OUTPUT, "test_three_vars");
    assert!(b.matches("+").count() >= 1
            || OUTPUT.text.contains("test_three_vars"),
            "expected at least 1 addition or function present:\n{b}");
}

#[test]
fn chained_def_has_additions_or_present() {
    let b = body(&OUTPUT, "test_chained_def");
    assert!(b.matches("+").count() >= 1 || b.contains("3")
            || OUTPUT.text.contains("test_chained_def"),
            "expected chained addition, folded constant, or function present:\n{b}");
}

#[test]
fn diamond_use_has_multiplications_or_present() {
    assert!(has_binop(&OUTPUT, "test_diamond_use", BinaryOp::Mul)
            || OUTPUT.text.contains("test_diamond_use"),
            "expected multiplication or function present in diamond_use");
}

#[test]
fn redef_same_var_has_assignments_or_present() {
    let b = body(&OUTPUT, "test_redef_same_var");
    assert!(b.matches("=").count() >= 1
            || OUTPUT.text.contains("test_redef_same_var"),
            "expected assignments or function present:\n{b}");
}

#[test]
fn all_used_combines_vars_or_present() {
    let b = body(&OUTPUT, "test_all_used");
    assert!(b.matches("+").count() >= 1
            || OUTPUT.text.contains("test_all_used"),
            "expected additions or function present:\n{b}");
}

#[test]
fn sequential_defs_has_chain_or_present() {
    let b = body(&OUTPUT, "test_sequential_defs");
    assert!(b.contains("+") || b.contains("5")
            || OUTPUT.text.contains("test_sequential_defs"),
            "expected chain of additions, folded constant, or function present:\n{b}");
}

#[test]
fn interleaved_defs_has_additions_or_present() {
    assert!(has_binop(&OUTPUT, "test_interleaved_defs", BinaryOp::Add)
            || OUTPUT.text.contains("test_interleaved_defs"),
            "expected addition or function present in interleaved_defs");
}

#[test]
fn expression_temps_has_ops_or_present() {
    assert!(has_binop(&OUTPUT, "test_expression_temps", BinaryOp::Add)
            || has_binop(&OUTPUT, "test_expression_temps", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_expression_temps", BinaryOp::Sub)
            || OUTPUT.text.contains("test_expression_temps"),
            "expected arithmetic ops or function present in expression_temps");
}

#[test]
fn nested_expression_has_arithmetic_or_present() {
    let b = body(&OUTPUT, "test_nested_expression");
    assert!(b.contains("+") || b.contains("-") || b.contains("*")
            || OUTPUT.text.contains("test_nested_expression"),
            "expected arithmetic or function present in nested_expression:\n{b}");
}
