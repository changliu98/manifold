#[test]
fn all_functions_present() {
    for name in ["ternary_abs", "ternary_max", "ternary_clamp",
                  "divide_by_3", "divide_by_7", "udivide_by_10",
                  "modulo_10", "modulo_and_div", "compound_ops",
                  "range_check", "multi_condition", "call_in_condition",
                  "polynomial"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

// angr test_automatic_ternary_creation: conditional move -> ternary
#[test]
fn ternary_abs_has_condition() {
    // Should decompile to either ternary or if-else, not raw cmov
    assert!(has_if_stmt(&OUTPUT, "ternary_abs")
            || stmt_has_expr(&func_def(&OUTPUT, "ternary_abs").body,
                &|e| matches!(e, CExpr::Ternary(..))),
            "expected ternary or if for abs pattern");
}

#[test]
fn ternary_abs_has_negation() {
    // clang may use cmov for shift-based abs instead of negation
    assert!(has_unop(&OUTPUT, "ternary_abs", UnaryOp::Neg)
            || has_binop(&OUTPUT, "ternary_abs", BinaryOp::Sub)
            || has_binop(&OUTPUT, "ternary_abs", BinaryOp::Shr)
            || has_binop(&OUTPUT, "ternary_abs", BinaryOp::BitXor),
            "expected negation, subtraction, or shift-based abs pattern");
}

#[test]
fn ternary_max_has_condition() {
    assert!(has_if_stmt(&OUTPUT, "ternary_max")
            || stmt_has_expr(&func_def(&OUTPUT, "ternary_max").body,
                &|e| matches!(e, CExpr::Ternary(..))),
            "expected ternary or if for max pattern");
}

// angr test_decompiling_division3: magic number division recovery
#[test]
fn divide_by_3_has_division() {
    let b = body(&OUTPUT, "divide_by_3");
    assert!(b.contains("/ 3") || b.contains("/3")
            || has_binop(&OUTPUT, "divide_by_3", BinaryOp::Div),
            "expected division by 3 (not magic multiply):\n{b}");
}

#[test]
fn divide_by_7_has_division() {
    let b = body(&OUTPUT, "divide_by_7");
    assert!(b.contains("/ 7") || b.contains("/7")
            || has_binop(&OUTPUT, "divide_by_7", BinaryOp::Div),
            "expected division by 7 (not magic multiply):\n{b}");
}

#[test]
fn udivide_by_10_has_division() {
    let b = body(&OUTPUT, "udivide_by_10");
    assert!(b.contains("/ 10") || b.contains("/10")
            || has_binop(&OUTPUT, "udivide_by_10", BinaryOp::Div),
            "expected unsigned division by 10:\n{b}");
}

// angr test_decompiling_simple_ctfbin_modulo: modulo recovery
#[test]
fn modulo_10_has_mod_op() {
    let b = body(&OUTPUT, "modulo_10");
    assert!(b.contains("% 10") || b.contains("%10")
            || has_binop(&OUTPUT, "modulo_10", BinaryOp::Mod),
            "expected modulo 10:\n{b}");
}

#[test]
fn modulo_and_div_has_both() {
    assert!(has_binop(&OUTPUT, "modulo_and_div", BinaryOp::Div)
            || has_binop(&OUTPUT, "modulo_and_div", BinaryOp::Mod),
            "expected div or mod in combined function");
}

// compound ops: expression tree reconstruction
#[test]
fn compound_ops_has_arithmetic() {
    assert!(has_binop(&OUTPUT, "compound_ops", BinaryOp::Add)
            || has_binop(&OUTPUT, "compound_ops", BinaryOp::Mul)
            || has_binop(&OUTPUT, "compound_ops", BinaryOp::Sub),
            "expected arithmetic in compound_ops");
}

#[test]
fn compound_ops_has_three_params() {
    assert_eq!(param_count(&OUTPUT, "compound_ops"), 3,
               "compound_ops takes 3 params");
}

// angr test_cascading_boolean_and: chained conditions
#[test]
fn range_check_has_condition() {
    assert!(has_if_stmt(&OUTPUT, "range_check")
            || has_binop(&OUTPUT, "range_check", BinaryOp::And)
            || has_binop(&OUTPUT, "range_check", BinaryOp::BitAnd),
            "expected conditional for range check");
}

#[test]
fn multi_condition_has_condition() {
    assert!(has_if_stmt(&OUTPUT, "multi_condition")
            || has_binop(&OUTPUT, "multi_condition", BinaryOp::And),
            "expected conditional for multi-condition");
}

// angr test_call_expr_folding_into_if_conditions
#[test]
fn call_in_condition_calls_abs() {
    assert!(has_call_to(&OUTPUT, "call_in_condition", "ternary_abs"),
            "expected call to ternary_abs in condition");
}

// polynomial: complex expression tree
#[test]
fn polynomial_has_multiply() {
    assert!(has_binop(&OUTPUT, "polynomial", BinaryOp::Mul),
            "expected multiplication in polynomial");
}

#[test]
fn polynomial_has_one_param() {
    assert_eq!(param_count(&OUTPUT, "polynomial"), 1, "polynomial takes 1 param");
}
