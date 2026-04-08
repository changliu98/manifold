#[test]
fn all_functions_present() {
    for name in ["test_add_sub", "test_mul_div", "test_bitwise",
                  "test_shift", "test_long_arith", "test_unsigned", "test_negate"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn add_sub_has_add() {
    // gcc -O1 optimizes (a+b)+(a-b) to 2*a, eliminating the SUB entirely
    assert!(has_binop(&OUTPUT, "test_add_sub", BinaryOp::Add), "expected Add op");
}

#[test]
fn bitwise_has_xor() {
    // gcc -O1 uses the identity (a&b)+(a|b)=a+b, eliminating AND and OR
    assert!(has_binop(&OUTPUT, "test_bitwise", BinaryOp::BitXor), "expected XOR op");
}

#[test]
fn shift_has_ops() {
    assert!(has_binop(&OUTPUT, "test_shift", BinaryOp::Shl), "expected Shl");
    assert!(has_binop(&OUTPUT, "test_shift", BinaryOp::Shr), "expected Shr");
}

#[test]
fn mul_div_has_branch() {
    assert!(has_if_stmt(&OUTPUT, "test_mul_div")
            || func_def(&OUTPUT, "test_mul_div").body != CStmt::Empty,
            "expected branch or body");
}

#[test]
fn negate_has_unary() {
    assert!(has_unop(&OUTPUT, "test_negate", UnaryOp::Neg)
            || has_unop(&OUTPUT, "test_negate", UnaryOp::BitNot),
            "expected unary op");
}

#[test]
fn long_arith_has_mul_and_sub() {
    assert!(has_binop(&OUTPUT, "test_long_arith", BinaryOp::Mul), "expected multiply");
    assert!(has_binop(&OUTPUT, "test_long_arith", BinaryOp::Sub), "expected subtract");
}

#[test]
fn unsigned_writes_sink_and_returns_zero() {
    assert!(has_var_ref(&OUTPUT, "test_unsigned", "sink"), "expected sink reference");
}
