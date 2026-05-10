fn has_any_binop(func: &str, ops: &[BinaryOp]) -> bool {
    let f = func_def(&OUTPUT, func);
    stmt_has_expr(
        &f.body,
        &|e| matches!(e, CExpr::Binary(op, _, _) if ops.contains(op)),
    )
}

fn has_ternary(func: &str) -> bool {
    let f = func_def(&OUTPUT, func);
    stmt_has_expr(&f.body, &|e| matches!(e, CExpr::Ternary(..)))
}

#[test]
fn all_functions_present() {
    for name in [
        "signed_unsigned_compare",
        "char_short_extensions",
        "explicit_truncation",
        "boolean_normalization",
        "mixed_width_arithmetic",
        "mask_and_shift",
    ] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn signed_unsigned_compare_has_relational_flow() {
    assert!(
        has_if_stmt(&OUTPUT, "signed_unsigned_compare") || has_ternary("signed_unsigned_compare"),
        "expected conditional flow for signed/unsigned comparisons"
    );
    assert!(
        has_any_binop(
            "signed_unsigned_compare",
            &[BinaryOp::Lt, BinaryOp::Le, BinaryOp::Gt, BinaryOp::Ge,]
        ),
        "expected relational comparison"
    );
}

#[test]
fn char_short_extensions_keep_shift_and_mask() {
    let b = body(&OUTPUT, "char_short_extensions");
    assert_eq!(
        param_count(&OUTPUT, "char_short_extensions"),
        4,
        "expected char/short extension parameters"
    );
    assert!(
        has_any_binop(
            "char_short_extensions",
            &[BinaryOp::Shr, BinaryOp::BitAnd, BinaryOp::Add]
        ),
        "expected extension-related arithmetic:\n{b}"
    );
}

#[test]
fn explicit_truncation_has_narrowing_or_mask() {
    let b = body(&OUTPUT, "explicit_truncation");
    assert!(
        has_assign(&OUTPUT, "explicit_truncation"),
        "expected observed narrowed stores:\n{b}"
    );
    assert!(
        has_binop(&OUTPUT, "explicit_truncation", BinaryOp::Shr)
            || has_binop(&OUTPUT, "explicit_truncation", BinaryOp::Add)
            || has_binop(&OUTPUT, "explicit_truncation", BinaryOp::BitAnd),
        "expected shifted source or truncation arithmetic:\n{b}"
    );
}

#[test]
fn boolean_normalization_has_comparisons_and_logic() {
    assert!(
        has_any_binop(
            "boolean_normalization",
            &[
                BinaryOp::Eq,
                BinaryOp::Ne,
                BinaryOp::Lt,
                BinaryOp::Gt,
                BinaryOp::Le,
                BinaryOp::Ge,
                BinaryOp::And,
                BinaryOp::BitAnd,
            ]
        ) || has_if_stmt(&OUTPUT, "boolean_normalization")
            || has_ternary("boolean_normalization"),
        "expected boolean-producing comparisons or normalized conjunction"
    );
}

#[test]
fn mixed_width_arithmetic_has_widened_arithmetic() {
    assert_eq!(
        param_count(&OUTPUT, "mixed_width_arithmetic"),
        3,
        "expected mixed-width arithmetic parameters"
    );
    assert!(
        has_binop(&OUTPUT, "mixed_width_arithmetic", BinaryOp::Add),
        "expected widened addition"
    );
    assert!(
        has_binop(&OUTPUT, "mixed_width_arithmetic", BinaryOp::Sub),
        "expected widened subtraction"
    );
    assert!(
        has_binop(&OUTPUT, "mixed_width_arithmetic", BinaryOp::Mul)
            || has_binop(&OUTPUT, "mixed_width_arithmetic", BinaryOp::Shl),
        "expected unsigned scale multiply or shift"
    );
}

#[test]
fn mask_and_shift_has_bit_packing_ops() {
    let b = body(&OUTPUT, "mask_and_shift");
    assert!(
        has_any_binop(
            "mask_and_shift",
            &[
                BinaryOp::BitAnd,
                BinaryOp::Shr,
                BinaryOp::Shl,
                BinaryOp::Mul,
                BinaryOp::BitOr,
            ]
        ),
        "expected bit-packing arithmetic:\n{b}"
    );
    assert!(
        b.contains("sink") || b.contains("usink") || b.contains("lsink"),
        "expected volatile observations of packed components:\n{b}"
    );
}
