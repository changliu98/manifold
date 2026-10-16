// The quotient (AX) and remainder (DX) of one DIV/IDIV are two results: a function using both must
// compute both, at the width of its operands.

// A Div or Mod whose dividend is not narrowed to 32 bits.  Clang may also emit a 32-bit fast path
// guarded by both operands fitting, where narrowing is exact, so only presence is required.
fn has_wide(func: &str, op: BinaryOp) -> bool {
    stmt_has_expr(&func_def(&OUTPUT, func).body, &|e| {
        matches!(e, CExpr::Binary(o, lhs, _)
            if *o == op && !matches!(lhs.as_ref(), CExpr::Cast(CType::Int(IntSize::Int, _), _)))
    })
}

#[test]
fn both_results_are_computed() {
    for func in ["sdiv64", "udiv64", "sdiv32", "udiv32", "round_count"] {
        assert!(has_binop(&OUTPUT, func, BinaryOp::Div), "{func} lost its quotient:\n{}", body(&OUTPUT, func));
        assert!(has_binop(&OUTPUT, func, BinaryOp::Mod), "{func} lost its remainder:\n{}", body(&OUTPUT, func));
    }
}

#[test]
fn wide_division_keeps_its_dividend() {
    for func in ["sdiv64", "udiv64"] {
        for op in [BinaryOp::Div, BinaryOp::Mod] {
            assert!(has_wide(func, op), "{func} has no 64-bit {op:?}:\n{}", body(&OUTPUT, func));
        }
    }
    assert!(has_wide("srem64", BinaryOp::Mod), "srem64 has no 64-bit Mod:\n{}", body(&OUTPUT, "srem64"));
}
