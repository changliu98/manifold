fn is_integer_bridge_to_float(expr: &CExpr) -> bool {
    matches!(
        expr,
        CExpr::Cast(CType::Float(_), inner)
            if matches!(inner.as_ref(), CExpr::Cast(CType::Int(_, _), _))
    )
}

#[test]
fn dump_output() {
    dump_output_if_env("POINTER_FLOAT_BRIDGE", &OUTPUT.text);
}

#[test]
fn pointer_conversion_keeps_integer_bridge() {
    let function = func_def(&OUTPUT, "record_pointer_bits");
    assert!(
        stmt_has_expr(&function.body, &is_integer_bridge_to_float),
        "expected a legal floating conversion through an integer type:\n{}",
        body(&OUTPUT, "record_pointer_bits")
    );
}
