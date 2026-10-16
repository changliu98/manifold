// A local buffer whose address may reach a call, here through a join with a heap pointer, is the
// callee's to fill: it must keep its whole extent instead of becoming a scalar.

fn type_bytes(ty: &CType) -> usize {
    match ty {
        CType::Int(IntSize::Char, _) | CType::Bool => 1,
        CType::Int(IntSize::Short, _) => 2,
        CType::Int(IntSize::Int, _) => 4,
        CType::Int(IntSize::Long | IntSize::LongLong, _) | CType::Pointer(..) => 8,
        CType::Int(IntSize::Int128, _) => 16,
        CType::Array(elem, Some(n)) => type_bytes(elem) * n,
        _ => 0,
    }
}

#[test]
fn buffer_keeps_its_extent() {
    let f = func_def(&OUTPUT, "with_temp_name");
    let addressed = std::cell::RefCell::new(std::collections::BTreeSet::new());
    stmt_has_expr(&f.body, &|e| {
        if let CExpr::Unary(UnaryOp::AddrOf, inner) = e {
            let mut base = inner.as_ref();
            while let CExpr::Index(b, _) | CExpr::Cast(_, b) | CExpr::Paren(b) = base {
                base = b.as_ref();
            }
            if let CExpr::Var(name) = base {
                addressed.borrow_mut().insert(name.clone());
            }
        }
        false
    });
    let widest = f
        .local_vars
        .iter()
        .filter(|v| addressed.borrow().contains(&v.name))
        .map(|v| type_bytes(&v.ty))
        .max()
        .unwrap_or(0);
    assert!(widest >= 256, "the 256-byte buffer is backed by {widest} bytes:\n{}", body(&OUTPUT, "with_temp_name"));
}
