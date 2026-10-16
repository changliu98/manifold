// A function whose switch dispatch was recovered keeps the out-parameter local it passes by address
// as one object: the reads after the call see what the callee stored.

// The local named under the address-of in `e`, through casts and indexing.
fn addressed_local(e: &CExpr) -> Option<String> {
    fn base(e: &CExpr) -> Option<String> {
        match e {
            CExpr::Var(name) => Some(name.clone()),
            CExpr::Index(inner, _) | CExpr::Cast(_, inner) | CExpr::Paren(inner) | CExpr::Member(inner, _) => base(inner),
            CExpr::Unary(UnaryOp::AddrOf, inner) => base(inner),
            _ => None,
        }
    }
    match e {
        CExpr::Unary(UnaryOp::AddrOf, inner) => base(inner),
        CExpr::Cast(_, inner) | CExpr::Paren(inner) => addressed_local(inner),
        _ => None,
    }
}

#[test]
fn out_parameter_is_read_back_from_the_passed_object() {
    let main = func_def(&OUTPUT, "main");
    let passed = std::cell::RefCell::new(Vec::new());
    stmt_has_expr(&main.body, &|e| {
        if let CExpr::Call(callee, args) = e {
            if matches!(unwrap_casts(callee), CExpr::Var(name) if name == "concat") && args.len() == 3 {
                passed.borrow_mut().extend(addressed_local(&args[2]));
            }
        }
        false
    });
    let passed = passed.into_inner();
    assert_eq!(passed.len(), 1, "concat's out-parameter is not a local's address:\n{}", body(&OUTPUT, "main"));
    let uses = std::cell::Cell::new(0usize);
    stmt_has_expr(&main.body, &|e| {
        if matches!(e, CExpr::Var(name) if *name == passed[0]) {
            uses.set(uses.get() + 1);
        }
        false
    });
    assert!(uses.get() >= 2, "{} is never read after concat stores through it:\n{}", passed[0], body(&OUTPUT, "main"));
}
