#[derive(Default)]
struct Declared(Vec<(String, CType)>);
impl ExprTransform for Declared {
    fn transform_stmt_in_expr(&mut self, stmt: CStmt) -> CStmt {
        self.transform_stmt(stmt)
    }
}
impl StmtTransform for Declared {
    fn transform_stmt(&mut self, stmt: CStmt) -> CStmt {
        match &stmt {
            CStmt::Decl(decls) | CStmt::For(Some(ForInit::Decl(decls)), _, _, _) => {
                self.0.extend(decls.iter().map(|d| (d.name.clone(), d.ty.clone())));
            }
            CStmt::Block(items) => {
                for item in items {
                    if let CBlockItem::Decl(decls) = item {
                        self.0.extend(decls.iter().map(|d| (d.name.clone(), d.ty.clone())));
                    }
                }
            }
            _ => {}
        }
        self.walk_stmt(stmt)
    }
}

/// Every declaration in a function: parameters, locals and block scopes.
fn declared(name: &str) -> Vec<(String, CType)> {
    let function = func_def(&OUTPUT, name);
    let mut all = Declared(
        function
            .params
            .iter()
            .filter_map(|p| p.name.clone().map(|n| (n, p.ty.clone())))
            .chain(function.local_vars.iter().map(|v| (v.name.clone(), v.ty.clone())))
            .collect(),
    );
    all.transform_stmt(function.body.clone());
    all.0
}

fn unqualified(ty: &CType) -> &CType {
    match ty {
        CType::Qualified(inner, _) => unqualified(inner),
        other => other,
    }
}

fn pointee(ty: &CType) -> Option<&CType> {
    match unqualified(ty) {
        CType::Pointer(inner, _) => Some(unqualified(inner)),
        _ => None,
    }
}

fn is_record_pointer(ty: &CType) -> bool {
    matches!(pointee(ty), Some(CType::Struct(_)))
}

fn is_char_pointer(ty: &CType) -> bool {
    matches!(pointee(ty), Some(CType::Int(IntSize::Char, _)))
}

#[test]
fn string_indexed_at_constant_offsets_is_not_a_record() {
    let types = declared("option_kind");
    assert!(
        !types.iter().any(|(_, t)| is_record_pointer(t)),
        "{}",
        body(&OUTPUT, "option_kind")
    );
}

#[test]
fn format_string_names_the_variadic_argument_type() {
    let types = declared("report");
    assert!(
        types.iter().any(|(_, t)| is_char_pointer(t)),
        "{}",
        body(&OUTPUT, "report")
    );
}

#[test]
fn large_file_mapping_is_a_full_width_pointer() {
    fn assigned_from(expr: &CExpr, callee: &str, out: &mut Vec<String>) {
        if let CExpr::Assign(_, lhs, rhs) = expr {
            if let (CExpr::Var(name), CExpr::Call(function, _)) =
                (unwrap_casts(lhs), unwrap_casts(rhs))
            {
                if matches!(unwrap_casts(function), CExpr::Var(f) if f == callee) {
                    out.push(name.clone());
                }
            }
        }
    }
    let function = func_def(&OUTPUT, "first_byte");
    let mut targets = Vec::new();
    struct Walk<'a>(&'a mut Vec<String>);
    impl ExprTransform for Walk<'_> {
        fn transform_expr(&mut self, expr: CExpr) -> CExpr {
            assigned_from(&expr, "mmap64", self.0);
            assigned_from(&expr, "mmap", self.0);
            self.walk_expr(expr)
        }
        fn transform_stmt_in_expr(&mut self, stmt: CStmt) -> CStmt {
            self.transform_stmt(stmt)
        }
    }
    impl StmtTransform for Walk<'_> {}
    Walk(&mut targets).transform_stmt(function.body.clone());
    assert!(!targets.is_empty(), "{}", body(&OUTPUT, "first_byte"));
    let types = declared("first_byte");
    for target in &targets {
        let ty = types.iter().find(|(n, _)| n == target).map(|(_, t)| t);
        assert!(
            ty.is_some_and(|t| pointee(t).is_some()),
            "{target}: {ty:?}\n{}",
            body(&OUTPUT, "first_byte")
        );
    }
}

#[test]
fn heterogeneous_record_keeps_its_identity() {
    let types = declared("pair_value");
    assert!(
        types.iter().any(|(_, t)| is_record_pointer(t)),
        "{}",
        body(&OUTPUT, "pair_value")
    );
}
