#[derive(Default)]
struct StorageTypes(Vec<CType>);
impl ExprTransform for StorageTypes {
    fn transform_stmt_in_expr(&mut self, stmt: CStmt) -> CStmt {
        self.transform_stmt(stmt)
    }
}
impl StmtTransform for StorageTypes {
    fn transform_stmt(&mut self, stmt: CStmt) -> CStmt {
        match &stmt {
            CStmt::Decl(declarations) | CStmt::For(Some(ForInit::Decl(declarations)), _, _, _) => {
                self.0.extend(declarations.iter().map(|d| d.ty.clone()));
            }
            CStmt::Block(items) => {
                for item in items {
                    if let CBlockItem::Decl(declarations) = item {
                        self.0.extend(declarations.iter().map(|d| d.ty.clone()));
                    }
                }
            }
            _ => {}
        }
        self.walk_stmt(stmt)
    }
}
fn storage_types(name: &str) -> Vec<CType> {
    let function = func_def(&OUTPUT, name);
    let mut types = StorageTypes(function.local_vars.iter().map(|d| d.ty.clone()).collect());
    types.transform_stmt(function.body.clone());
    types.0
}

#[test]
fn promoted_result_is_not_confused_with_its_byte_storage_source() {
    // Storage can be eliminated by copy propagation; do not require a dummy
    // byte declaration in final C. The observable arithmetic result must
    // nevertheless keep the promoted value width across the return boundary.
    for name in ["promoted_byte", "forwarded_promoted_byte"] {
        assert!(
            matches!(
                func_def(&OUTPUT, name).return_type,
                CType::Int(IntSize::Int | IntSize::Long | IntSize::LongLong, _)
            ),
            "{}",
            OUTPUT.text
        );
    }
    assert!(has_binop(&OUTPUT, "promoted_byte", BinaryOp::Add));
}

#[test]
fn genuinely_wide_storage_is_not_narrowed() {
    assert!(
        storage_types("wide_value")
            .iter()
            .any(|ty| matches!(ty, CType::Int(IntSize::Long | IntSize::LongLong, _))),
        "{}",
        body(&OUTPUT, "wide_value")
    );
}

#[test]
fn recovered_c_preserves_truncation_extension_and_promotion() {
    let binary = compile("storage_type_views_roundtrip", "gcc", &OUTPUT.text, "-O2");
    let result = Command::new(binary)
        .output()
        .expect("run recovered fixture");
    assert!(
        result.status.success(),
        "recovered fixture exited {:?}: {}\n{}",
        result.status.code(),
        String::from_utf8_lossy(&result.stderr),
        OUTPUT.text
    );
}
