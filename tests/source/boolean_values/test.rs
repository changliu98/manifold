#[derive(Default)]
struct Declared(Vec<CType>);
impl ExprTransform for Declared {
    fn transform_stmt_in_expr(&mut self, stmt: CStmt) -> CStmt {
        self.transform_stmt(stmt)
    }
}
impl StmtTransform for Declared {
    fn transform_stmt(&mut self, stmt: CStmt) -> CStmt {
        match &stmt {
            CStmt::Decl(decls) | CStmt::For(Some(ForInit::Decl(decls)), _, _, _) => {
                self.0.extend(decls.iter().map(|d| d.ty.clone()));
            }
            CStmt::Block(items) => {
                for item in items {
                    if let CBlockItem::Decl(decls) = item {
                        self.0.extend(decls.iter().map(|d| d.ty.clone()));
                    }
                }
            }
            _ => {}
        }
        self.walk_stmt(stmt)
    }
}

fn declared(name: &str) -> Vec<CType> {
    let function = func_def(&OUTPUT, name);
    let mut all = Declared(function.local_vars.iter().map(|v| v.ty.clone()).collect());
    all.transform_stmt(function.body.clone());
    all.0
}

fn has_bool(name: &str) -> bool {
    declared(name).iter().any(|t| matches!(t, CType::Bool))
}

#[test]
fn comparison_and_constant_byte_webs_are_bool() {
    assert!(has_bool("count_positive"), "{}", body(&OUTPUT, "count_positive"));
}

#[test]
fn negation_cycle_stays_bool() {
    assert!(has_bool("toggle"), "{}", body(&OUTPUT, "toggle"));
}

#[test]
fn counting_byte_is_not_bool() {
    assert!(!has_bool("byte_counter"), "{}", body(&OUTPUT, "byte_counter"));
}

#[test]
fn escaped_byte_is_not_bool() {
    assert!(!has_bool("escaped_mark"), "{}", body(&OUTPUT, "escaped_mark"));
}

#[test]
fn bool_declarations_preserve_behavior_under_recompilation() {
    let mut recovered = OUTPUT.tu.clone();
    recovered.decls.retain(|decl| !matches!(decl, TopLevelDecl::FuncDef(f)
        if !["count_positive", "toggle", "byte_counter", "overwrite", "escaped_mark"]
            .contains(&f.name.as_str())));
    recovered.decls.retain(|decl| !matches!(decl, TopLevelDecl::FuncDecl(f) if f.name == "main"));
    let mut source = manifold::decompile::passes::c_pass::print_translation_unit(&recovered);
    source.push_str(r#"
int main(void) {
    int values[3] = {1, -2, 3};
    int positives[2] = {4, 5};
    if (count_positive(values, 3) != -2) return 1;
    if (count_positive(positives, 2) != 2) return 2;
    for (int n = 0; n < 6; ++n)
        if (toggle(n) != (n & 1)) return 3;
    if (byte_counter("abc") != 3) return 4;
    if (byte_counter("") != 0) return 5;
    if (escaped_mark(1) != 7 || escaped_mark(0) != 7) return 6;
    return 0;
}
"#);
    for compiler in ["gcc", "clang"] {
        let binary = compile("boolean_values_roundtrip", compiler, &source, "-O2");
        let result = Command::new(binary).output().expect("execute recovered boolean fixture");
        assert!(result.status.success(), "{compiler}: {:?}\n{source}", result.status.code());
    }
}
