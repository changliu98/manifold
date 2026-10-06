#[derive(Default)]
struct LocalTypes(Vec<CType>);
impl ExprTransform for LocalTypes {
    fn transform_stmt_in_expr(&mut self, stmt: CStmt) -> CStmt {
        self.transform_stmt(stmt)
    }
}
impl StmtTransform for LocalTypes {
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
fn local_types(name: &str) -> Vec<CType> {
    let function = func_def(&OUTPUT, name);
    let mut types = LocalTypes(function.local_vars.iter().map(|d| d.ty.clone()).collect());
    types.transform_stmt(function.body.clone());
    types.0
}

#[test]
fn recovered_word_storage_has_a_word_declaration() {
    assert!(local_types("word_cell").iter().any(|t| matches!(t, CType::Int(IntSize::Int, _))),
            "{}", body(&OUTPUT, "word_cell"));
}

#[test]
fn independent_wide_storage_keeps_its_width() {
    assert!(local_types("wide_cell").iter().any(|t| matches!(t, CType::Int(IntSize::Long | IntSize::LongLong, _))),
            "{}", body(&OUTPUT, "wide_cell"));
}

#[test]
fn byte_storage_keeps_narrowing_visible() {
    assert!(has_assign(&OUTPUT, "byte_cell"), "{}", body(&OUTPUT, "byte_cell"));
}

#[test]
fn promoted_call_argument_keeps_the_physical_byte_declaration() {
    assert!(local_types("signed_byte_argument").iter().any(|t| matches!(t, CType::Int(IntSize::Char, _))),
            "{}", body(&OUTPUT, "signed_byte_argument"));
}

#[test]
fn pointer_arithmetic_and_all_callees_survive() {
    for name in ["word_cell", "wide_cell", "byte_cell", "character_cursor"] {
        func_def(&OUTPUT, name);
    }
    assert!(has_binop(&OUTPUT, "character_cursor", BinaryOp::Add),
            "{}", body(&OUTPUT, "character_cursor"));
}

#[test]
fn selected_types_preserve_observations_under_optimizing_recompilation() {
    // Keep the caller fixed: this test measures recovered implementation and
    // ABI behavior, independently of recovering the caller's initializers.
    let mut recovered = OUTPUT.tu.clone();
    recovered.decls.retain(|decl| !matches!(decl, TopLevelDecl::FuncDef(f)
        if !["word_cell", "wide_cell", "byte_cell", "character_cursor", "scalar_sink", "signed_byte_argument"].contains(&f.name.as_str())));
    recovered.decls.retain(|decl| !matches!(decl, TopLevelDecl::FuncDecl(f) if f.name == "main"));
    let mut source = manifold::decompile::passes::c_pass::print_translation_unit(&recovered);
    source.push_str(r#"
#include <stdint.h>
int main(void) {
    unsigned char text[2] = {'a', 'b'};
    if ((uint32_t)word_cell(UINT32_MAX) != (UINT32_MAX ^ UINT32_C(0x81234567))) return 1;
    if ((uint64_t)wide_cell(UINT64_C(0x100000001)) != UINT64_C(0x200000002)) return 2;
    if (*(unsigned char *)(uintptr_t)character_cursor(text) != 'b') return 3;
    if (byte_cell(257) != 1 || byte_cell(255) != 255 || byte_cell(128) != 128) return 4;
    const int inputs[] = {0, 1, 127, 128, 255, 256, -129, 65537};
    for (unsigned i = 0; i < sizeof(inputs) / sizeof(inputs[0]); ++i) {
        int byte = (unsigned)inputs[i] & 255;
        if (byte >= 128) byte -= 256;
        int expected = byte == 0 ? 7 : byte * 3 + 1;
        if ((int32_t)signed_byte_argument(inputs[i]) != expected) return 5;
    }
    return 0;
}
"#);
    for compiler in ["gcc", "clang"] {
        let binary = compile("type_recovery_roundtrip", compiler, &source, "-O2");
        let result = Command::new(binary).output().expect("execute recovered type fixture");
        assert!(result.status.success(), "{compiler}: {:?}\n{source}", result.status.code());
    }
}
