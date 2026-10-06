#[test]
fn reused_address_registers_keep_full_width_addresses() {
    let mut recovered = OUTPUT.tu.clone();
    recovered.decls.retain(|decl| !matches!(decl, TopLevelDecl::FuncDef(f)
        if !["tally", "pick_words"].contains(&f.name.as_str())));
    recovered.decls.retain(|decl| !matches!(decl, TopLevelDecl::FuncDecl(f) if f.name == "main"));
    let mut source = String::from("#include <malloc.h>\n#include <string.h>\n");
    source.push_str(&manifold::decompile::passes::c_pass::print_translation_unit(&recovered));
    source.push_str(r#"
int main(void) {
    /* Every allocation at a high mmap address, where a truncated pointer faults. */
    mallopt(M_MMAP_THRESHOLD, 0);
    int count = 0;
    char **words = pick_words("Mary had a little lamb", 4, &count);
    if (tally(10) != 36) return 1;
    if (tally(100) != 53361) return 2;
    if (count != 1 || strcmp(words[0], "little") != 0) return 3;
    return 0;
}
"#);
    for compiler in ["gcc", "clang"] {
        let binary = compile("address_register_reuse_roundtrip", compiler, &source, "-O0");
        let result = Command::new("timeout").arg("10s").arg(binary).status().unwrap();
        assert!(result.success(), "{compiler}: {:?}\n{source}", result.code());
    }
}
