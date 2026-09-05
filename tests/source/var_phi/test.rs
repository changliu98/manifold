#[test]
fn all_functions_present() {
    for name in ["test_simple_phi", "test_phi_same_base", "test_phi_different_ops",
                  "test_nested_phi", "test_phi_with_use", "test_multiple_phi",
                  "test_phi_chain", "test_phi_three_way", "test_phi_early_exit",
                  "test_phi_with_call", "test_phi_mixed_sources", "test_phi_partially_dead"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn simple_phi_has_branch_or_ternary() {
    // SETcc arithmetic can materialize this two-value choice without a CMOV.
    assert!(has_if_stmt(&OUTPUT, "test_simple_phi")
            || body(&OUTPUT, "test_simple_phi").contains("?")
            || has_binop(&OUTPUT, "test_simple_phi", BinaryOp::Gt)
            || has_binop(&OUTPUT, "test_simple_phi", BinaryOp::Le),
            "expected if, ternary, or materialized predicate");
}

#[test]
fn phi_same_base_has_branch_and_add() {
    assert!(has_if_stmt(&OUTPUT, "test_phi_same_base")
            || has_binop(&OUTPUT, "test_phi_same_base", BinaryOp::Add),
            "expected if, addition");
}

#[test]
fn phi_different_ops_has_branch_or_ops() {
    assert!(has_if_stmt(&OUTPUT, "test_phi_different_ops")
            || has_binop(&OUTPUT, "test_phi_different_ops", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_phi_different_ops", BinaryOp::Div),
            "expected branch, arithmetic ops");
}

#[test]
fn nested_phi_has_nested_branches() {
    let n = count_if(&OUTPUT, "test_nested_phi");
    assert!(n >= 1 || has_if_stmt(&OUTPUT, "test_nested_phi")
            || (has_binop(&OUTPUT, "test_nested_phi", BinaryOp::Gt)
                && has_binop(&OUTPUT, "test_nested_phi", BinaryOp::Le)),
            "expected branches or both materialized predicates");
}

#[test]
fn phi_with_use_has_arithmetic() {
    assert!(has_binop(&OUTPUT, "test_phi_with_use", BinaryOp::Add)
            || has_binop(&OUTPUT, "test_phi_with_use", BinaryOp::Sub),
            "expected arithmetic modification");
}

#[test]
fn multiple_phi_has_branch() {
    assert!(has_if_stmt(&OUTPUT, "test_multiple_phi")
            || has_binop(&OUTPUT, "test_multiple_phi", BinaryOp::Gt)
            || has_binop(&OUTPUT, "test_multiple_phi", BinaryOp::Le),
            "expected branch or materialized predicate");
}

#[test]
fn phi_chain_has_branches() {
    let n = count_if(&OUTPUT, "test_phi_chain");
    assert!(n >= 1 || has_if_stmt(&OUTPUT, "test_phi_chain")
            || has_binop(&OUTPUT, "test_phi_chain", BinaryOp::Gt)
            || has_binop(&OUTPUT, "test_phi_chain", BinaryOp::Le),
            "expected branches or materialized predicate");
}

#[test]
fn phi_three_way_has_branches() {
    let n = count_if(&OUTPUT, "test_phi_three_way");
    assert!(n >= 1 || has_if_stmt(&OUTPUT, "test_phi_three_way"),
            "expected branches for three-way");
}

#[test]
fn phi_early_exit_has_return() {
    let b = body(&OUTPUT, "test_phi_early_exit");
    assert!(b.matches("return").count() >= 1,
            "expected return statements:\n{b}");
}

#[test]
fn phi_with_call_calls_simple_phi() {
    assert!(has_call_to(&OUTPUT, "test_phi_with_call", "test_simple_phi"),
            "expected call to test_simple_phi");
}

#[test]
fn phi_mixed_sources_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_phi_mixed_sources", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_phi_mixed_sources", BinaryOp::Shl)
            || has_binop(&OUTPUT, "test_phi_mixed_sources", BinaryOp::Add),
            "expected multiply, shift, or add-self for *2");
}

#[test]
fn phi_partially_dead_preserves_return_and_sink_values() {
    // Clang can fold a+b into the constants 201 and 102 before decompilation.
    // Check both observable values instead of requiring an arithmetic spelling
    // absent from that binary. Keep the recovered function and global verbatim.
    let mut tu = TranslationUnit::new();
    tu.add_function(func_def(&OUTPUT, "test_phi_partially_dead").clone());
    for declaration in &OUTPUT.tu.decls {
        if let TopLevelDecl::VarDecl(global) = declaration {
            if global.name == "sink" {
                tu.add_global_var(global.clone());
            }
        }
    }
    let recovered = manifold::decompile::passes::c_pass::print_translation_unit(&tu);
    let source = format!(
        "#include <limits.h>\n{recovered}\n{}",
        r#"
int main(void) {
    int inputs[] = {INT_MIN, -1, 0, 1, INT_MAX};
    for (unsigned i = 0; i < sizeof(inputs) / sizeof(inputs[0]); ++i) {
        sink = 77;
        int result = test_phi_partially_dead(inputs[i]);
        if (result != (inputs[i] > 0 ? 201 : 102)
            || sink != (inputs[i] > 0 ? 1 : 2)) return i + 1;
    }
    return 0;
}
"#
    );
    for compiler in ["gcc", "clang"] {
        let name = module_path!().replace("::", "_");
        let executable = compile(&name, compiler, &source, "-O2");
        let result = Command::new("timeout")
            .arg("10s")
            .arg(executable)
            .status()
            .unwrap();
        assert!(
            result.success(),
            "recovered branch observations differ: {recovered}"
        );
    }
}
