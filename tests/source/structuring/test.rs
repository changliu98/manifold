#[test]
fn all_functions_present() {
    for name in ["if_else_if_chain", "no_goto_diamond", "short_circuit_and",
                  "short_circuit_or", "single_exit_value", "complex_no_goto",
                  "guard_chain", "classify"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

// --- angr test_ifelseif_x8664: if-else-if chain ---
#[test]
fn if_else_if_chain_has_multiple_branches() {
    assert!(count_if(&OUTPUT, "if_else_if_chain") >= 3
            || has_switch(&OUTPUT, "if_else_if_chain"),
            "expected 3+ if branches or switch");
}

#[test]
fn if_else_if_chain_has_else_if_or_switch() {
    let b = body(&OUTPUT, "if_else_if_chain");
    assert!(b.contains("else") || b.contains("switch") || b.contains("case"),
            "expected else-if chain or switch:\n{b}");
}

// --- angr test_decompilation_excessive_goto_removal: no goto ---
#[test]
fn no_goto_diamond_no_goto() {
    let b = body(&OUTPUT, "no_goto_diamond");
    assert!(!b.contains("goto "), "diamond if-else should not need goto:\n{b}");
}

#[test]
fn no_goto_diamond_has_nested_ifs() {
    assert!(count_if(&OUTPUT, "no_goto_diamond") >= 2, "expected nested if-else");
}

// --- angr test_decompiling_short_circuit_O0_func_1: no goto in short-circuit ---
#[test]
fn short_circuit_and_no_goto() {
    let b = body(&OUTPUT, "short_circuit_and");
    assert!(!b.contains("goto "),
            "short-circuit AND should not need goto:\n{b}");
}

#[test]
fn short_circuit_and_has_condition() {
    assert!(has_if_stmt(&OUTPUT, "short_circuit_and"), "expected if statement");
}

#[test]
fn short_circuit_or_no_goto() {
    let b = body(&OUTPUT, "short_circuit_or");
    assert!(!b.contains("goto "),
            "short-circuit OR should not need goto:\n{b}");
}

#[test]
fn short_circuit_or_has_condition() {
    assert!(has_if_stmt(&OUTPUT, "short_circuit_or"), "expected if statement");
}

// --- angr test_return_deduplication: single return ---
#[test]
fn single_exit_value_has_ifs() {
    assert!(count_if(&OUTPUT, "single_exit_value") >= 2, "expected 2+ if branches");
}

// --- angr test_decompiling_1after909_doit: no goto in complex flow ---
#[test]
fn complex_no_goto_no_goto() {
    let b = body(&OUTPUT, "complex_no_goto");
    assert!(!b.contains("goto "),
            "complex control flow should not need goto:\n{b}");
}

#[test]
fn complex_no_goto_has_nested_ifs() {
    assert!(count_if(&OUTPUT, "complex_no_goto") >= 2, "expected nested if statements");
}

// --- angr test_sensitive_eager_returns: guard chain ---
#[test]
fn guard_chain_has_multiple_returns() {
    let b = body(&OUTPUT, "guard_chain");
    assert!(b.matches("return").count() >= 3,
            "expected multiple return statements in guard chain:\n{b}");
}

#[test]
fn guard_chain_has_multiple_ifs() {
    assert!(count_if(&OUTPUT, "guard_chain") >= 3,
            "expected 3+ guard conditions");
}

// --- classify: deeply nested if-else ---
#[test]
fn classify_has_many_branches() {
    assert!(count_if(&OUTPUT, "classify") >= 4,
            "expected many if branches in classify");
}

#[test]
fn classify_no_goto() {
    let b = body(&OUTPUT, "classify");
    assert!(!b.contains("goto "),
            "classify should not need goto:\n{b}");
}

#[test]
fn classify_has_many_returns() {
    let b = body(&OUTPUT, "classify");
    assert!(b.matches("return").count() >= 5,
            "expected many distinct return values:\n{b}");
}
