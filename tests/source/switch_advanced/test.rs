#[test]
fn all_functions_present() {
    for name in ["switch_with_default", "switch_no_default", "switch_sparse",
                  "switch_in_loop", "switch_nested", "switch_with_fallthrough",
                  "switch_many_cases"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

// --- angr switch0: switch with default ---
#[test]
fn switch_with_default_has_switch_or_ifs() {
    assert!(has_switch(&OUTPUT, "switch_with_default")
            || count_if(&OUTPUT, "switch_with_default") >= 4,
            "expected switch or if-chain");
}

#[test]
fn switch_with_default_has_default_path() {
    // The default case assigns -1; verify the constant is present
    let b = body(&OUTPUT, "switch_with_default");
    assert!(b.contains("-1") || b.contains("0xffffffff") || b.contains("4294967295"),
            "expected default value -1:\n{b}");
}

// --- angr switch1: switch without default ---
#[test]
fn switch_no_default_has_switch_or_ifs() {
    assert!(has_switch(&OUTPUT, "switch_no_default")
            || count_if(&OUTPUT, "switch_no_default") >= 2,
            "expected switch or if-chain for 4-case switch");
}

// --- angr: sparse switch values ---
#[test]
fn switch_sparse_has_dispatch() {
    assert!(has_switch(&OUTPUT, "switch_sparse")
            || count_if(&OUTPUT, "switch_sparse") >= 3,
            "expected switch or if-chain for sparse values");
}

// --- angr: switch inside loop ---
#[test]
fn switch_in_loop_has_loop_and_dispatch() {
    assert!(has_any_loop(&OUTPUT, "switch_in_loop"), "expected loop");
    assert!(has_switch(&OUTPUT, "switch_in_loop")
            || count_if(&OUTPUT, "switch_in_loop") >= 2,
            "expected switch or if-chain inside loop");
}

// --- angr: nested switch (compiler may flatten at -O1) ---
#[test]
fn switch_nested_has_dispatch() {
    assert!(has_switch(&OUTPUT, "switch_nested")
            || count_if(&OUTPUT, "switch_nested") >= 2,
            "expected dispatch for nested switch");
}

// --- angr switch2: switch with fallthrough ---
#[test]
fn switch_with_fallthrough_has_dispatch() {
    assert!(has_switch(&OUTPUT, "switch_with_fallthrough")
            || count_if(&OUTPUT, "switch_with_fallthrough") >= 3,
            "expected switch or if-chain for fallthrough pattern");
}

// --- angr: large jump table switch (16 cases) ---
#[test]
fn switch_many_cases_has_dispatch() {
    assert!(has_switch(&OUTPUT, "switch_many_cases")
            || count_if(&OUTPUT, "switch_many_cases") >= 8,
            "expected switch or many ifs for 16-case jump table");
}

#[test]
fn switch_many_cases_has_square_values() {
    let b = body(&OUTPUT, "switch_many_cases");
    // At least some of the squared return values should appear
    let squares_found = ["100", "121", "144", "169", "196", "225"]
        .iter().filter(|s| b.contains(**s)).count();
    assert!(squares_found >= 3, "expected several squared return values:\n{b}");
}
