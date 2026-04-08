#[test]
fn all_functions_present() {
    for name in ["test_read_global", "test_write_global", "test_global_array_access",
                  "test_increment_global", "test_string_length", "test_use_global_string"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn global_array_access_has_branch() {
    assert!(has_if_stmt(&OUTPUT, "test_global_array_access")
            || body(&OUTPUT, "test_global_array_access").contains("return"),
            "expected branch");
}

#[test]
fn string_length_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_string_length"), "expected loop");
}

#[test]
fn write_global_has_assignment() {
    assert!(has_assign(&OUTPUT, "test_write_global"), "expected assignment");
}

#[test]
fn use_global_string_calls_strlen() {
    assert!(has_call_to(&OUTPUT, "test_use_global_string", "test_string_length"),
            "expected call to test_string_length");
}

#[test]
fn read_global_mentions_counter() {
    assert!(has_var_ref(&OUTPUT, "test_read_global", "global_counter"),
            "expected global read");
}

#[test]
fn increment_global_reads_and_writes_counter() {
    let b = body(&OUTPUT, "test_increment_global");
    assert!(b.matches("global_counter").count() >= 2, "expected read/write of global_counter:\n{b}");
    assert!(b.contains("+ 1"), "expected increment step:\n{b}");
}
