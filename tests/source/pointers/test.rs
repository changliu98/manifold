#[test]
fn all_functions_present() {
    for name in [
        "test_deref_write",
        "test_array_sum",
        "test_swap",
        "test_out_param",
        "test_ptr_arith",
        "test_null_check",
    ] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn array_sum_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_array_sum"), "expected loop");
}

#[test]
fn deref_write_has_assignment() {
    assert!(
        has_assign(&OUTPUT, "test_deref_write"),
        "expected assignment"
    );
}

#[test]
fn swap_has_multiple_assignments() {
    let b = body(&OUTPUT, "test_swap");
    assert!(
        count_assignments(&OUTPUT, "test_swap") >= 3,
        "expected 3+ assignments for swap:\n{b}"
    );
}

#[test]
fn null_check_has_branch() {
    assert!(
        has_if_stmt(&OUTPUT, "test_null_check"),
        "expected branch"
    );
}

#[test]
fn out_param_writes_through_pointer() {
    let b = body(&OUTPUT, "test_out_param");
    assert!(
        has_pointer_store(&OUTPUT, "test_out_param"),
        "expected out-parameter store:\n{b}"
    );
}

#[test]
fn ptr_arith_accesses_adjacent_slots() {
    let b = body(&OUTPUT, "test_ptr_arith");
    let recovered_fields = b.contains("ofs_0") && b.contains("ofs_4");
    let raw_offsets = count_memory_accesses(&OUTPUT, "test_ptr_arith") >= 2
        && (b.contains("+ 4") || b.contains("[4]"));
    assert!(
        recovered_fields || raw_offsets,
        "expected adjacent 4-byte accesses:\n{b}"
    );
}
