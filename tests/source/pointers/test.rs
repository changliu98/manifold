#[test]
fn all_functions_present() {
    for name in ["test_deref_write", "test_array_sum", "test_swap",
                  "test_out_param", "test_ptr_arith", "test_null_check"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn array_sum_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_array_sum"), "expected loop");
}

#[test]
fn deref_write_has_assignment() {
    assert!(has_assign(&OUTPUT, "test_deref_write"), "expected assignment");
}

#[test]
fn swap_has_multiple_assignments() {
    let b = body(&OUTPUT, "test_swap");
    assert!(b.matches("=").count() >= 3, "expected 3+ assignments for swap:\n{b}");
}

#[test]
fn null_check_has_branch() {
    assert!(has_if_stmt(&OUTPUT, "test_null_check")
            || body(&OUTPUT, "test_null_check").contains("return"),
            "expected branch");
}

#[test]
fn out_param_writes_through_pointer() {
    let b = body(&OUTPUT, "test_out_param");
    assert!(b.contains("ofs_0 ="), "expected out-parameter store:\n{b}");
}

#[test]
fn ptr_arith_accesses_adjacent_slots() {
    let b = body(&OUTPUT, "test_ptr_arith");
    assert!(b.contains("ofs_0"), "expected base slot load:\n{b}");
    assert!(b.contains("ofs_4"), "expected adjacent slot access:\n{b}");
}
