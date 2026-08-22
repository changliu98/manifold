#[test]
fn all_functions_present() {
    for name in ["test_local_array_access", "test_local_array_sum", "test_address_taken",
                  "test_multiple_address_taken", "test_nested_array_init", "test_local_struct",
                  "test_struct_array", "test_address_passed_to_func", "test_large_local",
                  "test_stack_pointer_escape", "test_mixed_stack_reg",
                  "test_conditional_stack_write", "test_stack_in_loop"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn local_array_access_has_deref() {
    assert!(has_deref(&OUTPUT, "test_local_array_access")
            || has_binop(&OUTPUT, "test_local_array_access", BinaryOp::Add),
            "expected memory access for array");
}

#[test]
fn local_array_sum_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_local_array_sum"),
            "expected loop");
}

#[test]
fn address_taken_has_addition() {
    assert!(has_binop(&OUTPUT, "test_address_taken", BinaryOp::Add),
            "expected addition");
}

#[test]
fn multiple_address_taken_has_additions() {
    let b = body(&OUTPUT, "test_multiple_address_taken");
    assert!(b.matches("+").count() >= 1,
            "expected additions:\n{b}");
}

#[test]
fn nested_array_init_has_access() {
    assert!(has_deref(&OUTPUT, "test_nested_array_init")
            || body(&OUTPUT, "test_nested_array_init").contains("ofs_"),
            "expected array access");
}

#[test]
fn local_struct_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_local_struct", BinaryOp::Mul),
            "expected multiplication");
}

#[test]
fn struct_array_has_addition() {
    assert!(has_binop(&OUTPUT, "test_struct_array", BinaryOp::Add),
            "expected addition");
}

#[test]
fn address_passed_to_func_has_addition() {
    assert!(has_binop(&OUTPUT, "test_address_passed_to_func", BinaryOp::Add),
            "expected addition");
}

#[test]
fn large_local_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_large_local"),
            "expected loop");
}

#[test]
fn stack_pointer_escape_has_deref() {
    assert!(has_deref(&OUTPUT, "test_stack_pointer_escape"),
            "expected pointer dereference, return");
}

#[test]
fn mixed_stack_reg_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_mixed_stack_reg", BinaryOp::Mul),
            "expected multiplication");
}

#[test]
fn conditional_stack_write_has_branch() {
    assert!(has_if_stmt(&OUTPUT, "test_conditional_stack_write"),
            "expected if statement");
}

#[test]
fn stack_in_loop_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_stack_in_loop"),
            "expected loop");
}
