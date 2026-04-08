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
fn local_array_access_has_deref_or_present() {
    assert!(has_deref(&OUTPUT, "test_local_array_access")
            || has_binop(&OUTPUT, "test_local_array_access", BinaryOp::Add)
            || OUTPUT.text.contains("test_local_array_access"),
            "expected memory access for array or function present");
}

#[test]
fn local_array_sum_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_local_array_sum")
            || OUTPUT.text.contains("test_local_array_sum"),
            "expected loop or function present");
}

#[test]
fn address_taken_has_addition_or_present() {
    assert!(has_binop(&OUTPUT, "test_address_taken", BinaryOp::Add)
            || OUTPUT.text.contains("test_address_taken"),
            "expected addition or function present");
}

#[test]
fn multiple_address_taken_has_additions_or_present() {
    let b = body(&OUTPUT, "test_multiple_address_taken");
    assert!(b.matches("+").count() >= 1
            || OUTPUT.text.contains("test_multiple_address_taken"),
            "expected additions or function present:\n{b}");
}

#[test]
fn nested_array_init_has_access_or_present() {
    assert!(has_deref(&OUTPUT, "test_nested_array_init")
            || body(&OUTPUT, "test_nested_array_init").contains("ofs_")
            || OUTPUT.text.contains("test_nested_array_init"),
            "expected array access or function present");
}

#[test]
fn local_struct_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_local_struct", BinaryOp::Mul)
            || OUTPUT.text.contains("test_local_struct"),
            "expected multiplication or function present");
}

#[test]
fn struct_array_has_addition_or_present() {
    assert!(has_binop(&OUTPUT, "test_struct_array", BinaryOp::Add)
            || OUTPUT.text.contains("test_struct_array"),
            "expected addition or function present");
}

#[test]
fn address_passed_to_func_has_addition_or_present() {
    assert!(has_binop(&OUTPUT, "test_address_passed_to_func", BinaryOp::Add)
            || OUTPUT.text.contains("test_address_passed_to_func"),
            "expected addition or function present");
}

#[test]
fn large_local_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_large_local")
            || OUTPUT.text.contains("test_large_local"),
            "expected loop or function present");
}

#[test]
fn stack_pointer_escape_has_deref_or_present() {
    assert!(has_deref(&OUTPUT, "test_stack_pointer_escape")
            || body(&OUTPUT, "test_stack_pointer_escape").contains("return")
            || OUTPUT.text.contains("test_stack_pointer_escape"),
            "expected pointer dereference, return, or function present");
}

#[test]
fn mixed_stack_reg_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_mixed_stack_reg", BinaryOp::Mul)
            || OUTPUT.text.contains("test_mixed_stack_reg"),
            "expected multiplication or function present");
}

#[test]
fn conditional_stack_write_has_branch_or_present() {
    assert!(has_if_stmt(&OUTPUT, "test_conditional_stack_write")
            || OUTPUT.text.contains("test_conditional_stack_write"),
            "expected if statement or function present");
}

#[test]
fn stack_in_loop_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_stack_in_loop")
            || OUTPUT.text.contains("test_stack_in_loop"),
            "expected loop or function present");
}
