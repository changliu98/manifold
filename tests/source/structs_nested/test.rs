#[test]
fn all_functions_present() {
    for name in ["read_nested", "write_nested", "array_of_structs_sum",
                  "linked_list_sum", "linked_list_length", "struct_chain_access",
                  "modify_through_pointer"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

// --- angr test_struct_access: nested field access chains ---
#[test]
fn read_nested_has_field_access() {
    // Should access nested struct fields through array indexing
    assert!(has_deref(&OUTPUT, "read_nested")
            || has_binop(&OUTPUT, "read_nested", BinaryOp::Add),
            "expected memory access for nested struct read");
}

#[test]
fn read_nested_has_two_params() {
    assert_eq!(param_count(&OUTPUT, "read_nested"), 2,
               "read_nested takes pointer + index");
}

#[test]
fn write_nested_has_assignments() {
    let b = body(&OUTPUT, "write_nested");
    assert!(b.matches("=").count() >= 4,
            "expected multiple assignments for struct field writes:\n{b}");
}

// --- array of structs: loop with struct field access ---
#[test]
fn array_of_structs_has_loop() {
    assert!(has_any_loop(&OUTPUT, "array_of_structs_sum"), "expected loop");
}

#[test]
fn array_of_structs_has_addition() {
    assert!(has_binop(&OUTPUT, "array_of_structs_sum", BinaryOp::Add),
            "expected addition in sum loop");
}

// --- linked list: pointer chasing loop ---
#[test]
fn linked_list_sum_has_loop() {
    assert!(has_any_loop(&OUTPUT, "linked_list_sum"), "expected loop");
}

#[test]
fn linked_list_sum_has_null_check() {
    // The while(cur != 0) or while(cur) should produce a comparison
    assert!(has_any_loop(&OUTPUT, "linked_list_sum"), "expected loop with null check");
    assert!(has_deref(&OUTPUT, "linked_list_sum")
            || has_binop(&OUTPUT, "linked_list_sum", BinaryOp::Add),
            "expected pointer access in linked list traversal");
}

#[test]
fn linked_list_length_has_loop() {
    assert!(has_any_loop(&OUTPUT, "linked_list_length"), "expected loop");
}

// --- struct chain: access through pointer member ---
#[test]
fn struct_chain_access_has_deref() {
    assert!(has_deref(&OUTPUT, "struct_chain_access")
            || has_binop(&OUTPUT, "struct_chain_access", BinaryOp::Add),
            "expected pointer dereference for chain access");
}

// --- modify through pointer: read-modify-write pattern ---
#[test]
fn modify_through_pointer_has_assignment() {
    assert!(has_assign(&OUTPUT, "modify_through_pointer"),
            "expected assignments through pointer");
}

#[test]
fn modify_through_pointer_has_arithmetic() {
    assert!(has_binop(&OUTPUT, "modify_through_pointer", BinaryOp::Add)
            || has_binop(&OUTPUT, "modify_through_pointer", BinaryOp::Mul)
            || has_binop(&OUTPUT, "modify_through_pointer", BinaryOp::Sub),
            "expected arithmetic on struct fields");
}
