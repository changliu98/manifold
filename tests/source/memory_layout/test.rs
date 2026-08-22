fn has_index_expr(func: &str) -> bool {
    let f = func_def(&OUTPUT, func);
    stmt_has_expr(&f.body, &|e| matches!(e, CExpr::Index(..)))
}

#[test]
fn all_functions_present() {
    for name in [
        "multidim_index",
        "nested_global_index",
        "pointer_to_pointer_walk",
        "struct_array_offsets",
        "local_aggregate_use",
        "byte_word_access",
    ] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn multidim_index_uses_global_grid_and_scaled_indexing() {
    let b = body(&OUTPUT, "multidim_index");
    assert!(
        has_index_expr("multidim_index")
            || has_deref(&OUTPUT, "multidim_index")
            || has_binop(&OUTPUT, "multidim_index", BinaryOp::Add),
        "expected multidimensional indexing or address arithmetic:\n{b}"
    );
}

#[test]
fn multidim_index_has_two_params() {
    assert_eq!(
        param_count(&OUTPUT, "multidim_index"),
        2,
        "multidim_index takes row and column"
    );
}

#[test]
fn nested_global_index_uses_bucket_array() {
    let b = body(&OUTPUT, "nested_global_index");
    assert!(
        has_index_expr("nested_global_index")
            || has_deref(&OUTPUT, "nested_global_index")
            || has_binop(&OUTPUT, "nested_global_index", BinaryOp::Add),
        "expected nested global array access:\n{b}"
    );
}

#[test]
fn nested_global_index_has_two_params() {
    assert_eq!(
        param_count(&OUTPUT, "nested_global_index"),
        2,
        "nested_global_index takes bucket and slot"
    );
}

#[test]
fn pointer_to_pointer_walk_has_loop_and_memory_access() {
    assert!(
        has_any_loop(&OUTPUT, "pointer_to_pointer_walk"),
        "expected traversal loop"
    );
    assert!(
        has_index_expr("pointer_to_pointer_walk") || has_deref(&OUTPUT, "pointer_to_pointer_walk"),
        "expected pointer-to-pointer load"
    );
}

#[test]
fn pointer_to_pointer_walk_has_two_params() {
    assert_eq!(
        param_count(&OUTPUT, "pointer_to_pointer_walk"),
        2,
        "pointer_to_pointer_walk takes rows pointer and length"
    );
}

#[test]
fn struct_array_offsets_walks_fields_in_loop() {
    assert!(
        has_any_loop(&OUTPUT, "struct_array_offsets"),
        "expected struct array loop"
    );
    assert!(
        has_field_access(&OUTPUT, "struct_array_offsets", "tag")
            || has_field_access(&OUTPUT, "struct_array_offsets", "count")
            || has_field_access(&OUTPUT, "struct_array_offsets", "value")
            || has_deref(&OUTPUT, "struct_array_offsets")
            || has_binop(&OUTPUT, "struct_array_offsets", BinaryOp::Add),
        "expected field-like accesses or equivalent offsets"
    );
}

#[test]
fn local_aggregate_use_has_stack_layout_activity() {
    let b = body(&OUTPUT, "local_aggregate_use");
    assert!(
        has_assign(&OUTPUT, "local_aggregate_use")
            || has_index_expr("local_aggregate_use")
            || has_field_access(&OUTPUT, "local_aggregate_use", "value")
            || b.contains("ofs_"),
        "expected local aggregate initialization/use:\n{b}"
    );
}

#[test]
fn byte_word_access_reads_and_writes_memory() {
    assert!(
        has_assign(&OUTPUT, "byte_word_access"),
        "expected writes through byte and word pointers"
    );
    assert!(
        has_index_expr("byte_word_access")
            || has_deref(&OUTPUT, "byte_word_access")
            || has_binop(&OUTPUT, "byte_word_access", BinaryOp::Add),
        "expected byte/word pointer memory accesses"
    );
}

#[test]
fn byte_word_access_has_three_params() {
    assert_eq!(
        param_count(&OUTPUT, "byte_word_access"),
        3,
        "byte_word_access takes byte pointer, word pointer, and index"
    );
}
