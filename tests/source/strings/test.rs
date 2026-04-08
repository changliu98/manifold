#[test]
fn all_functions_present() {
    for name in ["my_strlen", "my_strcmp", "count_char", "reverse_inplace",
                  "string_search", "use_string_literal", "my_strcpy"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

// --- angr test_decompiling_strings_local_strlen: strlen-like loop pattern ---
#[test]
fn strlen_has_loop() {
    assert!(has_any_loop(&OUTPUT, "my_strlen"), "strlen should have a loop");
}

#[test]
fn strlen_has_one_param() {
    assert_eq!(param_count(&OUTPUT, "my_strlen"), 1, "strlen takes one pointer param");
}

// --- angr test_decompiling_strings_local_strcat: two-pointer string function ---
#[test]
fn strcmp_has_two_params() {
    assert_eq!(param_count(&OUTPUT, "my_strcmp"), 2, "strcmp takes two pointer params");
}

#[test]
fn strcmp_has_loop_and_comparison() {
    assert!(has_any_loop(&OUTPUT, "my_strcmp"), "strcmp should have a loop");
    assert!(has_binop(&OUTPUT, "my_strcmp", BinaryOp::Sub)
            || has_binop(&OUTPUT, "my_strcmp", BinaryOp::Eq)
            || has_binop(&OUTPUT, "my_strcmp", BinaryOp::Ne),
            "strcmp should compare characters");
}

// --- count_char: loop with conditional increment ---
#[test]
fn count_char_has_loop_and_if() {
    assert!(has_any_loop(&OUTPUT, "count_char"), "expected loop");
    assert!(has_if_stmt(&OUTPUT, "count_char")
            || has_binop(&OUTPUT, "count_char", BinaryOp::Eq),
            "expected comparison in character counting");
}

// --- reverse_inplace: calls my_strlen, has loop ---
#[test]
fn reverse_calls_strlen() {
    assert!(has_call_to(&OUTPUT, "reverse_inplace", "my_strlen"),
            "reverse should call my_strlen");
}

#[test]
fn reverse_has_loop() {
    assert!(has_any_loop(&OUTPUT, "reverse_inplace"), "reverse should have a loop");
}

// --- string_search: nested loops ---
#[test]
fn string_search_has_nested_loops() {
    let b = body(&OUTPUT, "string_search");
    let loops = b.matches("while").count() + b.matches("for").count() + b.matches("do").count();
    assert!(loops >= 2, "string_search should have nested loops:\n{b}");
}

#[test]
fn string_search_calls_strlen() {
    assert!(has_call_to(&OUTPUT, "string_search", "my_strlen"),
            "string_search should call my_strlen");
}

// --- angr test_decompiling_strings_c_representation: string literal recovery ---
#[test]
fn use_string_literal_has_string_refs() {
    let b = body(&OUTPUT, "use_string_literal");
    assert!(b.contains("hello") || b.contains("goodbye") || b.contains("\""),
            "expected string literal references:\n{b}");
}

#[test]
fn use_string_literal_has_conditional() {
    assert!(has_if_stmt(&OUTPUT, "use_string_literal"), "expected if statement");
}

// --- angr test_simple_strcpy: post-increment loop pattern ---
#[test]
fn strcpy_has_loop() {
    assert!(has_any_loop(&OUTPUT, "my_strcpy"), "strcpy should have a loop");
}
