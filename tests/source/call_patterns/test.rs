#[test]
fn all_functions_present() {
    for name in ["pure_func", "side_effect_func", "call_ordering",
                  "call_in_branch", "multiple_same_calls",
                  "tail_call_helper", "tail_call_wrapper",
                  "add_func", "sub_func", "apply_op", "dispatch_by_flag",
                  "chain_a", "chain_b", "chain_c",
                  "many_args_callee", "many_args_caller", "with_callback"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

// --- angr test_call_expr_folding_call_order: side-effect call ordering ---
#[test]
fn call_ordering_has_two_calls() {
    let b = body(&OUTPUT, "call_ordering");
    assert!(b.matches("side_effect_func").count() >= 2,
            "expected two calls to side_effect_func:\n{b}");
}

// --- call result in condition ---
#[test]
fn call_in_branch_calls_pure_func() {
    assert!(has_call_to(&OUTPUT, "call_in_branch", "pure_func"),
            "expected call to pure_func");
}

#[test]
fn call_in_branch_has_condition() {
    assert!(has_if_stmt(&OUTPUT, "call_in_branch"),
            "expected if checking call result");
}

// --- angr test_decompiling_morton: multiple calls to same function ---
#[test]
fn multiple_same_calls_has_three_calls() {
    let b = body(&OUTPUT, "multiple_same_calls");
    assert!(b.matches("pure_func").count() >= 3,
            "expected 3 calls to pure_func:\n{b}");
}

#[test]
fn multiple_same_calls_has_three_params() {
    assert_eq!(param_count(&OUTPUT, "multiple_same_calls"), 3,
               "multiple_same_calls takes 3 params");
}

// --- angr test_tail_calls: recursive tail call ---
#[test]
fn tail_call_helper_is_recursive() {
    // clang may eliminate tail recursion into a loop
    assert!(has_call_to(&OUTPUT, "tail_call_helper", "tail_call_helper")
            || has_any_loop(&OUTPUT, "tail_call_helper"),
            "expected recursive call or loop in tail_call_helper");
}

#[test]
fn tail_call_wrapper_calls_helper() {
    assert!(has_call_to(&OUTPUT, "tail_call_wrapper", "tail_call_helper"),
            "expected call from wrapper to helper");
}

// --- angr test_function_pointer_identification: function pointer dispatch ---
#[test]
fn apply_op_has_indirect_call() {
    let f = func_def(&OUTPUT, "apply_op");
    assert!(stmt_has_expr(&f.body, &|e| matches!(e, CExpr::Call(..))),
            "expected indirect call in apply_op");
}

#[test]
fn dispatch_by_flag_has_condition() {
    assert!(has_if_stmt(&OUTPUT, "dispatch_by_flag"),
            "expected if to select function pointer");
}

#[test]
fn dispatch_by_flag_calls_apply() {
    assert!(has_call_to(&OUTPUT, "dispatch_by_flag", "apply_op"),
            "expected call to apply_op");
}

// --- chained calls: call tree preservation ---
#[test]
fn chain_a_calls_pure_func() {
    assert!(has_call_to(&OUTPUT, "chain_a", "pure_func"),
            "expected chain_a to call pure_func");
}

#[test]
fn chain_b_calls_chain_a() {
    assert!(has_call_to(&OUTPUT, "chain_b", "chain_a"),
            "expected chain_b to call chain_a");
}

#[test]
fn chain_c_calls_chain_b() {
    assert!(has_call_to(&OUTPUT, "chain_c", "chain_b"),
            "expected chain_c to call chain_b");
}

// --- angr: many arguments including stack args ---
#[test]
fn many_args_callee_has_eight_params() {
    assert_eq!(param_count(&OUTPUT, "many_args_callee"), 8,
               "many_args_callee takes 8 params (some on stack)");
}

#[test]
fn many_args_caller_calls_callee() {
    assert!(has_call_to(&OUTPUT, "many_args_caller", "many_args_callee"),
            "expected call with stack arguments");
}

// --- callback pattern: function pointer in loop ---
#[test]
fn with_callback_has_loop() {
    assert!(has_any_loop(&OUTPUT, "with_callback"), "expected loop");
}

#[test]
fn with_callback_has_indirect_call() {
    let f = func_def(&OUTPUT, "with_callback");
    assert!(stmt_has_expr(&f.body, &|e| matches!(e, CExpr::Call(..))),
            "expected indirect call through callback");
}
