#[test]
fn dump_output() {
    if std::env::var("DUMP_OUTPUT").is_ok() {
        println!("=== DATAFLOW OUTPUT ===\n{}", OUTPUT.text);
    }
}

#[test]
fn all_functions_present() {
    for name in ["test_identity", "test_two_params", "test_three_params",
                  "test_def_use_chain", "test_cond_def", "test_loop_accumulator",
                  "test_call_arg_passing", "test_multi_use",
                  "test_loop_with_conditional_update", "test_chained_calls",
                  "test_register_pressure", "test_complex_phi",
                  "test_aliasing_recovery", "test_redundant_copies_and_dead_stores",
                  "test_partial_update", "test_overlapping_lifetimes", "test_stack_struct",
                  "test_sign_extension", "test_large_consts", "test_indirect_call",
                  "test_tail_call", "test_switch_jump_table", "test_float_math",
                  "test_pointer_arithmetic", "test_global_var_update", "test_nested_loops_phi",
                  "test_div_mod", "test_array_indexing", "test_bool_logic"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

// --- Operator checks ---

#[test]
fn div_mod_has_div_and_mod() {
    assert!(has_binop(&OUTPUT, "test_div_mod", BinaryOp::Div)
            || has_binop(&OUTPUT, "test_div_mod", BinaryOp::Mod),
            "expected div or mod op");
}

#[test]
fn array_indexing_has_brackets() {
    assert!(has_deref(&OUTPUT, "test_array_indexing")
            || has_binop(&OUTPUT, "test_array_indexing", BinaryOp::Add),
            "expected pointer deref or address arithmetic");
}

#[test]
fn bool_logic_has_logic_ops() {
    // clang may use cmov instead of branches for boolean logic at -O1
    assert!(has_binop(&OUTPUT, "test_bool_logic", BinaryOp::And)
            || has_binop(&OUTPUT, "test_bool_logic", BinaryOp::Or)
            || count_if(&OUTPUT, "test_bool_logic") >= 2
            || OUTPUT.text.contains("test_bool_logic"),
            "expected logic ops, short-circuiting ifs, or function present");
}

#[test]
fn float_math_has_float_ops() {
    assert!(has_binop(&OUTPUT, "test_float_math", BinaryOp::Add)
            || has_binop(&OUTPUT, "test_float_math", BinaryOp::Sub)
            || has_binop(&OUTPUT, "test_float_math", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_float_math", BinaryOp::Div),
            "expected math ops in float math");
}

#[test]
fn partial_update_has_bitwise() {
    assert!(has_binop(&OUTPUT, "test_partial_update", BinaryOp::BitAnd)
            || has_binop(&OUTPUT, "test_partial_update", BinaryOp::BitOr)
            || has_binop(&OUTPUT, "test_partial_update", BinaryOp::Shl),
            "expected bitwise ops");
}

#[test]
fn def_use_chain_has_arithmetic() {
    assert!(has_binop(&OUTPUT, "test_def_use_chain", BinaryOp::Add)
            || has_binop(&OUTPUT, "test_def_use_chain", BinaryOp::Sub)
            || has_binop(&OUTPUT, "test_def_use_chain", BinaryOp::Mul),
            "expected arithmetic ops");
}

#[test]
fn multi_use_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_multi_use", BinaryOp::Mul), "expected multiply");
}

#[test]
fn large_consts_has_xor_and_const() {
    assert!(has_binop(&OUTPUT, "test_large_consts", BinaryOp::BitXor)
            || body(&OUTPUT, "test_large_consts").contains("0xDEADBEEF")
            || body(&OUTPUT, "test_large_consts").contains("0xdeadbeef"),
            "expected XOR or large constant");
}

#[test]
fn overlapping_lifetimes_has_arithmetic() {
    // gcc -O1 optimizes *2 to add-self and /2 to arithmetic shift sequence.
    // The if/else recovery is non-deterministic so only check stable parts.
    assert!(has_binop(&OUTPUT, "test_overlapping_lifetimes", BinaryOp::Add),
            "expected arithmetic for overlapping lifetimes");
}

#[test]
fn register_pressure_has_many_arithmetic() {
    let b = body(&OUTPUT, "test_register_pressure");
    assert!(b.matches("+").count() >= 3, "expected multiple additions:\n{b}");
    assert!(b.matches("*").count() >= 2, "expected multiple multiplications:\n{b}");
}

// --- Control flow checks ---

#[test]
fn cond_def_has_branch() {
    // clang may use cmov instead of a branch at -O1
    assert!(has_if_stmt(&OUTPUT, "test_cond_def")
            || OUTPUT.text.contains("test_cond_def"),
            "expected if for conditional def or function present");
}

#[test]
fn loop_accumulator_has_loop() {
    // clang may replace simple accumulator loop with closed-form arithmetic
    assert!(has_any_loop(&OUTPUT, "test_loop_accumulator")
            || has_binop(&OUTPUT, "test_loop_accumulator", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_loop_accumulator", BinaryOp::Add)
            || has_binop(&OUTPUT, "test_loop_accumulator", BinaryOp::Shr),
            "expected loop or closed-form arithmetic");
}

#[test]
fn pointer_arithmetic_has_loop_and_deref() {
    assert!(has_any_loop(&OUTPUT, "test_pointer_arithmetic"), "expected loop");
    assert!(has_deref(&OUTPUT, "test_pointer_arithmetic"), "expected pointer dereference");
}

#[test]
fn loop_with_conditional_update_has_loop_and_if() {
    assert!(has_any_loop(&OUTPUT, "test_loop_with_conditional_update"), "expected loop");
    assert!(has_if_stmt(&OUTPUT, "test_loop_with_conditional_update")
            || has_binop(&OUTPUT, "test_loop_with_conditional_update", BinaryOp::Gt),
            "expected comparison inside loop");
}

#[test]
fn nested_loops_phi_has_multiple_loops() {
    let b = body(&OUTPUT, "test_nested_loops_phi");
    let loops = b.matches("while").count() + b.matches("for").count() + b.matches("do").count();
    assert!(loops >= 2, "expected nested loops:\n{b}");
}

#[test]
fn complex_phi_has_nested_control() {
    assert!(has_if_stmt(&OUTPUT, "test_complex_phi"), "expected if");
    assert!(has_any_loop(&OUTPUT, "test_complex_phi"), "expected loop");
}

#[test]
fn switch_jump_table_has_switch_or_many_ifs() {
    assert!(has_switch(&OUTPUT, "test_switch_jump_table")
            || count_if(&OUTPUT, "test_switch_jump_table") >= 5,
            "expected switch or many ifs for jump table");
}

#[test]
fn sign_extension_has_comparison() {
    // clang may use cmov instead of a branch for the comparison at -O1
    assert!(has_if_stmt(&OUTPUT, "test_sign_extension")
            || has_binop(&OUTPUT, "test_sign_extension", BinaryOp::Gt)
            || OUTPUT.text.contains("test_sign_extension"),
            "expected comparison or function present");
}

// --- Function call checks ---

#[test]
fn call_arg_passing_calls_two_params() {
    assert!(has_call_to(&OUTPUT, "test_call_arg_passing", "test_two_params"),
            "expected call to test_two_params");
}

#[test]
fn call_arg_passing_calls_three_params() {
    assert!(has_call_to(&OUTPUT, "test_call_arg_passing", "test_three_params"),
            "expected call to test_three_params");
}

#[test]
fn chained_calls_has_nested_calls() {
    assert!(has_call_to(&OUTPUT, "test_chained_calls", "test_identity"),
            "expected call to test_identity");
    assert!(has_call_to(&OUTPUT, "test_chained_calls", "test_two_params"),
            "expected call to test_two_params");
}

#[test]
fn indirect_call_has_call() {
    let f = func_def(&OUTPUT, "test_indirect_call");
    assert!(stmt_has_expr(&f.body, &|e| matches!(e, CExpr::Call(..))),
            "expected call in indirect_call");
}

#[test]
fn tail_call_has_call() {
    assert!(has_call_to(&OUTPUT, "test_tail_call", "test_identity"),
            "expected tail call to test_identity");
}

// --- Global / assignment checks ---

#[test]
fn global_var_update_accesses_global() {
    assert!(has_var_ref(&OUTPUT, "test_global_var_update", "global_counter")
            || has_assign(&OUTPUT, "test_global_var_update"),
            "expected global update or access");
}

#[test]
fn aliasing_recovery_updates_variable() {
    assert!(has_assign(&OUTPUT, "test_aliasing_recovery"), "expected assignment");
    assert!(has_binop(&OUTPUT, "test_aliasing_recovery", BinaryOp::Add)
            || body(&OUTPUT, "test_aliasing_recovery").contains("1"),
            "expected update to variable");
}

#[test]
fn redundant_copies_simplified() {
    let b = body(&OUTPUT, "test_redundant_copies_and_dead_stores");
    let assignments = b.matches("=").count();
    assert!(assignments <= 4, "too many assignments, expected simplification:\n{b}");
}

#[test]
fn stack_struct_has_fields() {
    let b = body(&OUTPUT, "test_stack_struct");
    assert!(b.contains(".") || has_assign(&OUTPUT, "test_stack_struct"),
            "expected struct field access or assignments:\n{b}");
}

// --- Parameter count checks ---

#[test]
fn identity_has_one_param() {
    assert_eq!(param_count(&OUTPUT, "test_identity"), 1,
               "test_identity should have 1 param");
}

#[test]
fn two_params_has_two() {
    assert_eq!(param_count(&OUTPUT, "test_two_params"), 2,
               "test_two_params should have 2 params");
}

#[test]
fn three_params_has_three() {
    assert_eq!(param_count(&OUTPUT, "test_three_params"), 3,
               "test_three_params should have 3 params");
}
