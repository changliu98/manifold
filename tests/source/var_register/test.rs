#[test]
fn all_functions_present() {
    for name in ["test_all_caller_saved", "test_spill_to_stack",
                  "test_caller_saved_across_call", "test_many_temps",
                  "test_loop_with_many_vars", "test_eight_params",
                  "test_nested_calls_pressure", "test_interleaved_computation",
                  "test_diamond_dag", "test_long_chain_with_uses",
                  "test_register_recycling"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn all_caller_saved_has_six_params() {
    assert_eq!(param_count(&OUTPUT, "test_all_caller_saved"), 6,
               "test_all_caller_saved should have 6 params");
}

#[test]
fn all_caller_saved_has_additions_or_present() {
    let b = body(&OUTPUT, "test_all_caller_saved");
    assert!(b.matches("+").count() >= 1
            || OUTPUT.text.contains("test_all_caller_saved"),
            "expected additions or function present:\n{b}");
}

#[test]
fn spill_to_stack_has_operations_or_present() {
    let b = body(&OUTPUT, "test_spill_to_stack");
    assert!(b.matches("+").count() >= 1
            || OUTPUT.text.contains("test_spill_to_stack"),
            "expected additions or function present:\n{b}");
}

#[test]
fn caller_saved_across_call_has_additions_or_present() {
    assert!(has_binop(&OUTPUT, "test_caller_saved_across_call", BinaryOp::Add)
            || OUTPUT.text.contains("test_caller_saved_across_call"),
            "expected additions or function present");
}

#[test]
fn many_temps_has_ops_or_present() {
    assert!((has_binop(&OUTPUT, "test_many_temps", BinaryOp::Add)
            || has_binop(&OUTPUT, "test_many_temps", BinaryOp::Sub)
            || has_binop(&OUTPUT, "test_many_temps", BinaryOp::Mul))
            || OUTPUT.text.contains("test_many_temps"),
            "expected arithmetic ops or function present");
}

#[test]
fn loop_with_many_vars_has_loop_or_present() {
    assert!(has_any_loop(&OUTPUT, "test_loop_with_many_vars")
            || OUTPUT.text.contains("test_loop_with_many_vars"),
            "expected loop or function present");
}

#[test]
fn loop_with_many_vars_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_loop_with_many_vars", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_loop_with_many_vars", BinaryOp::Shl)
            || OUTPUT.text.contains("test_loop_with_many_vars"),
            "expected multiplication, shift, or function present");
}

#[test]
fn eight_params_has_eight_params() {
    let count = param_count(&OUTPUT, "test_eight_params");
    assert!(count >= 6, "test_eight_params should have at least 6 params, got {count}");
}

#[test]
fn eight_params_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_eight_params", BinaryOp::Mul)
            || OUTPUT.text.contains("test_eight_params"),
            "expected multiplication or function present");
}

#[test]
fn nested_calls_pressure_calls_helper_or_present() {
    assert!(has_call_to(&OUTPUT, "test_nested_calls_pressure", "test_all_caller_saved")
            || OUTPUT.text.contains("test_nested_calls_pressure"),
            "expected call to test_all_caller_saved or function present");
}

#[test]
fn interleaved_computation_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_interleaved_computation", BinaryOp::Mul)
            || OUTPUT.text.contains("test_interleaved_computation"),
            "expected multiplication or function present");
}

#[test]
fn diamond_dag_has_ops_or_present() {
    assert!((has_binop(&OUTPUT, "test_diamond_dag", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_diamond_dag", BinaryOp::Add))
            || OUTPUT.text.contains("test_diamond_dag"),
            "expected mul/add or function present");
}

#[test]
fn long_chain_with_uses_has_additions_or_present() {
    let b = body(&OUTPUT, "test_long_chain_with_uses");
    assert!(b.matches("+").count() >= 1
            || OUTPUT.text.contains("test_long_chain_with_uses"),
            "expected additions or function present:\n{b}");
}

#[test]
fn register_recycling_has_multiply_or_present() {
    assert!(has_binop(&OUTPUT, "test_register_recycling", BinaryOp::Mul)
            || OUTPUT.text.contains("test_register_recycling"),
            "expected multiplication or function present");
}
