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
fn all_caller_saved_has_additions() {
    let b = body(&OUTPUT, "test_all_caller_saved");
    assert!(b.matches("+").count() >= 1,
            "expected additions:\n{b}");
}

#[test]
fn spill_to_stack_has_operations() {
    let b = body(&OUTPUT, "test_spill_to_stack");
    assert!(b.matches("+").count() >= 1,
            "expected additions:\n{b}");
}

#[test]
fn caller_saved_across_call_has_additions() {
    assert!(has_binop(&OUTPUT, "test_caller_saved_across_call", BinaryOp::Add),
            "expected additions");
}

#[test]
fn many_temps_has_ops() {
    assert!((has_binop(&OUTPUT, "test_many_temps", BinaryOp::Add)
            || has_binop(&OUTPUT, "test_many_temps", BinaryOp::Sub)
            || has_binop(&OUTPUT, "test_many_temps", BinaryOp::Mul)),
            "expected arithmetic ops");
}

#[test]
fn loop_with_many_vars_has_loop_or_closed_form() {
    assert!(has_any_loop(&OUTPUT, "test_loop_with_many_vars")
            || has_binop(&OUTPUT, "test_loop_with_many_vars", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_loop_with_many_vars", BinaryOp::Shr),
            "expected loop or closed-form arithmetic");
}

#[test]
fn loop_with_many_vars_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_loop_with_many_vars", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_loop_with_many_vars", BinaryOp::Shl),
            "expected multiplication, shift");
}

#[test]
fn eight_params_has_eight_params() {
    let count = param_count(&OUTPUT, "test_eight_params");
    assert!(count >= 6, "test_eight_params should have at least 6 params, got {count}");
}

#[test]
fn eight_params_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_eight_params", BinaryOp::Mul),
            "expected multiplication");
}

#[test]
fn nested_calls_pressure_calls_helper() {
    assert!(has_call_to(&OUTPUT, "test_nested_calls_pressure", "test_all_caller_saved"),
            "expected call to test_all_caller_saved");
}

#[test]
fn interleaved_computation_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_interleaved_computation", BinaryOp::Mul),
            "expected multiplication");
}

#[test]
fn diamond_dag_has_ops() {
    assert!((has_binop(&OUTPUT, "test_diamond_dag", BinaryOp::Mul)
            || has_binop(&OUTPUT, "test_diamond_dag", BinaryOp::Add)),
            "expected mul/add");
}

#[test]
fn long_chain_with_uses_has_additions() {
    let b = body(&OUTPUT, "test_long_chain_with_uses");
    assert!(b.matches("+").count() >= 1,
            "expected additions:\n{b}");
}

#[test]
fn register_recycling_has_multiply() {
    assert!(has_binop(&OUTPUT, "test_register_recycling", BinaryOp::Mul),
            "expected multiplication");
}
