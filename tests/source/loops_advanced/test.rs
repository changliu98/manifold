#[test]
fn all_functions_present() {
    for name in ["multiple_sequential_loops", "sentinel_loop", "do_while_with_break",
                  "countdown", "loop_multi_exit", "triangle_sum",
                  "loop_with_call", "while_true_pattern"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

// --- angr test_decompiling_dirname_last_component_missing_loop: multiple for-loops ---
#[test]
fn multiple_sequential_loops_has_three_loops() {
    let b = body(&OUTPUT, "multiple_sequential_loops");
    let loops = b.matches("while").count() + b.matches("for").count() + b.matches("do").count();
    assert!(loops >= 3, "expected 3 sequential loops:\n{b}");
}

#[test]
fn multiple_sequential_loops_has_comparison() {
    assert!(has_if_stmt(&OUTPUT, "multiple_sequential_loops")
            || has_binop(&OUTPUT, "multiple_sequential_loops", BinaryOp::Gt),
            "expected comparison in max-finding loop");
}

// --- sentinel loop: while(*p) pattern ---
#[test]
fn sentinel_loop_has_loop() {
    assert!(has_any_loop(&OUTPUT, "sentinel_loop"), "expected loop");
}

#[test]
fn sentinel_loop_has_deref() {
    assert!(has_deref(&OUTPUT, "sentinel_loop")
            || has_binop(&OUTPUT, "sentinel_loop", BinaryOp::Add),
            "expected pointer dereference in sentinel loop");
}

// --- do-while with break ---
#[test]
fn do_while_with_break_has_loop() {
    assert!(has_any_loop(&OUTPUT, "do_while_with_break"), "expected loop");
}

#[test]
fn do_while_with_break_no_goto() {
    let b = body(&OUTPUT, "do_while_with_break");
    assert!(!b.contains("goto "), "do-while+break should not need goto:\n{b}");
}

// --- countdown: simple while loop ---
#[test]
fn countdown_has_loop() {
    // clang may replace simple countdown with closed-form arithmetic
    assert!(has_any_loop(&OUTPUT, "countdown")
            || has_binop(&OUTPUT, "countdown", BinaryOp::Mul)
            || has_binop(&OUTPUT, "countdown", BinaryOp::Add)
            || has_binop(&OUTPUT, "countdown", BinaryOp::Sub),
            "expected loop or arithmetic");
}

#[test]
fn countdown_has_decrement() {
    // clang may strength-reduce the loop away entirely
    assert!(has_binop(&OUTPUT, "countdown", BinaryOp::Sub)
            || has_binop(&OUTPUT, "countdown", BinaryOp::Add)
            || has_binop(&OUTPUT, "countdown", BinaryOp::Mul),
            "expected decrement or arithmetic operation");
}

// --- angr: loop with multiple exits (break + return) without goto ---
#[test]
fn loop_multi_exit_has_loop() {
    assert!(has_any_loop(&OUTPUT, "loop_multi_exit"), "expected loop");
}

#[test]
fn loop_multi_exit_no_goto() {
    let b = body(&OUTPUT, "loop_multi_exit");
    assert!(!b.contains("goto "),
            "loop with break+return should not need goto:\n{b}");
}

#[test]
fn loop_multi_exit_has_condition() {
    assert!(has_if_stmt(&OUTPUT, "loop_multi_exit"),
            "expected if inside loop");
}

// --- nested loops: triangle sum ---
#[test]
fn triangle_sum_has_nested_loops() {
    // clang may replace nested loops with closed-form arithmetic
    let b = body(&OUTPUT, "triangle_sum");
    let loops = b.matches("while").count() + b.matches("for").count() + b.matches("do").count();
    assert!(loops >= 2
            || has_binop(&OUTPUT, "triangle_sum", BinaryOp::Mul)
            || has_binop(&OUTPUT, "triangle_sum", BinaryOp::Add),
            "expected nested loops or arithmetic:\n{b}");
}

// --- angr test_call_expr_folding_call_loop: call inside loop ---
#[test]
fn loop_with_call_has_loop() {
    assert!(has_any_loop(&OUTPUT, "loop_with_call"), "expected loop");
}

#[test]
fn loop_with_call_calls_countdown() {
    assert!(has_call_to(&OUTPUT, "loop_with_call", "countdown"),
            "expected call to countdown inside loop");
}

// --- while(true) + break pattern ---
#[test]
fn while_true_pattern_has_loop() {
    assert!(has_any_loop(&OUTPUT, "while_true_pattern"), "expected loop");
}

#[test]
fn while_true_pattern_has_condition() {
    assert!(has_if_stmt(&OUTPUT, "while_true_pattern"),
            "expected break condition inside infinite loop");
}
