#[test]
fn all_functions_present() {
    for name in ["test_factorial", "test_fibonacci", "test_gcd",
                  "test_iterative_factorial", "test_mutual_even", "test_mutual_odd"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn factorial_calls_itself() {
    // clang may eliminate tail recursion into a loop
    assert!(has_call_to(&OUTPUT, "test_factorial", "test_factorial")
            || has_any_loop(&OUTPUT, "test_factorial"),
            "expected recursive call or loop");
}

#[test]
fn fibonacci_calls_itself() {
    assert!(has_call_to(&OUTPUT, "test_fibonacci", "test_fibonacci"), "expected recursive call");
}

#[test]
fn gcd_calls_itself() {
    // clang may eliminate tail recursion into a loop
    assert!(has_call_to(&OUTPUT, "test_gcd", "test_gcd")
            || has_any_loop(&OUTPUT, "test_gcd"),
            "expected recursive call or loop");
}

#[test]
fn iterative_factorial_has_loop() {
    assert!(has_any_loop(&OUTPUT, "test_iterative_factorial"), "expected loop");
}

#[test]
fn mutual_even_calls_odd() {
    assert!(has_call_to(&OUTPUT, "test_mutual_even", "test_mutual_odd"),
            "expected call to test_mutual_odd");
}

#[test]
fn mutual_odd_calls_even() {
    assert!(has_call_to(&OUTPUT, "test_mutual_odd", "test_mutual_even"),
            "expected call to test_mutual_even");
}
