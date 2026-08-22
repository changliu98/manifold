#[test]
fn variadic_stack_tail_is_recovered_semantically() {
    let function = func_def(&OUTPUT, "forward_variadic");
    assert!(function.is_variadic, "expected a variadic function");
    assert_eq!(
        function.params.len(),
        7,
        "only the named prefix belongs in the function signature"
    );
    assert!(
        has_call_to(&OUTPUT, "forward_variadic", "__builtin_next_arg"),
        "the first unnamed stack argument must not become a frame local:\n{}",
        body(&OUTPUT, "forward_variadic")
    );
}
