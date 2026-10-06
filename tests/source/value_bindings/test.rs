#[test]
fn selected_bindings_preserve_wide_intermediates_joins_and_loops() {
    // The GCC and Clang variants run concurrently. Do not let their oracle
    // compilers overwrite an executable that the other variant is running.
    let scope = module_path!().replace("::", "_");
    let reference_name = format!("value_bindings_reference_{scope}");
    let recovered_name = format!("value_bindings_recovered_{scope}");
    let reference = compile(&reference_name, "gcc", include_str!("input.c"), "-O0");
    let reference = Command::new(reference).output().expect("run reference");
    assert!(reference.status.success());
    for optimization in ["-O0", "-O2"] {
        let recovered = compile(&recovered_name, "gcc", &OUTPUT.text, optimization);
        let recovered = Command::new(recovered).output().expect("run recovered bindings");
        assert!(recovered.status.success(), "{}\n{}", String::from_utf8_lossy(&recovered.stderr), OUTPUT.text);
        assert_eq!(recovered.stdout, reference.stdout, "{}\n{}", optimization, OUTPUT.text);
    }
}
