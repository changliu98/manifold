// A position-independent binary reads an imported function's address from the GOT slot the
// dynamic linker fills (R_X86_64_GLOB_DAT). The slot is zero in the file, so recovering the read
// as a data global hands the program a null function pointer.

#[test]
fn imported_functions_are_passed_as_themselves() {
    for callee in ["free", "strcmp", "strcoll"] {
        assert!(
            has_var_ref(&OUTPUT, "main", callee),
            "main should pass {callee} as a function value:\n{}",
            body(&OUTPUT, "main")
        );
    }
}

#[test]
fn no_import_is_declared_as_data() {
    for callee in ["free", "strcmp", "strcoll"] {
        for spelling in [format!("long {callee} ="), format!("long {callee};"), format!("void *{callee};")] {
            assert!(!OUTPUT.text.contains(&spelling), "{callee} declared as data:\n{}", OUTPUT.text);
        }
    }
}
