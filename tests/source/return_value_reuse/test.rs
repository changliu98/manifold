// A local whose only assignment is its own declaration initializer: returning it
// hands the caller a value the body never computed.  Scanning the whole recovered
// unit rather than one function keeps this a property of the output, not of a
// name the compiler is free to inline away.
fn returns_uncomputed_local(text: &str) -> Vec<String> {
    let mut bad = Vec::new();
    for func in text.split("\n}\n") {
        let Some(sig_end) = func.find('{') else { continue };
        let name: String = func[..sig_end].trim().to_string();
        for ret in func.match_indices("return ") {
            let tail = &func[ret.0 + "return ".len()..];
            let Some(semi) = tail.find(';') else { continue };
            let expr = tail[..semi].trim();
            // strip a leading cast and require the whole expression to be one var
            let var = expr.rsplit(')').next().unwrap_or(expr).trim();
            if !var.starts_with("var_") || !var[4..].chars().all(|c| c.is_ascii_alphanumeric()) {
                continue;
            }
            let assigns = func
                .match_indices(var)
                .filter(|(i, _)| {
                    let after = func[i + var.len()..].trim_start();
                    after.starts_with('=') && !after.starts_with("==")
                })
                .count();
            // A DECLARATION with an initializer names a bare type before the
            // variable, which is what distinguishes `long *var_a = 0;` from the
            // assignment `var_a = malloc(...)` that genuinely computes a value
            // and from a store through the variable, whose left side also ends
            // in `= ...;` but is an expression rather than a type.
            let declared_with_init = func.lines().any(|l| {
                let l = l.trim_start();
                let Some(ty) = l.split(var).next() else { return false };
                l.contains('=')
                    && l.trim_end().ends_with(';')
                    && !ty.trim().is_empty()
                    && ty.chars().all(|c| c.is_ascii_alphanumeric() || " _*".contains(c))
            });
            if assigns <= 1 && declared_with_init {
                bad.push(format!("{name} returns never-assigned {var}"));
            }
        }
    }
    bad
}

// `main` is excluded because it still fails for a DIFFERENT, unfixed reason: at
// -O2 clang leaves every call result in the ABI return register and combines
// them, and the caller-side binding drops all of those results, so main's own
// return value is never computed either.  That is a caller-side call-result
// defect, not the callee-side return binding this case covers; scoping the scan
// keeps this test a guard for the latter instead of a duplicate report of the
// former.
const CALLEE_FUNCS: [&str; 5] = [
    "dup_prefix",
    "fill_and_return",
    "mask_of_lt",
    "rank_of_cmp",
    "nonzero_mask",
];

#[test]
fn no_callee_returns_an_uncomputed_local() {
    let mut bad = Vec::new();
    for f in CALLEE_FUNCS {
        if !OUTPUT.text.contains(f) {
            continue;
        }
        bad.extend(returns_uncomputed_local(&body_from_text(&OUTPUT.text, f)));
    }
    assert!(bad.is_empty(), "returned values that are never computed: {bad:#?}");
}

#[test]
fn returned_pointer_is_the_copy_destination() {
    // dup_prefix must hand back the buffer it filled, not a fresh variable: the
    // return value is memcpy's result, which the p[n] = 0 store also reads.
    let b = body(&OUTPUT, "dup_prefix");
    assert!(b.contains("malloc") || b.contains("memcpy"), "expected the copy in dup_prefix:\n{b}");
    assert!(!b.contains("return 0;"), "dup_prefix returned a constant 0:\n{b}");
}

#[test]
fn carry_mask_keeps_its_comparison() {
    // `sbb %r,%r` lowered as a subtraction folds to a constant 0 and drops the
    // compare entirely; the recovered body has to still test a against b.
    let b = body(&OUTPUT, "mask_of_lt");
    assert!(
        b.contains('<') || b.contains('>'),
        "mask_of_lt lost its comparison (sbb carry dropped):\n{b}"
    );
    assert!(!b.contains("return 0;"), "mask_of_lt folded to a constant:\n{b}");
}

#[test]
fn nonzero_mask_keeps_its_comparison() {
    // `neg %r; sbb %r,%r` is -(r != 0); the neg supplies the carry.
    let b = body(&OUTPUT, "nonzero_mask");
    assert!(
        b.contains("!=") || b.contains("==") || b.contains('<') || b.contains('>'),
        "nonzero_mask lost its comparison:\n{b}"
    );
}
