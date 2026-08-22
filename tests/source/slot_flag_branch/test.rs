// Whether an expression compares two literals, i.e. a condition whose operand
// was replaced by a constant instead of by the value the binary tests.
fn is_literal_vs_literal(e: &CExpr) -> bool {
    fn literal(e: &CExpr) -> bool {
        match e {
            CExpr::IntLit(_) | CExpr::CharLit(_) => true,
            CExpr::Cast(_, inner) | CExpr::Paren(inner) => literal(inner),
            _ => false,
        }
    }
    match e {
        CExpr::Binary(
            BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::Lt
            | BinaryOp::Le
            | BinaryOp::Gt
            | BinaryOp::Ge,
            lhs,
            rhs,
        ) => literal(lhs) && literal(rhs),
        _ => false,
    }
}

#[test]
fn all_functions_present() {
    for name in [
        "summarize_flag_conflict",
        "next_opt",
        "warn_same",
        "warn_conflict",
    ] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

// The flag slot is written by several instructions, so no single one of them
// is the slot's value at the compare.  Substituting one in leaves a condition
// that tests two literals against each other and always takes the same arm.
#[test]
fn flag_slot_compare_keeps_a_runtime_operand() {
    let f = func_def(&OUTPUT, "summarize_flag_conflict");
    assert!(
        !stmt_has_expr(&f.body, &is_literal_vs_literal),
        "a branch condition folded to a literal-vs-literal compare:\n{}",
        body(&OUTPUT, "summarize_flag_conflict")
    );
}

#[test]
fn flag_test_recovers_a_branch() {
    assert!(
        has_if_stmt(&OUTPUT, "summarize_flag_conflict"),
        "expected a recovered branch on the flag slot:\n{}",
        body(&OUTPUT, "summarize_flag_conflict")
    );
}

// Both arms of the conflict test have to survive.  A lost arm edge shows up
// as one of the two warning calls disappearing, or as control reaching the
// other one unconditionally.
#[test]
fn both_conflict_arms_survive() {
    let b = body(&OUTPUT, "summarize_flag_conflict");
    assert!(
        b.contains("warn_same"),
        "the max-depth-zero arm was dropped:\n{b}"
    );
    assert!(
        b.contains("warn_conflict"),
        "the positive-max-depth arm was dropped:\n{b}"
    );
}
