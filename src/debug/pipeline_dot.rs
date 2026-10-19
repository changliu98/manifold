// Generates Graphviz DOT representations of the pipeline pass dependency graph.
use crate::decompile::passes::pass::PassScheduler;

/// Generate Graphviz DOT strings (summary and detailed) of the pipeline dependency graph.
/// The pass list comes straight from `elevator::pipeline_passes`, the list the
/// pipeline actually runs: a second hand-maintained copy here silently fell
/// behind it and left `goto_elide` out of every dumped graph.
pub fn dump_pipeline_deps() -> (String, String) {
    let passes = crate::decompile::elevator::pipeline_passes();

    let schedule = PassScheduler::build_schedule(&passes);
    (schedule.to_dot_summary(), schedule.to_dot(&passes))
}

/// Relations declared but consumed by no rule body or extra_reads; must still be cross-checked against imperative rel_iter reads.
pub fn dump_dead_relations() -> String {
    use std::collections::{BTreeMap, BTreeSet};

    let mut declared: BTreeSet<String> = BTreeSet::new();
    let mut body_used: BTreeSet<String> = BTreeSet::new();
    let mut extra: BTreeSet<String> = BTreeSet::new();
    let mut producers: BTreeMap<String, Vec<&'static str>> = BTreeMap::new();
    let mut inputs_of: BTreeMap<String, Vec<&'static str>> = BTreeMap::new();

    // Read relation metadata straight from each ascent program: rule_deps() is only forwarded by declare_io_from! passes, so hand-rolled impls would look dead.
    macro_rules! gather {
        ($prog:ty, $label:expr) => {{
            for r in <$prog>::all_relations() {
                declared.insert(r.to_string());
            }
            for r in <$prog>::rule_outputs() {
                producers.entry(r.to_string()).or_default().push($label);
            }
            for r in <$prog>::inputs_only() {
                inputs_of.entry(r.to_string()).or_default().push($label);
            }
            for (b, _h) in <$prog>::rule_dependencies() {
                body_used.insert(b.to_string());
            }
        }};
    }
    // Only #[swap_db] programs share relations through DecompileDB; the rest read via rel_iter and are covered by the IMPREAD grep cross-check.
    use crate::decompile::analysis::*;
    use crate::decompile::passes::*;
    gather!(asm_pass::AsmPassProgram, "asm");
    gather!(canary_vla_pass::CanaryProgram, "canary_vla");
    gather!(clight_pass::ClightPassProgram, "clight");
    gather!(cminor_pass::CminorPassProgram, "cminor");
    gather!(cshminor_pass::CshminorPassProgram, "cshminor");
    gather!(csh_pass::CshPassProgram, "csh");
    gather!(global_array_pass::GlobalArrayPassProgram, "global_array");
    gather!(linear_pass::LinearPassProgram, "linear");
    gather!(mach_pass::MachPassProgram, "mach");
    gather!(ptr_to_pass::PtrToPassProgram, "ptr_to");
    gather!(
        rtl_dominator_pass::RTLDominatorPassProgram,
        "rtl_dominators"
    );
    gather!(rtl_pass::RTLPassProgram, "rtl");
    gather!(signature_pass::SignatureReconciliationProgram, "signature");
    gather!(stack_pass::StackAnalysisProgram, "stack");
    gather!(
        struct_recovery_pass::StructRecoveryProgram,
        "struct_recovery"
    );
    gather!(type_pass::TypePassProgram, "type");

    // extra_reads come from the IRPass wrappers (imperative reads declared for scheduling).
    for p in crate::decompile::elevator::pipeline_passes() {
        for r in p.extra_reads() {
            extra.insert(r.to_string());
            declared.insert(r.to_string());
        }
    }

    let mut out = String::new();
    out.push_str("=== RELATION USAGE ANALYSIS ===\n");
    out.push_str(&format!(
        "declared={} body_used={} extra_reads={}\n\n",
        declared.len(),
        body_used.len(),
        extra.len()
    ));
    out.push_str("--- CANDIDATE DEAD (declared, never a rule-body atom, never extra_read) ---\n");
    out.push_str(
        "--- (cross-check each against `rel_iter` string-literal reads before removing) ---\n",
    );
    for r in &declared {
        if !body_used.contains(r) && !extra.contains(r) {
            let prod = producers.get(r).map(|v| v.join(",")).unwrap_or_default();
            let inp = inputs_of.get(r).map(|v| v.join(",")).unwrap_or_default();
            out.push_str(&format!(
                "DEAD_CAND\t{}\tproducers=[{}]\tinputs_of=[{}]\n",
                r, prod, inp
            ));
        }
    }
    out.push_str("\n--- ALL_DECLARED ---\n");
    for r in &declared {
        out.push_str(&format!("ALL_DECLARED\t{}\n", r));
    }
    out.push_str("\n--- ALL_BODY_USED ---\n");
    for r in &body_used {
        out.push_str(&format!("ALL_BODY_USED\t{}\n", r));
    }
    out
}
