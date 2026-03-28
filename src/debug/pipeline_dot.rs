// Generates Graphviz DOT representations of the pipeline pass dependency graph.
use crate::decompile::passes::pass::{IRPass, PassScheduler};
use crate::decompile::passes::*;
use crate::decompile::analysis::*;

/// Generate Graphviz DOT strings (summary and detailed) of the pipeline dependency graph.
pub fn dump_pipeline_deps() -> (String, String) {
    let passes: Vec<Box<dyn IRPass>> = vec![
        Box::new(abi_pass::AbiPass),
        Box::new(canary_vla_pass::CanaryVlaPass),
        Box::new(asm_pass::AsmPass),
        Box::new(stack_pass::StackAnalysisPass),
        Box::new(mach_pass::MachPass),
        Box::new(linear_pass::LinearPass),
        Box::new(rtl_pass::RTLPass),
        Box::new(rtl_opt_pass::RtlOptPass),
        Box::new(type_pass::TypePass),
        Box::new(global_array_pass::GlobalArrayPass),
        Box::new(ptr_to_pass::PtrToPass),
        Box::new(struct_recovery_pass::StructRecoveryPass),
        Box::new(signature_pass::SignatureReconciliationPass),
        Box::new(cminor_pass::CminorPass),
        Box::new(csh_pass::CshPass),
        Box::new(cshminor_pass::CshminorPass),
        Box::new(structuring_pass::StructuringPass),
        Box::new(clight_pass::ClightPass),
        Box::new(clight_pass::ClightFieldPass),
        Box::new(clight_emit_pass::ClightEmitPass),
    ];

    let schedule = PassScheduler::build_schedule(&passes);
    (schedule.to_dot_summary(), schedule.to_dot(&passes))
}
