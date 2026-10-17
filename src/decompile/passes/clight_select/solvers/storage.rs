//! Storage preparation and layout search plugged into final selection.
use super::{Checker, Verdict};
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::clight_select::syntax::{
    ArtifactKey, Artifacts, FunctionContext, PreparedAnalysis,
};
use crate::decompile::passes::clight_select::{
    query::FunctionData, select::ProgramSelectionState, solvers::memory_theory,
    solvers::storage_theory,
};
use crate::decompile::passes::semantic_counterexample as storage;
use crate::x86::types::Node;
use std::collections::BTreeSet;
use z3::ast::Bool;
use z3::{Model, Optimize};

pub(crate) const DECISIONS: ArtifactKey<Vec<storage_theory::Decision>> =
    ArtifactKey::new("storage-layout");
pub(crate) struct Storage;
pub(crate) const PROBLEMS: ArtifactKey<Vec<storage::Prepared>> = ArtifactKey::new("storage-layout");

impl crate::decompile::passes::clight_select::solvers::Solver for Storage {
    fn name(&self) -> &'static str {
        "storage-layout"
    }
    fn reads(&self) -> &'static [&'static str] {
        static READS: std::sync::LazyLock<Vec<&'static str>> = std::sync::LazyLock::new(|| {
            let mut reads = storage::INPUTS.to_vec();
            reads.extend_from_slice(&[
                "semantic_storage_obligation",
                "semantic_storage_projection",
                "semantic_storage_selected_target",
            ]);
            reads.sort_unstable();
            reads.dedup();
            reads
        });
        &READS
    }
    fn writes(&self) -> &'static [&'static str] {
        &[
            "semantic_storage_obligation",
            "semantic_storage_counterexample",
            "semantic_storage_refinement",
            "semantic_storage_search",
            "selection_storage_request",
            "selection_storage_field_request",
        ]
    }
    fn prepare(
        &self,
        db: &DecompileDB,
        _functions: &mut [FunctionData],
    ) -> Option<Box<dyn PreparedAnalysis>> {
        Some(Box::new(Prepared(
            if db.semantic_ablations.disable_storage_search {
                Default::default()
            } else {
                storage::prepare(db)
            },
        )))
    }
    fn needs_check(&self, function: &FunctionData) -> bool {
        PROBLEMS
            .get(&function.analysis_facts)
            .is_some_and(|problems| !problems.is_empty())
    }
    fn audit_selection(&self, db: &mut DecompileDB) {
        storage::ledger::check_selection(db);
    }
    fn checker<'a>(
        &self,
        cx: &FunctionContext<'a>,
        opt: &Optimize,
    ) -> Option<Box<dyn crate::decompile::passes::clight_select::solvers::Checker + 'a>> {
        if !self.needs_check(cx.function) {
            return None;
        }
        let layouts = PROBLEMS
            .get(&cx.function.analysis_facts)?
            .iter()
            .map(|problem| {
                let mut encoding = storage_theory::Encoding::build(problem, opt);
                encoding.bind_candidates(cx.selections);
                encoding
            })
            .collect();
        Some(Box::new(Layouts(layouts)))
    }
}

struct Prepared(storage::Refinement);
impl PreparedAnalysis for Prepared {
    fn bind(&mut self, db: &DecompileDB, functions: &mut [FunctionData]) {
        memory_theory::bind_current_storage(db, functions, &mut self.0.pending);
        for function in functions {
            let problems = self
                .0
                .pending
                .iter()
                .filter(|p| p.problem.function == function.address)
                .cloned()
                .collect();
            PROBLEMS.insert(&mut function.analysis_facts, problems);
        }
    }
    fn publish(
        self: Box<Self>,
        db: &mut DecompileDB,
        functions: &[FunctionData],
        selection: &ProgramSelectionState,
    ) {
        // Preserve function/candidate order, not hash-table iteration order.
        let decisions: Vec<_> = functions
            .iter()
            .filter_map(|f| selection.analysis_results.get(&f.address))
            .filter_map(|results| DECISIONS.get(results))
            .flatten()
            .cloned()
            .collect();
        storage::publish_selection(db, self.0, &decisions);
    }
}

struct Layouts(Vec<storage_theory::Encoding>);
impl Checker for Layouts {
    fn round_limit(&self) -> usize {
        storage_theory::MAX_REFINEMENTS
    }
    fn check(&mut self, answer: &Model) -> Verdict {
        self.inspect(answer).into()
    }
    fn coupled_nodes(&self) -> BTreeSet<Node> {
        self.0.iter().flat_map(|l| l.coupled_nodes()).collect()
    }
    fn finish(
        self: Box<Self>,
        model: Option<&Model>,
        reason: &'static str,
        results: &mut Artifacts,
    ) {
        DECISIONS.insert(
            results,
            self.0
                .into_iter()
                .map(|l| l.finish(model, reason))
                .collect(),
        );
    }
}

impl Layouts {
    fn inspect(&mut self, model: &Model) -> Result<Vec<Bool>, &'static str> {
        let mut clauses = Vec::new();
        for layout in &mut self.0 {
            if let Some(clause) = layout.refine(model)? {
                clauses.push(clause);
            }
        }
        Ok(clauses)
    }
}
