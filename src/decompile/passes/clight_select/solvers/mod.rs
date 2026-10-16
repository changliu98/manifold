//! Solvers layered on the syntax check.
//!
//! The syntax check (`syntax`) chooses statements, declarations and types that
//! are legal C and best by the selection objective. A solver here checks that
//! answer against the machine. It may state obligations and hard guards up
//! front (`obligations`, `extend`), and it inspects each selected model
//! (`checker`), accepting it or refuting it with clauses the next solve must
//! satisfy. Add a solver to `PRODUCTION`; the syntax stack runs every solver
//! before its own components, in this order, which is part of the
//! deterministic selection policy.

pub(crate) mod completeness;
pub mod flow;
pub mod in_search;
pub mod integer_semantics;
pub(crate) mod memory_theory;
pub(crate) mod obligations;
pub(crate) mod observations;
pub(crate) mod producer_values;
pub(crate) mod profiles;
pub(crate) mod refinement;
pub(crate) mod semantics;
pub(crate) mod storage;
pub(crate) mod storage_theory;
pub(crate) mod transfers;
pub(crate) mod type_projection;
pub(crate) mod word_inputs;
pub(crate) mod word_views;

use std::collections::{BTreeSet, HashMap};
use z3::ast::Bool;
use z3::{Model, Optimize};

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::clight_select::query::FunctionData;
use crate::decompile::passes::clight_select::syntax::{
    Artifacts, CandidateAnalysis, FunctionContext, PreparedAnalysis,
};
use crate::x86::types::{ClightStmt, Node};
use obligations::Obligations;

pub(crate) static PRODUCTION: &[&dyn Solver] = &[
    &storage::Storage,
    &semantics::Semantics,
    &completeness::Completeness,
];

/// A solver on top of the syntax check. Stateless registration: Z3 values
/// belong to per-function sessions, never this shared descriptor (functions
/// are solved in independent Rayon contexts).
pub(crate) trait Solver: Sync {
    fn name(&self) -> &'static str;
    fn reads(&self) -> &'static [&'static str] {
        &[]
    }
    fn writes(&self) -> &'static [&'static str] {
        &[]
    }
    fn prepare(
        &self,
        _db: &DecompileDB,
        _functions: &mut [FunctionData],
    ) -> Option<Box<dyn PreparedAnalysis>> {
        None
    }
    /// Candidate obligations. The stack compiles all solvers' obligations into
    /// hard guards and validates declaration changes against them.
    fn obligations<'a>(&self, _function: &'a FunctionData, _out: &mut Obligations<'a>) {}
    /// Hard guards, and the priors they carry, stated up front in the
    /// function's problem.
    fn extend(&self, _cx: &FunctionContext<'_>) -> Option<Box<dyn CandidateAnalysis>> {
        None
    }
    /// Whether `checker` has anything to inspect in this function.
    fn needs_check(&self, _function: &FunctionData) -> bool {
        false
    }
    /// A checker of this function's answers, sharing the selector's Optimize.
    fn checker<'a>(
        &self,
        _cx: &FunctionContext<'a>,
        _opt: &Optimize,
    ) -> Option<Box<dyn Checker + 'a>> {
        None
    }
    /// The final trees have been installed on the blackboard. Audit only;
    /// representation changes must still request an upstream inference epoch.
    fn audit_selection(&self, _db: &mut DecompileDB) {}
    /// Final C admission is owned by the same module as candidate admission.
    /// This audit records evidence; it must not repair the selected program.
    fn audit_emission(&self, _db: &mut DecompileDB) {}
    /// Preserve precise selected origins before tree assembly absorbs nodes.
    fn retain_origins(
        &self,
        _function: &FunctionData,
        _indices: &HashMap<Node, Option<usize>>,
        _statements: &mut HashMap<Node, ClightStmt>,
    ) {
    }
}

/// What a checker concluded about one selected answer.
pub(crate) enum Verdict {
    Accept,
    /// Clauses over the selector's existing choice variables. Each must be
    /// false under the inspected answer, so the next solve cannot return it.
    Refute(Vec<Bool>),
    /// Unsupported or out of budget. Not acceptance: the extension is rolled
    /// back and its results stay uncertified.
    Unknown(&'static str),
}

/// A checker body written with `?`: no clauses accept the answer, an error
/// leaves it unknown.
impl From<Result<Vec<Bool>, &'static str>> for Verdict {
    fn from(inspection: Result<Vec<Bool>, &'static str>) -> Self {
        match inspection {
            Ok(clauses) if clauses.is_empty() => Verdict::Accept,
            Ok(clauses) => Verdict::Refute(clauses),
            Err(reason) => Verdict::Unknown(reason),
        }
    }
}

/// One function's answer checker, driven by `refinement::Session`.
pub(crate) trait Checker {
    fn round_limit(&self) -> usize;
    fn check(&mut self, answer: &Model) -> Verdict;
    /// Joint commitments may not be independently re-picked after solving.
    fn coupled_nodes(&self) -> BTreeSet<Node>;
    /// Restrictions required if the optional search is rolled back. A failed
    /// semantic extension must not leave its unchecked representations enabled.
    fn fallback_constraints(&self) -> Vec<Bool> {
        Vec::new()
    }
    fn finish(
        self: Box<Self>,
        answer: Option<&Model>,
        reason: &'static str,
        results: &mut Artifacts,
    );
    /// The terminal fallback is a different model. Modules may retain only
    /// certificates whose complete guards hold in that model; by default an
    /// aborted extension remains uncertified.
    fn finish_fallback(
        self: Box<Self>,
        _answer: Option<&Model>,
        reason: &'static str,
        results: &mut Artifacts,
    ) {
        self.finish(None, reason, results);
    }
}
