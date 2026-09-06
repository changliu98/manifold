//! Ordered, selection-owned analysis stack.
//!
//! An analysis declares its blackboard I/O and participates in preparation,
//! constraint construction, and/or model refinement. Candidate indices become
//! stable only at `bind`; all refiners share the selector's Optimize instance.
//! Add analyses in `PRODUCTION`, not branches in solve.rs or select.rs. Order
//! is explicit because it is part of the deterministic solver policy.

pub(crate) mod c_types;
pub(crate) mod constraints;
pub(crate) mod refinement;
mod semantics;
pub(crate) mod storage;

use std::any::Any;
use std::collections::{BTreeMap, HashMap};
use std::marker::PhantomData;
use std::sync::Arc;
use z3::ast::{Bool, Dynamic};
use z3::Optimize;

use super::obligations::Obligations;
use super::query::FunctionData;
use super::select::ProgramSelectionState;
use crate::decompile::elevator::DecompileDB;
use crate::x86::types::{ClightStmt, Ident, Node, RTLReg, XType};
use c_types::TypeDt;
use constraints::{ConstraintSink, SolveBackend};
use refinement::ModelAnalysis;

pub(crate) struct DeclarationContext<'a> {
    pub types: &'a TypeDt,
    pub function: &'a FunctionData,
    pub pins: &'a [(RTLReg, XType)],
}

pub(crate) struct FunctionContext<'a> {
    pub types: &'a TypeDt,
    pub function: &'a FunctionData,
    pub names: &'a HashMap<String, Ident>,
    pub registers: &'a [RTLReg],
    pub declarations: &'a HashMap<RTLReg, Dynamic>,
    pub nodes: &'a [Node],
    pub selections: &'a HashMap<Node, Vec<Bool>>,
    pub worlds: &'a [u8],
    pub world_variables: &'a HashMap<u8, Bool>,
    pub return_type: &'a Dynamic,
}

pub(crate) struct Candidate<'a> {
    pub node: Node,
    pub index: usize,
    pub statement: &'a ClightStmt,
    pub selected: Option<&'a Bool>,
}

/// Stateless registration. Z3 values belong to per-function sessions, never
/// this shared descriptor (functions are solved in independent Rayon contexts).
pub(crate) trait Analysis: Sync {
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
    fn constrain_declaration(
        &self,
        _cx: &DeclarationContext<'_>,
        _reg: RTLReg,
        _variable: &Dynamic,
        _sink: &dyn SolveBackend,
    ) {
    }
    fn constrain_interfaces(
        &self,
        _cx: &DeclarationContext<'_>,
        _variables: &HashMap<RTLReg, Dynamic>,
        _sink: &dyn SolveBackend,
    ) {
    }
    fn obligations<'a>(&self, _function: &'a FunctionData, _out: &mut Obligations<'a>) {}
    fn build(&self, _cx: &FunctionContext<'_>) -> Option<Box<dyn CandidateAnalysis>> {
        None
    }
    fn needs_refinement(&self, _function: &FunctionData) -> bool {
        false
    }
    fn start_refinement(
        &self,
        _cx: &FunctionContext<'_>,
        _opt: &Optimize,
    ) -> Option<Box<dyn ModelAnalysis>> {
        None
    }
    /// The final trees have been installed on the blackboard. Audit only;
    /// representation changes must still request an upstream inference epoch.
    fn audit_selection(&self, _db: &mut DecompileDB) {}
}

pub(crate) trait PreparedAnalysis {
    /// Called after every analysis has proposed candidates and the selector
    /// has sorted them. Do not add/reorder candidates after this boundary.
    fn bind(&mut self, _db: &DecompileDB, _functions: &mut [FunctionData]) {}
    fn publish(
        self: Box<Self>,
        _db: &mut DecompileDB,
        _functions: &[FunctionData],
        _selection: &ProgramSelectionState,
    ) {
    }
}

/// Every candidate rule uses the same recording sink. A hard obligation thus
/// constrains both the solver and its deterministic fixed-model re-pick.
pub(crate) trait CandidateAnalysis {
    /// Extra weight-1 objective terms. Count before computing the dominant C
    /// compatibility weight, so extensions cannot silently change its stratum.
    fn prior_count(&self) -> usize {
        0
    }
    fn constrain_function(&self, _cx: &FunctionContext<'_>, _sink: &ConstraintSink<'_>) {}
    fn constrain_candidate(
        &self,
        _cx: &FunctionContext<'_>,
        _candidate: &Candidate<'_>,
        _sink: &ConstraintSink<'_>,
    ) {
    }
}

pub(crate) struct Stack<'a> {
    analyses: &'a [&'a dyn Analysis],
}

// Preparation: storage evidence before value/word candidates. Constraint
// construction: semantic guards before recursive C constraints, unchanged.
static PRODUCTION: &[&dyn Analysis] = &[&storage::Storage, &semantics::Semantics, &c_types::CTypes];

impl<'a> Stack<'a> {
    pub(crate) fn new(analyses: &'a [&'a dyn Analysis]) -> Self {
        let mut names = std::collections::BTreeSet::new();
        for analysis in analyses {
            assert!(
                names.insert(analysis.name()),
                "duplicate selection analysis: {}",
                analysis.name()
            );
        }
        Self { analyses }
    }

    pub(crate) fn production() -> Stack<'static> {
        Stack::new(PRODUCTION)
    }
    pub(crate) fn modules(&self) -> impl Iterator<Item = &dyn Analysis> {
        self.analyses.iter().copied()
    }

    pub(crate) fn reads(&self) -> Vec<&'static str> {
        self.modules()
            .flat_map(Analysis::reads)
            .copied()
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    pub(crate) fn writes(&self) -> Vec<&'static str> {
        self.modules()
            .flat_map(Analysis::writes)
            .copied()
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    pub(crate) fn prepare(&self, db: &DecompileDB, functions: &mut [FunctionData]) -> Preparation {
        Preparation(
            self.modules()
                .filter_map(|a| a.prepare(db, functions))
                .collect(),
        )
    }

    pub(crate) fn build(&self, cx: &FunctionContext<'_>) -> Vec<Box<dyn CandidateAnalysis>> {
        let mut obligations = Obligations::default();
        for analysis in self.modules() {
            analysis.obligations(cx.function, &mut obligations);
        }
        let mut compiled: Vec<Box<dyn CandidateAnalysis>> = Vec::new();
        if !obligations.0.is_empty() {
            compiled.push(semantics::compile(cx, obligations));
        }
        compiled.extend(self.modules().filter_map(|a| a.build(cx)));
        compiled
    }

    pub(crate) fn needs_refinement(&self, function: &FunctionData) -> bool {
        self.modules().any(|a| a.needs_refinement(function))
    }

    pub(crate) fn audit_selection(&self, db: &mut DecompileDB) {
        for analysis in self.modules() {
            analysis.audit_selection(db);
        }
    }
}

pub(crate) struct Preparation(Vec<Box<dyn PreparedAnalysis>>);

impl Preparation {
    pub(crate) fn bind(&mut self, db: &DecompileDB, functions: &mut [FunctionData]) {
        for analysis in &mut self.0 {
            analysis.bind(db, functions);
        }
    }
    pub(crate) fn publish(
        self,
        db: &mut DecompileDB,
        functions: &[FunctionData],
        selection: &ProgramSelectionState,
    ) {
        for analysis in self.0 {
            analysis.publish(db, functions, selection);
        }
    }
}

/// Immutable, cloneable, solver-free module results. A typed key keeps payload
/// ownership in the module instead of extending a central result enum for
/// every new analysis. Send+Sync prevents Z3 context objects escaping a solve.
#[derive(Clone, Default)]
pub(crate) struct Artifacts(BTreeMap<&'static str, Arc<dyn Any + Send + Sync>>);

impl std::fmt::Debug for Artifacts {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.0.keys()).finish()
    }
}

pub(crate) struct ArtifactKey<T> {
    name: &'static str,
    marker: PhantomData<fn() -> T>,
}

impl<T: Any + Send + Sync> ArtifactKey<T> {
    pub(crate) const fn new(name: &'static str) -> Self {
        Self {
            name,
            marker: PhantomData,
        }
    }
    pub(crate) fn insert(&self, results: &mut Artifacts, value: T) {
        assert!(
            !results.0.contains_key(self.name),
            "duplicate analysis result: {}",
            self.name
        );
        results.0.insert(self.name, Arc::new(value));
    }
    pub(crate) fn get<'a>(&self, results: &'a Artifacts) -> Option<&'a T> {
        results.0.get(self.name).map(|value| {
            value
                .downcast_ref()
                .expect("analysis result key type mismatch")
        })
    }
}

#[cfg(test)]
mod tests;
