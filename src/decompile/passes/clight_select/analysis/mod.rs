//! Ordered, selection-owned analysis stack.
//!
//! An analysis declares its blackboard I/O and participates in preparation,
//! constraint construction, and/or model refinement. Candidate indices become
//! stable only at `bind`; all refiners share the selector's Optimize instance.
//! Add analyses in `PRODUCTION`, not branches in solve.rs or select.rs. Order
//! is explicit because it is part of the deterministic solver policy.

pub(crate) mod bindings;
pub(crate) mod c_types;
pub(crate) mod candidates;
pub(crate) mod completeness;
pub(crate) mod constraints;
pub(crate) mod declarations;
pub(crate) mod observations;
pub(crate) mod profiles;
pub(crate) mod refinement;
mod semantics;
pub(crate) mod storage;
pub(crate) mod transfers;
pub(crate) mod type_evidence;
mod type_flow;
mod type_projection;
pub(crate) mod type_recovery;

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

#[derive(Clone, Copy)]
pub(crate) struct FunctionContext<'a> {
    pub types: &'a TypeDt,
    pub function: &'a FunctionData,
    pub names: &'a HashMap<String, Ident>,
    pub registers: &'a [RTLReg],
    pub declarations: &'a HashMap<RTLReg, Dynamic>,
    pub concrete_declarations: &'a declarations::Declarations,
    pub nodes: &'a [Node],
    pub selections: &'a HashMap<Node, Vec<Bool>>,
    pub worlds: &'a [u8],
    pub world_variables: &'a HashMap<u8, Bool>,
    pub return_type: &'a Dynamic,
    /// One ordinary semantic preference, already scaled below C legality.
    pub primary_unit: u64,
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
        _concrete: &declarations::Declarations,
        _sink: &dyn SolveBackend,
    ) {
    }
    /// Propose concrete C declarations without changing the class fallback.
    /// The common builder owns their variables and passes them to all checks.
    fn declaration_alternatives(
        &self,
        _cx: &DeclarationContext<'_>,
        _reg: RTLReg,
    ) -> Vec<super::type_graph::TypeTerm> {
        Vec::new()
    }
    /// Existing analysis evidence is not a representation transformation.
    /// Unsupported checks retain these hypotheses, without certifying them;
    /// actual refutations still apply to the same concrete declaration choice.
    fn evidenced_declarations(
        &self,
        _cx: &DeclarationContext<'_>,
        _reg: RTLReg,
    ) -> Vec<super::type_graph::TypeTerm> {
        Vec::new()
    }
    fn obligations<'a>(&self, _function: &'a FunctionData, _out: &mut Obligations<'a>) {}
    fn build(&self, _cx: &FunctionContext<'_>) -> Option<Box<dyn CandidateAnalysis>> {
        None
    }
    fn needs_refinement(&self, _function: &FunctionData) -> bool {
        false
    }
    fn start_refinement<'a>(
        &self,
        _cx: &FunctionContext<'a>,
        _opt: &Optimize,
    ) -> Option<Box<dyn ModelAnalysis + 'a>> {
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
    /// Representation-only instances of a parent share its semantic prior.
    /// The owning analysis MUST hard-guard them by their admission conditions;
    /// this hook alone is neither a correctness proof nor a new preference.
    fn prior_family(&self, _node: Node, _parent: usize) -> Vec<usize> {
        Vec::new()
    }
    /// Extra weight-1 objective terms. Count before computing the dominant C
    /// compatibility weight, so extensions cannot silently change its stratum.
    fn prior_count(&self) -> usize {
        0
    }
    /// Total WEIGHT of optional representation preferences, strictly below
    /// the existing objective. This bound determines the common integer scale.
    fn secondary_count(&self) -> usize {
        0
    }
    /// Total weight of grounded evidence preferences. This tier is below C
    /// compatibility but above arbitrary statement/class representation priors.
    /// It is a declared bound, not a corpus-dependent tuning coefficient.
    fn evidence_count(&self) -> usize {
        0
    }
    /// Bounds the penalty for inventing a type shape absent from both the
    /// upstream domain and analysis proposals. C compatibility still wins.
    fn support_count(&self) -> usize {
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
static PRODUCTION: &[&dyn Analysis] = &[
    &storage::Storage,
    &semantics::Semantics,
    &completeness::Completeness,
    &type_recovery::TypeRecovery,
    &c_types::CTypes,
];

/// Experimental controls recorded per function by `Stack::prepare`; absent
/// under the production policy.
const ABLATIONS: ArtifactKey<crate::decompile::elevator::SemanticAblations> =
    ArtifactKey::new("selection-ablations");

fn semantic_admission_ablated(function: &FunctionData) -> bool {
    ABLATIONS
        .get(&function.analysis_facts)
        .is_some_and(|ablations| ablations.disable_semantic_admission)
}

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
        if db.semantic_ablations != Default::default() {
            for function in functions.iter_mut() {
                ABLATIONS.insert(&mut function.analysis_facts, db.semantic_ablations);
            }
        }
        Preparation(
            self.modules()
                .filter_map(|a| a.prepare(db, functions))
                .collect(),
        )
    }

    pub(crate) fn build(&self, cx: &FunctionContext<'_>) -> Vec<Box<dyn CandidateAnalysis>> {
        let obligations = self.obligations(cx.function);
        let mut compiled: Vec<Box<dyn CandidateAnalysis>> = Vec::new();
        if !obligations.0.is_empty() {
            compiled.push(semantics::compile(cx, obligations));
        }
        compiled.extend(self.modules().filter_map(|a| a.build(cx)));
        compiled
    }

    fn obligations<'f>(&self, function: &'f FunctionData) -> Obligations<'f> {
        let mut obligations = Obligations::default();
        if semantic_admission_ablated(function) {
            return obligations;
        }
        for analysis in self.modules() {
            analysis.obligations(function, &mut obligations);
        }
        obligations
    }

    fn refiners<'f>(
        &self,
        cx: &FunctionContext<'f>,
        opt: &'f Optimize,
    ) -> Vec<(&'static str, Box<dyn ModelAnalysis + 'f>)> {
        let mut result = Vec::new();
        // Declaration transfers are validator-backed admission as well.
        let transfers = (!semantic_admission_ablated(cx.function))
            .then(|| profiles::Profiles::start(cx, self.obligations(cx.function), opt))
            .flatten();
        if let Some(profiles) = transfers {
            result.push((
                "declaration-transfers",
                Box::new(profiles) as Box<dyn ModelAnalysis>,
            ));
        }
        result.extend(self.modules().filter_map(|module| {
            module
                .start_refinement(cx, opt)
                .map(|analysis| (module.name(), analysis))
        }));
        result
    }

    pub(crate) fn needs_refinement(&self, function: &FunctionData) -> bool {
        self.modules().any(|a| a.needs_refinement(function))
    }

    pub(crate) fn audit_selection(&self, db: &mut DecompileDB) {
        for analysis in self.modules() {
            analysis.audit_selection(db);
        }
    }
    pub(crate) fn audit_emission(&self, db: &mut DecompileDB) {
        for analysis in self.modules() {
            analysis.audit_emission(db);
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
trait Artifact: Send + Sync {
    fn value(&self) -> &(dyn Any + Send + Sync);
    fn project(&self, plan: &bindings::BindingPlan) -> Option<Arc<dyn Artifact>>;
}

struct OwnedArtifact<T> {
    value: T,
    project: Option<fn(&T, &bindings::BindingPlan) -> T>,
}

impl<T: Any + Send + Sync> Artifact for OwnedArtifact<T> {
    fn value(&self) -> &(dyn Any + Send + Sync) {
        &self.value
    }
    fn project(&self, plan: &bindings::BindingPlan) -> Option<Arc<dyn Artifact>> {
        self.project.map(|project| {
            Arc::new(Self {
                value: project(&self.value, plan),
                project: self.project,
            }) as Arc<dyn Artifact>
        })
    }
}

#[derive(Clone, Default)]
pub(crate) struct Artifacts(BTreeMap<&'static str, Arc<dyn Artifact>>);

impl Artifacts {
    /// Every artifact owner declares its own value-identity projection. The
    /// binding constructor must not maintain a second list of module caches.
    /// Native sites, CFG edges and physical storage identities do not change.
    pub(super) fn project_bindings(&mut self, plan: &bindings::BindingPlan) {
        for artifact in self.0.values_mut() {
            if let Some(projected) = artifact.project(plan) {
                *artifact = projected;
            }
        }
    }
}

impl std::fmt::Debug for Artifacts {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.0.keys()).finish()
    }
}

pub(crate) struct ArtifactKey<T> {
    name: &'static str,
    marker: PhantomData<fn() -> T>,
    project: Option<fn(&T, &bindings::BindingPlan) -> T>,
}

impl<T: Any + Send + Sync> ArtifactKey<T> {
    pub(crate) const fn new(name: &'static str) -> Self {
        Self {
            name,
            marker: PhantomData,
            project: None,
        }
    }
    /// Use for prepared facts containing C value identities. `new` is for
    /// identity-independent facts (e.g. native nodes) or post-solve results.
    pub(crate) const fn projected(
        name: &'static str,
        project: fn(&T, &bindings::BindingPlan) -> T,
    ) -> Self {
        Self {
            name,
            marker: PhantomData,
            project: Some(project),
        }
    }
    pub(crate) fn insert(&self, results: &mut Artifacts, value: T) {
        assert!(
            !results.0.contains_key(self.name),
            "duplicate analysis result: {}",
            self.name
        );
        results.0.insert(
            self.name,
            Arc::new(OwnedArtifact {
                value,
                project: self.project,
            }),
        );
    }
    pub(crate) fn get<'a>(&self, results: &'a Artifacts) -> Option<&'a T> {
        results.0.get(self.name).map(|value| {
            value
                .value()
                .downcast_ref()
                .expect("analysis result key type mismatch")
        })
    }
    /// Project an already-prepared artifact into a new binding vocabulary,
    /// before `bind`. This replaces the Arc in this function's preparation;
    /// it never mutates facts retained by another clone or a running solver.
    /// Ordinary publication still uses `insert` and rejects duplicate owners.
    pub(super) fn rebind(&self, results: &mut Artifacts, value: T) {
        assert!(
            self.get(results).is_some(),
            "cannot rebind an absent analysis artifact"
        );
        results.0.insert(
            self.name,
            Arc::new(OwnedArtifact {
                value,
                project: self.project,
            }),
        );
    }
}

#[cfg(test)]
mod tests;
