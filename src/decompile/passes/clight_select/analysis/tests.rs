use super::super::obligations::{Check, Obligation, Obligations, Verdict};
use super::refinement::ModelAnalysis;
use super::*;
use crate::decompile::passes::c_pass::types::CType;
use std::collections::BTreeSet;
use z3::Model;

fn fixture() -> FunctionData {
    let mut f = FunctionData::new(1, "modules".into(), vec![], vec![], None, 0, 10, true);
    f.node_statements
        .insert(10, vec![ClightStmt::Sskip, ClightStmt::Sskip]);
    f.node_statements
        .insert(20, vec![ClightStmt::Sskip, ClightStmt::Sskip]);
    f
}

#[derive(Clone)]
struct Rule {
    name: &'static str,
    node: Node,
    forbidden: usize,
}
impl Analysis for Rule {
    fn name(&self) -> &'static str {
        self.name
    }
    fn reads(&self) -> &'static [&'static str] {
        &["test_evidence", "rtl_inst"]
    }
    fn writes(&self) -> &'static [&'static str] {
        &["test_obligations"]
    }
    fn build(&self, _cx: &FunctionContext<'_>) -> Option<Box<dyn CandidateAnalysis>> {
        Some(Box::new(self.clone()))
    }
}
impl CandidateAnalysis for Rule {
    fn constrain_candidate(
        &self,
        _cx: &FunctionContext<'_>,
        candidate: &Candidate<'_>,
        sink: &ConstraintSink<'_>,
    ) {
        if candidate.node == self.node && candidate.index == self.forbidden {
            sink.assert_structural(candidate.selected, &Bool::from_bool(false));
        }
    }
}

#[test]
fn independent_modules_stack_without_solver_dispatch_changes() {
    let left = Rule {
        name: "left",
        node: 10,
        forbidden: 0,
    };
    let right = Rule {
        name: "right",
        node: 20,
        forbidden: 1,
    };
    for modules in [
        vec![&c_types::CTypes as &dyn Analysis, &left, &right],
        vec![&c_types::CTypes, &right, &left],
    ] {
        let out = super::super::solve::solve_function_z3_with_stack(
            &fixture(),
            &HashMap::new(),
            &[],
            &Stack::new(&modules),
        )
        .unwrap();
        assert_eq!(out.0[&10], Some(1));
        assert_eq!(out.0[&20], Some(0));
    }
}

#[test]
fn module_io_is_aggregated_and_deduplicated() {
    let left = Rule {
        name: "left",
        node: 10,
        forbidden: 0,
    };
    let right = Rule {
        name: "right",
        node: 20,
        forbidden: 1,
    };
    let modules: &[&dyn Analysis] = &[&left, &right];
    let stack = Stack::new(modules);
    assert_eq!(stack.reads(), ["rtl_inst", "test_evidence"]);
    assert_eq!(stack.writes(), ["test_obligations"]);
    use crate::decompile::passes::pass::IRPass;
    let pass = crate::decompile::passes::clight_emit_pass::ClightSelectPass;
    for input in Stack::production().reads() {
        assert!(pass.extra_reads().contains(&input), "{input}");
    }
    for output in Stack::production().writes() {
        assert!(pass.outputs().contains(&output), "{output}");
    }
}

#[test]
#[should_panic(expected = "duplicate selection analysis")]
fn duplicate_module_identity_is_rejected() {
    Stack::new(&[&c_types::CTypes, &c_types::CTypes]);
}

struct ExtraObligation(Verdict);
impl Obligation for ExtraObligation {
    fn family(&self) -> &'static str {
        "test-obligation"
    }
    fn check(
        &self,
        _validator: &super::super::integer_semantics::Validator,
        stmt: &ClightStmt,
        _declarations: &HashMap<RTLReg, CType>,
        _function: &FunctionData,
    ) -> Check {
        Check::plain(if matches!(stmt, ClightStmt::Sskip) {
            Verdict::Refuted
        } else {
            self.0
        })
    }
}
struct ExtraAnalysis(Verdict);
impl Analysis for ExtraAnalysis {
    fn name(&self) -> &'static str {
        "extra-obligation"
    }
    fn obligations<'a>(&self, _function: &'a FunctionData, out: &mut Obligations<'a>) {
        out.push(10, ExtraObligation(self.0));
    }
}

#[test]
fn new_obligation_uses_shared_refutation_and_repick_guards() {
    let mut f = fixture();
    f.node_statements
        .insert(10, vec![ClightStmt::Sskip, ClightStmt::Sreturn(None)]);
    for (verdict, expected) in [
        (Verdict::Equivalent, 1),
        (Verdict::Unknown, 0),
        (Verdict::Unsupported, 0),
        (Verdict::Refuted, 0),
    ] {
        let extra = ExtraAnalysis(verdict);
        let modules: &[&dyn Analysis] = &[&c_types::CTypes, &extra];
        let out = super::super::solve::solve_function_z3_with_stack(
            &f,
            &HashMap::new(),
            &[],
            &Stack::new(modules),
        )
        .unwrap();
        assert_eq!(out.0[&10], Some(expected), "{verdict:?}");
    }
}

#[derive(Clone, Copy)]
enum Behavior {
    Refine,
    Unknown,
    Stutter,
    Exhaust,
}
struct Search {
    name: &'static str,
    node: Node,
    behavior: Behavior,
}
impl Analysis for Search {
    fn name(&self) -> &'static str {
        self.name
    }
    fn needs_refinement(&self, _function: &FunctionData) -> bool {
        true
    }
    fn start_refinement(
        &self,
        cx: &FunctionContext<'_>,
        _opt: &Optimize,
    ) -> Option<Box<dyn ModelAnalysis>> {
        Some(Box::new(SearchSession {
            name: self.name,
            node: self.node,
            choice: cx.selections[&self.node][1].clone(),
            behavior: self.behavior,
        }))
    }
}
struct SearchSession {
    name: &'static str,
    node: Node,
    choice: Bool,
    behavior: Behavior,
}
impl ModelAnalysis for SearchSession {
    fn round_limit(&self) -> usize {
        if matches!(self.behavior, Behavior::Exhaust) {
            0
        } else {
            4
        }
    }
    fn inspect(&mut self, model: &Model) -> Result<Vec<Bool>, &'static str> {
        match self.behavior {
            Behavior::Unknown => Err("test unknown"),
            Behavior::Stutter => Ok(vec![Bool::from_bool(true)]),
            _ if model.eval(&self.choice, true).unwrap().as_bool() == Some(true) => Ok(vec![]),
            _ => Ok(vec![self.choice.clone()]),
        }
    }
    fn coupled_nodes(&self) -> BTreeSet<Node> {
        BTreeSet::from([self.node])
    }
    fn finish(
        self: Box<Self>,
        model: Option<&Model>,
        _reason: &'static str,
        results: &mut Artifacts,
    ) {
        ArtifactKey::new(self.name).insert(results, model.is_some());
    }
}

#[test]
fn two_refiners_share_the_model_and_protect_joint_selection_from_repick() {
    let left = Search {
        name: "search-left",
        node: 10,
        behavior: Behavior::Refine,
    };
    let right = Search {
        name: "search-right",
        node: 20,
        behavior: Behavior::Refine,
    };
    let modules: &[&dyn Analysis] = &[&c_types::CTypes, &left, &right];
    let out = super::super::solve::solve_function_z3_with_stack(
        &fixture(),
        &HashMap::new(),
        &[],
        &Stack::new(modules),
    )
    .unwrap();
    for node in [10, 20] {
        assert_eq!(out.0[&node], Some(1));
    }
    for name in ["search-left", "search-right"] {
        assert_eq!(ArtifactKey::<bool>::new(name).get(&out.5), Some(&true));
    }
}

#[test]
fn failed_optional_analysis_rolls_back_all_extensions_but_not_base_constraints() {
    for behavior in [Behavior::Unknown, Behavior::Stutter, Behavior::Exhaust] {
        let base = Rule {
            name: "base",
            node: 20,
            forbidden: 0,
        };
        let search = Search {
            name: "search",
            node: 10,
            behavior: Behavior::Refine,
        };
        let failed = Search {
            name: "failed",
            node: 10,
            behavior,
        };
        let modules: &[&dyn Analysis] = &[&c_types::CTypes, &base, &search, &failed];
        let out = super::super::solve::solve_function_z3_with_stack(
            &fixture(),
            &HashMap::new(),
            &[],
            &Stack::new(modules),
        )
        .unwrap();
        assert_eq!(out.0[&10], Some(0));
        assert_eq!(out.0[&20], Some(1));
        for name in ["search", "failed"] {
            assert_eq!(ArtifactKey::<bool>::new(name).get(&out.5), Some(&false));
        }
    }
}

#[test]
fn module_results_are_immutable_snapshots() {
    let key = ArtifactKey::<Vec<usize>>::new("test-result");
    let mut original = Artifacts::default();
    key.insert(&mut original, vec![1, 2]);
    let retained = original.clone();
    let mut replacement = Artifacts::default();
    key.insert(&mut replacement, vec![3]);
    assert_eq!(key.get(&retained).unwrap(), &[1, 2]);
    assert_eq!(key.get(&replacement).unwrap(), &[3]);
}

struct Joint;
impl Analysis for Joint {
    fn name(&self) -> &'static str {
        "joint"
    }
    fn build(&self, _cx: &FunctionContext<'_>) -> Option<Box<dyn CandidateAnalysis>> {
        Some(Box::new(Joint))
    }
}
impl CandidateAnalysis for Joint {
    fn constrain_function(&self, cx: &FunctionContext<'_>, sink: &ConstraintSink<'_>) {
        sink.assert_structural(None, &cx.selections[&10][1].xor(&cx.selections[&20][1]));
    }
}

#[test]
fn global_analysis_constraint_cannot_be_bypassed_by_independent_repick() {
    let modules: &[&dyn Analysis] = &[&c_types::CTypes, &Joint];
    let out = super::super::solve::solve_function_z3_with_stack(
        &fixture(),
        &HashMap::new(),
        &[],
        &Stack::new(modules),
    )
    .unwrap();
    assert_ne!(out.0[&10], out.0[&20]);
}

const BOUND_CHOICE: ArtifactKey<usize> = ArtifactKey::new("bound-choice");
struct Lifecycle;
impl Analysis for Lifecycle {
    fn name(&self) -> &'static str {
        "lifecycle"
    }
    fn writes(&self) -> &'static [&'static str] {
        &["test_published_choice"]
    }
    fn prepare(
        &self,
        _db: &DecompileDB,
        functions: &mut [FunctionData],
    ) -> Option<Box<dyn PreparedAnalysis>> {
        for function in functions {
            function
                .node_statements
                .get_mut(&10)
                .unwrap()
                .push(ClightStmt::Sreturn(None));
            function
                .analysis_candidates
                .entry(10)
                .or_default()
                .insert(ClightStmt::Sreturn(None));
        }
        Some(Box::new(Lifecycle))
    }
    fn build(&self, cx: &FunctionContext<'_>) -> Option<Box<dyn CandidateAnalysis>> {
        Some(Box::new(Rule {
            name: "bound-rule",
            node: 10,
            forbidden: *BOUND_CHOICE.get(&cx.function.analysis_facts).unwrap(),
        }))
    }
}
impl PreparedAnalysis for Lifecycle {
    fn bind(&mut self, _db: &DecompileDB, functions: &mut [FunctionData]) {
        for function in functions {
            let index = function.node_statements[&10]
                .iter()
                .position(|s| matches!(s, ClightStmt::Sreturn(None)))
                .unwrap();
            BOUND_CHOICE.insert(&mut function.analysis_facts, index);
        }
    }
    fn publish(
        self: Box<Self>,
        db: &mut DecompileDB,
        functions: &[FunctionData],
        selection: &ProgramSelectionState,
    ) {
        for function in functions {
            db.rel_push(
                "test_published_choice",
                (
                    function.address,
                    selection.candidate_idx[&(function.address, 10)],
                ),
            );
        }
    }
}

#[test]
fn prepared_evidence_binds_after_candidate_order_is_final_and_survives_dirty_clone() {
    let mut db = DecompileDB::default();
    let mut functions = vec![fixture()];
    let modules: &[&dyn Analysis] = &[&Lifecycle, &c_types::CTypes];
    let stack = Stack::new(modules);
    let mut preparation = stack.prepare(&db, &mut functions);
    // Simulate the selector's deterministic sort. A prepare-time index would
    // now ban the wrong statement; bind must use the finalized vocabulary.
    functions[0]
        .node_statements
        .get_mut(&10)
        .unwrap()
        .swap(0, 2);
    preparation.bind(&db, &mut functions);
    let dirty_clone = functions[0].clone();
    assert_eq!(BOUND_CHOICE.get(&dirty_clone.analysis_facts), Some(&0));
    let out = super::super::solve::solve_function_z3_with_stack(
        &dirty_clone,
        &HashMap::new(),
        &[],
        &stack,
    )
    .unwrap();
    assert_ne!(out.0[&10], Some(0));
    let mut state = ProgramSelectionState::default();
    state
        .candidate_idx
        .insert((dirty_clone.address, 10), out.0[&10]);
    preparation.publish(&mut db, &functions, &state);
    assert_eq!(
        db.rel_iter::<(u64, Option<usize>)>("test_published_choice")
            .copied()
            .collect::<Vec<_>>(),
        vec![(dirty_clone.address, out.0[&10])]
    );
}
