//! Solver integration for the abstract-semantics flow theory.
//!
//! `flow.rs` holds the evaluator and knows nothing about Z3; this module is the
//! glue. It runs at the propagator's FINAL callback, when Z3 has a complete
//! candidate assignment, decodes the selection from the fixed literals, folds
//! each basic block, and hands back an EXPLAINING CLAUSE for any contradiction:
//! the negation of the conjunction of the selection literals the contradicting
//! value actually depended on. Z3 treats a consequence propagated at final as a
//! reason to keep searching, so the search continues with that combination
//! ruled out.
//!
//! Final-callback scope, not per-fixed, is a deliberate v1 choice. A per-fixed
//! check would have to re-fold a block on every literal assignment; the final
//! check folds each block once per complete model and is bounded by the round
//! cap below.
//!
//! Two rules keep this from being able to lose an answer:
//!
//!   * A chain containing no selection literal is not a clause at all -- it
//!     would assert `false` and make the function UNSAT. Those are forced
//!     statements contradicting a machine fact, i.e. an adequacy gap, and are
//!     counted rather than injected.
//!   * A progress guard: inject only when some node on the chain has an
//!     alternative candidate that could hold instead. Without one, re-searching
//!     cannot reach a different answer.

use std::collections::{BTreeMap, BTreeSet};

use crate::decompile::passes::clight_select::solvers::flow::{
    self, Contradiction, FlowStats, LocKey,
};
use crate::decompile::passes::clight_select::solvers::in_search::propagator::{
    PropCb, Theory, VetoTheory,
};
use crate::x86::types::{ClightStmt, Node};

/// Per-function ceiling on final-check rounds.
///
/// Every injected clause is a HARD constraint that stays for the rest of the
/// solve, and the progress guard is only local: it knows an alternative exists
/// at one node, not that a globally consistent selection still does. Enough
/// clauses therefore make a function UNSAT, and an UNSAT function falls back to
/// the Optimize path where this theory has no effect at all -- so injecting
/// more can buy strictly less influence.
///
/// Measured on wc (137 functions, propagator engine), cap against Stage-A
/// fallbacks / clauses injected / selections the flow evidence decided:
///
///   cap 50 -> 38 fallbacks, 877 clauses,  8 decided
///   cap  4 -> 12 fallbacks, 228 clauses, 24 decided
///   cap  1 ->  0 fallbacks,  63 clauses, 17 decided
///
/// One is the default because it is the only setting that leaves the engine's
/// fallback behaviour exactly as it was without the theory, while still
/// deciding 17 selections. A first experiment should be strictly additive.
pub const DEFAULT_ROUND_CAP: usize = 1;

/// Everything the evaluator needs about one function, prepared once.
pub struct FlowProblem {
    pub blocks: Vec<flow::Block>,
    pub anchors: flow::FlowAnchors,
    pub candidates: BTreeMap<Node, Vec<ClightStmt>>,
    /// Nodes with more than one candidate, i.e. the ones carrying a literal.
    pub selectable: BTreeSet<Node>,
    /// Term index of each (node, candidate) selection literal, in the shared
    /// registered-term array the propagator hands to `PropCb`.
    pub literal_index: BTreeMap<(Node, usize), usize>,
    pub ptr64: bool,
    pub round_cap: usize,
    /// Exact contradiction sites whose clauses made a previous ground solve
    /// UNSAT.  Maximal-certification retries leave flow checking live at every
    /// other site.
    pub exempt_nodes: BTreeSet<Node>,
}

/// The one theory the propagator carries: a veto set plus the flow check.
pub struct SelectionTheory {
    veto: VetoTheory,
    /// Registered terms below this index belong to the veto set; the rest are
    /// selection literals the flow check reads.
    veto_len: usize,
    /// Selection literal `i` (term index `veto_len + i`) is this (node, index).
    literals: Vec<(Node, usize)>,
    /// Current truth of each selection literal, undone on backtrack.
    assign: Vec<Option<bool>>,
    trail: Vec<usize>,
    scopes: Vec<usize>,
    problem: FlowProblem,
    pub stats: FlowStats,
    /// Nodes named in an injected clause, for the guess-surface proxy.
    pub named_by_flow: BTreeSet<Node>,
    /// Exact sites at which this attempt successfully injected a clause.  This
    /// is deliberately narrower than `named_by_flow`, which contains every
    /// dependency in each explaining chain.
    pub injected_at: BTreeSet<Node>,
    rounds: usize,
}

#[derive(Debug, PartialEq, Eq)]
enum ClausePlan {
    CountOnly,
    Gap,
    Exempt,
    Inject(Vec<usize>),
}

impl SelectionTheory {
    pub fn new(
        veto: VetoTheory,
        veto_len: usize,
        literals: Vec<(Node, usize)>,
        problem: FlowProblem,
    ) -> SelectionTheory {
        let n = literals.len();
        SelectionTheory {
            veto,
            veto_len,
            literals,
            assign: vec![None; n],
            trail: Vec::new(),
            scopes: Vec::new(),
            problem,
            stats: FlowStats::default(),
            named_by_flow: BTreeSet::new(),
            injected_at: BTreeSet::new(),
            rounds: 0,
        }
    }

    pub fn veto(&self) -> &VetoTheory {
        &self.veto
    }

    /// The selection Z3 currently proposes, as (node, candidate index).
    fn decode(&self) -> BTreeMap<Node, usize> {
        let mut out: BTreeMap<Node, usize> = BTreeMap::new();
        for (i, (node, cand)) in self.literals.iter().enumerate() {
            if self.assign.get(i).copied().flatten() == Some(true) {
                // Exactly-one is asserted, so the first true literal is the
                // pick; taking the minimum keeps this deterministic even if a
                // malformed problem ever fixed two.
                out.entry(*node)
                    .and_modify(|c| *c = (*c).min(*cand))
                    .or_insert(*cand);
            }
        }
        out
    }

    /// Split the nodes into the ones whose statement is decided and the ones
    /// still open. An open node is handed over rather than dropped: it still
    /// runs, so the fold has to forget whatever it could write.
    fn selected_statements(
        &self,
        chosen: &BTreeMap<Node, usize>,
    ) -> (BTreeMap<Node, ClightStmt>, BTreeMap<Node, Vec<ClightStmt>>) {
        let mut out = BTreeMap::new();
        let mut open = BTreeMap::new();
        for (node, cands) in &self.problem.candidates {
            let idx = if cands.len() == 1 {
                0
            } else {
                match chosen.get(node) {
                    Some(i) => *i,
                    None => {
                        open.insert(*node, cands.clone());
                        continue;
                    }
                }
            };
            if let Some(stmt) = cands.get(idx) {
                out.insert(*node, stmt.clone());
            }
        }
        (out, open)
    }

    /// Term indices for the currently selected literals of every node on a
    /// chain. `None` when some node on the chain carries no literal, which
    /// means the chain is not expressible as a clause.
    fn chain_terms(
        &self,
        chain: &BTreeSet<Node>,
        chosen: &BTreeMap<Node, usize>,
    ) -> Option<Vec<usize>> {
        let mut out = Vec::new();
        for node in chain {
            let idx = chosen.get(node)?;
            let term = self.problem.literal_index.get(&(*node, *idx))?;
            out.push(*term);
        }
        if out.is_empty() {
            return None;
        }
        out.sort_unstable();
        out.dedup();
        Some(out)
    }

    fn plan_contradiction(
        &self,
        contra: &Contradiction,
        chosen: &BTreeMap<Node, usize>,
    ) -> ClausePlan {
        // Only architectural anchors can constrain the local selection.
        // GlobalType is deliberately returned as CountOnly: it is priced by
        // the program-level feedback loop, where its commitment can change.
        if !matches!(
            contra.kind,
            flow::AnchorKind::Chunk | flow::AnchorKind::ExternSignature
        ) {
            return ClausePlan::CountOnly;
        }
        if self.problem.exempt_nodes.contains(&contra.node) {
            return ClausePlan::Exempt;
        }
        let Some(terms) = self.chain_terms(&contra.chain, chosen) else {
            return ClausePlan::Gap;
        };
        if !flow::chain_has_alternative(
            contra,
            &self.problem.candidates,
            chosen,
            self.problem.ptr64,
        ) {
            return ClausePlan::Gap;
        }
        ClausePlan::Inject(terms)
    }
}

impl Theory for SelectionTheory {
    fn on_fixed(&mut self, cb: &PropCb<'_>, term: usize, value: bool) {
        if term < self.veto_len {
            self.veto.on_fixed(cb, term, value);
            return;
        }
        let i = term - self.veto_len;
        if i < self.assign.len() {
            self.assign[i] = Some(value);
            self.trail.push(i);
        }
    }

    fn on_push(&mut self) {
        self.scopes.push(self.trail.len());
    }

    fn on_pop(&mut self, n: u32) {
        for _ in 0..n {
            let Some(mark) = self.scopes.pop() else {
                break;
            };
            while self.trail.len() > mark {
                if let Some(i) = self.trail.pop() {
                    self.assign[i] = None;
                }
            }
        }
    }

    fn on_final(&mut self, cb: &PropCb<'_>) {
        self.stats.final_rounds += 1;
        self.rounds += 1;
        if self.rounds > self.problem.round_cap {
            if self.rounds == self.problem.round_cap + 1 {
                self.stats.caps_hit += 1;
            }
            return;
        }
        let chosen = self.decode();
        let (selected, open) = self.selected_statements(&chosen);
        if selected.is_empty() {
            return;
        }
        let (round_stats, contras) = flow::eval_function(
            &self.problem.blocks,
            &selected,
            &open,
            &self.problem.candidates,
            &self.problem.anchors,
            &self.problem.selectable,
            self.problem.ptr64,
        );
        // Block counts are a property of the final selection, not of each
        // intermediate round; only the certificate pass records them.
        let _ = round_stats;

        let mut injected = false;
        for contra in &contras {
            if injected {
                // One clause per round is enough: Z3 backtracks on the first
                // consequence anyway, and a second would be built from an
                // assignment the first has already ruled out.
                break;
            }
            // Only the two ARCHITECTURAL anchors are grounds to constrain the
            // search. A memory chunk is an instruction encoding and an extern
            // signature is the ABI; both are facts the machine cannot violate.
            //
            // The other two are not. A statement-vs-statement disagreement says
            // one of two spellings is wrong without saying which. A committed
            // global type is itself partly inferred upstream. Injecting either
            // drove 28% of wc's functions to UNSAT and straight back to the
            // fallback path, where this theory has no effect at all. Both are
            // still counted, and the certificate still reports them.
            let terms = match self.plan_contradiction(contra, &chosen) {
                ClausePlan::CountOnly => {
                    self.stats.contradictions += 1;
                    self.stats.count_kind(contra.kind);
                    continue;
                }
                ClausePlan::Gap => {
                    self.stats.gaps += 1;
                    self.stats.contradictions += 1;
                    self.stats.count_kind(contra.kind);
                    continue;
                }
                ClausePlan::Exempt => {
                    self.stats.gaps += 1;
                    self.stats.exemptions_skipped += 1;
                    self.stats.contradictions += 1;
                    self.stats.count_kind(contra.kind);
                    continue;
                }
                ClausePlan::Inject(terms) => terms,
            };
            if cb.conflict(&terms) {
                self.stats.clauses_injected += 1;
                self.stats.contradictions += 1;
                self.stats.count_kind(contra.kind);
                for node in &contra.chain {
                    self.named_by_flow.insert(*node);
                }
                self.injected_at.insert(contra.node);
                injected = true;
            }
        }
    }
}

/// Contradictions of the FINAL selection, i.e. the certificate pass. A block
/// that carries an anchor and no contradiction is FLOW-CERTIFIED: its selected
/// statements are consistent with every machine fact crossing it. That is flow
/// consistency over one tiny domain, not verification of the block.
pub fn certify(
    blocks: &[flow::Block],
    anchors: &flow::FlowAnchors,
    selected: &BTreeMap<Node, ClightStmt>,
    candidates: &BTreeMap<Node, Vec<ClightStmt>>,
    selectable: &BTreeSet<Node>,
    ptr64: bool,
) -> (FlowStats, Vec<Contradiction>) {
    // The final selection decides every node, so nothing is left open.
    flow::eval_function(
        blocks,
        selected,
        &BTreeMap::new(),
        candidates,
        anchors,
        selectable,
        ptr64,
    )
}

/// Label for a contradiction's location, shared by the audit and the
/// certificate output.
pub fn describe(c: &Contradiction) -> String {
    format!(
        "node={:#x} {} claims {} but {} is flowing (anchor {:?})",
        c.node,
        flow::loc_label(c.loc),
        flow::aval_label(c.claimed),
        flow::aval_label(c.flowing),
        c.kind
    )
}

/// True when the location is a plain register, which is the only kind the
/// tie-breaking proxy reports on.
pub fn is_reg_loc(loc: LocKey) -> bool {
    matches!(loc, LocKey::Reg(_))
}

#[cfg(test)]
mod tests {
    use crate::decompile::passes::clight_select::solvers::in_search::flow_theory::*;
    use crate::decompile::passes::clight_select::solvers::in_search::propagator::RawSolver;
    use crate::x86::types::{
        ClightAttr, ClightExpr, ClightFloatSize, ClightIntSize, ClightSignedness, ClightType,
        MemoryChunk,
    };
    use std::cell::RefCell;
    use std::rc::Rc;
    use z3::ast::Bool;
    use z3::SatResult;

    fn int32() -> ClightType {
        ClightType::Tint(
            ClightIntSize::I32,
            ClightSignedness::Signed,
            ClightAttr::default(),
        )
    }

    fn f64ty() -> ClightType {
        ClightType::Tfloat(ClightFloatSize::F64, ClightAttr::default())
    }

    /// Build a one-node problem: an MInt32-anchored register read by a node
    /// with `cands` candidates.
    fn problem(
        cands: Vec<ClightStmt>,
        round_cap: usize,
    ) -> (FlowProblem, Vec<Bool>, Vec<(Node, usize)>) {
        let load: Node = 0x10;
        let use_: Node = 0x11;
        let mut anchors = flow::FlowAnchors::default();
        anchors
            .chunk
            .insert(load, (5, flow::anchor_of_chunk(MemoryChunk::MInt32)));
        let mut candidates = BTreeMap::new();
        candidates.insert(
            load,
            vec![ClightStmt::Sset(5, ClightExpr::EconstInt(0, int32()))],
        );
        candidates.insert(use_, cands.clone());
        let selectable: BTreeSet<Node> = if cands.len() > 1 {
            [use_].into_iter().collect()
        } else {
            BTreeSet::new()
        };
        let mut literal_index = BTreeMap::new();
        let mut lits = Vec::new();
        let mut layout = Vec::new();
        if cands.len() > 1 {
            for i in 0..cands.len() {
                literal_index.insert((use_, i), i);
                lits.push(Bool::new_const(format!("sel_{}", i)));
                layout.push((use_, i));
            }
        }
        (
            FlowProblem {
                blocks: vec![vec![load, use_]],
                anchors,
                candidates,
                selectable,
                literal_index,
                ptr64: true,
                round_cap,
                exempt_nodes: BTreeSet::new(),
            },
            lits,
            layout,
        )
    }

    // The headline in-solve case: a float-annotated read of an integer-anchored
    // register, with an integer sibling available. The explaining clause must
    // rule the float candidate out and the search must land on the sibling.
    #[test]
    fn a_flow_clause_at_final_rules_out_the_contradicting_candidate() {
        let cfg = z3::Config::new();
        z3::with_z3_config(&cfg, || {
            let cands = vec![
                ClightStmt::Sset(7, ClightExpr::Etempvar(5, f64ty())),
                ClightStmt::Sset(7, ClightExpr::Etempvar(5, int32())),
            ];
            let (prob, lits, layout) = problem(cands, DEFAULT_ROUND_CAP);
            let mut solver = RawSolver::new_simple();
            solver.init_propagator();
            // Exactly one candidate, and prefer the float one, so only the flow
            // clause can move the answer.
            solver.assert(&Bool::or(&[&lits[0], &lits[1]]));
            solver.assert(&Bool::and(&[&lits[0], &lits[1]]).not());
            let theory = Rc::new(RefCell::new(SelectionTheory::new(
                VetoTheory::new(Vec::new()),
                0,
                layout,
                prob,
            )));
            solver.set_theory(theory.clone(), lits.clone());
            assert_eq!(solver.check_assumptions(&[]), SatResult::Sat);
            let m = solver.model().expect("model");
            assert_eq!(
                m.eval_bool(&lits[0]),
                Some(false),
                "float candidate survived"
            );
            assert_eq!(m.eval_bool(&lits[1]), Some(true));
            let t = theory.borrow();
            assert!(t.stats.clauses_injected >= 1, "no clause was injected");
            assert!(t.stats.final_rounds >= 2, "final check did not iterate");
        });
    }

    #[test]
    fn committed_global_disagreement_is_counted_but_never_vetoed() {
        let node: Node = 0x31;
        let symbol = 0x9000usize;
        let problem = FlowProblem {
            blocks: Vec::new(),
            anchors: flow::FlowAnchors::default(),
            candidates: [(
                node,
                vec![
                    ClightStmt::Sset(7, ClightExpr::Evar(symbol, f64ty())),
                    ClightStmt::Sset(7, ClightExpr::Evar(symbol, int32())),
                ],
            )]
            .into_iter()
            .collect(),
            selectable: [node].into_iter().collect(),
            literal_index: [((node, 0), 0), ((node, 1), 1)].into_iter().collect(),
            ptr64: true,
            round_cap: DEFAULT_ROUND_CAP,
            exempt_nodes: BTreeSet::new(),
        };
        let theory = SelectionTheory::new(
            VetoTheory::new(Vec::new()),
            0,
            vec![(node, 0), (node, 1)],
            problem,
        );
        let contradiction = Contradiction {
            node,
            loc: flow::LocKey::Var(symbol),
            claimed: flow::claim_of_type(&f64ty(), true),
            flowing: flow::claim_of_type(&int32(), true),
            kind: flow::AnchorKind::GlobalType,
            global_symbol: Some(symbol),
            chain: [node].into_iter().collect(),
        };
        assert_eq!(
            theory.plan_contradiction(&contradiction, &[(node, 0)].into_iter().collect()),
            ClausePlan::CountOnly
        );
    }

    #[test]
    fn exempted_gap_does_not_disable_flow_at_other_nodes() {
        let gap: Node = 0x41;
        let live: Node = 0x51;
        let candidates = [gap, live]
            .into_iter()
            .map(|node| {
                (
                    node,
                    vec![
                        ClightStmt::Sset(7, ClightExpr::Etempvar(5, f64ty())),
                        ClightStmt::Sset(7, ClightExpr::Etempvar(5, int32())),
                    ],
                )
            })
            .collect();
        let layout = vec![(gap, 0), (gap, 1), (live, 0), (live, 1)];
        let literal_index = layout
            .iter()
            .enumerate()
            .map(|(term, &(node, candidate))| ((node, candidate), term))
            .collect();
        let problem = FlowProblem {
            blocks: Vec::new(),
            anchors: flow::FlowAnchors::default(),
            candidates,
            selectable: [gap, live].into_iter().collect(),
            literal_index,
            ptr64: true,
            round_cap: DEFAULT_ROUND_CAP,
            exempt_nodes: [gap].into_iter().collect(),
        };
        let theory = SelectionTheory::new(VetoTheory::new(Vec::new()), 0, layout, problem);
        let contradiction = |node| Contradiction {
            node,
            loc: flow::LocKey::Reg(5),
            claimed: flow::claim_of_type(&f64ty(), true),
            flowing: flow::claim_of_type(&int32(), true),
            kind: flow::AnchorKind::Chunk,
            global_symbol: None,
            chain: [node].into_iter().collect(),
        };
        let chosen = [(gap, 0), (live, 0)].into_iter().collect();
        assert_eq!(
            theory.plan_contradiction(&contradiction(gap), &chosen),
            ClausePlan::Exempt
        );
        assert_eq!(
            theory.plan_contradiction(&contradiction(live), &chosen),
            ClausePlan::Inject(vec![2])
        );
    }

    // Same contradiction with no sibling: the progress guard must stop the
    // injection, the solve must stay SAT, and it must be counted as a gap.
    #[test]
    fn without_an_alternative_the_guard_records_a_gap_and_stays_sat() {
        let cfg = z3::Config::new();
        z3::with_z3_config(&cfg, || {
            let cands = vec![
                ClightStmt::Sset(7, ClightExpr::Etempvar(5, f64ty())),
                ClightStmt::Sset(8, ClightExpr::Etempvar(5, f64ty())),
            ];
            let (prob, lits, layout) = problem(cands, DEFAULT_ROUND_CAP);
            let mut solver = RawSolver::new_simple();
            solver.init_propagator();
            solver.assert(&Bool::or(&[&lits[0], &lits[1]]));
            solver.assert(&Bool::and(&[&lits[0], &lits[1]]).not());
            let theory = Rc::new(RefCell::new(SelectionTheory::new(
                VetoTheory::new(Vec::new()),
                0,
                layout,
                prob,
            )));
            solver.set_theory(theory.clone(), lits.clone());
            assert_eq!(solver.check_assumptions(&[]), SatResult::Sat);
            let t = theory.borrow();
            assert_eq!(t.stats.clauses_injected, 0);
            assert!(t.stats.gaps >= 1, "the gap was not recorded");
        });
    }

    // Termination: a cap of zero means no injection ever happens, so the search
    // must finish in one round rather than spin.
    #[test]
    fn the_round_cap_stops_injection_and_terminates() {
        let cfg = z3::Config::new();
        z3::with_z3_config(&cfg, || {
            let cands = vec![
                ClightStmt::Sset(7, ClightExpr::Etempvar(5, f64ty())),
                ClightStmt::Sset(7, ClightExpr::Etempvar(5, int32())),
            ];
            let (prob, lits, layout) = problem(cands, 0);
            let mut solver = RawSolver::new_simple();
            solver.init_propagator();
            solver.assert(&Bool::or(&[&lits[0], &lits[1]]));
            solver.assert(&Bool::and(&[&lits[0], &lits[1]]).not());
            let theory = Rc::new(RefCell::new(SelectionTheory::new(
                VetoTheory::new(Vec::new()),
                0,
                layout,
                prob,
            )));
            solver.set_theory(theory.clone(), lits.clone());
            assert_eq!(solver.check_assumptions(&[]), SatResult::Sat);
            let t = theory.borrow();
            assert_eq!(t.stats.clauses_injected, 0);
            assert_eq!(t.stats.caps_hit, 1);
        });
    }

    // A wide integer chunk is a bit-copy: the float reading is legitimate and
    // no clause may be injected for it.
    #[test]
    fn a_wide_chunk_bit_copy_injects_nothing() {
        let cfg = z3::Config::new();
        z3::with_z3_config(&cfg, || {
            let load: Node = 0x10;
            let use_: Node = 0x11;
            let mut anchors = flow::FlowAnchors::default();
            anchors
                .chunk
                .insert(load, (5, flow::anchor_of_chunk(MemoryChunk::MInt64)));
            let cands = vec![
                ClightStmt::Sset(7, ClightExpr::Etempvar(5, f64ty())),
                ClightStmt::Sset(7, ClightExpr::Etempvar(5, int32())),
            ];
            let mut candidates = BTreeMap::new();
            candidates.insert(
                load,
                vec![ClightStmt::Sset(5, ClightExpr::EconstInt(0, int32()))],
            );
            candidates.insert(use_, cands.clone());
            let mut literal_index = BTreeMap::new();
            let mut lits = Vec::new();
            let mut layout = Vec::new();
            for i in 0..cands.len() {
                literal_index.insert((use_, i), i);
                lits.push(Bool::new_const(format!("w_{}", i)));
                layout.push((use_, i));
            }
            let prob = FlowProblem {
                blocks: vec![vec![load, use_]],
                anchors,
                candidates,
                selectable: [use_].into_iter().collect(),
                literal_index,
                ptr64: true,
                round_cap: DEFAULT_ROUND_CAP,
                exempt_nodes: BTreeSet::new(),
            };
            let mut solver = RawSolver::new_simple();
            solver.init_propagator();
            solver.assert(&Bool::or(&[&lits[0], &lits[1]]));
            solver.assert(&Bool::and(&[&lits[0], &lits[1]]).not());
            solver.assert(&lits[0]);
            let theory = Rc::new(RefCell::new(SelectionTheory::new(
                VetoTheory::new(Vec::new()),
                0,
                layout,
                prob,
            )));
            solver.set_theory(theory.clone(), lits.clone());
            assert_eq!(solver.check_assumptions(&[]), SatResult::Sat);
            assert_eq!(theory.borrow().stats.clauses_injected, 0);
        });
    }

    // The veto half must keep working when a flow part sits behind it in the
    // same registered-term array.
    #[test]
    fn veto_terms_still_fire_alongside_the_flow_terms() {
        let cfg = z3::Config::new();
        z3::with_z3_config(&cfg, || {
            let vetoed = Bool::new_const("vetoed");
            let other = Bool::new_const("other");
            let cands = vec![ClightStmt::Sset(7, ClightExpr::Etempvar(5, int32()))];
            let (prob, _, _) = problem(cands, DEFAULT_ROUND_CAP);
            let mut solver = RawSolver::new_simple();
            solver.init_propagator();
            solver.assert(&Bool::or(&[&vetoed, &other]));
            let theory = Rc::new(RefCell::new(SelectionTheory::new(
                VetoTheory::new(vec!["test"]),
                1,
                Vec::new(),
                prob,
            )));
            solver.set_theory(theory.clone(), vec![vetoed.clone()]);
            assert_eq!(solver.check_assumptions(&[]), SatResult::Sat);
            let m = solver.model().expect("model");
            assert_eq!(m.eval_bool(&vetoed), Some(false));
            assert_eq!(m.eval_bool(&other), Some(true));
            assert!(theory.borrow().veto().fired_for("test") >= 1);
        });
    }
}
