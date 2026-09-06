//! Shared assertion and re-pick recording for every selection analysis.
use super::super::propagator::RawModel;
use crate::x86::types::Node;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use z3::ast::{Ast, Bool, Dynamic};

/// One recorded condition for the post-solve per-node re-pick: the raw (unguarded) condition (None = an unconditional penalty for this candidate) and its weight; weight u64::MAX marks a structural requirement (validity, not preference).
pub(crate) type RecordedCond = (Option<Bool>, u64);

// Where a built constraint lands. Both engines build the SAME formula through this: the Optimize engine hands softs to MaxSMT, the propagator engine attaches a relaxation literal per soft and minimizes them itself.
pub(crate) trait SolveBackend {
    fn assert_hard(&self, cond: &Bool);
    fn assert_soft(&self, cond: &Bool, weight: u64);
}

// The model reads the selection needs, over either engine's model representation.
pub(crate) trait ModelView {
    fn truth(&self, cond: &Bool) -> Option<bool>;
    fn integer(&self, term: &Dynamic) -> Option<i64>;
}

impl ModelView for z3::Model {
    fn truth(&self, cond: &Bool) -> Option<bool> {
        self.eval(cond, true).and_then(|x| x.as_bool())
    }
    fn integer(&self, term: &Dynamic) -> Option<i64> {
        self.eval(term, true)
            .and_then(|x| x.as_int())
            .and_then(|i| i.as_i64())
    }
}

impl ModelView for RawModel {
    fn truth(&self, cond: &Bool) -> Option<bool> {
        self.eval_bool(cond)
    }
    fn integer(&self, term: &Dynamic) -> Option<i64> {
        self.eval_i64(term)
    }
}

// Z3 is the sole selector: structural requirements are always HARD; there is no relaxed retry and no non-Z3 fallback (a function whose constraints are UNSAT yields no selection and signals an upstream candidate-generation bug).
pub(crate) struct ConstraintSink<'a> {
    backend: &'a dyn SolveBackend,
    // The per-function dominant soft weight (compat_w); carried here so the operator-typing rules in `type_of` can emit dominant-soft requirements without threading the weight through every recursive call.
    pub(crate) compat_w: u64,
    // Re-pick recording for multi-candidate nodes: every emitted condition is logged RAW and re-scored in Rust under the fixed model, since node selections are conditionally independent given it.
    record: RefCell<Option<Vec<RecordedCond>>>,
    // Per-function (guard, cond, weight) dedup for the OPTIMIZER side only: identical obligations carry the same MaxSMT meaning, and clause COUNT is the cost driver.
    asserted: RefCell<HashSet<(Option<Bool>, Bool, u64)>>,
}

impl<'a> ConstraintSink<'a> {
    pub(crate) fn new(backend: &'a dyn SolveBackend, compat_w: u64) -> Self {
        ConstraintSink {
            backend,
            compat_w,
            record: RefCell::new(None),
            asserted: RefCell::new(HashSet::new()),
        }
    }

    // True exactly once per distinct (guard, cond, w) within this function.
    pub(crate) fn first_assert(&self, guard: Option<&Bool>, cond: &Bool, w: u64) -> bool {
        self.asserted
            .borrow_mut()
            .insert((guard.cloned(), cond.clone(), w))
    }

    // Open a fresh per-candidate recording scope for the post-solve re-pick.
    pub(crate) fn begin_candidate(&self, recording: bool) {
        *self.record.borrow_mut() = if recording { Some(Vec::new()) } else { None };
    }

    // Close the per-candidate scope, returning the recorded conditions.
    pub(crate) fn take_recorded(&self) -> Vec<RecordedCond> {
        self.record.borrow_mut().take().unwrap_or_default()
    }

    pub(crate) fn log(&self, cond: Option<&Bool>, w: u64) {
        if let Some(buf) = self.record.borrow_mut().as_mut() {
            buf.push((cond.cloned(), w));
        }
    }

    // A selection preference: never asserted into the optimizer, only recorded for the post-solve re-pick (no-op outside a recording scope -- with a single candidate there is nothing to prefer).
    pub(crate) fn prefer(&self, cond: &Bool, w: u64) {
        self.log(Some(cond), w);
    }

    // An unconditional penalty against the current candidate (e.g. capturing a void callee's result); recorded for the re-pick alongside its z3 assertion.
    pub(crate) fn penalize_candidate(&self, w: u64) {
        self.log(None, w);
    }

    // A structural requirement: always hard.
    pub(crate) fn assert_structural(&self, guard: Option<&Bool>, cond: &Bool) {
        self.log(Some(cond), u64::MAX);
        if !self.first_assert(guard, cond, u64::MAX) {
            return;
        }
        let c = match guard {
            Some(g) => g.implies(cond.clone()),
            None => cond.clone(),
        };
        self.backend.assert_hard(&c);
    }

    pub(crate) fn assert_soft_tagged(
        &self,
        guard: Option<&Bool>,
        cond: &Bool,
        w: u64,
        tag: &'static str,
    ) {
        self.log(Some(cond), w);
        if !self.first_assert(guard, cond, w) {
            return;
        }
        SOFT_CLAUSES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        soft_tag_count(tag);
        match guard {
            Some(g) => self.backend.assert_soft(&g.implies(cond.clone()), w),
            None => self.backend.assert_soft(cond, w),
        }
    }

    // Soft assertion on a raw Bool (the candidate-penalty `!guard` forms and the priors).
    pub(crate) fn assert_soft_raw(&self, cond: &Bool, w: u64) {
        SOFT_CLAUSES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.backend.assert_soft(cond, w);
    }

    /// A formula involving another statement choice is not conditionally
    /// independent under a type-only model. Preserve the joint assignment for
    /// every referenced node (including its guard) during local re-picking.
    /// Module authors do not have to maintain a second dependency ledger for
    /// function-wide or cross-candidate hard constraints.
    pub(crate) fn joint_nodes(&self, choices: &HashMap<Node, Vec<Bool>>) -> BTreeSet<Node> {
        let variables: HashMap<Dynamic, Node> = choices
            .iter()
            .flat_map(|(&node, vars)| vars.iter().map(move |var| (Dynamic::from_ast(var), node)))
            .collect();
        let mut protected = BTreeSet::new();
        for (guard, condition, weight) in self.asserted.borrow().iter() {
            if *weight != u64::MAX {
                continue;
            }
            let mut pending = vec![Dynamic::from_ast(condition)];
            let mut seen = HashSet::new();
            let mut joint = false;
            while let Some(term) = pending.pop() {
                if !seen.insert(term.clone()) {
                    continue;
                }
                if let Some(&node) = variables.get(&term) {
                    protected.insert(node);
                    joint = true;
                }
                pending.extend(term.children());
            }
            if joint {
                if let Some(node) = guard
                    .as_ref()
                    .and_then(|g| variables.get(&Dynamic::from_ast(g)))
                {
                    protected.insert(*node);
                }
            }
        }
        protected
    }
}

// Run-wide asserted-soft-clause counter (P4 perf early-warning, CTYPING_PLAN D2: MaxSMT cost scales with conflicting soft-clause count -- the 15x lesson). Swap-reset and reported by infer_select_program.
pub(crate) static SOFT_CLAUSES: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
// Per-family soft-clause breakdown behind MANIFOLD_SOFT_BREAKDOWN (perf triage).
pub(crate) static SOFT_TAGS: std::sync::LazyLock<std::sync::Mutex<BTreeMap<&'static str, usize>>> =
    std::sync::LazyLock::new(|| std::sync::Mutex::new(BTreeMap::new()));

fn soft_tag_count(tag: &'static str) {
    if std::env::var("MANIFOLD_SOFT_BREAKDOWN").is_ok() {
        *SOFT_TAGS.lock().unwrap().entry(tag).or_default() += 1;
    }
}
