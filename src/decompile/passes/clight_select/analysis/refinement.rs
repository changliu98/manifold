//! One transactional model-refinement driver for all optional analyses.
//!
//! Base C and semantic constraints are outside the scope. If any optional
//! analysis cannot discharge its obligations, the entire extension is popped
//! and its results are explicitly uncertified. No failed proof relaxes a base
//! constraint. A learned clause must exclude its generating model.

use super::constraints::RecordedCond;
use super::{Artifacts, FunctionContext, Stack};
use crate::x86::types::Node;
use std::collections::{BTreeSet, HashMap};
use z3::ast::Bool;
use z3::{Model, Optimize, SatResult};

pub(crate) trait ModelAnalysis {
    fn round_limit(&self) -> usize;
    /// Empty clauses mean accepted; an error means unknown/unsupported, not
    /// acceptance. Clauses refer to this selector's existing choice variables.
    fn inspect(&mut self, model: &Model) -> Result<Vec<Bool>, &'static str>;
    /// Joint commitments may not be independently re-picked after solving.
    fn coupled_nodes(&self) -> BTreeSet<Node>;
    fn finish(
        self: Box<Self>,
        model: Option<&Model>,
        reason: &'static str,
        results: &mut Artifacts,
    );
}

struct Entry {
    name: &'static str,
    rounds: usize,
    analysis: Box<dyn ModelAnalysis>,
}

pub(crate) struct Session {
    entries: Vec<Entry>,
    results: Artifacts,
}

impl Session {
    pub(crate) fn start(stack: &Stack<'_>, cx: &FunctionContext<'_>, opt: &Optimize) -> Self {
        opt.push();
        let entries = stack
            .modules()
            .filter_map(|module| {
                let analysis = module.start_refinement(cx, opt)?;
                Some(Entry {
                    name: module.name(),
                    rounds: 0,
                    analysis,
                })
            })
            .collect();
        Self {
            entries,
            results: Artifacts::default(),
        }
    }

    pub(crate) fn active(&self) -> bool {
        !self.entries.is_empty()
    }

    /// True requests another solve. False permits extraction; any successful
    /// joint assignment has already been added to the shared re-pick ledger.
    pub(crate) fn advance(
        &mut self,
        model: Option<&Model>,
        status: SatResult,
        opt: &Optimize,
        selections: &HashMap<Node, Vec<Bool>>,
        recorded: &mut HashMap<Node, Vec<Vec<RecordedCond>>>,
    ) -> bool {
        if !self.active() {
            return false;
        }
        let mut failure = None;
        let mut refined = false;
        if let Some(model) = model {
            for entry in &mut self.entries {
                let clauses = match entry.analysis.inspect(model) {
                    Ok(clauses) => clauses,
                    Err(reason) => {
                        failure = Some(reason);
                        break;
                    }
                };
                if !clauses.is_empty() {
                    for clause in clauses {
                        if model.eval(&clause, true).and_then(|v| v.as_bool()) != Some(false) {
                            failure = Some("analysis witness did not exclude its generating model");
                            break;
                        }
                        opt.assert(&clause);
                    }
                    if failure.is_some() {
                        break;
                    }
                    if entry.rounds >= entry.analysis.round_limit() {
                        failure = Some("analysis refinement budget exhausted");
                        break;
                    }
                    entry.rounds += 1;
                    refined = true;
                }
            }
        } else {
            failure = Some(if status == SatResult::Unsat {
                "no model satisfies the accumulated analysis witnesses"
            } else {
                "analysis solve resource limit or unavailable model"
            });
        }
        if let Some(reason) = failure {
            for entry in self.entries.drain(..) {
                eprintln!(
                    "[selection-analysis] {} uncertified: {}",
                    entry.name, reason
                );
                entry.analysis.finish(None, reason, &mut self.results);
            }
            opt.pop();
            return true;
        }
        if refined {
            return true;
        }
        for entry in self.entries.drain(..) {
            for node in entry.analysis.coupled_nodes() {
                if let (Some(choices), Some(conditions)) =
                    (selections.get(&node), recorded.get_mut(&node))
                {
                    for (guard, conditions) in choices.iter().zip(conditions) {
                        conditions.push((Some(guard.clone()), u64::MAX));
                    }
                }
            }
            entry.analysis.finish(
                model,
                "all analysis witnesses and universal obligations discharged",
                &mut self.results,
            );
        }
        false
    }

    pub(crate) fn into_results(self) -> Artifacts {
        self.results
    }
}
