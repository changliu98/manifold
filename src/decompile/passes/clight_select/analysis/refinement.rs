//! One transactional model-refinement driver for all optional analyses.
//!
//! Base C and semantic constraints are outside the scope. If any optional
//! analysis cannot finish its refinement, the optional extension is popped
//! and its results are explicitly uncertified. No failed proof relaxes a base
//! constraint. A learned clause must exclude its generating model.

use super::{Artifacts, FunctionContext, Stack};
use crate::x86::types::Node;
use std::collections::BTreeSet;
use z3::ast::Bool;
use z3::{Model, Optimize, SatResult};

pub(crate) trait ModelAnalysis {
    fn round_limit(&self) -> usize;
    /// Empty clauses mean accepted; an error means unknown/unsupported, not
    /// acceptance. Clauses refer to this selector's existing choice variables.
    fn inspect(&mut self, model: &Model) -> Result<Vec<Bool>, &'static str>;
    /// Joint commitments may not be independently re-picked after solving.
    fn coupled_nodes(&self) -> BTreeSet<Node>;
    /// Restrictions required if the optional search is rolled back. A failed
    /// semantic extension must not leave its unchecked representations enabled.
    fn fallback_constraints(&self) -> Vec<Bool> {
        Vec::new()
    }
    fn finish(
        self: Box<Self>,
        model: Option<&Model>,
        reason: &'static str,
        results: &mut Artifacts,
    );
    /// The terminal fallback is a different model. Modules may retain only
    /// certificates whose complete guards hold in that model; by default an
    /// aborted extension remains uncertified.
    fn finish_fallback(
        self: Box<Self>,
        _model: Option<&Model>,
        reason: &'static str,
        results: &mut Artifacts,
    ) {
        self.finish(None, reason, results);
    }
}

struct Entry<'a> {
    name: &'static str,
    rounds: usize,
    analysis: Box<dyn ModelAnalysis + 'a>,
}

pub(crate) struct Session<'a> {
    entries: Vec<Entry<'a>>,
    fallback: Vec<(Entry<'a>, &'static str)>,
    results: Artifacts,
    coupled: BTreeSet<Node>,
    resource_start: u32,
}

fn resource_count(optimizer: &Optimize) -> Option<u32> {
    match optimizer.get_statistics().value("rlimit count") {
        Some(z3::StatisticsValue::UInt(count)) => Some(count),
        _ => None,
    }
}

fn remaining_work(limit: u32, start: u32, current: u32) -> u32 {
    limit.saturating_sub(current.wrapping_sub(start))
}

impl<'a> Session<'a> {
    pub(crate) fn start(stack: &Stack<'_>, cx: &FunctionContext<'a>, opt: &'a Optimize) -> Self {
        opt.push();
        let entries = stack
            .refiners(cx, opt)
            .into_iter()
            .map(|(name, analysis)| Entry {
                name,
                rounds: 0,
                analysis,
            })
            .collect();
        Self {
            entries,
            fallback: Vec::new(),
            results: Artifacts::default(),
            coupled: BTreeSet::new(),
            resource_start: resource_count(opt).unwrap_or(0),
        }
    }

    pub(crate) fn active(&self) -> bool {
        !self.entries.is_empty()
    }

    /// One deterministic work allowance for the whole refinement transaction,
    /// not a fresh full allowance on every Optimize::check. The unchanged
    /// fallback gets its ordinary terminal solve after the extension is popped.
    pub(crate) fn remaining_work(&self, optimizer: &Optimize, limit: u32) -> u32 {
        if !self.active() {
            return limit;
        }
        resource_count(optimizer).map_or(limit, |current| {
            remaining_work(limit, self.resource_start, current)
        })
    }

    /// True requests another solve. False permits extraction; any successful
    /// joint assignment has already been added to the shared re-pick ledger.
    pub(crate) fn advance(
        &mut self,
        model: Option<&Model>,
        status: SatResult,
        opt: &Optimize,
    ) -> bool {
        if !self.active() {
            for (entry, reason) in self.fallback.drain(..) {
                entry
                    .analysis
                    .finish_fallback(model, reason, &mut self.results);
            }
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
            let fallback: Vec<_> = self
                .entries
                .iter()
                .flat_map(|entry| entry.analysis.fallback_constraints())
                .collect();
            for entry in self.entries.drain(..) {
                self.coupled.extend(entry.analysis.coupled_nodes());
                eprintln!(
                    "[selection-analysis] {} uncertified: {}",
                    entry.name, reason
                );
                self.fallback.push((entry, reason));
            }
            opt.pop();
            for restriction in fallback {
                opt.assert(&restriction);
            }
            return true;
        }
        if refined {
            return true;
        }
        for entry in self.entries.drain(..) {
            self.coupled.extend(entry.analysis.coupled_nodes());
            entry.analysis.finish(
                model,
                "model accepted; certification coverage reported separately",
                &mut self.results,
            );
        }
        false
    }

    pub(crate) fn into_results(mut self) -> Artifacts {
        for (entry, reason) in self.fallback.drain(..) {
            entry
                .analysis
                .finish_fallback(None, reason, &mut self.results);
        }
        self.results
    }

    pub(crate) fn coupled_nodes(&self) -> &BTreeSet<Node> {
        &self.coupled
    }
}

#[cfg(test)]
mod budget_tests {
    use super::remaining_work;

    #[test]
    fn refinement_rounds_share_work_instead_of_resetting_it() {
        assert_eq!(remaining_work(100, 500, 500), 100);
        assert_eq!(remaining_work(100, 500, 530), 70);
        assert_eq!(remaining_work(100, 500, 590), 10);
        assert_eq!(remaining_work(100, 500, 600), 0);
        assert_eq!(remaining_work(100, 500, 650), 0);
        assert_eq!(remaining_work(100, u32::MAX - 9, 10), 80);
    }
}
