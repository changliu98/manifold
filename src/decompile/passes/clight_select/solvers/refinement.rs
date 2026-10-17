//! One transactional model-refinement driver for all optional analyses.
//!
//! Base C and semantic constraints are outside the scope. If any optional
//! analysis cannot finish its refinement, the optional extension is popped
//! and its results are explicitly uncertified. No failed proof relaxes a base
//! constraint. A learned clause must exclude its generating model.

use super::{Checker, Verdict};
use crate::decompile::passes::clight_select::syntax::{Artifacts, FunctionContext, Stack};
use crate::x86::types::Node;
use std::collections::BTreeSet;
use z3::{Model, Optimize, SatResult};

struct Entry<'a> {
    name: &'static str,
    rounds: usize,
    analysis: Box<dyn Checker + 'a>,
}

pub(crate) struct Session<'a> {
    entries: Vec<Entry<'a>>,
    fallback: Vec<(Entry<'a>, &'static str)>,
    results: Artifacts,
    coupled: BTreeSet<Node>,
    resource_start: u64,
}

/// The context's cumulative Z3 work count (rlimit units). Z3 omits a
/// statistic that is still zero and reports one above u32::MAX as a double.
pub(crate) fn resource_count(optimizer: &Optimize) -> u64 {
    match optimizer.get_statistics().value("rlimit count") {
        Some(z3::StatisticsValue::UInt(count)) => u64::from(count),
        Some(z3::StatisticsValue::Double(count)) => count as u64,
        None => 0,
    }
}

/// The parameters of one selection Optimize check: a deterministic work
/// allowance and nothing else. Optimize validates the whole set against its
/// `opt.*` keys and drops all of it over one unknown key such as
/// `random_seed` (silently under this crate); a wall-clock timeout would
/// make the selected model depend on machine load.
pub(crate) fn work_allowance(allowance: u32) -> z3::Params {
    let mut params = z3::Params::new();
    params.set_u32("rlimit", allowance);
    params
}

/// Whether a check that began at work count `before` stopped because it used
/// its whole `allowance`. Z3's reason string does not say (an exhausted
/// allowance may read "canceled", like a cancellation); the count does.
pub(crate) fn exhausted(optimizer: &Optimize, before: u64, allowance: u32) -> bool {
    resource_count(optimizer).saturating_sub(before) >= u64::from(allowance)
}

fn spent(limit: u32, start: u64, current: u64) -> bool {
    current.saturating_sub(start) >= u64::from(limit)
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
            resource_start: resource_count(opt),
        }
    }

    pub(crate) fn active(&self) -> bool {
        !self.entries.is_empty()
    }

    /// Whether the refinement transaction has spent its shared work `limit`,
    /// counted over all of its checks rather than reset on each. Consulted
    /// before a round, never inside a check: the round under way finishes
    /// within its check allowance, so the transaction ends within one check
    /// of `limit`. The unchanged fallback gets its ordinary terminal solve
    /// after the extension is popped.
    pub(crate) fn spent_work(&self, optimizer: &Optimize, limit: u32) -> bool {
        self.active() && spent(limit, self.resource_start, resource_count(optimizer))
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
                let clauses = match entry.analysis.check(model) {
                    Verdict::Accept => Vec::new(),
                    Verdict::Refute(clauses) => clauses,
                    Verdict::Unknown(reason) => {
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
    use crate::decompile::passes::clight_select::solvers::refinement::spent;

    #[test]
    fn the_work_allowance_bounds_an_optimize_check() {
        use z3::ast::Bool;
        z3::with_z3_config(&z3::Config::new(), || {
            let opt = z3::Optimize::new();
            let xs: Vec<Bool> = (0..24).map(|i| Bool::new_const(format!("x{i}"))).collect();
            for (i, x) in xs.iter().enumerate() {
                opt.assert_soft(x, (i % 5 + 1) as u64, None);
            }
            for pair in xs.windows(2) {
                opt.assert(&Bool::or(&[pair[0].not(), pair[1].not()]));
            }
            opt.set_params(
                &crate::decompile::passes::clight_select::solvers::refinement::work_allowance(1),
            );
            let before =
                crate::decompile::passes::clight_select::solvers::refinement::resource_count(&opt);
            assert_eq!(opt.check(&[]), z3::SatResult::Unknown);
            assert!(
                crate::decompile::passes::clight_select::solvers::refinement::exhausted(
                    &opt, before, 1
                )
            );
            opt.set_params(
                &crate::decompile::passes::clight_select::solvers::refinement::work_allowance(
                    u32::MAX,
                ),
            );
            let before =
                crate::decompile::passes::clight_select::solvers::refinement::resource_count(&opt);
            assert_eq!(opt.check(&[]), z3::SatResult::Sat);
            assert!(
                !crate::decompile::passes::clight_select::solvers::refinement::exhausted(
                    &opt,
                    before,
                    u32::MAX
                )
            );
        });
    }

    #[test]
    fn refinement_rounds_share_work_instead_of_resetting_it() {
        assert!(!spent(100, 500, 500));
        assert!(!spent(100, 500, 530));
        assert!(!spent(100, 500, 599));
        assert!(spent(100, 500, 600));
        assert!(spent(100, 500, 650));
        let past_u32 = u64::from(u32::MAX) + 10;
        assert!(!spent(100, past_u32 - 20, past_u32));
        assert!(spent(100, past_u32 - 200, past_u32));
    }
}
