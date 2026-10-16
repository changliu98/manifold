//! Storage is a theory of the final selector
//!
//! The caller supplies its existing per-function Optimize instance. Layout
//! variables share that instance with statement/type choices. A verifier sees
//! the complete machine obligation, while the learner sees only accumulated
//! byte/writer witnesses. New layouts require a clean inference-epoch replay
//! before they can authorize emitted C. No model is itself a C certificate.

use std::collections::BTreeMap;

use z3::ast::{Ast, Bool, Int};
use z3::{Model, Optimize};

use crate::decompile::passes::semantic_counterexample::{
    self as storage, Counterexample, FailureKind, Prepared, Representation, StorageId, Verdict,
    View,
};
use crate::x86::types::{Address, Node};

pub(crate) const MAX_REFINEMENTS: usize = 128;

#[derive(Clone, Debug)]
pub(crate) struct Step {
    pub extent: i64,
    pub shared: bool,
    pub joined_writes: Vec<Node>,
    pub witness: Option<Counterexample>,
}

#[derive(Clone, Debug)]
pub(crate) struct Decision {
    pub prepared: Prepared,
    pub steps: Vec<Step>,
    pub representation: Option<Representation>,
    pub requires_replay: bool,
    pub reason: &'static str,
}

pub(crate) struct Encoding {
    prepared: Prepared,
    shared: Bool,
    extent: Int,
    members: BTreeMap<Node, Bool>,
    candidate_writes: BTreeMap<Node, Vec<(Bool, Option<View>)>>,
    steps: Vec<Step>,
}

impl Encoding {
    /// A finite grammar: retain scalar storage, or introduce a frame object
    /// with a chosen extent and a chosen subset of writer embeddings. Neither
    /// observations nor the symbolic maximum choose these variables here.
    pub(crate) fn build(prepared: &Prepared, opt: &Optimize) -> Self {
        let p = &prepared.problem;
        let name = format!("storage_{:x}_{}", p.function, p.base);
        let shared = Bool::new_const(format!("{name}_shared"));
        let extent = Int::new_const(format!("{name}_extent"));
        let room = if p.base >= 0 {
            p.frame_size.saturating_sub(p.base)
        } else {
            p.base.saturating_neg()
        };
        let mut limit = room.min(storage::MAX_OBJECT_BYTES);
        // Physical object geometry, never CFG reachability.
        for &other in &p.other_roots {
            if other > p.base {
                limit = limit.min(other - p.base);
            }
        }
        for &(offset, width) in &prepared.unmapped {
            if storage::end(offset, width).is_some_and(|end| end > p.base) {
                limit = limit.min(offset.saturating_sub(p.base));
            }
        }
        opt.assert(&extent.ge(1));
        opt.assert(&shared.implies(extent.le(limit)));
        opt.assert(
            &shared
                .not()
                .implies(extent.eq(prepared.initial.argument.extent)),
        );
        let mut members = BTreeMap::new();
        for write in &p.writes {
            let member = Bool::new_const(format!("{name}_writer_{:x}", write.node));
            opt.assert(&member.implies(&shared));
            if let Some(end) = storage::end(write.offset, write.width)
                .and_then(|end| end.checked_sub(p.base))
                .filter(|_| write.offset >= p.base && write.width <= 8)
            {
                opt.assert(&member.implies(extent.ge(end)));
            } else {
                opt.assert(&member.not());
            }
            members.insert(write.node, member);
        }
        // These objectives follow the selector's existing objectives. With
        // independent writer bits, minimum membership uniquely leaves every
        // unconstrained writer in its original storage. No solver-order tie.
        opt.minimize(&shared.ite(&Int::from_i64(1), &Int::from_i64(0)));
        opt.minimize(&extent);
        let costs: Vec<_> = members
            .values()
            .map(|m| m.ite(&Int::from_i64(1), &Int::from_i64(0)))
            .collect();
        if !costs.is_empty() {
            opt.minimize(&Int::add(&costs));
        }
        Self {
            prepared: prepared.clone(),
            shared,
            extent,
            members,
            candidate_writes: BTreeMap::new(),
            steps: Vec::new(),
        }
    }

    /// Couple each provisional write embedding to the actual statement
    /// variable. A witness can now select another expression without first
    /// replacing an already adequate allocation.
    pub(crate) fn bind_candidates(
        &mut self,
        selections: &std::collections::HashMap<Node, Vec<Bool>>,
    ) {
        for (&node, views) in &self.prepared.candidate_writes {
            let guards = selections
                .get(&node)
                .cloned()
                .unwrap_or_else(|| vec![Bool::from_bool(true); views.len()]);
            if guards.len() == views.len() && (selections.contains_key(&node) || views.len() == 1) {
                self.candidate_writes.insert(
                    node,
                    guards.into_iter().zip(views.iter().copied()).collect(),
                );
            }
        }
    }

    pub(crate) fn coupled_nodes(&self) -> impl Iterator<Item = Node> + '_ {
        self.candidate_writes.keys().copied()
    }

    fn original_writes(&self, model: &Model) -> Option<BTreeMap<Node, View>> {
        let mut writes = self.prepared.initial.writes.clone();
        for (&node, choices) in &self.candidate_writes {
            let selected: Vec<_> = choices
                .iter()
                .filter(|(guard, _)| {
                    model.eval(guard, true).and_then(|v| v.as_bool()) == Some(true)
                })
                .collect();
            if selected.len() != 1 {
                return None;
            }
            writes.insert(node, selected[0].1?);
        }
        Some(writes)
    }

    fn representation(&self, model: &Model) -> Option<Representation> {
        let shared = model.eval(&self.shared, true)?.as_bool()?;
        let extent = model.eval(&self.extent, true)?.as_i64()?;
        let mut writes = self.original_writes(model)?;
        if !shared {
            return Some(Representation {
                writes,
                ..self.prepared.initial.clone()
            });
        }
        let p = &self.prepared.problem;
        let object = StorageId::Frame(storage::ledger::ObjectId {
            function: p.function,
            base: p.base,
        });
        for write in &p.writes {
            if model.eval(&self.members[&write.node], true)?.as_bool()? {
                writes.insert(
                    write.node,
                    View {
                        object,
                        offset: write.offset - p.base,
                        extent,
                    },
                );
            }
        }
        Some(Representation {
            address_preserved: true,
            argument: View {
                object,
                offset: 0,
                extent,
            },
            writes,
        })
    }

    /// Return a clause for this *particular* byte/writer witness. It must be
    /// false in the model that generated the witness; this is checked before
    /// assertion, making stuttering and non-guiding "refinements" errors.
    fn learn(&self, witness: &Counterexample) -> Option<Bool> {
        if witness.function != self.prepared.problem.function
            || witness.base != self.prepared.problem.base
        {
            return None;
        }
        match witness.kind {
            FailureKind::AddressMaterialization => Some(self.shared.clone()),
            FailureKind::Extent | FailureKind::CompleteAccess => {
                Some(if witness.observed_byte < 0 {
                    Bool::from_bool(false)
                } else {
                    self.extent.gt(witness.observed_byte)
                })
            }
            FailureKind::WriteCorrespondence => {
                let p = &self.prepared.problem;
                let node = witness.writer?;
                let write = p.writes.iter().find(|w| w.node == node)?;
                let machine_read = p.base.checked_add(witness.observed_byte)?;
                let source_read = self
                    .prepared
                    .initial
                    .argument
                    .offset
                    .checked_add(witness.observed_byte)?;
                let agrees = |view: &View| -> Option<bool> {
                    let mut same = true;
                    for byte in 0..write.width {
                        let machine_alias = write.offset.checked_add(byte as i64)? == machine_read;
                        let source_alias = view.object == self.prepared.initial.argument.object
                            && view.offset.checked_add(byte as i64)? == source_read;
                        same &= machine_alias == source_alias;
                    }
                    Some(same)
                };
                let original_agrees = if let Some(choices) = self.candidate_writes.get(&node) {
                    Bool::or(
                        &choices
                            .iter()
                            .filter_map(|(guard, view)| {
                                // Unsupported embeddings are not generalized from a
                                // different candidate's counterexample.
                                view.as_ref()
                                    .and_then(agrees)
                                    .unwrap_or(true)
                                    .then(|| guard.clone())
                            })
                            .collect::<Vec<_>>(),
                    )
                } else {
                    Bool::from_bool(agrees(self.prepared.initial.writes.get(&node)?)?)
                };
                let physically_aliases = (write.offset..storage::end(write.offset, write.width)?)
                    .contains(&machine_read);
                let joined_agrees = if physically_aliases {
                    self.members.get(&node)?.clone()
                } else {
                    Bool::from_bool(true)
                };
                Some(self.shared.ite(&joined_agrees, &original_agrees))
            }
        }
    }

    pub(crate) fn refine(&mut self, model: &Model) -> Result<Option<Bool>, &'static str> {
        let representation = self
            .representation(model)
            .ok_or("layout model unavailable")?;
        use crate::decompile::passes::clight_select::solvers::obligations::{Verdict as Outcome, Witness};
        let check = crate::decompile::passes::clight_select::solvers::obligations::check_layout(&self.prepared.problem, &representation);
        let witness = match (check.verdict, check.witness) {
            (Outcome::Equivalent, _) => None,
            (Outcome::Refuted, Some(Witness::Storage(witness))) => Some(witness),
            _ => return Err("storage verifier unknown or unsupported"),
        };
        self.steps.push(Step {
            extent: representation.argument.extent,
            shared: matches!(representation.argument.object, StorageId::Frame(_)),
            joined_writes: representation
                .writes
                .iter()
                .filter_map(|(&node, view)| {
                    (view.object == representation.argument.object).then_some(node)
                })
                .collect(),
            witness: witness.clone(),
        });
        let Some(witness) = witness else {
            return Ok(None);
        };
        let clause = self
            .learn(&witness)
            .ok_or("witness is outside the layout grammar")?;
        // The shared refinement driver checks progress and asserts the clause.
        Ok(Some(clause))
    }

    pub(crate) fn finish(self, model: Option<&Model>, reason: &'static str) -> Decision {
        let representation = model.and_then(|m| self.representation(m));
        let requires_replay = model
            .and_then(|m| m.eval(&self.shared, true))
            .and_then(|b| b.as_bool())
            .unwrap_or(false);
        Decision {
            prepared: self.prepared,
            steps: self.steps,
            representation,
            requires_replay,
            reason,
        }
    }
}

pub(crate) fn requests(decisions: &[Decision]) -> Vec<(Address, Node, i64, i64)> {
    decisions
        .iter()
        .filter(|d| d.requires_replay)
        .flat_map(|d| {
            let p = &d.prepared.problem;
            d.representation
                .iter()
                .filter(|r| matches!(r.argument.object, StorageId::Frame(_)))
                .flat_map(move |r| {
                    p.anchors
                        .iter()
                        .map(move |&anchor| (p.function, anchor, p.base, r.argument.extent))
                })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::decompile::passes::clight_select::solvers::storage_theory::*;
    use std::collections::{BTreeSet, HashMap};
    use storage::{Access, Problem};

    fn prepared() -> Prepared {
        let writes = vec![
            Access {
                node: 20,
                offset: 16,
                width: 1,
                local: 11,
            },
            Access {
                node: 30,
                offset: 20,
                width: 4,
                local: 12,
            },
            Access {
                node: 40,
                offset: 24,
                width: 2,
                local: 13,
            },
        ];
        let initial = Representation {
            address_preserved: true,
            argument: View {
                object: StorageId::Scalar(10),
                offset: 0,
                extent: 4,
            },
            writes: writes
                .iter()
                .map(|w| {
                    (
                        w.node,
                        View {
                            object: StorageId::Scalar(w.local),
                            offset: 0,
                            extent: w.width as i64,
                        },
                    )
                })
                .collect(),
        };
        Prepared {
            problem: Problem {
                function: 1,
                base: 16,
                call: 90,
                lea: 80,
                anchors: vec![80],
                root: 10,
                frame_size: 64,
                observations: vec![(0, 1), (4, 4), (9, 1)],
                fields: vec![],
                writes,
                reads: vec![],
                other_roots: BTreeSet::new(),
                index: None,
                views: vec![],
                minimum_extent: 0,
            },
            initial,
            unmapped: vec![],
            candidate_writes: BTreeMap::new(),
        }
    }

    fn final_select(p: Prepared) -> Decision {
        let mut f = crate::decompile::passes::clight_select::query::FunctionData::new(
            1,
            "search".into(),
            vec![],
            vec![],
            None,
            64,
            80,
            true,
        );
        crate::decompile::passes::clight_select::solvers::storage::PROBLEMS.insert(&mut f.analysis_facts, vec![p]);
        let result = crate::decompile::passes::clight_select::syntax::solve::solve_function_z3(&f, &HashMap::new(), &[]).unwrap().5;
        crate::decompile::passes::clight_select::solvers::storage::DECISIONS.get(&result).unwrap()[0].clone()
    }

    #[test]
    fn final_selector_learns_multiple_distinct_layouts_from_byte_and_writer_witnesses() {
        let decision = final_select(prepared());
        assert!(decision.steps.len() >= 5, "{decision:?}");
        assert!(decision.steps.last().unwrap().witness.is_none());
        let r = decision.representation.unwrap();
        assert_eq!(r.argument.extent, 10);
        assert_eq!(r.writes[&40].offset, 8);
        let shapes: BTreeSet<_> = decision
            .steps
            .iter()
            .map(|s| (s.shared, s.extent, s.joined_writes.clone()))
            .collect();
        assert_eq!(
            shapes.len(),
            decision.steps.len(),
            "every witness must exclude the generating layout"
        );
        assert!(decision.steps.iter().any(|s| s
            .witness
            .as_ref()
            .is_some_and(|w| w.kind == FailureKind::CompleteAccess)));
    }

    #[test]
    fn the_witness_writer_changes_membership_without_preconstructing_other_writes() {
        let p = prepared();
        let opt = Optimize::new();
        let encoding = Encoding::build(&p, &opt);
        let witness = Counterexample {
            function: 1,
            base: 16,
            call: 90,
            observed_byte: 4,
            writer: Some(30),
            kind: FailureKind::WriteCorrespondence,
            machine_byte: 1,
            represented_byte: 0,
            index_value: None,
        };
        opt.assert(&encoding.learn(&witness).unwrap());
        assert_eq!(opt.check(&[]), z3::SatResult::Sat);
        let r = encoding.representation(&opt.get_model().unwrap()).unwrap();
        assert_eq!(r.writes[&30].object, r.argument.object);
        assert_ne!(r.writes[&20].object, r.argument.object);
        assert_ne!(r.writes[&40].object, r.argument.object);
        assert_eq!(r.argument.extent, 8);
    }

    #[test]
    fn observations_outside_the_grammar_do_not_poison_the_ordinary_type_solve() {
        let mut p = prepared();
        p.problem.other_roots.insert(24);
        let decision = final_select(p);
        assert!(decision.representation.is_none());
        assert_eq!(
            decision.reason,
            "no model satisfies the accumulated analysis witnesses"
        );
    }

    #[test]
    fn a_storage_witness_can_change_the_statement_without_rebuilding_the_object() {
        let mut p = prepared();
        p.problem.writes.retain(|w| w.node == 30);
        p.problem.observations = vec![(4, 4)];
        let object = StorageId::Frame(storage::ledger::ObjectId {
            function: 1,
            base: 16,
        });
        p.initial.argument = View {
            object,
            offset: 0,
            extent: 16,
        };
        p.candidate_writes.insert(
            30,
            vec![
                Some(View {
                    object,
                    offset: 0,
                    extent: 16,
                }),
                Some(View {
                    object,
                    offset: 4,
                    extent: 16,
                }),
            ],
        );
        let opt = Optimize::new();
        let bad = Bool::new_const("wrong_target");
        let good = Bool::new_const("correct_target");
        opt.assert(&Bool::pb_eq(&[(&bad, 1), (&good, 1)], 1));
        opt.assert_soft(&bad, 1, None);
        let mut encoding = Encoding::build(&p, &opt);
        encoding.bind_candidates(&HashMap::from([(30, vec![bad.clone(), good.clone()])]));
        // Check the retain-existing branch of the grammar. The only repair
        // available here is statement reselection, not object construction.
        opt.assert(&encoding.shared.not());
        assert_eq!(opt.check(&[]), z3::SatResult::Sat);
        let model = opt.get_model().unwrap();
        assert_eq!(model.eval(&bad, true).unwrap().as_bool(), Some(true));
        let clause = encoding.refine(&model).unwrap().unwrap();
        assert_eq!(model.eval(&clause, true).unwrap().as_bool(), Some(false));
        opt.assert(&clause);
        assert_eq!(opt.check(&[]), z3::SatResult::Sat);
        let model = opt.get_model().unwrap();
        assert_eq!(model.eval(&good, true).unwrap().as_bool(), Some(true));
        assert!(encoding.refine(&model).unwrap().is_none());
        let decision = encoding.finish(Some(&model), "checked");
        assert!(!decision.requires_replay);
        assert_eq!(decision.steps.len(), 2);
        assert!(decision.steps[0]
            .witness
            .as_ref()
            .is_some_and(|w| w.writer == Some(30)));
        assert_eq!(decision.representation.unwrap().writes[&30].offset, 4);
    }

    #[test]
    fn complete_read_footprints_generate_extent_refinements() {
        let mut p = prepared();
        p.problem.reads.push(Access {
            node: 50,
            offset: 25,
            width: 4,
            local: 14,
        });
        let decision = final_select(p);
        assert_eq!(decision.representation.unwrap().argument.extent, 13);
        assert!(decision.steps.iter().any(|s| s
            .witness
            .as_ref()
            .is_some_and(|w| w.kind == FailureKind::CompleteAccess && w.writer == Some(50))));
    }

    #[test]
    fn a_witness_from_another_object_cannot_constrain_this_layout() {
        let p = prepared();
        let opt = Optimize::new();
        let encoding = Encoding::build(&p, &opt);
        let witness = Counterexample {
            function: 2,
            base: 16,
            call: 90,
            observed_byte: 7,
            writer: None,
            kind: FailureKind::Extent,
            machine_byte: 0,
            represented_byte: 0,
            index_value: None,
        };
        assert!(encoding.learn(&witness).is_none());
    }

    #[test]
    fn paired_call_views_do_not_invent_cross_product_accesses() {
        use crate::x86::op::Operation;
        use std::sync::Arc;
        use storage::symbolic::{Expr, Index};
        let mut p = prepared();
        p.problem.writes.clear();
        p.initial.writes.clear();
        p.problem.observations.clear();
        let index = |n| Index {
            expression: Arc::new(Expr::Apply(Operation::Olongconst(n), 64, vec![])),
            scale: 1,
            maximum_delta: n,
        };
        p.problem.views = vec![
            storage::ObservedView {
                call: 91,
                index: index(7),
                observations: vec![(0, 1)],
            },
            storage::ObservedView {
                call: 92,
                index: index(0),
                observations: vec![(9, 1)],
            },
        ];
        let decision = final_select(p);
        assert_eq!(decision.representation.unwrap().argument.extent, 10);
        assert!(decision
            .steps
            .iter()
            .any(|s| s.witness.as_ref().is_some_and(|w| w.call == 92)));
    }

    #[test]
    fn an_adequate_existing_object_does_not_request_rederivation() {
        let mut p = prepared();
        let object = StorageId::Frame(storage::ledger::ObjectId {
            function: 1,
            base: 16,
        });
        p.initial.argument = View {
            object,
            offset: 0,
            extent: 16,
        };
        p.problem.minimum_extent = 16;
        p.initial.writes = p
            .problem
            .writes
            .iter()
            .map(|w| {
                (
                    w.node,
                    View {
                        object,
                        offset: w.offset - 16,
                        extent: 16,
                    },
                )
            })
            .collect();
        let decision = final_select(p);
        assert!(!decision.requires_replay);
        assert_eq!(decision.steps.len(), 1);
        assert!(decision.steps[0].witness.is_none());
        assert!(requests(&[decision]).is_empty());
    }
}
