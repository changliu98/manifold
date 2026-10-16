//! Candidate value/definedness/effect obligations as a selection module.
use crate::decompile::passes::clight_select::select::ProgramSelectionState;
use crate::decompile::passes::clight_select::{candtype::{CandType, Sign}, solvers::memory_theory, solvers::producer_values, query::FunctionData, solvers::word_views};
use crate::decompile::passes::clight_select::syntax::c_types::{anchor_index, TypeDt};
use crate::decompile::passes::clight_select::syntax::constraints::ConstraintSink;
use crate::decompile::passes::clight_select::syntax::{Candidate, CandidateAnalysis, FunctionContext, PreparedAnalysis};
use crate::decompile::elevator::DecompileDB;
use crate::x86::types::{Node, RTLReg};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use z3::ast::{Bool, Dynamic};

// The explicit legacy profile remains the fallback for unrefined declarations.
pub(super) fn integer_declarations(
    func: &FunctionData,
) -> HashMap<RTLReg, crate::decompile::passes::c_pass::types::CType> {
    use crate::decompile::passes::c_pass::convert::from_relations::convert_param_type_from_param;
    use crate::decompile::passes::c_pass::helpers::candtype_to_ctype;
    use crate::decompile::passes::c_pass::types::CType;

    let mut declarations = HashMap::new();
    // Type evidence promotes observed singleton values into the explicit
    // domain. Unmanaged emitter-inferred locals remain unknown here.
    for (&reg, cands) in &func.var_type_candidates {
        let rendered = CandType::I64(Sign::Signed);
        let candidate = anchor_index(cands, rendered, false)
            .map(|i| cands[i])
            .unwrap_or(rendered);
        declarations.insert(reg, candtype_to_ctype(candidate, func.data_model));
    }
    for (&reg, param) in func.param_regs.iter().zip(&func.param_types) {
        let ty = convert_param_type_from_param(param, func.data_model);
        // The emitter refines its default long parameters from local types;
        // explicitly typed interface parameters keep their committed type.
        if ty != CType::long() || !declarations.contains_key(&reg) {
            declarations.insert(reg, ty);
        }
    }
    if let Some(graph) = crate::decompile::passes::clight_select::syntax::type_evidence::GRAPH.get(&func.analysis_facts) {
        declarations.retain(|reg, _| !graph.fixed_storage.contains(reg));
    }
    declarations
}

// Validate that profile, then guard every result by the classes of ALL input
// and output declarations it used. A pointer/float model is never excluded by
// an integer counterexample. Proven siblings must exist in the chosen world.
fn semantic_candidate_conditions(
    t: &TypeDt,
    tyvar: &HashMap<RTLReg, Dynamic>,
    concrete: &crate::decompile::passes::clight_select::syntax::declarations::Declarations,
    func: &FunctionData,
    nodes: &[Node],
    selections: &HashMap<Node, Vec<Bool>>,
    worlds: &[u8],
    world_vars: &HashMap<u8, Bool>,
    by_node: crate::decompile::passes::clight_select::solvers::obligations::Obligations<'_>,
) -> (BTreeMap<(Node, usize), Bool>, Vec<Bool>) {
    use crate::decompile::passes::clight_select::solvers::obligations::{Validator, Verdict};
    let declarations = integer_declarations(func);
    let validator = Validator::new();
    let mut out = BTreeMap::new();
    let mut preferences = Vec::new();
    let mut counts = [0usize; 4];
    let mut effect_counts: BTreeMap<&'static str, [usize; 4]> = BTreeMap::new();
    let mut gaps = 0usize;
    for node in nodes {
        for obligation in by_node.0.get(node).into_iter().flatten() {
            if !obligation.checks_legacy() {
                continue;
            }
            let effect = obligation.family();
            let candidates = &func.node_statements[node];
            let checks: Vec<_> = candidates
                .iter()
                .map(|stmt| {
                    let check = validator.check(obligation.as_ref(), stmt, &declarations, func);
                    let outcome = match check.verdict {
                        Verdict::Equivalent => 0,
                        Verdict::Refuted => 1,
                        Verdict::Unsupported => 2,
                        Verdict::Unknown => 3,
                    };
                    counts[outcome] += 1;
                    effect_counts.entry(effect).or_default()[outcome] += 1;
                    check
                })
                .collect();
            if checks.iter().all(|check| check.verdict == Verdict::Refuted) {
                gaps += 1;
            }
            let guard = |regs: &BTreeSet<RTLReg>,
                         profile: &HashMap<
                RTLReg,
                crate::decompile::passes::c_pass::types::CType,
            >| {
                Bool::and(
                    &regs
                        .iter()
                        .filter_map(|reg| {
                            tyvar.get(reg).map(|ty| {
                                // render_type maps both int and bare struct models to the
                                // integer carrier. Guard the emitted declaration, otherwise
                                // Optimize can evade a veto with struct and still emit int.
                                let class = Bool::and(&[t.is_ptr(ty).not(), t.is_float(ty).not()]);
                                if !concrete.0.contains_key(reg) {
                                    return class;
                                }
                                let exact = concrete.guard(
                                    *reg,
                                    profile.get(reg) == declarations.get(reg),
                                    |candidate| {
                                        profile.get(reg) == Some(&candidate.to_c(func.data_model))
                                    },
                                );
                                Bool::and(&[class, exact])
                            })
                        })
                        .collect::<Vec<_>>(),
                )
            };
            // A hard veto is conditional on the declaration profile. Give an
            // actually validated choice a small preference as well: otherwise a
            // syntactic tie can move a declaration into an unchecked pointer
            // profile solely to preserve the refuted statement's rank-0 prior.
            // This is a coverage preference, not proof about an unchecked profile.
            if checks.iter().any(|check| check.verdict == Verdict::Refuted) {
                if let Some(vars) = selections.get(node) {
                    let proved: Vec<Bool> = checks
                        .iter()
                        .enumerate()
                        .filter_map(|(ci, check)| {
                            (check.verdict == Verdict::Equivalent).then(|| {
                                Bool::and(&[
                                    vars[ci].clone(),
                                    guard(&check.registers, &declarations),
                                ])
                            })
                        })
                        .collect();
                    if !proved.is_empty() {
                        preferences.push(Bool::or(&proved));
                    }
                }
            }
            for (ci, check) in checks.iter().enumerate() {
                if check.verdict != Verdict::Refuted {
                    continue;
                }
                if matches!(
                    check.witness,
                    Some(crate::decompile::passes::clight_select::solvers::obligations::Witness::Representation { .. })
                ) {
                    // This result cast cannot express the native word under
                    // the decoder's input relation, for ANY C declaration
                    // profile. No address/lifetime equivalence is inferred.
                    out.insert((*node, ci), Bool::from_bool(false));
                    continue;
                }
                let witnesses: Vec<Bool> = checks
                    .iter()
                    .enumerate()
                    .filter_map(|(wi, witness)| {
                        if witness.verdict != Verdict::Equivalent {
                            return None;
                        }
                        let masks = func
                            .candidate_structure_worlds
                            .get(node)
                            .and_then(|m| m.get(wi));
                        let active: Vec<Bool> = worlds
                            .iter()
                            .filter(|world| masks.map_or(true, |m| m.contains(world)))
                            .map(|world| {
                                world_vars
                                    .get(world)
                                    .cloned()
                                    .unwrap_or_else(|| Bool::from_bool(true))
                            })
                            .collect();
                        Some(Bool::and(&[
                            guard(&witness.registers, &declarations),
                            Bool::or(&active),
                        ]))
                    })
                    .collect();
                if !witnesses.is_empty() {
                    let condition =
                        Bool::and(&[guard(&check.registers, &declarations), Bool::or(&witnesses)])
                            .not();
                    out.entry((*node, ci))
                        .and_modify(|old: &mut Bool| {
                            *old = Bool::and(&[old.clone(), condition.clone()]);
                        })
                        .or_insert(condition);
                }
            }
            // Concrete declarations are checked against the selected model
            // by the shared refinement session, not an eager cross product.
        }
    }
    if counts[0] + counts[1] > 0 {
        eprintln!("[selection-obligations] fn={:#x} equivalent={} refuted={} unsupported={} unknown={} guarded-vetoes={} gaps={}",
            func.address, counts[0], counts[1], counts[2], counts[3], out.len(), gaps);
        if !func.storage_writes.is_empty() || !func.storage_reads.is_empty() {
            eprintln!("[memory-obligations] fn={:#x} candidate-checks=[equivalent,refuted,unsupported,unknown] targets={:?} values={:?} reads={:?}",
                func.address, effect_counts.get("store-target").unwrap_or(&[0; 4]), effect_counts.get("store-value").unwrap_or(&[0; 4]), effect_counts.get("load-value").unwrap_or(&[0; 4]));
        }
    }
    (out, preferences)
}

pub(crate) struct Semantics;
impl crate::decompile::passes::clight_select::solvers::Solver for Semantics {
    fn name(&self) -> &'static str {
        "value-effects"
    }
    fn reads(&self) -> &'static [&'static str] {
        static READS: std::sync::LazyLock<Vec<&'static str>> = std::sync::LazyLock::new(|| {
            let mut reads = producer_values::INPUTS.to_vec();
            reads.extend_from_slice(&memory_theory::INPUTS);
            reads.extend_from_slice(crate::decompile::passes::clight_select::solvers::transfers::INPUTS);
            reads.extend_from_slice(crate::decompile::passes::clight_select::solvers::observations::INPUTS);
            reads.sort_unstable();
            reads.dedup();
            reads
        });
        &READS
    }
    fn writes(&self) -> &'static [&'static str] {
        &[
            "semantic_storage_obligation",
            "semantic_storage_selected_target",
        ]
    }
    fn prepare(
        &self,
        db: &DecompileDB,
        functions: &mut [FunctionData],
    ) -> Option<Box<dyn PreparedAnalysis>> {
        memory_theory::collect(db, functions);
        crate::decompile::passes::clight_select::solvers::observations::collect(db, functions);
        crate::decompile::passes::clight_select::solvers::transfers::collect(db, functions);
        for function in functions.iter_mut() {
            crate::decompile::passes::clight_select::solvers::transfers::project_frame_views(function);
        }
        producer_values::collect(db, functions);
        for function in functions {
            word_views::extend_candidates(function);
        }
        Some(Box::new(Semantics))
    }
    fn obligations<'a>(
        &self,
        function: &'a FunctionData,
        out: &mut crate::decompile::passes::clight_select::solvers::obligations::Obligations<'a>,
    ) {
        use crate::decompile::passes::clight_select::solvers::obligations::{
            CopyTransport, IntegerAt, LoadTransport, ReadValue, SwitchInput, WriteTarget,
            WriteValue,
        };
        // Nodes are visited in sorted order by the shared compiler. Preserve
        // contract order within each node and independent verifier quotas.
        for (&node, inst) in &function.integer_anchors {
            out.push(node, IntegerAt(node, inst));
            if matches!(inst, crate::x86::types::RTLInst::Icond(..)) {
                out.push(node, SwitchInput(node, inst));
            }
        }
        for contract in &function.storage_writes {
            out.push(contract.node, WriteTarget(contract));
            if let Some(inst) = function.memory_anchors.get(&contract.node) {
                out.push(contract.node, WriteValue(inst, contract));
            }
        }
        for contract in &function.storage_reads {
            out.push(contract.node, ReadValue(contract));
        }
        for (&node, load) in crate::decompile::passes::clight_select::solvers::transfers::LOADS
            .get(&function.analysis_facts)
            .into_iter()
            .flatten()
        {
            out.push(node, LoadTransport(load));
        }
        for (&node, copy) in crate::decompile::passes::clight_select::solvers::transfers::COPIES
            .get(&function.analysis_facts)
            .into_iter()
            .flatten()
        {
            out.push(node, CopyTransport(copy));
        }
    }
}
impl PreparedAnalysis for Semantics {
    fn publish(
        self: Box<Self>,
        db: &mut DecompileDB,
        functions: &[FunctionData],
        selection: &ProgramSelectionState,
    ) {
        memory_theory::record_selection(db, functions, selection);
    }
}
struct SemanticConditions {
    // Ordered for a deterministic Z3 release order (see integer_semantics Eval).
    conditions: BTreeMap<(Node, usize), Bool>,
    preferences: Vec<Bool>,
    repair_bound: usize,
}
impl CandidateAnalysis for SemanticConditions {
    fn prior_count(&self) -> usize {
        self.preferences.len() + self.repair_bound
    }
    fn constrain_function(&self, _cx: &FunctionContext<'_>, sink: &ConstraintSink<'_>) {
        for preference in &self.preferences {
            sink.assert_soft_tagged(None, preference, 1, "semantic_obligations");
        }
    }
    fn constrain_candidate(
        &self,
        _cx: &FunctionContext<'_>,
        candidate: &Candidate<'_>,
        sink: &ConstraintSink<'_>,
    ) {
        if let Some(condition) = self.conditions.get(&(candidate.node, candidate.index)) {
            sink.assert_structural(candidate.selected, condition);
        }
    }
}

pub(crate) fn compile(
    cx: &FunctionContext<'_>,
    obligations: crate::decompile::passes::clight_select::solvers::obligations::Obligations<'_>,
) -> Box<dyn CandidateAnalysis> {
    let (conditions, preferences) = semantic_candidate_conditions(
        cx.types,
        cx.declarations,
        cx.concrete_declarations,
        cx.function,
        cx.nodes,
        cx.selections,
        cx.worlds,
        cx.world_variables,
        obligations,
    );
    Box::new(SemanticConditions {
        conditions,
        preferences,
        // Refinement may add at most one proof-backed repair preference per
        // node. Reserve its weight before establishing C's dominant stratum.
        repair_bound: if cx.concrete_declarations.0.is_empty() {
            0
        } else {
            cx.nodes.len()
        },
    })
}
