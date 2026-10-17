//! Mandatory accounting for the memory-flag-select effect family.
//!
//! This is a scoped contract, not a whole-function proof. Opaque or missing
//! carriers cannot become successful executable output via solver fallback.
use crate::decompile::effects::flags::FlagSelect;
use crate::decompile::effects::{self, ArtifactId, EffectId, Outcome, Receipt, Stage};
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::clight_select::syntax::constraints::ConstraintSink;
use crate::decompile::passes::clight_select::syntax::{
    ArtifactKey, Candidate, CandidateAnalysis, FunctionContext, PreparedAnalysis,
};
use crate::decompile::passes::clight_select::{
    query::FunctionData,
    select::ProgramSelectionState,
    solvers::integer_semantics::Validator,
    solvers::obligations::{Check, Verdict},
};
use crate::mreg::Mreg;
use crate::x86::{
    op::{Addressing, Operation},
    types::*,
};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use z3::ast::Bool;

#[derive(Clone, Debug)]
struct Problem {
    node: Node,
    spec: FlagSelect,
    inst: Option<RTLInst>,
    captured: bool,
    ordered: bool,
    scalar_views: BTreeSet<RTLReg>,
    global_view: Option<Ident>,
}
#[derive(Clone, Debug)]
struct Facts {
    epoch: u32,
    problems: Vec<Problem>,
}
const FACTS: ArtifactKey<Facts> = ArtifactKey::projected("effect-completeness", |facts, plan| {
    let mut result = facts.clone();
    for problem in &mut result.problems {
        problem.inst = problem
            .inst
            .as_ref()
            .map(|inst| plan.native(problem.node, inst));
        // Scalar capture views describe reads at the capture, not the later
        // flag-select consumer. Their reaching binding may differ.
        problem.scalar_views = problem
            .scalar_views
            .iter()
            .map(|reg| plan.read(problem.spec.capture, *reg))
            .collect();
    }
    result
});

pub(super) fn has_contracts(function: &FunctionData) -> bool {
    FACTS
        .get(&function.analysis_facts)
        .is_some_and(|facts| !facts.problems.is_empty())
}

fn value_inputs(expr: &ClightExpr, out: &mut BTreeSet<RTLReg>) {
    match expr {
        ClightExpr::Etempvar(reg, _) => {
            out.insert(*reg as RTLReg);
        }
        ClightExpr::Ecast(e, _) | ClightExpr::Eunop(_, e, _) => value_inputs(e, out),
        ClightExpr::Ebinop(_, a, b, _) => {
            value_inputs(a, out);
            value_inputs(b, out);
        }
        ClightExpr::Econdition(c, a, b, _) => {
            value_inputs(c, out);
            value_inputs(a, out);
            value_inputs(b, out);
        }
        _ => {}
    }
}
fn primitive(stmt: &ClightStmt) -> &ClightStmt {
    match stmt {
        (ClightStmt::Slabel(_, s) | ClightStmt::Seffect(_, s)) => primitive(s),
        ClightStmt::Ssequence(s) if s.len() == 1 => primitive(&s[0]),
        _ => stmt,
    }
}
fn carries_value(inst: &RTLInst, stmt: &ClightStmt) -> bool {
    let RTLInst::Iop(Operation::Oflagselect(_), args, dst) = inst else {
        return false;
    };
    let rhs = match primitive(stmt) {
        ClightStmt::Sset(id, rhs) if *id as RTLReg == *dst => rhs,
        ClightStmt::Sreturn(Some(rhs)) => rhs,
        _ => return false,
    };
    let mut inputs = BTreeSet::new();
    value_inputs(rhs, &mut inputs);
    args.iter().all(|r| inputs.contains(r))
}
fn read_count(expr: &ClightExpr) -> usize {
    match expr {
        ClightExpr::Ederef(_, _) | ClightExpr::Efield(_, _, _) => 1,
        ClightExpr::Ecast(e, _) | ClightExpr::Eunop(_, e, _) => read_count(e),
        ClightExpr::Ebinop(_, a, b, _) => read_count(a) + read_count(b),
        ClightExpr::Econdition(c, a, b, _) => read_count(c) + read_count(a) + read_count(b),
        _ => 0,
    }
}
fn carries_read(
    inst: &RTLInst,
    stmt: &ClightStmt,
    scalar_views: &BTreeSet<RTLReg>,
    global_view: Option<Ident>,
) -> bool {
    let RTLInst::Iop(Operation::Oflagselect(spec), args, _) = inst else {
        return false;
    };
    let scalar = |mut rhs: &ClightExpr| {
        while let ClightExpr::Ecast(inner, _) = rhs {
            rhs = inner;
        }
        match rhs {
            ClightExpr::Etempvar(reg, _) => scalar_views.contains(&(*reg as RTLReg)),
            // A named global is a read, not an address constant. Match the
            // exact finalized load's symbol and chunk, never an arbitrary var.
            ClightExpr::Evar(id, ty) if global_view == Some(*id) => {
                let bytes = match ty {
                    ClightType::Tint(ClightIntSize::I8 | ClightIntSize::IBool, _, _) => 1,
                    ClightType::Tint(ClightIntSize::I16, _, _) => 2,
                    ClightType::Tint(ClightIntSize::I32, _, _) => 4,
                    ClightType::Tlong(..) | ClightType::Tpointer(..) => 8,
                    _ => 0,
                };
                bytes == spec.width
            }
            _ => false,
        }
    };
    matches!(primitive(stmt),ClightStmt::Sset(id,rhs) if args.get(2)==Some(&(*id as RTLReg)) && (read_count(rhs)==1 || scalar(rhs)))
}
/// The temporaries a frame-slot capture at `offset` is read through: the read's point-local
/// stack_var and, for an address-escaped slot, rtl_pass's single slot_escaped_canonical local,
/// the one cshminor reads that slot through. Each comes with its xtl_canonical image.
fn frame_capture_views(
    db: &DecompileDB,
    function: Address,
    capture: Node,
    offset: i64,
) -> BTreeSet<RTLReg> {
    let point = db
        .rel_iter::<(Address, Node, i64, RTLReg)>("stack_var")
        .filter(|&&(f, n, o, _)| f == function && n == capture && o == offset)
        .map(|&(.., reg)| reg);
    let escaped = db
        .rel_iter::<(Address, i64, RTLReg)>("slot_escaped_canonical")
        .filter(|&&(f, o, _)| f == function && o == offset)
        .map(|&(.., reg)| reg);
    let roots: BTreeSet<RTLReg> = point.chain(escaped).collect();
    let mut views = roots.clone();
    views.extend(
        db.rel_iter::<(RTLReg, RTLReg)>("xtl_canonical")
            .filter(|(from, _)| roots.contains(from))
            .map(|&(_, to)| to),
    );
    views
}
fn opaque(stmt: &ClightStmt) -> bool {
    matches!(primitive(stmt),ClightStmt::Scall(_,ClightExpr::EvarSymbol(name,_),_) if effects::is_opaque(name))
}
fn checked_value(
    inst: &RTLInst,
    stmt: &ClightStmt,
    function: &FunctionData,
    validator: &Validator,
) -> Check {
    let mut declarations =
        crate::decompile::passes::clight_select::solvers::semantics::integer_declarations(function);
    if let (RTLInst::Iop(_, _, dst), ClightStmt::Sreturn(Some(rhs))) = (inst, primitive(stmt)) {
        declarations.insert(
            *dst,
            crate::decompile::passes::c_pass::convert::from_relations::convert_clight_type(
                &function.return_type,
                function.data_model,
            ),
        );
        return validator.check(
            inst,
            &ClightStmt::Sset(*dst as Ident, rhs.clone()),
            &declarations,
            function.data_model,
        );
    }
    validator.check(inst, stmt, &declarations, function.data_model)
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct SelectedContract {
    pub function: Address,
    pub node: Node,
    pub spec: FlagSelect,
    pub epoch: u32,
    pub captured: bool,
    pub ordered: bool,
    pub select_present: bool,
    pub capture_present: bool,
    pub refuted: bool,
    pub select_alternative: Option<usize>,
    pub capture_alternative: Option<usize>,
}

impl SelectedContract {
    pub(crate) fn site(&self, node: Node) -> effects::EffectSite {
        effects::EffectSite {
            function: self.function,
            node,
            epoch: self.epoch,
            alternative: if node == self.node {
                self.select_alternative
            } else {
                self.capture_alternative
            }
            .unwrap_or(0),
        }
    }
}

pub(crate) struct Completeness;
fn audit_emitted(db: &mut crate::decompile::elevator::DecompileDB) {
    use crate::decompile::passes::c_pass::types::{CStmt, TopLevelDecl};
    use std::collections::BTreeMap;
    let contracts: Vec<_> = db
        .rel_iter::<SelectedContract>("effect_selected_contract")
        .cloned()
        .collect();
    if contracts.is_empty() {
        return;
    }
    let mut seen: BTreeMap<(u64, u64, u32, usize), Vec<CStmt>> = BTreeMap::new();
    if let Some(tu) = &db.cast_optimized_translation_unit {
        for declaration in &tu.decls {
            if let TopLevelDecl::FuncDef(function) = declaration {
                for (site, body) in effects::c::occurrences(&function.body) {
                    seen.entry((site.function, site.node, site.epoch, site.alternative))
                        .or_default()
                        .push(body);
                }
            }
        }
    }
    let previous: Vec<_> = db
        .rel_iter::<(u64, Receipt)>("effect_receipt")
        .cloned()
        .collect();
    let mut receipts = previous.clone();
    for contract in &contracts {
        let mut valid = contract.epoch == db.effect_epoch
            && previous.iter().any(|(f, r)| {
                *f == contract.function
                    && r.artifact.node == contract.node
                    && r.effect == contract.spec.read_effect()
                    && r.artifact.stage == Stage::Selection
                    && Some(r.artifact.alternative) == contract.select_alternative
                    && r.artifact.epoch == contract.epoch
                    && r.outcome == Outcome::Carried
            });
        for (node, alternative) in [
            (contract.node, contract.select_alternative),
            (contract.spec.capture, contract.capture_alternative),
        ] {
            let bodies = seen.get(&(
                contract.function,
                node,
                contract.epoch,
                alternative.unwrap_or(0),
            ));
            let retained = alternative.is_some()
                && bodies.is_some_and(|b| b.len() == 1 && !matches!(b[0], CStmt::Empty));
            if !retained {
                eprintln!("[effect-emission] function={:#x} node={:#x} epoch={} alternative={:?} occurrences={}",
                    contract.function,node,contract.epoch,alternative,bodies.map_or(0,Vec::len));
            }
            valid &= retained;
        }
        receipts.push((
            contract.function,
            Receipt {
                effect: contract.spec.read_effect(),
                artifact: ArtifactId {
                    epoch: contract.epoch,
                    stage: Stage::Emission,
                    node: contract.node,
                    alternative: contract.select_alternative.unwrap_or(0),
                },
                outcome: if valid {
                    Outcome::Carried
                } else {
                    Outcome::Missing
                },
                reason: if valid {
                    "scoped effect occurrences retained through C emission"
                } else {
                    "scoped effect has no unique admitted emitted occurrence"
                },
            },
        ));
    }
    let gaps = receipts
        .iter()
        .filter(|(_, r)| r.artifact.stage == Stage::Emission && r.outcome != Outcome::Carried)
        .count();
    eprintln!(
        "[effect-emission] scope=memory-flag-select bundles={} unresolved={}",
        contracts.len(),
        gaps
    );
    db.rel_set(
        "effect_receipt",
        receipts.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
}

impl crate::decompile::passes::clight_select::solvers::Solver for Completeness {
    fn name(&self) -> &'static str {
        "effect-completeness"
    }
    fn audit_emission(&self, db: &mut DecompileDB) {
        audit_emitted(db);
    }
    fn reads(&self) -> &'static [&'static str] {
        static INPUTS: std::sync::LazyLock<Vec<&'static str>> = std::sync::LazyLock::new(|| {
            let mut inputs = vec![
                "effect_flag_select",
                "effect_capture",
                "effect_capture_address",
                "effect_capture_value",
                "rtl_inst",
                "rtl_succ",
                "rtl_function_entry",
                "instr_in_function",
                "effect_selected_contract",
                "stack_var",
                "slot_escaped_canonical",
                "xtl_canonical",
            ];
            inputs.extend_from_slice(effects::capture::INPUTS);
            inputs.sort_unstable();
            inputs.dedup();
            inputs
        });
        &INPUTS
    }
    fn writes(&self) -> &'static [&'static str] {
        &["effect_selected_contract", "effect_receipt"]
    }
    fn retain_origins(
        &self,
        function: &FunctionData,
        indices: &HashMap<Node, Option<usize>>,
        statements: &mut HashMap<Node, ClightStmt>,
    ) {
        let Some(facts) = FACTS.get(&function.analysis_facts) else {
            return;
        };
        let nodes: BTreeSet<_> = facts
            .problems
            .iter()
            .flat_map(|p| [p.node, p.spec.capture])
            .collect();
        for node in nodes {
            if let Some(stmt) = statements.get_mut(&node) {
                // Identity belongs to the selected candidate, including its
                // labels/singleton sequences, not a particular syntax shape.
                *stmt = ClightStmt::Seffect(
                    effects::EffectSite {
                        function: function.address,
                        node,
                        epoch: facts.epoch,
                        alternative: indices.get(&node).copied().flatten().unwrap_or(0),
                    },
                    Box::new(stmt.clone()),
                );
            }
        }
    }
    fn prepare(
        &self,
        db: &DecompileDB,
        functions: &mut [FunctionData],
    ) -> Option<Box<dyn PreparedAnalysis>> {
        let mut instructions: BTreeMap<Node, Option<RTLInst>> = BTreeMap::new();
        for (node, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
            instructions
                .entry(*node)
                .and_modify(|old| {
                    if old.as_ref() != Some(inst) {
                        *old = None;
                    }
                })
                .or_insert(Some(inst.clone()));
        }
        let mut ownership: BTreeMap<Node, BTreeSet<Address>> = BTreeMap::new();
        for &(node, function) in db.rel_iter::<(Node, Address)>("instr_in_function") {
            ownership.entry(node).or_default().insert(function);
        }
        let entries: BTreeMap<_, _> = db
            .rel_iter::<(Address, Node)>("rtl_function_entry")
            .copied()
            .collect();
        let roots: Vec<_> = db
            .rel_iter::<(Node, FlagSelect, Mreg, Mreg)>("effect_flag_select")
            .copied()
            .collect();
        for function in functions {
            let mut problems = Vec::new();
            for &(node, spec, _, _) in &roots {
                if !ownership
                    .get(&node)
                    .is_some_and(|owners| owners.contains(&function.address))
                {
                    continue;
                }
                let inst = instructions.get(&node).cloned().flatten();
                let loaded = match &inst {
                    Some(RTLInst::Iop(Operation::Oflagselect(actual), args, _))
                        if *actual == spec && args.len() == 3 =>
                    {
                        Some(args[2])
                    }
                    _ => None,
                };
                let captured = matches!(instructions.get(&spec.capture), Some(Some(inst @ RTLInst::Iload(_, _, _, dst)))
                    if Some(*dst) == loaded && effects::capture::matches(db,function.address,spec.capture,spec.width,inst));
                let scalar_views = match instructions.get(&spec.capture) {
                    Some(Some(RTLInst::Iload(_, Addressing::Ainstack(offset), _, _))) => {
                        frame_capture_views(db, function.address, spec.capture, *offset)
                    }
                    _ => BTreeSet::new(),
                };
                let global_view = match instructions.get(&spec.capture) {
                    Some(Some(RTLInst::Iload(_, Addressing::Aglobal(symbol, 0), args, _)))
                        if args.is_empty() =>
                    {
                        Some(*symbol)
                    }
                    _ => None,
                };
                problems.push(Problem {
                    node,
                    spec,
                    inst,
                    captured,
                    ordered: false,
                    scalar_views,
                    global_view,
                });
            }
            if problems.is_empty() {
                continue;
            }
            problems.sort_by_key(|p| (p.node, p.spec));
            problems.dedup_by_key(|p| (p.node, p.spec));
            let captures = problems
                .iter()
                .filter(|p| p.captured)
                .map(|p| p.spec.capture)
                .collect();
            let edges: Vec<_> = db
                .rel_iter::<(Node, Node)>("rtl_succ")
                .copied()
                .filter(|(a, b)| {
                    ownership
                        .get(a)
                        .is_some_and(|o| o.contains(&function.address))
                        && ownership
                            .get(b)
                            .is_some_and(|o| o.contains(&function.address))
                })
                .collect();
            let before = entries
                .get(&function.address)
                .map(|&entry| {
                    effects::flow::must_captures((function.address, entry), &edges, &captures)
                })
                .unwrap_or_default();
            for problem in &mut problems {
                problem.ordered = before
                    .get(&problem.node)
                    .is_some_and(|state| state.0.contains(&problem.spec.capture));
            }
            FACTS.insert(
                &mut function.analysis_facts,
                Facts {
                    epoch: db.effect_epoch,
                    problems,
                },
            );
        }
        Some(Box::new(Completeness))
    }
    fn extend(&self, cx: &FunctionContext<'_>) -> Option<Box<dyn CandidateAnalysis>> {
        let facts = FACTS.get(&cx.function.analysis_facts)?;
        let validator = Validator::new();
        let mut vetoes = BTreeMap::new();
        for p in &facts.problems {
            if let Some(candidates) = cx.function.node_statements.get(&p.node) {
                for (index, stmt) in candidates.iter().enumerate() {
                    let Some(inst) = &p.inst else {
                        continue;
                    };
                    let check = checked_value(inst, stmt, cx.function, &validator);
                    if !carries_value(inst, stmt)
                        && check.verdict != Verdict::Equivalent
                        && !opaque(stmt)
                    {
                        vetoes.insert((p.node, index), Bool::from_bool(false));
                        continue;
                    }
                    if check.verdict == Verdict::Refuted {
                        let profile: Vec<_> = check
                            .registers
                            .iter()
                            .filter_map(|r| cx.declarations.get(r))
                            .map(|ty| {
                                Bool::and(&[cx.types.is_ptr(ty).not(), cx.types.is_float(ty).not()])
                            })
                            .collect();
                        vetoes.insert((p.node, index), Bool::and(&profile).not());
                    }
                }
            }
            if let (Some(inst), Some(candidates)) =
                (&p.inst, cx.function.node_statements.get(&p.spec.capture))
            {
                for (index, stmt) in candidates.iter().enumerate() {
                    if !carries_read(inst, stmt, &p.scalar_views, p.global_view) && !opaque(stmt) {
                        vetoes.insert((p.spec.capture, index), Bool::from_bool(false));
                    }
                }
            }
        }
        Some(Box::new(Rules(vetoes)))
    }
    fn audit_selection(&self, db: &mut DecompileDB) {
        let mut receipts = Vec::new();
        for contract in db.rel_iter::<SelectedContract>("effect_selected_contract") {
            let selected = db
                .clight_selected_functions
                .iter()
                .find(|f| f.address == contract.function);
            let present = selected.is_some_and(|f| {
                f.selected_candidate_nodes.contains(&contract.node)
                    && f.selected_candidate_nodes.contains(&contract.spec.capture)
            });
            let machine = ArtifactId {
                epoch: contract.epoch,
                stage: Stage::Machine,
                node: contract.spec.capture,
                alternative: 0,
            };
            let capture = ArtifactId {
                epoch: contract.epoch,
                stage: Stage::Selection,
                node: contract.spec.capture,
                alternative: contract.capture_alternative.unwrap_or(0),
            };
            let consumer = ArtifactId {
                epoch: contract.epoch,
                stage: Stage::Selection,
                node: contract.node,
                alternative: contract.select_alternative.unwrap_or(0),
            };
            let transfer = effects::contracts::Transfer {
                effect: contract.spec.read_effect(),
                inputs: vec![machine],
                outputs: vec![capture, consumer],
            };
            let selected_artifacts = if present {
                BTreeSet::from([capture, consumer])
            } else {
                BTreeSet::new()
            };
            let machine_artifacts: BTreeSet<_> = db
                .rel_iter::<(Node, Symbol, usize)>("effect_capture")
                .filter_map(|(node, _, width)| {
                    (*node == contract.spec.capture && *width == contract.spec.width)
                        .then_some(machine)
                })
                .collect();
            let transfer_present = effects::contracts::check_transfer(
                &transfer,
                &machine_artifacts,
                &selected_artifacts,
                db.effect_epoch,
            ) == Outcome::Carried;
            let outcome = if contract.refuted {
                Outcome::Refuted
            } else if contract.epoch != db.effect_epoch {
                Outcome::Missing
            } else if !contract.captured
                || !contract.capture_present
                || !contract.select_present
                || !transfer_present
            {
                Outcome::Missing
            } else if !contract.ordered {
                Outcome::Opaque
            } else {
                Outcome::Carried
            };
            if outcome != Outcome::Carried {
                eprintln!("[effect-completeness] function={:#x} consumer={:#x} capture={:#x} captured={} ordered={} select-present={} capture-present={} refuted={} transfer-present={}",
                    contract.function,contract.node,contract.spec.capture,contract.captured,contract.ordered,
                    contract.select_present,contract.capture_present,contract.refuted,transfer_present);
            }
            receipts.push((
                contract.function,
                Receipt {
                    effect: contract.spec.read_effect(),
                    artifact: consumer,
                    outcome,
                    reason: if outcome == Outcome::Carried {
                        "capture and consumer retained in the selected CFG"
                    } else {
                        "incomplete capture-to-consumer transfer"
                    },
                },
            ));
        }
        let missing = receipts
            .iter()
            .filter(|(_, r)| {
                matches!(
                    r.outcome,
                    Outcome::Missing | Outcome::Opaque | Outcome::Refuted
                )
            })
            .count();
        if !receipts.is_empty() {
            eprintln!(
                "[effect-completeness] scope=memory-flag-select bundles={} unresolved={}",
                receipts.len(),
                missing
            );
        }
        db.rel_set(
            "effect_receipt",
            receipts.into_iter().collect::<ascent::boxcar::Vec<_>>(),
        );
    }
}
struct Rules(BTreeMap<(Node, usize), Bool>);
#[cfg(test)]
mod read_tests {
    use crate::decompile::passes::clight_select::solvers::completeness::*;
    /// base32's proper_name_lite compares mbrtoc32's char32_t out-parameter in memory
    /// (`cmpl $0x7ff,0xc(%rsp); cmove`); once that slot's address escapes, cshminor reads it
    /// through the slot's canonical local, which must count as the capture's read.
    #[test]
    fn escaped_slot_capture_is_read_through_its_canonical_local() {
        let mut db = DecompileDB::default();
        db.rel_push("stack_var", (1_u64, 10_u64, 12_i64, 5_u64));
        db.rel_push("stack_var", (1_u64, 11_u64, 12_i64, 6_u64));
        db.rel_push("slot_escaped_canonical", (1_u64, 12_i64, 7_u64));
        db.rel_push("slot_escaped_canonical", (1_u64, 16_i64, 8_u64));
        db.rel_push("slot_escaped_canonical", (2_u64, 12_i64, 9_u64));
        db.rel_push("xtl_canonical", (7_u64, 17_u64));
        db.rel_push("xtl_canonical", (8_u64, 18_u64));
        assert_eq!(frame_capture_views(&db, 1, 10, 12), BTreeSet::from([5, 7, 17]));
        assert_eq!(frame_capture_views(&db, 1, 10, 4), BTreeSet::new());
    }
    #[test]
    fn effect_contract_and_candidates_share_binding_projection() {
        use crate::decompile::passes::clight_select::syntax::{
            bindings::BindingPlan, c_types::CTypes, Stack,
        };
        use crate::decompile::passes::clight_select::{
            candtype::{CandType, Sign},
            syntax::solve::solve_function_z3_with_stack,
        };
        use crate::decompile::passes::{clight_pass, cminor_pass};
        use std::sync::Arc;
        let spec = FlagSelect {
            capture: 10,
            producer: effects::flags::Producer::Compare,
            predicate: effects::flags::Predicate::Equal,
            width: 1,
            immediate: 0,
            result_bits: 64,
        };
        let inst = RTLInst::Iop(Operation::Oflagselect(spec), Arc::new(vec![1, 2, 3]), 4);
        let long = ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default());
        let expression = cminor_pass::csharp_expr_from_cminor(&CminorExpr::Eop(
            Operation::Oflagselect(spec),
            Arc::new(vec![1, 2, 3]),
        ))
        .unwrap();
        let types = (1..=5).map(|reg| (reg, long.clone())).collect();
        let selection = ClightStmt::Sset(
            4,
            clight_pass::clight_expr_from_csharp_with_types(&expression, &types, 8),
        );
        let capture = ClightStmt::Sset(3, ClightExpr::Etempvar(5, long));
        let plan = BindingPlan::from_test_events(
            [((20, 1), 11), ((20, 2), 12), ((20, 3), 13), ((10, 5), 15)],
            [((20, 4), 14), ((10, 3), 13)],
        );
        let mut f = FunctionData::new(
            1,
            "renamed_effect".into(),
            vec![],
            vec![],
            None,
            0,
            10,
            true,
        );
        FACTS.insert(
            &mut f.analysis_facts,
            Facts {
                epoch: 0,
                problems: vec![Problem {
                    node: 20,
                    spec,
                    inst: Some(inst.clone()),
                    captured: true,
                    ordered: true,
                    scalar_views: BTreeSet::from([5]),
                    global_view: None,
                }],
            },
        );
        let original = f.analysis_facts.clone();
        f.analysis_facts.project_bindings(&plan);
        f.node_statements
            .insert(10, vec![plan.statement(10, &capture)]);
        f.node_statements
            .insert(20, vec![plan.statement(20, &selection)]);
        for reg in 11..=15 {
            f.used_regs.insert(reg);
            f.var_types.insert(reg, CandType::I64(Sign::Unsigned));
            f.var_type_candidates
                .insert(reg, vec![CandType::I64(Sign::Unsigned)]);
        }
        let problem = &FACTS.get(&f.analysis_facts).unwrap().problems[0];
        assert!(!carries_value(&inst, &f.node_statements[&20][0]));
        assert!(carries_value(
            problem.inst.as_ref().unwrap(),
            &f.node_statements[&20][0]
        ));
        assert!(carries_read(
            problem.inst.as_ref().unwrap(),
            &f.node_statements[&10][0],
            &problem.scalar_views,
            None
        ));
        assert_eq!(
            FACTS.get(&original).unwrap().problems[0].inst.as_ref(),
            Some(&inst)
        );
        let out = solve_function_z3_with_stack(
            &f,
            &HashMap::new(),
            &[],
            &Stack::new(&[&Completeness], &[&CTypes]),
        )
        .unwrap();
        assert_eq!(out.0[&10], Some(0));
        assert_eq!(out.0[&20], Some(0));
        let mut state = ProgramSelectionState::default();
        for (node, choice) in out.0 {
            state.candidate_idx.insert((1, node), choice);
        }
        let mut db = DecompileDB::default();
        Box::new(Completeness).publish(&mut db, &[f], &state);
        let contracts: Vec<_> = db
            .rel_iter::<SelectedContract>("effect_selected_contract")
            .collect();
        assert_eq!(contracts.len(), 1);
        assert!(
            contracts[0].select_present && contracts[0].capture_present && !contracts[0].refuted
        );
    }

    #[test]
    fn global_read_requires_the_exact_symbol_and_width() {
        let spec = FlagSelect {
            capture: 10,
            producer: effects::flags::Producer::Compare,
            predicate: effects::flags::Predicate::Equal,
            width: 4,
            immediate: 0,
            result_bits: 64,
        };
        let inst = RTLInst::Iop(
            Operation::Oflagselect(spec),
            std::sync::Arc::new(vec![1, 2, 3]),
            4,
        );
        let ty = ClightType::Tint(
            ClightIntSize::I32,
            ClightSignedness::Signed,
            ClightAttr::default(),
        );
        let stmt = |symbol, ty| ClightStmt::Sset(3, ClightExpr::Evar(symbol, ty));
        assert!(carries_read(
            &inst,
            &stmt(100, ty.clone()),
            &BTreeSet::new(),
            Some(100)
        ));
        assert!(!carries_read(
            &inst,
            &stmt(101, ty),
            &BTreeSet::new(),
            Some(100)
        ));
        assert!(!carries_read(
            &inst,
            &stmt(
                100,
                ClightType::Tlong(ClightSignedness::Signed, ClightAttr::default())
            ),
            &BTreeSet::new(),
            Some(100)
        ));
    }
}
impl CandidateAnalysis for Rules {
    fn constrain_candidate(
        &self,
        _cx: &FunctionContext<'_>,
        candidate: &Candidate<'_>,
        sink: &ConstraintSink<'_>,
    ) {
        if let Some(condition) = self.0.get(&(candidate.node, candidate.index)) {
            sink.assert_structural(candidate.selected, condition);
        }
    }
}
impl PreparedAnalysis for Completeness {
    fn publish(
        self: Box<Self>,
        db: &mut DecompileDB,
        functions: &[FunctionData],
        state: &ProgramSelectionState,
    ) {
        let mut contracts = Vec::new();
        for function in functions {
            let Some(facts) = FACTS.get(&function.analysis_facts) else {
                continue;
            };
            let validator = Validator::new();
            let chosen = |node| {
                let index = state
                    .candidate_idx
                    .get(&(function.address, node))
                    .copied()
                    .unwrap_or_else(|| function.node_statements.contains_key(&node).then_some(0))?;
                function.node_statements.get(&node)?.get(index)
            };
            for p in &facts.problems {
                contracts.push(SelectedContract {
                    function: function.address,
                    node: p.node,
                    spec: p.spec,
                    epoch: facts.epoch,
                    captured: p.captured,
                    ordered: p.ordered,
                    select_present: p.inst.as_ref().zip(chosen(p.node)).is_some_and(|(i, s)| {
                        carries_value(i, s)
                            || checked_value(i, s, function, &validator).verdict
                                == Verdict::Equivalent
                    }),
                    capture_present: p
                        .inst
                        .as_ref()
                        .zip(chosen(p.spec.capture))
                        .is_some_and(|(i, s)| carries_read(i, s, &p.scalar_views, p.global_view)),
                    select_alternative: state
                        .candidate_idx
                        .get(&(function.address, p.node))
                        .copied()
                        .unwrap_or_else(|| {
                            function.node_statements.contains_key(&p.node).then_some(0)
                        }),
                    capture_alternative: state
                        .candidate_idx
                        .get(&(function.address, p.spec.capture))
                        .copied()
                        .unwrap_or_else(|| {
                            function
                                .node_statements
                                .contains_key(&p.spec.capture)
                                .then_some(0)
                        }),
                    refuted: p.inst.as_ref().zip(chosen(p.node)).is_some_and(|(i, s)| {
                        let check = checked_value(i, s, function, &validator);
                        check.verdict == Verdict::Refuted
                            && check.registers.iter().all(|r| {
                                let ty = state
                                    .var_type_override
                                    .get(&(function.address, *r))
                                    .copied()
                                    .or_else(|| {
                                        function
                                            .var_type_candidates
                                            .get(r)
                                            .and_then(|v| {
                                                v.get(
                                                    state
                                                        .var_decl_idx
                                                        .get(&(function.address, *r))
                                                        .copied()
                                                        .unwrap_or(0),
                                                )
                                            })
                                            .copied()
                                    });
                                ty.is_none_or(|t| !t.is_pointer() && !t.is_float())
                            })
                    }),
                });
            }
        }
        db.rel_set(
            "effect_selected_contract",
            contracts.into_iter().collect::<ascent::boxcar::Vec<_>>(),
        );
    }
}
