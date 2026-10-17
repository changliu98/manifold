//! Selection-owned structural declarations from role-separated evidence.
//!
//! View agreement is a representation cost, never a claim to recover the unique
//! original source type. Representation changes require the shared semantic checks or the
//! explicit-cast pointer transport check. Fixed interfaces/layouts stay fixed.

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::clight_select::syntax::constraints::ConstraintSink;
use crate::decompile::passes::clight_select::syntax::type_evidence::{self, COMMITMENTS, GRAPH};
use crate::decompile::passes::clight_select::syntax::{
    Candidate, CandidateAnalysis, Component, DeclarationContext, FunctionContext, PreparedAnalysis,
};
use crate::decompile::passes::clight_select::{
    query::FunctionData, select::ProgramSelectionState, type_graph::TypeTerm,
};
use crate::x86::types::{Address, Node, RTLReg};
use std::collections::BTreeMap;
use z3::ast::Bool;

pub(crate) struct TypeRecovery;
impl crate::decompile::passes::clight_select::syntax::Component for TypeRecovery {
    fn name(&self) -> &'static str {
        "type-recovery"
    }
    fn reads(&self) -> &'static [&'static str] {
        static READS: std::sync::LazyLock<Vec<&'static str>> = std::sync::LazyLock::new(|| {
            let mut reads = type_evidence::INPUTS.to_vec();
            reads.extend_from_slice(
                crate::decompile::passes::clight_select::solvers::producer_values::INPUTS,
            );
            reads.extend_from_slice(
                crate::decompile::passes::clight_select::syntax::bindings::INPUTS,
            );
            reads.sort_unstable();
            reads.dedup();
            reads
        });
        &READS
    }
    fn writes(&self) -> &'static [&'static str] {
        &["selection_type_recovery", "selection_type_admission", "selection_binding_storage"]
    }
    fn prepare(
        &self,
        db: &DecompileDB,
        functions: &mut [FunctionData],
    ) -> Option<Box<dyn PreparedAnalysis>> {
        // Every other hook keys off the evidence graph prepared here.
        if db.semantic_ablations.disable_type_recovery {
            return None;
        }
        type_evidence::collect_raw(db, functions);
        crate::decompile::passes::clight_select::syntax::bindings::prepare(db, functions);
        type_evidence::finalize(db, functions);
        // Type hypotheses add representation demands. Refresh the shared
        // must-dataflow/producer facts before candidate indices become stable;
        // the machine model must never borrow its width from a C declaration.
        crate::decompile::passes::clight_select::solvers::producer_values::collect(db, functions);
        for function in functions.iter_mut() {
            crate::decompile::passes::clight_select::solvers::word_views::extend_candidates(
                function,
            );
            crate::decompile::passes::clight_select::solvers::type_projection::extend_candidates(
                function,
            );
        }
        Some(Box::new(TypeRecovery))
    }
    fn declaration_alternatives(&self, cx: &DeclarationContext<'_>, reg: RTLReg) -> Vec<TypeTerm> {
        // Stage B pins a CLASS, not a C declaration spelling. Its projection
        // equality is enforced by CTypes; dropping the concrete domain here
        // silently erased every width/pointee choice in a dirty Stage-C solve.
        // Actual interface and storage owners remain fixed independently.
        if cx.function.param_regs.contains(&reg) {
            return vec![];
        }
        GRAPH
            .get(&cx.function.analysis_facts)
            .filter(|g| !g.fixed.contains(&reg))
            .and_then(|g| g.hypotheses.get(&reg))
            .into_iter()
            .flatten()
            .cloned()
            .collect()
    }
    fn evidenced_declarations(&self, cx: &DeclarationContext<'_>, reg: RTLReg) -> Vec<TypeTerm> {
        let mut supported: Vec<TypeTerm> = GRAPH
            .get(&cx.function.analysis_facts)
            .map(|graph| {
                type_evidence::supported_terms(graph, reg, cx.function.data_model)
                    .into_iter()
                    .filter(|ty| {
                        cx.function
                            .var_type_candidates
                            .get(&reg)
                            .into_iter()
                            .flatten()
                            .any(|candidate| {
                                TypeTerm::from_candidate(*candidate, cx.function.data_model) == *ty
                            })
                    })
                    .collect()
            })
            .unwrap_or_default();
        supported
            .extend(crate::decompile::passes::clight_select::syntax::type_flow::supported(cx, reg));
        supported
    }
    fn build(&self, cx: &FunctionContext<'_>) -> Option<Box<dyn CandidateAnalysis>> {
        let graph = GRAPH.get(&cx.function.analysis_facts)?;
        let mut preferences = Vec::new();
        let mut evidence_preferences = Vec::new();
        let mut interface_preferences = Vec::new();
        let declarations = DeclarationContext {
            types: cx.types,
            function: cx.function,
            pins: &[],
            interfaces: &crate::decompile::passes::clight_select::syntax::interfaces::InterfaceTerms::default(),
        };
        for hint in crate::decompile::passes::clight_select::syntax::type_flow::HINTS
            .get(&cx.function.analysis_facts)
            .into_iter()
            .flatten()
        {
            if !hint.active(&declarations) {
                continue;
            }
            let choices: Vec<_> = cx
                .concrete_declarations
                .options(hint.value)
                .filter_map(|(ty, selected)| (ty == hint.ty()).then_some(selected.clone()))
                .collect();
            if !choices.is_empty() {
                interface_preferences.push(Bool::or(&choices));
            }
        }
        let mut conditions = BTreeMap::new();
        let mut families = BTreeMap::<(Node, usize), std::collections::BTreeSet<usize>>::new();
        let mut projection_types = BTreeMap::<(Node, usize), Vec<Bool>>::new();
        for projection in
            crate::decompile::passes::clight_select::solvers::type_projection::PROJECTIONS
                .get(&cx.function.analysis_facts)
                .into_iter()
                .flatten()
        {
            let statements = &cx.function.node_statements[&projection.node];
            let parent = statements
                .iter()
                .position(|s| s == &projection.parent)
                .expect("projection retains its parent");
            let child = statements
                .iter()
                .position(|s| s == &projection.statement)
                .expect("projection is in the bound domain");
            let exact = Bool::or(
                &cx.concrete_declarations
                    .options(projection.reg)
                    .filter_map(|(ty, b)| (ty == &projection.ty).then_some(b.clone()))
                    .collect::<Vec<_>>(),
            );
            projection_types
                .entry((projection.node, child))
                .or_default()
                .push(exact);
            families
                .entry((projection.node, parent))
                .or_default()
                .insert(child);
        }
        for (candidate, types) in projection_types {
            conditions.insert(candidate, vec![Bool::or(&types)]);
        }
        // Index actual uses once; do not rescan the function AST for every
        // declaration. Sorted keys also make constraint construction stable.
        let mut uses = BTreeMap::<RTLReg, BTreeMap<(Node, usize), _>>::new();
        for (&node, statements) in &cx.function.node_statements {
            for (index, statement) in statements.iter().enumerate() {
                for reg in
                    crate::decompile::passes::clight_select::syntax::declarations::dependencies(
                        statement,
                    )
                {
                    if cx.concrete_declarations.0.contains_key(&reg) {
                        uses.entry(reg)
                            .or_default()
                            .insert((node, index), statement);
                    }
                }
            }
        }
        for fact in &graph.facts {
            if let crate::decompile::passes::clight_select::type_graph::Fact::Definition {
                node,
                value,
            } = fact
            {
                if !cx.concrete_declarations.0.contains_key(value) {
                    continue;
                }
                for (index, statement) in cx
                    .function
                    .node_statements
                    .get(node)
                    .into_iter()
                    .flatten()
                    .enumerate()
                {
                    uses.entry(*value)
                        .or_default()
                        .insert((*node, index), statement);
                }
            }
        }
        for (&reg, choice) in &cx.concrete_declarations.0 {
            // Evidence is scored by role, not by a class-gated implication.
            // Otherwise an ungrounded pointer receives a free reward simply
            // by making an integer evidence antecedent false.
            for bytes in type_evidence::storage_widths(graph, reg) {
                let fits: Vec<_> = cx
                    .concrete_declarations
                    .options(reg)
                    .filter_map(|(ty, b)| {
                        (ty.object_bytes(cx.function.data_model) == Some(bytes))
                            .then_some(b.clone())
                    })
                    .collect();
                if !fits.is_empty() {
                    evidence_preferences.push(Bool::or(&fits));
                }
            }
            let hints = type_evidence::value_hints(graph, reg, cx.function.data_model);
            let supported: Vec<_> = cx
                .concrete_declarations
                .options(reg)
                .filter_map(|(ty, b)| hints.contains(ty).then_some(b.clone()))
                .collect();
            if !supported.is_empty() {
                evidence_preferences.push(Bool::or(&supported));
            }
            // Compare representations inside each class. Padding a domain
            // with another class must not create positive evidence for it.
            let mut groups = BTreeMap::<u8, Vec<(&TypeTerm, &Bool, usize)>>::new();
            for (term, selected) in cx.concrete_declarations.options(reg) {
                let class = if term.is_integer() {
                    0
                } else if term.is_pointer() {
                    1
                } else {
                    2
                };
                groups.entry(class).or_default().push((
                    term,
                    selected,
                    type_evidence::view_cost(graph, reg, term, cx.function.data_model),
                ));
            }
            for options in groups.values() {
                let minimum = options.iter().map(|o| o.2).min().unwrap();
                let maximum = options.iter().map(|o| o.2).max().unwrap();
                let active = Bool::or(
                    &options
                        .iter()
                        .map(|(_, b, _)| (*b).clone())
                        .collect::<Vec<_>>(),
                );
                for limit in minimum..maximum {
                    let no_adapter = Bool::or(
                        &options
                            .iter()
                            .filter(|o| o.2 <= limit)
                            .map(|(_, b, _)| (*b).clone())
                            .collect::<Vec<_>>(),
                    );
                    preferences.push(active.implies(no_adapter));
                }
            }
            for (&(node, index), statement) in uses.get(&reg).into_iter().flatten() {
                for (id, selected) in &choice.alternatives {
                    if choice.legacy.contains(id) || choice.evidence.contains(id) {
                        continue;
                    }
                    let term = cx.concrete_declarations.term(*id);
                    if term.is_integer() {
                        continue;
                    } // selected-profile validation owns integer transfers
                    let covered = if term.is_pointer() {
                        // No implicit stride, effective-type or alignment
                        // claim: only explicitly fixed C access views.
                        choice
                            .legacy
                            .iter()
                            .map(|id| cx.concrete_declarations.term(*id))
                            .filter(|legacy| legacy.is_pointer())
                            .any(|legacy| {
                                crate::decompile::passes::clight_select::solvers::type_projection::pointer_transport(
                                    statement,
                                    reg,
                                    legacy,
                                    term,
                                    cx.function.data_model,
                                )
                            })
                    } else {
                        false // no floating-point representation verifier
                    };
                    if !covered {
                        conditions
                            .entry((node, index))
                            .or_insert_with(Vec::new)
                            .push(selected.not());
                    }
                }
            }
        }
        // Exact committed interfaces are stronger evidence than generic
        // machine access views. They describe expressions at a call boundary,
        // not the allocation type of an object reached through a pointer.
        let mut interface_sites = BTreeMap::<(Node, RTLReg, TypeTerm), Vec<Bool>>::new();
        for &node in cx.nodes {
            for (index, statement) in cx.function.node_statements[&node].iter().enumerate() {
                use crate::x86::types::ClightStmt;
                let ClightStmt::Scall(dst, callee, arguments) =
                    crate::decompile::passes::clight_select::solvers::memory_theory::primitive(
                        statement,
                    )
                else {
                    continue;
                };
                let Some(ident) =
                    crate::decompile::passes::clight_select::select::callee_ident_from_expr(
                        callee, cx.names,
                    )
                else {
                    continue;
                };
                let Some(signature) = cx.function.callee_signatures.get(&ident) else {
                    continue;
                };
                let guard = cx
                    .selections
                    .get(&node)
                    .map(|bs| bs[index].clone())
                    .unwrap_or_else(|| Bool::from_bool(true));
                let mut add = |reg, xtype, guard: Bool| {
                    use crate::decompile::passes::clight_select::candtype::CandType;
                    let candidate = CandType::from_xtype(&xtype);
                    if !candidate.is_pointer()
                        || matches!(candidate, CandType::PtrLong | CandType::PtrVoid)
                    {
                        return;
                    }
                    let term = TypeTerm::from_candidate(candidate, cx.function.data_model);
                    if cx
                        .concrete_declarations
                        .options(reg)
                        .any(|(ty, _)| *ty == term)
                    {
                        interface_sites
                            .entry((node, reg, term))
                            .or_default()
                            .push(guard);
                    }
                };
                // An open callee interface is evidence for each alternative
                // under its selector.
                let mut add_interface = |reg,
                                         committed: crate::x86::types::XType,
                                         open: Option<
                    &crate::decompile::passes::clight_select::syntax::interfaces::Alternatives,
                >| match open {
                    Some(alternatives) => {
                        for (xtype, selected) in alternatives {
                            add(reg, *xtype, Bool::and(&[guard.clone(), selected.clone()]));
                        }
                    }
                    None => add(reg, committed, guard.clone()),
                };
                if let Some(dst) = dst {
                    add_interface(
                        *dst as RTLReg,
                        signature.return_type,
                        cx.interfaces.ret(ident),
                    );
                }
                for (position, (argument, xtype)) in
                    arguments.iter().zip(&signature.param_types).enumerate()
                {
                    if let Some(reg) = interface_argument(argument) {
                        add_interface(reg, *xtype, cx.interfaces.param(ident, position));
                    }
                }
            }
        }
        for ((_, reg, term), sites) in interface_sites {
            let selected = Bool::or(
                &cx.concrete_declarations
                    .options(reg)
                    .filter_map(|(ty, b)| (*ty == term).then_some(b.clone()))
                    .collect::<Vec<_>>(),
            );
            interface_preferences.push(Bool::or(&sites).implies(selected));
        }
        // Keep exact class projection visible here for future type analyses;
        // it uses the same recursive term algebra as C legality.
        debug_assert!(cx
            .concrete_declarations
            .0
            .keys()
            .all(|r| cx.declarations.contains_key(r)));
        Some(Box::new(Choices {
            preferences,
            evidence_preferences,
            interface_preferences,
            conditions,
            families,
            unchanged: cx
                .concrete_declarations
                .0
                .values()
                .map(|c| c.fallback.clone())
                .collect(),
        }))
    }

    fn needs_refinement(&self, function: &FunctionData) -> bool {
        GRAPH
            .get(&function.analysis_facts)
            .is_some_and(|g| g.hypotheses.values().flatten().any(TypeTerm::is_integer))
    }
}

fn interface_argument(expression: &crate::x86::types::ClightExpr) -> Option<RTLReg> {
    use crate::x86::types::{ClightExpr, ClightType};
    match expression {
        ClightExpr::Etempvar(reg, _) => Some(*reg as RTLReg),
        ClightExpr::Ecast(inner, ClightType::Tpointer(..)) => interface_argument(inner),
        _ => None, // In particular, &object is not the type of object.
    }
}
#[cfg(test)]
mod tests {
    use crate::decompile::passes::clight_select::syntax::solve::solve_function_z3_with_stack;
    use crate::decompile::passes::clight_select::syntax::type_recovery::*;
    use crate::decompile::passes::clight_select::{
        candtype::{CandType, Sign},
        type_graph::{EvidenceGraph, Fact},
    };
    use crate::decompile::passes::clight_select::{
        solvers::semantics::Semantics,
        syntax::{c_types::CTypes, Stack},
    };
    use crate::x86::op::Operation;
    use crate::x86::types::*;
    use std::collections::BTreeSet;
    use std::collections::HashMap;
    use std::sync::Arc;

    fn fixture() -> FunctionData {
        let mut function = FunctionData::new(
            1,
            "concrete_types".into(),
            vec![],
            vec![],
            None,
            0,
            10,
            true,
        );
        for reg in [1, 2, 3] {
            function.var_type_candidates.insert(
                reg,
                vec![CandType::I64(Sign::Unsigned), CandType::I32(Sign::Unsigned)],
            );
        }
        function
    }
    fn precise_fixture() -> FunctionData {
        proposed_fixture(true)
    }
    fn proposed_fixture(supported: bool) -> FunctionData {
        let mut function = fixture();
        let term = TypeTerm::from_candidate(CandType::I32(Sign::Unsigned), function.data_model);
        let mut facts = BTreeSet::from([Fact::Definition { node: 10, value: 3 }]);
        if supported {
            facts.insert(Fact::Access {
                object: 3,
                node: 10,
                offset: -4,
                write: true,
                chunk: MemoryChunk::MInt32,
            });
        }
        GRAPH.insert(
            &mut function.analysis_facts,
            EvidenceGraph {
                hypotheses: BTreeMap::from([(3, BTreeSet::from([term]))]),
                facts,
                ..Default::default()
            },
        );
        function
    }
    fn constant(value: i32) -> ClightStmt {
        ClightStmt::Sset(
            3,
            ClightExpr::EconstInt(
                value,
                ClightType::Tint(
                    ClightIntSize::I32,
                    ClightSignedness::Unsigned,
                    ClightAttr::default(),
                ),
            ),
        )
    }
    fn selected(function: &FunctionData, with_recovery: bool) -> (usize, usize) {
        let components: Vec<&dyn crate::decompile::passes::clight_select::syntax::Component> =
            if with_recovery {
                vec![&TypeRecovery, &CTypes]
            } else {
                vec![&CTypes]
            };
        let outcome = solve_function_z3_with_stack(
            function,
            &HashMap::new(),
            &[],
            &Stack::new(&[&Semantics], &components),
        )
        .unwrap();
        assert!(
            outcome.2.is_empty(),
            "unexpected class escape: {:?}",
            outcome.2
        );
        (outcome.0[&10].unwrap(), outcome.1[&3])
    }

    #[test]
    fn concrete_width_is_selected_in_z3_not_reanchored_to_long() {
        let mut f = precise_fixture();
        f.node_statements.insert(10, vec![constant(42)]);
        f.integer_anchors.insert(
            10,
            RTLInst::Iop(Operation::Ointconst(42), Arc::new(vec![]), 3),
        );
        assert_eq!(selected(&f, false), (0, 0));
        for _ in 0..3 {
            assert_eq!(selected(&f, true), (0, 1));
        }
    }

    #[test]
    fn a_committed_integer_class_does_not_erase_a_concrete_width() {
        let mut f = precise_fixture();
        f.node_statements.insert(10, vec![constant(42)]);
        f.integer_anchors.insert(
            10,
            RTLInst::Iop(Operation::Ointconst(42), Arc::new(vec![]), 3),
        );
        // The Stage-B representative is a machine word. Stage C must retain
        // the existing 32-bit evidence within that committed integer class.
        let outcome = solve_function_z3_with_stack(
            &f,
            &HashMap::new(),
            &[(3, XType::Xlong)],
            &Stack::new(&[&Semantics], &[&TypeRecovery, &CTypes]),
        )
        .unwrap();
        assert_eq!(
            f.var_type_candidates[&3][outcome.1[&3]],
            CandType::I32(Sign::Unsigned)
        );
        assert_eq!(
            COMMITMENTS.get(&outcome.5).unwrap()[&3],
            TypeTerm::from_candidate(CandType::I32(Sign::Unsigned), f.data_model)
        );
    }

    #[test]
    fn a_class_pin_still_excludes_incompatible_concrete_types() {
        let f = precise_fixture();
        let types = crate::decompile::passes::clight_select::syntax::c_types::TypeDt::build();
        let optimizer = z3::Optimize::new();
        struct Sink<'a>(&'a z3::Optimize);
        impl crate::decompile::passes::clight_select::syntax::constraints::SolveBackend for Sink<'_> {
            fn assert_hard(&self, b: &Bool) {
                self.0.assert(b);
            }
            fn assert_soft(&self, b: &Bool, w: u64) {
                self.0.assert_soft(b, w, None);
            }
        }
        let sink = Sink(&optimizer);
        let pins = [(3, XType::Xptr)];
        let cx = DeclarationContext {
            types: &types,
            function: &f,
            pins: &pins,
            interfaces: &crate::decompile::passes::clight_select::syntax::interfaces::InterfaceTerms::default(),
        };
        let variable = types.fresh();
        let variables = HashMap::from([(3, variable.clone())]);
        CTypes.constrain_declaration(&cx, 3, &variable, &sink);
        let declarations =
            crate::decompile::passes::clight_select::syntax::declarations::Declarations::build(
                &Stack::new(&[], &[&TypeRecovery, &CTypes]),
                &cx,
                &[3],
                &variables,
                &sink,
            );
        CTypes.constrain_interfaces(&cx, &variables, &declarations, &sink);
        let (_, selected) = declarations
            .options(3)
            .find(|(t, _)| t.is_integer() && t.object_bytes(f.data_model) == Some(4))
            .unwrap();
        optimizer.assert(selected);
        assert_eq!(optimizer.check(&[]), z3::SatResult::Unsat);
    }

    #[test]
    fn concrete_recovery_cannot_redeclare_interface_owners() {
        let mut f = precise_fixture();
        f.param_regs.push(3);
        f.param_types.push(ParamType::Typed(XType::Xlong));
        let types = crate::decompile::passes::clight_select::syntax::c_types::TypeDt::build();
        let cx = DeclarationContext {
            types: &types,
            function: &f,
            pins: &[(3, XType::Xlong)],
            interfaces: &crate::decompile::passes::clight_select::syntax::interfaces::InterfaceTerms::default(),
        };
        assert!(TypeRecovery.declaration_alternatives(&cx, 3).is_empty());
    }

    #[test]
    fn a_generic_pointer_class_does_not_pin_pointer_depth() {
        let mut f = fixture();
        f.var_type_candidates
            .insert(3, vec![CandType::PtrLong, CandType::PtrCharPtr]);
        let ty = TypeTerm::from_candidate(CandType::PtrCharPtr, f.data_model);
        GRAPH.insert(
            &mut f.analysis_facts,
            EvidenceGraph {
                hypotheses: BTreeMap::from([(3, BTreeSet::from([ty.clone()]))]),
                facts: BTreeSet::from([Fact::ValueHint {
                    value: 3,
                    ty: ty.clone(),
                }]),
                ..Default::default()
            },
        );
        let outcome = solve_function_z3_with_stack(
            &f,
            &HashMap::new(),
            &[(3, XType::Xptr)],
            &Stack::new(&[&Semantics], &[&TypeRecovery, &CTypes]),
        )
        .unwrap();
        assert_eq!(
            f.var_type_candidates[&3][outcome.1[&3]],
            CandType::PtrCharPtr
        );
        assert_eq!(COMMITMENTS.get(&outcome.5).unwrap()[&3], ty);
    }

    #[test]
    fn grounded_type_evidence_can_choose_an_equivalent_nonpreferred_statement() {
        struct BindType;
        struct Bound(Bool);
        impl crate::decompile::passes::clight_select::syntax::Component for BindType {
            fn name(&self) -> &'static str {
                "test-type-statement-coupling"
            }
            fn build(&self, cx: &FunctionContext<'_>) -> Option<Box<dyn CandidateAnalysis>> {
                Some(Box::new(Bound(Bool::or(
                    &cx.concrete_declarations
                        .options(3)
                        .filter_map(|(ty, b)| {
                            (ty.object_bytes(cx.function.data_model) == Some(4))
                                .then_some(b.clone())
                        })
                        .collect::<Vec<_>>(),
                ))))
            }
        }
        impl CandidateAnalysis for Bound {
            fn constrain_candidate(
                &self,
                _: &FunctionContext<'_>,
                c: &Candidate<'_>,
                sink: &ConstraintSink<'_>,
            ) {
                let condition = if c.index == 1 {
                    self.0.clone()
                } else {
                    self.0.not()
                };
                sink.assert_structural(c.selected, &condition);
            }
        }
        let mut f = precise_fixture();
        f.node_statements.insert(
            10,
            vec![
                ClightStmt::Sset(
                    3,
                    ClightExpr::EconstLong(
                        42,
                        ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default()),
                    ),
                ),
                constant(42),
            ],
        );
        f.integer_anchors.insert(
            10,
            RTLInst::Iop(Operation::Ointconst(42), Arc::new(vec![]), 3),
        );
        let (solvers, components): (
            &[&dyn crate::decompile::passes::clight_select::solvers::Solver],
            &[&dyn crate::decompile::passes::clight_select::syntax::Component],
        ) = (&[&Semantics], &[&TypeRecovery, &CTypes, &BindType]);
        let out = solve_function_z3_with_stack(
            &f,
            &HashMap::new(),
            &[],
            &Stack::new(solvers, components),
        )
        .unwrap();
        assert_eq!(out.0[&10], Some(1));
        assert_eq!(
            out.1[&3], 1,
            "type evidence is not trapped below the rank-zero statement prior"
        );
    }

    #[test]
    fn counterexample_rejects_narrowing_that_loses_machine_result_bits() {
        let mut f = precise_fixture();
        let ty = ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default());
        f.node_statements.insert(
            10,
            vec![ClightStmt::Sset(
                3,
                ClightExpr::Ebinop(
                    ClightBinaryOp::Oadd,
                    Box::new(ClightExpr::Etempvar(1, ty.clone())),
                    Box::new(ClightExpr::Etempvar(2, ty.clone())),
                    ty,
                ),
            )],
        );
        f.integer_anchors
            .insert(10, RTLInst::Iop(Operation::Oaddl, Arc::new(vec![1, 2]), 3));
        assert_eq!(selected(&f, true), (0, 0));
    }

    #[test]
    fn statement_and_concrete_declaration_are_selected_jointly() {
        let mut f = precise_fixture();
        f.node_statements
            .insert(10, vec![constant(43), constant(42)]);
        f.integer_anchors.insert(
            10,
            RTLInst::Iop(Operation::Ointconst(42), Arc::new(vec![]), 3),
        );
        assert_eq!(selected(&f, true), (1, 1));
    }

    #[test]
    fn absent_evidence_leaves_the_class_fallback_unchanged() {
        let mut f = fixture();
        f.node_statements.insert(10, vec![constant(42)]);
        assert_eq!(selected(&f, true), selected(&f, false));
    }

    #[test]
    fn indistinguishable_views_do_not_invent_a_signedness_change() {
        let mut f = fixture();
        GRAPH.insert(
            &mut f.analysis_facts,
            EvidenceGraph {
                hypotheses: BTreeMap::from([(
                    3,
                    BTreeSet::from([TypeTerm::from_candidate(
                        CandType::I64(Sign::Signed),
                        f.data_model,
                    )]),
                )]),
                facts: BTreeSet::from([Fact::Access {
                    node: 10,
                    object: 3,
                    offset: -8,
                    write: true,
                    chunk: MemoryChunk::MInt64,
                }]),
                ..Default::default()
            },
        );
        f.node_statements.insert(
            10,
            vec![ClightStmt::Sset(
                3,
                ClightExpr::EconstLong(
                    42,
                    ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default()),
                ),
            )],
        );
        f.integer_anchors.insert(
            10,
            RTLInst::Iop(Operation::Olongconst(42), Arc::new(vec![]), 3),
        );
        assert_eq!(selected(&f, true), (0, 0));
    }

    #[test]
    fn unsupported_semantics_does_not_authorize_a_narrower_declaration() {
        let mut f = proposed_fixture(false);
        let ty = ClightType::Tint(
            ClightIntSize::I32,
            ClightSignedness::Unsigned,
            ClightAttr::default(),
        );
        f.node_statements.insert(
            10,
            vec![ClightStmt::Sset(
                3,
                ClightExpr::EvarSymbol("opaque_value".into(), ty),
            )],
        );
        f.integer_anchors.insert(
            10,
            RTLInst::Iop(Operation::Ointconst(42), Arc::new(vec![]), 3),
        );
        assert_eq!(selected(&f, true), (0, 0));
    }

    #[test]
    fn declarations_include_call_results_and_all_conditional_arms() {
        let ty = ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default());
        let reg = |r| ClightExpr::Etempvar(r, ty.clone());
        let call = ClightStmt::Scall(
            Some(4),
            ClightExpr::EvarSymbol("callee".into(), ty.clone()),
            vec![ClightExpr::Econdition(
                Box::new(reg(1)),
                Box::new(reg(2)),
                Box::new(reg(3)),
                ty.clone(),
            )],
        );
        assert_eq!(
            crate::decompile::passes::clight_select::syntax::declarations::dependencies(&call),
            BTreeSet::from([1, 2, 3, 4])
        );
    }

    #[test]
    fn known_pointee_survives_class_rendering() {
        let mut f = fixture();
        f.var_type_candidates.insert(
            3,
            vec![
                CandType::PtrChar,
                CandType::PtrLong,
                CandType::PtrInt,
                CandType::I64(Sign::Signed),
            ],
        );
        f.node_statements.insert(10, vec![ClightStmt::Sskip]);
        let term = TypeTerm::from_candidate(CandType::PtrChar, f.data_model);
        GRAPH.insert(
            &mut f.analysis_facts,
            EvidenceGraph {
                hypotheses: BTreeMap::from([(3, BTreeSet::from([term.clone()]))]),
                facts: BTreeSet::from([Fact::ValueHint { value: 3, ty: term }]),
                ..Default::default()
            },
        );
        assert_eq!(selected(&f, false), (0, 1));
        assert_eq!(selected(&f, true), (0, 0));
    }

    #[test]
    fn evidenced_hypothesis_stays_available_but_a_gap_cannot_authorize_narrowing() {
        let mut f = precise_fixture();
        f.node_statements.insert(
            10,
            vec![ClightStmt::Sset(
                3,
                ClightExpr::EvarSymbol(
                    "opaque_value".into(),
                    ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default()),
                ),
            )],
        );
        let (solvers, components): (
            &[&dyn crate::decompile::passes::clight_select::solvers::Solver],
            &[&dyn crate::decompile::passes::clight_select::syntax::Component],
        ) = (&[&Semantics], &[&TypeRecovery, &CTypes]);
        let out = solve_function_z3_with_stack(
            &f,
            &HashMap::new(),
            &[],
            &Stack::new(solvers, components),
        )
        .unwrap();
        assert_eq!(out.1[&3], 0);
        assert!(
            GRAPH.get(&f.analysis_facts).unwrap().hypotheses[&3].contains(
                &TypeTerm::from_candidate(CandType::I32(Sign::Unsigned), f.data_model)
            )
        );
        assert_eq!(
            type_evidence::ADMISSIONS.get(&out.5).unwrap()[&3],
            crate::decompile::passes::clight_select::type_graph::TypeAdmission::LegacyFallback
        );
        assert!(
            !COMMITMENTS.get(&out.5).unwrap().contains_key(&3),
            "a proposal must not become an unvalidated representation commitment"
        );
        assert!(
            !crate::decompile::passes::clight_select::solvers::profiles::VALIDATED
                .get(&out.5)
                .unwrap()
                .contains(&3)
        );
    }

    #[test]
    fn a_proved_word_definition_does_not_authorize_truncating_an_indexed_pointer_load() {
        let mut f = precise_fixture();
        f.var_type_candidates.insert(1, vec![CandType::PtrLong]);
        f.node_statements.insert(10, vec![constant(42)]);
        f.integer_anchors.insert(
            10,
            RTLInst::Iop(Operation::Ointconst(42), Arc::new(vec![]), 3),
        );
        let word = ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default());
        let pointer = ClightType::Tpointer(Arc::new(word.clone()), ClightAttr::default());
        let rhs = ClightExpr::Ederef(
            Box::new(ClightExpr::Ebinop(
                ClightBinaryOp::Oadd,
                Box::new(ClightExpr::Etempvar(1, pointer.clone())),
                Box::new(ClightExpr::Etempvar(2, word.clone())),
                pointer,
            )),
            word,
        );
        f.node_statements.insert(30, vec![ClightStmt::Sset(3, rhs)]);
        crate::decompile::passes::clight_select::solvers::transfers::LOADS.insert(
            &mut f.analysis_facts,
            BTreeMap::from([(
                30,
                crate::decompile::passes::clight_select::solvers::integer_semantics::LoadValue {
                    node: 30,
                    chunk: MemoryChunk::MAny64,
                    destination: 3,
                    write_bits: Some(64),
                    signed_word_load: false,
                },
            )]),
        );
        let (solvers, components): (
            &[&dyn crate::decompile::passes::clight_select::solvers::Solver],
            &[&dyn crate::decompile::passes::clight_select::syntax::Component],
        ) = (&[&Semantics], &[&TypeRecovery, &CTypes]);
        let out = solve_function_z3_with_stack(
            &f,
            &HashMap::new(),
            &[],
            &Stack::new(solvers, components),
        )
        .unwrap();
        assert_eq!(
            out.1[&3], 0,
            "a later wide definition must retain all loaded bits"
        );
        assert_eq!(
            COMMITMENTS.get(&out.5).unwrap().get(&3),
            Some(&TypeTerm::from_candidate(
                CandType::I64(Sign::Unsigned),
                f.data_model
            )),
            "the repaired wide binding must survive emission"
        );
        assert!(
            !crate::decompile::passes::clight_select::solvers::profiles::VALIDATED
                .get(&out.5)
                .unwrap()
                .contains(&3),
            "preserving a legacy proof dependency is not a new type certificate"
        );
    }

    #[test]
    fn escaped_array_owners_are_visible_before_scalar_selection() {
        let mut db = DecompileDB::default();
        for (node, offset, reg) in [(10_u64, -32_i64, 3_u64), (20, -24, 4)] {
            db.rel_push("stack_var", (1_u64, node, offset, reg));
            db.rel_push(
                "escaped_stack_region_field",
                (1_u64, -32_i64, offset + 32, MemoryChunk::MInt64),
            );
            db.rel_push(
                "type_storage_access",
                (1_u64, node, reg, offset, true, MemoryChunk::MInt8Unsigned),
            );
        }
        let mut f = fixture();
        f.var_type_candidates
            .insert(4, f.var_type_candidates[&3].clone());
        TypeRecovery.prepare(&db, std::slice::from_mut(&mut f));
        let graph = GRAPH.get(&f.analysis_facts).unwrap();
        for reg in [3, 4] {
            assert!(graph.fixed_storage.contains(&reg));
            assert!(!graph.hypotheses.contains_key(&reg));
        }
        assert!(graph.facts.iter().any(|fact| matches!(
            fact,
            Fact::Layout {
                object: 3,
                ty: TypeTerm::Array(_, Some(2))
            }
        )));
    }

    #[test]
    fn a_use_check_cannot_certify_its_own_narrow_input_relation() {
        let mut f = precise_fixture();
        let word = TypeTerm::from_candidate(CandType::I32(Sign::Unsigned), f.data_model);
        let mut graph = GRAPH.get(&f.analysis_facts).unwrap().clone();
        graph.hypotheses.insert(1, BTreeSet::from([word.clone()]));
        graph.facts.insert(Fact::ValueHint { value: 1, ty: word });
        // Construct the graph once: artifact replacement is intentionally not
        // an operation supported by the prepared-analysis interface.
        f.analysis_facts = crate::decompile::passes::clight_select::syntax::Artifacts::default();
        GRAPH.insert(&mut f.analysis_facts, graph);
        f.word_inputs.insert(10, BTreeSet::from([1]));
        f.node_statements.insert(
            10,
            vec![ClightStmt::Sset(
                3,
                ClightExpr::Ecast(
                    Box::new(ClightExpr::Etempvar(
                        1,
                        ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default()),
                    )),
                    ClightType::Tint(
                        ClightIntSize::I32,
                        ClightSignedness::Unsigned,
                        ClightAttr::default(),
                    ),
                ),
            )],
        );
        f.integer_anchors.insert(
            10,
            RTLInst::Iop(Operation::Ocast32unsigned, Arc::new(vec![1]), 3),
        );
        let (solvers, components): (
            &[&dyn crate::decompile::passes::clight_select::solvers::Solver],
            &[&dyn crate::decompile::passes::clight_select::syntax::Component],
        ) = (&[&Semantics], &[&TypeRecovery, &CTypes]);
        let out = solve_function_z3_with_stack(
            &f,
            &HashMap::new(),
            &[],
            &Stack::new(solvers, components),
        )
        .unwrap();
        assert_eq!(
            out.1[&1], 0,
            "a use cannot establish its own input representation invariant"
        );
        assert!(
            !crate::decompile::passes::clight_select::solvers::profiles::VALIDATED
                .get(&out.5)
                .unwrap()
                .contains(&1)
        );
    }

    #[test]
    fn refinement_failure_retains_complete_proofs_but_disables_unvalidated_changes() {
        struct Stop;
        impl crate::decompile::passes::clight_select::solvers::Solver for Stop {
            fn name(&self) -> &'static str {
                "stop"
            }
            fn checker<'a>(
                &self,
                _: &FunctionContext<'a>,
                _: &z3::Optimize,
            ) -> Option<Box<dyn crate::decompile::passes::clight_select::solvers::Checker + 'a>>
            {
                Some(Box::new(Stop))
            }
        }
        impl crate::decompile::passes::clight_select::solvers::Checker for Stop {
            fn round_limit(&self) -> usize {
                0
            }
            fn check(
                &mut self,
                _: &z3::Model,
            ) -> crate::decompile::passes::clight_select::solvers::Verdict {
                crate::decompile::passes::clight_select::solvers::Verdict::Unknown(
                    "test unsupported",
                )
            }
            fn coupled_nodes(&self) -> BTreeSet<Node> {
                BTreeSet::new()
            }
            fn finish(
                self: Box<Self>,
                _: Option<&z3::Model>,
                _: &'static str,
                _: &mut crate::decompile::passes::clight_select::syntax::Artifacts,
            ) {
            }
        }
        let (solvers, components): (
            &[&dyn crate::decompile::passes::clight_select::solvers::Solver],
            &[&dyn crate::decompile::passes::clight_select::syntax::Component],
        ) = (&[&Semantics, &Stop], &[&TypeRecovery, &CTypes]);
        for supported in [false, true] {
            let mut f = proposed_fixture(supported);
            f.node_statements.insert(10, vec![constant(42)]);
            f.integer_anchors.insert(
                10,
                RTLInst::Iop(Operation::Ointconst(42), Arc::new(vec![]), 3),
            );
            let out = solve_function_z3_with_stack(
                &f,
                &HashMap::new(),
                &[],
                &Stack::new(solvers, components),
            )
            .unwrap();
            if supported {
                assert_eq!(out.1[&3], 1, "an unrelated failed analysis must not discard a complete guarded transfer proof");
                assert!(COMMITMENTS.get(&out.5).unwrap().contains_key(&3));
                assert!(
                    crate::decompile::passes::clight_select::solvers::profiles::VALIDATED
                        .get(&out.5)
                        .unwrap()
                        .contains(&3)
                );
            } else {
                assert_eq!(out.1[&3], 0, "proof availability is not positive evidence for an unsupported source type");
                assert!(!COMMITMENTS.get(&out.5).unwrap().contains_key(&3));
            }
        }
        // A real lost-bit witness remains mandatory even when another module
        // exhausts its work. An independent but unvalidated narrowing must
        // not become eligible merely because a different profile was refuted.
        let mut f = precise_fixture();
        f.var_type_candidates
            .insert(4, f.var_type_candidates[&3].clone());
        let mut graph = GRAPH.get(&f.analysis_facts).unwrap().clone();
        graph.hypotheses.insert(4, graph.hypotheses[&3].clone());
        graph.facts.extend([
            Fact::Definition { node: 20, value: 4 },
            Fact::Access {
                node: 20,
                object: 4,
                offset: -8,
                write: true,
                chunk: MemoryChunk::MInt32,
            },
        ]);
        f.analysis_facts = crate::decompile::passes::clight_select::syntax::Artifacts::default();
        GRAPH.insert(&mut f.analysis_facts, graph);
        let word = ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default());
        f.node_statements.insert(
            10,
            vec![ClightStmt::Sset(
                3,
                ClightExpr::EconstLong(1 << 40, word.clone()),
            )],
        );
        f.integer_anchors.insert(
            10,
            RTLInst::Iop(Operation::Olongconst(1 << 40), Arc::new(vec![]), 3),
        );
        f.node_statements.insert(
            20,
            vec![ClightStmt::Sset(
                4,
                ClightExpr::EvarSymbol("opaque".into(), word),
            )],
        );
        let out = solve_function_z3_with_stack(
            &f,
            &HashMap::new(),
            &[],
            &Stack::new(solvers, components),
        )
        .unwrap();
        assert_eq!(
            out.1[&3], 0,
            "retained refutation forbids losing the high bit"
        );
        assert_eq!(
            out.1[&4], 0,
            "the fallback cannot emit another unchecked narrow profile"
        );
        assert!(
            !crate::decompile::passes::clight_select::solvers::profiles::VALIDATED
                .get(&out.5)
                .unwrap()
                .contains(&4)
        );
    }

    #[test]
    fn fallback_cannot_reuse_a_certificate_for_a_different_statement_choice() {
        struct ChangeChoice;
        struct RejectFirst(z3::ast::Bool);
        impl crate::decompile::passes::clight_select::solvers::Solver for ChangeChoice {
            fn name(&self) -> &'static str {
                "change-choice"
            }
            fn checker<'a>(
                &self,
                cx: &FunctionContext<'a>,
                _: &z3::Optimize,
            ) -> Option<Box<dyn crate::decompile::passes::clight_select::solvers::Checker + 'a>>
            {
                Some(Box::new(RejectFirst(cx.selections[&10][0].not())))
            }
        }
        impl crate::decompile::passes::clight_select::solvers::Checker for RejectFirst {
            fn round_limit(&self) -> usize {
                0
            }
            fn check(
                &mut self,
                _: &z3::Model,
            ) -> crate::decompile::passes::clight_select::solvers::Verdict {
                crate::decompile::passes::clight_select::solvers::Verdict::Unknown("test fallback")
            }
            fn coupled_nodes(&self) -> BTreeSet<Node> {
                BTreeSet::from([10])
            }
            fn fallback_constraints(&self) -> Vec<z3::ast::Bool> {
                vec![self.0.clone()]
            }
            fn finish(
                self: Box<Self>,
                _: Option<&z3::Model>,
                _: &'static str,
                _: &mut crate::decompile::passes::clight_select::syntax::Artifacts,
            ) {
            }
        }
        let mut f = precise_fixture();
        let second = ClightStmt::Sset(
            3,
            ClightExpr::Ecast(
                Box::new(ClightExpr::EconstInt(
                    42,
                    ClightType::Tint(
                        ClightIntSize::I32,
                        ClightSignedness::Signed,
                        ClightAttr::default(),
                    ),
                )),
                ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default()),
            ),
        );
        f.node_statements.insert(10, vec![constant(42), second]);
        f.integer_anchors.insert(
            10,
            RTLInst::Iop(Operation::Ointconst(42), Arc::new(vec![]), 3),
        );
        let (solvers, components): (
            &[&dyn crate::decompile::passes::clight_select::solvers::Solver],
            &[&dyn crate::decompile::passes::clight_select::syntax::Component],
        ) = (&[&Semantics, &ChangeChoice], &[&TypeRecovery, &CTypes]);
        let out = solve_function_z3_with_stack(
            &f,
            &HashMap::new(),
            &[],
            &Stack::new(solvers, components),
        )
        .unwrap();
        assert_eq!(out.0[&10], Some(1));
        assert_eq!(
            out.1[&3], 0,
            "a proof of candidate0 cannot certify candidate1"
        );
        assert!(
            !crate::decompile::passes::clight_select::solvers::profiles::VALIDATED
                .get(&out.5)
                .unwrap()
                .contains(&3)
        );
    }

    #[test]
    fn a_checked_switch_view_does_not_require_its_absorbed_comparisons_to_reappear() {
        use either::Either;
        let mut f = precise_fixture();
        f.structure_worlds = vec![0, 1];
        f.authoritative_structure_world = 0;
        let ty = TypeTerm::from_candidate(CandType::I32(Sign::Unsigned), f.data_model)
            .to_clight(f.data_model);
        f.node_statements.insert(10, vec![constant(42)]);
        f.integer_anchors.insert(
            10,
            RTLInst::Iop(Operation::Ointconst(42), Arc::new(vec![]), 3),
        );
        f.node_statements.insert(
            20,
            vec![ClightStmt::Sifthenelse(
                ClightExpr::Ebinop(
                    ClightBinaryOp::Oeq,
                    Box::new(ClightExpr::Etempvar(3, ty.clone())),
                    Box::new(ClightExpr::EconstInt(43, ty.clone())),
                    ty.clone(),
                ),
                Box::new(ClightStmt::Sgoto(40)),
                Box::new(ClightStmt::Sgoto(50)),
            )],
        );
        f.integer_anchors.insert(
            20,
            RTLInst::Icond(
                crate::x86::op::Condition::Ccompuimm(crate::x86::op::Comparison::Ceq, 43),
                Arc::new(vec![3]),
                Either::Right(40),
                Either::Right(50),
            ),
        );
        f.node_statements.insert(
            30,
            vec![ClightStmt::Sswitch(
                ClightExpr::Etempvar(3, ty),
                vec![
                    (Some(42), ClightStmt::Sgoto(40)),
                    (None, ClightStmt::Sgoto(50)),
                ],
            )],
        );
        f.integer_anchors.insert(
            30,
            RTLInst::Icond(
                crate::x86::op::Condition::Ccompuimm(crate::x86::op::Comparison::Ceq, 42),
                Arc::new(vec![3]),
                Either::Right(40),
                Either::Right(50),
            ),
        );
        f.candidate_structure_worlds
            .insert(10, vec![BTreeSet::from([0, 1])]);
        f.candidate_structure_worlds
            .insert(20, vec![BTreeSet::from([1])]);
        f.candidate_structure_worlds
            .insert(30, vec![BTreeSet::from([0])]);
        let (solvers, components): (
            &[&dyn crate::decompile::passes::clight_select::solvers::Solver],
            &[&dyn crate::decompile::passes::clight_select::syntax::Component],
        ) = (&[&Semantics], &[&TypeRecovery, &CTypes]);
        let out = solve_function_z3_with_stack(
            &f,
            &HashMap::new(),
            &[],
            &Stack::new(solvers, components),
        )
        .unwrap();
        assert_eq!(out.3, 0);
        assert_eq!(out.1[&3], 1);
        assert_eq!(out.0[&20], None);
        assert_eq!(out.0[&30], Some(0));
    }

    #[test]
    fn typed_calls_and_copies_do_not_erase_an_existing_pointer_hypothesis() {
        for name in ["fetch_text", "renamed_provider"] {
            let mut f = fixture();
            let char_ptr = TypeTerm::from_candidate(CandType::PtrChar, f.data_model);
            let ty = char_ptr.to_clight(f.data_model);
            f.return_type = ty.clone();
            f.var_type_candidates.insert(
                3,
                vec![CandType::PtrChar, CandType::PtrLong, CandType::PtrInt],
            );
            f.var_type_candidates
                .insert(4, f.var_type_candidates[&3].clone());
            f.node_statements.insert(
                10,
                vec![ClightStmt::Scall(
                    Some(3),
                    ClightExpr::EvarSymbol(name.into(), ty.clone()),
                    vec![],
                )],
            );
            f.node_statements.insert(
                11,
                vec![ClightStmt::Sset(4, ClightExpr::Etempvar(3, ty.clone()))],
            );
            f.node_statements.insert(
                12,
                vec![ClightStmt::Sreturn(Some(ClightExpr::Etempvar(
                    4,
                    ty.clone(),
                )))],
            );
            f.callee_signatures.insert(
                90,
                crate::decompile::passes::clight_select::query::CalleeSignature {
                    param_count: 0,
                    return_type: XType::Xcharptr,
                    param_types: vec![],
                    is_varargs: false,
                },
            );
            GRAPH.insert(
                &mut f.analysis_facts,
                EvidenceGraph {
                    hypotheses: [3, 4]
                        .into_iter()
                        .map(|r| (r, BTreeSet::from([char_ptr.clone()])))
                        .collect(),
                    facts: [3, 4]
                        .into_iter()
                        .map(|r| Fact::ValueHint {
                            value: r,
                            ty: char_ptr.clone(),
                        })
                        .collect(),
                    ..Default::default()
                },
            );
            let (solvers, components): (
                &[&dyn crate::decompile::passes::clight_select::solvers::Solver],
                &[&dyn crate::decompile::passes::clight_select::syntax::Component],
            ) = (&[&Semantics], &[&TypeRecovery, &CTypes]);
            let out = solve_function_z3_with_stack(
                &f,
                &HashMap::from([(name.into(), 90)]),
                &[],
                &Stack::new(solvers, components),
            )
            .unwrap();
            assert_eq!(out.1[&3], 0);
            assert_eq!(out.1[&4], 0);
        }
    }

    #[test]
    fn committed_interface_evidence_outweighs_a_conflicting_access_view() {
        let mut f = fixture();
        let char_ptr = TypeTerm::from_candidate(CandType::PtrChar, f.data_model);
        let int_ptr = TypeTerm::from_candidate(CandType::PtrInt, f.data_model);
        f.var_type_candidates.insert(
            3,
            vec![CandType::PtrLong, CandType::PtrChar, CandType::PtrInt],
        );
        f.node_statements.insert(
            10,
            vec![ClightStmt::Scall(
                Some(3),
                ClightExpr::Evar(90, char_ptr.to_clight(f.data_model)),
                vec![],
            )],
        );
        f.callee_signatures.insert(
            90,
            crate::decompile::passes::clight_select::query::CalleeSignature {
                param_count: 0,
                return_type: XType::Xcharptr,
                param_types: vec![],
                is_varargs: false,
            },
        );
        GRAPH.insert(
            &mut f.analysis_facts,
            EvidenceGraph {
                hypotheses: BTreeMap::from([(
                    3,
                    BTreeSet::from([char_ptr.clone(), int_ptr.clone()]),
                )]),
                facts: BTreeSet::from([
                    Fact::ValueHint {
                        value: 3,
                        ty: char_ptr,
                    },
                    Fact::ValueHint {
                        value: 3,
                        ty: int_ptr,
                    },
                    Fact::PointerAccess {
                        node: 11,
                        base: 3,
                        offset: 0,
                        write: false,
                        chunk: MemoryChunk::MInt32,
                    },
                ]),
                ..Default::default()
            },
        );
        let (solvers, components): (
            &[&dyn crate::decompile::passes::clight_select::solvers::Solver],
            &[&dyn crate::decompile::passes::clight_select::syntax::Component],
        ) = (&[&Semantics], &[&TypeRecovery, &CTypes]);
        let out = solve_function_z3_with_stack(
            &f,
            &HashMap::new(),
            &[],
            &Stack::new(solvers, components),
        )
        .unwrap();
        assert_eq!(out.1[&3], 1);
    }

    #[test]
    fn evidence_preparation_keeps_storage_webs_and_sign_alternatives_separate() {
        let mut db = DecompileDB::default();
        db.rel_push(
            "type_storage_access",
            (1_u64, 10_u64, 3_u64, -4_i64, true, MemoryChunk::MInt32),
        );
        db.rel_push(
            "type_storage_access",
            (1_u64, 11_u64, 4_u64, -16_i64, true, MemoryChunk::MInt64),
        );
        let mut f = fixture();
        f.var_type_candidates
            .insert(4, f.var_type_candidates[&3].clone());
        TypeRecovery.prepare(&db, std::slice::from_mut(&mut f));
        let g = GRAPH.get(&f.analysis_facts).unwrap();
        for (reg, size) in [(3, 4), (4, 8)] {
            assert_eq!(
                g.hypotheses[&reg].len(),
                2,
                "storage width must not decide signedness"
            );
            assert!(g.hypotheses[&reg]
                .iter()
                .all(|t| t.object_bytes(f.data_model) == Some(size)));
        }
    }

    #[test]
    fn unknown_storage_never_licenses_narrowing() {
        let mut db = DecompileDB::default();
        for chunk in [MemoryChunk::MInt32, MemoryChunk::Unknown] {
            db.rel_push(
                "type_storage_access",
                (1_u64, 10_u64, 3_u64, -4_i64, true, chunk),
            );
        }
        let mut f = fixture();
        TypeRecovery.prepare(&db, std::slice::from_mut(&mut f));
        let g = GRAPH.get(&f.analysis_facts).unwrap();
        assert!(g.unknown_storage.contains(&3));
        assert!(!g.hypotheses.contains_key(&3));
    }

    #[test]
    fn type_recovery_ablation_prepares_no_evidence() {
        let mut db = DecompileDB::default();
        db.rel_push(
            "type_storage_access",
            (1_u64, 10_u64, 3_u64, -4_i64, true, MemoryChunk::MInt32),
        );
        let mut production = fixture();
        assert!(TypeRecovery
            .prepare(&db, std::slice::from_mut(&mut production))
            .is_some());
        assert!(GRAPH.get(&production.analysis_facts).is_some());
        db.semantic_ablations.disable_type_recovery = true;
        let mut ablated = fixture();
        assert!(TypeRecovery
            .prepare(&db, std::slice::from_mut(&mut ablated))
            .is_none());
        assert!(GRAPH.get(&ablated.analysis_facts).is_none());
    }

    #[test]
    fn pointer_padding_is_not_pointee_evidence() {
        let db = DecompileDB::default();
        let mut f = fixture();
        f.var_type_candidates.insert(
            3,
            vec![
                CandType::PtrChar,
                CandType::PtrLong,
                CandType::PtrInt,
                CandType::PtrVoid,
            ],
        );
        TypeRecovery.prepare(&db, std::slice::from_mut(&mut f));
        assert!(!GRAPH
            .get(&f.analysis_facts)
            .unwrap()
            .hypotheses
            .contains_key(&3));
    }

    #[test]
    fn type_commitments_carry_the_checked_type_not_just_a_candidate_index() {
        let mut f = precise_fixture();
        f.node_statements.insert(10, vec![constant(42)]);
        f.integer_anchors.insert(
            10,
            RTLInst::Iop(Operation::Ointconst(42), Arc::new(vec![]), 3),
        );
        let (solvers, components): (
            &[&dyn crate::decompile::passes::clight_select::solvers::Solver],
            &[&dyn crate::decompile::passes::clight_select::syntax::Component],
        ) = (&[&Semantics], &[&TypeRecovery, &CTypes]);
        let out = solve_function_z3_with_stack(
            &f,
            &HashMap::new(),
            &[],
            &Stack::new(solvers, components),
        )
        .unwrap();
        assert_eq!(
            COMMITMENTS.get(&out.5).unwrap()[&3],
            TypeTerm::from_candidate(CandType::I32(Sign::Unsigned), f.data_model)
        );
    }

    #[test]
    fn a_checked_profile_commits_unchanged_input_declarations_too() {
        let mut f = precise_fixture();
        let wide = ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default());
        let word = ClightType::Tint(
            ClightIntSize::I32,
            ClightSignedness::Unsigned,
            ClightAttr::default(),
        );
        let input = |reg| {
            ClightExpr::Ecast(
                Box::new(ClightExpr::Etempvar(reg, wide.clone())),
                word.clone(),
            )
        };
        f.node_statements.insert(
            10,
            vec![ClightStmt::Sset(
                3,
                ClightExpr::Ebinop(
                    ClightBinaryOp::Oadd,
                    Box::new(input(1)),
                    Box::new(input(2)),
                    word.clone(),
                ),
            )],
        );
        f.integer_anchors
            .insert(10, RTLInst::Iop(Operation::Oadd, Arc::new(vec![1, 2]), 3));
        let (solvers, components): (
            &[&dyn crate::decompile::passes::clight_select::solvers::Solver],
            &[&dyn crate::decompile::passes::clight_select::syntax::Component],
        ) = (&[&Semantics], &[&TypeRecovery, &CTypes]);
        let out = solve_function_z3_with_stack(
            &f,
            &HashMap::new(),
            &[],
            &Stack::new(solvers, components),
        )
        .unwrap();
        let declarations = COMMITMENTS.get(&out.5).unwrap();
        assert_eq!(
            declarations[&3],
            TypeTerm::from_candidate(CandType::I32(Sign::Unsigned), f.data_model)
        );
        assert_eq!(
            declarations[&1],
            TypeTerm::from_candidate(CandType::I64(Sign::Unsigned), f.data_model)
        );
        assert_eq!(declarations[&2], declarations[&1]);
    }

    #[test]
    fn unanchored_statement_does_not_authorize_a_new_type() {
        let mut f = proposed_fixture(false);
        f.node_statements.insert(10, vec![constant(42)]);
        assert_eq!(selected(&f, true), (0, 0));
    }

    #[test]
    fn dropping_a_machine_definition_does_not_remove_its_type_obligation() {
        let mut f = proposed_fixture(false);
        f.node_statements.insert(10, vec![ClightStmt::Sskip]);
        f.integer_anchors.insert(
            10,
            RTLInst::Iop(Operation::Ointconst(42), Arc::new(vec![]), 3),
        );
        assert_eq!(selected(&f, true), (0, 0));
    }

    #[test]
    fn structural_pointer_hypotheses_need_no_new_legacy_enum_variant() {
        let mut f = fixture();
        f.var_type_candidates.insert(3, vec![CandType::PtrLong]);
        f.must_pointer_regs.insert(3);
        f.node_statements.insert(10, vec![constant(0)]);
        let term = TypeTerm::integer(16, Sign::Unsigned, f.data_model)
            .unwrap()
            .pointer();
        GRAPH.insert(
            &mut f.analysis_facts,
            EvidenceGraph {
                hypotheses: BTreeMap::from([(3, BTreeSet::from([term.clone()]))]),
                facts: BTreeSet::from([Fact::PointerAccess {
                    base: 3,
                    node: 10,
                    offset: 0,
                    write: false,
                    chunk: MemoryChunk::MInt16Unsigned,
                }]),
                ..Default::default()
            },
        );
        let (solvers, components): (
            &[&dyn crate::decompile::passes::clight_select::solvers::Solver],
            &[&dyn crate::decompile::passes::clight_select::syntax::Component],
        ) = (&[&Semantics], &[&TypeRecovery, &CTypes]);
        let out = solve_function_z3_with_stack(
            &f,
            &HashMap::new(),
            &[],
            &Stack::new(solvers, components),
        )
        .unwrap();
        assert_eq!(COMMITMENTS.get(&out.5).unwrap()[&3], term);
        assert!(term.legacy_candidate(f.data_model).is_none());
        assert_eq!(
            type_evidence::ADMISSIONS.get(&out.5).unwrap()[&3],
            crate::decompile::passes::clight_select::type_graph::TypeAdmission::ExplicitPointerViews
        );
    }

    #[test]
    fn structural_declaration_and_its_assignment_view_are_selected_together() {
        let mut f = fixture();
        f.var_type_candidates.insert(3, vec![CandType::PtrLong]);
        f.must_pointer_regs.insert(3);
        let before = TypeTerm::from_candidate(CandType::PtrLong, f.data_model);
        let after = TypeTerm::integer(16, Sign::Unsigned, f.data_model)
            .unwrap()
            .pointer();
        f.node_statements.insert(
            10,
            vec![ClightStmt::Sset(
                3,
                ClightExpr::Ecast(
                    Box::new(ClightExpr::Etempvar(
                        1,
                        ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default()),
                    )),
                    before.to_clight(f.data_model),
                ),
            )],
        );
        GRAPH.insert(
            &mut f.analysis_facts,
            EvidenceGraph {
                hypotheses: BTreeMap::from([(3, BTreeSet::from([after.clone()]))]),
                facts: BTreeSet::from([
                    Fact::Definition { node: 10, value: 3 },
                    Fact::PointerAccess {
                        base: 3,
                        node: 20,
                        offset: 0,
                        write: false,
                        chunk: MemoryChunk::MInt16Unsigned,
                    },
                ]),
                ..Default::default()
            },
        );
        crate::decompile::passes::clight_select::solvers::type_projection::extend_candidates(
            &mut f,
        );
        assert_eq!(f.node_statements[&10].len(), 2);
        let (solvers, components): (
            &[&dyn crate::decompile::passes::clight_select::solvers::Solver],
            &[&dyn crate::decompile::passes::clight_select::syntax::Component],
        ) = (&[&Semantics], &[&TypeRecovery, &CTypes]);
        let out = solve_function_z3_with_stack(
            &f,
            &HashMap::new(),
            &[],
            &Stack::new(solvers, components),
        )
        .unwrap();
        assert_eq!(
            out.0[&10],
            Some(1),
            "a representation view must not pay a second semantic prior"
        );
        assert_eq!(COMMITMENTS.get(&out.5).unwrap()[&3], after);
    }

    #[test]
    fn changing_function_names_and_addresses_does_not_change_a_proved_declaration() {
        for (name, address) in [("unrelated_alpha", 0x4000), ("renamed_beta", 0x90000000)] {
            let mut f = precise_fixture();
            f.name = name.into();
            f.address = address;
            f.node_statements.insert(10, vec![constant(42)]);
            f.integer_anchors.insert(
                10,
                RTLInst::Iop(Operation::Ointconst(42), Arc::new(vec![]), 3),
            );
            assert_eq!(selected(&f, true), (0, 1));
        }
    }
}
struct Choices {
    preferences: Vec<Bool>,
    evidence_preferences: Vec<Bool>,
    interface_preferences: Vec<Bool>,
    conditions: BTreeMap<(Node, usize), Vec<Bool>>,
    families: BTreeMap<(Node, usize), std::collections::BTreeSet<usize>>,
    unchanged: Vec<Bool>,
}
impl Choices {
    fn scales(&self) -> (usize, usize, usize, usize) {
        let view = self.unchanged.len() + 1;
        let secondary = self
            .preferences
            .len()
            .checked_mul(view)
            .and_then(|n| n.checked_add(self.unchanged.len()))
            .expect("type view bound");
        let interface = self.evidence_preferences.len() + 1;
        let evidence = self
            .interface_preferences
            .len()
            .checked_mul(interface)
            .and_then(|n| n.checked_add(self.evidence_preferences.len()))
            .expect("type evidence bound");
        (view, interface, secondary, evidence)
    }
}
impl CandidateAnalysis for Choices {
    fn prior_family(&self, node: Node, parent: usize) -> Vec<usize> {
        self.families
            .get(&(node, parent))
            .into_iter()
            .flatten()
            .copied()
            .collect()
    }
    fn secondary_count(&self) -> usize {
        self.scales().2
    }
    fn evidence_count(&self) -> usize {
        self.scales().3
    }
    fn constrain_function(&self, _cx: &FunctionContext<'_>, sink: &ConstraintSink<'_>) {
        let (view, interface, _, _) = self.scales();
        for preference in &self.interface_preferences {
            sink.assert_evidence_weighted(preference, interface as u64, "type_interfaces");
        }
        for preference in &self.evidence_preferences {
            sink.assert_evidence_weighted(preference, 1, "type_evidence");
        }
        for preference in &self.preferences {
            // Minimize view adapters first, then unnecessary changes. This
            // scale is a lexicographic bound, not a corpus-tuned weight.
            sink.assert_secondary_weighted(preference, view as u64, "type_views");
        }
        for unchanged in &self.unchanged {
            sink.assert_secondary(unchanged, "type_ambiguity");
        }
    }
    fn constrain_candidate(
        &self,
        _cx: &FunctionContext<'_>,
        candidate: &Candidate<'_>,
        sink: &ConstraintSink<'_>,
    ) {
        if let Some(conditions) = self.conditions.get(&(candidate.node, candidate.index)) {
            sink.assert_structural(candidate.selected, &Bool::and(conditions));
        }
    }
}
impl PreparedAnalysis for TypeRecovery {
    fn publish(
        self: Box<Self>,
        db: &mut DecompileDB,
        functions: &[FunctionData],
        selection: &ProgramSelectionState,
    ) {
        let mut rows = Vec::new();
        let mut admissions = Vec::new();
        crate::decompile::passes::clight_select::syntax::bindings::publish(db, functions);
        for function in functions {
            let Some(graph) = GRAPH.get(&function.analysis_facts) else {
                continue;
            };
            let committed = selection
                .analysis_results
                .get(&function.address)
                .and_then(|a| COMMITMENTS.get(a));
            if let Some(statuses) = selection
                .analysis_results
                .get(&function.address)
                .and_then(|a| type_evidence::ADMISSIONS.get(a))
            {
                for (&reg, status) in statuses {
                    admissions.push((function.address, reg, *status));
                }
            }
            for (&reg, hypotheses) in &graph.hypotheses {
                for ty in hypotheses {
                    rows.push((
                        function.address,
                        reg,
                        ty.clone(),
                        committed.and_then(|m| m.get(&reg)) == Some(ty),
                    ));
                }
            }
        }
        rows.sort();
        db.rel_set(
            "selection_type_recovery",
            rows.into_iter()
                .collect::<ascent::boxcar::Vec<(Address, RTLReg, TypeTerm, bool)>>(),
        );
        admissions.sort();
        db.rel_set(
            "selection_type_admission",
            admissions.into_iter().collect::<ascent::boxcar::Vec<_>>(),
        );
    }
}
