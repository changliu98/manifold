//! Interface evidence transported through native, width-preserving copies.
//!
//! This is evidence about a value, not an equality between C declaration
//! spellings. A declaration invariant must cover EVERY native definition.
//! Width-preserving copy cycles and joins may agree even when they have more
//! than one source. An unknown writer, conversion, or conflicting type joins
//! to Top, never a majority vote. This is a per-value type lattice, not a claim
//! that one definition reaches a particular use.
use crate::decompile::passes::c_pass::convert::from_relations::convert_param_type_from_param;
use crate::decompile::passes::clight_select::syntax::{ArtifactKey, DeclarationContext};
use crate::decompile::passes::clight_select::{
    candtype::CandType,
    query::FunctionData,
    type_graph::{EvidenceGraph, TypeTerm},
};
use crate::x86::types::*;
use ascent::{
    ascent,
    lattice::{constant_propagation::ConstPropagation, set::Set, Lattice, Product},
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Origin {
    Parameter(usize),
    CallResult(Node, Ident),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Source {
    reg: RTLReg,
    origin: Origin,
    ty: TypeTerm,
    bits: u32,
}

#[derive(Clone, Debug)]
pub(super) struct Hint {
    pub value: RTLReg,
    ty: TypeTerm,
    sources: Set<Source>,
}

// Derived invariants cannot be copied into a finer value partition. Recompute
// them from raw definitions/transfers after the binding projection.
pub(super) const HINTS: ArtifactKey<Vec<Hint>> =
    ArtifactKey::projected("transported-type-evidence", |_, _| Vec::new());

// Keep provenance orthogonal to agreement: two parameters of the same type
// agree on a declaration without claiming that they have the same VALUE.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Evidence {
    shape: ConstPropagation<(TypeTerm, u32)>,
    sources: Set<Source>,
}

impl PartialOrd for Evidence {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Product((&self.shape, &self.sources)).partial_cmp(&Product((&other.shape, &other.sources)))
    }
}

impl Lattice for Evidence {
    fn join_mut(&mut self, other: Self) -> bool {
        // Both coordinates must be updated, even if the first one changes.
        self.shape.join_mut(other.shape) | self.sources.join_mut(other.sources)
    }
    fn meet_mut(&mut self, other: Self) -> bool {
        self.shape.meet_mut(other.shape) | self.sources.meet_mut(other.sources)
    }
}

fn seed(source: Source) -> Evidence {
    Evidence {
        shape: ConstPropagation::Constant((source.ty.clone(), source.bits)),
        sources: Set::singleton(source),
    }
}

fn unknown() -> Evidence {
    Evidence {
        shape: ConstPropagation::Top,
        sources: Set::default(),
    }
}

fn transport(evidence: &Evidence, bits: u32) -> Evidence {
    match &evidence.shape {
        ConstPropagation::Constant((_, width)) if *width != bits => unknown(),
        _ => evidence.clone(),
    }
}

ascent! {
    struct Transport;
    relation edge(RTLReg, RTLReg, u32);
    lattice evidence(RTLReg, Evidence);
    evidence(*destination, transport(source, *bits)) <--
        edge(input, destination, bits), evidence(input, source);
}

fn precise(xtype: XType, model: crate::abi::DataModel) -> Option<TypeTerm> {
    if matches!(
        xtype,
        XType::Xvoid
            | XType::Xany32
            | XType::Xany64
            | XType::Xptr
            | XType::Xfloat
            | XType::Xsingle
            | XType::Xfuncptr
    ) {
        return None;
    }
    let term = TypeTerm::from_candidate(CandType::from_xtype(&xtype), model);
    (term.is_integer() || term.is_pointer()).then_some(term)
}

fn parameter(function: &FunctionData, position: usize) -> Option<TypeTerm> {
    let parameter = function.param_types.get(position)?;
    match parameter {
        ParamType::Typed(xtype) => precise(*xtype, function.data_model),
        ParamType::StructPointer(_) => TypeTerm::from_c(
            &convert_param_type_from_param(parameter, function.data_model),
            function.data_model,
        ),
        _ => None,
    }
}

fn direct_callee(expression: &ClightExpr) -> Option<Ident> {
    match expression {
        ClightExpr::Evar(id, _) => Some(*id),
        ClightExpr::Ecast(inner, _) => direct_callee(inner),
        _ => None,
    }
}

pub(super) fn apply(
    function: &mut FunctionData,
    graph: &mut EvidenceGraph,
    nodes: &BTreeSet<Node>,
    definitions: &BTreeMap<Node, BTreeSet<RTLReg>>,
    native: &BTreeMap<Node, Option<RTLInst>>,
) {
    let mut defs = BTreeMap::<RTLReg, BTreeSet<Node>>::new();
    for node in nodes {
        for &reg in definitions.get(node).into_iter().flatten() {
            defs.entry(reg).or_default().insert(*node);
        }
    }
    let parameters: BTreeSet<_> = function.param_regs.iter().copied().collect();
    let mut program = Transport::default();
    let mut covered = BTreeSet::new();
    let mut tracked = parameters.clone();
    let mut seeded_parameters = BTreeSet::new();
    for (position, &reg) in function.param_regs.iter().enumerate() {
        let Some(ty) = parameter(function, position) else {
            continue;
        };
        let Some(bytes) = ty.object_bytes(function.data_model) else {
            continue;
        };
        seeded_parameters.insert(reg);
        program.evidence.push((
            reg,
            seed(Source {
                reg,
                origin: Origin::Parameter(position),
                ty,
                bits: (bytes * 8) as u32,
            }),
        ));
    }
    for (&node, candidates) in &function.node_statements {
        let Some(Some(RTLInst::Icall(_, _, _, Some(destination), _))) = native.get(&node) else {
            continue;
        };
        let mut calls = BTreeSet::new();
        let complete = candidates.iter().all(|statement| {
            let ClightStmt::Scall(Some(dst), callee, _) =
                crate::decompile::passes::clight_select::solvers::memory_theory::primitive(
                    statement,
                )
            else {
                return false;
            };
            let Some(callee) = direct_callee(callee) else {
                return false;
            };
            calls.insert((*dst as RTLReg, callee));
            true
        });
        if !complete || calls.len() != 1 {
            continue;
        }
        let &(dst, callee) = calls.first().unwrap();
        if dst != *destination {
            continue;
        }
        let Some(signature) = function.callee_signatures.get(&callee) else {
            continue;
        };
        let Some(ty) = precise(signature.return_type, function.data_model) else {
            continue;
        };
        let Some(bytes) = ty.object_bytes(function.data_model) else {
            continue;
        };
        covered.insert((node, dst));
        tracked.insert(dst);
        program.evidence.push((
            dst,
            seed(Source {
                reg: dst,
                origin: Origin::CallResult(node, callee),
                ty,
                bits: (bytes * 8) as u32,
            }),
        ));
    }
    for copy in crate::decompile::passes::clight_select::solvers::transfers::COPIES
        .get(&function.analysis_facts)
        .into_iter()
        .flat_map(|c| c.values())
    {
        tracked.extend([copy.source, copy.destination]);
        if !nodes.contains(&copy.node)
            || !defs
                .get(&copy.destination)
                .is_some_and(|ds| ds.contains(&copy.node))
            || !matches!(native.get(&copy.node).and_then(Option::as_ref),
                Some(RTLInst::Iop(crate::x86::op::Operation::Omove, inputs, destination))
                    if inputs.as_slice() == [copy.source] && *destination == copy.destination)
            || graph.fixed_storage.contains(&copy.source)
            || graph.fixed_storage.contains(&copy.destination)
            || graph.unknown_storage.contains(&copy.source)
            || graph.unknown_storage.contains(&copy.destination)
            || copy.memory_input.is_some_and(|(bits, _)| bits != copy.bits)
        {
            continue;
        }
        covered.insert((copy.node, copy.destination));
        program
            .edge
            .push((copy.source, copy.destination, copy.bits));
    }
    for reg in tracked {
        // No missing definition is Bottom ("not visited yet"). Unaccounted
        // definitions poison the invariant, including writers on other arms.
        // An unseeded cycle remains Bottom and therefore invents no evidence.
        if graph.fixed_storage.contains(&reg)
            || graph.unknown_storage.contains(&reg)
            || (parameters.contains(&reg) && !seeded_parameters.contains(&reg))
            || (!parameters.contains(&reg) && !defs.contains_key(&reg))
            || defs
                .get(&reg)
                .into_iter()
                .flatten()
                .any(|node| !covered.contains(&(*node, reg)))
        {
            program.evidence.push((reg, unknown()));
        }
    }
    program.run();
    let mut hints = Vec::new();
    for (value, evidence) in program.evidence {
        let Evidence {
            shape: ConstPropagation::Constant((ty, _)),
            sources,
        } = evidence
        else {
            continue;
        };
        if graph.fixed.contains(&value) || sources.0.iter().all(|source| source.reg == value) {
            continue;
        }
        graph
            .hypotheses
            .entry(value)
            .or_default()
            .insert(ty.clone());
        hints.push(Hint { value, ty, sources });
    }
    hints.sort_by_key(|hint| hint.value);
    if HINTS.get(&function.analysis_facts).is_some() {
        HINTS.rebind(&mut function.analysis_facts, hints);
    } else {
        HINTS.insert(&mut function.analysis_facts, hints);
    }
}

impl Hint {
    pub(super) fn ty(&self) -> &TypeTerm {
        &self.ty
    }

    /// Stage C may replace an interface after preparation. Never keep a
    /// transported hint whose source interface is no longer the selected one.
    pub(super) fn active(&self, cx: &DeclarationContext<'_>) -> bool {
        self.sources.0.iter().all(|source| {
            let actual = match source.origin {
                Origin::Parameter(position) => {
                    if let Some((_, xtype)) = cx.pins.iter().find(|(reg, _)| *reg == source.reg) {
                        precise(*xtype, cx.function.data_model)
                    } else {
                        parameter(cx.function, position)
                    }
                }
                Origin::CallResult(_, callee) => cx
                    .function
                    .callee_signatures
                    .get(&callee)
                    .and_then(|signature| precise(signature.return_type, cx.function.data_model)),
            };
            actual.as_ref() == Some(&self.ty)
        })
    }
}

pub(super) fn supported(cx: &DeclarationContext<'_>, reg: RTLReg) -> Vec<TypeTerm> {
    HINTS
        .get(&cx.function.analysis_facts)
        .into_iter()
        .flatten()
        .filter(|hint| hint.value == reg && hint.active(cx))
        .map(|hint| hint.ty.clone())
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::decompile::passes::clight_select::solvers::integer_semantics::CopyValue;
    use crate::decompile::passes::clight_select::syntax::type_flow::*;
    use crate::x86::op::Operation;
    use std::sync::Arc;

    #[test]
    fn hashed_evidence_preserves_product_order_and_updates_both_coordinates() {
        let source = Source {
            reg: 10,
            origin: Origin::Parameter(0),
            ty: TypeTerm::from_candidate(CandType::PtrChar, crate::abi::DataModel::Lp64),
            bits: 64,
        };
        let precise = seed(source.clone());
        let unknown = unknown();
        assert_eq!(
            precise.partial_cmp(&unknown),
            None,
            "product order must not become lexicographic"
        );
        let mut joined = precise.clone();
        assert!(joined.join_mut(unknown));
        assert_eq!(joined.shape, ConstPropagation::Top);
        assert!(joined.sources.0.contains(&source));
        let mut set = std::collections::HashSet::new();
        set.insert(joined.clone());
        assert!(set.contains(&joined));
    }

    #[test]
    fn different_origins_of_one_type_agree_without_becoming_one_value() {
        let ty = TypeTerm::from_candidate(CandType::PtrChar, crate::abi::DataModel::Lp64);
        let mut program = Transport::default();
        for _ in 0..5 {
            program.evidence.push((
                10,
                seed(Source {
                    reg: 10,
                    origin: Origin::Parameter(0),
                    ty: ty.clone(),
                    bits: 64,
                }),
            ));
        }
        program.evidence.push((
            20,
            seed(Source {
                reg: 20,
                origin: Origin::Parameter(1),
                ty,
                bits: 64,
            }),
        ));
        program
            .edge
            .extend([(10, 30, 64), (20, 30, 64), (30, 40, 64)]);
        program.run();
        let (
            _,
            Evidence {
                shape,
                sources: origins,
            },
        ) = program.evidence.iter().find(|(reg, _)| *reg == 40).unwrap();
        assert!(matches!(shape, ConstPropagation::Constant(_)));
        assert_eq!(origins.0.len(), 2, "repeated facts are not extra votes");
    }

    #[test]
    fn interface_type_survives_full_width_spills_but_not_truncation_or_mutation() {
        let mut f = FunctionData::new(
            1,
            "transport".into(),
            vec![10],
            vec![ParamType::Typed(XType::Xcharptr)],
            None,
            0,
            100,
            true,
        );
        let copies = [
            (90, 10, 20, 64),
            (4, 20, 30, 64),
            (80, 30, 40, 32),
            (7, 30, 50, 64),
        ];
        let mut native = BTreeMap::new();
        let mut definitions = BTreeMap::<Node, BTreeSet<RTLReg>>::new();
        let mut contracts = BTreeMap::new();
        for (node, source, destination, bits) in copies {
            native.insert(
                node,
                Some(RTLInst::Iop(
                    Operation::Omove,
                    Arc::new(vec![source]),
                    destination,
                )),
            );
            definitions.entry(node).or_default().insert(destination);
            contracts.insert(
                node,
                CopyValue {
                    node,
                    source,
                    destination,
                    bits,
                    storage: true,
                    memory_input: None,
                },
            );
        }
        definitions.entry(8).or_default().insert(50);
        crate::decompile::passes::clight_select::solvers::transfers::COPIES
            .insert(&mut f.analysis_facts, contracts);
        let mut graph = EvidenceGraph::default();
        apply(
            &mut f,
            &mut graph,
            &BTreeSet::from([90, 4, 80, 7, 8]),
            &definitions,
            &native,
        );
        let pointer = TypeTerm::from_candidate(CandType::PtrChar, f.data_model);
        assert!(graph.hypotheses[&20].contains(&pointer));
        assert!(graph.hypotheses[&30].contains(&pointer));
        assert!(!graph.hypotheses.contains_key(&40));
        assert!(!graph.hypotheses.contains_key(&50));
    }

    fn joined_copies(
        second: XType,
        extra_writer: bool,
        reversed: bool,
    ) -> (FunctionData, EvidenceGraph) {
        let mut function = FunctionData::new(
            1,
            "definition_closed".into(),
            vec![10, 11],
            vec![ParamType::Typed(XType::Xcharptr), ParamType::Typed(second)],
            None,
            0,
            90,
            true,
        );
        // Deliberately unordered node ids. The declaration has two incoming
        // definitions and a copy cycle, not a fabricated address-order path.
        let mut copies = vec![(90, 10, 20), (4, 11, 20), (80, 20, 30), (7, 30, 20)];
        if reversed {
            copies.reverse();
        }
        let mut native = BTreeMap::new();
        let mut definitions = BTreeMap::<Node, BTreeSet<RTLReg>>::new();
        let mut contracts = BTreeMap::new();
        for (node, source, destination) in copies {
            native.insert(
                node,
                Some(RTLInst::Iop(
                    Operation::Omove,
                    Arc::new(vec![source]),
                    destination,
                )),
            );
            definitions.entry(node).or_default().insert(destination);
            contracts.insert(
                node,
                CopyValue {
                    node,
                    source,
                    destination,
                    bits: 64,
                    storage: true,
                    memory_input: None,
                },
            );
        }
        if extra_writer {
            native.insert(
                6,
                Some(RTLInst::Iop(Operation::Ointconst(1), Arc::new(vec![]), 20)),
            );
            definitions.entry(6).or_default().insert(20);
        }
        crate::decompile::passes::clight_select::solvers::transfers::COPIES
            .insert(&mut function.analysis_facts, contracts);
        let nodes = native.keys().copied().collect();
        let mut graph = EvidenceGraph::default();
        apply(&mut function, &mut graph, &nodes, &definitions, &native);
        (function, graph)
    }

    #[test]
    fn complete_agreeing_definitions_transport_through_copy_cycles() {
        for reversed in [false, true] {
            let (function, graph) = joined_copies(XType::Xcharptr, false, reversed);
            let ty = TypeTerm::from_candidate(CandType::PtrChar, function.data_model);
            assert_eq!(graph.hypotheses[&20], BTreeSet::from([ty.clone()]));
            assert_eq!(graph.hypotheses[&30], BTreeSet::from([ty]));
            let hints = HINTS.get(&function.analysis_facts).unwrap();
            assert_eq!(
                hints
                    .iter()
                    .find(|h| h.value == 30)
                    .unwrap()
                    .sources
                    .0
                    .len(),
                2
            );
        }
    }

    #[test]
    fn one_unknown_or_conflicting_definition_poison_the_whole_invariant() {
        for (second, extra) in [
            (XType::Xintptr, false),
            (XType::Xptr, false),
            (XType::Xcharptr, true),
        ] {
            let (_, graph) = joined_copies(second, extra, false);
            assert!(!graph.hypotheses.contains_key(&20));
            assert!(!graph.hypotheses.contains_key(&30));
        }
    }

    #[test]
    fn a_width_changing_arm_is_unknown_not_an_absent_vote() {
        let ty = TypeTerm::from_candidate(CandType::PtrChar, crate::abi::DataModel::Lp64);
        let mut program = Transport::default();
        program.evidence.push((
            10,
            seed(Source {
                reg: 10,
                origin: Origin::Parameter(0),
                ty,
                bits: 64,
            }),
        ));
        program
            .edge
            .extend([(10, 20, 64), (10, 20, 32), (20, 30, 64)]);
        program.run();
        assert!(program
            .evidence
            .iter()
            .any(|(reg, evidence)| *reg == 30 && evidence.shape == ConstPropagation::Top));
    }

    #[test]
    fn changing_any_interface_invalidates_agreed_evidence() {
        let (mut function, _) = joined_copies(XType::Xcharptr, false, false);
        let types = crate::decompile::passes::clight_select::syntax::c_types::TypeDt::build();
        let active = |function: &FunctionData| {
            let cx = DeclarationContext {
                types: &types,
                function,
                pins: &[],
                interfaces: &crate::decompile::passes::clight_select::syntax::interfaces::InterfaceTerms::default(),
            };
            supported(&cx, 30)
        };
        assert_eq!(active(&function).len(), 1);
        function.param_types[1] = ParamType::Typed(XType::Xintptr);
        assert!(active(&function).is_empty());
    }
}
