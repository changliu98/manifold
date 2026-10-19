//! Evidence collection and a corpus-independent representation policy.
//! Evidence is attached to storage, values, views, or committed interfaces;
//! hypotheses never become machine facts merely by being selected.

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::c_pass::types::*;
use crate::decompile::passes::clight_select::syntax::ArtifactKey;
use crate::decompile::passes::clight_select::{
    candtype::{CandType, Sign},
    query::FunctionData,
    type_graph::*,
};
use crate::mreg::Mreg;
use crate::x86::{op::Addressing, types::*};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

pub(crate) const GRAPH: ArtifactKey<EvidenceGraph> = ArtifactKey::projected(
    "type-evidence",
    crate::decompile::passes::clight_select::syntax::bindings::remap_graph,
);
pub(crate) const COMMITMENTS: ArtifactKey<BTreeMap<RTLReg, TypeTerm>> =
    ArtifactKey::new("type-commitments");
pub(crate) const ADMISSIONS: ArtifactKey<BTreeMap<RTLReg, TypeAdmission>> =
    ArtifactKey::new("type-admissions");
pub(crate) const INPUTS: &[&str] = &[
    "type_storage_access",
    "emit_var_type_candidate",
    "rtl_inst",
    "ltl_inst",
    "machine_register_write_view",
    "instr_in_function",
    "stack_struct_buffers",
    "stack_array_buffers",
    "slot_escaped_canonical",
    "slot_escaped_region_canonical",
    "stack_var",
    "escaped_stack_region_field",
    "escaped_stack_region_caller_field",
    "escaped_stack_region_extent",
    "stack_buffer_alias",
    "stack_buffer_end_alias",
    "stack_buffer_address_root",
];

fn chunk_types(chunk: MemoryChunk, model: crate::abi::DataModel) -> Vec<TypeTerm> {
    let widths = match chunk {
        MemoryChunk::MBool => return vec![TypeTerm::Bool],
        MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned => 8,
        MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned => 16,
        MemoryChunk::MInt32 | MemoryChunk::MAny32 => 32,
        MemoryChunk::MInt64 | MemoryChunk::MAny64 => 64,
        MemoryChunk::MFloat32 => return vec![TypeTerm::Float(32)],
        MemoryChunk::MFloat64 => return vec![TypeTerm::Float(64)],
        MemoryChunk::Unknown => return vec![],
    };
    [Sign::Signed, Sign::Unsigned]
        .into_iter()
        .filter_map(|s| TypeTerm::integer(widths, s, model))
        .collect()
}

/// Hypotheses grounded in value or storage evidence. A dereference width
/// describes an access view, not the pointee's source type, so PointerAccess
/// alone deliberately does not confer this status.
pub(crate) fn supported_terms(
    graph: &EvidenceGraph,
    reg: RTLReg,
    model: crate::abi::DataModel,
) -> BTreeSet<TypeTerm> {
    let mut result = BTreeSet::new();
    let generic = TypeTerm::from_candidate(CandType::PtrLong, model);
    let opaque = TypeTerm::from_candidate(CandType::PtrVoid, model);
    for fact in &graph.facts {
        match fact {
            Fact::ValueHint { value, ty } if *value == reg && *ty != generic && *ty != opaque => {
                if ty.is_integer() || ty.is_pointer() {
                    result.insert(ty.clone());
                }
            }
            Fact::Access { object, chunk, .. }
                if *object == reg && !graph.unknown_storage.contains(&reg) =>
            {
                result.extend(
                    chunk_types(*chunk, model)
                        .into_iter()
                        .filter(TypeTerm::is_integer),
                );
            }
            _ => {}
        }
    }
    result
}

/// Physical storage evidence is class-neutral: an eight-byte access supports
/// eight bytes of storage, not an integer instead of a pointer. Keep this
/// ranking fact separate from admission of a concrete spelling.
pub(crate) fn storage_widths(graph: &EvidenceGraph, reg: RTLReg) -> BTreeSet<usize> {
    graph
        .facts
        .iter()
        .filter_map(|fact| match fact {
            Fact::Access { object, chunk, .. }
                if *object == reg
                    && *chunk != MemoryChunk::Unknown
                    && !graph.unknown_storage.contains(&reg) =>
            {
                Some(crate::decompile::analysis::struct_recovery_pass::chunk_byte_size(chunk))
            }
            _ => None,
        })
        .collect()
}

/// Specific value alternatives form one disjunction, never a conditional
/// reward for leaving their class. A machine-word integer hint can originate
/// from an untyped ABI/storage floor and is not positive class evidence.
pub(crate) fn value_hints(
    graph: &EvidenceGraph,
    reg: RTLReg,
    model: crate::abi::DataModel,
) -> BTreeSet<TypeTerm> {
    let generic = TypeTerm::from_candidate(CandType::PtrLong, model);
    let opaque = TypeTerm::from_candidate(CandType::PtrVoid, model);
    graph
        .facts
        .iter()
        .filter_map(|fact| match fact {
            Fact::ValueHint { value, ty }
                if *value == reg
                    && *ty != generic
                    && *ty != opaque
                    && (!ty.is_integer()
                        || ty
                            .object_bytes(model)
                            .is_some_and(|n| n < model.pointer_size())) =>
            {
                Some(ty.clone())
            }
            _ => None,
        })
        .collect()
}

#[cfg(test)]
pub(crate) fn collect(db: &DecompileDB, functions: &mut [FunctionData]) {
    collect_raw(db, functions);
    finalize(db, functions);
}

/// Keep hypotheses and site-local observations until value identities are
/// established. In particular, do not join type-flow conflicts or prune an
/// entire native name before its independent definition webs are separated.
pub(super) fn collect_raw(db: &DecompileDB, functions: &mut [FunctionData]) {
    let (escaped_arrays, escaped_buffers) =
        crate::decompile::passes::c_pass::convert::from_relations::escaped_stack_layouts(db);
    let mut projected_storage = BTreeMap::<Address, BTreeSet<RTLReg>>::new();
    for name in ["stack_buffer_alias", "stack_buffer_end_alias"] {
        for &(function, member, root, _) in db.rel_iter::<(Address, RTLReg, RTLReg, usize)>(name) {
            projected_storage
                .entry(function)
                .or_default()
                .extend([member, root]);
        }
    }
    for &(function, root) in db.rel_iter::<(Address, RTLReg)>("stack_buffer_address_root") {
        projected_storage.entry(function).or_default().insert(root);
    }
    // These are storage owners in the existing layout projection, not free
    // scalar declarations. Keep every SSA version of an escaped cell out of
    // scalar recovery; do not freeze an integer spelling over a byte object.
    let mut escaped = BTreeMap::<Address, BTreeSet<RTLReg>>::new();
    let mut escaped_cells = BTreeSet::new();
    for relation in ["slot_escaped_canonical", "slot_escaped_region_canonical"] {
        for &(function, offset, reg) in db.rel_iter::<(Address, i64, RTLReg)>(relation) {
            escaped.entry(function).or_default().insert(reg);
            escaped_cells.insert((function, offset));
        }
    }
    for &(function, _, offset, reg) in db.rel_iter::<(Address, Node, i64, RTLReg)>("stack_var") {
        if escaped_cells.contains(&(function, offset)) {
            escaped.entry(function).or_default().insert(reg);
        }
    }
    let mut storage = BTreeMap::<Address, Vec<Fact>>::new();
    for &(function, node, object, offset, write, chunk) in
        db.rel_iter::<(Address, Node, RTLReg, i64, bool, MemoryChunk)>("type_storage_access")
    {
        storage.entry(function).or_default().push(Fact::Access {
            object,
            node,
            offset,
            write,
            chunk,
        });
    }
    let mut raw = BTreeMap::<RTLReg, BTreeSet<CandType>>::new();
    for &(reg, ty) in db.rel_iter::<(RTLReg, XType)>("emit_var_type_candidate") {
        raw.entry(reg)
            .or_default()
            .insert(CandType::from_xtype(&ty));
    }
    let mut rtl = BTreeMap::<Node, Option<RTLInst>>::new();
    let mut definitions = BTreeMap::<Node, BTreeSet<RTLReg>>::new();
    for (node, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        if let Some(reg) = crate::decompile::passes::rtl_optimize_pass::inst_def_use(inst).0 {
            definitions.entry(*node).or_default().insert(reg);
        }
        rtl.entry(*node)
            .and_modify(|old| {
                if old.as_ref() != Some(inst) {
                    *old = None;
                }
            })
            .or_insert_with(|| Some(inst.clone()));
    }
    let mut decoded = BTreeMap::<(Node, Mreg), BTreeSet<u32>>::new();
    for &(node, reg, bits) in db.rel_iter::<(Node, Mreg, u32)>("machine_register_write_view") {
        decoded.entry((node, reg)).or_default().insert(bits);
    }
    let mut destinations = BTreeMap::<Node, BTreeSet<Mreg>>::new();
    for (node, inst) in db.rel_iter::<(Node, LTLInst)>("ltl_inst") {
        if let LTLInst::Lop(_, _, dst)
        | LTLInst::Lload(_, _, _, dst)
        | LTLInst::Lgetstack(_, _, _, dst) = inst
        {
            destinations.entry(*node).or_default().insert(*dst);
        }
    }
    let mut function_nodes = BTreeMap::<Address, BTreeSet<Node>>::new();
    for &(node, f) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        function_nodes.entry(f).or_default().insert(node);
    }
    for function in functions {
        let mut graph = EvidenceGraph::default();
        graph.fixed_storage.extend(
            projected_storage
                .get(&function.address)
                .into_iter()
                .flatten(),
        );
        graph.fixed.extend(&graph.fixed_storage);
        graph.fixed.extend(&function.param_regs);
        graph
            .fixed_storage
            .extend(escaped.get(&function.address).into_iter().flatten());
        graph
            .fixed
            .extend(escaped.get(&function.address).into_iter().flatten());
        let model = function.data_model;
        let relevant: BTreeSet<_> = function
            .used_regs
            .iter()
            .chain(function.var_type_candidates.keys())
            .chain(function.var_types.keys())
            .copied()
            .collect();
        for &reg in &relevant {
            graph.entities.insert(Entity::Value(reg));
            for &candidate in raw.get(&reg).into_iter().flatten() {
                graph.facts.insert(Fact::ValueHint {
                    value: reg,
                    ty: TypeTerm::from_candidate(candidate, model),
                });
            }
        }
        for fact in storage.get(&function.address).into_iter().flatten() {
            let Fact::Access {
                object,
                node,
                offset,
                write,
                chunk,
            } = *fact
            else {
                unreachable!()
            };
            graph.entities.insert(Entity::Storage(object));
            graph
                .entities
                .insert(Entity::Access(node, object, offset, write));
            graph.facts.insert(fact.clone());
            if chunk == MemoryChunk::Unknown {
                graph.unknown_storage.insert(object);
            }
            if relevant.contains(&object) {
                graph
                    .hypotheses
                    .entry(object)
                    .or_default()
                    .extend(chunk_types(chunk, model));
            }
        }
        for (position, (&reg, parameter)) in function
            .param_regs
            .iter()
            .zip(&function.param_types)
            .enumerate()
        {
            graph.entities.insert(Entity::Parameter(position));
            graph.fixed.insert(reg);
            let c = crate::decompile::passes::c_pass::convert::from_relations::convert_param_type_from_param(parameter, model);
            if let Some(ty) = TypeTerm::from_c(&c, model) {
                graph.facts.insert(Fact::Interface {
                    parameter: Some(position),
                    value: Some(reg),
                    ty,
                });
            }
        }
        graph.entities.insert(Entity::Return);
        if let Some(ty) = TypeTerm::from_c(
            &crate::decompile::passes::c_pass::convert::from_relations::convert_clight_type(
                &function.return_type,
                model,
            ),
            model,
        ) {
            graph.facts.insert(Fact::Interface {
                parameter: None,
                value: None,
                ty,
            });
        }
        for (root, extent) in db
            .stack_struct_buffers
            .get(&function.address)
            .into_iter()
            .flatten()
        {
            graph.fixed.insert(*root);
            graph.fixed_storage.insert(*root);
            graph.facts.insert(Fact::Layout {
                object: *root,
                ty: TypeTerm::Array(
                    Arc::new(TypeTerm::Integer(IntSize::Char, Sign::Unsigned)),
                    usize::try_from(*extent).ok(),
                ),
            });
        }
        // These layouts used to be discovered only by the emitter. Include
        // both the owners and every absorbed SSA name in the same storage
        // vocabulary before allowing a scalar declaration choice.
        for (&root, &extent) in escaped_buffers
            .buffers
            .get(&function.address)
            .into_iter()
            .flatten()
        {
            graph.fixed.insert(root);
            graph.fixed_storage.insert(root);
            graph.facts.insert(Fact::Layout {
                object: root,
                ty: TypeTerm::Array(
                    Arc::new(TypeTerm::Integer(IntSize::Char, Sign::Unsigned)),
                    Some(extent),
                ),
            });
        }
        for &member in escaped_buffers
            .members
            .get(&function.address)
            .into_iter()
            .flat_map(|m| m.keys())
        {
            graph.fixed.insert(member);
            graph.fixed_storage.insert(member);
        }
        for &member in escaped_arrays
            .members
            .get(&function.address)
            .into_iter()
            .flat_map(|m| m.keys())
        {
            graph.fixed.insert(member);
            graph.fixed_storage.insert(member);
        }
        for (root, (chunk, count)) in db
            .stack_array_buffers
            .get(&function.address)
            .into_iter()
            .flatten()
            .chain(
                escaped_arrays
                    .arrays
                    .get(&function.address)
                    .into_iter()
                    .flatten(),
            )
        {
            graph.fixed.insert(*root);
            graph.fixed_storage.insert(*root);
            if let Some(element) = chunk_types(*chunk, model).first() {
                graph.facts.insert(Fact::Layout {
                    object: *root,
                    ty: TypeTerm::Array(Arc::new(element.clone()), Some(*count)),
                });
            }
        }
        // Fixed memory owners keep their allocation contract. Independent
        // scalar values in the same function remain eligible for inference.
        for write in &function.storage_writes {
            graph.fixed.insert(write.root);
            graph.fixed.extend(&write.locals);
            graph.fixed_storage.insert(write.root);
            graph.fixed_storage.extend(&write.locals);
        }
        for read in &function.storage_reads {
            graph.fixed.insert(read.root);
            graph.fixed_storage.insert(read.root);
        }
        graph.fixed.extend(function.reg_struct_ids.keys());
        for &node in function_nodes.get(&function.address).into_iter().flatten() {
            for &reg in definitions.get(&node).into_iter().flatten() {
                if relevant.contains(&reg) {
                    graph.facts.insert(Fact::Definition { node, value: reg });
                    // A declaration invariant must be closed under every
                    // native definition. A missing/ambiguous projection is a
                    // coverage gap, not permission to narrow its value domain.
                    if !function.node_statements.contains_key(&node)
                        || rtl.get(&node).is_none_or(|i| i.is_none())
                    {
                        graph.unknown_values.insert(reg);
                    }
                }
            }
            let Some(Some(inst)) = rtl.get(&node) else {
                continue;
            };
            if let Some(reg) = crate::decompile::passes::rtl_optimize_pass::inst_def_use(inst).0 {
                if let Some(bits) = destinations
                    .get(&node)
                    .filter(|s| s.len() == 1)
                    .and_then(|s| s.first())
                    .and_then(|r| decoded.get(&(node, *r)))
                    .filter(|s| s.len() == 1)
                    .and_then(|s| s.first())
                {
                    graph.facts.insert(Fact::Carrier {
                        node,
                        value: reg,
                        bits: *bits,
                    });
                    // A carrier alone does not prove integer-ness. Existing
                    // integer-only value hypotheses permit width alternatives.
                    if relevant.contains(&reg)
                        && raw
                            .get(&reg)
                            .is_some_and(|ts| !ts.is_empty() && ts.iter().all(|t| t.is_integer()))
                    {
                        graph.hypotheses.entry(reg).or_default().extend(
                            [Sign::Signed, Sign::Unsigned]
                                .into_iter()
                                .filter_map(|s| TypeTerm::integer(*bits, s, model)),
                        );
                    }
                }
            }
            // A typed memory view proposes a pointee interpretation, not an
            // allocation extent or proof that the object has this exact type.
            let access = match inst {
                RTLInst::Iload(chunk, Addressing::Aindexed(offset), args, _) if args.len() == 1 => {
                    Some((*chunk, args[0], *offset, false))
                }
                RTLInst::Istore(chunk, Addressing::Aindexed(offset), args, _)
                    if args.len() == 1 =>
                {
                    Some((*chunk, args[0], *offset, true))
                }
                _ => None,
            };
            if let Some((chunk, base, offset, write)) =
                access.filter(|(_, r, _, _)| relevant.contains(r))
            {
                graph
                    .entities
                    .insert(Entity::Access(node, base, offset, write));
                graph.facts.insert(Fact::PointerAccess {
                    node,
                    base,
                    offset,
                    write,
                    chunk,
                });
                for term in chunk_types(chunk, model) {
                    graph
                        .hypotheses
                        .entry(base)
                        .or_default()
                        .insert(term.pointer());
                }
            }
        }
        for &reg in &relevant {
            let Some(hints) = raw.get(&reg) else {
                continue;
            };
            let concrete: Vec<_> = hints
                .iter()
                .filter(|c| c.is_pointer() && **c != CandType::PtrLong && **c != CandType::PtrVoid)
                .copied()
                .collect();
            if !concrete.is_empty() {
                graph.hypotheses.entry(reg).or_default().extend(
                    concrete
                        .into_iter()
                        .map(|c| TypeTerm::from_candidate(c, model)),
                );
            }
        }
        graph.hypotheses.retain(|reg, _| !graph.fixed.contains(reg));
        GRAPH.insert(&mut function.analysis_facts, graph);
    }
}

/// Infer declaration invariants in the final binding vocabulary. Native
/// origins stay intact; only read/write value identities are projected.
pub(super) fn finalize(db: &DecompileDB, functions: &mut [FunctionData]) {
    let mut native = BTreeMap::<Node, Option<RTLInst>>::new();
    let mut definitions = BTreeMap::<Node, BTreeSet<RTLReg>>::new();
    for (node, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        if let Some(reg) = crate::decompile::passes::rtl_optimize_pass::inst_def_use(inst).0 {
            definitions.entry(*node).or_default().insert(reg);
        }
        native
            .entry(*node)
            .and_modify(|old| {
                if old.as_ref() != Some(inst) {
                    *old = None;
                }
            })
            .or_insert_with(|| Some(inst.clone()));
    }
    let mut owners = BTreeMap::<Address, BTreeSet<Node>>::new();
    for &(node, owner) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        owners.entry(owner).or_default().insert(node);
    }
    for function in functions {
        let Some(mut graph) = GRAPH.get(&function.analysis_facts).cloned() else {
            continue;
        };
        let plan = crate::decompile::passes::clight_select::syntax::bindings::PLAN
            .get(&function.analysis_facts)
            .cloned()
            .unwrap_or_default();
        let nodes = owners.get(&function.address).cloned().unwrap_or_default();
        let rtl: BTreeMap<_, _> = nodes
            .iter()
            .filter_map(|node| {
                native
                    .get(node)
                    .map(|inst| (*node, inst.as_ref().map(|i| plan.native(*node, i))))
            })
            .collect();
        let defs: BTreeMap<_, BTreeSet<_>> = nodes
            .iter()
            .filter_map(|node| {
                definitions
                    .get(node)
                    .map(|regs| (*node, regs.iter().map(|r| plan.write(*node, *r)).collect()))
            })
            .collect();
        // Unknown coverage is a property of an individual binding's sites,
        // not a bit to donate to all descendants of the old register name.
        graph.unknown_values = defs
            .iter()
            .filter(|(node, _)| {
                !function.node_statements.contains_key(node)
                    || rtl.get(node).is_none_or(Option::is_none)
            })
            .flat_map(|(_, regs)| regs.iter().copied())
            .collect();
        graph.unknown_storage = graph
            .facts
            .iter()
            .filter_map(|fact| match fact {
                Fact::Access {
                    object,
                    chunk: MemoryChunk::Unknown,
                    ..
                } => Some(*object),
                _ => None,
            })
            .collect();
        let model = function.data_model;
        crate::decompile::passes::clight_select::syntax::type_flow::apply(
            function, &mut graph, &nodes, &defs, &rtl,
        );
        // Gaps forbid new representation inventions, not already-supported
        // type hypotheses. Keep the distinction explicit through selection.
        let supported: BTreeMap<_, _> = graph
            .hypotheses
            .keys()
            .map(|&reg| {
                let original: BTreeSet<_> = function
                    .var_type_candidates
                    .get(&reg)
                    .into_iter()
                    .flatten()
                    .chain(function.var_types.get(&reg))
                    .map(|c| TypeTerm::from_candidate(*c, model))
                    .collect();
                (
                    reg,
                    supported_terms(&graph, reg, model)
                        .intersection(&original)
                        .cloned()
                        .collect::<BTreeSet<_>>(),
                )
            })
            .collect();
        graph.hypotheses.retain(|reg, terms| {
            if graph.fixed.contains(reg) {
                return false;
            }
            if graph.unknown_storage.contains(reg) || graph.unknown_values.contains(reg) {
                terms.retain(|ty| supported[reg].contains(ty));
            }
            !terms.is_empty()
        });
        // Make singleton declarations visible to the common solver. The
        // declaration builder, not the evidence graph, supplies compatibility
        // fallbacks; candidate-domain padding must never become evidence.
        for (&reg, terms) in &mut graph.hypotheses {
            function.var_type_candidates.entry(reg).or_insert_with(|| {
                vec![function
                    .var_types
                    .get(&reg)
                    .copied()
                    .unwrap_or(CandType::I64(Sign::Signed))]
            });
            terms.retain(|t| t.is_integer() || t.is_pointer() || matches!(t, TypeTerm::Float(_)));
        }
        // Type changes need operation obligations even at singleton statement
        // nodes. Obligation coverage must not depend on candidate multiplicity.
        let managed: BTreeSet<_> = graph.hypotheses.keys().copied().collect();
        for (&node, statements) in &function.node_statements {
            let native_use = rtl.get(&node).and_then(Option::as_ref).is_some_and(|inst| {
                let (definition, uses) =
                    crate::decompile::passes::rtl_optimize_pass::inst_def_use(inst);
                definition
                    .into_iter()
                    .chain(uses)
                    .any(|reg| managed.contains(&reg))
            });
            if native_use
                || statements.iter().any(|s| {
                    crate::decompile::passes::clight_select::syntax::declarations::dependencies(s)
                        .iter()
                        .any(|r| managed.contains(r))
                })
            {
                if let Some(Some(inst @ (RTLInst::Iop(..) | RTLInst::Icond(..)))) = rtl.get(&node) {
                    function.integer_anchors.insert(node, inst.clone());
                }
            }
        }
        GRAPH.rebind(&mut function.analysis_facts, graph);
    }
}

/// One policy across corpora: count representation adapters for DISTINCT view
/// requirements. Repeating a fact or renaming/rebasing its site changes no cost.
/// This is a preference among admissible interpretations, never a type proof.
pub(crate) fn view_cost(
    graph: &EvidenceGraph,
    reg: RTLReg,
    term: &TypeTerm,
    model: crate::abi::DataModel,
) -> usize {
    #[derive(PartialEq, Eq, PartialOrd, Ord)]
    enum Requirement {
        Storage(usize),
        Carrier(u32),
        Pointee(Vec<TypeTerm>),
        Hint(TypeTerm),
    }
    let mut requirements = BTreeSet::new();
    for fact in &graph.facts {
        match fact {
            Fact::Access { object, chunk, .. }
                if *object == reg && *chunk != MemoryChunk::Unknown && term.is_integer() =>
            {
                requirements.insert(Requirement::Storage(
                    crate::decompile::analysis::struct_recovery_pass::chunk_byte_size(chunk),
                ));
            }
            Fact::Carrier { value, bits, .. } if *value == reg && term.is_integer() => {
                requirements.insert(Requirement::Carrier(*bits));
            }
            Fact::PointerAccess { base, chunk, .. }
                if *base == reg && *chunk != MemoryChunk::Unknown && term.is_pointer() =>
            {
                requirements.insert(Requirement::Pointee(chunk_types(*chunk, model)));
            }
            Fact::ValueHint { value, ty }
                if *value == reg && ty.is_pointer() && term.is_pointer() =>
            {
                if *ty != TypeTerm::from_candidate(CandType::PtrLong, model)
                    && *ty != TypeTerm::from_candidate(CandType::PtrVoid, model)
                {
                    requirements.insert(Requirement::Hint(ty.clone()));
                }
            }
            _ => {}
        }
    }
    requirements
        .iter()
        .filter(|r| match r {
            Requirement::Storage(bytes) => term.object_bytes(model) != Some(*bytes),
            Requirement::Carrier(bits) => term
                .object_bytes(model)
                .is_none_or(|b| (b * 8).max(32) != *bits as usize),
            Requirement::Pointee(views) => match term {
                TypeTerm::Pointer(inner) => !views.contains(inner),
                _ => false,
            },
            Requirement::Hint(expected) => term != expected,
        })
        .count()
}

#[cfg(test)]
mod tests {
    use crate::abi::DataModel;
    use crate::decompile::passes::clight_select::syntax::type_evidence::*;
    use crate::x86::op::Operation;

    #[test]
    fn representation_cost_is_invariant_to_names_addresses_and_repeated_views() {
        let ty = TypeTerm::integer(64, Sign::Signed, DataModel::Lp64).unwrap();
        let graph = |reg, nodes: &[u64]| EvidenceGraph {
            facts: nodes
                .iter()
                .map(|&node| Fact::Access {
                    object: reg,
                    node,
                    offset: -4,
                    write: true,
                    chunk: MemoryChunk::MInt32,
                })
                .collect(),
            ..Default::default()
        };
        assert_eq!(view_cost(&graph(7, &[10]), 7, &ty, DataModel::Lp64), 1);
        assert_eq!(
            view_cost(&graph(900, &[80, 90, 70, 80]), 900, &ty, DataModel::Lp64),
            1
        );
    }

    #[test]
    fn distinct_pointer_views_are_not_collapsed_into_one_boolean_mismatch() {
        let graph = EvidenceGraph {
            facts: [MemoryChunk::MInt8Unsigned, MemoryChunk::MInt16Unsigned]
                .into_iter()
                .enumerate()
                .map(|(i, chunk)| Fact::PointerAccess {
                    node: i as u64,
                    base: 7,
                    offset: 0,
                    write: false,
                    chunk,
                })
                .collect(),
            ..Default::default()
        };
        assert_eq!(
            view_cost(
                &graph,
                7,
                &TypeTerm::from_candidate(CandType::PtrLong, DataModel::Lp64),
                DataModel::Lp64
            ),
            2
        );
        assert_eq!(
            view_cost(
                &graph,
                7,
                &TypeTerm::from_candidate(CandType::PtrChar, DataModel::Lp64),
                DataModel::Lp64
            ),
            1
        );
    }

    #[test]
    fn singleton_operations_gain_obligations_from_unique_machine_carriers() {
        let mut db = DecompileDB::default();
        let op = Operation::Ointconst(42);
        let machine = Mreg::x86("EAX");
        db.rel_push(
            "rtl_inst",
            (10_u64, RTLInst::Iop(op.clone(), Arc::new(vec![]), 3)),
        );
        db.rel_push(
            "ltl_inst",
            (10_u64, LTLInst::Lop(op, Arc::new(vec![]), machine)),
        );
        db.rel_push("machine_register_write_view", (10_u64, machine, 32_u32));
        db.rel_push("instr_in_function", (10_u64, 1_u64));
        db.rel_push("emit_var_type_candidate", (3_u64, XType::Xint));
        let mut f = FunctionData::new(1, "arbitrary".into(), vec![], vec![], None, 0, 10, true);
        f.var_types.insert(3, CandType::I64(Sign::Unsigned));
        f.node_statements.insert(
            10,
            vec![ClightStmt::Sset(
                3,
                ClightExpr::EconstInt(
                    42,
                    ClightType::Tint(
                        ClightIntSize::I32,
                        ClightSignedness::Unsigned,
                        ClightAttr::default(),
                    ),
                ),
            )],
        );
        collect(&db, std::slice::from_mut(&mut f));
        assert!(f.integer_anchors.contains_key(&10));
        assert_eq!(
            GRAPH.get(&f.analysis_facts).unwrap().hypotheses[&3].len(),
            2
        );
    }

    #[test]
    fn an_unprojected_native_definition_is_an_explicit_coverage_gap() {
        let mut db = DecompileDB::default();
        db.rel_push(
            "type_storage_access",
            (1_u64, 10_u64, 3_u64, -4_i64, true, MemoryChunk::MInt32),
        );
        db.rel_push(
            "rtl_inst",
            (
                99_u64,
                RTLInst::Iop(Operation::Olongconst(0x100000000), Arc::new(vec![]), 3),
            ),
        );
        db.rel_push("instr_in_function", (99_u64, 1_u64));
        let mut f = FunctionData::new(
            1,
            "missing_projection".into(),
            vec![],
            vec![],
            None,
            0,
            10,
            true,
        );
        f.var_types.insert(3, CandType::I64(Sign::Signed));
        collect(&db, std::slice::from_mut(&mut f));
        let graph = GRAPH.get(&f.analysis_facts).unwrap();
        assert!(graph.unknown_values.contains(&3));
        assert!(!graph.hypotheses.contains_key(&3));
        assert!(
            !f.var_type_candidates.contains_key(&3),
            "a gap must not change the legacy declaration domain"
        );
    }

    #[test]
    fn an_escaped_object_does_not_exclude_independent_value_recovery() {
        let mut db = DecompileDB::default();
        db.rel_push("slot_escaped_canonical", (1_u64, -8_i64, 3_u64));
        for reg in [3_u64, 4] {
            db.rel_push(
                "type_storage_access",
                (1_u64, reg, reg, -(reg as i64), true, MemoryChunk::MInt32),
            );
        }
        let mut f = FunctionData::new(
            1,
            "independent_values".into(),
            vec![],
            vec![],
            None,
            0,
            10,
            true,
        );
        for reg in [3, 4] {
            f.var_types.insert(reg, CandType::I64(Sign::Signed));
        }
        collect(&db, std::slice::from_mut(&mut f));
        let graph = GRAPH.get(&f.analysis_facts).unwrap();
        assert!(graph.fixed.contains(&3));
        assert!(!graph.hypotheses.contains_key(&3));
        assert!(graph.hypotheses.contains_key(&4));
    }
}
