//! Check actual typed Clight memory targets against decoded frame writes.
//!
//! Target/width contracts and independent RTL anchors feed the selector's
//! shared obligation interface. Pointer addition uses the source pointee size;
//! a matching byte count at the wrong offset fails. This module does not
//! establish initialization, dominance, or control-flow equivalence.

use crate::decompile::passes::clight_select::query::FunctionData;
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::semantic_counterexample::ledger::{self, ObjectId};
use crate::x86::types::*;
use std::collections::{BTreeMap, BTreeSet};

/// Direct reads plus the storage discovery/decoder helpers used below. The
/// selection registry unions these into the scheduler's declared dependencies.
pub(crate) static INPUTS: std::sync::LazyLock<Vec<&'static str>> = std::sync::LazyLock::new(|| {
    let mut reads = crate::decompile::passes::semantic_counterexample::INPUTS.to_vec();
    reads.extend_from_slice(&[
        "semantic_storage_obligation",
        "frame_read_storage_access_owner",
        "rtl_inst",
    ]);
    reads.sort_unstable();
    reads.dedup();
    reads
});

#[derive(Clone, Debug)]
pub(crate) struct WriteContract {
    pub object: ObjectId,
    pub node: Node,
    pub root: RTLReg,
    pub offset: i64,
    pub width: usize,
    pub locals: BTreeSet<RTLReg>,
}

#[derive(Clone, Debug)]
pub(crate) struct ReadContract {
    pub object: ObjectId,
    pub node: Node,
    pub root: RTLReg,
    pub offset: i64,
    pub width: usize,
    pub chunk: MemoryChunk,
    pub destination: RTLReg,
    pub write_bits: Option<u32>,
    pub signed_word_load: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Check {
    Matches,
    Mismatch,
    Unknown,
}

/// Bind the provisional model to storage that is ALREADY explicit in Clight.
/// This is not a timeout shortcut: the full verifier still checks this model.
/// Each write view is conditional on its statement candidate. The layout
/// verifier sees the selected view, and learns clauses over those same choices.
pub(crate) fn bind_current_storage(
    db: &DecompileDB,
    functions: &[FunctionData],
    pending: &mut [crate::decompile::passes::semantic_counterexample::Prepared],
) {
    use crate::decompile::passes::semantic_counterexample::{self as storage, StorageId, View};
    let canonical: BTreeMap<_, _> = db
        .rel_iter::<(RTLReg, RTLReg)>("xtl_canonical")
        .copied()
        .collect();
    let objects = storage::existing_byte_objects(db);
    for prepared in pending {
        if !prepared.initial.address_preserved {
            continue;
        }
        let p = &prepared.problem;
        let Some(function) = functions.iter().find(|f| f.address == p.function) else {
            continue;
        };
        let choices: Vec<_> = objects
            .iter()
            .filter(|(object, root, _)| {
                (object.function, object.base) == (p.function, p.base)
                    && canonical.get(root).copied().unwrap_or(*root) == p.root
            })
            .collect();
        if choices.len() != 1 {
            continue;
        }
        let &(object, root, extent) = choices[0];
        prepared.initial.argument = View {
            object: StorageId::Frame(object),
            offset: 0,
            extent,
        };
        for write in &p.writes {
            if !crate::decompile::passes::frame_write_pass::frame_interval_contains(
                p.base,
                extent as usize,
                write.offset,
                write.width,
            ) {
                continue;
            }
            let Some(candidates) = function
                .node_statements
                .get(&write.node)
                .filter(|c| !c.is_empty())
            else {
                continue;
            };
            let contract = WriteContract {
                object,
                node: write.node,
                root,
                offset: write.offset - p.base,
                width: write.width,
                locals: BTreeSet::from([write.local]),
            };
            let original = prepared.initial.writes.get(&write.node).copied();
            let views: Vec<_> = candidates
                .iter()
                .map(|stmt| match primitive(stmt) {
                    ClightStmt::Sassign(lhs, _)
                        if size(crate::decompile::passes::clight_select::syntax::solve::clight_expr_type(lhs), function.ptr64)
                            == Some(write.width as i64) =>
                    {
                        Some(View {
                            object: StorageId::Frame(object),
                            offset: lvalue(lhs, root, function)?,
                            extent,
                        })
                    }
                    ClightStmt::Sset(local, _) if contract.locals.contains(&(*local as RTLReg)) => {
                        original
                    }
                    _ => None,
                })
                .collect();
            if let Some(view) = views
                .first()
                .copied()
                .flatten()
                .filter(|view| views.iter().all(|other| *other == Some(*view)))
            {
                // Identical targets are independent of statement selection.
                // Preserve ordinary re-picking of their payload alternatives.
                prepared.initial.writes.insert(write.node, view);
            } else {
                prepared.candidate_writes.insert(write.node, views);
            }
        }
        // A repair may widen an existing allocation, never erase its other
        // already recovered views by choosing a smaller object.
        prepared.problem.minimum_extent = prepared.problem.minimum_extent.max(extent);
    }
}

pub(crate) fn collect(db: &DecompileDB, functions: &mut [FunctionData]) {
    let mut committed: BTreeMap<_, _> = ledger::committed(db)
        .into_iter()
        .map(|e| (e.object, e.extent))
        .collect();
    let mut roots: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
    for &(f, base, root) in db.rel_iter::<(Address, i64, RTLReg)>("slot_escaped_canonical") {
        roots
            .entry(ObjectId { function: f, base })
            .or_default()
            .insert(root);
    }
    // The same selection theory covers existing explicit byte buffers, not
    // only objects constructed by storage search. Require one physical frame
    // coordinate for the buffer's canonical root; value equality alone cannot
    // license a storage identity across distinct slots.
    let canonical: BTreeMap<_, _> = db
        .rel_iter::<(RTLReg, RTLReg)>("xtl_canonical")
        .copied()
        .collect();
    let canon = |r: RTLReg| canonical.get(&r).copied().unwrap_or(r);
    let mut local_sites: BTreeMap<(Address, Node, i64), BTreeSet<RTLReg>> = BTreeMap::new();
    for &(f, n, offset, local) in db.rel_iter::<(Address, Node, i64, RTLReg)>("stack_var") {
        local_sites
            .entry((f, n, offset))
            .or_default()
            .insert(canon(local));
    }
    for &(f, n, offset, local, _) in
        db.rel_iter::<(Address, Node, i64, RTLReg, usize)>("semantic_frame_member")
    {
        local_sites.entry((f, n, offset)).or_default().insert(local);
    }
    for (object, root, extent) in
        crate::decompile::passes::semantic_counterexample::existing_byte_objects(db)
    {
        committed.entry(object).or_insert(extent);
        roots.entry(object).or_default().insert(root);
    }
    let mut writes: BTreeMap<Address, Vec<WriteContract>> = BTreeMap::new();
    let (pieces, _) = crate::decompile::passes::semantic_counterexample::write_pieces(db);
    for (&f, pieces) in &pieces {
        for piece in pieces {
            let (node, offset, width) = (piece.node, piece.offset, piece.width);
            for (&object, &extent) in committed.iter().filter(|(id, _)| id.function == f) {
                if !crate::decompile::passes::frame_write_pass::frame_interval_contains(
                    object.base,
                    extent as usize,
                    offset,
                    width,
                ) {
                    continue;
                }
                let Some(root) = roots
                    .get(&object)
                    .filter(|r| r.len() == 1)
                    .and_then(|r| r.first())
                    .copied()
                else {
                    continue;
                };
                let mut locals = local_sites
                    .get(&(f, node, offset))
                    .cloned()
                    .unwrap_or_default();
                locals.insert(piece.local);
                writes.entry(f).or_default().push(WriteContract {
                    object,
                    node,
                    root,
                    offset: offset - object.base,
                    width,
                    locals,
                });
            }
        }
    }
    let mut anchors: BTreeMap<Node, Option<RTLInst>> = BTreeMap::new();
    for (node, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        anchors
            .entry(*node)
            .and_modify(|old| {
                if old.as_ref() != Some(inst) {
                    *old = None;
                }
            })
            .or_insert_with(|| Some(inst.clone()));
    }
    let mut owners: BTreeMap<(Address, Node), BTreeSet<(i64, i64, RTLReg)>> = BTreeMap::new();
    for &(f, n, offset, base, root) in
        db.rel_iter::<(Address, Node, i64, i64, RTLReg)>("frame_read_storage_access_owner")
    {
        owners
            .entry((f, n))
            .or_default()
            .insert((offset, base, root));
    }
    let mut reads: BTreeMap<(Address, Node), BTreeSet<(i64, usize)>> = BTreeMap::new();
    for &(f, n, offset, width) in
        db.rel_iter::<(Address, Node, i64, usize)>("frame_stack_read_bytes")
    {
        reads.entry((f, n)).or_default().insert((offset, width));
    }
    for function in functions {
        function.storage_writes = writes.remove(&function.address).unwrap_or_default();
        function
            .storage_writes
            .sort_by_key(|w| (w.node, w.object, w.offset, w.width));
        function.memory_anchors.clear();
        for write in &function.storage_writes {
            if let Some(Some(inst)) = anchors.get(&write.node) {
                function.memory_anchors.insert(write.node, inst.clone());
            }
        }
        function.storage_reads.clear();
        for (&(f, node), ownership) in &owners {
            if f != function.address || ownership.len() != 1 {
                continue;
            }
            let &(offset, base, root) = ownership.first().unwrap();
            let Some(footprint) = reads.get(&(f, node)).filter(|r| r.len() == 1) else {
                continue;
            };
            let &(decoded_offset, width) = footprint.first().unwrap();
            let Some(Some(RTLInst::Iload(
                chunk,
                crate::x86::op::Addressing::Ainstack(at),
                args,
                destination,
            ))) = anchors.get(&node)
            else {
                continue;
            };
            let object = ObjectId { function: f, base };
            // An exact scalar-cell read is an obligation even before an
            // array representation exists. Requiring a recovered byte buffer
            // here makes missing representation hide the machine observation.
            // Interior views still require a known containing object; do not
            // infer an aggregate's extent from the read we intend to check.
            let contained = committed.get(&object).map_or(offset == base, |&extent| {
                crate::decompile::passes::frame_write_pass::frame_interval_contains(
                    base,
                    extent as usize,
                    offset,
                    width,
                )
            });
            if !args.is_empty()
                || *at != offset
                || decoded_offset != offset
                || crate::decompile::analysis::struct_recovery_pass::chunk_byte_size(chunk) != width
                || !contained
                || roots.get(&object) != Some(&BTreeSet::from([root]))
            {
                continue;
            }
            function.storage_reads.push(ReadContract {
                object,
                node,
                root,
                offset: offset - base,
                width,
                chunk: *chunk,
                destination: *destination,
                write_bits: None,
                signed_word_load: false,
            });
        }
    }
}

fn size(ty: &ClightType, ptr64: bool) -> Option<i64> {
    match ty {
        ClightType::Tint(ClightIntSize::I8 | ClightIntSize::IBool, _, _) => Some(1),
        ClightType::Tint(ClightIntSize::I16, _, _) => Some(2),
        ClightType::Tint(ClightIntSize::I32, _, _)
        | ClightType::Tfloat(ClightFloatSize::F32, _) => Some(4),
        ClightType::Tlong(..) | ClightType::Tfloat(ClightFloatSize::F64, _) => Some(8),
        ClightType::Tpointer(..) => Some(if ptr64 { 8 } else { 4 }),
        ClightType::Tarray(element, count, _) if *count >= 0 => {
            size(element, ptr64)?.checked_mul(*count)
        }
        _ => None,
    }
}

fn constant(expr: &ClightExpr) -> Option<i64> {
    match expr {
        ClightExpr::EconstInt(value, _) => Some(*value as i64),
        ClightExpr::EconstLong(value, _) => Some(*value),
        _ => None,
    }
}

fn stride(expr: &ClightExpr, function: &FunctionData) -> Option<i64> {
    match crate::decompile::passes::clight_select::syntax::solve::clight_expr_type(expr) {
        ClightType::Tpointer(element, _) | ClightType::Tarray(element, _, _) => {
            size(element, function.ptr64)
        }
        _ => None,
    }
}

fn address(expr: &ClightExpr, root: RTLReg, function: &FunctionData) -> Option<i64> {
    match expr {
        ClightExpr::Evar(id, ClightType::Tarray(..))
        | ClightExpr::Etempvar(id, ClightType::Tarray(..))
            if *id as RTLReg == root =>
        {
            Some(0)
        }
        ClightExpr::Eaddrof(inner, _) => lvalue(inner, root, function),
        ClightExpr::Ecast(inner, ClightType::Tpointer(..)) => address(inner, root, function),
        ClightExpr::Ebinop(op @ (ClightBinaryOp::Oadd | ClightBinaryOp::Osub), lhs, rhs, _) => {
            let displacement = constant(rhs)?.checked_mul(stride(lhs, function)?)?;
            let base = address(lhs, root, function)?;
            if *op == ClightBinaryOp::Oadd {
                base.checked_add(displacement)
            } else {
                base.checked_sub(displacement)
            }
        }
        _ => None,
    }
}

fn lvalue(expr: &ClightExpr, root: RTLReg, function: &FunctionData) -> Option<i64> {
    match expr {
        ClightExpr::Evar(id, _) | ClightExpr::Etempvar(id, _) if *id as RTLReg == root => Some(0),
        ClightExpr::Ederef(pointer, _) => address(pointer, root, function),
        ClightExpr::Efield(base, field, _) => {
            let ClightType::Tstruct(id, _) = crate::decompile::passes::clight_select::syntax::solve::clight_expr_type(base) else {
                return None;
            };
            let offsets: BTreeSet<_> = function
                .struct_fields
                .get(&(*id as i64))?
                .iter()
                .filter(|(_, name, _)| name == field)
                .map(|(offset, _, _)| *offset)
                .collect();
            if offsets.len() != 1 {
                return None;
            }
            lvalue(base, root, function)?.checked_add(*offsets.first()?)
        }
        _ => None,
    }
}

/// Only a primitive (possibly provenance-wrapped) is one effect. Finding one
/// matching write inside a sequence cannot establish the other effects agree.
pub(crate) fn primitive(stmt: &ClightStmt) -> &ClightStmt {
    match stmt {
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => primitive(inner),
        ClightStmt::Ssequence(items) if items.len() == 1 => primitive(&items[0]),
        _ => stmt,
    }
}

/// One explicit scalar read, with its byte target checked independently of
/// the value expression. Calls, multiple reads and volatile accesses are not
/// silently abstracted into an arbitrary integer.
pub(crate) fn read_operand<'a>(
    rhs: &'a ClightExpr,
    contract: &ReadContract,
    function: &FunctionData,
) -> Option<&'a ClightExpr> {
    let operand = single_read_operand(rhs)?;
    (lvalue(operand, contract.root, function) == Some(contract.offset)
        && size(crate::decompile::passes::clight_select::syntax::solve::clight_expr_type(operand), function.ptr64)
            == Some(contract.width as i64))
    .then_some(operand)
}

/// The sole value-producing read, without a claim about its address. Used by
/// the load-transport obligation, which checks the declaration's preservation
/// of the loaded word separately from target/alias/layout validation.
pub(crate) fn single_read_operand(rhs: &ClightExpr) -> Option<&ClightExpr> {
    fn visit<'a>(
        expr: &'a ClightExpr,
        found: &mut Vec<&'a ClightExpr>,
        fuel: &mut usize,
    ) -> Option<()> {
        *fuel = fuel.checked_sub(1)?;
        match expr {
            ClightExpr::Ederef(..) | ClightExpr::Efield(..) => found.push(expr),
            ClightExpr::Ecast(inner, _) | ClightExpr::Eunop(_, inner, _) => {
                visit(inner, found, fuel)?
            }
            ClightExpr::Ebinop(_, lhs, rhs, _) => {
                visit(lhs, found, fuel)?;
                visit(rhs, found, fuel)?;
            }
            ClightExpr::EconstInt(..) | ClightExpr::EconstLong(..) | ClightExpr::Etempvar(..) => {}
            _ => return None,
        }
        Some(())
    }
    let mut found = Vec::new();
    visit(rhs, &mut found, &mut 96)?;
    if found.len() != 1 {
        return None;
    }
    Some(found[0])
}

pub(crate) fn check(stmt: &ClightStmt, contract: &WriteContract, function: &FunctionData) -> Check {
    match primitive(stmt) {
        ClightStmt::Sassign(lhs, _) => {
            let Some(offset) = lvalue(lhs, contract.root, function) else {
                return Check::Unknown;
            };
            let Some(width) = size(crate::decompile::passes::clight_select::syntax::solve::clight_expr_type(lhs), function.ptr64) else {
                return Check::Unknown;
            };
            if offset == contract.offset && width == contract.width as i64 {
                Check::Matches
            } else {
                Check::Mismatch
            }
        }
        ClightStmt::Sset(local, _) if contract.locals.contains(&(*local as RTLReg)) => {
            Check::Mismatch
        }
        _ => Check::Unknown,
    }
}

pub(crate) fn record_selection(
    db: &mut DecompileDB,
    functions: &[FunctionData],
    state: &crate::decompile::passes::clight_select::select::ProgramSelectionState,
) {
    let mut checked = Vec::new();
    for function in functions {
        for contract in &function.storage_writes {
            let Some(Some(index)) = state.candidate_idx.get(&(function.address, contract.node))
            else {
                continue;
            };
            let Some(stmt) = function
                .node_statements
                .get(&contract.node)
                .and_then(|c| c.get(*index))
            else {
                continue;
            };
            if check(stmt, contract, function) == Check::Matches {
                checked.push((
                    function.address,
                    contract.node,
                    contract.object,
                    contract.offset,
                    contract.width,
                ));
            }
        }
    }
    db.rel_set(
        "semantic_storage_selected_target",
        checked.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
}

#[cfg(test)]
mod tests {
    use crate::decompile::passes::clight_select::solvers::memory_theory::*;
    use std::collections::HashMap;
    use std::sync::Arc;

    fn fixture() -> (FunctionData, WriteContract) {
        let mut f = FunctionData::new(1, "targets".into(), vec![], vec![], None, 32, 30, true);
        f.used_regs.insert(10);
        f.var_type_candidates
            .insert(10, vec![crate::decompile::passes::clight_select::candtype::CandType::PtrChar]);
        let w = WriteContract {
            object: ObjectId {
                function: 1,
                base: 16,
            },
            node: 30,
            root: 10,
            offset: 4,
            width: 4,
            locals: BTreeSet::from([12]),
        };
        (f, w)
    }

    #[test]
    fn exact_scalar_cell_reads_do_not_require_a_preexisting_byte_array() {
        let mut db = DecompileDB::default();
        db.rel_push("slot_escaped_canonical", (1_u64, 12_i64, 10_u64));
        db.rel_push(
            "frame_read_storage_access_owner",
            (1_u64, 40_u64, 12_i64, 12_i64, 10_u64),
        );
        db.rel_push("frame_stack_read_bytes", (1_u64, 40_u64, 12_i64, 4_usize));
        db.rel_push(
            "rtl_inst",
            (
                40_u64,
                RTLInst::Iload(
                    MemoryChunk::MAny32,
                    crate::x86::op::Addressing::Ainstack(12),
                    Arc::new(vec![]),
                    13,
                ),
            ),
        );
        let (mut function, _) = fixture();
        collect(&db, std::slice::from_mut(&mut function));
        assert_eq!(function.storage_reads.len(), 1);
        assert_eq!(function.storage_reads[0].offset, 0);
        assert!(db.stack_struct_buffers.is_empty());
        db.rel_set(
            "frame_read_storage_access_owner",
            [(1_u64, 40_u64, 12_i64, 8_i64, 10_u64)]
                .into_iter()
                .collect::<ascent::boxcar::Vec<_>>(),
        );
        collect(&db, std::slice::from_mut(&mut function));
        assert!(
            function.storage_reads.is_empty(),
            "an unknown interior extent is not a scalar cell"
        );
    }

    fn store(index: i64, element: ClightIntSize) -> ClightStmt {
        let attr = ClightAttr::default();
        let byte = ClightType::Tint(ClightIntSize::I8, ClightSignedness::Unsigned, attr.clone());
        let word = ClightType::Tint(ClightIntSize::I32, ClightSignedness::Unsigned, attr.clone());
        let element = ClightType::Tint(element, ClightSignedness::Unsigned, attr.clone());
        let array = ClightType::Tarray(Arc::new(byte), 16, attr.clone());
        let pointer = ClightType::Tpointer(Arc::new(element), attr.clone());
        let root = ClightExpr::Eaddrof(
            Box::new(ClightExpr::Evar(10, array.clone())),
            ClightType::Tpointer(Arc::new(array), attr.clone()),
        );
        let addr = ClightExpr::Ebinop(
            ClightBinaryOp::Oadd,
            Box::new(ClightExpr::Ecast(Box::new(root), pointer.clone())),
            Box::new(ClightExpr::EconstLong(
                index,
                ClightType::Tlong(ClightSignedness::Signed, attr.clone()),
            )),
            pointer,
        );
        let lhs = ClightExpr::Ederef(
            Box::new(ClightExpr::Ecast(
                Box::new(addr),
                ClightType::Tpointer(Arc::new(word.clone()), attr),
            )),
            word.clone(),
        );
        ClightStmt::Sassign(lhs, ClightExpr::EconstInt(7, word))
    }

    #[test]
    fn pointer_stride_and_offset_are_checked_independently_of_write_width() {
        let (f, w) = fixture();
        assert_eq!(check(&store(4, ClightIntSize::I8), &w, &f), Check::Matches);
        assert_eq!(check(&store(1, ClightIntSize::I32), &w, &f), Check::Matches);
        assert_eq!(check(&store(1, ClightIntSize::I8), &w, &f), Check::Mismatch);
        assert_eq!(
            check(&store(4, ClightIntSize::I32), &w, &f),
            Check::Mismatch
        );
    }

    #[test]
    fn final_maxsmt_and_post_model_repick_reject_the_wrong_byte_target() {
        let (mut f, w) = fixture();
        f.storage_writes.push(w);
        f.node_statements.insert(
            30,
            vec![store(1, ClightIntSize::I8), store(4, ClightIntSize::I8)],
        );
        let outcome = crate::decompile::passes::clight_select::syntax::solve::solve_function_z3(&f, &HashMap::new(), &[]).unwrap();
        assert_eq!(outcome.0[&30], Some(1));
    }

    #[test]
    fn existing_storage_binding_retains_each_candidates_distinct_write_view() {
        use crate::decompile::passes::semantic_counterexample::{
            self as storage, Access, Prepared, Problem, Representation, StorageId, View,
        };
        let mut db = DecompileDB::default();
        db.rel_push("func_stacksz", (1_u64, 100_u64, "test", 32_u64));
        db.rel_push("stack_var", (1_u64, 30_u64, 0_i64, 10_u64));
        db.stack_struct_buffers.insert(1, HashMap::from([(10, 16)]));
        for has_unchecked in [false, true] {
            let (mut function, _) = fixture();
            let mut candidates = vec![store(4, ClightIntSize::I8)];
            if has_unchecked {
                candidates.push(ClightStmt::Sset(
                    12,
                    ClightExpr::EconstInt(
                        0,
                        ClightType::Tint(
                            ClightIntSize::I32,
                            ClightSignedness::Signed,
                            ClightAttr::default(),
                        ),
                    ),
                ));
            }
            function.node_statements.insert(30, candidates);
            let mut pending = vec![Prepared {
                problem: Problem {
                    function: 1,
                    base: 0,
                    call: 90,
                    lea: 80,
                    anchors: vec![80],
                    root: 10,
                    frame_size: 32,
                    observations: vec![(4, 4)],
                    fields: vec![],
                    writes: vec![Access {
                        node: 30,
                        offset: 4,
                        width: 4,
                        local: 12,
                    }],
                    reads: vec![],
                    other_roots: BTreeSet::new(),
                    index: None,
                    views: vec![],
                    minimum_extent: 0,
                },
                initial: Representation {
                    address_preserved: true,
                    argument: View {
                        object: StorageId::Scalar(10),
                        offset: 0,
                        extent: 4,
                    },
                    writes: BTreeMap::from([(
                        30,
                        View {
                            object: StorageId::Scalar(12),
                            offset: 0,
                            extent: 4,
                        },
                    )]),
                },
                unmapped: vec![],
                candidate_writes: BTreeMap::new(),
            }];
            bind_current_storage(&db, &[function.clone()], &mut pending);
            assert_eq!(pending[0].problem.minimum_extent, 16);
            let valid = matches!(
                storage::validate_complete(&pending[0].problem, &pending[0].initial),
                storage::Verdict::Validated
            );
            assert_eq!(valid, !has_unchecked);
            if has_unchecked {
                let views = &pending[0].candidate_writes[&30];
                assert!(matches!(
                    views[0],
                    Some(View {
                        object: StorageId::Frame(_),
                        offset: 4,
                        ..
                    })
                ));
                assert!(matches!(
                    views[1],
                    Some(View {
                        object: StorageId::Scalar(12),
                        ..
                    })
                ));
            }
            crate::decompile::passes::clight_select::solvers::storage::PROBLEMS.insert(&mut function.analysis_facts, pending);
            let outcome =
                crate::decompile::passes::clight_select::syntax::solve::solve_function_z3(&function, &HashMap::new(), &[]).unwrap();
            assert_eq!(outcome.0[&30], Some(0));
            let decisions = crate::decompile::passes::clight_select::solvers::storage::DECISIONS
                .get(&outcome.5)
                .unwrap();
            assert_eq!(decisions.len(), 1);
            assert!(!decisions[0].requires_replay);
            assert!(decisions[0].representation.is_some());
        }
    }
}
