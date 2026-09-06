//! Check actual typed Clight memory targets against decoded frame writes.
//!
//! This is a target/width correspondence theory, not a payload, dominance or
//! control-flow equivalence certificate. Pointer addition is interpreted at
//! the source pointee size; a matching byte count at the wrong offset fails.

use super::query::FunctionData;
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::semantic_counterexample::ledger::{self, ObjectId};
use crate::x86::types::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug)]
pub(crate) struct WriteContract {
    pub object: ObjectId,
    pub node: Node,
    pub root: RTLReg,
    pub offset: i64,
    pub width: usize,
    pub locals: BTreeSet<RTLReg>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Check {
    Matches,
    Mismatch,
    Unknown,
}

/// Bind the provisional model to storage that is ALREADY explicit in Clight.
/// This is not a timeout shortcut: the full verifier still checks this model.
/// A writer is shared only if every available candidate has the exact target
/// and width, so subsequent statement selection cannot invalidate the binding.
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
            if candidates
                .iter()
                .all(|s| check(s, &contract, function) == Check::Matches)
            {
                prepared.initial.writes.insert(
                    write.node,
                    View {
                        object: StorageId::Frame(object),
                        offset: write.offset - p.base,
                        extent,
                    },
                );
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
    for function in functions {
        function.storage_writes = writes.remove(&function.address).unwrap_or_default();
        function
            .storage_writes
            .sort_by_key(|w| (w.node, w.object, w.offset, w.width));
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
    match super::solve::clight_expr_type(expr) {
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
            let ClightType::Tstruct(id, _) = super::solve::clight_expr_type(base) else {
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

pub(crate) fn check(stmt: &ClightStmt, contract: &WriteContract, function: &FunctionData) -> Check {
    match stmt {
        ClightStmt::Sassign(lhs, _) => {
            let Some(offset) = lvalue(lhs, contract.root, function) else {
                return Check::Unknown;
            };
            let Some(width) = size(super::solve::clight_expr_type(lhs), function.ptr64) else {
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
        ClightStmt::Slabel(_, inner) => check(inner, contract, function),
        ClightStmt::Ssequence(statements) => {
            let checks: Vec<_> = statements
                .iter()
                .map(|s| check(s, contract, function))
                .collect();
            if checks.contains(&Check::Matches) {
                Check::Matches
            } else if checks.contains(&Check::Mismatch) {
                Check::Mismatch
            } else {
                Check::Unknown
            }
        }
        _ => Check::Unknown,
    }
}

pub(crate) fn record_selection(
    db: &mut DecompileDB,
    functions: &[FunctionData],
    state: &super::select::ProgramSelectionState,
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
    use super::*;
    use std::collections::HashMap;
    use std::sync::Arc;

    fn fixture() -> (FunctionData, WriteContract) {
        let mut f = FunctionData::new(1, "targets".into(), vec![], vec![], None, 32, 30, true);
        f.used_regs.insert(10);
        f.var_type_candidates
            .insert(10, vec![super::super::candtype::CandType::PtrChar]);
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
        let outcome = super::super::solve::solve_function_z3(&f, &HashMap::new(), &[]).unwrap();
        assert_eq!(outcome.0[&30], Some(1));
    }

    #[test]
    fn existing_storage_binding_requires_every_candidate_to_preserve_the_write() {
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
            }];
            bind_current_storage(&db, &[function], &mut pending);
            assert_eq!(pending[0].problem.minimum_extent, 16);
            let valid = matches!(
                storage::validate_complete(&pending[0].problem, &pending[0].initial),
                storage::Verdict::Validated
            );
            assert_eq!(valid, !has_unchecked);
        }
    }
}
