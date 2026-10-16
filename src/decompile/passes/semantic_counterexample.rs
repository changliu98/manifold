//! Machine-origin storage obligations consumed by final Clight selection.
//!
//! This is a storage-lens validator, not a whole-program equivalence checker.
//! It asks whether a read through the escaped address observes the same bytes
//! after an arbitrary physical write under a proposed C object mapping. A SAT
//! model is a representation counterexample; UNSAT validates those finite lens
//! obligations for arbitrary byte values. No execution/reachability claim is
//! inferred from frame offsets. The caller/callee evidence is separately gated.

use std::collections::{BTreeMap, BTreeSet};

use z3::ast::{Ast, Bool, BV};
use z3::SatResult;

use crate::decompile::analysis::struct_recovery_pass::chunk_byte_size;
use crate::decompile::elevator::DecompileDB;
use crate::mreg::Mreg;
use crate::x86::types::{Address, MemoryChunk, Node, RTLReg, Symbol};

pub mod ledger;
mod machine;
pub(crate) mod symbolic;

pub(crate) const MAX_OBJECT_BYTES: i64 = 4096;
const MAX_OBJECTS: usize = 64;
const MAX_ACCESSES: usize = 256;

/// All imperative discovery inputs, including symbolic lattice handoffs.
/// Selection declares these to the scheduler; no hidden RTL-side solve.
pub(crate) const INPUTS: &[&str] = &[
    "unnormalized_frame_stack_write",
    "unknown_reg_value_reaches_use",
    "semantic_unknown_reg_value_reaches_use",
    "escaped_stack_region_field",
    "slot_escaped_canonical",
    "slot_escaped_region_canonical",
    "instr_in_function",
    "func_stacksz",
    "stack_var",
    "xtl_canonical",
    "abi_int_arg_position",
    "call_arg_mapping",
    "call_target_func",
    "arg_setup_candidate",
    "exact_frame_stack_lea",
    "renderable_stack_addr_result",
    "frame_stack_write_bytes",
    "frame_stack_read_bytes",
    "stack_var_chunk",
    "machine_frame_anchor",
    "settled_sp_frame_shift",
    "ltl_inst",
    "semantic_value_sources",
    "machine_register_write_view",
    "semantic_frame_dependencies",
    "semantic_parameter_field",
    "rtl_inst_candidate",
    "reg_rtl",
    "semantic_frame_object",
    "semantic_frame_member",
    "semantic_frame_write_piece",
];

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FailureKind {
    AddressMaterialization,
    Extent,
    WriteCorrespondence,
    CompleteAccess,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Counterexample {
    pub function: Address,
    pub base: i64,
    pub call: Node,
    pub observed_byte: i64,
    pub writer: Option<Node>,
    pub kind: FailureKind,
    pub machine_byte: u8,
    pub represented_byte: u8,
    /// Value of the machine index in an indexed representation-law witness.
    pub index_value: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RefinementRecord {
    pub function: Address,
    pub base: i64,
    pub call: Node,
    pub extent: i64,
    pub constructed: bool,
    pub validated: bool,
    pub regenerated: bool,
    pub reason: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Access {
    pub node: Node,
    pub offset: i64,
    pub width: usize,
    pub local: RTLReg,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct View {
    pub object: StorageId,
    pub offset: i64,
    pub extent: i64,
}

/// A source storage object is not a machine register value. The epoch bridge
/// may give them a common spelling, but their proof identities stay distinct.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum StorageId {
    Scalar(RTLReg),
    Frame(ledger::ObjectId),
}

#[derive(Clone, Debug)]
pub(crate) struct ObservedView {
    pub call: Node,
    pub index: symbolic::Index,
    pub observations: Vec<(i64, usize)>,
}

#[derive(Clone, Debug)]
pub(crate) struct Problem {
    pub function: Address,
    pub base: i64,
    pub call: Node,
    pub lea: Node,
    pub anchors: Vec<Node>,
    pub root: RTLReg,
    pub frame_size: i64,
    pub observations: Vec<(i64, usize)>,
    pub fields: Vec<(i64, MemoryChunk)>,
    pub writes: Vec<Access>,
    pub reads: Vec<Access>,
    pub other_roots: BTreeSet<i64>,
    pub index: Option<symbolic::Index>,
    pub views: Vec<ObservedView>,
    /// Other known views of the same physical base must fit too.
    pub minimum_extent: i64,
}

#[derive(Clone, Debug)]
pub(crate) struct Representation {
    pub address_preserved: bool,
    pub argument: View,
    pub writes: BTreeMap<Node, View>,
}

#[derive(Clone, Debug)]
pub(crate) enum Verdict {
    Validated,
    Refuted(Counterexample),
    Unknown,
}

pub(crate) fn end(offset: i64, width: usize) -> Option<i64> {
    offset.checked_add(i64::try_from(width).ok()?)
}

pub(crate) fn within_frame(base: i64, extent: i64, frame_size: i64) -> bool {
    if extent <= 0 || extent > MAX_OBJECT_BYTES || frame_size <= 0 {
        return false;
    }
    let Some(high) = base.checked_add(extent) else {
        return false;
    };
    (base >= 0 && high <= frame_size) || (base >= -frame_size && high <= 0)
}

pub(crate) fn validate(problem: &Problem, representation: &Representation) -> Verdict {
    if !representation.address_preserved {
        return Verdict::Refuted(Counterexample {
            function: problem.function,
            base: problem.base,
            call: problem.call,
            observed_byte: 0,
            writer: None,
            kind: FailureKind::AddressMaterialization,
            machine_byte: 0,
            represented_byte: 0,
            index_value: None,
        });
    }
    if !problem.views.is_empty() {
        // Preserve the pairing between each call's actual pointer expression
        // and its own observation footprint. A cross-product invents accesses
        // which no call performs and can spuriously reject a valid embedding.
        for view in &problem.views {
            let mut part = problem.clone();
            part.views.clear();
            part.call = view.call;
            part.index = Some(view.index.clone());
            part.observations = view.observations.clone();
            match validate_indexed(&part, representation) {
                Verdict::Validated => {}
                other => return other,
            }
        }
        return Verdict::Validated;
    }
    if problem.index.is_some() {
        return validate_indexed(problem, representation);
    }
    // Fixed offsets make byte aliasing decidable structurally. Do not invoke
    // SMT merely to select arbitrary values for two unequal free bytes.
    for &(offset, width) in &problem.observations {
        for byte in 0..width {
            let Some(relative) = offset.checked_add(byte as i64) else {
                return Verdict::Unknown;
            };
            let Some(c_read) = representation.argument.offset.checked_add(relative) else {
                return Verdict::Unknown;
            };
            if c_read < 0 || c_read >= representation.argument.extent {
                return witness(problem, relative, None, FailureKind::Extent);
            }
            let Some(machine_read) = problem.base.checked_add(relative) else {
                return Verdict::Unknown;
            };
            for write in &problem.writes {
                let Some(view) = representation.writes.get(&write.node) else {
                    return Verdict::Unknown;
                };
                if view.offset < 0 || end(view.offset, write.width).is_none_or(|e| e > view.extent)
                {
                    return Verdict::Unknown;
                }
                // The value of every written byte is universally arbitrary.
                // Test both alias directions: an omitted physical alias and
                // an invented C alias can each change the observed byte.
                for byte in 0..write.width {
                    let Some(machine_write) = write.offset.checked_add(byte as i64) else {
                        return Verdict::Unknown;
                    };
                    let Some(c_write) = view.offset.checked_add(byte as i64) else {
                        return Verdict::Unknown;
                    };
                    let expected_alias = machine_write == machine_read;
                    let represented_alias =
                        view.object == representation.argument.object && c_write == c_read;
                    if expected_alias == represented_alias {
                        continue;
                    }
                    return witness(
                        problem,
                        relative,
                        Some(write.node),
                        FailureKind::WriteCorrespondence,
                    );
                }
            }
        }
    }
    Verdict::Validated
}

fn witness(problem: &Problem, byte: i64, writer: Option<Node>, kind: FailureKind) -> Verdict {
    Verdict::Refuted(Counterexample {
        function: problem.function,
        base: problem.base,
        call: problem.call,
        observed_byte: byte,
        writer,
        kind,
        machine_byte: u8::from(kind == FailureKind::WriteCorrespondence),
        represented_byte: 0,
        index_value: None,
    })
}

/// Complete physical accesses and intermediate pointer views are checked by
/// the verifier, independently of the learner's finite witness set.
pub(crate) fn validate_complete(problem: &Problem, representation: &Representation) -> Verdict {
    if representation.argument.extent < problem.minimum_extent {
        return witness(
            problem,
            problem.minimum_extent - 1,
            None,
            FailureKind::Extent,
        );
    }
    if matches!(representation.argument.object, StorageId::Frame(_)) {
        let Some(high) = problem.base.checked_add(representation.argument.extent) else {
            return Verdict::Unknown;
        };
        for access in problem.writes.iter().chain(&problem.reads) {
            let Some(access_end) = end(access.offset, access.width) else {
                return Verdict::Unknown;
            };
            if access.offset < high && access_end > problem.base {
                if access.offset < problem.base || access.width > 8 {
                    return Verdict::Unknown;
                }
                if access_end > high {
                    return witness(
                        problem,
                        access_end - problem.base - 1,
                        Some(access.node),
                        FailureKind::CompleteAccess,
                    );
                }
                if problem.writes.contains(access) {
                    let Some(view) = representation.writes.get(&access.node) else {
                        return Verdict::Unknown;
                    };
                    if view.object != representation.argument.object
                        || view.offset != access.offset - problem.base
                    {
                        return witness(
                            problem,
                            access.offset - problem.base,
                            Some(access.node),
                            FailureKind::WriteCorrespondence,
                        );
                    }
                }
            }
        }
    }
    validate(problem, representation)
}

#[cfg(test)]
fn byte_object(problem: &Problem) -> Result<Representation, &'static str> {
    let mut extent = problem
        .observations
        .iter()
        .filter_map(|&(o, w)| end(o, w))
        .max()
        .ok_or("no observations")?;
    if let Some(index) = &problem.index {
        extent = extent
            .checked_add(index.maximum_delta)
            .ok_or("extent overflow")?;
    }
    extent = extent.max(problem.minimum_extent);
    if !within_frame(problem.base, extent, problem.frame_size) {
        return Err("observation outside the proven local frame");
    }
    // A physical write/read may straddle a callee field and its padding.
    // The candidate must hold the complete access, not just its observed byte.
    loop {
        let high = problem.base.checked_add(extent).ok_or("extent overflow")?;
        let mut enlarged = high;
        for access in problem.writes.iter().chain(&problem.reads) {
            let access_end = end(access.offset, access.width).ok_or("access overflow")?;
            if access.offset < high && access_end > problem.base {
                if access.offset < problem.base || access.width > 8 {
                    return Err("unsupported crossing or wide access");
                }
                enlarged = enlarged.max(access_end);
            }
        }
        let next = enlarged
            .checked_sub(problem.base)
            .ok_or("extent overflow")?;
        if !within_frame(problem.base, next, problem.frame_size) {
            return Err("complete access outside the proven local frame");
        }
        if next == extent {
            break;
        }
        extent = next;
    }
    let high = problem.base.checked_add(extent).ok_or("extent overflow")?;
    if problem
        .other_roots
        .iter()
        .any(|&root| root > problem.base && root < high)
    {
        return Err("another address-taken object intersects this candidate");
    }
    let writes = problem
        .writes
        .iter()
        .map(|a| {
            let inside =
                a.offset >= problem.base && end(a.offset, a.width).is_some_and(|e| e <= high);
            (
                a.node,
                if inside {
                    View {
                        object: StorageId::Frame(ledger::ObjectId {
                            function: problem.function,
                            base: problem.base,
                        }),
                        offset: a.offset - problem.base,
                        extent,
                    }
                } else {
                    View {
                        object: StorageId::Scalar(a.local),
                        offset: 0,
                        extent: a.width as i64,
                    }
                },
            )
        })
        .collect();
    Ok(Representation {
        address_preserved: true,
        argument: View {
            object: StorageId::Frame(ledger::ObjectId {
                function: problem.function,
                base: problem.base,
            }),
            offset: 0,
            extent,
        },
        writes,
    })
}

#[derive(Clone, Debug)]
pub(crate) struct Prepared {
    pub problem: Problem,
    pub initial: Representation,
    pub unmapped: Vec<(i64, usize)>,
    /// Final-selection candidate order, not relation iteration order. None
    /// denotes an unmodeled effect and cannot authorize storage validation.
    pub candidate_writes: BTreeMap<Node, Vec<Option<View>>>,
}

/// Verify the lowering's byte partition against the independent decoder
/// footprint before exposing word-sized obligations to selection. Sorting
/// here compares physical byte coordinates, never instruction reachability.
pub(crate) fn write_pieces(
    db: &DecompileDB,
) -> (
    BTreeMap<Address, Vec<Access>>,
    BTreeMap<Address, Vec<(i64, usize)>>,
) {
    let canonical: BTreeMap<_, _> = db
        .rel_iter::<(RTLReg, RTLReg)>("xtl_canonical")
        .copied()
        .collect();
    let canon = |r: RTLReg| canonical.get(&r).copied().unwrap_or(r);
    let mut locals: BTreeMap<(Address, Node, i64), BTreeSet<RTLReg>> = BTreeMap::new();
    for &(f, n, o, r) in db.rel_iter::<(Address, Node, i64, RTLReg)>("stack_var") {
        locals.entry((f, n, o)).or_default().insert(canon(r));
    }
    let definitions: BTreeSet<_> = db
        .rel_iter::<(Node, crate::x86::types::RTLInst)>("rtl_inst_candidate")
        .filter_map(|(n, inst)| match inst {
            crate::x86::types::RTLInst::Iop(_, _, r)
            | crate::x86::types::RTLInst::Iload(_, _, _, r) => Some((*n, canon(*r))),
            _ => None,
        })
        .collect();
    let mut pieces: BTreeMap<(Address, Node), Vec<Access>> = BTreeMap::new();
    for &(f, parent, node, offset, width, local) in
        db.rel_iter::<(Address, Node, Node, i64, usize, RTLReg)>("semantic_frame_write_piece")
    {
        pieces.entry((f, parent)).or_default().push(Access {
            node,
            offset,
            width,
            local: canon(local),
        });
    }
    let mut writes: BTreeMap<Address, Vec<Access>> = BTreeMap::new();
    let mut unknown: BTreeMap<Address, Vec<(i64, usize)>> = BTreeMap::new();
    for &(f, parent, offset, width) in
        db.rel_iter::<(Address, Node, i64, usize)>("frame_stack_write_bytes")
    {
        let mut rows = pieces.get(&(f, parent)).cloned().unwrap_or_default();
        rows.sort_by_key(|a| (a.offset, a.width, a.node, a.local));
        rows.dedup();
        // Unit/evaluation DBs and older ordinary scalar producers may not
        // publish pieces. The single-cell case has an exact direct witness.
        if rows.is_empty() && width <= 8 {
            if let Some(local) = locals
                .get(&(f, parent, offset))
                .filter(|s| s.len() == 1)
                .and_then(|s| s.first())
            {
                rows.push(Access {
                    node: parent,
                    offset,
                    width,
                    local: *local,
                });
            }
        }
        let mut cursor = Some(offset);
        for piece in &rows {
            if cursor != Some(piece.offset)
                || storage_chunk(piece.width).is_none()
                || (width > 8 && !definitions.contains(&(piece.node, piece.local)))
            {
                cursor = None;
                break;
            }
            cursor = end(piece.offset, piece.width);
        }
        if !rows.is_empty() && cursor == end(offset, width) {
            writes.entry(f).or_default().extend(rows);
        } else {
            unknown.entry(f).or_default().push((offset, width));
        }
    }
    for rows in writes.values_mut() {
        rows.sort_by_key(|a| (a.node, a.offset, a.width, a.local));
        rows.dedup();
    }
    (writes, unknown)
}

fn frame_accesses(
    db: &DecompileDB,
) -> (
    BTreeMap<Address, (Vec<Access>, Vec<Access>)>,
    BTreeMap<Address, Vec<(i64, usize)>>,
) {
    let (writes, mut unknown) = write_pieces(db);
    let mut all: BTreeMap<_, _> = writes
        .into_iter()
        .map(|(f, w)| (f, (w, Vec::new())))
        .collect();
    let canonical: BTreeMap<_, _> = db
        .rel_iter::<(RTLReg, RTLReg)>("xtl_canonical")
        .copied()
        .collect();
    let mut locals: BTreeMap<(Address, Node, i64), BTreeSet<RTLReg>> = BTreeMap::new();
    for &(f, n, o, r) in db.rel_iter::<(Address, Node, i64, RTLReg)>("stack_var") {
        locals
            .entry((f, n, o))
            .or_default()
            .insert(canonical.get(&r).copied().unwrap_or(r));
    }
    for &(f, node, offset, width) in
        db.rel_iter::<(Address, Node, i64, usize)>("frame_stack_read_bytes")
    {
        if let Some(local) = locals
            .get(&(f, node, offset))
            .filter(|s| s.len() == 1)
            .and_then(|s| s.first())
        {
            all.entry(f).or_default().1.push(Access {
                node,
                offset,
                width,
                local: *local,
            });
        } else {
            unknown.entry(f).or_default().push((offset, width));
        }
    }
    (all, unknown)
}

/// Existing explicit byte allocations have the same per-use access laws as
/// synthesized ones. This establishes a coordinate mapping, not a proof of
/// their initialization or all emitted behavior.
pub(crate) fn existing_byte_objects(db: &DecompileDB) -> Vec<(ledger::ObjectId, RTLReg, i64)> {
    let canonical: BTreeMap<_, _> = db
        .rel_iter::<(RTLReg, RTLReg)>("xtl_canonical")
        .copied()
        .collect();
    let mut coordinates: BTreeMap<(Address, RTLReg), BTreeSet<i64>> = BTreeMap::new();
    for &(f, _, offset, local) in db.rel_iter::<(Address, Node, i64, RTLReg)>("stack_var") {
        coordinates
            .entry((f, canonical.get(&local).copied().unwrap_or(local)))
            .or_default()
            .insert(offset);
    }
    let mut frames: BTreeMap<Address, BTreeSet<u64>> = BTreeMap::new();
    for &(f, _, _, size) in db.rel_iter::<(Address, Address, Symbol, u64)>("func_stacksz") {
        frames.entry(f).or_default().insert(size);
    }
    let mut objects = Vec::new();
    for (&function, buffers) in &db.stack_struct_buffers {
        for (&root, &extent) in buffers {
            let canonical = canonical.get(&root).copied().unwrap_or(root);
            let Some(base) = coordinates
                .get(&(function, canonical))
                .filter(|s| s.len() == 1)
                .and_then(|s| s.first())
                .copied()
            else {
                continue;
            };
            let Some(frame) = frames
                .get(&function)
                .filter(|s| s.len() == 1)
                .and_then(|s| s.first())
                .and_then(|s| i64::try_from(*s).ok())
            else {
                continue;
            };
            if within_frame(base, extent, frame) {
                objects.push((ledger::ObjectId { function, base }, root, extent));
            }
        }
    }
    objects.sort_by_key(|r| (r.0, r.1, r.2));
    objects
}

#[derive(Default)]
pub(crate) struct Refinement {
    pub objects: Vec<(Address, Node, i64, i64)>,
    pub fields: Vec<(Address, i64, i64, MemoryChunk)>,
    pub counterexamples: Vec<Counterexample>,
    pub records: Vec<RefinementRecord>,
    pub obligations: Vec<ledger::Event>,
    pub pending: Vec<Prepared>,
}

pub(crate) fn record_materialization(db: &mut DecompileDB) -> bool {
    use crate::decompile::passes::frame_write_pass::frame_interval_contains;
    use ledger::{Event, Outcome, Stage};
    let mut valid = true;
    let mut events = Vec::new();
    let mut materialized = BTreeSet::new();
    let (writes, unknown) = if db
        .rel_iter::<(Address, Node, i64, i64)>("semantic_frame_object")
        .next()
        .is_some()
    {
        write_pieces(db)
    } else {
        (BTreeMap::new(), BTreeMap::new())
    };
    for &(func, anchor, base, extent) in
        db.rel_iter::<(Address, Node, i64, i64)>("semantic_frame_object")
    {
        let root = db
            .rel_iter::<(Address, i64, RTLReg)>("slot_escaped_canonical")
            .any(|r| (r.0, r.1) == (func, base));
        let members: BTreeSet<_> = db
            .rel_iter::<(Address, Node, i64, RTLReg, usize)>("semantic_frame_member")
            .filter(|r| r.0 == func)
            .map(|r| (r.1, r.2, r.4))
            .collect();
        let complete = root
            && !unknown
                .get(&func)
                .into_iter()
                .flatten()
                .any(|&(o, w)| o < base + extent && end(o, w).is_some_and(|end| end > base))
            && writes
                .get(&func)
                .into_iter()
                .flatten()
                .filter(|r| frame_interval_contains(base, extent as usize, r.offset, r.width))
                .all(|r| members.contains(&(r.node, r.offset, r.width)))
            && db
                .rel_iter::<(Address, Node, i64, usize)>("frame_stack_read_bytes")
                .filter(|r| r.0 == func && frame_interval_contains(base, extent as usize, r.2, r.3))
                .all(|r| members.contains(&(r.1, r.2, r.3)));
        valid &= complete;
        if complete {
            materialized.insert((func, base));
        }
        let mut event = Event::new(func, anchor, base);
        event.extent = extent;
        events.push(event.at(
            Stage::Rtl,
            if complete {
                Outcome::Proven
            } else {
                Outcome::Unsupported
            },
            if complete {
                "selector-requested epoch materialized every physical member"
            } else {
                "selector-requested epoch failed to materialize storage"
            },
        ));
    }
    let mut records: Vec<_> = db
        .rel_iter::<RefinementRecord>("semantic_storage_refinement")
        .cloned()
        .collect();
    for record in &mut records {
        if record.validated && materialized.contains(&(record.function, record.base)) {
            record.regenerated = true;
            record.reason = "final-selector layout materialized in a fresh inference epoch";
        }
    }
    if !events.is_empty() {
        eprintln!(
            "[storage-materialization] objects={} complete={}",
            materialized.len(),
            valid
        );
    }
    db.rel_set(
        "semantic_storage_refinement",
        records.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
    ledger::append(db, events);
    valid
}

pub(crate) fn publish_selection(
    db: &mut DecompileDB,
    mut refinement: Refinement,
    decisions: &[crate::decompile::passes::clight_select::solvers::storage_theory::Decision],
) {
    use ledger::{Event, Outcome, Stage};
    let requests = crate::decompile::passes::clight_select::solvers::storage_theory::requests(decisions);
    for decision in decisions {
        let p = &decision.prepared.problem;
        let mut event = Event::new(p.function, p.lea, p.base);
        event.call = p.call;
        if let Some(witness) = decision.steps.iter().find_map(|s| s.witness.clone()) {
            refinement.counterexamples.push(witness);
            refinement.obligations.push(event.at(
                Stage::Representation,
                Outcome::Refuted,
                "final selector learned a storage witness",
            ));
        }
        for (iteration, step) in decision.steps.iter().enumerate() {
            eprintln!("[storage-search] function={:#x} base={} candidate={} shared={} extent={} joined={} witness={:?}",
                p.function, p.base, iteration, step.shared, step.extent, step.joined_writes.len(),
                step.witness.as_ref().map(|w| (w.kind, w.observed_byte, w.writer)));
        }
        if let Some(record) = refinement
            .records
            .iter_mut()
            .find(|r| (r.function, r.base) == (p.function, p.base))
        {
            record.reason = decision.reason;
            if let Some(r) = decision
                .representation
                .as_ref()
                .filter(|r| matches!(r.argument.object, StorageId::Frame(_)))
            {
                record.extent = r.argument.extent;
                record.constructed = decision.requires_replay;
                record.validated = true;
                event.extent = r.argument.extent;
                refinement.obligations.push(event.at(
                    Stage::Representation,
                    Outcome::Proven,
                    if decision.requires_replay { "selector discharged storage laws; re-derivation required" }
                    else { "existing Clight allocation and explicit write views satisfy storage laws" },
                ));
                if !decision.requires_replay {
                    eprintln!("[storage-reuse] function={:#x} base={} extent={} no-replay=true", p.function,p.base,r.argument.extent);
                }
            } else if decision.representation.is_none() {
                refinement.obligations.push(event.at(
                    Stage::Representation,
                    Outcome::Unknown,
                    decision.reason,
                ));
            }
        }
    }
    let fields: Vec<_> = decisions
        .iter()
        .filter(|d| {
            d.requires_replay && d.representation
                .as_ref()
                .is_some_and(|r| matches!(r.argument.object, StorageId::Frame(_)))
        })
        .flat_map(|d| {
            d.prepared
                .problem
                .fields
                .iter()
                .map(|&(o, c)| (d.prepared.problem.function, d.prepared.problem.base, o, c))
        })
        .collect();
    if !refinement.records.is_empty() {
        eprintln!("[semantic-counterexample] checked-gaps={} counterexamples={} constructed={} validated={} regenerated=pending-selection-feedback",
            refinement.records.len(), refinement.counterexamples.len(),
            refinement.records.iter().filter(|r| r.constructed).count(),
            refinement.records.iter().filter(|r| r.validated).count());
    }
    db.rel_set(
        "selection_storage_request",
        requests.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "selection_storage_field_request",
        fields.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
    for decision in decisions {
        db.rel_push("semantic_storage_search", decision.clone());
    }
    ledger::append(db, refinement.obligations);
    for witness in refinement.counterexamples {
        db.rel_push("semantic_storage_counterexample", witness);
    }
    for record in refinement.records {
        db.rel_push("semantic_storage_refinement", record);
    }
}

/// The first grammar targets only missing backing objects. Existing recovered
/// regions are controls; their full emitted access semantics are not claimed
/// to have been checked by this pilot. Calls must use a unique direct LEA and
/// the actual argument/definition mapping, not proximity to a call instruction.
pub(crate) fn prepare(db: &DecompileDB) -> Refinement {
    let mut result = Refinement::default();
    let indexed_bases: BTreeSet<_> = db
        .rel_iter::<(Address, Node, i64, i64, Option<Mreg>, Mreg, u32)>("machine_frame_anchor")
        .filter(|r| r.4.is_some())
        .map(|r| (r.0, r.2))
        .collect();
    let unknown_frame_writes: BTreeSet<_> = db
        .rel_iter::<(Address, Node)>("unnormalized_frame_stack_write")
        .map(|r| r.0)
        .collect();
    let unknown_arguments: BTreeSet<_> = [
        "unknown_reg_value_reaches_use",
        "semantic_unknown_reg_value_reaches_use",
    ]
    .into_iter()
    .flat_map(|name| db.rel_iter::<(Address, Node, Mreg)>(name).copied())
    .collect();
    let mut regions: BTreeMap<(Address, i64), BTreeSet<(i64, MemoryChunk)>> = BTreeMap::new();
    for &(func, base, offset, chunk) in
        db.rel_iter::<(Address, i64, i64, MemoryChunk)>("escaped_stack_region_field")
    {
        let width = chunk_byte_size(&chunk);
        if offset >= 0 && width > 0 && width <= 8 && end(offset, width).is_some() {
            regions
                .entry((func, base))
                .or_default()
                .insert((offset, chunk));
        }
    }
    let existing: BTreeSet<_> = ["slot_escaped_canonical", "slot_escaped_region_canonical"]
        .into_iter()
        .flat_map(|name| {
            db.rel_iter::<(Address, i64, RTLReg)>(name)
                .map(|r| (r.0, r.1))
        })
        .collect();
    let mut owners: BTreeMap<Node, BTreeSet<Address>> = BTreeMap::new();
    for &(node, func) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        owners.entry(node).or_default().insert(func);
    }
    let mut frames: BTreeMap<Address, BTreeSet<i64>> = BTreeMap::new();
    for &(func, _, _, size) in db.rel_iter::<(Address, Address, Symbol, u64)>("func_stacksz") {
        if let Ok(size) = i64::try_from(size) {
            frames.entry(func).or_default().insert(size);
        }
    }
    let canonical: BTreeMap<_, _> = db
        .rel_iter::<(RTLReg, RTLReg)>("xtl_canonical")
        .copied()
        .collect();
    let canon = |r: RTLReg| canonical.get(&r).copied().unwrap_or(r);
    let mut locals: BTreeMap<(Address, Node, i64), BTreeSet<RTLReg>> = BTreeMap::new();
    for &(func, node, offset, local) in db.rel_iter::<(Address, Node, i64, RTLReg)>("stack_var") {
        locals
            .entry((func, node, offset))
            .or_default()
            .insert(canon(local));
    }
    let positions: BTreeMap<_, _> = db
        .rel_iter::<(Mreg, usize)>("abi_int_arg_position")
        .copied()
        .collect();
    let mut call_args: BTreeMap<(Node, usize), BTreeSet<RTLReg>> = BTreeMap::new();
    for &(call, pos, reg) in db.rel_iter::<(Node, usize, RTLReg)>("call_arg_mapping") {
        call_args.entry((call, pos)).or_default().insert(canon(reg));
    }
    let mut callees: BTreeMap<Node, BTreeSet<Address>> = BTreeMap::new();
    for &(call, callee) in db.rel_iter::<(Node, Address)>("call_target_func") {
        callees.entry(call).or_default().insert(callee);
    }
    let mut setups: BTreeMap<Node, Vec<(Mreg, Node)>> = BTreeMap::new();
    for &(lea, reg, call) in db.rel_iter::<(Node, Mreg, Node)>("arg_setup_candidate") {
        setups.entry(lea).or_default().push((reg, call));
    }
    let exact: BTreeSet<_> = db
        .rel_iter::<(Address, Address, i64)>("exact_frame_stack_lea")
        .copied()
        .collect();
    let mut roots: BTreeMap<(Address, i64), BTreeSet<(Node, RTLReg)>> = BTreeMap::new();
    for &(lea, base, raw) in db.rel_iter::<(Node, i64, RTLReg)>("renderable_stack_addr_result") {
        let Some(own) = owners.get(&lea).filter(|o| o.len() == 1) else {
            continue;
        };
        let func = *own.first().unwrap();
        if exact.contains(&(func, lea, base)) {
            roots.entry((func, base)).or_default().insert((lea, raw));
        }
    }
    let (accesses, unmapped) = frame_accesses(db);
    for ((func, base), fields) in regions {
        if existing.contains(&(func, base))
            || fields.len() < 2
            || indexed_bases.contains(&(func, base))
        {
            continue;
        }
        let mut record = RefinementRecord {
            function: func,
            base,
            call: 0,
            extent: 0,
            constructed: false,
            validated: false,
            regenerated: false,
            reason: "unsupported evidence",
        };
        if unknown_frame_writes.contains(&func) {
            record.reason = "an unknown frame write may alias the candidate";
            result.records.push(record);
            continue;
        }
        let Some(root_set) = roots.get(&(func, base)).filter(|r| r.len() == 1) else {
            record.reason = "ambiguous or missing direct frame root";
            result.records.push(record);
            continue;
        };
        let &(lea, raw) = root_set.first().unwrap();
        let Some(local_set) = locals.get(&(func, lea, base)).filter(|s| s.len() == 1) else {
            record.reason = "ambiguous root local";
            result.records.push(record);
            continue;
        };
        let root = *local_set.first().unwrap();
        let Some(frame) = frames
            .get(&func)
            .filter(|f| f.len() == 1)
            .and_then(|f| f.first())
            .copied()
        else {
            record.reason = "ambiguous frame size";
            result.records.push(record);
            continue;
        };
        let calls: BTreeSet<_> = setups
            .get(&lea)
            .into_iter()
            .flatten()
            .filter_map(|&(reg, call)| {
                if unknown_arguments.contains(&(func, call, reg)) {
                    return None;
                }
                if owners.get(&call) != Some(&BTreeSet::from([func])) {
                    return None;
                }
                let pos = positions.get(&reg)?;
                if call_args.get(&(call, *pos)) != Some(&BTreeSet::from([canon(raw)])) {
                    return None;
                }
                let targets = callees.get(&call)?;
                (targets.len() == 1 && frames.contains_key(targets.first()?)).then_some(call)
            })
            .collect();
        let Some(&call) = calls.first() else {
            record.reason = "no exact direct internal call binding";
            result.records.push(record);
            continue;
        };
        record.call = call;
        let (mut writes, mut reads) = accesses.get(&func).cloned().unwrap_or_default();
        writes.sort_by_key(|a| (a.node, a.offset, a.width));
        writes.dedup();
        reads.sort_by_key(|a| (a.node, a.offset, a.width));
        reads.dedup();
        if writes.len() + reads.len() > MAX_ACCESSES
            || fields.len() > MAX_ACCESSES
            || result.pending.len() >= MAX_OBJECTS
        {
            record.reason = "resource budget";
            result.records.push(record);
            continue;
        }
        let mut problem = Problem {
            function: func,
            base,
            call,
            lea,
            anchors: vec![lea],
            root,
            frame_size: frame,
            observations: fields
                .iter()
                .map(|&(offset, chunk)| (offset, chunk_byte_size(&chunk)))
                .collect(),
            fields: fields.into_iter().collect(),
            writes,
            reads,
            other_roots: roots
                .keys()
                .filter_map(|&(f, offset)| (f == func && offset != base).then_some(offset))
                .collect(),
            index: None,
            views: Vec::new(),
            minimum_extent: 0,
        };
        problem.observations.sort();
        problem.observations.dedup();
        let scalar_extent = db
            .rel_iter::<(Address, i64, MemoryChunk)>("stack_var_chunk")
            .filter(|r| (r.0, r.1) == (func, base))
            .map(|r| chunk_byte_size(&r.2) as i64)
            .max()
            .unwrap_or(4);
        let initial = Representation {
            address_preserved: true,
            argument: View {
                object: StorageId::Scalar(root),
                offset: 0,
                extent: scalar_extent,
            },
            writes: problem
                .writes
                .iter()
                .map(|a| {
                    (
                        a.node,
                        View {
                            object: StorageId::Scalar(a.local),
                            offset: 0,
                            extent: a.width as i64,
                        },
                    )
                })
                .collect(),
        };
        result.pending.push(Prepared {
            problem,
            initial,
            unmapped: unmapped.get(&func).cloned().unwrap_or_default(),
            candidate_writes: BTreeMap::new(),
        });
        record.reason = "pending final-selection storage theory";
        result.records.push(record);
    }
    machine::discover(db, &mut result);
    result
}

pub(crate) fn storage_chunk(width: usize) -> Option<MemoryChunk> {
    match width {
        1 => Some(MemoryChunk::MInt8Unsigned),
        2 => Some(MemoryChunk::MInt16Unsigned),
        4 => Some(MemoryChunk::MAny32),
        8 => Some(MemoryChunk::MAny64),
        _ => None,
    }
}

fn validate_indexed(problem: &Problem, representation: &Representation) -> Verdict {
    let index = problem.index.as_ref().unwrap();
    let solver = symbolic::solver();
    let value = symbolic::encode(&index.expression, &solver);
    let delta = value.zero_ext(64).bvmul(BV::from_i64(index.scale, 128));
    let before = BV::new_const("storage_before", 8);
    let written = BV::new_const("storage_written", 8);
    let mut obligations = Vec::new();
    for &(offset, width) in &problem.observations {
        for byte in 0..width {
            let Some(relative) = offset.checked_add(byte as i64) else {
                return Verdict::Unknown;
            };
            let observed = delta.bvadd(BV::from_i64(relative, 128));
            let c_read = observed.bvadd(BV::from_i64(representation.argument.offset, 128));
            obligations.push((
                c_read.bvuge(BV::from_i64(representation.argument.extent, 128)),
                observed.clone(),
                None,
                FailureKind::Extent,
                written.clone(),
                before.clone(),
            ));
            let m_read = observed.bvadd(BV::from_i64(problem.base, 128));
            for write in &problem.writes {
                let Some(view) = representation.writes.get(&write.node) else {
                    return Verdict::Unknown;
                };
                if view.offset < 0 || end(view.offset, write.width).is_none_or(|e| e > view.extent)
                {
                    return Verdict::Unknown;
                }
                // Exact affine correspondence discharges the byte-alias law
                // structurally for all index values, without enumerating them.
                if view.object == representation.argument.object
                    && view.offset - representation.argument.offset == write.offset - problem.base
                {
                    continue;
                }
                for byte in 0..write.width {
                    let m_alias = m_read.eq(BV::from_i64(write.offset + byte as i64, 128));
                    let c_alias = if view.object == representation.argument.object {
                        c_read.eq(BV::from_i64(view.offset + byte as i64, 128))
                    } else {
                        Bool::from_bool(false)
                    };
                    let m = m_alias.ite(&written, &before);
                    let c = c_alias.ite(&written, &before);
                    obligations.push((
                        m.eq(&c).not(),
                        observed.clone(),
                        Some(write.node),
                        FailureKind::WriteCorrespondence,
                        m,
                        c,
                    ));
                }
            }
        }
    }
    if obligations.is_empty() {
        return Verdict::Validated;
    }
    solver.assert(Bool::or(
        &obligations.iter().map(|o| o.0.clone()).collect::<Vec<_>>(),
    ));
    match solver.check() {
        SatResult::Unsat => Verdict::Validated,
        SatResult::Unknown => Verdict::Unknown,
        SatResult::Sat => {
            let Some(model) = solver.get_model() else {
                return Verdict::Unknown;
            };
            let Some((_, observed, writer, kind, machine, represented)) = obligations
                .iter()
                .find(|o| model.eval(&o.0, true).and_then(|v| v.as_bool()) == Some(true))
            else {
                return Verdict::Unknown;
            };
            let Some(observed) = model
                .eval(observed, true)
                .and_then(|v| v.as_u64())
                .and_then(|v| i64::try_from(v).ok())
            else {
                return Verdict::Unknown;
            };
            Verdict::Refuted(Counterexample {
                function: problem.function,
                base: problem.base,
                call: problem.call,
                observed_byte: observed,
                writer: *writer,
                kind: *kind,
                machine_byte: model
                    .eval(machine, true)
                    .and_then(|v| v.as_u64())
                    .unwrap_or(0) as u8,
                represented_byte: model
                    .eval(represented, true)
                    .and_then(|v| v.as_u64())
                    .unwrap_or(0) as u8,
                index_value: model.eval(&value, true).and_then(|v| v.as_u64()),
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Exercise discovery through the real final-selector model. Production
    // RTL never invokes this helper or any storage solver.
    fn discover(db: &DecompileDB) -> Refinement {
        let mut result = prepare(db);
        for prepared in &result.pending {
            let p = &prepared.problem;
            let mut function = crate::decompile::passes::clight_select::query::FunctionData::new(
                p.function,
                "storage_test".into(),
                vec![],
                vec![],
                None,
                p.frame_size as u64,
                p.lea,
                true,
            );
            crate::decompile::passes::clight_select::solvers::storage::PROBLEMS
                .insert(&mut function.analysis_facts, vec![prepared.clone()]);
            let outcome = crate::decompile::passes::clight_select::syntax::solve::solve_function_z3(
                &function,
                &std::collections::HashMap::new(),
                &[],
            )
            .unwrap();
            for decision in crate::decompile::passes::clight_select::solvers::storage::DECISIONS
                .get(&outcome.5).into_iter().flatten().cloned() {
                if let Some(witness) = decision.steps.iter().find_map(|s| s.witness.clone()) {
                    result.counterexamples.push(witness);
                }
                let record = result
                    .records
                    .iter_mut()
                    .find(|r| (r.function, r.base) == (p.function, p.base))
                    .unwrap();
                record.reason = decision.reason;
                if let Some(r) = decision
                    .representation
                    .filter(|r| matches!(r.argument.object, StorageId::Frame(_)))
                {
                    result
                        .objects
                        .push((p.function, p.lea, p.base, r.argument.extent));
                    result
                        .fields
                        .extend(p.fields.iter().map(|&(o, c)| (p.function, p.base, o, c)));
                    record.extent = r.argument.extent;
                    record.constructed = true;
                    record.validated = true;
                }
            }
        }
        result
    }

    fn problem() -> Problem {
        Problem {
            function: 1,
            base: 16,
            call: 90,
            lea: 80,
            anchors: vec![80],
            root: 10,
            frame_size: 64,
            observations: vec![(0, 1), (4, 4), (9, 1)],
            fields: vec![],
            writes: vec![
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
            ],
            reads: vec![],
            other_roots: BTreeSet::new(),
            index: None,
            views: Vec::new(),
            minimum_extent: 0,
        }
    }

    #[test]
    fn counterexample_constructs_a_missing_object_and_validates_its_lens() {
        let p = problem();
        let initial = Representation {
            address_preserved: true,
            argument: View {
                object: StorageId::Scalar(p.root),
                offset: 0,
                extent: 4,
            },
            writes: p
                .writes
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
        assert!(matches!(validate(&p, &initial), Verdict::Refuted(_)));
        let candidate = byte_object(&p).unwrap();
        assert!(matches!(validate(&p, &candidate), Verdict::Validated));
        assert_eq!(candidate.argument.extent, 10);
        assert_eq!(candidate.writes[&40].offset, 8);
    }

    #[test]
    fn enough_bytes_without_shared_identity_is_not_a_valid_representation() {
        let p = problem();
        let mut candidate = byte_object(&p).unwrap();
        candidate.writes.get_mut(&30).unwrap().object = StorageId::Scalar(999);
        let Verdict::Refuted(counterexample) = validate(&p, &candidate) else {
            panic!("lost alias accepted");
        };
        assert_eq!(counterexample.kind, FailureKind::WriteCorrespondence);
        assert_eq!(counterexample.writer, Some(30));
        assert_ne!(counterexample.machine_byte, counterexample.represented_byte);
    }

    #[test]
    fn disjoint_machine_bytes_must_not_become_aliased_c_bytes() {
        let p = problem();
        let mut candidate = byte_object(&p).unwrap();
        candidate.writes.get_mut(&40).unwrap().offset = 0;
        assert!(matches!(validate(&p, &candidate), Verdict::Refuted(_)));
    }

    #[test]
    fn partial_stores_preserve_the_unwritten_bytes_and_complete_padding() {
        let mut p = problem();
        p.observations = vec![(4, 4), (8, 1)];
        let candidate = byte_object(&p).unwrap();
        assert_eq!(candidate.argument.extent, 10);
        assert!(matches!(validate(&p, &candidate), Verdict::Validated));
    }

    #[test]
    fn unknown_bounds_and_other_address_taken_roots_do_not_force_a_guess() {
        let mut p = problem();
        p.frame_size = 20;
        assert!(byte_object(&p).is_err());
        p.frame_size = 64;
        p.other_roots.insert(20);
        assert!(byte_object(&p).is_err());
    }

    #[test]
    fn instruction_numbering_does_not_change_storage_correspondence() {
        let mut p = problem();
        p.writes[0].node = 1000;
        p.writes[1].node = 1;
        p.call = 2;
        assert!(matches!(
            validate(&p, &byte_object(&p).unwrap()),
            Verdict::Validated
        ));
    }

    fn seeded_gap() -> DecompileDB {
        let mut db = DecompileDB::default();
        let p = problem();
        db.rel_push("func_stacksz", (p.function, 100_u64, "caller", 64_u64));
        db.rel_push("func_stacksz", (200_u64, 220_u64, "callee", 16_u64));
        for node in [p.lea, p.call, 20, 30, 40] {
            db.rel_push("instr_in_function", (node, p.function));
        }
        db.rel_push("exact_frame_stack_lea", (p.function, p.lea, p.base));
        db.rel_push("renderable_stack_addr_result", (p.lea, p.base, 500_u64));
        db.rel_push("stack_var", (p.function, p.lea, p.base, p.root));
        db.rel_push("arg_setup_candidate", (p.lea, Mreg::DI, p.call));
        db.rel_push("abi_int_arg_position", (Mreg::DI, 0_usize));
        db.rel_push("call_arg_mapping", (p.call, 0_usize, 500_u64));
        db.rel_push("call_target_func", (p.call, 200_u64));
        for (offset, chunk) in [
            (0_i64, MemoryChunk::MInt8Unsigned),
            (4, MemoryChunk::MInt32),
            (9, MemoryChunk::MInt8Unsigned),
        ] {
            db.rel_push(
                "escaped_stack_region_field",
                (p.function, p.base, offset, chunk),
            );
        }
        for write in p.writes {
            db.rel_push(
                "frame_stack_write_bytes",
                (p.function, write.node, write.offset, write.width),
            );
            db.rel_push(
                "stack_var",
                (p.function, write.node, write.offset, write.local),
            );
        }
        db
    }

    #[test]
    fn production_discovery_constructs_only_after_the_existing_model_is_refuted() {
        let mut db = seeded_gap();
        let repair = discover(&db);
        assert_eq!(repair.objects, vec![(1, 80, 16, 10)]);
        assert_eq!(repair.counterexamples.len(), 1);
        assert!(repair.records[0].constructed && repair.records[0].validated);
        assert!(!repair.records[0].regenerated);
        assert_eq!(
            db.rel_iter::<(Address, i64, RTLReg)>("slot_escaped_canonical")
                .count(),
            0
        );
        db.rel_push("slot_escaped_canonical", (1_u64, 16_i64, 10_u64));
        assert!(discover(&db).objects.is_empty());
    }

    #[test]
    fn ambiguous_call_bindings_and_unmapped_physical_writes_do_not_refine() {
        let mut db = seeded_gap();
        db.rel_push("call_arg_mapping", (90_u64, 0_usize, 999_u64));
        assert!(discover(&db).objects.is_empty());
        let mut db = seeded_gap();
        db.rel_push("frame_stack_write_bytes", (1_u64, 50_u64, 21_i64, 1_usize));
        let repair = discover(&db);
        assert!(repair.objects.is_empty());
        assert_eq!(
            repair.records[0].reason,
            "no model satisfies the accumulated analysis witnesses"
        );
    }

    #[test]
    fn superposed_function_ownership_cannot_supply_a_call_contract() {
        let mut db = seeded_gap();
        db.rel_push("instr_in_function", (90_u64, 200_u64));
        assert!(discover(&db).objects.is_empty());
    }

    #[test]
    fn write_partition_requires_all_bytes_and_both_lowered_definitions() {
        use crate::x86::{op::Operation, types::RTLInst};
        let mut db = DecompileDB::default();
        db.rel_push("frame_stack_write_bytes", (1_u64, 20_u64, 16_i64, 16_usize));
        db.rel_push(
            "semantic_frame_write_piece",
            (1_u64, 20_u64, 20_u64, 16_i64, 8_usize, 11_u64),
        );
        db.rel_push(
            "semantic_frame_write_piece",
            (1_u64, 20_u64, 30_u64, 24_i64, 8_usize, 12_u64),
        );
        db.rel_push(
            "rtl_inst_candidate",
            (
                20_u64,
                RTLInst::Iop(Operation::Olongconst(1), std::sync::Arc::new(vec![]), 11),
            ),
        );
        assert_eq!(write_pieces(&db).1[&1], vec![(16, 16)]);
        db.rel_push(
            "rtl_inst_candidate",
            (
                30_u64,
                RTLInst::Iop(Operation::Olongconst(2), std::sync::Arc::new(vec![]), 12),
            ),
        );
        let (pieces, unknown) = write_pieces(&db);
        assert!(unknown.is_empty());
        assert_eq!(pieces[&1].len(), 2);
        db.rel_set(
            "semantic_frame_write_piece",
            vec![
                (1_u64, 20_u64, 20_u64, 16_i64, 8_usize, 11_u64),
                (1, 20, 30, 23, 8, 12),
            ]
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
        );
        assert_eq!(
            write_pieces(&db).1[&1],
            vec![(16, 16)],
            "overlap is not a complete partition"
        );
    }

    #[test]
    fn slot_aliases_are_canonicalized_before_ambiguity_checks() {
        let mut db = seeded_gap();
        db.rel_push("stack_var", (1_u64, 20_u64, 16_i64, 999_u64));
        db.rel_push("xtl_canonical", (999_u64, 11_u64));
        let repair = discover(&db);
        assert_eq!(repair.objects, vec![(1, 80, 16, 10)]);
        assert_eq!(repair.counterexamples.len(), 1);
    }

    #[test]
    fn unknown_frame_writes_and_unknown_argument_arms_stay_unsupported() {
        let mut db = seeded_gap();
        db.rel_push("unnormalized_frame_stack_write", (1_u64, 50_u64));
        let repair = discover(&db);
        assert!(repair.objects.is_empty());
        assert!(repair.counterexamples.is_empty());
        assert_eq!(
            repair.records[0].reason,
            "an unknown frame write may alias the candidate"
        );
        let mut db = seeded_gap();
        db.rel_push("unknown_reg_value_reaches_use", (1_u64, 90_u64, Mreg::DI));
        assert!(discover(&db).objects.is_empty());
    }
}
