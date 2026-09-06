//! Demand discovery is independent of escape-candidate success. This module
//! binds immutable decoder anchors to the first RTL epoch, refutes that epoch's
//! scalar interpretation, and asks the shared storage grammar for a model.

use std::collections::{BTreeMap, BTreeSet};

use super::ledger::{Event, Outcome, Stage};
use super::symbolic::{self, Bound, SourceIndex};
use super::*;
use crate::x86::op::{Addressing, Operation};
use crate::x86::types::RTLInst;

pub(super) fn discover(db: &DecompileDB, out: &mut Refinement) {
    let mut anchors: Vec<_> = db
        .rel_iter::<(Address, Node, i64, i64, Option<Mreg>, Mreg, u32)>("machine_frame_anchor")
        .copied()
        .collect();
    if anchors.is_empty() {
        return;
    }
    anchors.sort_unstable();
    anchors.dedup();
    let mut view_sites: BTreeMap<(Address, i64), BTreeSet<Node>> = BTreeMap::new();
    let mut groups: BTreeMap<(Address, i64), Vec<(Node, Mreg, Option<Mreg>, i64, u32)>> =
        BTreeMap::new();
    let mut coordinates: BTreeMap<(Address, Node), BTreeSet<i64>> = BTreeMap::new();
    for &(f, n, base, scale, index, destination, bits) in &anchors {
        view_sites.entry((f, base)).or_default().insert(n);
        groups
            .entry((f, base))
            .or_default()
            .push((n, destination, index, scale, bits));
        coordinates.entry((f, n)).or_default().insert(base);
    }
    let terms = SourceIndex::from_db(db);
    let mut owners: BTreeMap<Node, BTreeSet<Address>> = BTreeMap::new();
    for &(node, function) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        owners.entry(node).or_default().insert(function);
    }
    let mut shifts: BTreeMap<(Address, Node), BTreeSet<i64>> = BTreeMap::new();
    for &(f, n, s) in db.rel_iter::<(Address, Node, i64)>("settled_sp_frame_shift") {
        shifts.entry((f, n)).or_default().insert(s);
    }
    let canonical: BTreeMap<_, _> = db
        .rel_iter::<(RTLReg, RTLReg)>("xtl_canonical")
        .copied()
        .collect();
    let canon = |r: RTLReg| canonical.get(&r).copied().unwrap_or(r);
    let mut locals: BTreeMap<(Address, Node, i64), BTreeSet<RTLReg>> = BTreeMap::new();
    let mut local_offsets: BTreeMap<(Address, RTLReg), BTreeSet<i64>> = BTreeMap::new();
    for &(f, n, o, r) in db.rel_iter::<(Address, Node, i64, RTLReg)>("stack_var") {
        locals.entry((f, n, o)).or_default().insert(canon(r));
        local_offsets.entry((f, canon(r))).or_default().insert(o);
    }
    let mut frames: BTreeMap<Address, BTreeSet<i64>> = BTreeMap::new();
    for &(f, _, _, size) in db.rel_iter::<(Address, Address, Symbol, u64)>("func_stacksz") {
        if let Ok(size) = i64::try_from(size) {
            frames.entry(f).or_default().insert(size);
        }
    }
    let mut chunks: BTreeMap<(Address, i64), usize> = BTreeMap::new();
    for &(f, o, c) in db.rel_iter::<(Address, i64, MemoryChunk)>("stack_var_chunk") {
        chunks
            .entry((f, o))
            .and_modify(|w| *w = (*w).max(chunk_byte_size(&c)))
            .or_insert(chunk_byte_size(&c));
    }
    let existing: BTreeSet<_> = db
        .rel_iter::<(Address, i64, RTLReg)>("slot_escaped_canonical")
        .map(|r| (r.0, r.1))
        .collect();
    let mut minimum_extents: BTreeMap<(Address, i64), i64> = BTreeMap::new();
    for &(f, base, offset, chunk) in
        db.rel_iter::<(Address, i64, i64, MemoryChunk)>("escaped_stack_region_field")
    {
        if let Some(high) = end(offset, chunk_byte_size(&chunk)) {
            minimum_extents
                .entry((f, base))
                .and_modify(|v| *v = (*v).max(high))
                .or_insert(high);
        }
    }
    let unknown_writes: BTreeSet<_> = db
        .rel_iter::<(Address, Node)>("unnormalized_frame_stack_write")
        .map(|r| r.0)
        .collect();
    let unknown_args: BTreeSet<_> = db
        .rel_iter::<(Address, Node, Mreg)>("semantic_unknown_reg_value_reaches_use")
        .copied()
        .collect();
    let mut bases: BTreeMap<Address, BTreeSet<i64>> = BTreeMap::new();
    for &(f, _, base) in db.rel_iter::<(Address, Node, i64)>("exact_frame_stack_lea") {
        bases.entry(f).or_default().insert(base);
    }
    for &(f, _, base, _, _, _, _) in &anchors {
        bases.entry(f).or_default().insert(base);
    }
    let mut setups: BTreeMap<(Node, Mreg), BTreeSet<Node>> = BTreeMap::new();
    for &(n, r, call) in db.rel_iter::<(Node, Mreg, Node)>("arg_setup_candidate") {
        setups.entry((n, r)).or_default().insert(call);
    }
    let positions: BTreeMap<_, _> = db
        .rel_iter::<(Mreg, usize)>("abi_int_arg_position")
        .copied()
        .collect();
    let mut registers: BTreeMap<(Node, Mreg), BTreeSet<RTLReg>> = BTreeMap::new();
    for &(n, r, value) in db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl") {
        registers.entry((n, r)).or_default().insert(value);
    }
    let mut args: BTreeMap<(Node, usize), BTreeSet<RTLReg>> = BTreeMap::new();
    for &(call, pos, value) in db.rel_iter::<(Node, usize, RTLReg)>("call_arg_mapping") {
        args.entry((call, pos)).or_default().insert(value);
    }
    let mut bindings: BTreeMap<(Address, i64), BTreeSet<(Node, usize, Mreg)>> = BTreeMap::new();
    for (&(call, position), values) in &args {
        if values.len() != 1 {
            continue;
        }
        for (&reg, &pos) in &positions {
            if pos != position {
                continue;
            }
            for &function in owners.get(&call).into_iter().flatten() {
                let origins = terms.frame_origins(function, call, reg);
                let base_set: BTreeSet<_> = origins
                    .iter()
                    .flat_map(|n| {
                        coordinates
                            .get(&(function, *n))
                            .into_iter()
                            .flatten()
                            .copied()
                    })
                    .collect();
                if !origins.is_empty()
                    && base_set.len() == 1
                    && origins
                        .iter()
                        .all(|n| coordinates.get(&(function, *n)) == Some(&base_set))
                {
                    let base = *base_set.first().unwrap();
                    bindings
                        .entry((function, base))
                        .or_default()
                        .insert((call, position, reg));
                }
            }
        }
    }
    let mut targets: BTreeMap<Node, BTreeSet<Address>> = BTreeMap::new();
    for &(call, target) in db.rel_iter::<(Node, Address)>("call_target_func") {
        targets.entry(call).or_default().insert(target);
    }
    let mut fields: BTreeMap<(Address, usize), BTreeSet<(Node, i64, MemoryChunk)>> =
        BTreeMap::new();
    for &(f, pos, witness, offset, chunk) in
        db.rel_iter::<(Address, usize, Node, i64, MemoryChunk)>("semantic_parameter_field")
    {
        if offset >= 0 && storage_chunk(chunk_byte_size(&chunk)).is_some() {
            fields
                .entry((f, pos))
                .or_default()
                .insert((witness, offset, chunk));
        }
    }
    let (accesses, unmapped) = frame_accesses(db);
    let mut attempted = BTreeSet::new();
    for (function, anchor, base, scale, index, destination, bits) in anchors {
        let mut event = Event::new(function, anchor, base);
        out.obligations.push(event.clone());
        let reject = |out: &mut Refinement, event: &Event, reason| {
            out.obligations
                .push(event.at(Stage::Anchor, Outcome::Unsupported, reason));
        };
        if bits as usize != db.abi().pointer_size * 8 || scale <= 0 {
            reject(out, &event, "unsupported machine address width or scale");
            continue;
        }
        if owners.get(&anchor) != Some(&BTreeSet::from([function]))
            || shifts.get(&(function, anchor)) != Some(&BTreeSet::from([0]))
        {
            reject(
                out,
                &event,
                "ambiguous ownership or unsupported frame coordinate",
            );
            continue;
        }
        if existing.contains(&(function, base)) {
            reject(
                out,
                &event,
                "existing storage representation outside this synthesis domain",
            );
            continue;
        }
        let group = &groups[&(function, base)];
        if group.iter().any(|&(node, _, _, scale, bits)| {
            bits as usize != db.abi().pointer_size * 8
                || scale <= 0
                || coordinates.get(&(function, node)) != Some(&BTreeSet::from([base]))
                || owners.get(&node) != Some(&BTreeSet::from([function]))
                || shifts.get(&(function, node)) != Some(&BTreeSet::from([0]))
        }) {
            reject(
                out,
                &event,
                "joint anchors disagree about ownership or frame coordinates",
            );
            continue;
        }
        if out
            .pending
            .iter()
            .any(|r| (r.problem.function, r.problem.base) == (function, base))
            || !attempted.insert((function, base))
        {
            continue;
        }
        if out.pending.len() >= MAX_OBJECTS || unknown_writes.contains(&function) {
            reject(
                out,
                &event,
                "resource limit or unknown physical frame write",
            );
            continue;
        }
        let Some(root_set) = locals
            .get(&(function, anchor, base))
            .filter(|r| !r.is_empty())
        else {
            reject(out, &event, "missing frame storage identity");
            continue;
        };
        if root_set
            .iter()
            .any(|r| local_offsets.get(&(function, *r)) != Some(&BTreeSet::from([base])))
        {
            reject(
                out,
                &event,
                "one value web names different frame coordinates",
            );
            continue;
        }
        let root = *root_set.first().unwrap();
        // Confirm the initial RTL epoch still expresses the decoder's exact
        // stack base. The anchor remains recorded even when lowering lost it.
        let base_values: BTreeSet<_> = db
            .rel_iter::<(Node, RTLInst)>("rtl_inst_candidate")
            .filter_map(|(n, inst)| {
                if *n != anchor {
                    return None;
                }
                match inst {
                    RTLInst::Iop(Operation::Oleal(Addressing::Ainstack(o)), a, value)
                        if *o == base && a.is_empty() =>
                    {
                        Some(canonical.get(value).copied().unwrap_or(*value))
                    }
                    _ => None,
                }
            })
            .collect();
        if base_values.len() != 1 {
            reject(
                out,
                &event,
                "machine anchor lacks an exact RTL address expression",
            );
            continue;
        }
        let Some(frame_size) = frames
            .get(&function)
            .filter(|s| s.len() == 1)
            .and_then(|s| s.first())
            .copied()
        else {
            reject(out, &event, "ambiguous frame bounds");
            continue;
        };
        let mut call_fields = BTreeSet::new();
        let mut calls = BTreeSet::new();
        let mut call_contracts = BTreeMap::new();
        let mut unmodeled_binding = false;
        for &(call, position, argument_register) in
            bindings.get(&(function, base)).into_iter().flatten()
        {
            if unknown_args.contains(&(function, call, argument_register))
                || owners.get(&call) != Some(&BTreeSet::from([function]))
            {
                unmodeled_binding = true;
                break;
            }
            let Some(target) = targets
                .get(&call)
                .filter(|t| t.len() == 1)
                .and_then(|t| t.first())
            else {
                unmodeled_binding = true;
                break;
            };
            let Some(observed) = fields.get(&(*target, position)) else {
                unmodeled_binding = true;
                break;
            };
            calls.insert(call);
            call_contracts.insert((call, position, argument_register), observed.clone());
            call_fields.extend(observed.iter().map(|&(_, offset, chunk)| (offset, chunk)));
        }
        if unmodeled_binding {
            reject(
                out,
                &event,
                "a frame call binding lacks an exact observation contract",
            );
            continue;
        }
        let Some(&call) = calls.first() else {
            reject(out, &event, "no exact internal-call observation contract");
            continue;
        };
        event.call = call;
        let (mut writes, mut reads) = accesses.get(&function).cloned().unwrap_or_default();
        writes.sort_by_key(|a| (a.node, a.offset, a.width));
        writes.dedup();
        reads.sort_by_key(|a| (a.node, a.offset, a.width));
        reads.dedup();
        if call_fields.len() > MAX_ACCESSES || writes.len() + reads.len() > MAX_ACCESSES {
            reject(out, &event, "storage access budget");
            continue;
        }
        let roots: Vec<_> = group
            .iter()
            .map(|&(n, dst, index, scale, _)| (n, dst, index, scale))
            .collect();
        let mut views = Vec::new();
        let mut materialized_extent = 0;
        let mut view_failure = None;
        for (&(call, _, register), observations) in &call_contracts {
            let pointer = terms.pointer_group(function, call, register, &roots);
            match symbolic::affine_view(&pointer, frame_size.saturating_sub(base)) {
                Ok((relative, extent)) => {
                    materialized_extent = materialized_extent.max(extent);
                    let observations: Vec<_> = observations
                        .iter()
                        .map(|&(_, offset, chunk)| (offset, chunk_byte_size(&chunk)))
                        .collect();
                    let end = observations
                        .iter()
                        .filter_map(|&(o, w)| end(o, w))
                        .max()
                        .unwrap_or(0);
                    match symbolic::maximum_delta(
                        &relative,
                        1,
                        frame_size.saturating_sub(base).saturating_sub(end),
                    ) {
                        Bound::Proven(maximum_delta) => views.push(ObservedView {
                            call,
                            observations,
                            index: symbolic::Index {
                                expression: relative,
                                scale: 1,
                                maximum_delta,
                            },
                        }),
                        other => {
                            view_failure = Some(other);
                            break;
                        }
                    }
                }
                Err(reason) => {
                    view_failure = Some(reason);
                    break;
                }
            }
        }
        if let Some(reason) = view_failure {
            out.obligations.push(event.at(
                Stage::Representation,
                if reason == Bound::Unknown {
                    Outcome::Unknown
                } else {
                    Outcome::Unsupported
                },
                "compositional frame-address view is not established",
            ));
            continue;
        }
        let problem = Problem {
            function,
            base,
            call,
            lea: anchor,
            anchors: view_sites[&(function, base)].iter().copied().collect(),
            root,
            frame_size,
            observations: call_fields
                .iter()
                .map(|(o, c)| (*o, chunk_byte_size(c)))
                .collect(),
            fields: Vec::new(),
            writes,
            reads,
            other_roots: bases
                .get(&function)
                .into_iter()
                .flatten()
                .filter(|o| **o != base)
                .copied()
                .collect(),
            index: None,
            views,
            minimum_extent: minimum_extents
                .get(&(function, base))
                .copied()
                .unwrap_or(0)
                .max(materialized_extent),
        };
        // The initial scalar interpretation has no address/value bridge for
        // the synthetic frame base. A scalar's bytes are not its address.
        let initial = Representation {
            address_preserved: !root_set.contains(base_values.first().unwrap()),
            argument: View {
                object: StorageId::Scalar(root),
                offset: 0,
                extent: chunks.get(&(function, base)).copied().unwrap_or(4) as i64,
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
        out.pending.push(Prepared {
            problem,
            initial,
            unmapped: unmapped.get(&function).cloned().unwrap_or_default(),
            candidate_writes: BTreeMap::new(),
        });
        out.records.push(RefinementRecord {
            function,
            base,
            call,
            extent: 0,
            constructed: false,
            validated: false,
            regenerated: false,
            reason: "pending final-selection storage theory",
        });
    }
}
