//! CFG-derived representation relations for frame values used as machine words.
//!
//! A C signed 32-bit carrier can hold a register's low bits faithfully while
//! C's later sign extension differs from the machine's zeroed upper word.
//! Track that fact at the USE, not by declaration spelling or instruction order.
//! The state is a point-keyed must lattice, bounded to 128 demanded frame-value
//! registers per function. Calls and unknown effects conservatively kill it.

use super::query::FunctionData;
use crate::decompile::elevator::DecompileDB;
use crate::x86::types::*;
use ascent::{
    ascent,
    lattice::{Dual, set::Set},
};
use std::collections::{BTreeMap, BTreeSet};

const MAX_TRACKED: usize = 128;

fn transfer(state: &Set<RTLReg>, inst: &RTLInst, introduced: &Set<RTLReg>) -> Set<RTLReg> {
    if matches!(
        inst,
        RTLInst::Icall(..) | RTLInst::Itailcall(..) | RTLInst::Ibuiltin(..)
    ) {
        return Set::default();
    }
    let definition = crate::decompile::passes::rtl_optimize_pass::inst_def_use(inst).0;
    let mut next = state.0.clone();
    if let Some(reg) = definition {
        next.remove(&reg);
    }
    next.extend(introduced.0.iter().copied());
    Set(next)
}

ascent! {
    struct WordInputs;
    relation instruction(Node, RTLInst);
    relation owner(Address, Node);
    relation entry(Address, Node);
    relation successor(Node, Node);
    relation introduced(Address, Node, Set<RTLReg>);
    relation query(Address, Node, RTLReg);
    lattice before(Address, Node, Dual<Set<RTLReg>>);
    before(*function, *node, Dual(Set::default())) <-- entry(function, node);
    before(*function, *next, Dual(transfer(&state.0, inst, introduced))) <--
        before(function, node, state), successor(node, next),
        owner(function, next), instruction(node, inst), introduced(function, node, introduced);
    before(*function, *next, Dual(Set::default())) <--
        before(function, node, _), successor(node, next), owner(function, next), !instruction(node, _);
    relation known(Address, Node, RTLReg);
    known(*function, *node, *register) <-- query(function, node, register), before(function, node, state),
        if state.0.contains(register);
}

pub(crate) fn collect(
    db: &DecompileDB,
    functions: &mut [FunctionData],
    instructions: &BTreeMap<Node, Option<RTLInst>>,
    owners: &BTreeMap<Node, BTreeSet<Address>>,
    decoded_bits: &impl Fn(Node) -> Option<u32>,
) {
    let mut entries: BTreeMap<Address, BTreeSet<Node>> = BTreeMap::new();
    for &(function, entry) in db.rel_iter::<(Address, Node)>("rtl_function_entry") {
        entries.entry(function).or_default().insert(entry);
    }
    let mut demands: BTreeMap<Address, BTreeSet<RTLReg>> = BTreeMap::new();
    let mut program = WordInputs::default();
    for function in functions.iter_mut() {
        function.word_inputs.clear();
        if !function.ptr64 {
            continue;
        }
        let tracked: BTreeSet<_> = function
            .storage_reads
            .iter()
            .map(|r| r.destination)
            .collect();
        if tracked.is_empty() || tracked.len() > MAX_TRACKED {
            continue;
        }
        let Some(entry) = entries
            .get(&function.address)
            .filter(|e| e.len() == 1)
            .and_then(|e| e.first())
        else {
            continue;
        };
        program.entry.push((function.address, *entry));
        for (&node, candidates) in &function.node_statements {
            let mut uses = BTreeSet::new();
            for candidate in candidates {
                if let ClightStmt::Sset(_, _) = super::memory_theory::primitive(candidate) {
                    uses.extend(
                        crate::decompile::passes::cminor_pass::extract_var_reads_from_stmt(
                            super::memory_theory::primitive(candidate),
                        )
                        .into_iter()
                        .map(|r| r as RTLReg),
                    );
                }
            }
            for register in uses.intersection(&tracked) {
                program.query.push((function.address, node, *register));
            }
        }
        demands.insert(function.address, tracked);
    }
    if demands.is_empty() {
        return;
    }
    for (&node, owner_set) in owners {
        for function in owner_set {
            let Some(tracked) = demands.get(function) else {
                continue;
            };
            program.owner.push((*function, node));
            let mut introduced = BTreeSet::new();
            if decoded_bits(node) == Some(32) {
                if let Some(Some(inst)) = instructions.get(&node) {
                    if let Some(destination) =
                        crate::decompile::passes::rtl_optimize_pass::inst_def_use(inst).0
                    {
                        if tracked.contains(&destination) {
                            introduced.insert(destination);
                        }
                    }
                }
            }
            program.introduced.push((*function, node, Set(introduced)));
        }
    }
    for (&node, inst) in instructions {
        if let Some(inst) = inst {
            program.instruction.push((node, inst.clone()));
        }
    }
    program
        .successor
        .extend(db.rel_iter::<(Node, Node)>("rtl_succ").copied());
    program.run();
    let mut facts: BTreeMap<Address, BTreeMap<Node, BTreeSet<RTLReg>>> = BTreeMap::new();
    for (function, node, register) in program.known {
        facts
            .entry(function)
            .or_default()
            .entry(node)
            .or_default()
            .insert(register);
    }
    for function in functions {
        function.word_inputs = facts.remove(&function.address).unwrap_or_default();
        // New input views can make an originally singleton operation
        // refinable. Its anchor still comes from unique finalized RTL.
        for node in function.word_inputs.keys() {
            if let Some(Some(inst @ RTLInst::Iop(..))) = instructions.get(node) {
                function.integer_anchors.insert(*node, inst.clone());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::x86::op::Operation;
    use std::sync::Arc;

    #[test]
    fn word_facts_follow_cfg_paths_and_die_at_redefinition_or_call() {
        for variant in 0..4 {
            let mut p = WordInputs::default();
            for node in [1, 90, 80, 30] {
                p.owner.push((1, node));
                p.introduced.push((
                    1,
                    node,
                    if node == 90 {
                        Set::singleton(13)
                    } else {
                        Set::default()
                    },
                ));
            }
            p.instruction.push((1, RTLInst::Inop));
            p.instruction.push((
                90,
                RTLInst::Iload(
                    MemoryChunk::MAny32,
                    crate::x86::op::Addressing::Ainstack(0),
                    Arc::new(vec![]),
                    13,
                ),
            ));
            p.instruction.push((30, RTLInst::Ireturn(13)));
            let middle = match variant {
                2 => RTLInst::Iop(Operation::Olongconst(-1), Arc::new(vec![]), 13),
                3 => RTLInst::Ibuiltin("unknown_effect".into(), vec![], BuiltinArg::BAInt(0)),
                _ => RTLInst::Inop,
            };
            p.instruction.push((80, middle));
            p.entry.push((1, 1));
            p.successor.extend([(1, 90), (90, 80), (80, 30)]);
            if variant == 1 {
                p.successor.push((1, 30));
            }
            p.query.push((1, 30, 13));
            p.run();
            assert_eq!(!p.known.is_empty(), variant == 0,
                "numeric node order is not availability; a bypass/redefinition/call must invalidate it");
        }
    }

    #[test]
    fn a_backedge_definition_does_not_prove_the_first_iteration_input() {
        let mut p = WordInputs::default();
        for node in [1, 30, 90, 10] {
            p.owner.push((1, node));
            p.instruction.push((node, RTLInst::Inop));
            p.introduced.push((
                1,
                node,
                if node == 90 {
                    Set::singleton(13)
                } else {
                    Set::default()
                },
            ));
        }
        p.entry.push((1, 1));
        p.successor.extend([(1, 30), (30, 90), (90, 30), (30, 10)]);
        p.query.push((1, 30, 13));
        p.query.push((1, 10, 13));
        p.run();
        assert!(p.known.is_empty());
    }
}
