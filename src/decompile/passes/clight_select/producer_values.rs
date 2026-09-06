//! Pure producer equalities at a queried use, certified by RTL availability.
//!
//! These are semantic input relations, not candidate-derived assumptions. The
//! producer's operands are unchanged on every entry-to-use path. Only one pure
//! producer is expanded; nested producers need availability at the final use,
//! not merely at an intermediate node. Memory and call results stay opaque.

use std::collections::{BTreeMap, BTreeSet};

use super::query::FunctionData;
use crate::decompile::elevator::DecompileDB;
use crate::mreg::Mreg;
use crate::x86::op::Operation;
use crate::x86::types::*;

pub(crate) const INPUTS: &[&str] = &[
    "rtl_available_value",
    "rtl_inst",
    "instr_in_function",
    "ltl_inst",
    "machine_register_write_view",
    "instruction",
    "rtl_function_entry",
    "rtl_succ",
];

#[derive(Clone, Debug)]
pub(crate) struct Producer {
    pub definition: Node,
    pub operation: Operation,
    pub arguments: Args,
    /// Exact decoder destination view, not the guessed C declaration width.
    pub write_bits: Option<u32>,
}

pub(crate) fn collect(db: &DecompileDB, functions: &mut [FunctionData]) {
    let mut instructions: BTreeMap<Node, Option<RTLInst>> = BTreeMap::new();
    for (node, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        instructions
            .entry(*node)
            .and_modify(|old| {
                if old.as_ref() != Some(inst) {
                    *old = None;
                }
            })
            .or_insert_with(|| Some(inst.clone()));
    }
    let mut owners: BTreeMap<Node, BTreeSet<Address>> = BTreeMap::new();
    for &(node, function) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        owners.entry(node).or_default().insert(function);
    }
    let mut destinations: BTreeMap<Node, BTreeSet<Mreg>> = BTreeMap::new();
    for (node, inst) in db.rel_iter::<(Node, LTLInst)>("ltl_inst") {
        if let LTLInst::Lop(_, _, dst)
        | LTLInst::Lgetstack(_, _, _, dst)
        | LTLInst::Lload(_, _, _, dst) = inst
        {
            destinations.entry(*node).or_default().insert(*dst);
        }
    }
    let mut mnemonics: BTreeMap<Node, BTreeSet<Symbol>> = BTreeMap::new();
    for row in db.rel_iter::<(
        Address,
        usize,
        Symbol,
        Symbol,
        Symbol,
        Symbol,
        Symbol,
        Symbol,
        usize,
        usize,
    )>("instruction")
    {
        mnemonics.entry(row.0).or_default().insert(row.3);
    }
    let mut widths: BTreeMap<(Node, Mreg), BTreeSet<u32>> = BTreeMap::new();
    for &(node, register, bits) in db.rel_iter::<(Node, Mreg, u32)>("machine_register_write_view") {
        widths.entry((node, register)).or_default().insert(bits);
    }
    let decoded_bits = |node: Node| {
        destinations
            .get(&node)
            .filter(|r| r.len() == 1)
            .and_then(|r| r.first())
            .filter(|r| matches!(r, Mreg::X86(_)))
            .and_then(|r| widths.get(&(node, *r)))
            .filter(|w| w.len() == 1)
            .and_then(|w| w.first())
            .copied()
    };
    super::word_inputs::collect(db, functions, &instructions, &owners, &decoded_bits);
    let mut equalities: BTreeMap<(Address, Node, RTLReg), BTreeSet<Node>> = BTreeMap::new();
    for &(function, usage, register, definition) in
        db.rel_iter::<(Address, Node, RTLReg, Node)>("rtl_available_value")
    {
        equalities
            .entry((function, usage, register))
            .or_default()
            .insert(definition);
    }
    for function in functions {
        function.value_producers.clear();
        for read in &mut function.storage_reads {
            read.write_bits = decoded_bits(read.node);
            read.signed_word_load = read.width == 4
                && read.write_bits == Some(64)
                && mnemonics
                    .get(&read.node)
                    .filter(|m| m.len() == 1)
                    .and_then(|m| m.first())
                    .is_some_and(|m| matches!(*m, "MOVSX" | "MOVSXD"));
        }
        let effect_nodes: BTreeSet<_> = function
            .storage_writes
            .iter()
            .map(|w| w.node)
            .chain(function.word_inputs.keys().copied())
            .collect();
        for (&(owner, usage, register), definitions) in &equalities {
            if owner != function.address || definitions.len() != 1 || !effect_nodes.contains(&usage)
            {
                continue;
            }
            let definition = *definitions.first().unwrap();
            let sole_owner = BTreeSet::from([owner]);
            if owners.get(&definition) != Some(&sole_owner)
                || owners.get(&usage) != Some(&sole_owner)
            {
                continue;
            }
            let Some(Some(RTLInst::Iop(operation, arguments, destination))) =
                instructions.get(&definition)
            else {
                continue;
            };
            if *destination != register || arguments.contains(destination) || definition == usage {
                continue;
            }
            let write_bits = decoded_bits(definition);
            function.value_producers.insert(
                (usage, register),
                Producer {
                    definition,
                    operation: operation.clone(),
                    arguments: arguments.clone(),
                    write_bits,
                },
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::passes::clight_select::memory_theory::WriteContract;
    use crate::decompile::passes::semantic_counterexample::ledger::ObjectId;
    use std::sync::Arc;

    fn fixture() -> (DecompileDB, FunctionData) {
        let mut db = DecompileDB::default();
        db.rel_push(
            "rtl_inst",
            (
                90_u64,
                RTLInst::Iop(Operation::Ointconst(7), Arc::new(vec![]), 7),
            ),
        );
        db.rel_push("instr_in_function", (90_u64, 1_u64));
        db.rel_push("instr_in_function", (30_u64, 1_u64));
        db.rel_push(
            "ltl_inst",
            (
                90_u64,
                LTLInst::Lop(Operation::Ointconst(7), Arc::new(vec![]), Mreg::AX),
            ),
        );
        db.rel_push("machine_register_write_view", (90_u64, Mreg::AX, 32_u32));
        let mut function =
            FunctionData::new(1, "producer".into(), vec![], vec![], None, 32, 90, true);
        function.storage_writes.push(WriteContract {
            object: ObjectId {
                function: 1,
                base: 0,
            },
            node: 30,
            root: 10,
            offset: 4,
            width: 4,
            locals: BTreeSet::from([12]),
        });
        (db, function)
    }

    #[test]
    fn collection_requires_an_explicit_availability_certificate() {
        let (mut db, mut function) = fixture();
        collect(&db, std::slice::from_mut(&mut function));
        assert!(function.value_producers.is_empty());
        db.rel_push("rtl_available_value", (1_u64, 30_u64, 7_u64, 90_u64));
        collect(&db, std::slice::from_mut(&mut function));
        let producer = &function.value_producers[&(30, 7)];
        assert_eq!(producer.definition, 90);
        assert_eq!(producer.write_bits, Some(32));
        assert_eq!(producer.operation, Operation::Ointconst(7));
    }

    #[test]
    fn competing_definitions_or_owners_cannot_supply_a_value_equation() {
        for ambiguous_definition in [false, true] {
            let (mut db, mut function) = fixture();
            db.rel_push("rtl_available_value", (1_u64, 30_u64, 7_u64, 90_u64));
            if ambiguous_definition {
                db.rel_push(
                    "rtl_inst",
                    (
                        90_u64,
                        RTLInst::Iop(Operation::Ointconst(8), Arc::new(vec![]), 7),
                    ),
                );
            } else {
                db.rel_push("instr_in_function", (90_u64, 2_u64));
            }
            collect(&db, std::slice::from_mut(&mut function));
            assert!(function.value_producers.is_empty());
        }
    }
}
