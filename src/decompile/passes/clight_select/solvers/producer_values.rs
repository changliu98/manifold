//! Pure producer equalities at a queried use, certified by RTL availability.
//!
//! These are semantic input relations, not candidate-derived assumptions. The
//! producer's operands are unchanged on every entry-to-use path. Only one pure
//! producer is expanded; nested producers need availability at the final use,
//! not merely at an intermediate node. Memory and call results stay opaque.

use std::collections::{BTreeMap, BTreeSet};

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::clight_select::query::FunctionData;
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
    // This collection can run again after binding recovery adds demands.
    // Interpret native read/write identities in that same vocabulary before
    // running any CFG analysis, not by renaming only its conclusions.
    let plans: BTreeMap<_, _> = functions
        .iter()
        .filter_map(|function| {
            crate::decompile::passes::clight_select::syntax::bindings::PLAN
                .get(&function.analysis_facts)
                .map(|plan| (function.address, plan.clone()))
        })
        .collect();
    for (&node, instruction) in &mut instructions {
        if let Some(plan) = owners
            .get(&node)
            .filter(|owners| owners.len() == 1)
            .and_then(|owners| owners.first())
            .and_then(|owner| plans.get(owner))
        {
            *instruction = instruction.as_ref().map(|inst| plan.native(node, inst));
        }
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
    crate::decompile::passes::clight_select::solvers::word_inputs::collect(
        db,
        functions,
        &instructions,
        &owners,
        &decoded_bits,
    );
    let mut equalities: BTreeMap<(Address, Node, RTLReg), BTreeSet<Node>> = BTreeMap::new();
    for &(function, usage, register, definition) in
        db.rel_iter::<(Address, Node, RTLReg, Node)>("rtl_available_value")
    {
        let register = plans
            .get(&function)
            .map_or(register, |plan| plan.read(usage, register));
        equalities
            .entry((function, usage, register))
            .or_default()
            .insert(definition);
    }
    let mut entries = BTreeMap::<Address, BTreeSet<Node>>::new();
    for &(owner, entry) in db.rel_iter::<(Address, Node)>("rtl_function_entry") {
        entries.entry(owner).or_default().insert(entry);
    }
    let edges: Vec<_> = db.rel_iter::<(Node, Node)>("rtl_succ").copied().collect();
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
            .chain(function.integer_anchors.keys().copied())
            .collect();
        if let Some(&entry) = entries
            .get(&function.address)
            .filter(|e| e.len() == 1)
            .and_then(|e| e.first())
        {
            let sole_owner = BTreeSet::from([function.address]);
            let native: BTreeMap<_, _> = instructions
                .iter()
                .filter_map(|(&node, inst)| {
                    (owners.get(&node) == Some(&sole_owner))
                        .then(|| inst.clone().map(|i| (node, i)))
                        .flatten()
                })
                .collect();
            let mut definitions = BTreeMap::<RTLReg, BTreeSet<Node>>::new();
            for (&node, inst) in &native {
                if let Some(reg) = crate::decompile::passes::rtl_optimize_pass::inst_def_use(inst).0
                {
                    definitions.entry(reg).or_default().insert(node);
                }
            }
            let mut queries = BTreeSet::new();
            for &usage in &effect_nodes {
                let Some(inst) = native.get(&usage) else {
                    continue;
                };
                for reg in crate::decompile::passes::rtl_optimize_pass::inst_def_use(inst).1 {
                    let Some(&definition) = definitions
                        .get(&reg)
                        .filter(|d| d.len() == 1)
                        .and_then(|d| d.first())
                    else {
                        continue;
                    };
                    let Some(RTLInst::Iop(_, args, _)) = native.get(&definition) else {
                        continue;
                    };
                    if args.is_empty() {
                        continue;
                    }
                    let demanded = function
                        .node_statements
                        .get(&usage)
                        .into_iter()
                        .flatten()
                        .any(|s| {
                            let deps = crate::decompile::passes::clight_select::syntax::declarations::dependencies(s);
                            !deps.contains(&reg) && args.iter().all(|a| deps.contains(a))
                        });
                    if demanded {
                        queries.insert((definition, reg, usage));
                    }
                }
            }
            if !queries.is_empty() {
                let queries: Vec<_> = queries.into_iter().collect();
                for (definition, reg, usage) in
                    crate::decompile::passes::rtl_optimize_pass::available_value_queries(
                        entry, &native, &edges, &queries,
                    )
                {
                    equalities
                        .entry((function.address, usage, reg))
                        .or_default()
                        .insert(definition);
                }
            }
        }
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
    use crate::decompile::passes::clight_select::solvers::memory_theory::WriteContract;
    use crate::decompile::passes::clight_select::solvers::producer_values::*;
    use crate::decompile::passes::semantic_counterexample::ledger::ObjectId;
    use std::sync::Arc;

    #[test]
    fn queried_value_availability_is_structural_and_unknown_paths_kill_it() {
        use crate::decompile::passes::rtl_optimize_pass::available_value_queries;
        let instructions = BTreeMap::from([
            (90, RTLInst::Inop),
            (80, RTLInst::Iop(Operation::Omove, Arc::new(vec![1]), 2)),
            (
                4,
                RTLInst::Iop(Operation::Oaddlimm(1), Arc::new(vec![2]), 3),
            ),
        ]);
        let query = [(80, 2, 4)];
        assert_eq!(
            available_value_queries(90, &instructions, &[(90, 80), (80, 4)], &query),
            BTreeSet::from(query)
        );
        assert!(available_value_queries(
            90,
            &instructions,
            &[(90, 80), (80, 4), (90, 7), (7, 4)],
            &query
        )
        .is_empty());
        let mut overwritten = instructions.clone();
        overwritten.insert(
            7,
            RTLInst::Iop(Operation::Ointconst(0), Arc::new(vec![]), 1),
        );
        assert!(
            available_value_queries(90, &overwritten, &[(90, 80), (80, 7), (7, 4)], &query)
                .is_empty()
        );
    }

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
