//! Machine observation boundaries shared by the selection validators.
//!
//! Physical operand widths and transparent CFG edges survive promotion and
//! branch-threading without borrowing facts from a candidate C expression.
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::clight_select::query::FunctionData;
use crate::decompile::passes::clight_select::syntax::{ArtifactKey, Artifacts};
use crate::x86::types::*;
use ascent::{ascent, lattice::set::Set};
use std::collections::{BTreeMap, BTreeSet};

pub(super) const INPUTS: &[&str] = &[
    "machine_comparison_view",
    "instr_in_function",
    "instruction",
    "rtl_inst",
    "rtl_succ",
];
const OBSERVATIONS: ArtifactKey<Observations> = ArtifactKey::new("native-observations");

#[derive(Default, Clone, Debug)]
pub(crate) struct Observations {
    pub comparisons: BTreeMap<Node, u32>,
    targets: BTreeMap<Node, Node>,
}

ascent! {
    struct Endpoints;
    relation terminal(Address, Node);
    relation silent_edge(Address, Node, Node);
    // Each node has at most one successor here. The lattice payload is a
    // singleton endpoint, not a materialized transitive reachability relation.
    lattice endpoint(Address, Node, Set<Node>);
    endpoint(*f, *n, Set(BTreeSet::from([*n]))) <-- terminal(f, n);
    endpoint(*f, *n, endpoint.clone()) <--
        silent_edge(f, n, next), endpoint(f, next, endpoint);
}

pub(super) fn collect(db: &DecompileDB, functions: &mut [FunctionData]) {
    let mut owners = BTreeMap::<Node, BTreeSet<Address>>::new();
    for &(node, owner) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        owners.entry(node).or_default().insert(owner);
    }
    let mut instructions = BTreeMap::<Node, BTreeSet<Symbol>>::new();
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
        instructions.entry(row.0).or_default().insert(row.3);
    }
    let mut rtl = BTreeMap::<Node, Option<RTLInst>>::new();
    for (node, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        rtl.entry(*node)
            .and_modify(|old| {
                if old.as_ref() != Some(inst) {
                    *old = None;
                }
            })
            .or_insert_with(|| Some(inst.clone()));
    }
    let mut successors = BTreeMap::<Node, BTreeSet<Node>>::new();
    for &(node, next) in db.rel_iter::<(Node, Node)>("rtl_succ") {
        successors.entry(node).or_default().insert(next);
    }
    let mut program = Endpoints::default();
    for (&node, node_owners) in &owners {
        let transparent = instructions
            .get(&node)
            .filter(|v| v.len() == 1)
            .and_then(|v| v.first())
            .is_some_and(|m| matches!(*m, "NOP" | "JMP"));
        let next = successors
            .get(&node)
            .filter(|s| s.len() == 1)
            .and_then(|s| s.first());
        for &owner in node_owners {
            let silent = next.filter(|next| {
                transparent
                    && owners.get(next) == Some(node_owners)
                    && node_owners.len() == 1
                    && match rtl.get(&node).and_then(Option::as_ref) {
                        Some(RTLInst::Inop) => true,
                        Some(RTLInst::Ibranch(either::Either::Right(target))) => target == *next,
                        _ => false,
                    }
            });
            if let Some(&next) = silent {
                program.silent_edge.push((owner, node, next));
            } else {
                program.terminal.push((owner, node));
            }
        }
    }
    program.run();
    let mut observations = BTreeMap::<Address, Observations>::new();
    for (owner, node, endpoints) in program.endpoint {
        if endpoints.len() == 1 {
            observations
                .entry(owner)
                .or_default()
                .targets
                .insert(node, *endpoints.iter().next().unwrap());
        }
    }
    let mut widths = BTreeMap::<Node, BTreeSet<u32>>::new();
    for &(node, bits) in db.rel_iter::<(Node, u32)>("machine_comparison_view") {
        widths.entry(node).or_default().insert(bits);
    }
    for (node, widths) in widths {
        if widths.len() != 1 {
            continue;
        }
        let bits = *widths.first().unwrap();
        if !matches!(bits, 8 | 16 | 32 | 64) {
            continue;
        }
        for &owner in owners.get(&node).into_iter().flatten() {
            observations
                .entry(owner)
                .or_default()
                .comparisons
                .insert(node, bits);
        }
    }
    for function in functions {
        OBSERVATIONS.insert(
            &mut function.analysis_facts,
            observations.remove(&function.address).unwrap_or_default(),
        );
    }
}

pub(crate) fn comparison_width(facts: &Artifacts, node: Node) -> Option<u32> {
    OBSERVATIONS.get(facts)?.comparisons.get(&node).copied()
}

pub(crate) fn same_target(facts: &Artifacts, a: Node, b: Node) -> bool {
    a == b
        || OBSERVATIONS.get(facts).is_some_and(|o| {
            o.targets
                .get(&a)
                .is_some_and(|target| o.targets.get(&b) == Some(target))
        })
}

#[cfg(test)]
pub(crate) fn set_comparison(facts: &mut Artifacts, node: Node, bits: u32) {
    OBSERVATIONS.insert(
        facts,
        Observations {
            comparisons: BTreeMap::from([(node, bits)]),
            ..Default::default()
        },
    );
}

#[cfg(test)]
mod tests {
    use crate::decompile::passes::clight_select::solvers::observations::*;

    #[test]
    fn branch_threading_uses_cfg_edges_and_does_not_erase_cycles_or_effects() {
        let mut db = DecompileDB::default();
        // Deliberately scrambled ids. 900 -> 30 -> 400 is the silent path;
        // adjacent node 31 is unrelated; 700 <-> 800 is an infinite loop.
        for (node, next, mnemonic) in [
            (900_u64, 30_u64, "NOP"),
            (30, 400, "JMP"),
            (31, 400, "ADD"),
            (700, 800, "JMP"),
            (800, 700, "JMP"),
        ] {
            db.rel_push("instr_in_function", (node, 1_u64));
            db.rel_push(
                "instruction",
                (
                    node, 1_usize, "", mnemonic, "", "", "", "", 0_usize, 0_usize,
                ),
            );
            db.rel_push(
                "rtl_inst",
                (node, RTLInst::Ibranch(either::Either::Right(next))),
            );
            db.rel_push("rtl_succ", (node, next));
        }
        db.rel_push("instr_in_function", (400_u64, 1_u64));
        let mut f = FunctionData::new(1, "endpoints".into(), vec![], vec![], None, 0, 900, true);
        collect(&db, std::slice::from_mut(&mut f));
        assert!(same_target(&f.analysis_facts, 900, 400));
        assert!(!same_target(&f.analysis_facts, 31, 400));
        assert!(!same_target(&f.analysis_facts, 700, 800));
        assert!(same_target(&f.analysis_facts, 700, 700));
    }
}
