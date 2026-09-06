//! Exact reuse of a pure Ascent fixpoint across representation-inference epochs.
//!
//! Equality is over complete input fact SETS, not hashes, addresses, or a
//! guessed "unaffected function" set. Only the latest key/result per entry is
//! retained. Internal reachability/dominance lattices are never cached or
//! exported, and a miss always runs the original rules from empty outputs.

use super::{CsharpminorStmt, Node, RTLReg, StructuringProgram};
use std::collections::{HashMap, HashSet};
use std::sync::Mutex;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Inputs {
    stmt: HashSet<(Node, CsharpminorStmt)>,
    seq_next: HashSet<(Node, Node)>,
    jumptable_target: HashSet<(Node, Node)>,
    entry_node: HashSet<(Node,)>,
    packed_alu_node: HashSet<(Node,)>,
    optimized_gap_node: HashSet<(Node,)>,
    pointer_reg: HashSet<(RTLReg,)>,
}

impl Inputs {
    fn from_program(p: &StructuringProgram) -> Self {
        Self {
            stmt: p.stmt.iter().cloned().collect(),
            seq_next: p.seq_next.iter().copied().collect(),
            jumptable_target: p.jumptable_target.iter().copied().collect(),
            entry_node: p.entry_node.iter().copied().collect(),
            packed_alu_node: p.packed_alu_node.iter().copied().collect(),
            optimized_gap_node: p.optimized_gap_node.iter().copied().collect(),
            pointer_reg: p.pointer_reg.iter().copied().collect(),
        }
    }
}

/// Only facts actually consumed by structure(), not the large analysis DB.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct Facts {
    pub join_point: Vec<(Node, Node)>,
    pub scond_node: Vec<(Node, Node, Node)>,
    pub scond_no_join: Vec<(Node,)>,
    pub ifbody_true: Vec<(Node, Node)>,
    pub ifbody_false: Vec<(Node, Node)>,
    pub vec_bypass_rewrite: Vec<(Node, Node)>,
    pub trim_node: Vec<(Node,)>,
    pub cond_is_break: Vec<(Node, Node)>,
    pub switch_chain: Vec<(Node, Node, u64, i64, Node)>,
    pub primary_switch: Vec<(Node, u64)>,
}

impl Facts {
    fn from_program(p: &StructuringProgram) -> Self {
        fn set<T: Ord + Copy>(iter: impl Iterator<Item = T>) -> Vec<T> {
            let mut rows: Vec<_> = iter.collect();
            rows.sort_unstable();
            rows.dedup();
            rows
        }
        Self {
            join_point: set(p.join_point.iter().copied()),
            scond_node: set(p.scond_node.iter().copied()),
            scond_no_join: set(p.scond_no_join.iter().copied()),
            ifbody_true: set(p.ifbody_true.iter().copied()),
            ifbody_false: set(p.ifbody_false.iter().copied()),
            vec_bypass_rewrite: set(p.vec_bypass_rewrite.iter().copied()),
            trim_node: set(p.trim_node.iter().copied()),
            cond_is_break: set(p.cond_is_break.iter().copied()),
            switch_chain: set(p.switch_chain.iter().copied()),
            primary_switch: set(p.primary_switch.iter().copied()),
        }
    }
}

#[derive(Default)]
pub(super) struct Fixpoints(Mutex<HashMap<Node, (Inputs, Facts)>>);

impl Fixpoints {
    fn lookup(&self, entry: Node, inputs: &Inputs) -> Option<Facts> {
        let cache = self.0.lock().unwrap();
        let (previous, facts) = cache.get(&entry)?;
        (previous == inputs).then(|| facts.clone())
    }
}

pub(super) fn run(program: &mut StructuringProgram, memo: Option<&Fixpoints>) -> Facts {
    let inputs = memo.map(|_| Inputs::from_program(program));
    let entry = program.entry_node.iter().map(|(node,)| *node).min();
    // The entry is merely a cache bucket, NEVER a reachability/order test.
    if let (Some(memo), Some(inputs), Some(entry)) = (memo, inputs.as_ref(), entry) {
        if let Some(facts) = memo.lookup(entry, inputs) {
            eprintln!("[inference-reuse] analysis=structuring entry={entry:#x} nodes={} exact-inputs=true", inputs.stmt.len());
            return facts;
        }
    }
    program.run();
    let facts = Facts::from_program(program);
    if let (Some(memo), Some(inputs), Some(entry)) = (memo, inputs, entry) {
        memo.0
            .lock()
            .unwrap()
            .insert(entry, (inputs, facts.clone()));
    }
    facts
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::passes::pass::IRPass;
    use crate::x86::op::{Comparison, Condition};
    use crate::x86::types::{Constant, CsharpminorExpr};

    fn fixture() -> Box<StructuringProgram> {
        let mut p = Box::new(StructuringProgram::default());
        p.stmt.extend([
            (
                10,
                CsharpminorStmt::Scond(
                    Condition::Ccomplimm(Comparison::Ceq, 0),
                    vec![CsharpminorExpr::Evar(1)],
                    20,
                    30,
                ),
            ),
            (20, CsharpminorStmt::Sjump(40)),
            (30, CsharpminorStmt::Sjump(40)),
            (
                40,
                CsharpminorStmt::Sreturn(CsharpminorExpr::Econst(Constant::Olongconst(7))),
            ),
        ]);
        p.entry_node.push((10,));
        p
    }

    #[test]
    fn cache_schema_covers_every_ascent_input() {
        let actual: HashSet<_> = StructuringProgram::inputs_only().iter().copied().collect();
        let expected = HashSet::from([
            "stmt",
            "seq_next",
            "jumptable_target",
            "entry_node",
            "packed_alu_node",
            "optimized_gap_node",
            "pointer_reg",
        ]);
        assert_eq!(
            actual, expected,
            "new rule inputs must enter the exact memo key"
        );
        let pass = super::super::StructuringPass::default();
        assert!(pass.inputs().contains(&"csharp_stmt"));
        assert!(pass.outputs().contains(&"switch_chain_default"));
    }

    #[test]
    fn cached_facts_equal_a_fresh_fixpoint_and_ignore_input_order() {
        let cache = Fixpoints::default();
        let expected = run(&mut fixture(), None);
        assert_eq!(run(&mut fixture(), Some(&cache)), expected);
        let mut reordered = fixture();
        let mut rows: Vec<_> = reordered.stmt.iter().cloned().collect();
        rows.reverse();
        rows.push(rows[0].clone());
        reordered.stmt = rows.into_iter().collect();
        assert!(cache
            .lookup(10, &Inputs::from_program(&reordered))
            .is_some());
        assert_eq!(run(&mut reordered, Some(&cache)), expected);
    }

    #[test]
    fn every_input_family_invalidates_the_cached_fixpoint() {
        let cache = Fixpoints::default();
        run(&mut fixture(), Some(&cache));
        let mutations: [fn(&mut StructuringProgram); 7] = [
            |p: &mut StructuringProgram| {
                p.stmt.push((50, CsharpminorStmt::Snop));
            },
            |p: &mut StructuringProgram| {
                p.seq_next.push((40, 50));
            },
            |p: &mut StructuringProgram| {
                p.jumptable_target.push((10, 50));
            },
            |p: &mut StructuringProgram| {
                p.entry_node.push((20,));
            },
            |p: &mut StructuringProgram| {
                p.packed_alu_node.push((20,));
            },
            |p: &mut StructuringProgram| {
                p.optimized_gap_node.push((20,));
            },
            |p: &mut StructuringProgram| {
                p.pointer_reg.push((1,));
            },
        ];
        for mutate in mutations {
            let mut changed = fixture();
            mutate(&mut changed);
            assert!(cache.lookup(10, &Inputs::from_program(&changed)).is_none());
        }
    }

    #[test]
    fn changed_payload_and_changed_cfg_are_recomputed() {
        let cache = Fixpoints::default();
        run(&mut fixture(), Some(&cache));
        let changed = || {
            let mut program = fixture();
            program.stmt = program
                .stmt
                .iter()
                .map(|(node, stmt)| {
                    (
                        *node,
                        if *node == 20 {
                            CsharpminorStmt::Sreturn(CsharpminorExpr::Evar(9))
                        } else {
                            stmt.clone()
                        },
                    )
                })
                .collect();
            program
        };
        let fresh_inputs = Inputs::from_program(&changed());
        assert!(cache.lookup(10, &fresh_inputs).is_none());
        let expected = run(&mut changed(), None);
        let result = run(&mut changed(), Some(&cache));
        assert_eq!(result, expected);
        assert_eq!(cache.lookup(10, &fresh_inputs), Some(result));
        assert!(
            cache
                .lookup(10, &Inputs::from_program(&fixture()))
                .is_none(),
            "only the latest epoch is retained, not a growing history"
        );
    }
}
