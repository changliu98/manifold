use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::x86::types::{Address, Node, Symbol};
use ascent::ascent_par;
use ascent::lattice::set::Set;
use ascent::Dual;

// Add a block to its strict-dominator set. The lattice joins predecessor
// states by intersection through Dual<Set<_>>.
fn dom_set_with_self(strict: &Set<Address>, block: Address) -> Set<Address> {
    let mut dominators = strict.0.clone();
    dominators.insert(block);
    Set(dominators)
}

ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct RTLDominatorPassProgram;

    relation block_in_function(Node, Address);
    relation call_targets_noreturn(Node);
    relation code_in_block(Address, Address);
    relation ddisasm_cfg_edge(Address, Address, Symbol);

    // The disassembly CFG deliberately records a physical fallthrough after
    // every call before Linear knows whether the call returns. Exclude the
    // infeasible fallthroughs proved by Linear before computing dominance.
    #[local] relation cfg_block_edge(Address, Address);
    cfg_block_edge(*src_block, *dst_block) <--
        ddisasm_cfg_edge(src, dst, edge_type),
        if *edge_type != "call" && *edge_type != "indirect" && *edge_type != "indirect_call",
        !call_targets_noreturn(src),
        code_in_block(src, src_block),
        code_in_block(dst, dst_block);

    #[local] relation func_entry_block(Address, Address);
    func_entry_block(func, entry_block) <--
        block_in_function(entry_block, func),
        code_in_block(func, entry_block);

    // Both lattices remain pass-local. Their point-keyed state is
    // O(blocks * dominator depth); no pairwise dominance relation or history
    // of improving lattice snapshots is materialized.
    #[local] lattice block_strict_dom_set(Address, Address, Dual<Set<Address>>);
    #[local] lattice block_dom_set(Address, Address, Dual<Set<Address>>);

    block_dom_set(*func, *entry_block, Dual(Set::singleton(*entry_block))) <--
        func_entry_block(func, entry_block);

    block_strict_dom_set(*func, *block, Dual(predecessor_doms.0.clone())) <--
        block_dom_set(func, predecessor, predecessor_doms),
        cfg_block_edge(predecessor, block),
        block_in_function(block, func),
        !func_entry_block(func, block);

    block_dom_set(*func, *block, Dual(dom_set_with_self(&strict.0, *block))) <--
        block_strict_dom_set(func, block, strict),
        !func_entry_block(func, block);
}

pub struct RTLDominatorPass;

impl IRPass for RTLDominatorPass {
    fn name(&self) -> &'static str {
        "rtl_dominators"
    }

    fn run(&self, db: &mut DecompileDB) {
        let mut prog = RTLDominatorPassProgram::default();
        prog.swap_db_fields(db);
        prog.run();

        // Ascent has reached its fixpoint, so each RwLock contains only the
        // final Dual<Set> value. Clone each final point-keyed row exactly once;
        // publishing from inside the recursive program would retain transient
        // supersets after later predecessor intersections.
        let mut settled: Vec<(Address, Address, Set<Address>)> = prog
            .block_dom_set
            .iter()
            .map(|row| {
                let row = row.read().expect("RTL dominator lattice row lock poisoned");
                (row.0, row.1, row.2 .0.clone())
            })
            .collect();
        settled.sort_by_key(|(func, block, _)| (*func, *block));

        if db.measure_rule_times {
            let pass_name = "RTLDominatorPassProgram".to_string();
            let summary = format!(
                "=== Rule Times ===\n{}\n\n=== Relation Sizes ===\n{}",
                prog.scc_times_summary(),
                prog.relation_sizes_summary(),
            );
            eprintln!(
                "[RULE_TIMES] pass {}\n{}\n[/RULE_TIMES]",
                pass_name, summary
            );
            db.rule_time_reports.push((pass_name, summary));
        }

        prog.swap_db_fields(db);

        // Always replace the output, including an empty result, so a reused
        // DecompileDB cannot retain summaries from an earlier pipeline run.
        let relation = ascent::boxcar::Vec::new();
        for fact in settled {
            relation.push(fact);
        }
        db.rel_set("settled_block_dom_set", relation);
    }

    // Keep generated input metadata so a future body relation cannot be
    // omitted silently from a parallel scheduler sub-DB. The output remains
    // explicit because it is published imperatively after the fixpoint.
    fn inputs(&self) -> &'static [&'static str] {
        RTLDominatorPassProgram::inputs_only()
    }

    fn outputs(&self) -> &'static [&'static str] {
        &["settled_block_dom_set"]
    }
}

#[cfg(test)]
mod tests {
    use super::RTLDominatorPass;
    use crate::decompile::elevator::DecompileDB;
    use crate::decompile::passes::pass::IRPass;
    use ascent::lattice::set::Set;
    use std::collections::BTreeSet;

    #[test]
    fn direct_pointer_dominators_publish_only_the_settled_diamond_intersection() {
        let mut db = DecompileDB::default();
        let func: u64 = 0x1000;
        let entry = 0x9000;
        let left = 0x3000;
        let right = 0x7000;
        let join = 0x2000;
        let left_target = 0x3010;
        let right_target = 0x7010;

        for block in [entry, left, right, join] {
            db.rel_push("block_in_function", (block, func));
            // Use the block node itself as its representative instruction.
            db.rel_push("code_in_block", (block, block));
        }
        db.rel_push("code_in_block", (func, entry));
        db.rel_push("code_in_block", (left_target, left));
        db.rel_push("code_in_block", (right_target, right));
        for edge in [
            (entry, left_target, "branch"),
            (entry, right_target, "fallthrough"),
            (left, join, "fallthrough"),
            (right, join, "fallthrough"),
        ] {
            db.rel_push("ddisasm_cfg_edge", edge);
        }

        RTLDominatorPass.run(&mut db);

        let rows: Vec<_> = db
            .rel_iter::<(u64, u64, Set<u64>)>("settled_block_dom_set")
            .filter(|(owner, _, _)| *owner == func)
            .collect();
        assert_eq!(rows.len(), 4, "one final summary is published per block");
        let join_doms = rows
            .iter()
            .find_map(|(_, block, doms)| (*block == join).then_some(doms))
            .expect("join must have a final dominator summary");
        assert_eq!(join_doms.0, BTreeSet::from([entry, join]));
        assert!(!join_doms.0.contains(&left));
        assert!(!join_doms.0.contains(&right));

        // Reusing a DB with no CFG must replace, rather than append to, the
        // ordinary summary from the preceding run.
        db.rel_set(
            "block_in_function",
            ascent::boxcar::Vec::<(u64, u64)>::new(),
        );
        db.rel_set(
            "call_targets_noreturn",
            ascent::boxcar::Vec::<(u64,)>::new(),
        );
        db.rel_set("code_in_block", ascent::boxcar::Vec::<(u64, u64)>::new());
        db.rel_set(
            "ddisasm_cfg_edge",
            ascent::boxcar::Vec::<(u64, u64, &'static str)>::new(),
        );
        RTLDominatorPass.run(&mut db);
        assert_eq!(
            db.rel_iter::<(u64, u64, Set<u64>)>("settled_block_dom_set")
                .count(),
            0
        );
    }

    #[test]
    fn direct_pointer_dominators_exclude_only_proven_noreturn_fallthroughs() {
        let mut db = DecompileDB::default();
        let returning_func: u64 = 0x1000;
        let returning_entry: u64 = 0x9000;
        let returning_dst: u64 = 0x3000;
        let returning_target: u64 = 0x3010;
        let noreturn_func: u64 = 0x2000;
        let noreturn_entry: u64 = 0x8000;
        let noreturn_dst: u64 = 0x4000;
        let noreturn_target: u64 = 0x4010;

        for (func, entry, dst, target) in [
            (
                returning_func,
                returning_entry,
                returning_dst,
                returning_target,
            ),
            (noreturn_func, noreturn_entry, noreturn_dst, noreturn_target),
        ] {
            for block in [entry, dst] {
                db.rel_push("block_in_function", (block, func));
                db.rel_push("code_in_block", (block, block));
            }
            db.rel_push("code_in_block", (func, entry));
            db.rel_push("code_in_block", (target, dst));
            db.rel_push("ddisasm_cfg_edge", (entry, target, "fallthrough"));
        }
        db.rel_push("call_targets_noreturn", (noreturn_entry,));

        RTLDominatorPass.run(&mut db);

        let rows: BTreeSet<_> = db
            .rel_iter::<(u64, u64, Set<u64>)>("settled_block_dom_set")
            .map(|(func, block, _)| (*func, *block))
            .collect();
        assert!(rows.contains(&(returning_func, returning_dst)));
        assert!(rows.contains(&(noreturn_func, noreturn_entry)));
        assert!(!rows.contains(&(noreturn_func, noreturn_dst)));
    }
}
