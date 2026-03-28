

use std::collections::BTreeSet;
use crate::decompile::disassembly::instruction::DecodedInsn;
use crate::decompile::elevator::DecompileDB;
use crate::x86::types::*;

// Returns true if the instruction is a branch, trap, or other control transfer.
fn is_branch(mnem: &str) -> bool {
    mnem.starts_with('J')
        || mnem == "RET"
        || mnem == "CALL"
        || mnem == "LOOP"
        || mnem == "LOOPE"
        || mnem == "LOOPNE"
        || mnem == "INT3"
        || mnem == "HLT"
        || mnem == "UD2"
        || mnem == "SYSCALL"
}

// Build basic blocks and populate block, code_in_block, code_in_refined_block, and block_boundaries.
pub fn build_blocks(db: &mut DecompileDB, insns: &[DecodedInsn], extra_leaders: &[u64]) {
    if insns.is_empty() { return; }

    // Pre-compute branch targets from immediate operands
    let mut op_imm_map: std::collections::HashMap<&str, i64> = std::collections::HashMap::new();
    for (id, val, _) in db.rel_iter::<(Symbol, i64, usize)>("op_immediate") {
        op_imm_map.insert(id, *val);
    }

    let mut branch_targets: std::collections::HashMap<u64, u64> = std::collections::HashMap::new();
    for (addr, _sz, _pfx, mnem, op1, _op2, _op3, _op4, _, _) in db.rel_iter::<(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize)>("unrefinedinstruction") {
        if !mnem.starts_with('J') && *mnem != "CALL" && !mnem.starts_with("LOOP") {
            continue;
        }
        if *op1 == "0" { continue; }
        if let Some(&val) = op_imm_map.get(op1) {
            branch_targets.insert(*addr, val as u64);
        }
    }

    // Collect block leaders: first insn, branch successors/targets, symbols, extra leaders
    let mut leaders: BTreeSet<u64> = BTreeSet::new();

    leaders.insert(insns[0].address);

    let addr_set: std::collections::HashMap<u64, usize> =
        insns.iter().enumerate().map(|(i, d)| (d.address, i)).collect();

    for (i, insn) in insns.iter().enumerate() {
        if is_branch(insn.mnemonic) {
            if i + 1 < insns.len() {
                let next_addr = insns[i + 1].address;
                if insn.address + insn.size as u64 == next_addr {
                    leaders.insert(next_addr);
                }
            }

            if let Some(&target) = branch_targets.get(&insn.address) {
                if addr_set.contains_key(&target) {
                    leaders.insert(target);
                }
            }
        }
    }

    for (addr, _, _) in db.rel_iter::<(Address, Symbol, Symbol)>("symbols") {
        if addr_set.contains_key(addr) {
            leaders.insert(*addr);
        }
    }

    for &addr in extra_leaders {
        if addr_set.contains_key(&addr) {
            leaders.insert(addr);
        }
    }

    // Assign each instruction to its containing block
    let leader_vec: Vec<u64> = leaders.iter().copied().collect();

    let mut block_vec: Vec<(u64,)> = Vec::new();
    let mut code_in_block_vec: Vec<(u64, u64)> = Vec::new();
    let mut block_boundaries_vec: Vec<(u64, u64, u64)> = Vec::new();

    let mut leader_idx = 0;
    for insn in insns {
        while leader_idx + 1 < leader_vec.len()
            && insn.address >= leader_vec[leader_idx + 1]
        {
            leader_idx += 1;
        }
        let block_start = leader_vec[leader_idx];
        code_in_block_vec.push((insn.address, block_start));
    }

    for &l in &leader_vec {
        block_vec.push((l,));
    }

    for i in 0..leader_vec.len() {
        let start = leader_vec[i];
        let next_block = if i + 1 < leader_vec.len() {
            leader_vec[i + 1]
        } else {
            insns.last().map(|d| d.address + d.size as u64).unwrap_or(start)
        };
        let last_insn = code_in_block_vec.iter()
            .filter(|(_, b)| *b == start)
            .map(|(a, _)| *a)
            .max()
            .unwrap_or(start);
        block_boundaries_vec.push((start, last_insn, next_block));
    }

    db.rel_set("block", block_vec.into_iter().collect::<ascent::boxcar::Vec<_>>());
    db.rel_set("code_in_block", code_in_block_vec.clone().into_iter().collect::<ascent::boxcar::Vec<_>>());
    db.rel_set("code_in_refined_block", code_in_block_vec.into_iter().collect::<ascent::boxcar::Vec<_>>());
    db.rel_set("block_boundaries", block_boundaries_vec.into_iter().collect::<ascent::boxcar::Vec<_>>());
}
