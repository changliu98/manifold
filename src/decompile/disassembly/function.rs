
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use crate::decompile::elevator::DecompileDB;
use super::instruction::DecodedInsn;
use crate::x86::types::*;

// Infer function entry points and assign blocks to functions via CFG reachability.
pub fn infer_functions(db: &mut DecompileDB, insns: &[DecodedInsn]) {
    let leak = |s: String| -> &'static str { Box::leak(s.into_boxed_str()) };

    // Collect function entry points from FUNC symbols, call targets, and main
    let mut entries: BTreeSet<u64> = BTreeSet::new();

    for (addr, _size, sym_type, _bind, sect_type, ..) in db.rel_iter::<(Address, usize, Symbol, Symbol, Symbol, usize, Symbol, usize, Symbol)>("symbol_table") {
        if *sym_type == "FUNC" && *sect_type != "UNDEF" {
            entries.insert(*addr);
        }
    }

    for (_, callee) in db.rel_iter::<(Address, Address)>("direct_call") {
        entries.insert(*callee);
    }

    for (addr,) in db.rel_iter::<(Address,)>("main_function") {
        entries.insert(*addr);
    }

    // Filter prologue-detected entries that overlap jump table targets or known FUNC ranges
    let prologue_entries = detect_prologue_entries(insns);

    let jump_table_targets: HashSet<u64> = db.rel_iter::<(Node, usize, Node)>("jump_table_target")
        .map(|(_jmp, _idx, target)| *target)
        .collect();
    let filtered_prologue: BTreeSet<u64> = prologue_entries
        .iter()
        .filter(|addr| !jump_table_targets.contains(addr))
        .copied()
        .collect();
    if prologue_entries.len() != filtered_prologue.len() {
        log::debug!("Filtered {} prologue entries that are jump table targets",
                  prologue_entries.len() - filtered_prologue.len());
    }

    let func_ranges: Vec<(u64, u64)> = db.rel_iter::<(Address, usize, Symbol, Symbol, Symbol, usize, Symbol, usize, Symbol)>("symbol_table")
        .filter(|(addr, size, sym_type, ..)| *sym_type == "FUNC" && *size > 0 && *addr > 0)
        .map(|(addr, size, ..)| (*addr, *addr + *size as u64))
        .collect();
    let before_sym_filter = filtered_prologue.len();
    let filtered_prologue: BTreeSet<u64> = filtered_prologue
        .into_iter()
        .filter(|addr| !func_ranges.iter().any(|(start, end)| *addr > *start && *addr < *end))
        .collect();
    if before_sym_filter != filtered_prologue.len() {
        log::debug!("Filtered {} prologue entries inside known FUNC symbol ranges",
                  before_sym_filter - filtered_prologue.len());
    }

    entries.extend(&filtered_prologue);

    // Build func_entry and ddisasm_function_entry relations
    let mut func_entry: Vec<(&'static str, u64)> = Vec::new();
    let mut func_entry_set: Vec<(u64,)> = Vec::new();

    let mut name_for_addr: HashMap<u64, &'static str> = HashMap::new();
    for (addr, name, _) in db.rel_iter::<(Address, Symbol, Symbol)>("symbols") {
        name_for_addr.entry(*addr).or_insert(*name);
    }

    let plt_addrs: HashSet<u64> = db.rel_iter::<(Address, Symbol)>("plt_block").map(|(a, _)| *a).collect();

    for &entry_addr in &entries {
        let name = name_for_addr.get(&entry_addr)
            .copied()
            .unwrap_or_else(|| leak(format!("FUN_{:x}", entry_addr)));

        if !plt_addrs.contains(&entry_addr) {
            func_entry.push((name, entry_addr));
        }
        func_entry_set.push((entry_addr,));
    }

    db.rel_set("func_entry", func_entry.into_iter().collect::<ascent::boxcar::Vec<_>>());
    db.rel_set("ddisasm_function_entry", func_entry_set.into_iter().collect::<ascent::boxcar::Vec<_>>());

    // Block-to-function assignment via BFS over non-call CFG edges
    let blocks: HashSet<u64> = db.rel_iter::<(Address,)>("block").map(|(a,)| *a).collect();

    let mut insn_to_block: HashMap<u64, u64> = HashMap::new();
    for (insn_addr, block_addr) in db.rel_iter::<(Address, Address)>("code_in_block") {
        insn_to_block.insert(*insn_addr, *block_addr);
    }

    let mut block_successors: HashMap<u64, Vec<u64>> = HashMap::new();
    for (src, dst, edge_type) in db.rel_iter::<(Address, Address, Symbol)>("ddisasm_cfg_edge") {
        if *edge_type == "call" || *edge_type == "indirect" || *edge_type == "indirect_call" {
            continue;
        }
        let src_block = insn_to_block.get(src);
        let dst_block = insn_to_block.get(dst);
        if let (Some(&sb), Some(&db_addr)) = (src_block, dst_block) {
            block_successors.entry(sb).or_default().push(db_addr);
        }
    }

    let mut block_in_function: Vec<(u64, u64)> = Vec::new();

    for &entry_addr in &entries {
        if !blocks.contains(&entry_addr) { continue; }

        let mut visited: HashSet<u64> = HashSet::new();
        let mut queue: VecDeque<u64> = VecDeque::new();
        queue.push_back(entry_addr);
        visited.insert(entry_addr);

        while let Some(block_addr) = queue.pop_front() {
            block_in_function.push((block_addr, entry_addr));

            if let Some(succs) = block_successors.get(&block_addr) {
                for &succ in succs {
                    if !visited.contains(&succ)
                        && (!entries.contains(&succ) || succ == entry_addr)
                    {
                        visited.insert(succ);
                        queue.push_back(succ);
                    }
                }
            }
        }
    }

    // Rescue orphaned blocks reachable only via indirect edges
    {
        let assigned_blocks: HashSet<u64> = block_in_function.iter().map(|(b, _)| *b).collect();

        let entry_vec: Vec<u64> = entries.iter().copied().collect();

        let mut funcs_with_indirect: HashSet<u64> = HashSet::new();
        for (src, _dst, edge_type) in db.rel_iter::<(Address, Address, Symbol)>("ddisasm_cfg_edge") {
            if *edge_type == "indirect" {
                if let Some(&src_block) = insn_to_block.get(src) {
                    for &(block, func) in block_in_function.iter() {
                        if block == src_block {
                            funcs_with_indirect.insert(func);
                        }
                    }
                }
            }
        }

        let mut rescued = 0u32;
        for &func_entry in &funcs_with_indirect {
            let func_end = entry_vec.iter()
                .filter(|&&e| e > func_entry)
                .copied()
                .next()
                .unwrap_or(u64::MAX);

            for &(block_addr,) in db.rel_iter::<(Address,)>("block") {
                if block_addr > func_entry
                    && block_addr < func_end
                    && !assigned_blocks.contains(&block_addr)
                    && !entries.contains(&block_addr)
                {
                    block_in_function.push((block_addr, func_entry));
                    rescued += 1;
                }
            }
        }
        if rescued > 0 {
            log::debug!("Function inference: rescued {} orphaned blocks via indirect-jump heuristic", rescued);
        }
    }

    // Implicit function entries for orphaned root blocks (no predecessors, non-padding)
    {
        let assigned_blocks: HashSet<u64> = block_in_function.iter().map(|(b, _)| *b).collect();

        let mut has_pred: HashSet<u64> = HashSet::new();
        for (src, dst, edge_type) in db.rel_iter::<(Address, Address, Symbol)>("ddisasm_cfg_edge") {
            if *edge_type == "call" || *edge_type == "indirect_call" {
                continue;
            }
            if let Some(&dst_block) = insn_to_block.get(dst) {
                if let Some(&src_block) = insn_to_block.get(src) {
                    if src_block != dst_block {
                        has_pred.insert(dst_block);
                    }
                }
            }
        }

        let mut implicit_entries: Vec<u64> = Vec::new();
        for &(block_addr,) in db.rel_iter::<(Address,)>("block") {
            if assigned_blocks.contains(&block_addr) { continue; }
            if has_pred.contains(&block_addr) { continue; }
            if plt_addrs.contains(&block_addr) { continue; }
            let is_padding = db.rel_iter::<(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize)>("unrefinedinstruction")
                .find(|(addr, ..)| *addr == block_addr)
                .map(|(_, _, _, mnem, ..)| matches!(*mnem, "NOP" | "INT3" | "HLT" | "UD2"))
                .unwrap_or(true);
            if is_padding { continue; }
            implicit_entries.push(block_addr);
        }

        if !implicit_entries.is_empty() {
            let new_count = implicit_entries.len();
            for &entry_addr in &implicit_entries {
                let mut visited: HashSet<u64> = HashSet::new();
                let mut queue: VecDeque<u64> = VecDeque::new();
                queue.push_back(entry_addr);
                visited.insert(entry_addr);

                while let Some(block_addr) = queue.pop_front() {
                    if !assigned_blocks.contains(&block_addr) {
                        block_in_function.push((block_addr, entry_addr));
                    }
                    if let Some(succs) = block_successors.get(&block_addr) {
                        for &succ in succs {
                            if !visited.contains(&succ)
                                && !assigned_blocks.contains(&succ)
                                && !entries.contains(&succ)
                            {
                                visited.insert(succ);
                                queue.push_back(succ);
                            }
                        }
                    }
                }
            }

            for &entry_addr in &implicit_entries {
                let name = name_for_addr.get(&entry_addr)
                    .copied()
                    .unwrap_or_else(|| leak(format!("FUN_{:x}", entry_addr)));
                db.rel_push("func_entry", (name, entry_addr));
                db.rel_push("ddisasm_function_entry", (entry_addr,));
                entries.insert(entry_addr);
            }
            log::debug!("Function inference: {} implicit function entries from orphaned root blocks", new_count);
        }
    }

    // Predecessor-based propagation for remaining unassigned blocks
    {
        let mut block_preds: HashMap<u64, Vec<u64>> = HashMap::new();
        for (src, dst, edge_type) in db.rel_iter::<(Address, Address, Symbol)>("ddisasm_cfg_edge") {
            if *edge_type == "call" || *edge_type == "indirect_call" {
                continue;
            }
            if let (Some(&src_block), Some(&dst_block)) = (insn_to_block.get(src), insn_to_block.get(dst)) {
                if src_block != dst_block {
                    block_preds.entry(dst_block).or_default().push(src_block);
                }
            }
        }

        let mut propagated = 0u32;
        for _round in 0..20 {
            let assigned: HashMap<u64, u64> = block_in_function.iter()
                .copied()
                .collect();
            let mut new_assignments: Vec<(u64, u64)> = Vec::new();

            for &(block_addr,) in db.rel_iter::<(Address,)>("block") {
                if assigned.contains_key(&block_addr) {
                    continue;
                }
                if let Some(preds) = block_preds.get(&block_addr) {
                    let mut pred_funcs: HashSet<u64> = HashSet::new();
                    let mut all_assigned = true;
                    for &pred in preds {
                        if let Some(&func) = assigned.get(&pred) {
                            pred_funcs.insert(func);
                        } else {
                            all_assigned = false;
                        }
                    }
                    if pred_funcs.len() == 1 && (all_assigned || preds.len() == 1) {
                        let func = *pred_funcs.iter().next().unwrap();
                        new_assignments.push((block_addr, func));
                    }
                }
            }

            if new_assignments.is_empty() {
                break;
            }
            propagated += new_assignments.len() as u32;
            block_in_function.extend(new_assignments);
        }
        if propagated > 0 {
            log::debug!("Function inference: propagated {} blocks via predecessor edges", propagated);
        }
    }

    {
        let assigned_blocks: HashSet<u64> = block_in_function.iter().map(|(b, _)| *b).collect();
        let unassigned_count = blocks.len() - assigned_blocks.len();
        let func_count = entries.len();
        log::info!("Function inference: {} functions, {}/{} blocks assigned ({} unassigned padding/PLT)",
                  func_count, assigned_blocks.len(), blocks.len(), unassigned_count);
    }

    db.rel_set("block_in_function", block_in_function.into_iter().collect::<ascent::boxcar::Vec<_>>());
}

// Detect function entries via prologue patterns (ENDBR64, push rbp, sub rsp) after terminals.
pub fn detect_prologue_entries(insns: &[DecodedInsn]) -> BTreeSet<u64> {
    let mut entries = BTreeSet::new();
    if insns.is_empty() { return entries; }

    let is_terminal = |m: &str| -> bool {
        matches!(m, "RET" | "JMP" | "HLT" | "UD2" | "INT3")
    };

    let is_padding = |m: &str| -> bool {
        matches!(m, "NOP" | "INT3")
    };

    let is_prologue_start = |insn: &DecodedInsn| -> bool {
        if insn.mnemonic == "ENDBR64" {
            return true;
        }
        if insn.mnemonic == "PUSH" && insn.op_str.to_uppercase().contains("RBP") {
            return true;
        }
        if insn.mnemonic == "SUB" && insn.op_str.to_uppercase().contains("RSP") {
            return true;
        }
        false
    };

    for i in 1..insns.len() {
        if !is_prologue_start(&insns[i]) {
            continue;
        }

        let mut j = i - 1;
        while j > 0 && is_padding(insns[j].mnemonic) {
            j -= 1;
        }

        if is_terminal(insns[j].mnemonic) {
            entries.insert(insns[i].address);
        }
    }

    entries
}
