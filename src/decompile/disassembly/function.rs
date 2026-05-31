
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

    // main_function is seeded earlier by detect_main_via_libc_start_main so main becomes a block leader and named entry.
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

    // Seed entries from data code pointers (vtable/fn-ptr tables, PIE addends): keep clean block leaders not inside a FUNC range, not jump-table targets, not PLT stubs.
    {
        let block_leaders: HashSet<u64> = db.rel_iter::<(Address,)>("block").map(|(a,)| *a).collect();
        let plt_addrs: HashSet<u64> = db.rel_iter::<(Address, Symbol)>("plt_block").map(|(a, _)| *a).collect();
        let mut seeded = 0u32;
        for (_slot, target) in db.rel_iter::<(Address, Address)>("code_pointer_in_data") {
            let target = *target;
            if entries.contains(&target) { continue; }
            if !block_leaders.contains(&target) { continue; }
            if jump_table_targets.contains(&target) { continue; }
            if plt_addrs.contains(&target) { continue; }
            if func_ranges.iter().any(|(start, end)| target > *start && target < *end) { continue; }
            entries.insert(target);
            seeded += 1;
        }
        if seeded > 0 {
            log::debug!("Function inference: seeded {} entries from code pointers in data", seeded);
        }
    }

    // Seed entries from cross-function tail-call jmps (-O1+ `call;ret` becomes `jmp`); see seed_tailcall_entries.
    {
        let new_seeds = seed_tailcall_entries(db, insns, &entries, &jump_table_targets, &func_ranges);
        let n = new_seeds.len();
        for t in new_seeds {
            entries.insert(t);
        }
        if n > 0 {
            log::debug!("Function inference: seeded {} entries from cross-function tail-call jmps", n);
        }
    }

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

// A C++ EH landing pad (`endbr64; mov <reg>,%rax/%rdx`) is an unwinder resume target, not a function entry; insns[i] is the candidate ENDBR64.
fn is_eh_landing_pad_at(insns: &[DecodedInsn], i: usize) -> bool {
    if insns[i].mnemonic != "ENDBR64" { return false; }
    let Some(next) = insns.get(i + 1) else { return false; };
    if next.mnemonic != "MOV" { return false; }
    // capstone Intel op_str is "DST, SRC"; an EH pad moves FROM %rax/%rdx (the source, 2nd operand).
    let op = next.op_str.to_uppercase();
    matches!(op.rsplit(',').next().map(str::trim), Some("RAX") | Some("RDX"))
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

    // ENDBR64 is a CET landing pad placed only at indirect-branch/call targets (function entries), never mid-function.
    let is_endbr = |insn: &DecodedInsn| -> bool { insn.mnemonic == "ENDBR64" };

    let is_other_prologue = |insn: &DecodedInsn| -> bool {
        (insn.mnemonic == "PUSH" && insn.op_str.to_uppercase().contains("RBP"))
            || (insn.mnemonic == "SUB" && insn.op_str.to_uppercase().contains("RSP"))
    };

    for i in 1..insns.len() {
        let endbr = is_endbr(&insns[i]);
        if !endbr && !is_other_prologue(&insns[i]) {
            continue;
        }

        let mut j = i - 1;
        while j > 0 && is_padding(insns[j].mnemonic) {
            j -= 1;
        }

        let prev = insns[j].mnemonic;
        // A terminal predecessor bounds any prologue; for ENDBR64 a CALL predecessor (no-return call) also bounds a fresh function, excluding EH pads.
        if (is_terminal(prev) || (endbr && prev == "CALL")) && !is_eh_landing_pad_at(insns, i) {
            entries.insert(insns[i].address);
        }
    }

    entries
}

// Minimal union-find over u64 keys grouping instructions into intra-function fall-through components, used by seed_tailcall_entries.
struct UnionFind {
    parent: HashMap<u64, u64>,
    size: HashMap<u64, u64>,
}

impl UnionFind {
    fn new() -> Self {
        UnionFind { parent: HashMap::new(), size: HashMap::new() }
    }
    fn find(&mut self, x: u64) -> u64 {
        self.parent.entry(x).or_insert(x);
        self.size.entry(x).or_insert(1);
        // Iterative root walk + path compression (avoids deep recursion on long instruction chains).
        let mut root = x;
        while self.parent[&root] != root {
            root = self.parent[&root];
        }
        let mut cur = x;
        while cur != root {
            let next = self.parent[&cur];
            self.parent.insert(cur, root);
            cur = next;
        }
        root
    }
    fn union(&mut self, a: u64, b: u64) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb { return; }
        let (sa, sb) = (self.size[&ra], self.size[&rb]);
        let (big, small) = if sa >= sb { (ra, rb) } else { (rb, ra) };
        self.parent.insert(small, big);
        self.size.insert(big, sa + sb);
    }
}

// Seed new entries from cross-function tail-call jmps (`jmp callee` shape of `call;ret`); a tail call requires a different nearest-known-entry AND a different fall-through component (else intra-function), plus guards: clean block leader, not a jump-table/PLT/EH-pad target, not inside a known FUNC range, preceded by a terminal (yields zero seeds at -O0).
fn seed_tailcall_entries(
    db: &DecompileDB,
    insns: &[DecodedInsn],
    entries: &BTreeSet<u64>,
    jump_table_targets: &HashSet<u64>,
    func_ranges: &[(u64, u64)],
) -> Vec<u64> {
    if insns.is_empty() { return Vec::new(); }

    let is_terminal = |m: &str| -> bool {
        matches!(m, "RET" | "JMP" | "HLT" | "UD2" | "INT3")
    };
    let is_padding = |m: &str| -> bool {
        matches!(m, "NOP" | "INT3")
    };
    let is_uncond_terminal = |m: &str| -> bool {
        // Instructions after which control does NOT fall through to the next instruction.
        matches!(m, "RET" | "JMP" | "HLT" | "UD2")
    };
    let is_cond_jump = |m: &str| -> bool {
        matches!(m,
            "JE" | "JNE" | "JL" | "JLE" | "JG" | "JGE"
            | "JB" | "JBE" | "JA" | "JAE" | "JP" | "JNP"
            | "JO" | "JNO" | "JS" | "JNS"
            | "JCXZ" | "JECXZ" | "JRCXZ"
            | "LOOP" | "LOOPE" | "LOOPNE")
    };

    let addr_set: HashSet<u64> = insns.iter().map(|i| i.address).collect();

    // Resolved single-target direct JMP/Jcc/CALL immediates; jump-table dispatcher jmps are handled via jump_table_target below.
    let mut direct_jmp_target: HashMap<u64, u64> = HashMap::new();
    for (src, dst) in db.rel_iter::<(Address, Address)>("direct_jump") {
        // Keep only single-target jmps (a jump-table dispatcher has many direct_jump rows for one src).
        direct_jmp_target.entry(*src).or_insert(*dst);
    }
    // Jump-table dispatcher jmp addresses (to exclude from the tail-call scan) and their case targets.
    let mut jt_dispatcher: HashSet<u64> = HashSet::new();
    let mut jt_edges: Vec<(u64, u64)> = Vec::new();
    for (jmp_addr, _idx, target) in db.rel_iter::<(Node, usize, Node)>("jump_table_target") {
        jt_dispatcher.insert(*jmp_addr);
        jt_edges.push((*jmp_addr, *target));
    }

    // Build fall-through-component union-find: join on every edge except unconditional `jmp <imm>`.
    let mut uf = UnionFind::new();
    for (k, insn) in insns.iter().enumerate() {
        let m = insn.mnemonic;
        // Fall-through to the next instruction unless this is an unconditional terminal.
        if !is_uncond_terminal(m) {
            if let Some(next) = insns.get(k + 1) {
                uf.union(insn.address, next.address);
            }
        }
        // Conditional branch: both the fall-through (above) and the taken target stay in-function.
        if is_cond_jump(m) {
            if let Some(&t) = direct_jmp_target.get(&insn.address) {
                if addr_set.contains(&t) {
                    uf.union(insn.address, t);
                }
            }
        }
    }
    // Jump-table dispatch edges keep all switch cases in the dispatcher's function.
    for (jmp_addr, target) in &jt_edges {
        if addr_set.contains(target) {
            uf.union(*jmp_addr, *target);
        }
    }

    // Sorted known entries for the nearest-preceding-entry test.
    let known_entries: Vec<u64> = entries.iter().copied().collect(); // BTreeSet -> already ascending
    let nearest_entry = |addr: u64| -> Option<u64> {
        match known_entries.binary_search(&addr) {
            Ok(_) => Some(addr),
            Err(0) => None,
            Err(i) => Some(known_entries[i - 1]),
        }
    };

    // Index for the "preceded by a terminal" leader test.
    let addr_to_idx: HashMap<u64, usize> =
        insns.iter().enumerate().map(|(i, d)| (d.address, i)).collect();
    let preceded_by_terminal = |target: u64| -> bool {
        let Some(&k) = addr_to_idx.get(&target) else { return false; };
        if k == 0 { return false; }
        let mut j = k - 1;
        while j > 0 && is_padding(insns[j].mnemonic) {
            j -= 1;
        }
        is_terminal(insns[j].mnemonic)
    };

    let block_leaders: HashSet<u64> = db.rel_iter::<(Address,)>("block").map(|(a,)| *a).collect();
    let plt_addrs: HashSet<u64> = db.rel_iter::<(Address, Symbol)>("plt_block").map(|(a, _)| *a).collect();
    // Full PLT-section spans, covering the PLT-0 resolver and stub tails (not in plt_block) so a jmp into them is not seeded as a tail call.
    let plt_ranges: Vec<(u64, u64)> =
        db.rel_iter::<(Address, Address)>("plt_section_range").map(|(s, e)| (*s, *e)).collect();
    let in_plt_section = |addr: u64| -> bool {
        plt_ranges.iter().any(|(s, e)| addr >= *s && addr < *e)
    };

    // EH landing-pad leaders: a jmp originating in such a pad is an exception resume into its owning function, not a tail call, so map each instruction to its block leader.
    let mut insn_to_leader: HashMap<u64, u64> = HashMap::new();
    for (insn_addr, block_addr) in db.rel_iter::<(Address, Address)>("code_in_block") {
        insn_to_leader.insert(*insn_addr, *block_addr);
    }
    let eh_pad_leaders: HashSet<u64> = (0..insns.len())
        .filter(|&i| is_eh_landing_pad_at(insns, i))
        .map(|i| insns[i].address)
        .collect();

    let mut seeds: BTreeSet<u64> = BTreeSet::new();
    for insn in insns {
        if insn.mnemonic != "JMP" { continue; }
        if jt_dispatcher.contains(&insn.address) { continue; }   // switch dispatch, not a tail call
        // A jmp from an EH landing-pad block is an exception resume into its owning function, never a tail call.
        if insn_to_leader.get(&insn.address).map_or(false, |l| eh_pad_leaders.contains(l)) { continue; }
        let Some(&target) = direct_jmp_target.get(&insn.address) else { continue; };
        if target == 0 || !addr_set.contains(&target) { continue; }
        if entries.contains(&target) { continue; }               // already a known entry
        // Cross-function discriminators (both required): nearest known entry differs AND source/target sit in different fall-through components.
        if nearest_entry(insn.address) == nearest_entry(target) { continue; }
        if uf.find(insn.address) == uf.find(target) { continue; }
        // Spurious-entry guards (a)-(e) plus the PLT-section and EH-landing-pad exclusions.
        if !block_leaders.contains(&target) { continue; }
        if jump_table_targets.contains(&target) { continue; }
        if plt_addrs.contains(&target) { continue; }
        if in_plt_section(target) { continue; }
        if eh_pad_leaders.contains(&target) { continue; }
        if func_ranges.iter().any(|(s, e)| target > *s && target < *e) { continue; }
        if !preceded_by_terminal(target) { continue; }
        seeds.insert(target);
    }
    seeds.into_iter().collect()
}

// Parse `lea rdi, [rip +/- 0xN]` and return the absolute target address, else None. Used to recover main from _start.
fn parse_lea_rdi_rip_relative(insn: &DecodedInsn) -> Option<u64> {
    if insn.mnemonic != "LEA" {
        return None;
    }
    let op = insn.op_str;
    if !op.starts_with("RDI") {
        return None;
    }
    let bracket_start = op.find('[')?;
    let bracket_end = op.find(']')?;
    let inner = op[bracket_start + 1..bracket_end].trim();
    let rest = inner.strip_prefix("RIP")?.trim();
    let (sign, hex) = if let Some(s) = rest.strip_prefix('-') {
        (-1i64, s.trim())
    } else if let Some(s) = rest.strip_prefix('+') {
        (1i64, s.trim())
    } else if rest.is_empty() {
        return Some(insn.address + insn.size as u64);
    } else {
        return None;
    };
    let hex = hex.strip_prefix("0X").unwrap_or(hex);
    let disp = i64::from_str_radix(hex, 16).ok()? * sign;
    Some((insn.address as i64 + insn.size as i64 + disp) as u64)
}

// Recover main from _start's `lea main(%rip), %rdi; ...; call __libc_start_main` by scanning first 32 insns from ELF entry; None if "main" symbol exists or no match.
pub fn detect_main_via_libc_start_main(
    db: &DecompileDB,
    insns: &[DecodedInsn],
) -> Option<u64> {
    let has_main_sym = db
        .rel_iter::<(Address, usize, Symbol, Symbol, Symbol, usize, Symbol, usize, Symbol)>("symbol_table")
        .any(|(_, _, _, _, _, _, _, _, name)| *name == "main");
    if has_main_sym {
        return None;
    }

    let entry_addr = db.rel_iter::<(Address,)>("main_function")
        .next()
        .map(|(a,)| *a)?;

    let start_idx = insns.binary_search_by_key(&entry_addr, |i| i.address).ok()?;
    let insn_addrs: HashSet<u64> = insns.iter().map(|i| i.address).collect();
    let end_idx = (start_idx + 32).min(insns.len());

    for i in start_idx..end_idx {
        if let Some(target) = parse_lea_rdi_rip_relative(&insns[i]) {
            if target != entry_addr && insn_addrs.contains(&target) {
                return Some(target);
            }
        }
    }
    None
}
