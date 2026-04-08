
use std::collections::{HashMap, HashSet, VecDeque};

use crate::decompile::elevator::DecompileDB;
use crate::x86::mach::Mreg;
use crate::x86::types::{Node, RTLReg};

// Union-find with path compression; representative is always the minimum RTLReg per class.
pub struct UnionFind {
    parent: HashMap<RTLReg, RTLReg>,
    rank: HashMap<RTLReg, u32>,
}

impl UnionFind {
    pub fn new() -> Self {
        Self {
            parent: HashMap::new(),
            rank: HashMap::new(),
        }
    }

    pub fn make_set(&mut self, x: RTLReg) {
        self.parent.entry(x).or_insert(x);
        self.rank.entry(x).or_insert(0);
    }

    pub fn find(&mut self, x: RTLReg) -> RTLReg {
        let p = *self.parent.get(&x).unwrap_or(&x);
        if p == x {
            return x;
        }
        let root = self.find(p);
        self.parent.insert(x, root);
        root
    }

    pub fn union(&mut self, x: RTLReg, y: RTLReg) {
        let rx = self.find(x);
        let ry = self.find(y);
        if rx == ry {
            return;
        }

        let (min_root, max_root) = if rx < ry { (rx, ry) } else { (ry, rx) };

        let rank_min = *self.rank.get(&min_root).unwrap_or(&0);
        let rank_max = *self.rank.get(&max_root).unwrap_or(&0);

        self.parent.insert(max_root, min_root);
        if rank_min == rank_max {
            self.rank.insert(min_root, rank_min + 1);
        } else if rank_max > rank_min {
            self.rank.insert(min_root, rank_max + 1);
        }
    }
}

pub fn compute_variable_assignment(db: &mut DecompileDB) {
    let mut uf = UnionFind::new();

    let reg_xtl_data: Vec<(Node, Mreg, RTLReg)> = db
        .rel_iter::<(Node, Mreg, RTLReg)>("reg_xtl")
        .cloned()
        .collect();

    let stack_xtl_data: Vec<(u64, u64, i64, RTLReg)> = db
        .rel_iter::<(u64, u64, i64, RTLReg)>("stack_xtl")
        .cloned()
        .collect();

    let alias_edge_data: Vec<(RTLReg, RTLReg)> = db
        .rel_iter::<(RTLReg, RTLReg)>("alias_edge")
        .cloned()
        .collect();

    let is_def_data: Vec<(Node, RTLReg)> = db
        .rel_iter::<(Node, RTLReg)>("is_def")
        .cloned()
        .collect();

    for &(_, _, id) in &reg_xtl_data {
        uf.make_set(id);
    }
    for &(_, _, _, id) in &stack_xtl_data {
        uf.make_set(id);
    }
    for &(_, id) in &is_def_data {
        uf.make_set(id);
    }
    for &(id1, id2) in &alias_edge_data {
        uf.make_set(id1);
        uf.make_set(id2);
    }

    for &(id1, id2) in &alias_edge_data {
        uf.union(id1, id2);
    }

    // Positive-evidence coalescing: merge canonicals for (func, mreg) when a direct reg_def_used link exists with no intervening def, as a conservative safety net for missed alias_edge connections.
    {
        let instr_func_data: Vec<(Node, u64)> = db
            .rel_iter::<(Node, u64)>("instr_in_function")
            .cloned()
            .collect();
        let node_to_func: HashMap<Node, u64> = instr_func_data.into_iter().collect();

        let is_def_set: HashSet<(Node, RTLReg)> = is_def_data.iter().cloned().collect();

        // (node, mreg) -> def-side canonical (the is_def ID's canonical)
        let mut node_mreg_def_canonical: HashMap<(Node, Mreg), RTLReg> = HashMap::new();
        for &(node, id) in &is_def_data {
            for &(n, mreg, xtl_id) in &reg_xtl_data {
                if n == node && xtl_id == id {
                    node_mreg_def_canonical.insert((node, mreg), uf.find(id));
                    break;
                }
            }
        }

        // (node, mreg) -> use-side canonicals (IDs that are NOT defs at this node)
        let mut node_mreg_use_canonicals: HashMap<(Node, Mreg), Vec<RTLReg>> = HashMap::new();
        for &(node, mreg, id) in &reg_xtl_data {
            if !is_def_set.contains(&(node, id)) {
                let canonical = uf.find(id);
                node_mreg_use_canonicals
                    .entry((node, mreg))
                    .or_default()
                    .push(canonical);
            }
        }
        for v in node_mreg_use_canonicals.values_mut() {
            v.sort_unstable();
            v.dedup();
        }

        let reg_def_used_data: Vec<(Node, Mreg, Node)> = db
            .rel_iter::<(Node, Mreg, Node)>("reg_def_used")
            .cloned()
            .collect();

        // Build function-scoped block reachability to validate has_intervening_def entries.
        let code_in_block_data: Vec<(Node, Node)> = db.rel_iter::<(Node, Node)>("code_in_block").cloned().collect();
        let block_in_func_data: Vec<(Node, u64)> = db.rel_iter::<(Node, u64)>("block_in_function").cloned().collect();
        let cfg_edges: Vec<(Node, Node, &str)> = db.rel_iter::<(Node, Node, &str)>("ddisasm_cfg_edge").cloned().collect();

        let node_to_block: HashMap<Node, Node> = code_in_block_data.iter().map(|&(n, b)| (n, b)).collect();
        let block_to_func: HashMap<Node, u64> = block_in_func_data.iter().map(|&(b, f)| (b, f)).collect();

        // Build per-function block adjacency from cfg edges (excluding calls).
        let mut func_block_adj: HashMap<u64, HashMap<Node, Vec<Node>>> = HashMap::new();
        for &(src, dst, edge_type) in &cfg_edges {
            if edge_type == "call" || edge_type == "indirect" || edge_type == "indirect_call" { continue; }
            if let Some(&src_blk) = node_to_block.get(&src) {
                if let (Some(&f1), Some(&f2)) = (block_to_func.get(&src_blk), block_to_func.get(&dst)) {
                    if f1 == f2 {
                        func_block_adj.entry(f1).or_default().entry(src_blk).or_default().push(dst);
                    }
                }
            }
        }

        // Compute per-function block dominance to identify back-edges.
        // A block d dominates block b if d is on every path from the entry to b.
        // We use BFS-based reachability-avoiding to compute this.
        let mut func_back_edges: HashMap<u64, HashSet<(Node, Node)>> = HashMap::new();
        {
            // Collect functions and their entry blocks.
            let mut func_entries: HashMap<u64, Node> = HashMap::new();
            for (&blk, &func) in &block_to_func {
                // The entry block contains the function start address.
                if let Some(&(n, _b)) = code_in_block_data.iter().find(|&&(n, b)| b == blk && n == func) {
                    let _ = n;
                    func_entries.insert(func, blk);
                }
            }

            for (&func, &entry_blk) in &func_entries {
                let adj = match func_block_adj.get(&func) { Some(a) => a, None => continue };

                // Collect all blocks in this function.
                let func_blocks: Vec<Node> = block_to_func.iter()
                    .filter(|(_, &f)| f == func)
                    .map(|(&b, _)| b)
                    .collect();

                // BFS to find all reachable blocks from entry.
                let mut reachable: HashSet<Node> = HashSet::new();
                {
                    let mut q = VecDeque::new();
                    reachable.insert(entry_blk);
                    q.push_back(entry_blk);
                    while let Some(blk) = q.pop_front() {
                        if let Some(nexts) = adj.get(&blk) {
                            for &nb in nexts {
                                if reachable.insert(nb) { q.push_back(nb); }
                            }
                        }
                    }
                }

                // For each reachable block d, check if d dominates some successor's target
                // by testing if entry can reach that target without going through d.
                // block_dom(b, d) = d dominates b = entry cannot reach b while avoiding d.
                // A back-edge is (src_blk, dst_blk) where dst_blk dominates src_blk.
                // We compute: can entry reach src_blk without going through dst_blk?
                // If not, then dst_blk dominates src_blk, and (src_blk -> dst_blk) is a back-edge.

                // For each CFG edge (src_blk -> dst_blk), check if dst_blk dominates src_blk.
                for &src_blk in &func_blocks {
                    if !reachable.contains(&src_blk) { continue; }
                    if let Some(nexts) = adj.get(&src_blk) {
                        for &dst_blk in nexts {
                            if !reachable.contains(&dst_blk) { continue; }
                            // Check if dst_blk dominates src_blk:
                            // dst_blk dominates src_blk iff entry cannot reach src_blk while avoiding dst_blk.
                            if dst_blk == src_blk {
                                // Self-loop: the block dominates itself, so this is a back-edge.
                                func_back_edges.entry(func).or_default().insert((src_blk, dst_blk));
                                continue;
                            }
                            if dst_blk == entry_blk {
                                // Entry dominates everything reachable.
                                func_back_edges.entry(func).or_default().insert((src_blk, dst_blk));
                                continue;
                            }
                            // BFS from entry avoiding dst_blk: can we reach src_blk?
                            let mut visited_avoid: HashSet<Node> = HashSet::new();
                            let mut q = VecDeque::new();
                            visited_avoid.insert(entry_blk);
                            if entry_blk != dst_blk {
                                q.push_back(entry_blk);
                            }
                            let mut reached_src = entry_blk == src_blk;
                            while let Some(blk) = q.pop_front() {
                                if blk == src_blk { reached_src = true; break; }
                                if let Some(nbs) = adj.get(&blk) {
                                    for &nb in nbs {
                                        if nb != dst_blk && visited_avoid.insert(nb) {
                                            q.push_back(nb);
                                        }
                                    }
                                }
                            }
                            if !reached_src {
                                // dst_blk dominates src_blk -> this is a back-edge.
                                func_back_edges.entry(func).or_default().insert((src_blk, dst_blk));
                            }
                        }
                    }
                }
            }
        }

        // BFS-based block reachability check, excluding back-edges.
        let block_reaches = |func: u64, from_blk: Node, to_blk: Node| -> bool {
            if from_blk == to_blk { return true; }
            let adj = match func_block_adj.get(&func) { Some(a) => a, None => return false };
            let back_edges = func_back_edges.get(&func);
            let mut visited = HashSet::new();
            let mut queue = VecDeque::new();
            visited.insert(from_blk);
            queue.push_back(from_blk);
            while let Some(blk) = queue.pop_front() {
                if let Some(nexts) = adj.get(&blk) {
                    for &nb in nexts {
                        // Skip back-edges (where destination dominates source).
                        if let Some(be) = back_edges {
                            if be.contains(&(blk, nb)) { continue; }
                        }
                        if nb == to_blk { return true; }
                        if visited.insert(nb) { queue.push_back(nb); }
                    }
                }
            }
            false
        };

        // Collect all (def_addr, mreg) that define mreg for intervening-def validation.
        let asm_effective_def: HashSet<(Node, Mreg)> = db.rel_iter::<(Node, Mreg)>("asm_effective_def").cloned().collect();

        // Validate has_intervening_def: check that a REAL intervening def exists on a function-scoped CFG path.
        let validate_intervening = |def_addr: Node, use_addr: Node, mreg: Mreg, func: u64| -> bool {
            let def_blk = match node_to_block.get(&def_addr) { Some(&b) => b, None => return false };
            let use_blk = match node_to_block.get(&use_addr) { Some(&b) => b, None => return false };
            for &(mid_addr, ref mid_mreg) in &asm_effective_def {
                if *mid_mreg != mreg || mid_addr == def_addr || mid_addr == use_addr { continue; }
                if node_to_func.get(&mid_addr) != Some(&func) { continue; }
                let mid_blk = match node_to_block.get(&mid_addr) { Some(&b) => b, None => continue };
                // Same-block: check address ordering.
                if def_blk == mid_blk && mid_blk == use_blk {
                    if mid_addr > def_addr && mid_addr < use_addr { return true; }
                    continue;
                }
                // Cross-block: check block reachability.
                if block_reaches(func, def_blk, mid_blk) && block_reaches(func, mid_blk, use_blk) {
                    return true;
                }
            }
            false
        };

        // For each def->use edge, merge canonicals using function-scoped validation.
        for &(def_addr, mreg, use_addr) in &reg_def_used_data {
            if def_addr != use_addr && validate_intervening(def_addr, use_addr, mreg, *node_to_func.get(&def_addr).unwrap_or(&0)) {
                continue;
            }
            match (node_to_func.get(&def_addr), node_to_func.get(&use_addr)) {
                (Some(f1), Some(f2)) if f1 == f2 => {}
                _ => continue,
            }
            let def_canonical = match node_mreg_def_canonical.get(&(def_addr, mreg)) {
                Some(&dc) => uf.find(dc),
                None => continue,
            };
            if let Some(use_canonicals) = node_mreg_use_canonicals.get(&(use_addr, mreg)) {
                for &uc in use_canonicals {
                    let uc = uf.find(uc);
                    if uc != def_canonical {
                        uf.union(def_canonical, uc);
                    }
                }
            }
        }
    }

    let xtl_canonical = ascent::boxcar::Vec::new();
    let mut all_ids: Vec<RTLReg> = Vec::new();
    for &(_, _, id) in &reg_xtl_data {
        all_ids.push(id);
    }
    for &(_, _, _, id) in &stack_xtl_data {
        all_ids.push(id);
    }
    for &(_, id) in &is_def_data {
        all_ids.push(id);
    }
    for &(id1, id2) in &alias_edge_data {
        all_ids.push(id1);
        all_ids.push(id2);
    }
    all_ids.sort_unstable();
    all_ids.dedup();

    for id in &all_ids {
        let canonical = uf.find(*id);
        xtl_canonical.push((*id, canonical));
    }
    db.rel_set("xtl_canonical", xtl_canonical);
}
