
use std::collections::{HashMap, HashSet};

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

// Phase 2: union-find over alias_edge to compute xtl_canonical, then populate reg_rtl.
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

        let intervening_set: HashSet<(Node, Node, Mreg)> = db
            .rel_iter::<(Node, Node, Mreg)>("has_intervening_def")
            .cloned()
            .collect();

        let reg_def_used_data: Vec<(Node, Mreg, Node)> = db
            .rel_iter::<(Node, Mreg, Node)>("reg_def_used")
            .cloned()
            .collect();

        // For each uninterrupted def->use edge, merge the def-side canonical with the use-side canonical(s).
        for &(def_addr, mreg, use_addr) in &reg_def_used_data {
            if intervening_set.contains(&(def_addr, use_addr, mreg)) {
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
