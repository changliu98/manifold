use std::collections::{HashMap, HashSet};

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::x86::op::Condition;
use crate::x86::types::*;

// Convert an Osel-derived condition expression back into a (Condition, args) pair for Sifthenelse. Returns None for non-comparison conditions, which are left as ternaries.
fn cond_from_select_expr(e: &CsharpminorExpr) -> Option<(Condition, Vec<CsharpminorExpr>)> {
    let CsharpminorExpr::Ebinop(op, lhs, rhs) = e else {
        return None;
    };
    let lhs_c = (**lhs).clone();
    let imm = match rhs.as_ref() {
        CsharpminorExpr::Econst(Constant::Ointconst(c)) => Some(*c as i64),
        CsharpminorExpr::Econst(Constant::Olongconst(c)) => Some(*c),
        _ => None,
    };
    Some(match (op, imm) {
        (CminorBinop::Ocmp(c), Some(k)) => (Condition::Ccompimm(*c, k), vec![lhs_c]),
        (CminorBinop::Ocmpu(c), Some(k)) => (Condition::Ccompuimm(*c, k), vec![lhs_c]),
        (CminorBinop::Ocmpl(c), Some(k)) => (Condition::Ccomplimm(*c, k), vec![lhs_c]),
        (CminorBinop::Ocmplu(c), Some(k)) => (Condition::Ccompluimm(*c, k), vec![lhs_c]),
        (CminorBinop::Ocmp(c), None) => (Condition::Ccomp(*c), vec![lhs_c, (**rhs).clone()]),
        (CminorBinop::Ocmpu(c), None) => (Condition::Ccompu(*c), vec![lhs_c, (**rhs).clone()]),
        (CminorBinop::Ocmpl(c), None) => (Condition::Ccompl(*c), vec![lhs_c, (**rhs).clone()]),
        (CminorBinop::Ocmplu(c), None) => (Condition::Ccomplu(*c), vec![lhs_c, (**rhs).clone()]),
        (CminorBinop::Ocmpf(c), _) => (Condition::Ccompf(*c), vec![lhs_c, (**rhs).clone()]),
        (CminorBinop::Ocmpfs(c), _) => (Condition::Ccompfs(*c), vec![lhs_c, (**rhs).clone()]),
        (CminorBinop::Ocmpnotf(c), _) => (Condition::Cnotcompf(*c), vec![lhs_c, (**rhs).clone()]),
        (CminorBinop::Ocmpnotfs(c), _) => (Condition::Cnotcompfs(*c), vec![lhs_c, (**rhs).clone()]),
        _ => return None,
    })
}

// Linear-in-disc value: `coeff * disc + constant`. Used to symbolically evaluate the RHS of Sset chains in closed-form switch detection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LinearVal {
    coeff: i64,
    constant: i64,
}

impl LinearVal {
    fn from_const(c: i64) -> Self {
        Self {
            coeff: 0,
            constant: c,
        }
    }
    fn from_disc() -> Self {
        Self {
            coeff: 1,
            constant: 0,
        }
    }
    // Wrapping arithmetic throughout to match eval() (machine-register algebra mod 2^64): an oversized IR constant wraps instead of panicking in debug, and non-switch shapes are rejected later by the case-count/uniqueness checks.
    fn add(self, other: Self) -> Self {
        Self {
            coeff: self.coeff.wrapping_add(other.coeff),
            constant: self.constant.wrapping_add(other.constant),
        }
    }
    fn sub(self, other: Self) -> Self {
        Self {
            coeff: self.coeff.wrapping_sub(other.coeff),
            constant: self.constant.wrapping_sub(other.constant),
        }
    }
    // Only linear-times-constant is supported: gcc/LLVM switch lowering produces only affine maps (a*disc+b), never disc*disc, so quadratic is impossible from a real switch and must not be rewritten.
    fn mul(self, other: Self) -> Option<Self> {
        if other.coeff == 0 {
            Some(Self {
                coeff: self.coeff.wrapping_mul(other.constant),
                constant: self.constant.wrapping_mul(other.constant),
            })
        } else if self.coeff == 0 {
            Some(Self {
                coeff: self.constant.wrapping_mul(other.coeff),
                constant: self.constant.wrapping_mul(other.constant),
            })
        } else {
            None
        }
    }
    fn eval(self, disc: i64) -> i64 {
        self.coeff.wrapping_mul(disc).wrapping_add(self.constant)
    }
}

fn collect_leaf_evars<F: FnMut(RTLReg)>(expr: &CsharpminorExpr, f: &mut F) {
    match expr {
        CsharpminorExpr::Evar(r) => f(*r),
        CsharpminorExpr::Ebinop(_, lhs, rhs) => {
            collect_leaf_evars(lhs, f);
            collect_leaf_evars(rhs, f);
        }
        CsharpminorExpr::Eunop(_, inner) => collect_leaf_evars(inner, f),
        CsharpminorExpr::Eload(_, addr) => collect_leaf_evars(addr, f),
        CsharpminorExpr::Econdition(c, t, e) => {
            collect_leaf_evars(c, f);
            collect_leaf_evars(t, f);
            collect_leaf_evars(e, f);
        }
        _ => {}
    }
}

fn eval_csharp_expr(
    expr: &CsharpminorExpr,
    disc_reg: RTLReg,
    reg_vals: &HashMap<RTLReg, LinearVal>,
) -> Option<LinearVal> {
    match expr {
        CsharpminorExpr::Evar(r) => {
            if *r == disc_reg {
                Some(LinearVal::from_disc())
            } else {
                reg_vals.get(r).copied()
            }
        }
        CsharpminorExpr::Econst(c) => match c {
            Constant::Ointconst(v) => Some(LinearVal::from_const(*v as i64)),
            Constant::Olongconst(v) => Some(LinearVal::from_const(*v)),
            _ => None,
        },
        CsharpminorExpr::Ebinop(op, lhs, rhs) => {
            let l = eval_csharp_expr(lhs, disc_reg, reg_vals)?;
            let r = eval_csharp_expr(rhs, disc_reg, reg_vals)?;
            match op {
                CminorBinop::Oadd | CminorBinop::Oaddl => Some(l.add(r)),
                CminorBinop::Osub | CminorBinop::Osubl => Some(l.sub(r)),
                CminorBinop::Omul | CminorBinop::Omull => l.mul(r),
                _ => None,
            }
        }
        _ => None,
    }
}

// Symbolically evaluate expr to a LinearVal using only reg_vals, so a register read always reflects its most recent in-block definition; returns None for any non-affine sub-expression.
fn eval_linear(expr: &CsharpminorExpr, reg_vals: &HashMap<RTLReg, LinearVal>) -> Option<LinearVal> {
    match expr {
        CsharpminorExpr::Evar(r) => reg_vals.get(r).copied(),
        CsharpminorExpr::Econst(c) => match c {
            Constant::Ointconst(v) => Some(LinearVal::from_const(*v as i64)),
            Constant::Olongconst(v) => Some(LinearVal::from_const(*v)),
            _ => None,
        },
        CsharpminorExpr::Ebinop(op, lhs, rhs) => {
            let l = eval_linear(lhs, reg_vals)?;
            let r = eval_linear(rhs, reg_vals)?;
            match op {
                CminorBinop::Oadd | CminorBinop::Oaddl => Some(l.add(r)),
                CminorBinop::Osub | CminorBinop::Osubl => Some(l.sub(r)),
                CminorBinop::Omul | CminorBinop::Omull => l.mul(r),
                _ => None,
            }
        }
        _ => None,
    }
}

// True if the statement can leave the straight-line run inside a basic block. CLOSED-1 refuses to fold a reaching-def chain across such a statement: only then is the cmov's discriminant provably the value the bound check tests.
fn is_control_transfer(s: &CsharpminorStmt) -> bool {
    !matches!(
        s,
        CsharpminorStmt::Sset(..)
            | CsharpminorStmt::Sstore(..)
            | CsharpminorStmt::Scall(..)
            | CsharpminorStmt::Sbuiltin(..)
            | CsharpminorStmt::Snop
    )
}

/// Function-local statement graph used by the closed-form recognizers.
///
/// `cminor_succ` is the authoritative CFG at this layer.  Node identifiers are
/// opaque: neither recognizer uses their magnitude to infer execution order.
struct StatementCfg {
    stmts: HashMap<Node, CsharpminorStmt>,
    succs: HashMap<Node, HashSet<Node>>,
    preds: HashMap<Node, HashSet<Node>>,
    block_of: HashMap<Node, Node>,
    block_nodes: HashMap<Node, HashSet<Node>>,
}

impl StatementCfg {
    fn new(
        stmts: HashMap<Node, CsharpminorStmt>,
        global_block_of: &HashMap<Node, Node>,
        global_succs: &HashMap<Node, HashSet<Node>>,
        global_preds: &HashMap<Node, HashSet<Node>>,
    ) -> Self {
        let mut succs: HashMap<Node, HashSet<Node>> = HashMap::new();
        let mut preds: HashMap<Node, HashSet<Node>> = HashMap::new();
        for &node in stmts.keys() {
            // Retain every edge incident to this function view.  An unexpected
            // cross-function endpoint then makes a candidate ambiguous instead
            // of being silently discarded.  Starting from the function's nodes
            // avoids rescanning the whole binary CFG once per function.
            if let Some(dsts) = global_succs.get(&node) {
                for &dst in dsts {
                    succs.entry(node).or_default().insert(dst);
                    preds.entry(dst).or_default().insert(node);
                }
            }
            if let Some(srcs) = global_preds.get(&node) {
                for &src in srcs {
                    succs.entry(src).or_default().insert(node);
                    preds.entry(node).or_default().insert(src);
                }
            }
        }

        let mut block_of = HashMap::new();
        let mut block_nodes: HashMap<Node, HashSet<Node>> = HashMap::new();
        for &node in stmts.keys() {
            if let Some(&block) = global_block_of.get(&node) {
                block_of.insert(node, block);
                block_nodes.entry(block).or_default().insert(node);
            }
        }

        Self {
            stmts,
            succs,
            preds,
            block_of,
            block_nodes,
        }
    }

    fn same_block_preds(&self, node: Node, block: Node) -> Vec<Node> {
        self.preds
            .get(&node)
            .into_iter()
            .flat_map(|ps| ps.iter().copied())
            .filter(|p| self.block_of.get(p).copied() == Some(block))
            .collect()
    }

    /// Statements from the unique block root through the statement immediately
    /// preceding `target`, in CFG execution order.  Refuse disconnected blocks,
    /// joins, side entries, forks, cycles, and control transfers.
    fn unique_block_prefix(&self, target: Node) -> Option<Vec<Node>> {
        let block = *self.block_of.get(&target)?;
        let nodes = self.block_nodes.get(&block)?;

        let roots: Vec<Node> = nodes
            .iter()
            .copied()
            .filter(|n| self.same_block_preds(*n, block).is_empty())
            .collect();
        if roots.len() != 1 {
            return None;
        }
        let root = roots[0];

        let mut reverse_prefix = Vec::new();
        let mut seen = HashSet::from([target]);
        let mut current = target;
        loop {
            let all_preds = self.preds.get(&current).cloned().unwrap_or_default();
            if all_preds.iter().any(|p| !self.stmts.contains_key(p)) {
                return None;
            }
            let same_block = self.same_block_preds(current, block);
            if same_block.is_empty() {
                // The explicit block root may have one incoming edge from its
                // predecessor block.  More than one is a join, not a unique
                // straight-line entry.
                if current != root || all_preds.len() > 1 {
                    return None;
                }
                break;
            }
            if same_block.len() != 1 || all_preds.len() != 1 {
                return None;
            }

            let pred = same_block[0];
            let pred_stmt = self.stmts.get(&pred)?;
            if is_control_transfer(pred_stmt) {
                return None;
            }
            let pred_succs = self.succs.get(&pred)?;
            if pred_succs.len() != 1 || !pred_succs.contains(&current) {
                return None;
            }
            if !seen.insert(pred) {
                return None;
            }
            reverse_prefix.push(pred);
            current = pred;
        }

        reverse_prefix.reverse();
        Some(reverse_prefix)
    }

    /// Statements strictly after `start` through a unique terminal return.
    /// The entire basic block must be this one structural path; this keeps an
    /// unreachable fragment in the same block from being mistaken for a suffix.
    fn unique_block_suffix_to_return(&self, start: Node) -> Option<Vec<Node>> {
        let block = *self.block_of.get(&start)?;
        let prefix = self.unique_block_prefix(start)?;
        let mut covered: HashSet<Node> = prefix.into_iter().collect();
        covered.insert(start);

        let mut suffix = Vec::new();
        let mut current = start;
        loop {
            let stmt = self.stmts.get(&current)?;
            if current != start && matches!(stmt, CsharpminorStmt::Sreturn(_)) {
                if self.succs.get(&current).is_some_and(|ss| !ss.is_empty()) {
                    return None;
                }
                let block_nodes = self.block_nodes.get(&block)?;
                return (covered == *block_nodes).then_some(suffix);
            }
            if is_control_transfer(stmt) {
                return None;
            }

            let successors = self.succs.get(&current)?;
            if successors.len() != 1 {
                return None;
            }
            let next = *successors.iter().next()?;
            if !self.stmts.contains_key(&next) || self.block_of.get(&next).copied() != Some(block) {
                return None;
            }
            let next_preds = self.preds.get(&next)?;
            if next_preds.len() != 1 || !next_preds.contains(&current) {
                return None;
            }
            if !covered.insert(next) {
                return None;
            }
            suffix.push(next);
            current = next;
        }
    }
}

// Detect closed-form switches in one function: Pattern A (masked discriminant + sequential formula), Pattern B (cmov with bound check).
fn detect_closed_form_in_func(
    cfg: &StatementCfg,
    func_has_data_lookup: bool,
    out_entries: &mut Vec<(Node, RTLReg, RTLReg, bool, i64)>,
    out_cases: &mut Vec<(Node, i64, i64)>,
) {
    if cfg.stmts.is_empty() {
        return;
    }

    // Data-lookup guard: a function whose switch was lowered to a rodata value table is recovered by data_lookup_table, and Pattern B would collapse that real switch into a degenerate closed form.
    if !func_has_data_lookup {
        detect_pattern_b(cfg, out_entries, out_cases);
    }

    detect_pattern_a(cfg, out_entries, out_cases);
}

// Pattern B: cmov closed-form (Econdition with unsigned bound check, single Sset rewriting dst).
fn detect_pattern_b(
    cfg: &StatementCfg,
    out_entries: &mut Vec<(Node, RTLReg, RTLReg, bool, i64)>,
    out_cases: &mut Vec<(Node, i64, i64)>,
) {
    for (node, s) in &cfg.stmts {
        let CsharpminorStmt::Sset(dst, expr) = s else {
            continue;
        };
        let CsharpminorExpr::Econdition(cond, true_val, false_val) = expr else {
            continue;
        };

        // CLOSED-3: a 0-based switch dispatch always uses an UNSIGNED upper-bound test (the lowering subtracts the low case then compares unsigned). Signed Ocmp/Ocmpl compares come from min/max/clamp idioms, not switch dispatch, so accept only Ocmpu/Ocmplu here.
        let cond_info = match cond.as_ref() {
            CsharpminorExpr::Ebinop(CminorBinop::Ocmpu(cmp), l, r)
            | CsharpminorExpr::Ebinop(CminorBinop::Ocmplu(cmp), l, r) => {
                if let (CsharpminorExpr::Evar(disc), CsharpminorExpr::Econst(c)) =
                    (l.as_ref(), r.as_ref())
                {
                    let bound = match c {
                        Constant::Ointconst(v) => *v as i64,
                        Constant::Olongconst(v) => *v,
                        _ => continue,
                    };
                    // Cge/Cgt send out-of-range to default, Clt/Cle send in-range to the formula; saturating_add keeps an out-of-range bound from overflowing before the [2,32] range guard rejects it.
                    let (case_count, default_is_true) = match cmp {
                        crate::x86::op::Comparison::Cge => (bound, true),
                        crate::x86::op::Comparison::Cgt => (bound.saturating_add(1), true),
                        crate::x86::op::Comparison::Clt => (bound, false),
                        crate::x86::op::Comparison::Cle => (bound.saturating_add(1), false),
                        _ => continue,
                    };
                    if case_count < 2 || case_count > 32 {
                        continue;
                    }
                    Some((*disc, case_count, default_is_true))
                } else {
                    None
                }
            }
            _ => None,
        };
        let (disc_reg, case_count, default_is_true) = match cond_info {
            Some(t) => t,
            None => continue,
        };

        // CLOSED-1: reaching definitions come only from the unique structural
        // predecessor path in this basic block.  Node/address magnitude says
        // nothing about which statement executes first.
        let Some(prefix_nodes) = cfg.unique_block_prefix(*node) else {
            continue;
        };
        let inblock_prefix: Vec<(Node, &CsharpminorStmt)> = prefix_nodes
            .into_iter()
            .filter_map(|n| cfg.stmts.get(&n).map(|s| (n, s)))
            .collect();

        let (default_branch_expr, formula_branch_expr) = if default_is_true {
            (true_val.as_ref(), false_val.as_ref())
        } else {
            (false_val.as_ref(), true_val.as_ref())
        };

        let true_const = match default_branch_expr {
            CsharpminorExpr::Evar(r) => {
                let mut found = None;
                for (_, s2) in &inblock_prefix {
                    match s2 {
                        CsharpminorStmt::Sset(d2, e2) if *d2 == *r => {
                            if let CsharpminorExpr::Econst(c) = e2 {
                                found = match c {
                                    Constant::Ointconst(v) => Some(*v as i64),
                                    Constant::Olongconst(v) => Some(*v),
                                    _ => None,
                                };
                            } else {
                                found = None;
                            }
                        }
                        CsharpminorStmt::Scall(Some(d2), ..)
                        | CsharpminorStmt::Sbuiltin(Some(d2), ..)
                            if *d2 == *r =>
                        {
                            found = None;
                        }
                        _ => {}
                    }
                }
                found
            }
            CsharpminorExpr::Econst(c) => match c {
                Constant::Ointconst(v) => Some(*v as i64),
                Constant::Olongconst(v) => Some(*v),
                _ => None,
            },
            _ => None,
        };
        let default_val = match true_const {
            Some(v) => v,
            None => continue,
        };

        let temp_reg = match formula_branch_expr {
            CsharpminorExpr::Evar(r) => *r,
            _ => continue,
        };

        // CLOSED-2: anchor the switch on disc_reg and express the formula as affine in it, since bound-check and formula registers are different SSA names of one value.
        let mut defined_inblock: HashSet<RTLReg> = HashSet::new();
        let mut entry_live: HashSet<RTLReg> = HashSet::new();
        for (_, s2) in &inblock_prefix {
            match s2 {
                CsharpminorStmt::Sset(d2, e2) => {
                    // A read counts as entry-live only if the register has not yet been defined in-block.
                    collect_leaf_evars(e2, &mut |r| {
                        if !defined_inblock.contains(&r) {
                            entry_live.insert(r);
                        }
                    });
                    defined_inblock.insert(*d2);
                }
                CsharpminorStmt::Scall(Some(d2), ..) | CsharpminorStmt::Sbuiltin(Some(d2), ..) => {
                    defined_inblock.insert(*d2);
                }
                _ => {}
            }
        }
        // disc_reg is read at the cmov; it is entry-live iff it was never redefined in-block.
        if !defined_inblock.contains(&disc_reg) {
            entry_live.insert(disc_reg);
        }

        // Candidate free variables: disc_reg first (when entry-live), then every other block-entry-live register in deterministic (sorted) order so the chosen fold never depends on HashSet iteration order.
        let mut base_candidates: Vec<RTLReg> = Vec::new();
        if entry_live.contains(&disc_reg) {
            base_candidates.push(disc_reg);
        }
        {
            let mut sorted_live: Vec<RTLReg> = entry_live
                .iter()
                .copied()
                .filter(|r| *r != disc_reg)
                .collect();
            sorted_live.sort_unstable();
            base_candidates.extend(sorted_live);
        }

        // formula re-expressed as affine in disc_reg.
        let mut formula: Option<LinearVal> = None;
        for &base in &base_candidates {
            let mut reg_vals: HashMap<RTLReg, LinearVal> = HashMap::new();
            reg_vals.insert(base, LinearVal::from_disc());
            for (_, s2) in &inblock_prefix {
                match s2 {
                    CsharpminorStmt::Sset(d2, e2) => {
                        if let Some(lv) = eval_linear(e2, &reg_vals) {
                            reg_vals.insert(*d2, lv);
                        } else {
                            reg_vals.remove(d2);
                        }
                    }
                    CsharpminorStmt::Scall(Some(d2), ..)
                    | CsharpminorStmt::Sbuiltin(Some(d2), ..) => {
                        reg_vals.remove(d2);
                    }
                    _ => {}
                }
            }
            // disc in terms of base; the bound check reads disc_reg at the cmov.
            let disc_lv = if defined_inblock.contains(&disc_reg) {
                match reg_vals.get(&disc_reg) {
                    Some(lv) => *lv,
                    None => continue,
                }
            } else {
                // disc_reg never redefined in-block: it equals the entry value of disc_reg.
                if base == disc_reg {
                    LinearVal::from_disc()
                } else {
                    continue;
                }
            };
            // The discriminant must be an invertible affine function of base (coeff +/-1) for an integer-exact change of variable.
            if disc_lv.coeff != 1 && disc_lv.coeff != -1 {
                continue;
            }
            let Some(temp_lv) = reg_vals.get(&temp_reg).copied() else {
                continue;
            };
            // Change of variable base -> disc_reg, exact for cd in {+1,-1}: temp(disc) = (ct*cd)*disc + (dt - ct*cd*dd).
            let cd = disc_lv.coeff;
            let dd = disc_lv.constant;
            let coeff_disc = temp_lv.coeff.wrapping_mul(cd);
            let const_disc = temp_lv
                .constant
                .wrapping_sub(temp_lv.coeff.wrapping_mul(cd).wrapping_mul(dd));
            if coeff_disc == 0 {
                continue;
            }
            formula = Some(LinearVal {
                coeff: coeff_disc,
                constant: const_disc,
            });
            break;
        }

        let formula = match formula {
            Some(f) => f,
            None => continue,
        };
        // The emitted switch always discriminates on disc_reg (the bound-checked value); cases are indexed 0..case_count over it.
        let final_disc = disc_reg;

        let mut case_set: HashSet<i64> = HashSet::new();
        let mut cases: Vec<(i64, i64)> = Vec::with_capacity(case_count as usize);
        for k in 0..case_count {
            let v = formula.eval(k);
            if !case_set.insert(v) {
                cases.clear();
                break;
            }
            cases.push((k, v));
        }
        if cases.is_empty() {
            continue;
        }

        out_entries.push((*node, final_disc, *dst, true, default_val));
        for (k, v) in cases {
            out_cases.push((*node, k, v));
        }
    }
}

// Pattern A: masked discriminant with sequential closed-form, requiring straight-line code, no redefinition of disc_reg after the mask, and poisoning dst on an unevaluable RHS.
fn detect_pattern_a(
    cfg: &StatementCfg,
    out_entries: &mut Vec<(Node, RTLReg, RTLReg, bool, i64)>,
    out_cases: &mut Vec<(Node, i64, i64)>,
) {
    // Every mask is considered independently.  Iteration order is immaterial:
    // a candidate's suffix is determined entirely by CFG edges.
    for (&mask_node, mask_stmt) in &cfg.stmts {
        let (disc_reg, mask) = match mask_stmt {
            CsharpminorStmt::Sset(dst, CsharpminorExpr::Ebinop(op, lhs, rhs))
                if matches!(op, CminorBinop::Oand | CminorBinop::Oandl) =>
            {
                let (CsharpminorExpr::Evar(src), CsharpminorExpr::Econst(c)) =
                    (lhs.as_ref(), rhs.as_ref())
                else {
                    continue;
                };
                if src != dst {
                    continue;
                }
                let mask = match c {
                    Constant::Ointconst(v) => *v as i64,
                    Constant::Olongconst(v) => *v,
                    _ => continue,
                };
                if mask <= 0 || mask > 31 || (mask & (mask + 1)) != 0 {
                    continue;
                }
                (*dst, mask)
            }
            _ => continue,
        };

        let Some(path) = cfg.unique_block_suffix_to_return(mask_node) else {
            continue;
        };
        let mut reg_vals: HashMap<RTLReg, LinearVal> = HashMap::new();
        let mut return_reg: Option<RTLReg> = None;
        let mut return_node: Option<Node> = None;
        let mut last_set_node_for_reg: HashMap<RTLReg, Node> = HashMap::new();
        let mut ok = true;
        for n in path {
            let Some(s) = cfg.stmts.get(&n) else {
                ok = false;
                break;
            };
            match s {
                CsharpminorStmt::Sset(d, e) => {
                    // Discriminant purity: any redefinition makes the emitted Sswitch discriminant stale even when the RHS is affine-evaluable.
                    if *d == disc_reg {
                        ok = false;
                        break;
                    }
                    if let Some(lv) = eval_csharp_expr(e, disc_reg, &reg_vals) {
                        reg_vals.insert(*d, lv);
                        last_set_node_for_reg.insert(*d, n);
                    } else {
                        // (3) unevaluable RHS: poison dst; only bail later if it feeds the formula.
                        reg_vals.remove(d);
                    }
                }
                CsharpminorStmt::Sreturn(e) => {
                    if let CsharpminorExpr::Evar(r) = e {
                        return_reg = Some(*r);
                        return_node = Some(n);
                    }
                    break;
                }
                CsharpminorStmt::Snop => continue,
                // Memory effects touch no register dataflow and are preserved downstream in order.
                CsharpminorStmt::Sstore(..) => continue,
                // Calls/builtins: preserve side effects downstream; poison the result reg (unknown value), bail if it overwrites disc_reg.
                CsharpminorStmt::Scall(dst, ..) | CsharpminorStmt::Sbuiltin(dst, ..) => {
                    if let Some(d) = dst {
                        if *d == disc_reg {
                            ok = false;
                            break;
                        }
                        reg_vals.remove(d);
                    }
                }
                // `unique_block_suffix_to_return` already rejects every
                // transfer.  Keep this refusal defensive against future new
                // Csharpminor statement variants.
                _ => {
                    ok = false;
                    break;
                }
            }
        }

        if ok {
            if let (Some(rreg), Some(rnode)) = (return_reg, return_node) {
                if let Some(&formula) = reg_vals.get(&rreg) {
                    if formula.coeff != 0 {
                        let case_count = mask + 1;
                        let mut case_set: HashSet<i64> = HashSet::new();
                        let mut cases: Vec<(i64, i64)> = Vec::with_capacity(case_count as usize);
                        let mut all_unique = true;
                        for k in 0..case_count {
                            let v = formula.eval(k);
                            if !case_set.insert(v) {
                                all_unique = false;
                                break;
                            }
                            cases.push((k, v));
                        }
                        if all_unique {
                            let switch_node =
                                last_set_node_for_reg.get(&rreg).copied().unwrap_or(rnode);
                            out_entries.push((switch_node, disc_reg, rreg, false, 0));
                            for (k, v) in cases {
                                out_cases.push((switch_node, k, v));
                            }
                        }
                    }
                }
            }
        }
    }
}

pub struct ClosedFormSwitchPass;

impl IRPass for ClosedFormSwitchPass {
    fn name(&self) -> &'static str {
        "closed_form_switch"
    }

    fn run(&self, db: &mut DecompileDB) {
        // Shared nodes can legitimately belong to more than one function.  Do
        // not collapse that relation with last-write-wins HashMap insertion.
        let mut node_to_funcs: HashMap<Node, HashSet<Address>> = HashMap::new();
        for (node, func) in db.rel_iter::<(Node, Address)>("instr_in_function") {
            node_to_funcs.entry(*node).or_default().insert(*func);
        }

        // Preserve each function view of a shared statement, but refuse a node
        // with multiple distinct selected statements rather than selecting one
        // from relation iteration order.
        let mut stmt_choices: HashMap<Address, HashMap<Node, HashSet<CsharpminorStmt>>> =
            HashMap::new();
        for (node, stmt) in db.rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt") {
            if let Some(funcs) = node_to_funcs.get(node) {
                for &func in funcs {
                    stmt_choices
                        .entry(func)
                        .or_default()
                        .entry(*node)
                        .or_default()
                        .insert(stmt.clone());
                }
            }
        }
        let stmts_by_func: HashMap<Address, HashMap<Node, CsharpminorStmt>> = stmt_choices
            .into_iter()
            .map(|(func, choices)| {
                let stmts = choices
                    .into_iter()
                    .filter_map(|(node, variants)| {
                        (variants.len() == 1).then(|| (node, variants.into_iter().next().unwrap()))
                    })
                    .collect();
                (func, stmts)
            })
            .collect();

        // `code_in_block` explicitly identifies block membership; conflicting
        // membership is ambiguous and therefore omitted.
        let mut block_choices: HashMap<Node, HashSet<Node>> = HashMap::new();
        for (node, block) in db.rel_iter::<(Address, Address)>("code_in_block") {
            block_choices.entry(*node).or_default().insert(*block);
        }
        let block_of: HashMap<Node, Node> = block_choices
            .into_iter()
            .filter_map(|(node, blocks)| {
                (blocks.len() == 1).then(|| (node, *blocks.iter().next().unwrap()))
            })
            .collect();

        let mut cfg_succs: HashMap<Node, HashSet<Node>> = HashMap::new();
        let mut cfg_preds: HashMap<Node, HashSet<Node>> = HashMap::new();
        for (src, dst) in db.rel_iter::<(Node, Node)>("cminor_succ") {
            cfg_succs.entry(*src).or_default().insert(*dst);
            cfg_preds.entry(*dst).or_default().insert(*src);
        }

        // Functions containing a recovered data-lookup dispatch, which Pattern B must skip entirely since the real switch is recovered from the rodata table by a mutually exclusive lowering.
        let mut data_lookup_funcs: HashSet<Address> = HashSet::new();
        for (node, _base, _count, _scale, _idx) in
            db.rel_iter::<(Node, u64, usize, i64, &'static str)>("data_lookup_table")
        {
            if let Some(funcs) = node_to_funcs.get(node) {
                data_lookup_funcs.extend(funcs.iter().copied());
            }
        }

        let mut new_entries: Vec<(Node, RTLReg, RTLReg, bool, i64)> = Vec::new();
        let mut new_cases: Vec<(Node, i64, i64)> = Vec::new();

        for (func, stmts) in stmts_by_func {
            let func_has_data_lookup = data_lookup_funcs.contains(&func);
            let cfg = StatementCfg::new(stmts, &block_of, &cfg_succs, &cfg_preds);
            detect_closed_form_in_func(
                &cfg,
                func_has_data_lookup,
                &mut new_entries,
                &mut new_cases,
            );
        }

        // Stable relation storage only; tuple ordering is not used as control
        // flow or as a recognizer tie-break.
        new_entries.sort_unstable();
        new_entries.dedup();
        new_cases.sort_unstable();
        new_cases.dedup();

        let entry_rel = ascent::boxcar::Vec::<(Node, RTLReg, RTLReg, bool, i64)>::new();
        for e in &new_entries {
            entry_rel.push(*e);
        }
        db.rel_set("closed_form_switch", entry_rel);

        let case_rel = ascent::boxcar::Vec::<(Node, i64, i64)>::new();
        for c in &new_cases {
            case_rel.push(*c);
        }
        db.rel_set("closed_form_switch_case", case_rel);

        // Lift dispatch-style reuse-cmov selects (marked by rtl_pass) into if/else, skipping any node just detected as a closed-form switch (clight builds those from the facts above). Runs after detection so closed-form recovery sees the original conditional expression first.
        let reuse: HashSet<Node> = db
            .rel_iter::<(Node,)>("cmov_reuse_node")
            .map(|(n,)| *n)
            .collect();
        if !reuse.is_empty() {
            let switch_nodes: HashSet<Node> = new_entries.iter().map(|(n, ..)| *n).collect();
            let lifted: Vec<(Node, CsharpminorStmt)> = db
                .rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt")
                .filter_map(|(n, s)| {
                    if !reuse.contains(n) || switch_nodes.contains(n) {
                        return None;
                    }
                    if let CsharpminorStmt::Sset(
                        reg,
                        CsharpminorExpr::Econdition(cond_expr, true_val, false_val),
                    ) = s
                    {
                        if let Some((cond, cond_args)) = cond_from_select_expr(cond_expr) {
                            let then_stmt =
                                Box::new(CsharpminorStmt::Sset(*reg, (**true_val).clone()));
                            let else_stmt =
                                Box::new(CsharpminorStmt::Sset(*reg, (**false_val).clone()));
                            return Some((
                                *n,
                                CsharpminorStmt::Sifthenelse(cond, cond_args, then_stmt, else_stmt),
                            ));
                        }
                    }
                    None
                })
                .collect();
            if !lifted.is_empty() {
                let lifted_nodes: HashSet<Node> = lifted.iter().map(|(n, _)| *n).collect();
                let new_stmt_rel = ascent::boxcar::Vec::<(Node, CsharpminorStmt)>::new();
                for (n, s) in db.rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt") {
                    if !lifted_nodes.contains(n) {
                        new_stmt_rel.push((*n, s.clone()));
                    }
                }
                for t in lifted {
                    new_stmt_rel.push(t);
                }
                db.rel_set("csharp_stmt", new_stmt_rel);
            }
        }
    }

    fn inputs(&self) -> &'static [&'static str] {
        &[
            "csharp_stmt",
            "instr_in_function",
            "cmov_reuse_node",
            "code_in_block",
            "data_lookup_table",
            "cminor_succ",
        ]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "closed_form_switch",
            "closed_form_switch_case",
            "csharp_stmt",
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::x86::op::Comparison;
    use either::Either;

    fn var(reg: RTLReg) -> CsharpminorExpr {
        CsharpminorExpr::Evar(reg)
    }

    fn konst(value: i64) -> CsharpminorExpr {
        CsharpminorExpr::Econst(Constant::Olongconst(value))
    }

    fn bin(op: CminorBinop, lhs: CsharpminorExpr, rhs: CsharpminorExpr) -> CsharpminorExpr {
        CsharpminorExpr::Ebinop(op, Box::new(lhs), Box::new(rhs))
    }

    fn graph(
        stmts: Vec<(Node, CsharpminorStmt)>,
        edges: &[(Node, Node)],
        blocks: &[(Node, Node)],
    ) -> StatementCfg {
        let mut succs: HashMap<Node, HashSet<Node>> = HashMap::new();
        let mut preds: HashMap<Node, HashSet<Node>> = HashMap::new();
        for &(src, dst) in edges {
            succs.entry(src).or_default().insert(dst);
            preds.entry(dst).or_default().insert(src);
        }
        StatementCfg::new(
            stmts.into_iter().collect(),
            &blocks.iter().copied().collect(),
            &succs,
            &preds,
        )
    }

    fn cmov_stmt() -> CsharpminorStmt {
        CsharpminorStmt::Sset(
            4,
            CsharpminorExpr::Econdition(
                Box::new(bin(CminorBinop::Ocmpu(Comparison::Cge), var(1), konst(4))),
                Box::new(var(2)),
                Box::new(var(3)),
            ),
        )
    }

    fn pattern_b_stmts() -> Vec<(Node, CsharpminorStmt)> {
        vec![
            (90, CsharpminorStmt::Sset(2, konst(-1))),
            (
                10,
                CsharpminorStmt::Sset(3, bin(CminorBinop::Oaddl, var(1), konst(5))),
            ),
            (70, cmov_stmt()),
        ]
    }

    fn pattern_a_stmts() -> Vec<(Node, CsharpminorStmt)> {
        vec![
            (200, CsharpminorStmt::Snop),
            (
                90,
                CsharpminorStmt::Sset(1, bin(CminorBinop::Oandl, var(1), konst(3))),
            ),
            (
                10,
                CsharpminorStmt::Sset(2, bin(CminorBinop::Omull, var(1), konst(100))),
            ),
            (
                80,
                CsharpminorStmt::Sset(3, bin(CminorBinop::Oaddl, var(2), konst(5))),
            ),
            (20, CsharpminorStmt::Sreturn(var(3))),
        ]
    }

    fn detect(
        cfg: &StatementCfg,
    ) -> (
        Vec<(Node, RTLReg, RTLReg, bool, i64)>,
        Vec<(Node, i64, i64)>,
    ) {
        let mut entries = Vec::new();
        let mut cases = Vec::new();
        detect_closed_form_in_func(cfg, false, &mut entries, &mut cases);
        entries.sort_unstable();
        cases.sort_unstable();
        (entries, cases)
    }

    #[test]
    fn pattern_b_uses_nonmonotonic_cfg_prefix() {
        let cfg = graph(
            pattern_b_stmts(),
            &[(90, 10), (10, 70)],
            &[(90, 500), (10, 500), (70, 500)],
        );

        let (entries, cases) = detect(&cfg);
        assert_eq!(entries, vec![(70, 1, 4, true, -1)]);
        assert_eq!(cases, vec![(70, 0, 5), (70, 1, 6), (70, 2, 7), (70, 3, 8)]);
    }

    #[test]
    fn pattern_a_uses_nonmonotonic_cfg_suffix() {
        let cfg = graph(
            pattern_a_stmts(),
            &[(200, 90), (90, 10), (10, 80), (80, 20)],
            &[(200, 500), (90, 500), (10, 500), (80, 500), (20, 500)],
        );

        let (entries, cases) = detect(&cfg);
        assert_eq!(entries, vec![(80, 1, 3, false, 0)]);
        assert_eq!(
            cases,
            vec![(80, 0, 5), (80, 1, 105), (80, 2, 205), (80, 3, 305)]
        );
    }

    #[test]
    fn disconnected_definition_is_not_a_prefix() {
        let cfg = graph(
            pattern_b_stmts(),
            &[(10, 70)],
            &[(90, 500), (10, 500), (70, 500)],
        );

        assert!(detect(&cfg).0.is_empty());
    }

    #[test]
    fn side_entry_into_formula_chain_is_rejected() {
        let mut stmts = pattern_b_stmts();
        stmts.push((60, CsharpminorStmt::Snop));
        let cfg = graph(
            stmts,
            &[(90, 10), (60, 10), (10, 70)],
            &[(90, 500), (10, 500), (70, 500), (60, 600)],
        );

        assert!(detect(&cfg).0.is_empty());
    }

    #[test]
    fn opaque_call_result_kills_reaching_formula_value() {
        let mut stmts = pattern_b_stmts();
        stmts.push((
            50,
            CsharpminorStmt::Scall(
                Some(3),
                None,
                Either::Right(Either::Right("opaque")),
                Vec::new(),
            ),
        ));
        let cfg = graph(
            stmts,
            &[(90, 10), (10, 50), (50, 70)],
            &[(90, 500), (10, 500), (50, 500), (70, 500)],
        );

        assert!(detect(&cfg).0.is_empty());
    }

    #[test]
    fn intervening_branch_is_not_a_straight_line_suffix() {
        let mut stmts = pattern_a_stmts();
        stmts.push((
            40,
            CsharpminorStmt::Scond(Condition::Ccompimm(Comparison::Ceq, 0), Vec::new(), 10, 60),
        ));
        stmts.push((60, CsharpminorStmt::Sreturn(var(3))));
        let cfg = graph(
            stmts,
            &[(200, 90), (90, 40), (40, 10), (40, 60), (10, 80), (80, 20)],
            &[
                (200, 500),
                (90, 500),
                (40, 500),
                (10, 500),
                (60, 500),
                (80, 500),
                (20, 500),
            ],
        );

        assert!(detect(&cfg).0.is_empty());
    }

    #[test]
    fn scheduler_clones_authoritative_statement_cfg() {
        assert!(ClosedFormSwitchPass.inputs().contains(&"cminor_succ"));
    }
}
