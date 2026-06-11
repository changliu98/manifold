use std::collections::{HashMap, HashSet};

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::x86::op::Condition;
use crate::x86::types::*;

// Convert an Osel-derived condition expression back into a (Condition, args) pair for Sifthenelse. Returns None for non-comparison conditions, which are left as ternaries.
fn cond_from_select_expr(e: &CsharpminorExpr) -> Option<(Condition, Vec<CsharpminorExpr>)> {
    let CsharpminorExpr::Ebinop(op, lhs, rhs) = e else { return None; };
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
    fn from_const(c: i64) -> Self { Self { coeff: 0, constant: c } }
    fn from_disc() -> Self { Self { coeff: 1, constant: 0 } }
    // Wrapping arithmetic throughout to match eval() (machine-register algebra mod 2^64): an oversized IR constant wraps instead of panicking in debug, and non-switch shapes are rejected later by the case-count/uniqueness checks.
    fn add(self, other: Self) -> Self {
        Self { coeff: self.coeff.wrapping_add(other.coeff), constant: self.constant.wrapping_add(other.constant) }
    }
    fn sub(self, other: Self) -> Self {
        Self { coeff: self.coeff.wrapping_sub(other.coeff), constant: self.constant.wrapping_sub(other.constant) }
    }
    // Only linear-times-constant is supported: gcc/LLVM switch lowering produces only affine maps (a*disc+b), never disc*disc, so quadratic is impossible from a real switch and must not be rewritten.
    fn mul(self, other: Self) -> Option<Self> {
        if other.coeff == 0 {
            Some(Self { coeff: self.coeff.wrapping_mul(other.constant), constant: self.constant.wrapping_mul(other.constant) })
        } else if self.coeff == 0 {
            Some(Self { coeff: self.constant.wrapping_mul(other.coeff), constant: self.constant.wrapping_mul(other.constant) })
        } else {
            None
        }
    }
    fn eval(self, disc: i64) -> i64 { self.coeff.wrapping_mul(disc).wrapping_add(self.constant) }
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
            if *r == disc_reg { Some(LinearVal::from_disc()) }
            else { reg_vals.get(r).copied() }
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

// Detect closed-form switches inside one function. Pattern A: masked discriminant + sequential closed-form: Sset(R, R & M); Sset(S, formula(R)); ...; Sreturn(S). Pattern B: cmov with bound check: Sset(dst, Econdition(disc_bound_check, dst_old, temp_formula)).
fn detect_closed_form_in_func(
    stmts: &[(Node, CsharpminorStmt)],
    out_entries: &mut Vec<(Node, RTLReg, RTLReg, bool, i64)>,
    out_cases: &mut Vec<(Node, i64, i64)>,
) {
    if stmts.is_empty() { return; }

    // Pattern B: cmov closed-form (Econdition with bound check, single Sset rewriting dst).
    for (node, s) in stmts {
        if let CsharpminorStmt::Sset(dst, expr) = s {
            if let CsharpminorExpr::Econdition(cond, true_val, false_val) = expr {
                let cond_info = match cond.as_ref() {
                    CsharpminorExpr::Ebinop(CminorBinop::Ocmp(cmp), l, r)
                    | CsharpminorExpr::Ebinop(CminorBinop::Ocmpu(cmp), l, r)
                    | CsharpminorExpr::Ebinop(CminorBinop::Ocmpl(cmp), l, r)
                    | CsharpminorExpr::Ebinop(CminorBinop::Ocmplu(cmp), l, r) => {
                        if let (CsharpminorExpr::Evar(disc), CsharpminorExpr::Econst(c)) =
                            (l.as_ref(), r.as_ref())
                        {
                            let bound = match c {
                                Constant::Ointconst(v) => *v as i64,
                                Constant::Olongconst(v) => *v,
                                _ => continue,
                            };
                            // Cge/Cgt: disc out-of-range goes to default (true branch is default). Clt/Cle: disc in-range goes to formula (false branch is default). saturating_add keeps an out-of-range bound (e.g. i64::MAX from a non-switch compare) from overflowing before the [2,32] range guard rejects it.
                            let (case_count, default_is_true) = match cmp {
                                crate::x86::op::Comparison::Cge => (bound, true),
                                crate::x86::op::Comparison::Cgt => (bound.saturating_add(1), true),
                                crate::x86::op::Comparison::Clt => (bound, false),
                                crate::x86::op::Comparison::Cle => (bound.saturating_add(1), false),
                                _ => continue,
                            };
                            if case_count < 2 || case_count > 32 { continue; }
                            Some((*disc, case_count, default_is_true))
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                let (disc_reg, case_count, default_is_true) = match cond_info { Some(t) => t, None => continue };

                let (default_branch_expr, formula_branch_expr) = if default_is_true {
                    (true_val.as_ref(), false_val.as_ref())
                } else {
                    (false_val.as_ref(), true_val.as_ref())
                };

                let true_const = match default_branch_expr {
                    CsharpminorExpr::Evar(r) => {
                        let mut found = None;
                        for (n, s2) in stmts {
                            if *n >= *node { break; }
                            if let CsharpminorStmt::Sset(d2, e2) = s2 {
                                if *d2 == *r {
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
                let default_val = match true_const { Some(v) => v, None => continue };

                let temp_reg = match formula_branch_expr {
                    CsharpminorExpr::Evar(r) => *r,
                    _ => continue,
                };

                // The asm-to-RTL pass renames machine regs per-instruction, so the bound-check's reg may differ from the register the formula was computed from. Try several candidates including leaf regs in prior Ssets.
                let mut disc_candidates: Vec<RTLReg> = vec![disc_reg];
                {
                    let mut seen: std::collections::HashSet<RTLReg> = disc_candidates.iter().copied().collect();
                    for (n, s2) in stmts {
                        if *n >= *node { break; }
                        if let CsharpminorStmt::Sset(_, e2) = s2 {
                            collect_leaf_evars(e2, &mut |r| {
                                if seen.insert(r) {
                                    disc_candidates.push(r);
                                }
                            });
                        }
                    }
                }

                let mut chosen: Option<(RTLReg, LinearVal)> = None;
                for &cand in &disc_candidates {
                    let mut reg_vals: HashMap<RTLReg, LinearVal> = HashMap::new();
                    for (n, s2) in stmts {
                        if *n >= *node { break; }
                        if let CsharpminorStmt::Sset(d2, e2) = s2 {
                            if let Some(lv) = eval_csharp_expr(e2, cand, &reg_vals) {
                                reg_vals.insert(*d2, lv);
                            } else {
                                reg_vals.remove(d2);
                            }
                        }
                    }
                    if let Some(&formula) = reg_vals.get(&temp_reg) {
                        if formula.coeff != 0 {
                            chosen = Some((cand, formula));
                            break;
                        }
                    }
                }

                let (final_disc, formula) = match chosen { Some(c) => c, None => continue };

                let mut case_set: std::collections::HashSet<i64> = std::collections::HashSet::new();
                let mut cases: Vec<(i64, i64)> = Vec::with_capacity(case_count as usize);
                for k in 0..case_count {
                    let v = formula.eval(k);
                    if !case_set.insert(v) {
                        cases.clear();
                        break;
                    }
                    cases.push((k, v));
                }
                if cases.is_empty() { continue; }

                out_entries.push((*node, final_disc, *dst, true, default_val));
                for (k, v) in cases {
                    out_cases.push((*node, k, v));
                }
            }
        }
    }

    // Pattern A: masked discriminant with sequential closed-form. Three safety conditions: (1) straight-line only (no branches), (2) disc_reg never redefined after mask (prevents miscompile where gcc lowers `(x&7)*100+5` by clobbering the masked reg in-place, causing stale discriminant reads), (3) unevaluable RHS poisons dst. Sstore/Scall side effects are skipped rather than bailed to handle the common "compute; store to global; return" shape.
    if let Some((_mask_node, mask_idx, disc_reg, mask)) = stmts.iter().enumerate()
        .find_map(|(i, (n, s))| match s {
            CsharpminorStmt::Sset(dst, expr) => {
                if let CsharpminorExpr::Ebinop(op, lhs, rhs) = expr {
                    let is_and = matches!(op, CminorBinop::Oand | CminorBinop::Oandl);
                    if !is_and { return None; }
                    if let (CsharpminorExpr::Evar(src), CsharpminorExpr::Econst(c)) = (lhs.as_ref(), rhs.as_ref()) {
                        if *src != *dst { return None; }
                        let m = match c {
                            Constant::Ointconst(v) => *v as i64,
                            Constant::Olongconst(v) => *v,
                            _ => return None,
                        };
                        if m > 0 && m <= 31 && (m & (m + 1)) == 0 {
                            return Some((*n, i, *dst, m));
                        }
                    }
                }
                None
            }
            _ => None,
        })
    {
        // Path purity: a jump into the walked region lets switch_node be reached without the mask, so bail if any jump target lands inside (exempting the Sreturn itself, which never executes switch_node).
        let mut jump_targets: HashSet<Node> = HashSet::new();
        for (_, s) in stmts {
            match s {
                CsharpminorStmt::Scond(_, _, t1, t2) => {
                    jump_targets.insert(*t1);
                    jump_targets.insert(*t2);
                }
                CsharpminorStmt::Sjump(t) => {
                    jump_targets.insert(*t);
                }
                CsharpminorStmt::Sjumptable(_, targets) => {
                    for t in targets.iter() {
                        jump_targets.insert(*t);
                    }
                }
                _ => {}
            }
        }

        let mut reg_vals: HashMap<RTLReg, LinearVal> = HashMap::new();
        let mut return_reg: Option<RTLReg> = None;
        let mut return_node: Option<Node> = None;
        let mut last_set_node_for_reg: HashMap<RTLReg, Node> = HashMap::new();
        let mut ok = true;
        for (n, s) in &stmts[mask_idx + 1..] {
            if jump_targets.contains(n) && !matches!(s, CsharpminorStmt::Sreturn(_)) {
                ok = false;
                break;
            }
            match s {
                CsharpminorStmt::Sset(d, e) => {
                    // Discriminant purity: any redefinition makes the emitted Sswitch discriminant stale even when the RHS is affine-evaluable.
                    if *d == disc_reg {
                        ok = false;
                        break;
                    }
                    if let Some(lv) = eval_csharp_expr(e, disc_reg, &reg_vals) {
                        reg_vals.insert(*d, lv);
                        last_set_node_for_reg.insert(*d, *n);
                    } else {
                        // (3) unevaluable RHS: poison dst; only bail later if it feeds the formula.
                        reg_vals.remove(d);
                    }
                }
                CsharpminorStmt::Sreturn(e) => {
                    if let CsharpminorExpr::Evar(r) = e {
                        return_reg = Some(*r);
                        return_node = Some(*n);
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
                // (1) any control transfer breaks the straight-line premise.
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
                        let mut case_set: std::collections::HashSet<i64> = std::collections::HashSet::new();
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
                            let switch_node = last_set_node_for_reg.get(&rreg).copied().unwrap_or(rnode);
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
    fn name(&self) -> &'static str { "closed_form_switch" }

    fn run(&self, db: &mut DecompileDB) {
        let stmts_by_func: HashMap<Address, Vec<(Node, CsharpminorStmt)>> = {
            let mut by_func: HashMap<Address, Vec<(Node, CsharpminorStmt)>> = HashMap::new();
            let in_func: HashMap<Node, Address> = db
                .rel_iter::<(Node, Address)>("instr_in_function")
                .map(|(n, f)| (*n, *f))
                .collect();
            for (node, stmt) in db.rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt") {
                if let Some(&func) = in_func.get(node) {
                    by_func.entry(func).or_default().push((*node, stmt.clone()));
                }
            }
            for stmts in by_func.values_mut() {
                stmts.sort_by_key(|(n, _)| *n);
            }
            by_func
        };

        let mut new_entries: Vec<(Node, RTLReg, RTLReg, bool, i64)> = Vec::new();
        let mut new_cases: Vec<(Node, i64, i64)> = Vec::new();

        for stmts in stmts_by_func.values() {
            detect_closed_form_in_func(stmts, &mut new_entries, &mut new_cases);
        }

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
        let reuse: HashSet<Node> = db.rel_iter::<(Node,)>("cmov_reuse_node").map(|(n,)| *n).collect();
        if !reuse.is_empty() {
            let switch_nodes: HashSet<Node> = new_entries.iter().map(|(n, ..)| *n).collect();
            let lifted: Vec<(Node, CsharpminorStmt)> = db
                .rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt")
                .filter_map(|(n, s)| {
                    if !reuse.contains(n) || switch_nodes.contains(n) {
                        return None;
                    }
                    if let CsharpminorStmt::Sset(reg, CsharpminorExpr::Econdition(cond_expr, true_val, false_val)) = s {
                        if let Some((cond, cond_args)) = cond_from_select_expr(cond_expr) {
                            let then_stmt = Box::new(CsharpminorStmt::Sset(*reg, (**true_val).clone()));
                            let else_stmt = Box::new(CsharpminorStmt::Sset(*reg, (**false_val).clone()));
                            return Some((*n, CsharpminorStmt::Sifthenelse(cond, cond_args, then_stmt, else_stmt)));
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
        &["csharp_stmt", "instr_in_function", "cmov_reuse_node"]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &["closed_form_switch", "closed_form_switch_case", "csharp_stmt"]
    }
}
