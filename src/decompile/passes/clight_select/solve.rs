use std::collections::HashMap;
use rayon::prelude::*;

use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{DatatypeAccessor, DatatypeBuilder, DatatypeSort, Optimize, SatResult, Sort};

use crate::x86::types::{Address, ClightBinaryOp, ClightExpr, ClightStmt, ClightType, Ident, Node, RTLReg, XType};
use crate::decompile::passes::clight_select::query::FunctionData;
use crate::decompile::passes::clight_select::select::{
    callee_ident_from_expr, scan_pure_int_regs_stmt, ProgramSelectionState,
};

// Variant order in the Ty datatype; indices into DatatypeSort::variants.
const V_VOID: usize = 0;
const V_INT: usize = 1;
const V_FLOAT: usize = 2;
const V_STRUCT: usize = 3;
const V_PTR: usize = 4;

// Handles to the recursive `Ty` datatype, built once per Z3 Context (per worker thread).
struct TypeDt {
    dt: DatatypeSort,
}

impl TypeDt {
    fn build() -> Self {
        let dt = DatatypeBuilder::new("Ty")
            .variant("void", vec![])
            .variant("int", vec![])
            .variant("float", vec![])
            .variant("struct", vec![("sid", DatatypeAccessor::Sort(Sort::int()))])
            .variant("ptr", vec![("pointee", DatatypeAccessor::datatype("Ty"))])
            .finish();
        TypeDt { dt }
    }

    fn void(&self) -> Dynamic { self.dt.variants[V_VOID].constructor.apply(&[]) }
    fn int(&self) -> Dynamic { self.dt.variants[V_INT].constructor.apply(&[]) }
    fn float(&self) -> Dynamic { self.dt.variants[V_FLOAT].constructor.apply(&[]) }
    fn struct_(&self, sid: i64) -> Dynamic {
        self.dt.variants[V_STRUCT].constructor.apply(&[&Int::from_i64(sid)])
    }
    fn ptr(&self, pointee: &Dynamic) -> Dynamic {
        self.dt.variants[V_PTR].constructor.apply(&[pointee])
    }

    fn is_int(&self, x: &Dynamic) -> Bool { self.dt.variants[V_INT].tester.apply(&[x]).as_bool().unwrap() }
    fn is_float(&self, x: &Dynamic) -> Bool { self.dt.variants[V_FLOAT].tester.apply(&[x]).as_bool().unwrap() }
    fn is_struct(&self, x: &Dynamic) -> Bool { self.dt.variants[V_STRUCT].tester.apply(&[x]).as_bool().unwrap() }
    fn is_ptr(&self, x: &Dynamic) -> Bool { self.dt.variants[V_PTR].tester.apply(&[x]).as_bool().unwrap() }
    fn pointee(&self, x: &Dynamic) -> Dynamic { self.dt.variants[V_PTR].accessors[0].apply(&[x]) }

    // A fresh free type variable.
    fn fresh(&self) -> Dynamic {
        Dynamic::from_ast(&z3::ast::Datatype::fresh_const("ty", &self.dt.sort))
    }
}

// XType (signature types) -> a concrete Ty term.
fn xtype_to_ty(t: &TypeDt, xt: &XType) -> Dynamic {
    match xt {
        XType::Xvoid => t.void(),
        XType::Xfloat | XType::Xsingle => t.float(),
        XType::XstructPtr(sid) => t.ptr(&t.struct_(*sid as i64)),
        XType::Xptr | XType::Xcharptr | XType::Xcharptrptr | XType::Xintptr
        | XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr => t.ptr(&t.int()),
        _ => t.int(),
    }
}

// ClightType (expression annotations) -> a concrete Ty term.
fn clight_to_ty(t: &TypeDt, ct: &ClightType) -> Dynamic {
    match ct {
        ClightType::Tvoid => t.void(),
        ClightType::Tfloat(..) => t.float(),
        ClightType::Tstruct(sid, _) => t.struct_(*sid as i64),
        ClightType::Tpointer(inner, _) => {
            let pointee = clight_to_ty(t, inner);
            t.ptr(&pointee)
        }
        _ => t.int(),
    }
}

// Candidate type-string -> a concrete Ty term (the provenance prior).
fn cand_str_to_ty(t: &TypeDt, s: &str) -> Dynamic {
    if let Some(rest) = s.strip_prefix("ptr_struct_") {
        if let Ok(sid) = i64::from_str_radix(rest, 16) {
            return t.ptr(&t.struct_(sid));
        }
        return t.ptr(&t.int());
    }
    if s.starts_with("ptr_") {
        let pointee = if s == "ptr_double" || s == "ptr_float" { t.float() } else { t.int() };
        return t.ptr(&pointee);
    }
    if s.starts_with("float_") { return t.float(); }
    if s.starts_with("int_") { return t.int(); }
    t.int()
}

// float<->ptr is the only hard-illegal conversion under `-w` (int<->ptr, widths, int<->float are silent); returns the Bool "a and b are compatible".
fn compatible(t: &TypeDt, a: &Dynamic, b: &Dynamic) -> Bool {
    let bad1 = Bool::and(&[t.is_float(a), t.is_ptr(b)]);
    let bad2 = Bool::and(&[t.is_ptr(a), t.is_float(b)]);
    // A by-value struct is incompatible with any non-struct (scalar/pointer); penalizing `*(p+n) = scalar` where p was mistyped as a struct pointer pushes p to a scalar pointer so the matching int-deref form is selected.
    let bad3 = Bool::and(&[t.is_struct(a), t.is_struct(b).not()]);
    let bad4 = Bool::and(&[t.is_struct(a).not(), t.is_struct(b)]);
    Bool::or(&[bad1, bad2, bad3, bad4]).not()
}

fn assert_guarded(opt: &Optimize, guard: Option<&Bool>, cond: &Bool) {
    match guard {
        Some(g) => opt.assert(&g.implies(cond.clone())),
        None => opt.assert(cond),
    }
}

fn assert_soft_guarded(opt: &Optimize, guard: Option<&Bool>, cond: &Bool, w: u64) {
    match guard {
        Some(g) => opt.assert_soft(&g.implies(cond.clone()), w, None),
        None => opt.assert_soft(cond, w, None),
    }
}

// True if a cast operand's type comes from an inferable register (a free Ty var the solver can drive) rather than a concrete annotation/constant; a hard structural constraint only helps on a free var, so concrete operands stay soft (else a single-candidate node can go UNSAT).
fn cast_operand_is_inferable(e: &ClightExpr, tyvar: &HashMap<RTLReg, Dynamic>) -> bool {
    match e {
        ClightExpr::Etempvar(id, _) => tyvar.contains_key(&(*id as RTLReg)),
        ClightExpr::Ecast(inner, _) => cast_operand_is_inferable(inner, tyvar),
        _ => false,
    }
}

// True if `e`'s inferred type term is built from a free register variable (register var, deref of one, or pointer-arith result carrying one), so a structural constraint on it is satisfiable; any other form is fully concrete and asserting is_ptr/is_struct on it is redundant or forces whole-function UNSAT, so those are skipped and left to the emitter.
fn base_drives_free_var(e: &ClightExpr, tyvar: &HashMap<RTLReg, Dynamic>) -> bool {
    match e {
        ClightExpr::Etempvar(id, _) => tyvar.contains_key(&(*id as RTLReg)),
        ClightExpr::Ederef(inner, _) => base_drives_free_var(inner, tyvar),
        ClightExpr::Ebinop(ClightBinaryOp::Oadd | ClightBinaryOp::Osub, l, r, _) => {
            base_drives_free_var(l, tyvar) || base_drives_free_var(r, tyvar)
        }
        _ => false,
    }
}

// The single operator-typing rule: returns the Ty term of `e` and asserts the structural requirements its sub-expressions impose; `tyvar` holds each inferable register's free variable, non-inferable leaves fall back to their annotated type.
fn type_of(
    t: &TypeDt,
    tyvar: &HashMap<RTLReg, Dynamic>,
    opt: &Optimize,
    guard: Option<&Bool>,
    e: &ClightExpr,
) -> Dynamic {
    match e {
        ClightExpr::Etempvar(id, ct) => {
            tyvar.get(&(*id as RTLReg)).cloned().unwrap_or_else(|| clight_to_ty(t, ct))
        }
        ClightExpr::EconstInt(_, _) | ClightExpr::EconstLong(_, _) => t.int(),
        ClightExpr::EconstFloat(_, _) | ClightExpr::EconstSingle(_, _) => t.float(),
        ClightExpr::Evar(_, ct) | ClightExpr::EvarSymbol(_, ct) => clight_to_ty(t, ct),
        ClightExpr::Ederef(inner, _) => {
            let it = type_of(t, tyvar, opt, guard, inner);
            // deref requires a pointer and the result is the pointee; assert only when the base drives a free variable (on a concrete base it is redundant or forces whole-function UNSAT).
            if base_drives_free_var(inner, tyvar) {
                assert_guarded(opt, guard, &t.is_ptr(&it));
            }
            t.pointee(&it)
        }
        ClightExpr::Eaddrof(inner, _) => {
            let it = type_of(t, tyvar, opt, guard, inner);
            t.ptr(&it)
        }
        ClightExpr::Efield(base, _, ct) => {
            let bt = type_of(t, tyvar, opt, guard, base);
            // the field base (for `e.f`, or the pointee for `e->f` = (*p).f) must be a struct; assert only when it drives a free variable, for the same reason as deref above.
            if base_drives_free_var(base, tyvar) {
                assert_guarded(opt, guard, &t.is_struct(&bt));
            }
            clight_to_ty(t, ct)
        }
        ClightExpr::Ecast(inner, ct) => {
            let it = type_of(t, tyvar, opt, guard, inner);
            let tgt = clight_to_ty(t, ct);
            // Casting a floating operand to a pointer is illegal C everywhere; for an inferable register enforce "operand is not float" HARD (drives a float-confused register off float, never conflicts with the is_ptr/is_struct hard constraints so it cannot force UNSAT), but keep it soft for a concrete/constant operand so a single-candidate node is not forced UNSAT.
            if matches!(ct, ClightType::Tpointer(..)) {
                let not_float = t.is_float(&it).not();
                if cast_operand_is_inferable(inner, tyvar) {
                    assert_guarded(opt, guard, &not_float);
                } else {
                    assert_soft_guarded(opt, guard, &not_float, 8);
                }
            }
            // Remaining cast mismatches (pointer->float, struct<->scalar) stay soft nudges, as before.
            assert_soft_guarded(opt, guard, &compatible(t, &it, &tgt), 8);
            tgt
        }
        ClightExpr::Ebinop(op, l, r, ct) => {
            let lt = type_of(t, tyvar, opt, guard, l);
            let rt = type_of(t, tyvar, opt, guard, r);
            // Pointer arithmetic (p + n / p - n) carries the pointer operand's type so a deref of the result constrains the base pointer's POINTEE (else `*(p + n) = scalar` leaves p unconstrained and a wrong struct-pointer prior survives); the pointer operand is itself inferred, so select it with `ite` rather than statically.
            match op {
                ClightBinaryOp::Oadd | ClightBinaryOp::Osub => {
                    // The result is a pointer ONLY if an operand is; a pointer `ct` must not be the fallback (it would let a deref `*(base + off)` be satisfied by the annotation, so the base register escapes the is_ptr requirement, stays scalar/`long`, and the emitter prints a deref of a non-pointer), so force a non-pointer fallback and let pointer-ness derive from `lt`/`rt`.
                    let ann = match ct {
                        ClightType::Tpointer(..) => t.int(),
                        other => clight_to_ty(t, other),
                    };
                    let inner = t.is_ptr(&rt).ite(&rt, &ann);
                    t.is_ptr(&lt).ite(&lt, &inner)
                }
                _ => clight_to_ty(t, ct),
            }
        }
        ClightExpr::Eunop(_, inner, ct) => {
            let _ = type_of(t, tyvar, opt, guard, inner);
            clight_to_ty(t, ct)
        }
        ClightExpr::Econdition(c, a, b, ct) => {
            let _ = type_of(t, tyvar, opt, guard, c);
            let _ = type_of(t, tyvar, opt, guard, a);
            let _ = type_of(t, tyvar, opt, guard, b);
            clight_to_ty(t, ct)
        }
        _ => t.int(),
    }
}

// Walk a statement, emitting the operator-typing constraints; `guard` selects the candidate so the constraints only bind when that candidate form is chosen for the node.
fn constrain_stmt(
    t: &TypeDt,
    tyvar: &HashMap<RTLReg, Dynamic>,
    opt: &Optimize,
    guard: Option<&Bool>,
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    func_ret: &Dynamic,
    compat_w: u64,
    stmt: &crate::x86::types::ClightStmt,
) {
    use crate::x86::types::ClightStmt;
    match stmt {
        ClightStmt::Sassign(lhs, rhs) => {
            let lt = type_of(t, tyvar, opt, guard, lhs);
            let rt = type_of(t, tyvar, opt, guard, rhs);
            assert_soft_guarded(opt, guard, &compatible(t, &lt, &rt), compat_w);
        }
        ClightStmt::Sset(id, e) => {
            let rt = type_of(t, tyvar, opt, guard, e);
            if let Some(lv) = tyvar.get(&(*id as RTLReg)) {
                assert_soft_guarded(opt, guard, &compatible(t, lv, &rt), compat_w);
            }
        }
        ClightStmt::Scall(ret, f, args) => {
            let _ = type_of(t, tyvar, opt, guard, f);
            // Cross-function: bind each argument and the result to the callee's signature.
            let sig = callee_ident_from_expr(f, name_to_ident)
                .and_then(|id| func.callee_signatures.get(&id));
            for (i, a) in args.iter().enumerate() {
                let at = type_of(t, tyvar, opt, guard, a);
                if let Some(sig) = sig {
                    if let Some(pt) = sig.param_types.get(i) {
                        let want = xtype_to_ty(t, pt);
                        assert_soft_guarded(opt, guard, &compatible(t, &at, &want), compat_w);
                    }
                }
            }
            if let (Some(rid), Some(sig)) = (ret, sig) {
                if let Some(lv) = tyvar.get(&(*rid as RTLReg)) {
                    let want = xtype_to_ty(t, &sig.return_type);
                    assert_soft_guarded(opt, guard, &compatible(t, lv, &want), compat_w);
                }
            }
            // return/void agreement (caller side): capturing the result of a void callee yields "void value not ignored as it ought to be", so when this call is a refinable candidate, penalize the result-capturing form so a non-capturing candidate is chosen.
            if let (Some(_), Some(sig)) = (ret, sig) {
                if matches!(sig.return_type, XType::Xvoid) {
                    if let Some(g) = guard {
                        opt.assert_soft(&g.not(), compat_w, None);
                    }
                }
            }
        }
        ClightStmt::Sreturn(ret) => {
            // return/void agreement (callee side): is_void(return_type) <=> the return carries no value; a value-return in a void function or a valueless return in a non-void function is a frontend error, so when the return is a refinable candidate, penalize the mismatching form so the agreeing one is selected.
            let is_void_fn = matches!(func.return_type, ClightType::Tvoid);
            match ret {
                Some(e) => {
                    let et = type_of(t, tyvar, opt, guard, e);
                    assert_soft_guarded(opt, guard, &compatible(t, &et, func_ret), compat_w);
                    if is_void_fn {
                        if let Some(g) = guard {
                            opt.assert_soft(&g.not(), compat_w, None);
                        }
                    }
                }
                None => {
                    if !is_void_fn {
                        if let Some(g) = guard {
                            opt.assert_soft(&g.not(), compat_w, None);
                        }
                    }
                }
            }
        }
        ClightStmt::Sifthenelse(c, a, b) => {
            let _ = type_of(t, tyvar, opt, guard, c);
            constrain_stmt(t, tyvar, opt, guard, func, name_to_ident, func_ret, compat_w, a);
            constrain_stmt(t, tyvar, opt, guard, func, name_to_ident, func_ret, compat_w, b);
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss {
                constrain_stmt(t, tyvar, opt, guard, func, name_to_ident, func_ret, compat_w, s);
            }
        }
        ClightStmt::Sloop(a, b) => {
            constrain_stmt(t, tyvar, opt, guard, func, name_to_ident, func_ret, compat_w, a);
            constrain_stmt(t, tyvar, opt, guard, func, name_to_ident, func_ret, compat_w, b);
        }
        ClightStmt::Slabel(_, inner) => {
            constrain_stmt(t, tyvar, opt, guard, func, name_to_ident, func_ret, compat_w, inner);
        }
        ClightStmt::Sswitch(e, cases) => {
            let _ = type_of(t, tyvar, opt, guard, e);
            for (_, s) in cases {
                constrain_stmt(t, tyvar, opt, guard, func, name_to_ident, func_ret, compat_w, s);
            }
        }
        _ => {}
    }
}

// Integer-only operators (`* / % << >> & | ^` and bitwise `~`) require integer operands (a pointer/float operand is a hard "invalid operands to binary expression" error); drive each inferable operand register toward int, soft with dominant weight rather than hard so a register also forced to a pointer by a deref elsewhere keeps that type and only this site stays mis-typed instead of forcing whole-function UNSAT.
fn constrain_int_ops(
    t: &TypeDt,
    tyvar: &HashMap<RTLReg, Dynamic>,
    opt: &Optimize,
    guard: Option<&Bool>,
    w: u64,
    stmt: &ClightStmt,
) {
    let mut int_regs: std::collections::BTreeSet<RTLReg> = std::collections::BTreeSet::new();
    scan_pure_int_regs_stmt(stmt, &mut int_regs);
    for reg in int_regs {
        if let Some(tv) = tyvar.get(&reg) {
            assert_soft_guarded(opt, guard, &t.is_int(tv), w);
        }
    }
}

// Render a model's inferred Ty value for `reg` to a candidate type-string.
fn render_type(t: &TypeDt, model: &z3::Model, tv: &Dynamic, reg: RTLReg, func: &FunctionData) -> String {
    let truth = |b: Bool| model.eval(&b, true).and_then(|x| x.as_bool()).unwrap_or(false);
    if truth(t.is_ptr(tv)) {
        let p = t.pointee(tv);
        if truth(t.is_struct(&p)) {
            if let Some(&sid) = func.reg_struct_ids.get(&reg) {
                return format!("ptr_struct_{:x}", sid);
            }
            // sid from the model if upstream didn't record one.
            if let Some(sid) = model
                .eval(&t.dt.variants[V_STRUCT].accessors[0].apply(&[&p]), true)
                .and_then(|x| x.as_int())
                .and_then(|i| i.as_i64())
            {
                return format!("ptr_struct_{:x}", sid);
            }
            return "ptr_I64".to_string();
        }
        if truth(t.is_float(&p)) {
            return "ptr_double".to_string();
        }
        return "ptr_I64".to_string();
    }
    if truth(t.is_float(tv)) {
        return "float_F64".to_string();
    }
    "int_I64".to_string()
}

// Pick the candidate index whose string best matches the rendered inferred type; None if no candidate is even in the same class (a genuinely-new inferred type that must be carried as an override).
fn anchor_index(cands: &[String], rendered: &str) -> Option<usize> {
    // Exact match wins, except `ptr_void` (emits `void*`, an incomplete pointee that can't be deref-assigned); for it, fall through to prefer a complete scalar pointer below.
    if rendered != "ptr_void" {
        if let Some(i) = cands.iter().position(|c| c == rendered) {
            return Some(i);
        }
    }
    // Classes: struct-pointer is distinct from scalar/generic pointer, so a scalar-pointer inference never anchors back onto a `ptr_struct` candidate (which would reintroduce the struct mismatch).
    let class = |s: &str| -> u8 {
        if s.starts_with("ptr_struct_") { 0 }
        else if s.starts_with("ptr_") { 1 }
        else if s.starts_with("float_") { 2 }
        else { 3 }
    };
    let rc = class(rendered);
    if rc == 1 {
        // A scalar/generic pointer: prefer a COMPLETE pointee (int*/long*/char*) over void* (incomplete, not assignable through); only fall back to ptr_void if nothing complete is available.
        for pref in ["ptr_I64", "ptr_int", "ptr_char"] {
            if let Some(i) = cands.iter().position(|c| c == pref) {
                return Some(i);
            }
        }
        if let Some(i) = cands.iter().position(|c| class(c) == 1 && c != "ptr_void") {
            return Some(i);
        }
    }
    cands.iter().position(|c| class(c) == rc)
}

fn solve_function(
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
) -> (HashMap<Node, Option<usize>>, HashMap<RTLReg, usize>, HashMap<RTLReg, String>) {
    // Each function solves in its OWN fresh, isolated Z3 context: the crate's `Optimize::new()` reuses a per-thread context across functions, so accumulated state (and thus MaxSMT tie-breaking) depends on rayon's non-deterministic work-stealing order and makes the emitted C non-reproducible; a fresh context per solve removes that coupling while keeping par_iter parallelism deterministic.
    let mut cfg = z3::Config::new();
    cfg.set_param_value("random_seed", "0");
    z3::with_z3_config(&cfg, || {
    let t = TypeDt::build();
    let opt = Optimize::new();
    let mut params = z3::Params::new();
    // Bound the solve by a DETERMINISTIC resource budget (`rlimit`), not a wall-clock `timeout` (which fires at load-/thread-dependent points and makes the per-function fallback and emitted C vary run to run); the wall-clock `timeout` is kept only as a generous hang backstop that `rlimit` should always trip before.
    params.set_u32("rlimit", 20_000_000);
    params.set_u32("timeout", 120_000);
    params.set_u32("random_seed", 0);
    opt.set_params(&params);

    // Free type variable per inferable register (deterministic order).
    let mut regs: Vec<RTLReg> = func.var_type_candidates.keys().copied().collect();
    regs.sort();
    let mut tyvar: HashMap<RTLReg, Dynamic> = HashMap::new();
    for &reg in &regs {
        tyvar.insert(reg, t.fresh());
    }

    // Diagnostic: dump the candidates the lifting pass produced for a target function (by name substring), to distinguish "correct candidate absent (lifting bug)" from "present but not selected (selector bug)".
    if std::env::var("MANIFOLD_DUMP_CANDS").map(|s| !s.is_empty() && func.name.contains(&s)).unwrap_or(false) {
        eprintln!("=== CANDS fn={} addr={:#x} ===", func.name, func.address);
        for &reg in &regs {
            let nm = crate::decompile::passes::c_pass::helpers::param_name_for_reg(reg);
            eprintln!("  {} (reg {:#x}): {:?}", nm, reg, func.var_type_candidates[&reg]);
        }
        let mut ns: Vec<Node> = func.node_statements.keys().copied().collect();
        ns.sort();
        for n in &ns {
            let stmts = &func.node_statements[n];
            let dbg = format!("{:?}", stmts);
            if stmts.len() > 1 || dbg.contains("Ederef") {
                eprintln!("  node {:#x} ({} cand stmts):", n, stmts.len());
                for (i, s) in stmts.iter().enumerate() {
                    eprintln!("    [{}] {:?}", i, s);
                }
            }
        }
    }

    // Statement-selection booleans for multi-candidate nodes (exactly one per node).
    let mut nodes: Vec<Node> = func.node_statements.keys().copied().collect();
    nodes.sort();
    let mut selvar: HashMap<Node, Vec<Bool>> = HashMap::new();
    for &node in &nodes {
        let m = func.node_statements[&node].len();
        if m > 1 {
            let vars: Vec<Bool> = (0..m).map(|_| Bool::fresh_const("s")).collect();
            let refs: Vec<(&Bool, i32)> = vars.iter().map(|b| (b, 1)).collect();
            opt.assert(&Bool::pb_eq(&refs, 1));
            selvar.insert(node, vars);
        }
    }

    let func_ret = match &func.return_type {
        ClightType::Tvoid => t.void(),
        other => clight_to_ty(&t, other),
    };

    let compat_w: u64 = (regs.len() + selvar.len()) as u64 + 1;

    // Emit constraints for every candidate statement, guarded by its selection boolean when refinable.
    for &node in &nodes {
        let cands = &func.node_statements[&node];
        match selvar.get(&node) {
            Some(vars) => {
                for (ci, stmt) in cands.iter().enumerate() {
                    constrain_stmt(&t, &tyvar, &opt, Some(&vars[ci]), func, name_to_ident, &func_ret, compat_w, stmt);
                    constrain_int_ops(&t, &tyvar, &opt, Some(&vars[ci]), compat_w, stmt);
                }
            }
            None => {
                constrain_stmt(&t, &tyvar, &opt, None, func, name_to_ident, &func_ret, compat_w, &cands[0]);
                constrain_int_ops(&t, &tyvar, &opt, None, compat_w, &cands[0]);
            }
        }
    }

    // Soft provenance: prefer each register's priority-0 candidate type, and the priority-0 statement.
    for &reg in &regs {
        if let Some(c0) = func.var_type_candidates[&reg].first() {
            let prior = cand_str_to_ty(&t, c0);
            opt.assert_soft(&tyvar[&reg]._eq(prior), 1u64, None);
        }
    }
    let mut sel_nodes: Vec<Node> = selvar.keys().copied().collect();
    sel_nodes.sort();
    for node in &sel_nodes {
        opt.assert_soft(&selvar[node][0], 1u64, None);
    }

    let mut cand_out: HashMap<Node, Option<usize>> = HashMap::new();
    let mut ty_out: HashMap<RTLReg, usize> = HashMap::new();
    let mut ty_override: HashMap<RTLReg, String> = HashMap::new();

    let model = match opt.check(&[]) {
        SatResult::Sat => opt.get_model(),
        _ => None,
    };

    match model {
        Some(m) => {
            for &node in &nodes {
                match selvar.get(&node) {
                    Some(vars) => {
                        let mut chosen = 0usize;
                        for (i, b) in vars.iter().enumerate() {
                            if m.eval(b, true).and_then(|x| x.as_bool()).unwrap_or(false) {
                                chosen = i;
                                break;
                            }
                        }
                        cand_out.insert(node, Some(chosen));
                    }
                    None => {
                        cand_out.insert(node, Some(0));
                    }
                }
            }
            for &reg in &regs {
                let rendered = render_type(&t, &m, &tyvar[&reg], reg, func);
                let cands = &func.var_type_candidates[&reg];
                match anchor_index(cands, &rendered) {
                    Some(idx) => {
                        ty_out.insert(reg, idx);
                    }
                    None => {
                        // Genuinely-new inferred type: carry it out-of-band so the emitter still sees it.
                        ty_out.insert(reg, 0);
                        ty_override.insert(reg, rendered);
                    }
                }
            }
        }
        None => {
            for &node in &nodes {
                cand_out.insert(node, Some(0));
            }
        }
    }

    (cand_out, ty_out, ty_override)
    })
}

// #3 helpers: program-wide struct field-type inference (a field that stored a pointer must not stay scalar/float, which forces an illegal `(double)ptr` store); field types are shared across functions, so this scans candidate statements globally rather than in the per-function parallel solve.

// (struct_name, field_name) key of a field-access lvalue `base->f`, matching query.rs candidate keys.
fn field_key_of_lvalue(e: &ClightExpr) -> Option<(String, String)> {
    if let ClightExpr::Efield(base, fid, _) = e {
        if let ClightExpr::Ederef(_, ClightType::Tstruct(sid, _)) = base.as_ref() {
            let struct_name = format!("struct_{:x}", sid);
            let field_name = crate::decompile::passes::csh_pass::field_ident_to_name(*fid);
            return Some((struct_name, field_name));
        }
    }
    None
}

// True if a stored value is a pointer (address-of, a global/function symbol, or a pointer-annotated value).
fn clight_value_is_ptr(e: &ClightExpr) -> bool {
    match e {
        ClightExpr::Eaddrof(..) | ClightExpr::EvarSymbol(..) => true,
        ClightExpr::Ecast(_, ct) | ClightExpr::Etempvar(_, ct) | ClightExpr::Evar(_, ct) => {
            matches!(ct, ClightType::Tpointer(..))
        }
        _ => false,
    }
}

// Record (struct,field) keys that receive a pointer-valued store anywhere in `stmt`.
fn scan_field_ptr_stores(stmt: &ClightStmt, out: &mut std::collections::HashSet<(String, String)>) {
    match stmt {
        ClightStmt::Sassign(lhs, rhs) => {
            if clight_value_is_ptr(rhs) {
                if let Some(key) = field_key_of_lvalue(lhs) {
                    out.insert(key);
                }
            }
        }
        ClightStmt::Sifthenelse(_, a, b) | ClightStmt::Sloop(a, b) => {
            scan_field_ptr_stores(a, out);
            scan_field_ptr_stores(b, out);
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss {
                scan_field_ptr_stores(s, out);
            }
        }
        ClightStmt::Slabel(_, inner) => scan_field_ptr_stores(inner, out),
        ClightStmt::Sswitch(_, cases) => {
            for (_, s) in cases {
                scan_field_ptr_stores(s, out);
            }
        }
        _ => {}
    }
}

// Whole-program selection via generic inference; merges per-function results into a ProgramSelectionState.
pub(crate) fn infer_select_program(
    functions: &[FunctionData],
    name_to_ident: &HashMap<String, Ident>,
) -> ProgramSelectionState {
    let per_func: Vec<(Address, HashMap<Node, Option<usize>>, HashMap<RTLReg, usize>, HashMap<RTLReg, String>)> =
        functions
            .par_iter()
            .map(|f| {
                let (c, t, o) = solve_function(f, name_to_ident);
                (f.address, c, t, o)
            })
            .collect();

    let mut candidate_idx = HashMap::new();
    let mut var_decl_idx = HashMap::new();
    let mut var_type_override = HashMap::new();
    for (addr, cmap, tmap, omap) in per_func {
        for (node, idx) in cmap {
            candidate_idx.insert((addr, node), idx);
        }
        for (reg, idx) in tmap {
            var_decl_idx.insert((addr, reg), idx);
        }
        for (reg, s) in omap {
            var_type_override.insert((addr, reg), s);
        }
    }

    // #3: program-wide struct field-type inference. Start from upstream defaults, then for any field receiving a pointer-valued store re-select a pointer candidate (a C-decl string containing '*', preferring a struct pointer) when one exists, so the field is no longer a scalar/float that forces an illegal `(double)ptr` store.
    let mut field_cands: HashMap<(String, String), Vec<String>> = HashMap::new();
    for func in functions {
        for (key, cands) in &func.struct_field_type_candidates {
            field_cands.entry(key.clone()).or_insert_with(|| cands.clone());
        }
    }
    let mut field_ptr_stored: std::collections::HashSet<(String, String)> = std::collections::HashSet::new();
    for func in functions {
        for cands in func.node_statements.values() {
            for stmt in cands {
                scan_field_ptr_stores(stmt, &mut field_ptr_stored);
            }
        }
    }
    let mut struct_field_type_idx = HashMap::new();
    for func in functions {
        for (key, idx) in &func.struct_field_type_idx {
            struct_field_type_idx.entry(key.clone()).or_insert(*idx);
        }
    }
    for key in &field_ptr_stored {
        if let Some(cands) = field_cands.get(key) {
            let pick = cands
                .iter()
                .position(|c| c.contains('*') && c.contains("struct"))
                .or_else(|| cands.iter().position(|c| c.contains('*')));
            if let Some(i) = pick {
                struct_field_type_idx.insert(key.clone(), i);
            }
        }
    }

    ProgramSelectionState {
        candidate_idx,
        var_decl_idx,
        struct_field_type_idx,
        var_type_override,
    }
}
