use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
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

    fn is_void(&self, x: &Dynamic) -> Bool { self.dt.variants[V_VOID].tester.apply(&[x]).as_bool().unwrap() }
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

// TR-1: structural requirements are HARD in primary, deferred as dominating-soft in the UNSAT relaxed retry so max-consistency wins over collapsing to candidate[0]; total soft weight is tracked so the dominating weight is exact.
struct ConstraintSink<'a> {
    opt: &'a Optimize,
    relax: bool,
    deferred_structural: RefCell<Vec<Bool>>,
    soft_total: Cell<u64>,
}

impl<'a> ConstraintSink<'a> {
    fn new(opt: &'a Optimize, relax: bool) -> Self {
        ConstraintSink {
            opt,
            relax,
            deferred_structural: RefCell::new(Vec::new()),
            soft_total: Cell::new(0),
        }
    }

    // A structural requirement: hard in the primary attempt, deferred dominating-soft in the relaxed retry.
    fn assert_structural(&self, guard: Option<&Bool>, cond: &Bool) {
        let c = match guard {
            Some(g) => g.implies(cond.clone()),
            None => cond.clone(),
        };
        if self.relax {
            self.deferred_structural.borrow_mut().push(c);
        } else {
            self.opt.assert(&c);
        }
    }

    fn assert_soft(&self, guard: Option<&Bool>, cond: &Bool, w: u64) {
        self.soft_total.set(self.soft_total.get().saturating_add(w));
        match guard {
            Some(g) => self.opt.assert_soft(&g.implies(cond.clone()), w, None),
            None => self.opt.assert_soft(cond, w, None),
        }
    }

    // Soft assertion on a raw Bool (the candidate-penalty `!guard` forms and the priors).
    fn assert_soft_raw(&self, cond: &Bool, w: u64) {
        self.soft_total.set(self.soft_total.get().saturating_add(w));
        self.opt.assert_soft(cond, w, None);
    }

    // Relaxed retry: materialize deferred structural requirements at a dominating weight so fewest-violations is the primary objective, soft preferences are tie-breaks.
    fn flush_structural(&self) {
        let w = self.soft_total.get().saturating_add(1);
        for c in self.deferred_structural.borrow().iter() {
            self.opt.assert_soft(c, w, None);
        }
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
    sink: &ConstraintSink,
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
            let it = type_of(t, tyvar, sink, guard, inner);
            // deref requires a pointer and the result is the pointee; assert only when the base drives a free variable (on a concrete base it is redundant or forces whole-function UNSAT).
            if base_drives_free_var(inner, tyvar) {
                sink.assert_structural(guard, &t.is_ptr(&it));
            }
            t.pointee(&it)
        }
        ClightExpr::Eaddrof(inner, _) => {
            let it = type_of(t, tyvar, sink, guard, inner);
            t.ptr(&it)
        }
        ClightExpr::Efield(base, _, ct) => {
            let bt = type_of(t, tyvar, sink, guard, base);
            // the field base (for `e.f`, or the pointee for `e->f` = (*p).f) must be a struct; assert only when it drives a free variable, for the same reason as deref above.
            if base_drives_free_var(base, tyvar) {
                sink.assert_structural(guard, &t.is_struct(&bt));
            }
            clight_to_ty(t, ct)
        }
        ClightExpr::Ecast(inner, ct) => {
            let it = type_of(t, tyvar, sink, guard, inner);
            let tgt = clight_to_ty(t, ct);
            // Casting a floating operand to a pointer is illegal C everywhere; for an inferable register enforce "operand is not float" HARD (drives a float-confused register off float, never conflicts with the is_ptr/is_struct hard constraints so it cannot force UNSAT), but keep it soft for a concrete/constant operand so a single-candidate node is not forced UNSAT.
            if matches!(ct, ClightType::Tpointer(..)) {
                let not_float = t.is_float(&it).not();
                if cast_operand_is_inferable(inner, tyvar) {
                    sink.assert_structural(guard, &not_float);
                } else {
                    sink.assert_soft(guard, &not_float, 8);
                }
            }
            // Remaining cast mismatches (pointer->float, struct<->scalar) stay soft nudges, as before.
            sink.assert_soft(guard, &compatible(t, &it, &tgt), 8);
            tgt
        }
        ClightExpr::Ebinop(op, l, r, ct) => {
            let lt = type_of(t, tyvar, sink, guard, l);
            let rt = type_of(t, tyvar, sink, guard, r);
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
            let _ = type_of(t, tyvar, sink, guard, inner);
            clight_to_ty(t, ct)
        }
        ClightExpr::Econdition(c, a, b, ct) => {
            let _ = type_of(t, tyvar, sink, guard, c);
            let _ = type_of(t, tyvar, sink, guard, a);
            let _ = type_of(t, tyvar, sink, guard, b);
            clight_to_ty(t, ct)
        }
        _ => t.int(),
    }
}

// Walk a statement, emitting the operator-typing constraints; `guard` selects the candidate so the constraints only bind when that candidate form is chosen for the node.
fn constrain_stmt(
    t: &TypeDt,
    tyvar: &HashMap<RTLReg, Dynamic>,
    sink: &ConstraintSink,
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
            let lt = type_of(t, tyvar, sink, guard, lhs);
            let rt = type_of(t, tyvar, sink, guard, rhs);
            sink.assert_soft(guard, &compatible(t, &lt, &rt), compat_w);
        }
        ClightStmt::Sset(id, e) => {
            let rt = type_of(t, tyvar, sink, guard, e);
            if let Some(lv) = tyvar.get(&(*id as RTLReg)) {
                sink.assert_soft(guard, &compatible(t, lv, &rt), compat_w);
            }
        }
        ClightStmt::Scall(ret, f, args) => {
            let _ = type_of(t, tyvar, sink, guard, f);
            // Cross-function: bind each argument and the result to the callee's signature.
            let sig = callee_ident_from_expr(f, name_to_ident)
                .and_then(|id| func.callee_signatures.get(&id));
            for (i, a) in args.iter().enumerate() {
                let at = type_of(t, tyvar, sink, guard, a);
                if let Some(sig) = sig {
                    if let Some(pt) = sig.param_types.get(i) {
                        let want = xtype_to_ty(t, pt);
                        sink.assert_soft(guard, &compatible(t, &at, &want), compat_w);
                    }
                }
            }
            if let (Some(rid), Some(sig)) = (ret, sig) {
                if let Some(lv) = tyvar.get(&(*rid as RTLReg)) {
                    let want = xtype_to_ty(t, &sig.return_type);
                    sink.assert_soft(guard, &compatible(t, lv, &want), compat_w);
                }
            }
            // return/void agreement (caller side): capturing the result of a void callee yields "void value not ignored as it ought to be", so when this call is a refinable candidate, penalize the result-capturing form so a non-capturing candidate is chosen.
            if let (Some(_), Some(sig)) = (ret, sig) {
                if matches!(sig.return_type, XType::Xvoid) {
                    if let Some(g) = guard {
                        sink.assert_soft_raw(&g.not(), compat_w);
                    }
                }
            }
        }
        ClightStmt::Sreturn(ret) => {
            // return/void agreement (callee side): is_void(return_type) <=> the return carries no value; a value-return in a void function or a valueless return in a non-void function is a frontend error, so when the return is a refinable candidate, penalize the mismatching form so the agreeing one is selected.
            let is_void_fn = matches!(func.return_type, ClightType::Tvoid);
            match ret {
                Some(e) => {
                    let et = type_of(t, tyvar, sink, guard, e);
                    sink.assert_soft(guard, &compatible(t, &et, func_ret), compat_w);
                    if is_void_fn {
                        if let Some(g) = guard {
                            sink.assert_soft_raw(&g.not(), compat_w);
                        }
                    }
                }
                None => {
                    if !is_void_fn {
                        if let Some(g) = guard {
                            sink.assert_soft_raw(&g.not(), compat_w);
                        }
                    }
                }
            }
        }
        ClightStmt::Sifthenelse(c, a, b) => {
            let _ = type_of(t, tyvar, sink, guard, c);
            constrain_stmt(t, tyvar, sink, guard, func, name_to_ident, func_ret, compat_w, a);
            constrain_stmt(t, tyvar, sink, guard, func, name_to_ident, func_ret, compat_w, b);
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss {
                constrain_stmt(t, tyvar, sink, guard, func, name_to_ident, func_ret, compat_w, s);
            }
        }
        ClightStmt::Sloop(a, b) => {
            constrain_stmt(t, tyvar, sink, guard, func, name_to_ident, func_ret, compat_w, a);
            constrain_stmt(t, tyvar, sink, guard, func, name_to_ident, func_ret, compat_w, b);
        }
        ClightStmt::Slabel(_, inner) => {
            constrain_stmt(t, tyvar, sink, guard, func, name_to_ident, func_ret, compat_w, inner);
        }
        ClightStmt::Sswitch(e, cases) => {
            let _ = type_of(t, tyvar, sink, guard, e);
            for (_, s) in cases {
                constrain_stmt(t, tyvar, sink, guard, func, name_to_ident, func_ret, compat_w, s);
            }
        }
        _ => {}
    }
}

// Integer-only operators (`* / % << >> & | ^` and bitwise `~`) require integer operands (a pointer/float operand is a hard "invalid operands to binary expression" error); drive each inferable operand register toward int, soft with dominant weight rather than hard so a register also forced to a pointer by a deref elsewhere keeps that type and only this site stays mis-typed instead of forcing whole-function UNSAT.
fn constrain_int_ops(
    t: &TypeDt,
    tyvar: &HashMap<RTLReg, Dynamic>,
    sink: &ConstraintSink,
    guard: Option<&Bool>,
    w: u64,
    stmt: &ClightStmt,
) {
    let mut int_regs: BTreeSet<RTLReg> = BTreeSet::new();
    scan_pure_int_regs_stmt(stmt, &mut int_regs);
    for reg in int_regs {
        if let Some(tv) = tyvar.get(&reg) {
            sink.assert_soft(guard, &t.is_int(tv), w);
        }
    }
}

// Render a model's inferred Ty for `reg` to a type-string; `allow_void` (TR-6) permits `ptr_void` only when the register is never used as a deref/field base, so an incomplete pointee can't break a deref-assign.
fn render_type(
    t: &TypeDt,
    model: &z3::Model,
    tv: &Dynamic,
    reg: RTLReg,
    func: &FunctionData,
    allow_void: bool,
) -> String {
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
        if allow_void && truth(t.is_void(&p)) {
            return "ptr_void".to_string();
        }
        return "ptr_I64".to_string();
    }
    if truth(t.is_float(tv)) {
        return "float_F64".to_string();
    }
    "int_I64".to_string()
}

// Bit width of a candidate type-string, for nearest-width anchoring within a class.
fn type_str_width(s: &str) -> u32 {
    if s.starts_with("ptr_") { return 64; }
    if s == "float_F32" { return 32; }
    if s == "float_F64" { return 64; }
    if s == "int_IBool" { return 8; }
    if s.starts_with("int_I8") { return 8; }
    if s.starts_with("int_I16") { return 16; }
    if s.starts_with("int_I32") || s == "int_U32" { return 32; }
    if s.starts_with("int_I64") || s == "int_U64" { return 64; }
    64
}

// Pick the candidate index best matching the rendered inferred type; None means genuinely-new type (carry as override). `allow_void` mirrors render_type's license: ptr_void anchoring requires the register is never deref/field-based.
fn anchor_index(cands: &[String], rendered: &str, allow_void: bool) -> Option<usize> {
    // ptr_void without the license emits an incomplete pointee that can't be deref-assigned; fall through to prefer a complete scalar pointer.
    if rendered != "ptr_void" || allow_void {
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
        // ptr_void is still a pointer-class anchor when nothing with a complete pointee is available.
        return cands.iter().position(|c| c == "ptr_void");
    }
    // Same class, no exact width: take nearest-width candidate; ties break to the earlier (higher-priority) index.
    let rw = type_str_width(rendered);
    cands
        .iter()
        .enumerate()
        .filter(|(_, c)| class(c) == rc)
        .min_by_key(|(i, c)| (type_str_width(c).abs_diff(rw), *i))
        .map(|(i, _)| i)
}

// TR-1: graded solve -- primary (hard structural), then on failure: (1) unknown-with-model: budget died mid-MaxSMT but a hard-satisfying best-so-far model exists, reuse it; (2) UNSAT: relaxed re-solve with structural as dominating-soft (max-consistency); (3) no model: deterministic greedy anchored fallback, linear in program size.
fn solve_function(
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
) -> (HashMap<Node, Option<usize>>, HashMap<RTLReg, usize>, HashMap<RTLReg, String>) {
    match solve_function_z3(func, name_to_ident, false) {
        Ok((c, ty, ov, grade)) => {
            if matches!(grade, SatResult::Unknown) {
                TYPE_SOLVE_PARTIAL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                eprintln!(
                    "[clight-select] WARN: type solve for {} ({:#x}) exhausted its rlimit budget mid-optimization; reusing the best model found ({} nodes, {} regs)",
                    func.name,
                    func.address,
                    func.node_statements.len(),
                    func.var_type_candidates.len()
                );
            }
            (c, ty, ov)
        }
        Err(first) => {
            // The primary solve produced no usable model. Surface it (TR-1 diagnostic) and degrade.
            TYPE_SOLVE_FALLBACKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            if matches!(first, SatResult::Unsat) {
                // UNSAT proof fit the budget, so a relaxed re-solve (fresh context, fresh budget) is affordable and cannot UNSAT.
                if let Ok((c, ty, ov, _)) = solve_function_z3(func, name_to_ident, true) {
                    TYPE_SOLVE_RELAXED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    eprintln!(
                        "[clight-select] WARN: type solve was UNSAT for {} ({:#x}); recovered via relaxed re-solve (structural constraints soft, max-consistency model) ({} nodes, {} regs)",
                        func.name,
                        func.address,
                        func.node_statements.len(),
                        func.var_type_candidates.len()
                    );
                    return (c, ty, ov);
                }
            }
            // No model (budget died before first SAT subcall, or relaxed retry failed): fall back to deterministic greedy anchored selection.
            eprintln!(
                "[clight-select] WARN: type solve fell back for {} ({:#x}): {}; using greedy anchored per-node selection ({} nodes, {} regs)",
                func.name,
                func.address,
                match first {
                    SatResult::Unsat => "UNSAT",
                    SatResult::Unknown => "unknown (rlimit/timeout)",
                    SatResult::Sat => "sat but no model",
                },
                func.node_statements.len(),
                func.var_type_candidates.len()
            );
            greedy_anchored_fallback(func, name_to_ident)
        }
    }
}

// One Z3 attempt; `relax=true` is the TR-1 retry with structural as dominating-soft. Returns the selection + the SatResult that yielded the model, or the failing SatResult when no model is available.
#[allow(clippy::type_complexity)]
fn solve_function_z3(
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    relax: bool,
) -> Result<
    (HashMap<Node, Option<usize>>, HashMap<RTLReg, usize>, HashMap<RTLReg, String>, SatResult),
    SatResult,
> {
    // Fresh Z3 context per function: reusing a per-thread context leaks accumulated MaxSMT state across functions, making tie-breaking depend on rayon scheduling order and the emitted C non-reproducible. NOTE: do not set "random_seed" on Config -- z3 rejects it as a no-op and emits async per-context warnings to stderr.
    let cfg = z3::Config::new();
    z3::with_z3_config(&cfg, || {
    let t = TypeDt::build();
    let opt = Optimize::new();
    let sink = ConstraintSink::new(&opt, relax);
    let mut params = z3::Params::new();
    // Use deterministic `rlimit` budget, not wall-clock `timeout`; the timeout is a hang backstop only. CAVEAT: z3 4.8.x (system libz3 4.8.12) ignores rlimit through Optimize params -- verified empirically, z3 4.13 honors it -- so on such libs every unknown is wall-clock-driven; the model-reuse path guards itself via get_reason_unknown to preserve determinism.
    params.set_u32("rlimit", crate::decompile::elevator::config::SOLVE_RLIMIT);
    params.set_u32("timeout", crate::decompile::elevator::config::SOLVE_TIMEOUT_MS);
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
                    constrain_stmt(&t, &tyvar, &sink, Some(&vars[ci]), func, name_to_ident, &func_ret, compat_w, stmt);
                    constrain_int_ops(&t, &tyvar, &sink, Some(&vars[ci]), compat_w, stmt);
                }
            }
            None => {
                constrain_stmt(&t, &tyvar, &sink, None, func, name_to_ident, &func_ret, compat_w, &cands[0]);
                constrain_int_ops(&t, &tyvar, &sink, None, compat_w, &cands[0]);
            }
        }
    }

    // Soft provenance: prefer each register's priority-0 candidate type, and the priority-0 statement.
    for &reg in &regs {
        if let Some(c0) = func.var_type_candidates[&reg].first() {
            let prior = cand_str_to_ty(&t, c0);
            sink.assert_soft_raw(&tyvar[&reg]._eq(prior), 1u64);
        }
    }
    let mut sel_nodes: Vec<Node> = selvar.keys().copied().collect();
    sel_nodes.sort();
    for node in &sel_nodes {
        sink.assert_soft_raw(&selvar[node][0], 1u64);
    }

    // Relaxed retry: materialize structural requirements at dominating weight (no-op in primary attempt).
    sink.flush_structural();

    let mut cand_out: HashMap<Node, Option<usize>> = HashMap::new();
    let mut ty_out: HashMap<RTLReg, usize> = HashMap::new();
    let mut ty_override: HashMap<RTLReg, String> = HashMap::new();

    let check_result = opt.check(&[]);
    let model = match check_result {
        SatResult::Sat => opt.get_model(),
        // Partial-solve reuse (TR-1): on `unknown`, reuse the best-so-far model only when the budget exhausted was the deterministic `rlimit`; a wall-clock unknown would make the model timing-dependent. NOTE: z3 <= 4.8 does not propagate rlimit through Optimize (stays cold by construction on those libs).
        SatResult::Unknown => {
            let resource_budget = opt
                .get_reason_unknown()
                .map(|r| r.contains("resource"))
                .unwrap_or(false);
            if resource_budget { opt.get_model() } else { None }
        }
        SatResult::Unsat => None,
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
            // TR-6: void* license -- denied for any register used as deref/field base (casts included) in any selected statement, so an incomplete pointee can never break an emitted deref.
            let mut ptr_ev: BTreeMap<RTLReg, RegPtrEvidence> = BTreeMap::new();
            for &node in &nodes {
                if let Some(Some(ci)) = cand_out.get(&node) {
                    if let Some(stmt) = func.node_statements[&node].get(*ci) {
                        collect_reg_ptr_evidence_stmt(stmt, &mut ptr_ev);
                    }
                }
            }
            for &reg in &regs {
                let allow_void = ptr_ev.get(&reg).map(|e| !e.any_deref).unwrap_or(true);
                let rendered = render_type(&t, &m, &tyvar[&reg], reg, func, allow_void);
                let cands = &func.var_type_candidates[&reg];
                match anchor_index(cands, &rendered, allow_void) {
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
            Ok((cand_out, ty_out, ty_override, check_result))
        }
        None => Err(check_result),
    }
    })
}

// TR-1 run-wide counters: FALLBACKS = no model, RELAXED = recovered via relaxed re-solve, PARTIAL = over-budget model reused.
static TYPE_SOLVE_FALLBACKS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static TYPE_SOLVE_RELAXED: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static TYPE_SOLVE_PARTIAL: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

// ---- per-register structural pointer-use evidence (TR-1 greedy fallback + TR-6 void license) ----

#[derive(Default, Clone, Copy)]
struct RegPtrEvidence {
    // Bare deref base (`*r`, `*(r+n)`) -- shape the solver hard-asserts is_ptr on.
    bare_deref: bool,
    // Bare field base (`r->f`) -- shape the solver hard-asserts is_struct(pointee) on.
    bare_field: bool,
    // Deref/field involvement in any form including casts -- denies TR-6 void* license even when solver does not hard-assert (memory is still read through the register).
    any_deref: bool,
    // Cast to a pointer type (casts peeled) -- shape the solver hard-asserts not-is_float on for an inferable register.
    cast_to_ptr: bool,
    // Returned (casts peeled) -- return-compat soft is compat_w-weighted, dominating the weight-1 prior and flipping a class-conflicting register like a hard constraint.
    returned: bool,
}

// Root inferable register of a bare deref/field chain (mirrors base_drives_free_var: tempvar, deref, add/sub) WITHOUT peeling casts.
fn bare_chain_root(e: &ClightExpr) -> Option<RTLReg> {
    match e {
        ClightExpr::Etempvar(id, _) => Some(*id as RTLReg),
        ClightExpr::Ederef(inner, _) => bare_chain_root(inner),
        ClightExpr::Ebinop(ClightBinaryOp::Oadd | ClightBinaryOp::Osub, l, r, _) => {
            bare_chain_root(l).or_else(|| bare_chain_root(r))
        }
        _ => None,
    }
}

// Like bare_chain_root but also peels casts -- conservative root set for denying the void-pointee license.
fn loose_chain_root(e: &ClightExpr) -> Option<RTLReg> {
    match e {
        ClightExpr::Etempvar(id, _) => Some(*id as RTLReg),
        ClightExpr::Ederef(inner, _) | ClightExpr::Ecast(inner, _) => loose_chain_root(inner),
        ClightExpr::Ebinop(ClightBinaryOp::Oadd | ClightBinaryOp::Osub, l, r, _) => {
            loose_chain_root(l).or_else(|| loose_chain_root(r))
        }
        _ => None,
    }
}

fn collect_reg_ptr_evidence_expr(e: &ClightExpr, out: &mut BTreeMap<RTLReg, RegPtrEvidence>) {
    match e {
        ClightExpr::Ederef(inner, _) => {
            if let Some(r) = bare_chain_root(inner) {
                out.entry(r).or_default().bare_deref = true;
            }
            if let Some(r) = loose_chain_root(inner) {
                out.entry(r).or_default().any_deref = true;
            }
            collect_reg_ptr_evidence_expr(inner, out);
        }
        ClightExpr::Efield(base, _, _) => {
            if let Some(r) = bare_chain_root(base) {
                out.entry(r).or_default().bare_field = true;
            }
            if let Some(r) = loose_chain_root(base) {
                out.entry(r).or_default().any_deref = true;
            }
            collect_reg_ptr_evidence_expr(base, out);
        }
        ClightExpr::Ecast(inner, ct) => {
            // cast-to-pointer whose operand peels to a register is the solver's hard not-float site.
            if matches!(ct, ClightType::Tpointer(..)) {
                let mut peeled = inner.as_ref();
                while let ClightExpr::Ecast(i2, _) = peeled {
                    peeled = i2;
                }
                if let ClightExpr::Etempvar(id, _) = peeled {
                    out.entry(*id as RTLReg).or_default().cast_to_ptr = true;
                }
            }
            collect_reg_ptr_evidence_expr(inner, out);
        }
        ClightExpr::Eaddrof(inner, _) | ClightExpr::Eunop(_, inner, _) => {
            collect_reg_ptr_evidence_expr(inner, out);
        }
        ClightExpr::Ebinop(_, l, r, _) => {
            collect_reg_ptr_evidence_expr(l, out);
            collect_reg_ptr_evidence_expr(r, out);
        }
        ClightExpr::Econdition(c, a, b, _) => {
            collect_reg_ptr_evidence_expr(c, out);
            collect_reg_ptr_evidence_expr(a, out);
            collect_reg_ptr_evidence_expr(b, out);
        }
        _ => {}
    }
}

fn collect_reg_ptr_evidence_stmt(stmt: &ClightStmt, out: &mut BTreeMap<RTLReg, RegPtrEvidence>) {
    match stmt {
        ClightStmt::Sassign(l, r) => {
            collect_reg_ptr_evidence_expr(l, out);
            collect_reg_ptr_evidence_expr(r, out);
        }
        ClightStmt::Sset(_, e) => collect_reg_ptr_evidence_expr(e, out),
        ClightStmt::Scall(_, f, args) => {
            collect_reg_ptr_evidence_expr(f, out);
            for a in args {
                collect_reg_ptr_evidence_expr(a, out);
            }
        }
        ClightStmt::Sreturn(Some(e)) => {
            let mut peeled = e;
            while let ClightExpr::Ecast(i2, _) = peeled {
                peeled = i2;
            }
            if let ClightExpr::Etempvar(id, _) = peeled {
                out.entry(*id as RTLReg).or_default().returned = true;
            }
            collect_reg_ptr_evidence_expr(e, out);
        }
        ClightStmt::Sifthenelse(c, a, b) => {
            collect_reg_ptr_evidence_expr(c, out);
            collect_reg_ptr_evidence_stmt(a, out);
            collect_reg_ptr_evidence_stmt(b, out);
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss {
                collect_reg_ptr_evidence_stmt(s, out);
            }
        }
        ClightStmt::Sloop(a, b) => {
            collect_reg_ptr_evidence_stmt(a, out);
            collect_reg_ptr_evidence_stmt(b, out);
        }
        ClightStmt::Slabel(_, inner) => collect_reg_ptr_evidence_stmt(inner, out),
        ClightStmt::Sswitch(e, cases) => {
            collect_reg_ptr_evidence_expr(e, out);
            for (_, s) in cases {
                collect_reg_ptr_evidence_stmt(s, out);
            }
        }
        _ => {}
    }
}

// ---- TR-1 greedy anchored fallback (no Z3) ----

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum GClass { Void, Int, Float, Struct, Ptr, PtrStruct, PtrFloat }

fn gclass_is_ptr(c: GClass) -> bool {
    matches!(c, GClass::Ptr | GClass::PtrStruct | GClass::PtrFloat)
}

fn gclass_pointee(c: GClass) -> GClass {
    match c {
        GClass::PtrStruct => GClass::Struct,
        GClass::PtrFloat => GClass::Float,
        _ => GClass::Int,
    }
}

// Candidate type-string -> class (mirrors cand_str_to_ty).
fn gclass_of_cand_str(s: &str) -> GClass {
    if s.starts_with("ptr_struct_") {
        return GClass::PtrStruct;
    }
    if s == "ptr_double" || s == "ptr_float" {
        return GClass::PtrFloat;
    }
    if s.starts_with("ptr_") {
        return GClass::Ptr;
    }
    if s.starts_with("float_") {
        return GClass::Float;
    }
    GClass::Int
}

// ClightType -> class (mirrors clight_to_ty).
fn gclass_of_clight(ct: &ClightType) -> GClass {
    match ct {
        ClightType::Tvoid => GClass::Void,
        ClightType::Tfloat(..) => GClass::Float,
        ClightType::Tstruct(..) => GClass::Struct,
        ClightType::Tpointer(inner, _) => match inner.as_ref() {
            ClightType::Tstruct(..) => GClass::PtrStruct,
            ClightType::Tfloat(..) => GClass::PtrFloat,
            _ => GClass::Ptr,
        },
        _ => GClass::Int,
    }
}

// XType -> class (mirrors xtype_to_ty, including its ptr(int) collapse of specific pointers).
fn gclass_of_xtype(xt: &XType) -> GClass {
    match xt {
        XType::Xvoid => GClass::Void,
        XType::Xfloat | XType::Xsingle => GClass::Float,
        XType::XstructPtr(_) => GClass::PtrStruct,
        XType::Xptr | XType::Xcharptr | XType::Xcharptrptr | XType::Xintptr
        | XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr => GClass::Ptr,
        _ => GClass::Int,
    }
}

// compatible() mirror: float<->ptr and struct<->non-struct are the mismatches.
fn gcompat(a: GClass, b: GClass) -> bool {
    let bad1 = a == GClass::Float && gclass_is_ptr(b);
    let bad2 = gclass_is_ptr(a) && b == GClass::Float;
    let bad3 = a == GClass::Struct && b != GClass::Struct;
    let bad4 = a != GClass::Struct && b == GClass::Struct;
    !(bad1 || bad2 || bad3 || bad4)
}

// Greedy violation weights mirroring solver ordering: unsatisfiable structural requirement > compat_w mismatch > cast nudge > int-op nudge > prior flip.
const G_HARD: u64 = 1 << 20;
const G_MED: u64 = 16;
const G_CAST: u64 = 8;
const G_INT: u64 = 4;
const G_FLIP: u64 = 1;

struct GreedyEnv<'a> {
    func: &'a FunctionData,
    name_to_ident: &'a HashMap<String, Ident>,
    anchors: &'a BTreeMap<RTLReg, GClass>,
    func_ret: GClass,
}

// Cost of a structural requirement on `reg`: G_FLIP if some candidate satisfies it (solver would flip at prior cost), G_HARD otherwise.
fn greedy_flip_cost(env: &GreedyEnv, reg: RTLReg, ok: impl Fn(&str) -> bool) -> u64 {
    match env.func.var_type_candidates.get(&reg) {
        Some(cands) if cands.iter().any(|c| ok(c)) => G_FLIP,
        _ => G_HARD,
    }
}

// type_of mirror: returns the class of `e` and accumulates violation costs against the anchors.
fn greedy_expr(env: &GreedyEnv, e: &ClightExpr, cost: &mut u64) -> GClass {
    match e {
        ClightExpr::Etempvar(id, ct) => env
            .anchors
            .get(&(*id as RTLReg))
            .copied()
            .unwrap_or_else(|| gclass_of_clight(ct)),
        ClightExpr::EconstInt(..) | ClightExpr::EconstLong(..) => GClass::Int,
        ClightExpr::EconstFloat(..) | ClightExpr::EconstSingle(..) => GClass::Float,
        ClightExpr::Evar(_, ct) | ClightExpr::EvarSymbol(_, ct) => gclass_of_clight(ct),
        ClightExpr::Ederef(inner, _) => {
            let ic = greedy_expr(env, inner, cost);
            if !gclass_is_ptr(ic) {
                if let Some(root) = bare_chain_root(inner) {
                    if env.anchors.contains_key(&root) {
                        *cost += greedy_flip_cost(env, root, |s| s.starts_with("ptr_"));
                    }
                }
            }
            gclass_pointee(ic)
        }
        ClightExpr::Eaddrof(inner, _) => {
            let ic = greedy_expr(env, inner, cost);
            match ic {
                GClass::Struct => GClass::PtrStruct,
                GClass::Float => GClass::PtrFloat,
                _ => GClass::Ptr,
            }
        }
        ClightExpr::Efield(base, _, ct) => {
            let bc = greedy_expr(env, base, cost);
            if bc != GClass::Struct {
                if let Some(root) = bare_chain_root(base) {
                    if env.anchors.contains_key(&root) {
                        *cost += greedy_flip_cost(env, root, |s| s.starts_with("ptr_struct_"));
                    }
                }
            }
            gclass_of_clight(ct)
        }
        ClightExpr::Ecast(inner, ct) => {
            let ic = greedy_expr(env, inner, cost);
            let tgt = gclass_of_clight(ct);
            if matches!(ct, ClightType::Tpointer(..)) && ic == GClass::Float {
                // cast-to-pointer of a float: flip-gradable for an inferable register (mirrors the hard assert), weight-8 nudge otherwise.
                let mut peeled = inner.as_ref();
                while let ClightExpr::Ecast(i2, _) = peeled {
                    peeled = i2;
                }
                match peeled {
                    ClightExpr::Etempvar(id, _) if env.anchors.contains_key(&(*id as RTLReg)) => {
                        *cost += greedy_flip_cost(env, *id as RTLReg, |s| !s.starts_with("float_"));
                    }
                    _ => *cost += G_CAST,
                }
            }
            if !gcompat(ic, tgt) {
                *cost += G_CAST;
            }
            tgt
        }
        ClightExpr::Ebinop(op, l, r, ct) => {
            let lc = greedy_expr(env, l, cost);
            let rc = greedy_expr(env, r, cost);
            match op {
                ClightBinaryOp::Oadd | ClightBinaryOp::Osub => {
                    // Pointer arithmetic carries the pointer operand's class; a pointer annotation must not be the fallback (mirrors type_of).
                    if gclass_is_ptr(lc) {
                        lc
                    } else if gclass_is_ptr(rc) {
                        rc
                    } else {
                        match ct {
                            ClightType::Tpointer(..) => GClass::Int,
                            other => gclass_of_clight(other),
                        }
                    }
                }
                _ => gclass_of_clight(ct),
            }
        }
        ClightExpr::Eunop(_, inner, ct) => {
            let _ = greedy_expr(env, inner, cost);
            gclass_of_clight(ct)
        }
        ClightExpr::Econdition(c, a, b, ct) => {
            let _ = greedy_expr(env, c, cost);
            let _ = greedy_expr(env, a, cost);
            let _ = greedy_expr(env, b, cost);
            gclass_of_clight(ct)
        }
        _ => GClass::Int,
    }
}

// constrain_stmt mirror: accumulates the compat_w-grade violations.
fn greedy_stmt(env: &GreedyEnv, stmt: &ClightStmt, cost: &mut u64) {
    match stmt {
        ClightStmt::Sassign(lhs, rhs) => {
            let lc = greedy_expr(env, lhs, cost);
            let rc = greedy_expr(env, rhs, cost);
            if !gcompat(lc, rc) {
                *cost += G_MED;
            }
        }
        ClightStmt::Sset(id, e) => {
            let rc = greedy_expr(env, e, cost);
            if let Some(&lc) = env.anchors.get(&(*id as RTLReg)) {
                if !gcompat(lc, rc) {
                    *cost += G_MED;
                }
            }
        }
        ClightStmt::Scall(ret, f, args) => {
            let _ = greedy_expr(env, f, cost);
            let sig = callee_ident_from_expr(f, env.name_to_ident)
                .and_then(|id| env.func.callee_signatures.get(&id));
            for (i, a) in args.iter().enumerate() {
                let at = greedy_expr(env, a, cost);
                if let Some(sig) = sig {
                    if let Some(pt) = sig.param_types.get(i) {
                        if !gcompat(at, gclass_of_xtype(pt)) {
                            *cost += G_MED;
                        }
                    }
                }
            }
            if let (Some(rid), Some(sig)) = (ret, sig) {
                if let Some(&lc) = env.anchors.get(&(*rid as RTLReg)) {
                    if !gcompat(lc, gclass_of_xtype(&sig.return_type)) {
                        *cost += G_MED;
                    }
                }
                // void-callee result capture penalty (mirrors the !guard soft).
                if matches!(sig.return_type, XType::Xvoid) {
                    *cost += G_MED;
                }
            }
        }
        ClightStmt::Sreturn(ret) => {
            let is_void_fn = env.func_ret == GClass::Void;
            match ret {
                Some(e) => {
                    let et = greedy_expr(env, e, cost);
                    if !gcompat(et, env.func_ret) {
                        *cost += G_MED;
                    }
                    if is_void_fn {
                        *cost += G_MED;
                    }
                }
                None => {
                    if !is_void_fn {
                        *cost += G_MED;
                    }
                }
            }
        }
        ClightStmt::Sifthenelse(c, a, b) => {
            let _ = greedy_expr(env, c, cost);
            greedy_stmt(env, a, cost);
            greedy_stmt(env, b, cost);
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss {
                greedy_stmt(env, s, cost);
            }
        }
        ClightStmt::Sloop(a, b) => {
            greedy_stmt(env, a, cost);
            greedy_stmt(env, b, cost);
        }
        ClightStmt::Slabel(_, inner) => greedy_stmt(env, inner, cost),
        ClightStmt::Sswitch(e, cases) => {
            let _ = greedy_expr(env, e, cost);
            for (_, s) in cases {
                greedy_stmt(env, s, cost);
            }
        }
        _ => {}
    }
}

fn greedy_candidate_cost(env: &GreedyEnv, stmt: &ClightStmt) -> u64 {
    let mut cost = 0u64;
    greedy_stmt(env, stmt, &mut cost);
    // constrain_int_ops mirror: integer-only operators want integer operand registers.
    let mut int_regs: BTreeSet<RTLReg> = BTreeSet::new();
    scan_pure_int_regs_stmt(stmt, &mut int_regs);
    for reg in int_regs {
        if let Some(&c) = env.anchors.get(&reg) {
            if c != GClass::Int {
                cost += G_INT;
            }
        }
    }
    cost
}

// TR-1 final backstop: deterministic per-node anchored selection without Z3. Anchors start at the priority-0 candidate prior, are upgraded by structural facts in single-candidate nodes (the sites solver asserts hard + the two dominating-soft shapes), and each multi-candidate node picks the cheapest-violation candidate. Soft-vs-soft global rebalancing is NOT done (solver's job); greedy keeps the prior. /usr/bin/sed forced-fallback benchmark: 37 recompile errors vs 37 for full solve, vs 52 for blind candidate[0].
fn greedy_anchored_fallback(
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
) -> (HashMap<Node, Option<usize>>, HashMap<RTLReg, usize>, HashMap<RTLReg, String>) {
    let mut sorted_regs: Vec<RTLReg> = func.var_type_candidates.keys().copied().collect();
    sorted_regs.sort();
    let mut anchors: BTreeMap<RTLReg, GClass> = BTreeMap::new();
    for &reg in &sorted_regs {
        if let Some(c0) = func.var_type_candidates[&reg].first() {
            anchors.insert(reg, gclass_of_cand_str(c0));
        }
    }
    let func_ret_class = gclass_of_clight(&func.return_type);

    let mut nodes: Vec<Node> = func.node_statements.keys().copied().collect();
    nodes.sort();

    // Structural facts from unconditional (single-candidate) nodes upgrade the anchors.
    let mut fact_ev: BTreeMap<RTLReg, RegPtrEvidence> = BTreeMap::new();
    for &node in &nodes {
        let cands = &func.node_statements[&node];
        if cands.len() == 1 {
            collect_reg_ptr_evidence_stmt(&cands[0], &mut fact_ev);
        }
    }
    for (&reg, ev) in &fact_ev {
        if !anchors.contains_key(&reg) {
            // Non-inferable registers keep their annotations, like the solver.
            continue;
        }
        if ev.bare_field {
            anchors.insert(reg, GClass::PtrStruct);
        } else if ev.bare_deref && !gclass_is_ptr(anchors[&reg]) {
            anchors.insert(reg, GClass::Ptr);
        } else if (ev.cast_to_ptr || (ev.returned && !gcompat(GClass::Float, func_ret_class)))
            && anchors[&reg] == GClass::Float
        {
            // Hard not-float (cast-to-pointer) or dominating return-compat makes the float prior unreachable; model lands on int.
            anchors.insert(reg, GClass::Int);
        }
    }

    let env = GreedyEnv {
        func,
        name_to_ident,
        anchors: &anchors,
        func_ret: func_ret_class,
    };

    let mut cand_out: HashMap<Node, Option<usize>> = HashMap::new();
    for &node in &nodes {
        let cands = &func.node_statements[&node];
        if cands.len() <= 1 {
            cand_out.insert(node, Some(0));
            continue;
        }
        let mut best_cost = u64::MAX;
        let mut best_idx = 0usize;
        for (ci, stmt) in cands.iter().enumerate() {
            let cost = greedy_candidate_cost(&env, stmt);
            if cost < best_cost {
                best_cost = cost;
                best_idx = ci;
            }
        }
        cand_out.insert(node, Some(best_idx));
    }

    // Register declarations from the hard evidence of the selected statements.
    let mut sel_ev: BTreeMap<RTLReg, RegPtrEvidence> = BTreeMap::new();
    for &node in &nodes {
        if let Some(Some(ci)) = cand_out.get(&node) {
            if let Some(stmt) = func.node_statements[&node].get(*ci) {
                collect_reg_ptr_evidence_stmt(stmt, &mut sel_ev);
            }
        }
    }
    let mut ty_out: HashMap<RTLReg, usize> = HashMap::new();
    let mut ty_override: HashMap<RTLReg, String> = HashMap::new();
    for &reg in &sorted_regs {
        let ev = match sel_ev.get(&reg) {
            Some(ev) => ev,
            None => continue, // no structural evidence: keep the prior (candidate[0])
        };
        let cands = &func.var_type_candidates[&reg];
        let rendered = if ev.bare_field {
            match func.reg_struct_ids.get(&reg) {
                Some(&sid) => format!("ptr_struct_{:x}", sid),
                None => "ptr_I64".to_string(),
            }
        } else if ev.bare_deref {
            "ptr_I64".to_string()
        } else if (ev.cast_to_ptr || (ev.returned && !gcompat(GClass::Float, func_ret_class)))
            && cands.first().map(|c| gclass_of_cand_str(c) == GClass::Float).unwrap_or(false)
        {
            // not-float must-fact (or dominating return-compat) overrides float prior (see anchor pass above).
            "int_I64".to_string()
        } else {
            continue;
        };
        match anchor_index(cands, &rendered, false) {
            Some(idx) => {
                ty_out.insert(reg, idx);
            }
            None => {
                ty_out.insert(reg, 0);
                ty_override.insert(reg, rendered);
            }
        }
    }

    (cand_out, ty_out, ty_override)
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

// (struct,field) key of a field-access VALUE (a load `base->f`, possibly cast-wrapped).
fn field_key_of_expr(e: &ClightExpr) -> Option<(String, String)> {
    match e {
        ClightExpr::Ecast(inner, _) => field_key_of_expr(inner),
        _ => field_key_of_lvalue(e),
    }
}

fn xtype_is_ptr_class(xt: &XType) -> bool {
    matches!(
        xt,
        XType::Xptr
            | XType::Xcharptr
            | XType::Xcharptrptr
            | XType::Xintptr
            | XType::Xfloatptr
            | XType::Xsingleptr
            | XType::Xfuncptr
            | XType::XstructPtr(_)
    )
}

// True if the expression carries a pointer value: explicit (addrof, symbol, pointer-annotated) or implicit via TR-3 (a register solved as a pointer, possibly cast-wrapped, carried by pointer arithmetic, or loaded from a pointer-annotated field).
fn clight_value_is_ptr(e: &ClightExpr, ptr_regs: &HashSet<RTLReg>) -> bool {
    match e {
        ClightExpr::Eaddrof(..) | ClightExpr::EvarSymbol(..) => true,
        ClightExpr::Etempvar(id, ct) => {
            matches!(ct, ClightType::Tpointer(..)) || ptr_regs.contains(&(*id as RTLReg))
        }
        ClightExpr::Evar(_, ct) => matches!(ct, ClightType::Tpointer(..)),
        ClightExpr::Ecast(inner, ct) => {
            matches!(ct, ClightType::Tpointer(..)) || clight_value_is_ptr(inner, ptr_regs)
        }
        // Pointer arithmetic: `p + n` carries the pointer operand; `p - q` only when rhs is not a pointer (pointer difference is an integer).
        ClightExpr::Ebinop(ClightBinaryOp::Oadd, l, r, _) => {
            clight_value_is_ptr(l, ptr_regs) || clight_value_is_ptr(r, ptr_regs)
        }
        ClightExpr::Ebinop(ClightBinaryOp::Osub, l, r, _) => {
            clight_value_is_ptr(l, ptr_regs) && !clight_value_is_ptr(r, ptr_regs)
        }
        ClightExpr::Ederef(_, ct) | ClightExpr::Efield(_, _, ct) => {
            matches!(ct, ClightType::Tpointer(..))
        }
        _ => false,
    }
}

// Record (struct,field) keys with pointer evidence (TR-3): pointer-valued store, field value consumed as a pointer, or field passed as pointer argument.
fn scan_field_ptr_stores(
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    ptr_regs: &HashSet<RTLReg>,
    stmt: &ClightStmt,
    out: &mut HashSet<(String, String)>,
) {
    match stmt {
        ClightStmt::Sassign(lhs, rhs) => {
            if clight_value_is_ptr(rhs, ptr_regs) {
                if let Some(key) = field_key_of_lvalue(lhs) {
                    out.insert(key);
                }
            }
        }
        ClightStmt::Sset(id, e) => {
            // Out-flow: the field's value lands in a register selected as a pointer.
            if ptr_regs.contains(&(*id as RTLReg)) {
                if let Some(key) = field_key_of_expr(e) {
                    out.insert(key);
                }
            }
        }
        ClightStmt::Scall(_, f, args) => {
            // Arg-flow: the field is passed where the callee expects a pointer.
            if let Some(sig) = callee_ident_from_expr(f, name_to_ident)
                .and_then(|id| func.callee_signatures.get(&id))
            {
                for (i, a) in args.iter().enumerate() {
                    if let Some(pt) = sig.param_types.get(i) {
                        if xtype_is_ptr_class(pt) {
                            if let Some(key) = field_key_of_expr(a) {
                                out.insert(key);
                            }
                        }
                    }
                }
            }
        }
        ClightStmt::Sifthenelse(_, a, b) | ClightStmt::Sloop(a, b) => {
            scan_field_ptr_stores(func, name_to_ident, ptr_regs, a, out);
            scan_field_ptr_stores(func, name_to_ident, ptr_regs, b, out);
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss {
                scan_field_ptr_stores(func, name_to_ident, ptr_regs, s, out);
            }
        }
        ClightStmt::Slabel(_, inner) => {
            scan_field_ptr_stores(func, name_to_ident, ptr_regs, inner, out)
        }
        ClightStmt::Sswitch(_, cases) => {
            for (_, s) in cases {
                scan_field_ptr_stores(func, name_to_ident, ptr_regs, s, out);
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

    // TR-1 run summary: how many functions shipped a degraded type solve (per-function WARN lines above carry the detail). Swap-reset so in-process multi-binary runs (tests) report per program.
    let fallbacks = TYPE_SOLVE_FALLBACKS.swap(0, std::sync::atomic::Ordering::Relaxed);
    let relaxed = TYPE_SOLVE_RELAXED.swap(0, std::sync::atomic::Ordering::Relaxed);
    let partial = TYPE_SOLVE_PARTIAL.swap(0, std::sync::atomic::Ordering::Relaxed);
    if fallbacks > 0 || partial > 0 {
        eprintln!(
            "[clight-select] WARN: type solve degraded for {}/{} functions ({} partial-model reuse, {} relaxed re-solve, {} greedy anchored)",
            fallbacks + partial,
            functions.len(),
            partial,
            relaxed,
            fallbacks.saturating_sub(relaxed)
        );
    }

    // TR-3: registers solved as pointers (override > selected candidate > sole upstream type in var_types) are the implicit pointer-flow facts for field-typing below.
    let mut ptr_regs_by_addr: HashMap<Address, HashSet<RTLReg>> = HashMap::new();
    {
        let func_by_addr: HashMap<Address, &FunctionData> =
            functions.iter().map(|f| (f.address, f)).collect();
        for (addr, _cmap, tmap, omap) in &per_func {
            let func = match func_by_addr.get(addr) {
                Some(f) => *f,
                None => continue,
            };
            let set = ptr_regs_by_addr.entry(*addr).or_default();
            for (reg, cands) in &func.var_type_candidates {
                let sel: Option<&str> = omap.get(reg).map(|s| s.as_str()).or_else(|| {
                    let idx = tmap.get(reg).copied().unwrap_or(0);
                    cands.get(idx).map(|s| s.as_str())
                });
                if sel.map(|s| s.starts_with("ptr_")).unwrap_or(false) {
                    set.insert(*reg);
                }
            }
            for (reg, ty) in &func.var_types {
                if !func.var_type_candidates.contains_key(reg) && ty.starts_with("ptr_") {
                    set.insert(*reg);
                }
            }
        }
    }

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

    // #3: program-wide struct field-type inference. Start from upstream defaults, then for any field with pointer evidence (a pointer-valued store, the value consumed as a pointer, or passed as a pointer argument - TR-3) re-select a pointer candidate (a C-decl string containing '*', preferring a struct pointer) when one exists, so the field is no longer a scalar/float that forces an illegal `(double)ptr` store.
    let mut field_cands: HashMap<(String, String), Vec<String>> = HashMap::new();
    for func in functions {
        for (key, cands) in &func.struct_field_type_candidates {
            field_cands.entry(key.clone()).or_insert_with(|| cands.clone());
        }
    }
    let empty_ptr_regs: HashSet<RTLReg> = HashSet::new();
    let mut field_ptr_stored: HashSet<(String, String)> = HashSet::new();
    for func in functions {
        let pr = ptr_regs_by_addr.get(&func.address).unwrap_or(&empty_ptr_regs);
        for cands in func.node_statements.values() {
            for stmt in cands {
                scan_field_ptr_stores(func, name_to_ident, pr, stmt, &mut field_ptr_stored);
            }
        }
    }
    // NOTE (TR-3): `struct_field_type_idx` has no downstream consumer yet -- struct defs are emitted from emit_struct_field/query.rs before this solve runs, and struct_field_type_candidates was never populated (stranded by clang_refine->z3 migration). Evidence is correct; wiring belongs in query.rs/clight_field.
    if std::env::var("MANIFOLD_TR3_TRACE").is_ok() {
        let mut keys: Vec<&(String, String)> = field_ptr_stored.iter().collect();
        keys.sort();
        for (s, f) in keys {
            eprintln!("[clight-select] TR3: field {}.{} has pointer evidence", s, f);
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
