//! C legality, class consistency, and concrete declaration rendering.
//!
//! This is one selection analysis; recursive C rules do not own solver policy.

use super::super::candtype::{CandClass, CandType, Sign};
use super::super::query::{FunctionData, InterfaceClass, KnownGlobalTypes};
use super::super::select::callee_ident_from_expr;
use super::constraints::{ConstraintSink, ModelView, SolveBackend};
use super::{Analysis, Candidate, CandidateAnalysis, DeclarationContext, FunctionContext};
use crate::x86::types::XType;
use crate::x86::types::{ClightBinaryOp, ClightExpr, ClightStmt, ClightType, Ident, RTLReg};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use z3::ast::{Bool, Dynamic, Int};
use z3::{DatatypeAccessor, DatatypeBuilder, DatatypeSort, Sort};

pub(crate) struct CTypes;

impl Analysis for CTypes {
    fn name(&self) -> &'static str {
        "c-types"
    }

    fn constrain_declaration(
        &self,
        cx: &DeclarationContext<'_>,
        reg: RTLReg,
        tv: &Dynamic,
        backend: &dyn SolveBackend,
    ) {
        let (t, func, interface_pins) = (cx.types, cx.function, cx.pins);
        // Domain pruning: a register decl never renders as bare func/void/union (render_type falls back to int_I64), so excluding those variants HARD shrinks every clause's search space at zero MaxSMT cost and lets the Sset compat formula drop their arms (wt_cast_to_reg).
        backend.assert_hard(&t.is_func(tv).not());
        backend.assert_hard(&t.is_void(tv).not());
        backend.assert_hard(&t.is_union(tv).not());
        // Stage C receives an interface commitment selected only after
        // full legality pricing.  Let an explicit non-pointer commitment
        // supersede Stage A's pointer-only pruning; otherwise the old
        // heuristic and the new hard pin contradict each other before
        // any statement candidate is considered, making every corrected
        // wrapper interface UNSAT.  Pointer pins retain the pruning.
        let pinned_non_pointer = interface_pins.iter().any(|(pinned_reg, xtype)| {
            *pinned_reg == reg && !InterfaceClass::from_xtype(xtype).is_pointer()
        });
        if func.must_pointer_regs.contains(&reg) && !pinned_non_pointer {
            backend.assert_hard(&t.is_ptr(tv));
        }
        // Float-class pruning (RC-1): the is_float axis is otherwise free, so require positive upstream float evidence; excluding the float variant HARD cannot cause UNSAT since nothing forces is_float.
        let cands = func.var_type_candidates.get(&reg);
        let has_float_cand = cands
            .map(|cs| cs.iter().any(|c| c.is_float() || c.is_float_pointee()))
            .unwrap_or(false);
        // RC-1: a register carrying a concrete non-float pointer candidate is a pointer, so close the is_float axis to stop MaxSMT fabricating double; ptr_double/ptr_float excluded.
        let has_concrete_ptr = cands
            .map(|cs| cs.iter().any(|c| c.is_pointer() && !c.is_float_pointee()))
            .unwrap_or(false);
        let pinned_float = interface_pins.iter().any(|(pinned_reg, xtype)| {
            *pinned_reg == reg && matches!(xtype, XType::Xfloat | XType::Xsingle)
        });
        let has_float_evidence = pinned_float || (has_float_cand && !has_concrete_ptr);
        if !has_float_evidence {
            backend.assert_hard(&t.is_float(tv).not());
        }
    }

    fn constrain_interfaces(
        &self,
        cx: &DeclarationContext<'_>,
        tyvar: &HashMap<RTLReg, Dynamic>,
        backend: &dyn SolveBackend,
    ) {
        let (t, interface_pins) = (cx.types, cx.pins);
        // Stage-C only: the committed own-interface class is a hard input to
        // the dirty re-solve.  Stage A passes an empty slice and remains
        // byte-identical, including compat_w and variable counts.
        for (reg, xtype) in interface_pins {
            if let Some(variable) = tyvar.get(reg) {
                backend.assert_hard(&variable._eq(xtype_to_ty(t, xtype)));
            }
        }
    }

    fn build(&self, _cx: &FunctionContext<'_>) -> Option<Box<dyn CandidateAnalysis>> {
        Some(Box::new(CTypes))
    }
}

impl CandidateAnalysis for CTypes {
    fn constrain_candidate(
        &self,
        cx: &FunctionContext<'_>,
        candidate: &Candidate<'_>,
        sink: &ConstraintSink<'_>,
    ) {
        let rules = RuleSink {
            common: sink,
            agree_seen: RefCell::new(HashSet::new()),
        };
        constrain_stmt(
            cx.types,
            cx.declarations,
            &rules,
            candidate.selected,
            cx.function,
            cx.names,
            cx.return_type,
            sink.compat_w,
            candidate.statement,
        );
    }
}

/// Dedup of repeated C annotation-class preferences is local to this module,
/// not shared mutable state that other analyses need to know about.
struct RuleSink<'a, 'b> {
    common: &'a ConstraintSink<'b>,
    agree_seen: RefCell<HashSet<(RTLReg, u8)>>,
}
impl<'a, 'b> std::ops::Deref for RuleSink<'a, 'b> {
    type Target = ConstraintSink<'b>;
    fn deref(&self) -> &Self::Target {
        self.common
    }
}

// Variant order in the Ty datatype; indices into DatatypeSort::variants.
const V_VOID: usize = 0;
const V_INT: usize = 1;
const V_FLOAT: usize = 2;
const V_STRUCT: usize = 3;
const V_UNION: usize = 4;
const V_FUNC: usize = 5;
const V_PTR: usize = 6;

// Per-Context handles to the recursive Ty datatype; the algebra models type CLASSES only, since width/signedness payloads carried no constraint information and exploded maxres.
pub(crate) struct TypeDt {
    dt: DatatypeSort,
}

impl TypeDt {
    pub(crate) fn build() -> Self {
        let dt = DatatypeBuilder::new("Ty")
            .variant("void", vec![])
            .variant("int", vec![])
            .variant("float", vec![])
            .variant("struct", vec![("sid", DatatypeAccessor::Sort(Sort::int()))])
            .variant("union", vec![("uid", DatatypeAccessor::Sort(Sort::int()))])
            .variant("func", vec![])
            .variant("ptr", vec![("pointee", DatatypeAccessor::datatype("Ty"))])
            .finish();
        TypeDt { dt }
    }

    pub(crate) fn void(&self) -> Dynamic {
        self.dt.variants[V_VOID].constructor.apply(&[])
    }
    pub(crate) fn int(&self) -> Dynamic {
        self.dt.variants[V_INT].constructor.apply(&[])
    }
    pub(crate) fn float(&self) -> Dynamic {
        self.dt.variants[V_FLOAT].constructor.apply(&[])
    }
    pub(crate) fn struct_(&self, sid: i64) -> Dynamic {
        self.dt.variants[V_STRUCT]
            .constructor
            .apply(&[&Int::from_i64(sid)])
    }
    pub(crate) fn union_(&self, uid: i64) -> Dynamic {
        self.dt.variants[V_UNION]
            .constructor
            .apply(&[&Int::from_i64(uid)])
    }
    pub(crate) fn func(&self) -> Dynamic {
        self.dt.variants[V_FUNC].constructor.apply(&[])
    }
    pub(crate) fn ptr(&self, pointee: &Dynamic) -> Dynamic {
        self.dt.variants[V_PTR].constructor.apply(&[pointee])
    }

    pub(crate) fn is_void(&self, x: &Dynamic) -> Bool {
        self.dt.variants[V_VOID]
            .tester
            .apply(&[x])
            .as_bool()
            .unwrap()
    }
    pub(crate) fn is_int(&self, x: &Dynamic) -> Bool {
        self.dt.variants[V_INT]
            .tester
            .apply(&[x])
            .as_bool()
            .unwrap()
    }
    pub(crate) fn is_float(&self, x: &Dynamic) -> Bool {
        self.dt.variants[V_FLOAT]
            .tester
            .apply(&[x])
            .as_bool()
            .unwrap()
    }
    pub(crate) fn is_struct(&self, x: &Dynamic) -> Bool {
        self.dt.variants[V_STRUCT]
            .tester
            .apply(&[x])
            .as_bool()
            .unwrap()
    }
    pub(crate) fn is_union(&self, x: &Dynamic) -> Bool {
        self.dt.variants[V_UNION]
            .tester
            .apply(&[x])
            .as_bool()
            .unwrap()
    }
    pub(crate) fn is_func(&self, x: &Dynamic) -> Bool {
        self.dt.variants[V_FUNC]
            .tester
            .apply(&[x])
            .as_bool()
            .unwrap()
    }
    pub(crate) fn is_ptr(&self, x: &Dynamic) -> Bool {
        self.dt.variants[V_PTR]
            .tester
            .apply(&[x])
            .as_bool()
            .unwrap()
    }
    pub(crate) fn pointee(&self, x: &Dynamic) -> Dynamic {
        self.dt.variants[V_PTR].accessors[0].apply(&[x])
    }
    pub(crate) fn struct_sid(&self, x: &Dynamic) -> Dynamic {
        self.dt.variants[V_STRUCT].accessors[0].apply(&[x])
    }

    // The post-typeconv integer universe (one class on this algebra).
    pub(crate) fn is_intish(&self, x: &Dynamic) -> Bool {
        self.is_int(x)
    }
    // Arithmetic class: int/float -- what classify_binarith accepts.
    pub(crate) fn is_arith(&self, x: &Dynamic) -> Bool {
        Bool::or(&[self.is_int(x), self.is_float(x)])
    }
    // Pointer-shaped after decay: a pointer or a function (functions decay).
    pub(crate) fn is_ptrish(&self, x: &Dynamic) -> Bool {
        Bool::or(&[self.is_ptr(x), self.is_func(x)])
    }
    // classify_bool: int/float/ptr accept, struct/union/void reject.
    pub(crate) fn is_boolish(&self, x: &Dynamic) -> Bool {
        Bool::or(&[self.is_arith(x), self.is_ptrish(x)])
    }

    // A fresh free type variable.
    pub(crate) fn fresh(&self) -> Dynamic {
        Dynamic::from_ast(&z3::ast::Datatype::fresh_const("ty", &self.dt.sort))
    }
}

// XType (signature types) -> a concrete Ty term.
pub(crate) fn xtype_to_ty(t: &TypeDt, xt: &XType) -> Dynamic {
    match xt {
        XType::Xvoid => t.void(),
        XType::Xfloat | XType::Xsingle => t.float(),
        XType::XstructPtr(sid) => t.ptr(&t.struct_(*sid as i64)),
        XType::Xfloatptr | XType::Xsingleptr => t.ptr(&t.float()),
        XType::Xfuncptr => t.ptr(&t.func()),
        XType::Xptr | XType::Xcharptr | XType::Xcharptrptr | XType::Xintptr => t.ptr(&t.int()),
        _ => t.int(),
    }
}

// ClightType (expression annotations) -> a concrete Ty term at OPERATOR positions: typeconv applies (the whole integer family collapses to the int class, arrays decay, function decay is handled via classify_fun's ptrish acceptance).
pub(crate) fn clight_to_ty(t: &TypeDt, ct: &ClightType) -> Dynamic {
    match ct {
        ClightType::Tvoid => t.void(),
        ClightType::Tint(..) | ClightType::Tlong(..) | ClightType::Tint128(..) => t.int(),
        ClightType::Tfloat(..) => t.float(),
        ClightType::Tstruct(sid, _) => t.struct_(*sid as i64),
        ClightType::Tunion(uid, _) => t.union_(*uid as i64),
        ClightType::Tfunction(..) => t.func(),
        ClightType::Tpointer(inner, _) => {
            let pointee = clight_to_ty(t, inner);
            t.ptr(&pointee)
        }
        ClightType::Tarray(inner, _, _) => {
            // typeconv: arrays decay to element pointers.
            let pointee = clight_to_ty(t, inner);
            t.ptr(&pointee)
        }
    }
}

// Candidate type -> a concrete Ty term (the provenance prior); classes only -- width and signedness live in the candidate itself and are resolved at the anchor.
pub(crate) fn cand_to_ty(t: &TypeDt, candidate: CandType) -> Dynamic {
    match candidate {
        CandType::PtrStruct(sid) => t.ptr(&t.struct_(sid as i64)),
        CandType::PtrDouble | CandType::PtrFloat => t.ptr(&t.float()),
        CandType::PtrVoid => t.ptr(&t.void()),
        CandType::PtrFunc => t.ptr(&t.func()),
        // ptr_ptr_char keeps an int pointee here: the class algebra only tests pointer-ness at
        // this depth, and giving it a pointer pointee would change deref chains, not just decls.
        CandType::PtrLong | CandType::PtrChar | CandType::PtrCharPtr | CandType::PtrInt => {
            t.ptr(&t.int())
        }
        CandType::F32 | CandType::F64 => t.float(),
        // The register domain excludes void (asserted hard below), so a void candidate stands in
        // as int rather than becoming an unsatisfiable prior.
        CandType::Void
        | CandType::Bool
        | CandType::I8(_)
        | CandType::I16(_)
        | CandType::I32(_)
        | CandType::I64(_) => t.int(),
    }
}

// wt_cast at the class level: float<->ptr, cross-kind composites, a void source and a function target are errors, while int<->ptr/width/float conversions are silent; composite IDs are deliberately not compared.
pub(crate) fn wt_cast_term(t: &TypeDt, from: &Dynamic, to: &Dynamic) -> Bool {
    let bad_f2p = Bool::and(&[t.is_float(from), t.is_ptrish(to)]);
    let bad_p2f = Bool::and(&[t.is_ptrish(from), t.is_float(to)]);
    let comp_ok = Bool::or(&[
        Bool::and(&[t.is_struct(from), t.is_struct(to)]),
        Bool::and(&[t.is_union(from), t.is_union(to)]),
    ]);
    let comp_involved = Bool::or(&[
        t.is_struct(from),
        t.is_union(from),
        t.is_struct(to),
        t.is_union(to),
    ]);
    let comp_bad = Bool::and(&[comp_involved, comp_ok.not()]);
    let bad_void_src = t.is_void(from);
    let bad_to_func = t.is_func(to);
    let illegal = Bool::or(&[bad_f2p, bad_p2f, comp_bad, bad_void_src, bad_to_func]);
    // cast_case_void: ANY source converts to void.
    Bool::or(&[t.is_void(to), illegal.not()])
}

// wt_cast specialized for a pruned register variable TO-side, dropping the func/void/union arms to 8 testers instead of 14 on the hottest obligation family.
pub(crate) fn wt_cast_to_reg(t: &TypeDt, from: &Dynamic, lv: &Dynamic) -> Bool {
    let bad_f2p = Bool::and(&[t.is_float(from), t.is_ptr(lv)]);
    let bad_p2f = Bool::and(&[t.is_ptrish(from), t.is_float(lv)]);
    // lv can never be a union (domain pruning), so a union SOURCE is illegal for every register target; struct sources pair only with struct targets.
    let bad_comp = Bool::or(&[
        Bool::and(&[t.is_struct(from), t.is_struct(lv).not()]),
        Bool::and(&[t.is_struct(from).not(), t.is_struct(lv)]),
        t.is_union(from),
    ]);
    let bad_void_src = t.is_void(from);
    Bool::or(&[bad_f2p, bad_p2f, bad_comp, bad_void_src]).not()
}

// "a and b agree on POINTERNESS", the axis the Sset-level SEL-AGREE preference operates on, demoting a crossing whose printed cast gcc rejects.
fn ptr_class_eq(t: &TypeDt, a: &Dynamic, b: &Dynamic) -> Bool {
    t.is_ptr(a)._eq(&t.is_ptr(b))
}

// type_binop legality at the class level, one clause per node; parity with ctyping::type_binop is test-enforced.
pub(crate) fn binop_legal_term(
    t: &TypeDt,
    op: ClightBinaryOp,
    ltm: &Dynamic,
    rtm: &Dynamic,
) -> Bool {
    use ClightBinaryOp::*;
    match op {
        Oadd => Bool::or(&[
            Bool::and(&[t.is_ptrish(ltm), t.is_intish(rtm)]),
            Bool::and(&[t.is_intish(ltm), t.is_ptrish(rtm)]),
            Bool::and(&[t.is_arith(ltm), t.is_arith(rtm)]),
        ]),
        Osub => Bool::or(&[
            Bool::and(&[t.is_ptrish(ltm), t.is_intish(rtm)]),
            Bool::and(&[t.is_ptrish(ltm), t.is_ptrish(rtm)]),
            Bool::and(&[t.is_arith(ltm), t.is_arith(rtm)]),
        ]),
        Omul | Odiv => Bool::and(&[t.is_arith(ltm), t.is_arith(rtm)]),
        Omod | Oand | Oor | Oxor | Oshl | Oshr => Bool::and(&[t.is_intish(ltm), t.is_intish(rtm)]),
        Oeq | One | Olt | Ogt | Ole | Oge => Bool::or(&[
            Bool::and(&[t.is_ptrish(ltm), t.is_ptrish(rtm)]),
            Bool::and(&[t.is_ptrish(ltm), t.is_intish(rtm)]),
            Bool::and(&[t.is_intish(ltm), t.is_ptrish(rtm)]),
            Bool::and(&[t.is_arith(ltm), t.is_arith(rtm)]),
        ]),
    }
}

// No C binary operator accepts one pointer-shaped operand together with one floating operand: classify_add/classify_sub/classify_cmp have no such case, and every fallback (binarith, binarith_int) rejects pointers outright. So this arm of binop legality holds for EVERY op, and unlike the rest of the rulebook it can be enforced HARD.
//
// Hard is safe here only in the float direction. The hard type set never REQUIRES a register to be float -- it only ever removes the float variant (the RC-1 pruning above asserts `!is_float` when upstream shows no float evidence) -- so forbidding float on an operand the solver still controls is always satisfiable. Forbidding the POINTER side instead can contradict a hard `is_ptr` coming from a deref of the same register; integer-register-to-float casts avoid that conflict with a generated integer-bridge candidate, while the arith/intish arms of binop_legal_term stay soft where no equivalent local rewrite is guaranteed.
//
// Each implication is emitted only when the operand being tested for float is symbolic. With a concretely-floating operand the clause would collapse to `!is_ptrish(other)`, re-introducing that same conflict, and no choice of types could fix the expression anyway -- the soft binop_legal clause prices it and a rival candidate wins.
pub(crate) fn no_ptr_float_term(t: &TypeDt, ptr_side: &Dynamic, float_side: &Dynamic) -> Bool {
    Bool::and(&[t.is_ptrish(ptr_side), t.is_float(float_side)]).not()
}

fn assert_no_ptr_float_mix(
    t: &TypeDt,
    sink: &RuleSink,
    guard: Option<&Bool>,
    lt: &TyTerm,
    rt: &TyTerm,
    ltm: &Dynamic,
    rtm: &Dynamic,
) {
    if rt.is_sym() {
        sink.assert_structural(guard, &no_ptr_float_term(t, ltm, rtm));
    }
    if lt.is_sym() {
        sink.assert_structural(guard, &no_ptr_float_term(t, rtm, ltm));
    }
}

// type_unop legality (Ctyping.v:52): ! accepts any scalar; ~ integers only; - and __builtin_fabs numerics only.
pub(crate) fn unop_legal_term(
    t: &TypeDt,
    op: crate::x86::types::ClightUnaryOp,
    itm: &Dynamic,
) -> Bool {
    use crate::x86::types::ClightUnaryOp::*;
    match op {
        Onotbool => t.is_boolish(itm),
        Onotint => t.is_intish(itm),
        Oneg | Oabsfloat => t.is_arith(itm),
    }
}

fn cast_operand_is_inferable(e: &ClightExpr, tyvar: &HashMap<RTLReg, Dynamic>) -> bool {
    match e {
        ClightExpr::Etempvar(id, _) => tyvar.contains_key(&(*id as RTLReg)),
        ClightExpr::Ecast(inner, _) => cast_operand_is_inferable(inner, tyvar),
        _ => false,
    }
}

// True when e's inferred type term carries a free register variable, so a structural constraint on it is satisfiable; fully concrete forms are skipped and left to the emitter.
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

fn direct_known_global_type<'a>(
    known: &'a KnownGlobalTypes,
    e: &ClightExpr,
) -> Option<&'a ClightType> {
    match e {
        ClightExpr::Evar(id, _) => known.by_ident.get(id),
        _ => None,
    }
}

/// A typed term with freeness: Conc folds in Rust with no Z3 emission, Sym flows a free variable so obligations can steer a register type; freeness decides fold-vs-emit only.
enum TyTerm {
    Conc(ClightType),
    Sym(Dynamic),
}

impl TyTerm {
    pub(crate) fn is_sym(&self) -> bool {
        matches!(self, TyTerm::Sym(_))
    }
    pub(crate) fn term(&self, t: &TypeDt) -> Dynamic {
        match self {
            TyTerm::Conc(ct) => clight_to_ty(t, ct),
            TyTerm::Sym(d) => d.clone(),
        }
    }
}

// True when an obligation over these operands can steer the model (any free variable involved); concrete sites fold silently.
fn any_sym(parts: &[&TyTerm]) -> bool {
    parts.iter().any(|p| p.is_sym())
}

// The single operator-typing rule: returns the TyTerm of `e` and emits the classify-derived obligations its sub-expressions impose (Cop.v/Ctyping.v at the post-typeconv class level); `tyvar` holds each inferable register's free variable, non-inferable leaves fall back to their annotated type.
fn type_of(
    t: &TypeDt,
    tyvar: &HashMap<RTLReg, Dynamic>,
    sink: &RuleSink,
    guard: Option<&Bool>,
    func: &FunctionData,
    e: &ClightExpr,
) -> TyTerm {
    match e {
        ClightExpr::Etempvar(id, ct) => {
            match tyvar.get(&(*id as RTLReg)) {
                Some(tv) => {
                    // SEL-AGREE (class match): prefer the candidate whose annotation CLASS matches the register's model class, weight 2, so it outranks the candidate-[0] prior but yields to every semantic constraint.
                    {
                        let class_id: u8 = match ct {
                            ClightType::Tpointer(..) => 0,
                            ClightType::Tfloat(..) => 1,
                            ClightType::Tstruct(..) => 2,
                            ClightType::Tint(..) | ClightType::Tlong(..) => 3,
                            _ => u8::MAX,
                        };
                        if class_id != u8::MAX
                            && sink
                                .agree_seen
                                .borrow_mut()
                                .insert((*id as RTLReg, class_id))
                        {
                            let agree = match class_id {
                                0 => t.is_ptr(tv),
                                1 => t.is_float(tv),
                                2 => t.is_struct(tv),
                                _ => t.is_intish(tv),
                            };
                            sink.prefer(&agree, 2);
                        }
                    }
                    TyTerm::Sym(tv.clone())
                }
                None => TyTerm::Conc(ct.clone()),
            }
        }
        ClightExpr::EconstInt(_, ct)
        | ClightExpr::EconstLong(_, ct)
        | ClightExpr::EconstFloat(_, ct)
        | ClightExpr::EconstSingle(_, ct) => TyTerm::Conc(ct.clone()),
        ClightExpr::Evar(id, ct) => TyTerm::Conc(
            func.known_global_types
                .by_ident
                .get(id)
                .cloned()
                .unwrap_or_else(|| ct.clone()),
        ),
        ClightExpr::EvarSymbol(_, ct) => TyTerm::Conc(ct.clone()),
        ClightExpr::Ederef(inner, ct) => {
            let it = type_of(t, tyvar, sink, guard, func, inner);
            // deref requires a pointer and the result is the pointee; assert only when the base drives a free variable (on a concrete base it is redundant or forces whole-function UNSAT) -- the D1-frozen hard set.
            if base_drives_free_var(inner, tyvar) {
                sink.assert_structural(guard, &t.is_ptr(&it.term(t)));
            }
            match it {
                TyTerm::Sym(d) => TyTerm::Sym(t.pointee(&d)),
                TyTerm::Conc(c) => {
                    // Fold: pointer/array yield the element; anything else is the re-pick's business -- recover with the annotation.
                    match crate::decompile::passes::clight_select::ctyping::type_deref(&c) {
                        Some(elem) => TyTerm::Conc(elem),
                        None => TyTerm::Conc(ct.clone()),
                    }
                }
            }
        }
        ClightExpr::Eaddrof(inner, _) => {
            let it = type_of(t, tyvar, sink, guard, func, inner);
            match it {
                TyTerm::Sym(d) => TyTerm::Sym(t.ptr(&d)),
                TyTerm::Conc(c) => TyTerm::Conc(ClightType::Tpointer(
                    std::sync::Arc::new(c),
                    crate::x86::types::ClightAttr::default(),
                )),
            }
        }
        ClightExpr::Efield(base, _, ct) => {
            let bt = type_of(t, tyvar, sink, guard, func, base);
            // the field base (for `e.f`, or the pointee for `e->f` = (*p).f) must be a struct; assert only when it drives a free variable, for the same reason as deref above.
            if base_drives_free_var(base, tyvar) {
                sink.assert_structural(guard, &t.is_struct(&bt.term(t)));
            } else if matches!(
                base.as_ref(),
                ClightExpr::Evar(_, ClightType::Tstruct(..))
                    | ClightExpr::Etempvar(_, ClightType::Tstruct(..))
            ) {
                // A struct-VALUE member access whose base folds only to a concrete Tstruct annotation is the member-of-non-struct error, priced here so a raw byte-offset alternative wins; p->f is untouched.
                sink.penalize_candidate(8);
            }
            TyTerm::Conc(ct.clone())
        }
        ClightExpr::Ecast(inner, ct) => {
            let it = type_of(t, tyvar, sink, guard, func, inner);
            if it.is_sym() {
                let itm = it.term(t);
                // Casting a floating operand to a pointer is illegal C, enforced HARD for an inferable register but soft otherwise so a single-candidate node is not forced UNSAT.
                if matches!(ct, ClightType::Tpointer(..)) {
                    let not_float = t.is_float(&itm).not();
                    if cast_operand_is_inferable(inner, tyvar) {
                        sink.assert_structural(guard, &not_float);
                    } else {
                        sink.assert_soft_tagged(guard, &not_float, 8, "cast_to_ptr");
                    }
                }
                // A direct pointer-to-float cast is invalid C. ClightPass adds
                // an integer-bridge candidate for every machine
                // integer-register-to-float conversion whose source variant
                // is pointer-shaped, so rejecting the direct candidate HARD
                // is satisfiable even when a dereference fixes the register
                // as a pointer. Concrete/non-inferable operands remain soft:
                // there is no type variable for this clause to drive, and an
                // isolated single-candidate expression must report a
                // generation gap rather than make the whole function UNSAT.
                if matches!(ct, ClightType::Tfloat(..)) {
                    let not_ptr = t.is_ptrish(&itm).not();
                    if cast_operand_is_inferable(inner, tyvar) {
                        sink.assert_structural(guard, &not_ptr);
                    } else {
                        sink.assert_soft_tagged(guard, &not_ptr, 8, "cast_to_float");
                    }
                }
                // Remaining wt_cast mismatches (struct<->scalar, void source) are RECORDED-ONLY: the re-pick prices every cast exactly, and asserting these 16k+ clauses bought nothing.
                let tgt = clight_to_ty(t, ct);
                sink.prefer(&wt_cast_term(t, &itm, &tgt), 8);
                // The weight-1 SEL-AGREE cast-level pointerness nudge was retired as subsumed; the Sset-level and Etempvar class-match preferences are not subsumed and stay.
            } else if direct_known_global_type(func.known_global_types.as_ref(), inner).is_some() {
                // Concrete known globals carry an authoritative declaration
                // type. Unlike ordinary concrete annotations, a mismatch here
                // is actionable: ClightPass supplies a definition-local,
                // emitter-typed load alternative even when lifting began with
                // only a machine-chunk cast.
                let itm = it.term(t);
                let tgt = clight_to_ty(t, ct);
                sink.assert_soft_tagged(
                    guard,
                    &wt_cast_term(t, &itm, &tgt),
                    sink.compat_w,
                    "known_global_cast",
                );
            }
            TyTerm::Conc(ct.clone())
        }
        ClightExpr::Ebinop(op, l, r, ct) => {
            let lt = type_of(t, tyvar, sink, guard, func, l);
            let rt = type_of(t, tyvar, sink, guard, func, r);
            if any_sym(&[&lt, &rt]) {
                let ltm = lt.term(t);
                let rtm = rt.term(t);
                // A float-typed arithmetic node requires non-pointer operands, since p + 0.1f is an invalid-operands error nothing silences; dominant-soft like the float-cast rule above.
                if matches!(ct, ClightType::Tfloat(..)) {
                    sink.assert_soft_tagged(
                        guard,
                        &t.is_ptrish(&ltm).not(),
                        sink.compat_w,
                        "float_binop",
                    );
                    sink.assert_soft_tagged(
                        guard,
                        &t.is_ptrish(&rtm).not(),
                        sink.compat_w,
                        "float_binop",
                    );
                }
                // The integer mirror: an INT-annotated int-only op has integer operands by RTL construction, stronger than classify_binarith, which legally admits floats and let registers drift float.
                if matches!(
                    op,
                    ClightBinaryOp::Omul
                        | ClightBinaryOp::Odiv
                        | ClightBinaryOp::Omod
                        | ClightBinaryOp::Oand
                        | ClightBinaryOp::Oor
                        | ClightBinaryOp::Oxor
                        | ClightBinaryOp::Oshl
                        | ClightBinaryOp::Oshr
                ) && matches!(ct, ClightType::Tint(..) | ClightType::Tlong(..))
                {
                    if lt.is_sym() {
                        sink.assert_soft_tagged(
                            guard,
                            &t.is_intish(&ltm),
                            sink.compat_w,
                            "int_binop",
                        );
                    }
                    if rt.is_sym() {
                        sink.assert_soft_tagged(
                            guard,
                            &t.is_intish(&rtm),
                            sink.compat_w,
                            "int_binop",
                        );
                    }
                }
                // The pointer/float arm of binop legality is a hard requirement; the rest stays a dominant soft.
                assert_no_ptr_float_mix(t, sink, guard, &lt, &rt, &ltm, &rtm);
                sink.assert_soft_tagged(
                    guard,
                    &binop_legal_term(t, *op, &ltm, &rtm),
                    sink.compat_w,
                    "binop_legal",
                );
                // Pointer arithmetic carries the pointer operand's type so a deref of the result constrains the base's POINTEE; the pointer operand is itself inferred, so select it with ite.
                match op {
                    ClightBinaryOp::Oadd | ClightBinaryOp::Osub => {
                        // The result is a pointer ONLY if an operand is, so force a non-pointer fallback or a deref could be satisfied by the annotation and the base register would escape is_ptr.
                        let ann = match ct {
                            ClightType::Tpointer(..) => t.int(),
                            other => clight_to_ty(t, other),
                        };
                        let res = if matches!(op, ClightBinaryOp::Oadd) {
                            let inner = t.is_ptr(&rtm).ite(&rtm, &ann);
                            t.is_ptr(&ltm).ite(&ltm, &inner)
                        } else {
                            let both = Bool::and(&[t.is_ptr(&ltm), t.is_ptr(&rtm)]);
                            let l_only = t.is_ptr(&ltm).ite(&ltm, &ann);
                            both.ite(&t.int(), &l_only)
                        };
                        TyTerm::Sym(res)
                    }
                    _ => TyTerm::Conc(ct.clone()),
                }
            } else {
                // Fully concrete: fold (the re-pick prices any error); annotation is the result.
                TyTerm::Conc(ct.clone())
            }
        }
        ClightExpr::Eunop(op, inner, ct) => {
            let it = type_of(t, tyvar, sink, guard, func, inner);
            // type_unop legality (Ctyping.v:52): ! accepts any scalar; ~ integers only; -/__builtin_fabs numerics only. New in P4 -- previously unops were entirely unconstrained.
            if it.is_sym() {
                sink.assert_soft_tagged(
                    guard,
                    &unop_legal_term(t, *op, &it.term(t)),
                    sink.compat_w,
                    "unop_legal",
                );
            }
            TyTerm::Conc(ct.clone())
        }
        ClightExpr::Econdition(c, a, b, ct) => {
            let tc = type_of(t, tyvar, sink, guard, func, c);
            // wt_bool on the ?: condition (new in P4): struct/union/void-typed conditions are frontend errors.
            if tc.is_sym() {
                sink.assert_soft_tagged(
                    guard,
                    &t.is_boolish(&tc.term(t)),
                    sink.compat_w,
                    "cond_bool",
                );
            }
            let _ = type_of(t, tyvar, sink, guard, func, a);
            let _ = type_of(t, tyvar, sink, guard, func, b);
            TyTerm::Conc(ct.clone())
        }
        ClightExpr::Esizeof(_, ct) | ClightExpr::Ealignof(_, ct) => TyTerm::Conc(ct.clone()),
    }
}

// Walk a statement emitting operator-typing constraints, guarded so they bind only for the selected candidate; the old constrain_int_ops register scan is retired as subsumed.
fn constrain_stmt(
    t: &TypeDt,
    tyvar: &HashMap<RTLReg, Dynamic>,
    sink: &RuleSink,
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
            let lt = type_of(t, tyvar, sink, guard, func, lhs);
            let rt = type_of(t, tyvar, sink, guard, func, rhs);
            // `wt_cast` quite correctly accepts conversion *to* void for a
            // discarded-value cast, but an assignment destination must name
            // an object type.  Price a void pointee separately so both the
            // MaxSMT model and the fixed-model exact re-pick prefer a real
            // byte/word store whenever lifting supplied one.
            if lt.is_sym() || matches!(&lt, TyTerm::Conc(ClightType::Tvoid)) {
                sink.assert_soft_tagged(
                    guard,
                    &t.is_void(&lt.term(t)).not(),
                    compat_w,
                    "assign_lvalue_nonvoid",
                );
            }
            if any_sym(&[&lt, &rt]) {
                sink.assert_soft_tagged(
                    guard,
                    &wt_cast_term(t, &rt.term(t), &lt.term(t)),
                    compat_w,
                    "assign_compat",
                );
            }
        }
        ClightStmt::Sset(id, e) => {
            let rt = type_of(t, tyvar, sink, guard, func, e);
            if let Some(lv) = tyvar.get(&(*id as RTLReg)) {
                sink.assert_soft_tagged(
                    guard,
                    &wt_cast_to_reg(t, &rt.term(t), lv),
                    compat_w,
                    "set_compat",
                );
                // SEL-AGREE (Sset level): prefer an rhs whose pointerness matches the destination, weight 2, which also demotes a float rhs into a pointer destination that the wt count cannot foresee.
                sink.prefer(&ptr_class_eq(t, lv, &rt.term(t)), 2);
            }
        }
        ClightStmt::Scall(ret, f, args) => {
            let ft = type_of(t, tyvar, sink, guard, func, f);
            // classify_fun (new in P4): a call through a non-function object is a frontend error; steer a register-typed callee toward pointer-ness (the model has no fnptr pointee discipline beyond ptrish).
            if ft.is_sym() {
                sink.assert_soft_tagged(guard, &t.is_ptrish(&ft.term(t)), compat_w, "callee_fun");
            }
            // Cross-function: bind each argument and the result to the callee's signature.
            let sig = callee_ident_from_expr(f, name_to_ident)
                .and_then(|id| func.callee_signatures.get(&id));
            for (i, a) in args.iter().enumerate() {
                let at = type_of(t, tyvar, sink, guard, func, a);
                if at.is_sym() {
                    if let Some(sig) = sig {
                        if let Some(pt) = sig.param_types.get(i) {
                            let want = xtype_to_ty(t, pt);
                            sink.assert_soft_tagged(
                                guard,
                                &wt_cast_term(t, &at.term(t), &want),
                                compat_w,
                                "call_arg",
                            );
                        }
                    }
                }
            }
            if let (Some(rid), Some(sig)) = (ret, sig) {
                if let Some(lv) = tyvar.get(&(*rid as RTLReg)) {
                    let want = xtype_to_ty(t, &sig.return_type);
                    sink.assert_soft_tagged(
                        guard,
                        &wt_cast_to_reg(t, &want, lv),
                        compat_w,
                        "call_ret",
                    );
                }
            }
            // return/void agreement (caller side): capturing the result of a void callee yields "void value not ignored as it ought to be", so when this call is a refinable candidate, penalize the result-capturing form so a non-capturing candidate is chosen.
            if let (Some(_), Some(sig)) = (ret, sig) {
                if matches!(sig.return_type, XType::Xvoid) {
                    if let Some(g) = guard {
                        sink.assert_soft_raw(&g.not(), compat_w);
                        sink.penalize_candidate(compat_w);
                    }
                }
            }
        }
        ClightStmt::Sreturn(ret) => {
            // return/void agreement on the callee side: a value-return in a void function or a valueless return in a non-void one is a frontend error, so penalize the mismatching form.
            let is_void_fn = matches!(func.return_type, ClightType::Tvoid);
            match ret {
                Some(e) => {
                    let et = type_of(t, tyvar, sink, guard, func, e);
                    if et.is_sym() {
                        sink.assert_soft_tagged(
                            guard,
                            &wt_cast_term(t, &et.term(t), func_ret),
                            compat_w,
                            "ret_compat",
                        );
                    }
                    if is_void_fn {
                        if let Some(g) = guard {
                            sink.assert_soft_raw(&g.not(), compat_w);
                            sink.penalize_candidate(compat_w);
                        }
                    }
                }
                None => {
                    if !is_void_fn {
                        if let Some(g) = guard {
                            sink.assert_soft_raw(&g.not(), compat_w);
                            sink.penalize_candidate(compat_w);
                        }
                    }
                }
            }
        }
        ClightStmt::Sifthenelse(c, a, b) => {
            let tc = type_of(t, tyvar, sink, guard, func, c);
            // wt_bool on the branch condition (new in P4): struct/union/void conditions are frontend errors.
            if tc.is_sym() {
                sink.assert_soft_tagged(guard, &t.is_boolish(&tc.term(t)), compat_w, "if_bool");
            }
            constrain_stmt(
                t,
                tyvar,
                sink,
                guard,
                func,
                name_to_ident,
                func_ret,
                compat_w,
                a,
            );
            constrain_stmt(
                t,
                tyvar,
                sink,
                guard,
                func,
                name_to_ident,
                func_ret,
                compat_w,
                b,
            );
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss {
                constrain_stmt(
                    t,
                    tyvar,
                    sink,
                    guard,
                    func,
                    name_to_ident,
                    func_ret,
                    compat_w,
                    s,
                );
            }
        }
        ClightStmt::Sloop(a, b) => {
            constrain_stmt(
                t,
                tyvar,
                sink,
                guard,
                func,
                name_to_ident,
                func_ret,
                compat_w,
                a,
            );
            constrain_stmt(
                t,
                tyvar,
                sink,
                guard,
                func,
                name_to_ident,
                func_ret,
                compat_w,
                b,
            );
        }
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => {
            constrain_stmt(
                t,
                tyvar,
                sink,
                guard,
                func,
                name_to_ident,
                func_ret,
                compat_w,
                inner,
            );
        }
        ClightStmt::Sswitch(e, cases) => {
            let te = type_of(t, tyvar, sink, guard, func, e);
            // classify_switch (new in P4): the scrutinee must be an integer.
            if te.is_sym() {
                sink.assert_soft_tagged(guard, &t.is_intish(&te.term(t)), compat_w, "switch_int");
            }
            for (_, s) in cases {
                constrain_stmt(
                    t,
                    tyvar,
                    sink,
                    guard,
                    func,
                    name_to_ident,
                    func_ret,
                    compat_w,
                    s,
                );
            }
        }
        _ => {}
    }
}

// Render a model's inferred Ty for reg as a candidate type; allow_void permits ptr_void only when the register is never a deref/field base. CLASS-level renders only, widths chosen at anchor_index.
pub(crate) fn render_type(
    t: &TypeDt,
    model: &dyn ModelView,
    tv: &Dynamic,
    reg: RTLReg,
    func: &FunctionData,
    allow_void: bool,
) -> CandType {
    let truth = |b: Bool| model.truth(&b).unwrap_or(false);
    if truth(t.is_ptr(tv)) {
        let p = t.pointee(tv);
        if truth(t.is_struct(&p)) {
            if let Some(&sid) = func.reg_struct_ids.get(&reg) {
                return CandType::PtrStruct(sid);
            }
            // sid from the model if upstream didn't record one. The Z3 Int is the `as i64` image
            // of a usize sid, so map it back the same way rather than dropping the high bit.
            if let Some(sid) = model.integer(&t.struct_sid(&p)) {
                return CandType::PtrStruct(sid as usize);
            }
            return CandType::PtrLong;
        }
        if truth(t.is_float(&p)) {
            return CandType::PtrDouble;
        }
        if truth(t.is_func(&p)) {
            return CandType::PtrFunc;
        }
        if allow_void && truth(t.is_void(&p)) {
            return CandType::PtrVoid;
        }
        return CandType::PtrLong;
    }
    if truth(t.is_float(tv)) {
        return CandType::F64;
    }
    CandType::I64(Sign::Signed)
}

// Pick the candidate index best matching the rendered inferred type; None means genuinely-new type (carry as override). `allow_void` mirrors render_type's license: ptr_void anchoring requires the register is never deref/field-based.
pub(crate) fn anchor_index(
    cands: &[CandType],
    rendered: CandType,
    allow_void: bool,
) -> Option<usize> {
    // The Ty algebra carries classes only, so render_type spells EVERY integer `int_I64`. Matching
    // that literally makes the spelling beat an equally wide candidate that differs from it only in
    // signedness -- a dimension the model cannot represent and the render therefore cannot mean.
    // Within the integer class, match on width instead and let the priority-sorted candidate order
    // (which does carry the upstream sign evidence) pick. Width still binds, so a narrow candidate
    // is never widened onto or narrowed into.
    if rendered.is_integer() {
        if let Some(i) = cands
            .iter()
            .position(|c| c.is_integer() && c.width() == rendered.width())
        {
            return Some(i);
        }
    }
    // ptr_void without the license emits an incomplete pointee that can't be deref-assigned; fall through to prefer a complete scalar pointer.
    if rendered != CandType::PtrVoid || allow_void {
        if let Some(i) = cands.iter().position(|c| *c == rendered) {
            return Some(i);
        }
    }
    // Classes: struct-pointer is distinct from scalar/generic pointer, so a scalar-pointer inference never anchors back onto a `ptr_struct` candidate (which would reintroduce the struct mismatch).
    let rc = rendered.class();
    if rc == CandClass::Ptr {
        // A scalar/generic pointer: prefer a COMPLETE pointee (int*/long*/char*) over void* (incomplete, not assignable through); only fall back to ptr_void if nothing complete is available.
        for pref in [CandType::PtrLong, CandType::PtrInt, CandType::PtrChar] {
            if let Some(i) = cands.iter().position(|c| *c == pref) {
                return Some(i);
            }
        }
        if let Some(i) = cands
            .iter()
            .position(|c| c.class() == CandClass::Ptr && *c != CandType::PtrVoid)
        {
            return Some(i);
        }
        // ptr_void is still a pointer-class anchor when nothing with a complete pointee is available.
        return cands.iter().position(|c| *c == CandType::PtrVoid);
    }
    // Same class, no exact width: take nearest-width candidate; ties break to the earlier (higher-priority) index.
    let rw = rendered.width();
    cands
        .iter()
        .enumerate()
        .filter(|(_, c)| c.class() == rc)
        .min_by_key(|(i, c)| (c.width().abs_diff(rw), *i))
        .map(|(i, _)| i)
}
