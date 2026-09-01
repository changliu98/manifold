use rayon::prelude::*;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;
use std::sync::Arc;

use z3::ast::{Bool, Dynamic, Int};
use z3::{DatatypeAccessor, DatatypeBuilder, DatatypeSort, Optimize, SatResult, Sort};

use crate::decompile::elevator::config::CONFIG;
use crate::decompile::passes::clight_select::candtype::{CandClass, CandType, Sign};
use crate::decompile::passes::clight_select::propagator::{
    RawModel, RawSolver, Theory, VetoTheory,
};
use crate::decompile::passes::clight_select::query::{
    CalleeSignature, CommittedInterfaces, FunctionData, InterfaceClass, KnownGlobalTypes,
};
use crate::decompile::passes::clight_select::select::{
    callee_ident_from_expr, ProgramSelectionState,
};
use crate::x86::types::{
    Address, ClightBinaryOp, ClightExpr, ClightIntSize, ClightStmt, ClightType, Ident, Node,
    ParamType, RTLReg, XType,
};

// Variant order in the Ty datatype; indices into DatatypeSort::variants.
const V_VOID: usize = 0;
const V_INT: usize = 1;
const V_FLOAT: usize = 2;
const V_STRUCT: usize = 3;
const V_UNION: usize = 4;
const V_FUNC: usize = 5;
const V_PTR: usize = 6;

// Per-Context handles to the recursive Ty datatype; the algebra models type CLASSES only, since width/signedness payloads carried no constraint information and exploded maxres.
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
            .variant("union", vec![("uid", DatatypeAccessor::Sort(Sort::int()))])
            .variant("func", vec![])
            .variant("ptr", vec![("pointee", DatatypeAccessor::datatype("Ty"))])
            .finish();
        TypeDt { dt }
    }

    fn void(&self) -> Dynamic {
        self.dt.variants[V_VOID].constructor.apply(&[])
    }
    fn int(&self) -> Dynamic {
        self.dt.variants[V_INT].constructor.apply(&[])
    }
    fn float(&self) -> Dynamic {
        self.dt.variants[V_FLOAT].constructor.apply(&[])
    }
    fn struct_(&self, sid: i64) -> Dynamic {
        self.dt.variants[V_STRUCT]
            .constructor
            .apply(&[&Int::from_i64(sid)])
    }
    fn union_(&self, uid: i64) -> Dynamic {
        self.dt.variants[V_UNION]
            .constructor
            .apply(&[&Int::from_i64(uid)])
    }
    fn func(&self) -> Dynamic {
        self.dt.variants[V_FUNC].constructor.apply(&[])
    }
    fn ptr(&self, pointee: &Dynamic) -> Dynamic {
        self.dt.variants[V_PTR].constructor.apply(&[pointee])
    }

    fn is_void(&self, x: &Dynamic) -> Bool {
        self.dt.variants[V_VOID]
            .tester
            .apply(&[x])
            .as_bool()
            .unwrap()
    }
    fn is_int(&self, x: &Dynamic) -> Bool {
        self.dt.variants[V_INT]
            .tester
            .apply(&[x])
            .as_bool()
            .unwrap()
    }
    fn is_float(&self, x: &Dynamic) -> Bool {
        self.dt.variants[V_FLOAT]
            .tester
            .apply(&[x])
            .as_bool()
            .unwrap()
    }
    fn is_struct(&self, x: &Dynamic) -> Bool {
        self.dt.variants[V_STRUCT]
            .tester
            .apply(&[x])
            .as_bool()
            .unwrap()
    }
    fn is_union(&self, x: &Dynamic) -> Bool {
        self.dt.variants[V_UNION]
            .tester
            .apply(&[x])
            .as_bool()
            .unwrap()
    }
    fn is_func(&self, x: &Dynamic) -> Bool {
        self.dt.variants[V_FUNC]
            .tester
            .apply(&[x])
            .as_bool()
            .unwrap()
    }
    fn is_ptr(&self, x: &Dynamic) -> Bool {
        self.dt.variants[V_PTR]
            .tester
            .apply(&[x])
            .as_bool()
            .unwrap()
    }
    fn pointee(&self, x: &Dynamic) -> Dynamic {
        self.dt.variants[V_PTR].accessors[0].apply(&[x])
    }
    fn struct_sid(&self, x: &Dynamic) -> Dynamic {
        self.dt.variants[V_STRUCT].accessors[0].apply(&[x])
    }

    // The post-typeconv integer universe (one class on this algebra).
    fn is_intish(&self, x: &Dynamic) -> Bool {
        self.is_int(x)
    }
    // Arithmetic class: int/float -- what classify_binarith accepts.
    fn is_arith(&self, x: &Dynamic) -> Bool {
        Bool::or(&[self.is_int(x), self.is_float(x)])
    }
    // Pointer-shaped after decay: a pointer or a function (functions decay).
    fn is_ptrish(&self, x: &Dynamic) -> Bool {
        Bool::or(&[self.is_ptr(x), self.is_func(x)])
    }
    // classify_bool: int/float/ptr accept, struct/union/void reject.
    fn is_boolish(&self, x: &Dynamic) -> Bool {
        Bool::or(&[self.is_arith(x), self.is_ptrish(x)])
    }

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
        XType::Xfloatptr | XType::Xsingleptr => t.ptr(&t.float()),
        XType::Xfuncptr => t.ptr(&t.func()),
        XType::Xptr | XType::Xcharptr | XType::Xcharptrptr | XType::Xintptr => t.ptr(&t.int()),
        _ => t.int(),
    }
}

// ClightType (expression annotations) -> a concrete Ty term at OPERATOR positions: typeconv applies (the whole integer family collapses to the int class, arrays decay, function decay is handled via classify_fun's ptrish acceptance).
fn clight_to_ty(t: &TypeDt, ct: &ClightType) -> Dynamic {
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
fn cand_to_ty(t: &TypeDt, candidate: CandType) -> Dynamic {
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
fn wt_cast_term(t: &TypeDt, from: &Dynamic, to: &Dynamic) -> Bool {
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
fn wt_cast_to_reg(t: &TypeDt, from: &Dynamic, lv: &Dynamic) -> Bool {
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
fn binop_legal_term(t: &TypeDt, op: ClightBinaryOp, ltm: &Dynamic, rtm: &Dynamic) -> Bool {
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
fn no_ptr_float_term(t: &TypeDt, ptr_side: &Dynamic, float_side: &Dynamic) -> Bool {
    Bool::and(&[t.is_ptrish(ptr_side), t.is_float(float_side)]).not()
}

fn assert_no_ptr_float_mix(
    t: &TypeDt,
    sink: &ConstraintSink,
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
fn unop_legal_term(t: &TypeDt, op: crate::x86::types::ClightUnaryOp, itm: &Dynamic) -> Bool {
    use crate::x86::types::ClightUnaryOp::*;
    match op {
        Onotbool => t.is_boolish(itm),
        Onotint => t.is_intish(itm),
        Oneg | Oabsfloat => t.is_arith(itm),
    }
}

/// One recorded condition for the post-solve per-node re-pick: the raw (unguarded) condition (None = an unconditional penalty for this candidate) and its weight; weight u64::MAX marks a structural requirement (validity, not preference).
type RecordedCond = (Option<Bool>, u64);

// Where a built constraint lands. Both engines build the SAME formula through this: the Optimize engine hands softs to MaxSMT, the propagator engine attaches a relaxation literal per soft and minimizes them itself.
trait SolveBackend {
    fn assert_hard(&self, cond: &Bool);
    fn assert_soft(&self, cond: &Bool, weight: u64);
}

struct OptimizeBackend<'a> {
    opt: &'a Optimize,
    // Recorded only so the A/B can price this engine's model on the same scale as the other's; never read by the search itself.
    softs: RefCell<Vec<(Bool, u64)>>,
}

impl<'a> OptimizeBackend<'a> {
    fn new(opt: &'a Optimize) -> Self {
        OptimizeBackend {
            opt,
            softs: RefCell::new(Vec::new()),
        }
    }

    fn into_softs(self) -> Vec<(Bool, u64)> {
        self.softs.into_inner()
    }
}

impl SolveBackend for OptimizeBackend<'_> {
    fn assert_hard(&self, cond: &Bool) {
        self.opt.assert(cond);
    }
    fn assert_soft(&self, cond: &Bool, weight: u64) {
        self.opt.assert_soft(cond, weight, None);
        self.softs.borrow_mut().push((cond.clone(), weight));
    }
}

// Soft clause `c` at weight `w` becomes the hard clause `c \/ r` with a fresh relaxation literal `r`; `r` true means `c` is violated, so minimizing the r's minimizes the MaxSAT cost.
struct RelaxBackend<'a> {
    solver: &'a RawSolver,
    softs: RefCell<Vec<(Bool, Bool, u64)>>,
}

impl<'a> RelaxBackend<'a> {
    fn new(solver: &'a RawSolver) -> Self {
        RelaxBackend {
            solver,
            softs: RefCell::new(Vec::new()),
        }
    }

    fn into_softs(self) -> Vec<(Bool, Bool, u64)> {
        self.softs.into_inner()
    }
}

impl SolveBackend for RelaxBackend<'_> {
    fn assert_hard(&self, cond: &Bool) {
        self.solver.assert(cond);
    }
    fn assert_soft(&self, cond: &Bool, weight: u64) {
        let relax = Bool::fresh_const("r");
        self.solver
            .assert(&Bool::or(&[cond.clone(), relax.clone()]));
        self.softs.borrow_mut().push((cond.clone(), relax, weight));
    }
}

// The MaxSAT objective of a model, priced identically for both engines: the total weight of the soft clauses it violates, plus the per-weight-class violation counts the stratified loop optimizes.
fn weighted_cost(model: &dyn ModelView, softs: &[(Bool, u64)]) -> (u64, BTreeMap<u64, usize>) {
    let mut total = 0u64;
    let mut per_class: BTreeMap<u64, usize> = BTreeMap::new();
    for (clause, weight) in softs {
        if model.truth(clause) == Some(false) {
            total = total.saturating_add(*weight);
            *per_class.entry(*weight).or_default() += 1;
        }
    }
    (total, per_class)
}

// Diagnostic only, never changes output: prints the model's objective so an A/B run can compare the two engines' optima directly.
fn report_cost(engine: &str, func: &FunctionData, model: &dyn ModelView, softs: &[(Bool, u64)]) {
    if std::env::var("MANIFOLD_SOLVER_COST").is_err() {
        return;
    }
    let (total, per_class) = weighted_cost(model, softs);
    let breakdown = per_class
        .iter()
        .rev()
        .map(|(w, n)| format!("{w}x{n}"))
        .collect::<Vec<_>>()
        .join(" ");
    eprintln!(
        "[cost] {} {:#x} engine={} softs={} total={} [{}]",
        func.name,
        func.address,
        engine,
        softs.len(),
        total,
        breakdown
    );
}

// The model reads the selection needs, over either engine's model representation.
trait ModelView {
    fn truth(&self, cond: &Bool) -> Option<bool>;
    fn integer(&self, term: &Dynamic) -> Option<i64>;
}

impl ModelView for z3::Model {
    fn truth(&self, cond: &Bool) -> Option<bool> {
        self.eval(cond, true).and_then(|x| x.as_bool())
    }
    fn integer(&self, term: &Dynamic) -> Option<i64> {
        self.eval(term, true)
            .and_then(|x| x.as_int())
            .and_then(|i| i.as_i64())
    }
}

impl ModelView for RawModel {
    fn truth(&self, cond: &Bool) -> Option<bool> {
        self.eval_bool(cond)
    }
    fn integer(&self, term: &Dynamic) -> Option<i64> {
        self.eval_i64(term)
    }
}

// Z3 is the sole selector: structural requirements are always HARD; there is no relaxed retry and no non-Z3 fallback (a function whose constraints are UNSAT yields no selection and signals an upstream candidate-generation bug).
struct ConstraintSink<'a> {
    backend: &'a dyn SolveBackend,
    // The per-function dominant soft weight (compat_w); carried here so the operator-typing rules in `type_of` can emit dominant-soft requirements without threading the weight through every recursive call.
    compat_w: u64,
    // Per-candidate dedup for the SEL-AGREE Etempvar class-match preference: a register read N times with the same annotation class in one candidate statement needs ONE preference, not N. Cleared by begin_candidate().
    agree_seen: RefCell<HashSet<(RTLReg, u8)>>,
    // Re-pick recording for multi-candidate nodes: every emitted condition is logged RAW and re-scored in Rust under the fixed model, since node selections are conditionally independent given it.
    record: RefCell<Option<Vec<RecordedCond>>>,
    // Per-function (guard, cond, weight) dedup for the OPTIMIZER side only: identical obligations carry the same MaxSMT meaning, and clause COUNT is the cost driver.
    asserted: RefCell<HashSet<(Option<Bool>, Bool, u64)>>,
}

impl<'a> ConstraintSink<'a> {
    fn new(backend: &'a dyn SolveBackend, compat_w: u64) -> Self {
        ConstraintSink {
            backend,
            compat_w,
            agree_seen: RefCell::new(HashSet::new()),
            record: RefCell::new(None),
            asserted: RefCell::new(HashSet::new()),
        }
    }

    // True exactly once per distinct (guard, cond, w) within this function.
    fn first_assert(&self, guard: Option<&Bool>, cond: &Bool, w: u64) -> bool {
        self.asserted
            .borrow_mut()
            .insert((guard.cloned(), cond.clone(), w))
    }

    // Open a fresh per-candidate scope: resets the class-match preference dedup and (for multi-candidate nodes) starts recording conditions for the post-solve re-pick.
    fn begin_candidate(&self, recording: bool) {
        self.agree_seen.borrow_mut().clear();
        *self.record.borrow_mut() = if recording { Some(Vec::new()) } else { None };
    }

    // Close the per-candidate scope, returning the recorded conditions.
    fn take_recorded(&self) -> Vec<RecordedCond> {
        self.record.borrow_mut().take().unwrap_or_default()
    }

    fn log(&self, cond: Option<&Bool>, w: u64) {
        if let Some(buf) = self.record.borrow_mut().as_mut() {
            buf.push((cond.cloned(), w));
        }
    }

    // A selection preference: never asserted into the optimizer, only recorded for the post-solve re-pick (no-op outside a recording scope -- with a single candidate there is nothing to prefer).
    fn prefer(&self, cond: &Bool, w: u64) {
        self.log(Some(cond), w);
    }

    // An unconditional penalty against the current candidate (e.g. capturing a void callee's result); recorded for the re-pick alongside its z3 assertion.
    fn penalize_candidate(&self, w: u64) {
        self.log(None, w);
    }

    // A structural requirement: always hard.
    fn assert_structural(&self, guard: Option<&Bool>, cond: &Bool) {
        self.log(Some(cond), u64::MAX);
        if !self.first_assert(guard, cond, u64::MAX) {
            return;
        }
        let c = match guard {
            Some(g) => g.implies(cond.clone()),
            None => cond.clone(),
        };
        self.backend.assert_hard(&c);
    }

    fn assert_soft_tagged(&self, guard: Option<&Bool>, cond: &Bool, w: u64, tag: &'static str) {
        self.log(Some(cond), w);
        if !self.first_assert(guard, cond, w) {
            return;
        }
        SOFT_CLAUSES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        soft_tag_count(tag);
        match guard {
            Some(g) => self.backend.assert_soft(&g.implies(cond.clone()), w),
            None => self.backend.assert_soft(cond, w),
        }
    }

    // Soft assertion on a raw Bool (the candidate-penalty `!guard` forms and the priors).
    fn assert_soft_raw(&self, cond: &Bool, w: u64) {
        SOFT_CLAUSES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.backend.assert_soft(cond, w);
    }
}

// Run-wide asserted-soft-clause counter (P4 perf early-warning, CTYPING_PLAN D2: MaxSMT cost scales with conflicting soft-clause count -- the 15x lesson). Swap-reset and reported by infer_select_program.
static SOFT_CLAUSES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
// Construction-vs-solve attribution for the P4 perf gate.
static BUILD_NS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static CHECK_NS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

// Per-family soft-clause breakdown behind MANIFOLD_SOFT_BREAKDOWN (perf triage).
static SOFT_TAGS: std::sync::LazyLock<std::sync::Mutex<BTreeMap<&'static str, usize>>> =
    std::sync::LazyLock::new(|| std::sync::Mutex::new(BTreeMap::new()));

fn soft_tag_count(tag: &'static str) {
    if std::env::var("MANIFOLD_SOFT_BREAKDOWN").is_ok() {
        *SOFT_TAGS.lock().unwrap().entry(tag).or_default() += 1;
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
    fn is_sym(&self) -> bool {
        matches!(self, TyTerm::Sym(_))
    }
    fn term(&self, t: &TypeDt) -> Dynamic {
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
    sink: &ConstraintSink,
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
        ClightStmt::Slabel(_, inner) => {
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
fn render_type(
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
fn anchor_index(cands: &[CandType], rendered: CandType, allow_void: bool) -> Option<usize> {
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

// Z3-only solve: a Sat model IS the selection, and UNSAT gives no selection so the consumer keeps upstream defaults; there is deliberately no relaxed retry, since UNSAT is an upstream bug.
fn solve_function(
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    maximal_flow_certification: bool,
) -> (
    HashMap<Node, Option<usize>>,
    HashMap<RTLReg, usize>,
    HashMap<RTLReg, CandType>,
    u8,
) {
    match solve_function_engine(func, name_to_ident, &[], maximal_flow_certification) {
        Ok((c, ty, ov, structure_world, grade)) => {
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
            (c, ty, ov, structure_world)
        }
        Err(first) => {
            TYPE_SOLVE_NO_MODEL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            eprintln!(
                "[clight-select] WARN: type solve for {} ({:#x}) produced no model ({}); emitting no selection, upstream defaults apply ({} nodes, {} regs)",
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
            (
                HashMap::new(),
                HashMap::new(),
                HashMap::new(),
                func.authoritative_structure_world,
            )
        }
    }
}

// Everything the constraint build produces that a model has to be read against; shared verbatim by both engines.
struct BuiltFunction {
    t: TypeDt,
    regs: Vec<RTLReg>,
    tyvar: HashMap<RTLReg, Dynamic>,
    structure_worlds: Vec<u8>,
    structure_world_var: HashMap<u8, Bool>,
    nodes: Vec<Node>,
    selvar: HashMap<Node, Vec<Bool>>,
    recorded: HashMap<Node, Vec<Vec<RecordedCond>>>,
}

// The single constraint build, engine-independent: identical hard constraints and identical soft families whichever backend consumes them.
fn build_function_constraints(
    t: TypeDt,
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    interface_pins: &[(RTLReg, XType)],
    backend: &dyn SolveBackend,
) -> BuiltFunction {
    {
        // Free type variable per inferable register (deterministic order).
        let mut regs: Vec<RTLReg> = func.var_type_candidates.keys().copied().collect();
        regs.sort();
        let mut tyvar: HashMap<RTLReg, Dynamic> = HashMap::new();
        for &reg in &regs {
            let tv = t.fresh();
            // Domain pruning: a register decl never renders as bare func/void/union (render_type falls back to int_I64), so excluding those variants HARD shrinks every clause's search space at zero MaxSMT cost and lets the Sset compat formula drop their arms (wt_cast_to_reg).
            backend.assert_hard(&t.is_func(&tv).not());
            backend.assert_hard(&t.is_void(&tv).not());
            backend.assert_hard(&t.is_union(&tv).not());
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
                backend.assert_hard(&t.is_ptr(&tv));
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
                backend.assert_hard(&t.is_float(&tv).not());
            }
            tyvar.insert(reg, tv);
        }
        // Stage-C only: the committed own-interface class is a hard input to
        // the dirty re-solve.  Stage A passes an empty slice and remains
        // byte-identical, including compat_w and variable counts.
        for (reg, xtype) in interface_pins {
            if let Some(variable) = tyvar.get(reg) {
                backend.assert_hard(&variable._eq(xtype_to_ty(&t, xtype)));
            }
        }

        // Diagnostic: dump the candidates the lifting pass produced for a target function (by name substring), to distinguish "correct candidate absent (lifting bug)" from "present but not selected (selector bug)".
        if std::env::var("MANIFOLD_DUMP_CANDS")
            .map(|s| !s.is_empty() && func.name.contains(&s))
            .unwrap_or(false)
        {
            eprintln!("=== CANDS fn={} addr={:#x} ===", func.name, func.address);
            for &reg in &regs {
                let nm = crate::decompile::passes::c_pass::helpers::param_name_for_reg(reg);
                eprintln!(
                    "  {} (reg {:#x}): {:?}",
                    nm, reg, func.var_type_candidates[&reg]
                );
            }
            let mut ns: Vec<Node> = func.node_statements.keys().copied().collect();
            ns.sort();
            for n in &ns {
                let stmts = &func.node_statements[n];
                let dbg = format!("{:?}", stmts);
                if stmts.len() > 1 || dbg.contains("Ederef") {
                    eprintln!("  node {:#x} ({} cand stmts):", n, stmts.len());
                    for (i, s) in stmts.iter().enumerate() {
                        eprintln!(
                            "    [{}] worlds={:?} {:?}",
                            i,
                            func.candidate_structure_worlds
                                .get(n)
                                .and_then(|masks| masks.get(i)),
                            s
                        );
                    }
                }
            }
        }

        // Function-level structure worlds are one-hot.  Statement choices are
        // then guarded by their world provenance, so an Sswitch can never be
        // combined with raw comparison-chain members and flat back edges can
        // never enter an assembled loop.
        let mut structure_worlds = func.structure_worlds.clone();
        structure_worlds.sort_unstable();
        structure_worlds.dedup();
        if structure_worlds.is_empty() {
            structure_worlds.push(func.authoritative_structure_world);
        }
        if let Some(position) = structure_worlds
            .iter()
            .position(|world| *world == func.authoritative_structure_world)
        {
            structure_worlds.swap(0, position);
        } else {
            structure_worlds.insert(0, func.authoritative_structure_world);
        }
        let mut structure_world_var: HashMap<u8, Bool> = HashMap::new();
        if structure_worlds.len() > 1 {
            let vars: Vec<Bool> = structure_worlds
                .iter()
                .map(|_| Bool::fresh_const("structure_world"))
                .collect();
            let refs: Vec<(&Bool, i32)> = vars.iter().map(|var| (var, 1)).collect();
            backend.assert_hard(&Bool::pb_eq(&refs, 1));
            for (&world, var) in structure_worlds.iter().zip(vars) {
                structure_world_var.insert(world, var);
            }
        }

        // Statement-selection booleans are also needed for a one-candidate
        // node that is absent from one world: false means the chosen world
        // omits that node entirely.
        let mut nodes: Vec<Node> = func.node_statements.keys().copied().collect();
        nodes.sort();
        let mut selvar: HashMap<Node, Vec<Bool>> = HashMap::new();
        let all_worlds: BTreeSet<u8> = structure_worlds.iter().copied().collect();
        for &node in &nodes {
            let m = func.node_statements[&node].len();
            let masks = func
                .candidate_structure_worlds
                .get(&node)
                .cloned()
                .unwrap_or_else(|| vec![all_worlds.clone(); m]);
            let world_conditional = structure_worlds.len() > 1
                && (masks.len() != m || masks.iter().any(|mask| mask != &all_worlds));
            if m > 1 || world_conditional {
                let vars: Vec<Bool> = (0..m).map(|_| Bool::fresh_const("s")).collect();
                if structure_worlds.len() == 1 {
                    let refs: Vec<(&Bool, i32)> = vars.iter().map(|b| (b, 1)).collect();
                    backend.assert_hard(&Bool::pb_eq(&refs, 1));
                } else {
                    for (candidate, selected) in vars.iter().enumerate() {
                        let allowed = masks.get(candidate).unwrap_or(&all_worlds);
                        let allowed_vars: Vec<Bool> = allowed
                            .iter()
                            .filter_map(|world| structure_world_var.get(world).cloned())
                            .collect();
                        if allowed_vars.is_empty() {
                            backend.assert_hard(&selected.not());
                        } else {
                            backend.assert_hard(&selected.implies(Bool::or(&allowed_vars)));
                        }
                    }
                    for world in &structure_worlds {
                        let allowed_candidates: Vec<(&Bool, i32)> = vars
                            .iter()
                            .enumerate()
                            .filter(|(candidate, _)| {
                                masks.get(*candidate).unwrap_or(&all_worlds).contains(world)
                            })
                            .map(|(_, selected)| (selected, 1))
                            .collect();
                        if !allowed_candidates.is_empty() {
                            backend.assert_hard(
                                &structure_world_var[world]
                                    .implies(Bool::pb_eq(&allowed_candidates, 1)),
                            );
                        }
                    }
                }
                selvar.insert(node, vars);
            }
        }

        let func_ret = match &func.return_type {
            ClightType::Tvoid => t.void(),
            other => clight_to_ty(&t, other),
        };

        // Weight strata must remain identical to the authoritative pipeline.
        // World-conditional singleton nodes and flat-only alternatives are a
        // representation expansion, not new baseline choices; counting them
        // in compat_w changes unrelated candidate/type optima even when world
        // zero wins.  Count only nodes that were genuinely refinable inside
        // the authoritative world.
        let authoritative_refinable_nodes = nodes
            .iter()
            .filter(|node| {
                func.candidate_structure_worlds.get(node).map_or(
                    func.node_statements[node].len() > 1,
                    |masks| {
                        masks
                            .iter()
                            .filter(|worlds| worlds.contains(&func.authoritative_structure_world))
                            .count()
                            > 1
                    },
                )
            })
            .count();
        // Weight strata: priors 1 < SEL-AGREE 2 < cast nudges 8 < dominant
        // compat_w.  Preserve the pre-world formula exactly.
        let compat_w: u64 = (regs.len() + authoritative_refinable_nodes) as u64 + 1;
        let sink = ConstraintSink::new(backend, compat_w);

        // Emit constraints for every candidate statement, guarded by its selection boolean when refinable; multi-candidate nodes also record their conditions for the post-solve re-pick.
        let mut recorded: HashMap<Node, Vec<Vec<RecordedCond>>> = HashMap::new();
        for &node in &nodes {
            let cands = &func.node_statements[&node];
            match selvar.get(&node) {
                Some(vars) => {
                    let mut per_cand = Vec::with_capacity(cands.len());
                    for (ci, stmt) in cands.iter().enumerate() {
                        sink.begin_candidate(true);
                        constrain_stmt(
                            &t,
                            &tyvar,
                            &sink,
                            Some(&vars[ci]),
                            func,
                            name_to_ident,
                            &func_ret,
                            compat_w,
                            stmt,
                        );
                        per_cand.push(sink.take_recorded());
                    }
                    recorded.insert(node, per_cand);
                }
                None => {
                    sink.begin_candidate(false);
                    constrain_stmt(
                        &t,
                        &tyvar,
                        &sink,
                        None,
                        func,
                        name_to_ident,
                        &func_ret,
                        compat_w,
                        &cands[0],
                    );
                }
            }
        }

        // Soft provenance: prefer each register's priority-0 candidate type, and the priority-0 statement.
        for &reg in &regs {
            if let Some(&c0) = func.var_type_candidates[&reg].first() {
                let prior = cand_to_ty(&t, c0);
                sink.assert_soft_raw(&tyvar[&reg]._eq(prior), 1u64);
            }
        }
        let mut sel_nodes: Vec<Node> = selvar.keys().copied().collect();
        sel_nodes.sort();
        for node in &sel_nodes {
            let authoritative_candidates: Vec<usize> = func
                .candidate_structure_worlds
                .get(node)
                .map(|masks| {
                    masks
                        .iter()
                        .enumerate()
                        .filter_map(|(index, worlds)| {
                            worlds
                                .contains(&func.authoritative_structure_world)
                                .then_some(index)
                        })
                        .collect()
                })
                .unwrap_or_else(|| (0..func.node_statements[node].len()).collect());
            // The legacy solver had a statement prior only at a node with
            // multiple authoritative candidates.  Do not let a newly added
            // flat sibling create a fresh objective term.
            if authoritative_candidates.len() > 1 {
                sink.assert_soft_raw(&selvar[node][authoritative_candidates[0]], 1u64);
            }
        }
        if let Some(authoritative) = structure_world_var.get(&func.authoritative_structure_world) {
            sink.assert_soft_raw(authoritative, 1u64);
        }
        // (No canonical tie-break clauses: the width/signedness/float-size payload dimensions that created solver-side ties were REMOVED from the datatype -- see the TypeDt comment. Class-level ties cannot reach the output: the anchor maps each class to one deterministic candidate.)

        BuiltFunction {
            t,
            regs,
            tyvar,
            structure_worlds,
            structure_world_var,
            nodes,
            selvar,
            recorded,
        }
    }
}

// Read one model into the per-function selection. Engine-independent: a pure function of the model plus the built terms.
#[allow(clippy::type_complexity)]
fn extract_selection(
    m: &dyn ModelView,
    built: &BuiltFunction,
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
) -> (
    HashMap<Node, Option<usize>>,
    HashMap<RTLReg, usize>,
    HashMap<RTLReg, CandType>,
    u8,
) {
    let BuiltFunction {
        t,
        regs,
        tyvar,
        structure_worlds,
        structure_world_var,
        nodes,
        selvar,
        recorded,
    } = built;
    let selected_structure_world = structure_worlds
        .iter()
        .find(|world| {
            structure_world_var
                .get(world)
                .is_some_and(|var| m.truth(var).unwrap_or(false))
        })
        .copied()
        .unwrap_or(func.authoritative_structure_world);
    let mut cand_out: HashMap<Node, Option<usize>> = HashMap::new();
    let mut ty_out: HashMap<RTLReg, usize> = HashMap::new();
    let mut ty_override: HashMap<RTLReg, CandType> = HashMap::new();
    // P3: the re-pick scores each candidate by its EXACT frontend-error count under the model, covering concrete bases that the z3 structural asserts exempt; allow_void=false breaks the cycle.
    let wt_env = {
        let mut temps: HashMap<Ident, ClightType> = HashMap::new();
        for &reg in regs {
            let rendered = render_type(t, m, &tyvar[&reg], reg, func, false);
            // Type by the ANCHORED candidate, not the raw class render: the emitter prints candidates[anchor], so the anchored candidate is the decl gcc will see -- width/signedness fidelity the class-level model no longer carries (deterministic: anchor_index is a pure function).
            let cands = &func.var_type_candidates[&reg];
            let decl = anchor_index(cands, rendered, false)
                .and_then(|i| cands.get(i).copied())
                .unwrap_or(rendered);
            temps.insert(
                reg as Ident,
                crate::decompile::passes::clight_select::wt_audit::candtype_to_clight(decl),
            );
        }
        for (reg, candidate) in &func.var_types {
            if !tyvar.contains_key(reg) {
                temps.entry(*reg as Ident).or_insert_with(|| {
                    crate::decompile::passes::clight_select::wt_audit::candtype_to_clight(
                        *candidate,
                    )
                });
            }
        }
        // Params are a gap-filler ONLY: for an inferable param reg the MODEL rendering must win, or the signature's ParamType clobbers a model-typed struct pointer and flips selection.
        for (reg, pt) in func.param_regs.iter().zip(func.param_types.iter()) {
            if tyvar.contains_key(reg) {
                continue;
            }
            temps.entry(*reg as Ident).or_insert_with(|| {
                crate::decompile::passes::clight_select::wt_audit::param_type_to_clight(pt)
            });
        }
        let (fields, known) =
            crate::decompile::passes::clight_select::wt_audit::fields_from_struct_fields(
                &func.struct_fields,
            );
        crate::decompile::passes::clight_select::wt_audit::AuditEnv::from_parts(
            temps,
            fields,
            known,
            func.return_type.clone(),
            &func.callee_signatures,
            name_to_ident,
            func.known_global_types.as_ref(),
            func.ptr64,
        )
    };
    for &node in nodes {
        match selvar.get(&node) {
            Some(vars) => {
                // z3's own pick (consistent with every asserted constraint) is the fallback when nothing was recorded.
                let Some(mut chosen) = vars
                    .iter()
                    .position(|selected| m.truth(selected).unwrap_or(false))
                else {
                    // This node does not exist in the selected structural
                    // world.  It must remain absent through tree assembly.
                    cand_out.insert(node, None);
                    continue;
                };
                // Exact-wt re-pick (P3): with the model fixed, score each candidate by fewest exact frontend errors, then structural conditions, then soft weight, then index, and take the minimum.
                if let Some(per_cand) = recorded.get(&node) {
                    let truth = |c: &Bool| m.truth(c).unwrap_or(true);
                    let cands = &func.node_statements[&node];
                    let mut best: Option<(u64, u64, u64, u64, usize)> = None;
                    for (ci, conds) in per_cand.iter().enumerate() {
                        let allowed = func
                            .candidate_structure_worlds
                            .get(&node)
                            .and_then(|masks| masks.get(ci))
                            .map_or(true, |worlds| worlds.contains(&selected_structure_world));
                        if !allowed {
                            continue;
                        }
                        let wt = cands
                            .get(ci)
                            .map(|stmt| {
                                let errs =
                                    crate::decompile::passes::clight_select::ctyping::wt_check_stmt(
                                        stmt, &wt_env,
                                    );
                                crate::decompile::passes::clight_select::ctyping::error_count(&errs)
                                    as u64
                            })
                            .unwrap_or(0);
                        // Lossy 64->32 truncations: ranked above soft preferences, uniform when truncation is unavoidable.
                        let narrow = cands.get(ci).map(count_truncating_casts_stmt).unwrap_or(0);
                        let mut sviol = 0u64;
                        let mut wviol = 0u64;
                        for (cond, w) in conds {
                            let ok = match cond {
                                Some(c) => truth(c),
                                None => false,
                            };
                            if !ok {
                                if *w == u64::MAX {
                                    sviol += 1;
                                } else {
                                    wviol = wviol.saturating_add(*w);
                                }
                            }
                        }
                        let key = (wt, sviol, narrow, wviol, ci);
                        if best.is_none_or(|b| key < b) {
                            best = Some(key);
                        }
                    }
                    if let Some((_, _, _, _, ci)) = best {
                        chosen = ci;
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
    for &node in nodes {
        if let Some(Some(ci)) = cand_out.get(&node) {
            if let Some(stmt) = func.node_statements[&node].get(*ci) {
                collect_reg_ptr_evidence_stmt(stmt, &mut ptr_ev);
            }
        }
    }
    for &reg in regs {
        let allow_void = ptr_ev.get(&reg).map(|e| !e.any_deref).unwrap_or(true);
        let rendered = render_type(t, m, &tyvar[&reg], reg, func, allow_void);
        let cands = &func.var_type_candidates[&reg];
        match anchor_index(cands, rendered, allow_void) {
            Some(idx) => {
                ty_out.insert(reg, idx);
            }
            None => {
                // Belt-and-suspenders (RC-1): an override may widen width within an evidenced class but must never invent the float CLASS, so a float render absent from the candidate set falls back to the anchor.
                let render_is_float = rendered.is_float();
                let cands_have_float = cands.iter().any(|c| c.is_float() || c.is_float_pointee());
                if render_is_float && !cands_have_float {
                    ty_out.insert(reg, 0);
                } else {
                    // Genuinely-new inferred type: carry it out-of-band so the emitter still sees it.
                    ty_out.insert(reg, 0);
                    ty_override.insert(reg, rendered);
                }
            }
        }
    }

    (cand_out, ty_out, ty_override, selected_structure_world)
}

// The per-function selection a solve produces, plus the SatResult that yielded it.
type SolveOutcome = (
    HashMap<Node, Option<usize>>,
    HashMap<RTLReg, usize>,
    HashMap<RTLReg, CandType>,
    u8,
    SatResult,
);

// The single Z3 solve. Returns the selection + the SatResult that yielded the model, or the failing SatResult when no model is available.
fn solve_function_z3(
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    interface_pins: &[(RTLReg, XType)],
) -> Result<SolveOutcome, SatResult> {
    // Fresh Z3 context per function: reusing one leaks MaxSMT state across functions and makes tie-breaking depend on rayon order. Do not set random_seed -- z3 rejects it and warns to stderr.
    let cfg = z3::Config::new();
    z3::with_z3_config(&cfg, || {
        let build_t0 = std::time::Instant::now();
        let t = TypeDt::build();
        let opt = Optimize::new();
        let mut params = z3::Params::new();
        // Use the deterministic rlimit budget, not wall-clock timeout, which is a hang backstop only; z3 4.8.x ignores rlimit through Optimize params, so the model-reuse path guards itself.
        params.set_u32("rlimit", CONFIG.solve.rlimit);
        params.set_u32("timeout", CONFIG.solve.timeout_ms);
        params.set_u32("random_seed", 0);
        opt.set_params(&params);

        let (built, softs) = {
            let backend = OptimizeBackend::new(&opt);
            let built =
                build_function_constraints(t, func, name_to_ident, interface_pins, &backend);
            (built, backend.into_softs())
        };

        BUILD_NS.fetch_add(
            build_t0.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        let check_t0 = std::time::Instant::now();
        let check_result = opt.check(&[]);
        CHECK_NS.fetch_add(
            check_t0.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        let model = match check_result {
            SatResult::Sat => opt.get_model(),
            // Partial-solve reuse (TR-1): on unknown, reuse the best-so-far model only when the deterministic rlimit was exhausted, since a wall-clock unknown would be timing-dependent.
            SatResult::Unknown => {
                let resource_budget = opt
                    .get_reason_unknown()
                    .map(|r| r.contains("resource"))
                    .unwrap_or(false);
                if resource_budget {
                    opt.get_model()
                } else {
                    None
                }
            }
            SatResult::Unsat => None,
        };

        match model {
            Some(m) => {
                report_cost("optimize", func, &m, &softs);
                let (cand_out, ty_out, ty_override, structure_world) =
                    extract_selection(&m, &built, func, name_to_ident);
                Ok((cand_out, ty_out, ty_override, structure_world, check_result))
            }
            None => Err(check_result),
        }
    })
}

// Minimum violated soft count found for one weight class.
#[derive(Debug, Clone, Copy)]
struct StratumOptimum {
    weight: u64,
    size: usize,
    violated: usize,
}

// Stratified lexicographic MaxSAT on a plain Solver.
//
// Softs are grouped by weight; within a group weights are equal, so the group's
// cost is a cardinality and `pb_le` over its relaxation literals bounds it. The
// groups are minimized from the heaviest down, each one hardened at its optimum
// before the next is searched.
//
// This is the LEXICOGRAPHIC optimum. It coincides with Optimize's weighted-sum
// optimum only where a class outweighs everything below it: compat_w is built as
// (regs + selvars + 1), which dominates the weight-1 priors by construction, but
// the intermediate 8 and 2 classes are not dominant, so the two engines can
// legitimately disagree there. The A/B run measures how often that happens.
fn stratified_maxsat(
    solver: &RawSolver,
    softs: &[(Bool, u64)],
) -> (SatResult, Vec<StratumOptimum>, u64) {
    let mut by_weight: BTreeMap<u64, Vec<Bool>> = BTreeMap::new();
    for (literal, weight) in softs {
        by_weight.entry(*weight).or_default().push(literal.clone());
    }
    let mut strata: Vec<(u64, Vec<Bool>)> = by_weight.into_iter().collect();
    strata.reverse();

    let mut checks = 1u64;
    let baseline = solver.check();
    if !matches!(baseline, SatResult::Sat) {
        return (baseline, Vec::new(), checks);
    }

    let mut optima = Vec::new();
    for (weight, literals) in &strata {
        if literals.is_empty() {
            continue;
        }
        let refs: Vec<(&Bool, i32)> = literals.iter().map(|b| (b, 1)).collect();
        let size = literals.len();
        // Probe "no violation in this class" first: most classes are fully
        // satisfiable and the probe skips the whole search when they are.
        let mut lo = 0usize;
        solver.push();
        solver.assert(&Bool::pb_le(&refs, 0));
        checks += 1;
        let zero = solver.check();
        solver.pop(1);
        match zero {
            SatResult::Sat => {}
            SatResult::Unsat => {
                lo = 1;
                let mut hi = size;
                while lo < hi {
                    let mid = lo + (hi - lo) / 2;
                    solver.push();
                    solver.assert(&Bool::pb_le(&refs, mid as i32));
                    checks += 1;
                    let probe = solver.check();
                    solver.pop(1);
                    match probe {
                        SatResult::Sat => hi = mid,
                        SatResult::Unsat => lo = mid + 1,
                        SatResult::Unknown => return (SatResult::Unknown, optima, checks),
                    }
                }
            }
            SatResult::Unknown => return (SatResult::Unknown, optima, checks),
        }
        if lo < size {
            solver.assert(&Bool::pb_le(&refs, lo as i32));
        }
        optima.push(StratumOptimum {
            weight: *weight,
            size,
            violated: lo,
        });
    }

    // One last check so the retained model is the one satisfying every hardened bound.
    checks += 1;
    (solver.check(), optima, checks)
}

// Engine B (experiment): the same formula on a plain Solver, its optimum found
// by the stratified loop above, with the branch-signedness theory attached as a
// Z3 user propagator so behavioral evidence prunes the search itself.
fn solve_function_propagator_attempt(
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    interface_pins: &[(RTLReg, XType)],
    exempt_nodes: &BTreeSet<Node>,
) -> (Result<SolveOutcome, SatResult>, BTreeSet<Node>) {
    let cfg = z3::Config::new();
    z3::with_z3_config(&cfg, || {
        let build_t0 = std::time::Instant::now();
        let t = TypeDt::build();
        let mut solver = RawSolver::new_simple();
        solver.set_params_u32(&[
            ("rlimit", CONFIG.solve.rlimit),
            ("timeout", CONFIG.solve.timeout_ms),
            ("random_seed", 0),
        ]);
        // The plugin has to exist while the assertions are internalized.
        solver.init_propagator();

        let (built, softs) = {
            let backend = RelaxBackend::new(&solver);
            let built =
                build_function_constraints(t, func, name_to_ident, interface_pins, &backend);
            (built, backend.into_softs())
        };

        let (branch_vetoes, build_stats) =
            crate::decompile::passes::clight_select::branch_theory::build_branch_theory(
                &built.nodes,
                &func.node_statements,
                &built.selvar,
                &func.cond_branch_class,
            );
        let (class_vetoes, class_stats) =
            crate::decompile::passes::clight_select::class_theory::build_class_theory(
                &built.nodes,
                &func.node_statements,
                &built.selvar,
                &func.used_regs,
                &func.class_evidence,
            );
        if build_stats.nodes_watched > 0 {
            eprintln!(
                "[branch-theory] {} ({:#x}) watched={} vetoed-literals={} of {} multi-candidate nodes",
                func.name,
                func.address,
                build_stats.nodes_watched,
                build_stats.literals_vetoed,
                build_stats.multi_candidate_nodes
            );
        }
        if class_stats.nodes_watched > 0 || class_stats.nodes_all_contradict > 0 {
            eprintln!(
                "[class-theory] {} ({:#x}) watched={} vetoed-literals={} all-contradict-nodes={} single-class-webs={} conflicted-webs={}",
                func.name,
                func.address,
                class_stats.nodes_watched,
                class_stats.literals_vetoed,
                class_stats.nodes_all_contradict,
                class_stats.webs_single_class,
                class_stats.webs_conflicted
            );
        }

        // Both veto theories are veto sets, so one propagator carries both; the
        // tags keep their statistics apart. The flow theory then rides on the
        // same propagator, its selection literals registered after the veto
        // terms so the index split tells them apart.
        let mut tags: Vec<&'static str> =
            vec![crate::decompile::passes::clight_select::branch_theory::TAG; branch_vetoes.len()];
        tags.extend(
            std::iter::repeat(crate::decompile::passes::clight_select::class_theory::TAG)
                .take(class_vetoes.len()),
        );
        let mut terms = branch_vetoes;
        terms.extend(class_vetoes);
        let veto_len = terms.len();

        let mut literal_layout: Vec<(Node, usize)> = Vec::new();
        let mut literal_index: BTreeMap<(Node, usize), usize> = BTreeMap::new();
        let mut sorted_sel: Vec<Node> = built.selvar.keys().copied().collect();
        sorted_sel.sort_unstable();
        for node in sorted_sel {
            for (i, lit) in built.selvar[&node].iter().enumerate() {
                literal_index.insert((node, i), terms.len());
                terms.push(lit.clone());
                literal_layout.push((node, i));
            }
        }
        let problem = crate::decompile::passes::clight_select::flow_theory::FlowProblem {
            blocks: func.flow_blocks.clone(),
            anchors: func.flow_anchors.clone(),
            candidates: func
                .node_statements
                .iter()
                .map(|(n, c)| (*n, c.clone()))
                .collect(),
            selectable: built.selvar.keys().copied().collect(),
            literal_index,
            ptr64: func.ptr64,
            round_cap: crate::decompile::passes::clight_select::flow_theory::DEFAULT_ROUND_CAP,
            exempt_nodes: exempt_nodes.clone(),
        };
        let theory = Rc::new(RefCell::new(
            crate::decompile::passes::clight_select::flow_theory::SelectionTheory::new(
                VetoTheory::new(tags),
                veto_len,
                literal_layout,
                problem,
            ),
        ));
        solver.set_theory(theory.clone(), terms);

        BUILD_NS.fetch_add(
            build_t0.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        let relax_lits: Vec<(Bool, u64)> = softs
            .iter()
            .map(|(_, relax, weight)| (relax.clone(), *weight))
            .collect();
        let clauses: Vec<(Bool, u64)> = softs
            .iter()
            .map(|(clause, _, weight)| (clause.clone(), *weight))
            .collect();
        let check_t0 = std::time::Instant::now();
        let (check_result, optima, checks) = stratified_maxsat(&solver, &relax_lits);
        CHECK_NS.fetch_add(
            check_t0.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );

        let mut stats = build_stats;
        let flow_named: BTreeSet<Node>;
        let flow_injected: BTreeSet<Node>;
        {
            let t = theory.borrow();
            let v = t.veto();
            stats.vetoes_fired =
                v.fired_for(crate::decompile::passes::clight_select::branch_theory::TAG);
            stats.conflicts_injected =
                v.conflicts_for(crate::decompile::passes::clight_select::branch_theory::TAG);
            let mut cstats = class_stats;
            cstats.vetoes_fired =
                v.fired_for(crate::decompile::passes::clight_select::class_theory::TAG);
            cstats.conflicts_injected =
                v.conflicts_for(crate::decompile::passes::clight_select::class_theory::TAG);
            CLASS_STATS.lock().unwrap().merge(&cstats);
            FLOW_STATS.lock().unwrap().merge(&t.stats);
            flow_named = t.named_by_flow.clone();
            flow_injected = t.injected_at.clone();
        }
        BRANCH_STATS.lock().unwrap().merge(&stats);
        SOLVER_CHECKS.fetch_add(checks, std::sync::atomic::Ordering::Relaxed);
        if std::env::var("MANIFOLD_SOLVER_STRATA").is_ok() {
            for optimum in &optima {
                eprintln!(
                    "[maxsat] {} ({:#x}) w={} violated={}/{}",
                    func.name, func.address, optimum.weight, optimum.violated, optimum.size
                );
            }
        }

        let model = match check_result {
            SatResult::Sat => solver.model(),
            // Same policy as the Optimize path: a best-so-far model is reusable
            // only when the deterministic rlimit ran out, never on wall clock.
            SatResult::Unknown => {
                let resource_budget = solver
                    .reason_unknown()
                    .map(|r| r.contains("resource"))
                    .unwrap_or(false);
                if resource_budget {
                    solver.model()
                } else {
                    None
                }
            }
            SatResult::Unsat => None,
        };

        let result = match model {
            Some(m) => {
                report_cost("propagator", func, &m, &clauses);
                let (cand_out, ty_out, ty_override, structure_world) =
                    extract_selection(&m, &built, func, name_to_ident);
                // Guess-surface proxy. When the flow theory named a node in a
                // clause and that node's final pick is not candidate 0, the
                // weight-1 syntactic prior lost to behavioral evidence: the
                // answer came from what the machine does, not from what the
                // objective prefers. Counting those sizes how much of the
                // selection is still being decided by preference.
                let ties = flow_named
                    .iter()
                    .filter(|n| matches!(cand_out.get(*n), Some(Some(i)) if *i != 0))
                    .count();
                if ties > 0 {
                    let mut g = FLOW_STATS.lock().unwrap();
                    g.ties_determined_by_flow += ties;
                }
                Ok((cand_out, ty_out, ty_override, structure_world, check_result))
            }
            None => Err(check_result),
        };
        (result, flow_injected)
    })
}

fn first_new_flow_exemption(
    injected_at: &BTreeSet<Node>,
    exempt_nodes: &BTreeSet<Node>,
) -> Option<Node> {
    injected_at.difference(exempt_nodes).next().copied()
}

/// Preserve as much of the ground flow theory as possible.  A failed attempt
/// reports the exact contradiction sites at which it injected clauses; those
/// sites are audited gaps in the combined ground formula, so a retry exempts
/// only them.  Every other node remains checked by the same theory.  If an
/// UNSAT attempt did not inject a new flow clause, the failure belongs to the
/// base formula or another theory and the ordinary Optimize fallback remains
/// the only safe recovery.
fn solve_function_propagator(
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    interface_pins: &[(RTLReg, XType)],
    maximal_flow_certification: bool,
) -> Result<SolveOutcome, SatResult> {
    let mut exempt_nodes = BTreeSet::new();
    let mut retries = 0usize;
    loop {
        let (result, injected_at) =
            solve_function_propagator_attempt(func, name_to_ident, interface_pins, &exempt_nodes);
        let Err(SatResult::Unsat) = result else {
            if retries > 0 {
                eprintln!(
                    "[flow] maximal-certification fn={} ({:#x}) retries={} exempted-gap-nodes={}",
                    func.name,
                    func.address,
                    retries,
                    exempt_nodes
                        .iter()
                        .map(|node| format!("{node:#x}"))
                        .collect::<Vec<_>>()
                        .join(",")
                );
            }
            return result;
        };
        if !maximal_flow_certification {
            return Err(SatResult::Unsat);
        }
        let Some(new_node) = first_new_flow_exemption(&injected_at, &exempt_nodes) else {
            if retries > 0 {
                eprintln!(
                    "[flow] maximal-certification fn={} ({:#x}) retries={} exempted-gap-nodes={} result=UNSAT",
                    func.name,
                    func.address,
                    retries,
                    exempt_nodes
                        .iter()
                        .map(|node| format!("{node:#x}"))
                        .collect::<Vec<_>>()
                        .join(",")
                );
            }
            return Err(SatResult::Unsat);
        };
        // Add exactly one deterministic site.  Exempting the whole failed
        // attempt's clause set can discard constraints that were jointly
        // satisfiable; one-at-a-time deletion keeps the retained theory
        // maximal for this deterministic retry order.
        exempt_nodes.insert(new_node);
        retries += 1;
        let mut stats = FLOW_STATS.lock().unwrap();
        stats.unsat_retries += 1;
        stats.exempted_nodes += 1;
    }
}

/// Which per-function selection engine runs. Production is fixed to Optimize;
/// the propagator remains only for the explicit maximal-certification ablation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SolveEngine {
    Optimize,
    Propagator,
}

fn selected_solve_engine(maximal_flow_certification: bool) -> SolveEngine {
    if maximal_flow_certification {
        SolveEngine::Propagator
    } else {
        SolveEngine::Optimize
    }
}

// Run-wide A/B counters.
static ENGINE_OPTIMIZE_FUNCS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
static ENGINE_PROPAGATOR_FUNCS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
static ENGINE_FALLBACKS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static ENGINE_RESCUED: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static ENGINE_PANICS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static SOLVER_CHECKS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static ENGINE_OPTIMIZE_NS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static ENGINE_PROPAGATOR_NS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static BRANCH_STATS: std::sync::LazyLock<
    std::sync::Mutex<crate::decompile::passes::clight_select::branch_theory::BranchStats>,
> = std::sync::LazyLock::new(|| std::sync::Mutex::new(Default::default()));
static CLASS_STATS: std::sync::LazyLock<
    std::sync::Mutex<crate::decompile::passes::clight_select::class_theory::ClassStats>,
> = std::sync::LazyLock::new(|| std::sync::Mutex::new(Default::default()));
/// Flow-theory counters accumulated across every per-function solve in a run.
/// The certificate pass adds the block counts afterwards.
static FLOW_STATS: std::sync::LazyLock<
    std::sync::Mutex<crate::decompile::passes::clight_select::flow::FlowStats>,
> = std::sync::LazyLock::new(|| std::sync::Mutex::new(Default::default()));

/// Take the in-solve flow counters and reset them, so a second decompilation in
/// the same process starts clean.
pub(crate) fn flow_stats_snapshot() -> crate::decompile::passes::clight_select::flow::FlowStats {
    let mut guard = FLOW_STATS.lock().unwrap();
    let snapshot = *guard;
    *guard = Default::default();
    snapshot
}

/// Run one function through the fixed production engine, or through the
/// explicit maximal-certification ablation. Fall back to Optimize on any
/// propagator-side error or panic so the ablation cannot lose a function. Note
/// that the release profile is `panic = "abort"`, so the panic arm only rescues
/// debug builds; a release panic still aborts.
fn solve_function_engine(
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    interface_pins: &[(RTLReg, XType)],
    maximal_flow_certification: bool,
) -> Result<SolveOutcome, SatResult> {
    if selected_solve_engine(maximal_flow_certification) == SolveEngine::Optimize {
        let started = std::time::Instant::now();
        let out = solve_function_z3(func, name_to_ident, interface_pins);
        ENGINE_OPTIMIZE_NS.fetch_add(
            started.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        ENGINE_OPTIMIZE_FUNCS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        return out;
    }

    let started = std::time::Instant::now();
    let attempt = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solve_function_propagator(
            func,
            name_to_ident,
            interface_pins,
            maximal_flow_certification,
        )
    }));
    ENGINE_PROPAGATOR_NS.fetch_add(
        started.elapsed().as_nanos() as u64,
        std::sync::atomic::Ordering::Relaxed,
    );
    match attempt {
        Ok(Ok(outcome)) => {
            ENGINE_PROPAGATOR_FUNCS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            Ok(outcome)
        }
        Ok(Err(grade)) => {
            ENGINE_FALLBACKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            eprintln!(
                "[clight-select] propagator engine yielded no model for {} ({:#x}): {:?}; falling back to optimize",
                func.name, func.address, grade
            );
            fallback_to_optimize(func, name_to_ident, interface_pins)
        }
        Err(_) => {
            ENGINE_PANICS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            ENGINE_FALLBACKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            eprintln!(
                "[clight-select] propagator engine panicked on {} ({:#x}); falling back to optimize",
                func.name, func.address
            );
            fallback_to_optimize(func, name_to_ident, interface_pins)
        }
    }
}

fn fallback_to_optimize(
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    interface_pins: &[(RTLReg, XType)],
) -> Result<SolveOutcome, SatResult> {
    let started = std::time::Instant::now();
    let out = solve_function_z3(func, name_to_ident, interface_pins);
    ENGINE_OPTIMIZE_NS.fetch_add(
        started.elapsed().as_nanos() as u64,
        std::sync::atomic::Ordering::Relaxed,
    );
    ENGINE_OPTIMIZE_FUNCS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    // A fallback the Optimize path also cannot model is a pre-existing UNSAT the
    // two engines share, not a divergence between them; only the rescued ones
    // measure the new engine losing a function the old one keeps.
    if out.is_ok() {
        ENGINE_RESCUED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
    out
}

// Swap-reset so an in-process multi-binary run reports per program.
fn report_engine_stats(functions: usize, maximal_flow_certification: bool) {
    let optimize = ENGINE_OPTIMIZE_FUNCS.swap(0, std::sync::atomic::Ordering::Relaxed);
    let propagator = ENGINE_PROPAGATOR_FUNCS.swap(0, std::sync::atomic::Ordering::Relaxed);
    let fallbacks = ENGINE_FALLBACKS.swap(0, std::sync::atomic::Ordering::Relaxed);
    let rescued = ENGINE_RESCUED.swap(0, std::sync::atomic::Ordering::Relaxed);
    let panics = ENGINE_PANICS.swap(0, std::sync::atomic::Ordering::Relaxed);
    let checks = SOLVER_CHECKS.swap(0, std::sync::atomic::Ordering::Relaxed);
    let optimize_ms = ENGINE_OPTIMIZE_NS.swap(0, std::sync::atomic::Ordering::Relaxed) / 1_000_000;
    let propagator_ms =
        ENGINE_PROPAGATOR_NS.swap(0, std::sync::atomic::Ordering::Relaxed) / 1_000_000;
    let branch = {
        let mut guard = BRANCH_STATS.lock().unwrap();
        let snapshot = *guard;
        *guard = Default::default();
        snapshot
    };
    eprintln!(
        "[clight-select] engine={:?} funcs={} optimize={} ({}ms cpu) propagator={} ({}ms cpu) fallbacks={} (rescued={}) panics={} solver-checks={}",
        selected_solve_engine(maximal_flow_certification), functions, optimize, optimize_ms, propagator, propagator_ms, fallbacks, rescued, panics, checks
    );
    let class = {
        let mut guard = CLASS_STATS.lock().unwrap();
        let snapshot = *guard;
        *guard = Default::default();
        snapshot
    };
    if selected_solve_engine(maximal_flow_certification) == SolveEngine::Propagator {
        eprintln!(
            "[clight-select] branch-theory: multi-cand-nodes={} mcond-addrs={} classified={} watched={} vetoed-literals={} vetoes-fired={} conflicts={} fresh-callbacks={}",
            branch.multi_candidate_nodes,
            branch.branch_addresses,
            branch.nodes_classified,
            branch.nodes_watched,
            branch.literals_vetoed,
            branch.vetoes_fired,
            branch.conflicts_injected,
            crate::decompile::passes::clight_select::propagator::fresh_callback_count()
        );
        eprintln!(
            "[clight-select] class-theory: single-class-webs={} conflicted-webs={} watched={} all-contradict-nodes={} vetoed-literals={} vetoes-fired={} conflicts={}",
            class.webs_single_class,
            class.webs_conflicted,
            class.nodes_watched,
            class.nodes_all_contradict,
            class.literals_vetoed,
            class.vetoes_fired,
            class.conflicts_injected
        );
    }
}

// Run-wide counters: NO_MODEL = z3 yielded no model (function shipped with no selection), PARTIAL = over-budget best-so-far model reused.
static TYPE_SOLVE_NO_MODEL: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static TYPE_SOLVE_PARTIAL: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

// ---- per-register structural pointer-use evidence (TR-6 void license) ----

#[derive(Default, Clone, Copy)]
struct RegPtrEvidence {
    // Deref/field involvement in any form including casts -- denies TR-6 void* license even when solver does not hard-assert (memory is still read through the register).
    any_deref: bool,
}

// Deref/field chain root (tempvar, deref, add/sub), peeling casts -- conservative root set for denying the void-pointee license.
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
            if let Some(r) = loose_chain_root(inner) {
                out.entry(r).or_default().any_deref = true;
            }
            collect_reg_ptr_evidence_expr(inner, out);
        }
        ClightExpr::Efield(base, _, _) => {
            if let Some(r) = loose_chain_root(base) {
                out.entry(r).or_default().any_deref = true;
            }
            collect_reg_ptr_evidence_expr(base, out);
        }
        ClightExpr::Ecast(inner, _)
        | ClightExpr::Eaddrof(inner, _)
        | ClightExpr::Eunop(_, inner, _) => {
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
        ClightStmt::Sreturn(Some(e)) => collect_reg_ptr_evidence_expr(e, out),
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

// Static type annotation carried by any Clight expression (the last field of every variant).
pub(crate) fn clight_expr_type(e: &ClightExpr) -> &ClightType {
    match e {
        ClightExpr::EconstInt(_, t)
        | ClightExpr::EconstFloat(_, t)
        | ClightExpr::EconstSingle(_, t)
        | ClightExpr::EconstLong(_, t)
        | ClightExpr::Evar(_, t)
        | ClightExpr::EvarSymbol(_, t)
        | ClightExpr::Etempvar(_, t)
        | ClightExpr::Ederef(_, t)
        | ClightExpr::Eaddrof(_, t)
        | ClightExpr::Eunop(_, _, t)
        | ClightExpr::Ebinop(_, _, _, t)
        | ClightExpr::Ecast(_, t)
        | ClightExpr::Efield(_, _, t)
        | ClightExpr::Esizeof(_, t)
        | ClightExpr::Ealignof(_, t)
        | ClightExpr::Econdition(_, _, _, t) => t,
    }
}

// Price lossy 64->32 Ecast narrowings as a tie-breaker only, steering away from a needless truncation when a width-preserving candidate exists; float sources excluded.
fn is_wide64_lossy_source(t: &ClightType) -> bool {
    matches!(
        t,
        ClightType::Tpointer(_, _) | ClightType::Tfunction(_, _, _) | ClightType::Tlong(_, _)
    )
}

fn is_narrow_int_target(t: &ClightType) -> bool {
    matches!(
        t,
        ClightType::Tint(
            ClightIntSize::I8 | ClightIntSize::I16 | ClightIntSize::I32 | ClightIntSize::IBool,
            _,
            _
        )
    )
}

fn count_truncating_casts_expr(e: &ClightExpr) -> u64 {
    let mut n = 0u64;
    if let ClightExpr::Ecast(inner, target) = e {
        if is_wide64_lossy_source(clight_expr_type(inner)) && is_narrow_int_target(target) {
            n += 1;
        }
    }
    match e {
        ClightExpr::Ederef(i, _)
        | ClightExpr::Eaddrof(i, _)
        | ClightExpr::Eunop(_, i, _)
        | ClightExpr::Ecast(i, _)
        | ClightExpr::Efield(i, _, _) => n += count_truncating_casts_expr(i),
        ClightExpr::Ebinop(_, l, r, _) => {
            n += count_truncating_casts_expr(l);
            n += count_truncating_casts_expr(r);
        }
        ClightExpr::Econdition(c, a, b, _) => {
            n += count_truncating_casts_expr(c);
            n += count_truncating_casts_expr(a);
            n += count_truncating_casts_expr(b);
        }
        _ => {}
    }
    n
}

fn count_truncating_casts_stmt(stmt: &ClightStmt) -> u64 {
    match stmt {
        ClightStmt::Sassign(l, r) => {
            count_truncating_casts_expr(l) + count_truncating_casts_expr(r)
        }
        ClightStmt::Sset(_, e) => count_truncating_casts_expr(e),
        ClightStmt::Scall(_, f, args) => {
            count_truncating_casts_expr(f)
                + args.iter().map(count_truncating_casts_expr).sum::<u64>()
        }
        ClightStmt::Sreturn(Some(e)) => count_truncating_casts_expr(e),
        ClightStmt::Sifthenelse(c, _, _) => count_truncating_casts_expr(c),
        ClightStmt::Sswitch(e, _) => count_truncating_casts_expr(e),
        ClightStmt::Slabel(_, inner) => count_truncating_casts_stmt(inner),
        _ => 0,
    }
}

// Whole-program selection: one Z3 solve per function (in parallel), merged into a ProgramSelectionState. Z3 is the only selector; functions whose solve yields no model simply contribute no entries.
pub(crate) fn infer_select_program(
    functions: &[FunctionData],
    name_to_ident: &HashMap<String, Ident>,
    maximal_flow_certification: bool,
) -> ProgramSelectionState {
    let per_func: Vec<(
        Address,
        HashMap<Node, Option<usize>>,
        HashMap<RTLReg, usize>,
        HashMap<RTLReg, CandType>,
        u8,
    )> = functions
        .par_iter()
        .map(|f| {
            let (c, t, o, world) = solve_function(f, name_to_ident, maximal_flow_certification);
            (f.address, c, t, o, world)
        })
        .collect();

    // Run summary: how many functions shipped a degraded type solve (per-function WARN lines above carry the detail). Swap-reset so in-process multi-binary runs (tests) report per program.
    let no_model = TYPE_SOLVE_NO_MODEL.swap(0, std::sync::atomic::Ordering::Relaxed);
    let partial = TYPE_SOLVE_PARTIAL.swap(0, std::sync::atomic::Ordering::Relaxed);
    if no_model > 0 || partial > 0 {
        eprintln!(
            "[clight-select] WARN: type solve degraded for {}/{} functions ({} partial-model reuse, {} no model / no selection)",
            no_model + partial,
            functions.len(),
            partial,
            no_model
        );
    }
    let softs = SOFT_CLAUSES.swap(0, std::sync::atomic::Ordering::Relaxed);
    let build_ms = BUILD_NS.swap(0, std::sync::atomic::Ordering::Relaxed) / 1_000_000;
    let check_ms = CHECK_NS.swap(0, std::sync::atomic::Ordering::Relaxed) / 1_000_000;
    eprintln!(
        "[clight-select] asserted soft clauses: {} across {} functions (cpu: build {}ms, check {}ms)",
        softs,
        functions.len(),
        build_ms,
        check_ms
    );
    report_engine_stats(functions.len(), maximal_flow_certification);
    if std::env::var("MANIFOLD_SOFT_BREAKDOWN").is_ok() {
        let mut tags = SOFT_TAGS.lock().unwrap();
        let line = tags
            .iter()
            .map(|(k, v)| format!("{}={}", k, v))
            .collect::<Vec<_>>()
            .join(" ");
        eprintln!("[clight-select] soft breakdown: {}", line);
        tags.clear();
    }

    let mut candidate_idx = HashMap::new();
    let mut structure_world = HashMap::new();
    let mut var_decl_idx = HashMap::new();
    let mut var_type_override = HashMap::new();
    for (addr, cmap, tmap, omap, world) in per_func {
        structure_world.insert(addr, world);
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

    let state = ProgramSelectionState {
        candidate_idx,
        structure_world,
        var_decl_idx,
        var_type_override,
    };
    dump_selection("stage-a", &state);
    state
}

/// Diagnostic only, never changes output: a sorted, engine-independent dump of
/// the per-function selection, so an A/B run can count exactly how many
/// functions the two engines select identically.
fn dump_selection(stage: &str, state: &ProgramSelectionState) {
    if std::env::var("MANIFOLD_DUMP_SELECTION").is_err() {
        return;
    }
    let mut lines: Vec<String> = Vec::new();
    for ((addr, node), idx) in &state.candidate_idx {
        lines.push(format!("stmt {:#x} {:#x} {:?}", addr, node, idx));
    }
    for (addr, world) in &state.structure_world {
        lines.push(format!("world {:#x} {}", addr, world));
    }
    for ((addr, reg), idx) in &state.var_decl_idx {
        lines.push(format!("decl {:#x} {:#x} {}", addr, reg, idx));
    }
    for ((addr, reg), candidate) in &state.var_type_override {
        lines.push(format!("over {:#x} {:#x} {:?}", addr, reg, candidate));
    }
    lines.sort();
    for line in lines {
        eprintln!("[selection {}] {}", stage, line);
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct DirtyResolveStats {
    pub dirty_count: usize,
    pub resolved_count: usize,
    pub fallback_count: usize,
    pub elapsed_ms: u128,
}

fn committed_param_type(xtype: XType) -> ParamType {
    match xtype {
        XType::XstructPtr(sid) => ParamType::StructPointer(sid),
        other => ParamType::Typed(other),
    }
}

/// Stage C: update every function's cheap callee-signature map, then re-solve
/// only functions whose committed interface or Stage-B declaration differs
/// from the Stage-A model. An unknown/UNSAT dirty solve leaves the Stage-A
/// selection and candidate indexing intact.
pub(crate) fn resolve_dirty_functions(
    functions: &mut [FunctionData],
    name_to_ident: &HashMap<String, Ident>,
    stage_a: &ProgramSelectionState,
    dirty: &BTreeSet<Address>,
    committed: &CommittedInterfaces,
    declaration_assignments: &BTreeMap<(Address, RTLReg), InterfaceClass>,
    maximal_flow_certification: bool,
) -> (ProgramSelectionState, DirtyResolveStats) {
    let started = std::time::Instant::now();
    let signatures = committed.callee_signatures();
    let mut state = stage_a.clone();
    let mut resolved_count = 0usize;
    let mut fallback_count = 0usize;

    for func in functions.iter_mut() {
        func.callee_signatures = signatures.clone();
        let mut globals = func.known_global_types.as_ref().clone();
        for (&ident, xtype) in &committed.globals {
            globals.by_ident.insert(
                ident,
                crate::decompile::passes::clight_select::wt_audit::xtype_to_clight(xtype),
            );
        }
        // `flow_anchors.global` was initially built from rank-0 types in the
        // query layer.  Stage C must replace that view at the same handoff as
        // the type-checker's map; otherwise a "committed GlobalType"
        // disagreement is actually measured against stale pre-Stage-B data.
        func.flow_anchors.global = globals
            .by_ident
            .iter()
            .filter_map(|(&ident, ty)| {
                let anchor =
                    crate::decompile::passes::clight_select::flow::claim_of_type(ty, func.ptr64);
                (!anchor.is_top()).then_some((ident, anchor))
            })
            .collect();
        func.known_global_types = Arc::new(globals);

        let own_signature = committed.function(func.address as Ident).cloned();
        let is_dirty = dirty.contains(&func.address);
        // A dirty function whose re-solve fails below keeps Stage B's committed signature over a
        // Stage-A body that was never selected against it. Reverting the signature here does NOT
        // fix that: `committed` is what every CALLER was already given, so a revert only moves the
        // disagreement to the call sites -- measured as +2 member-of-non-struct on `yes` and
        // `basename`. The inconsistency is not closable on the callee side; it needs Stage B to
        // stop committing interfaces the callee's candidate set cannot satisfy.
        if let Some(signature) = &own_signature {
            func.return_type =
                crate::decompile::passes::csh_pass::clight_type_from_xtype(&signature.return_type);
            for (position, xtype) in signature.param_types.iter().copied().enumerate() {
                if let Some(slot) = func.param_types.get_mut(position) {
                    *slot = committed_param_type(xtype);
                }
            }
        }
        if !is_dirty {
            continue;
        }

        // Candidate vectors are positional: the Stage-A selection stores
        // indices into them.  Build the Stage-C domain on a clone and publish
        // it only after a SAT solve, so Unknown/UNSAT truly preserves the
        // original selection rather than interpreting its indices in a
        // reordered vector.
        let mut resolve_func = func.clone();
        let mut pins = Vec::new();
        let mut materialize_pin = |reg: RTLReg, xtype: XType| {
            let committed_candidate = CandType::from_xtype(&xtype);
            let candidates = resolve_func.var_type_candidates.entry(reg).or_default();
            if let Some(index) = candidates
                .iter()
                .position(|candidate| *candidate == committed_candidate)
            {
                let candidate = candidates.remove(index);
                candidates.insert(0, candidate);
            } else {
                candidates.insert(0, committed_candidate);
            }
            if candidates.len() == 1 {
                if let Some(&previous) = resolve_func.var_types.get(&reg) {
                    if previous != committed_candidate {
                        candidates.push(previous);
                    }
                }
            }
            pins.push((reg, xtype));
        };
        if let Some(signature) = &own_signature {
            for (position, xtype) in signature.param_types.iter().copied().enumerate() {
                let Some(&reg) = func.param_regs.get(position) else {
                    continue;
                };
                materialize_pin(reg, xtype);
            }
        }
        for (&(address, reg), &class) in declaration_assignments {
            if address == func.address {
                materialize_pin(reg, class.representative_xtype());
            }
        }
        // A one-candidate vector still materializes a Ty variable;
        // cardinality was a generation artifact, never certainty.
        drop(materialize_pin);

        match solve_function_engine(
            &resolve_func,
            name_to_ident,
            &pins,
            maximal_flow_certification,
        ) {
            Ok((candidates, declarations, overrides, structure_world, SatResult::Sat)) => {
                *func = resolve_func;
                state.structure_world.insert(func.address, structure_world);
                state
                    .candidate_idx
                    .retain(|(address, _), _| *address != func.address);
                state
                    .var_decl_idx
                    .retain(|(address, _), _| *address != func.address);
                state
                    .var_type_override
                    .retain(|(address, _), _| *address != func.address);
                for (node, choice) in candidates {
                    state.candidate_idx.insert((func.address, node), choice);
                }
                for (reg, choice) in declarations {
                    state.var_decl_idx.insert((func.address, reg), choice);
                }
                for (reg, candidate) in overrides {
                    state
                        .var_type_override
                        .insert((func.address, reg), candidate);
                }
                resolved_count += 1;
            }
            Ok((_, _, _, _, grade)) => {
                fallback_count += 1;
                eprintln!(
                    "[interface-solve] WARN: dirty re-solve for {} ({:#x}) returned {:?}; retaining Stage-A selection",
                    func.name, func.address, grade
                );
            }
            Err(grade) => {
                fallback_count += 1;
                eprintln!(
                    "[interface-solve] WARN: dirty re-solve for {} ({:#x}) had no model ({:?}); retaining Stage-A selection",
                    func.name, func.address, grade
                );
            }
        }
    }

    // Stage-C solves run through the same engine dispatcher; report and reset here so their counters never leak into the next program's Stage-A summary.
    report_engine_stats(dirty.len(), maximal_flow_certification);
    dump_selection("stage-c", &state);
    (
        state,
        DirtyResolveStats {
            dirty_count: dirty.len(),
            resolved_count,
            fallback_count,
            elapsed_ms: started.elapsed().as_millis(),
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::passes::clight_select::ctyping;
    use crate::decompile::passes::clight_select::query::{
        CommittedFunctionInterface, InterfaceAuthority,
    };
    use crate::x86::types::{
        ClightAttr, ClightFloatSize, ClightIntSize, ClightSignedness, ClightUnaryOp,
    };
    use std::sync::Arc;
    use z3::ast::Ast; // for `.simplify()` on Bool, used in tests below

    fn synthetic_ids<const N: usize>() -> [u64; N] {
        std::array::from_fn(|index| index as u64 + 1)
    }

    fn a() -> ClightAttr {
        ClightAttr::default()
    }

    fn committed_param(address: Address, xtype: XType) -> CommittedInterfaces {
        let mut committed = CommittedInterfaces::default();
        committed.functions.insert(
            address as Ident,
            CommittedFunctionInterface {
                signature: CalleeSignature {
                    param_count: 1,
                    return_type: XType::Xvoid,
                    param_types: vec![xtype],
                    is_varargs: false,
                },
                authority: InterfaceAuthority::Reconciled,
            },
        );
        committed
    }

    #[test]
    fn structure_world_selection_never_mixes_correlated_node_candidates() {
        let func_addr = 0x1000;
        let first = 0x1010;
        let second = 0x1020;
        let structured = crate::decompile::analysis::structuring_pass::STRUCTURE_WORLD_STRUCTURED;
        let flat = crate::decompile::analysis::structuring_pass::STRUCTURE_WORLD_FLAT;
        let mut func = FunctionData::new(
            func_addr,
            "world_atomicity".into(),
            Vec::new(),
            Vec::new(),
            None,
            0,
            first,
            true,
        );
        func.structure_worlds = vec![structured, flat];
        func.authoritative_structure_world = structured;
        // Opposite local candidate orders make an independent node selector
        // prefer the unsound mixed pair.  World masks must force (0, 1) or
        // (1, 0), never (0, 0) or (1, 1).
        func.node_statements
            .insert(first, vec![ClightStmt::Sgoto(1), ClightStmt::Sgoto(2)]);
        func.candidate_structure_worlds.insert(
            first,
            vec![BTreeSet::from([structured]), BTreeSet::from([flat])],
        );
        func.node_statements
            .insert(second, vec![ClightStmt::Sgoto(3), ClightStmt::Sgoto(4)]);
        func.candidate_structure_worlds.insert(
            second,
            vec![BTreeSet::from([flat]), BTreeSet::from([structured])],
        );

        let (choices, _, _, selected_world) = solve_function(&func, &HashMap::new(), false);
        let first_choice = choices[&first].expect("first node is active");
        let second_choice = choices[&second].expect("second node is active");
        assert!(func.candidate_structure_worlds[&first][first_choice].contains(&selected_world));
        assert!(func.candidate_structure_worlds[&second][second_choice].contains(&selected_world));
        assert!(matches!((first_choice, second_choice), (0, 1) | (1, 0)));
    }

    #[test]
    fn dirty_unsat_preserves_stage_a_candidate_indices() {
        let [address] = synthetic_ids();
        let reg = 11;
        let mut func = FunctionData::new(
            address,
            "unsat_dirty".into(),
            vec![reg],
            vec![ParamType::Integer],
            None,
            0,
            1,
            true,
        );
        func.var_type_candidates
            .insert(reg, vec![CandType::I64(Sign::Signed), CandType::PtrVoid]);
        let before = func.var_type_candidates.clone();
        let stage_a = ProgramSelectionState {
            candidate_idx: HashMap::new(),
            structure_world: HashMap::new(),
            var_decl_idx: [((address, reg), 1)].into_iter().collect(),
            var_type_override: HashMap::new(),
        };
        let (state, stats) = resolve_dirty_functions(
            std::slice::from_mut(&mut func),
            &HashMap::new(),
            &stage_a,
            &[address].into_iter().collect(),
            &committed_param(address, XType::Xvoid),
            &BTreeMap::new(),
            false,
        );
        assert_eq!(stats.fallback_count, 1);
        assert_eq!(func.var_type_candidates, before);
        assert_eq!(state.var_decl_idx, stage_a.var_decl_idx);
        assert_eq!(state.candidate_idx, stage_a.candidate_idx);
    }

    #[test]
    fn dirty_float_pin_overrides_stage_a_float_pruning() {
        let [address] = synthetic_ids();
        let reg = 12;
        let mut func = FunctionData::new(
            address,
            "float_dirty".into(),
            vec![reg],
            vec![ParamType::Pointer],
            None,
            0,
            1,
            true,
        );
        func.var_type_candidates
            .insert(reg, vec![CandType::PtrVoid, CandType::F64]);
        let stage_a = ProgramSelectionState {
            candidate_idx: HashMap::new(),
            structure_world: HashMap::new(),
            var_decl_idx: [((address, reg), 0)].into_iter().collect(),
            var_type_override: HashMap::new(),
        };
        let (state, stats) = resolve_dirty_functions(
            std::slice::from_mut(&mut func),
            &HashMap::new(),
            &stage_a,
            &[address].into_iter().collect(),
            &committed_param(address, XType::Xfloat),
            &BTreeMap::new(),
            false,
        );
        assert_eq!(stats.resolved_count, 1);
        assert_eq!(stats.fallback_count, 0);
        let chosen = state.var_decl_idx[&(address, reg)];
        assert!(func.var_type_candidates[&reg][chosen].is_float());
    }

    #[test]
    fn dirty_scalar_pin_overrides_stage_a_pointer_pruning() {
        let [address] = synthetic_ids();
        let reg = 13;
        let mut func = FunctionData::new(
            address,
            "scalar_dirty".into(),
            vec![reg],
            vec![ParamType::Pointer],
            None,
            0,
            1,
            true,
        );
        func.var_type_candidates
            .insert(reg, vec![CandType::PtrVoid, CandType::I64(Sign::Signed)]);
        func.must_pointer_regs.insert(reg);
        let stage_a = ProgramSelectionState {
            candidate_idx: HashMap::new(),
            structure_world: HashMap::new(),
            var_decl_idx: [((address, reg), 0)].into_iter().collect(),
            var_type_override: HashMap::new(),
        };
        let (state, stats) = resolve_dirty_functions(
            std::slice::from_mut(&mut func),
            &HashMap::new(),
            &stage_a,
            &[address].into_iter().collect(),
            &committed_param(address, XType::Xlong),
            &BTreeMap::new(),
            false,
        );

        assert_eq!(stats.resolved_count, 1);
        assert_eq!(stats.fallback_count, 0);
        let chosen = state.var_decl_idx[&(address, reg)];
        assert_eq!(
            func.var_type_candidates[&reg][chosen],
            CandType::I64(Sign::Signed)
        );
    }

    #[test]
    fn stage_c_refreshes_flow_global_anchors_even_when_body_is_clean() {
        let [address] = synthetic_ids();
        let symbol = 0x9000usize;
        let mut func = FunctionData::new(
            address,
            "global_anchor".into(),
            Vec::new(),
            Vec::new(),
            None,
            0,
            1,
            true,
        );
        func.flow_anchors.global.insert(
            symbol,
            crate::decompile::passes::clight_select::flow::anchor_of_xtype(&XType::Xint, true),
        );
        let mut committed = CommittedInterfaces::default();
        committed.globals.insert(symbol, XType::Xfloat);
        let stage_a = ProgramSelectionState {
            candidate_idx: HashMap::new(),
            structure_world: HashMap::new(),
            var_decl_idx: HashMap::new(),
            var_type_override: HashMap::new(),
        };
        let (_, stats) = resolve_dirty_functions(
            std::slice::from_mut(&mut func),
            &HashMap::new(),
            &stage_a,
            &BTreeSet::new(),
            &committed,
            &BTreeMap::new(),
            false,
        );
        assert_eq!(stats.dirty_count, 0);
        assert_eq!(
            func.flow_anchors.global[&symbol],
            crate::decompile::passes::clight_select::flow::anchor_of_xtype(&XType::Xfloat, true,)
        );
    }

    #[test]
    fn maximal_certification_plans_one_deterministic_new_site_per_retry() {
        let injected: BTreeSet<Node> = [0x30, 0x10, 0x20].into_iter().collect();
        let mut exempt: BTreeSet<Node> = [0x10].into_iter().collect();
        assert_eq!(first_new_flow_exemption(&injected, &exempt), Some(0x20));
        exempt.insert(0x20);
        assert_eq!(first_new_flow_exemption(&injected, &exempt), Some(0x30));
        exempt.insert(0x30);
        assert_eq!(first_new_flow_exemption(&injected, &exempt), None);
    }

    #[test]
    fn maximal_certification_selects_propagator_without_environment_gate() {
        assert_eq!(selected_solve_engine(true), SolveEngine::Propagator);
        assert_eq!(selected_solve_engine(false), SolveEngine::Optimize);
    }

    // Class-level representatives: every Ty variant, both composite-id cases.
    fn type_set() -> Vec<ClightType> {
        use ClightFloatSize::*;
        use ClightIntSize::*;
        use ClightSignedness::*;
        vec![
            ClightType::Tvoid,
            ClightType::Tint(I32, Signed, a()),
            ClightType::Tint(I32, Unsigned, a()),
            ClightType::Tlong(Signed, a()),
            ClightType::Tlong(Unsigned, a()),
            ClightType::Tfloat(F32, a()),
            ClightType::Tfloat(F64, a()),
            ClightType::Tpointer(Arc::new(ClightType::Tlong(Signed, a())), a()),
            ClightType::Tpointer(Arc::new(ClightType::Tvoid), a()),
            ClightType::Tpointer(Arc::new(ClightType::Tfloat(F64, a())), a()),
            ClightType::Tpointer(Arc::new(ClightType::Tstruct(1, a())), a()),
            ClightType::Tstruct(1, a()),
            ClightType::Tstruct(2, a()),
            ClightType::Tunion(7, a()),
            ClightType::Tunion(8, a()),
            ClightType::Tfunction(
                Arc::new(vec![]),
                Arc::new(ClightType::Tvoid),
                Default::default(),
            ),
        ]
    }

    // A closed (variable-free) Bool term is valid iff it is true; the solver check is the robust ground-truth evaluator (simplify alone can leave datatype tester applications unreduced).
    fn eval_closed(b: &Bool) -> bool {
        if let Some(v) = b.clone().simplify().as_bool() {
            return v;
        }
        let s = z3::Solver::new();
        s.assert(&b.not());
        matches!(s.check(), SatResult::Unsat)
    }

    /// The Z3 relaxation and the executable checker must agree on every concrete class-level pair except the composite-id relaxation, where the test asserts soundness only.
    #[test]
    fn wt_cast_term_matches_ctyping() {
        z3::with_z3_config(&z3::Config::new(), || {
            let t = TypeDt::build();
            for from in type_set() {
                for to in type_set() {
                    let term = wt_cast_term(&t, &clight_to_ty(&t, &from), &clight_to_ty(&t, &to));
                    let z3_legal = eval_closed(&term);
                    let same_kind_composites = matches!(
                        (&from, &to),
                        (ClightType::Tstruct(..), ClightType::Tstruct(..))
                            | (ClightType::Tunion(..), ClightType::Tunion(..))
                    );
                    // Pointer width moves a cast between non-Default cases only (Pointer/I2I/L2L/I2L/L2I/...), never in or out of Default, so LEGALITY is width-independent and parity must hold at both.
                    for ptr64 in [true, false] {
                        let ct_legal = ctyping::wt_cast(ptr64, &from, &to);
                        if same_kind_composites {
                            assert!(
                                z3_legal || !ct_legal,
                                "wt_cast soundness (ptr64={}): {} -> {}",
                                ptr64,
                                ctyping::ty_str(&from),
                                ctyping::ty_str(&to)
                            );
                        } else {
                            assert_eq!(
                                z3_legal,
                                ct_legal,
                                "wt_cast parity (ptr64={}): {} -> {} (z3 {}, ctyping {})",
                                ptr64,
                                ctyping::ty_str(&from),
                                ctyping::ty_str(&to),
                                z3_legal,
                                ct_legal
                            );
                        }
                    }
                }
            }
        });
    }

    /// wt_cast_to_reg is wt_cast_term specialized to the pruned register domain (no bare func/void/union targets) -- they must agree there.
    #[test]
    fn wt_cast_to_reg_matches_full_on_pruned_domain() {
        use ClightFloatSize::*;
        use ClightSignedness::*;
        let reg_targets = vec![
            ClightType::Tint(ClightIntSize::I32, Signed, a()),
            ClightType::Tlong(Unsigned, a()),
            ClightType::Tfloat(F64, a()),
            ClightType::Tpointer(Arc::new(ClightType::Tlong(Signed, a())), a()),
            ClightType::Tstruct(1, a()),
        ];
        z3::with_z3_config(&z3::Config::new(), || {
            let t = TypeDt::build();
            for from in type_set() {
                for to in &reg_targets {
                    let full = eval_closed(&wt_cast_term(
                        &t,
                        &clight_to_ty(&t, &from),
                        &clight_to_ty(&t, to),
                    ));
                    let spec = eval_closed(&wt_cast_to_reg(
                        &t,
                        &clight_to_ty(&t, &from),
                        &clight_to_ty(&t, to),
                    ));
                    assert_eq!(
                        full,
                        spec,
                        "to-reg specialization: {} -> {}",
                        ctyping::ty_str(&from),
                        ctyping::ty_str(to)
                    );
                }
            }
        });
    }

    #[test]
    fn binop_legality_matches_ctyping() {
        use ClightBinaryOp::*;
        let ops = [
            Oadd, Osub, Omul, Odiv, Omod, Oand, Oor, Oxor, Oshl, Oshr, Oeq, One, Olt, Ogt, Ole, Oge,
        ];
        z3::with_z3_config(&z3::Config::new(), || {
            let t = TypeDt::build();
            for op in ops {
                for l in type_set() {
                    for r in type_set() {
                        let term =
                            binop_legal_term(&t, op, &clight_to_ty(&t, &l), &clight_to_ty(&t, &r));
                        let z3_legal = eval_closed(&term);
                        // The z3 encoding classifies with width-agnostic is_ptrish/is_intish, so legality must agree at BOTH pointer widths; only the ptr-minus-ptr RESULT type moves with the width.
                        for ptr64 in [true, false] {
                            let ct_legal = ctyping::type_binop(ptr64, op, &l, &r).is_some();
                            assert_eq!(
                                z3_legal,
                                ct_legal,
                                "binop parity (ptr64={}): {:?} on ({}, {})",
                                ptr64,
                                op,
                                ctyping::ty_str(&l),
                                ctyping::ty_str(&r)
                            );
                        }
                    }
                }
            }
        });
    }

    // Soundness of hardening the pointer/float arm: whenever the hard clause is violated, EVERY binop is
    // ill-typed under ctyping, so the clause can never cut off a selection that would have printed valid C.
    // A pair the clause rejects but some op accepts would be a silent loss of a legal program.
    #[test]
    fn ptr_float_mix_is_illegal_for_every_binop() {
        use ClightBinaryOp::*;
        let ops = [
            Oadd, Osub, Omul, Odiv, Omod, Oand, Oor, Oxor, Oshl, Oshr, Oeq, One, Olt, Ogt, Ole, Oge,
        ];
        z3::with_z3_config(&z3::Config::new(), || {
            let t = TypeDt::build();
            let mut violations = 0usize;
            for l in type_set() {
                for r in type_set() {
                    let (ltm, rtm) = (clight_to_ty(&t, &l), clight_to_ty(&t, &r));
                    for (ptr_side, float_side, lhs_is_ptr) in
                        [(&ltm, &rtm, true), (&rtm, &ltm, false)]
                    {
                        if eval_closed(&no_ptr_float_term(&t, ptr_side, float_side)) {
                            continue;
                        }
                        violations += 1;
                        for op in ops {
                            for ptr64 in [true, false] {
                                assert!(
                                    ctyping::type_binop(ptr64, op, &l, &r).is_none(),
                                    "hard ptr/float clause rejects a pair ctyping accepts (ptr64={}, lhs_is_ptr={}): {:?} on ({}, {})",
                                    ptr64,
                                    lhs_is_ptr,
                                    op,
                                    ctyping::ty_str(&l),
                                    ctyping::ty_str(&r)
                                );
                            }
                        }
                    }
                }
            }
            // Guard against the clause silently becoming vacuous (e.g. if is_ptrish or is_float lost a variant).
            assert!(
                violations > 0,
                "the ptr/float clause never fired over type_set(); it is no longer constraining anything"
            );
        });
    }

    #[test]
    fn unop_legality_matches_ctyping() {
        use ClightUnaryOp::*;
        z3::with_z3_config(&z3::Config::new(), || {
            let t = TypeDt::build();
            for op in [Onotbool, Onotint, Oneg, Oabsfloat] {
                for x in type_set() {
                    let term = unop_legal_term(&t, op, &clight_to_ty(&t, &x));
                    let z3_legal = eval_closed(&term);
                    // Width-agnostic on the z3 side, so parity must hold at both widths.
                    for ptr64 in [true, false] {
                        let ct_legal = ctyping::type_unop(ptr64, op, &x).is_some();
                        assert_eq!(
                            z3_legal,
                            ct_legal,
                            "unop parity (ptr64={}): {:?} on {}",
                            ptr64,
                            op,
                            ctyping::ty_str(&x)
                        );
                    }
                }
            }
        });
    }

    /// D8 lockstep: both declaration consumers agree, for EVERY candidate variant, on whether it
    /// is a pointer and whether it is a float. Both are total matches now, so this catches a new
    /// variant being classified inconsistently rather than a string falling to a `long` default.
    #[test]
    fn candidate_vocabulary_lockstep() {
        use crate::decompile::passes::c_pass::types::CType;
        use crate::decompile::passes::clight_select::candtype::all_variants;
        use crate::decompile::passes::clight_select::wt_audit::candtype_to_clight;
        for candidate in all_variants() {
            let ctype = crate::decompile::passes::c_pass::helpers::candtype_to_ctype(
                candidate,
                crate::abi::DataModel::Lp64,
            );
            let clight = candtype_to_clight(candidate);
            assert_eq!(
                matches!(ctype, CType::Pointer(..)),
                candidate.is_pointer(),
                "emitter disagrees on pointerness of {:?}",
                candidate
            );
            assert_eq!(
                matches!(clight, ClightType::Tpointer(..)),
                candidate.is_pointer(),
                "checker disagrees on pointerness of {:?}",
                candidate
            );
            assert_eq!(
                matches!(ctype, CType::Float(_)),
                candidate.is_float(),
                "emitter disagrees on floatness of {:?}",
                candidate
            );
            assert_eq!(
                matches!(clight, ClightType::Tfloat(..)),
                candidate.is_float(),
                "checker disagrees on floatness of {:?}",
                candidate
            );
        }
    }

    #[test]
    fn authoritative_global_type_drives_exact_statement_repick() {
        use crate::decompile::passes::clight_select::query::KnownGlobalTypes;

        let attr = ClightAttr::default();
        let tlong = ClightType::Tlong(ClightSignedness::Signed, attr.clone());
        let tdouble = ClightType::Tfloat(ClightFloatSize::F64, attr.clone());
        let tchar_ptr = ClightType::Tpointer(
            Arc::new(ClightType::Tint(
                ClightIntSize::I8,
                ClightSignedness::Signed,
                attr,
            )),
            ClightAttr::default(),
        );

        // The machine load is annotated `long`, while the authoritative emitted
        // declaration is a character pointer. Synthetic identifiers keep this
        // regression independent of any particular binary layout.
        let [global_raw, reg, func_addr, load_node, other_use] = synthetic_ids();
        let global = global_raw as Ident;
        let mut func = FunctionData::new(
            func_addr,
            "authoritative-global-repick".to_string(),
            Vec::new(),
            Vec::new(),
            None,
            0,
            func_addr,
            true,
        );
        func.used_regs.insert(reg);
        func.var_types.insert(reg, CandType::F64);
        func.var_type_candidates
            .insert(reg, vec![CandType::F64, CandType::I64(Sign::Signed)]);
        func.known_global_types = Arc::new(KnownGlobalTypes {
            by_ident: [(global, tchar_ptr)].into_iter().collect(),
            ..KnownGlobalTypes::default()
        });
        func.node_statements.insert(
            load_node,
            vec![
                ClightStmt::Sset(
                    reg as Ident,
                    ClightExpr::Ecast(Box::new(ClightExpr::Evar(global, tlong.clone())), tdouble),
                ),
                ClightStmt::Sset(reg as Ident, ClightExpr::Evar(global, tlong.clone())),
            ],
        );
        // Keep the model on the integer declaration, as the real function's
        // other uses did, so this specifically tests post-model re-picking.
        func.node_statements.insert(
            other_use,
            vec![ClightStmt::Sswitch(
                ClightExpr::Etempvar(reg as Ident, tlong),
                Vec::new(),
            )],
        );

        let (statement_idx, declaration_idx, _, _) = solve_function(&func, &HashMap::new(), false);
        assert_eq!(declaration_idx.get(&reg), Some(&1));
        assert_eq!(statement_idx.get(&load_node), Some(&Some(1)));
    }

    #[test]
    fn exact_statement_repick_rejects_a_void_lvalue_store() {
        let attr = ClightAttr::default();
        let tlong = ClightType::Tlong(ClightSignedness::Signed, attr.clone());
        let tint = ClightType::Tint(ClightIntSize::I32, ClightSignedness::Signed, attr.clone());
        let tchar = ClightType::Tint(ClightIntSize::I8, ClightSignedness::Unsigned, attr.clone());
        let ptr_void = ClightType::Tpointer(Arc::new(ClightType::Tvoid), attr.clone());
        let ptr_char = ClightType::Tpointer(Arc::new(tchar.clone()), attr);

        let [reg, func_addr, store_node] = synthetic_ids();
        let mut func = FunctionData::new(
            func_addr,
            "void-lvalue-repick".to_string(),
            Vec::new(),
            Vec::new(),
            None,
            0,
            func_addr,
            true,
        );
        func.used_regs.insert(reg);
        func.var_types.insert(reg, CandType::PtrVoid);
        func.var_type_candidates
            .insert(reg, vec![CandType::PtrVoid, CandType::PtrChar]);

        let base = ClightExpr::Etempvar(reg as Ident, tlong);
        let rhs = ClightExpr::EconstInt(0, tint);
        func.node_statements.insert(
            store_node,
            vec![
                ClightStmt::Sassign(
                    ClightExpr::Ederef(
                        Box::new(ClightExpr::Ecast(Box::new(base.clone()), ptr_void)),
                        ClightType::Tvoid,
                    ),
                    rhs.clone(),
                ),
                ClightStmt::Sassign(
                    ClightExpr::Ederef(
                        Box::new(ClightExpr::Ecast(Box::new(base), ptr_char)),
                        tchar,
                    ),
                    rhs,
                ),
            ],
        );

        let (statement_idx, _, _, _) = solve_function(&func, &HashMap::new(), false);
        assert_eq!(statement_idx.get(&store_node), Some(&Some(1)));
    }

    #[test]
    fn must_pointer_fact_overrides_an_integer_declaration_prior() {
        let [reg, func_addr] = synthetic_ids();
        let mut func = FunctionData::new(
            func_addr,
            "must-pointer".to_string(),
            Vec::new(),
            Vec::new(),
            None,
            0,
            func_addr,
            true,
        );
        func.used_regs.insert(reg);
        func.must_pointer_regs.insert(reg);
        func.var_types.insert(reg, CandType::I32(Sign::Signed));
        func.var_type_candidates
            .insert(reg, vec![CandType::I32(Sign::Signed), CandType::PtrChar]);

        let (_, declarations, _, _) = solve_function(&func, &HashMap::new(), false);

        assert_eq!(declarations.get(&reg), Some(&1));
    }
}
