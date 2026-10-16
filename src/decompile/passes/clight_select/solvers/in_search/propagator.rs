//! Minimal safe bindings for Z3's user-propagator API plus the raw `Z3_solver`
//! handle it has to be attached to.
//!
//! The `z3` 0.20 crate wraps neither the propagator API nor the raw solver
//! pointer (`Solver::z3_slv` is private and has no accessor), so a propagator
//! solve cannot reuse `z3::Solver`. Everything here goes through `z3-sys` on the
//! thread-local `z3::Context`, so the ASTs built by the high-level crate
//! (`Bool`, `Dynamic`) are usable unchanged.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::ffi::{CStr, CString};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

use z3::ast::{Ast, Bool, Dynamic};
use z3::{Context, SatResult};
use z3_sys::*;

// Times Z3 asked for a fresh propagator state for a spawned sub-solver. A plain
// Z3_mk_solver never does this; a nonzero count means some spawned solver ran
// without the theory and its models are not theory-consistent.
static FRESH_CALLS: AtomicUsize = AtomicUsize::new(0);

pub fn fresh_callback_count() -> usize {
    FRESH_CALLS.load(Ordering::Relaxed)
}

/// A behavioral theory consulted during the search. Terms are identified by
/// their index into the slice handed to `RawSolver::attach`.
pub trait Theory {
    /// A registered term was fixed to `value`.
    fn on_fixed(&mut self, cb: &PropCb<'_>, term: usize, value: bool);
    /// Every decision variable is assigned; last chance to reject the model.
    fn on_final(&mut self, _cb: &PropCb<'_>) {}
    /// Z3 opened a backtracking scope. A theory that remembers fixed values
    /// must mark its trail here.
    fn on_push(&mut self) {}
    /// Z3 backtracked out of `n` scopes; everything fixed inside them is unfixed
    /// again.
    fn on_pop(&mut self, _n: u32) {}
}

/// A theory that is nothing but a veto set: every registered term is a
/// candidate literal some evidence has ruled out, so the search fixing any of
/// them to true is an immediate conflict.
///
/// Both behavioral theories have exactly this shape, and several can share one
/// propagator by concatenating their veto lists; the per-term tag keeps their
/// statistics apart afterwards.
pub struct VetoTheory {
    tags: Vec<&'static str>,
    pub fired: BTreeMap<&'static str, usize>,
    pub conflicts: BTreeMap<&'static str, usize>,
}

impl VetoTheory {
    /// `tags[i]` names the evidence that vetoed registered term `i`.
    pub fn new(tags: Vec<&'static str>) -> Self {
        VetoTheory {
            tags,
            fired: BTreeMap::new(),
            conflicts: BTreeMap::new(),
        }
    }

    pub fn fired_for(&self, tag: &str) -> usize {
        self.fired.get(tag).copied().unwrap_or(0)
    }

    pub fn conflicts_for(&self, tag: &str) -> usize {
        self.conflicts.get(tag).copied().unwrap_or(0)
    }
}

impl Theory for VetoTheory {
    fn on_fixed(&mut self, cb: &PropCb<'_>, term: usize, value: bool) {
        if !value {
            return;
        }
        let Some(&tag) = self.tags.get(term) else {
            return;
        };
        *self.fired.entry(tag).or_default() += 1;
        if cb.conflict(&[term]) {
            *self.conflicts.entry(tag).or_default() += 1;
        }
    }
}

/// Callback handle valid only for the duration of one propagator callback.
pub struct PropCb<'a> {
    ctx: Z3_context,
    cb: Z3_solver_callback,
    terms: &'a [Bool],
}

impl PropCb<'_> {
    /// Reject the current partial assignment: the listed fixed terms cannot all
    /// hold together. Encoded as a consequence of `false`, which is Z3's
    /// conflict form.
    pub fn conflict(&self, premise: &[usize]) -> bool {
        let asts: Vec<Z3_ast> = premise
            .iter()
            .filter_map(|i| self.terms.get(*i))
            .map(|b| b.get_z3_ast())
            .collect();
        let Some(f) = (unsafe { Z3_mk_false(self.ctx) }) else {
            return false;
        };
        unsafe {
            Z3_solver_propagate_consequence(
                self.ctx,
                self.cb,
                asts.len() as u32,
                asts.as_ptr(),
                0,
                std::ptr::null(),
                std::ptr::null(),
                f,
            )
        }
    }

    /// Propagate `conseq` as implied by the listed fixed terms.
    pub fn propagate(&self, premise: &[usize], conseq: &Bool) -> bool {
        let asts: Vec<Z3_ast> = premise
            .iter()
            .filter_map(|i| self.terms.get(*i))
            .map(|b| b.get_z3_ast())
            .collect();
        unsafe {
            Z3_solver_propagate_consequence(
                self.ctx,
                self.cb,
                asts.len() as u32,
                asts.as_ptr(),
                0,
                std::ptr::null(),
                std::ptr::null(),
                conseq.get_z3_ast(),
            )
        }
    }
}

// The user_context Z3 hands back to every callback. Address stability comes from
// the Box; RawSolver keeps it alive for the solver's whole life.
struct PropState {
    // Carried explicitly rather than read from the thread-local: a callback must
    // resolve terms against the context that owns them, whatever thread runs it.
    ctx: Option<Z3_context>,
    theory: Option<Rc<RefCell<dyn Theory>>>,
    terms: Vec<Bool>,
    // Z3_get_ast_id of each registered term -> its index in `terms`.
    ids: HashMap<u32, usize>,
}

impl PropState {
    fn term_index(&self, ctx: Z3_context, t: Z3_ast) -> Option<usize> {
        let id = unsafe { Z3_get_ast_id(ctx, t) };
        self.ids.get(&id).copied()
    }
}

// No callback may unwind into C; every body is wrapped and a panic is swallowed
// (it degrades the theory to a no-op, never corrupts the solver).
unsafe extern "C" fn fixed_eh(
    user: *mut std::ffi::c_void,
    cb: Z3_solver_callback,
    t: Z3_ast,
    value: Z3_ast,
) {
    let _ = catch_unwind(AssertUnwindSafe(|| {
        if user.is_null() {
            return;
        }
        let state = unsafe { &mut *(user as *mut PropState) };
        let (Some(theory), Some(ctx)) = (state.theory.clone(), state.ctx) else {
            return;
        };
        let Some(index) = state.term_index(ctx, t) else {
            return;
        };
        let truth = match unsafe { Z3_get_bool_value(ctx, value) } {
            Z3_L_TRUE => true,
            Z3_L_FALSE => false,
            _ => return,
        };
        let handle = PropCb {
            ctx,
            cb,
            terms: &state.terms,
        };
        theory.borrow_mut().on_fixed(&handle, index, truth);
    }));
}

unsafe extern "C" fn final_eh(user: *mut std::ffi::c_void, cb: Z3_solver_callback) {
    let _ = catch_unwind(AssertUnwindSafe(|| {
        if user.is_null() {
            return;
        }
        let state = unsafe { &mut *(user as *mut PropState) };
        let (Some(theory), Some(ctx)) = (state.theory.clone(), state.ctx) else {
            return;
        };
        let handle = PropCb {
            ctx,
            cb,
            terms: &state.terms,
        };
        theory.borrow_mut().on_final(&handle);
    }));
}

// Scope hooks forward to the theory, which is what lets a stateful one keep a
// trail of fixed values that survives backtracking correctly.
unsafe extern "C" fn scope_push(user: *mut std::ffi::c_void) {
    let _ = catch_unwind(AssertUnwindSafe(|| {
        if user.is_null() {
            return;
        }
        let state = unsafe { &mut *(user as *mut PropState) };
        if let Some(theory) = state.theory.clone() {
            theory.borrow_mut().on_push();
        }
    }));
}

unsafe extern "C" fn scope_pop(user: *mut std::ffi::c_void, n: u32) {
    let _ = catch_unwind(AssertUnwindSafe(|| {
        if user.is_null() {
            return;
        }
        let state = unsafe { &mut *(user as *mut PropState) };
        if let Some(theory) = state.theory.clone() {
            theory.borrow_mut().on_pop(n);
        }
    }));
}

unsafe extern "C" fn push_eh(user: *mut std::ffi::c_void, _cb: Z3_solver_callback) {
    unsafe { scope_push(user) };
}

unsafe extern "C" fn pop_eh(user: *mut std::ffi::c_void, _cb: Z3_solver_callback, n: u32) {
    unsafe { scope_pop(user, n) };
}

// A spawned sub-solver lives in another context, so our registered terms mean
// nothing there; hand it a theory-free state rather than terms from the wrong
// context. The leak is one empty struct per spawn and the counter makes the
// event visible instead of silent.
unsafe extern "C" fn fresh_eh(
    _user: *mut std::ffi::c_void,
    _new_ctx: Z3_context,
) -> *mut std::ffi::c_void {
    FRESH_CALLS.fetch_add(1, Ordering::Relaxed);
    let empty = Box::new(PropState {
        ctx: None,
        theory: None,
        terms: Vec::new(),
        ids: HashMap::new(),
    });
    Box::into_raw(empty) as *mut std::ffi::c_void
}

/// A model owned outside the `z3` crate's `Model` wrapper.
pub struct RawModel {
    // Keeps the context alive independently of the thread-local, which
    // `with_z3_config` swaps back on the way out.
    _owner: Context,
    ctx: Z3_context,
    model: Z3_model,
}

impl RawModel {
    fn eval_raw(&self, ast: Z3_ast, completion: bool) -> Option<Z3_ast> {
        let mut out: Z3_ast = ast;
        let ok = unsafe { Z3_model_eval(self.ctx, self.model, ast, completion, &mut out) };
        if !ok {
            return None;
        }
        unsafe { Z3_inc_ref(self.ctx, out) };
        Some(out)
    }

    pub fn eval_bool(&self, b: &Bool) -> Option<bool> {
        let v = self.eval_raw(b.get_z3_ast(), true)?;
        let truth = match unsafe { Z3_get_bool_value(self.ctx, v) } {
            Z3_L_TRUE => Some(true),
            Z3_L_FALSE => Some(false),
            _ => None,
        };
        unsafe { Z3_dec_ref(self.ctx, v) };
        truth
    }

    pub fn eval_i64(&self, d: &Dynamic) -> Option<i64> {
        let v = self.eval_raw(d.get_z3_ast(), true)?;
        let mut out: i64 = 0;
        let ok = unsafe { Z3_get_numeral_int64(self.ctx, v, &mut out) };
        unsafe { Z3_dec_ref(self.ctx, v) };
        if ok {
            Some(out)
        } else {
            None
        }
    }
}

impl Drop for RawModel {
    fn drop(&mut self) {
        unsafe { Z3_model_dec_ref(self.ctx, self.model) };
    }
}

/// A `Z3_solver` we own outright, so a user propagator can be attached to it.
pub struct RawSolver {
    // Keeps the context alive independently of the thread-local, which
    // `with_z3_config` swaps back on the way out.
    owner: Context,
    ctx: Z3_context,
    solver: Z3_solver,
    // Declared after `solver` so it outlives the dec_ref in Drop.
    state: Option<Box<PropState>>,
}

impl RawSolver {
    /// A plain incremental SMT solver ("smt" tactic). `Z3_mk_solver`'s combined
    /// solver switches between two sub-solvers, which is exactly the spawning
    /// the propagator cannot follow.
    pub fn new_simple() -> Self {
        let owner = Context::thread_local();
        let ctx = owner.get_z3_context();
        let solver =
            unsafe { Z3_mk_simple_solver(ctx) }.expect("Z3_mk_simple_solver returned null");
        unsafe { Z3_solver_inc_ref(ctx, solver) };
        RawSolver {
            owner,
            ctx,
            solver,
            state: None,
        }
    }

    pub fn set_params_u32(&self, entries: &[(&str, u32)]) {
        let params = unsafe { Z3_mk_params(self.ctx) }.expect("Z3_mk_params returned null");
        unsafe { Z3_params_inc_ref(self.ctx, params) };
        for (key, value) in entries {
            let name = CString::new(*key).expect("param name has no interior nul");
            let sym = unsafe { Z3_mk_string_symbol(self.ctx, name.as_ptr()) }
                .expect("Z3_mk_string_symbol returned null");
            unsafe { Z3_params_set_uint(self.ctx, params, sym, *value) };
        }
        unsafe { Z3_solver_set_params(self.ctx, self.solver, params) };
        unsafe { Z3_params_dec_ref(self.ctx, params) };
    }

    /// Install the (still theory-less) propagator plugin. Call this before
    /// asserting anything, so the plugin exists while the assertions are
    /// internalized; the theory itself can be supplied later.
    pub fn init_propagator(&mut self) {
        let mut state = Box::new(PropState {
            ctx: Some(self.ctx),
            theory: None,
            terms: Vec::new(),
            ids: HashMap::new(),
        });
        let user = state.as_mut() as *mut PropState as *mut std::ffi::c_void;
        unsafe {
            Z3_solver_propagate_init(
                self.ctx,
                self.solver,
                user,
                Some(push_eh),
                Some(pop_eh),
                Some(fresh_eh),
            );
            Z3_solver_propagate_fixed(self.ctx, self.solver, Some(fixed_eh));
            Z3_solver_propagate_final(self.ctx, self.solver, Some(final_eh));
        }
        self.state = Some(state);
    }

    /// Supply the theory and register the terms it watches. Must run before any
    /// `check`, and after `init_propagator`.
    pub fn set_theory(&mut self, theory: Rc<RefCell<dyn Theory>>, terms: Vec<Bool>) {
        let state = self
            .state
            .as_mut()
            .expect("set_theory requires init_propagator");
        state.ids.clear();
        for (index, term) in terms.iter().enumerate() {
            let id = unsafe { Z3_get_ast_id(self.ctx, term.get_z3_ast()) };
            state.ids.insert(id, index);
        }
        state.terms = terms;
        state.theory = Some(theory);
        for term in &state.terms {
            unsafe { Z3_solver_propagate_register(self.ctx, self.solver, term.get_z3_ast()) };
        }
    }

    /// Attach `theory` and register `terms` in one step.
    pub fn attach(&mut self, theory: Rc<RefCell<dyn Theory>>, terms: Vec<Bool>) {
        self.init_propagator();
        self.set_theory(theory, terms);
    }

    pub fn assert(&self, c: &Bool) {
        unsafe { Z3_solver_assert(self.ctx, self.solver, c.get_z3_ast()) };
    }

    pub fn push(&self) {
        unsafe { Z3_solver_push(self.ctx, self.solver) };
    }

    pub fn pop(&self, n: u32) {
        unsafe { Z3_solver_pop(self.ctx, self.solver, n) };
    }

    pub fn check(&self) -> SatResult {
        lbool_to_sat(unsafe { Z3_solver_check(self.ctx, self.solver) })
    }

    pub fn check_assumptions(&self, assumptions: &[Bool]) -> SatResult {
        let asts: Vec<Z3_ast> = assumptions.iter().map(|b| b.get_z3_ast()).collect();
        lbool_to_sat(unsafe {
            Z3_solver_check_assumptions(self.ctx, self.solver, asts.len() as u32, asts.as_ptr())
        })
    }

    pub fn model(&self) -> Option<RawModel> {
        let model = unsafe { Z3_solver_get_model(self.ctx, self.solver) }?;
        unsafe { Z3_model_inc_ref(self.ctx, model) };
        Some(RawModel {
            _owner: self.owner.clone(),
            ctx: self.ctx,
            model,
        })
    }

    pub fn reason_unknown(&self) -> Option<String> {
        let p = unsafe { Z3_solver_get_reason_unknown(self.ctx, self.solver) };
        if p.is_null() {
            return None;
        }
        unsafe { CStr::from_ptr(p) }
            .to_str()
            .ok()
            .map(str::to_owned)
    }
}

impl Drop for RawSolver {
    fn drop(&mut self) {
        unsafe { Z3_solver_dec_ref(self.ctx, self.solver) };
    }
}

fn lbool_to_sat(v: Z3_lbool) -> SatResult {
    match v {
        Z3_L_TRUE => SatResult::Sat,
        Z3_L_FALSE => SatResult::Unsat,
        _ => SatResult::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use crate::decompile::passes::clight_select::solvers::in_search::propagator::*;

    // Vetoes every listed term the search fixes to true, and counts the vetoes.
    struct VetoTheory {
        vetoed: Vec<usize>,
        fired: usize,
    }

    impl Theory for VetoTheory {
        fn on_fixed(&mut self, cb: &PropCb<'_>, term: usize, value: bool) {
            if value && self.vetoed.contains(&term) {
                self.fired += 1;
                cb.conflict(&[term]);
            }
        }
    }

    // Propagates one lemma the moment any registered term is fixed, exercising
    // the non-conflict consequence path.
    struct LemmaTheory {
        lemma: Bool,
        fired: usize,
    }

    impl Theory for LemmaTheory {
        fn on_fixed(&mut self, cb: &PropCb<'_>, term: usize, _value: bool) {
            self.fired += 1;
            cb.propagate(&[term], &self.lemma);
        }
    }

    // Exactly-one over three booleans; the propagator vetoes b0 and b1 on fixed,
    // so the only survivor is b2.
    #[test]
    fn propagator_veto_forces_the_surviving_candidate() {
        let cfg = z3::Config::new();
        z3::with_z3_config(&cfg, || {
            let vars: Vec<Bool> = (0..3).map(|_| Bool::fresh_const("t")).collect();
            let mut solver = RawSolver::new_simple();
            let refs: Vec<(&Bool, i32)> = vars.iter().map(|b| (b, 1)).collect();
            solver.assert(&Bool::pb_eq(&refs, 1));
            let theory = Rc::new(RefCell::new(VetoTheory {
                vetoed: vec![0, 1],
                fired: 0,
            }));
            solver.attach(theory.clone(), vars.clone());

            assert_eq!(solver.check(), SatResult::Sat);
            let model = solver.model().expect("sat check must yield a model");
            assert_eq!(model.eval_bool(&vars[0]), Some(false));
            assert_eq!(model.eval_bool(&vars[1]), Some(false));
            assert_eq!(model.eval_bool(&vars[2]), Some(true));

            // Forcing a vetoed candidate must be unsatisfiable, which also
            // guarantees the veto ran rather than the model order happening to
            // avoid it.
            assert_eq!(
                solver.check_assumptions(&[vars[0].clone()]),
                SatResult::Unsat
            );
            assert_eq!(
                solver.check_assumptions(&[vars[1].clone()]),
                SatResult::Unsat
            );
            assert!(theory.borrow().fired > 0, "the veto must actually fire");
            assert_eq!(fresh_callback_count(), 0);
        });
    }

    // Same shape, but the theory forces the survivor by propagating a lemma
    // instead of raising a conflict, proving the consequence path carries real
    // implications and not only conflicts.
    #[test]
    fn propagator_lemma_forces_the_surviving_candidate() {
        let cfg = z3::Config::new();
        z3::with_z3_config(&cfg, || {
            let vars: Vec<Bool> = (0..3).map(|_| Bool::fresh_const("l")).collect();
            let mut solver = RawSolver::new_simple();
            let refs: Vec<(&Bool, i32)> = vars.iter().map(|b| (b, 1)).collect();
            solver.assert(&Bool::pb_eq(&refs, 1));
            let theory = Rc::new(RefCell::new(LemmaTheory {
                lemma: vars[2].clone(),
                fired: 0,
            }));
            solver.attach(theory.clone(), vars.clone());

            assert_eq!(solver.check(), SatResult::Sat);
            let model = solver.model().expect("sat check must yield a model");
            assert_eq!(model.eval_bool(&vars[2]), Some(true));
            // The lemma has force: assuming a rival candidate contradicts it.
            assert_eq!(
                solver.check_assumptions(&[vars[0].clone()]),
                SatResult::Unsat
            );
            assert!(theory.borrow().fired > 0);
        });
    }

    // The veto must survive push/pop and assumption-driven checks, which is how
    // the stratified MaxSAT loop drives the solver.
    #[test]
    fn propagator_veto_survives_push_pop() {
        let cfg = z3::Config::new();
        z3::with_z3_config(&cfg, || {
            let vars: Vec<Bool> = (0..3).map(|_| Bool::fresh_const("p")).collect();
            let mut solver = RawSolver::new_simple();
            let refs: Vec<(&Bool, i32)> = vars.iter().map(|b| (b, 1)).collect();
            solver.assert(&Bool::pb_eq(&refs, 1));
            let theory = Rc::new(RefCell::new(VetoTheory {
                vetoed: vec![0, 1],
                fired: 0,
            }));
            solver.attach(theory.clone(), vars.clone());

            solver.push();
            solver.assert(&vars[2].not());
            assert_eq!(solver.check(), SatResult::Unsat);
            solver.pop(1);

            assert_eq!(solver.check(), SatResult::Sat);
            let model = solver.model().expect("sat check must yield a model");
            assert_eq!(model.eval_bool(&vars[2]), Some(true));

            assert_eq!(solver.check_assumptions(&[vars[2].clone()]), SatResult::Sat);
            assert_eq!(
                solver.check_assumptions(&[vars[0].clone()]),
                SatResult::Unsat
            );
        });
    }

    // A panicking callback must not unwind into Z3.
    #[test]
    fn panicking_theory_is_contained() {
        struct Boom;
        impl Theory for Boom {
            fn on_fixed(&mut self, _cb: &PropCb<'_>, _term: usize, _value: bool) {
                panic!("theory panic");
            }
        }
        let cfg = z3::Config::new();
        z3::with_z3_config(&cfg, || {
            let vars: Vec<Bool> = (0..2).map(|_| Bool::fresh_const("b")).collect();
            let mut solver = RawSolver::new_simple();
            let refs: Vec<(&Bool, i32)> = vars.iter().map(|b| (b, 1)).collect();
            solver.assert(&Bool::pb_eq(&refs, 1));
            solver.attach(Rc::new(RefCell::new(Boom)), vars.clone());
            let hook = std::panic::take_hook();
            std::panic::set_hook(Box::new(|_| {}));
            let result = solver.check();
            std::panic::set_hook(hook);
            assert_eq!(result, SatResult::Sat);
        });
    }
}
