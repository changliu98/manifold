use rayon::prelude::*;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;
use std::sync::Arc;

use crate::decompile::passes::clight_select::syntax::c_types::*;
use crate::decompile::passes::clight_select::syntax::constraints::{
    ConstraintSink, ModelView, RecordedCond, SolveBackend, Tier, TierCost, SOFT_CLAUSES, SOFT_TAGS,
};
use crate::decompile::passes::clight_select::syntax::{
    self, Artifacts, Candidate, DeclarationContext, FunctionContext, Stack,
};
use z3::ast::{Bool, Dynamic};
use z3::{Optimize, SatResult};

mod audit;

use crate::decompile::elevator::config::CONFIG;
use crate::decompile::passes::clight_select::candtype::{CandType, Sign};
use crate::decompile::passes::clight_select::query::{
    CommittedInterfaces, FunctionData, InterfaceClass,
};
use crate::decompile::passes::clight_select::select::ProgramSelectionState;
use crate::decompile::passes::clight_select::solvers::in_search::propagator::{
    RawSolver, VetoTheory,
};
use crate::x86::types::{
    Address, ClightBinaryOp, ClightExpr, ClightIntSize, ClightStmt, ClightType, Ident, Node,
    ParamType, RTLReg, XType,
};

struct OptimizeBackend<'a> {
    opt: &'a Optimize,
    // Asserted by `flush` once every weight is known; also prices the model for the engine A/B.
    softs: RefCell<Vec<(Bool, u64)>>,
    // Each soft clause's objective level, which prices a model across functions.
    levels: RefCell<Vec<(Bool, Tier, u64)>>,
}

impl<'a> OptimizeBackend<'a> {
    fn new(opt: &'a Optimize) -> Self {
        OptimizeBackend {
            opt,
            softs: RefCell::new(Vec::new()),
            levels: RefCell::new(Vec::new()),
        }
    }

    fn into_softs(self) -> (Vec<(Bool, u64)>, Vec<(Bool, Tier, u64)>) {
        (self.softs.into_inner(), self.levels.into_inner())
    }
}

impl SolveBackend for OptimizeBackend<'_> {
    fn assert_hard(&self, cond: &Bool) {
        self.opt.assert(cond);
    }
    // Deferred to `flush`: the strata are known only once every weight is.
    fn assert_soft(&self, cond: &Bool, weight: u64) {
        self.softs.borrow_mut().push((cond.clone(), weight));
    }
    fn assert_soft_at(&self, cond: &Bool, weight: u64, tier: Tier, units: u64) {
        self.levels.borrow_mut().push((cond.clone(), tier, units));
        self.assert_soft(cond, weight);
    }
}

impl OptimizeBackend<'_> {
    /// Assert the recorded soft clauses as lexicographic objective strata.
    ///
    /// Weight classes are visited heaviest first. A stratum closes once the
    /// gcd of its weights exceeds the total weight of every lighter clause:
    /// two different costs of the stratum then differ by more than all
    /// lighter clauses together, so minimizing the strata in order reaches
    /// the weighted-sum optimum itself (ties may resolve to a different
    /// optimal model). `reserve` is the total weight of the `reserve_at`
    /// clauses refinement may add later; it counts as a present class.
    /// Z3 ranks objectives by first declaration, so every stratum is
    /// declared here, heaviest first.
    fn flush(&self, reserve_at: u64, reserve: u64) -> SoftGroups {
        let softs = self.softs.borrow();
        let mut mass: BTreeMap<u64, u128> = BTreeMap::new();
        for (_, weight) in softs.iter() {
            *mass.entry(*weight).or_default() += u128::from(*weight);
        }
        *mass.entry(reserve_at).or_default() += u128::from(reserve);
        let mut lighter: u128 = mass.values().sum();
        let mut stratum_of: BTreeMap<u64, usize> = BTreeMap::new();
        let mut strata = 0;
        let mut divisor = 0;
        for (&weight, &class_mass) in mass.iter().rev() {
            lighter -= class_mass;
            divisor = gcd(divisor, weight);
            stratum_of.insert(weight, strata);
            if u128::from(divisor) > lighter {
                strata += 1;
                divisor = 0;
            }
        }
        let groups: Vec<z3::Symbol> = (0..strata)
            .map(|k| z3::Symbol::String(format!("stratum{k}")))
            .collect();
        let mut members = vec![Vec::new(); strata];
        for (cond, weight) in softs.iter() {
            members[stratum_of[weight]].push((cond, *weight));
        }
        for (group, members) in groups.iter().zip(&members) {
            if members.is_empty() {
                // Only the reserved class lives here. A true clause costs
                // nothing but fixes the stratum's rank now.
                self.opt
                    .assert_soft(&Bool::from_bool(true), reserve_at, Some(group.clone()));
            }
            for (cond, weight) in members {
                self.opt.assert_soft(*cond, *weight, Some(group.clone()));
            }
        }
        SoftGroups {
            groups: stratum_of
                .into_iter()
                .map(|(weight, k)| (weight, groups[k].clone()))
                .collect(),
            added: RefCell::new(Vec::new()),
        }
    }
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// One function's objective strata by weight class, so a soft clause that
/// refinement adds joins the stratum `flush` reserved for its weight.
#[derive(Default)]
pub(crate) struct SoftGroups {
    groups: BTreeMap<u64, z3::Symbol>,
    // Clauses refinement adds, in ordinary-preference units of `assert_soft`'s weight.
    added: RefCell<Vec<(Bool, u64)>>,
}

impl SoftGroups {
    pub(crate) fn assert_soft(&self, opt: &Optimize, cond: &Bool, weight: u64) {
        let group = self
            .groups
            .get(&weight)
            .unwrap_or_else(|| panic!("soft weight {weight} has no reserved objective stratum"));
        opt.assert_soft(cond, weight, Some(group.clone()));
        self.added.borrow_mut().push((cond.clone(), weight));
    }
}

/// A model's cost level by level: the built clauses at their recorded
/// levels, and the clauses refinement added as ordinary preferences in
/// units of `primary_unit`.
fn level_cost(
    model: &dyn ModelView,
    levels: &[(Bool, Tier, u64)],
    groups: &SoftGroups,
    primary_unit: u64,
) -> TierCost {
    let mut cost = TierCost::default();
    for (cond, tier, units) in levels {
        if model.truth(cond) != Some(true) {
            cost.add(*tier, *units);
        }
    }
    for (cond, weight) in groups.added.borrow().iter() {
        if model.truth(cond) != Some(true) {
            cost.add(Tier::Primary, weight / primary_unit.max(1));
        }
    }
    cost
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

// Construction-vs-solve attribution for the P4 perf gate.
static BUILD_NS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static CHECK_NS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

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
    Artifacts,
) {
    match solve_function_engine(func, name_to_ident, &[], maximal_flow_certification) {
        Ok((c, ty, ov, structure_world, grade, artifacts)) => {
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
            (c, ty, ov, structure_world, artifacts)
        }
        Err(first) => {
            TYPE_SOLVE_NO_MODEL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            eprintln!(
                "[clight-select] WARN: type solve for {} ({:#x}) produced no model ({}); emitting no selection, upstream defaults apply ({} nodes, {} regs)",
                func.name,
                func.address,
                match first {
                    SatResult::Unsat => "UNSAT",
                    SatResult::Unknown => "unknown (work allowance exhausted or incomplete)",
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
                Artifacts::default(),
            )
        }
    }
}

// Everything the constraint build produces that a model has to be read against; shared verbatim by both engines.
struct BuiltFunction {
    t: TypeDt,
    regs: Vec<RTLReg>,
    tyvar: HashMap<RTLReg, Dynamic>,
    concrete_declarations: syntax::declarations::Declarations,
    structure_worlds: Vec<u8>,
    structure_world_var: HashMap<u8, Bool>,
    nodes: Vec<Node>,
    selvar: HashMap<Node, Vec<Bool>>,
    recorded: HashMap<Node, Vec<Vec<RecordedCond>>>,
    func_ret: Dynamic,
    interfaces: syntax::interfaces::InterfaceTerms,
    primary_unit: u64,
    soft_groups: SoftGroups,
}

impl BuiltFunction {
    fn context<'a>(
        &'a self,
        func: &'a FunctionData,
        names: &'a HashMap<String, Ident>,
    ) -> FunctionContext<'a> {
        FunctionContext {
            types: &self.t,
            function: func,
            names,
            registers: &self.regs,
            declarations: &self.tyvar,
            concrete_declarations: &self.concrete_declarations,
            nodes: &self.nodes,
            selections: &self.selvar,
            worlds: &self.structure_worlds,
            world_variables: &self.structure_world_var,
            return_type: &self.func_ret,
            interfaces: &self.interfaces,
            primary_unit: self.primary_unit,
            soft_groups: &self.soft_groups,
        }
    }
}

// The single constraint build, engine-independent: identical hard constraints and identical soft families whichever backend consumes them.
fn build_function_constraints(
    t: TypeDt,
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    interface_pins: &[(RTLReg, XType)],
    backend: &dyn SolveBackend,
) -> BuiltFunction {
    build_function_constraints_with_stack(
        t,
        func,
        name_to_ident,
        interface_pins,
        backend,
        &Stack::production(),
    )
}

fn build_function_constraints_with_stack(
    t: TypeDt,
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    interface_pins: &[(RTLReg, XType)],
    backend: &dyn SolveBackend,
    stack: &Stack<'_>,
) -> BuiltFunction {
    {
        // Open interface choices (none for an ordinary solve).
        let interfaces = syntax::interfaces::InterfaceTerms::build(&func.free_interfaces, backend);
        // Free type variable per inferable register (deterministic order).
        let mut regs: Vec<RTLReg> = func.var_type_candidates.keys().copied().collect();
        regs.sort();
        let mut tyvar: HashMap<RTLReg, Dynamic> = HashMap::new();
        let declarations = DeclarationContext {
            types: &t,
            function: func,
            pins: interface_pins,
            interfaces: &interfaces,
        };
        for &reg in &regs {
            let tv = t.fresh();
            for module in stack.components() {
                module.constrain_declaration(&declarations, reg, &tv, backend);
            }
            tyvar.insert(reg, tv);
        }
        let concrete_declarations =
            syntax::declarations::Declarations::build(stack, &declarations, &regs, &tyvar, backend);
        for module in stack.components() {
            module.constrain_interfaces(&declarations, &tyvar, &concrete_declarations, backend);
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
        let no_soft_groups = SoftGroups::default();
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

        let func_ret = match interfaces.ret(func.address as Ident) {
            Some(alternatives) => syntax::interfaces::own_return_term(&t, func, alternatives),
            None => match &func.return_type {
                ClightType::Tvoid => t.void(),
                other => clight_to_ty(&t, other),
            },
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
        let cx = FunctionContext {
            types: &t,
            function: func,
            names: name_to_ident,
            registers: &regs,
            declarations: &tyvar,
            concrete_declarations: &concrete_declarations,
            nodes: &nodes,
            selections: &selvar,
            worlds: &structure_worlds,
            world_variables: &structure_world_var,
            return_type: &func_ret,
            interfaces: &interfaces,
            primary_unit: 0, // the bound is established after all modules build
            // Strata exist only after the build; the build-time context carries none.
            soft_groups: &no_soft_groups,
        };
        let analyses = stack.build(&cx);
        let extra_priors: usize = analyses.iter().map(|a| a.prior_count()).sum();
        // The world preference can also be violated. Include it in the
        // complete lower-tier bound; otherwise it can buy back one unit of
        // evidence at a stratum boundary.
        let world_prior = usize::from(structure_worlds.len() > 1);
        let compat_w =
            (regs.len() + authoritative_refinable_nodes + extra_priors + world_prior) as u64 + 1;
        let secondary_count = analyses.iter().map(|a| a.secondary_count()).sum();
        let evidence_count = analyses.iter().map(|a| a.evidence_count()).sum();
        let support_count = analyses.iter().map(|a| a.support_count()).sum();
        let sink = ConstraintSink::with_supported_objectives(
            backend,
            compat_w,
            secondary_count,
            evidence_count,
            support_count,
        );
        for analysis in &analyses {
            analysis.constrain_function(&cx, &sink);
        }

        // Emit constraints for every candidate statement, guarded by its selection boolean when refinable; multi-candidate nodes also record their conditions for the post-solve re-pick.
        let mut recorded: HashMap<Node, Vec<Vec<RecordedCond>>> = HashMap::new();
        for &node in &nodes {
            let cands = &func.node_statements[&node];
            match selvar.get(&node) {
                Some(vars) => {
                    let mut per_cand = Vec::with_capacity(cands.len());
                    for (ci, stmt) in cands.iter().enumerate() {
                        sink.begin_candidate(true);
                        let candidate = Candidate {
                            node,
                            index: ci,
                            statement: stmt,
                            selected: Some(&vars[ci]),
                        };
                        for analysis in &analyses {
                            analysis.constrain_candidate(&cx, &candidate, &sink);
                        }
                        per_cand.push(sink.take_recorded());
                    }
                    recorded.insert(node, per_cand);
                }
                None => {
                    sink.begin_candidate(false);
                    let candidate = Candidate {
                        node,
                        index: 0,
                        statement: &cands[0],
                        selected: None,
                    };
                    for analysis in &analyses {
                        analysis.constrain_candidate(&cx, &candidate, &sink);
                    }
                }
            }
        }

        for node in sink.joint_nodes(&selvar) {
            if let Some(per_candidate) = recorded.get_mut(&node) {
                for (guard, conditions) in selvar[&node].iter().zip(per_candidate) {
                    conditions.push((Some(guard.clone()), u64::MAX));
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
                let parent = authoritative_candidates[0];
                let family: BTreeSet<_> = std::iter::once(parent)
                    .chain(analyses.iter().flat_map(|a| a.prior_family(*node, parent)))
                    .filter(|i| authoritative_candidates.contains(i))
                    .collect();
                sink.assert_soft_raw(
                    &Bool::or(
                        &family
                            .into_iter()
                            .map(|i| selvar[node][i].clone())
                            .collect::<Vec<_>>(),
                    ),
                    1u64,
                );
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
            concrete_declarations,
            structure_worlds,
            structure_world_var,
            nodes,
            selvar,
            recorded,
            func_ret,
            interfaces,
            primary_unit: secondary_count as u64 + 1,
            soft_groups: SoftGroups::default(),
        }
    }
}

// Read one model into the per-function selection. Engine-independent: a pure function of the model plus the built terms.
fn candidate_satisfies_hard_conditions(model: &dyn ModelView, conditions: &[RecordedCond]) -> bool {
    conditions.iter().all(|(condition, weight)| {
        *weight != u64::MAX
            || condition
                .as_ref()
                .is_some_and(|c| model.truth(c) == Some(true))
    })
}

#[allow(clippy::type_complexity)]
fn extract_selection(
    m: &dyn ModelView,
    built: &BuiltFunction,
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    allow_repick: bool,
    coupled: &BTreeSet<Node>,
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
        concrete_declarations,
        structure_worlds,
        structure_world_var,
        nodes,
        selvar,
        recorded,
        ..
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
            let decl = concrete_declarations.render(t, m, &tyvar[&reg], reg, func, false);
            temps.insert(reg as Ident, decl.to_clight(func.data_model));
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
                // Re-pick only among candidates satisfying all hard
                // obligations under the fixed model and structural world.
                if let Some(per_cand) = recorded
                    .get(&node)
                    .filter(|_| allow_repick && !coupled.contains(&node))
                {
                    let truth = |c: &Bool| m.truth(c).unwrap_or(false);
                    let cands = &func.node_statements[&node];
                    let mut best: Option<(u64, u64, u64, usize)> = None;
                    for (ci, conds) in per_cand.iter().enumerate() {
                        let allowed = func
                            .candidate_structure_worlds
                            .get(&node)
                            .and_then(|masks| masks.get(ci))
                            .map_or(true, |worlds| worlds.contains(&selected_structure_world));
                        if !allowed {
                            continue;
                        }
                        // Hard obligations are admission criteria, including
                        // guarded semantic vetoes. Never trade one away for a
                        // smaller frontend-error count. Unknown is not proof.
                        if !candidate_satisfies_hard_conditions(m, conds) {
                            continue;
                        }
                        let wt = cands
                            .get(ci)
                            .map(|stmt| {
                                let errs =
                                    crate::decompile::passes::clight_select::syntax::ctyping::wt_check_stmt(
                                        stmt, &wt_env,
                                    );
                                crate::decompile::passes::clight_select::syntax::ctyping::error_count(&errs)
                                    as u64
                            })
                            .unwrap_or(0);
                        // Lossy 64->32 truncations: ranked above soft preferences, uniform when truncation is unavoidable.
                        let narrow = cands.get(ci).map(count_truncating_casts_stmt).unwrap_or(0);
                        let mut wviol = 0u64;
                        for (cond, w) in conds {
                            let ok = match cond {
                                Some(c) => truth(c),
                                None => false,
                            };
                            if !ok {
                                if *w != u64::MAX {
                                    wviol = wviol.saturating_add(*w);
                                }
                            }
                        }
                        let key = (wt, narrow, wviol, ci);
                        if best.is_none_or(|b| key < b) {
                            best = Some(key);
                        }
                    }
                    if let Some((_, _, _, ci)) = best {
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
        let rendered = concrete_declarations.render(t, m, &tyvar[&reg], reg, func, allow_void);
        // Compatibility index for older consumers. Structural commitments,
        // not this lossy adapter, own emission and concrete C auditing.
        let rendered = rendered
            .legacy_candidate(func.data_model)
            .unwrap_or_else(|| {
                if rendered.is_pointer() {
                    CandType::PtrLong
                } else {
                    CandType::I64(Sign::Signed)
                }
            });
        let cands = &func.var_type_candidates[&reg];
        match cands.iter().position(|candidate| *candidate == rendered) {
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
pub(crate) type SolveOutcome = (
    HashMap<Node, Option<usize>>,
    HashMap<RTLReg, usize>,
    HashMap<RTLReg, CandType>,
    u8,
    SatResult,
    Artifacts,
);

// The single Z3 solve. Returns the selection + the SatResult that yielded the model, or the failing SatResult when no model is available.
pub(crate) fn solve_function_z3(
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    interface_pins: &[(RTLReg, XType)],
) -> Result<SolveOutcome, SatResult> {
    solve_function_z3_with_stack(func, name_to_ident, interface_pins, &Stack::production())
}

pub(crate) fn solve_function_z3_with_stack(
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    interface_pins: &[(RTLReg, XType)],
    stack: &Stack<'_>,
) -> Result<SolveOutcome, SatResult> {
    solve_function_counted(func, name_to_ident, interface_pins, stack).0
}

/// The solve of `solve_function_z3_with_stack`, and the Z3 work it spent in
/// rlimit units: deterministic, unlike its time.
pub(crate) fn solve_function_counted(
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    interface_pins: &[(RTLReg, XType)],
    stack: &Stack<'_>,
) -> (Result<SolveOutcome, SatResult>, u64) {
    // Fresh Z3 context per function: reusing one leaks MaxSMT state across functions and makes tie-breaking depend on rayon order. Do not set random_seed -- Optimize rejects it, and with it the whole parameter set.
    let cfg = z3::Config::new();
    z3::with_z3_config(&cfg, || {
        let build_t0 = std::time::Instant::now();
        let t = TypeDt::build();
        let opt = Optimize::new();
        let outcome = solve_in(
            &opt,
            t,
            build_t0,
            func,
            name_to_ident,
            interface_pins,
            stack,
        );
        let work =
            crate::decompile::passes::clight_select::solvers::refinement::resource_count(&opt);
        (outcome, work)
    })
}

fn solve_in(
    opt: &Optimize,
    t: TypeDt,
    build_t0: std::time::Instant,
    func: &FunctionData,
    name_to_ident: &HashMap<String, Ident>,
    interface_pins: &[(RTLReg, XType)],
    stack: &Stack<'_>,
) -> Result<SolveOutcome, SatResult> {
    // Bounds every check on its own, including each refinement round.
    opt.set_params(
        &crate::decompile::passes::clight_select::solvers::refinement::work_allowance(
            CONFIG.solve.rlimit,
        ),
    );

    let (built, (softs, levels)) = {
        let backend = OptimizeBackend::new(&opt);
        let mut built = build_function_constraints_with_stack(
            t,
            func,
            name_to_ident,
            interface_pins,
            &backend,
            stack,
        );
        // Refinement may add one repair preference per selectable node.
        built.soft_groups = backend.flush(
            built.primary_unit,
            (built.selvar.len() as u64)
                .checked_mul(built.primary_unit)
                .expect("selection repair bound"),
        );
        // An open interface prefers its reconciled (rank-zero) choice. The
        // group is declared after every stratum, so it only breaks ties of
        // the function's own objective and never enters its cost.
        for selected in built.interfaces.rank_zero() {
            opt.assert_soft(
                selected,
                1,
                Some(z3::Symbol::String("interface-prior".into())),
            );
        }
        (built, backend.into_softs())
    };

    let audit = audit::Snapshot::start(func, &opt);

    BUILD_NS.fetch_add(
        build_t0.elapsed().as_nanos() as u64,
        std::sync::atomic::Ordering::Relaxed,
    );
    let mut refinements =
        crate::decompile::passes::clight_select::solvers::refinement::Session::start(
            stack,
            &built.context(func, name_to_ident),
            &opt,
        );
    loop {
        if refinements.spent_work(&opt, CONFIG.solve.refinement_rlimit) {
            eprintln!(
                "[selection-analysis] fn={:#x} shared refinement work budget exhausted",
                func.address
            );
            if refinements.advance(None, SatResult::Unknown, &opt) {
                continue;
            }
        }
        let work_before =
            crate::decompile::passes::clight_select::solvers::refinement::resource_count(&opt);
        let check_t0 = std::time::Instant::now();
        let check_result = opt.check(&[]);
        CHECK_NS.fetch_add(
            check_t0.elapsed().as_nanos() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        let model = match check_result {
            SatResult::Sat => opt.get_model(),
            // Only reuse a partial model that the work allowance cut off
            // (deterministic), and only outside an uncertified analysis
            // extension.
            SatResult::Unknown
                if !refinements.active()
                    && crate::decompile::passes::clight_select::solvers::refinement::exhausted(
                        &opt,
                        work_before,
                        CONFIG.solve.rlimit,
                    ) =>
            {
                opt.get_model()
            }
            SatResult::Unknown | SatResult::Unsat => None,
        };
        if refinements.advance(model.as_ref(), check_result, &opt) {
            continue;
        }
        match model {
            Some(m) => {
                if !built
                    .concrete_declarations
                    .0
                    .keys()
                    .all(|&reg| built.concrete_declarations.selected(&m, reg).is_some())
                {
                    audit.finish(&built, func, &opt, &softs, None, SatResult::Unknown);
                    return Err(SatResult::Unknown);
                }
                // A resource-limited partial model may retain the legacy
                // path, but cannot authorize a new concrete representation.
                if check_result != SatResult::Sat
                        && built
                            .concrete_declarations
                            .admissions(&m)
                            .values()
                            .any(|s| *s != crate::decompile::passes::clight_select::type_graph::TypeAdmission::LegacyFallback)
                    {
                        audit.finish(&built, func, &opt, &softs, None, SatResult::Unknown);
                        return Err(SatResult::Unknown);
                    }
                report_cost("optimize", func, &m, &softs);
                let interface_choices = built.interfaces.choices(&m);
                let cost = level_cost(&m, &levels, &built.soft_groups, built.primary_unit);
                let (cand_out, ty_out, ty_override, structure_world) = extract_selection(
                    &m,
                    &built,
                    func,
                    name_to_ident,
                    true,
                    refinements.coupled_nodes(),
                );
                let mut results = refinements.into_results();
                let commitments = built
                    .concrete_declarations
                    .commitments(&m, &cand_out, &results);
                syntax::type_evidence::COMMITMENTS.insert(&mut results, commitments);
                syntax::type_evidence::ADMISSIONS
                    .insert(&mut results, built.concrete_declarations.admissions(&m));
                if !built.interfaces.is_empty() {
                    syntax::interfaces::CHOICES.insert(&mut results, interface_choices);
                }
                syntax::interfaces::COST.insert(&mut results, cost);
                audit.finish(&built, func, &opt, &softs, Some(&m), check_result);
                return Ok((
                    cand_out,
                    ty_out,
                    ty_override,
                    structure_world,
                    check_result,
                    results,
                ));
            }
            None => {
                audit.finish(&built, func, &opt, &softs, None, check_result);
                return Err(check_result);
            }
        }
    }
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
            crate::decompile::passes::clight_select::solvers::in_search::branch_theory::build_branch_theory(
                &built.nodes,
                &func.node_statements,
                &built.selvar,
                &func.cond_branch_class,
            );
        let (class_vetoes, class_stats) =
            crate::decompile::passes::clight_select::solvers::in_search::class_theory::build_class_theory(
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
        let mut tags: Vec<&'static str> = vec![
                crate::decompile::passes::clight_select::solvers::in_search::branch_theory::TAG;
                branch_vetoes.len()
            ];
        tags.extend(
            std::iter::repeat(
                crate::decompile::passes::clight_select::solvers::in_search::class_theory::TAG,
            )
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
        let problem = crate::decompile::passes::clight_select::solvers::in_search::flow_theory::FlowProblem {
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
            round_cap: crate::decompile::passes::clight_select::solvers::in_search::flow_theory::DEFAULT_ROUND_CAP,
            exempt_nodes: exempt_nodes.clone(),
        };
        let theory = Rc::new(RefCell::new(
            crate::decompile::passes::clight_select::solvers::in_search::flow_theory::SelectionTheory::new(
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
            stats.vetoes_fired = v.fired_for(
                crate::decompile::passes::clight_select::solvers::in_search::branch_theory::TAG,
            );
            stats.conflicts_injected = v.conflicts_for(
                crate::decompile::passes::clight_select::solvers::in_search::branch_theory::TAG,
            );
            let mut cstats = class_stats;
            cstats.vetoes_fired = v.fired_for(
                crate::decompile::passes::clight_select::solvers::in_search::class_theory::TAG,
            );
            cstats.conflicts_injected = v.conflicts_for(
                crate::decompile::passes::clight_select::solvers::in_search::class_theory::TAG,
            );
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
                if !built
                    .concrete_declarations
                    .0
                    .keys()
                    .all(|&reg| built.concrete_declarations.selected(&m, reg).is_some())
                {
                    return (Err(SatResult::Unknown), flow_injected);
                }
                if check_result != SatResult::Sat
                    && built
                        .concrete_declarations
                        .admissions(&m)
                        .values()
                        .any(|s| *s != crate::decompile::passes::clight_select::type_graph::TypeAdmission::LegacyFallback)
                {
                    return (Err(SatResult::Unknown), flow_injected);
                }
                report_cost("propagator", func, &m, &clauses);
                let (cand_out, ty_out, ty_override, structure_world) =
                    // The propagator learns constraints spanning candidates.
                    // Independent re-picking cannot preserve those clauses.
                    extract_selection(&m, &built, func, name_to_ident, false, &BTreeSet::new());
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
                let mut results = Artifacts::default();
                let commitments = built
                    .concrete_declarations
                    .commitments(&m, &cand_out, &results);
                syntax::type_evidence::COMMITMENTS.insert(&mut results, commitments);
                syntax::type_evidence::ADMISSIONS
                    .insert(&mut results, built.concrete_declarations.admissions(&m));
                Ok((
                    cand_out,
                    ty_out,
                    ty_override,
                    structure_world,
                    check_result,
                    results,
                ))
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
    std::sync::Mutex<
        crate::decompile::passes::clight_select::solvers::in_search::branch_theory::BranchStats,
    >,
> = std::sync::LazyLock::new(|| std::sync::Mutex::new(Default::default()));
static CLASS_STATS: std::sync::LazyLock<
    std::sync::Mutex<
        crate::decompile::passes::clight_select::solvers::in_search::class_theory::ClassStats,
    >,
> = std::sync::LazyLock::new(|| std::sync::Mutex::new(Default::default()));
/// Flow-theory counters accumulated across every per-function solve in a run.
/// The certificate pass adds the block counts afterwards.
static FLOW_STATS: std::sync::LazyLock<
    std::sync::Mutex<crate::decompile::passes::clight_select::solvers::flow::FlowStats>,
> = std::sync::LazyLock::new(|| std::sync::Mutex::new(Default::default()));

/// Take the in-solve flow counters and reset them, so a second decompilation in
/// the same process starts clean.
pub(crate) fn flow_stats_snapshot(
) -> crate::decompile::passes::clight_select::solvers::flow::FlowStats {
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
    if selected_solve_engine(maximal_flow_certification) == SolveEngine::Optimize
        || Stack::production().needs_refinement(func)
    {
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
            crate::decompile::passes::clight_select::solvers::in_search::propagator::fresh_callback_count()
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
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => {
            collect_reg_ptr_evidence_stmt(inner, out)
        }
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
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => {
            count_truncating_casts_stmt(inner)
        }
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
        Artifacts,
    )> = functions
        .par_iter()
        .map(|f| {
            let (c, t, o, world, artifacts) =
                solve_function(f, name_to_ident, maximal_flow_certification);
            (f.address, c, t, o, world, artifacts)
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
    let mut analysis_results = BTreeMap::new();
    for (addr, cmap, tmap, omap, world, decisions) in per_func {
        analysis_results.insert(addr, decisions);
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
        analysis_results,
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

pub(crate) fn committed_param_type(xtype: XType) -> ParamType {
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

    // Every function first receives the same program-level commitments. A
    // dirty re-solve then reads only its own clone plus those commitments, so
    // the re-solves are independent: they run in parallel, and their results
    // are applied in function order.
    let mut jobs: Vec<(usize, FunctionData, Vec<(RTLReg, XType)>)> = Vec::new();
    for (index, func) in functions.iter_mut().enumerate() {
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
                let anchor = crate::decompile::passes::clight_select::solvers::flow::claim_of_type(
                    ty, func.ptr64,
                );
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
        jobs.push((index, resolve_func, pins));
    }

    let outcomes: Vec<(usize, FunctionData, Result<SolveOutcome, SatResult>)> = jobs
        .into_par_iter()
        .map(|(index, resolve_func, pins)| {
            let outcome = solve_function_engine(
                &resolve_func,
                name_to_ident,
                &pins,
                maximal_flow_certification,
            );
            (index, resolve_func, outcome)
        })
        .collect();

    for (index, resolve_func, outcome) in outcomes {
        let func = &mut functions[index];
        match outcome {
            Ok((
                candidates,
                declarations,
                overrides,
                structure_world,
                SatResult::Sat,
                decisions,
            )) => {
                state.analysis_results.insert(func.address, decisions);
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
            Ok((_, _, _, _, grade, _)) => {
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
#[path = "solve_tests.rs"]
mod tests;
