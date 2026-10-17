//! One selection problem for the whole program.
//!
//! Every function's statement, declaration and type choices and the
//! program's interface choices (each function's parameter and return types,
//! each global's type) under one objective: each level of
//! `constraints::Tier` summed over the whole program, highest first, then
//! the interface priors: one per variable chosen away from its target, the
//! alternative every function touching it prefers or, where they differ,
//! its reconciled rank zero. A function's part depends only on the
//! interface choices its problem touches, its neighbourhood.
//!
//! One Z3 call over all of it does not scale: the merged per-function
//! problems alone take 2 to 17 times the separate solves' CPU, on one thread.
//! It is solved in two levels instead, on the problem without answer checks
//! (the syntax check proper):
//!
//! 1. Each function with its neighbourhood open: the least cost it can reach
//!    under any choice of it, its bound, and the choice that reaches it.
//! 2. A master over the interface choices minimizes the program objective
//!    with each function at its strongest known bound: the exact cost of a
//!    neighbourhood choice already solved, else the most any applicable
//!    lower bound says.
//! 3. Each function whose neighbourhood choice is new is solved with it
//!    pinned; where that choice leaves one of the function's preferred
//!    values, the function is also solved with only that variable pinned,
//!    a bound for every choice keeping it.
//!
//! The rounds repeat until the cost of the master's choice meets the
//! master's bound, which proves it optimal, or until the round cap, which
//! keeps the best choice found. Each function is then solved once more under
//! the committed choice with the solvers checking its answer, its interface
//! data set to the choice so the checkers read it.

use rayon::prelude::*;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;
use std::time::Instant;
use z3::ast::{Bool, Int};
use z3::{Optimize, SatResult};

use super::constraints::{Tier, TierCost};
use super::interfaces::{self, FreeInterfaces, CHOICES, COST};
use super::solve::{
    committed_param_type, solve_function_counted, solve_function_z3_with_stack, SolveOutcome,
};
use super::Stack;
use crate::decompile::elevator::config::CONFIG;
use crate::decompile::passes::clight_select::candtype::CandType;
use crate::decompile::passes::clight_select::query::{
    CommittedInterfaces, FunctionData, InterfaceAlternative, InterfaceVar, InterfaceVarId,
    InterfaceVars,
};
use crate::decompile::passes::clight_select::select::{
    callee_ident_from_expr, ProgramSelectionState,
};
use crate::decompile::passes::clight_select::solvers::flow::claim_of_type;
use crate::decompile::passes::clight_select::solvers::refinement::work_allowance;
use crate::decompile::passes::clight_select::wt_audit::xtype_to_clight;
use crate::decompile::passes::csh_pass::clight_type_from_xtype;
use crate::x86::types::{Address, ClightExpr, ClightStmt, ClightType, Ident, XType};

/// The open interface choices of one function, in a fixed order.
type Neighbourhood = Vec<(InterfaceVarId, Vec<InterfaceAlternative>)>;
/// One alternative for each variable of a neighbourhood, by position.
type Choice = Vec<usize>;
/// One alternative for each interface variable (rank zero where absent).
type Assignment = BTreeMap<InterfaceVarId, usize>;
/// The alternative each variable's prior prefers (rank zero where absent).
type Targets = BTreeMap<InterfaceVarId, usize>;
/// The program objective of an assignment: its levels, then its priors.
type Objective = (TierCost, u64);

/// The cost of a choice under which the function has no model: above any
/// feasible one.
const INFEASIBLE: TierCost = TierCost([1 << 32, 0, 0, 0, 0]);
/// The master weighs each objective level by a power of this, above any
/// program's total at the level below.
const LEVEL_BASE: u64 = 1 << 34;

/// One function's part of the program problem.
struct Table {
    neighbourhood: Neighbourhood,
    /// The least cost under any neighbourhood choice, and whether the solve
    /// proved it.
    bound: TierCost,
    exact_bound: bool,
    /// The choice that reaches the bound.
    preferred: Choice,
    /// Exact costs of the neighbourhood choices solved so far.
    solved: BTreeMap<Choice, TierCost>,
    /// The least cost with one variable (by position) pinned to one
    /// alternative and the others open: a bound for every choice keeping it.
    partial: BTreeMap<(usize, usize), TierCost>,
}

impl Table {
    fn choice(&self, assignment: &Assignment) -> Choice {
        self.neighbourhood
            .iter()
            .map(|(id, _)| assignment.get(id).copied().unwrap_or(0))
            .collect()
    }

    /// The strongest cost known for `choice`: exact if solved, else the
    /// highest applicable lower bound.
    fn estimate(&self, choice: &Choice) -> TierCost {
        if let Some(cost) = self.solved.get(choice) {
            return *cost;
        }
        self.partial
            .iter()
            .filter(|((position, alternative), _)| choice[*position] == *alternative)
            .map(|(_, cost)| *cost)
            .fold(self.bound, std::cmp::max)
    }
}

pub(crate) struct ProgramSolve {
    pub(crate) state: ProgramSelectionState,
    pub(crate) committed: CommittedInterfaces,
    pub(crate) stats: ProgramSolveStats,
    pub(crate) dump: String,
}

#[derive(Debug, Default)]
pub(crate) struct ProgramSolveStats {
    pub(crate) functions: usize,
    pub(crate) open_variables: usize,
    /// The open variables functions prefer different alternatives of.
    pub(crate) contested: usize,
    pub(crate) pinned_solves: usize,
    pub(crate) partial_solves: usize,
    pub(crate) rounds: usize,
    pub(crate) proven: bool,
    pub(crate) bound: Objective,
    pub(crate) cost: Objective,
    pub(crate) changed_from_rank0: usize,
    pub(crate) no_model: usize,
    /// Z3 work (rlimit units) of the open solves, and of the rounds' solves.
    pub(crate) relaxed_work: u64,
    pub(crate) round_work: u64,
    /// Whether the rounds stopped at their work budget.
    pub(crate) exhausted: bool,
    pub(crate) relaxed_ms: u128,
    pub(crate) pinned_ms: u128,
    pub(crate) master_ms: u128,
    pub(crate) checked_ms: u128,
}

/// `bodiless` lists the functions emitted without a C body (imports,
/// skip-listed library functions): what lifting saw of them decides nothing
/// about their own interface, which only their callers' typing shapes.
pub(crate) fn solve(
    functions: &mut Vec<FunctionData>,
    vars: &InterfaceVars,
    initial: &CommittedInterfaces,
    names: &HashMap<String, Ident>,
    bodiless: &BTreeSet<Address>,
    model: crate::abi::DataModel,
) -> ProgramSolve {
    let by_id: BTreeMap<&InterfaceVarId, &InterfaceVar> =
        vars.vars.iter().map(|var| (&var.id, var)).collect();
    let mut stats = ProgramSolveStats {
        functions: functions.len(),
        ..Default::default()
    };
    let fixed = unsplittable_globals(functions, &by_id);
    let neighbourhoods: Vec<Neighbourhood> = functions
        .iter()
        .map(|function| {
            neighbourhood(
                function,
                &by_id,
                &fixed,
                !bodiless.contains(&function.address),
                names,
            )
        })
        .collect();
    stats.open_variables = neighbourhoods
        .iter()
        .flatten()
        .map(|(id, _)| id)
        .collect::<BTreeSet<_>>()
        .len();
    let called_globals: BTreeSet<Ident> = called_globals(functions, &by_id)
        .into_iter()
        .filter(|symbol| !fixed.contains(symbol))
        .collect();
    let unchecked = Stack::production().without_checks();
    let trace = std::env::var_os("MANIFOLD_PROGRAM_SOLVE_TRACE").is_some();

    // 1. Bounds.
    let started = Instant::now();
    // Each function's open solve's work also predicts its pinned solves'.
    let (mut tables, predicted): (Vec<Table>, Vec<u64>) = functions
        .par_iter()
        .zip(&neighbourhoods)
        .map(|(function, neighbourhood)| bound(function, neighbourhood, names, &unchecked))
        .unzip();
    stats.relaxed_work = predicted.iter().sum();
    stats.relaxed_ms = started.elapsed().as_millis();
    let budget = stats
        .relaxed_work
        .saturating_mul(CONFIG.interface.max_round_work);
    if trace {
        for (function, table) in functions.iter().zip(&tables) {
            let off: Vec<String> = table
                .neighbourhood
                .iter()
                .zip(&table.preferred)
                .filter(|(_, &choice)| choice != 0)
                .map(|((id, _), choice)| format!("{}={choice}", id.label()))
                .collect();
            eprintln!(
                "[program-solve] table {} vars={} exact={} bound={:?} preferred-off-rank0=[{}]",
                function.name,
                table.neighbourhood.len(),
                table.exact_bound,
                table.bound.0,
                off.join(",")
            );
        }
    }

    // Each variable's target: the alternative every function touching it
    // prefers, where they agree, else rank zero.
    let mut preferences: BTreeMap<&InterfaceVarId, BTreeSet<usize>> = BTreeMap::new();
    for table in &tables {
        for ((id, _), &alternative) in table.neighbourhood.iter().zip(&table.preferred) {
            preferences.entry(id).or_default().insert(alternative);
        }
    }
    let targets: Targets = preferences
        .into_iter()
        .map(|(id, alternatives)| {
            let agreed = alternatives.len() == 1;
            stats.contested += usize::from(!agreed);
            (
                id.clone(),
                if agreed {
                    alternatives.into_iter().next().unwrap()
                } else {
                    0
                },
            )
        })
        .collect();

    // 2-3. Rounds. With nothing learned the master keeps every variable at
    // its target, so round one gives every function what all agree on and
    // the reconciled interfaces where they differ.
    let mut incumbent: Option<(Objective, Assignment)> = None;
    // Per function, the milliseconds and the number of its pinned solves.
    let mut effort = vec![(0u128, 0usize); functions.len()];
    loop {
        let round_started = Instant::now();
        let started = Instant::now();
        let assignment = master(&tables, &by_id, &called_globals, &targets);
        stats.master_ms += started.elapsed().as_millis();
        let master_bound = objective(
            &tables,
            &assignment,
            &called_globals,
            &by_id,
            &targets,
            Table::estimate,
        );
        stats.bound = master_bound;
        // The master's optimum bounds every assignment from below, so an
        // incumbent at it is optimal, whichever round found it.
        let exact_bounds = tables.iter().all(|table| table.exact_bound);
        if incumbent
            .as_ref()
            .is_some_and(|(best, _)| *best == master_bound && exact_bounds)
        {
            stats.proven = true;
            break;
        }
        let exact: Vec<(usize, Choice)> = tables
            .iter()
            .enumerate()
            .filter_map(|(index, table)| {
                let choice = table.choice(&assignment);
                (!table.solved.contains_key(&choice)).then_some((index, choice))
            })
            .collect();
        // A round runs only if the budget pays for its exact solves; the
        // first always runs, for an incumbent.
        let cost_of_exact: u64 = exact.iter().map(|(index, _)| predicted[*index]).sum();
        if incumbent.is_some() && stats.round_work.saturating_add(cost_of_exact) > budget {
            stats.exhausted = true;
            break;
        }
        stats.rounds += 1;

        let started = Instant::now();
        stats.pinned_solves += exact.len();
        let solved: Vec<(usize, Choice, TierCost, u64, u128)> = exact
            .into_par_iter()
            .map(|(index, choice)| {
                let started = Instant::now();
                let pins: Vec<Option<usize>> = choice.iter().map(|&c| Some(c)).collect();
                let (result, work) = pinned(
                    &functions[index],
                    &tables[index].neighbourhood,
                    &pins,
                    names,
                    &unchecked,
                );
                let cost = result.map(|(cost, _)| cost).unwrap_or(INFEASIBLE);
                (index, choice, cost, work, started.elapsed().as_millis())
            })
            .collect();
        for (index, choice, cost, work, ms) in solved {
            tables[index].solved.insert(choice, cost);
            stats.round_work += work;
            effort[index].0 += ms;
            effort[index].1 += 1;
        }
        let cost = objective(
            &tables,
            &assignment,
            &called_globals,
            &by_id,
            &targets,
            |table, choice| table.solved[choice],
        );
        if incumbent.as_ref().is_none_or(|(best, _)| cost < *best) {
            incumbent = Some((cost, assignment.clone()));
        }
        let best = incumbent.as_ref().expect("an incumbent").0;
        let proven = best == master_bound && exact_bounds;
        stats.proven = proven;
        let last = proven || stats.rounds >= CONFIG.interface.max_rounds;

        // A function above its bound learns what each of its deviations from
        // its preferred choice costs on its own, for the rounds to come:
        // cheapest first, while the budget pays.
        let mut deviations: Vec<(usize, usize, usize)> = if last {
            Vec::new()
        } else {
            tables
                .iter()
                .enumerate()
                .flat_map(|(index, table)| {
                    let choice = table.choice(&assignment);
                    let above = table.solved[&choice] > table.bound;
                    choice
                        .into_iter()
                        .enumerate()
                        .filter(move |&(position, alternative)| {
                            above
                                && alternative != table.preferred[position]
                                && !table.partial.contains_key(&(position, alternative))
                        })
                        .map(move |(position, alternative)| (index, position, alternative))
                })
                .collect()
        };
        deviations.sort_by_key(|&(index, position, alternative)| {
            (predicted[index], index, position, alternative)
        });
        let mut room = budget.saturating_sub(stats.round_work);
        let affordable = deviations
            .iter()
            .take_while(|&&(index, _, _)| {
                let fits = predicted[index] <= room;
                room = room.saturating_sub(predicted[index]);
                fits
            })
            .count();
        deviations.truncate(affordable);
        stats.partial_solves += deviations.len();
        type Learned = (
            usize,
            usize,
            usize,
            Option<(TierCost, Option<Choice>)>,
            u64,
            u128,
        );
        let learned: Vec<Learned> = deviations
            .into_par_iter()
            .map(|(index, position, alternative)| {
                let started = Instant::now();
                let mut pins = vec![None; tables[index].neighbourhood.len()];
                pins[position] = Some(alternative);
                let (result, work) = pinned(
                    &functions[index],
                    &tables[index].neighbourhood,
                    &pins,
                    names,
                    &unchecked,
                );
                (
                    index,
                    position,
                    alternative,
                    result,
                    work,
                    started.elapsed().as_millis(),
                )
            })
            .collect();
        for (index, position, alternative, result, work, ms) in learned {
            stats.round_work += work;
            effort[index].0 += ms;
            effort[index].1 += 1;
            let table = &mut tables[index];
            match result {
                Some((cost, reached)) => {
                    table.partial.insert((position, alternative), cost);
                    // The choice reaching a proven partial optimum costs exactly it.
                    if let Some(reached) = reached {
                        table.solved.entry(reached).or_insert(cost);
                    }
                }
                None => {
                    table.partial.insert((position, alternative), INFEASIBLE);
                }
            }
        }
        stats.pinned_ms += started.elapsed().as_millis();
        if trace {
            eprintln!(
                "[program-solve] round {} changed={} pinned={} partial={} bound={:?}/{} cost={:?}/{} best={:?}/{} work={} {}ms",
                stats.rounds, assignment.len(), stats.pinned_solves, stats.partial_solves,
                master_bound.0 .0, master_bound.1, cost.0 .0, cost.1, best.0 .0, best.1,
                stats.round_work, round_started.elapsed().as_millis()
            );
        }
        if last {
            break;
        }
    }
    let (cost, assignment) = incumbent.expect("at least one round");
    stats.cost = cost;
    stats.changed_from_rank0 = assignment.len();
    if trace {
        let mut costly: Vec<(u128, usize, &str)> = effort
            .iter()
            .zip(functions.iter())
            .filter(|((_, count), _)| *count > 0)
            .map(|(&(ms, count), function)| (ms, count, function.name.as_str()))
            .collect();
        costly.sort_by(|a, b| b.cmp(a));
        for (ms, count, name) in costly.iter().take(8) {
            eprintln!("[program-solve] effort {name} solves={count} {ms}ms");
        }
    }

    // The committed choice, with the solvers checking each function's answer.
    let started = Instant::now();
    let checked: Vec<(FunctionData, Option<SolveOutcome>)> = functions
        .par_iter()
        .zip(&tables)
        .map(|(function, table)| {
            let choice = table.choice(&assignment);
            let mut chosen = committed(function, &table.neighbourhood, &choice);
            let outcome =
                solve_function_z3_with_stack(&chosen, names, &[], &Stack::production()).ok();
            chosen.free_interfaces = FreeInterfaces::default();
            (chosen, outcome)
        })
        .collect();
    stats.checked_ms = started.elapsed().as_millis();

    let mut state = ProgramSelectionState::default();
    for (index, (function, outcome)) in checked.into_iter().enumerate() {
        let address = function.address;
        match outcome {
            Some((candidates, declarations, overrides, world, grade, results)) => {
                if grade != SatResult::Sat {
                    eprintln!(
                        "[program-solve] WARN: {} ({:#x}) exhausted its rlimit budget; reusing the best model found",
                        function.name, address
                    );
                }
                state.analysis_results.insert(address, results);
                state.structure_world.insert(address, world);
                for (node, choice) in candidates {
                    state.candidate_idx.insert((address, node), choice);
                }
                for (reg, choice) in declarations {
                    state.var_decl_idx.insert((address, reg), choice);
                }
                for (reg, candidate) in overrides {
                    state.var_type_override.insert((address, reg), candidate);
                }
            }
            None => {
                stats.no_model += 1;
                eprintln!(
                    "[program-solve] WARN: {} ({:#x}) has no model under its committed interface; emitting no selection, upstream defaults apply",
                    function.name, address
                );
                state
                    .structure_world
                    .insert(address, function.authoritative_structure_world);
                state.analysis_results.insert(address, Default::default());
            }
        }
        functions[index] = function;
    }
    let committed = super::interface_solve::commit_choices(
        vars,
        &assignment,
        initial,
        functions,
        &state,
        names,
        model,
    );
    let dump = render(&tables, &assignment, &by_id);
    ProgramSolve {
        state,
        committed,
        stats,
        dump,
    }
}

/// The interface variables a function's problem touches and can choose:
/// its own parameters and return when it has a C body (`owns_interface`),
/// the callees' at its calls, the globals it names. Every own parameter is
/// one, used or not: its callers choose it too, and the body it reaches is
/// typed under the choice only if its own problem sees it. ABI-fixed and
/// single-alternative variables stay committed, as do the globals in `fixed`.
fn neighbourhood(
    function: &FunctionData,
    vars: &BTreeMap<&InterfaceVarId, &InterfaceVar>,
    fixed: &BTreeSet<Ident>,
    owns_interface: bool,
    names: &HashMap<String, Ident>,
) -> Neighbourhood {
    let own = function.address as Ident;
    let mut ids = BTreeSet::new();
    if owns_interface {
        for position in 0..function.param_regs.len() {
            ids.insert(InterfaceVarId::Param {
                function: own,
                position,
            });
        }
        ids.insert(InterfaceVarId::Return { function: own });
    }
    for statements in function.node_statements.values() {
        for statement in statements {
            calls(statement, &mut |callee, arguments| {
                let Some(callee) = callee_ident_from_expr(callee, names) else {
                    return;
                };
                if !function.callee_signatures.contains_key(&callee) {
                    return;
                }
                for position in 0..arguments {
                    ids.insert(InterfaceVarId::Param {
                        function: callee,
                        position,
                    });
                }
                ids.insert(InterfaceVarId::Return { function: callee });
            });
            let mut globals = BTreeSet::new();
            interfaces::globals_named(statement, &mut globals);
            ids.extend(
                globals
                    .into_iter()
                    .filter(|symbol| !fixed.contains(symbol))
                    .map(|symbol| InterfaceVarId::Global { symbol }),
            );
        }
    }
    ids.into_iter()
        .filter_map(|id| {
            let var = vars.get(&id)?;
            (!var.hard_rank0 && var.domain.len() > 1).then(|| (id, var.domain.clone()))
        })
        .collect()
}

/// The open globals some statement names together with others whose
/// alternatives would combine into more than `max_global_cases` typings of
/// it. They stay committed program-wide, so every function types them as the
/// program declares them.
fn unsplittable_globals(
    functions: &[FunctionData],
    vars: &BTreeMap<&InterfaceVarId, &InterfaceVar>,
) -> BTreeSet<Ident> {
    let mut out = BTreeSet::new();
    for function in functions {
        for statements in function.node_statements.values() {
            for statement in statements {
                let mut named = BTreeSet::new();
                interfaces::globals_named(statement, &mut named);
                let open: Vec<(Ident, usize)> = named
                    .into_iter()
                    .filter_map(|symbol| {
                        let var = vars.get(&InterfaceVarId::Global { symbol })?;
                        (!var.hard_rank0 && var.domain.len() > 1)
                            .then_some((symbol, var.domain.len()))
                    })
                    .collect();
                let cases = open
                    .iter()
                    .fold(1usize, |cases, (_, size)| cases.saturating_mul(*size));
                if cases > CONFIG.interface.max_global_cases {
                    out.extend(open.iter().map(|(symbol, _)| *symbol));
                }
            }
        }
    }
    out
}

/// Every call in `statement`: its callee expression and argument count.
fn calls(statement: &ClightStmt, visit: &mut impl FnMut(&ClightExpr, usize)) {
    match statement {
        ClightStmt::Scall(_, callee, arguments) => visit(callee, arguments.len()),
        ClightStmt::Seffect(_, inner) | ClightStmt::Slabel(_, inner) => calls(inner, visit),
        ClightStmt::Ssequence(statements) => statements.iter().for_each(|s| calls(s, visit)),
        ClightStmt::Sifthenelse(_, then, otherwise) => {
            calls(then, visit);
            calls(otherwise, visit);
        }
        ClightStmt::Sloop(body, step) => {
            calls(body, visit);
            calls(step, visit);
        }
        ClightStmt::Sswitch(_, cases) => cases.iter().for_each(|(_, s)| calls(s, visit)),
        _ => {}
    }
}

/// The globals some candidate calls directly: calling one that is not a
/// function pointer is a C error no function's typing sees, since a named
/// global is typed by its declaration.
fn called_globals(
    functions: &[FunctionData],
    vars: &BTreeMap<&InterfaceVarId, &InterfaceVar>,
) -> BTreeSet<Ident> {
    let mut out = BTreeSet::new();
    for function in functions {
        for statements in function.node_statements.values() {
            for statement in statements {
                calls(statement, &mut |callee, _| {
                    if let ClightExpr::Evar(symbol, _) = callee {
                        if vars
                            .get(&InterfaceVarId::Global { symbol: *symbol })
                            .is_some_and(|var| {
                                !var.hard_rank0
                                    && var.domain.iter().any(|alt| alt.xtype == XType::Xfuncptr)
                            })
                        {
                            out.insert(*symbol);
                        }
                    }
                });
            }
        }
    }
    out
}

/// A function with its neighbourhood open, each variable pinned where `pins`
/// says. An own parameter may be declared as any of its alternatives: they
/// join its register's candidates, so even a register lifting proposed no
/// type for has a type variable, and the body is typed by the chosen class
/// rather than by its annotations.
fn open(
    function: &FunctionData,
    neighbourhood: &Neighbourhood,
    pins: &[Option<usize>],
) -> FunctionData {
    let mut open = function.clone();
    let own = function.address as Ident;
    for (id, domain) in neighbourhood {
        if let InterfaceVarId::Param {
            function: owner,
            position,
        } = id
        {
            if *owner != own {
                continue;
            }
            let Some(reg) = function.param_regs.get(*position) else {
                continue;
            };
            let candidates = open.var_type_candidates.entry(*reg).or_default();
            for alternative in domain {
                let candidate = CandType::from_xtype(&alternative.xtype);
                if !candidates.contains(&candidate) {
                    candidates.push(candidate);
                }
            }
        }
    }
    open.free_interfaces = FreeInterfaces(
        neighbourhood
            .iter()
            .zip(pins)
            .map(|((id, domain), pin)| (id.clone(), (domain.clone(), *pin)))
            .collect(),
    );
    open
}

/// The function under `choice` pinned, with its interface data set to the
/// choice so that whatever reads `FunctionData` (the checkers, the re-pick)
/// sees it. The alternative already committed keeps its precise type.
fn committed(
    function: &FunctionData,
    neighbourhood: &Neighbourhood,
    choice: &Choice,
) -> FunctionData {
    let pins: Vec<Option<usize>> = choice.iter().map(|&c| Some(c)).collect();
    let mut pinned = open(function, neighbourhood, &pins);
    let own = function.address as Ident;
    let mut globals = None;
    for ((id, domain), &index) in neighbourhood.iter().zip(choice) {
        let alternative = domain[index].xtype;
        match *id {
            InterfaceVarId::Param {
                function: owner,
                position,
            } if owner == own => {
                if let Some(slot) = pinned.param_types.get_mut(position) {
                    *slot = committed_param_type(alternative);
                }
            }
            InterfaceVarId::Param {
                function: callee,
                position,
            } => {
                if let Some(signature) = pinned.callee_signatures.get_mut(&callee) {
                    if let Some(slot) = signature.param_types.get_mut(position) {
                        *slot = alternative;
                    }
                }
            }
            InterfaceVarId::Return { function: owner } if owner == own => {
                if !keeps(domain, Some(&function.return_type), index) {
                    pinned.return_type = clight_type_from_xtype(&alternative);
                }
            }
            InterfaceVarId::Return { function: callee } => {
                if let Some(signature) = pinned.callee_signatures.get_mut(&callee) {
                    signature.return_type = alternative;
                }
            }
            InterfaceVarId::Global { symbol } => {
                let known = function.known_global_types.by_ident.get(&symbol);
                if !keeps(domain, known, index) {
                    globals
                        .get_or_insert_with(|| function.known_global_types.as_ref().clone())
                        .by_ident
                        .insert(symbol, xtype_to_clight(&alternative));
                }
            }
        }
    }
    if let Some(globals) = globals {
        // The flow view of global types is read together with the checker's map.
        pinned.flow_anchors.global = globals
            .by_ident
            .iter()
            .filter_map(|(&ident, ty)| {
                let anchor = claim_of_type(ty, pinned.ptr64);
                (!anchor.is_top()).then_some((ident, anchor))
            })
            .collect();
        pinned.known_global_types = Arc::new(globals);
    }
    pinned
}

/// Whether choosing `index` keeps `committed`, the type already on
/// `FunctionData` (with its precise spelling).
fn keeps(domain: &[InterfaceAlternative], committed: Option<&ClightType>, index: usize) -> bool {
    interfaces::committed_in(
        domain.iter().map(|alternative| &alternative.xtype),
        committed,
    ) == Some(index)
}

/// The function's bound: its neighbourhood open, no answer checks. And the
/// solve's work.
fn bound(
    function: &FunctionData,
    neighbourhood: &Neighbourhood,
    names: &HashMap<String, Ident>,
    unchecked: &Stack<'_>,
) -> (Table, u64) {
    let mut table = Table {
        neighbourhood: neighbourhood.clone(),
        bound: TierCost::default(),
        exact_bound: true,
        preferred: vec![0; neighbourhood.len()],
        solved: BTreeMap::new(),
        partial: BTreeMap::new(),
    };
    let (outcome, work) = solve_function_counted(
        &open(function, neighbourhood, &vec![None; neighbourhood.len()]),
        names,
        &[],
        unchecked,
    );
    match outcome {
        Ok((_, _, _, _, grade, results)) => {
            if let Some(choices) = CHOICES.get(&results) {
                table.preferred = neighbourhood
                    .iter()
                    .map(|(id, _)| choices.get(id).copied().unwrap_or(0))
                    .collect();
            }
            let cost = COST.get(&results).copied().unwrap_or_default();
            if grade == SatResult::Sat {
                // The open optimum is the pinned optimum of the choice reaching it.
                table.bound = cost;
                table.solved.insert(table.preferred.clone(), cost);
            } else {
                // A model cut off by the work allowance bounds nothing.
                table.exact_bound = false;
            }
        }
        // No model with every choice open: none under any choice.
        Err(SatResult::Unsat) => {
            table.bound = INFEASIBLE;
            table.solved.insert(table.preferred.clone(), INFEASIBLE);
        }
        Err(_) => table.exact_bound = false,
    }
    (table, work)
}

/// The least cost with the variables `pins` names pinned and the others
/// open, without answer checks (the bound's own problem, so the two compare;
/// only the checked solve sets the function's interface data to a choice),
/// and the full choice reaching it when the solve proved it. None when the
/// function has no model there. And the solve's work.
fn pinned(
    function: &FunctionData,
    neighbourhood: &Neighbourhood,
    pins: &[Option<usize>],
    names: &HashMap<String, Ident>,
    unchecked: &Stack<'_>,
) -> (Option<(TierCost, Option<Choice>)>, u64) {
    let (outcome, work) =
        solve_function_counted(&open(function, neighbourhood, pins), names, &[], unchecked);
    let result = match outcome {
        Ok((_, _, _, _, grade, results)) => {
            let cost = COST.get(&results).copied().unwrap_or_default();
            let reached = (grade == SatResult::Sat).then(|| {
                let choices = CHOICES.get(&results);
                neighbourhood
                    .iter()
                    .zip(pins)
                    .map(|((id, _), pin)| {
                        pin.or_else(|| choices.and_then(|c| c.get(id).copied()))
                            .unwrap_or(0)
                    })
                    .collect()
            });
            Some((cost, reached))
        }
        Err(_) => None,
    };
    (result, work)
}

/// The interface-level terms of an assignment: a C error for each called
/// global not declared a function pointer, and one per variable chosen away
/// from its target (the priors, below every level).
fn interface_terms(
    assignment: &Assignment,
    called_globals: &BTreeSet<Ident>,
    vars: &BTreeMap<&InterfaceVarId, &InterfaceVar>,
    targets: &Targets,
) -> Objective {
    let mut cost = TierCost::default();
    for &symbol in called_globals {
        let id = InterfaceVarId::Global { symbol };
        let chosen = assignment.get(&id).copied().unwrap_or(0);
        if vars[&id].domain[chosen].xtype != XType::Xfuncptr {
            cost.add(Tier::Compat, 1);
        }
    }
    let away = targets
        .iter()
        .filter(|(id, &target)| assignment.get(*id).copied().unwrap_or(0) != target)
        .count()
        + assignment
            .keys()
            .filter(|id| !targets.contains_key(*id))
            .count();
    (cost, away as u64)
}

/// The program objective of an assignment, each function costed by `cost`.
fn objective(
    tables: &[Table],
    assignment: &Assignment,
    called_globals: &BTreeSet<Ident>,
    vars: &BTreeMap<&InterfaceVarId, &InterfaceVar>,
    targets: &Targets,
    cost: impl Fn(&Table, &Choice) -> TierCost,
) -> Objective {
    let (mut total, priors) = interface_terms(assignment, called_globals, vars, targets);
    for table in tables {
        total = total + cost(table, &table.choice(assignment));
    }
    (total, priors)
}

/// The master: one alternative per open variable, minimizing the program
/// objective with each function at its strongest known cost (`Table::estimate`),
/// so its optimum bounds every assignment's objective from below. The levels
/// are weighed into one integer so that a function's cost can be the most of
/// its applicable bounds; the priors break ties toward the targets.
fn master(
    tables: &[Table],
    vars: &BTreeMap<&InterfaceVarId, &InterfaceVar>,
    called_globals: &BTreeSet<Ident>,
    targets: &Targets,
) -> Assignment {
    let open: BTreeSet<&InterfaceVarId> = tables
        .iter()
        .flat_map(|table| table.neighbourhood.iter().map(|(id, _)| id))
        .chain(called_globals.iter().filter_map(|&symbol| {
            vars.get_key_value(&InterfaceVarId::Global { symbol })
                .map(|(id, _)| *id)
        }))
        .collect();
    z3::with_z3_config(&z3::Config::new(), || {
        let opt = Optimize::new();
        opt.set_params(&work_allowance(CONFIG.solve.rlimit));
        let mut selectors: BTreeMap<&InterfaceVarId, Vec<Bool>> = BTreeMap::new();
        for &id in &open {
            let alternatives: Vec<Bool> = vars[id]
                .domain
                .iter()
                .map(|_| Bool::fresh_const("choose"))
                .collect();
            let one: Vec<(&Bool, i32)> = alternatives.iter().map(|s| (s, 1)).collect();
            opt.assert(&Bool::pb_eq(&one, 1));
            selectors.insert(id, alternatives);
        }
        // Level k weighs LEVEL_BASE^(4-k): a whole program's total at a lower
        // level stays below one unit of the level above.
        let base = Int::from_u64(LEVEL_BASE);
        let mut weights = vec![Int::from_u64(1)];
        for _ in 0..4 {
            let next = Int::mul(&[weights.last().unwrap(), &base]);
            weights.push(next);
        }
        weights.reverse();
        let weigh = |cost: &TierCost| {
            let terms: Vec<Int> = cost
                .0
                .iter()
                .zip(&weights)
                .map(|(&units, weight)| Int::mul(&[&Int::from_u64(units), weight]))
                .collect();
            Int::add(&terms)
        };
        let zero = Int::from_u64(0);
        let one = Int::from_u64(1);
        let mut total = zero.clone();
        for table in tables {
            if table.neighbourhood.is_empty() {
                continue;
            }
            let cost = Int::fresh_const("function");
            opt.assert(&cost.ge(&weigh(&table.bound)));
            for (choice, exact) in &table.solved {
                let matches = Bool::and(
                    &table
                        .neighbourhood
                        .iter()
                        .zip(choice)
                        .map(|((id, _), &index)| selectors[id][index].clone())
                        .collect::<Vec<_>>(),
                );
                opt.assert(&matches.implies(cost.ge(&weigh(exact))));
            }
            for (&(position, alternative), bound) in &table.partial {
                let (id, _) = &table.neighbourhood[position];
                opt.assert(&selectors[id][alternative].implies(cost.ge(&weigh(bound))));
            }
            total = Int::add(&[&total, &cost]);
        }
        for &symbol in called_globals {
            let id = InterfaceVarId::Global { symbol };
            if let Some(choices) = selectors.get(&id) {
                let pointer: Vec<Bool> = vars[&id]
                    .domain
                    .iter()
                    .zip(choices)
                    .filter(|(alternative, _)| alternative.xtype == XType::Xfuncptr)
                    .map(|(_, selected)| selected.clone())
                    .collect();
                let violated = Bool::or(&pointer)
                    .not()
                    .ite(&weights[Tier::Compat as usize], &zero);
                total = Int::add(&[&total, &violated]);
            }
        }
        opt.minimize(&total);
        let mut priors = zero.clone();
        for (id, choices) in &selectors {
            let target = targets.get(*id).copied().unwrap_or(0);
            priors = Int::add(&[&priors, &choices[target].not().ite(&one, &zero)]);
        }
        opt.minimize(&priors);

        let mut assignment = Assignment::new();
        if opt.check(&[]) != SatResult::Sat {
            eprintln!(
                "[program-solve] WARN: the interface master has no optimum; keeping rank zero"
            );
            return assignment;
        }
        let model = opt.get_model().expect("a master model");
        for (id, choices) in &selectors {
            let chosen = choices
                .iter()
                .position(|selected| {
                    model.eval(selected, true).and_then(|v| v.as_bool()) == Some(true)
                })
                .unwrap_or(0);
            if chosen != 0 {
                assignment.insert((*id).clone(), chosen);
            }
        }
        assignment
    })
}

/// The committed choices, for `--dump-interface-instance`.
fn render(
    tables: &[Table],
    assignment: &Assignment,
    vars: &BTreeMap<&InterfaceVarId, &InterfaceVar>,
) -> String {
    let mut out = String::from("id\trank0\tchosen\tdomain\n");
    for (id, var) in vars {
        let chosen = assignment.get(*id).copied().unwrap_or(0);
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\n",
            id.label(),
            var.domain[0].class.label(),
            var.domain[chosen].class.label(),
            var.domain
                .iter()
                .enumerate()
                .map(|(rank, alternative)| format!(
                    "{rank}:{}:{:?}",
                    alternative.class.label(),
                    alternative.xtype
                ))
                .collect::<Vec<_>>()
                .join(","),
        ));
    }
    let open: usize = tables.iter().map(|table| table.neighbourhood.len()).sum();
    out.push_str(&format!("# function-neighbourhood-variables={open}\n"));
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::passes::clight_select::candtype::Sign;
    use crate::decompile::passes::clight_select::query::{CalleeSignature, InterfaceClass};
    use crate::x86::types::{
        ClightAttr, ClightFloatSize, ClightIntSize, ClightSignedness, ParamType,
    };

    const F: Ident = 0x100;
    const G: Ident = 0x200;

    fn pointer() -> ClightType {
        ClightType::Tpointer(
            Arc::new(ClightType::Tint(
                ClightIntSize::I8,
                ClightSignedness::Signed,
                ClightAttr::default(),
            )),
            ClightAttr::default(),
        )
    }
    fn int() -> ClightType {
        ClightType::Tint(
            ClightIntSize::I32,
            ClightSignedness::Signed,
            ClightAttr::default(),
        )
    }
    fn alternatives(xtypes: &[XType]) -> Vec<InterfaceAlternative> {
        xtypes
            .iter()
            .map(|xtype| InterfaceAlternative {
                class: InterfaceClass::from_xtype(xtype),
                xtype: *xtype,
            })
            .collect()
    }

    /// F calls G with register 5 (a pointer when `caller_pointer`), and G's
    /// parameter register 3 is dereferenced when `callee_pointer`. G's
    /// committed parameter type is int.
    fn program(caller_pointer: bool, callee_pointer: bool) -> (Vec<FunctionData>, InterfaceVars) {
        let mut caller = FunctionData::new(F as u64, "f".into(), vec![], vec![], None, 0, 20, true);
        let argument = if caller_pointer { pointer() } else { int() };
        caller.var_type_candidates.insert(
            5,
            vec![if caller_pointer {
                CandType::PtrChar
            } else {
                CandType::I32(Sign::Signed)
            }],
        );
        if caller_pointer {
            caller.must_pointer_regs.insert(5);
        }
        caller.node_statements.insert(
            20,
            vec![ClightStmt::Scall(
                None,
                ClightExpr::Evar(G, int()),
                vec![ClightExpr::Etempvar(5, argument)],
            )],
        );
        caller.callee_signatures.insert(
            G,
            CalleeSignature {
                param_count: 1,
                return_type: XType::Xvoid,
                param_types: vec![XType::Xint],
                is_varargs: false,
            },
        );
        let mut callee = FunctionData::new(
            G as u64,
            "g".into(),
            vec![3],
            vec![ParamType::Typed(XType::Xint)],
            None,
            0,
            30,
            true,
        );
        callee
            .var_type_candidates
            .insert(3, vec![CandType::I32(Sign::Signed), CandType::PtrChar]);
        callee
            .var_type_candidates
            .insert(6, vec![CandType::I32(Sign::Signed)]);
        let statement = if callee_pointer {
            callee.must_pointer_regs.insert(3);
            ClightStmt::Sset(
                6,
                ClightExpr::Ederef(Box::new(ClightExpr::Etempvar(3, pointer())), int()),
            )
        } else {
            ClightStmt::Sset(6, ClightExpr::EconstInt(0, int()))
        };
        callee.node_statements.insert(30, vec![statement]);
        let vars = InterfaceVars {
            vars: vec![InterfaceVar {
                id: InterfaceVarId::Param {
                    function: G,
                    position: 0,
                },
                domain: alternatives(&[XType::Xint, XType::Xptr]),
                hard_rank0: false,
            }],
            diagnostics: Default::default(),
        };
        (vec![caller, callee], vars)
    }

    fn run(functions: &mut Vec<FunctionData>, vars: &InterfaceVars) -> ProgramSolve {
        solve(
            functions,
            vars,
            &CommittedInterfaces::default(),
            &HashMap::new(),
            &BTreeSet::new(),
            crate::abi::DataModel::Lp64,
        )
    }

    #[test]
    fn a_parameter_both_sides_use_as_a_pointer_is_committed_a_pointer() {
        let (mut functions, vars) = program(true, true);
        let outcome = run(&mut functions, &vars);
        assert_eq!(outcome.stats.changed_from_rank0, 1, "{:?}", outcome.stats);
        assert!(outcome.stats.proven, "{:?}", outcome.stats);
        // Each function is solved, and checked, under the committed choice:
        // the pointer, on both sides.
        assert!(outcome.state.candidate_idx.contains_key(&(F as u64, 20)));
        assert!(outcome.state.candidate_idx.contains_key(&(G as u64, 30)));
        assert_eq!(
            functions[0].callee_signatures[&G].param_types,
            vec![XType::Xptr]
        );
        assert_eq!(
            functions[1].param_types,
            vec![ParamType::Typed(XType::Xptr)]
        );
    }

    #[test]
    fn an_interface_no_function_needs_changed_keeps_its_rank_zero_type() {
        let (mut functions, vars) = program(false, false);
        let outcome = run(&mut functions, &vars);
        assert_eq!(outcome.stats.changed_from_rank0, 0, "{:?}", outcome.stats);
        assert!(outcome.stats.proven, "{:?}", outcome.stats);
    }

    /// `g(p)` with a pointer p, where g's parameter, committed a pointer, is
    /// converted to a double in g's body and lifting proposed no type for its
    /// register (ln's force_linkat). The caller may pass p as it is or
    /// converted; the body needs an integer, and only g's own problem sees it.
    #[test]
    fn a_parameter_lifting_typed_nothing_for_is_chosen_by_its_body_too() {
        let (mut functions, mut vars) = program(true, false);
        let long = || ClightType::Tlong(ClightSignedness::Signed, ClightAttr::default());
        let double = || ClightType::Tfloat(ClightFloatSize::F64, ClightAttr::default());
        let callee = &mut functions[1];
        callee.var_type_candidates.remove(&3);
        callee.param_types = vec![ParamType::Typed(XType::Xptr)];
        callee.var_type_candidates.insert(6, vec![CandType::F64]);
        callee.node_statements.insert(
            30,
            vec![ClightStmt::Sset(
                6,
                ClightExpr::Ecast(Box::new(ClightExpr::Etempvar(3, long())), double()),
            )],
        );
        let caller = &mut functions[0];
        caller.callee_signatures.get_mut(&G).unwrap().param_types = vec![XType::Xptr];
        caller
            .node_statements
            .get_mut(&20)
            .unwrap()
            .push(ClightStmt::Scall(
                None,
                ClightExpr::Evar(G, int()),
                vec![ClightExpr::Ecast(
                    Box::new(ClightExpr::Etempvar(5, pointer())),
                    long(),
                )],
            ));
        vars.vars[0].domain = alternatives(&[XType::Xptr, XType::Xlong]);
        let outcome = run(&mut functions, &vars);
        assert_eq!(outcome.stats.changed_from_rank0, 1, "{:?}", outcome.stats);
        assert_eq!(
            functions[1].param_types,
            vec![ParamType::Typed(XType::Xlong)]
        );
        assert_eq!(
            functions[0].callee_signatures[&G].param_types,
            vec![XType::Xlong]
        );
    }
}
