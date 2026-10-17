#![allow(dead_code, unused_variables, unused_imports, unused_mut)]

use crate::decompile::elevator::config::CONFIG;
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::clight_select::candtype::CandType;
use crate::decompile::passes::clight_select::query::{
    extract_functions, extract_ite_info, extract_loop_info, FunctionData, IteInfo, LoopInfo,
};
use crate::decompile::passes::csh_pass::ident_from_node;
use crate::x86::types::*;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// Per-function selection extracted from the Z3 program state: indices into FunctionData's candidate arrays.
#[derive(Clone, Debug)]
struct SelectionState {
    /// Per statement node: Some(idx) = use candidate[idx], None = SKIP.
    candidate_idx: HashMap<Node, Option<usize>>,
}

fn primary_memory_type(expr: &ClightExpr) -> Option<&ClightType> {
    match expr {
        ClightExpr::Ederef(_, ty)
        | ClightExpr::Efield(_, _, ty)
        | ClightExpr::Evar(_, ty)
        | ClightExpr::Etempvar(_, ty) => Some(ty),
        ClightExpr::Eunop(_, inner, _) | ClightExpr::Ecast(inner, _) => primary_memory_type(inner),
        _ => None,
    }
}

fn stmt_primary_memory_type(stmt: &ClightStmt) -> Option<&ClightType> {
    match stmt {
        ClightStmt::Sset(_, rhs) => primary_memory_type(rhs),
        ClightStmt::Sassign(lhs, _) => primary_memory_type(lhs),
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => stmt_primary_memory_type(inner),
        ClightStmt::Ssequence(statements) if statements.len() == 1 => {
            stmt_primary_memory_type(&statements[0])
        }
        _ => None,
    }
}

fn stmt_matches_authoritative_chunk(stmt: &ClightStmt, chunk: MemoryChunk) -> bool {
    let expected = crate::decompile::passes::csh_pass::clight_type_from_chunk(&chunk);
    stmt_primary_memory_type(stmt) == Some(&expected)
}

fn superset_provenance_priority(
    stmt: &ClightStmt,
    authoritative_chunk: Option<MemoryChunk>,
    has_authoritative_spelling: bool,
) -> u8 {
    if has_authoritative_spelling
        && authoritative_chunk.is_some_and(|chunk| stmt_matches_authoritative_chunk(stmt, chunk))
    {
        0
    } else if has_authoritative_spelling {
        1
    } else {
        0
    }
}

#[derive(Clone, Default)]
pub(crate) struct ProgramSelectionState {
    pub(crate) analysis_results:
        BTreeMap<Address, crate::decompile::passes::clight_select::syntax::Artifacts>,
    /// (func_addr, node) -> candidate index
    pub(crate) candidate_idx: HashMap<(Address, Node), Option<usize>>,
    /// One atomic CFG/structure interpretation per function.
    pub(crate) structure_world: HashMap<Address, u8>,
    /// (func_addr, reg) -> type candidate index
    pub(crate) var_decl_idx: HashMap<(Address, RTLReg), usize>,
    /// (func_addr, reg) -> inferred type-string for registers whose inferred type is not among the enumerated candidates (generic-inference path only, empty otherwise); applied as a synthetic candidate.
    pub(crate) var_type_override: HashMap<(Address, RTLReg), CandType>,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct SelectedFunction {
    pub address: Address,
    pub name: String,
    pub entry_node: Node,
    pub return_type: ClightType,
    pub param_regs: Vec<RTLReg>,
    pub param_types: Vec<ParamType>,
    pub stack_size: u64,
    pub structure_world: u8,

    pub statements: HashMap<Node, ClightStmt>,

    /// Nodes for which the solver (or deterministic no-model fallback) chose
    /// a concrete candidate before tree assembly. This is exact provenance;
    /// equal candidate values at another node do not imply that node was
    /// selected.
    pub selected_candidate_nodes: HashSet<Node>,

    /// Exact fixed memory-write width of the solver-selected candidate at its
    /// originating node, captured before tree assembly can move or duplicate
    /// equal statements. Diagnostic coverage provenance only.
    pub selected_write_bytes: HashMap<Node, usize>,

    pub successors: HashMap<Node, Vec<Node>>,

    pub used_regs: HashSet<RTLReg>,

    pub struct_fields: HashMap<i64, Vec<(i64, Ident, MemoryChunk)>>,

    pub sseq_groups: HashMap<Node, Vec<Node>>,

    pub var_types: HashMap<RTLReg, CandType>,
    pub var_type_candidates: HashMap<RTLReg, Vec<CandType>>,
    pub var_decl_idx: HashMap<RTLReg, usize>,
    /// Exact selection-owned declarations; legacy candidate indices are only
    /// compatibility projections for types outside the old finite vocabulary.
    pub concrete_declarations:
        BTreeMap<RTLReg, crate::decompile::passes::clight_select::type_graph::TypeTerm>,
    /// CFG-certified native definition webs behind the selected C bindings.
    pub(crate) binding_plan: crate::decompile::passes::clight_select::syntax::bindings::BindingPlan,

    pub loop_headers: HashSet<Node>,
    pub switch_heads: HashSet<Node>,

    pub reg_struct_ids: HashMap<RTLReg, usize>,

    pub loop_info: HashMap<Node, LoopInfo>,
}

pub fn select_clight_stmts(db: &mut DecompileDB) -> Result<Vec<SelectedFunction>, String> {
    let data_model = db.data_model();
    let (mut functions, id_to_name, mut committed_interfaces, interface_vars) =
        extract_functions(db)?;
    let mut analyses = crate::decompile::passes::clight_select::syntax::Stack::production()
        .prepare(db, &mut functions);
    // Reversing Stacking turns a physical frame-cell write into `Sset` of the
    // cell's canonical local.  Retain that structural identity for the width
    // audit; an arbitrary SSA temporary at the same node is not memory-write
    // evidence and must never be credited.
    let mut stack_vars_by_func: HashMap<Address, HashSet<RTLReg>> = HashMap::new();
    for (func, _, _, reg) in db.rel_iter::<(Address, Address, i64, RTLReg)>("stack_var") {
        stack_vars_by_func.entry(*func).or_default().insert(*reg);
    }

    // Refutation half: report what the candidate sets cannot express, before
    // any selection runs. Diagnostic only; it reads the candidates and prints.
    if let Some(first) = functions.first() {
        let evidence = first.class_evidence.clone();
        crate::decompile::passes::clight_select::adequacy::adequacy_audit(&functions, &evidence);
    }

    let mut name_to_ident: HashMap<String, Ident> = HashMap::new();
    {
        // Iterate in sorted (id, name) order so that, on a sanitized-name collision, the surviving Ident is deterministic across runs.
        let mut sorted_id_name: Vec<(&usize, &String)> = id_to_name.iter().collect();
        sorted_id_name.sort_by_key(|(id, name)| (**id, (*name).clone()));
        for (id, name) in sorted_id_name {
            let sanitized =
                crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(
                    name,
                );
            name_to_ident.entry(sanitized).or_insert(*id as Ident);
            name_to_ident.entry(name.clone()).or_insert(*id as Ident);
        }
    }
    {
        let mut sorted_funcs: Vec<&FunctionData> = functions.iter().collect();
        sorted_funcs.sort_by_key(|f| f.address);
        for func in sorted_funcs {
            name_to_ident
                .entry(func.name.clone())
                .or_insert(func.address as Ident);
        }
    }

    // Sort candidates deterministically.  A post-RTL superset node keeps the
    // authoritative memory spelling first for no-model/UNSAT fallback; Z3 can
    // still select its signedness sibling.  Existing field/byte-address
    // preferences remain the next strata.
    for func in &mut functions {
        let mut nodes: Vec<Node> = func.node_statements.keys().copied().collect();
        nodes.sort_unstable();
        for node in nodes {
            let authoritative_structure_world = func.authoritative_structure_world;
            let hypotheses = func.analysis_candidates.get(&node);
            let candidates = func
                .node_statements
                .get_mut(&node)
                .expect("candidate node collected above");
            let all_worlds: BTreeSet<u8> = func.structure_worlds.iter().copied().collect();
            let mut world_masks = func
                .candidate_structure_worlds
                .remove(&node)
                .unwrap_or_else(|| vec![all_worlds.clone(); candidates.len()]);
            while world_masks.len() < candidates.len() {
                world_masks.push(all_worlds.clone());
            }
            world_masks.truncate(candidates.len());
            if candidates.len() > 1 {
                // When a node offers a byte-addressed `(char *)base + c` alongside a bare `base + c` on a non-char pointer, both compile but the bare form silently re-scales the constant by the element size (B2 mis-scaling), so demote it and search the byte-correct char-cast candidate first.
                let has_byte_cast = candidates.iter().any(stmt_uses_charcast_ptr_arith);
                let authoritative_chunk =
                    func.rtl_superset_authoritative_chunks.get(&node).copied();
                let has_authoritative_spelling = authoritative_chunk.is_some_and(|chunk| {
                    candidates
                        .iter()
                        .any(|stmt| stmt_matches_authoritative_chunk(stmt, chunk))
                });
                let mut paired: Vec<(ClightStmt, BTreeSet<u8>)> =
                    candidates.drain(..).zip(world_masks.drain(..)).collect();
                paired.sort_by_key(|(s, worlds)| {
                    let structure_priority =
                        u8::from(!worlds.contains(&authoritative_structure_world));
                    let provenance_priority = superset_provenance_priority(
                        s,
                        authoritative_chunk,
                        has_authoritative_spelling,
                    );
                    // Lower key sorts first. Field-form gets 0, raw-deref form gets 1.
                    let prefers_field = stmt_uses_efield(s);
                    let priority: u8 = if prefers_field {
                        0
                    } else if has_byte_cast
                        && stmt_uses_bare_nonchar_ptr_const_arith(s)
                        && !stmt_uses_charcast_ptr_arith(s)
                    {
                        2
                    } else {
                        1
                    };
                    (
                        structure_priority,
                        // Analysis-generated interpretations are hypotheses, not a
                        // replacement for the ordinary no-model fallback.
                        u8::from(hypotheses.is_some_and(|views| views.contains(s))),
                        provenance_priority,
                        priority,
                        stmt_deterministic_hash(s),
                    )
                });
                let (sorted_candidates, sorted_worlds): (Vec<_>, Vec<_>) =
                    paired.into_iter().unzip();
                *candidates = sorted_candidates;
                world_masks = sorted_worlds;
            }
            func.candidate_structure_worlds.insert(node, world_masks);
        }
    }

    // Bind after the final priority ordering: candidate indices are solver
    // identities, never positions in an unordered upstream relation. Binding
    // earlier could apply a correct view to a different selected statement.
    analyses.bind(db, &mut functions);

    // Dump candidate distribution stats when CANDIDATE_STATS_OUT is set
    if let Ok(out_path) = std::env::var("CANDIDATE_STATS_OUT") {
        let mut histogram: std::collections::BTreeMap<usize, usize> =
            std::collections::BTreeMap::new();
        let mut total_nodes: usize = 0;
        for func in &functions {
            for stmts in func.node_statements.values() {
                total_nodes += 1;
                *histogram.entry(stmts.len()).or_insert(0) += 1;
            }
        }
        // Write as JSON: {"total_nodes": N, "total_functions": N, "histogram": {"1": N, "2": N, ...}}
        let hist_json: String = histogram
            .iter()
            .map(|(k, v)| format!("\"{}\": {}", k, v))
            .collect::<Vec<_>>()
            .join(", ");
        let json = format!(
            "{{\"total_nodes\": {}, \"total_functions\": {}, \"histogram\": {{{}}}}}",
            total_nodes,
            functions.len(),
            hist_json
        );
        let _ = std::fs::write(&out_path, &json);
    }

    let loop_info_all = extract_loop_info(db);
    let ite_info_all = extract_ite_info(db);

    // Determinism diagnostic: fingerprint solver-relevant FunctionData fields before z3 solve -- stable fields + flipping selection means variance is inside z3's model; a moving field names the upstream source.
    if std::env::var("DET_FP").is_ok() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let fh = |s: &str| -> u64 {
            let mut h = DefaultHasher::new();
            s.hash(&mut h);
            h.finish()
        };
        let sorted_kv = |it: Vec<String>| -> String {
            let mut v = it;
            v.sort();
            v.join(",")
        };
        for f in &functions {
            // Candidate vectors keep their stored order (position = priority); maps are key-sorted.
            let vtc = sorted_kv(
                f.var_type_candidates
                    .iter()
                    .map(|(r, cs)| format!("{}:{:?}", r, cs))
                    .collect(),
            );
            let ns = sorted_kv(
                f.node_statements
                    .iter()
                    .map(|(n, ss)| format!("{}:{:?}", n, ss))
                    .collect(),
            );
            let sigs = sorted_kv(
                f.callee_signatures
                    .iter()
                    .map(|(id, s)| {
                        format!(
                            "{}:{}/{:?}/{:?}",
                            id, s.param_count, s.return_type, s.param_types
                        )
                    })
                    .collect(),
            );
            let sftc = sorted_kv(
                f.struct_field_type_candidates
                    .iter()
                    .map(|(k, v)| format!("{:?}:{:?}", k, v))
                    .collect(),
            );
            let sfti = sorted_kv(
                f.struct_field_type_idx
                    .iter()
                    .map(|(k, v)| format!("{:?}:{}", k, v))
                    .collect(),
            );
            let rsi = sorted_kv(
                f.reg_struct_ids
                    .iter()
                    .map(|(k, v)| format!("{}:{}", k, v))
                    .collect(),
            );
            let gti = sorted_kv(
                f.known_global_types
                    .by_ident
                    .iter()
                    .map(|(id, ty)| format!("{}:{:?}", id, ty))
                    .collect(),
            );
            eprintln!(
                "[FP-IN] {:016x} vtc={:016x} ns={:016x} sigs={:016x} ret={:016x} rsi={:016x} sftc={:016x} sfti={:016x} gti={:016x}",
                f.address, fh(&vtc), fh(&ns), fh(&sigs), fh(&format!("{:?}", f.return_type)),
                fh(&rsi), fh(&sftc), fh(&sfti), fh(&gti),
            );
        }
    }

    // Statement-form + type selection is done entirely by the Z3/SMT inference model; the clang-in-the-loop greedy search has been removed (full migration to Z3).
    let mut best_state =
        crate::decompile::passes::clight_select::syntax::solve::infer_select_program(
            &functions,
            &name_to_ident,
            db.ablate_flow_max_certification,
        );

    if !db.ablate_scope_function {
        let stage_b_input_globals = committed_interfaces.globals.clone();
        let outcome = crate::decompile::passes::clight_select::syntax::interface_solve::solve(
            &functions,
            &best_state,
            &interface_vars,
            &committed_interfaces,
            &name_to_ident,
            data_model,
        );
        eprintln!(
            "[interface-solve] vars={} decl-vars={} edges={} solve={}ms unsat={} fallback={} changed-vs-rank0={} changed-decls={}",
            outcome.stats.variable_count,
            outcome.stats.declaration_variable_count,
            outcome.stats.edge_count,
            outcome.stats.solve_ms,
            outcome.stats.unsat_count,
            outcome.stats.fallback_count,
            outcome.stats.changed_from_rank0,
            outcome.stats.changed_declarations,
        );
        let stage_b_choice_ranks = outcome.choice_ranks.clone();
        let mut stage_c_dirty = outcome.dirty_functions.clone();
        if db.ablate_flow_anchor_reopen {
            let changed_globals: BTreeSet<Ident> = outcome
                .choice_ranks
                .keys()
                .filter_map(|id| match id {
                    crate::decompile::passes::clight_select::query::InterfaceVarId::Global {
                        symbol,
                    } if stage_b_input_globals.get(symbol)
                        != outcome.committed.globals.get(symbol) =>
                    {
                        Some(*symbol)
                    }
                    _ => None,
                })
                .collect();
            stage_c_dirty.extend(
                crate::decompile::passes::clight_select::syntax::interface_solve::functions_referencing_globals(
                    &functions,
                    &changed_globals,
                ),
            );
        }
        committed_interfaces = outcome.committed;
        db.interface_instance_dump = outcome.instance_dump;
        let (resolved_state, dirty_stats) =
            crate::decompile::passes::clight_select::syntax::solve::resolve_dirty_functions(
                &mut functions,
                &name_to_ident,
                &best_state,
                &stage_c_dirty,
                &committed_interfaces,
                &outcome.declaration_assignments,
                db.ablate_flow_max_certification,
            );
        best_state = resolved_state;
        eprintln!(
            "[interface-solve] dirty={}/{} resolved={} fallback={} re-solve={}ms",
            dirty_stats.dirty_count,
            functions.len(),
            dirty_stats.resolved_count,
            dirty_stats.fallback_count,
            dirty_stats.elapsed_ms,
        );

        if db.ablate_flow_anchor_reopen {
            let feedback = committed_global_flow_feedback(&functions, &best_state);
            if feedback.is_empty() {
                eprintln!(
                    "[interface-solve] flow-anchor-reopen prices=0 reopened=0 changed=0 dirty=0"
                );
            } else {
                let prior_globals = committed_interfaces.globals.clone();
                let reopened = crate::decompile::passes::clight_select::syntax::interface_solve::solve_with_global_feedback(
                    &functions,
                    &best_state,
                    &interface_vars,
                    &committed_interfaces,
                    &name_to_ident,
                    &feedback,
                    Some(&stage_b_choice_ranks),
                    data_model,
                );
                let requested_symbols: BTreeSet<Ident> =
                    feedback.iter().map(|item| item.symbol).collect();
                let changed_symbols: BTreeSet<Ident> = requested_symbols
                    .iter()
                    .copied()
                    .filter(|&symbol| {
                        prior_globals.get(&symbol) != reopened.committed.globals.get(&symbol)
                    })
                    .collect();
                let reopen_dirty = crate::decompile::passes::clight_select::syntax::interface_solve::functions_referencing_globals(
                    &functions,
                    &changed_symbols,
                );
                let reopened_count = requested_symbols
                    .iter()
                    .filter(|&&symbol| {
                        reopened.assignments.contains_key(
                            &crate::decompile::passes::clight_select::query::InterfaceVarId::Global {
                                symbol,
                            },
                        )
                    })
                    .count();
                eprintln!(
                    "[interface-solve] flow-anchor-reopen prices={} reopened={} changed={} dirty={}",
                    feedback.len(),
                    reopened_count,
                    changed_symbols.len(),
                    reopen_dirty.len(),
                );
                committed_interfaces = reopened.committed;
                db.interface_instance_dump = reopened.instance_dump;
                if !reopen_dirty.is_empty() {
                    let (resolved_state, reopen_stats) =
                        crate::decompile::passes::clight_select::syntax::solve::resolve_dirty_functions(
                            &mut functions,
                            &name_to_ident,
                            &best_state,
                            &reopen_dirty,
                            &committed_interfaces,
                            &reopened.declaration_assignments,
                            db.ablate_flow_max_certification,
                        );
                    best_state = resolved_state;
                    eprintln!(
                        "[interface-solve] flow-anchor-reopen resolved={} fallback={} re-solve={}ms",
                        reopen_stats.resolved_count,
                        reopen_stats.fallback_count,
                        reopen_stats.elapsed_ms,
                    );
                }
            }
        }
    } else {
        eprintln!("[interface-solve] disabled by --ablate-scope=function (Stage A unchanged)");
        db.interface_instance_dump.clear();
    }
    db.committed_interfaces = committed_interfaces;
    db.interface_vars = interface_vars;
    analyses.publish(db, &functions, &best_state);

    for func in &functions {
        let world = best_state
            .structure_world
            .get(&func.address)
            .copied()
            .unwrap_or(func.authoritative_structure_world);
        for (node, masks) in &func.candidate_structure_worlds {
            let Some(Some(index)) = best_state
                .candidate_idx
                .get(&(func.address, *node))
                .copied()
            else {
                continue;
            };
            if masks
                .get(index)
                .is_some_and(|worlds| !worlds.contains(&world))
            {
                return Err(format!(
                    "selector chose candidate {index} at {node:#x} outside structure world {world} in {:#x}",
                    func.address
                ));
            }
        }
    }

    let multi_world_functions = functions
        .iter()
        .filter(|func| func.structure_worlds.len() > 1)
        .count();
    let flat_selected = functions
        .iter()
        .filter(|func| {
            best_state
                .structure_world
                .get(&func.address)
                .copied()
                .unwrap_or(func.authoritative_structure_world)
                != func.authoritative_structure_world
        })
        .count();
    eprintln!(
        "[structure-superset] multi-world-functions={} flat-selected={} authoritative-selected={}",
        multi_world_functions,
        flat_selected,
        functions.len().saturating_sub(flat_selected),
    );

    // Split result into per-function SelectedFunction
    let selected: Vec<SelectedFunction> = functions
        .iter()
        .map(|func| {
            build_selected_function_from_program_state(
                func,
                &best_state,
                &loop_info_all,
                &ite_info_all,
                db.abi().pointer_size,
                stack_vars_by_func.get(&func.address),
            )
        })
        .collect();

    // Corpus gauge for the pointer-to-float generation family.  Count exact
    // selected AST occurrences before tree assembly/postselect rewriting can
    // move, duplicate, or erase them.
    let selected_integer_float_bridges: usize = selected
        .iter()
        .flat_map(|func| func.statements.values())
        .map(count_integer_float_bridge_casts_stmt)
        .sum();
    eprintln!(
        "[clight-select] integer-float-bridge-casts selected={}",
        selected_integer_float_bridges,
    );

    // Read-only wt audit (CTYPING_PLAN.md P2): frontend-typing diagnoses over the selected statements/decls, stderr only.
    if std::env::var("MANIFOLD_WT_AUDIT_OFF").is_err() {
        crate::decompile::passes::clight_select::wt_audit::wt_audit(
            &functions,
            &selected,
            &name_to_ident,
        );
    }

    // Certificate pass: fold the FINAL selection and report the flow-certified
    // fraction. Read-only, and it runs whichever engine produced the selection.
    flow_certificate(&functions, &selected);

    if std::env::var("DET_FP").is_ok() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let fh = |s: &str| -> u64 {
            let mut h = DefaultHasher::new();
            s.hash(&mut h);
            h.finish()
        };
        for f in &selected {
            let mut st: Vec<String> = f
                .statements
                .iter()
                .map(|(n, s)| format!("{}:{:?}", n, s))
                .collect();
            st.sort();
            let mut su: Vec<String> = f
                .successors
                .iter()
                .map(|(n, v)| format!("{}:{:?}", n, v))
                .collect();
            su.sort();
            let mut sg: Vec<String> = f
                .sseq_groups
                .iter()
                .map(|(k, v)| format!("{}:{:?}", k, v))
                .collect();
            sg.sort();
            // LoopInfo HashMaps have non-deterministic Debug order; key-sort so the fingerprint only moves on real content changes.
            let mut li: Vec<String> = f
                .loop_info
                .iter()
                .map(|(n, v)| {
                    let mut bs: Vec<String> = v
                        .exit_targets
                        .iter()
                        .map(|(k, s)| format!("{}:{:?}", k, s))
                        .collect();
                    bs.sort();
                    let mut er: Vec<(Node, (Node, Node))> =
                        v.exit_returns.iter().map(|(k, p)| (*k, *p)).collect();
                    er.sort();
                    format!(
                        "{}:body={:?} primary={:?} breaks=[{}] rets={:?}",
                        n,
                        v.body_nodes,
                        v.primary_exit,
                        bs.join(","),
                        er
                    )
                })
                .collect();
            li.sort();
            let mut rsi: Vec<String> = f
                .reg_struct_ids
                .iter()
                .map(|(k, v)| format!("{}:{}", k, v))
                .collect();
            rsi.sort();
            eprintln!(
                "[FP-A] {:016x} stmts={:016x} succ={:016x} sseq={:016x} linfo={:016x} rsi={:016x}",
                f.address,
                fh(&st.join(",")),
                fh(&su.join(",")),
                fh(&sg.join(",")),
                fh(&li.join(",")),
                fh(&rsi.join(",")),
            );
        }
    }

    Ok(selected)
}

fn selected_flow_statements(
    func: &FunctionData,
    state: &ProgramSelectionState,
) -> BTreeMap<Node, ClightStmt> {
    func.node_statements
        .iter()
        .filter_map(|(&node, candidates)| {
            let choice = state
                .candidate_idx
                .get(&(func.address, node))
                .copied()
                .unwrap_or(Some(0))?;
            candidates
                .get(choice)
                .or_else(|| candidates.first())
                .cloned()
                .map(|stmt| (node, stmt))
        })
        .collect()
}

/// Read the final Stage-C body without changing it.  A GlobalType
/// contradiction is feedback for the program-level commitment that supplied
/// the anchor, so retain the exact function/site/symbol and the body's claim.
fn committed_global_flow_feedback(
    functions: &[FunctionData],
    state: &ProgramSelectionState,
) -> Vec<crate::decompile::passes::clight_select::syntax::interface_solve::GlobalFlowDisagreement> {
    use crate::decompile::passes::clight_select::{
        solvers::flow, solvers::in_search::flow_theory, syntax::interface_solve,
    };

    let mut feedback = BTreeSet::new();
    for func in functions {
        if func.flow_blocks.is_empty() || func.flow_anchors.global.is_empty() {
            continue;
        }
        let selected = selected_flow_statements(func, state);
        let candidates: BTreeMap<Node, Vec<ClightStmt>> = func
            .node_statements
            .iter()
            .map(|(&node, candidates)| (node, candidates.clone()))
            .collect();
        let selectable: BTreeSet<Node> = candidates
            .iter()
            .filter(|(_, candidates)| candidates.len() > 1)
            .map(|(&node, _)| node)
            .collect();
        let (_, contradictions) = flow_theory::certify(
            &func.flow_blocks,
            &func.flow_anchors,
            &selected,
            &candidates,
            &selectable,
            func.ptr64,
        );
        for contradiction in contradictions {
            if contradiction.kind != flow::AnchorKind::GlobalType {
                continue;
            }
            let Some(symbol) = contradiction.global_symbol else {
                continue;
            };
            feedback.insert(interface_solve::GlobalFlowDisagreement {
                function: func.address,
                node: contradiction.node,
                symbol,
                claimed: contradiction.claimed,
            });
        }
    }
    feedback.into_iter().collect()
}

/// Fold the FINAL selection through the flow evaluator and report the certified
/// fraction, together with whatever the in-solve theory did during the search.
///
/// A block is FLOW-CERTIFIED when a machine anchor reaches it and its selected
/// statements carry values consistent with every anchor it crosses, over the
/// (class, width) domain. That is flow consistency, not verification: the
/// domain is tiny, the analysis is intra-block, and a certified block can still
/// be wrong in every way the domain cannot see.
fn flow_certificate(functions: &[FunctionData], selected: &[SelectedFunction]) {
    use crate::decompile::passes::clight_select::solvers::in_search::flow_theory;
    use std::collections::{BTreeMap, BTreeSet};

    // Two different measurements share the line: what the search did while
    // solving, and what the final selection looks like now. Keep them apart.
    let in_solve = crate::decompile::passes::clight_select::syntax::solve::flow_stats_snapshot();
    let mut total = crate::decompile::passes::clight_select::solvers::flow::FlowStats::default();
    let detail = std::env::var("MANIFOLD_FLOW").unwrap_or_default();
    let want_detail = |name: &str| match detail.as_str() {
        "" => false,
        "1" | "true" => true,
        pat => name.contains(pat),
    };

    let mut lines: Vec<String> = Vec::new();
    for (func, sel) in functions.iter().zip(selected.iter()) {
        if func.flow_blocks.is_empty() || func.flow_anchors.is_empty() {
            continue;
        }
        let stmts: BTreeMap<Node, ClightStmt> = sel
            .statements
            .iter()
            .map(|(n, s)| (*n, s.clone()))
            .collect();
        let selectable: BTreeSet<Node> = func
            .node_statements
            .iter()
            .filter(|(_, c)| c.len() > 1)
            .map(|(n, _)| *n)
            .collect();
        let all_candidates: BTreeMap<Node, Vec<ClightStmt>> = func
            .node_statements
            .iter()
            .map(|(n, c)| (*n, c.clone()))
            .collect();
        let (stats, contras) = flow_theory::certify(
            &func.flow_blocks,
            &func.flow_anchors,
            &stmts,
            &all_candidates,
            &selectable,
            func.ptr64,
        );
        total.merge(&stats);
        if want_detail(&func.name) {
            for c in &contras {
                lines.push(format!(
                    "  FLOW-UNCERTIFIED fn={} ({:#x}) {}",
                    func.name,
                    func.address,
                    flow_theory::describe(c)
                ));
            }
        }
    }

    if total.blocks_checked == 0 {
        return;
    }
    let pct = if total.blocks_anchored == 0 {
        0.0
    } else {
        100.0 * total.blocks_certified as f64 / total.blocks_anchored as f64
    };
    eprintln!(
        "[flow] blocks={} anchored={} flow-certified={} ({:.1}% of anchored) contradictions={} by-chunk={} by-extern-sig={} by-global={} by-statement={} | in-solve: clauses={} gaps={} final-rounds={} caps-hit={} ties-determined-by-flow={} unsat-retries={} exempted-nodes={} exemption-skips={}",
        total.blocks_checked,
        total.blocks_anchored,
        total.blocks_certified,
        pct,
        total.contradictions,
        total.by_chunk,
        total.by_extern_signature,
        total.by_global_type,
        total.by_statement_only,
        in_solve.clauses_injected,
        in_solve.gaps,
        in_solve.final_rounds,
        in_solve.caps_hit,
        in_solve.ties_determined_by_flow,
        in_solve.unsat_retries,
        in_solve.exempted_nodes,
        in_solve.exemptions_skipped,
    );
    lines.sort();
    lines.dedup();
    for line in lines {
        eprintln!("{}", line);
    }
}

fn det_fp_stage(addr: Address, stage: &str, statements: &HashMap<Node, ClightStmt>) {
    if let Ok(want) = std::env::var("CF3_DUMP") {
        if let Ok(waddr) = u64::from_str_radix(want.trim_start_matches("0x"), 16) {
            if waddr == addr {
                let mut keys: Vec<Node> = statements.keys().copied().collect();
                keys.sort_unstable();
                let sw: usize = statements.values().map(count_switches).sum();
                eprintln!("[DUMP-{}] {} keys, {} switches", stage, keys.len(), sw);
                if let Ok(hdr) = std::env::var("CF3_DUMP_NODE") {
                    if let Ok(h) = u64::from_str_radix(hdr.trim_start_matches("0x"), 16) {
                        if let Some(s) = statements.get(&h) {
                            eprintln!("[DUMP-{}] node {:x}: {:?}", stage, h, s);
                        }
                        let mut goto_owners: Vec<Node> = statements
                            .iter()
                            .filter_map(|(owner, stmt)| {
                                collect_goto_targets(stmt).contains(&h).then_some(*owner)
                            })
                            .collect();
                        goto_owners.sort_unstable();
                        let mut label_owners: Vec<Node> = statements
                            .iter()
                            .filter_map(|(owner, stmt)| {
                                stmt_contains_label(stmt, ident_from_node(h)).then_some(*owner)
                            })
                            .collect();
                        label_owners.sort_unstable();
                        eprintln!(
                            "[DUMP-{}] target {:x}: goto_owners={:?} label_owners={:?}",
                            stage, h, goto_owners, label_owners
                        );
                    }
                }
            }
        }
    }
    if std::env::var("DET_FP").is_err() {
        return;
    }
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut items: Vec<String> = statements
        .iter()
        .map(|(n, s)| format!("{}:{:?}", n, s))
        .collect();
    items.sort();
    let mut h = DefaultHasher::new();
    items.join(",").hash(&mut h);
    eprintln!("[FP-{}] {:016x} {:016x}", stage, addr, h.finish());
}

fn assemble_sseq_groups(
    statements: &mut HashMap<Node, ClightStmt>,
    groups: &HashMap<Node, Vec<Node>>,
) -> HashMap<Node, Vec<Node>> {
    let mut applied = HashMap::new();
    let mut claimed_members = HashSet::new();

    // Query rejects overlapping groups.  Keep the invariant explicit here so
    // later emission can map each removed member to exactly one live anchor.
    for members in groups.values() {
        for &member in members {
            assert!(
                claimed_members.insert(member),
                "overlapping Clight straight-line groups reached selection at node {member:#x}"
            );
        }
    }

    // Groups are disjoint, so HashMap iteration order cannot affect the result.
    for members in groups.values() {
        // Record exactly the statement keys this stage will coalesce.  A
        // member already absent after loop/ITE assembly remains a transparent
        // node in the full successor graph; claiming it here would falsely
        // attribute an earlier transformation to S4.  Exact empty goto
        // targets are materialized as labeled skips by query and therefore do
        // appear in this live set.
        let live_members: Vec<Node> = members
            .iter()
            .copied()
            .filter(|member| statements.contains_key(member))
            .collect();
        if live_members.len() <= 1 {
            continue;
        }

        let anchor = live_members[0];
        let seq_stmts: Vec<ClightStmt> = live_members
            .iter()
            .map(|member| {
                statements
                    .get(member)
                    .expect("live sequence member disappeared before assembly")
                    .clone()
            })
            .collect();
        statements.insert(anchor, ClightStmt::Ssequence(flatten_sequence(seq_stmts)));
        for &member in live_members.iter().skip(1) {
            statements.remove(&member);
        }
        applied.insert(anchor, live_members);
    }

    applied
}

fn assert_sseq_anchors_survive(
    statements: &HashMap<Node, ClightStmt>,
    protected: &HashSet<Node>,
    stage: &str,
) {
    assert!(
        protected
            .iter()
            .all(|anchor| statements.contains_key(anchor)),
        "an applied Clight straight-line anchor was removed during {stage}"
    );
}

/// Build a SelectedFunction from the program-level search result for one function.
fn build_selected_function_from_program_state(
    func: &FunctionData,
    program_state: &ProgramSelectionState,
    loop_info_all: &HashMap<Address, HashMap<Node, LoopInfo>>,
    ite_info_all: &HashMap<Address, HashMap<Node, IteInfo>>,
    pointer_size: usize,
    stack_vars: Option<&HashSet<RTLReg>>,
) -> SelectedFunction {
    let addr = func.address;
    let structure_world = program_state
        .structure_world
        .get(&addr)
        .copied()
        .unwrap_or(func.authoritative_structure_world);
    let structured_world = structure_world == func.authoritative_structure_world;
    let successors = func
        .successors_by_structure_world
        .get(&structure_world)
        .unwrap_or(&func.successors);

    // Extract per-function SelectionState from the program state
    let mut candidate_idx = HashMap::new();
    for (node, _) in &func.node_statements {
        if let Some(idx) = program_state.candidate_idx.get(&(addr, *node)) {
            candidate_idx.insert(*node, *idx);
        }
    }
    let mut var_decl_idx = func.var_decl_idx.clone();
    for (reg, _) in &func.var_decl_idx {
        if let Some(&idx) = program_state.var_decl_idx.get(&(addr, *reg)) {
            var_decl_idx.insert(*reg, idx);
        }
    }
    // Also pick up var_decl_idx for regs that only appeared in var_type_candidates
    for reg in func.var_type_candidates.keys() {
        if let Some(&idx) = program_state.var_decl_idx.get(&(addr, *reg)) {
            var_decl_idx.insert(*reg, idx);
        }
    }

    // Apply generic-inference type overrides: a register whose inferred type is not among its enumerated candidates gets that type appended as a synthetic candidate with var_decl_idx pointed at it, so the emitter (which reads var_type_candidates[var_decl_idx]) sees the inferred type unchanged.
    let mut var_type_candidates = func.var_type_candidates.clone();
    if !program_state.var_type_override.is_empty() {
        for ((ov_addr, reg), ty) in &program_state.var_type_override {
            if *ov_addr != addr {
                continue;
            }
            let cands = var_type_candidates.entry(*reg).or_default();
            let idx = cands.iter().position(|c| c == ty).unwrap_or_else(|| {
                cands.push(ty.clone());
                cands.len() - 1
            });
            var_decl_idx.insert(*reg, idx);
        }
    }

    let concrete_declarations = program_state
        .analysis_results
        .get(&addr)
        .and_then(|results| {
            crate::decompile::passes::clight_select::syntax::type_evidence::COMMITMENTS.get(results)
        })
        .cloned()
        .unwrap_or_default();
    let mut stack_var_types = HashMap::new();
    let binding_plan = crate::decompile::passes::clight_select::syntax::bindings::PLAN
        .get(&func.analysis_facts)
        .cloned()
        .unwrap_or_default();
    let storage_registers: HashSet<_> = stack_vars
        .into_iter()
        .flatten()
        .copied()
        .chain(binding_plan.storage.iter().map(|(_, _, binding)| *binding))
        .collect();
    for reg in storage_registers {
        if let Some(term) = concrete_declarations.get(&reg) {
            stack_var_types.insert(reg as Ident, term.to_clight(func.data_model));
            continue;
        }
        let index = var_decl_idx.get(&reg).copied().unwrap_or(0);
        let selected_type = var_type_candidates
            .get(&reg)
            .and_then(|candidates| candidates.get(index))
            .or_else(|| func.var_types.get(&reg));
        if let Some(&selected_type) = selected_type {
            stack_var_types.insert(
                reg as Ident,
                crate::decompile::passes::clight_select::wt_audit::candtype_to_clight(
                    selected_type,
                ),
            );
        }
    }

    let per_func_state = SelectionState { candidate_idx };

    // Materialize and post-process
    let mut statements = materialize_statements(&per_func_state, func, structure_world);
    let selected_candidate_nodes = statements.keys().copied().collect();
    let selected_write_bytes = statements
        .iter()
        .filter_map(|(node, stmt)| {
            let width = crate::decompile::analysis::coverage_pass::stmt_selected_write_bytes(
                stmt,
                pointer_size,
                &stack_var_types,
            );
            (width > 0).then_some((*node, width))
        })
        .collect();
    crate::decompile::passes::clight_select::syntax::Stack::production().retain_origins(
        func,
        &per_func_state.candidate_idx,
        &mut statements,
    );
    det_fp_stage(func.address, "S1mat", &statements);
    redirect_gotos_through_selected_away_nodes(&mut statements, successors);
    if structured_world {
        duplicate_straight_line_return_tails(&mut statements, successors);
    }
    det_fp_stage(func.address, "S1cfg", &statements);

    let func_loop_info = if structured_world {
        loop_info_all
            .get(&func.address)
            .cloned()
            .unwrap_or_default()
    } else {
        HashMap::new()
    };
    let applied_sseq_groups = if structured_world {
        assemble_loops(&mut statements, &func_loop_info, successors);
        det_fp_stage(func.address, "S2loop", &statements);

        let func_ite_info = ite_info_all.get(&func.address).cloned().unwrap_or_default();
        assemble_ite(&mut statements, &func_ite_info, successors);
        det_fp_stage(func.address, "S3ite", &statements);

        let applied = assemble_sseq_groups(&mut statements, &func.sseq_groups);
        let protected: HashSet<Node> = applied.keys().copied().collect();
        det_fp_stage(func.address, "S4sseq", &statements);
        materialize_cfg_fallthrough_gotos(&mut statements, successors);
        det_fp_stage(func.address, "S4cfg", &statements);
        inline_control_flow_bodies(&mut statements, successors, &protected);
        assert_sseq_anchors_survive(&statements, &protected, "S5 inlining");
        det_fp_stage(func.address, "S5inline", &statements);
        flatten_cascading_ifthenelse_all(&mut statements);
        det_fp_stage(func.address, "S6flat", &statements);
        inline_switch_case_bodies(&mut statements, &protected);
        assert_sseq_anchors_survive(&statements, &protected, "S6 switch inlining");
        det_fp_stage(func.address, "S6sw", &statements);
        deduplicate_identical_blocks(&mut statements, &protected, successors);
        assert_sseq_anchors_survive(&statements, &protected, "S7 deduplication");
        det_fp_stage(func.address, "S7dedup", &statements);
        materialize_cfg_fallthrough_gotos(&mut statements, successors);
        det_fp_stage(func.address, "S7cfg", &statements);
        ensure_goto_labels(&mut statements);
        det_fp_stage(func.address, "S8labels", &statements);
        assert_sseq_anchors_survive(&statements, &protected, "final labeling");
        applied
    } else {
        // Conservative world: retain the flat semantic CFG and make every
        // fallthrough/target explicit.  No loop, if, switch, straight-line,
        // or block-inlining transform is allowed to leak in from world zero.
        materialize_cfg_fallthrough_gotos(&mut statements, successors);
        ensure_goto_labels(&mut statements);
        HashMap::new()
    };

    SelectedFunction {
        address: func.address,
        name: func.name.clone(),
        entry_node: func.entry_node,
        return_type: func.return_type.clone(),
        param_regs: func.param_regs.clone(),
        param_types: func.param_types.clone(),
        stack_size: func.stack_size,
        structure_world,
        statements,
        selected_candidate_nodes,
        selected_write_bytes,
        successors: successors.clone(),
        used_regs: func.used_regs.clone(),
        struct_fields: func.struct_fields.clone(),
        sseq_groups: applied_sseq_groups,
        var_types: func.var_types.clone(),
        var_type_candidates,
        var_decl_idx,
        concrete_declarations,
        binding_plan,
        loop_headers: if structured_world {
            func.loop_headers.clone()
        } else {
            HashSet::new()
        },
        switch_heads: if structured_world {
            func.switch_heads.clone()
        } else {
            HashSet::new()
        },
        reg_struct_ids: func.reg_struct_ids.clone(),
        loop_info: func_loop_info,
    }
}

fn materialize_statements(
    state: &SelectionState,
    func: &FunctionData,
    structure_world: u8,
) -> HashMap<Node, ClightStmt> {
    let mut statements = HashMap::new();
    for (node, candidates) in &func.node_statements {
        // A node MISSING from the map means the solver emitted no selection
        // for this function (z3 yielded no model): fall back to the first
        // candidate belonging to the selected structural world.  An explicit
        // None entry = SKIP this node.
        let fallback = func
            .candidate_structure_worlds
            .get(node)
            .and_then(|masks| {
                masks
                    .iter()
                    .position(|worlds| worlds.contains(&structure_world))
            })
            .or_else(|| (!candidates.is_empty()).then_some(0));
        match state.candidate_idx.get(node).copied().unwrap_or(fallback) {
            Some(idx) => {
                if let Some(stmt) = candidates.get(idx).or_else(|| candidates.last()) {
                    statements.insert(*node, stmt.clone());
                }
            }
            None => {
                // SKIP: omit this node. ensure_goto_labels will add labeled Sskip if needed.
            }
        }
    }
    statements
}

fn stmt_deterministic_hash(stmt: &ClightStmt) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    stmt.hash(&mut hasher);
    hasher.finish()
}

/// True if the stmt (or any sub-stmt/sub-expr) contains an Efield access; used to prefer recovered struct-field forms over raw pointer derefs in candidate selection.
fn stmt_uses_efield(stmt: &ClightStmt) -> bool {
    fn expr_has_efield(e: &ClightExpr) -> bool {
        match e {
            ClightExpr::Efield(..) => true,
            ClightExpr::Ederef(inner, _)
            | ClightExpr::Eaddrof(inner, _)
            | ClightExpr::Eunop(_, inner, _)
            | ClightExpr::Ecast(inner, _) => expr_has_efield(inner),
            ClightExpr::Ebinop(_, l, r, _) => expr_has_efield(l) || expr_has_efield(r),
            ClightExpr::Econdition(c, t, f, _) => {
                expr_has_efield(c) || expr_has_efield(t) || expr_has_efield(f)
            }
            _ => false,
        }
    }
    match stmt {
        ClightStmt::Sassign(l, r) => expr_has_efield(l) || expr_has_efield(r),
        ClightStmt::Sset(_, e) => expr_has_efield(e),
        ClightStmt::Scall(_, f, args) => expr_has_efield(f) || args.iter().any(expr_has_efield),
        ClightStmt::Sbuiltin(_, _, _, args) => args.iter().any(expr_has_efield),
        ClightStmt::Sreturn(Some(e)) => expr_has_efield(e),
        ClightStmt::Sifthenelse(c, t, e) => {
            expr_has_efield(c) || stmt_uses_efield(t) || stmt_uses_efield(e)
        }
        ClightStmt::Ssequence(ss) => ss.iter().any(stmt_uses_efield),
        ClightStmt::Sloop(a, b) => stmt_uses_efield(a) || stmt_uses_efield(b),
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => stmt_uses_efield(inner),
        ClightStmt::Sswitch(e, cases) => {
            expr_has_efield(e) || cases.iter().any(|(_, s)| stmt_uses_efield(s))
        }
        _ => false,
    }
}

/// True if the pointee is a 1-byte char type, i.e. `base + c` is already byte arithmetic.
fn is_char_pointee(ty: &ClightType) -> bool {
    matches!(ty, ClightType::Tpointer(inner, _) if matches!(inner.as_ref(), ClightType::Tint(ClightIntSize::I8, _, _)))
}

/// True if the stmt contains a byte-addressed pointer add/sub `(char *)base + c` (the B2-correct form: offset is bytes, not scaled by an element size).
fn stmt_uses_charcast_ptr_arith(stmt: &ClightStmt) -> bool {
    fn expr_has(e: &ClightExpr) -> bool {
        if let ClightExpr::Ebinop(op, l, r, _) = e {
            if matches!(op, ClightBinaryOp::Oadd | ClightBinaryOp::Osub) {
                let l_char = matches!(l.as_ref(), ClightExpr::Ecast(_, t) if is_char_pointee(t));
                let r_char = matches!(r.as_ref(), ClightExpr::Ecast(_, t) if is_char_pointee(t));
                if l_char || r_char {
                    return true;
                }
            }
        }
        match e {
            ClightExpr::Ederef(inner, _)
            | ClightExpr::Eaddrof(inner, _)
            | ClightExpr::Eunop(_, inner, _)
            | ClightExpr::Ecast(inner, _)
            | ClightExpr::Efield(inner, _, _) => expr_has(inner),
            ClightExpr::Ebinop(_, l, r, _) => expr_has(l) || expr_has(r),
            ClightExpr::Econdition(c, t, f, _) => expr_has(c) || expr_has(t) || expr_has(f),
            _ => false,
        }
    }
    walk_stmt_exprs(stmt, &expr_has)
}

/// True if the stmt contains a bare add/sub of a non-zero integer CONSTANT to a non-char pointer (e.g. `base + 10`, `base` is `T *`, T != char); C re-scales the constant by sizeof(T), so this form mis-scales whenever the constant is a raw byte offset.
fn stmt_uses_bare_nonchar_ptr_const_arith(stmt: &ClightStmt) -> bool {
    fn const_val(e: &ClightExpr) -> Option<i64> {
        match e {
            ClightExpr::EconstInt(v, _) => Some(*v as i64),
            ClightExpr::EconstLong(v, _) => Some(*v),
            _ => None,
        }
    }
    fn bare_nonchar_ptr(e: &ClightExpr) -> bool {
        // A pointer operand that is not itself a char-cast (which would already be byte arithmetic).
        if matches!(e, ClightExpr::Ecast(_, t) if is_char_pointee(t)) {
            return false;
        }
        let ty = crate::decompile::passes::csh_pass::clight_expr_type(e);
        matches!(ty, ClightType::Tpointer(ref inner, _) if !matches!(inner.as_ref(), ClightType::Tint(ClightIntSize::I8, _, _)))
    }
    fn expr_has(e: &ClightExpr) -> bool {
        if let ClightExpr::Ebinop(op, l, r, _) = e {
            if matches!(op, ClightBinaryOp::Oadd | ClightBinaryOp::Osub) {
                let lc = const_val(l);
                let rc = const_val(r);
                if matches!(rc, Some(c) if c != 0) && bare_nonchar_ptr(l) {
                    return true;
                }
                if matches!(lc, Some(c) if c != 0) && bare_nonchar_ptr(r) {
                    return true;
                }
            }
        }
        match e {
            ClightExpr::Ederef(inner, _)
            | ClightExpr::Eaddrof(inner, _)
            | ClightExpr::Eunop(_, inner, _)
            | ClightExpr::Ecast(inner, _)
            | ClightExpr::Efield(inner, _, _) => expr_has(inner),
            ClightExpr::Ebinop(_, l, r, _) => expr_has(l) || expr_has(r),
            ClightExpr::Econdition(c, t, f, _) => expr_has(c) || expr_has(t) || expr_has(f),
            _ => false,
        }
    }
    walk_stmt_exprs(stmt, &expr_has)
}

/// Apply an expression predicate to every top-level expression carried by a statement (recursing into nested statements); returns true if it holds for any of them.
fn walk_stmt_exprs(stmt: &ClightStmt, pred: &dyn Fn(&ClightExpr) -> bool) -> bool {
    match stmt {
        ClightStmt::Sassign(l, r) => pred(l) || pred(r),
        ClightStmt::Sset(_, e) => pred(e),
        ClightStmt::Scall(_, f, args) => pred(f) || args.iter().any(|a| pred(a)),
        ClightStmt::Sbuiltin(_, _, _, args) => args.iter().any(|a| pred(a)),
        ClightStmt::Sreturn(Some(e)) => pred(e),
        ClightStmt::Sifthenelse(c, t, e) => {
            pred(c) || walk_stmt_exprs(t, pred) || walk_stmt_exprs(e, pred)
        }
        ClightStmt::Ssequence(ss) => ss.iter().any(|s| walk_stmt_exprs(s, pred)),
        ClightStmt::Sloop(a, b) => walk_stmt_exprs(a, pred) || walk_stmt_exprs(b, pred),
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => walk_stmt_exprs(inner, pred),
        ClightStmt::Sswitch(e, cases) => {
            pred(e) || cases.iter().any(|(_, s)| walk_stmt_exprs(s, pred))
        }
        _ => false,
    }
}

fn count_integer_float_bridge_casts_expr(expr: &ClightExpr) -> usize {
    let here = usize::from(matches!(
        expr,
        ClightExpr::Ecast(inner, ClightType::Tfloat(..))
            if matches!(
                inner.as_ref(),
                ClightExpr::Ecast(_, ClightType::Tint(..) | ClightType::Tlong(..))
            )
    ));
    here + match expr {
        ClightExpr::Ederef(inner, _)
        | ClightExpr::Eaddrof(inner, _)
        | ClightExpr::Eunop(_, inner, _)
        | ClightExpr::Ecast(inner, _)
        | ClightExpr::Efield(inner, _, _) => count_integer_float_bridge_casts_expr(inner),
        ClightExpr::Ebinop(_, left, right, _) => {
            count_integer_float_bridge_casts_expr(left)
                + count_integer_float_bridge_casts_expr(right)
        }
        ClightExpr::Econdition(cond, then_expr, else_expr, _) => {
            count_integer_float_bridge_casts_expr(cond)
                + count_integer_float_bridge_casts_expr(then_expr)
                + count_integer_float_bridge_casts_expr(else_expr)
        }
        _ => 0,
    }
}

fn count_integer_float_bridge_casts_stmt(stmt: &ClightStmt) -> usize {
    match stmt {
        ClightStmt::Sassign(left, right) => {
            count_integer_float_bridge_casts_expr(left)
                + count_integer_float_bridge_casts_expr(right)
        }
        ClightStmt::Sset(_, expr) | ClightStmt::Sreturn(Some(expr)) => {
            count_integer_float_bridge_casts_expr(expr)
        }
        ClightStmt::Scall(_, callee, args) => {
            count_integer_float_bridge_casts_expr(callee)
                + args
                    .iter()
                    .map(count_integer_float_bridge_casts_expr)
                    .sum::<usize>()
        }
        ClightStmt::Sbuiltin(_, _, _, args) => {
            args.iter().map(count_integer_float_bridge_casts_expr).sum()
        }
        ClightStmt::Ssequence(stmts) => stmts
            .iter()
            .map(count_integer_float_bridge_casts_stmt)
            .sum(),
        ClightStmt::Sifthenelse(cond, then_stmt, else_stmt) => {
            count_integer_float_bridge_casts_expr(cond)
                + count_integer_float_bridge_casts_stmt(then_stmt)
                + count_integer_float_bridge_casts_stmt(else_stmt)
        }
        ClightStmt::Sloop(body, increment) => {
            count_integer_float_bridge_casts_stmt(body)
                + count_integer_float_bridge_casts_stmt(increment)
        }
        ClightStmt::Sswitch(expr, cases) => {
            count_integer_float_bridge_casts_expr(expr)
                + cases
                    .iter()
                    .map(|(_, stmt)| count_integer_float_bridge_casts_stmt(stmt))
                    .sum::<usize>()
        }
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => count_integer_float_bridge_casts_stmt(inner),
        _ => 0,
    }
}

fn is_semantic_skip(stmt: &ClightStmt) -> bool {
    match stmt {
        ClightStmt::Sskip => true,
        ClightStmt::Slabel(_, inner) => is_semantic_skip(inner),
        ClightStmt::Ssequence(stmts) => stmts.iter().all(is_semantic_skip),
        _ => false,
    }
}

/// Resolve a CFG target against the statements that survived selection.  Only
/// a unique successor may forward an absent/Sskip node; ambiguity, cycles, or
/// a path back into the loop body reject loop assembly.
fn resolve_live_outside_target(
    target: Node,
    statements: &HashMap<Node, ClightStmt>,
    successors: &HashMap<Node, Vec<Node>>,
    body_node_set: &HashSet<Node>,
) -> Option<Node> {
    let mut current = target;
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(current) || body_node_set.contains(&current) {
            return None;
        }
        if statements
            .get(&current)
            .is_some_and(|stmt| !is_semantic_skip(stmt))
        {
            return Some(current);
        }
        match successors.get(&current).map(Vec::as_slice) {
            Some([next]) => current = *next,
            _ => return None,
        }
    }
}

/// Resolve the first selected statement reached from a loop entry while
/// staying inside that loop.  This is the structural body frontier used by a
/// `continue`: a dominance header can select to Sskip while its unique CFG
/// successor is the first emitted operation.
fn resolve_live_inside_target(
    target: Node,
    statements: &HashMap<Node, ClightStmt>,
    successors: &HashMap<Node, Vec<Node>>,
    body_node_set: &HashSet<Node>,
) -> Option<Node> {
    let mut current = target;
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(current) || !body_node_set.contains(&current) {
            return None;
        }
        if statements
            .get(&current)
            .is_some_and(|stmt| !is_semantic_skip(stmt))
        {
            return Some(current);
        }
        match successors.get(&current).map(Vec::as_slice) {
            Some([next]) => current = *next,
            _ => return None,
        }
    }
}

#[derive(Debug)]
enum SelectedOutsideTarget {
    NoGoto,
    Unique {
        raw_targets: HashSet<Node>,
        resolved_target: Node,
    },
    Ambiguous,
}

/// Recover the outside arm from the statement that the solver actually
/// selected for a loop-exit node.  Candidate-level loop metadata can name a
/// transparent branch shim that another selected candidate bypasses.  The
/// selected statement is authoritative for the expression and its immediate
/// targets; loop membership plus unique CFG forwarding establishes which arm
/// leaves the loop.
///
/// This intentionally visits only statement forms that `replace_exact_gotos`
/// can rewrite.  A goto inside an already assembled nested loop or switch is
/// owned by that construct and must not become an exit of the enclosing loop.
fn selected_unique_outside_target(
    stmt: &ClightStmt,
    statements: &HashMap<Node, ClightStmt>,
    successors: &HashMap<Node, Vec<Node>>,
    body_node_set: &HashSet<Node>,
) -> SelectedOutsideTarget {
    fn collect(stmt: &ClightStmt, targets: &mut HashSet<Node>) {
        match stmt {
            ClightStmt::Sgoto(target) => {
                targets.insert(*target as Node);
            }
            ClightStmt::Sifthenelse(_, then_stmt, else_stmt) => {
                collect(then_stmt, targets);
                collect(else_stmt, targets);
            }
            ClightStmt::Ssequence(stmts) => {
                for stmt in stmts {
                    collect(stmt, targets);
                }
            }
            (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => collect(inner, targets),
            _ => {}
        }
    }

    let mut goto_targets = HashSet::new();
    collect(stmt, &mut goto_targets);
    if goto_targets.is_empty() {
        return SelectedOutsideTarget::NoGoto;
    }

    let mut by_resolved: HashMap<Node, HashSet<Node>> = HashMap::new();
    for raw_target in goto_targets {
        if let Some(resolved_target) =
            resolve_live_outside_target(raw_target, statements, successors, body_node_set)
        {
            by_resolved
                .entry(resolved_target)
                .or_default()
                .insert(raw_target);
        }
    }
    if by_resolved.len() != 1 {
        return SelectedOutsideTarget::Ambiguous;
    }
    let (resolved_target, raw_targets) = by_resolved.into_iter().next().unwrap();
    SelectedOutsideTarget::Unique {
        raw_targets,
        resolved_target,
    }
}

fn forwarding_goto_target(stmt: &ClightStmt) -> Option<Node> {
    match stmt {
        ClightStmt::Sgoto(target) => Some(*target as Node),
        ClightStmt::Slabel(_, inner) => forwarding_goto_target(inner),
        _ => None,
    }
}

fn single_temp_assignment(stmt: &ClightStmt) -> Option<Ident> {
    match stmt {
        ClightStmt::Sset(dst, _) => Some(*dst),
        ClightStmt::Slabel(_, inner) => single_temp_assignment(inner),
        _ => None,
    }
}

fn temp_assignment_before_forwarding_goto(stmt: &ClightStmt) -> Option<(Ident, Node)> {
    match stmt {
        ClightStmt::Slabel(_, inner) => temp_assignment_before_forwarding_goto(inner),
        ClightStmt::Ssequence(items) => {
            let mut semantic = items.iter().filter(|item| !is_semantic_skip(item)).rev();
            let target = semantic.next().and_then(forwarding_goto_target)?;
            let dst = semantic.next().and_then(single_temp_assignment)?;
            Some((dst, target))
        }
        _ => None,
    }
}

fn append_exact_return(stmt: &ClightStmt, return_expr: &ClightExpr) -> Option<ClightStmt> {
    match stmt {
        ClightStmt::Sset(_, _) => Some(ClightStmt::Ssequence(vec![
            stmt.clone(),
            ClightStmt::Sreturn(Some(return_expr.clone())),
        ])),
        ClightStmt::Slabel(label, inner) => append_exact_return(inner, return_expr)
            .map(|rewritten| ClightStmt::Slabel(*label, Box::new(rewritten))),
        _ => None,
    }
}

fn replace_terminal_forwarding_goto_with_return(
    stmt: &ClightStmt,
    target: Node,
    return_expr: &ClightExpr,
) -> Option<ClightStmt> {
    match stmt {
        ClightStmt::Sgoto(goto_target) if *goto_target as Node == target => {
            Some(ClightStmt::Sreturn(Some(return_expr.clone())))
        }
        ClightStmt::Slabel(label, inner) => {
            replace_terminal_forwarding_goto_with_return(inner, target, return_expr)
                .map(|rewritten| ClightStmt::Slabel(*label, Box::new(rewritten)))
        }
        ClightStmt::Ssequence(items) => {
            let index = items.iter().rposition(|item| !is_semantic_skip(item))?;
            let replacement =
                replace_terminal_forwarding_goto_with_return(&items[index], target, return_expr)?;
            let mut rewritten = items.clone();
            rewritten[index] = replacement;
            Some(ClightStmt::Ssequence(rewritten))
        }
        _ => None,
    }
}

fn resolve_exact_temp_return(
    start: Node,
    dst: Ident,
    statements: &HashMap<Node, ClightStmt>,
    successors: &HashMap<Node, Vec<Node>>,
) -> Option<ClightExpr> {
    let mut current = start;
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(current) {
            return None;
        }
        match statements.get(&current) {
            Some(stmt) if is_semantic_skip(stmt) => {}
            Some(stmt) => {
                match strip_outer_labels(stmt) {
                    ClightStmt::Sreturn(Some(ClightExpr::Etempvar(ret, ty))) if ret == dst => {
                        return Some(ClightExpr::Etempvar(ret, ty));
                    }
                    _ => {}
                }
                let goto_target = forwarding_goto_target(stmt)?;
                match successors.get(&current).map(Vec::as_slice) {
                    Some([next]) if *next == goto_target => {
                        current = goto_target;
                        continue;
                    }
                    _ => return None,
                }
            }
            None => {}
        }
        match successors.get(&current).map(Vec::as_slice) {
            Some([next]) => current = *next,
            _ => return None,
        }
    }
}

/// Duplicate a common straight-line return tail into the assignment that
/// feeds it.  This reverses the compiler's shared-epilogue lowering without
/// guessing at source layout: every intermediate node must be absent/Sskip or
/// a pure forwarding goto that agrees with its sole CFG successor, and the
/// terminal return must read exactly the assigned temporary.  Keeping the
/// assignment before the duplicated return preserves its C conversion.
fn duplicate_straight_line_return_tails(
    statements: &mut HashMap<Node, ClightStmt>,
    successors: &HashMap<Node, Vec<Node>>,
) {
    let mut nodes: Vec<Node> = statements.keys().copied().collect();
    nodes.sort_unstable();
    enum ReturnRewrite {
        Append(Node, ClightExpr),
        ReplaceGoto(Node, Node, ClightExpr),
    }
    let mut rewrites = Vec::new();

    for node in nodes {
        let Some(stmt) = statements.get(&node) else {
            continue;
        };
        if let Some(dst) = single_temp_assignment(stmt) {
            if let Some([first]) = successors.get(&node).map(Vec::as_slice) {
                if let Some(return_expr) =
                    resolve_exact_temp_return(*first, dst, statements, successors)
                {
                    rewrites.push(ReturnRewrite::Append(node, return_expr));
                    continue;
                }
            }
        }
        if let Some((dst, target)) = temp_assignment_before_forwarding_goto(stmt) {
            if let Some(return_expr) =
                resolve_exact_temp_return(target, dst, statements, successors)
            {
                rewrites.push(ReturnRewrite::ReplaceGoto(node, target, return_expr));
            }
        }
    }

    for rewrite in rewrites {
        match rewrite {
            ReturnRewrite::Append(node, return_expr) => {
                if let Some(original) = statements.get(&node).cloned() {
                    if let Some(rewritten) = append_exact_return(&original, &return_expr) {
                        statements.insert(node, rewritten);
                    }
                }
            }
            ReturnRewrite::ReplaceGoto(node, target, return_expr) => {
                if let Some(original) = statements.get(&node).cloned() {
                    if let Some(rewritten) = replace_terminal_forwarding_goto_with_return(
                        &original,
                        target,
                        &return_expr,
                    ) {
                        statements.insert(node, rewritten);
                    }
                }
            }
        }
    }
}

/// Resolve through selected-away nodes and pure forwarding gotos to the next
/// semantic effect.  The explicit goto must agree with the sole CFG successor;
/// otherwise the path is ambiguous and cannot establish exit equivalence.
fn resolve_effective_outside_target(
    target: Node,
    statements: &HashMap<Node, ClightStmt>,
    successors: &HashMap<Node, Vec<Node>>,
    body_node_set: &HashSet<Node>,
) -> Option<Node> {
    let mut current = target;
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(current) || body_node_set.contains(&current) {
            return None;
        }
        match statements.get(&current) {
            Some(stmt) if is_semantic_skip(stmt) => {}
            Some(stmt) => {
                let Some(goto_target) = forwarding_goto_target(stmt) else {
                    return Some(current);
                };
                match successors.get(&current).map(Vec::as_slice) {
                    Some([next]) if *next == goto_target => {
                        current = goto_target;
                        continue;
                    }
                    _ => return None,
                }
            }
            None => {}
        }
        match successors.get(&current).map(Vec::as_slice) {
            Some([next]) => current = *next,
            _ => return None,
        }
    }
}

/// A control-transfer target can be a Clight-selected-away instruction (for
/// example, a targeted machine no-op whose only purpose was to carry the CFG
/// edge).  Retarget exact gotos only when that transparent CFG chain has one
/// surviving frontier.  Ambiguous paths and cycles retain the original target.
fn redirect_gotos_through_selected_away_nodes(
    statements: &mut HashMap<Node, ClightStmt>,
    successors: &HashMap<Node, Vec<Node>>,
) {
    let empty_body = HashSet::new();
    let mut targets: Vec<Node> = function_goto_targets(statements).into_iter().collect();
    targets.sort_unstable();
    let mut redirect_map = HashMap::new();
    for target in targets {
        if let Some(live) = resolve_live_outside_target(target, statements, successors, &empty_body)
        {
            if live != target {
                redirect_map.insert(target, live);
            }
        }
    }
    if redirect_map.is_empty() {
        return;
    }

    let mut owners: Vec<Node> = statements.keys().copied().collect();
    owners.sort_unstable();
    for owner in owners {
        if let Some(stmt) = statements.get(&owner).cloned() {
            statements.insert(owner, redirect_gotos_in_stmt(&stmt, &redirect_map));
        }
    }
}

fn ensure_node_label(statements: &mut HashMap<Node, ClightStmt>, node: Node) {
    let label = ident_from_node(node);
    if let Some(stmt) = statements.get(&node).cloned() {
        if !matches!(&stmt, ClightStmt::Slabel(existing, _) if *existing == label) {
            statements.insert(node, ClightStmt::Slabel(label, Box::new(stmt)));
        }
    }
}

/// A distinct outside target may share the primary loop exit only when its
/// selected effect is identical, both targets flow through a unique CFG path
/// to the same next live statement, and the alternate target belongs solely
/// to this exit.  Exact Clight equality after label removal is deliberately
/// stronger than semantic equality; uncertainty keeps the original goto.
fn can_share_primary_exit_target(
    alternate: Node,
    primary: Node,
    statements: &HashMap<Node, ClightStmt>,
    successors: &HashMap<Node, Vec<Node>>,
    body_node_set: &HashSet<Node>,
    pred_counts: &HashMap<Node, usize>,
) -> bool {
    if alternate == primary || pred_counts.get(&alternate).copied() != Some(1) {
        return false;
    }
    let Some(alternate_stmt) = statements.get(&alternate) else {
        return false;
    };
    let Some(primary_stmt) = statements.get(&primary) else {
        return false;
    };
    if strip_outer_labels(alternate_stmt) != strip_outer_labels(primary_stmt) {
        return false;
    }

    let resolve_successor = |node: Node| -> Option<Node> {
        match successors.get(&node).map(Vec::as_slice) {
            Some([next]) => {
                resolve_effective_outside_target(*next, statements, successors, body_node_set)
            }
            _ => None,
        }
    };
    match (resolve_successor(alternate), resolve_successor(primary)) {
        (Some(alternate_next), Some(primary_next)) => alternate_next == primary_next,
        _ => false,
    }
}

fn assemble_loops(
    statements: &mut HashMap<Node, ClightStmt>,
    loop_info: &HashMap<Node, LoopInfo>,
    successors: &HashMap<Node, Vec<Node>>,
) {
    // Process smallest loops first (inner before outer). Break ties by header address.
    let mut headers: Vec<(&Node, &LoopInfo)> = loop_info.iter().collect();
    headers.sort_by(|a, b| {
        a.1.body_nodes
            .len()
            .cmp(&b.1.body_nodes.len())
            .then(a.0.cmp(b.0))
    });

    // Top-level value nodes tail-duplicated into a loop exit branch, removed here so they are not also hoisted outside; only single-predecessor nodes, since a shared return still has another path.
    let mut absorbed_value_nodes: Vec<Node> = Vec::new();
    // Return nodes orphaned when their sole feeding value node was absorbed; left in place a loop break can fall THROUGH them and emit the wrong early-exit value. Pruned structurally, never by address.
    let mut dup_ret_nodes: Vec<Node> = Vec::new();
    let pred_counts = count_predecessors(successors);

    for (&header, info) in &headers {
        let header_label = ident_from_node(header);
        // Body iteration follows execution order: synthetic addresses execute immediately after their base, so a naive numeric sort would emit the synth Sset at the bottom and break RMW order.
        let mut body_iter_nodes: Vec<Node> = info.body_nodes.iter().copied().collect();
        if !body_iter_nodes.contains(&header) {
            body_iter_nodes.push(header);
        }
        body_iter_nodes.sort_by_key(|&n| crate::util::exec_order_key(n));
        // Rotate so the HEADER is the first emitted element, since Scontinue and the implicit loop-back re-enter at the body's FIRST statement; dominance guarantees every entry passes the header.
        if let Some(pos) = body_iter_nodes.iter().position(|&n| n == header) {
            body_iter_nodes.rotate_left(pos);
        }
        let body_node_set: HashSet<Node> = body_iter_nodes.iter().copied().collect();

        // A `continue` re-enters at the FIRST emitted body element, which the
        // rotation above makes the header, so the frontier is the header read
        // through whatever selection deleted.  The primary exit's in-loop arm
        // is only the frontier when that walk cannot run at all -- a header
        // selected away while still branching -- because for a pre-tested loop
        // that arm is the SECOND emitted element, and binding continue to it
        // skips the header test and spins on an unchanged condition.
        let header_continue_frontier =
            resolve_live_inside_target(header, statements, successors, &body_node_set);
        let primary_continue_frontier = info.primary_exit.as_ref().and_then(|primary| {
            let stmt = statements.get(&primary.exit_node)?;
            let mut targets: Vec<Node> = collect_goto_targets(stmt)
                .into_iter()
                .filter(|target| body_node_set.contains(target))
                .collect();
            targets.sort_unstable();
            targets.dedup();
            (targets.len() == 1).then(|| targets[0])
        });
        let body_top_label: Option<Ident> = header_continue_frontier
            .or(primary_continue_frontier)
            .map(ident_from_node);

        // Resolve every outside edge before mutating this loop.  If an exact
        // target was selected away, walk only its unique CFG successor chain;
        // otherwise keep the original flat control flow rather than guessing.
        let primary_metadata_target = info.primary_exit.as_ref().and_then(|pe| pe.exit_target);
        let mut primary_exit_labels: HashSet<Ident> = HashSet::new();
        let primary_exit_target: Option<Node> = match primary_metadata_target {
            Some(metadata_target) => {
                let selected_target = info
                    .primary_exit
                    .as_ref()
                    .and_then(|primary| statements.get(&primary.exit_node))
                    .map(|stmt| {
                        selected_unique_outside_target(stmt, statements, successors, &body_node_set)
                    })
                    .unwrap_or(SelectedOutsideTarget::NoGoto);
                match selected_target {
                    SelectedOutsideTarget::Unique {
                        raw_targets,
                        resolved_target,
                    } => {
                        primary_exit_labels.extend(raw_targets.into_iter().map(ident_from_node));
                        primary_exit_labels.insert(ident_from_node(resolved_target));
                        Some(resolved_target)
                    }
                    SelectedOutsideTarget::NoGoto => {
                        match resolve_live_outside_target(
                            metadata_target,
                            statements,
                            successors,
                            &body_node_set,
                        ) {
                            Some(live) => {
                                primary_exit_labels.insert(ident_from_node(metadata_target));
                                primary_exit_labels.insert(ident_from_node(live));
                                Some(live)
                            }
                            None => {
                                if std::env::var("LOOP_ASSEMBLY_TRACE").is_ok() {
                                    eprintln!(
                                        "[loop-assembly] skip header={header:#x}: primary target {metadata_target:#x} has no unique live outside frontier"
                                    );
                                }
                                continue;
                            }
                        }
                    }
                    SelectedOutsideTarget::Ambiguous => {
                        if std::env::var("LOOP_ASSEMBLY_TRACE").is_ok() {
                            eprintln!(
                                "[loop-assembly] skip header={header:#x}: selected primary exit has no unique outside arm"
                            );
                        }
                        continue;
                    }
                }
            }
            None => None,
        };
        // exit node -> (resolved outside target, all selected labels that
        // denote that same edge and are safe to rewrite).
        let mut resolved_break_targets: HashMap<Node, (Node, HashSet<Ident>)> = HashMap::new();
        let mut unresolved_break_target = false;
        for (&exit_node, &metadata_target) in &info.exit_targets {
            let selected_target = statements
                .get(&exit_node)
                .map(|stmt| {
                    selected_unique_outside_target(stmt, statements, successors, &body_node_set)
                })
                .unwrap_or(SelectedOutsideTarget::NoGoto);
            match selected_target {
                SelectedOutsideTarget::Unique {
                    raw_targets,
                    resolved_target,
                } => {
                    let mut labels: HashSet<Ident> =
                        raw_targets.into_iter().map(ident_from_node).collect();
                    labels.insert(ident_from_node(resolved_target));
                    resolved_break_targets.insert(exit_node, (resolved_target, labels));
                }
                SelectedOutsideTarget::NoGoto => {
                    match resolve_live_outside_target(
                        metadata_target,
                        statements,
                        successors,
                        &body_node_set,
                    ) {
                        Some(live) => {
                            resolved_break_targets.insert(
                                exit_node,
                                (
                                    live,
                                    HashSet::from([
                                        ident_from_node(metadata_target),
                                        ident_from_node(live),
                                    ]),
                                ),
                            );
                        }
                        None => {
                            unresolved_break_target = true;
                            break;
                        }
                    }
                }
                SelectedOutsideTarget::Ambiguous => {
                    unresolved_break_target = true;
                    break;
                }
            }
        }
        if unresolved_break_target {
            if std::env::var("LOOP_ASSEMBLY_TRACE").is_ok() {
                eprintln!(
                    "[loop-assembly] skip header={header:#x}: a non-primary exit has no unique live outside frontier"
                );
            }
            continue;
        }
        if let Some(target) = primary_exit_target {
            ensure_node_label(statements, target);
        }
        for (target, _) in resolved_break_targets.values() {
            ensure_node_label(statements, *target);
        }

        // A primary exit may use `break` for readability, but only together
        // with an explicit post-loop goto to its structurally-derived target.
        // Every other outside edge remains a goto in the loop body so distinct
        // exits cannot collapse onto whichever top-level node PR orders next.
        let shared_primary_breaks: HashSet<Node> = primary_exit_target
            .map(|primary| {
                resolved_break_targets
                    .iter()
                    .filter_map(|(&exit_node, (alternate, _))| {
                        (*alternate == primary
                            || can_share_primary_exit_target(
                                *alternate,
                                primary,
                                statements,
                                successors,
                                &body_node_set,
                                &pred_counts,
                            ))
                        .then_some(exit_node)
                    })
                    .collect()
            })
            .unwrap_or_default();

        // Function-wide, not body-local: an earlier loop or branch may jump
        // into a member this assembler is about to absorb.
        let goto_targets = function_goto_targets(statements);

        let mut body_stmts: Vec<ClightStmt> = Vec::new();
        // Originating node of each body statement, index-aligned with body_stmts (the CF-4 guard resolves goto targets to body positions through it).
        let mut body_stmt_nodes: Vec<Node> = Vec::new();
        // A5 absorptions commit only if the loop itself commits (CF-4 guard below); pushing straight to absorbed_value_nodes would delete the value node even when the Sloop is skipped.
        let mut loop_absorbed: Vec<Node> = Vec::new();
        // Return nodes duplicated into this loop's exit branches whose value node is being absorbed (same commit gating as loop_absorbed).
        let mut loop_dup_rets: Vec<Node> = Vec::new();

        let mut selected_exit_missing = false;
        for &node in &body_iter_nodes {
            let mut stmt = match statements.get(&node) {
                Some(s) => s.clone(),
                None => continue,
            };

            // Preserve the condition/type/copy-propagation decisions made by
            // clight_select.  Loop metadata contributes only the exact CFG
            // edge to rewrite; it must never replace the selected guard with
            // a separately materialized candidate expression.
            if let Some(&raw_target) = info.exit_targets.get(&node) {
                let (resolved_target, target_labels) = resolved_break_targets
                    .get(&node)
                    .expect("all exit targets resolved before loop assembly");

                let mut replacement = ClightStmt::Sgoto(ident_from_node(*resolved_target));
                let mut absorbed_return: Option<(Node, Node)> = None;
                if let Some(&(value_node, ret_node)) = info.exit_returns.get(&node) {
                    if let Some(tail) = build_return_tail(statements, value_node, ret_node) {
                        replacement = tail;
                        absorbed_return = Some((value_node, ret_node));
                    }
                }
                if absorbed_return.is_none() && shared_primary_breaks.contains(&node) {
                    replacement = ClightStmt::Sbreak;
                }

                let (rewritten, replacements) =
                    replace_exact_gotos(&stmt, target_labels, &replacement);
                if replacements == 0 {
                    // Selection removed or fundamentally changed the branch;
                    // without its chosen guard there is no sound loop rewrite.
                    if std::env::var("LOOP_ASSEMBLY_TRACE").is_ok() {
                        eprintln!(
                            "[loop-assembly] skip header={header:#x}: selected exit {node:#x} has no goto for metadata target {raw_target:#x} or resolved target {resolved_target:#x}; stmt={stmt:#?}"
                        );
                    }
                    selected_exit_missing = true;
                    break;
                }
                stmt = rewritten;

                if let Some((value_node, ret_node)) = absorbed_return {
                    if pred_counts.get(&value_node).copied().unwrap_or(0) <= 1 {
                        loop_absorbed.push(value_node);
                        if value_node != ret_node {
                            loop_dup_rets.push(ret_node);
                        }
                    }
                } else if shared_primary_breaks.contains(&node) {
                    if Some(*resolved_target) != primary_exit_target {
                        loop_absorbed.push(*resolved_target);
                    }
                }
            }

            // Convert true back-edges to continue.  Only the unique primary
            // exit may become break; all other outside-loop gotos keep their
            // exact targets.
            let mut converted =
                convert_loop_gotos(&stmt, header_label, body_top_label, &primary_exit_labels);
            // The PRIMARY exit also flows to a return when the loop has 2+ distinct return-exits, so tail-duplicate its own return in place of its break or its value collapses onto the other exit's.
            if info.primary_exit.as_ref().map(|pe| pe.exit_node) == Some(node) {
                if let Some(&(value_node, ret_node)) = info.exit_returns.get(&node) {
                    if let Some(tail) = build_return_tail(statements, value_node, ret_node) {
                        converted = replace_break_with(&converted, &tail);
                        if pred_counts.get(&value_node).copied().unwrap_or(0) <= 1 {
                            loop_absorbed.push(value_node);
                            if value_node != ret_node {
                                loop_dup_rets.push(ret_node);
                            }
                        }
                    }
                }
            }
            // Check nonempty: peel through Slabel wrappers to see if innermost is Sskip.
            let mut s = &converted;
            let mut outer_label: Option<Ident> = None;
            while let ClightStmt::Slabel(lbl, inner) = s {
                if outer_label.is_none() {
                    outer_label = Some(*lbl);
                }
                s = inner;
            }
            let is_skip = matches!(s, ClightStmt::Sskip);
            // Preserve label-only Sskip when another body stmt gotos this label; otherwise the label is needed for control flow inside the loop, but the body would emit it outside via ensure_goto_labels.
            let target_within_body = outer_label
                .map(|lbl| node != header && goto_targets.contains(&(lbl as Node)))
                .unwrap_or(false);
            if !is_skip || target_within_body {
                if is_skip {
                    body_stmts.push(converted);
                } else {
                    // Strip one outer label so the body falls through via the parent Ssequence, unless an in-body goto targets it: ensure_goto_labels would re-create it OUTSIDE the loop and the body would be dropped.
                    let stripped = match converted {
                        ClightStmt::Slabel(lbl, inner)
                            if node == header || !goto_targets.contains(&(lbl as Node)) =>
                        {
                            *inner
                        }
                        other => other,
                    };
                    body_stmts.push(stripped);
                }
                body_stmt_nodes.push(node);
                // Upstream trimming deletes a body node's jmp header assuming POSITION supplies the loop-back, true only for the exec-LAST node, so materialize Scontinue for any other such node.
                if let Some(succs) = successors.get(&node) {
                    if succs.len() == 1
                        && succs[0] == header
                        && body_stmts
                            .last()
                            .map(stmt_may_fall_through)
                            .unwrap_or(false)
                    {
                        body_stmts.push(ClightStmt::Scontinue);
                        body_stmt_nodes.push(node);
                    }
                }
            }
        }

        if selected_exit_missing {
            continue;
        }

        // Remove trailing Scontinue (redundant at end of loop body)
        while body_stmts.last() == Some(&ClightStmt::Scontinue) {
            body_stmts.pop();
            body_stmt_nodes.pop();
        }

        // CF-4 guard: a loop must be re-enterable, so if the assembled body has no continue and cannot fall off its end, skip assembly rather than wrap a non-loop in while(1) and trap interior back-edges.
        if !loop_body_can_reenter(
            &body_stmts,
            &body_stmt_nodes,
            &body_node_set,
            header,
            body_iter_nodes.first().copied(),
        ) {
            if std::env::var("CF4_TRACE").is_ok() {
                eprintln!(
                    "[cf4] skip header={:#x} label={} body={:#?}",
                    header, header_label, body_stmts
                );
            }
            continue;
        }
        absorbed_value_nodes.extend(loop_absorbed);
        dup_ret_nodes.extend(loop_dup_rets);

        let body = match body_stmts.len() {
            0 => ClightStmt::Sskip,
            1 => body_stmts.into_iter().next().unwrap(),
            _ => ClightStmt::Ssequence(flatten_sequence(body_stmts)),
        };

        let loop_stmt = ClightStmt::Sloop(Box::new(body), Box::new(ClightStmt::Sskip));

        // Append an explicit goto to the exit target so a break reaches it regardless of DFS layout; simplify_fallthrough_gotos drops it when the exit is already next.
        let loop_stmt = match primary_exit_target {
            Some(target) => {
                ClightStmt::Ssequence(vec![loop_stmt, ClightStmt::Sgoto(ident_from_node(target))])
            }
            None => loop_stmt,
        };

        // Preserve label on the header node if present
        let final_stmt = match statements.get(&header) {
            Some(ClightStmt::Slabel(lbl, _)) => ClightStmt::Slabel(*lbl, Box::new(loop_stmt)),
            _ => loop_stmt,
        };

        statements.insert(header, final_stmt);

        // Remove body nodes from top-level
        for &node in &info.body_nodes {
            if node != header {
                statements.remove(&node);
            }
        }
    }

    // Drop value nodes absorbed by an A5 tail-duplication so they are not also emitted outside the loop.
    for node in absorbed_value_nodes {
        statements.remove(&node);
    }

    // Prune return nodes orphaned by the tail-duplication above when no goto and no top-level CFG predecessor still reaches them; judged structurally, never by address ordering.
    if !dup_ret_nodes.is_empty() {
        // Goto targets referenced anywhere in the surviving statements (recurses into nested loop/if/switch bodies).
        let mut goto_targets: HashSet<Node> = HashSet::new();
        for stmt in statements.values() {
            for t in collect_goto_targets(stmt) {
                goto_targets.insert(t);
            }
        }
        let mut seen: HashSet<Node> = HashSet::new();
        for ret_node in dup_ret_nodes {
            if !seen.insert(ret_node) {
                continue;
            }
            if !statements.contains_key(&ret_node) {
                continue;
            }
            if goto_targets.contains(&ret_node) {
                continue;
            }
            // A live CFG predecessor is any surviving top-level node (other than ret_node itself) whose successor set includes ret_node.
            let pred_alive = successors.iter().any(|(p, succs)| {
                *p != ret_node && statements.contains_key(p) && succs.contains(&ret_node)
            });
            if pred_alive {
                continue;
            }
            statements.remove(&ret_node);
        }
    }
}

// Build the tail-duplicated return for an A5 loop exit: the value assignment at value_node then the return at ret_node, each node's label stripped (originals stay labeled until the absorbed value node is removed; ret_node may be shared, so it is duplicated, not moved).
fn build_return_tail(
    statements: &HashMap<Node, ClightStmt>,
    value_node: Node,
    ret_node: Node,
) -> Option<ClightStmt> {
    let val = strip_outer_labels(statements.get(&value_node)?);
    if value_node == ret_node {
        Some(val)
    } else {
        let ret = strip_outer_labels(statements.get(&ret_node)?);
        Some(ClightStmt::Ssequence(vec![val, ret]))
    }
}

// Peel any leading Slabel wrappers off a statement so a duplicated copy carries no duplicate label.
fn strip_outer_labels(s: &ClightStmt) -> ClightStmt {
    match s {
        ClightStmt::Slabel(_, inner) => strip_outer_labels(inner),
        other => other.clone(),
    }
}

/// Replace gotos to one structurally identified CFG exit while preserving the
/// selected statement's expressions.  Do not descend into an already
/// assembled loop or switch: `break` would bind to that nested construct, not
/// to the loop currently being assembled.
fn replace_exact_gotos(
    stmt: &ClightStmt,
    targets: &HashSet<Ident>,
    replacement: &ClightStmt,
) -> (ClightStmt, usize) {
    match stmt {
        ClightStmt::Sgoto(target) if targets.contains(target) => (replacement.clone(), 1),
        ClightStmt::Sifthenelse(cond, then_stmt, else_stmt) => {
            let (then_stmt, then_count) = replace_exact_gotos(then_stmt, targets, replacement);
            let (else_stmt, else_count) = replace_exact_gotos(else_stmt, targets, replacement);
            (
                ClightStmt::Sifthenelse(cond.clone(), Box::new(then_stmt), Box::new(else_stmt)),
                then_count + else_count,
            )
        }
        ClightStmt::Ssequence(stmts) => {
            let mut count = 0;
            let rewritten = stmts
                .iter()
                .map(|stmt| {
                    let (stmt, replacements) = replace_exact_gotos(stmt, targets, replacement);
                    count += replacements;
                    stmt
                })
                .collect();
            (ClightStmt::Ssequence(rewritten), count)
        }
        ClightStmt::Slabel(label, inner) => {
            let (inner, count) = replace_exact_gotos(inner, targets, replacement);
            (ClightStmt::Slabel(*label, Box::new(inner)), count)
        }
        _ => (stmt.clone(), 0),
    }
}

// Replace every Sbreak in a selected primary-exit statement with the given
// tail, turning `if (cond) break` into `if (cond) { value; return }`.
fn replace_break_with(stmt: &ClightStmt, tail: &ClightStmt) -> ClightStmt {
    match stmt {
        ClightStmt::Sbreak => tail.clone(),
        ClightStmt::Sifthenelse(c, t, e) => ClightStmt::Sifthenelse(
            c.clone(),
            Box::new(replace_break_with(t, tail)),
            Box::new(replace_break_with(e, tail)),
        ),
        ClightStmt::Ssequence(ss) => {
            ClightStmt::Ssequence(ss.iter().map(|s| replace_break_with(s, tail)).collect())
        }
        ClightStmt::Slabel(l, inner) => {
            ClightStmt::Slabel(*l, Box::new(replace_break_with(inner, tail)))
        }
        other => other.clone(),
    }
}

// Assemble compound if-then-else from structural metadata (analogous to assemble_loops); operates on already-typed ClightStmt so no type decisions are made. Count ClightStmt tree nodes; bounds assemble_ite against pathological overlapping if-bodies.
fn clight_stmt_size(s: &ClightStmt) -> usize {
    match s {
        ClightStmt::Ssequence(v) => 1 + v.iter().map(clight_stmt_size).sum::<usize>(),
        ClightStmt::Sifthenelse(_, a, b) => 1 + clight_stmt_size(a) + clight_stmt_size(b),
        ClightStmt::Sloop(a, b) => 1 + clight_stmt_size(a) + clight_stmt_size(b),
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => 1 + clight_stmt_size(inner),
        ClightStmt::Sswitch(_, cases) => {
            1 + cases
                .iter()
                .map(|(_, c)| clight_stmt_size(c))
                .sum::<usize>()
        }
        _ => 1,
    }
}

/// Order an ITE arm from its structural entry over function CFG edges.  Arm
/// membership is a set; its stored vector order must never be interpreted as
/// execution order (synthetic nodes deliberately have high tag bits).
///
/// A preorder DFS is insufficient here.  In a converging acyclic arm, the
/// branch can target both a shared body and an out-of-line guard which itself
/// reaches that body.  Visiting the body first relocates the guard after the
/// body's formerly implicit exit fallthrough and changes that fallthrough into
/// an accidental trip through the guard.  Topological order preserves every
/// intra-arm predecessor constraint.  Numeric sorting is used only as a
/// deterministic tie-break between structurally ready roots/components, never
/// to derive reachability.
fn order_ite_arm_nodes(
    body_nodes: &[Node],
    entry: Option<Node>,
    successors: &HashMap<Node, Vec<Node>>,
) -> Vec<Node> {
    let body_set: HashSet<Node> = body_nodes.iter().copied().collect();
    if body_set.len() <= 1 {
        return body_nodes.to_vec();
    }

    let mut indegree: HashMap<Node, usize> =
        body_set.iter().copied().map(|node| (node, 0)).collect();
    for &node in &body_set {
        if let Some(succs) = successors.get(&node) {
            let mut unique_succs: Vec<Node> = succs
                .iter()
                .copied()
                .filter(|succ| body_set.contains(succ))
                .collect();
            unique_succs.sort_unstable();
            unique_succs.dedup();
            for succ in unique_succs {
                if body_set.contains(&succ) {
                    *indegree.get_mut(&succ).expect("arm successor is a member") += 1;
                }
            }
        }
    }

    let mut ready: Vec<Node> = body_set
        .iter()
        .copied()
        .filter(|node| indegree[node] == 0)
        .collect();
    ready.sort_unstable_by_key(|node| std::cmp::Reverse((Some(*node) != entry, *node)));

    let mut ordered = Vec::with_capacity(body_set.len());
    let mut visited = HashSet::new();
    while !ready.is_empty() {
        let node = ready.pop().expect("ready arm node");
        if !visited.insert(node) {
            continue;
        }
        ordered.push(node);
        let mut nexts: Vec<Node> = successors
            .get(&node)
            .into_iter()
            .flatten()
            .copied()
            .filter(|next| body_set.contains(next))
            .collect();
        nexts.sort_unstable();
        nexts.dedup();
        for next in nexts {
            let degree = indegree.get_mut(&next).expect("arm successor is a member");
            *degree -= 1;
            if *degree == 0 {
                ready.push(next);
            }
        }
        ready.sort_unstable_by_key(|candidate| {
            std::cmp::Reverse((Some(*candidate) != entry, *candidate))
        });
        ready.dedup();
    }

    // Loop bodies normally never enter ITE membership, but malformed or
    // irreducible input can leave a cyclic component.  Keep its ordering
    // structural by walking CFG edges from a deterministic seed rather than
    // pretending node magnitude proves an execution order.
    let mut seeds: Vec<Node> = body_set
        .iter()
        .copied()
        .filter(|node| !visited.contains(node))
        .collect();
    seeds.sort_unstable_by_key(|node| (Some(*node) != entry, *node));
    for seed in seeds {
        let mut stack = vec![seed];
        while let Some(node) = stack.pop() {
            if !body_set.contains(&node) || !visited.insert(node) {
                continue;
            }
            ordered.push(node);
            let mut nexts: Vec<Node> = successors
                .get(&node)
                .into_iter()
                .flatten()
                .copied()
                .filter(|next| body_set.contains(next) && !visited.contains(next))
                .collect();
            nexts.sort_unstable();
            nexts.dedup();
            for next in nexts.into_iter().rev() {
                stack.push(next);
            }
        }
    }
    ordered
}

fn assemble_ite(
    statements: &mut HashMap<Node, ClightStmt>,
    ite_info: &HashMap<Node, IteInfo>,
    successors: &HashMap<Node, Vec<Node>>,
) {
    if ite_info.is_empty() {
        return;
    }

    // Process smallest bodies first (inner before outer) so nested compounds are ready when an outer branch collects them.
    let mut branches: Vec<(&Node, &IteInfo)> = ite_info.iter().collect();
    branches.sort_by(|a, b| {
        let a_size = a.1.true_body_nodes.len() + a.1.false_body_nodes.len();
        let b_size = b.1.true_body_nodes.len() + b.1.false_body_nodes.len();
        a_size.cmp(&b_size).then(b.0.cmp(a.0))
    });

    // Per-branch cap on assembled-compound size to bound 2^depth shared-node duplication; 0 binds observed since CF-1, kept as a backstop with smallest-first for O(cap) construction.
    let node_cap: usize = CONFIG.select.ite_max_nodes;
    for (&branch, info) in &branches {
        // A join-based ITE without one structurally unique immediate
        // post-dominator is unsafe to assemble.  `no_join` branches are the
        // explicit one-arm-exits case and intentionally have no join.
        if !info.no_join && info.join_node.is_none() {
            continue;
        }
        // Branch holds Sifthenelse from clight_pass flat Scond rule, possibly wrapped in Slabel.
        let unwrapped = match statements.get(&branch) {
            Some(ClightStmt::Slabel(_, inner)) => inner.as_ref(),
            Some(other) => other,
            None => continue,
        };
        let (cond, then_target, else_target) = match unwrapped {
            ClightStmt::Sifthenelse(c, t, e) => (c.clone(), t.clone(), e.clone()),
            _ => continue,
        };
        let branch_arm_entry = |stmt: &ClightStmt| match stmt {
            ClightStmt::Sgoto(target) => Some(*target as Node),
            _ => None,
        };
        let true_body_nodes = order_ite_arm_nodes(
            &info.true_body_nodes,
            branch_arm_entry(then_target.as_ref()),
            successors,
        );
        let false_body_nodes = order_ite_arm_nodes(
            &info.false_body_nodes,
            branch_arm_entry(else_target.as_ref()),
            successors,
        );
        // An arm is moved out of the function's flat layout.  Preserve a
        // statement's implicit CFG transfer whenever its unique live
        // successor will not be the next statement in that moved arm.  The
        // join is not exempt: nothing in this pass fixes what the emitter
        // prints after the compound, so "falls out of the arm" is not a
        // spelling of "reaches the join".  Emit the edge; goto_elide drops it
        // last, once the printed layout is settled.  Only adjacency the arm
        // itself controls -- the next materialized member of this same arm --
        // is left implicit here.
        let frontier = live_stmt_frontiers(statements, successors);
        let arm_fallthrough_plans = |body_nodes: &[Node]| -> HashMap<Node, Node> {
            let mut plans = HashMap::new();
            for (index, &source) in body_nodes.iter().enumerate() {
                let Some(stmt) = statements.get(&source) else {
                    continue;
                };
                if !stmt_may_fall_through(stmt) {
                    continue;
                }
                let Some(target) = unique_live_successor(source, &frontier, successors) else {
                    continue;
                };
                let next_materialized = body_nodes[index + 1..].iter().copied().find(|node| {
                    statements
                        .get(node)
                        .is_some_and(|stmt| !matches!(stmt, ClightStmt::Sskip))
                });
                if target != source && next_materialized != Some(target) {
                    plans.insert(source, target);
                }
            }
            plans
        };
        let true_fallthrough_plans = arm_fallthrough_plans(&true_body_nodes);
        let false_fallthrough_plans = arm_fallthrough_plans(&false_body_nodes);

        // Recompute after every inner compound: assembly can introduce an
        // exact goto which the next outer compound must keep targetable.  Add
        // the transfers planned above so a target moved into this compound
        // retains its sole label definition.
        let mut referenced_targets = function_goto_targets(statements);
        referenced_targets.extend(true_fallthrough_plans.values().copied());
        referenced_targets.extend(false_fallthrough_plans.values().copied());

        // A shared node that is either switch-bearing or the target of any
        // surviving goto stays once at top level.  Cloning a targeted label
        // into both arms would emit duplicate C label definitions.
        let mut preserved_nodes: HashSet<Node> = info
            .true_body_nodes
            .iter()
            .filter(|&&n| info.false_body_nodes.contains(&n))
            .filter(|&&n| {
                referenced_targets.contains(&n)
                    || statements
                        .get(&n)
                        .map(stmt_contains_switch)
                        .unwrap_or(false)
            })
            .copied()
            .collect();

        // An arm member with a live CFG predecessor outside that arm is not
        // single-entry and cannot be moved exclusively inside the compound.
        // Keep one top-level definition and make this arm jump to it.  This
        // covers implicit fallthrough predecessors too; goto-label scans alone
        // cannot see those edges after an intermediate statement became Snop.
        for body_nodes in [&info.true_body_nodes, &info.false_body_nodes] {
            let body_set: HashSet<Node> = body_nodes.iter().copied().collect();
            for &node in body_nodes {
                let has_live_external_pred = successors.iter().any(|(pred, succs)| {
                    *pred != branch
                        && !body_set.contains(pred)
                        && statements.contains_key(pred)
                        && succs.contains(&node)
                });
                if has_live_external_pred {
                    preserved_nodes.insert(node);
                }
            }
        }

        // Once an arm enters a preserved multi-entry node, every in-arm node
        // structurally reachable from it must remain top-level as well.  If a
        // downstream node were absorbed into this compound, the external path
        // would reach the preserved definition and then lose its CFG
        // successor (or fall through according to unrelated C layout).
        for body_nodes in [&info.true_body_nodes, &info.false_body_nodes] {
            let body_set: HashSet<Node> = body_nodes.iter().copied().collect();
            let mut worklist: Vec<Node> = preserved_nodes
                .iter()
                .copied()
                .filter(|node| body_set.contains(node))
                .collect();
            let mut visited: HashSet<Node> = worklist.iter().copied().collect();
            while let Some(node) = worklist.pop() {
                for succ in successors.get(&node).into_iter().flatten().copied() {
                    if body_set.contains(&succ) && visited.insert(succ) {
                        preserved_nodes.insert(succ);
                        worklist.push(succ);
                    }
                }
            }
        }

        let collect_body =
            |body_nodes: &[Node], fallthrough_plans: &HashMap<Node, Node>| -> ClightStmt {
                let mut body_stmts: Vec<ClightStmt> = Vec::new();
                for &node in body_nodes {
                    if preserved_nodes.contains(&node) {
                        body_stmts.push(ClightStmt::Sgoto(ident_from_node(node)));
                        continue;
                    }
                    if let Some(stmt) = statements.get(&node) {
                        // The node identity is normally subsumed by the compound,
                        // except when a goto still needs to enter at this exact
                        // point after the node moves into the branch body.
                        let mut stripped = match stmt {
                            ClightStmt::Slabel(lbl, _)
                                if referenced_targets.contains(&(*lbl as Node)) =>
                            {
                                stmt.clone()
                            }
                            ClightStmt::Slabel(_, inner) => (**inner).clone(),
                            other => other.clone(),
                        };
                        if let Some(&target) = fallthrough_plans.get(&node) {
                            append_cfg_goto(&mut stripped, target);
                        }
                        if !matches!(&stripped, ClightStmt::Sskip) {
                            body_stmts.push(stripped);
                        }
                    }
                }
                match body_stmts.len() {
                    0 => ClightStmt::Sskip,
                    1 => body_stmts.into_iter().next().unwrap(),
                    _ => ClightStmt::Ssequence(flatten_sequence(body_stmts)),
                }
            };

        let mut then_body = collect_body(&true_body_nodes, &true_fallthrough_plans);
        let mut else_body = collect_body(&false_body_nodes, &false_fallthrough_plans);

        // A branch side whose listed members contribute no statement still
        // owns its exact CFG edge, and that stays true when the edge goes to
        // the join: this pass does not decide what the emitter prints after
        // the compound.  Gotos through genuinely selected-away nodes were
        // resolved before structural assembly.  At this point a missing
        // target may instead have been moved into an inner compound;
        // following its raw successors would silently retarget the edge away
        // from the label now nested in that compound.
        let resolve_empty_arm = |body: &ClightStmt, original: &ClightStmt| {
            if !is_semantic_skip(body) {
                return body.clone();
            }
            original.clone()
        };
        then_body = resolve_empty_arm(&then_body, then_target.as_ref());
        else_body = resolve_empty_arm(&else_body, else_target.as_ref());

        let compound = ClightStmt::Sifthenelse(cond, Box::new(then_body), Box::new(else_body));
        // Bound 2^depth shared-node duplication: if a branch's assembled compound is absurdly large, leave it flat with its goto edges rather than nest it. Only degenerate structuring trips this.
        let csize = clight_stmt_size(&compound);
        if csize > node_cap {
            eprintln!("[assemble_ite] branch {:x}: compound too large ({} nodes > cap {}); left flat with gotos to avoid 2^depth blowup", branch, csize, node_cap);
            continue;
        }

        let wrapped = match statements.get(&branch) {
            Some(ClightStmt::Slabel(lbl, _)) => ClightStmt::Slabel(*lbl, Box::new(compound)),
            _ => compound,
        };
        statements.insert(branch, wrapped);

        // Remove consumed body nodes from top-level; shared target/switch
        // and externally-entered definitions stay once, while their arms retain
        // exact gotos to them.
        for &node in &info.true_body_nodes {
            if !preserved_nodes.contains(&node) {
                statements.remove(&node);
            }
        }
        for &node in &info.false_body_nodes {
            if !preserved_nodes.contains(&node) {
                statements.remove(&node);
            }
        }
    }
}

// Total Sswitch count in a statement tree (CF3_DUMP diagnostics).
fn count_switches(s: &ClightStmt) -> usize {
    match s {
        ClightStmt::Sswitch(_, cases) => {
            1 + cases
                .iter()
                .map(|(_, cs)| count_switches(cs))
                .sum::<usize>()
        }
        ClightStmt::Ssequence(ss) => ss.iter().map(count_switches).sum(),
        ClightStmt::Sifthenelse(_, a, b) => count_switches(a) + count_switches(b),
        ClightStmt::Sloop(a, b) => count_switches(a) + count_switches(b),
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => count_switches(inner),
        _ => 0,
    }
}

// Whether a statement (sub)tree contains an Sswitch - the CF-1 "heavy dispatch" criterion.
fn stmt_contains_switch(s: &ClightStmt) -> bool {
    match s {
        ClightStmt::Sswitch(..) => true,
        ClightStmt::Ssequence(ss) => ss.iter().any(stmt_contains_switch),
        ClightStmt::Sifthenelse(_, a, b) => stmt_contains_switch(a) || stmt_contains_switch(b),
        ClightStmt::Sloop(a, b) => stmt_contains_switch(a) || stmt_contains_switch(b),
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => stmt_contains_switch(inner),
        _ => false,
    }
}

/// Convert true loop back-edges to `continue`.  A uniquely identified primary
/// exit may become `break` because assemble_loops appends an exact goto after
/// the loop; every other goto keeps its target.
fn convert_loop_gotos(
    stmt: &ClightStmt,
    header_label: Ident,
    body_top_label: Option<Ident>,
    primary_exit_targets: &HashSet<Ident>,
) -> ClightStmt {
    match stmt {
        ClightStmt::Sgoto(target) => {
            if *target == header_label || Some(*target) == body_top_label {
                ClightStmt::Scontinue
            } else if primary_exit_targets.contains(target) {
                ClightStmt::Sbreak
            } else {
                stmt.clone()
            }
        }
        // Continue-conversion descends into switch cases, since continue binds to the enclosing LOOP, but break conversion must not: an Sbreak inside a case would bind to the SWITCH.
        ClightStmt::Sswitch(e, cases) => {
            let new_cases = cases
                .iter()
                .map(|(v, s)| (*v, convert_case_continues(s, header_label, body_top_label)))
                .collect();
            ClightStmt::Sswitch(e.clone(), new_cases)
        }
        ClightStmt::Sifthenelse(cond, then_box, else_box) => {
            let new_then =
                convert_loop_gotos(then_box, header_label, body_top_label, primary_exit_targets);
            let new_else =
                convert_loop_gotos(else_box, header_label, body_top_label, primary_exit_targets);
            ClightStmt::Sifthenelse(cond.clone(), Box::new(new_then), Box::new(new_else))
        }
        ClightStmt::Ssequence(stmts) => {
            let new_stmts: Vec<ClightStmt> = stmts
                .iter()
                .map(|s| convert_loop_gotos(s, header_label, body_top_label, primary_exit_targets))
                .collect();
            ClightStmt::Ssequence(new_stmts)
        }
        ClightStmt::Slabel(lbl, inner) => {
            let new_inner =
                convert_loop_gotos(inner, header_label, body_top_label, primary_exit_targets);
            ClightStmt::Slabel(*lbl, Box::new(new_inner))
        }
        _ => stmt.clone(),
    }
}

// CF-3: inline externalized switch case bodies when every goto to the label comes from ONE switch, regrouping its entries into a fall-through run; only bodies that provably DIVERT are moved.
fn inline_switch_case_bodies(
    statements: &mut HashMap<Node, ClightStmt>,
    protected: &HashSet<Node>,
) {
    // Reference counts: every goto in the function vs gotos appearing exactly as a switch entry, plus how many distinct switches reference each target.
    let mut total_gotos: HashMap<Ident, usize> = HashMap::new();
    for s in statements.values() {
        for t in collect_goto_targets(s) {
            *total_gotos.entry(t as Ident).or_default() += 1;
        }
    }
    let mut entry_gotos: HashMap<Ident, usize> = HashMap::new();
    let mut switch_count: HashMap<Ident, usize> = HashMap::new();
    fn scan_switches(
        s: &ClightStmt,
        entry_gotos: &mut HashMap<Ident, usize>,
        switch_count: &mut HashMap<Ident, usize>,
    ) {
        match s {
            ClightStmt::Sswitch(_, cases) => {
                let mut seen_here: HashSet<Ident> = HashSet::new();
                for (_, cs) in cases {
                    if let ClightStmt::Sgoto(t) = cs {
                        *entry_gotos.entry(*t).or_default() += 1;
                        seen_here.insert(*t);
                    }
                    scan_switches(cs, entry_gotos, switch_count);
                }
                for t in seen_here {
                    *switch_count.entry(t).or_default() += 1;
                }
            }
            ClightStmt::Ssequence(ss) => ss
                .iter()
                .for_each(|x| scan_switches(x, entry_gotos, switch_count)),
            ClightStmt::Sifthenelse(_, a, b) => {
                scan_switches(a, entry_gotos, switch_count);
                scan_switches(b, entry_gotos, switch_count);
            }
            ClightStmt::Sloop(a, b) => {
                scan_switches(a, entry_gotos, switch_count);
                scan_switches(b, entry_gotos, switch_count);
            }
            (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => scan_switches(inner, entry_gotos, switch_count),
            _ => {}
        }
    }
    for s in statements.values() {
        scan_switches(s, &mut entry_gotos, &mut switch_count);
    }
    let inlinable: HashSet<Ident> = entry_gotos
        .iter()
        .filter(|(t, &ec)| {
            total_gotos.get(t).copied().unwrap_or(0) == ec
                && switch_count.get(t).copied().unwrap_or(0) == 1
        })
        .map(|(&t, _)| t)
        .collect();
    if inlinable.is_empty() {
        return;
    }

    // Harvest inlinable top-level labeled bodies: body and predecessor must divert and key must equal label; loop-level Sbreak/Scontinue bodies are excluded because their binding would change.
    let mut harvested: HashMap<Ident, ClightStmt> = HashMap::new();
    let mut top_keys: Vec<Node> = statements.keys().copied().collect();
    top_keys.sort_by_key(|&n| crate::util::exec_order_key(n));
    for (i, &k) in top_keys.iter().enumerate() {
        if let Some(ClightStmt::Slabel(lbl, inner)) = statements.get(&k) {
            if !protected.contains(&k)
                && inlinable.contains(lbl)
                && k == *lbl as Node
                && !stmt_may_fall_through(inner)
                && !matches!(inner.as_ref(), ClightStmt::Slabel(..))
                && !contains_escaping_break(inner)
                && !contains_loop_level_continue(inner)
            {
                let prev_diverts = i == 0
                    || top_keys
                        .get(i - 1)
                        .and_then(|p| statements.get(p))
                        .map(|s| !stmt_may_fall_through(s))
                        .unwrap_or(false);
                if i == 0 {
                    // The function's first statement is fallen into from the prologue: never movable.
                    continue;
                }
                if prev_diverts {
                    let lbl = *lbl;
                    let inner = (**inner).clone();
                    statements.remove(&k);
                    harvested.insert(lbl, inner);
                }
            }
        }
    }

    // Rebuild every tree: sequences may also hold the body as a SIBLING of the switch (loop bodies after assemble_loops). Sorted: claims are uncontested (switch_count==1), but the harvested pool is shared mutable state - never let HashMap arrival order decide anything.
    let mut keys: Vec<Node> = statements.keys().copied().collect();
    keys.sort_unstable();
    for k in keys {
        if let Some(stmt) = statements.remove(&k) {
            let rebuilt = rebuild_with_inlined_cases(stmt, &inlinable, &mut harvested);
            statements.insert(k, rebuilt);
        }
    }

    // Safety: anything harvested but never claimed goes back untouched (its gotos still exist).
    for (lbl, body) in harvested {
        statements.insert(lbl as Node, ClightStmt::Slabel(lbl, Box::new(body)));
    }
}

// Claimable entry targets for switches in `s`: excludes uniform-target switches (left for range-if rendering) and does not descend into Ssequence (those pools were already processed). Mirror of inline_into_switches traversal; best-effort -- unclaimed bodies are positionally restored.
fn collect_claimable_entry_targets(s: &ClightStmt, out: &mut HashSet<Ident>) {
    match s {
        ClightStmt::Sswitch(_, cases) => {
            for (_, cs) in cases {
                if let ClightStmt::Sgoto(t) = cs {
                    let uniform = cases
                        .iter()
                        .filter(|(v, _)| v.is_some())
                        .all(|(_, c)| matches!(c, ClightStmt::Sgoto(g) if g == t));
                    if !uniform {
                        out.insert(*t);
                    }
                }
                collect_claimable_entry_targets(cs, out);
            }
        }
        ClightStmt::Sifthenelse(_, a, b) | ClightStmt::Sloop(a, b) => {
            collect_claimable_entry_targets(a, out);
            collect_claimable_entry_targets(b, out);
        }
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => collect_claimable_entry_targets(inner, out),
        _ => {}
    }
}

fn rebuild_with_inlined_cases(
    stmt: ClightStmt,
    inlinable: &HashSet<Ident>,
    harvested: &mut HashMap<Ident, ClightStmt>,
) -> ClightStmt {
    match stmt {
        ClightStmt::Ssequence(ss) => {
            // First recurse, then let switches in this sequence claim diverting labeled SIBLINGS.
            let mut elems: Vec<ClightStmt> = ss
                .into_iter()
                .map(|s| rebuild_with_inlined_cases(s, inlinable, harvested))
                .collect();
            // Best-effort filter: exclude siblings claimable only by a switch elsewhere or a uniform-target switch, reducing unnecessary harvest+restore churn; soundness rests on exact positional restoration of unclaimed leftovers.
            let mut claimable_here: HashSet<Ident> = HashSet::new();
            for e in &elems {
                collect_claimable_entry_targets(e, &mut claimable_here);
            }
            // Harvest inlinable diverting labeled siblings; Scontinue bodies only at zero Sloop crossings where binding is preserved, each recording its position for exact restore if unclaimed.
            let mut local: HashMap<Ident, (usize, usize, ClightStmt)> = HashMap::new();
            let mut harvest_seq = 0usize;
            let mut kept: Vec<ClightStmt> = Vec::with_capacity(elems.len());
            for e in elems.drain(..) {
                let movable = match &e {
                    ClightStmt::Slabel(l, inner)
                        if inlinable.contains(l)
                            && claimable_here.contains(l)
                            && !matches!(inner.as_ref(), ClightStmt::Slabel(..))
                            && !stmt_may_fall_through(inner)
                            && !contains_escaping_break(inner) =>
                    {
                        kept.last()
                            .map(|p| !stmt_may_fall_through(p))
                            .unwrap_or(false)
                    }
                    _ => false,
                };
                if movable {
                    if let ClightStmt::Slabel(l, inner) = e {
                        local.insert(l, (kept.len(), harvest_seq, *inner));
                        harvest_seq += 1;
                    }
                } else {
                    kept.push(e);
                }
            }
            for e in kept.iter_mut() {
                inline_into_switches(e, inlinable, &mut local, harvested, 0);
            }
            // Restore unclaimed locals at recorded positions in descending (idx, seq) order to preserve relative order; indices remain valid since claims only mutate in-place.
            let mut leftovers: Vec<(usize, usize, Ident, ClightStmt)> = local
                .drain()
                .map(|(lbl, (idx, seq, body))| (idx, seq, lbl, body))
                .collect();
            leftovers.sort_unstable_by(|a, b| (b.0, b.1).cmp(&(a.0, a.1)));
            for (idx, _seq, lbl, body) in leftovers {
                kept.insert(idx.min(kept.len()), ClightStmt::Slabel(lbl, Box::new(body)));
            }
            ClightStmt::Ssequence(kept)
        }
        ClightStmt::Sifthenelse(c, a, b) => ClightStmt::Sifthenelse(
            c,
            Box::new(rebuild_with_inlined_cases(*a, inlinable, harvested)),
            Box::new(rebuild_with_inlined_cases(*b, inlinable, harvested)),
        ),
        ClightStmt::Sloop(a, b) => ClightStmt::Sloop(
            Box::new(rebuild_with_inlined_cases(*a, inlinable, harvested)),
            Box::new(rebuild_with_inlined_cases(*b, inlinable, harvested)),
        ),
        ClightStmt::Slabel(l, inner) => ClightStmt::Slabel(
            l,
            Box::new(rebuild_with_inlined_cases(*inner, inlinable, harvested)),
        ),
        mut other => {
            let mut empty: HashMap<Ident, (usize, usize, ClightStmt)> = HashMap::new();
            inline_into_switches(&mut other, inlinable, &mut empty, harvested, 0);
            other
        }
    }
}

// Regroup a switch's owned goto entries into a stacked fall-through run ending with the inlined body; loop_crossings must be zero for a body containing continue, since an Sloop rebinds it.
fn inline_into_switches(
    stmt: &mut ClightStmt,
    inlinable: &HashSet<Ident>,
    local: &mut HashMap<Ident, (usize, usize, ClightStmt)>,
    harvested: &mut HashMap<Ident, ClightStmt>,
    loop_crossings: usize,
) {
    match stmt {
        ClightStmt::Sswitch(_, cases) => {
            // Targets claimable for this switch, in first-appearance order.
            let mut order: Vec<Ident> = Vec::new();
            for (_, cs) in cases.iter() {
                if let ClightStmt::Sgoto(t) = cs {
                    if inlinable.contains(t)
                        && !order.contains(t)
                        && (local.contains_key(t) || harvested.contains_key(t))
                    {
                        order.push(*t);
                    }
                }
            }
            for t in order {
                // Uniform-dispatch guard: a switch where every valued entry targets the same `t` is degenerate -- leave all-goto so the emitter can render it as a range/equality `if` via try_switch_to_range_if; claiming here would freeze it as a stacked-case switch.
                let uniform = cases
                    .iter()
                    .filter(|(v, _)| v.is_some())
                    .all(|(_, cs)| matches!(cs, ClightStmt::Sgoto(g) if *g == t));
                if uniform {
                    continue;
                }
                // Past an Sloop boundary the enclosing loop changed, so a continue-carrying body must not be claimed; check before pool removal so it remains available to a zero-crossing switch.
                if loop_crossings > 0
                    && local
                        .get(&t)
                        .is_some_and(|(_, _, b)| contains_loop_level_continue(b))
                {
                    continue;
                }
                // Fall-through-predecessor gate: the run re-insertion keeps the FIRST `goto t` slot but removes later ones, so a falling predecessor of a later slot would be rerouted. Refuse claiming when any non-first `goto t` entry has a falling predecessor; keeping gotos is always safe.
                let first_goto_idx = cases
                    .iter()
                    .position(|(_, cs)| matches!(cs, ClightStmt::Sgoto(g) if *g == t));
                let falls_into_removed = cases.iter().enumerate().any(|(i, (_, cs))| {
                    matches!(cs, ClightStmt::Sgoto(g) if *g == t)
                        && Some(i) != first_goto_idx
                        && i > 0
                        && stmt_may_fall_through(&cases[i - 1].1)
                });
                if falls_into_removed {
                    continue;
                }
                // Track origin pool so an empty-run can restore the body with position data intact.
                let (body, local_slot) = match local.remove(&t) {
                    Some((idx, seq, b)) => (b, Some((idx, seq))),
                    None => match harvested.remove(&t) {
                        Some(b) => (b, None),
                        None => continue,
                    },
                };
                if std::env::var("CF3_INLINE_TRACE").is_ok() {
                    let bd = format!("{:?}", body);
                    eprintln!(
                        "[cf3-inline] claim target={:#x} body={}",
                        t,
                        &bd[..bd.len().min(300)]
                    );
                }
                // Remove all `goto t` entries, re-inserting the stacked run at the FIRST removed position to preserve case order (appending at end drifts cases out of order, e.g. cases 2/4/5 below 10 in cut).
                let mut run_vals: Vec<Option<Z>> = Vec::new();
                let mut first_pos: Option<usize> = None;
                let mut kept_cases: Vec<(Option<Z>, ClightStmt)> = Vec::with_capacity(cases.len());
                for (v, cs) in cases.drain(..) {
                    if matches!(&cs, ClightStmt::Sgoto(g) if *g == t) {
                        if first_pos.is_none() {
                            first_pos = Some(kept_cases.len());
                        }
                        run_vals.push(v);
                    } else {
                        kept_cases.push((v, cs));
                    }
                }
                *cases = kept_cases;
                if run_vals.is_empty() {
                    // Cannot happen for targets collected above, but silently dropping a claimed body deletes statements; restore to origin pool.
                    match local_slot {
                        Some((idx, seq)) => {
                            local.insert(t, (idx, seq, body));
                        }
                        None => {
                            harvested.insert(t, body);
                        }
                    }
                    continue;
                }
                let insert_at = first_pos.unwrap_or(cases.len());
                let mut run: Vec<(Option<Z>, ClightStmt)> = Vec::new();
                for (i, v) in run_vals.iter().enumerate() {
                    if i + 1 == run_vals.len() {
                        run.push((*v, body.clone()));
                    } else {
                        run.push((*v, ClightStmt::Sskip));
                    }
                }
                for (i, entry) in run.into_iter().enumerate() {
                    cases.insert(insert_at + i, entry);
                }
            }
            for (_, cs) in cases.iter_mut() {
                inline_into_switches(cs, inlinable, local, harvested, loop_crossings);
            }
        }
        ClightStmt::Sifthenelse(_, a, b) => {
            inline_into_switches(a, inlinable, local, harvested, loop_crossings);
            inline_into_switches(b, inlinable, local, harvested, loop_crossings);
        }
        ClightStmt::Slabel(_, inner) => {
            inline_into_switches(inner, inlinable, local, harvested, loop_crossings)
        }
        ClightStmt::Sloop(a, b) => {
            inline_into_switches(a, inlinable, local, harvested, loop_crossings + 1);
            inline_into_switches(b, inlinable, local, harvested, loop_crossings + 1);
        }
        _ => {}
    }
}

// Restricted goto conversion inside switch case bodies: ONLY loop-header/body-top gotos become Scontinue (binding through the switch to the enclosing loop); everything else is untouched. A nested Sloop captures continue, so recursion stops there.
fn convert_case_continues(
    stmt: &ClightStmt,
    header_label: Ident,
    body_top_label: Option<Ident>,
) -> ClightStmt {
    match stmt {
        ClightStmt::Sgoto(target) if *target == header_label || Some(*target) == body_top_label => {
            ClightStmt::Scontinue
        }
        ClightStmt::Ssequence(ss) => ClightStmt::Ssequence(
            ss.iter()
                .map(|s| convert_case_continues(s, header_label, body_top_label))
                .collect(),
        ),
        ClightStmt::Sifthenelse(c, t, e) => ClightStmt::Sifthenelse(
            c.clone(),
            Box::new(convert_case_continues(t, header_label, body_top_label)),
            Box::new(convert_case_continues(e, header_label, body_top_label)),
        ),
        ClightStmt::Slabel(lbl, inner) => ClightStmt::Slabel(
            *lbl,
            Box::new(convert_case_continues(inner, header_label, body_top_label)),
        ),
        ClightStmt::Sswitch(e, cases) => ClightStmt::Sswitch(
            e.clone(),
            cases
                .iter()
                .map(|(v, s)| (*v, convert_case_continues(s, header_label, body_top_label)))
                .collect(),
        ),
        _ => stmt.clone(),
    }
}

// CF-4: whether an assembled body can start a second iteration, via a loop-level Scontinue or a path falling off the end; gotos resolve against the producing NODE, and it is conservative toward true.
fn loop_body_can_reenter(
    body: &[ClightStmt],
    body_stmt_nodes: &[Node],
    body_node_set: &HashSet<Node>,
    header: Node,
    body_top: Option<Node>,
) -> bool {
    if body.iter().any(contains_loop_level_continue) {
        return true;
    }
    let mut targets: HashSet<Node> = HashSet::new();
    for s in body {
        for t in collect_goto_targets(s) {
            targets.insert(t);
        }
    }
    // A goto to the header or to the exec-first body node is a back-edge even when it could not become Scontinue (convert_loop_gotos does not descend into Sswitch, so case-body back-edges stay as gotos).
    if targets.contains(&header) || body_top.is_some_and(|t| targets.contains(&t)) {
        return true;
    }
    let pos: HashMap<Node, usize> = body_stmt_nodes
        .iter()
        .enumerate()
        .map(|(i, &n)| (n, i))
        .collect();
    let mut entries: Vec<usize> = vec![0];
    for t in &targets {
        if let Some(&i) = pos.get(t) {
            entries.push(i);
        } else if body_node_set.contains(t) {
            // In-body target with no emitted statement of its own (absorbed/merged): position unknown, give up.
            return true;
        }
        // Otherwise the goto leaves the loop (kept only for switch-nested exits): it diverts.
    }
    entries.sort_unstable();
    entries.dedup();
    // Re-enterable iff some entry's straight-line suffix may fall off the end (gotos divert at their own position; resumption at another emitted node is covered by that node's entry).
    'entry: for &e in &entries {
        for s in &body[e..] {
            if !stmt_may_fall_through(s) {
                continue 'entry;
            }
        }
        return true;
    }
    false
}

// Scontinue bound to the CURRENT loop level: a nested Sloop captures its own continues; Sswitch does not capture continue (C semantics), so case bodies are searched.
fn contains_loop_level_continue(s: &ClightStmt) -> bool {
    match s {
        ClightStmt::Scontinue => true,
        ClightStmt::Ssequence(ss) => ss.iter().any(contains_loop_level_continue),
        ClightStmt::Sifthenelse(_, t, e) => {
            contains_loop_level_continue(t) || contains_loop_level_continue(e)
        }
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => contains_loop_level_continue(inner),
        ClightStmt::Sswitch(_, cases) => {
            cases.iter().any(|(_, st)| contains_loop_level_continue(st))
        }
        ClightStmt::Sloop(..) => false,
        _ => false,
    }
}

// Sbreak that escapes the statement OUTWARD (not captured by a nested Sloop or Sswitch).
fn contains_escaping_break(s: &ClightStmt) -> bool {
    match s {
        ClightStmt::Sbreak => true,
        ClightStmt::Ssequence(ss) => ss.iter().any(contains_escaping_break),
        ClightStmt::Sifthenelse(_, t, e) => {
            contains_escaping_break(t) || contains_escaping_break(e)
        }
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => contains_escaping_break(inner),
        ClightStmt::Sloop(..) | ClightStmt::Sswitch(..) => false,
        _ => false,
    }
}

// MAY execution fall off the end of this statement in straight-line position? A nested loop completes only via its own break, a switch via an escaping break or its last case falling out.
fn stmt_may_fall_through(s: &ClightStmt) -> bool {
    match s {
        ClightStmt::Sreturn(_)
        | ClightStmt::Sgoto(_)
        | ClightStmt::Sbreak
        | ClightStmt::Scontinue => false,
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => stmt_may_fall_through(inner),
        ClightStmt::Ssequence(ss) => ss.iter().all(stmt_may_fall_through),
        ClightStmt::Sifthenelse(_, t, e) => stmt_may_fall_through(t) || stmt_may_fall_through(e),
        ClightStmt::Sloop(b, _) => contains_escaping_break(b),
        ClightStmt::Sswitch(_, cases) => {
            cases.iter().any(|(_, st)| contains_escaping_break(st))
                || cases
                    .last()
                    .map_or(true, |(_, st)| stmt_may_fall_through(st))
        }
        _ => true,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LiveStmtFrontier {
    Unique(Node),
    Ambiguous,
}

fn join_live_stmt_frontier(
    left: Option<LiveStmtFrontier>,
    right: LiveStmtFrontier,
) -> LiveStmtFrontier {
    match (left, right) {
        (None, value) => value,
        (Some(LiveStmtFrontier::Ambiguous), _) | (_, LiveStmtFrontier::Ambiguous) => {
            LiveStmtFrontier::Ambiguous
        }
        (Some(LiveStmtFrontier::Unique(left)), LiveStmtFrontier::Unique(right))
            if left == right =>
        {
            LiveStmtFrontier::Unique(left)
        }
        (Some(LiveStmtFrontier::Unique(_)), LiveStmtFrontier::Unique(_)) => {
            LiveStmtFrontier::Ambiguous
        }
    }
}

/// Compute the first surviving statement reached through selected-away CFG
/// nodes.  Surviving nodes are lattice boundaries; propagation through the
/// remaining CFG is unknown -> unique -> ambiguous and therefore O(V + E),
/// without materializing a pairwise reachability relation.
fn live_stmt_frontiers(
    statements: &HashMap<Node, ClightStmt>,
    successors: &HashMap<Node, Vec<Node>>,
) -> HashMap<Node, LiveStmtFrontier> {
    let live: HashSet<Node> = statements.keys().copied().collect();
    let mut reverse: HashMap<Node, Vec<Node>> = HashMap::new();
    for (&source, targets) in successors {
        for &target in targets {
            if source != target {
                reverse.entry(target).or_default().push(source);
            }
        }
    }

    let mut state: HashMap<Node, LiveStmtFrontier> = live
        .iter()
        .copied()
        .map(|node| (node, LiveStmtFrontier::Unique(node)))
        .collect();
    let mut work: Vec<Node> = live.iter().copied().collect();
    while let Some(node) = work.pop() {
        let incoming = state[&node];
        let Some(predecessors) = reverse.get(&node) else {
            continue;
        };
        for &pred in predecessors {
            if live.contains(&pred) {
                continue;
            }
            let joined = join_live_stmt_frontier(state.get(&pred).copied(), incoming);
            if state.get(&pred).copied() != Some(joined) {
                state.insert(pred, joined);
                work.push(pred);
            }
        }
    }
    state
}

fn unique_live_successor(
    source: Node,
    frontier: &HashMap<Node, LiveStmtFrontier>,
    successors: &HashMap<Node, Vec<Node>>,
) -> Option<Node> {
    let mut raw_successors = successors.get(&source)?.clone();
    raw_successors.sort_unstable();
    raw_successors.dedup();
    if raw_successors.is_empty() {
        return None;
    }

    let mut joined = None;
    for successor in raw_successors {
        let next = frontier.get(&successor).copied()?;
        joined = Some(join_live_stmt_frontier(joined, next));
    }
    match joined {
        Some(LiveStmtFrontier::Unique(target)) => Some(target),
        _ => None,
    }
}

fn append_cfg_goto(stmt: &mut ClightStmt, target: Node) {
    match stmt {
        // Keep a node's entry label attached to its first effect, not to the
        // transfer appended after that effect.
        ClightStmt::Slabel(_, inner) => append_cfg_goto(inner, target),
        ClightStmt::Ssequence(items) => items.push(ClightStmt::Sgoto(ident_from_node(target))),
        _ => {
            let effect = std::mem::replace(stmt, ClightStmt::Sskip);
            *stmt = ClightStmt::Ssequence(vec![effect, ClightStmt::Sgoto(ident_from_node(target))]);
        }
    }
}

/// Make every uniquely determined top-level fallthrough explicit before C
/// layout.  RPO may legally place another branch between a value statement
/// and its join, so adjacency is not a semantic representation of this CFG
/// edge.  The emitter later removes only gotos whose target is actually the
/// immediately following labeled statement in the finalized layout.
fn materialize_cfg_fallthrough_gotos(
    statements: &mut HashMap<Node, ClightStmt>,
    successors: &HashMap<Node, Vec<Node>>,
) {
    let frontier = live_stmt_frontiers(statements, successors);
    let mut sources: Vec<Node> = statements.keys().copied().collect();
    sources.sort_unstable();
    let mut plans = Vec::new();

    for source in sources {
        let Some(stmt) = statements.get(&source) else {
            continue;
        };
        if !stmt_may_fall_through(stmt) {
            continue;
        }
        // A frontier that resolves back to SOURCE is not a layout
        // fallthrough.  It arises when the source statement is a compound
        // (notably a recovered switch) whose raw CFG successors are internal
        // nodes already absorbed by that same statement.  Appending a goto in
        // that case turns the compound's ordinary default continuation into
        // an artificial self-loop.
        if let Some(target) = unique_live_successor(source, &frontier, successors) {
            if target != source {
                plans.push((source, target));
            }
        }
    }

    for (source, target) in plans {
        if let Some(stmt) = statements.get_mut(&source) {
            append_cfg_goto(stmt, target);
        }
    }
}

pub(crate) fn callee_ident_from_expr(
    func_expr: &ClightExpr,
    name_to_ident: &HashMap<String, Ident>,
) -> Option<Ident> {
    match func_expr {
        ClightExpr::Evar(id, _) => Some(*id as Ident),
        ClightExpr::EvarSymbol(name, _) => {
            let key = name.to_string();
            if let Some(&id) = name_to_ident.get(&key) {
                return Some(id);
            }
            let sanitized =
                crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(
                    name,
                );
            name_to_ident.get(&sanitized).copied()
        }
        ClightExpr::Eaddrof(inner, _) => callee_ident_from_expr(inner, name_to_ident),
        ClightExpr::Ecast(inner, _) => callee_ident_from_expr(inner, name_to_ident),
        _ => None,
    }
}

fn flatten_sequence(stmts: Vec<ClightStmt>) -> Vec<ClightStmt> {
    let mut result = Vec::new();
    for stmt in stmts {
        match stmt {
            ClightStmt::Ssequence(nested) => {
                result.extend(flatten_sequence(nested));
            }
            ClightStmt::Sskip => {}
            _ => {
                result.push(stmt);
            }
        }
    }
    result
}

fn is_control_flow_stmt(stmt: &ClightStmt) -> bool {
    match stmt {
        ClightStmt::Sifthenelse(_, _, _)
        | ClightStmt::Sloop(_, _)
        | ClightStmt::Sgoto(_)
        | ClightStmt::Sreturn(_)
        | ClightStmt::Sbreak
        | ClightStmt::Scontinue
        | ClightStmt::Sswitch(_, _) => true,
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => is_control_flow_stmt(inner),
        ClightStmt::Ssequence(stmts) => stmts.iter().any(is_control_flow_stmt),
        _ => false,
    }
}

fn is_value_stmt(stmt: &ClightStmt) -> bool {
    match stmt {
        ClightStmt::Scall(_, _, _)
        | ClightStmt::Sset(_, _)
        | ClightStmt::Sassign(_, _)
        | ClightStmt::Sbuiltin(_, _, _, _) => true,
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => is_value_stmt(inner),
        ClightStmt::Ssequence(stmts) => stmts.iter().any(is_value_stmt),
        _ => false,
    }
}

// Depth bound for goto-chain inlining, charging the measured target depth so backward chains cannot compound to stack overflow; 256 admits all observed real chains (~81 max).

// Tree depth measured iteratively (not recursively) so it is safe to call on the arbitrarily deep trees this measurement exists to fence.
fn stmt_depth(root: &ClightStmt) -> usize {
    let mut max = 0usize;
    let mut work: Vec<(&ClightStmt, usize)> = vec![(root, 1)];
    while let Some((s, d)) = work.pop() {
        if d > max {
            max = d;
        }
        match s {
            ClightStmt::Ssequence(ss) => work.extend(ss.iter().map(|c| (c, d + 1))),
            ClightStmt::Sifthenelse(_, a, b) | ClightStmt::Sloop(a, b) => {
                work.push((a.as_ref(), d + 1));
                work.push((b.as_ref(), d + 1));
            }
            (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => work.push((inner.as_ref(), d + 1)),
            ClightStmt::Sswitch(_, cases) => work.extend(cases.iter().map(|(_, c)| (c, d + 1))),
            _ => {}
        }
    }
    max
}

fn count_predecessors(successors: &HashMap<Node, Vec<Node>>) -> HashMap<Node, usize> {
    let mut preds = HashMap::new();
    for succs in successors.values() {
        for &succ in succs {
            *preds.entry(succ).or_insert(0) += 1;
        }
    }
    preds
}

fn deduplicate_identical_blocks(
    statements: &mut HashMap<Node, ClightStmt>,
    protected: &HashSet<Node>,
    successors: &HashMap<Node, Vec<Node>>,
) {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    // Falling out of a non-terminal Clight statement is part of the basic
    // block's semantics.  Equal visible statements with different CFG
    // continuations are therefore not interchangeable.
    let mut content_hash: HashMap<(u64, Vec<Node>), Vec<Node>> = HashMap::new();

    for (&node, stmt) in statements.iter() {
        let core_stmt = match stmt {
            ClightStmt::Slabel(_, inner) => inner.as_ref(),
            other => other,
        };

        match core_stmt {
            ClightStmt::Sskip | ClightStmt::Sbreak | ClightStmt::Scontinue => continue,
            ClightStmt::Sgoto(_) => continue,
            _ => {}
        }

        let mut hasher = DefaultHasher::new();
        core_stmt.hash(&mut hasher);
        let hash = hasher.finish();
        let mut cfg_successors = successors.get(&node).cloned().unwrap_or_default();
        cfg_successors.sort_unstable();
        cfg_successors.dedup();

        content_hash
            .entry((hash, cfg_successors))
            .or_default()
            .push(node);
    }

    let mut redirect_map: HashMap<Node, Node> = HashMap::new();

    for ((_hash, _cfg_successors), mut nodes) in content_hash {
        if nodes.len() <= 1 {
            continue;
        }

        let protected_nodes: Vec<Node> = nodes
            .iter()
            .copied()
            .filter(|node| protected.contains(node))
            .collect();
        if protected_nodes.len() > 1 {
            // Two independently applied sequence anchors carry distinct CFG
            // identities even when their statement trees happen to match.
            continue;
        }
        nodes.sort();
        let canonical = protected_nodes.first().copied().unwrap_or(nodes[0]);
        let canonical_stmt = statements.get(&canonical);

        for &other in &nodes {
            if other == canonical {
                continue;
            }
            let other_stmt = statements.get(&other);
            let canonical_core = match canonical_stmt {
                Some(ClightStmt::Slabel(_, inner)) => Some(inner.as_ref()),
                Some(other) => Some(other),
                None => None,
            };
            let other_core = match other_stmt {
                Some(ClightStmt::Slabel(_, inner)) => Some(inner.as_ref()),
                Some(other) => Some(other),
                None => None,
            };

            if canonical_core == other_core {
                redirect_map.insert(other, canonical);
            }
        }
    }

    if redirect_map.is_empty() {
        return;
    }

    log::debug!("Deduplicating {} identical blocks", redirect_map.len());

    let mut nodes_to_update: Vec<Node> = statements.keys().copied().collect();
    nodes_to_update.sort();
    for node in nodes_to_update {
        if let Some(stmt) = statements.get(&node).cloned() {
            let updated = redirect_gotos_in_stmt(&stmt, &redirect_map);
            if updated != stmt {
                statements.insert(node, updated);
            }
        }
    }

    for duplicate in redirect_map.keys() {
        statements.remove(duplicate);
    }
}

fn redirect_gotos_in_stmt(stmt: &ClightStmt, redirect_map: &HashMap<Node, Node>) -> ClightStmt {
    match stmt {
        ClightStmt::Sgoto(target) => {
            let target_node = *target as Node;
            if let Some(&canonical) = redirect_map.get(&target_node) {
                ClightStmt::Sgoto(canonical as Ident)
            } else {
                stmt.clone()
            }
        }
        ClightStmt::Sifthenelse(cond, then_box, else_box) => {
            let new_then = redirect_gotos_in_stmt(then_box, redirect_map);
            let new_else = redirect_gotos_in_stmt(else_box, redirect_map);
            ClightStmt::Sifthenelse(cond.clone(), Box::new(new_then), Box::new(new_else))
        }
        ClightStmt::Sloop(body, incr) => {
            let new_body = redirect_gotos_in_stmt(body, redirect_map);
            let new_incr = redirect_gotos_in_stmt(incr, redirect_map);
            ClightStmt::Sloop(Box::new(new_body), Box::new(new_incr))
        }
        ClightStmt::Ssequence(stmts) => {
            let new_stmts: Vec<_> = stmts
                .iter()
                .map(|s| redirect_gotos_in_stmt(s, redirect_map))
                .collect();
            ClightStmt::Ssequence(new_stmts)
        }
        ClightStmt::Slabel(lbl, inner) => {
            let new_inner = redirect_gotos_in_stmt(inner, redirect_map);
            ClightStmt::Slabel(*lbl, Box::new(new_inner))
        }
        ClightStmt::Sswitch(expr, cases) => {
            let new_cases: Vec<_> = cases
                .iter()
                .map(|(label, s)| (label.clone(), redirect_gotos_in_stmt(s, redirect_map)))
                .collect();
            ClightStmt::Sswitch(expr.clone(), new_cases)
        }
        _ => stmt.clone(),
    }
}

fn inline_control_flow_bodies(
    statements: &mut HashMap<Node, ClightStmt>,
    successors: &HashMap<Node, Vec<Node>>,
    protected: &HashSet<Node>,
) {
    let preds = count_predecessors(successors);
    let mut predecessor_nodes: HashMap<Node, Vec<Node>> = HashMap::new();
    for (&pred, succs) in successors {
        for &succ in succs {
            predecessor_nodes.entry(succ).or_default().push(pred);
        }
    }
    for sources in predecessor_nodes.values_mut() {
        sources.sort_unstable();
        sources.dedup();
    }
    // A goto that is still present inside an assembled loop owns an exact
    // control-flow edge.  Inlining its target into the loop body changes the
    // target's fallthrough continuation: an outside exit target would now
    // fall through to the next loop iteration.  Preserve every such target at
    // top level; true back-edges have already become `continue`, so retaining
    // the remaining gotos is the conservative, structurally-derived choice.
    let mut loop_goto_targets: HashSet<Node> = HashSet::new();
    for stmt in statements.values() {
        collect_loop_goto_targets(stmt, 0, &mut loop_goto_targets);
    }
    let protected_inline_targets: HashSet<Node> =
        protected.union(&loop_goto_targets).copied().collect();
    let mut inlined_nodes: HashSet<Node> = HashSet::new();
    let mut nodes_to_process: Vec<Node> = statements.keys().copied().collect();
    nodes_to_process.sort();

    // Lazily-filled assembled-tree depth per node; the splice gate charges the target's full depth so backward-ordered chains cannot compound past CONFIG.select.max_goto_inline_depth.
    let mut depth_of: HashMap<Node, usize> = HashMap::new();

    for node in nodes_to_process {
        if let Some(stmt) = statements.get(&node).cloned() {
            let mut visiting = HashSet::new();
            visiting.insert(node);
            let (inlined, newly_inlined) = inline_stmt_recursive_track(
                &stmt,
                node,
                statements,
                &preds,
                &predecessor_nodes,
                &protected_inline_targets,
                &mut visiting,
                0,
                &mut depth_of,
            );
            // Free absorbed children immediately: each inlined node has pred_count==1 so it is referenced nowhere else, and keeping every fully-inlined tree is O(n^2) memory that OOMs large functions.
            for &n in &newly_inlined {
                statements.remove(&n);
                depth_of.remove(&n);
            }
            inlined_nodes.extend(newly_inlined);
            if inlined != stmt {
                depth_of.insert(node, stmt_depth(&inlined));
                statements.insert(node, inlined);
            }
        }
    }

    if std::env::var("RB2_TRACE").is_ok() {
        let max_d = depth_of.values().copied().max().unwrap_or(0);
        let max_live = statements
            .iter()
            .map(|(n, s)| (stmt_depth(s), *n))
            .max()
            .unwrap_or((0, 0));
        eprintln!(
            "[rb2] S5 done: max depth_of={} live max stmt_depth={} at node {:x}",
            max_d, max_live.0, max_live.1
        );
    }

    let referenced: HashSet<Node> = statements
        .values()
        .flat_map(|stmt| collect_goto_targets(stmt))
        .collect();

    statements.retain(|node, stmt| {
        if protected.contains(node) {
            return true;
        }
        if inlined_nodes.contains(node) && !referenced.contains(node) {
            return false;
        }

        let is_referenced = referenced.contains(node);
        let has_multiple_preds = preds.get(node).map_or(false, |&count| count > 1);
        let has_no_preds = preds.get(node).is_none();
        let is_control = is_control_flow_stmt(stmt);
        let is_value = is_value_stmt(stmt);

        is_referenced || has_multiple_preds || has_no_preds || is_control || is_value
    });
}

fn collect_loop_goto_targets(stmt: &ClightStmt, loop_depth: usize, out: &mut HashSet<Node>) {
    match stmt {
        ClightStmt::Sgoto(target) if loop_depth > 0 => {
            out.insert(*target as Node);
        }
        ClightStmt::Ssequence(stmts) => {
            for stmt in stmts {
                collect_loop_goto_targets(stmt, loop_depth, out);
            }
        }
        ClightStmt::Sifthenelse(_, then_stmt, else_stmt) => {
            collect_loop_goto_targets(then_stmt, loop_depth, out);
            collect_loop_goto_targets(else_stmt, loop_depth, out);
        }
        ClightStmt::Sloop(body, incr) => {
            collect_loop_goto_targets(body, loop_depth + 1, out);
            collect_loop_goto_targets(incr, loop_depth + 1, out);
        }
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => collect_loop_goto_targets(inner, loop_depth, out),
        ClightStmt::Sswitch(_, cases) => {
            for (_, stmt) in cases {
                collect_loop_goto_targets(stmt, loop_depth, out);
            }
        }
        _ => {}
    }
}

fn flatten_cascading_ifthenelse_all(statements: &mut HashMap<Node, ClightStmt>) {
    let mut nodes: Vec<Node> = statements.keys().copied().collect();
    nodes.sort();
    for node in nodes {
        if let Some(stmt) = statements.get(&node).cloned() {
            let flattened = flatten_cascading_ifthenelse(&stmt);
            if flattened != stmt {
                statements.insert(node, flattened);
            }
        }
    }
}

fn flatten_cascading_ifthenelse(stmt: &ClightStmt) -> ClightStmt {
    if let ClightStmt::Sifthenelse(cond, then_box, else_box) = stmt {
        if let ClightStmt::Sgoto(exit_label) = else_box.as_ref() {
            let exit = *exit_label;
            let mut result_stmts: Vec<ClightStmt> = Vec::new();
            let mut found_cascade = false;

            let mut cur_cond = cond;
            let mut cur_then: &ClightStmt = then_box.as_ref();

            loop {
                if let Some((prefix, inner_cond, inner_then, inner_else)) =
                    extract_trailing_ifthenelse(cur_then)
                {
                    if let ClightStmt::Sgoto(inner_exit) = inner_else {
                        if *inner_exit == exit {
                            found_cascade = true;
                            result_stmts.push(ClightStmt::Sifthenelse(
                                cur_cond.clone(),
                                Box::new(ClightStmt::Sskip),
                                Box::new(ClightStmt::Sgoto(exit)),
                            ));
                            for s in prefix {
                                result_stmts.push(flatten_cascading_ifthenelse(s));
                            }
                            cur_cond = inner_cond;
                            cur_then = inner_then;
                            continue;
                        }
                    }
                }
                break;
            }

            if found_cascade {
                result_stmts.push(ClightStmt::Sifthenelse(
                    cur_cond.clone(),
                    Box::new(flatten_cascading_ifthenelse(cur_then)),
                    Box::new(ClightStmt::Sgoto(exit)),
                ));
                return ClightStmt::Ssequence(flatten_sequence(result_stmts));
            }
        }
    }

    match stmt {
        ClightStmt::Sifthenelse(cond, then_box, else_box) => ClightStmt::Sifthenelse(
            cond.clone(),
            Box::new(flatten_cascading_ifthenelse(then_box)),
            Box::new(flatten_cascading_ifthenelse(else_box)),
        ),
        ClightStmt::Ssequence(stmts) => ClightStmt::Ssequence(
            stmts
                .iter()
                .map(|s| flatten_cascading_ifthenelse(s))
                .collect(),
        ),
        ClightStmt::Slabel(lbl, inner) => {
            ClightStmt::Slabel(*lbl, Box::new(flatten_cascading_ifthenelse(inner)))
        }
        ClightStmt::Sloop(body, incr) => ClightStmt::Sloop(
            Box::new(flatten_cascading_ifthenelse(body)),
            Box::new(flatten_cascading_ifthenelse(incr)),
        ),
        _ => stmt.clone(),
    }
}

fn extract_trailing_ifthenelse(
    stmt: &ClightStmt,
) -> Option<(Vec<&ClightStmt>, &ClightExpr, &ClightStmt, &ClightStmt)> {
    match stmt {
        ClightStmt::Ssequence(stmts) if !stmts.is_empty() => {
            let last = stmts.last().unwrap();
            let core = match last {
                ClightStmt::Slabel(_, inner) => inner.as_ref(),
                other => other,
            };
            if let ClightStmt::Sifthenelse(cond, then_box, else_box) = core {
                let prefix: Vec<&ClightStmt> = stmts[..stmts.len() - 1].iter().collect();
                Some((prefix, cond, then_box.as_ref(), else_box.as_ref()))
            } else {
                None
            }
        }
        ClightStmt::Sifthenelse(cond, then_box, else_box) => {
            Some((vec![], cond, then_box.as_ref(), else_box.as_ref()))
        }
        ClightStmt::Slabel(_, inner) => {
            if let ClightStmt::Sifthenelse(cond, then_box, else_box) = inner.as_ref() {
                Some((vec![], cond, then_box.as_ref(), else_box.as_ref()))
            } else {
                None
            }
        }
        _ => None,
    }
}

// `depth` is structural position depth (not a follow counter): the native stack cost the printer pays at this position.
fn inline_stmt_recursive_track(
    stmt: &ClightStmt,
    owner: Node,
    statements: &HashMap<Node, ClightStmt>,
    preds: &HashMap<Node, usize>,
    predecessor_nodes: &HashMap<Node, Vec<Node>>,
    protected_targets: &HashSet<Node>,
    visiting: &mut HashSet<Node>,
    depth: usize,
    depth_of: &mut HashMap<Node, usize>,
) -> (ClightStmt, Vec<Node>) {
    let mut inlined = Vec::new();

    let result = match stmt {
        ClightStmt::Sifthenelse(cond, then_box, else_box) => {
            let (then_stmt, then_inlined) = inline_body_if_local_track(
                &**then_box,
                owner,
                statements,
                preds,
                predecessor_nodes,
                protected_targets,
                visiting,
                depth + 1,
                depth_of,
            );
            let (else_stmt, else_inlined) = inline_body_if_local_track(
                &**else_box,
                owner,
                statements,
                preds,
                predecessor_nodes,
                protected_targets,
                visiting,
                depth + 1,
                depth_of,
            );
            inlined.extend(then_inlined);
            inlined.extend(else_inlined);
            ClightStmt::Sifthenelse(cond.clone(), Box::new(then_stmt), Box::new(else_stmt))
        }
        ClightStmt::Sloop(body_box, incr_box) => {
            let (body_stmt, body_inlined) = inline_body_if_local_track(
                &**body_box,
                owner,
                statements,
                preds,
                predecessor_nodes,
                protected_targets,
                visiting,
                depth + 1,
                depth_of,
            );
            let (incr_stmt, incr_inlined) = inline_body_if_local_track(
                &**incr_box,
                owner,
                statements,
                preds,
                predecessor_nodes,
                protected_targets,
                visiting,
                depth + 1,
                depth_of,
            );
            inlined.extend(body_inlined);
            inlined.extend(incr_inlined);
            ClightStmt::Sloop(Box::new(body_stmt), Box::new(incr_stmt))
        }
        ClightStmt::Ssequence(stmts) => {
            let mut result_stmts = Vec::new();
            for s in stmts {
                let (inlined_s, s_inlined) = inline_stmt_recursive_track(
                    s,
                    owner,
                    statements,
                    preds,
                    predecessor_nodes,
                    protected_targets,
                    visiting,
                    depth + 1,
                    depth_of,
                );
                result_stmts.push(inlined_s);
                inlined.extend(s_inlined);
            }
            ClightStmt::Ssequence(flatten_sequence(result_stmts))
        }
        ClightStmt::Slabel(lbl, inner) => {
            let (inner_inlined, inner_nodes) = inline_stmt_recursive_track(
                &**inner,
                owner,
                statements,
                preds,
                predecessor_nodes,
                protected_targets,
                visiting,
                depth + 1,
                depth_of,
            );
            inlined.extend(inner_nodes);
            ClightStmt::Slabel(*lbl, Box::new(inner_inlined))
        }
        ClightStmt::Sswitch(expr, cases) => {
            let mut new_cases = Vec::new();
            for (label, case_stmt) in cases {
                let (inlined_case, case_inlined) = inline_body_if_local_track(
                    case_stmt,
                    owner,
                    statements,
                    preds,
                    predecessor_nodes,
                    protected_targets,
                    visiting,
                    depth + 1,
                    depth_of,
                );
                inlined.extend(case_inlined);
                new_cases.push((label.clone(), inlined_case));
            }
            ClightStmt::Sswitch(expr.clone(), new_cases)
        }
        _ => stmt.clone(),
    };

    (result, inlined)
}

fn inline_body_if_local_track(
    stmt: &ClightStmt,
    owner: Node,
    statements: &HashMap<Node, ClightStmt>,
    preds: &HashMap<Node, usize>,
    predecessor_nodes: &HashMap<Node, Vec<Node>>,
    protected_targets: &HashSet<Node>,
    visiting: &mut HashSet<Node>,
    depth: usize,
    depth_of: &mut HashMap<Node, usize>,
) -> (ClightStmt, Vec<Node>) {
    match stmt {
        ClightStmt::Sgoto(target_ident) => {
            let target_node = *target_ident as u64;
            let pred_count = preds.get(&target_node).copied().unwrap_or(0);
            // A structured statement can contain a synthesized goto whose
            // source is not the target's raw CFG predecessor.  Moving the
            // target into that goto and deleting it globally is unsound while
            // a distinct predecessor still survives at top level: its
            // fallthrough edge would lose the target entirely.  Inline only
            // when every still-materialized predecessor is this statement's
            // owner; an absent predecessor has already been structurally
            // absorbed into an enclosing statement.
            let has_other_live_predecessor =
                predecessor_nodes.get(&target_node).is_some_and(|sources| {
                    sources
                        .iter()
                        .any(|source| *source != owner && statements.contains_key(source))
                });

            if pred_count == 1
                && !has_other_live_predecessor
                && !protected_targets.contains(&target_node)
                && !visiting.contains(&target_node)
            {
                if let Some(target_stmt) = statements.get(&target_node) {
                    if is_trivial_labeled_goto(target_stmt) {
                        return (stmt.clone(), vec![]);
                    }
                    // Admit only if (depth + target's already-expanded tree depth) stays within CONFIG.select.max_goto_inline_depth; keeping the goto is always safe.
                    let target_depth = *depth_of
                        .entry(target_node)
                        .or_insert_with(|| stmt_depth(target_stmt));
                    if depth > 300 && std::env::var("RB2_TRACE").is_ok() {
                        eprintln!(
                            "[rb2] RUNAWAY depth={} target={:x} tdepth={}",
                            depth, target_node, target_depth
                        );
                    }
                    if depth + target_depth <= CONFIG.select.max_goto_inline_depth {
                        visiting.insert(target_node);
                        let (recursed_stmt, mut recursed_nodes) = inline_stmt_recursive_track(
                            target_stmt,
                            owner,
                            statements,
                            preds,
                            predecessor_nodes,
                            protected_targets,
                            visiting,
                            depth + 1,
                            depth_of,
                        );
                        recursed_nodes.push(target_node);
                        return (recursed_stmt, recursed_nodes);
                    }
                }
            }

            (stmt.clone(), vec![])
        }
        _ => inline_stmt_recursive_track(
            stmt,
            owner,
            statements,
            preds,
            predecessor_nodes,
            protected_targets,
            visiting,
            depth,
            depth_of,
        ),
    }
}

fn is_trivial_labeled_goto(stmt: &ClightStmt) -> bool {
    match stmt {
        ClightStmt::Slabel(_, inner) => matches!(**inner, ClightStmt::Sgoto(_)),
        ClightStmt::Sgoto(_) => true,
        _ => false,
    }
}

fn collect_goto_targets(stmt: &ClightStmt) -> Vec<Node> {
    let mut targets = Vec::new();
    collect_goto_targets_recursive(stmt, &mut targets);
    targets
}

/// Every compound assembler uses this function-wide target set before it
/// absorbs nodes.  A selected `Sgoto` owns an exact target identity until a
/// later layout pass proves the edge is an adjacent fallthrough.
fn function_goto_targets(statements: &HashMap<Node, ClightStmt>) -> HashSet<Node> {
    statements.values().flat_map(collect_goto_targets).collect()
}

fn collect_goto_targets_recursive(stmt: &ClightStmt, targets: &mut Vec<Node>) {
    match stmt {
        ClightStmt::Sgoto(target) => {
            targets.push(*target as u64);
        }
        ClightStmt::Sifthenelse(_, then_stmt, else_stmt) => {
            collect_goto_targets_recursive(then_stmt, targets);
            collect_goto_targets_recursive(else_stmt, targets);
        }
        ClightStmt::Sloop(body, incr) => {
            collect_goto_targets_recursive(body, targets);
            collect_goto_targets_recursive(incr, targets);
        }
        ClightStmt::Ssequence(stmts) => {
            for s in stmts {
                collect_goto_targets_recursive(s, targets);
            }
        }
        ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner) => {
            collect_goto_targets_recursive(inner, targets);
        }
        ClightStmt::Sswitch(_, cases) => {
            for (_, s) in cases {
                collect_goto_targets_recursive(s, targets);
            }
        }
        _ => {}
    }
}

fn collect_label_defs_recursive(stmt: &ClightStmt, labels: &mut HashSet<usize>) {
    match stmt {
        ClightStmt::Seffect(_, inner) => collect_label_defs_recursive(inner, labels),
        ClightStmt::Slabel(lbl, inner) => {
            labels.insert(*lbl);
            collect_label_defs_recursive(inner, labels);
        }
        ClightStmt::Sifthenelse(_, then_stmt, else_stmt) => {
            collect_label_defs_recursive(then_stmt, labels);
            collect_label_defs_recursive(else_stmt, labels);
        }
        ClightStmt::Sloop(body, incr) => {
            collect_label_defs_recursive(body, labels);
            collect_label_defs_recursive(incr, labels);
        }
        ClightStmt::Ssequence(stmts) => {
            for s in stmts {
                collect_label_defs_recursive(s, labels);
            }
        }
        ClightStmt::Sswitch(_, cases) => {
            for (_, s) in cases {
                collect_label_defs_recursive(s, labels);
            }
        }
        _ => {}
    }
}

fn stmt_contains_label(stmt: &ClightStmt, target_label: usize) -> bool {
    match stmt {
        ClightStmt::Seffect(_, inner) => stmt_contains_label(inner, target_label),
        ClightStmt::Slabel(lbl, inner) => {
            *lbl == target_label || stmt_contains_label(inner, target_label)
        }
        ClightStmt::Sifthenelse(_, then_stmt, else_stmt) => {
            stmt_contains_label(then_stmt, target_label)
                || stmt_contains_label(else_stmt, target_label)
        }
        ClightStmt::Sloop(body, incr) => {
            stmt_contains_label(body, target_label) || stmt_contains_label(incr, target_label)
        }
        ClightStmt::Ssequence(stmts) => stmts.iter().any(|s| stmt_contains_label(s, target_label)),
        ClightStmt::Sswitch(_, cases) => cases
            .iter()
            .any(|(_, s)| stmt_contains_label(s, target_label)),
        _ => false,
    }
}

fn ensure_goto_labels(statements: &mut HashMap<Node, ClightStmt>) {
    let mut goto_targets: HashSet<usize> = HashSet::new();
    let mut label_defs: HashSet<usize> = HashSet::new();
    for stmt in statements.values() {
        for target_node in collect_goto_targets(stmt) {
            goto_targets.insert(target_node as usize);
        }
        collect_label_defs_recursive(stmt, &mut label_defs);
    }

    let mut missing: Vec<usize> = goto_targets.difference(&label_defs).copied().collect();
    missing.sort();
    for label_ident in missing {
        let already_nested = statements
            .values()
            .any(|s| stmt_contains_label(s, label_ident));
        if already_nested {
            continue;
        }

        let node = label_ident as Node;
        if let Some(stmt) = statements.get(&node) {
            let wrapped = ClightStmt::Slabel(label_ident, Box::new(stmt.clone()));
            statements.insert(node, wrapped);
        } else {
            statements.insert(
                node,
                ClightStmt::Slabel(label_ident, Box::new(ClightStmt::Sskip)),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::decompile::passes::clight_select::select::*;
    use std::sync::Arc;

    fn synthetic_ids<const N: usize>() -> [u64; N] {
        std::array::from_fn(|index| index as u64 + 1)
    }

    fn test_expr() -> ClightExpr {
        ClightExpr::EconstInt(
            1,
            ClightType::Tint(
                ClightIntSize::I32,
                ClightSignedness::Signed,
                ClightAttr::default(),
            ),
        )
    }

    #[test]
    fn effect_identity_does_not_hide_an_existing_goto_label() {
        let target = 900_u64;
        let marked = ClightStmt::Seffect(crate::decompile::effects::EffectSite {
            function:1,node:target,epoch:0,alternative:0,
        }, Box::new(ClightStmt::Slabel(target as Ident,Box::new(ClightStmt::Sset(1,test_expr())))));
        let mut statements = HashMap::from([(10,ClightStmt::Sgoto(target as Ident)),(target,marked.clone())]);
        ensure_goto_labels(&mut statements);
        assert_eq!(statements[&target],marked);
        assert!(stmt_contains_label(&statements[&target],target as Ident));
    }

    #[test]
    fn rtl_superset_fallback_prefers_the_authoritative_subword_chunk() {
        let address = ClightExpr::Etempvar(
            1,
            ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default()),
        );
        let signed_ty =
            crate::decompile::passes::csh_pass::clight_type_from_chunk(&MemoryChunk::MInt8Signed);
        let unsigned_ty =
            crate::decompile::passes::csh_pass::clight_type_from_chunk(&MemoryChunk::MInt8Unsigned);
        let assert_prefers_unsigned = |signed: ClightStmt, unsigned: ClightStmt| {
            let mut candidates = vec![signed, unsigned.clone()];
            let authoritative = Some(MemoryChunk::MInt8Unsigned);
            let has_authoritative = candidates
                .iter()
                .any(|stmt| stmt_matches_authoritative_chunk(stmt, authoritative.unwrap()));
            candidates.sort_by_key(|stmt| {
                (
                    superset_provenance_priority(stmt, authoritative, has_authoritative),
                    stmt_deterministic_hash(stmt),
                )
            });
            assert_eq!(candidates[0], unsigned);
        };

        assert_prefers_unsigned(
            ClightStmt::Sset(
                2,
                ClightExpr::Ederef(Box::new(address.clone()), signed_ty.clone()),
            ),
            ClightStmt::Sset(
                2,
                ClightExpr::Ederef(Box::new(address.clone()), unsigned_ty.clone()),
            ),
        );
        assert_prefers_unsigned(
            ClightStmt::Sset(2, ClightExpr::Evar(9, signed_ty.clone())),
            ClightStmt::Sset(2, ClightExpr::Evar(9, unsigned_ty.clone())),
        );
        assert_prefers_unsigned(
            ClightStmt::Sset(2, ClightExpr::Etempvar(9, signed_ty.clone())),
            ClightStmt::Sset(2, ClightExpr::Etempvar(9, unsigned_ty.clone())),
        );
        assert_prefers_unsigned(
            ClightStmt::Sset(
                2,
                ClightExpr::Efield(Box::new(address.clone()), 3, signed_ty.clone()),
            ),
            ClightStmt::Sset(
                2,
                ClightExpr::Efield(Box::new(address.clone()), 3, unsigned_ty.clone()),
            ),
        );

        // Store provenance comes from the LHS.  An unrelated authoritative-type
        // dereference in the RHS must not make the signed LHS look preferred.
        let rhs = ClightExpr::Ederef(Box::new(address.clone()), unsigned_ty.clone());
        assert_prefers_unsigned(
            ClightStmt::Sassign(
                ClightExpr::Ederef(Box::new(address.clone()), signed_ty),
                rhs.clone(),
            ),
            ClightStmt::Sassign(ClightExpr::Ederef(Box::new(address), unsigned_ty), rhs),
        );
    }

    #[test]
    fn final_stage_c_global_disagreement_becomes_interface_feedback() {
        let address = 1;
        let symbol = 0x9000usize;
        let load = 0x10;
        let use_ = 0x11;
        let int_ty = ClightType::Tint(
            ClightIntSize::I32,
            ClightSignedness::Signed,
            ClightAttr::default(),
        );
        let float_ty = ClightType::Tfloat(ClightFloatSize::F64, ClightAttr::default());
        let mut func = FunctionData::new(
            address,
            "feedback".into(),
            Vec::new(),
            Vec::new(),
            None,
            0,
            load,
            true,
        );
        func.node_statements.insert(
            load,
            vec![ClightStmt::Sset(
                5,
                ClightExpr::Evar(symbol, int_ty.clone()),
            )],
        );
        func.node_statements.insert(
            use_,
            vec![ClightStmt::Sset(
                6,
                ClightExpr::Etempvar(5, float_ty.clone()),
            )],
        );
        func.flow_blocks = vec![vec![load, use_]];
        func.flow_anchors.global.insert(
            symbol,
            crate::decompile::passes::clight_select::solvers::flow::claim_of_type(&int_ty, true),
        );
        let state = ProgramSelectionState {
            candidate_idx: HashMap::new(),
            structure_world: HashMap::new(),
            var_decl_idx: HashMap::new(),
            var_type_override: HashMap::new(),
            analysis_results: BTreeMap::new(),
        };
        let feedback = committed_global_flow_feedback(&[func], &state);
        assert_eq!(feedback.len(), 1, "{feedback:?}");
        assert_eq!(feedback[0].function, address);
        assert_eq!(feedback[0].node, use_);
        assert_eq!(feedback[0].symbol, symbol);
        assert_eq!(
            feedback[0].claimed,
            crate::decompile::passes::clight_select::solvers::flow::claim_of_type(&float_ty, true)
        );
    }

    fn guarded_goto(exit_target: Node, continue_target: Node) -> ClightStmt {
        ClightStmt::Sifthenelse(
            test_expr(),
            Box::new(ClightStmt::Sgoto(ident_from_node(exit_target))),
            Box::new(ClightStmt::Sgoto(ident_from_node(continue_target))),
        )
    }

    fn has_break(stmt: &ClightStmt) -> bool {
        match stmt {
            ClightStmt::Sbreak => true,
            ClightStmt::Ssequence(stmts) => stmts.iter().any(has_break),
            ClightStmt::Sifthenelse(_, then_stmt, else_stmt) => {
                has_break(then_stmt) || has_break(else_stmt)
            }
            ClightStmt::Sloop(body, incr) => has_break(body) || has_break(incr),
            ClightStmt::Slabel(_, inner) => has_break(inner),
            ClightStmt::Sswitch(_, cases) => cases.iter().any(|(_, stmt)| has_break(stmt)),
            _ => false,
        }
    }

    fn has_loop(stmt: &ClightStmt) -> bool {
        match stmt {
            ClightStmt::Sloop(..) => true,
            ClightStmt::Ssequence(stmts) => stmts.iter().any(has_loop),
            ClightStmt::Sifthenelse(_, then_stmt, else_stmt) => {
                has_loop(then_stmt) || has_loop(else_stmt)
            }
            ClightStmt::Slabel(_, inner) => has_loop(inner),
            ClightStmt::Sswitch(_, cases) => cases.iter().any(|(_, stmt)| has_loop(stmt)),
            _ => false,
        }
    }

    fn stmt_contains_tempvar(stmt: &ClightStmt, target: Ident) -> bool {
        fn expr_contains_tempvar(expr: &ClightExpr, target: Ident) -> bool {
            match expr {
                ClightExpr::Etempvar(reg, _) => *reg == target,
                ClightExpr::Ederef(inner, _)
                | ClightExpr::Eaddrof(inner, _)
                | ClightExpr::Eunop(_, inner, _)
                | ClightExpr::Ecast(inner, _)
                | ClightExpr::Efield(inner, _, _) => expr_contains_tempvar(inner, target),
                ClightExpr::Ebinop(_, left, right, _) => {
                    expr_contains_tempvar(left, target) || expr_contains_tempvar(right, target)
                }
                ClightExpr::Econdition(cond, then_expr, else_expr, _) => {
                    expr_contains_tempvar(cond, target)
                        || expr_contains_tempvar(then_expr, target)
                        || expr_contains_tempvar(else_expr, target)
                }
                _ => false,
            }
        }

        walk_stmt_exprs(stmt, &|expr| expr_contains_tempvar(expr, target))
    }

    fn count_label_occurrences(stmt: &ClightStmt, label: Ident) -> usize {
        match stmt {
            ClightStmt::Slabel(existing, inner) => {
                usize::from(*existing == label) + count_label_occurrences(inner, label)
            }
            ClightStmt::Ssequence(stmts) => stmts
                .iter()
                .map(|stmt| count_label_occurrences(stmt, label))
                .sum(),
            ClightStmt::Sifthenelse(_, then_stmt, else_stmt) => {
                count_label_occurrences(then_stmt, label)
                    + count_label_occurrences(else_stmt, label)
            }
            ClightStmt::Sloop(body, incr) => {
                count_label_occurrences(body, label) + count_label_occurrences(incr, label)
            }
            ClightStmt::Sswitch(_, cases) => cases
                .iter()
                .map(|(_, stmt)| count_label_occurrences(stmt, label))
                .sum(),
            _ => 0,
        }
    }

    #[test]
    fn sseq_dead_head_reanchors_and_reports_only_applied_members() {
        let dead_head = 90;
        let first_live = 10;
        let second_live = 70;
        let mut statements = HashMap::from([
            (first_live, ClightStmt::Sgoto(111)),
            (second_live, ClightStmt::Sgoto(222)),
        ]);
        let groups = HashMap::from([(dead_head, vec![dead_head, first_live, second_live])]);

        let applied = assemble_sseq_groups(&mut statements, &groups);

        assert_eq!(
            applied,
            HashMap::from([(first_live, vec![first_live, second_live])])
        );
        assert!(!applied.contains_key(&dead_head));
        assert!(!statements.contains_key(&dead_head));
        assert!(!statements.contains_key(&second_live));
        match statements.get(&first_live) {
            Some(ClightStmt::Ssequence(seq)) => {
                assert!(matches!(
                    seq.as_slice(),
                    [ClightStmt::Sgoto(111), ClightStmt::Sgoto(222)]
                ));
            }
            other => panic!("expected structurally ordered sequence at live anchor: {other:#?}"),
        }
    }

    #[test]
    #[should_panic(expected = "overlapping Clight straight-line groups")]
    fn sseq_selection_rejects_overlapping_handoff() {
        let mut statements = HashMap::from([
            (1, ClightStmt::Sgoto(11)),
            (2, ClightStmt::Sgoto(22)),
            (3, ClightStmt::Sgoto(33)),
        ]);
        let groups = HashMap::from([(1, vec![1, 2]), (3, vec![3, 2])]);
        let _ = assemble_sseq_groups(&mut statements, &groups);
    }

    #[test]
    fn sseq_anchor_survives_unique_predecessor_inlining() {
        let pred = 1;
        let anchor = 10;
        let member = 70;
        let mut statements = HashMap::from([
            (
                pred,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(anchor as Ident)),
                    Box::new(ClightStmt::Sskip),
                ),
            ),
            (anchor, ClightStmt::Sset(1, test_expr())),
            (member, ClightStmt::Sset(2, test_expr())),
        ]);
        let groups = HashMap::from([(anchor, vec![anchor, member])]);
        let applied = assemble_sseq_groups(&mut statements, &groups);
        let protected: HashSet<Node> = applied.keys().copied().collect();
        let successors = HashMap::from([(pred, vec![anchor]), (anchor, vec![member])]);

        let mut unprotected = statements.clone();
        inline_control_flow_bodies(&mut unprotected, &successors, &HashSet::new());
        assert!(
            !unprotected.contains_key(&anchor),
            "the fixture must exercise the generic S5 absorption path"
        );

        inline_control_flow_bodies(&mut statements, &successors, &protected);
        assert_eq!(applied.get(&anchor), Some(&vec![anchor, member]));
        assert!(statements.contains_key(&anchor));
        assert!(collect_goto_targets(statements.get(&pred).unwrap()).contains(&anchor));
    }

    #[test]
    fn sseq_anchor_is_canonical_for_identical_unprotected_block() {
        let anchor = 10;
        let lower_unprotected = 5;
        let body = ClightStmt::Ssequence(vec![
            ClightStmt::Sset(1, test_expr()),
            ClightStmt::Sset(2, test_expr()),
        ]);
        let mut statements = HashMap::from([(lower_unprotected, body.clone()), (anchor, body)]);
        let protected = HashSet::from([anchor]);

        deduplicate_identical_blocks(&mut statements, &protected, &HashMap::new());

        assert!(statements.contains_key(&anchor));
        assert!(!statements.contains_key(&lower_unprotected));
    }

    #[test]
    fn identical_sseq_anchors_are_never_merged() {
        let first_anchor = 10;
        let second_anchor = 20;
        let body = ClightStmt::Ssequence(vec![
            ClightStmt::Sset(1, test_expr()),
            ClightStmt::Sset(2, test_expr()),
        ]);
        let mut statements = HashMap::from([(first_anchor, body.clone()), (second_anchor, body)]);
        let protected = HashSet::from([first_anchor, second_anchor]);

        deduplicate_identical_blocks(&mut statements, &protected, &HashMap::new());

        assert!(statements.contains_key(&first_anchor));
        assert!(statements.contains_key(&second_anchor));
    }

    #[test]
    fn identical_value_blocks_with_different_cfg_successors_stay_distinct() {
        let [first, second_pred, second_next, first_next, second, first_pred] = synthetic_ids();
        let value = ClightStmt::Sset(1, test_expr());
        let mut statements = HashMap::from([
            (first_pred, ClightStmt::Sgoto(ident_from_node(first))),
            (first, value.clone()),
            (first_next, ClightStmt::Sreturn(None)),
            (second_pred, ClightStmt::Sgoto(ident_from_node(second))),
            (second, value),
            (second_next, ClightStmt::Sreturn(Some(test_expr()))),
        ]);
        let successors = HashMap::from([
            (first_pred, vec![first]),
            (first, vec![first_next]),
            (second_pred, vec![second]),
            (second, vec![second_next]),
        ]);

        deduplicate_identical_blocks(&mut statements, &HashSet::new(), &successors);

        assert!(statements.contains_key(&first));
        assert!(statements.contains_key(&second));
        assert!(collect_goto_targets(statements.get(&first_pred).unwrap()).contains(&first));
        assert!(collect_goto_targets(statements.get(&second_pred).unwrap()).contains(&second));
    }

    #[test]
    fn multiple_loop_exits_keep_distinct_targets() {
        let header = 0x100;
        let first_exit = 0x110;
        let second_exit = 0x120;
        let latch = 0x130;
        let first_raw_target = 0x200;
        let first_target = 0x210;
        let second_target = 0x300;

        let mut statements = HashMap::from([
            (header, ClightStmt::Sskip),
            (first_exit, guarded_goto(first_raw_target, second_exit)),
            (second_exit, guarded_goto(second_target, latch)),
            (latch, ClightStmt::Sgoto(ident_from_node(header))),
            (first_target, ClightStmt::Sreturn(None)),
            (second_target, ClightStmt::Sreturn(None)),
        ]);
        let mut info = LoopInfo::default();
        info.body_nodes = vec![first_exit, second_exit, latch];
        info.exit_targets.insert(first_exit, first_raw_target);
        info.exit_targets.insert(second_exit, second_target);

        assemble_loops(
            &mut statements,
            &HashMap::from([(header, info)]),
            &HashMap::from([
                (first_exit, vec![first_raw_target, second_exit]),
                (second_exit, vec![second_target, latch]),
                (first_raw_target, vec![first_target]),
                (latch, vec![header]),
            ]),
        );

        let assembled = statements.get(&header).expect("loop header retained");
        let targets: HashSet<Node> = collect_goto_targets(assembled).into_iter().collect();
        assert!(
            targets.contains(&first_target),
            "first exit target was lost: {assembled:#?}"
        );
        assert!(
            targets.contains(&second_target),
            "second exit target was lost: {assembled:#?}"
        );
        assert!(
            !has_break(assembled),
            "non-primary exits collapsed to break: {assembled:#?}"
        );
    }

    #[test]
    fn a_selected_primary_exit_without_an_inside_target_has_no_continue_frontier() {
        use crate::decompile::passes::clight_select::query::PrimaryExitData;
        fn has_return(stmt: &ClightStmt) -> bool {
            match stmt {
                ClightStmt::Sreturn(_) => true,
                ClightStmt::Slabel(_,inner) => has_return(inner),
                ClightStmt::Ssequence(items) => items.iter().any(has_return),
                ClightStmt::Sloop(body,step) => has_return(body) || has_return(step),
                ClightStmt::Sifthenelse(_,yes,no) => has_return(yes) || has_return(no),
                ClightStmt::Sswitch(_,cases) => cases.iter().any(|(_,stmt)| has_return(stmt)),
                _ => false,
            }
        }
        for exits_by_return in [false,true] {
            let (header,exit,outside) = (0x100_u64,0x110_u64,0x200_u64);
            let exit_stmt = if exits_by_return { ClightStmt::Sreturn(None) }
                else { ClightStmt::Sgoto(ident_from_node(outside)) };
            let mut statements = HashMap::from([
                (header,ClightStmt::Sset(1,test_expr())),
                (exit,exit_stmt), (outside,ClightStmt::Sreturn(None)),
            ]);
            let info = LoopInfo { body_nodes: vec![exit],
                primary_exit: Some(PrimaryExitData { exit_node: exit,
                    exit_target: (!exits_by_return).then_some(outside) }),
                ..LoopInfo::default()
            };
            let successors = HashMap::from([(header,vec![exit]),
                (exit,if exits_by_return { vec![] } else { vec![outside] })]);
            assemble_loops(&mut statements,&HashMap::from([(header,info)]),&successors);
            assert!(!statements.is_empty());
            assert!(statements.values().any(has_return),"selected return was lost: {statements:?}");
        }
    }

    #[test]
    fn nonprimary_loop_exit_preserves_selected_guard_expression() {
        let [header, exit_node, outside] = synthetic_ids();
        let selected_reg = 0xfeed;
        let ty = ClightType::Tint(
            ClightIntSize::I32,
            ClightSignedness::Signed,
            ClightAttr::default(),
        );
        let selected_guard = ClightExpr::Etempvar(selected_reg, ty);
        let mut statements = HashMap::from([
            (header, ClightStmt::Sskip),
            (
                exit_node,
                ClightStmt::Sifthenelse(
                    selected_guard,
                    Box::new(ClightStmt::Sgoto(ident_from_node(outside))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(header))),
                ),
            ),
            (outside, ClightStmt::Sreturn(None)),
        ]);
        let mut info = LoopInfo::default();
        info.body_nodes = vec![exit_node];
        info.exit_targets.insert(exit_node, outside);

        assemble_loops(
            &mut statements,
            &HashMap::from([(header, info)]),
            &HashMap::from([(exit_node, vec![outside, header])]),
        );

        let assembled = statements.get(&header).expect("loop header retained");
        assert!(
            has_loop(assembled),
            "loop was not assembled: {assembled:#?}"
        );
        assert!(
            stmt_contains_tempvar(assembled, selected_reg),
            "loop assembly replaced the solver-selected guard: {assembled:#?}"
        );
    }

    #[test]
    fn nonprimary_loop_exit_uses_selected_structural_target_over_stale_candidate_target() {
        let [selected_outside, header, stale_target, exit_node, _unused_a, _unused_b] =
            synthetic_ids();
        let mut statements = HashMap::from([
            (header, ClightStmt::Sskip),
            (
                exit_node,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(selected_outside))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(header))),
                ),
            ),
            (selected_outside, ClightStmt::Sreturn(None)),
            (
                stale_target,
                ClightStmt::Sgoto(ident_from_node(selected_outside)),
            ),
        ]);
        let mut info = LoopInfo::default();
        info.body_nodes = vec![exit_node];
        // Another upstream candidate reaches the same outside path through a
        // transparent shim, but it is not the candidate selected above.
        info.exit_targets.insert(exit_node, stale_target);

        assemble_loops(
            &mut statements,
            &HashMap::from([(header, info)]),
            &HashMap::from([
                (exit_node, vec![selected_outside, header]),
                (stale_target, vec![selected_outside]),
            ]),
        );

        let assembled = statements.get(&header).expect("loop header retained");
        assert!(
            has_loop(assembled),
            "selected exit target was rejected in favor of stale candidate metadata: {assembled:#?}"
        );
        assert!(
            collect_goto_targets(assembled).contains(&selected_outside),
            "selected outside edge was lost: {assembled:#?}"
        );
    }

    #[test]
    fn selected_away_loop_header_uses_unique_live_body_frontier() {
        let [header, body, latch, exit] = synthetic_ids();
        let mut statements = HashMap::from([
            (header, ClightStmt::Sskip),
            (body, ClightStmt::Sset(1, test_expr())),
            (
                latch,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(exit))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(body))),
                ),
            ),
            (exit, ClightStmt::Sreturn(None)),
        ]);
        let mut info = LoopInfo::default();
        info.body_nodes = vec![body, latch];
        info.primary_exit = Some(
            crate::decompile::passes::clight_select::query::PrimaryExitData {
                exit_node: latch,
                exit_target: Some(exit),
            },
        );

        assemble_loops(
            &mut statements,
            &HashMap::from([(header, info)]),
            &HashMap::from([(latch, vec![exit, header])]),
        );

        let assembled = statements.get(&header).expect("loop header retained");
        assert!(
            has_loop(assembled),
            "loop was not assembled: {assembled:#?}"
        );
        assert!(!statements.contains_key(&body));
        assert!(!statements.contains_key(&latch));
    }

    // A pre-tested loop's exit test IS the header, so its in-loop arm is the
    // element after the header, not the loop-back frontier.  Binding continue
    // to that arm re-runs the test on unchanged state and never leaves.
    #[test]
    fn pre_tested_header_keeps_its_in_loop_arm_out_of_continue() {
        let header = 0x400;
        let step = 0x410;
        let latch = 0x420;
        let exit = 0x500;
        let mut statements = HashMap::from([
            (
                header,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(exit))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(step))),
                ),
            ),
            (
                step,
                ClightStmt::Slabel(
                    ident_from_node(step),
                    Box::new(ClightStmt::Sset(1, test_expr())),
                ),
            ),
            (latch, ClightStmt::Sgoto(ident_from_node(header))),
            (exit, ClightStmt::Sreturn(None)),
        ]);
        let mut info = LoopInfo::default();
        info.body_nodes = vec![step, latch];
        info.primary_exit = Some(
            crate::decompile::passes::clight_select::query::PrimaryExitData {
                exit_node: header,
                exit_target: Some(exit),
            },
        );

        assemble_loops(
            &mut statements,
            &HashMap::from([(header, info)]),
            &HashMap::from([
                (header, vec![exit, step]),
                (step, vec![latch]),
                (latch, vec![header]),
            ]),
        );

        let assembled = statements.get(&header).expect("loop header retained");
        assert!(
            has_loop(assembled),
            "loop was not assembled: {assembled:#?}"
        );
        assert!(
            collect_goto_targets(assembled).contains(&step),
            "the header's in-loop arm collapsed onto continue: {assembled:#?}"
        );
        assert_eq!(
            count_label_occurrences(assembled, ident_from_node(step)),
            1,
            "the body statement the header branches to was dropped: {assembled:#?}"
        );
    }

    #[test]
    fn straight_line_common_return_is_duplicated_after_its_exact_assignment() {
        let [value, bridge, ret] = synthetic_ids();
        let ty = crate::decompile::passes::csh_pass::default_int_type();
        let mut statements = HashMap::from([
            (value, ClightStmt::Sset(7, test_expr())),
            (bridge, ClightStmt::Sgoto(ident_from_node(ret))),
            (ret, ClightStmt::Sreturn(Some(ClightExpr::Etempvar(7, ty)))),
        ]);
        let successors = HashMap::from([(value, vec![bridge]), (bridge, vec![ret])]);

        duplicate_straight_line_return_tails(&mut statements, &successors);

        assert!(matches!(
            statements.get(&value),
            Some(ClightStmt::Ssequence(seq))
                if matches!(seq.as_slice(), [ClightStmt::Sset(7, _), ClightStmt::Sreturn(Some(ClightExpr::Etempvar(7, _)))])
        ));
    }

    #[test]
    fn duplicated_sequence_tail_replaces_only_its_terminal_goto_with_return() {
        let [value, bridge, ret] = synthetic_ids();
        let ty = crate::decompile::passes::csh_pass::default_int_type();
        let side_effect = ClightStmt::Sassign(ClightExpr::Etempvar(9, ty.clone()), test_expr());
        let mut statements = HashMap::from([
            (
                value,
                ClightStmt::Ssequence(vec![
                    side_effect.clone(),
                    ClightStmt::Sset(7, test_expr()),
                    ClightStmt::Sgoto(ident_from_node(bridge)),
                ]),
            ),
            (bridge, ClightStmt::Sgoto(ident_from_node(ret))),
            (ret, ClightStmt::Sreturn(Some(ClightExpr::Etempvar(7, ty)))),
        ]);
        let successors = HashMap::from([(value, vec![bridge]), (bridge, vec![ret])]);

        duplicate_straight_line_return_tails(&mut statements, &successors);

        assert!(matches!(
            statements.get(&value),
            Some(ClightStmt::Ssequence(seq))
                if seq.first() == Some(&side_effect)
                    && matches!(seq.last(), Some(ClightStmt::Sreturn(Some(ClightExpr::Etempvar(7, _)))))
        ));
    }

    #[test]
    fn selected_away_target_resolves_to_next_sequential_loop() {
        let outer_branch = 0x300;
        let header = 0x400;
        let body = 0x410;
        let raw_target = 0x500;
        let target = 0x510;
        let alternate = 0x520;
        let join = 0x530;
        let mut statements = HashMap::from([
            (
                outer_branch,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(header))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(alternate))),
                ),
            ),
            (
                header,
                ClightStmt::Slabel(
                    ident_from_node(header),
                    Box::new(ClightStmt::Sifthenelse(
                        test_expr(),
                        Box::new(ClightStmt::Sgoto(ident_from_node(raw_target))),
                        Box::new(ClightStmt::Sgoto(ident_from_node(body))),
                    )),
                ),
            ),
            (body, ClightStmt::Sgoto(ident_from_node(header))),
            (target, ClightStmt::Sset(1, test_expr())),
            (alternate, ClightStmt::Sgoto(ident_from_node(join))),
            (join, ClightStmt::Sreturn(None)),
        ]);
        let mut info = LoopInfo::default();
        info.body_nodes = vec![body];
        info.primary_exit = Some(
            crate::decompile::passes::clight_select::query::PrimaryExitData {
                exit_node: header,
                exit_target: Some(raw_target),
            },
        );

        assemble_loops(
            &mut statements,
            &HashMap::from([(header, info)]),
            &HashMap::from([(body, vec![header]), (raw_target, vec![target])]),
        );

        assert!(
            collect_goto_targets(statements.get(&header).expect("loop header retained"))
                .contains(&target)
        );
        assert!(
            !collect_goto_targets(statements.get(&header).unwrap()).contains(&raw_target),
            "selected-away primary target remained as a dangling goto"
        );

        assemble_ite(
            &mut statements,
            &HashMap::from([(
                outer_branch,
                IteInfo {
                    true_body_nodes: vec![header, target],
                    false_body_nodes: vec![alternate],
                    join_node: Some(join),
                    no_join: false,
                },
            )]),
            &HashMap::new(),
        );

        let assembled = statements
            .get(&outer_branch)
            .expect("outer branch retained");
        assert!(
            stmt_contains_label(assembled, ident_from_node(target)),
            "loop exit target label was stripped by ITE assembly: {assembled:#?}"
        );
        assert!(!statements.contains_key(&target));
    }

    #[test]
    fn ambiguous_absent_exit_target_declines_loop_assembly() {
        let header = 0x800;
        let exit = 0x810;
        let latch = 0x820;
        let raw_target = 0x900;
        let mut statements = HashMap::from([
            (header, ClightStmt::Sskip),
            (exit, guarded_goto(raw_target, latch)),
            (latch, ClightStmt::Sgoto(ident_from_node(header))),
            (0x910, ClightStmt::Sreturn(None)),
            (0x920, ClightStmt::Sreturn(None)),
        ]);
        let mut info = LoopInfo::default();
        info.body_nodes = vec![exit, latch];
        info.exit_targets.insert(exit, raw_target);

        assemble_loops(
            &mut statements,
            &HashMap::from([(header, info)]),
            &HashMap::from([(raw_target, vec![0x910, 0x920]), (latch, vec![header])]),
        );

        assert_eq!(statements.get(&header), Some(&ClightStmt::Sskip));
        assert!(statements.contains_key(&exit));
    }

    #[test]
    fn equivalent_nonprimary_exit_uses_primary_break_target() {
        let header = 0x980;
        let alternate_exit = 0x990;
        let primary_exit = 0x9a0;
        let primary_target = 0x9b0;
        let alternate_target = 0x9c0;
        let primary_bridge = 0x9d0;
        let continuation = 0x9e0;
        let value_stmt = || ClightStmt::Sset(1, test_expr());
        let mut statements = HashMap::from([
            (header, ClightStmt::Sskip),
            (alternate_exit, guarded_goto(alternate_target, primary_exit)),
            (
                primary_exit,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(primary_target))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(header))),
                ),
            ),
            (
                primary_target,
                ClightStmt::Slabel(ident_from_node(primary_target), Box::new(value_stmt())),
            ),
            (
                alternate_target,
                ClightStmt::Slabel(ident_from_node(alternate_target), Box::new(value_stmt())),
            ),
            (
                primary_bridge,
                ClightStmt::Sgoto(ident_from_node(continuation)),
            ),
            (continuation, ClightStmt::Sreturn(None)),
        ]);
        let mut info = LoopInfo::default();
        info.body_nodes = vec![alternate_exit, primary_exit];
        info.exit_targets.insert(alternate_exit, alternate_target);
        info.primary_exit = Some(
            crate::decompile::passes::clight_select::query::PrimaryExitData {
                exit_node: primary_exit,
                exit_target: Some(primary_target),
            },
        );
        let successors = HashMap::from([
            (alternate_exit, vec![alternate_target, primary_exit]),
            (alternate_target, vec![continuation]),
            (primary_exit, vec![primary_target, header]),
            (primary_target, vec![primary_bridge]),
            (primary_bridge, vec![continuation]),
        ]);

        assemble_loops(
            &mut statements,
            &HashMap::from([(header, info)]),
            &successors,
        );

        let assembled = statements.get(&header).expect("loop header retained");
        let targets = collect_goto_targets(assembled);
        assert!(has_break(assembled));
        assert!(targets.contains(&primary_target));
        assert!(!targets.contains(&alternate_target));
        assert!(
            !statements.contains_key(&alternate_target),
            "single-predecessor equivalent target was not absorbed"
        );
    }

    #[test]
    fn exit_target_equivalence_rejects_unproven_paths() {
        let primary = 0xaa0;
        let alternate = 0xab0;
        let continuation = 0xac0;
        let other_continuation = 0xad0;
        let body_nodes = HashSet::new();
        let same_effect = ClightStmt::Sset(1, test_expr());
        let base_statements = HashMap::from([
            (
                primary,
                ClightStmt::Slabel(ident_from_node(primary), Box::new(same_effect.clone())),
            ),
            (alternate, same_effect.clone()),
            (continuation, ClightStmt::Sreturn(None)),
            (other_continuation, ClightStmt::Sreturn(None)),
        ]);
        let base_successors = HashMap::from([
            (primary, vec![continuation]),
            (alternate, vec![continuation]),
        ]);
        let single_pred = HashMap::from([(alternate, 1)]);
        assert!(can_share_primary_exit_target(
            alternate,
            primary,
            &base_statements,
            &base_successors,
            &body_nodes,
            &single_pred,
        ));

        let mut different_effect = base_statements.clone();
        different_effect.insert(alternate, ClightStmt::Sset(2, test_expr()));
        assert!(!can_share_primary_exit_target(
            alternate,
            primary,
            &different_effect,
            &base_successors,
            &body_nodes,
            &single_pred,
        ));

        let different_successor = HashMap::from([
            (primary, vec![continuation]),
            (alternate, vec![other_continuation]),
        ]);
        assert!(!can_share_primary_exit_target(
            alternate,
            primary,
            &base_statements,
            &different_successor,
            &body_nodes,
            &single_pred,
        ));

        let ambiguous_successor = HashMap::from([
            (primary, vec![continuation]),
            (alternate, vec![continuation, other_continuation]),
        ]);
        assert!(!can_share_primary_exit_target(
            alternate,
            primary,
            &base_statements,
            &ambiguous_successor,
            &body_nodes,
            &single_pred,
        ));

        assert!(!can_share_primary_exit_target(
            alternate,
            primary,
            &base_statements,
            &base_successors,
            &body_nodes,
            &HashMap::from([(alternate, 2)]),
        ));
    }

    #[test]
    fn loop_assembly_keeps_preheader_and_external_member_gotos() {
        let preheader = 0xa00;
        let external_reentry = 0xa08;
        let header = 0xa10;
        let member = 0xa20;
        let latch = 0xa30;
        let mut statements = HashMap::from([
            (preheader, ClightStmt::Sgoto(ident_from_node(header))),
            (external_reentry, ClightStmt::Sgoto(ident_from_node(member))),
            (
                header,
                ClightStmt::Slabel(ident_from_node(header), Box::new(ClightStmt::Sskip)),
            ),
            (
                member,
                ClightStmt::Slabel(
                    ident_from_node(member),
                    Box::new(ClightStmt::Sset(1, test_expr())),
                ),
            ),
            (latch, ClightStmt::Sgoto(ident_from_node(header))),
        ]);
        let mut info = LoopInfo::default();
        info.body_nodes = vec![member, latch];

        assemble_loops(
            &mut statements,
            &HashMap::from([(header, info)]),
            &HashMap::from([(latch, vec![header])]),
        );

        assert!(matches!(
            statements.get(&preheader),
            Some(ClightStmt::Sgoto(target)) if *target == ident_from_node(header)
        ));
        assert!(matches!(
            statements.get(&external_reentry),
            Some(ClightStmt::Sgoto(target)) if *target == ident_from_node(member)
        ));
        let assembled = statements.get(&header).expect("loop header retained");
        assert_eq!(
            count_label_occurrences(assembled, ident_from_node(header)),
            1,
            "loop header label was duplicated inside its own body: {assembled:#?}"
        );
        assert!(
            stmt_contains_label(assembled, ident_from_node(member)),
            "external entry target label was stripped from loop body: {assembled:#?}"
        );
    }

    #[test]
    fn empty_ite_arm_uses_the_structural_join_as_compound_continuation() {
        let branch = 0xb00;
        let body = 0xb10;
        let join = 0xb20;
        let mut statements = HashMap::from([
            (
                branch,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(join))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(body))),
                ),
            ),
            (body, ClightStmt::Sset(1, test_expr())),
            (join, ClightStmt::Sreturn(None)),
        ]);

        let successors = HashMap::from([(branch, vec![join, body]), (body, vec![join])]);
        assemble_ite(
            &mut statements,
            &HashMap::from([(
                branch,
                IteInfo {
                    true_body_nodes: Vec::new(),
                    false_body_nodes: vec![body],
                    join_node: Some(join),
                    no_join: false,
                },
            )]),
            &successors,
        );

        // Both sides reach the join, so both encode it.  Assembly cannot see
        // what the emitter will print after the compound, so neither edge may
        // be left to adjacency here; goto_elide removes whichever one the
        // final layout makes redundant.
        let assembled = statements.get(&branch).expect("branch retained");
        assert_eq!(
            collect_goto_targets(assembled),
            vec![join, join],
            "an ITE arm dropped its exact edge to the join: {assembled:#?}"
        );

        // Every path out of the compound is now explicit, so the boundary has
        // no fallthrough left to materialize and no duplicate goto appears.
        materialize_cfg_fallthrough_gotos(&mut statements, &successors);
        let assembled = statements.get(&branch).expect("branch retained");
        assert_eq!(
            collect_goto_targets(assembled),
            vec![join, join],
            "the compound boundary duplicated an already-explicit edge: {assembled:#?}"
        );
    }

    #[test]
    fn terminal_forwarding_bridge_to_ite_join_keeps_its_exact_edge() {
        let [branch, body, bridge, other, join] = synthetic_ids();
        let mut statements = HashMap::from([
            (
                branch,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(body))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(other))),
                ),
            ),
            (body, ClightStmt::Sset(1, test_expr())),
            (
                bridge,
                ClightStmt::Slabel(
                    ident_from_node(bridge),
                    Box::new(ClightStmt::Sgoto(ident_from_node(join))),
                ),
            ),
            (other, ClightStmt::Sset(2, test_expr())),
            (join, ClightStmt::Sreturn(None)),
        ]);
        let successors = HashMap::from([
            (branch, vec![body, other]),
            (body, vec![bridge]),
            (bridge, vec![join]),
            (other, vec![join]),
        ]);

        assemble_ite(
            &mut statements,
            &HashMap::from([(
                branch,
                IteInfo {
                    true_body_nodes: vec![body, bridge],
                    false_body_nodes: vec![other],
                    join_node: Some(join),
                    no_join: false,
                },
            )]),
            &successors,
        );

        // A forwarding bridge at the end of an arm is a real CFG edge, not a
        // spelling of "whatever the emitter prints after this compound".  It
        // stays explicit here and only goto_elide, which sees the printed
        // layout, may drop it.
        let assembled = statements.get(&branch).expect("branch retained");
        assert_eq!(
            collect_goto_targets(assembled),
            vec![join, join],
            "a terminal forwarding bridge lost its exact edge to the join: {assembled:#?}"
        );
    }

    #[test]
    fn absorbed_arm_members_do_not_create_a_goto_before_the_live_join_bridge() {
        let [branch, body, absorbed, bridge, other, join] = synthetic_ids();
        let mut statements = HashMap::from([
            (
                branch,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(body))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(other))),
                ),
            ),
            (body, ClightStmt::Sset(1, test_expr())),
            (
                bridge,
                ClightStmt::Slabel(
                    ident_from_node(bridge),
                    Box::new(ClightStmt::Sgoto(ident_from_node(join))),
                ),
            ),
            (other, ClightStmt::Sset(2, test_expr())),
            (join, ClightStmt::Sreturn(None)),
        ]);
        let successors = HashMap::from([
            (branch, vec![body, other]),
            (body, vec![absorbed]),
            (absorbed, vec![bridge]),
            (bridge, vec![join]),
            (other, vec![join]),
        ]);

        assemble_ite(
            &mut statements,
            &HashMap::from([(
                branch,
                IteInfo {
                    true_body_nodes: vec![body, absorbed, bridge],
                    false_body_nodes: vec![other],
                    join_node: Some(join),
                    no_join: false,
                },
            )]),
            &successors,
        );

        // The absorbed member is emitted in arm order immediately before the
        // bridge, so no arm-local goto to the bridge is manufactured.  Only
        // the bridge's own edge to the join, which leaves the compound,
        // survives as a goto.
        let assembled = statements.get(&branch).expect("branch retained");
        assert!(
            !collect_goto_targets(assembled).contains(&bridge),
            "an absorbed metadata member manufactured an arm-local goto: {assembled:#?}"
        );
        assert_eq!(
            collect_goto_targets(assembled),
            vec![join, join],
            "an arm dropped its exact edge to the join: {assembled:#?}"
        );
    }

    #[test]
    fn selected_away_ite_targets_resolve_before_structural_assembly() {
        let branch = 0xb40;
        let true_skip = 0xb50;
        let false_skip = 0xb60;
        let true_live = 0xb70;
        let false_live = 0xb80;
        let mut statements = HashMap::from([
            (
                branch,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(true_skip))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(false_skip))),
                ),
            ),
            (
                true_skip,
                ClightStmt::Slabel(ident_from_node(true_skip), Box::new(ClightStmt::Sskip)),
            ),
            (
                false_skip,
                ClightStmt::Slabel(ident_from_node(false_skip), Box::new(ClightStmt::Sskip)),
            ),
            (true_live, ClightStmt::Sreturn(None)),
            (false_live, ClightStmt::Sset(1, test_expr())),
        ]);
        let successors =
            HashMap::from([(true_skip, vec![true_live]), (false_skip, vec![false_live])]);

        redirect_gotos_through_selected_away_nodes(&mut statements, &successors);
        assemble_ite(
            &mut statements,
            &HashMap::from([(
                branch,
                IteInfo {
                    true_body_nodes: vec![true_skip],
                    false_body_nodes: vec![false_skip],
                    join_node: None,
                    no_join: true,
                },
            )]),
            &successors,
        );

        let targets: HashSet<Node> =
            collect_goto_targets(statements.get(&branch).expect("branch retained"))
                .into_iter()
                .collect();
        assert_eq!(targets, HashSet::from([true_live, false_live]));
    }

    #[test]
    fn nested_ite_keeps_goto_to_target_consumed_by_inner_compound() {
        let later_branch = 0xb00;
        let earlier_branch = 0xc00;
        let consumed_target = 0xd00;
        let unrelated_live_successor = 0xe00;
        let exit = 0xf00;
        let mut statements = HashMap::from([
            (
                earlier_branch,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(consumed_target))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(exit))),
                ),
            ),
            (
                later_branch,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(consumed_target))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(exit))),
                ),
            ),
            (
                consumed_target,
                ClightStmt::Slabel(
                    ident_from_node(consumed_target),
                    Box::new(ClightStmt::Sset(1, test_expr())),
                ),
            ),
            (unrelated_live_successor, ClightStmt::Sreturn(None)),
            (exit, ClightStmt::Sreturn(None)),
        ]);
        let infos = HashMap::from([
            (
                earlier_branch,
                IteInfo {
                    true_body_nodes: vec![consumed_target],
                    false_body_nodes: Vec::new(),
                    join_node: Some(exit),
                    no_join: false,
                },
            ),
            (
                later_branch,
                IteInfo {
                    true_body_nodes: vec![consumed_target],
                    false_body_nodes: Vec::new(),
                    join_node: Some(exit),
                    no_join: false,
                },
            ),
        ]);

        // Both branches were already redirected to CONSUMED_TARGET before
        // ITE assembly, while the immutable raw CFG still records an older
        // route.  The larger tie-break branch is assembled first and moves the
        // target label into its compound.
        assemble_ite(
            &mut statements,
            &infos,
            &HashMap::from([
                (later_branch, vec![0xa00, exit]),
                (0xa00, vec![consumed_target]),
                (consumed_target, vec![unrelated_live_successor]),
            ]),
        );

        let later = statements
            .get(&later_branch)
            .expect("later branch retained");
        let targets = collect_goto_targets(later);
        assert!(
            targets.contains(&consumed_target),
            "edge to nested target label was lost: {later:#?}"
        );
        assert!(
            !targets.contains(&unrelated_live_successor),
            "edge was retargeted through a node consumed by prior assembly: {later:#?}"
        );
        assert_eq!(
            statements
                .values()
                .map(|stmt| count_label_occurrences(stmt, ident_from_node(consumed_target)))
                .sum::<usize>(),
            1,
            "consumed target must retain exactly one nested label definition"
        );
    }

    #[test]
    fn ite_arm_statement_order_follows_cfg_across_synthetic_nodes() {
        let branch = 0xba0;
        let entry = 0x9000;
        let synthetic = (1_u64 << 62) | 0x9001;
        let tail = 0x0100;
        let false_live = 0x0200;
        let exit = 0x0300;
        let first = ClightStmt::Sset(1, test_expr());
        let second = ClightStmt::Sset(2, test_expr());
        let jump = ClightStmt::Sgoto(ident_from_node(exit));
        let mut statements = HashMap::from([
            (
                branch,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(entry))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(false_live))),
                ),
            ),
            (entry, first.clone()),
            (synthetic, second.clone()),
            (tail, jump.clone()),
            (false_live, ClightStmt::Sreturn(None)),
            (exit, ClightStmt::Sreturn(None)),
        ]);

        // Deliberately use the numeric set order: TAIL sorts before ENTRY and
        // the tagged synthetic node sorts last, while CFG execution is
        // ENTRY -> SYNTHETIC -> TAIL.
        assemble_ite(
            &mut statements,
            &HashMap::from([(
                branch,
                IteInfo {
                    true_body_nodes: vec![tail, entry, synthetic],
                    false_body_nodes: Vec::new(),
                    join_node: Some(exit),
                    no_join: false,
                },
            )]),
            &HashMap::from([
                (branch, vec![entry, false_live]),
                (entry, vec![synthetic]),
                (synthetic, vec![tail]),
                (tail, vec![exit]),
            ]),
        );

        let assembled = statements.get(&branch).expect("branch retained");
        let then_body = match assembled {
            ClightStmt::Sifthenelse(_, then_body, _) => then_body.as_ref(),
            other => panic!("expected assembled ITE, got {other:#?}"),
        };
        // ENTRY and SYNTHETIC keep CFG order, and TAIL's transfer to the join
        // stays exact: assembly cannot see what the emitter prints after the
        // compound, so the edge is only dropped later, by goto_elide, and only
        // when the printed layout really places the join next.
        assert_eq!(
            then_body,
            &ClightStmt::Ssequence(vec![first, second, jump]),
            "ITE arm used node magnitude instead of structural CFG order, or dropped its terminal join transfer"
        );
    }

    #[test]
    fn ite_arm_orders_out_of_line_guard_before_its_shared_body() {
        let [shared_body, join, arm_entry, out_of_line_guard] = synthetic_ids();

        // ARM_ENTRY can enter SHARED_BODY directly or visit GUARD first; the
        // guard's continuing edge then converges on SHARED_BODY.  A preorder
        // walk which chooses the numerically smaller body first emits
        // ENTRY, BODY, GUARD and changes BODY's exit fallthrough into a trip
        // through GUARD.  The structural order is ENTRY, GUARD, BODY.
        let ordered = order_ite_arm_nodes(
            &[shared_body, arm_entry, out_of_line_guard],
            Some(arm_entry),
            &HashMap::from([
                (arm_entry, vec![shared_body, out_of_line_guard]),
                (out_of_line_guard, vec![join, shared_body]),
                (shared_body, vec![join]),
            ]),
        );

        assert_eq!(ordered, vec![arm_entry, out_of_line_guard, shared_body]);
    }

    #[test]
    fn ite_assembly_materializes_transfers_leaving_moved_arms() {
        let branch = 0x6000;
        let stop_effect = 0x9000;
        let stop_jump = 0x9010;
        let continuing_effect = 0x1000;
        let continuing_tail = 0x1010;
        let continuation = 0x2000;
        let stop = 0x3000;
        let effect = ClightStmt::Sset(1, test_expr());
        let mut statements = HashMap::from([
            (
                branch,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(stop_effect))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(continuing_effect))),
                ),
            ),
            (stop_effect, effect.clone()),
            (stop_jump, ClightStmt::Sgoto(ident_from_node(stop))),
            (continuing_effect, effect.clone()),
            (continuing_tail, effect),
            (continuation, ClightStmt::Sreturn(None)),
            (stop, ClightStmt::Sreturn(None)),
        ]);
        let successors = HashMap::from([
            (branch, vec![stop_effect, continuing_effect]),
            (stop_effect, vec![stop_jump]),
            (stop_jump, vec![stop]),
            (continuing_effect, vec![continuing_tail]),
            (continuing_tail, vec![continuation]),
        ]);

        // The explicit STOP_JUMP is deliberately not a member of the stopping
        // arm, matching a no-join branch whose out-of-line jump stays at top
        // level.  CONTINUING_TAIL likewise used to rely on flat-layout
        // fallthrough to CONTINUATION.
        assemble_ite(
            &mut statements,
            &HashMap::from([(
                branch,
                IteInfo {
                    true_body_nodes: vec![stop_effect],
                    false_body_nodes: vec![continuing_effect, continuing_tail],
                    join_node: None,
                    no_join: true,
                },
            )]),
            &successors,
        );

        let assembled = statements.get(&branch).expect("branch retained");
        let (then_body, else_body) = match assembled {
            ClightStmt::Sifthenelse(_, then_body, else_body) => {
                (then_body.as_ref(), else_body.as_ref())
            }
            other => panic!("expected assembled ITE, got {other:#?}"),
        };
        assert!(collect_goto_targets(then_body).contains(&stop_jump));
        assert!(collect_goto_targets(else_body).contains(&continuation));
        assert!(!collect_goto_targets(else_body).contains(&stop_jump));
    }

    #[test]
    fn targeted_node_shared_by_ite_arms_has_one_label_definition() {
        let branch = 0xc00;
        let shared = 0xc10;
        let external = 0xc20;
        let mut statements = HashMap::from([
            (
                branch,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(shared))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(shared))),
                ),
            ),
            (
                shared,
                ClightStmt::Slabel(
                    ident_from_node(shared),
                    Box::new(ClightStmt::Sset(1, test_expr())),
                ),
            ),
            (external, ClightStmt::Sgoto(ident_from_node(shared))),
        ]);

        assemble_ite(
            &mut statements,
            &HashMap::from([(
                branch,
                IteInfo {
                    true_body_nodes: vec![shared],
                    false_body_nodes: vec![shared],
                    join_node: None,
                    no_join: true,
                },
            )]),
            &HashMap::new(),
        );

        let definitions: usize = statements
            .values()
            .map(|stmt| count_label_occurrences(stmt, ident_from_node(shared)))
            .sum();
        assert_eq!(definitions, 1, "target label was cloned into both arms");
        assert!(statements.contains_key(&shared));
        let branch_targets = collect_goto_targets(statements.get(&branch).unwrap());
        assert_eq!(
            branch_targets
                .iter()
                .filter(|&&target| target == shared)
                .count(),
            2
        );
    }

    #[test]
    fn ite_keeps_arm_member_with_live_external_cfg_predecessor() {
        let branch = 0xc40;
        let arm_member = 0xc50;
        let other_arm = 0xc60;
        let external_fallthrough = 0xc70;
        let exit = 0xc80;
        let mut statements = HashMap::from([
            (
                branch,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(arm_member))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(other_arm))),
                ),
            ),
            (
                arm_member,
                ClightStmt::Slabel(
                    ident_from_node(arm_member),
                    Box::new(ClightStmt::Sgoto(ident_from_node(exit))),
                ),
            ),
            (other_arm, ClightStmt::Sreturn(None)),
            (external_fallthrough, ClightStmt::Sset(1, test_expr())),
            (exit, ClightStmt::Sreturn(None)),
        ]);

        assemble_ite(
            &mut statements,
            &HashMap::from([(
                branch,
                IteInfo {
                    true_body_nodes: vec![arm_member],
                    false_body_nodes: vec![other_arm],
                    join_node: Some(exit),
                    no_join: false,
                },
            )]),
            &HashMap::from([
                (branch, vec![arm_member, other_arm]),
                (external_fallthrough, vec![arm_member]),
                (arm_member, vec![exit]),
            ]),
        );

        assert!(
            statements.contains_key(&arm_member),
            "ITE assembly moved a multi-entry arm member out of its external CFG path"
        );
        let branch_targets = collect_goto_targets(statements.get(&branch).unwrap());
        assert!(branch_targets.contains(&arm_member));
        assert_eq!(
            statements
                .values()
                .map(|stmt| count_label_occurrences(stmt, ident_from_node(arm_member)))
                .sum::<usize>(),
            1
        );
    }

    #[test]
    fn ite_keeps_cfg_suffix_after_externally_entered_arm_member() {
        let branch = 0xe00;
        let arm_prefix = 0xe50;
        let external_entry = 0xe10;
        let downstream = 0xe80;
        let other_arm = 0xe40;
        let external_pred = 0xe70;
        let exit = 0xe20;
        let mut statements = HashMap::from([
            (
                branch,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(arm_prefix))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(other_arm))),
                ),
            ),
            (arm_prefix, ClightStmt::Sset(1, test_expr())),
            (
                external_entry,
                ClightStmt::Slabel(
                    ident_from_node(external_entry),
                    Box::new(ClightStmt::Sset(2, test_expr())),
                ),
            ),
            (downstream, ClightStmt::Sset(3, test_expr())),
            (other_arm, ClightStmt::Sgoto(ident_from_node(exit))),
            (
                external_pred,
                ClightStmt::Sgoto(ident_from_node(external_entry)),
            ),
            (exit, ClightStmt::Sreturn(None)),
        ]);

        assemble_ite(
            &mut statements,
            &HashMap::from([(
                branch,
                IteInfo {
                    // Deliberately scramble numeric order: reachability comes
                    // only from the CFG below.
                    true_body_nodes: vec![downstream, arm_prefix, external_entry],
                    false_body_nodes: vec![other_arm],
                    join_node: Some(exit),
                    no_join: false,
                },
            )]),
            &HashMap::from([
                (branch, vec![arm_prefix, other_arm]),
                (arm_prefix, vec![external_entry]),
                (external_pred, vec![external_entry]),
                (external_entry, vec![downstream]),
                (downstream, vec![exit]),
                (other_arm, vec![exit]),
            ]),
        );

        assert!(statements.contains_key(&external_entry));
        assert!(
            statements.contains_key(&downstream),
            "ITE assembly detached the externally entered node from its CFG successor"
        );
        assert!(!statements.contains_key(&arm_prefix));
        assert!(collect_goto_targets(statements.get(&branch).unwrap()).contains(&external_entry));
    }

    #[test]
    fn outer_ite_recomputes_targets_introduced_by_inner_ite() {
        let outer = 0xd00;
        let inner = 0xd10;
        let shared_switch = 0xd20;
        let filler = 0xd30;
        let join = 0xd40;
        let unused_true = 0xd50;
        let unused_false = 0xd60;
        let mut statements = HashMap::from([
            (
                outer,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(inner))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(join))),
                ),
            ),
            (
                inner,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(unused_true))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(unused_false))),
                ),
            ),
            (
                shared_switch,
                ClightStmt::Slabel(
                    ident_from_node(shared_switch),
                    Box::new(ClightStmt::Sswitch(
                        test_expr(),
                        vec![(None, ClightStmt::Sskip)],
                    )),
                ),
            ),
            (filler, ClightStmt::Sset(1, test_expr())),
            (join, ClightStmt::Sreturn(None)),
            (unused_true, ClightStmt::Sskip),
            (unused_false, ClightStmt::Sskip),
        ]);
        let infos = HashMap::from([
            (
                inner,
                IteInfo {
                    true_body_nodes: vec![shared_switch],
                    false_body_nodes: vec![shared_switch],
                    join_node: None,
                    no_join: true,
                },
            ),
            (
                outer,
                IteInfo {
                    true_body_nodes: vec![inner, shared_switch, filler],
                    false_body_nodes: Vec::new(),
                    join_node: Some(join),
                    no_join: false,
                },
            ),
        ]);

        assert!(!function_goto_targets(&statements).contains(&shared_switch));
        assemble_ite(&mut statements, &infos, &HashMap::new());

        let assembled = statements.get(&outer).expect("outer branch retained");
        assert!(
            collect_goto_targets(assembled).contains(&shared_switch),
            "inner compound did not introduce the shared target: {assembled:#?}"
        );
        assert!(
            stmt_contains_label(assembled, ident_from_node(shared_switch)),
            "outer compound used a stale target set and stripped the label: {assembled:#?}"
        );
        assert!(!statements.contains_key(&shared_switch));
    }

    #[test]
    fn switch_adjacent_exits_remain_gotos() {
        let header = 0x600;
        let body_top = 0x610;
        let primary_target = 0x700;
        let other_target = 0x710;
        let stmt = ClightStmt::Ssequence(vec![
            ClightStmt::Sswitch(
                test_expr(),
                vec![
                    (Some(0), ClightStmt::Sgoto(ident_from_node(primary_target))),
                    (None, ClightStmt::Sgoto(ident_from_node(header))),
                ],
            ),
            ClightStmt::Sifthenelse(
                test_expr(),
                Box::new(ClightStmt::Sgoto(ident_from_node(other_target))),
                Box::new(ClightStmt::Sgoto(ident_from_node(body_top))),
            ),
        ]);

        let converted = convert_loop_gotos(
            &stmt,
            ident_from_node(header),
            Some(ident_from_node(body_top)),
            &HashSet::from([ident_from_node(primary_target)]),
        );
        let targets: HashSet<Node> = collect_goto_targets(&converted).into_iter().collect();

        // A primary-target goto nested in a switch must remain a goto because
        // `break` would bind to the switch, not the enclosing loop.
        assert!(
            targets.contains(&primary_target),
            "switch exit target was lost: {converted:#?}"
        );
        assert!(
            targets.contains(&other_target),
            "adjacent exit target was lost: {converted:#?}"
        );
        assert!(contains_loop_level_continue(&converted));
    }

    #[test]
    fn generic_inliner_preserves_target_referenced_from_inside_loop() {
        let header = 0xe00;
        let exit_branch = 0xe10;
        let exit_target = 0xf00;
        let after_target = 0xf10;
        let mut statements = HashMap::from([
            (
                header,
                ClightStmt::Sloop(
                    Box::new(ClightStmt::Sifthenelse(
                        test_expr(),
                        Box::new(ClightStmt::Sgoto(ident_from_node(exit_target))),
                        Box::new(ClightStmt::Scontinue),
                    )),
                    Box::new(ClightStmt::Sskip),
                ),
            ),
            (
                exit_target,
                ClightStmt::Slabel(
                    ident_from_node(exit_target),
                    Box::new(ClightStmt::Sset(1, test_expr())),
                ),
            ),
            (after_target, ClightStmt::Sreturn(None)),
        ]);
        let successors = HashMap::from([
            (exit_branch, vec![exit_target]),
            (exit_target, vec![after_target]),
        ]);

        inline_control_flow_bodies(&mut statements, &successors, &HashSet::new());

        let loop_stmt = statements.get(&header).expect("loop remains top-level");
        assert!(
            collect_goto_targets(loop_stmt).contains(&exit_target),
            "loop exit was changed into loop-body fallthrough: {loop_stmt:#?}"
        );
        assert!(
            statements.contains_key(&exit_target),
            "exact loop-exit target was absorbed into the loop"
        );
    }

    #[test]
    fn generic_inliner_still_inlines_non_loop_unique_target() {
        let branch = 0x1000;
        let target = 0x1010;
        let mut statements = HashMap::from([
            (
                branch,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(target))),
                    Box::new(ClightStmt::Sreturn(None)),
                ),
            ),
            (
                target,
                ClightStmt::Slabel(ident_from_node(target), Box::new(ClightStmt::Sreturn(None))),
            ),
        ]);
        let successors = HashMap::from([(branch, vec![target])]);

        inline_control_flow_bodies(&mut statements, &successors, &HashSet::new());

        let branch_stmt = statements.get(&branch).expect("branch remains top-level");
        assert!(
            !collect_goto_targets(branch_stmt).contains(&target),
            "ordinary unique target was needlessly kept as a goto: {branch_stmt:#?}"
        );
        assert!(!statements.contains_key(&target));
    }

    #[test]
    fn pre_inline_fallthrough_keeps_success_return_with_absorbed_block() {
        let branch = 0x1000;
        let failure = 0x9000;
        let success = 0x2000;
        let success_return = 0x2010;
        let mut statements = HashMap::from([
            (
                branch,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(failure))),
                    Box::new(ClightStmt::Sgoto(ident_from_node(success))),
                ),
            ),
            (failure, ClightStmt::Sreturn(None)),
            (success, ClightStmt::Sset(1, test_expr())),
            (success_return, ClightStmt::Sreturn(Some(test_expr()))),
        ]);
        let successors = HashMap::from([
            (branch, vec![failure, success]),
            (success, vec![success_return]),
        ]);

        materialize_cfg_fallthrough_gotos(&mut statements, &successors);
        inline_control_flow_bodies(&mut statements, &successors, &HashSet::new());

        let branch_stmt = statements.get(&branch).expect("branch remains top-level");
        let else_body = match branch_stmt {
            ClightStmt::Sifthenelse(_, _, else_body) => else_body.as_ref(),
            other => panic!("expected inlined branch, got {other:#?}"),
        };
        assert!(
            !stmt_may_fall_through(else_body),
            "absorbed success block lost its CFG return: {else_body:#?}"
        );
        assert!(!statements.contains_key(&success));
    }

    #[test]
    fn pre_inline_fallthrough_does_not_create_compound_self_loop() {
        let compound = 0x1000;
        let absorbed_internal = 0x1010;
        let mut statements = HashMap::from([(
            compound,
            ClightStmt::Slabel(
                ident_from_node(compound),
                Box::new(ClightStmt::Sswitch(
                    test_expr(),
                    vec![(None, ClightStmt::Sskip)],
                )),
            ),
        )]);
        let successors = HashMap::from([
            (compound, vec![absorbed_internal]),
            (absorbed_internal, vec![compound]),
        ]);

        materialize_cfg_fallthrough_gotos(&mut statements, &successors);

        let selected = statements
            .get(&compound)
            .expect("compound remains selected");
        assert!(
            !collect_goto_targets(selected).contains(&compound),
            "absorbed internal CFG nodes created an artificial self-loop: {selected:#?}"
        );
    }

    #[test]
    fn generic_inliner_keeps_target_for_distinct_live_cfg_predecessor() {
        let synthesized_goto_owner = 0x1000;
        let fallthrough_pred = 0x2000;
        let target = 0x2010;
        let mut statements = HashMap::from([
            (
                synthesized_goto_owner,
                ClightStmt::Sifthenelse(
                    test_expr(),
                    Box::new(ClightStmt::Sgoto(ident_from_node(target))),
                    Box::new(ClightStmt::Sreturn(None)),
                ),
            ),
            (
                fallthrough_pred,
                ClightStmt::Slabel(
                    ident_from_node(fallthrough_pred),
                    Box::new(ClightStmt::Sskip),
                ),
            ),
            (
                target,
                ClightStmt::Slabel(ident_from_node(target), Box::new(ClightStmt::Sreturn(None))),
            ),
        ]);
        // The synthesized goto lives in an assembled statement tree, while
        // the original CFG reaches target by fallthrough from a different,
        // still-materialized node.  A predecessor count of one alone cannot
        // authorize globally deleting target.
        let successors = HashMap::from([(fallthrough_pred, vec![target])]);

        inline_control_flow_bodies(&mut statements, &successors, &HashSet::new());

        assert!(statements.contains_key(&target));
        assert!(
            collect_goto_targets(statements.get(&synthesized_goto_owner).unwrap())
                .contains(&target)
        );
    }

    #[test]
    fn generic_inliner_keeps_single_predecessor_goto_statement() {
        let predecessor = 0x1000;
        let jump = 0x1010;
        let target = 0x20;
        let mut statements = HashMap::from([
            (predecessor, ClightStmt::Sset(1, test_expr())),
            (
                jump,
                ClightStmt::Slabel(
                    ident_from_node(jump),
                    Box::new(ClightStmt::Sgoto(ident_from_node(target))),
                ),
            ),
            (
                target,
                ClightStmt::Slabel(ident_from_node(target), Box::new(ClightStmt::Sreturn(None))),
            ),
        ]);
        let successors = HashMap::from([(predecessor, vec![jump]), (jump, vec![target])]);

        inline_control_flow_bodies(&mut statements, &successors, &HashSet::new());

        assert!(
            statements.contains_key(&jump),
            "an exact CFG jump is control flow even with one fallthrough predecessor"
        );
    }

    #[test]
    fn cfg_fallthrough_crossing_an_interposed_branch_becomes_an_explicit_goto() {
        let source = (1u64 << 62) | 0x7468;
        let selected_away = 0x746c;
        let target = 0x746e;
        let unrelated = 0x7600;
        let mut statements = HashMap::from([
            (source, ClightStmt::Sset(1, test_expr())),
            (target, ClightStmt::Sreturn(Some(test_expr()))),
            (unrelated, ClightStmt::Sreturn(None)),
        ]);
        let successors = HashMap::from([
            (source, vec![selected_away]),
            (selected_away, vec![target]),
            (unrelated, vec![target]),
        ]);

        materialize_cfg_fallthrough_gotos(&mut statements, &successors);
        ensure_goto_labels(&mut statements);

        assert_eq!(
            collect_goto_targets(statements.get(&source).unwrap()),
            vec![target]
        );
        assert!(stmt_contains_label(
            statements.get(&target).unwrap(),
            ident_from_node(target)
        ));
    }

    #[test]
    fn cfg_fallthrough_with_distinct_live_frontiers_stays_unclaimed() {
        let source = 0x1000;
        let left = 0x2000;
        let right = 0x3000;
        let mut statements = HashMap::from([
            (source, ClightStmt::Sset(1, test_expr())),
            (left, ClightStmt::Sreturn(None)),
            (right, ClightStmt::Sreturn(None)),
        ]);
        let successors = HashMap::from([(source, vec![left, right])]);

        materialize_cfg_fallthrough_gotos(&mut statements, &successors);

        assert!(collect_goto_targets(statements.get(&source).unwrap()).is_empty());
    }

    #[test]
    fn goto_through_selected_away_node_retargets_unique_live_frontier() {
        let source = 0x1000;
        let transparent = 0x1010;
        let target = 0x1020;
        let mut statements = HashMap::from([
            (source, ClightStmt::Sgoto(ident_from_node(transparent))),
            (target, ClightStmt::Sreturn(None)),
        ]);
        let successors = HashMap::from([(transparent, vec![target])]);

        redirect_gotos_through_selected_away_nodes(&mut statements, &successors);

        assert_eq!(
            statements.get(&source),
            Some(&ClightStmt::Sgoto(ident_from_node(target)))
        );
    }

    #[test]
    fn goto_through_ambiguous_selected_away_node_keeps_exact_target() {
        let source = 0x1000;
        let transparent = 0x1010;
        let left = 0x1020;
        let right = 0x1030;
        let mut statements = HashMap::from([
            (source, ClightStmt::Sgoto(ident_from_node(transparent))),
            (left, ClightStmt::Sreturn(None)),
            (right, ClightStmt::Sreturn(None)),
        ]);
        let successors = HashMap::from([(transparent, vec![left, right])]);

        redirect_gotos_through_selected_away_nodes(&mut statements, &successors);

        assert_eq!(
            statements.get(&source),
            Some(&ClightStmt::Sgoto(ident_from_node(transparent)))
        );
    }
}
