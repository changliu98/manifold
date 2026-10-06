use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::decompile::passes::rtl_optimize_pass::observable_stack_storage_regs;
use crate::util::{exec_order_key, is_synthetic_node, semantic_node_address};
use crate::x86::op::{Comparison, Condition};
use crate::x86::types::{
    Address, BuiltinArg, CminorBinop, Constant, CsharpminorExpr, CsharpminorStmt, Node, RTLReg,
    Symbol, XType,
};
use ascent::ascent_par;
use ascent::lattice::set::Set;
use ascent::Dual;
use log::debug;
use rayon::prelude::*;
use std::collections::{HashMap, HashSet};

type CsharpStmtCandidates = HashMap<Node, Vec<CsharpminorStmt>>;

/// Function-scoped structural interpretations carried to the Clight selector.
/// World zero is deliberately the pre-existing pipeline result so a missing
/// model or an incomplete downstream consumer remains byte-for-byte
/// compatible.  The flat world retains the optimized Csharpminor CFG before
/// loop/if/switch materialization and must be selected atomically.
pub const STRUCTURE_WORLD_STRUCTURED: u8 = 0;
pub const STRUCTURE_WORLD_FLAT: u8 = 1;

fn stmt_candidate_key(stmt: &CsharpminorStmt) -> (bool, String) {
    // Snop is a last-resort conversion failure, never the semantic
    // representative when the same node has a real statement candidate.
    (matches!(stmt, CsharpminorStmt::Snop), format!("{stmt:?}"))
}

fn stable_stmt_candidates<I>(rows: I) -> CsharpStmtCandidates
where
    I: IntoIterator<Item = (Node, CsharpminorStmt)>,
{
    let mut grouped: CsharpStmtCandidates = HashMap::new();
    for (node, stmt) in rows {
        grouped.entry(node).or_default().push(stmt);
    }
    for candidates in grouped.values_mut() {
        candidates.sort_by_cached_key(stmt_candidate_key);
        candidates.dedup();
    }
    grouped
}

fn canonical_working(candidates: &CsharpStmtCandidates) -> HashMap<Node, CsharpminorStmt> {
    candidates
        .iter()
        .filter_map(|(&node, stmts)| stmts.first().cloned().map(|stmt| (node, stmt)))
        .collect()
}

/// Transform every alternative at one node while keeping the transformed
/// semantic representative in slot zero.  The remaining candidates are
/// sorted and deduplicated so later relation order cannot affect selection.
fn transform_stmt_candidates(
    candidates: &mut CsharpStmtCandidates,
    node: Node,
    mut transform: impl FnMut(&CsharpminorStmt) -> CsharpminorStmt,
) {
    let Some(old) = candidates.remove(&node) else {
        return;
    };
    let mut iter = old.into_iter();
    let Some(first) = iter.next() else {
        return;
    };
    let canonical = transform(&first);
    let mut alternatives: Vec<CsharpminorStmt> = iter.map(|stmt| transform(&stmt)).collect();
    alternatives.sort_by_cached_key(stmt_candidate_key);
    alternatives.dedup();
    alternatives.retain(|stmt| stmt != &canonical);
    let mut transformed = Vec::with_capacity(alternatives.len() + 1);
    transformed.push(canonical);
    transformed.extend(alternatives);
    candidates.insert(node, transformed);
}

fn replace_stmt_candidates(
    candidates: &mut CsharpStmtCandidates,
    node: Node,
    stmt: CsharpminorStmt,
) {
    set_stmt_candidates_with_canonical(candidates, node, stmt, Vec::new());
}

fn set_stmt_candidates_with_canonical(
    candidates: &mut CsharpStmtCandidates,
    node: Node,
    canonical: CsharpminorStmt,
    mut alternatives: Vec<CsharpminorStmt>,
) {
    alternatives.sort_by_cached_key(stmt_candidate_key);
    alternatives.dedup();
    alternatives.retain(|stmt| stmt != &canonical);
    let mut stmts = Vec::with_capacity(alternatives.len() + 1);
    stmts.push(canonical);
    stmts.extend(alternatives);
    candidates.insert(node, stmts);
}

fn refresh_working_node(
    working: &mut HashMap<Node, CsharpminorStmt>,
    candidates: &CsharpStmtCandidates,
    node: Node,
) {
    if let Some(stmt) = candidates.get(&node).and_then(|stmts| stmts.first()) {
        working.insert(node, stmt.clone());
    }
}

fn dom_set_with_self(strict: &Set<Node>, n: Node) -> Set<Node> {
    let mut s = strict.0.clone();
    s.insert(n);
    Set(s)
}

fn affine_pointer_base(expr: &CsharpminorExpr) -> Option<RTLReg> {
    match expr {
        CsharpminorExpr::Evar(reg) => Some(*reg),
        CsharpminorExpr::Ebinop(CminorBinop::Oaddl, lhs, rhs)
            if matches!(rhs.as_ref(), CsharpminorExpr::Econst(_)) =>
        {
            affine_pointer_base(lhs)
        }
        CsharpminorExpr::Ebinop(CminorBinop::Oaddl, lhs, rhs)
            if matches!(lhs.as_ref(), CsharpminorExpr::Econst(_)) =>
        {
            affine_pointer_base(rhs)
        }
        _ => None,
    }
}

#[derive(Default)]
pub struct StructuringPass {
    // This pure-analysis cache belongs to one pipeline invocation. It is not
    // inferred state: replay/rollback still restores every blackboard output.
    fixpoints: structuring_memo::Fixpoints,
}

#[path = "structuring_memo.rs"]
mod structuring_memo;

impl IRPass for StructuringPass {
    fn name(&self) -> &'static str {
        "Structuring"
    }

    fn run(&self, db: &mut DecompileDB) {
        // Structuring needs one statement per CFG node, but the relation is
        // intentionally multi-valued.  Pick a stable non-Snop representative
        // for structural analysis and retain every alternative for the Clight
        // selector; collecting the relation directly into a HashMap made the
        // chosen semantics depend on parallel relation iteration order.
        let mut candidates = stable_stmt_candidates(
            db.rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt_candidate")
                .map(|(n, s)| (*n, s.clone()))
                .collect::<Vec<_>>(),
        );
        let mut working = canonical_working(&candidates);

        // These names denote externally observable memory cells, even though
        // reverse Stacking represents their writes as Sset.  Every later
        // scalar optimization must preserve that distinction.
        let mut protected_stack_regs: HashSet<RTLReg> = observable_stack_storage_regs(db)
            .into_values()
            .flatten()
            .collect();
        // Copy/constant elimination currently has no effect-transfer schema.
        // Preserve the explicit contract inputs instead of deleting a capture
        // and trying to reconstruct its origin after the optimizer ran.
        for &(node,) in db.rel_iter::<(Node,)>("effect_value_boundary") {
            for statement in candidates.get(&node).into_iter().flatten() {
                protected_stack_regs.extend(stmt_uses_set(statement));
                if let CsharpminorStmt::Sset(dst, _) = statement {
                    protected_stack_regs.insert(*dst);
                }
            }
        }

        // Apply optimizations to the representative and all retained
        // alternatives in lockstep.
        propagate_copies(&mut working, &mut candidates, db, &protected_stack_regs);
        inline_constants(&mut working, &mut candidates, db, &protected_stack_regs);
        eliminate_dead_returns(&mut working, &mut candidates, db);
        inline_single_use_temps(&mut working, &mut candidates, db, &protected_stack_regs);
        lift_setcc_arith_to_ite(&mut working, &mut candidates, db);

        // instr_in_function is multi-valued: shared nodes (e.g. PLT trampolines) belong to every reaching function.
        let node_to_funcs: HashMap<Node, Vec<Address>> = {
            let mut groups: HashMap<Node, Vec<Address>> = HashMap::new();
            for (n, f) in db.rel_iter::<(Node, Address)>("instr_in_function") {
                groups.entry(*n).or_default().push(*f);
            }
            for v in groups.values_mut() {
                v.sort();
                v.dedup();
            }
            groups
        };

        // Next relation for target resolution and sequential ordering
        let next_map: HashMap<Node, Node> = db
            .rel_iter::<(Node, Node)>("next")
            .map(|&(a, b)| (a, b))
            .collect();

        // Blocks containing an unrepresented optimized operation. Packed ALU
        // and REP string operations leave no statement at their own address,
        // so flag the surviving statements at block granularity.
        let code_in_block_map: HashMap<Address, Address> = db
            .rel_iter::<(Address, Address)>("code_in_block")
            .map(|&(a, b)| (a, b))
            .collect();
        let packed_alu_blocks: HashSet<Address> = {
            let mut s: HashSet<Address> = HashSet::new();
            for &(a,) in db.rel_iter::<(Address,)>("packed_alu_addr") {
                if let Some(&blk) = code_in_block_map.get(&a) {
                    s.insert(blk);
                }
            }
            s
        };
        let optimized_gap_blocks: HashSet<Address> = {
            let mut blocks = packed_alu_blocks.clone();
            for &(address,) in db.rel_iter::<(Address,)>("optimized_bulk_addr") {
                if let Some(&block) = code_in_block_map.get(&address) {
                    blocks.insert(block);
                }
            }
            blocks
        };
        // Stmt nodes in a packed block; node id low bits are the instruction address (top 2 bits are tail-dup copy tags), so mask them to recover it.
        let packed_alu_nodes: HashSet<Node> = if packed_alu_blocks.is_empty() {
            HashSet::new()
        } else {
            db.rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt_candidate")
                .filter_map(|(n, _)| {
                    let addr = semantic_node_address(*n);
                    code_in_block_map
                        .get(&addr)
                        .filter(|blk| packed_alu_blocks.contains(blk))
                        .map(|_| *n)
                })
                .collect()
        };
        let optimized_gap_nodes: HashSet<Node> = if optimized_gap_blocks.is_empty() {
            HashSet::new()
        } else {
            db.rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt_candidate")
                .filter_map(|(node, _)| {
                    let address = semantic_node_address(*node);
                    code_in_block_map
                        .get(&address)
                        .filter(|block| optimized_gap_blocks.contains(block))
                        .map(|_| *node)
                })
                .collect()
        };
        let mut pointer_regs: HashSet<RTLReg> = db
            .rel_iter::<(RTLReg,)>("is_ptr")
            .map(|(reg,)| *reg)
            .collect();
        pointer_regs.extend(
            db.rel_iter::<(Address, RTLReg, XType)>("emit_function_param_type")
                .filter_map(|(_, reg, xtype)| {
                    matches!(
                        xtype,
                        XType::Xptr
                            | XType::Xcharptr
                            | XType::Xcharptrptr
                            | XType::Xintptr
                            | XType::Xfloatptr
                            | XType::Xsingleptr
                            | XType::Xfuncptr
                            | XType::XstructPtr(_)
                    )
                    .then_some(*reg)
                }),
        );

        // CF-6: include cminor_succ preds so taint-mirror can catch edges clight sees but the function-local stmt view misses (cross-function preds, preds with no csharp stmt); values sorted for determinism.
        let (cminor_succs, cminor_preds): (HashMap<Node, Vec<Node>>, HashMap<Node, Vec<Node>>) = {
            let mut succs: HashMap<Node, Vec<Node>> = HashMap::new();
            let mut preds: HashMap<Node, Vec<Node>> = HashMap::new();
            for &(src, dst) in db.rel_iter::<(Node, Node)>("cminor_succ") {
                succs.entry(src).or_default().push(dst);
                preds.entry(dst).or_default().push(src);
            }
            for v in succs.values_mut().chain(preds.values_mut()) {
                v.sort_unstable();
                v.dedup();
            }
            (succs, preds)
        };
        let expansion_sources: HashSet<Node> = db
            .rel_iter::<(Node, Node)>("rtl_expansion_edge")
            .map(|(src, _)| *src)
            .collect();

        // The raw machine entry is a fallback for isolated/partial pipelines.
        // Cshminor's func_entry_node overrides it with the post-optimizer,
        // active-Cminor entry, preserving a synthetic expansion at function
        // start instead of resolving the stale raw address through `next`.
        let mut func_entry: HashMap<Address, Node> = db
            .rel_iter::<(Address, Symbol, Node)>("emit_function")
            .map(|(addr, _, entry)| (*addr, *entry))
            .collect();
        for &(func, entry) in db.rel_iter::<(Address, Node)>("func_entry_node") {
            func_entry.insert(func, entry);
        }

        let mut all_stmts: Vec<(Node, CsharpminorStmt)> = working
            .iter()
            .map(|(&node, stmt)| (node, stmt.clone()))
            .collect();
        all_stmts.sort_by_key(|(node, _)| exec_order_key(*node));

        let mut func_stmts: HashMap<Address, Vec<(Node, CsharpminorStmt)>> = HashMap::new();
        let mut unowned_nodes: Vec<Node> = Vec::new();

        for (node, stmt) in &all_stmts {
            // Synthetic nodes (tail_dup_pass copies) are not in instr_in_function; fall back to the masked base id to group them into their base node's function.
            let owner = node_to_funcs
                .get(node)
                .or_else(|| node_to_funcs.get(&semantic_node_address(*node)));
            if let Some(funcs) = owner {
                for &func_addr in funcs {
                    func_stmts
                        .entry(func_addr)
                        .or_default()
                        .push((*node, stmt.clone()));
                }
            } else {
                unowned_nodes.push(*node);
            }
        }

        for stmts in func_stmts.values_mut() {
            stmts.sort_by_key(|(n, _)| exec_order_key(*n));
        }

        // Process functions in parallel from a sorted outer vector. HashMap
        // iteration order must not become relation insertion order.
        let mut funcs: Vec<(Address, Vec<(Node, CsharpminorStmt)>)> =
            func_stmts.into_iter().collect();
        funcs.sort_by_key(|(func, _)| *func);
        let per_func_results: Vec<_> = funcs
            .par_iter()
            .map(|(func_addr, stmts)| {
                if stmts.len() <= 1 {
                    return (
                        *func_addr,
                        stmts.clone(),
                        StructuringResult {
                            stmts: stmts.clone(),
                            switch_chain_members: vec![],
                            valid_switches: vec![],
                            switch_defaults: vec![],
                            ifbody_true: vec![],
                            ifbody_false: vec![],
                            join_points: vec![],
                            scond_no_join: vec![],
                        },
                    );
                }

                let declared_entry = func_entry.get(func_addr).copied();
                let structured = structure_with_memo(
                    stmts,
                    &next_map,
                    &cminor_succs,
                    &expansion_sources,
                    declared_entry,
                    &cminor_preds,
                    &packed_alu_nodes,
                    &optimized_gap_nodes,
                    &pointer_regs,
                    Some(&self.fixpoints),
                );
                (*func_addr, stmts.clone(), structured)
            })
            .collect();

        // Cshminor already derives loop structure in Ascent.  Structuring's
        // own Ascent program derives joins and switch candidates below.  A
        // function with either kind of structural metadata needs a flat world
        // even when its statement values happen to be unchanged.
        let loop_structured_functions: HashSet<Address> = db
            .rel_iter::<(Address, Node, Node)>("emit_loop_body")
            .map(|(func, _, _)| *func)
            .collect();

        // Merge results
        let mut result_stmts: Vec<(Node, CsharpminorStmt)> = Vec::new();
        let mut structure_worlds: Vec<(Address, u8, bool)> = Vec::new();
        let mut csharp_stmt_worlds: Vec<(Address, u8, Node, CsharpminorStmt)> = Vec::new();
        let mut structure_unchanged_nodes: Vec<(Address, Node)> = Vec::new();
        let mut all_switch_members: Vec<(Address, Node, Node, u64, i64, Node)> = Vec::new();
        let mut all_valid_switches: Vec<(Address, Node, u64)> = Vec::new();
        let mut all_switch_defaults: Vec<(Address, Node, Node)> = Vec::new();
        let mut all_ifbody_true: Vec<(Address, Node, Node)> = Vec::new();
        let mut all_ifbody_false: Vec<(Address, Node, Node)> = Vec::new();
        let mut all_join_points: Vec<(Address, Node, Node)> = Vec::new();
        let mut all_scond_no_join: Vec<(Address, Node)> = Vec::new();
        for (func_addr, flat_stmts, structured) in per_func_results {
            let flat_canonical: HashMap<Node, CsharpminorStmt> =
                flat_stmts.iter().cloned().collect();
            let structured_canonical: HashMap<Node, CsharpminorStmt> =
                structured.stmts.iter().cloned().collect();
            let has_flat_world = flat_canonical != structured_canonical
                || !structured.valid_switches.is_empty()
                || !structured.ifbody_true.is_empty()
                || !structured.ifbody_false.is_empty()
                || !structured.join_points.is_empty()
                || !structured.scond_no_join.is_empty()
                || loop_structured_functions.contains(&func_addr);
            structure_worlds.push((func_addr, STRUCTURE_WORLD_STRUCTURED, true));
            if has_flat_world {
                structure_worlds.push((func_addr, STRUCTURE_WORLD_FLAT, false));
                for (node, _) in &flat_stmts {
                    if let Some(stmts) = candidates.get(node) {
                        csharp_stmt_worlds.extend(
                            stmts
                                .iter()
                                .cloned()
                                .map(|stmt| (func_addr, STRUCTURE_WORLD_FLAT, *node, stmt)),
                        );
                    }
                }
            }

            let switch_nodes: HashSet<Node> = structured
                .valid_switches
                .iter()
                .map(|(head, _)| *head)
                .chain(
                    structured
                        .switch_chain_members
                        .iter()
                        .map(|(_, member, _, _, _)| *member),
                )
                .collect();
            for (node, stmt) in structured.stmts {
                // A structurally unchanged node retains every optimized data
                // candidate.  A control-flow rewrite is intentionally
                // single-valued because its replacement encodes the recovered
                // CFG, not a type/printing alternative.
                if working.get(&node) == Some(&stmt) {
                    if let Some(stmts) = candidates.get(&node) {
                        result_stmts.extend(stmts.iter().cloned().map(|s| (node, s)));
                        csharp_stmt_worlds.extend(
                            stmts
                                .iter()
                                .cloned()
                                .map(|s| (func_addr, STRUCTURE_WORLD_STRUCTURED, node, s)),
                        );
                        // Switch materialization is metadata-driven: the raw
                        // Scond may be byte-identical in both worlds while the
                        // structured world suppresses the comparison chain.
                        // Do not mark its head shared.
                        if has_flat_world && !switch_nodes.contains(&node) {
                            structure_unchanged_nodes.push((func_addr, node));
                        }
                        continue;
                    }
                }
                result_stmts.push((node, stmt.clone()));
                csharp_stmt_worlds.push((func_addr, STRUCTURE_WORLD_STRUCTURED, node, stmt));
            }
            for (head, member, reg, val, target) in &structured.switch_chain_members {
                all_switch_members.push((func_addr, *head, *member, *reg, *val, *target));
            }
            for (head, reg) in &structured.valid_switches {
                all_valid_switches.push((func_addr, *head, *reg));
            }
            for (head, target) in &structured.switch_defaults {
                all_switch_defaults.push((func_addr, *head, *target));
            }
            for (branch, member) in &structured.ifbody_true {
                all_ifbody_true.push((func_addr, *branch, *member));
            }
            for (branch, member) in &structured.ifbody_false {
                all_ifbody_false.push((func_addr, *branch, *member));
            }
            for (branch, join) in &structured.join_points {
                all_join_points.push((func_addr, *branch, *join));
            }
            for branch in &structured.scond_no_join {
                all_scond_no_join.push((func_addr, *branch));
            }
        }

        unowned_nodes.sort_unstable();
        unowned_nodes.dedup();
        for node in unowned_nodes {
            if let Some(stmts) = candidates.get(&node) {
                result_stmts.extend(stmts.iter().cloned().map(|stmt| (node, stmt)));
            }
        }

        // Preserve pre-existing csharp_stmt tuples in case the single-producer invariant breaks.
        let existing: Vec<(Node, CsharpminorStmt)> = db
            .rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt")
            .map(|(n, s)| (*n, s.clone()))
            .collect();

        // Shared nodes are structured once per owning function, so the same
        // tuple can appear multiple times. Sort before deduplication so every
        // downstream reader sees a stable relation order as well as the same
        // set of facts.
        let mut tuples: Vec<(Node, CsharpminorStmt)> =
            existing.into_iter().chain(result_stmts).collect();
        tuples.sort_by_cached_key(|(node, stmt)| (*node, stmt_candidate_key(stmt)));
        tuples.dedup();
        let new_rel = ascent::boxcar::Vec::<(Node, CsharpminorStmt)>::new();
        for tuple in tuples {
            new_rel.push(tuple);
        }
        db.rel_set("csharp_stmt", new_rel);

        let switch_member_rel = ascent::boxcar::Vec::<(Address, Node, Node, u64, i64, Node)>::new();
        for tuple in all_switch_members {
            switch_member_rel.push(tuple);
        }
        db.rel_set("switch_chain_member", switch_member_rel);

        let valid_switch_rel = ascent::boxcar::Vec::<(Address, Node, u64)>::new();
        for tuple in &all_valid_switches {
            valid_switch_rel.push(*tuple);
        }
        db.rel_set("valid_switch_chain", valid_switch_rel);

        let switch_default_rel = ascent::boxcar::Vec::<(Address, Node, Node)>::new();
        for tuple in all_switch_defaults {
            switch_default_rel.push(tuple);
        }
        db.rel_set("switch_chain_default", switch_default_rel);

        let emit_switch_rel = ascent::boxcar::Vec::<(Address, Node, u64)>::new();
        for tuple in &all_valid_switches {
            emit_switch_rel.push(*tuple);
        }
        db.rel_set("emit_switch_chain", emit_switch_rel);

        // Export if-body structural metadata for clight_select compound assembly
        let ifbody_true_rel = ascent::boxcar::Vec::<(Address, Node, Node)>::new();
        for tuple in all_ifbody_true {
            ifbody_true_rel.push(tuple);
        }
        db.rel_set("emit_ifbody_true", ifbody_true_rel);

        let ifbody_false_rel = ascent::boxcar::Vec::<(Address, Node, Node)>::new();
        for tuple in all_ifbody_false {
            ifbody_false_rel.push(tuple);
        }
        db.rel_set("emit_ifbody_false", ifbody_false_rel);

        let join_point_rel = ascent::boxcar::Vec::<(Address, Node, Node)>::new();
        for tuple in all_join_points {
            join_point_rel.push(tuple);
        }
        db.rel_set("emit_join_point", join_point_rel);

        let scond_no_join_rel = ascent::boxcar::Vec::<(Address, Node)>::new();
        for tuple in all_scond_no_join {
            scond_no_join_rel.push(tuple);
        }
        db.rel_set("emit_scond_no_join", scond_no_join_rel);

        structure_worlds.sort_unstable();
        structure_worlds.dedup();
        db.rel_set(
            "structure_world",
            structure_worlds
                .into_iter()
                .collect::<ascent::boxcar::Vec<(Address, u8, bool)>>(),
        );
        csharp_stmt_worlds.sort_by_cached_key(|(func, world, node, stmt)| {
            (*func, *world, *node, stmt_candidate_key(stmt))
        });
        csharp_stmt_worlds.dedup();
        db.rel_set(
            "csharp_stmt_world",
            csharp_stmt_worlds
                .into_iter()
                .collect::<ascent::boxcar::Vec<(Address, u8, Node, CsharpminorStmt)>>(),
        );
        structure_unchanged_nodes.sort_unstable();
        structure_unchanged_nodes.dedup();
        db.rel_set(
            "structure_unchanged_node",
            structure_unchanged_nodes
                .into_iter()
                .collect::<ascent::boxcar::Vec<(Address, Node)>>(),
        );
    }

    fn inputs(&self) -> &'static [&'static str] {
        &[
            "csharp_stmt_candidate",
            "effect_value_boundary",
            "csharp_stmt",
            "instr_in_function",
            "single_def_const",
            "slot_escaped_canonical",
            "slot_escaped_region_canonical",
            "frame_read_storage_owner",
            "stack_var",
            "dead_def",
            "code_in_block",
            "next",
            "emit_inline_temp",
            "emit_var_type_candidate",
            "emit_function",
            "func_entry_node",
            "emit_function_param_candidate",
            "emit_function_param_type",
            "packed_alu_addr",
            "optimized_bulk_addr",
            "is_ptr",
            "emit_loop_body",
            // Authoritative semantic CFG.  Both are read imperatively; without
            // declaring them the parallel scheduler supplies empty relations.
            "cminor_succ",
            "rtl_expansion_edge",
            // Read by the dead-copy type transfer below, which is imperative
            // and would see an empty relation in a parallel sub-DB otherwise.
            "web_class_gpr",
            "web_class_fp",
        ]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "csharp_stmt",
            "switch_chain_member",
            "switch_chain_default",
            "valid_switch_chain",
            "emit_switch_chain",
            "emit_ifbody_true",
            "emit_ifbody_false",
            "emit_join_point",
            "emit_scond_no_join",
            "emit_var_type_candidate",
            "structure_world",
            "csharp_stmt_world",
            "structure_unchanged_node",
        ]
    }
}

// A CsharpminorExpr that is statically a nonzero integer constant.
fn expr_is_nonzero_int_const(e: &CsharpminorExpr) -> bool {
    matches!(
        e,
        CsharpminorExpr::Econst(Constant::Ointconst(n))
            | CsharpminorExpr::Econst(Constant::Olongconst(n))
        if *n != 0
    )
}

fn is_terminal_stmt(stmt: &CsharpminorStmt) -> bool {
    match stmt {
        CsharpminorStmt::Sjump(_)
        | CsharpminorStmt::Sreturn(_)
        | CsharpminorStmt::Stailcall(_, _, _)
        | CsharpminorStmt::Scond(_, _, _, _)
        | CsharpminorStmt::Sjumptable(_, _) => true,
        // A direct call is terminal when abi::call_is_noreturn says so, keeping structuring in agreement with abi_pass, linear_pass and cshminor.
        CsharpminorStmt::Scall(_, _, either::Either::Right(either::Either::Right(name)), args) => {
            crate::abi::call_is_noreturn(name, || {
                args.first().map_or(false, expr_is_nonzero_int_const)
            })
        }
        CsharpminorStmt::Sifthenelse(_, _, then_s, else_s) => {
            is_terminal_stmt(then_s) && is_terminal_stmt(else_s)
        }
        // A duplicated tail is one Sseq node standing in for a straight line, so its terminality is that of its LAST element.
        CsharpminorStmt::Sseq(inner) => inner.last().map_or(false, is_terminal_stmt),
        _ => false,
    }
}

// Explicit CFG targets of an Sseq node's terminal element, so a duplicated tail gets the same outgoing edges the flat rules give a bare Sjump/Scond.
fn sseq_terminal_targets(stmt: &CsharpminorStmt) -> Vec<Node> {
    match stmt {
        CsharpminorStmt::Sseq(inner) => match inner.last() {
            Some(CsharpminorStmt::Sjump(t)) => vec![*t],
            Some(CsharpminorStmt::Scond(_, _, t, f)) => vec![*t, *f],
            Some(CsharpminorStmt::Sjumptable(_, targets)) => targets.as_ref().to_vec(),
            _ => vec![],
        },
        _ => vec![],
    }
}

// CFG analysis, reachability, if-then-else body, loop, and switch detection
ascent_par! {
    #[swap_db]
    pub struct StructuringProgram;

    relation stmt(Node, CsharpminorStmt);
    relation seq_next(Node, Node);

    relation cfg_edge(Node, Node);
    cfg_edge(*node, *target) <--
        stmt(node, ?CsharpminorStmt::Sjump(target));

    cfg_edge(*node, *t) <--
        stmt(node, ?CsharpminorStmt::Scond(_, _, t, _));
    cfg_edge(*node, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(_, _, _, f));

    relation jumptable_target(Node, Node);
    cfg_edge(*node, *target) <-- jumptable_target(node, target);

    // A duplicated-tail Sseq transfers via its LAST element; mirror the flat Sjump/Scond edges so its dominance matches the straight line it stands in for.
    cfg_edge(*node, *target) <--
        stmt(node, s),
        for target in sseq_terminal_targets(s).iter();

    relation is_terminal(Node);
    is_terminal(*node) <-- stmt(node, s), if is_terminal_stmt(s);

    cfg_edge(*node, *next) <--
        stmt(node, _),
        seq_next(node, next),
        !is_terminal(node);

    // Scond where neither target dominates the branch (not a back edge) is an if-then-else candidate
    relation scond_node(Node, Node, Node);
    scond_node(*node, *t, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(_, _, t, f)),
        dom_set(node, branch_doms),
        if *node == *t || !branch_doms.0.contains(t),
        if *node == *f || !branch_doms.0.contains(f);

    // Demand-driven reachability from scond targets. Each CFG point owns one
    // union-lattice value containing the targets that reach it, rather than an
    // O(T*V) materialized pair relation.
    relation scond_target(Node);
    scond_target(*t) <-- scond_node(_, t, _);
    scond_target(*f) <-- scond_node(_, _, f);

    #[local] lattice scond_sources_at(Node, Set<Node>);
    scond_sources_at(*next, Set::singleton(*src)) <--
        scond_target(src),
        cfg_edge(src, next);
    scond_sources_at(*next, sources.clone()) <--
        scond_sources_at(cur, sources),
        cfg_edge(cur, next);

    // Preserve the old reach-or-equal boundary: a loop header reaches itself
    // only through an actual cycle, while terminal and non-header targets seed
    // their own point.
    scond_sources_at(*t, Set::singleton(*t)) <-- scond_target(t), is_terminal(t);
    scond_sources_at(*t, Set::singleton(*t)) <-- scond_target(t), !loop_header(t);

    relation join_candidate(Node, Node);
    join_candidate(*branch, *node) <--
        scond_node(branch, t, f),
        scond_sources_at(node, sources),
        if sources.0.contains(t),
        if sources.0.contains(f),
        pdom_set(branch, branch_pdoms),
        if *branch != *node && branch_pdoms.0.contains(node);

    // Immediate post-dominator selection over join candidates from the postdominates lattice: a candidate is NOT immediate if some other candidate fails to post-dominate it. Never by node address.
    relation exists_closer_join(Node, Node);
    exists_closer_join(*branch, *j) <--
        join_candidate(branch, j),
        join_candidate(branch, j2),
        if j2 != j,
        pdom_set(j, j_pdoms),
        if !j_pdoms.0.contains(j2);

    relation ipdom_join(Node, Node);
    ipdom_join(*branch, *j) <--
        join_candidate(branch, j),
        !exists_closer_join(branch, j);

    relation join_point(Node, Node);
    join_point(*branch, *node) <--
        ipdom_join(branch, node);

    // (target, branch): each condition branch's two CFG targets, tagged with the branch.
    relation scond_branch_target(Node, Node);
    scond_branch_target(*t, *branch) <-- scond_node(branch, t, _);
    scond_branch_target(*f, *branch) <-- scond_node(branch, _, f);

    // A node directly targeted by >=2 distinct condition branches.
    relation multi_branch_target(Node);
    multi_branch_target(*node) <--
        scond_branch_target(node, b1),
        scond_branch_target(node, b2),
        if b1 != b2;

    // A shared landing pad of a MULTI-WAY guard chain (targeted by >=2 branches and flowing to a join itself targeted by >=2) must stay standalone, or inlining steals it from the other guards.
    relation shared_target(Node);
    shared_target(*node) <--
        multi_branch_target(node),
        join_point(_, j),
        multi_branch_target(j),
        scond_sources_at(j, sources),
        if sources.0.contains(node);

    // A node targeted by >=2 condition branches that is not itself any branch's structured join is a cross-branch landing pad and must stay standalone; the first rule catches only branch-target merges.
    shared_target(*node) <--
        multi_branch_target(node),
        !join_point(_, node);

    // If-body membership: nodes reachable from branch targets, stopping at join point
    relation ifbody_true(Node, Node);
    relation ifbody_false(Node, Node);
    ifbody_true(*branch, *t) <--
        scond_node(branch, t, _),
        join_point(branch, join),
        if t != join,
        !shared_target(t),
        !loop_header(t);

    ifbody_true(*branch, *next) <--
        ifbody_true(branch, cur),
        cfg_edge(cur, next),
        join_point(branch, join),
        if next != join,
        !shared_target(next),
        dom_set(next, next_doms),
        if *next != *branch && next_doms.0.contains(branch),
        !loop_header(next),
        !loop_body_node(next);

    ifbody_false(*branch, *f) <--
        scond_node(branch, _, f),
        join_point(branch, join),
        if f != join,
        !shared_target(f),
        !loop_header(f);

    ifbody_false(*branch, *next) <--
        ifbody_false(branch, cur),
        cfg_edge(cur, next),
        join_point(branch, join),
        if next != join,
        !shared_target(next),
        dom_set(next, next_doms),
        if *next != *branch && next_doms.0.contains(branch),
        !loop_header(next),
        !loop_body_node(next);

    // Where each loop's primary exit-condition lands outside the body, used to thread the if-body walk through a loop as a unit.
    relation loop_exit_to(Node, Node);
    loop_exit_to(*header, *exit) <-- loop_exit_cond(header, _, exit, _);

    // Loop-as-unit if-body inclusion: admit a branch-contained loop HEADER as one member and resume from the loop's EXIT, so a branch whose body is a loop does not get an empty body.
    ifbody_true(*branch, *t) <--
        scond_node(branch, t, _),
        join_point(branch, join),
        if t != join,
        !shared_target(t),
        loop_header(t);
    ifbody_false(*branch, *f) <--
        scond_node(branch, _, f),
        join_point(branch, join),
        if f != join,
        !shared_target(f),
        loop_header(f);
    // (b) walk reaches a loop header: include it.
    ifbody_true(*branch, *h) <--
        ifbody_true(branch, cur),
        cfg_edge(cur, h),
        loop_header(h),
        join_point(branch, join),
        if h != join,
        !shared_target(h),
        dom_set(h, h_doms),
        if *h != *branch && h_doms.0.contains(branch);
    ifbody_false(*branch, *h) <--
        ifbody_false(branch, cur),
        cfg_edge(cur, h),
        loop_header(h),
        join_point(branch, join),
        if h != join,
        !shared_target(h),
        dom_set(h, h_doms),
        if *h != *branch && h_doms.0.contains(branch);
    // (c) resume the walk from the loop's exit (the plain recursive rules carry on from there).
    ifbody_true(*branch, *exit) <--
        ifbody_true(branch, h),
        loop_header(h),
        loop_exit_to(h, exit),
        join_point(branch, join),
        if exit != join,
        !shared_target(exit),
        !loop_header(exit),
        !loop_body_node(exit),
        dom_set(exit, exit_doms),
        if *exit != *branch && exit_doms.0.contains(branch);
    ifbody_false(*branch, *exit) <--
        ifbody_false(branch, h),
        loop_header(h),
        loop_exit_to(h, exit),
        join_point(branch, join),
        if exit != join,
        !shared_target(exit),
        !loop_header(exit),
        !loop_body_node(exit),
        dom_set(exit, exit_doms),
        if *exit != *branch && exit_doms.0.contains(branch);

    // No-join case: one branch exits, the other continues
    relation scond_no_join(Node);
    scond_no_join(*branch) <--
        scond_node(branch, _, _),
        !join_candidate(branch, _);

    // Reconvergence node of a no-join branch (reachable from BOTH arms): a shared continuation the walk must stop at, derived from CFG reachability; synthetic tail-dup copies are excluded.
    relation no_join_reconverge(Node, Node);
    no_join_reconverge(*branch, *node) <--
        scond_no_join(branch),
        scond_node(branch, t, f),
        scond_sources_at(node, sources),
        if sources.0.contains(t),
        if sources.0.contains(f),
        if node != t,
        if node != f,
        if !is_synthetic_node(*node);

    // A node that reconverges an ENCLOSING no-join branch must stay top-level, but only when the inner branch does not itself dominate it, or the branch's exclusive subtree gets blocked out of its arm.
    relation enclosing_reconverge(Node, Node);
    enclosing_reconverge(*branch, *node) <--
        scond_node(branch, _, _),
        no_join_reconverge(outer, node),
        if outer != branch,
        dom_set(branch, branch_doms),
        if branch_doms.0.contains(outer),
        dom_set(node, node_doms),
        if *node == *branch || !node_doms.0.contains(branch);

    ifbody_true(*branch, *t) <--
        scond_no_join(branch),
        scond_node(branch, t, _),
        !shared_target(t),
        !no_join_reconverge(branch, t),
        !enclosing_reconverge(branch, t),
        !loop_header(t);
    ifbody_true(*branch, *next) <--
        scond_no_join(branch),
        ifbody_true(branch, cur),
        cfg_edge(cur, next),
        !shared_target(next),
        !no_join_reconverge(branch, next),
        !enclosing_reconverge(branch, next),
        dom_set(next, next_doms),
        if *next != *branch && next_doms.0.contains(branch),
        !loop_header(next),
        !loop_body_node(next);

    ifbody_false(*branch, *f) <--
        scond_no_join(branch),
        scond_node(branch, _, f),
        !shared_target(f),
        !no_join_reconverge(branch, f),
        !enclosing_reconverge(branch, f),
        !loop_header(f);
    ifbody_false(*branch, *next) <--
        scond_no_join(branch),
        ifbody_false(branch, cur),
        cfg_edge(cur, next),
        !shared_target(next),
        !no_join_reconverge(branch, next),
        !enclosing_reconverge(branch, next),
        dom_set(next, next_doms),
        if *next != *branch && next_doms.0.contains(branch),
        !loop_header(next),
        !loop_body_node(next);

    // No-join loop-as-unit: admit the loop HEADER as the continuing arm's sole member when the branch dominates it, or the empty arm falls through into the floated loop.
    ifbody_true(*branch, *t) <--
        scond_no_join(branch),
        scond_node(branch, t, _),
        !shared_target(t),
        loop_header(t),
        dom_set(t, t_doms),
        if *t != *branch && t_doms.0.contains(branch);
    ifbody_false(*branch, *f) <--
        scond_no_join(branch),
        scond_node(branch, _, f),
        !shared_target(f),
        loop_header(f),
        dom_set(f, f_doms),
        if *f != *branch && f_doms.0.contains(branch);
    // Walk reaches a loop header (the arm leads into the loop through some intermediate code).
    ifbody_true(*branch, *h) <--
        scond_no_join(branch),
        ifbody_true(branch, cur),
        cfg_edge(cur, h),
        loop_header(h),
        !shared_target(h),
        dom_set(h, h_doms),
        if *h != *branch && h_doms.0.contains(branch);
    ifbody_false(*branch, *h) <--
        scond_no_join(branch),
        ifbody_false(branch, cur),
        cfg_edge(cur, h),
        loop_header(h),
        !shared_target(h),
        dom_set(h, h_doms),
        if *h != *branch && h_doms.0.contains(branch);

    // Entry node for the function (lowest address statement node)
    relation entry_node(Node);

    // Lattice-based dominator computation (Cooper-Harvey-Kennedy flavor), same shape as cshminor_pass. Storage is O(V*d) (d = dom-tree depth) vs the O(V^2) path_avoiding workspace this replaces; on vim it drops the pass peak by tens of GB.
    #[local] lattice strict_dom_set(Node, Dual<Set<Node>>);
    lattice dom_set(Node, Dual<Set<Node>>);

    dom_set(*entry, Dual(Set::singleton(*entry))) <--
        entry_node(entry);

    strict_dom_set(*n, Dual(p_doms.0.clone())) <--
        cfg_edge(p, n),
        dom_set(p, p_doms),
        !entry_node(n);

    dom_set(*n, Dual(dom_set_with_self(&strict.0, *n))) <--
        strict_dom_set(n, strict),
        !entry_node(n);

    // Post-dominators: dominance on the reversed CFG seeded from exit nodes; an if-join must post-dominate the branch, rejecting joins on one branch's exclusive error path.
    relation exit_node(Node);
    exit_node(*n) <-- stmt(n, _), !cfg_edge(n, _);

    #[local] lattice strict_pdom_set(Node, Dual<Set<Node>>);
    lattice pdom_set(Node, Dual<Set<Node>>);

    pdom_set(*ex, Dual(Set::singleton(*ex))) <--
        exit_node(ex);

    strict_pdom_set(*n, Dual(s_doms.0.clone())) <--
        cfg_edge(n, s),
        pdom_set(s, s_doms),
        !exit_node(n);

    pdom_set(*n, Dual(dom_set_with_self(&strict.0, *n))) <--
        strict_pdom_set(n, strict),
        !exit_node(n);

    // Predecessor relation for reverse walks
    relation pred(Node, Node);
    pred(*to, *from) <-- cfg_edge(from, to);

    // Back edge: CFG edge where the target dominates the source (proper loop detection)
    relation back_edge(Node, Node);
    back_edge(*node, *target) <--
        cfg_edge(node, target),
        dom_set(node, node_doms),
        if node_doms.0.contains(target),
        if *target != *node;
    // Self-loops are always back edges
    back_edge(*node, *node) <--
        cfg_edge(node, target),
        if *target == *node;

    // Natural loop body via reverse walk from latch
    relation loop_header(Node);
    loop_header(*header) <-- back_edge(_, header);

    relation loop_body(Node, Node);
    loop_body(*header, *header) <-- back_edge(_, header);
    loop_body(*header, *src) <-- back_edge(src, header);
    loop_body(*header, *p) <--
        loop_body(header, node),
        pred(node, p),
        dom_set(p, p_doms),
        if p_doms.0.contains(header),
        if *p != *header;

    // Flat projection: node belongs to some loop body (used to guard if-body expansion)
    relation loop_body_node(Node);
    loop_body_node(*node) <-- loop_body(_, node);

    // Auto-vectorized (SIMD) loop bypass: a node whose block held a packed ALU op, whose arithmetic produced no statements and whose computed values are garbage.
    relation packed_alu_node(Node);
    // Broader optimized gap used for acyclic compiler-versioned arms. This is
    // packed_alu_node plus unrepresented REP bulk-memory blocks.
    relation optimized_gap_node(Node);
    relation pointer_reg(RTLReg);

    // A vector loop: a loop whose body contains a packed-ALU node. Its result cannot be trusted.
    relation vector_loop_header(Node);
    vector_loop_header(*h) <-- loop_header(h), loop_body(h, m), packed_alu_node(m);

    // A scalar loop (a real loop with no packed op) is gcc's complete fallback behind a runtime alias/size guard, so routing control to it is the correct recovery.
    relation scalar_loop_header(Node);
    scalar_loop_header(*h) <-- loop_header(h), !vector_loop_header(h);

    // The compiler's alias/range versioning guard computes a byte distance
    // between two pointer values and compares it unsigned against a small
    // constant.  Require the pointer-producing subtraction to dominate the
    // guard; no instruction-address ordering substitutes for this proof.
    relation pointer_carrier_def(Node, RTLReg);
    pointer_carrier_def(*node, *dst) <--
        stmt(node, ?CsharpminorStmt::Sset(dst, CsharpminorExpr::Evar(src))),
        pointer_reg(*src);
    pointer_carrier_def(*node, *dst) <--
        stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        if let CsharpminorExpr::Ebinop(CminorBinop::Oaddl, lhs, rhs) = expr,
        if matches!(rhs.as_ref(), CsharpminorExpr::Econst(_)),
        if let CsharpminorExpr::Evar(src) = lhs.as_ref(),
        pointer_reg(*src);
    pointer_carrier_def(*node, *dst) <--
        stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        if let CsharpminorExpr::Ebinop(CminorBinop::Oaddl, lhs, rhs) = expr,
        if matches!(lhs.as_ref(), CsharpminorExpr::Econst(_)),
        if let CsharpminorExpr::Evar(src) = rhs.as_ref(),
        pointer_reg(*src);

    relation pointer_distance_def(Node, RTLReg);
    pointer_distance_def(*node, *dst) <--
        stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        if let CsharpminorExpr::Ebinop(op, lhs, rhs) = expr,
        if matches!(op, CminorBinop::Osubl),
        if let Some(lhs_reg) = affine_pointer_base(lhs),
        if let Some(rhs_reg) = affine_pointer_base(rhs),
        pointer_reg(lhs_reg),
        pointer_reg(rhs_reg);
    pointer_distance_def(*node, *dst) <--
        stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        if let CsharpminorExpr::Ebinop(CminorBinop::Osubl, lhs, rhs) = expr,
        if let CsharpminorExpr::Evar(lhs_reg) = lhs.as_ref(),
        if lhs_reg == dst,
        if let Some(rhs_reg) = affine_pointer_base(rhs),
        pointer_reg(rhs_reg),
        pointer_carrier_def(origin, dst),
        dom_set(node, dominators),
        if dominators.0.contains(origin);

    relation alias_range_guard(Node);
    alias_range_guard(*guard) <--
        scond_node(guard, _, _),
        stmt(guard, ?CsharpminorStmt::Scond(cond, args, _, _)),
        if matches!(cond,
            Condition::Ccompluimm(Comparison::Cle | Comparison::Clt, _)),
        if args.len() == 1,
        if let CsharpminorExpr::Evar(distance) = &args[0],
        pointer_distance_def(def, distance),
        dom_set(guard, dominators),
        if dominators.0.contains(def);

    relation scond_reaches_optimized_gap(Node);
    scond_reaches_optimized_gap(*target) <--
        scond_target(target),
        optimized_gap_node(gap),
        scond_sources_at(gap, sources),
        if sources.0.contains(target);

    relation structurally_complete_version_guard(Node);
    structurally_complete_version_guard(*guard) <-- join_point(guard, _);
    structurally_complete_version_guard(*guard) <-- scond_no_join(guard);

    // Guard whose one CFG target reaches the vector header and whose other reaches a scalar header without it; rewritten to Sjump(scalar_target), making the vector region dead.
    relation scond_reaches_vector(Node);
    scond_reaches_vector(*t) <--
        scond_target(t),
        vector_loop_header(vh),
        scond_sources_at(vh, sources),
        if sources.0.contains(t);

    relation scond_reaches_scalar_loop(Node);
    scond_reaches_scalar_loop(*t) <--
        scond_target(t),
        scalar_loop_header(sh),
        scond_sources_at(sh, sources),
        if sources.0.contains(t);

    // (guard_node, scalar_arm_target): rewrite guard_node's Scond to Sjump(scalar_arm_target).
    relation vec_bypass_rewrite(Node, Node);
    vec_bypass_rewrite(*g, *f) <--
        scond_node(g, t, f),
        !loop_body_node(g),
        // t is the vector arm, f is the scalar arm
        scond_reaches_vector(t),
        scond_reaches_scalar_loop(f),
        !scond_reaches_vector(f);
    vec_bypass_rewrite(*g, *t) <--
        scond_node(g, t, f),
        !loop_body_node(g),
        // f is the vector arm, t is the scalar arm
        scond_reaches_vector(f),
        scond_reaches_scalar_loop(t),
        !scond_reaches_vector(t);

    // Fixed-size/unrolled versioning has the same compiler contract but no
    // natural loops. When exactly one structurally complete guard target can
    // reach a positively identified optimized gap, route to the other target.
    // Source-set reachability handles shared scalar targets and rejects a gap
    // reached only after both arms reconverge.
    vec_bypass_rewrite(*g, *f) <--
        alias_range_guard(g),
        scond_node(g, t, f),
        structurally_complete_version_guard(g),
        scond_reaches_optimized_gap(t),
        !scond_reaches_optimized_gap(f),
        !loop_body_node(g);
    vec_bypass_rewrite(*g, *t) <--
        alias_range_guard(g),
        scond_node(g, t, f),
        structurally_complete_version_guard(g),
        scond_reaches_optimized_gap(f),
        !scond_reaches_optimized_gap(t),
        !loop_body_node(g);

    // Loop exit condition: Scond where one target stays in the loop and one exits
    relation loop_exit_cond(Node, Node, Node, Node);
    loop_exit_cond(*header, *cond_node, *f, *t) <--
        loop_body(header, cond_node),
        stmt(cond_node, ?CsharpminorStmt::Scond(_, _, t, f)),
        loop_body(header, t),
        !loop_body(header, f);

    loop_exit_cond(*header, *cond_node, *t, *f) <--
        loop_body(header, cond_node),
        stmt(cond_node, ?CsharpminorStmt::Scond(_, _, t, f)),
        loop_body(header, f),
        !loop_body(header, t);

    // Sjump inside loop targeting outside becomes break
    relation loop_break_jump(Node, Node, Node);

    loop_break_jump(*header, *node, *target) <--
        loop_body(header, node),
        stmt(node, ?CsharpminorStmt::Sjump(target)),
        !loop_body(header, target);

    relation goto_is_break(Node, Node);
    goto_is_break(*node, *target) <-- loop_break_jump(_, node, target);

    relation cond_is_break(Node, Node);
    cond_is_break(*cond_node, *exit_target) <-- loop_exit_cond(_, cond_node, exit_target, _);

    relation trim_node(Node);

    // A sequential Sjump is removable only when the jump node is not itself an
    // explicit CFG destination.  Once a targeted jump is removed, the Clight
    // pass must synthesize a label-only placeholder for incoming gotos.  Later
    // structural layout is free to place that label away from the jump's
    // successor, so C fallthrough no longer implements the original edge.
    relation explicit_cfg_target(Node);
    explicit_cfg_target(*target) <--
        stmt(_, ?CsharpminorStmt::Sjump(target));
    explicit_cfg_target(*target) <--
        stmt(_, ?CsharpminorStmt::Scond(_, _, target, _));
    explicit_cfg_target(*target) <--
        stmt(_, ?CsharpminorStmt::Scond(_, _, _, target));
    explicit_cfg_target(*target) <--
        jumptable_target(_, target);

    // Keep explicit jumps through structural assembly.  `seq_next` is allowed
    // to use the semantic Cminor CFG for synthetic expansion stages, whereas
    // removing a jump requires a proof about the final printed layout.  In
    // particular, an ordinary Sjump has its target as its sole semantic
    // successor; treating that fact as physical fallthrough deletes every
    // untargeted forward jump.  GotoElide runs after all tree rewrites and is
    // the layer that can safely remove a transfer whose label is truly next.

    // Do not erase an if-arm's explicit jump merely because its target is in
    // the same structural arm or is the arm's join.  Collected nodes are not
    // necessarily adjacent in layout, and the other arm can remain top-level;
    // falling out of such a node would execute unrelated statements first.
    // The sequential-next rule above is the structural proof that an ordinary
    // jump is an actual fallthrough.

    // Deleting a back-edge jump assumes position supplies the loop-back, which
    // only one node per loop can do: the body's last statement.  A header
    // reached by several back edges therefore cannot have them all implicit.
    // Every `break` in a getopt-style dispatch is a back edge to the loop
    // header, so trimming them all made each switch case fall through into the
    // next one and finally into the no-match error path.  With the jump kept,
    // clight_select converts it to Scontinue (or leaves an explicit goto),
    // both of which re-enter the loop.
    relation multi_latch_header(Node);
    multi_latch_header(*header) <--
        back_edge(a, header),
        back_edge(b, header),
        if a != b;

    trim_node(*node) <--
        back_edge(node, target),
        stmt(node, ?CsharpminorStmt::Sjump(_)),
        !multi_latch_header(target);

    trim_node(*node) <-- goto_is_break(node, _);
    trim_node(*node) <-- cond_is_break(node, _);

    // Switch chain detection over if-else-if equality chains, excluding loop-exit conditions, or the chain extends across the break test and the case bodies are trimmed as switch interior.
    relation compares_eq(Node, u64, i64, Node, Node);

    // Ceq: true branch is the matching case, false branch continues
    compares_eq(*node, *reg, *val, *t, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompimm(cmp, val) = cond,
        if *cmp == Comparison::Ceq,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0],
        !cond_is_break(node, _);

    compares_eq(*node, *reg, *val, *t, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompuimm(cmp, val) = cond,
        if *cmp == Comparison::Ceq,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0],
        !cond_is_break(node, _);

    compares_eq(*node, *reg, *val, *t, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccomplimm(cmp, val) = cond,
        if *cmp == Comparison::Ceq,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0],
        !cond_is_break(node, _);

    compares_eq(*node, *reg, *val, *t, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompluimm(cmp, val) = cond,
        if *cmp == Comparison::Ceq,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0],
        !cond_is_break(node, _);

    // Cne: inverted; false branch matches (reg == val), true continues
    compares_eq(*node, *reg, *val, *f, *t) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompimm(cmp, val) = cond,
        if *cmp == Comparison::Cne,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0],
        !cond_is_break(node, _);

    compares_eq(*node, *reg, *val, *f, *t) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompuimm(cmp, val) = cond,
        if *cmp == Comparison::Cne,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0],
        !cond_is_break(node, _);

    compares_eq(*node, *reg, *val, *f, *t) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccomplimm(cmp, val) = cond,
        if *cmp == Comparison::Cne,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0],
        !cond_is_break(node, _);

    compares_eq(*node, *reg, *val, *f, *t) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompluimm(cmp, val) = cond,
        if *cmp == Comparison::Cne,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0],
        !cond_is_break(node, _);

    relation switch_chain(Node, Node, u64, i64, Node);
    switch_chain(*node, *node, *reg, *val, *t) <--
        compares_eq(node, reg, val, t, _);

    // Direct chain only: false branch of prev is a compares_eq on the same register. Bridge rules across non-Ceq Sconds were removed because their Scond outlived the dead-coded chain and jumped to dropped members.
    switch_chain(*head, *f, *reg, *next_val, *next_t) <--
        switch_chain(head, prev, reg, _, _),
        compares_eq(prev, _, _, _, f),
        compares_eq(f, reg, next_val, next_t, _);

    relation switch_count(Node, usize);
    switch_count(*head, count) <--
        switch_chain(head, _, _, _, _),
        agg count = ascent::aggregators::count() in switch_chain(head, _, _, _, _);

    relation valid_switch(Node, u64);
    valid_switch(*head, *reg) <--
        switch_count(head, count),
        if *count >= 3,
        switch_chain(head, _, reg, _, _);

    relation is_interior_member(Node);
    is_interior_member(*member) <--
        switch_chain(head, member, _, _, _),
        if head != member;

    relation primary_switch(Node, u64);
    primary_switch(*head, *reg) <--
        valid_switch(head, reg),
        !is_interior_member(head);

    relation switch_default(Node, Node);
    switch_default(*head, *f) <--
        primary_switch(head, _),
        switch_chain(head, member, _, _, _),
        compares_eq(member, _, _, _, f),
        !switch_chain(head, f, _, _, _);

    trim_node(*member) <--
        primary_switch(head, _),
        switch_chain(head, member, _, _, _),
        if head != member;

}

#[cfg(test)]
mod structural_lattice_tests {
    use super::{
        compute_sequential_edges, detect_comparison_tree_switches, structure,
        unmerge_pure_branch_tails, StructuringProgram,
    };
    use crate::util::{MULTI_SYNTH_NODE_BIT, MULTI_SYNTH_STAGE_SHIFT};
    use crate::x86::op::{Comparison, Condition};
    use crate::x86::types::{CminorBinop, Constant, CsharpminorExpr, CsharpminorStmt};
    use std::collections::{HashMap, HashSet};

    fn synthetic_ids<const N: usize>() -> [u64; N] {
        std::array::from_fn(|index| index as u64 + 1)
    }

    #[test]
    fn acyclic_alias_versioning_routes_around_unrepresented_optimized_arm() {
        const PTR_A: u64 = 10;
        const PTR_B: u64 = 11;
        const DISTANCE: u64 = 12;
        let [carrier, distance_def, guard, scalar, optimized] = synthetic_ids();

        let mut prog = StructuringProgram::default();
        prog.stmt.extend([
            (
                carrier,
                CsharpminorStmt::Sset(DISTANCE, CsharpminorExpr::Evar(PTR_A)),
            ),
            (
                distance_def,
                CsharpminorStmt::Sset(
                    DISTANCE,
                    CsharpminorExpr::Ebinop(
                        CminorBinop::Osubl,
                        Box::new(CsharpminorExpr::Evar(DISTANCE)),
                        Box::new(CsharpminorExpr::Evar(PTR_B)),
                    ),
                ),
            ),
            (
                guard,
                CsharpminorStmt::Scond(
                    Condition::Ccompluimm(Comparison::Cle, 8),
                    vec![CsharpminorExpr::Evar(DISTANCE)],
                    scalar,
                    optimized,
                ),
            ),
            (
                scalar,
                CsharpminorStmt::Sreturn(CsharpminorExpr::Econst(Constant::Olongconst(1))),
            ),
            (
                optimized,
                CsharpminorStmt::Sreturn(CsharpminorExpr::Econst(Constant::Olongconst(2))),
            ),
        ]);
        prog.seq_next
            .extend([(carrier, distance_def), (distance_def, guard)]);
        prog.entry_node.push((carrier,));
        prog.pointer_reg.extend([(PTR_A,), (PTR_B,)]);
        prog.optimized_gap_node.push((optimized,));

        prog.run();

        assert!(prog.alias_range_guard.iter().any(|fact| fact == &(guard,)));
        assert!(prog
            .vec_bypass_rewrite
            .iter()
            .any(|fact| fact == &(guard, scalar)));

        let mut nonpointer = StructuringProgram::default();
        nonpointer.stmt = prog.stmt.clone();
        nonpointer.seq_next = prog.seq_next.clone();
        nonpointer.entry_node.push((carrier,));
        nonpointer.optimized_gap_node.push((optimized,));
        nonpointer.run();
        assert!(nonpointer.vec_bypass_rewrite.is_empty());
    }

    #[test]
    fn multi_stage_expansion_uses_semantic_cfg_not_raw_bypass() {
        let event = 0x900;
        let stage1 = event | MULTI_SYNTH_NODE_BIT | (1 << MULTI_SYNTH_STAGE_SHIFT);
        let stage2 = event | MULTI_SYNTH_NODE_BIT | (2 << MULTI_SYNTH_STAGE_SHIFT);
        let next = 0x50;
        let stmts = [event, stage1, stage2, next]
            .into_iter()
            .map(|node| (node, CsharpminorStmt::Snop))
            .collect::<Vec<_>>();
        let raw_next = HashMap::from([(event, next)]);
        let semantic_succs = HashMap::from([
            (event, vec![stage1]),
            (stage1, vec![stage2]),
            (stage2, vec![next]),
        ]);
        let expansion_sources = HashSet::from([event, stage1, stage2]);

        let edges =
            compute_sequential_edges(&stmts, &raw_next, &semantic_succs, &expansion_sources);

        assert!(edges.contains(&(event, stage1)));
        assert!(edges.contains(&(stage1, stage2)));
        assert!(edges.contains(&(stage2, next)));
        assert!(!edges.contains(&(event, next)));
    }

    #[test]
    fn retargeted_predecessor_enters_surviving_multi_stage_tail() {
        let pred = 0x10;
        let removed_stage0 = 0x900;
        let stage1 = removed_stage0 | MULTI_SYNTH_NODE_BIT | (1 << MULTI_SYNTH_STAGE_SHIFT);
        let next = 0x50;
        let stmts = [pred, stage1, next]
            .into_iter()
            .map(|node| (node, CsharpminorStmt::Snop))
            .collect::<Vec<_>>();
        // Machine layout still bypasses the expansion, but optimizer CFG
        // repair has structurally retargeted the ordinary predecessor.
        let raw_next = HashMap::from([(pred, next)]);
        let semantic_succs = HashMap::from([(pred, vec![stage1]), (stage1, vec![next])]);
        let expansion_sources = HashSet::from([removed_stage0, stage1]);

        let edges =
            compute_sequential_edges(&stmts, &raw_next, &semantic_succs, &expansion_sources);

        assert!(edges.contains(&(pred, stage1)));
        assert!(edges.contains(&(stage1, next)));
        assert!(!edges.contains(&(pred, next)));
    }

    #[test]
    fn tail_unmerge_preserves_every_multi_stage_statement() {
        let pred1 = 0x10;
        let pred2 = 0x20;
        let event = 0x900;
        let stage1 = event | MULTI_SYNTH_NODE_BIT | (1 << MULTI_SYNTH_STAGE_SHIFT);
        let stage2 = event | MULTI_SYNTH_NODE_BIT | (2 << MULTI_SYNTH_STAGE_SHIFT);
        let jump = 0x50;
        let ret = 0x60;
        let event_stmt = CsharpminorStmt::Sset(1, CsharpminorExpr::Evar(10));
        let stage1_stmt = CsharpminorStmt::Sset(2, CsharpminorExpr::Evar(11));
        let stage2_stmt = CsharpminorStmt::Sset(3, CsharpminorExpr::Evar(12));
        let jump_stmt = CsharpminorStmt::Sjump(ret);
        let expected = vec![
            event_stmt.clone(),
            stage1_stmt.clone(),
            stage2_stmt.clone(),
            jump_stmt.clone(),
        ];
        let mut stmts = vec![
            (pred1, CsharpminorStmt::Sjump(event)),
            (pred2, CsharpminorStmt::Sjump(event)),
            (event, event_stmt),
            (stage1, stage1_stmt),
            (stage2, stage2_stmt),
            (jump, jump_stmt),
            (ret, CsharpminorStmt::Sreturn(CsharpminorExpr::Evar(3))),
        ];
        // Raw machine fallthrough jumps directly from the real event to the
        // next real instruction; the semantic Cminor CFG contains its scalar
        // stages and is authoritative for duplication.
        let raw_next = HashMap::from([(event, jump)]);
        let semantic_succs = HashMap::from([
            (event, vec![stage1]),
            (stage1, vec![stage2]),
            (stage2, vec![jump]),
        ]);
        let expansion_sources = HashSet::from([event, stage1, stage2]);

        unmerge_pure_branch_tails(&mut stmts, &raw_next, &semantic_succs, &expansion_sources);

        let duplicate = event | (1u64 << 62);
        assert!(stmts.iter().any(|(node, stmt)| {
            *node == duplicate
                && matches!(stmt, CsharpminorStmt::Sseq(seq) if seq.as_slice() == expected.as_slice())
        }));
    }

    #[test]
    fn nonmonotonic_diamond_uses_point_lattices_for_its_join() {
        let [true_arm, join, branch, exit, false_arm] = synthetic_ids();

        // Neither address order nor distance describes this diamond: one arm
        // runs numerically backward and the other forward, while JOIN is below
        // both the branch and false arm.
        let mut prog = StructuringProgram::default();
        prog.entry_node.push((branch,));
        prog.stmt.push((
            branch,
            CsharpminorStmt::Scond(
                Condition::Ccompimm(Comparison::Ceq, 0),
                vec![],
                true_arm,
                false_arm,
            ),
        ));
        for node in [true_arm, false_arm, join, exit] {
            prog.stmt.push((node, CsharpminorStmt::Snop));
        }
        prog.seq_next.push((true_arm, join));
        prog.seq_next.push((false_arm, join));
        prog.seq_next.push((join, exit));

        prog.run();

        assert!(prog.join_point.iter().any(|fact| fact == &(branch, join)));
        assert!(!prog.join_point.iter().any(|fact| fact == &(branch, exit)));
        assert!(prog.scond_sources_at.iter().any(|fact| {
            let fact = fact.read().expect("scond source lattice lock poisoned");
            fact.0 == join && fact.1 .0.contains(&true_arm) && fact.1 .0.contains(&false_arm)
        }));
    }

    #[test]
    fn out_of_line_if_arm_preserves_explicit_join_jump() {
        const BRANCH: u64 = 0x4000;
        const TRUE_ARM: u64 = 0x9000;
        const TRUE_TAIL: u64 = 0x0800;
        const FALSE_ARM: u64 = 0x1000;
        const JOIN: u64 = 0x2000;
        const EXIT: u64 = 0x3000;
        const PHYSICAL_AFTER_TRUE: u64 = 0xa000;
        const PHYSICAL_AFTER_TAIL: u64 = 0x0900;

        // The true arm is physically out of line.  Its first jump targets a
        // member of the same arm and its tail jumps to JOIN, but neither
        // target is the jump's layout successor.  Replacing either edge with C
        // fallthrough would execute the wrong region first.
        let mut prog = StructuringProgram::default();
        prog.entry_node.push((BRANCH,));
        prog.stmt.push((
            BRANCH,
            CsharpminorStmt::Scond(
                Condition::Ccompimm(Comparison::Ceq, 0),
                vec![],
                TRUE_ARM,
                FALSE_ARM,
            ),
        ));
        prog.stmt
            .push((TRUE_ARM, CsharpminorStmt::Sjump(TRUE_TAIL)));
        prog.stmt.push((TRUE_TAIL, CsharpminorStmt::Sjump(JOIN)));
        for node in [
            FALSE_ARM,
            JOIN,
            EXIT,
            PHYSICAL_AFTER_TRUE,
            PHYSICAL_AFTER_TAIL,
        ] {
            prog.stmt.push((node, CsharpminorStmt::Snop));
        }
        prog.seq_next.push((FALSE_ARM, JOIN));
        prog.seq_next.push((JOIN, EXIT));
        prog.seq_next.push((TRUE_ARM, PHYSICAL_AFTER_TRUE));
        prog.seq_next.push((TRUE_TAIL, PHYSICAL_AFTER_TAIL));

        prog.run();

        assert!(prog.join_point.iter().any(|fact| fact == &(BRANCH, JOIN)));
        assert!(prog
            .ifbody_true
            .iter()
            .any(|fact| fact == &(BRANCH, TRUE_ARM)));
        assert!(prog
            .ifbody_true
            .iter()
            .any(|fact| fact == &(BRANCH, TRUE_TAIL)));
        assert!(!prog.trim_node.iter().any(|fact| fact == &(TRUE_ARM,)));
        assert!(!prog.trim_node.iter().any(|fact| fact == &(TRUE_TAIL,)));
    }

    #[test]
    fn targeted_sequential_jump_remains_an_explicit_transfer() {
        const ENTRY: u64 = 0x9000;
        const LANDING_PAD: u64 = 0x0100;
        const EPILOGUE: u64 = 0x0200;

        // LANDING_PAD's jump happens to target its physical successor, but an
        // out-of-line predecessor targets the pad.  Dropping the jump would
        // leave only a synthesized label whose later C layout need not remain
        // adjacent to EPILOGUE.
        let mut prog = StructuringProgram::default();
        prog.entry_node.push((ENTRY,));
        prog.stmt.push((ENTRY, CsharpminorStmt::Sjump(LANDING_PAD)));
        prog.stmt
            .push((LANDING_PAD, CsharpminorStmt::Sjump(EPILOGUE)));
        prog.stmt.push((EPILOGUE, CsharpminorStmt::Snop));
        prog.seq_next.push((LANDING_PAD, EPILOGUE));

        prog.run();

        assert!(prog
            .explicit_cfg_target
            .iter()
            .any(|fact| fact == &(LANDING_PAD,)));
        assert!(!prog.trim_node.iter().any(|fact| fact == &(LANDING_PAD,)));
    }

    #[test]
    fn untargeted_semantic_successor_does_not_prove_layout_fallthrough() {
        const JUMP: u64 = 0x10;
        const TARGET: u64 = 0x80;

        let mut prog = StructuringProgram::default();
        prog.entry_node.push((JUMP,));
        prog.stmt.push((JUMP, CsharpminorStmt::Sjump(TARGET)));
        prog.stmt.push((TARGET, CsharpminorStmt::Snop));
        // This is exactly what happens when sequential-edge recovery is fed
        // the authoritative Cminor successor of an explicit jump.  It is a
        // semantic edge, not evidence that TARGET will be printed next.
        prog.seq_next.push((JUMP, TARGET));

        prog.run();

        assert!(!prog.trim_node.iter().any(|fact| fact == &(JUMP,)));
    }

    #[test]
    fn comparison_tree_crossing_a_loop_exit_is_not_partially_lifted() {
        let [second, loop_exit_leaf, head, case_one, case_two, case_three, exit_case, default, third] =
            synthetic_ids();
        const DISC: u64 = 7;

        let eq = |value, ifso, ifnot| {
            CsharpminorStmt::Scond(
                Condition::Ccompuimm(Comparison::Ceq, value),
                vec![CsharpminorExpr::Evar(DISC)],
                ifso,
                ifnot,
            )
        };
        let stmts = vec![
            (head, eq(1, case_one, second)),
            (second, eq(2, case_two, third)),
            (third, eq(3, case_three, loop_exit_leaf)),
            (loop_exit_leaf, eq(4, exit_case, default)),
        ];
        let break_nodes = HashSet::from([loop_exit_leaf]);

        let switches = detect_comparison_tree_switches(&stmts, &HashMap::new(), &break_nodes);

        // Silently truncating at LOOP_EXIT_LEAF would fabricate a three-case
        // switch and lose both its case and default edges.  Keep the original
        // CFG until switch/default and loop-exit structure can be represented
        // together.
        assert!(switches.is_empty());
    }

    #[test]
    fn comparison_chain_records_its_unmatched_default_edge() {
        let [head, second, third, case_one, case_two, case_three, default] = synthetic_ids();
        const DISC: u64 = 7;
        let eq = |value, ifso, ifnot| {
            CsharpminorStmt::Scond(
                Condition::Ccompimm(Comparison::Ceq, value),
                vec![CsharpminorExpr::Evar(DISC)],
                ifso,
                ifnot,
            )
        };
        let stmts = vec![
            (head, eq(1, case_one, second)),
            (second, eq(2, case_two, third)),
            (third, eq(3, case_three, default)),
            (case_one, CsharpminorStmt::Snop),
            (case_two, CsharpminorStmt::Snop),
            (case_three, CsharpminorStmt::Snop),
            (default, CsharpminorStmt::Snop),
        ];
        let mut preds: HashMap<u64, Vec<u64>> = HashMap::new();
        for (source, stmt) in &stmts {
            if let CsharpminorStmt::Scond(_, _, ifso, ifnot) = stmt {
                preds.entry(*ifso).or_default().push(*source);
                preds.entry(*ifnot).or_default().push(*source);
            }
        }

        let structured = structure(
            &stmts,
            &HashMap::new(),
            &HashMap::new(),
            &HashSet::new(),
            Some(head),
            &preds,
            &HashSet::new(),
            &HashSet::new(),
            &HashSet::new(),
        );

        assert!(structured
            .switch_defaults
            .iter()
            .any(|fact| fact == &(head, default)));
    }

    #[test]
    fn range_switch_default_includes_the_rowless_root_exit() {
        let [head, second, third, below, gap, middle, above] = synthetic_ids();
        let condition = |cmp, value, yes, no| {
            CsharpminorStmt::Scond(
                Condition::Ccompimm(cmp, value),
                vec![CsharpminorExpr::Evar(7)],
                yes,
                no,
            )
        };
        // x<=10 takes BELOW; 11..12 takes GAP; 13..16 takes MIDDLE;
        // x>16 takes ABOVE. A switch rooted at HEAD cannot use just ABOVE
        // as its default: the unbounded BELOW arm has no enumerable rows.
        let stmts = vec![
            (head, condition(Comparison::Cgt, 10, second, below)),
            (second, condition(Comparison::Cle, 12, gap, third)),
            (third, condition(Comparison::Cle, 16, middle, above)),
            (
                below,
                CsharpminorStmt::Sreturn(CsharpminorExpr::Econst(Constant::Ointconst(1))),
            ),
            (
                gap,
                CsharpminorStmt::Sreturn(CsharpminorExpr::Econst(Constant::Ointconst(2))),
            ),
            (
                middle,
                CsharpminorStmt::Sreturn(CsharpminorExpr::Econst(Constant::Ointconst(3))),
            ),
            (
                above,
                CsharpminorStmt::Sreturn(CsharpminorExpr::Econst(Constant::Ointconst(4))),
            ),
        ];
        let mut preds: HashMap<u64, Vec<u64>> = HashMap::new();
        for (node, stmt) in &stmts {
            if let CsharpminorStmt::Scond(_, _, yes, no) = stmt {
                preds.entry(*yes).or_default().push(*node);
                preds.entry(*no).or_default().push(*node);
            }
        }
        let result = structure(
            &stmts,
            &HashMap::new(),
            &HashMap::new(),
            &HashSet::new(),
            Some(head),
            &preds,
            &HashSet::new(),
            &HashSet::new(),
            &HashSet::new(),
        );
        assert!(!result.valid_switches.iter().any(|(root, _)| *root == head));
    }

    #[test]
    fn parity_partition_is_not_collapsed_to_a_single_switch_case() {
        let [head, small, parity, nonprime, prime, trial] = synthetic_ids();
        const DISC: u64 = 7;
        let stmts = vec![
            (
                head,
                CsharpminorStmt::Scond(
                    Condition::Ccompimm(Comparison::Cle, 1),
                    vec![CsharpminorExpr::Evar(DISC)],
                    nonprime,
                    small,
                ),
            ),
            (
                small,
                CsharpminorStmt::Scond(
                    Condition::Ccompimm(Comparison::Cle, 3),
                    vec![CsharpminorExpr::Evar(DISC)],
                    prime,
                    parity,
                ),
            ),
            (
                parity,
                CsharpminorStmt::Scond(
                    Condition::Cmaskzero(1),
                    vec![CsharpminorExpr::Evar(DISC)],
                    nonprime,
                    trial,
                ),
            ),
            (nonprime, CsharpminorStmt::Snop),
            (prime, CsharpminorStmt::Snop),
            (trial, CsharpminorStmt::Snop),
        ];

        let switches = detect_comparison_tree_switches(&stmts, &HashMap::new(), &HashSet::new());

        assert!(switches.is_empty());
    }

    #[test]
    fn comparison_tree_suffix_is_not_redirected_to_full_switch_head() {
        let [suffix, low, case_60, case_62, case_37, case_47, head, low_tail, high, default] =
            synthetic_ids();
        const DISC: u64 = 7;

        let cond = |cmp, value, ifso, ifnot| {
            CsharpminorStmt::Scond(
                Condition::Ccompuimm(cmp, value),
                vec![CsharpminorExpr::Evar(DISC)],
                ifso,
                ifnot,
            )
        };
        let stmts = vec![
            (head, cond(Comparison::Ceq, 60, case_60, suffix)),
            (
                suffix,
                CsharpminorStmt::Scond(
                    Condition::Ccompimm(Comparison::Cgt, 60),
                    vec![CsharpminorExpr::Evar(DISC)],
                    high,
                    low,
                ),
            ),
            (high, cond(Comparison::Cne, 62, default, case_62)),
            (low, cond(Comparison::Ceq, 37, case_37, low_tail)),
            (low_tail, cond(Comparison::Cne, 47, default, case_47)),
            (case_60, CsharpminorStmt::Snop),
            (case_62, CsharpminorStmt::Snop),
            (case_37, CsharpminorStmt::Snop),
            (case_47, CsharpminorStmt::Snop),
            (default, CsharpminorStmt::Snop),
        ];
        let mut preds: HashMap<u64, Vec<u64>> = HashMap::new();
        for (src, stmt) in &stmts {
            if let CsharpminorStmt::Scond(_, _, ifso, ifnot) = stmt {
                preds.entry(*ifso).or_default().push(*src);
                preds.entry(*ifnot).or_default().push(*src);
            }
        }

        let structured = structure(
            &stmts,
            &HashMap::new(),
            &HashMap::new(),
            &HashSet::new(),
            Some(head),
            &preds,
            &HashSet::new(),
            &HashSet::new(),
            &HashSet::new(),
        );

        assert!(structured
            .valid_switches
            .iter()
            .any(|(switch_head, _)| *switch_head == head));
        let suffix_stmt = structured
            .stmts
            .iter()
            .find_map(|(node, stmt)| (*node == suffix).then_some(stmt))
            .expect("suffix comparison remains represented");
        assert!(
            matches!(suffix_stmt, CsharpminorStmt::Scond(..)),
            "strict switch suffix was redirected to the full head: {suffix_stmt:#?}"
        );
    }
}

pub struct StructuringResult {
    pub stmts: Vec<(Node, CsharpminorStmt)>,
    pub switch_chain_members: Vec<(Node, Node, u64, i64, Node)>,
    pub valid_switches: Vec<(Node, u64)>,
    pub switch_defaults: Vec<(Node, Node)>,
    pub ifbody_true: Vec<(Node, Node)>,
    pub ifbody_false: Vec<(Node, Node)>,
    pub join_points: Vec<(Node, Node)>,
    pub scond_no_join: Vec<Node>,
}

// Un-merge a shared value-assigning tail reached only by >=2 explicit branches, so structuring folds each copy into its own arm instead of leaving one block to interpose in a fall-through slot.
fn unmerge_pure_branch_tails(
    current_stmts: &mut Vec<(Node, CsharpminorStmt)>,
    next_map: &HashMap<Node, Node>,
    cminor_succs: &HashMap<Node, Vec<Node>>,
    expansion_sources: &HashSet<Node>,
) {
    const SYNTH_BIT: u64 = 1u64 << 62;
    const SYNTH_BIT2: u64 = 1u64 << 63;
    const MAX_TAIL: usize = 8;

    let stmt_map: HashMap<Node, CsharpminorStmt> = current_stmts.iter().cloned().collect();
    let stmt_nodes: HashSet<Node> = current_stmts.iter().map(|(n, _)| *n).collect();

    let stmt_next = |n: Node| -> Option<Node> {
        sequential_stmt_successor(n, next_map, cminor_succs, expansion_sources, &stmt_nodes)
    };

    let branch_targets = |s: &CsharpminorStmt| -> Vec<Node> {
        match s {
            CsharpminorStmt::Sjump(t) => vec![*t],
            CsharpminorStmt::Scond(_, _, t, f) => vec![*t, *f],
            CsharpminorStmt::Sjumptable(_, targets) => targets.as_ref().to_vec(),
            _ => vec![],
        }
    };

    let mut branch_preds: HashMap<Node, Vec<Node>> = HashMap::new();
    let mut fall_preds: HashMap<Node, Vec<Node>> = HashMap::new();
    for (n, s) in current_stmts.iter() {
        for t in branch_targets(s) {
            if stmt_nodes.contains(&t) {
                branch_preds.entry(t).or_default().push(*n);
            }
        }
        if !is_terminal_stmt(s) {
            if let Some(nx) = stmt_next(*n) {
                fall_preds.entry(nx).or_default().push(*n);
            }
        }
    }
    let pred_count = |node: Node| -> usize {
        branch_preds.get(&node).map_or(0, |v| v.len())
            + fall_preds.get(&node).map_or(0, |v| v.len())
    };

    let mut new_stmts: Vec<(Node, CsharpminorStmt)> = Vec::new();
    let mut rewires: HashMap<Node, Vec<(Node, Node)>> = HashMap::new();

    let mut entries: Vec<Node> = stmt_nodes.iter().copied().collect();
    entries.sort_unstable();
    for entry in entries {
        let bps: Vec<Node> = match branch_preds.get(&entry) {
            Some(v) => {
                let mut d = v.clone();
                d.sort_unstable();
                d.dedup();
                d
            }
            None => continue,
        };
        if !(2..=3).contains(&bps.len()) {
            continue;
        }
        // Reached ONLY by branches: no fall-through pred to anchor the block in place.
        if fall_preds.get(&entry).map_or(0, |v| v.len()) != 0 {
            continue;
        }
        let synth_ids = [entry | SYNTH_BIT, entry | SYNTH_BIT2];
        if synth_ids.iter().any(|s| stmt_nodes.contains(s)) {
            continue;
        }
        // Every pred we redirect must be a retargetable Scond/Sjump.
        if bps.iter().any(|p| {
            !matches!(
                stmt_map.get(p),
                Some(CsharpminorStmt::Scond(_, _, _, _)) | Some(CsharpminorStmt::Sjump(_))
            )
        }) {
            continue;
        }
        // Bounded single-entry straight-line tail ending in an unconditional jump.
        let mut chain: Vec<Node> = vec![entry];
        let mut cur = entry;
        let mut ok = false;
        loop {
            let s = &stmt_map[&cur];
            if is_terminal_stmt(s) {
                ok = matches!(s, CsharpminorStmt::Sjump(_));
                break;
            }
            let nx = match stmt_next(cur) {
                Some(nx) if stmt_nodes.contains(&nx) => nx,
                _ => break,
            };
            if pred_count(nx) != 1 {
                break;
            }
            if chain.len() >= MAX_TAIL {
                break;
            }
            chain.push(nx);
            cur = nx;
        }
        if !ok {
            continue;
        }
        // Hazard gate: assigns a value (the datum a mis-fallen-through path inherits) and has no call, since call tails are a different hazard.
        if chain
            .iter()
            .any(|n| matches!(stmt_map[n], CsharpminorStmt::Scall(_, _, _, _)))
        {
            continue;
        }
        if !chain.iter().any(|n| {
            matches!(
                stmt_map[n],
                CsharpminorStmt::Sset(_, _) | CsharpminorStmt::Sstore(_, _, _)
            )
        }) {
            continue;
        }
        // Scope to RETURN tails: follow the exit jump through straight-line nodes and require an Sreturn, since duplicating into a loop continuation or switch merge would mangle it.
        let jump_target = match &stmt_map[chain.last().unwrap()] {
            CsharpminorStmt::Sjump(t) => *t,
            _ => continue,
        };
        let mut cur_r = jump_target;
        let mut reaches_return = false;
        for _ in 0..24 {
            match stmt_map.get(&cur_r) {
                Some(CsharpminorStmt::Sreturn(_)) => {
                    reaches_return = true;
                    break;
                }
                Some(CsharpminorStmt::Sjump(t)) => cur_r = *t,
                Some(s) if is_terminal_stmt(s) => break,
                _ => match stmt_next(cur_r) {
                    Some(nx) => cur_r = nx,
                    None => break,
                },
            }
        }
        if !reaches_return {
            continue;
        }
        let seq: Vec<CsharpminorStmt> = chain.iter().map(|n| stmt_map[n].clone()).collect();
        for (i, &pred) in bps[..bps.len() - 1].iter().enumerate() {
            new_stmts.push((synth_ids[i], CsharpminorStmt::Sseq(seq.clone())));
            rewires.entry(pred).or_default().push((entry, synth_ids[i]));
        }
    }

    if new_stmts.is_empty() {
        return;
    }

    for (n, s) in current_stmts.iter_mut() {
        if let Some(edits) = rewires.get(n) {
            for &(from, to) in edits {
                match s {
                    CsharpminorStmt::Sjump(t) => {
                        if *t == from {
                            *t = to;
                        }
                    }
                    CsharpminorStmt::Scond(_, _, t, f) => {
                        if *t == from {
                            *t = to;
                        }
                        if *f == from {
                            *f = to;
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    current_stmts.extend(new_stmts);
}

// Run CFG analysis, if-then-else construction, loop recovery, and break/continue conversion
pub fn structure(
    stmts: &[(Node, CsharpminorStmt)],
    next_map: &HashMap<Node, Node>,
    cminor_succs: &HashMap<Node, Vec<Node>>,
    expansion_sources: &HashSet<Node>,
    declared_entry: Option<Node>,
    cminor_preds: &HashMap<Node, Vec<Node>>,
    packed_alu_nodes: &HashSet<Node>,
    optimized_gap_nodes: &HashSet<Node>,
    pointer_regs: &HashSet<RTLReg>,
) -> StructuringResult {
    structure_with_memo(
        stmts,
        next_map,
        cminor_succs,
        expansion_sources,
        declared_entry,
        cminor_preds,
        packed_alu_nodes,
        optimized_gap_nodes,
        pointer_regs,
        None,
    )
}

fn structure_with_memo(
    stmts: &[(Node, CsharpminorStmt)],
    next_map: &HashMap<Node, Node>,
    cminor_succs: &HashMap<Node, Vec<Node>>,
    expansion_sources: &HashSet<Node>,
    declared_entry: Option<Node>,
    cminor_preds: &HashMap<Node, Vec<Node>>,
    packed_alu_nodes: &HashSet<Node>,
    optimized_gap_nodes: &HashSet<Node>,
    pointer_regs: &HashSet<RTLReg>,
    memo: Option<&structuring_memo::Fixpoints>,
) -> StructuringResult {
    if stmts.is_empty() {
        return StructuringResult {
            stmts: vec![],
            switch_chain_members: vec![],
            valid_switches: vec![],
            switch_defaults: vec![],
            ifbody_true: vec![],
            ifbody_false: vec![],
            join_points: vec![],
            scond_no_join: vec![],
        };
    }

    let mut current_stmts: Vec<(Node, CsharpminorStmt)> = stmts.to_vec();
    current_stmts.sort_by_key(|(n, _)| exec_order_key(*n));

    // Resolve synthetic/missing Scond targets by walking `next` chain.
    let stmt_nodes: HashSet<Node> = current_stmts.iter().map(|(n, _)| *n).collect();

    let resolve_target = |target: Node| -> Node {
        if stmt_nodes.contains(&target) {
            return target;
        }
        let real_addr = semantic_node_address(target);
        if stmt_nodes.contains(&real_addr) {
            return real_addr;
        }
        // Resolves into synthetic chains too: a branch may land on a fused store (e.g. `global = CONST`) whose real head has no statement after const folding.
        walk_next_to_stmt(real_addr, next_map, &stmt_nodes).unwrap_or(target)
    };

    for (_, stmt) in &mut current_stmts {
        match stmt {
            CsharpminorStmt::Scond(_, _, ifso, ifnot) => {
                *ifso = resolve_target(*ifso);
                *ifnot = resolve_target(*ifnot);
            }
            CsharpminorStmt::Sjump(target) => {
                *target = resolve_target(*target);
            }
            _ => {}
        }
    }

    // Un-merge shared value tails before dominance is computed, so structuring folds each copy into its arm (see unmerge_pure_branch_tails).
    unmerge_pure_branch_tails(
        &mut current_stmts,
        next_map,
        cminor_succs,
        expansion_sources,
    );

    let mut prog = StructuringProgram::default();

    for (node, s) in &current_stmts {
        prog.stmt.push((*node, s.clone()));
        if packed_alu_nodes.contains(node) {
            prog.packed_alu_node.push((*node,));
        }
        if optimized_gap_nodes.contains(node) {
            prog.optimized_gap_node.push((*node,));
        }
    }
    // pointer_reg is only consumed at a variable use in stmt. This exact
    // semijoin removes unrelated functions' pointer facts from the pure
    // analysis input, without approximating any CFG or dataflow relation.
    let used_regs: HashSet<_> = current_stmts
        .iter()
        .flat_map(|(_, stmt)| stmt_uses_set(stmt))
        .collect();
    prog.pointer_reg
        .extend(used_regs.intersection(pointer_regs).map(|reg| (*reg,)));

    let seq_edges =
        compute_sequential_edges(&current_stmts, next_map, cminor_succs, expansion_sources);
    for &(a, b) in &seq_edges {
        prog.seq_next.push((a, b));
    }

    for (node, stmt) in &current_stmts {
        if let CsharpminorStmt::Sjumptable(_, targets) = stmt {
            for t in targets.as_ref() {
                prog.jumptable_target.push((*node, *t));
            }
        }
    }

    // Authoritative entry from emit_function, resolved to a stmt node through `next` chain; falls back to lowest-address stmt if emit_function entry is missing or unreachable.
    let entry_node = declared_entry
        .and_then(|e| {
            if stmt_nodes.contains(&e) {
                Some(e)
            } else {
                walk_next_to_stmt(e, next_map, &stmt_nodes)
            }
        })
        .unwrap_or_else(|| {
            debug!("structuring: falling back to lowest-address entry");
            current_stmts[0].0
        });
    prog.entry_node.push((entry_node,));

    // Cache only the Ascent fixpoint's exported facts. Target resolution,
    // tail expansion, and all later imperative consumers run on fresh epoch
    // inputs, including cross-function predecessors and candidate payloads.
    let prog = structuring_memo::run(&mut prog, memo);

    let stmt_map: HashMap<Node, CsharpminorStmt> = current_stmts.iter().cloned().collect();

    let join_points: HashMap<Node, Node> = prog
        .join_point
        .iter()
        .map(|(branch, join)| (*branch, *join))
        .collect();

    let scond_nodes: HashMap<Node, (Node, Node)> = prog
        .scond_node
        .iter()
        .map(|(branch, t, f)| (*branch, (*t, *f)))
        .collect();

    let no_join_nodes: HashSet<Node> = prog.scond_no_join.iter().map(|(n,)| *n).collect();

    let mut true_bodies: HashMap<Node, Vec<Node>> = HashMap::new();
    for (branch, member) in &prog.ifbody_true {
        true_bodies.entry(*branch).or_default().push(*member);
    }
    for nodes in true_bodies.values_mut() {
        nodes.sort();
    }

    let mut false_bodies: HashMap<Node, Vec<Node>> = HashMap::new();
    for (branch, member) in &prog.ifbody_false {
        false_bodies.entry(*branch).or_default().push(*member);
    }
    for nodes in false_bodies.values_mut() {
        nodes.sort();
    }

    // Auto-vectorized loop bypass: rewrite each vector-gating guard to jump unconditionally to its scalar arm, deduped by guard and deterministic via sort.
    let vec_bypass_rewrites: Vec<(Node, Node)> = {
        let mut v: Vec<(Node, Node)> = prog
            .vec_bypass_rewrite
            .iter()
            .map(|(g, t)| (*g, *t))
            .collect();
        v.sort_unstable();
        v.dedup_by_key(|(g, _)| *g);
        v
    };

    let trimmed: HashSet<Node> = prog.trim_node.iter().map(|(n,)| *n).collect();

    let loop_exit_cond_nodes: HashSet<Node> = prog.cond_is_break.iter().map(|(n, _)| *n).collect();

    let mut switch_chain_members: Vec<(Node, Node, u64, i64, Node)> = prog
        .switch_chain
        .iter()
        .filter(|(head, _, _, _, _)| prog.primary_switch.iter().any(|(h, _)| h == head))
        .map(|(head, member, reg, val, target)| (*head, *member, *reg, *val, *target))
        .collect();

    let mut valid_switches: Vec<(Node, u64)> = prog
        .primary_switch
        .iter()
        .map(|(head, reg)| (*head, *reg))
        .collect();

    // Fallback imperative comparison-tree analysis, deduplicated by head AND by any node already in an Ascent chain, or the walker rediscovers each chain from every interior Ceq node.
    let ascent_chain_nodes: HashSet<Node> = switch_chain_members
        .iter()
        .map(|(_, member, _, _, _)| *member)
        .collect();

    // CF-1: two roots with the same discriminant, member nodes and value->target map are one physical dispatch entered at different points, so every duplicate collapses to goto canonical_head.
    let mut canon_by_shape: HashMap<(u64, Vec<Node>, Vec<(i64, Node)>), Node> = HashMap::new();
    let mut dup_redirects: Vec<(Node, Node)> = Vec::new();
    {
        let mut by_head: HashMap<Node, (u64, Vec<Node>, Vec<(i64, Node)>)> = HashMap::new();
        for (head, member, reg, val, target) in &switch_chain_members {
            let e = by_head
                .entry(*head)
                .or_insert((*reg, Vec::new(), Vec::new()));
            e.1.push(*member);
            e.2.push((*val, *target));
        }
        // Sorted member set + sorted (value -> target) map form the shape key; heads visit in ascending order so the lowest head is deterministically canonical.
        let mut heads: Vec<Node> = by_head.keys().copied().collect();
        heads.sort_unstable();
        let mut dup_heads: HashSet<Node> = HashSet::new();
        for h in heads {
            let (reg, mut members, mut pairs) = by_head.remove(&h).expect("head collected above");
            members.sort_unstable();
            members.dedup();
            pairs.sort_unstable();
            pairs.dedup();
            match canon_by_shape.entry((reg, members, pairs)) {
                std::collections::hash_map::Entry::Occupied(e) => {
                    dup_redirects.push((h, *e.get()));
                    dup_heads.insert(h);
                }
                std::collections::hash_map::Entry::Vacant(v) => {
                    v.insert(h);
                }
            }
        }
        switch_chain_members.retain(|(head, _, _, _, _)| !dup_heads.contains(head));
        valid_switches.retain(|(head, _)| !dup_heads.contains(head));
    }

    // Walker fallback roots flow through the same shape canonicalization, processed LARGEST-first so a full-cascade walk canonicalizes before the mid-entry walks that see only its tail.
    let mut tree_results =
        detect_comparison_tree_switches(&current_stmts, next_map, &loop_exit_cond_nodes);
    tree_results.sort_by(|a, b| b.2.len().cmp(&a.2.len()).then(a.0.cmp(&b.0)));
    // CF-6 diagnostics: per-function dump of walker inputs/results and canonicalization decisions. Buffered into one eprint per function so parallel structure() calls do not interleave lines.
    let cf6_trace = std::env::var("MANIFOLD_CF6_TRACE").is_ok();
    if cf6_trace {
        let mut buf = String::new();
        buf.push_str(&format!("[CF6] === function entry {:#x} ===\n", entry_node));
        for (n, s) in &current_stmts {
            match s {
                CsharpminorStmt::Scond(cond, args, t, f) => {
                    buf.push_str(&format!(
                        "[CF6] stmt {:#x}: Scond {:?} args={:?} t={:#x} f={:#x} break={}\n",
                        n,
                        cond,
                        args,
                        t,
                        f,
                        loop_exit_cond_nodes.contains(n)
                    ));
                }
                CsharpminorStmt::Sset(d, e) => {
                    buf.push_str(&format!("[CF6] stmt {:#x}: Sset r{} = {:?}\n", n, d, e));
                }
                CsharpminorStmt::Sjump(t) => {
                    buf.push_str(&format!("[CF6] stmt {:#x}: Sjump {:#x}\n", n, t));
                }
                _ => {}
            }
        }
        let mut ac: Vec<(Node, Node, u64, i64, Node)> = switch_chain_members.clone();
        ac.sort_unstable();
        for (h, m, r, v, t) in ac {
            buf.push_str(&format!(
                "[CF6] ascent row: head={:#x} member={:#x} reg=r{} val={} target={:#x}\n",
                h, m, r, v, t
            ));
        }
        for (head, reg, cases, _) in &tree_results {
            buf.push_str(&format!(
                "[CF6] walker root {:#x} reg=r{} cases={:?}\n",
                head,
                reg,
                cases
                    .iter()
                    .map(|(v, t, m)| format!("{}=>{:#x}@{:#x}", v, t, m))
                    .collect::<Vec<_>>()
            ));
        }
        eprint!("{}", buf);
    }
    // Per-reg union of member nodes already claimed by kept switches; a root with all members claimed but non-matching value pairs is skipped outright, since redirecting into a rebased space is UNSOUND.
    let mut kept_members_by_reg: HashMap<u64, HashSet<Node>> = HashMap::new();
    for (_, member, reg, _, _) in &switch_chain_members {
        kept_members_by_reg.entry(*reg).or_default().insert(*member);
    }
    let mut tree_dispatch_members = HashMap::<Node, HashSet<Node>>::new();
    for (head, reg, cases, dispatch_members) in &tree_results {
        if ascent_chain_nodes.contains(head) {
            continue;
        }
        if cases.len() >= 3 {
            let mut members: Vec<Node> = cases.iter().map(|(_, _, m)| *m).collect();
            members.sort_unstable();
            members.dedup();
            let mut pairs: Vec<(i64, Node)> = cases.iter().map(|(v, t, _)| (*v, *t)).collect();
            pairs.sort_unstable();
            pairs.dedup();
            // A comparison-tree suffix can be a strict subset of an already
            // recovered switch.  It must not be redirected to the containing
            // switch's head: reaching the suffix proves that earlier cases
            // did not match, and restarting at the head both re-enables those
            // cases and turns the all-default path into a cycle.  The
            // canonical chain already owns the shared member nodes; its
            // taint analysis below keeps any externally entered member live.
            let subset_canon = canon_by_shape
                .iter()
                .filter_map(|((kreg, kmembers, kpairs), khead)| {
                    if *kreg == *reg
                        && members.iter().all(|m| kmembers.binary_search(m).is_ok())
                        && pairs.iter().all(|p| kpairs.binary_search(p).is_ok())
                    {
                        Some(*khead)
                    } else {
                        None
                    }
                })
                .min();
            if let Some(canon) = subset_canon {
                if cf6_trace {
                    eprintln!(
                        "[CF6] root {:#x} skipped: strict suffix of containing switch {:#x}",
                        head, canon
                    );
                }
                continue;
            }
            // Cross-space mid-entry: every member node already claimed by kept same-reg switches, but the value pairs differ (entry after an in-place rebase). Skip without redirect.
            if let Some(kept) = kept_members_by_reg.get(reg) {
                if !members.is_empty() && members.iter().all(|m| kept.contains(m)) {
                    if cf6_trace {
                        eprintln!("[CF6] root {:#x} skipped: member nodes already claimed by kept same-reg switches", head);
                    }
                    continue;
                }
            }
            canon_by_shape.insert((*reg, members, pairs), *head);
            let kept = kept_members_by_reg.entry(*reg).or_default();
            for &(val, target, member_node) in cases {
                switch_chain_members.push((*head, member_node, *reg, val, target));
                kept.insert(member_node);
            }
            valid_switches.push((*head, *reg));
            tree_dispatch_members.insert(*head, dispatch_members.clone());
        }
    }

    // CF-6: clight suppresses clean chain members, so rewrite each untainted leaf to Sjump(exit) and reattribute its case rows to the head, making the surviving goto the default routing.
    let mut leaf_rewrites: Vec<(Node, Node)> = Vec::new();
    let mut switch_defaults: Vec<(Node, Node)> = Vec::new();
    {
        // Local CFG pred map mirrors the edge set clight's chain_member_tainted sees via cminor_succ.
        let seq_map: HashMap<Node, Node> = seq_edges.iter().copied().collect();
        let mut pred_map: HashMap<Node, Vec<Node>> = HashMap::new();
        for (n, s) in &current_stmts {
            let mut outs: Vec<Node> = Vec::new();
            match s {
                CsharpminorStmt::Scond(_, _, t, f) => {
                    outs.push(*t);
                    outs.push(*f);
                }
                CsharpminorStmt::Sjump(t) => outs.push(*t),
                CsharpminorStmt::Sjumptable(_, ts) => outs.extend(ts.iter().copied()),
                _ => {}
            }
            if !is_terminal_stmt(s) {
                if let Some(&nx) = seq_map.get(n) {
                    outs.push(nx);
                }
            }
            for o in outs {
                pred_map.entry(o).or_default().push(*n);
            }
        }

        // Only sole-owner non-head members are rewrite-eligible: a node claimed by another switch would have its goto suppressed or collide with that switch's Sswitch materialization.
        let mut member_heads: HashMap<Node, Vec<Node>> = HashMap::new();
        for (h, m, _, _, _) in &switch_chain_members {
            if *m != *h {
                member_heads.entry(*m).or_default().push(*h);
            }
        }
        for (head, members) in &tree_dispatch_members {
            for member in members.iter().filter(|member| *member != head) {
                member_heads.entry(*member).or_default().push(*head);
            }
        }
        for v in member_heads.values_mut() {
            v.sort_unstable();
            v.dedup();
        }
        let head_set: HashSet<Node> = valid_switches.iter().map(|(h, _)| *h).collect();

        // Heads in ascending order for deterministic processing.
        let mut heads: Vec<Node> = valid_switches.iter().map(|(h, _)| *h).collect();
        heads.sort_unstable();
        heads.dedup();
        let mut demoted_heads: HashSet<Node> = HashSet::new();
        for head in heads {
            let rows: Vec<(Node, Node)> = switch_chain_members
                .iter()
                .filter(|(h, _, _, _, _)| *h == head)
                .map(|(_, m, _, _, t)| (*m, *t))
                .collect();
            let mut chain: HashSet<Node> = rows.iter().map(|(m, _)| *m).collect();
            chain.insert(head);
            // Case rows omit range splitters and other pure dispatch plumbing.
            // Reuse the walker's actual CFG footprint: an edge into a rowless
            // splitter is internal, but an unbounded edge to a body is not.
            if let Some(members) = tree_dispatch_members.get(&head) {
                chain.extend(members);
            }
            let case_targets: HashSet<Node> = rows.iter().map(|(_, t)| *t).collect();
            // Taint fixpoint mirroring clight's chain_member_tainted: union of local and cminor_succ preds is a superset, so the mirror can only over-taint (safe: skips rewrites), never under-taint.
            let mut tainted: HashSet<Node> = HashSet::new();
            loop {
                let mut changed = false;
                for &m in &chain {
                    if m == head || tainted.contains(&m) {
                        continue;
                    }
                    let local = pred_map.get(&m).map(|v| v.as_slice()).unwrap_or(&[]);
                    let global = cminor_preds.get(&m).map(|v| v.as_slice()).unwrap_or(&[]);
                    if local
                        .iter()
                        .chain(global.iter())
                        .any(|p| !chain.contains(p) || tainted.contains(p))
                    {
                        tainted.insert(m);
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            let mut members: Vec<Node> = chain.iter().copied().filter(|m| *m != head).collect();
            members.sort_unstable();
            members.dedup();
            // Leaf = exactly one chain-exiting branch. Rewrite is sound: untainted leaves are only reached through suppressed in-chain compares, so `goto exit` IS the no-match branch.
            let mut head_leaves: Vec<(Node, Node)> = Vec::new();
            let mut exits: std::collections::BTreeSet<Node> = std::collections::BTreeSet::new();
            for &m in &members {
                if let Some(CsharpminorStmt::Scond(_, _, t, f)) = stmt_map.get(&m) {
                    let t_exit = !chain.contains(t) && !case_targets.contains(t);
                    let f_exit = !chain.contains(f) && !case_targets.contains(f);
                    match (t_exit, f_exit) {
                        (true, false) => {
                            exits.insert(*t);
                            head_leaves.push((m, *t));
                        }
                        (false, true) => {
                            exits.insert(*f);
                            head_leaves.push((m, *f));
                        }
                        // Both in-chain: suppressible. Both exiting: not one goto -- leave raw compare.
                        _ => {}
                    }
                }
            }
            // A splitter head with multiple no-match exits is unsound as a defaultless Sswitch, since rowless values would misroute silently; a non-splitter head's multiple leaf exits are fine.
            let head_splitter = match stmt_map.get(&head) {
                Some(CsharpminorStmt::Scond(_, _, t, f)) => {
                    // A head branch exiting the chain without hitting a case target is a no-match destination.
                    if !chain.contains(t) && !case_targets.contains(t) {
                        exits.insert(*t);
                    }
                    if !chain.contains(f) && !case_targets.contains(f) {
                        exits.insert(*f);
                    }
                    !case_targets.contains(t) && !case_targets.contains(f)
                }
                // Non-compare head: treat conservatively as splitter to demote multi-exit chains.
                _ => true,
            };
            if head_splitter && exits.len() > 1 {
                demoted_heads.insert(head);
                if cf6_trace {
                    eprintln!(
                        "[CF6] head {:#x} demoted: splitter head with {} distinct no-match exits {:?}",
                        head,
                        exits.len(),
                        exits.iter().map(|e| format!("{:#x}", e)).collect::<Vec<_>>()
                    );
                }
                continue;
            }
            // The unmatched edge of the final comparison is the semantic
            // default.  Recover it independently of leaf suppression: a leaf
            // can also be reached from a case body and therefore must remain
            // live, while the switch still needs an explicit default goto.
            let mut default_targets = std::collections::BTreeSet::new();
            for &(member, case_target) in &rows {
                let Some(CsharpminorStmt::Scond(_, _, ifso, ifnot)) = stmt_map.get(&member) else {
                    continue;
                };
                let unmatched = match (*ifso == case_target, *ifnot == case_target) {
                    (true, false) => Some(*ifnot),
                    (false, true) => Some(*ifso),
                    _ => None,
                };
                if let Some(target) = unmatched.filter(|target| !chain.contains(target)) {
                    default_targets.insert(target);
                }
            }
            // A root range guard may have an unbounded branch that emits no
            // case rows. Its exit is still part of the default domain. Ignoring
            // it can replace a live case body with a later leaf's default.
            // One switch has one default: conflicting exits keep the CFG.
            default_targets.extend(exits);
            if default_targets.len() > 1 {
                demoted_heads.insert(head);
                continue;
            }
            if default_targets.len() == 1 {
                switch_defaults.push((head, *default_targets.iter().next().unwrap()));
            }
            for (m, exit) in head_leaves {
                if tainted.contains(&m) {
                    continue;
                }
                if head_set.contains(&m) {
                    continue;
                }
                if member_heads
                    .get(&m)
                    .map_or(false, |hs| hs.as_slice() != [head])
                {
                    continue;
                }
                leaf_rewrites.push((m, exit));
            }
        }
        if !demoted_heads.is_empty() {
            valid_switches.retain(|(h, _)| !demoted_heads.contains(h));
            switch_chain_members.retain(|(h, _, _, _, _)| !demoted_heads.contains(h));
        }
        if cf6_trace {
            for (m, ex) in &leaf_rewrites {
                eprintln!(
                    "[CF6] leaf member {:#x} rewritten to goto {:#x} (no-match routing)",
                    m, ex
                );
            }
        }
        // Reattribute rewritten leaves' case rows to their head so chain_member_node no longer suppresses the node (its statement is now the default goto).
        let leaf_set: HashSet<Node> = leaf_rewrites.iter().map(|(m, _)| *m).collect();
        for row in switch_chain_members.iter_mut() {
            if leaf_set.contains(&row.1) {
                row.1 = row.0;
            }
        }
    }

    // Includes rewritten leaf nodes so they are excluded from if-then-else metadata: their scond_node/join facts describe a compare that no longer exists.
    let switch_member_nodes: HashSet<Node> = switch_chain_members
        .iter()
        .map(|(_, member, _, _, _)| *member)
        .chain(leaf_rewrites.iter().map(|(m, _)| *m))
        .collect();

    // Valid if-then-else branches for metadata export, excluding loop exit conditions, switch members, and vector-bypass guards whose Scond becomes an unconditional Sjump.
    let bypass_guard_set: HashSet<Node> = vec_bypass_rewrites.iter().map(|(g, _)| *g).collect();
    let skip_branches: HashSet<Node> = loop_exit_cond_nodes
        .iter()
        .chain(switch_member_nodes.iter())
        .chain(bypass_guard_set.iter())
        .copied()
        .collect();

    let valid_ite_branches: HashSet<Node> = join_points
        .keys()
        .chain(no_join_nodes.iter())
        .filter(|branch| !skip_branches.contains(branch))
        .copied()
        .collect();

    // Flat output: keep all statements, only trim redundant Sjumps and switch interior nodes
    let mut result_stmts: Vec<(Node, CsharpminorStmt)> = current_stmts.clone();

    result_stmts.retain(|(node, stmt)| {
        !(trimmed.contains(node) && matches!(stmt, CsharpminorStmt::Sjump(_)))
    });

    // Apply CF-1 duplicate-root redirects, replacing the duplicate's compare with a jump to the canonical head; sound because shape identity implies the identical dispatch and no-match continuation.
    for (dup, canon) in &dup_redirects {
        for entry in result_stmts.iter_mut() {
            if entry.0 == *dup {
                entry.1 = CsharpminorStmt::Sjump(*canon);
            }
        }
    }

    // Apply CF-6 leaf rewrites after dup_redirects: a node claimed by both gets the direct default goto (shorter than re-dispatching through the canonical head; both are correct).
    for (leaf, exit) in &leaf_rewrites {
        for entry in result_stmts.iter_mut() {
            if entry.0 == *leaf {
                entry.1 = CsharpminorStmt::Sjump(*exit);
            }
        }
    }

    // Apply the vectorized-loop bypass: the vector region becomes unreachable and is pruned downstream, leaving only gcc's scalar aliasing-case loop.
    for (guard, scalar_t) in &vec_bypass_rewrites {
        for entry in result_stmts.iter_mut() {
            if entry.0 == *guard {
                entry.1 = CsharpminorStmt::Sjump(*scalar_t);
            }
        }
    }

    result_stmts.sort_by_key(|(n, _)| exec_order_key(*n));

    // Export if-body membership metadata (filtered to valid branches only)
    let mut out_ifbody_true: Vec<(Node, Node)> = Vec::new();
    let mut out_ifbody_false: Vec<(Node, Node)> = Vec::new();
    for (&branch, members) in &true_bodies {
        if valid_ite_branches.contains(&branch) {
            for &member in members {
                out_ifbody_true.push((branch, member));
            }
        }
    }
    for (&branch, members) in &false_bodies {
        if valid_ite_branches.contains(&branch) {
            for &member in members {
                out_ifbody_false.push((branch, member));
            }
        }
    }

    let out_join_points: Vec<(Node, Node)> = join_points
        .iter()
        .filter(|(branch, _)| valid_ite_branches.contains(branch))
        .map(|(&branch, &join)| (branch, join))
        .collect();

    let out_scond_no_join: Vec<Node> = no_join_nodes
        .iter()
        .filter(|branch| valid_ite_branches.contains(branch))
        .copied()
        .collect();

    debug!("=== Structuring complete ===");

    StructuringResult {
        stmts: result_stmts,
        switch_chain_members,
        valid_switches,
        switch_defaults,
        ifbody_true: out_ifbody_true,
        ifbody_false: out_ifbody_false,
        join_points: out_join_points,
        scond_no_join: out_scond_no_join,
    }
}

/// Walk GCC comparison trees (mixed eq/ne/range checks) to extract switch case values.
fn switch_disc_offset(op: &crate::x86::types::CminorBinop, cst: &Constant) -> Option<i64> {
    use crate::x86::types::CminorBinop;
    let raw = match (op, cst) {
        (CminorBinop::Oaddl, Constant::Olongconst(v))
        | (CminorBinop::Oadd, Constant::Ointconst(v))
        | (CminorBinop::Oaddl, Constant::Ointconst(v))
        | (CminorBinop::Oadd, Constant::Olongconst(v)) => *v,
        (CminorBinop::Osubl, Constant::Olongconst(v))
        | (CminorBinop::Osub, Constant::Ointconst(v))
        | (CminorBinop::Osubl, Constant::Ointconst(v))
        | (CminorBinop::Osub, Constant::Olongconst(v)) => v.wrapping_neg(),
        _ => return None,
    };
    if raw < i32::MIN as i64 || raw > i32::MAX as i64 {
        return None;
    }
    Some(raw)
}

// Path-interval helpers for the comparison-tree walker (inclusive bounds in root-discriminant space; None = unbounded).
fn clamp_lo(lo: Option<i64>, v: i64) -> Option<i64> {
    Some(lo.map_or(v, |l| l.max(v)))
}
fn clamp_hi(hi: Option<i64>, v: i64) -> Option<i64> {
    Some(hi.map_or(v, |h| h.min(v)))
}
// A finite, small, non-negative interval that may be enumerated as switch cases. Width and sign policy mirror the established unsigned range arms (< 32 values, lower bound >= 0).
fn enumerable_range(lo: Option<i64>, hi: Option<i64>) -> Option<(i64, i64)> {
    let (l, h) = (lo?, hi?);
    if l >= 0 && h >= l && h.checked_sub(l).map_or(false, |w| w < 32) {
        Some((l, h))
    } else {
        None
    }
}

/// True when a range-guard target is INTERIOR dispatch rather than a case body; enumeration is sound only on a body, and unresolved chains conservatively count as interior.
fn range_target_is_interior(
    start: Node,
    disc_reg: RTLReg,
    stmt_map: &HashMap<Node, &CsharpminorStmt>,
    seq_next_map: &HashMap<Node, Node>,
    resolve_reg: &dyn Fn(RTLReg) -> (RTLReg, i64),
    cond_break_nodes: &HashSet<Node>,
) -> bool {
    let mut cur = start;
    for _ in 0..8 {
        if cond_break_nodes.contains(&cur) {
            return true;
        }
        match stmt_map.get(&cur) {
            Some(CsharpminorStmt::Scond(cond, args, _, _)) if args.len() == 1 => {
                let reg_opt = match &args[0] {
                    CsharpminorExpr::Evar(r) => Some(*r),
                    CsharpminorExpr::Ebinop(_, lhs, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
                        (CsharpminorExpr::Evar(r), CsharpminorExpr::Econst(_)) => Some(*r),
                        _ => None,
                    },
                    _ => None,
                };
                return match reg_opt {
                    Some(r) => {
                        let is_cmp = matches!(
                            cond,
                            Condition::Ccompimm(_, _)
                                | Condition::Ccompuimm(_, _)
                                | Condition::Ccomplimm(_, _)
                                | Condition::Ccompluimm(_, _)
                                | Condition::Cmaskzero(_)
                                | Condition::Cmasknotzero(_)
                        );
                        is_cmp && resolve_reg(r).0 == disc_reg
                    }
                    None => false,
                };
            }
            Some(CsharpminorStmt::Scond(_, _, _, _)) => return false,
            Some(CsharpminorStmt::Sjumptable(_, _)) => return true,
            Some(CsharpminorStmt::Sjump(t)) => {
                if *t == cur {
                    return false;
                }
                cur = *t;
            }
            Some(CsharpminorStmt::Snop) => match seq_next_map.get(&cur) {
                Some(&n) => cur = n,
                None => return false,
            },
            Some(CsharpminorStmt::Sset(_, expr)) => {
                // Discriminant-rebasing prelude (dst = disc +/- const, in-place or derived copy) precedes deeper dispatch; any other statement begins a case body.
                let rebase = match expr {
                    CsharpminorExpr::Ebinop(op, lhs, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
                        (CsharpminorExpr::Evar(src), CsharpminorExpr::Econst(cst)) => {
                            switch_disc_offset(op, cst).is_some() && resolve_reg(*src).0 == disc_reg
                        }
                        _ => false,
                    },
                    _ => false,
                };
                if !rebase {
                    return false;
                }
                match seq_next_map.get(&cur) {
                    Some(&n) => cur = n,
                    None => return false,
                }
            }
            _ => return false,
        }
    }
    true
}

/// Walk GCC comparison trees (mixed eq/ne/range checks) to extract switch case values.
fn detect_comparison_tree_switches(
    stmts: &[(Node, CsharpminorStmt)],
    next_map: &HashMap<Node, Node>,
    cond_break_nodes: &HashSet<Node>,
) -> Vec<(Node, u64, Vec<(i64, Node, Node)>, HashSet<Node>)> {
    #[derive(Default)]
    struct TreeWalk {
        visited: HashSet<Node>,
        dispatch: HashSet<Node>,
    }
    let stmt_map: HashMap<Node, &CsharpminorStmt> = stmts.iter().map(|(n, s)| (*n, s)).collect();

    let stmt_node_set: HashSet<Node> = stmts.iter().map(|(n, _)| *n).collect();
    let seq_next_map: HashMap<Node, Node> = stmts
        .iter()
        .filter_map(|&(node, _)| {
            walk_next_to_stmt(node, next_map, &stmt_node_set).map(|nxt| (node, nxt))
        })
        .collect();

    // Track register derivations: dst = src +/- offset. Skip self-derivations (dst == src) which arise from in-place updates like `eax = eax + N`; treating them as offset chains corrupts accumulation when other Sconds reference the same reg before the update.
    let mut reg_derivation: HashMap<RTLReg, (RTLReg, i64)> = HashMap::new();
    for (_, s) in stmts {
        if let CsharpminorStmt::Sset(dst, expr) = s {
            match expr {
                CsharpminorExpr::Ebinop(op, lhs, rhs) => {
                    if let (CsharpminorExpr::Evar(src), CsharpminorExpr::Econst(cst)) =
                        (lhs.as_ref(), rhs.as_ref())
                    {
                        if *src == *dst {
                            continue;
                        }
                        if let Some(off) = switch_disc_offset(op, cst) {
                            reg_derivation.insert(*dst, (*src, off));
                        }
                    }
                }
                _ => {}
            }
        }
    }

    // Resolve register to root discriminant + cumulative offset
    let resolve_reg = |reg: RTLReg| -> (RTLReg, i64) {
        let mut current = reg;
        let mut total_offset: i64 = 0;
        let mut visited = HashSet::new();
        while let Some(&(src, off)) = reg_derivation.get(&current) {
            if !visited.insert(current) {
                break;
            }
            total_offset += off;
            current = src;
        }
        (current, total_offset)
    };

    // Walk the comparison tree collecting (case_value, target, member_node); local_disc_offset tracks in-place discriminant updates and path_lo/path_hi carry the interval in ROOT discriminant space.
    fn walk_tree(
        node: Node,
        disc_reg: RTLReg,
        local_disc_offset: i64,
        path_lo: Option<i64>,
        path_hi: Option<i64>,
        stmt_map: &HashMap<Node, &CsharpminorStmt>,
        seq_next_map: &HashMap<Node, Node>,
        reg_derivation: &HashMap<RTLReg, (RTLReg, i64)>,
        resolve_reg: &dyn Fn(RTLReg) -> (RTLReg, i64),
        cond_break_nodes: &HashSet<Node>,
        cases: &mut Vec<(i64, Node, Node)>,
        visited: &mut TreeWalk,
    ) {
        if !visited.visited.insert(node) {
            return;
        }

        // A loop-exit compare cannot be represented by this switch candidate:
        // truncating the walk here would emit a partial switch and silently
        // lose the remaining case/default edges.  The caller sees this node in
        // `visited` and rejects the whole candidate, preserving the raw CFG.
        if cond_break_nodes.contains(&node) {
            return;
        }

        // Track in-place self-updates of the discriminant for subsequent compares on this path: `Sset(disc_reg, disc_reg + N)` updates local_disc_offset by N.
        if let Some(s) = stmt_map.get(&node) {
            if stmt_def_reg(s) == Some(disc_reg) {
                if let CsharpminorStmt::Sset(_, expr) = s {
                    if let CsharpminorExpr::Ebinop(op, lhs, rhs) = expr {
                        if let (CsharpminorExpr::Evar(src), CsharpminorExpr::Econst(cst)) =
                            (lhs.as_ref(), rhs.as_ref())
                        {
                            if *src == disc_reg {
                                if let Some(off) = switch_disc_offset(op, cst) {
                                    if let Some(&next) = seq_next_map.get(&node) {
                                        visited.dispatch.insert(node);
                                        // The path interval is in root space (compare offsets renormalize), so it passes through unchanged.
                                        walk_tree(
                                            next,
                                            disc_reg,
                                            local_disc_offset + off,
                                            path_lo,
                                            path_hi,
                                            stmt_map,
                                            seq_next_map,
                                            reg_derivation,
                                            resolve_reg,
                                            cond_break_nodes,
                                            cases,
                                            visited,
                                        );
                                    }
                                    return;
                                }
                            }
                        }
                    }
                }
                // Any other redefinition of the discriminant KILLS the dispatch value: later compares test an unrelated value, and continuing with the stale offset fabricates case rows.
                return;
            }
        }

        // Match Scond with arg either Evar(reg) or Ebinop(Oaddl/Oadd, Evar(reg), Econst(offset)); the inline-temp pattern GCC/clang emits for `(disc - K) <op> imm`.
        let cmp = match stmt_map.get(&node) {
            Some(CsharpminorStmt::Scond(cond, args, ifso, ifnot)) if args.len() == 1 => {
                let (reg_opt, inline_off) = match &args[0] {
                    CsharpminorExpr::Evar(reg) => (Some(*reg), 0i64),
                    CsharpminorExpr::Ebinop(op, lhs, rhs) => {
                        if let (CsharpminorExpr::Evar(reg), CsharpminorExpr::Econst(cst)) =
                            (lhs.as_ref(), rhs.as_ref())
                        {
                            match switch_disc_offset(op, cst) {
                                Some(o) => (Some(*reg), o),
                                None => (None, 0),
                            }
                        } else {
                            (None, 0)
                        }
                    }
                    _ => (None, 0),
                };
                reg_opt.map(|reg| (reg, inline_off, *cond, *ifso, *ifnot))
            }
            _ => None,
        };

        let (reg, inline_off, cond, ifso, ifnot) = match cmp {
            Some(c) => c,
            None => {
                // Only pure control may be walked through: any state change kills row attribution, since the head's dispatch jumps over it; discriminant-rebase Ssets are exempt as dispatch plumbing.
                match stmt_map.get(&node) {
                    Some(CsharpminorStmt::Sjump(t)) => {
                        if *t != node {
                            visited.dispatch.insert(node);
                            walk_tree(
                                *t,
                                disc_reg,
                                local_disc_offset,
                                path_lo,
                                path_hi,
                                stmt_map,
                                seq_next_map,
                                reg_derivation,
                                resolve_reg,
                                cond_break_nodes,
                                cases,
                                visited,
                            );
                        }
                    }
                    Some(CsharpminorStmt::Snop) => {
                        if let Some(&next) = seq_next_map.get(&node) {
                            visited.dispatch.insert(node);
                            walk_tree(
                                next,
                                disc_reg,
                                local_disc_offset,
                                path_lo,
                                path_hi,
                                stmt_map,
                                seq_next_map,
                                reg_derivation,
                                resolve_reg,
                                cond_break_nodes,
                                cases,
                                visited,
                            );
                        }
                    }
                    Some(CsharpminorStmt::Sset(_, expr)) => {
                        let rebase_copy = match expr {
                            CsharpminorExpr::Ebinop(op, lhs, rhs) => {
                                match (lhs.as_ref(), rhs.as_ref()) {
                                    (CsharpminorExpr::Evar(src), CsharpminorExpr::Econst(cst)) => {
                                        switch_disc_offset(op, cst).is_some()
                                            && resolve_reg(*src).0 == disc_reg
                                    }
                                    _ => false,
                                }
                            }
                            _ => false,
                        };
                        if rebase_copy {
                            if let Some(&next) = seq_next_map.get(&node) {
                                visited.dispatch.insert(node);
                                walk_tree(
                                    next,
                                    disc_reg,
                                    local_disc_offset,
                                    path_lo,
                                    path_hi,
                                    stmt_map,
                                    seq_next_map,
                                    reg_derivation,
                                    resolve_reg,
                                    cond_break_nodes,
                                    cases,
                                    visited,
                                );
                            }
                        }
                    }
                    _ => {}
                }
                return;
            }
        };

        let (root_reg, derive_off) = resolve_reg(reg);
        // Apply the local offset only if the comparison's register IS the discriminant (an in-place update to disc_reg shifts the effective compared value).
        let path_off = if root_reg == disc_reg {
            local_disc_offset
        } else {
            0
        };
        let offset = derive_off + inline_off + path_off;
        let is_disc = root_reg == disc_reg;
        // Every condition traversed below belongs to the dispatch footprint,
        // even when it only partitions paths and contributes no case rows.
        // In particular, a mask test on the source of a masked discriminant
        // must not be mistaken for a default body.
        visited.dispatch.insert(node);

        match cond {
            // Ceq: true branch = case body, false continues
            Condition::Ccompimm(Comparison::Ceq, val)
            | Condition::Ccompuimm(Comparison::Ceq, val)
            | Condition::Ccomplimm(Comparison::Ceq, val)
            | Condition::Ccompluimm(Comparison::Ceq, val)
                if is_disc =>
            {
                let case_val = val - offset;
                cases.push((case_val, ifso, node));
                walk_tree(
                    ifnot,
                    disc_reg,
                    local_disc_offset,
                    path_lo,
                    path_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
            }

            // Cne: false branch = case body (inverted), true continues
            Condition::Ccompimm(Comparison::Cne, val)
            | Condition::Ccompuimm(Comparison::Cne, val)
            | Condition::Ccomplimm(Comparison::Cne, val)
            | Condition::Ccompluimm(Comparison::Cne, val)
                if is_disc =>
            {
                let case_val = val - offset;
                cases.push((case_val, ifnot, node));
                walk_tree(
                    ifso,
                    disc_reg,
                    local_disc_offset,
                    path_lo,
                    path_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
            }

            // Cmaskzero(M) on disc is (disc & M) == 0, which when the AND bounded disc to [0..M] is exactly disc == 0, so treat it like Ceq(0); clang -O1 fuses the and and je into it.
            Condition::Cmaskzero(mask) if is_disc && mask > 0 && (mask & (mask + 1)) == 0 => {
                let case_val = -offset;
                cases.push((case_val, ifso, node));
                walk_tree(
                    ifnot,
                    disc_reg,
                    local_disc_offset,
                    path_lo,
                    path_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
            }

            // Cmasknotzero(M) on disc means `(disc & M) != 0`. With M = 2^n - 1, this is the negation of case 0. Treat like Cne(0).
            Condition::Cmasknotzero(mask) if is_disc && mask > 0 && (mask & (mask + 1)) == 0 => {
                let case_val = -offset;
                cases.push((case_val, ifnot, node));
                walk_tree(
                    ifso,
                    disc_reg,
                    local_disc_offset,
                    path_lo,
                    path_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
            }

            // Unsigned disc < bound with a non-positive offset enumerates a bounded range for the true branch, which also implies a signed interval that narrows the path for nested signed guards.
            Condition::Ccompuimm(Comparison::Clt, bound)
            | Condition::Ccompluimm(Comparison::Clt, bound)
                if is_disc =>
            {
                let disc_lower = -offset;
                let disc_upper = bound - offset - 1;
                if disc_lower >= 0 && disc_upper >= disc_lower && (disc_upper - disc_lower) < 32 {
                    for v in disc_lower..=disc_upper {
                        cases.push((v, ifso, node));
                    }
                }
                let (t_lo, t_hi) = if disc_lower >= 0 && disc_upper >= disc_lower {
                    (clamp_lo(path_lo, disc_lower), clamp_hi(path_hi, disc_upper))
                } else {
                    (path_lo, path_hi)
                };
                walk_tree(
                    ifso,
                    disc_reg,
                    local_disc_offset,
                    t_lo,
                    t_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
                walk_tree(
                    ifnot,
                    disc_reg,
                    local_disc_offset,
                    path_lo,
                    path_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
            }

            // Unsigned `disc <= bound`: similar but inclusive upper bound.
            Condition::Ccompuimm(Comparison::Cle, bound)
            | Condition::Ccompluimm(Comparison::Cle, bound)
                if is_disc =>
            {
                let disc_lower = -offset;
                let disc_upper = bound - offset;
                if disc_lower >= 0 && disc_upper >= disc_lower && (disc_upper - disc_lower) < 32 {
                    for v in disc_lower..=disc_upper {
                        cases.push((v, ifso, node));
                    }
                }
                let (t_lo, t_hi) = if disc_lower >= 0 && disc_upper >= disc_lower {
                    (clamp_lo(path_lo, disc_lower), clamp_hi(path_hi, disc_upper))
                } else {
                    (path_lo, path_hi)
                };
                walk_tree(
                    ifso,
                    disc_reg,
                    local_disc_offset,
                    t_lo,
                    t_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
                walk_tree(
                    ifnot,
                    disc_reg,
                    local_disc_offset,
                    path_lo,
                    path_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
            }

            // Unsigned (disc + neg_off) > bound with neg_off < 0: false branch represents disc in [-off, -off + bound]. Used by gcc -O1 to test a contiguous case cluster like `case 2: case 3:` via `sub $2,%eax; cmp $1,%eax; ja default`.
            Condition::Ccompuimm(Comparison::Cgt, bound)
            | Condition::Ccompluimm(Comparison::Cgt, bound)
                if is_disc && offset < 0 =>
            {
                let disc_lower = -offset;
                let disc_upper = bound - offset;
                if disc_lower >= 0 && disc_upper >= disc_lower && (disc_upper - disc_lower) < 32 {
                    for v in disc_lower..=disc_upper {
                        cases.push((v, ifnot, node));
                    }
                }
                let (f_lo, f_hi) = if disc_lower >= 0 && disc_upper >= disc_lower {
                    (clamp_lo(path_lo, disc_lower), clamp_hi(path_hi, disc_upper))
                } else {
                    (path_lo, path_hi)
                };
                walk_tree(
                    ifso,
                    disc_reg,
                    local_disc_offset,
                    path_lo,
                    path_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
                walk_tree(
                    ifnot,
                    disc_reg,
                    local_disc_offset,
                    f_lo,
                    f_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
            }

            // Unsigned (disc + neg_off) >= bound: false branch represents disc in [-off, -off + bound - 1].
            Condition::Ccompuimm(Comparison::Cge, bound)
            | Condition::Ccompluimm(Comparison::Cge, bound)
                if is_disc && offset < 0 =>
            {
                let disc_lower = -offset;
                let disc_upper = bound - offset - 1;
                if disc_lower >= 0 && disc_upper >= disc_lower && (disc_upper - disc_lower) < 32 {
                    for v in disc_lower..=disc_upper {
                        cases.push((v, ifnot, node));
                    }
                }
                let (f_lo, f_hi) = if disc_lower >= 0 && disc_upper >= disc_lower {
                    (clamp_lo(path_lo, disc_lower), clamp_hi(path_hi, disc_upper))
                } else {
                    (path_lo, path_hi)
                };
                walk_tree(
                    ifso,
                    disc_reg,
                    local_disc_offset,
                    path_lo,
                    path_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
                walk_tree(
                    ifnot,
                    disc_reg,
                    local_disc_offset,
                    f_lo,
                    f_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
            }

            // SIGNED range guards narrow the path interval, and a branch whose interval becomes finite and small is a contiguous case CLUSTER, enumerated as cases when it lands on a body not further dispatch.
            Condition::Ccompimm(scmp, val) | Condition::Ccomplimm(scmp, val)
                if is_disc
                    && matches!(
                        scmp,
                        Comparison::Cgt | Comparison::Cge | Comparison::Clt | Comparison::Cle
                    ) =>
            {
                // Bound in root-disc space, since the compare tests (disc_root + offset); on overflow the branch intervals stay UNNARROWED and must not enumerate, or both branches bind the same values.
                let b = val.checked_sub(offset);
                let (t_lo, t_hi, f_lo, f_hi) = match (scmp, b) {
                    (Comparison::Cgt, Some(b)) => (
                        b.checked_add(1).map_or(path_lo, |x| clamp_lo(path_lo, x)),
                        path_hi,
                        path_lo,
                        clamp_hi(path_hi, b),
                    ),
                    (Comparison::Cge, Some(b)) => (
                        clamp_lo(path_lo, b),
                        path_hi,
                        path_lo,
                        b.checked_sub(1).map_or(path_hi, |x| clamp_hi(path_hi, x)),
                    ),
                    (Comparison::Clt, Some(b)) => (
                        path_lo,
                        b.checked_sub(1).map_or(path_hi, |x| clamp_hi(path_hi, x)),
                        clamp_lo(path_lo, b),
                        path_hi,
                    ),
                    (Comparison::Cle, Some(b)) => (
                        path_lo,
                        clamp_hi(path_hi, b),
                        b.checked_add(1).map_or(path_lo, |x| clamp_lo(path_lo, x)),
                        path_hi,
                    ),
                    _ => (path_lo, path_hi, path_lo, path_hi),
                };
                if b.is_some() {
                    if let Some((l, h)) = enumerable_range(t_lo, t_hi) {
                        if !range_target_is_interior(
                            ifso,
                            disc_reg,
                            stmt_map,
                            seq_next_map,
                            resolve_reg,
                            cond_break_nodes,
                        ) {
                            for v in l..=h {
                                cases.push((v, ifso, node));
                            }
                        }
                    }
                    if let Some((l, h)) = enumerable_range(f_lo, f_hi) {
                        if !range_target_is_interior(
                            ifnot,
                            disc_reg,
                            stmt_map,
                            seq_next_map,
                            resolve_reg,
                            cond_break_nodes,
                        ) {
                            for v in l..=h {
                                cases.push((v, ifnot, node));
                            }
                        }
                    }
                }
                walk_tree(
                    ifso,
                    disc_reg,
                    local_disc_offset,
                    t_lo,
                    t_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
                walk_tree(
                    ifnot,
                    disc_reg,
                    local_disc_offset,
                    f_lo,
                    f_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
            }

            // Other range guards on the discriminant (unsigned Cgt/Cge with offset >= 0): partition the disc space without binding case values; cases come only from Ceq/Cne leaves below.
            Condition::Ccompuimm(Comparison::Cgt, _)
            | Condition::Ccompluimm(Comparison::Cgt, _)
            | Condition::Ccompuimm(Comparison::Cge, _)
            | Condition::Ccompluimm(Comparison::Cge, _)
                if is_disc =>
            {
                walk_tree(
                    ifso,
                    disc_reg,
                    local_disc_offset,
                    path_lo,
                    path_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
                walk_tree(
                    ifnot,
                    disc_reg,
                    local_disc_offset,
                    path_lo,
                    path_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
            }

            // Non-discriminant or mask test: explore both branches
            _ => {
                walk_tree(
                    ifso,
                    disc_reg,
                    local_disc_offset,
                    path_lo,
                    path_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
                walk_tree(
                    ifnot,
                    disc_reg,
                    local_disc_offset,
                    path_lo,
                    path_hi,
                    stmt_map,
                    seq_next_map,
                    reg_derivation,
                    resolve_reg,
                    cond_break_nodes,
                    cases,
                    visited,
                );
            }
        }
    }

    // Find switch roots (Ceq/Cne/range-guard on a register, possibly via offset binop) and walk to enumerate cases; out-of-range branches reach a Ceq/Cne leaf or fall through to default.
    let mut results = Vec::new();
    let mut used_heads: HashSet<Node> = HashSet::new();

    for (node, s) in stmts {
        // Loop-exit Sconds match the discriminant pattern syntactically but are not switch cases; treating them as roots replays a chain the Ascent rules already recovered, duplicating switches.
        if cond_break_nodes.contains(node) {
            continue;
        }
        if let CsharpminorStmt::Scond(cond, args, _, _) = s {
            if args.len() != 1 {
                continue;
            }
            // Extract reg (possibly through Oaddl/Osubl with constant inline offset)
            let reg_opt: Option<RTLReg> = match &args[0] {
                CsharpminorExpr::Evar(reg) => Some(*reg),
                CsharpminorExpr::Ebinop(_, lhs, rhs) => {
                    if let (CsharpminorExpr::Evar(reg), CsharpminorExpr::Econst(_)) =
                        (lhs.as_ref(), rhs.as_ref())
                    {
                        Some(*reg)
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if let Some(reg) = reg_opt {
                let is_disc_compare = matches!(
                    cond,
                    Condition::Ccompimm(_, _)
                        | Condition::Ccompuimm(_, _)
                        | Condition::Ccomplimm(_, _)
                        | Condition::Ccompluimm(_, _)
                        | Condition::Cmaskzero(_)
                        | Condition::Cmasknotzero(_)
                );
                if !is_disc_compare {
                    continue;
                }

                let (root_reg, _) = resolve_reg(reg);
                if used_heads.contains(node) {
                    continue;
                }

                let mut cases: Vec<(i64, Node, Node)> = Vec::new();
                let mut visited = TreeWalk::default();
                walk_tree(
                    *node,
                    root_reg,
                    0i64,
                    None,
                    None,
                    &stmt_map,
                    &seq_next_map,
                    &reg_derivation,
                    &resolve_reg,
                    cond_break_nodes,
                    &mut cases,
                    &mut visited,
                );

                // The walker deliberately stops at loop-exit conditions.  A
                // candidate that reaches one is therefore incomplete, not a
                // smaller valid switch: retain the original comparison tree.
                if visited.visited.iter().any(|n| cond_break_nodes.contains(n)) {
                    continue;
                }

                // A mask predicate partitions many values; it is not an
                // equality case unless the complete incoming domain lies in
                // one mask period.  This walker cannot prove that across
                // arbitrary CFG joins.  Lifting the mask would otherwise turn
                // "all even values" into only `case 0` and delete the parity
                // branch, so preserve the original comparison tree.
                let has_discriminant_mask = visited.visited.iter().any(|visited_node| {
                    let Some(CsharpminorStmt::Scond(cond, args, _, _)) = stmt_map.get(visited_node)
                    else {
                        return false;
                    };
                    if !matches!(cond, Condition::Cmaskzero(_) | Condition::Cmasknotzero(_)) {
                        return false;
                    }
                    let Some(mask_reg) = args.first().and_then(|arg| match arg {
                        CsharpminorExpr::Evar(reg) => Some(*reg),
                        CsharpminorExpr::Ebinop(_, lhs, _) => match lhs.as_ref() {
                            CsharpminorExpr::Evar(reg) => Some(*reg),
                            _ => None,
                        },
                        _ => None,
                    }) else {
                        return false;
                    };
                    resolve_reg(mask_reg).0 == root_reg
                });
                if has_discriminant_mask {
                    continue;
                }

                // Deduplicate cases by value (keep first occurrence)
                let mut seen_vals: HashSet<i64> = HashSet::new();
                cases.retain(|(val, _, _)| seen_vals.insert(*val));

                // A real switch covers >= 2 distinct targets; a range-guard chain funnelling every value to ONE target is a single range test, and building a Sswitch there fabricates a back-edge.
                let distinct_targets: HashSet<Node> = cases.iter().map(|(_, t, _)| *t).collect();
                if cases.len() >= 3 && distinct_targets.len() >= 2 {
                    used_heads.insert(*node);
                    results.push((*node, root_reg as u64, cases, visited.dispatch));
                }
            }
        }
    }

    results
}

// Walk the execution-order chain from start until a stmt_nodes member is reached, splicing synthetic members in at their real-address position or they become unreachable islands.
fn walk_next_to_stmt(
    start: Node,
    next_map: &HashMap<Node, Node>,
    stmt_nodes: &HashSet<Node>,
) -> Option<Node> {
    const S1: u64 = crate::util::SYNTH_NODE_BIT; // executes 1st after its real address
    const S2: u64 = 1u64 << 63; // executes 2nd (two-step chains, e.g. arith_store_*)
    let base = start & !(S1 | S2);
    // Remaining members of start's own synthetic chain execute before next(base).
    if start & (S1 | S2) == 0 && stmt_nodes.contains(&(base | S1)) {
        return Some(base | S1);
    }
    if start & S2 == 0 && stmt_nodes.contains(&(base | S2)) {
        return Some(base | S2);
    }
    let mut cur = base;
    let mut visited: HashSet<Node> = HashSet::new();
    while visited.insert(cur) {
        let nxt = *next_map.get(&cur)?;
        if stmt_nodes.contains(&nxt) {
            return Some(nxt);
        }
        // A statement-less successor may still head a synthetic chain (e.g. its Sset folded away, leaving the fused store at nxt | 1<<62).
        if stmt_nodes.contains(&(nxt | S1)) {
            return Some(nxt | S1);
        }
        if stmt_nodes.contains(&(nxt | S2)) {
            return Some(nxt | S2);
        }
        cur = nxt;
    }
    None
}

fn compute_sequential_edges(
    stmts: &[(Node, CsharpminorStmt)],
    next_map: &HashMap<Node, Node>,
    cminor_succs: &HashMap<Node, Vec<Node>>,
    expansion_sources: &HashSet<Node>,
) -> Vec<(Node, Node)> {
    let stmt_nodes: HashSet<Node> = stmts.iter().map(|(n, _)| *n).collect();
    stmts
        .iter()
        .filter_map(|(node, _)| {
            sequential_stmt_successor(
                *node,
                next_map,
                cminor_succs,
                expansion_sources,
                &stmt_nodes,
            )
            .map(|next| (*node, next))
        })
        .collect()
}

fn sequential_stmt_successor(
    node: Node,
    next_map: &HashMap<Node, Node>,
    cminor_succs: &HashMap<Node, Vec<Node>>,
    expansion_sources: &HashSet<Node>,
    stmt_nodes: &HashSet<Node>,
) -> Option<Node> {
    // Prefer the post-optimization Cminor CFG whenever it has a successor for
    // this node. This is also required for an ordinary predecessor retargeted
    // into stage 1 after an expansion's real stage 0 was optimized away: the
    // predecessor is not itself an expansion member, while raw `next` still
    // bypasses the surviving semantic stages. Expansion members with no
    // semantic successor must not fall back to raw `next` either. Stage ids
    // remain identity/order only; reachability comes exclusively from CFG
    // edges.
    if cminor_succs.contains_key(&node)
        || expansion_sources.contains(&node)
        || crate::util::multi_synth_stage(node).is_some()
    {
        let mut resolved: Vec<Node> = cminor_succs
            .get(&node)
            .into_iter()
            .flatten()
            .filter_map(|succ| {
                if stmt_nodes.contains(succ) {
                    Some(*succ)
                } else {
                    walk_cminor_to_stmt(*succ, cminor_succs, stmt_nodes)
                }
            })
            .collect();
        resolved.sort_unstable();
        resolved.dedup();
        return (resolved.len() == 1).then(|| resolved[0]);
    }
    walk_next_to_stmt(node, next_map, stmt_nodes)
}

fn walk_cminor_to_stmt(
    start: Node,
    cminor_succs: &HashMap<Node, Vec<Node>>,
    stmt_nodes: &HashSet<Node>,
) -> Option<Node> {
    let mut current = start;
    let mut visited = HashSet::new();
    while visited.insert(current) {
        if stmt_nodes.contains(&current) {
            return Some(current);
        }
        let successors = cminor_succs.get(&current)?;
        if successors.len() != 1 {
            return None;
        }
        current = successors[0];
    }
    None
}

fn lift_setcc_arith_to_ite(
    working: &mut HashMap<Node, CsharpminorStmt>,
    candidates: &mut CsharpStmtCandidates,
    db: &DecompileDB,
) {
    use crate::x86::types::CminorBinop;
    use std::collections::HashMap as Map;
    let next_map: Map<Node, Node> = db
        .rel_iter::<(Node, Node)>("next")
        .map(|&(a, b)| (a, b))
        .collect();

    fn walk_to_working(
        start: Node,
        next_map: &Map<Node, Node>,
        working: &HashMap<Node, CsharpminorStmt>,
    ) -> Option<Node> {
        let mut cur = start;
        let mut seen = HashSet::new();
        while seen.insert(cur) {
            match next_map.get(&cur) {
                Some(&n) => {
                    if working.contains_key(&n) {
                        return Some(n);
                    }
                    cur = n;
                }
                None => return None,
            }
        }
        None
    }

    fn cminor_cmp_to_condition(op: &CminorBinop, rhs_const: i64) -> Option<Condition> {
        match op {
            CminorBinop::Ocmp(c) => Some(Condition::Ccompimm(*c, rhs_const)),
            CminorBinop::Ocmpu(c) => Some(Condition::Ccompuimm(*c, rhs_const)),
            CminorBinop::Ocmpl(c) => Some(Condition::Ccomplimm(*c, rhs_const)),
            CminorBinop::Ocmplu(c) => Some(Condition::Ccompluimm(*c, rhs_const)),
            _ => None,
        }
    }

    let snapshot: Vec<(Node, CsharpminorStmt)> =
        working.iter().map(|(n, s)| (*n, s.clone())).collect();
    let mut rewrites: Vec<(Node, CsharpminorStmt, Node)> = Vec::new();

    for (n1, s1) in &snapshot {
        let (reg1, cmp_op, arg_reg, rhs_const) = match s1 {
            CsharpminorStmt::Sset(r, CsharpminorExpr::Ebinop(op, lhs, rhs))
                if matches!(
                    op,
                    CminorBinop::Ocmp(_)
                        | CminorBinop::Ocmpu(_)
                        | CminorBinop::Ocmpl(_)
                        | CminorBinop::Ocmplu(_)
                ) =>
            {
                match (lhs.as_ref(), rhs.as_ref()) {
                    (
                        CsharpminorExpr::Evar(arg),
                        CsharpminorExpr::Econst(Constant::Ointconst(c)),
                    ) => (*r, op.clone(), *arg, *c as i64),
                    (
                        CsharpminorExpr::Evar(arg),
                        CsharpminorExpr::Econst(Constant::Olongconst(c)),
                    ) => (*r, op.clone(), *arg, *c),
                    _ => continue,
                }
            }
            _ => continue,
        };

        let cond = match cminor_cmp_to_condition(&cmp_op, rhs_const) {
            Some(c) => c,
            None => continue,
        };

        let n2 = match walk_to_working(*n1, &next_map, working) {
            Some(n) => n,
            None => continue,
        };
        let s2 = match working.get(&n2) {
            Some(s) => s.clone(),
            None => continue,
        };

        let (add_const, is_long) = match &s2 {
            CsharpminorStmt::Sset(r, CsharpminorExpr::Ebinop(op, lhs, rhs)) if *r == reg1 => {
                let is_long = matches!(op, CminorBinop::Oaddl);
                if !is_long && !matches!(op, CminorBinop::Oadd) {
                    continue;
                }
                match (lhs.as_ref(), rhs.as_ref()) {
                    (CsharpminorExpr::Evar(v), CsharpminorExpr::Econst(Constant::Ointconst(c)))
                        if *v == reg1 =>
                    {
                        (*c as i64, is_long)
                    }
                    (
                        CsharpminorExpr::Evar(v),
                        CsharpminorExpr::Econst(Constant::Olongconst(c)),
                    ) if *v == reg1 => (*c, is_long),
                    _ => continue,
                }
            }
            _ => continue,
        };

        let true_const = if is_long {
            Constant::Olongconst(add_const + 1)
        } else {
            Constant::Ointconst(add_const + 1)
        };
        let false_const = if is_long {
            Constant::Olongconst(add_const)
        } else {
            Constant::Ointconst(add_const)
        };

        let cond_args = vec![CsharpminorExpr::Evar(arg_reg)];
        let then_stmt = Box::new(CsharpminorStmt::Sset(
            reg1,
            CsharpminorExpr::Econst(true_const),
        ));
        let else_stmt = Box::new(CsharpminorStmt::Sset(
            reg1,
            CsharpminorExpr::Econst(false_const),
        ));

        let ite = CsharpminorStmt::Sifthenelse(cond, cond_args, then_stmt, else_stmt);
        rewrites.push((*n1, ite, n2));
    }

    for (n1, ite, n2) in rewrites {
        replace_stmt_candidates(candidates, n1, ite);
        replace_stmt_candidates(candidates, n2, CsharpminorStmt::Snop);
        refresh_working_node(working, candidates, n1);
        refresh_working_node(working, candidates, n2);
    }
}

fn inline_constants(
    working: &mut HashMap<Node, CsharpminorStmt>,
    candidates: &mut CsharpStmtCandidates,
    db: &DecompileDB,
    escaped_stack_regs: &HashSet<RTLReg>,
) {
    let mut def_count: HashMap<RTLReg, usize> = HashMap::new();
    for (_, stmt) in working.iter() {
        match stmt {
            CsharpminorStmt::Sset(reg, _) => {
                *def_count.entry(*reg).or_insert(0) += 1;
            }
            CsharpminorStmt::Scall(Some(reg), _, _, _) => {
                *def_count.entry(*reg).or_insert(0) += 1;
            }
            CsharpminorStmt::Sbuiltin(Some(reg), _, _, _) => {
                *def_count.entry(*reg).or_insert(0) += 1;
            }
            _ => {}
        }
    }

    let param_regs: HashSet<RTLReg> = db
        .rel_iter::<(Address, RTLReg)>("emit_function_param_candidate")
        .map(|&(_, r)| r)
        .collect();
    for &reg in &param_regs {
        *def_count.entry(reg).or_insert(0) += 1;
    }

    let mut const_map: HashMap<RTLReg, Constant> = HashMap::new();
    let mut multi_def: HashSet<RTLReg> = HashSet::new();
    // Sort so first-seen-wins-unless-conflict is order-invariant.
    let mut sdc_tuples: Vec<(RTLReg, Constant)> = db
        .rel_iter::<(RTLReg, Constant)>("single_def_const")
        .cloned()
        .collect();
    sdc_tuples.sort_by(|a, b| {
        a.0.cmp(&b.0)
            .then_with(|| format!("{:?}", a.1).cmp(&format!("{:?}", b.1)))
    });
    for (reg, cst) in sdc_tuples {
        if escaped_stack_regs.contains(&reg) {
            continue;
        }
        if multi_def.contains(&reg) {
            continue;
        }
        if def_count.get(&reg).copied().unwrap_or(0) > 1 {
            multi_def.insert(reg);
            continue;
        }
        if let Some(existing) = const_map.get(&reg) {
            if *existing != cst {
                const_map.remove(&reg);
                multi_def.insert(reg);
            }
        } else {
            const_map.insert(reg, cst);
        }
    }
    if const_map.is_empty() {
        return;
    }

    let const_set_nodes: HashSet<Node> = working
        .iter()
        .filter_map(|(node, stmt)| {
            if let CsharpminorStmt::Sset(reg, CsharpminorExpr::Econst(cst)) = stmt {
                if const_map.get(reg) == Some(cst) {
                    Some(*node)
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect();

    let mut nodes: Vec<Node> = working.keys().copied().collect();
    nodes.sort_unstable();
    for node in nodes {
        let stmt = working.get(&node).unwrap().clone();
        if const_set_nodes.contains(&node) {
            if let CsharpminorStmt::Sset(reg, CsharpminorExpr::Econst(cst)) = &stmt {
                if const_map.get(reg) == Some(cst) {
                    replace_stmt_candidates(candidates, node, CsharpminorStmt::Snop);
                    refresh_working_node(working, candidates, node);
                    continue;
                }
            }
        }
        transform_stmt_candidates(candidates, node, |candidate| {
            subst_consts_in_stmt(candidate, &const_map)
        });
        refresh_working_node(working, candidates, node);
    }
}

fn subst_consts_in_expr(
    expr: &CsharpminorExpr,
    consts: &HashMap<RTLReg, Constant>,
) -> CsharpminorExpr {
    match expr {
        CsharpminorExpr::Evar(reg) => {
            if let Some(cst) = consts.get(reg) {
                CsharpminorExpr::Econst(cst.clone())
            } else {
                expr.clone()
            }
        }
        CsharpminorExpr::Eunop(op, inner) => {
            CsharpminorExpr::Eunop(op.clone(), Box::new(subst_consts_in_expr(inner, consts)))
        }
        CsharpminorExpr::Ebinop(op, lhs, rhs) => CsharpminorExpr::Ebinop(
            op.clone(),
            Box::new(subst_consts_in_expr(lhs, consts)),
            Box::new(subst_consts_in_expr(rhs, consts)),
        ),
        CsharpminorExpr::Eload(chunk, addr) => {
            CsharpminorExpr::Eload(*chunk, Box::new(subst_consts_in_expr(addr, consts)))
        }
        CsharpminorExpr::Econdition(cond, t, f) => CsharpminorExpr::Econdition(
            Box::new(subst_consts_in_expr(cond, consts)),
            Box::new(subst_consts_in_expr(t, consts)),
            Box::new(subst_consts_in_expr(f, consts)),
        ),
        _ => expr.clone(),
    }
}

fn subst_consts_in_stmt(
    stmt: &CsharpminorStmt,
    consts: &HashMap<RTLReg, Constant>,
) -> CsharpminorStmt {
    match stmt {
        CsharpminorStmt::Sset(reg, expr) => {
            CsharpminorStmt::Sset(*reg, subst_consts_in_expr(expr, consts))
        }
        CsharpminorStmt::Sstore(chunk, addr, val) => CsharpminorStmt::Sstore(
            *chunk,
            subst_consts_in_expr(addr, consts),
            subst_consts_in_expr(val, consts),
        ),
        CsharpminorStmt::Scall(dst, sig, callee, args) => {
            let new_callee = match callee {
                either::Either::Left(expr) => {
                    either::Either::Left(subst_consts_in_expr(expr, consts))
                }
                r => r.clone(),
            };
            let new_args: Vec<_> = args
                .iter()
                .map(|a| subst_consts_in_expr(a, consts))
                .collect();
            CsharpminorStmt::Scall(*dst, sig.clone(), new_callee, new_args)
        }
        CsharpminorStmt::Stailcall(sig, callee, args) => {
            let new_callee = match callee {
                either::Either::Left(expr) => {
                    either::Either::Left(subst_consts_in_expr(expr, consts))
                }
                r => r.clone(),
            };
            let new_args: Vec<_> = args
                .iter()
                .map(|a| subst_consts_in_expr(a, consts))
                .collect();
            CsharpminorStmt::Stailcall(sig.clone(), new_callee, new_args)
        }
        CsharpminorStmt::Scond(cond, args, ifso, ifnot) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| subst_consts_in_expr(a, consts))
                .collect();
            CsharpminorStmt::Scond(cond.clone(), new_args, *ifso, *ifnot)
        }
        CsharpminorStmt::Sjumptable(expr, targets) => {
            CsharpminorStmt::Sjumptable(subst_consts_in_expr(expr, consts), targets.clone())
        }
        CsharpminorStmt::Sreturn(expr) => {
            CsharpminorStmt::Sreturn(subst_consts_in_expr(expr, consts))
        }
        CsharpminorStmt::Sseq(stmts) => {
            let new_stmts: Vec<_> = stmts
                .iter()
                .map(|s| subst_consts_in_stmt(s, consts))
                .collect();
            CsharpminorStmt::Sseq(new_stmts)
        }
        CsharpminorStmt::Sbuiltin(dst, name, args, res) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| subst_consts_in_builtin_arg(a, consts))
                .collect();
            let new_res = subst_consts_in_builtin_arg(res, consts);
            CsharpminorStmt::Sbuiltin(*dst, name.clone(), new_args, new_res)
        }
        _ => stmt.clone(),
    }
}

fn subst_consts_in_builtin_arg(
    arg: &BuiltinArg<CsharpminorExpr>,
    consts: &HashMap<RTLReg, Constant>,
) -> BuiltinArg<CsharpminorExpr> {
    match arg {
        BuiltinArg::BA(expr) => BuiltinArg::BA(subst_consts_in_expr(expr, consts)),
        BuiltinArg::BASplitLong(hi, lo) => BuiltinArg::BASplitLong(
            Box::new(subst_consts_in_builtin_arg(hi, consts)),
            Box::new(subst_consts_in_builtin_arg(lo, consts)),
        ),
        BuiltinArg::BAAddPtr(base, ofs) => BuiltinArg::BAAddPtr(
            Box::new(subst_consts_in_builtin_arg(base, consts)),
            Box::new(subst_consts_in_builtin_arg(ofs, consts)),
        ),
        _ => arg.clone(),
    }
}

// CFG-based copy propagation; analysis in CopyPropagationProgram, fixpoint fold in Rust.
fn propagate_copies(
    working: &mut HashMap<Node, CsharpminorStmt>,
    candidates: &mut CsharpStmtCandidates,
    db: &mut DecompileDB,
    escaped_stack_regs: &HashSet<RTLReg>,
) {
    use crate::x86::types::XType;

    let mut prog = CopyPropagationProgram::default();
    for (node, stmt) in working.iter() {
        prog.stmt.push((*node, stmt.clone()));
    }
    // VR-2: cminor_succ covers synthetic bit-62 nodes via rtl_succ bridge rules, making their kills visible to the cross-block available-copies lattice.
    for &(a, b) in db.rel_iter::<(Node, Node)>("cminor_succ") {
        prog.edge.push((a, b));
    }
    for &(_, entry) in db.rel_iter::<(Address, Node)>("func_entry_node") {
        prog.entry.push((entry,));
    }
    for &reg in escaped_stack_regs {
        prog.protected_copy_dst.push((reg,));
    }

    prog.run();

    // Gather per-node applicable substitutions: Vec<(dst, src)>.
    let mut substs_by_node: HashMap<Node, Vec<(RTLReg, RTLReg)>> = HashMap::new();
    for (u, dst, src) in &prog.applicable_subst {
        substs_by_node.entry(*u).or_default().push((*dst, *src));
    }

    // Fold to fixpoint per node and per retained alternative; sort pairs first
    // for determinism.
    for (node, pairs) in &mut substs_by_node {
        pairs.sort();
        pairs.dedup();
        transform_stmt_candidates(candidates, *node, |candidate| {
            let mut current = candidate.clone();
            loop {
                let mut changed = false;
                for &(dst, src) in pairs.iter() {
                    let next = subst_var_in_stmt(&current, dst, src);
                    if next != current {
                        current = next;
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            current
        });
        refresh_working_node(working, candidates, *node);
    }

    let dead_copies: HashSet<Node> = prog.dead_copy_v2.iter().map(|(n,)| *n).collect();

    if substs_by_node.is_empty() && dead_copies.is_empty() {
        return;
    }

    // For each dead copy, transfer dst's types to src via Ascent's copy_intro.
    let existing_types: Vec<(RTLReg, XType)> = db
        .rel_iter::<(RTLReg, XType)>("emit_var_type_candidate")
        .cloned()
        .collect();
    // The two webs a dead copy joins are still two webs, and the machine keeps
    // them in registers of its own choosing. Transferring a float type onto a
    // web that only ever lives in general-purpose registers contradicts the
    // register file, so that one type is left behind; everything else moves.
    let class_gpr: HashSet<RTLReg> = db
        .rel_iter::<(RTLReg,)>("web_class_gpr")
        .map(|(r,)| *r)
        .collect();
    let class_fp: HashSet<RTLReg> = db
        .rel_iter::<(RTLReg,)>("web_class_fp")
        .map(|(r,)| *r)
        .collect();
    let float_denied =
        |reg: RTLReg| -> bool { class_gpr.contains(&reg) && !class_fp.contains(&reg) };
    let intros_by_node: HashMap<Node, (RTLReg, RTLReg)> = prog
        .copy_intro
        .iter()
        .map(|(n, dst, src)| (*n, (*dst, *src)))
        .collect();
    for &copy_node in &dead_copies {
        if let Some(&(dst, src)) = intros_by_node.get(&copy_node) {
            for (reg, xty) in &existing_types {
                if *reg != dst {
                    continue;
                }
                if matches!(xty, XType::Xfloat | XType::Xsingle) && float_denied(src) {
                    continue;
                }
                db.rel_push("emit_var_type_candidate", (src, xty.clone()));
            }
        }
    }

    for node in &dead_copies {
        replace_stmt_candidates(candidates, *node, CsharpminorStmt::Snop);
        refresh_working_node(working, candidates, *node);
    }
}

// Helpers used by propagate_copies and its Ascent rules.

fn stmt_uses_set(stmt: &CsharpminorStmt) -> HashSet<RTLReg> {
    let mut vars = HashSet::new();
    match stmt {
        CsharpminorStmt::Sset(_, expr) => collect_expr_vars(expr, &mut vars),
        CsharpminorStmt::Sstore(_, addr, val) => {
            collect_expr_vars(addr, &mut vars);
            collect_expr_vars(val, &mut vars);
        }
        CsharpminorStmt::Scall(_, _, callee, args) => {
            if let either::Either::Left(e) = callee {
                collect_expr_vars(e, &mut vars);
            }
            for a in args {
                collect_expr_vars(a, &mut vars);
            }
        }
        CsharpminorStmt::Stailcall(_, callee, args) => {
            if let either::Either::Left(e) = callee {
                collect_expr_vars(e, &mut vars);
            }
            for a in args {
                collect_expr_vars(a, &mut vars);
            }
        }
        CsharpminorStmt::Sbuiltin(_, _, args, res) => {
            for a in args {
                collect_builtin_arg_vars(a, &mut vars);
            }
            collect_builtin_arg_vars(res, &mut vars);
        }
        CsharpminorStmt::Scond(_, args, _, _) => {
            for a in args {
                collect_expr_vars(a, &mut vars);
            }
        }
        CsharpminorStmt::Sjumptable(expr, _) => collect_expr_vars(expr, &mut vars),
        CsharpminorStmt::Sreturn(expr) => collect_expr_vars(expr, &mut vars),
        _ => {}
    }
    vars
}

fn stmt_def_reg(stmt: &CsharpminorStmt) -> Option<RTLReg> {
    match stmt {
        CsharpminorStmt::Sset(reg, _) => Some(*reg),
        CsharpminorStmt::Scall(Some(reg), _, _, _) => Some(*reg),
        CsharpminorStmt::Sbuiltin(Some(reg), _, _, _) => Some(*reg),
        _ => None,
    }
}

fn subst_var_in_expr(expr: &CsharpminorExpr, old: RTLReg, new: RTLReg) -> CsharpminorExpr {
    match expr {
        CsharpminorExpr::Evar(r) if *r == old => CsharpminorExpr::Evar(new),
        CsharpminorExpr::Eunop(op, inner) => {
            CsharpminorExpr::Eunop(op.clone(), Box::new(subst_var_in_expr(inner, old, new)))
        }
        CsharpminorExpr::Ebinop(op, l, r) => CsharpminorExpr::Ebinop(
            op.clone(),
            Box::new(subst_var_in_expr(l, old, new)),
            Box::new(subst_var_in_expr(r, old, new)),
        ),
        CsharpminorExpr::Eload(chunk, addr) => {
            CsharpminorExpr::Eload(*chunk, Box::new(subst_var_in_expr(addr, old, new)))
        }
        CsharpminorExpr::Econdition(c, t, f) => CsharpminorExpr::Econdition(
            Box::new(subst_var_in_expr(c, old, new)),
            Box::new(subst_var_in_expr(t, old, new)),
            Box::new(subst_var_in_expr(f, old, new)),
        ),
        _ => expr.clone(),
    }
}

fn subst_var_in_ba(
    ba: &BuiltinArg<CsharpminorExpr>,
    old: RTLReg,
    new: RTLReg,
) -> BuiltinArg<CsharpminorExpr> {
    match ba {
        BuiltinArg::BA(e) => BuiltinArg::BA(subst_var_in_expr(e, old, new)),
        BuiltinArg::BASplitLong(a, b) => BuiltinArg::BASplitLong(
            Box::new(subst_var_in_ba(a, old, new)),
            Box::new(subst_var_in_ba(b, old, new)),
        ),
        BuiltinArg::BAAddPtr(a, b) => BuiltinArg::BAAddPtr(
            Box::new(subst_var_in_ba(a, old, new)),
            Box::new(subst_var_in_ba(b, old, new)),
        ),
        _ => ba.clone(),
    }
}

fn subst_var_in_stmt(stmt: &CsharpminorStmt, old: RTLReg, new: RTLReg) -> CsharpminorStmt {
    match stmt {
        CsharpminorStmt::Sset(dst, expr) => {
            CsharpminorStmt::Sset(*dst, subst_var_in_expr(expr, old, new))
        }
        CsharpminorStmt::Sstore(chunk, addr, val) => CsharpminorStmt::Sstore(
            *chunk,
            subst_var_in_expr(addr, old, new),
            subst_var_in_expr(val, old, new),
        ),
        CsharpminorStmt::Scall(dst, sig, callee, args) => {
            let new_callee = match callee {
                either::Either::Left(e) => either::Either::Left(subst_var_in_expr(e, old, new)),
                other => other.clone(),
            };
            let new_args: Vec<_> = args
                .iter()
                .map(|a| subst_var_in_expr(a, old, new))
                .collect();
            CsharpminorStmt::Scall(dst.clone(), sig.clone(), new_callee, new_args)
        }
        CsharpminorStmt::Stailcall(sig, callee, args) => {
            let new_callee = match callee {
                either::Either::Left(e) => either::Either::Left(subst_var_in_expr(e, old, new)),
                other => other.clone(),
            };
            let new_args: Vec<_> = args
                .iter()
                .map(|a| subst_var_in_expr(a, old, new))
                .collect();
            CsharpminorStmt::Stailcall(sig.clone(), new_callee, new_args)
        }
        CsharpminorStmt::Sbuiltin(dst, name, args, res) => {
            let new_args: Vec<_> = args.iter().map(|a| subst_var_in_ba(a, old, new)).collect();
            let new_res = subst_var_in_ba(res, old, new);
            CsharpminorStmt::Sbuiltin(dst.clone(), name.clone(), new_args, new_res)
        }
        CsharpminorStmt::Scond(cond, args, ifso, ifnot) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| subst_var_in_expr(a, old, new))
                .collect();
            CsharpminorStmt::Scond(cond.clone(), new_args, *ifso, *ifnot)
        }
        CsharpminorStmt::Sjumptable(expr, targets) => {
            CsharpminorStmt::Sjumptable(subst_var_in_expr(expr, old, new), targets.clone())
        }
        CsharpminorStmt::Sreturn(expr) => {
            CsharpminorStmt::Sreturn(subst_var_in_expr(expr, old, new))
        }
        _ => stmt.clone(),
    }
}

// VR-2 helpers: available-copies dataflow over the statement-level CFG.

// Transfer one statement through the avail-copies lattice: kill entries whose dst or src is redefined, then gen the statement's own copy.
fn copy_transfer(
    avail: &Set<(Node, RTLReg, RTLReg)>,
    node: Node,
    stmt: &CsharpminorStmt,
) -> Set<(Node, RTLReg, RTLReg)> {
    let def = stmt_def_reg(stmt);
    let mut out: std::collections::BTreeSet<(Node, RTLReg, RTLReg)> = avail
        .0
        .iter()
        .filter(|(_, dst, src)| def.map_or(true, |d| d != *dst && d != *src))
        .copied()
        .collect();
    if let CsharpminorStmt::Sset(dst, CsharpminorExpr::Evar(src)) = stmt {
        if dst != src {
            out.insert((node, *dst, *src));
        }
    }
    Set(out)
}

// Entries of the avail set that copy into `dst`, as (intro, src) pairs.
fn avail_copies_of(avail: &Set<(Node, RTLReg, RTLReg)>, dst: RTLReg) -> Vec<(Node, RTLReg)> {
    avail
        .0
        .iter()
        .filter(|(_, d, _)| *d == dst)
        .map(|(i, _, s)| (*i, *s))
        .collect()
}

// CopyPropagationProgram: Ascent copy propagation. Outputs applicable_subst, dead_copy_v2, copy_intro.
ascent_par! {
    pub struct CopyPropagationProgram;

    relation stmt(Node, CsharpminorStmt);
    // VR-2 inputs: statement-level CFG edges (cminor_succ) and function entry nodes.
    relation edge(Node, Node);
    relation entry(Node);
    // A reverse-Stacking Sset into an address-escaped cell is a memory store,
    // not a substitutable register rename.
    relation protected_copy_dst(RTLReg);

    // Registers used (read) at a node. Computed once per stmt.
    relation stmt_uses(Node, RTLReg);
    stmt_uses(*n, reg) <--
        stmt(n, s),
        let used = stmt_uses_set(s),
        for reg in used;

    // Copy introductions: Sset(dst, Evar(src)) with dst != src.
    relation copy_intro(Node, RTLReg, RTLReg);
    copy_intro(*n, *dst, *src) <--
        stmt(n, ?CsharpminorStmt::Sset(dst, CsharpminorExpr::Evar(src))),
        if dst != src,
        !protected_copy_dst(dst);

    // The copy introduced at `intro` is live at use-node `u`. This is derived
    // only from the CFG lattice below; node magnitude is not execution order.
    relation copy_active_at(Node, RTLReg, RTLReg, Node);

    // VR-2: avail_in is a Dual<Set> intersection lattice keeping only path-invariant copies, so loop safety falls out of the meet and loop-interior copies never appear at first-iteration reads.
    lattice avail_in(Node, Dual<Set<(Node, RTLReg, RTLReg)>>);

    // Function entries start with no available copies.
    avail_in(*e, Dual(Set::default())) <-- entry(e);

    // Propagate along CFG edges through the pred's transfer (kill defs, then gen intro).
    avail_in(*n, Dual(copy_transfer(&pin.0, *p, s))) <--
        edge(p, n),
        avail_in(p, pin),
        stmt(p, s);

    // Pred without a statement in this program's view has unknown effects: kill everything.
    avail_in(*n, Dual(Set::default())) <--
        edge(p, n),
        avail_in(p, _),
        !stmt(p, _);

    // Cross-block coverage feeds the same active/covered/dead pipeline; tuples materialize only at use sites.
    copy_active_at(*u, *dst, src, intro) <--
        stmt_uses(u, dst),
        !protected_copy_dst(dst),
        avail_in(u, av),
        for (intro, src) in avail_copies_of(&av.0, *dst);

    // The copy at intro has a use of dst it does NOT cover (a loop-carried read), so substituting would strip dst's def and collapse the loop-carried value to its pre-loop definition.
    relation copy_use_uncovered(Node);
    copy_use_uncovered(*intro) <--
        copy_intro(intro, dst, src),
        stmt_uses(u, dst),
        !copy_active_at(u, dst, src, intro);

    // Anchored on original uses; the Rust fold runs the chain to fixpoint.
    relation applicable_subst(Node, RTLReg, RTLReg);
    applicable_subst(*u, *dst, *src) <--
        copy_active_at(u, dst, src, intro),
        stmt_uses(u, dst),
        !copy_use_uncovered(intro);

    // Chain extension: once a subst introduces mid and avail_in still carries mid = root, mid->root applies at u too, letting the fold chase outer -> mid -> root across call-split blocks.
    applicable_subst(*u, *mid, root) <--
        applicable_subst(u, _, mid),
        !protected_copy_dst(mid),
        avail_in(u, av),
        for (intro, root) in avail_copies_of(&av.0, *mid),
        !copy_use_uncovered(intro);

    // A copy is dead if at least one substitution fires for it AND every use of dst is covered.
    relation dead_copy_v2(Node);
    dead_copy_v2(*intro) <--
        copy_intro(intro, dst, src),
        copy_active_at(u, dst, src, intro),
        stmt_uses(u, dst),
        !copy_use_uncovered(intro);
}

fn eliminate_dead_returns(
    working: &mut HashMap<Node, CsharpminorStmt>,
    candidates: &mut CsharpStmtCandidates,
    db: &DecompileDB,
) {
    let dead_regs: HashSet<RTLReg> = db
        .rel_iter::<(RTLReg,)>("dead_def")
        .map(|&(reg,)| reg)
        .collect();
    if dead_regs.is_empty() {
        return;
    }

    // Cross-check dead_def claims against actual uses in working to avoid dropping live returns.
    let mut used_regs: HashSet<RTLReg> = HashSet::new();
    for stmt in candidates.values().flat_map(|stmts| stmts.iter()) {
        match stmt {
            CsharpminorStmt::Sset(_, expr) => {
                collect_expr_vars(expr, &mut used_regs);
            }
            CsharpminorStmt::Sstore(_, addr, value) => {
                collect_expr_vars(addr, &mut used_regs);
                collect_expr_vars(value, &mut used_regs);
            }
            CsharpminorStmt::Sreturn(expr) => {
                collect_expr_vars(expr, &mut used_regs);
            }
            CsharpminorStmt::Scall(_, _, callee, args) => {
                if let either::Either::Left(expr) = callee {
                    collect_expr_vars(expr, &mut used_regs);
                }
                for a in args.iter() {
                    collect_expr_vars(a, &mut used_regs);
                }
            }
            CsharpminorStmt::Stailcall(_, callee, args) => {
                if let either::Either::Left(expr) = callee {
                    collect_expr_vars(expr, &mut used_regs);
                }
                for a in args.iter() {
                    collect_expr_vars(a, &mut used_regs);
                }
            }
            CsharpminorStmt::Sbuiltin(_, _, args, res) => {
                for a in args.iter() {
                    collect_builtin_arg_vars(a, &mut used_regs);
                }
                collect_builtin_arg_vars(res, &mut used_regs);
            }
            CsharpminorStmt::Scond(_, args, _, _) => {
                for a in args.iter() {
                    collect_expr_vars(a, &mut used_regs);
                }
            }
            CsharpminorStmt::Sjumptable(expr, _) => {
                collect_expr_vars(expr, &mut used_regs);
            }
            _ => {}
        }
    }

    // Sort nodes so deterministic even if downstream reads working in insertion order.
    let mut nodes: Vec<Node> = working.keys().copied().collect();
    nodes.sort();
    for node in nodes {
        transform_stmt_candidates(candidates, node, |stmt| match stmt {
            CsharpminorStmt::Scall(Some(dst), sig, callee, args)
                if dead_regs.contains(dst) && !used_regs.contains(dst) =>
            {
                CsharpminorStmt::Scall(None, sig.clone(), callee.clone(), args.clone())
            }
            _ => stmt.clone(),
        });
        refresh_working_node(working, candidates, node);
    }
}

/// Collect free variable registers referenced inside a BuiltinArg<CsharpminorExpr>.
fn collect_builtin_arg_vars(ba: &BuiltinArg<CsharpminorExpr>, out: &mut HashSet<RTLReg>) {
    match ba {
        BuiltinArg::BA(e) => collect_expr_vars(e, out),
        BuiltinArg::BASplitLong(a, b) | BuiltinArg::BAAddPtr(a, b) => {
            collect_builtin_arg_vars(a, out);
            collect_builtin_arg_vars(b, out);
        }
        _ => {}
    }
}

/// Collect all free variable registers referenced in an expression.
fn collect_expr_vars(expr: &CsharpminorExpr, out: &mut HashSet<RTLReg>) {
    match expr {
        CsharpminorExpr::Evar(r) => {
            out.insert(*r);
        }
        CsharpminorExpr::Eunop(_, inner) => collect_expr_vars(inner, out),
        CsharpminorExpr::Ebinop(_, l, r) => {
            collect_expr_vars(l, out);
            collect_expr_vars(r, out);
        }
        CsharpminorExpr::Eload(_, addr) => collect_expr_vars(addr, out),
        CsharpminorExpr::Econdition(c, t, f) => {
            collect_expr_vars(c, out);
            collect_expr_vars(t, out);
            collect_expr_vars(f, out);
        }
        _ => {}
    }
}

/// Count occurrences of `Evar(reg)` in an expression.
fn count_var_in_expr(expr: &CsharpminorExpr, reg: RTLReg) -> usize {
    match expr {
        CsharpminorExpr::Evar(r) => {
            if *r == reg {
                1
            } else {
                0
            }
        }
        CsharpminorExpr::Eunop(_, inner) => count_var_in_expr(inner, reg),
        CsharpminorExpr::Ebinop(_, l, r) => count_var_in_expr(l, reg) + count_var_in_expr(r, reg),
        CsharpminorExpr::Eload(_, addr) => count_var_in_expr(addr, reg),
        CsharpminorExpr::Econdition(c, t, f) => {
            count_var_in_expr(c, reg) + count_var_in_expr(t, reg) + count_var_in_expr(f, reg)
        }
        _ => 0,
    }
}

fn count_var_in_builtin_arg(ba: &BuiltinArg<CsharpminorExpr>, reg: RTLReg) -> usize {
    match ba {
        BuiltinArg::BA(e) => count_var_in_expr(e, reg),
        BuiltinArg::BASplitLong(a, b) | BuiltinArg::BAAddPtr(a, b) => {
            count_var_in_builtin_arg(a, reg) + count_var_in_builtin_arg(b, reg)
        }
        _ => 0,
    }
}

/// Count occurrences of `Evar(reg)` in a statement.
fn count_var_in_stmt(stmt: &CsharpminorStmt, reg: RTLReg) -> usize {
    match stmt {
        CsharpminorStmt::Sset(_, expr) => count_var_in_expr(expr, reg),
        CsharpminorStmt::Sstore(_, addr, val) => {
            count_var_in_expr(addr, reg) + count_var_in_expr(val, reg)
        }
        CsharpminorStmt::Scall(_, _, callee, args) => {
            let c = if let either::Either::Left(e) = callee {
                count_var_in_expr(e, reg)
            } else {
                0
            };
            c + args
                .iter()
                .map(|a| count_var_in_expr(a, reg))
                .sum::<usize>()
        }
        CsharpminorStmt::Stailcall(_, callee, args) => {
            let c = if let either::Either::Left(e) = callee {
                count_var_in_expr(e, reg)
            } else {
                0
            };
            c + args
                .iter()
                .map(|a| count_var_in_expr(a, reg))
                .sum::<usize>()
        }
        CsharpminorStmt::Sbuiltin(_, _, args, res) => {
            args.iter()
                .map(|a| count_var_in_builtin_arg(a, reg))
                .sum::<usize>()
                + count_var_in_builtin_arg(res, reg)
        }
        CsharpminorStmt::Scond(_, args, _, _) => args
            .iter()
            .map(|a| count_var_in_expr(a, reg))
            .sum::<usize>(),
        CsharpminorStmt::Sjumptable(expr, _) => count_var_in_expr(expr, reg),
        CsharpminorStmt::Sreturn(expr) => count_var_in_expr(expr, reg),
        CsharpminorStmt::Sseq(stmts) => stmts
            .iter()
            .map(|s| count_var_in_stmt(s, reg))
            .sum::<usize>(),
        _ => 0,
    }
}

/// Substitute `replacement` for every `Evar(reg)` in an expression.
fn subst_expr_for_var_in_expr(
    expr: &CsharpminorExpr,
    reg: RTLReg,
    replacement: &CsharpminorExpr,
) -> CsharpminorExpr {
    match expr {
        CsharpminorExpr::Evar(r) if *r == reg => replacement.clone(),
        CsharpminorExpr::Eunop(op, inner) => CsharpminorExpr::Eunop(
            op.clone(),
            Box::new(subst_expr_for_var_in_expr(inner, reg, replacement)),
        ),
        CsharpminorExpr::Ebinop(op, l, r) => CsharpminorExpr::Ebinop(
            op.clone(),
            Box::new(subst_expr_for_var_in_expr(l, reg, replacement)),
            Box::new(subst_expr_for_var_in_expr(r, reg, replacement)),
        ),
        CsharpminorExpr::Eload(chunk, addr) => CsharpminorExpr::Eload(
            *chunk,
            Box::new(subst_expr_for_var_in_expr(addr, reg, replacement)),
        ),
        CsharpminorExpr::Econdition(c, t, f) => CsharpminorExpr::Econdition(
            Box::new(subst_expr_for_var_in_expr(c, reg, replacement)),
            Box::new(subst_expr_for_var_in_expr(t, reg, replacement)),
            Box::new(subst_expr_for_var_in_expr(f, reg, replacement)),
        ),
        _ => expr.clone(),
    }
}

fn subst_expr_for_var_in_ba(
    ba: &BuiltinArg<CsharpminorExpr>,
    reg: RTLReg,
    replacement: &CsharpminorExpr,
) -> BuiltinArg<CsharpminorExpr> {
    match ba {
        BuiltinArg::BA(e) => BuiltinArg::BA(subst_expr_for_var_in_expr(e, reg, replacement)),
        BuiltinArg::BASplitLong(a, b) => BuiltinArg::BASplitLong(
            Box::new(subst_expr_for_var_in_ba(a, reg, replacement)),
            Box::new(subst_expr_for_var_in_ba(b, reg, replacement)),
        ),
        BuiltinArg::BAAddPtr(a, b) => BuiltinArg::BAAddPtr(
            Box::new(subst_expr_for_var_in_ba(a, reg, replacement)),
            Box::new(subst_expr_for_var_in_ba(b, reg, replacement)),
        ),
        _ => ba.clone(),
    }
}

/// Substitute `replacement` for every `Evar(reg)` in a statement.
fn subst_expr_for_var_in_stmt(
    stmt: &CsharpminorStmt,
    reg: RTLReg,
    replacement: &CsharpminorExpr,
) -> CsharpminorStmt {
    match stmt {
        CsharpminorStmt::Sset(dst, expr) => {
            CsharpminorStmt::Sset(*dst, subst_expr_for_var_in_expr(expr, reg, replacement))
        }
        CsharpminorStmt::Sstore(chunk, addr, val) => CsharpminorStmt::Sstore(
            *chunk,
            subst_expr_for_var_in_expr(addr, reg, replacement),
            subst_expr_for_var_in_expr(val, reg, replacement),
        ),
        CsharpminorStmt::Scall(dst, sig, callee, args) => {
            let new_callee = match callee {
                either::Either::Left(e) => {
                    either::Either::Left(subst_expr_for_var_in_expr(e, reg, replacement))
                }
                other => other.clone(),
            };
            let new_args: Vec<_> = args
                .iter()
                .map(|a| subst_expr_for_var_in_expr(a, reg, replacement))
                .collect();
            CsharpminorStmt::Scall(*dst, sig.clone(), new_callee, new_args)
        }
        CsharpminorStmt::Stailcall(sig, callee, args) => {
            let new_callee = match callee {
                either::Either::Left(e) => {
                    either::Either::Left(subst_expr_for_var_in_expr(e, reg, replacement))
                }
                other => other.clone(),
            };
            let new_args: Vec<_> = args
                .iter()
                .map(|a| subst_expr_for_var_in_expr(a, reg, replacement))
                .collect();
            CsharpminorStmt::Stailcall(sig.clone(), new_callee, new_args)
        }
        CsharpminorStmt::Sbuiltin(dst, name, args, res) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| subst_expr_for_var_in_ba(a, reg, replacement))
                .collect();
            let new_res = subst_expr_for_var_in_ba(res, reg, replacement);
            CsharpminorStmt::Sbuiltin(*dst, name.clone(), new_args, new_res)
        }
        CsharpminorStmt::Scond(cond, args, ifso, ifnot) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| subst_expr_for_var_in_expr(a, reg, replacement))
                .collect();
            CsharpminorStmt::Scond(cond.clone(), new_args, *ifso, *ifnot)
        }
        CsharpminorStmt::Sjumptable(expr, targets) => CsharpminorStmt::Sjumptable(
            subst_expr_for_var_in_expr(expr, reg, replacement),
            targets.clone(),
        ),
        CsharpminorStmt::Sreturn(expr) => {
            CsharpminorStmt::Sreturn(subst_expr_for_var_in_expr(expr, reg, replacement))
        }
        CsharpminorStmt::Sseq(stmts) => {
            let new_stmts: Vec<_> = stmts
                .iter()
                .map(|s| subst_expr_for_var_in_stmt(s, reg, replacement))
                .collect();
            CsharpminorStmt::Sseq(new_stmts)
        }
        _ => stmt.clone(),
    }
}

/// Returns true if an expression is pure (no memory loads).
fn expr_is_pure(expr: &CsharpminorExpr) -> bool {
    match expr {
        CsharpminorExpr::Evar(_) | CsharpminorExpr::Econst(_) | CsharpminorExpr::Eaddrof(_) => true,
        CsharpminorExpr::Eunop(_, inner) => expr_is_pure(inner),
        CsharpminorExpr::Ebinop(_, l, r) => expr_is_pure(l) && expr_is_pure(r),
        CsharpminorExpr::Eload(_, _) => false,
        CsharpminorExpr::Econdition(c, t, f) => {
            expr_is_pure(c) && expr_is_pure(t) && expr_is_pure(f)
        }
    }
}

/// Inline single-def/single-use Iop temps; skips Iload, backward refs, and intervening redefs.
fn inline_single_use_temps(
    working: &mut HashMap<Node, CsharpminorStmt>,
    stmt_candidates: &mut CsharpStmtCandidates,
    db: &DecompileDB,
    protected_stack_regs: &HashSet<RTLReg>,
) {
    let inline_regs: HashSet<RTLReg> = db.rel_iter::<RTLReg>("emit_inline_temp").copied().collect();
    if inline_regs.is_empty() {
        return;
    }

    // Build def map: reg -> (node, candidate expressions). A temp is
    // inlinable only when every alternative at its defining node defines the
    // same register with a pure expression. This makes candidate preservation
    // conservative instead of choosing one definition arbitrarily.
    let mut def_map: HashMap<RTLReg, (Node, Vec<CsharpminorExpr>)> = HashMap::new();
    let mut multi_def: HashSet<RTLReg> = HashSet::new();
    let mut nodes: Vec<Node> = stmt_candidates.keys().copied().collect();
    nodes.sort_unstable();
    for node in nodes {
        let Some(stmts) = stmt_candidates.get(&node) else {
            continue;
        };
        let Some(CsharpminorStmt::Sset(reg, _)) = stmts.first() else {
            continue;
        };
        if !inline_regs.contains(reg) || protected_stack_regs.contains(reg) {
            continue;
        }
        let mut exprs = Vec::with_capacity(stmts.len());
        let uniform = stmts.iter().all(|stmt| match stmt {
            CsharpminorStmt::Sset(candidate_reg, expr) if candidate_reg == reg => {
                exprs.push(expr.clone());
                true
            }
            _ => false,
        });
        if !uniform || exprs.iter().any(|expr| !expr_is_pure(expr)) {
            multi_def.insert(*reg);
            continue;
        }
        if def_map.contains_key(reg) {
            multi_def.insert(*reg);
        } else {
            def_map.insert(*reg, (node, exprs));
        }
    }
    for reg in &multi_def {
        def_map.remove(reg);
    }

    if def_map.is_empty() {
        return;
    }

    // Build a conservative use map across every statement alternative. Uses
    // may differ between alternatives, but all must be confined to one node
    // and no alternative may duplicate the temp.
    let mut use_sites: HashMap<RTLReg, Vec<Node>> = HashMap::new();
    let mut unsafe_use: HashSet<RTLReg> = HashSet::new();
    let mut use_nodes: Vec<Node> = stmt_candidates.keys().copied().collect();
    use_nodes.sort_unstable();
    for node in use_nodes {
        let stmts = &stmt_candidates[&node];
        for (&reg, (def_node, _)) in &def_map {
            if node == *def_node {
                continue;
            }
            let mut used_here = false;
            for stmt in stmts {
                let count = count_var_in_stmt(stmt, reg);
                if count > 1 {
                    unsafe_use.insert(reg);
                }
                used_here |= count == 1;
            }
            if used_here {
                use_sites.entry(reg).or_default().push(node);
            }
        }
    }
    for sites in use_sites.values_mut() {
        sites.sort_unstable();
        sites.dedup();
    }

    // Process in sorted node order (by def_node address) for determinism.
    let mut candidates: Vec<(RTLReg, Node, Vec<CsharpminorExpr>)> = def_map
        .into_iter()
        .map(|(reg, (node, exprs))| (reg, node, exprs))
        .collect();
    candidates.sort_by_key(|(_, node, _)| exec_order_key(*node));

    // Track modified nodes to avoid stale substitutions in chained temps
    let mut modified_nodes: HashSet<Node> = HashSet::new();

    let mut inlined = 0usize;
    for (reg, def_node, def_exprs) in &candidates {
        if modified_nodes.contains(def_node) {
            continue;
        }
        if unsafe_use.contains(reg) {
            continue;
        }

        let sites = match use_sites.get(reg) {
            Some(s) => s,
            None => continue,
        };
        if sites.len() != 1 {
            continue;
        }
        let use_node = sites[0];

        if modified_nodes.contains(&use_node) {
            continue;
        }

        // Backward-reference and intervening-redefinition safety are enforced upstream by src_not_redefined_on_paths_to_uses, so the old unsound address-window scan is gone (STRUCT-1).

        let use_stmts = match stmt_candidates.get(&use_node) {
            Some(stmts) => stmts.clone(),
            None => continue,
        };
        let Some(canonical_use) = use_stmts.first() else {
            continue;
        };
        let Some(canonical_def) = def_exprs.first() else {
            continue;
        };
        let canonical = if count_var_in_stmt(canonical_use, *reg) == 1 {
            subst_expr_for_var_in_stmt(canonical_use, *reg, canonical_def)
        } else {
            canonical_use.clone()
        };
        let mut alternatives = Vec::new();
        for use_stmt in &use_stmts {
            match count_var_in_stmt(use_stmt, *reg) {
                0 => alternatives.push(use_stmt.clone()),
                1 => alternatives.extend(
                    def_exprs
                        .iter()
                        .map(|expr| subst_expr_for_var_in_stmt(use_stmt, *reg, expr)),
                ),
                _ => unreachable!("unsafe uses were rejected above"),
            }
        }
        set_stmt_candidates_with_canonical(stmt_candidates, use_node, canonical, alternatives);
        replace_stmt_candidates(stmt_candidates, *def_node, CsharpminorStmt::Snop);
        refresh_working_node(working, stmt_candidates, use_node);
        refresh_working_node(working, stmt_candidates, *def_node);
        modified_nodes.insert(use_node);
        modified_nodes.insert(*def_node);
        inlined += 1;
    }

    if inlined > 0 {
        debug!("inline_single_use_temps: inlined {} temporaries", inlined);
    }
}

#[cfg(test)]
mod candidate_handoff_tests {
    use super::{
        stable_stmt_candidates, StructuringPass, STRUCTURE_WORLD_FLAT, STRUCTURE_WORLD_STRUCTURED,
    };
    use crate::decompile::elevator::DecompileDB;
    use crate::decompile::passes::pass::IRPass;
    use crate::x86::types::{
        CminorBinop, Constant, CsharpminorExpr, CsharpminorStmt, MemoryChunk, Node,
    };

    fn alternatives() -> Vec<CsharpminorStmt> {
        vec![
            CsharpminorStmt::Snop,
            CsharpminorStmt::Sset(7, CsharpminorExpr::Evar(11)),
            CsharpminorStmt::Sset(7, CsharpminorExpr::Evar(12)),
        ]
    }

    #[test]
    fn candidate_grouping_is_order_independent_and_prefers_a_real_statement() {
        let node = 0x20;
        let forward = stable_stmt_candidates(
            alternatives()
                .into_iter()
                .map(|stmt| (node, stmt))
                .collect::<Vec<_>>(),
        );
        let reverse = stable_stmt_candidates(
            alternatives()
                .into_iter()
                .rev()
                .map(|stmt| (node, stmt))
                .collect::<Vec<_>>(),
        );

        assert_eq!(forward, reverse);
        assert_eq!(forward[&node].len(), 3);
        assert!(!matches!(forward[&node][0], CsharpminorStmt::Snop));
    }

    fn run_with_order(rows: impl IntoIterator<Item = CsharpminorStmt>) -> Vec<CsharpminorStmt> {
        let node: Node = 0x20;
        let func = 0x10;
        let mut db = DecompileDB::default();
        for stmt in rows {
            db.rel_push("csharp_stmt_candidate", (node, stmt));
        }
        db.rel_push("instr_in_function", (node, func));
        db.rel_push("emit_function", (func, "candidate_order", node));

        StructuringPass::default().run(&mut db);

        let mut result: Vec<CsharpminorStmt> = db
            .rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt")
            .filter_map(|(n, stmt)| (*n == node).then_some(stmt.clone()))
            .collect();
        result.sort_by_cached_key(|stmt| format!("{stmt:?}"));
        result
    }

    #[test]
    fn structuring_retains_candidates_independent_of_relation_insertion_order() {
        let forward = run_with_order(alternatives());
        let reverse = run_with_order(alternatives().into_iter().rev());

        assert_eq!(forward, reverse);
        assert_eq!(forward.len(), 3);
    }

    #[test]
    fn effect_boundaries_keep_copy_and_constant_inputs_until_a_checked_transfer() {
        let mut db = DecompileDB::default();
        let function = 1_u64;
        let value = Constant::Ointconst(7);
        let statements = [
            (
                30_u64,
                CsharpminorStmt::Sset(11, CsharpminorExpr::Econst(value.clone())),
            ),
            (10, CsharpminorStmt::Sset(12, CsharpminorExpr::Evar(11))),
            (20, CsharpminorStmt::Sreturn(CsharpminorExpr::Evar(12))),
        ];
        for (node, statement) in &statements {
            db.rel_push("csharp_stmt_candidate", (*node, statement.clone()));
            db.rel_push("instr_in_function", (*node, function));
        }
        db.rel_push("emit_function", (function, "effect_boundary", 30_u64));
        db.rel_push("func_entry_node", (function, 30_u64));
        for edge in [(30_u64, 10_u64), (10, 20)] {
            db.rel_push("next", edge);
            db.rel_push("cminor_succ", edge);
        }
        db.rel_push("single_def_const", (11_u64, value));
        db.rel_push("effect_value_boundary", (10_u64,));
        db.rel_push("emit_inline_temp", 12_u64);
        StructuringPass::default().run(&mut db);
        for row in &statements[..2] {
            assert!(db
                .rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt")
                .any(|actual| actual == row));
        }
    }

    #[test]
    fn loop_metadata_publishes_atomic_structured_and_flat_worlds() {
        let func = 0x1000;
        let node = 0x1010;
        let stmt = CsharpminorStmt::Sset(7, CsharpminorExpr::Evar(11));
        let mut db = DecompileDB::default();
        db.rel_push("csharp_stmt_candidate", (node, stmt.clone()));
        db.rel_push("instr_in_function", (node, func));
        db.rel_push("emit_function", (func, "worlds", node));
        // Cshminor's Ascent loop analysis is a structural interpretation even
        // when this one-node fixture leaves the statement value unchanged.
        db.rel_push("emit_loop_body", (func, node, node));

        StructuringPass::default().run(&mut db);

        let mut worlds: Vec<_> = db
            .rel_iter::<(u64, u8, bool)>("structure_world")
            .copied()
            .collect();
        worlds.sort_unstable();
        assert_eq!(
            worlds,
            vec![
                (func, STRUCTURE_WORLD_STRUCTURED, true),
                (func, STRUCTURE_WORLD_FLAT, false),
            ]
        );
        for world in [STRUCTURE_WORLD_STRUCTURED, STRUCTURE_WORLD_FLAT] {
            assert!(db
                .rel_iter::<(u64, u8, Node, CsharpminorStmt)>("csharp_stmt_world")
                .any(|row| row == &(func, world, node, stmt.clone())));
        }
        assert!(db
            .rel_iter::<(u64, Node)>("structure_unchanged_node")
            .any(|row| row == &(func, node)));
    }

    #[test]
    fn structuring_keeps_a_definition_observed_as_overlapping_stack_storage() {
        let func: u64 = 0x1000;
        let writer: Node = 0x1010;
        let read: Node = 0x1020;
        let owner: u64 = 0x7000;
        let read_value: u64 = 0x7100;
        let initial = Constant::Ointconst(0xa1a0);
        let mut db = DecompileDB::default();

        db.rel_push(
            "csharp_stmt_candidate",
            (
                writer,
                CsharpminorStmt::Sset(owner, CsharpminorExpr::Econst(initial.clone())),
            ),
        );
        db.rel_push(
            "csharp_stmt_candidate",
            (
                read,
                CsharpminorStmt::Sset(
                    read_value,
                    CsharpminorExpr::Eload(
                        MemoryChunk::MInt8Unsigned,
                        Box::new(CsharpminorExpr::Ebinop(
                            CminorBinop::Oaddl,
                            Box::new(CsharpminorExpr::Eaddrof(owner as usize)),
                            Box::new(CsharpminorExpr::Econst(Constant::Olongconst(1))),
                        )),
                    ),
                ),
            ),
        );
        db.rel_push("single_def_const", (owner, initial));
        db.rel_push("emit_inline_temp", owner);
        db.rel_push(
            "frame_read_storage_owner",
            (func, read, 5_i64, 4_i64, owner),
        );
        db.rel_push("instr_in_function", (writer, func));
        db.rel_push("instr_in_function", (read, func));
        db.rel_push("emit_function", (func, "observed_storage", writer));
        db.rel_push("next", (writer, read));
        db.rel_push("cminor_succ", (writer, read));

        StructuringPass::default().run(&mut db);

        let writer_stmts: Vec<_> = db
            .rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt")
            .filter_map(|(node, stmt)| (*node == writer).then_some(stmt))
            .collect();
        assert!(writer_stmts.iter().any(|stmt| matches!(
            stmt,
            CsharpminorStmt::Sset(reg, CsharpminorExpr::Econst(Constant::Ointconst(0xa1a0)))
                if *reg == owner
        )));
        assert!(!writer_stmts
            .iter()
            .any(|stmt| matches!(stmt, CsharpminorStmt::Snop)));
    }
}

#[cfg(test)]
mod copy_propagation_tests {
    use super::{
        canonical_working, inline_constants, propagate_copies, CopyPropagationProgram,
        CsharpStmtCandidates,
    };
    use crate::decompile::elevator::DecompileDB;
    use crate::x86::types::{Constant, CsharpminorExpr, CsharpminorStmt};
    use std::collections::{HashMap, HashSet};

    const SRC: u64 = 11;
    const DST: u64 = 22;

    fn synthetic_ids<const N: usize>() -> [u64; N] {
        std::array::from_fn(|index| index as u64 + 100)
    }

    fn copy_stmt() -> CsharpminorStmt {
        CsharpminorStmt::Sset(DST, CsharpminorExpr::Evar(SRC))
    }

    fn use_stmt() -> CsharpminorStmt {
        CsharpminorStmt::Sreturn(CsharpminorExpr::Evar(DST))
    }

    #[test]
    fn descending_node_ids_propagate_only_along_cfg_edges() {
        let [use_node, intro] = synthetic_ids();

        let mut prog = CopyPropagationProgram::default();
        prog.stmt.push((intro, copy_stmt()));
        prog.stmt.push((use_node, use_stmt()));
        prog.entry.push((intro,));
        prog.edge.push((intro, use_node));

        prog.run();

        assert!(prog
            .applicable_subst
            .iter()
            .any(|fact| fact == &(use_node, DST, SRC)));
        assert!(prog.dead_copy_v2.iter().any(|fact| fact == &(intro,)));
    }

    #[test]
    fn escaped_stack_cell_copy_is_not_a_register_rename() {
        let [intro, use_node] = synthetic_ids();

        let mut prog = CopyPropagationProgram::default();
        prog.stmt.push((intro, copy_stmt()));
        prog.stmt.push((use_node, use_stmt()));
        prog.entry.push((intro,));
        prog.edge.push((intro, use_node));
        prog.protected_copy_dst.push((DST,));

        prog.run();

        assert!(!prog
            .copy_intro
            .iter()
            .any(|fact| fact == &(intro, DST, SRC)));
        assert!(!prog
            .applicable_subst
            .iter()
            .any(|fact| fact == &(use_node, DST, SRC)));
        assert!(!prog.dead_copy_v2.iter().any(|fact| fact == &(intro,)));
    }

    #[test]
    fn escaped_stack_cell_survives_copy_and_constant_folding_pipeline() {
        let [constant_node, store_node, use_node, func] = synthetic_ids();
        let escaped = DST;
        let mut candidates: CsharpStmtCandidates = HashMap::from([
            (
                constant_node,
                vec![CsharpminorStmt::Sset(
                    SRC,
                    CsharpminorExpr::Econst(Constant::Olongconst(0x17_0000_000b)),
                )],
            ),
            (store_node, vec![copy_stmt()]),
            (use_node, vec![use_stmt()]),
        ]);
        let mut working = canonical_working(&candidates);
        let mut db = DecompileDB::default();
        db.rel_push("func_entry_node", (func, constant_node));
        db.rel_push("cminor_succ", (constant_node, store_node));
        db.rel_push("cminor_succ", (store_node, use_node));
        db.rel_push(
            "single_def_const",
            (SRC, Constant::Olongconst(0x17_0000_000b)),
        );
        let escaped_regs = HashSet::from([escaped]);

        propagate_copies(&mut working, &mut candidates, &mut db, &escaped_regs);
        inline_constants(&mut working, &mut candidates, &db, &escaped_regs);

        assert!(matches!(
            working.get(&store_node),
            Some(CsharpminorStmt::Sset(dst, CsharpminorExpr::Econst(
                Constant::Olongconst(0x17_0000_000b)
            ))) if *dst == escaped
        ));
        assert!(matches!(
            working.get(&use_node),
            Some(CsharpminorStmt::Sreturn(CsharpminorExpr::Evar(reg))) if *reg == escaped
        ));
    }

    #[test]
    fn disconnected_numeric_neighbors_do_not_propagate_copies() {
        let [intro, use_node] = synthetic_ids();

        let mut prog = CopyPropagationProgram::default();
        prog.stmt.push((intro, copy_stmt()));
        prog.stmt.push((use_node, use_stmt()));
        prog.entry.push((intro,));

        prog.run();

        assert!(!prog
            .applicable_subst
            .iter()
            .any(|fact| fact == &(use_node, DST, SRC)));
        assert!(!prog.dead_copy_v2.iter().any(|fact| fact == &(intro,)));
    }

    #[test]
    fn branch_merge_rejects_copy_killed_on_one_path() {
        let [clean, use_node, intro, kill] = synthetic_ids();

        let mut prog = CopyPropagationProgram::default();
        prog.stmt.push((intro, copy_stmt()));
        prog.stmt.push((clean, CsharpminorStmt::Snop));
        prog.stmt
            .push((kill, CsharpminorStmt::Sset(SRC, CsharpminorExpr::Evar(33))));
        prog.stmt.push((use_node, use_stmt()));
        prog.entry.push((intro,));
        prog.edge.extend([
            (intro, clean),
            (intro, kill),
            (clean, use_node),
            (kill, use_node),
        ]);

        prog.run();

        assert!(!prog
            .applicable_subst
            .iter()
            .any(|fact| fact == &(use_node, DST, SRC)));
        assert!(!prog.dead_copy_v2.iter().any(|fact| fact == &(intro,)));
    }
}
