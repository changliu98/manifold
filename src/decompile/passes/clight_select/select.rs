#![allow(dead_code, unused_variables, unused_imports, unused_mut)]

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::clight_select::query::{
    extract_functions, extract_ite_info, extract_loop_info,
    CalleeSignature, FunctionData, IteInfo, LoopInfo,
};
use crate::decompile::passes::c_pass::convert::from_relations::{convert_stmt, ConversionContext};
use crate::decompile::passes::c_pass::helpers::{xtype_string_to_ctype, convert_param_type_from_param, param_name_for_reg};
use crate::decompile::passes::c_pass::print;
use crate::decompile::passes::csh_pass::ident_from_node;
use crate::x86::types::*;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::ffi::{CStr, CString};
use std::os::raw::c_uint;
use rayon::prelude::*;

/// Synthetic node base for variable declaration nodes (ID = DECL_NODE_BASE + register_id).
const DECL_NODE_BASE: u64 = 0xDEC0_0000_0000_0000;

/// Synthetic node base for function parameter nodes (ID = PARAM_NODE_BASE + param_position).
const PARAM_NODE_BASE: u64 = 0xDECA_0000_0000_0000;

/// Synthetic node base for struct field definition "nodes".
const STRUCT_FIELD_NODE_BASE: u64 = 0xDEF0_0000_0000_0000;

/// Lightweight index-based backtracking state storing only indices into FunctionData's candidate arrays.
#[derive(Clone, Debug)]
struct SelectionState {
    /// Per statement node: Some(idx) = use candidate[idx], None = SKIP.
    candidate_idx: HashMap<Node, Option<usize>>,
}

pub(crate) struct ProgramSelectionState {
    /// (func_addr, node) -> candidate index
    pub(crate) candidate_idx: HashMap<(Address, Node), Option<usize>>,
    /// (func_addr, reg) -> type candidate index
    pub(crate) var_decl_idx: HashMap<(Address, RTLReg), usize>,
    /// Global struct field type selections (shared across functions)
    pub(crate) struct_field_type_idx: HashMap<(String, String), usize>,
    /// (func_addr, reg) -> inferred type-string for registers whose inferred type is not among the enumerated candidates (generic-inference path only, empty otherwise); applied as a synthetic candidate.
    pub(crate) var_type_override: HashMap<(Address, RTLReg), String>,
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

    pub statements: HashMap<Node, ClightStmt>,

    pub successors: HashMap<Node, Vec<Node>>,

    pub used_regs: HashSet<RTLReg>,

    pub struct_fields: HashMap<i64, Vec<(i64, Ident, MemoryChunk)>>,

    pub sseq_groups: HashMap<Node, Vec<Node>>,

    pub var_types: HashMap<RTLReg, String>,
    pub var_type_candidates: HashMap<RTLReg, Vec<String>>,
    pub var_decl_idx: HashMap<RTLReg, usize>,

    pub loop_headers: HashSet<Node>,
    pub switch_heads: HashSet<Node>,

    pub reg_struct_ids: HashMap<RTLReg, usize>,

    pub loop_info: HashMap<Node, LoopInfo>,
}


pub fn select_clight_stmts(db: &DecompileDB) -> Result<Vec<SelectedFunction>, String> {
    let (mut functions, id_to_name) = extract_functions(db)?;

    let mut name_to_ident: HashMap<String, Ident> = HashMap::new();
    {
        // Iterate in sorted (id, name) order so that, on a sanitized-name collision, the surviving Ident is deterministic across runs.
        let mut sorted_id_name: Vec<(&usize, &String)> = id_to_name.iter().collect();
        sorted_id_name.sort_by_key(|(id, name)| (**id, (*name).clone()));
        for (id, name) in sorted_id_name {
            let sanitized = crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(name);
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

    // Sort candidates deterministically: prefer Efield form over raw pointer-deref-with-cast (so search starts on the recovered-field variant when both compile); secondary key is a deterministic hash (Ascent parallel order is arbitrary).
    for func in &mut functions {
        for candidates in func.node_statements.values_mut() {
            if candidates.len() > 1 {
                // When a node offers a byte-addressed `(char *)base + c` alongside a bare `base + c` on a non-char pointer, both compile but the bare form silently re-scales the constant by the element size (B2 mis-scaling), so demote it and search the byte-correct char-cast candidate first.
                let has_byte_cast = candidates.iter().any(stmt_uses_charcast_ptr_arith);
                candidates.sort_by_key(|s| {
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
                    (priority, stmt_deterministic_hash(s))
                });
            }
        }
    }

    // Dump candidate distribution stats when CANDIDATE_STATS_OUT is set
    if let Ok(out_path) = std::env::var("CANDIDATE_STATS_OUT") {
        let mut histogram: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
        let mut total_nodes: usize = 0;
        for func in &functions {
            for stmts in func.node_statements.values() {
                total_nodes += 1;
                *histogram.entry(stmts.len()).or_insert(0) += 1;
            }
        }
        // Write as JSON: {"total_nodes": N, "total_functions": N, "histogram": {"1": N, "2": N, ...}}
        let hist_json: String = histogram.iter()
            .map(|(k, v)| format!("\"{}\": {}", k, v))
            .collect::<Vec<_>>().join(", ");
        let json = format!(
            "{{\"total_nodes\": {}, \"total_functions\": {}, \"histogram\": {{{}}}}}",
            total_nodes, functions.len(), hist_json
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
            let vtc = sorted_kv(f.var_type_candidates.iter().map(|(r, cs)| format!("{}:{:?}", r, cs)).collect());
            let ns = sorted_kv(f.node_statements.iter().map(|(n, ss)| format!("{}:{:?}", n, ss)).collect());
            let sigs = sorted_kv(f.callee_signatures.iter().map(|(id, s)| {
                format!("{}:{}/{:?}/{:?}", id, s.param_count, s.return_type, s.param_types)
            }).collect());
            let sftc = sorted_kv(f.struct_field_type_candidates.iter().map(|(k, v)| format!("{:?}:{:?}", k, v)).collect());
            let sfti = sorted_kv(f.struct_field_type_idx.iter().map(|(k, v)| format!("{:?}:{}", k, v)).collect());
            let rsi = sorted_kv(f.reg_struct_ids.iter().map(|(k, v)| format!("{}:{}", k, v)).collect());
            eprintln!(
                "[FP-IN] {:016x} vtc={:016x} ns={:016x} sigs={:016x} ret={:016x} rsi={:016x} sftc={:016x} sfti={:016x}",
                f.address, fh(&vtc), fh(&ns), fh(&sigs), fh(&format!("{:?}", f.return_type)),
                fh(&rsi), fh(&sftc), fh(&sfti),
            );
        }
    }

    // Statement-form + type selection is done entirely by the Z3/SMT inference model; the clang-in-the-loop greedy search has been removed (full migration to Z3).
    let best_state =
        crate::decompile::passes::clight_select::solve::infer_select_program(&functions, &name_to_ident);

    // Split result into per-function SelectedFunction
    let selected: Vec<SelectedFunction> = functions
        .iter()
        .map(|func| {
            build_selected_function_from_program_state(
                func, &best_state, &loop_info_all, &ite_info_all,
            )
        })
        .collect();

    if std::env::var("DET_FP").is_ok() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let fh = |s: &str| -> u64 {
            let mut h = DefaultHasher::new();
            s.hash(&mut h);
            h.finish()
        };
        for f in &selected {
            let mut st: Vec<String> = f.statements.iter().map(|(n, s)| format!("{}:{:?}", n, s)).collect();
            st.sort();
            let mut su: Vec<String> = f.successors.iter().map(|(n, v)| format!("{}:{:?}", n, v)).collect();
            su.sort();
            let mut sg: Vec<String> = f.sseq_groups.iter().map(|(k, v)| format!("{}:{:?}", k, v)).collect();
            sg.sort();
            // LoopInfo HashMaps have non-deterministic Debug order; key-sort so the fingerprint only moves on real content changes.
            let mut li: Vec<String> = f.loop_info.iter().map(|(n, v)| {
                let mut bs: Vec<String> = v.break_stmts.iter().map(|(k, s)| format!("{}:{:?}", k, s)).collect();
                bs.sort();
                let mut er: Vec<(Node, (Node, Node))> = v.exit_returns.iter().map(|(k, p)| (*k, *p)).collect();
                er.sort();
                format!(
                    "{}:body={:?} exit={:?} step={:?} primary={:?} breaks=[{}] rets={:?}",
                    n, v.body_nodes, v.exit_node, v.step_node, v.primary_exit, bs.join(","), er
                )
            }).collect();
            li.sort();
            let mut rsi: Vec<String> = f.reg_struct_ids.iter().map(|(k, v)| format!("{}:{}", k, v)).collect();
            rsi.sort();
            eprintln!(
                "[FP-A] {:016x} stmts={:016x} succ={:016x} sseq={:016x} linfo={:016x} rsi={:016x}",
                f.address, fh(&st.join(",")), fh(&su.join(",")), fh(&sg.join(",")),
                fh(&li.join(",")), fh(&rsi.join(",")),
            );
        }
    }

    Ok(selected)
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
    let mut items: Vec<String> = statements.iter().map(|(n, s)| format!("{}:{:?}", n, s)).collect();
    items.sort();
    let mut h = DefaultHasher::new();
    items.join(",").hash(&mut h);
    eprintln!("[FP-{}] {:016x} {:016x}", stage, addr, h.finish());
}

/// Build a SelectedFunction from the program-level search result for one function.
fn build_selected_function_from_program_state(
    func: &FunctionData,
    program_state: &ProgramSelectionState,
    loop_info_all: &HashMap<Address, HashMap<Node, LoopInfo>>,
    ite_info_all: &HashMap<Address, HashMap<Node, IteInfo>>,
) -> SelectedFunction {
    let addr = func.address;

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

    let per_func_state = SelectionState { candidate_idx };

    // Materialize and post-process
    let mut statements = materialize_statements(&per_func_state, func);
    det_fp_stage(func.address, "S1mat", &statements);

    let func_loop_info = loop_info_all.get(&func.address).cloned().unwrap_or_default();

    assemble_loops(&mut statements, &func_loop_info, &func.successors);
    det_fp_stage(func.address, "S2loop", &statements);

    let func_ite_info = ite_info_all.get(&func.address).cloned().unwrap_or_default();
    assemble_ite(&mut statements, &func_ite_info);
    det_fp_stage(func.address, "S3ite", &statements);

    // Sort sseq groups by head so overlapping groups resolve deterministically.
    let mut sorted_sseq: Vec<(Node, Vec<Node>)> = func.sseq_groups.iter()
        .map(|(&h, m)| (h, m.clone()))
        .collect();
    sorted_sseq.sort_by_key(|(h, _)| *h);
    for (head, members) in &sorted_sseq {
        if members.len() <= 1 {
            continue;
        }
        let mut seq_stmts = Vec::new();
        for &member_node in members {
            if let Some(stmt) = statements.get(&member_node) {
                seq_stmts.push(stmt.clone());
            }
        }
        if seq_stmts.len() > 1 {
            let flattened = flatten_sequence(seq_stmts);
            statements.insert(*head, ClightStmt::Ssequence(flattened));
            for &member_node in members {
                if member_node != *head {
                    statements.remove(&member_node);
                }
            }
        }
    }

    det_fp_stage(func.address, "S4sseq", &statements);
    inline_control_flow_bodies(&mut statements, &func.successors);
    det_fp_stage(func.address, "S5inline", &statements);
    flatten_cascading_ifthenelse_all(&mut statements);
    det_fp_stage(func.address, "S6flat", &statements);
    // CF-3 always on (gate removed 2026-06-10): /bin/ls -2.2% gotos; case bodies that stay multi-referenced until CF-6 deduplication become inlinable afterward.
    inline_switch_case_bodies(&mut statements);
    det_fp_stage(func.address, "S6sw", &statements);
    deduplicate_identical_blocks(&mut statements);
    det_fp_stage(func.address, "S7dedup", &statements);
    ensure_goto_labels(&mut statements);
    det_fp_stage(func.address, "S8labels", &statements);

    SelectedFunction {
        address: func.address,
        name: func.name.clone(),
        entry_node: func.entry_node,
        return_type: func.return_type.clone(),
        param_regs: func.param_regs.clone(),
        param_types: func.param_types.clone(),
        stack_size: func.stack_size,
        statements,
        successors: func.successors.clone(),
        used_regs: func.used_regs.clone(),
        struct_fields: func.struct_fields.clone(),
        sseq_groups: func.sseq_groups.clone(),
        var_types: func.var_types.clone(),
        var_type_candidates,
        var_decl_idx,
        loop_headers: func.loop_headers.clone(),
        switch_heads: func.switch_heads.clone(),
        reg_struct_ids: func.reg_struct_ids.clone(),
        loop_info: func_loop_info,
    }
}


fn materialize_statements(
    state: &SelectionState,
    func: &FunctionData,
) -> HashMap<Node, ClightStmt> {
    let mut statements = HashMap::new();
    for (node, candidates) in &func.node_statements {
        match state.candidate_idx.get(node).copied().flatten() {
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

fn scan_deref_regs_expr(expr: &ClightExpr) -> Vec<(RTLReg, bool)> {
    let mut out = Vec::new();
    match expr {
        ClightExpr::Efield(inner, _, _) => {
            // The inner should be Ederef(Etempvar(reg, _), Tstruct(...))
            if let ClightExpr::Ederef(ptr_expr, _) = inner.as_ref() {
                match ptr_expr.as_ref() {
                    ClightExpr::Etempvar(id, _) => out.push((*id as RTLReg, true)),
                    ClightExpr::Ecast(inner2, _) => {
                        if let ClightExpr::Etempvar(id, _) = inner2.as_ref() {
                            out.push((*id as RTLReg, true));
                        }
                    }
                    _ => {}
                }
                out.extend(scan_deref_regs_expr(ptr_expr));
            } else {
                out.extend(scan_deref_regs_expr(inner));
            }
        }
        ClightExpr::Ederef(inner, _) => {
            match inner.as_ref() {
                ClightExpr::Etempvar(id, _) => out.push((*id as RTLReg, false)),
                ClightExpr::Ecast(inner2, _) => {
                    if let ClightExpr::Etempvar(id, _) = inner2.as_ref() {
                        out.push((*id as RTLReg, false));
                    }
                }
                _ => {}
            }
            out.extend(scan_deref_regs_expr(inner));
        }
        ClightExpr::Eunop(_, inner, _) => out.extend(scan_deref_regs_expr(inner)),
        ClightExpr::Ebinop(_, l, r, _) => {
            out.extend(scan_deref_regs_expr(l));
            out.extend(scan_deref_regs_expr(r));
        }
        ClightExpr::Ecast(inner, _) => out.extend(scan_deref_regs_expr(inner)),
        ClightExpr::Eaddrof(inner, _) => out.extend(scan_deref_regs_expr(inner)),
        ClightExpr::Econdition(c, t, f, _) => {
            out.extend(scan_deref_regs_expr(c));
            out.extend(scan_deref_regs_expr(t));
            out.extend(scan_deref_regs_expr(f));
        }
        _ => {}
    }
    out
}

/// Walk an expression and collect register IDs directly used by mul/div/mod/and/or/xor/shl/shr (ill-typed on C pointers); drives the "force int" half of constraint propagation.
fn scan_pure_int_regs_expr(expr: &ClightExpr, out: &mut BTreeSet<RTLReg>) {
    match expr {
        ClightExpr::Ebinop(op, l, r, _) => {
            let pure_int = matches!(
                op,
                ClightBinaryOp::Omul
                    | ClightBinaryOp::Odiv
                    | ClightBinaryOp::Omod
                    | ClightBinaryOp::Oand
                    | ClightBinaryOp::Oor
                    | ClightBinaryOp::Oxor
                    | ClightBinaryOp::Oshl
                    | ClightBinaryOp::Oshr
            );
            if pure_int {
                let mut peel = |e: &ClightExpr| {
                    let mut cur = e;
                    loop {
                        match cur {
                            ClightExpr::Etempvar(id, _) => {
                                out.insert(*id as RTLReg);
                                break;
                            }
                            ClightExpr::Ecast(inner, _) => cur = inner,
                            _ => break,
                        }
                    }
                };
                peel(l);
                peel(r);
            }
            scan_pure_int_regs_expr(l, out);
            scan_pure_int_regs_expr(r, out);
        }
        ClightExpr::Ederef(inner, _)
        | ClightExpr::Eaddrof(inner, _)
        | ClightExpr::Eunop(_, inner, _)
        | ClightExpr::Ecast(inner, _)
        | ClightExpr::Efield(inner, _, _) => scan_pure_int_regs_expr(inner, out),
        ClightExpr::Econdition(c, t, f, _) => {
            scan_pure_int_regs_expr(c, out);
            scan_pure_int_regs_expr(t, out);
            scan_pure_int_regs_expr(f, out);
        }
        _ => {}
    }
}

pub(crate) fn scan_pure_int_regs_stmt(stmt: &ClightStmt, out: &mut BTreeSet<RTLReg>) {
    match stmt {
        ClightStmt::Sassign(l, r) => { scan_pure_int_regs_expr(l, out); scan_pure_int_regs_expr(r, out); }
        ClightStmt::Sset(_, e) => scan_pure_int_regs_expr(e, out),
        ClightStmt::Scall(_, f, args) => {
            scan_pure_int_regs_expr(f, out);
            for a in args { scan_pure_int_regs_expr(a, out); }
        }
        ClightStmt::Sreturn(Some(e)) => scan_pure_int_regs_expr(e, out),
        ClightStmt::Sifthenelse(c, t, e) => {
            scan_pure_int_regs_expr(c, out);
            scan_pure_int_regs_stmt(t, out);
            scan_pure_int_regs_stmt(e, out);
        }
        ClightStmt::Ssequence(ss) => { for s in ss { scan_pure_int_regs_stmt(s, out); } }
        ClightStmt::Sloop(a, b) => { scan_pure_int_regs_stmt(a, out); scan_pure_int_regs_stmt(b, out); }
        ClightStmt::Slabel(_, inner) => scan_pure_int_regs_stmt(inner, out),
        ClightStmt::Sswitch(e, cases) => {
            scan_pure_int_regs_expr(e, out);
            for (_, s) in cases { scan_pure_int_regs_stmt(s, out); }
        }
        _ => {}
    }
}

pub(crate) fn scan_deref_regs_stmt(stmt: &ClightStmt) -> Vec<(RTLReg, bool)> {
    let mut out = Vec::new();
    match stmt {
        ClightStmt::Sassign(lhs, rhs) => {
            out.extend(scan_deref_regs_expr(lhs));
            out.extend(scan_deref_regs_expr(rhs));
        }
        ClightStmt::Sset(_, expr) => out.extend(scan_deref_regs_expr(expr)),
        ClightStmt::Scall(_, f, args) => {
            out.extend(scan_deref_regs_expr(f));
            for a in args { out.extend(scan_deref_regs_expr(a)); }
        }
        ClightStmt::Sreturn(Some(e)) => out.extend(scan_deref_regs_expr(e)),
        ClightStmt::Sifthenelse(c, t, e) => {
            out.extend(scan_deref_regs_expr(c));
            out.extend(scan_deref_regs_stmt(t));
            out.extend(scan_deref_regs_stmt(e));
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss { out.extend(scan_deref_regs_stmt(s)); }
        }
        ClightStmt::Slabel(_, inner) => out.extend(scan_deref_regs_stmt(inner)),
        _ => {}
    }
    out
}

// The static Clight type carried by an expression.
fn clight_expr_type(e: &ClightExpr) -> &ClightType {
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
            ClightExpr::Econdition(c, t, f, _) => expr_has_efield(c) || expr_has_efield(t) || expr_has_efield(f),
            _ => false,
        }
    }
    match stmt {
        ClightStmt::Sassign(l, r) => expr_has_efield(l) || expr_has_efield(r),
        ClightStmt::Sset(_, e) => expr_has_efield(e),
        ClightStmt::Scall(_, f, args) => expr_has_efield(f) || args.iter().any(expr_has_efield),
        ClightStmt::Sbuiltin(_, _, _, args) => args.iter().any(expr_has_efield),
        ClightStmt::Sreturn(Some(e)) => expr_has_efield(e),
        ClightStmt::Sifthenelse(c, t, e) => expr_has_efield(c) || stmt_uses_efield(t) || stmt_uses_efield(e),
        ClightStmt::Ssequence(ss) => ss.iter().any(stmt_uses_efield),
        ClightStmt::Sloop(a, b) => stmt_uses_efield(a) || stmt_uses_efield(b),
        ClightStmt::Slabel(_, inner) => stmt_uses_efield(inner),
        ClightStmt::Sswitch(e, cases) => expr_has_efield(e) || cases.iter().any(|(_, s)| stmt_uses_efield(s)),
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
        ClightStmt::Sifthenelse(c, t, e) => pred(c) || walk_stmt_exprs(t, pred) || walk_stmt_exprs(e, pred),
        ClightStmt::Ssequence(ss) => ss.iter().any(|s| walk_stmt_exprs(s, pred)),
        ClightStmt::Sloop(a, b) => walk_stmt_exprs(a, pred) || walk_stmt_exprs(b, pred),
        ClightStmt::Slabel(_, inner) => walk_stmt_exprs(inner, pred),
        ClightStmt::Sswitch(e, cases) => pred(e) || cases.iter().any(|(_, s)| walk_stmt_exprs(s, pred)),
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
    headers.sort_by(|a, b| a.1.body_nodes.len().cmp(&b.1.body_nodes.len()).then(a.0.cmp(b.0)));

    // Top-level value nodes tail-duplicated into a loop exit branch (A5), removed below so they are not also emitted (hoisted) outside the loop; each has a single predecessor (its exit), so removing it cannot orphan another path.
    let mut absorbed_value_nodes: Vec<Node> = Vec::new();

    for (&header, info) in &headers {
        let header_label = ident_from_node(header);
        // Body iteration follows execution order: synthetic addresses (bit 62 set, e.g. arith_load fused Add) execute immediately after their base address, so naive numeric sort places them after every real-address node in the body and the synth Sset would emit at the bottom of the loop body, breaking the read-modify-write order of memory ops.
        let mut body_iter_nodes: Vec<Node> = info.body_nodes.iter().copied().collect();
        if !body_iter_nodes.contains(&header) {
            body_iter_nodes.push(header);
        }
        body_iter_nodes.sort_by_key(|&n| crate::util::exec_order_key(n));
        // Rotate so the HEADER is the first emitted element. Scontinue and the implicit fall-off-the-end loop-back both re-enter at the body's FIRST statement, so they mean "goto header" only when the header is that statement. gcc's rotated layouts place body code below the header address (the entry jumps forward to the condition/call cluster), which would otherwise leave the header mid-sequence and make every continue land on the wrong node. Dominance guarantees every external entry into the loop passes the header, so starting the emitted body there matches the real entry edge.
        if let Some(pos) = body_iter_nodes.iter().position(|&n| n == header) {
            body_iter_nodes.rotate_left(pos);
        }
        let body_node_set: HashSet<Node> = body_iter_nodes.iter().copied().collect();

        // Rotated loops (gcc -O0 `jmp .Lcond; .Lbody: ...; .Lcond: cmp; jg .Lbody`): the dominance header is the COND node, which execution order places LAST in the assembled body, so the latch edge emits as a goto to the exec-FIRST body node rather than to the header. A goto to the body's first statement is exactly `continue` for the while(1) we are building, so it converts like a header goto.
        let body_top_label: Option<Ident> = body_iter_nodes.first().map(|&n| ident_from_node(n));

        // Determine exit target: the node just after the loop.
        let exit_target_label: Option<Ident> = info.primary_exit.as_ref().map(|pe| {
            // Use the primary exit node; exact target resolved by goto matching below.
            ident_from_node(pe.exit_node)
        });

        // Collect goto targets within the body so we don't drop label-only Sskip nodes that another body stmt jumps to (e.g. cond's else branch targeting the body's first instruction). Dropping them re-creates the label outside the loop via ensure_goto_labels and leaks the body out via the goto.
        let mut body_goto_targets: HashSet<Ident> = HashSet::new();
        for &node in &body_iter_nodes {
            if let Some(stmt) = statements.get(&node) {
                for t in collect_goto_targets(stmt) {
                    body_goto_targets.insert(t as Ident);
                }
            }
        }

        let mut body_stmts: Vec<ClightStmt> = Vec::new();
        // Originating node of each body statement, index-aligned with body_stmts (the CF-4 guard resolves goto targets to body positions through it).
        let mut body_stmt_nodes: Vec<Node> = Vec::new();
        // A5 absorptions commit only if the loop itself commits (CF-4 guard below); pushing straight to absorbed_value_nodes would delete the value node even when the Sloop is skipped.
        let mut loop_absorbed: Vec<Node> = Vec::new();

        for &node in &body_iter_nodes {
            // Use pre-built break statement if this is a non-primary loop exit
            if let Some(break_stmt) = info.break_stmts.get(&node) {
                // A5: if this exit flows to a function return, tail-duplicate the value assignment + the return into the branch rather than emitting a valueless break, which drops the returned value at the post-loop join.
                if let Some(&(value_node, ret_node)) = info.exit_returns.get(&node) {
                    if let Some(tail) = build_return_tail(statements, value_node, ret_node) {
                        body_stmts.push(replace_break_with(break_stmt, &tail));
                        body_stmt_nodes.push(node);
                        loop_absorbed.push(value_node);
                        continue;
                    }
                }
                body_stmts.push(break_stmt.clone());
                body_stmt_nodes.push(node);
                continue;
            }

            let stmt = match statements.get(&node) {
                Some(s) => s.clone(),
                None => continue,
            };

            // Convert gotos: header_label->Scontinue, outside loop->Sbreak, recurse into branches.
            let converted = convert_loop_gotos(&stmt, header_label, body_top_label, &body_node_set, &exit_target_label);
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
                .map(|lbl| body_goto_targets.contains(&lbl))
                .unwrap_or(false);
            if !is_skip || target_within_body {
                if is_skip {
                    body_stmts.push(converted);
                } else {
                    // Strip one outer label so the body's natural fallthrough threads via the parent Ssequence - UNLESS a goto within this body targets the label: then it must stay on the statement, or ensure_goto_labels re-creates it as an empty top-level Sskip OUTSIDE the loop and every in-loop goto (switch case entries especially) jumps out to nothing, leaving the real body statements unreachable to be dropped downstream (the vanishing-case-body bug).
                    let stripped = match converted {
                        ClightStmt::Slabel(lbl, inner) if !body_goto_targets.contains(&lbl) => *inner,
                        other => other,
                    };
                    body_stmts.push(stripped);
                }
                body_stmt_nodes.push(node);
                // Upstream trimming deletes a body node's `jmp header` back-edge on the assumption that POSITION supplies the loop-back - true only for the exec-LAST body node. For any other node whose sole control successor is the header and whose statement can fall through, materialize the loop-back as Scontinue, or its execution would fall into the NEXT case body (fall-through corruption between reordered case bodies).
                if let Some(succs) = successors.get(&node) {
                    if succs.len() == 1
                        && succs[0] == header
                        && body_stmts.last().map(stmt_may_fall_through).unwrap_or(false)
                    {
                        body_stmts.push(ClightStmt::Scontinue);
                        body_stmt_nodes.push(node);
                    }
                }
            }
        }

        // Remove trailing Scontinue (redundant at end of loop body)
        while body_stmts.last() == Some(&ClightStmt::Scontinue) {
            body_stmts.pop();
            body_stmt_nodes.pop();
        }

        // CF-4 guard: a loop must be re-enterable. If the assembled body has no loop-level continue and no path can fall off its end, every path leaves on iteration 1 - the construct is not a loop (typically the dominance-filtered body excluded the shared hubs that carry the real cycle, CF-2). Wrapping it in while(1) lies about control flow and traps interior labels' back-edges as gotos (a goto cannot become `continue` through a foreign loop level - the quotearg case). Skip assembly and leave the nodes flat; the real cycle, if any, lives at an interior label.
        if !loop_body_can_reenter(
            &body_stmts,
            &body_stmt_nodes,
            &body_node_set,
            header,
            body_iter_nodes.first().copied(),
        ) {
            if std::env::var("CF4_TRACE").is_ok() {
                eprintln!("[cf4] skip header={:#x} label={} body={:#?}", header, header_label, body_stmts);
            }
            continue;
        }
        absorbed_value_nodes.extend(loop_absorbed);

        let body = match body_stmts.len() {
            0 => ClightStmt::Sskip,
            1 => body_stmts.into_iter().next().unwrap(),
            _ => ClightStmt::Ssequence(flatten_sequence(body_stmts)),
        };

        let loop_stmt = ClightStmt::Sloop(Box::new(body), Box::new(ClightStmt::Sskip));

        // Preserve label on the header node if present
        let final_stmt = match statements.get(&header) {
            Some(ClightStmt::Slabel(lbl, _)) => {
                ClightStmt::Slabel(*lbl, Box::new(loop_stmt))
            }
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

// Replace every Sbreak in a (pre-built break) statement with the given tail statement, turning `if(cond) break` into `if(cond) { value; return }` for an A5 exit that flows to a function return.
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
        ClightStmt::Slabel(_, inner) => 1 + clight_stmt_size(inner),
        ClightStmt::Sswitch(_, cases) => 1 + cases.iter().map(|(_, c)| clight_stmt_size(c)).sum::<usize>(),
        _ => 1,
    }
}

fn assemble_ite(
    statements: &mut HashMap<Node, ClightStmt>,
    ite_info: &HashMap<Node, IteInfo>,
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

    // Per-branch cap on assembled-compound size to bound 2^depth shared-node duplication. CF-9 (2026-06-10): 0 binds observed after CF-1 removed the dispatch duplication that caused the original 122-branch blowup; keep as backstop -- smallest-first ensures O(cap) construction even on degenerate inputs.
    let node_cap: usize = crate::decompile::elevator::config::ITE_MAX_NODES;

    for (&branch, info) in &branches {
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

        // A trailing `goto <join>` in an if-body is a redundant fallthrough ONLY when the join is the next top-level statement after the whole compound; since final emit is address-sorted, tail-merged code can place an if-body's value store at a HIGHER address than the merged join with an unconditional store interposed, so popping the goto makes the body fall through it and overwrite the value (A5 dead return-overwrite -> lookups return 0/NULL). Pop only when the join is the immediate top-level successor of the body span, else keep the goto early-exit (keeping a goto is always safe, at worst a redundant jump; dropping a needed one is the bug).
        let should_pop_join_goto = match info.join_node {
            Some(join) => {
                let body_span_max = info
                    .true_body_nodes
                    .iter()
                    .chain(info.false_body_nodes.iter())
                    .copied()
                    .max()
                    .map(|m| m.max(branch))
                    .unwrap_or(branch);
                statements.keys().filter(|n| **n > body_span_max).min().copied() == Some(join)
            }
            None => false,
        };

        // CF-1: a node shared by BOTH arms would be duplicated into each structured context, and the duplication compounds across nesting levels - one binary dispatch switch emitted dozens of times (119 copies observed in __strftime_internal). A switch-bearing shared node is therefore NOT embedded: it stays once at top level and each arm reaches it by goto; the compounding stops at the first switch-bearing level. Cheap shared nodes keep duplicating (that genuinely avoids gotos).
        let shared_preserved: HashSet<Node> = info
            .true_body_nodes
            .iter()
            .filter(|n| info.false_body_nodes.contains(n))
            .filter(|n| statements.get(n).map(stmt_contains_switch).unwrap_or(false))
            .copied()
            .collect();

        let collect_body = |body_nodes: &[Node]| -> ClightStmt {
            let mut body_stmts: Vec<ClightStmt> = Vec::new();
            for &node in body_nodes {
                if shared_preserved.contains(&node) {
                    body_stmts.push(ClightStmt::Sgoto(ident_from_node(node)));
                    continue;
                }
                if let Some(stmt) = statements.get(&node) {
                    // Strip outer label; the node identity is subsumed by the compound
                    let stripped = match stmt {
                        ClightStmt::Slabel(_, inner) => (**inner).clone(),
                        other => other.clone(),
                    };
                    if !matches!(&stripped, ClightStmt::Sskip) {
                        body_stmts.push(stripped);
                    }
                }
            }
            // Remove trailing gotos to the join point only when it is the textual fallthrough.
            if should_pop_join_goto {
                if let Some(join) = info.join_node {
                    let join_ident = ident_from_node(join);
                    while let Some(ClightStmt::Sgoto(target)) = body_stmts.last() {
                        if *target == join_ident {
                            body_stmts.pop();
                        } else {
                            break;
                        }
                    }
                }
            }
            match body_stmts.len() {
                0 => ClightStmt::Sskip,
                1 => body_stmts.into_iter().next().unwrap(),
                _ => ClightStmt::Ssequence(flatten_sequence(body_stmts)),
            }
        };

        let mut then_body = collect_body(&info.true_body_nodes);
        let mut else_body = collect_body(&info.false_body_nodes);

        // A branch side whose body was not inlined because its target is a (merging) shared landing pad (excluded from the if-body seeds in the structuring pass) must keep its original `goto target` rather than collapse to an empty Sskip that silently drops the control edge and loses the condition. Only restore the goto when the target is a real jump elsewhere (not the join point, where an empty side is a legitimate fallthrough). then_target/else_target are the flat Scond's `Sgoto(ident)` statements from clight_pass.
        let join_ident = info.join_node.map(ident_from_node);
        let goto_is_to_join = |g: &ClightStmt| matches!(g, ClightStmt::Sgoto(t) if Some(*t) == join_ident);
        if info.true_body_nodes.is_empty()
            && matches!(then_body, ClightStmt::Sskip)
            && matches!(then_target.as_ref(), ClightStmt::Sgoto(_))
            && !goto_is_to_join(then_target.as_ref())
        {
            then_body = (*then_target).clone();
        }
        if info.false_body_nodes.is_empty()
            && matches!(else_body, ClightStmt::Sskip)
            && matches!(else_target.as_ref(), ClightStmt::Sgoto(_))
            && !goto_is_to_join(else_target.as_ref())
        {
            else_body = (*else_target).clone();
        }

        let compound = ClightStmt::Sifthenelse(cond, Box::new(then_body), Box::new(else_body));

        // Duplicating a shared node into both arms is intentional (it avoids gotos), but on dense reconverging control flow that duplication compounds 2^depth across deeply nested branches and exhausts memory (362705: 122 branches, ~all body nodes shared by both sides -> a single compound reaching billions of nodes). Bound it: if one branch's assembled compound is absurdly large, leave that branch flat (its scond keeps its goto edges) rather than nest it. Real functions are orders of magnitude smaller, so this only trips on degenerate structuring; the skipped branch's body nodes stay top-level for the gotos.
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

        // Remove consumed body nodes from top-level (preserved shared switch-bearing nodes stay - the arms goto them)
        for &node in &info.true_body_nodes {
            if !shared_preserved.contains(&node) {
                statements.remove(&node);
            }
        }
        for &node in &info.false_body_nodes {
            if !shared_preserved.contains(&node) {
                statements.remove(&node);
            }
        }
    }
}

// Total Sswitch count in a statement tree (CF3_DUMP diagnostics).
fn count_switches(s: &ClightStmt) -> usize {
    match s {
        ClightStmt::Sswitch(_, cases) => {
            1 + cases.iter().map(|(_, cs)| count_switches(cs)).sum::<usize>()
        }
        ClightStmt::Ssequence(ss) => ss.iter().map(count_switches).sum(),
        ClightStmt::Sifthenelse(_, a, b) => count_switches(a) + count_switches(b),
        ClightStmt::Sloop(a, b) => count_switches(a) + count_switches(b),
        ClightStmt::Slabel(_, inner) => count_switches(inner),
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
        ClightStmt::Slabel(_, inner) => stmt_contains_switch(inner),
        _ => false,
    }
}

/// Convert gotos in a loop body: header-targeting becomes Scontinue, outside-loop becomes Sbreak, recursing into branches.
fn convert_loop_gotos(
    stmt: &ClightStmt,
    header_label: Ident,
    body_top_label: Option<Ident>,
    body_node_set: &HashSet<Node>,
    _exit_target_label: &Option<Ident>,
) -> ClightStmt {
    match stmt {
        ClightStmt::Sgoto(target) => {
            if *target == header_label || Some(*target) == body_top_label {
                ClightStmt::Scontinue
            } else {
                // Check if the target is outside the loop body
                let target_node = *target as Node;
                if !body_node_set.contains(&target_node) {
                    ClightStmt::Sbreak
                } else {
                    stmt.clone()
                }
            }
        }
        // Continue-conversion descends into switch cases: `continue` inside a switch binds to the enclosing LOOP (C semantics), so a case-body goto back to the loop header/body-top is exactly `continue`. Break conversion must NOT descend - Sbreak inside a case would bind to the SWITCH; a goto that leaves the loop from within a case stays a goto.
        ClightStmt::Sswitch(e, cases) => {
            let new_cases = cases
                .iter()
                .map(|(v, s)| (*v, convert_case_continues(s, header_label, body_top_label)))
                .collect();
            ClightStmt::Sswitch(e.clone(), new_cases)
        }
        ClightStmt::Sifthenelse(cond, then_box, else_box) => {
            let new_then = convert_loop_gotos(then_box, header_label, body_top_label, body_node_set, _exit_target_label);
            let new_else = convert_loop_gotos(else_box, header_label, body_top_label, body_node_set, _exit_target_label);
            ClightStmt::Sifthenelse(cond.clone(), Box::new(new_then), Box::new(new_else))
        }
        ClightStmt::Ssequence(stmts) => {
            let new_stmts: Vec<ClightStmt> = stmts
                .iter()
                .map(|s| convert_loop_gotos(s, header_label, body_top_label, body_node_set, _exit_target_label))
                .collect();
            ClightStmt::Ssequence(new_stmts)
        }
        ClightStmt::Slabel(lbl, inner) => {
            let new_inner = convert_loop_gotos(inner, header_label, body_top_label, body_node_set, _exit_target_label);
            ClightStmt::Slabel(*lbl, Box::new(new_inner))
        }
        _ => stmt.clone(),
    }
}

// CF-3: inline externalized switch case bodies. Lowering emits `case K: goto L_k` with the body as a separate labeled statement (often shared by several stacked case values); when EVERY goto to that label in the function comes from ONE switch's entries, the body belongs to that switch exclusively: its entries regroup into a contiguous C fall-through run (`case v1: case v2: <body>`) with the body inlined at the run's end and the label dropped. Only bodies that provably DIVERT (return / goto / continue on every path) are moved - a falling-through body at its original position continues into the next sibling statement, which inlining would change.
fn inline_switch_case_bodies(statements: &mut HashMap<Node, ClightStmt>) {
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
            ClightStmt::Ssequence(ss) => ss.iter().for_each(|x| scan_switches(x, entry_gotos, switch_count)),
            ClightStmt::Sifthenelse(_, a, b) => {
                scan_switches(a, entry_gotos, switch_count);
                scan_switches(b, entry_gotos, switch_count);
            }
            ClightStmt::Sloop(a, b) => {
                scan_switches(a, entry_gotos, switch_count);
                scan_switches(b, entry_gotos, switch_count);
            }
            ClightStmt::Slabel(_, inner) => scan_switches(inner, entry_gotos, switch_count),
            _ => {}
        }
    }
    for s in statements.values() {
        scan_switches(s, &mut entry_gotos, &mut switch_count);
    }
    let inlinable: HashSet<Ident> = entry_gotos
        .iter()
        .filter(|(t, &ec)| {
            total_gotos.get(t).copied().unwrap_or(0) == ec && switch_count.get(t).copied().unwrap_or(0) == 1
        })
        .map(|(&t, _)| t)
        .collect();
    if inlinable.is_empty() {
        return;
    }

    // Harvest inlinable top-level labeled bodies: the body must divert, its predecessor must divert (else falls into the label), and key must equal label (unclaimed restore uses `lbl as Node`). Bodies with loop-level Sbreak/Scontinue are excluded: Sbreak binds to the claiming switch, Scontinue binds to whatever loop encloses the claim site.
    let mut harvested: HashMap<Ident, ClightStmt> = HashMap::new();
    let mut top_keys: Vec<Node> = statements.keys().copied().collect();
    top_keys.sort_by_key(|&n| crate::util::exec_order_key(n));
    for (i, &k) in top_keys.iter().enumerate() {
        if let Some(ClightStmt::Slabel(lbl, inner)) = statements.get(&k) {
            if inlinable.contains(lbl)
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
        ClightStmt::Slabel(_, inner) => collect_claimable_entry_targets(inner, out),
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
            // Harvest inlinable diverting labeled siblings: predecessor must divert, single-label only, no escaping Sbreak (would rebind to the claiming switch). Scontinue-carrying bodies allowed only at zero Sloop crossings where binding is preserved. Each entry records (kept-position, harvest-seq) for exact positional restore if unclaimed.
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
                        kept.last().map(|p| !stmt_may_fall_through(p)).unwrap_or(false)
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
        ClightStmt::Slabel(l, inner) => {
            ClightStmt::Slabel(l, Box::new(rebuild_with_inlined_cases(*inner, inlinable, harvested)))
        }
        mut other => {
            let mut empty: HashMap<Ident, (usize, usize, ClightStmt)> = HashMap::new();
            inline_into_switches(&mut other, inlinable, &mut empty, harvested, 0);
            other
        }
    }
}

// Mutate every Sswitch within `stmt` (not crossing into nested sequences - those were handled by the recursion): regroup entries whose stmt is `goto t` for an owned target into a stacked fall-through run ending with the inlined body. `loop_crossings` counts Sloop boundaries descended since the pool's home sequence: a body containing loop-level Scontinue may only be claimed at zero crossings, where the continue still binds to the same loop it bound to at the body's original sibling position (a switch does not capture continue; an Sloop does).
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
                    if inlinable.contains(t) && !order.contains(t) && (local.contains_key(t) || harvested.contains_key(t)) {
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
                    && local.get(&t).is_some_and(|(_, _, b)| contains_loop_level_continue(b))
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
                    eprintln!("[cf3-inline] claim target={:#x} body={}", t, &bd[..bd.len().min(300)]);
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
        ClightStmt::Sgoto(target)
            if *target == header_label || Some(*target) == body_top_label =>
        {
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

// CF-4 (assemble_loops guard): whether an assembled loop body can start a second iteration - a loop-level Scontinue exists, or some execution path can fall off the end of the body (the implicit loop-back). Gotos are resolved against the NODE that produced each body statement (labels are not materialized yet at assembly time, so a goto's target node may carry no Slabel): a goto to an emitted in-body node makes that node's position a secondary entry point; a goto to an in-body node whose statement was absorbed cannot be positioned and conservatively reports re-enterable. Conservative toward `true`: only a provable no-reentry returns false (skipping the Sloop wrapper). Calls are treated as falling through (a body ending in a noreturn call still reports re-enterable; refining that needs ABI noreturn knowledge - ABI-2).
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
        ClightStmt::Slabel(_, inner) => contains_loop_level_continue(inner),
        ClightStmt::Sswitch(_, cases) => cases.iter().any(|(_, st)| contains_loop_level_continue(st)),
        ClightStmt::Sloop(..) => false,
        _ => false,
    }
}

// Sbreak that escapes the statement OUTWARD (not captured by a nested Sloop or Sswitch).
fn contains_escaping_break(s: &ClightStmt) -> bool {
    match s {
        ClightStmt::Sbreak => true,
        ClightStmt::Ssequence(ss) => ss.iter().any(contains_escaping_break),
        ClightStmt::Sifthenelse(_, t, e) => contains_escaping_break(t) || contains_escaping_break(e),
        ClightStmt::Slabel(_, inner) => contains_escaping_break(inner),
        ClightStmt::Sloop(..) | ClightStmt::Sswitch(..) => false,
        _ => false,
    }
}

// MAY execution fall off the end of this statement in straight-line position? Gotos divert at this level (cross-label resumption is handled by loop_body_can_reenter's entry-point enumeration). A nested loop only completes forward via a break of its own; a switch completes via an escaping break or its last case falling out.
fn stmt_may_fall_through(s: &ClightStmt) -> bool {
    match s {
        ClightStmt::Sreturn(_)
        | ClightStmt::Sgoto(_)
        | ClightStmt::Sbreak
        | ClightStmt::Scontinue => false,
        ClightStmt::Slabel(_, inner) => stmt_may_fall_through(inner),
        ClightStmt::Ssequence(ss) => ss.iter().all(stmt_may_fall_through),
        ClightStmt::Sifthenelse(_, t, e) => stmt_may_fall_through(t) || stmt_may_fall_through(e),
        ClightStmt::Sloop(b, _) => contains_escaping_break(b),
        ClightStmt::Sswitch(_, cases) => {
            cases.iter().any(|(_, st)| contains_escaping_break(st))
                || cases.last().map_or(true, |(_, st)| stmt_may_fall_through(st))
        }
        _ => true,
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
            let sanitized = crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(name);
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
        | ClightStmt::Sreturn(_)
        | ClightStmt::Sbreak
        | ClightStmt::Scontinue
        | ClightStmt::Sswitch(_, _) => true,
        ClightStmt::Slabel(_, inner) => is_control_flow_stmt(inner),
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
        ClightStmt::Slabel(_, inner) => is_value_stmt(inner),
        ClightStmt::Ssequence(stmts) => stmts.iter().any(is_value_stmt),
        _ => false,
    }
}

// Depth bound for goto-chain inlining: admits a splice only while (depth at goto) + (target's assembled tree depth) stays within this limit, preventing unbounded native-stack growth in recursive walks and the downstream printer. RB-2: the old FOLLOW counter didn't bound depth for backward chains -- each root spliced an already-expanded tree compounding linearly until stack overflow; charging the measured target depth closes that. 256 admits all observed real chains (~81 max); deeper chains keep one residual goto per cap window.
const MAX_GOTO_INLINE_DEPTH: usize = 256;

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
            ClightStmt::Slabel(_, inner) => work.push((inner.as_ref(), d + 1)),
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

fn deduplicate_identical_blocks(statements: &mut HashMap<Node, ClightStmt>) {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let mut content_hash: HashMap<u64, Vec<Node>> = HashMap::new();

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

        content_hash.entry(hash).or_default().push(node);
    }

    let mut redirect_map: HashMap<Node, Node> = HashMap::new();

    for (_hash, mut nodes) in content_hash {
        if nodes.len() <= 1 {
            continue;
        }

        nodes.sort();
        let canonical = nodes[0];
        let canonical_stmt = statements.get(&canonical);

        for &other in &nodes[1..] {
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
) {
    let preds = count_predecessors(successors);
    let mut inlined_nodes: HashSet<Node> = HashSet::new();
    let mut nodes_to_process: Vec<Node> = statements.keys().copied().collect();
    nodes_to_process.sort();

    // Lazily-filled assembled-tree depth per node; the splice gate charges the target's full depth so backward-ordered chains cannot compound past MAX_GOTO_INLINE_DEPTH.
    let mut depth_of: HashMap<Node, usize> = HashMap::new();

    for node in nodes_to_process {
        if let Some(stmt) = statements.get(&node).cloned() {
            let mut visiting = HashSet::new();
            visiting.insert(node);
            let (inlined, newly_inlined) =
                inline_stmt_recursive_track(&stmt, statements, &preds, &mut visiting, 0, &mut depth_of);
            // Free absorbed children immediately. Each inlined node has pred_count==1 (its only predecessor is the node we just inlined it into), so it is not referenced elsewhere and its content now lives inside `inlined`. Without this, every node's fully-inlined tree coexists in `statements` until the retain below; O(n^2) memory on long pred==1 chains, which OOMs large functions (e.g. 136803, stuck here at >11G).
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
    statements: &HashMap<Node, ClightStmt>,
    preds: &HashMap<Node, usize>,
    visiting: &mut HashSet<Node>,
    depth: usize,
    depth_of: &mut HashMap<Node, usize>,
) -> (ClightStmt, Vec<Node>) {
    let mut inlined = Vec::new();

    let result = match stmt {
        ClightStmt::Sifthenelse(cond, then_box, else_box) => {
            let (then_stmt, then_inlined) =
                inline_body_if_local_track(&**then_box, statements, preds, visiting, depth + 1, depth_of);
            let (else_stmt, else_inlined) =
                inline_body_if_local_track(&**else_box, statements, preds, visiting, depth + 1, depth_of);
            inlined.extend(then_inlined);
            inlined.extend(else_inlined);
            ClightStmt::Sifthenelse(cond.clone(), Box::new(then_stmt), Box::new(else_stmt))
        }
        ClightStmt::Sloop(body_box, incr_box) => {
            let (body_stmt, body_inlined) =
                inline_body_if_local_track(&**body_box, statements, preds, visiting, depth + 1, depth_of);
            let (incr_stmt, incr_inlined) =
                inline_body_if_local_track(&**incr_box, statements, preds, visiting, depth + 1, depth_of);
            inlined.extend(body_inlined);
            inlined.extend(incr_inlined);
            ClightStmt::Sloop(Box::new(body_stmt), Box::new(incr_stmt))
        }
        ClightStmt::Ssequence(stmts) => {
            let mut result_stmts = Vec::new();
            for s in stmts {
                let (inlined_s, s_inlined) =
                    inline_stmt_recursive_track(s, statements, preds, visiting, depth + 1, depth_of);
                result_stmts.push(inlined_s);
                inlined.extend(s_inlined);
            }
            ClightStmt::Ssequence(flatten_sequence(result_stmts))
        }
        ClightStmt::Slabel(lbl, inner) => {
            let (inner_inlined, inner_nodes) =
                inline_stmt_recursive_track(&**inner, statements, preds, visiting, depth + 1, depth_of);
            inlined.extend(inner_nodes);
            ClightStmt::Slabel(*lbl, Box::new(inner_inlined))
        }
        ClightStmt::Sswitch(expr, cases) => {
            let mut new_cases = Vec::new();
            for (label, case_stmt) in cases {
                let (inlined_case, case_inlined) =
                    inline_body_if_local_track(case_stmt, statements, preds, visiting, depth + 1, depth_of);
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
    statements: &HashMap<Node, ClightStmt>,
    preds: &HashMap<Node, usize>,
    visiting: &mut HashSet<Node>,
    depth: usize,
    depth_of: &mut HashMap<Node, usize>,
) -> (ClightStmt, Vec<Node>) {
    match stmt {
        ClightStmt::Sgoto(target_ident) => {
            let target_node = *target_ident as u64;
            let pred_count = preds.get(&target_node).copied().unwrap_or(0);

            if pred_count == 1 && !visiting.contains(&target_node) {
                if let Some(target_stmt) = statements.get(&target_node) {
                    if is_trivial_labeled_goto(target_stmt) {
                        return (stmt.clone(), vec![]);
                    }
                    // Admit only if (depth + target's already-expanded tree depth) stays within MAX_GOTO_INLINE_DEPTH; keeping the goto is always safe.
                    let target_depth = *depth_of
                        .entry(target_node)
                        .or_insert_with(|| stmt_depth(target_stmt));
                    if depth > 300 && std::env::var("RB2_TRACE").is_ok() {
                        eprintln!("[rb2] RUNAWAY depth={} target={:x} tdepth={}", depth, target_node, target_depth);
                    }
                    if depth + target_depth <= MAX_GOTO_INLINE_DEPTH {
                        visiting.insert(target_node);
                        let (recursed_stmt, mut recursed_nodes) = inline_stmt_recursive_track(
                            target_stmt, statements, preds, visiting, depth + 1, depth_of,
                        );
                        recursed_nodes.push(target_node);
                        return (recursed_stmt, recursed_nodes);
                    }
                }
            }

            (stmt.clone(), vec![])
        }
        _ => inline_stmt_recursive_track(stmt, statements, preds, visiting, depth, depth_of),
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
        ClightStmt::Slabel(_, inner) => {
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
        ClightStmt::Slabel(lbl, inner) => {
            *lbl == target_label || stmt_contains_label(inner, target_label)
        }
        ClightStmt::Sifthenelse(_, then_stmt, else_stmt) => {
            stmt_contains_label(then_stmt, target_label)
                || stmt_contains_label(else_stmt, target_label)
        }
        ClightStmt::Sloop(body, incr) => {
            stmt_contains_label(body, target_label)
                || stmt_contains_label(incr, target_label)
        }
        ClightStmt::Ssequence(stmts) => {
            stmts.iter().any(|s| stmt_contains_label(s, target_label))
        }
        ClightStmt::Sswitch(_, cases) => {
            cases.iter().any(|(_, s)| stmt_contains_label(s, target_label))
        }
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
        let already_nested = statements.values().any(|s| stmt_contains_label(s, label_ident));
        if already_nested {
            continue;
        }

        let node = label_ident as Node;
        if let Some(stmt) = statements.get(&node) {
            let wrapped = ClightStmt::Slabel(label_ident, Box::new(stmt.clone()));
            statements.insert(node, wrapped);
        } else {
            statements.insert(node, ClightStmt::Slabel(label_ident, Box::new(ClightStmt::Sskip)));
        }
    }
}
