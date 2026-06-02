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

/// Precomputed metadata about refinable nodes in a function.
struct RefinableMetadata {
    refinable_set: BTreeSet<Node>,
    decl_node_to_reg: BTreeMap<Node, RTLReg>,
    param_node_to_pos: BTreeMap<Node, usize>,
}

// Program-level (whole-program) selection types

/// Program-level selection state covering all functions, keyed by (func_addr, node/reg).
#[derive(Clone, Debug)]
struct ProgramSelectionState {
    /// (func_addr, node) -> candidate index
    candidate_idx: HashMap<(Address, Node), Option<usize>>,
    /// (func_addr, reg) -> type candidate index
    var_decl_idx: HashMap<(Address, RTLReg), usize>,
    /// Global struct field type selections (shared across functions)
    struct_field_type_idx: HashMap<(String, String), usize>,
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
                candidates.sort_by_key(|s| {
                    // Lower key sorts first. Field-form gets 0, raw-deref form gets 1.
                    let prefers_field = stmt_uses_efield(s);
                    let priority: u8 = if prefers_field { 0 } else { 1 };
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

    // Build global struct fields map from all functions' emit_struct_fields
    let mut global_struct_fields: HashMap<i64, Vec<(i64, Ident, MemoryChunk)>> = HashMap::new();
    for func in &functions {
        for (base_key, fields) in &func.struct_fields {
            global_struct_fields.entry(*base_key).or_insert_with(|| fields.clone());
        }
    }

    // Build canonical struct ID -> register-based base_key; sort per-func and sort Vec values so find_map is stable across runs.
    let mut global_canonical_to_reg_key: HashMap<i64, Vec<i64>> = HashMap::new();
    for func in &functions {
        let mut sorted_pairs: Vec<(RTLReg, usize)> =
            func.reg_struct_ids.iter().map(|(&r, &s)| (r, s)).collect();
        sorted_pairs.sort();
        for (reg, sid) in sorted_pairs {
            let reg_key = reg as i64;
            let canonical_key = sid as i64;
            global_canonical_to_reg_key.entry(canonical_key).or_default().push(reg_key);
        }
    }
    for v in global_canonical_to_reg_key.values_mut() {
        v.sort();
        v.dedup();
    }

    if clang_sys::load().is_err() {
        panic!("libclang not found; install libclang-dev or set LIBCLANG_PATH");
    }

    let best_state = function_based_parallel_search(
        &functions, &global_struct_fields, &global_canonical_to_reg_key,
        &name_to_ident,
    );

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
            let mut li: Vec<String> = f.loop_info.iter().map(|(n, v)| format!("{}:{:?}", n, v)).collect();
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

    let per_func_state = SelectionState { candidate_idx };

    // Materialize and post-process
    let mut statements = materialize_statements(&per_func_state, func);
    det_fp_stage(func.address, "S1mat", &statements);

    let func_loop_info = loop_info_all.get(&func.address).cloned().unwrap_or_default();

    assemble_loops(&mut statements, &func_loop_info);
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
        var_type_candidates: func.var_type_candidates.clone(),
        var_decl_idx,
        loop_headers: func.loop_headers.clone(),
        switch_heads: func.switch_heads.clone(),
        reg_struct_ids: func.reg_struct_ids.clone(),
        loop_info: func_loop_info,
    }
}


#[derive(Debug)]
struct ClangError {
    line: usize,
    column: usize,
    message: String,
}

/// Extract the register ID from a `var_<digits>` token at or before `column` on the given source line.
fn extract_reg_at_column(source: &str, line: usize, column: usize) -> Option<RTLReg> {
    let line_text = source.lines().nth(line.saturating_sub(1))?;
    let col_idx = column.saturating_sub(1).min(line_text.len());
    let bytes = line_text.as_bytes();
    let is_ident_byte = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut start = col_idx;
    while start > 0 && is_ident_byte(bytes[start - 1]) {
        start -= 1;
    }
    let mut end = col_idx;
    while end < bytes.len() && is_ident_byte(bytes[end]) {
        end += 1;
    }
    if start >= end { return None; }
    let token = &line_text[start..end];
    let rest = token.strip_prefix("var_")?;
    rest.parse::<RTLReg>().ok()
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

/// Determine from a clang error whether a variable should be pointer (Some(true)), integer (Some(false)), or unrelated (None).
fn error_wants_ptr(msg: &str) -> Option<bool> {
    // Strong signals: declaration should match the expression type.
    if msg.contains("pointer to integer conversion") {
        return Some(true);
    }
    if msg.contains("integer to pointer conversion") {
        return Some(false);
    }
    if msg.contains("indirection requires pointer") {
        return Some(true);
    }
    if msg.contains("subscripted value is not an array, pointer, or vector") {
        return Some(true);
    }
    if msg.contains("makes pointer from integer without a cast") {
        return Some(true);
    }
    if msg.contains("makes integer from pointer without a cast") {
        return Some(false);
    }
    if msg.contains("comparison between pointer and integer") {
        // Ambiguous direction; prefer pointer (the more specific commitment usually came from clang).
        return Some(true);
    }
    if msg.contains("incompatible pointer types") {
        return Some(true);
    }
    if msg.contains("member reference base type") && msg.contains("is not a structure or union") {
        return Some(true);
    }
    if msg.contains("arithmetic on a pointer to void") {
        return Some(false);
    }
    None
}

/// Find the type candidate index matching the desired ptr/int direction for a decl/param node.
fn find_directed_type_idx(
    reg: RTLReg,
    want_ptr: bool,
    current_idx: usize,
    func: &FunctionData,
) -> Option<usize> {
    let candidates = func.var_type_candidates.get(&reg)?;
    for (i, type_str) in candidates.iter().enumerate() {
        if i == current_idx { continue; }
        let is_ptr = type_str.starts_with("ptr_");
        if is_ptr == want_ptr {
            return Some(i);
        }
    }
    None
}

fn build_program_initial_state(functions: &[FunctionData]) -> ProgramSelectionState {
    let mut candidate_idx = HashMap::new();
    let mut var_decl_idx = HashMap::new();
    let mut struct_field_type_idx = HashMap::new();

    for func in functions {
        let addr = func.address;
        for (node, _candidates) in &func.node_statements {
            candidate_idx.insert((addr, *node), Some(0));
        }
        for (reg, idx) in &func.var_decl_idx {
            var_decl_idx.insert((addr, *reg), *idx);
        }
        for (key, idx) in &func.struct_field_type_idx {
            struct_field_type_idx.entry(key.clone()).or_insert(*idx);
        }
    }

    ProgramSelectionState { candidate_idx, var_decl_idx, struct_field_type_idx }
}

/// Per-function selection state for hybrid search.
#[derive(Clone, Debug)]
struct HybridFunctionState {
    candidate_idx: BTreeMap<Node, Option<usize>>,
    var_decl_idx: BTreeMap<RTLReg, usize>,
    struct_field_type_idx: BTreeMap<(String, String), usize>,
}

fn build_hybrid_initial_state(func: &FunctionData) -> HybridFunctionState {
    let mut candidate_idx = BTreeMap::new();
    for (node, _candidates) in &func.node_statements {
        candidate_idx.insert(*node, Some(0));
    }
    HybridFunctionState {
        candidate_idx,
        var_decl_idx: func.var_decl_idx.iter().map(|(k, v)| (*k, *v)).collect(),
        struct_field_type_idx: func.struct_field_type_idx.iter().map(|(k, v)| (k.clone(), *v)).collect(),
    }
}

fn build_hybrid_refinable_metadata(func: &FunctionData) -> RefinableMetadata {
    let param_reg_set: HashSet<RTLReg> = func.param_regs.iter().copied().collect();
    let mut refinable_set = BTreeSet::new();
    let mut decl_node_to_reg = BTreeMap::new();
    let mut param_node_to_pos = BTreeMap::new();

    for (node, cands) in &func.node_statements {
        if cands.len() > 1 {
            refinable_set.insert(*node);
        }
    }
    for reg in func.var_type_candidates.keys() {
        if !param_reg_set.contains(reg) {
            let node = DECL_NODE_BASE.wrapping_add(*reg);
            refinable_set.insert(node);
            decl_node_to_reg.insert(node, *reg);
        }
    }
    for (pos, reg) in func.param_regs.iter().enumerate() {
        if func.var_type_candidates.contains_key(reg) {
            let node = PARAM_NODE_BASE.wrapping_add(pos as u64);
            refinable_set.insert(node);
            param_node_to_pos.insert(node, pos);
        }
    }
    RefinableMetadata { refinable_set, decl_node_to_reg, param_node_to_pos }
}

/// Scan a ClightExpr for Ederef operand registers; needs_struct_ptr=true when deref is inside an Efield.
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

fn scan_pure_int_regs_stmt(stmt: &ClightStmt, out: &mut BTreeSet<RTLReg>) {
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

fn scan_deref_regs_stmt(stmt: &ClightStmt) -> Vec<(RTLReg, bool)> {
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

/// Pre-search constraint propagation: force pointer types for registers that all candidates agree must be dereferenced.
fn propagate_type_constraints(
    state: &mut HybridFunctionState,
    func: &FunctionData,
    _meta: &RefinableMetadata,
) {
    // Per register, track whether every candidate that mentions it derefs it: reg -> (all_deref, any_non_deref, needs_struct_ptr).
    let mut reg_deref_info: BTreeMap<RTLReg, (bool, bool, Option<usize>)> = BTreeMap::new();

    // Sorted iteration: deterministic entry.2 update when a reg spans nodes with different sids.
    let mut sorted_nodes: Vec<Node> = func.node_statements.keys().copied().collect();
    sorted_nodes.sort();
    for node in &sorted_nodes {
        let candidates = &func.node_statements[node];
        // Collect deref regs across ALL candidates for this node
        let mut regs_in_any_candidate: BTreeSet<RTLReg> = BTreeSet::new();
        let mut regs_derefed_in_all: Option<BTreeSet<RTLReg>> = None;
        let mut struct_ptr_regs: BTreeMap<RTLReg, usize> = BTreeMap::new();

        for stmt in candidates {
            let deref_regs: BTreeSet<RTLReg> = scan_deref_regs_stmt(stmt)
                .into_iter()
                .map(|(reg, needs_struct)| {
                    if needs_struct {
                        if let Some(&sid) = func.reg_struct_ids.get(&reg) {
                            struct_ptr_regs.insert(reg, sid);
                        }
                    }
                    reg
                })
                .collect();

            // Collect all regs mentioned in any deref across any candidate
            regs_in_any_candidate.extend(&deref_regs);

            // Intersect to find regs derefed in ALL candidates
            regs_derefed_in_all = Some(match regs_derefed_in_all {
                None => deref_regs,
                Some(prev) => prev.intersection(&deref_regs).copied().collect(),
            });
        }

        // Only mark a register as needing pointer if it's derefed in ALL candidates
        if let Some(universal_deref_regs) = regs_derefed_in_all {
            for reg in &universal_deref_regs {
                let entry = reg_deref_info.entry(*reg).or_insert((true, false, None));
                // Still universally derefed across all nodes so far
                if let Some(&sid) = struct_ptr_regs.get(reg) {
                    entry.2 = Some(sid);
                }
            }
            // Regs derefed in some but not all candidates: mark as ambiguous
            for reg in regs_in_any_candidate.difference(&universal_deref_regs) {
                let entry = reg_deref_info.entry(*reg).or_insert((true, false, None));
                entry.1 = true; // has a non-deref path
            }
        }
    }

    // Only force pointer for registers that are universally derefed and never ambiguous
    let reg_needs_ptr: BTreeSet<RTLReg> = reg_deref_info.iter()
        .filter(|(_, (all_deref, any_non_deref, _))| *all_deref && !*any_non_deref)
        .map(|(reg, _)| *reg)
        .collect();
    let reg_needs_struct_ptr: BTreeMap<RTLReg, usize> = reg_deref_info.iter()
        .filter(|(_, (all_deref, any_non_deref, sid))| *all_deref && !*any_non_deref && sid.is_some())
        .map(|(reg, (_, _, sid))| (*reg, sid.unwrap()))
        .collect();

    // Force pointer types for registers that need them
    for reg in &reg_needs_ptr {
        if let Some(candidates) = func.var_type_candidates.get(reg) {
            let current_idx = state.var_decl_idx.get(reg).copied().unwrap_or(0);
            let current_is_ptr = candidates.get(current_idx)
                .map(|s| s.starts_with("ptr_"))
                .unwrap_or(false);
            if current_is_ptr { continue; }

            // Find a struct pointer candidate first if needed
            if let Some(&sid) = reg_needs_struct_ptr.get(reg) {
                let target = format!("ptr_struct_{:x}", sid);
                if let Some(idx) = candidates.iter().position(|s| *s == target) {
                    state.var_decl_idx.insert(*reg, idx);
                    continue;
                }
            }
            // Otherwise find any pointer candidate
            if let Some(idx) = candidates.iter().position(|s| s.starts_with("ptr_")) {
                state.var_decl_idx.insert(*reg, idx);
            }
        }
    }

    // Inverse: a reg used by mul/div/mod/and/or/xor/shl/shr (in any candidate) that is never deref'd and has no struct must be int (those ops are ill-typed on pointers).
    let mut pure_int_regs: BTreeSet<RTLReg> = BTreeSet::new();
    for node in &sorted_nodes {
        for stmt in &func.node_statements[node] {
            scan_pure_int_regs_stmt(stmt, &mut pure_int_regs);
        }
    }
    let any_deref_regs: BTreeSet<RTLReg> = reg_deref_info.keys().copied().collect();
    for reg in &pure_int_regs {
        if any_deref_regs.contains(reg) { continue; }
        if func.reg_struct_ids.contains_key(reg) { continue; }
        if let Some(candidates) = func.var_type_candidates.get(reg) {
            let current_idx = state.var_decl_idx.get(reg).copied().unwrap_or(0);
            let current_is_ptr = candidates.get(current_idx)
                .map(|s| s.starts_with("ptr_"))
                .unwrap_or(false);
            if !current_is_ptr { continue; }
            // Prefer int_I64 then int_I32 then any non-ptr non-float candidate.
            let preferred = ["int_I64", "int_I32", "int_I64_unsigned", "int_I32_unsigned"];
            let chosen = preferred.iter()
                .find_map(|p| candidates.iter().position(|s| s == *p))
                .or_else(|| candidates.iter().position(|s|
                    !s.starts_with("ptr_") && !s.starts_with("float_")));
            if let Some(idx) = chosen {
                state.var_decl_idx.insert(*reg, idx);
            }
        }
    }
}

/// Deterministic hash of a single ClightStmt for candidate sorting.
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

/// Deterministic hash of a HybridFunctionState for beam tie-breaking.
fn state_deterministic_hash(state: &HybridFunctionState) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    // BTreeMap iterates in sorted order, so hash is deterministic
    for (node, idx) in &state.candidate_idx {
        node.hash(&mut hasher);
        idx.hash(&mut hasher);
    }
    for (reg, idx) in &state.var_decl_idx {
        reg.hash(&mut hasher);
        idx.hash(&mut hasher);
    }
    for (key, idx) in &state.struct_field_type_idx {
        key.hash(&mut hasher);
        idx.hash(&mut hasher);
    }
    hasher.finish()
}

fn build_hybrid_alternatives(
    node: Node, state: &HybridFunctionState, func: &FunctionData, meta: &RefinableMetadata,
) -> Vec<Option<usize>> {
    let mut alts = Vec::new();
    if node >= STRUCT_FIELD_NODE_BASE { return alts; }
    if let Some(&pos) = meta.param_node_to_pos.get(&node) {
        let reg = func.param_regs[pos];
        if let Some(candidates) = func.var_type_candidates.get(&reg) {
            let current = state.var_decl_idx.get(&reg).copied().unwrap_or(0);
            for i in 0..candidates.len() { if i != current { alts.push(Some(i)); } }
        }
        return alts;
    }
    if let Some(&reg) = meta.decl_node_to_reg.get(&node) {
        if let Some(candidates) = func.var_type_candidates.get(&reg) {
            let current = state.var_decl_idx.get(&reg).copied().unwrap_or(0);
            for i in 0..candidates.len() { if i != current { alts.push(Some(i)); } }
        }
        return alts;
    }
    if let Some(candidates) = func.node_statements.get(&node) {
        let current = state.candidate_idx.get(&node).copied().flatten();
        for i in 0..candidates.len() { if Some(i) != current { alts.push(Some(i)); } }
        if current.is_some() { alts.push(None); }
    }
    alts
}

fn apply_hybrid_choice(
    state: &mut HybridFunctionState, node: Node, value: Option<usize>,
    func: &FunctionData, meta: &RefinableMetadata,
) {
    if let Some(&pos) = meta.param_node_to_pos.get(&node) {
        let reg = func.param_regs[pos];
        if let Some(idx) = value { state.var_decl_idx.insert(reg, idx); }
    } else if let Some(&reg) = meta.decl_node_to_reg.get(&node) {
        if let Some(idx) = value { state.var_decl_idx.insert(reg, idx); }
    } else {
        state.candidate_idx.insert(node, value);
    }
}

/// Merge a per-function search result into the program-level state.
fn merge_hybrid_into_program_state(
    program_state: &mut ProgramSelectionState,
    func_addr: Address,
    hybrid: &HybridFunctionState,
) {
    for (node, idx) in &hybrid.candidate_idx {
        program_state.candidate_idx.insert((func_addr, *node), *idx);
    }
    for (reg, idx) in &hybrid.var_decl_idx {
        program_state.var_decl_idx.insert((func_addr, *reg), *idx);
    }
    for (key, idx) in &hybrid.struct_field_type_idx {
        program_state.struct_field_type_idx.insert(key.clone(), *idx);
    }
}

fn function_based_parallel_search(
    functions: &[FunctionData],
    global_struct_fields: &HashMap<i64, Vec<(i64, Ident, MemoryChunk)>>,
    global_canonical_to_reg_key: &HashMap<i64, Vec<i64>>,
    name_to_ident: &HashMap<String, Ident>,
) -> ProgramSelectionState {
    // Profiling on ls (step_budget=64): 1534 clang calls / 3331 cache hits across 285 functions; 63% remain unresolved when search ends, and the top 10% of functions consume 16-64 calls each (the long tail dominating wall time). Lowered default to 16: p90 of "calls per function" was already 16, so the median and 90th percentile are untouched; the change cuts the long tail that wasn't converging anyway.
    let step_budget: usize = std::env::var("CLIGHT_SELECT_STEPS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(16);

    let max_per_node: usize = std::env::var("CLIGHT_SELECT_PER_NODE")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(2);

    let mut funcs_to_search: Vec<usize> = functions.iter().enumerate()
        .filter(|(_, func)| {
            func.node_statements.values().any(|c| c.len() > 1)
                || !func.var_type_candidates.is_empty()
        })
        .map(|(i, _)| i)
        .collect();
    funcs_to_search.sort_by_key(|&i| functions[i].address);

    let raw: Vec<Option<(Address, HybridFunctionState, CegarSearchStats)>> = funcs_to_search
        .par_iter()
        .map(|&func_idx| {
            let _ = clang_sys::load();
            let func = &functions[func_idx];

            let meta = build_hybrid_refinable_metadata(func);
            if meta.refinable_set.is_empty() {
                return None;
            }

            let (state, stats) = function_standalone_search(
                func, &meta,
                global_struct_fields, global_canonical_to_reg_key,
                name_to_ident,
                step_budget, max_per_node,
            );

            Some((func.address, state, stats))
        })
        .collect();

    let mut results: Vec<(Address, HybridFunctionState)> = Vec::with_capacity(raw.len());
    let mut all_stats: Vec<(Address, CegarSearchStats)> = Vec::with_capacity(raw.len());
    for entry in raw.into_iter().flatten() {
        let (addr, state, stats) = entry;
        results.push((addr, state));
        all_stats.push((addr, stats));
    }
    results.sort_by_key(|(addr, _)| *addr);
    all_stats.sort_by_key(|(addr, _)| *addr);

    if std::env::var("CLIGHT_SELECT_STATS").is_ok() {
        let mut calls: Vec<usize> = all_stats.iter().map(|(_, s)| s.clang_calls).collect();
        let mut hits: Vec<usize> = all_stats.iter().map(|(_, s)| s.cache_hits).collect();
        let mut steps: Vec<usize> = all_stats.iter().map(|(_, s)| s.steps_used).collect();
        let funcs_n = calls.len();
        let total_calls: usize = calls.iter().sum();
        let total_hits: usize = hits.iter().sum();
        let total_steps: usize = steps.iter().sum();
        let unresolved: usize = all_stats.iter().filter(|(_, s)| s.final_errors > 0).count();
        let maxed_out: usize = all_stats.iter().filter(|(_, s)| s.max_outer_iters_reached).count();
        calls.sort();
        hits.sort();
        steps.sort();
        let pct = |v: &[usize], p: f64| -> usize {
            if v.is_empty() { 0 } else {
                let idx = ((v.len() as f64 - 1.0) * p).round() as usize;
                v[idx.min(v.len() - 1)]
            }
        };
        eprintln!(
            "[cegar-stats] funcs={} total_clang_calls={} total_cache_hits={} total_steps={} unresolved={} max_iters_reached={}",
            funcs_n, total_calls, total_hits, total_steps, unresolved, maxed_out
        );
        eprintln!(
            "[cegar-stats] calls/func: min={} p50={} p75={} p90={} p95={} p99={} max={}",
            pct(&calls, 0.0), pct(&calls, 0.5), pct(&calls, 0.75),
            pct(&calls, 0.90), pct(&calls, 0.95), pct(&calls, 0.99),
            pct(&calls, 1.0)
        );
        eprintln!(
            "[cegar-stats] cache_hits/func: min={} p50={} p90={} max={}",
            pct(&hits, 0.0), pct(&hits, 0.5), pct(&hits, 0.90), pct(&hits, 1.0)
        );
        eprintln!(
            "[cegar-stats] steps/func: min={} p50={} p90={} max={}",
            pct(&steps, 0.0), pct(&steps, 0.5), pct(&steps, 0.90), pct(&steps, 1.0)
        );
    }

    let mut program_state = build_program_initial_state(functions);
    for (addr, hybrid) in &results {
        merge_hybrid_into_program_state(&mut program_state, *addr, hybrid);
    }

    program_state
}

/// Standalone per-function search: emits this function in isolation and validates with clang.
#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct CegarSearchStats {
    pub clang_calls: usize,
    pub cache_hits: usize,
    pub final_errors: usize,
    pub max_outer_iters_reached: bool,
    pub steps_used: usize,
}

fn function_standalone_search(
    func: &FunctionData,
    meta: &RefinableMetadata,
    global_struct_fields: &HashMap<i64, Vec<(i64, Ident, MemoryChunk)>>,
    global_canonical_to_reg_key: &HashMap<i64, Vec<i64>>,
    name_to_ident: &HashMap<String, Ident>,
    step_budget: usize,
    max_per_node: usize,
) -> (HybridFunctionState, CegarSearchStats) {
    let mut state = build_hybrid_initial_state(func);
    let mut func_view = func.clone();

    // Constraint propagation: force logically required types before any clang call
    propagate_type_constraints(&mut state, func, meta);

    let clang_calls = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let cache_hits = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));

    // Cache evaluation results keyed by the hash of the emitted C code. The CEGAR search re-evaluates many near-identical states (bisection over fix subsets, beam search ties), and changes to state fields that do not affect this function's emitted code produce identical c_code and identical clang outputs -- so the cache avoids the ~30ms libclang invocation for any state that emits a C string we have already checked. Per-function cache; freed when the search returns. Wrapped in Arc<Mutex> because Wave 2 and beam search call `evaluate` from `par_iter`, so the cache must be shared safely across rayon workers.
    let clang_cache: std::sync::Arc<
        std::sync::Mutex<HashMap<u64, (usize, Vec<Node>, HashMap<Node, Vec<String>>)>>,
    > = std::sync::Arc::new(std::sync::Mutex::new(HashMap::new()));

    // Evaluate: emit single function -> clang, return (error_count, sorted_error_nodes, node_errors)
    let evaluate = |state: &HybridFunctionState, func_view: &mut FunctionData|
        -> (usize, Vec<Node>, HashMap<Node, Vec<String>>) {
        // Apply state to view
        for (reg, idx_ref) in func_view.var_decl_idx.iter_mut() {
            if let Some(&idx) = state.var_decl_idx.get(reg) {
                *idx_ref = idx;
            }
        }
        for (key, idx_ref) in func_view.struct_field_type_idx.iter_mut() {
            if let Some(&idx) = state.struct_field_type_idx.get(key) {
                *idx_ref = idx;
            }
        }
        // Materialize statements
        let mut stmts = HashMap::new();
        for (node, candidates) in &func.node_statements {
            if let Some(idx) = state.candidate_idx.get(node).copied().flatten() {
                if let Some(stmt) = candidates.get(idx).or_else(|| candidates.last()) {
                    stmts.insert(*node, stmt.clone());
                }
            }
        }
        let (c_code, line_map) = emit_function_c(func_view, &stmts, global_struct_fields, global_canonical_to_reg_key, name_to_ident);

        let cache_key = {
            use std::collections::hash_map::DefaultHasher;
            use std::hash::{Hash, Hasher};
            let mut h = DefaultHasher::new();
            c_code.hash(&mut h);
            h.finish()
        };
        if let Some(cached) = clang_cache.lock().unwrap().get(&cache_key) {
            cache_hits.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            return cached.clone();
        }

        clang_calls.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let errors = run_clang_check(&c_code);
        if errors.is_empty() {
            let result = (0usize, Vec::new(), HashMap::new());
            clang_cache.lock().unwrap().insert(cache_key, result.clone());
            return result;
        }
        // Map errors to nodes
        let mut error_nodes = Vec::new();
        let mut seen = HashSet::new();
        let mut node_errors: HashMap<Node, Vec<String>> = HashMap::new();
        for error in &errors {
            if let Some(&node) = line_map.get(&error.line) {
                node_errors.entry(node).or_default().push(error.message.clone());
                let is_refinable = meta.refinable_set.contains(&node) || node >= STRUCT_FIELD_NODE_BASE;
                if is_refinable && seen.insert(node) {
                    error_nodes.push(node);
                } else if !is_refinable {
                    // Prefer the register identified by the error column.
                    let preferred = extract_reg_at_column(&c_code, error.line, error.column);
                    let stmt_regs: Vec<RTLReg> = stmts.get(&node)
                        .map(|s| crate::decompile::passes::clight_select::query::collect_stmt_regs(s))
                        .unwrap_or_default();
                    let target_regs: Vec<RTLReg> = match preferred {
                        Some(r) if stmt_regs.contains(&r) => vec![r],
                        Some(r) => vec![r],
                        None => stmt_regs,
                    };
                    for reg in &target_regs {
                        if let Some(pos) = func.param_regs.iter().position(|r| r == reg) {
                            let pn = PARAM_NODE_BASE.wrapping_add(pos as u64);
                            if meta.param_node_to_pos.contains_key(&pn) && seen.insert(pn) {
                                node_errors.entry(pn).or_default().push(error.message.clone());
                                error_nodes.push(pn);
                            }
                        }
                        let dn = DECL_NODE_BASE.wrapping_add(*reg);
                        if meta.decl_node_to_reg.contains_key(&dn) && seen.insert(dn) {
                            node_errors.entry(dn).or_default().push(error.message.clone());
                            error_nodes.push(dn);
                        }
                    }
                }
            }
        }
        // Sort for deterministic processing order
        error_nodes.sort();
        let result = (errors.len(), error_nodes, node_errors);
        clang_cache.lock().unwrap().insert(cache_key, result.clone());
        result
    };

    let (mut current_errors, mut error_nodes, mut node_errors) = evaluate(&state, &mut func_view);
    let mut steps = 0usize;
    let wave12_budget = step_budget * 3 / 4;
    let max_outer_iters: usize = 4;
    let mut iter = 0usize;

    let make_stats = |steps: usize, errors: usize, iter: usize| CegarSearchStats {
        clang_calls: clang_calls.load(std::sync::atomic::Ordering::Relaxed),
        cache_hits: cache_hits.load(std::sync::atomic::Ordering::Relaxed),
        final_errors: errors,
        max_outer_iters_reached: iter >= max_outer_iters,
        steps_used: steps,
    };

    if current_errors == 0 { return (state, make_stats(steps, current_errors, iter)); }

    // Outer iteration: re-run Wave 1 + Wave 2 while errors strictly decrease.
    while iter < max_outer_iters && current_errors > 0 && steps < wave12_budget {
        iter += 1;
        let pre_iter_errors = current_errors;

        // Wave 1: collect directed fixes (deterministically by sorted error_nodes), then try the full batch. If errors regress, bisect to extract the helpful subset.
        let mut fix_pairs: Vec<(RTLReg, usize)> = Vec::new();
        let mut seen_regs: HashSet<RTLReg> = HashSet::new();
        for &node in &error_nodes {
            let directed = node_errors.get(&node).and_then(|msgs| {
                for msg in msgs {
                    let want_ptr = error_wants_ptr(msg)?;
                    let reg = if let Some(&pos) = meta.param_node_to_pos.get(&node) {
                        Some(func.param_regs[pos])
                    } else if let Some(&r) = meta.decl_node_to_reg.get(&node) {
                        Some(r)
                    } else { None };
                    if let Some(reg) = reg {
                        let current = state.var_decl_idx.get(&reg).copied().unwrap_or(0);
                        if let Some(new_idx) = find_directed_type_idx(reg, want_ptr, current, func) {
                            return Some((reg, new_idx));
                        }
                    }
                }
                None
            });
            if let Some((reg, new_idx)) = directed {
                if seen_regs.insert(reg) {
                    fix_pairs.push((reg, new_idx));
                }
            }
        }

        // Bisection: try a slice, and if it does not improve, recursively split; each evaluate() call costs 1 step. Returns the best (errors, state, en, ne) found.
        fn bisect_apply(
            base: &HybridFunctionState,
            base_errors: usize,
            base_en: &[Node],
            base_ne: &HashMap<Node, Vec<String>>,
            fixes: &[(RTLReg, usize)],
            steps: &mut usize,
            budget: usize,
            evaluate: &mut dyn FnMut(&HybridFunctionState) -> (usize, Vec<Node>, HashMap<Node, Vec<String>>),
        ) -> (HybridFunctionState, usize, Vec<Node>, HashMap<Node, Vec<String>>) {
            if fixes.is_empty() || *steps >= budget {
                return (base.clone(), base_errors, base_en.to_vec(), base_ne.clone());
            }
            let mut trial = base.clone();
            for (reg, idx) in fixes {
                trial.var_decl_idx.insert(*reg, *idx);
            }
            *steps += 1;
            let (e, en, ne) = evaluate(&trial);
            // Strict decrease only (matches Wave 2 / outer-loop progress check); committing ties would let the outer loop mistake a tie for progress and never converge.
            if e < base_errors {
                return (trial, e, en, ne);
            }
            if fixes.len() == 1 {
                return (base.clone(), base_errors, base_en.to_vec(), base_ne.clone());
            }
            let mid = fixes.len() / 2;
            let (s1, e1, en1, ne1) = bisect_apply(base, base_errors, base_en, base_ne, &fixes[..mid], steps, budget, evaluate);
            bisect_apply(&s1, e1, &en1, &ne1, &fixes[mid..], steps, budget, evaluate)
        }

        if !fix_pairs.is_empty() && steps < wave12_budget {
            // bisect_apply needs an FnMut over a closure that captures func_view.
            let mut eval_fn = |s: &HybridFunctionState| evaluate(s, &mut func_view);
            let (new_state, new_err, new_en, new_ne) = bisect_apply(
                &state, current_errors, &error_nodes, &node_errors,
                &fix_pairs, &mut steps, wave12_budget, &mut eval_fn,
            );
            state = new_state;
            current_errors = new_err;
            error_nodes = new_en;
            node_errors = new_ne;
            if current_errors == 0 { return (state, make_stats(steps, current_errors, iter)); }
        }

        // Wave 2: per error-node, try alternatives in parallel; keep strict best.
        let sorted_errors: Vec<Node> = error_nodes.clone();
        for node in &sorted_errors {
            if steps >= wave12_budget { break; }

            let alts = build_hybrid_alternatives(*node, &state, func, meta);
            if alts.is_empty() { continue; }

            let cap_per_node = if max_per_node == 0 { alts.len() } else { max_per_node };
            let budget_here = (wave12_budget - steps).min(alts.len()).min(cap_per_node);
            if budget_here == 0 { break; }
            steps += budget_here;

            type TrialResult = (usize, HybridFunctionState, usize, Vec<Node>, HashMap<Node, Vec<String>>);
            let results: Vec<TrialResult> = alts[..budget_here].par_iter().enumerate()
                .map(|(i, &alt)| {
                    let _ = clang_sys::load();
                    let mut trial = state.clone();
                    apply_hybrid_choice(&mut trial, *node, alt, func, meta);
                    let mut fv = func.clone();
                    let (e, en, ne) = evaluate(&trial, &mut fv);
                    (i, trial, e, en, ne)
                })
                .collect();

            if let Some((_, new_state, new_err, new_en, new_ne)) = results.into_iter()
                .min_by(|a, b| a.2.cmp(&b.2).then(a.0.cmp(&b.0)))
            {
                if new_err < current_errors {
                    state = new_state;
                    current_errors = new_err;
                    error_nodes = new_en;
                    node_errors = new_ne;
                    if current_errors == 0 { return (state, make_stats(steps, current_errors, iter)); }
                }
            }
        }

        if current_errors >= pre_iter_errors {
            break;
        }
    }

    let beam_width_cap: usize = std::env::var("CLIGHT_SELECT_BEAM_WIDTH")
        .ok().and_then(|v| v.parse().ok()).unwrap_or(8);
    // Scale beam width with the remaining error count: more errors -> wider beam, bounded by cap. Floor of 3 preserves prior behavior.
    let beam_width: usize = (current_errors / 2).max(3).min(beam_width_cap);
    if steps < step_budget && current_errors > 0 {
        let remaining_errors: Vec<Node> = error_nodes.iter()
            .filter(|n| !build_hybrid_alternatives(**n, &state, func, meta).is_empty())
            .copied()
            .collect();

        if !remaining_errors.is_empty() {
            let mut beam: Vec<(HybridFunctionState, usize, Vec<Node>, HashMap<Node, Vec<String>>)> =
                vec![(state.clone(), current_errors, error_nodes.clone(), node_errors.clone())];

            for &node in &remaining_errors {
                if steps >= step_budget { break; }

                let mut next_beam: Vec<(HybridFunctionState, usize, Vec<Node>, HashMap<Node, Vec<String>>)> =
                    beam.iter()
                        .map(|(s, e, en, ne)| (s.clone(), *e, en.clone(), ne.clone()))
                        .collect();

                let mut trial_specs: Vec<(usize, Option<usize>)> = Vec::new();
                for (b, (beam_state, _, _, _)) in beam.iter().enumerate() {
                    let alts = build_hybrid_alternatives(node, beam_state, func, meta);
                    for alt in &alts {
                        trial_specs.push((b, *alt));
                    }
                }
                let cap = step_budget - steps;
                let trial_len = trial_specs.len().min(cap);
                let trial_specs = &trial_specs[..trial_len];
                steps += trial_len;

                let trials: Vec<(HybridFunctionState, usize, Vec<Node>, HashMap<Node, Vec<String>>)> =
                    trial_specs.par_iter().map(|&(b, alt)| {
                        let _ = clang_sys::load();
                        let (beam_state, _, _, _) = &beam[b];
                        let mut trial = beam_state.clone();
                        apply_hybrid_choice(&mut trial, node, alt, func, meta);
                        let mut fv = func.clone();
                        let (e, en, ne) = evaluate(&trial, &mut fv);
                        (trial, e, en, ne)
                    }).collect();

                next_beam.extend(trials);

                next_beam.sort_by(|a, b| {
                    a.1.cmp(&b.1)
                        .then_with(|| state_deterministic_hash(&a.0).cmp(&state_deterministic_hash(&b.0)))
                });
                next_beam.truncate(beam_width);
                next_beam.dedup_by(|a, b| state_deterministic_hash(&a.0) == state_deterministic_hash(&b.0));
                beam = next_beam;

                if beam.first().map_or(false, |b| b.1 == 0) { break; }
            }

            // Take the best from the beam
            if let Some((best, best_err, _, _)) = beam.into_iter().next() {
                if best_err <= current_errors {
                    state = best;
                    current_errors = best_err;
                }
            }
        }
    }

    if current_errors > 0 {
        log::warn!(
            "clight_select: function 0x{:x} emitted with {} clang errors remaining after {} steps (budget {})",
            func.address, current_errors, steps, step_budget
        );
    }

    let stats = make_stats(steps, current_errors, iter);
    (state, stats)
}

fn assemble_loops(
    statements: &mut HashMap<Node, ClightStmt>,
    loop_info: &HashMap<Node, LoopInfo>,
) {
    // Process smallest loops first (inner before outer). Break ties by header address.
    let mut headers: Vec<(&Node, &LoopInfo)> = loop_info.iter().collect();
    headers.sort_by(|a, b| a.1.body_nodes.len().cmp(&b.1.body_nodes.len()).then(a.0.cmp(b.0)));

    for (&header, info) in &headers {
        let header_label = ident_from_node(header);
        // Body iteration follows execution order: synthetic addresses (bit 62 set, e.g. arith_load fused Add) execute immediately after their base address, so naive numeric sort places them after every real-address node in the body and the synth Sset would emit at the bottom of the loop body, breaking the read-modify-write order of memory ops.
        let mut body_iter_nodes: Vec<Node> = info.body_nodes.iter().copied().collect();
        if !body_iter_nodes.contains(&header) {
            body_iter_nodes.push(header);
        }
        body_iter_nodes.sort_by_key(|&n| crate::util::exec_order_key(n));
        let body_node_set: HashSet<Node> = body_iter_nodes.iter().copied().collect();

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

        for &node in &body_iter_nodes {
            // Use pre-built break statement if this is a non-primary loop exit
            if let Some(break_stmt) = info.break_stmts.get(&node) {
                body_stmts.push(break_stmt.clone());
                continue;
            }

            let stmt = match statements.get(&node) {
                Some(s) => s.clone(),
                None => continue,
            };

            // Convert gotos: header_label->Scontinue, outside loop->Sbreak, recurse into branches.
            let converted = convert_loop_gotos(&stmt, header_label, &body_node_set, &exit_target_label);
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
                    // Strip one outer label so the body's natural fallthrough threads via the parent Ssequence; downstream label-restoration adds it back when a goto actually targets it.
                    let stripped = match converted {
                        ClightStmt::Slabel(_, inner) => *inner,
                        other => other,
                    };
                    body_stmts.push(stripped);
                }
            }
        }

        // Remove trailing Scontinue (redundant at end of loop body)
        while body_stmts.last() == Some(&ClightStmt::Scontinue) {
            body_stmts.pop();
        }

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
}

// Assemble compound if-then-else from structural metadata (analogous to assemble_loops); operates on already-typed ClightStmt so no type decisions are made.
// Count ClightStmt tree nodes; bounds assemble_ite against pathological overlapping if-bodies.
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

    // Per-branch ceiling on assembled-compound size; bounds the 2^depth shared-node duplication
    // blowup on degenerate control flow. Far above any real function's nesting, so it only trips
    // on pathological structuring (configurable via ITE_MAX_NODES).
    let node_cap: usize = std::env::var("ITE_MAX_NODES").ok().and_then(|v| v.parse().ok()).unwrap_or(1_000_000);

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

        let collect_body = |body_nodes: &[Node]| -> ClightStmt {
            let mut body_stmts: Vec<ClightStmt> = Vec::new();
            for &node in body_nodes {
                if let Some(stmt) = statements.get(&node) {
                    // Strip outer label -- the node identity is subsumed by the compound
                    let stripped = match stmt {
                        ClightStmt::Slabel(_, inner) => (**inner).clone(),
                        other => other.clone(),
                    };
                    if !matches!(&stripped, ClightStmt::Sskip) {
                        body_stmts.push(stripped);
                    }
                }
            }
            // Remove trailing gotos to the join point (they become fallthrough)
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
            match body_stmts.len() {
                0 => ClightStmt::Sskip,
                1 => body_stmts.into_iter().next().unwrap(),
                _ => ClightStmt::Ssequence(flatten_sequence(body_stmts)),
            }
        };

        let mut then_body = collect_body(&info.true_body_nodes);
        let mut else_body = collect_body(&info.false_body_nodes);

        // A branch side whose body was not inlined because its target is a (merging) shared landing pad -- excluded from the if-body seeds in the structuring pass -- must keep its original `goto target` rather than collapse to an empty Sskip that silently drops the control edge and loses the condition. Only restore the goto when the target is a real jump elsewhere (not the join point, where an empty side is a legitimate fallthrough). then_target/else_target are the flat Scond's `Sgoto(ident)` statements from clight_pass.
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

        // Duplicating a shared node into both arms is intentional (it avoids gotos), but on dense
        // reconverging control flow that duplication compounds 2^depth across deeply nested
        // branches and exhausts memory (362705: 122 branches, ~all body nodes shared by both sides
        // -> a single compound reaching billions of nodes). Bound it: if one branch's assembled
        // compound is absurdly large, leave that branch flat (its scond keeps its goto edges)
        // rather than nest it. Real functions are orders of magnitude smaller, so this only trips
        // on degenerate structuring; the skipped branch's body nodes stay top-level for the gotos.
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

        // Remove consumed body nodes from top-level
        for &node in &info.true_body_nodes {
            statements.remove(&node);
        }
        for &node in &info.false_body_nodes {
            statements.remove(&node);
        }
    }
}

/// Convert gotos in a loop body: header-targeting becomes Scontinue, outside-loop becomes Sbreak, recursing into branches.
fn convert_loop_gotos(
    stmt: &ClightStmt,
    header_label: Ident,
    body_node_set: &HashSet<Node>,
    _exit_target_label: &Option<Ident>,
) -> ClightStmt {
    match stmt {
        ClightStmt::Sgoto(target) => {
            if *target == header_label {
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
        ClightStmt::Sifthenelse(cond, then_box, else_box) => {
            let new_then = convert_loop_gotos(then_box, header_label, body_node_set, _exit_target_label);
            let new_else = convert_loop_gotos(else_box, header_label, body_node_set, _exit_target_label);
            ClightStmt::Sifthenelse(cond.clone(), Box::new(new_then), Box::new(new_else))
        }
        ClightStmt::Ssequence(stmts) => {
            let new_stmts: Vec<ClightStmt> = stmts
                .iter()
                .map(|s| convert_loop_gotos(s, header_label, body_node_set, _exit_target_label))
                .collect();
            ClightStmt::Ssequence(new_stmts)
        }
        ClightStmt::Slabel(lbl, inner) => {
            let new_inner = convert_loop_gotos(inner, header_label, body_node_set, _exit_target_label);
            ClightStmt::Slabel(*lbl, Box::new(new_inner))
        }
        _ => stmt.clone(),
    }
}


/// Convert an xtype string (e.g. "ptr_int", "int_I64") to a ClightType.
fn xtype_str_to_clight_type(s: &str) -> ClightType {
    let attr = ClightAttr::default();
    if s.starts_with("ptr_") {
        // All pointer types -> Tpointer(Tlong) as a generic 64-bit pointer
        ClightType::Tpointer(std::sync::Arc::new(
            ClightType::Tlong(ClightSignedness::Signed, attr.clone())),
            attr,
        )
    } else if s == "int_I32" || s == "int_U32" || s == "int_I32_unsigned" {
        ClightType::Tint(ClightIntSize::I32, ClightSignedness::Signed, attr)
    } else {
        ClightType::Tlong(ClightSignedness::Signed, attr)
    }
}

fn xtype_to_clight_type(xt: &XType) -> ClightType {
    let attr = ClightAttr::default();
    match xt {
        XType::Xvoid => ClightType::Tvoid,
        XType::Xbool => ClightType::Tint(ClightIntSize::IBool, ClightSignedness::Signed, attr),
        XType::Xint8signed => ClightType::Tint(ClightIntSize::I8, ClightSignedness::Signed, attr),
        XType::Xint8unsigned => ClightType::Tint(ClightIntSize::I8, ClightSignedness::Unsigned, attr),
        XType::Xint16signed => ClightType::Tint(ClightIntSize::I16, ClightSignedness::Signed, attr),
        XType::Xint16unsigned => ClightType::Tint(ClightIntSize::I16, ClightSignedness::Unsigned, attr),
        XType::Xint | XType::Xany32 => ClightType::Tint(ClightIntSize::I32, ClightSignedness::Signed, attr),
        XType::Xintunsigned => ClightType::Tint(ClightIntSize::I32, ClightSignedness::Unsigned, attr),
        XType::Xlong | XType::Xany64 => ClightType::Tlong(ClightSignedness::Signed, attr),
        XType::Xlongunsigned => ClightType::Tlong(ClightSignedness::Unsigned, attr),
        XType::Xfloat => ClightType::Tfloat(ClightFloatSize::F64, attr),
        XType::Xsingle => ClightType::Tfloat(ClightFloatSize::F32, attr),
        XType::Xptr => ClightType::Tpointer(
            std::sync::Arc::new(ClightType::Tlong(ClightSignedness::Signed, attr.clone())),
            attr,
        ),
        XType::Xcharptr => ClightType::Tpointer(
            std::sync::Arc::new(ClightType::Tint(ClightIntSize::I8, ClightSignedness::Signed, attr.clone())),
            attr,
        ),
        XType::Xcharptrptr => ClightType::Tpointer(
            std::sync::Arc::new(ClightType::Tpointer(
                std::sync::Arc::new(ClightType::Tint(ClightIntSize::I8, ClightSignedness::Signed, attr.clone())),
                attr.clone(),
            )),
            attr,
        ),
        XType::Xintptr => ClightType::Tpointer(
            std::sync::Arc::new(ClightType::Tint(ClightIntSize::I32, ClightSignedness::Signed, attr.clone())),
            attr,
        ),
        XType::Xfloatptr => ClightType::Tpointer(
            std::sync::Arc::new(ClightType::Tfloat(ClightFloatSize::F64, attr.clone())),
            attr,
        ),
        XType::Xsingleptr => ClightType::Tpointer(
            std::sync::Arc::new(ClightType::Tfloat(ClightFloatSize::F32, attr.clone())),
            attr,
        ),
        XType::Xfuncptr => ClightType::Tpointer(
            std::sync::Arc::new(ClightType::Tlong(ClightSignedness::Signed, attr.clone())),
            attr,
        ),
        XType::XstructPtr(sid) => ClightType::Tpointer(
            std::sync::Arc::new(ClightType::Tstruct(*sid, attr.clone())),
            attr,
        ),
    }
}

fn callee_ident_from_expr(
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

/// Add explicit casts to fix ptr/int type mismatches in a ClightStmt (values are correct on x86-64, only C types differ).
fn fixup_ptr_int_casts(
    stmt: &ClightStmt,
    var_decl_type: &dyn Fn(Ident) -> Option<ClightType>,
    callee_param_types: &dyn Fn(&ClightExpr) -> Option<Vec<ClightType>>,
) -> ClightStmt {
    fn fixup_expr(expr: &ClightExpr) -> ClightExpr {
        match expr {
            // Ederef(addr, ty): cast addr to long* if non-pointer so the deref produces long.
            ClightExpr::Ederef(inner, ty) => {
                let fixed_inner = fixup_expr(inner);
                let inner_ty = clight_expr_type(&fixed_inner);
                if !matches!(inner_ty, ClightType::Tpointer(..)) {
                    let long_ty = ClightType::Tlong(ClightSignedness::Signed, ClightAttr::default());
                    let ptr_long = ClightType::Tpointer(
                        std::sync::Arc::new(long_ty.clone()),
                        ClightAttr::default(),
                    );
                    ClightExpr::Ederef(
                        Box::new(ClightExpr::Ecast(Box::new(fixed_inner), ptr_long)),
                        long_ty,
                    )
                } else {
                    ClightExpr::Ederef(Box::new(fixed_inner), ty.clone())
                }
            }
            // Recurse into sub-expressions
            ClightExpr::Eunop(op, inner, ty) =>
                ClightExpr::Eunop(*op, Box::new(fixup_expr(inner)), ty.clone()),
            ClightExpr::Ebinop(op, l, r, ty) =>
                ClightExpr::Ebinop(*op, Box::new(fixup_expr(l)), Box::new(fixup_expr(r)), ty.clone()),
            ClightExpr::Ecast(inner, ty) =>
                ClightExpr::Ecast(Box::new(fixup_expr(inner)), ty.clone()),
            ClightExpr::Eaddrof(inner, ty) =>
                ClightExpr::Eaddrof(Box::new(fixup_expr(inner)), ty.clone()),
            ClightExpr::Efield(inner, id, ty) =>
                ClightExpr::Efield(Box::new(fixup_expr(inner)), *id, ty.clone()),
            ClightExpr::Econdition(c, t, f, ty) =>
                ClightExpr::Econdition(Box::new(fixup_expr(c)), Box::new(fixup_expr(t)), Box::new(fixup_expr(f)), ty.clone()),
            // Leaves: no recursion needed
            _ => expr.clone(),
        }
    }

    match stmt {
        ClightStmt::Sassign(lhs, rhs) => {
            ClightStmt::Sassign(fixup_expr(lhs), fixup_expr(rhs))
        }
        ClightStmt::Sset(id, expr) => {
            let fixed = fixup_expr(expr);
            // Cast RHS to match the variable's declared type if ptr/int mismatch
            let rhs = if let Some(decl_ty) = var_decl_type(*id) {
                let rhs_ty = clight_expr_type(&fixed);
                let rhs_is_ptr = matches!(rhs_ty, ClightType::Tpointer(..));
                let decl_is_ptr = matches!(decl_ty, ClightType::Tpointer(..));
                if rhs_is_ptr != decl_is_ptr {
                    ClightExpr::Ecast(Box::new(fixed), decl_ty)
                } else {
                    fixed
                }
            } else {
                fixed
            };
            ClightStmt::Sset(*id, rhs)
        }
        ClightStmt::Scall(ret, func, args) => {
            let fixed_func = fixup_expr(func);
            let param_types = callee_param_types(&fixed_func);
            let fixed_args: Vec<ClightExpr> = args.iter().enumerate().map(|(i, a)| {
                let fixed_a = fixup_expr(a);
                if let Some(ref pts) = param_types {
                    if let Some(target_ty) = pts.get(i) {
                        let arg_ty = clight_expr_type(&fixed_a);
                        let arg_is_ptr = matches!(arg_ty, ClightType::Tpointer(..));
                        let target_is_ptr = matches!(target_ty, ClightType::Tpointer(..));
                        if arg_is_ptr != target_is_ptr {
                            return ClightExpr::Ecast(Box::new(fixed_a), target_ty.clone());
                        }
                    }
                }
                fixed_a
            }).collect();
            ClightStmt::Scall(*ret, fixed_func, fixed_args)
        }
        ClightStmt::Sbuiltin(ret, ef, tys, args) => {
            ClightStmt::Sbuiltin(*ret, ef.clone(), tys.clone(), args.iter().map(|a| fixup_expr(a)).collect())
        }
        ClightStmt::Sifthenelse(cond, t, f) => {
            ClightStmt::Sifthenelse(fixup_expr(cond), Box::new(fixup_ptr_int_casts(t, var_decl_type, callee_param_types)), Box::new(fixup_ptr_int_casts(f, var_decl_type, callee_param_types)))
        }
        ClightStmt::Ssequence(stmts) => {
            ClightStmt::Ssequence(stmts.iter().map(|s| fixup_ptr_int_casts(s, var_decl_type, callee_param_types)).collect())
        }
        ClightStmt::Sloop(a, b) => {
            ClightStmt::Sloop(Box::new(fixup_ptr_int_casts(a, var_decl_type, callee_param_types)), Box::new(fixup_ptr_int_casts(b, var_decl_type, callee_param_types)))
        }
        ClightStmt::Sswitch(expr, cases) => {
            ClightStmt::Sswitch(fixup_expr(expr), cases.iter().map(|(v, s)| (*v, fixup_ptr_int_casts(s, var_decl_type, callee_param_types))).collect())
        }
        ClightStmt::Sreturn(Some(expr)) => {
            ClightStmt::Sreturn(Some(fixup_expr(expr)))
        }
        ClightStmt::Slabel(id, inner) => {
            ClightStmt::Slabel(*id, Box::new(fixup_ptr_int_casts(inner, var_decl_type, callee_param_types)))
        }
        _ => stmt.clone(),
    }
}

/// Emit a standalone C source for `func` with a line-number-to-node mapping for clang validation.
#[allow(dead_code)]
fn emit_function_c(
    func: &FunctionData,
    statements: &HashMap<Node, ClightStmt>,
    global_struct_fields: &HashMap<i64, Vec<(i64, Ident, MemoryChunk)>>,
    global_canonical_to_reg_key: &HashMap<i64, Vec<i64>>,
    name_to_ident: &HashMap<String, Ident>,
) -> (String, HashMap<usize, Node>) {
    use crate::decompile::passes::c_pass::types::{CExpr, CStmt, CType, TypeQualifiers};

    let mut out = String::new();
    let mut line_map: HashMap<usize, Node> = HashMap::new();

    let mut ctx = ConversionContext::new(HashMap::new());
    let mut all_cstmts: Vec<(Node, CStmt)> = Vec::new();
    {
        // Build lookup: variable ident -> current declared ClightType
        let var_decl_type = |ident: Ident| -> Option<ClightType> {
            let reg = ident as RTLReg;
            if let Some(candidates) = func.var_type_candidates.get(&reg) {
                let idx = func.var_decl_idx.get(&reg).copied().unwrap_or(0);
                let type_str = candidates.get(idx)
                    .or_else(|| func.var_types.get(&reg))
                    .map(|s| s.as_str())
                    .unwrap_or("int_I64");
                Some(xtype_str_to_clight_type(type_str))
            } else if let Some(type_str) = func.var_types.get(&reg) {
                Some(xtype_str_to_clight_type(type_str))
            } else if func.reg_struct_ids.contains_key(&reg) {
                let sid = func.reg_struct_ids[&reg];
                let attr = ClightAttr::default();
                Some(ClightType::Tpointer(
                    std::sync::Arc::new(ClightType::Tstruct(sid, attr.clone())),
                    attr,
                ))
            } else {
                None
            }
        };

        let callee_param_types = |f: &ClightExpr| -> Option<Vec<ClightType>> {
            let id = callee_ident_from_expr(f, name_to_ident)?;
            let sig = func.callee_signatures.get(&id)?;
            Some(sig.param_types.iter().map(xtype_to_clight_type).collect())
        };

        let mut sorted_nodes: Vec<Node> = statements.keys().copied().collect();
        sorted_nodes.sort();
        for node in &sorted_nodes {
            let clight_stmt = &statements[node];
            let fixed = fixup_ptr_int_casts(clight_stmt, &var_decl_type, &callee_param_types);
            let cstmt = convert_stmt(&fixed, &mut ctx);
            all_cstmts.push((*node, cstmt));
        }
    }

    let mut all_var_refs: HashSet<String> = HashSet::new();
    let mut all_func_calls: HashSet<String> = HashSet::new();
    for (_, cstmt) in &all_cstmts {
        collect_cstmt_names(cstmt, &mut all_var_refs, &mut all_func_calls);
    }

    out.push_str("#include <stddef.h>\n");
    out.push_str("#include <stdint.h>\n");

    let mut field_usage_types: HashMap<(String, String), Vec<String>> = HashMap::new();
    {
        let mut sorted_stmt_nodes: Vec<Node> = statements.keys().copied().collect();
        sorted_stmt_nodes.sort();
        for node in &sorted_stmt_nodes {
            let clight_stmt = &statements[node];
            collect_field_usage_types(clight_stmt, &mut field_usage_types);
        }
    }

    let mut struct_names: HashSet<String> = HashSet::new();
    let mut sorted_reg_sids: Vec<(&RTLReg, &usize)> = func.reg_struct_ids.iter().collect();
    sorted_reg_sids.sort_by_key(|(reg, _)| **reg);
    for (_reg, sid) in sorted_reg_sids {
        struct_names.insert(format!("struct_{:x}", sid));
    }
    for var_type in ctx.var_types.values() {
        collect_struct_names_from_ctype(var_type, &mut struct_names);
    }
    for type_str in func.var_types.values() {
        if type_str.starts_with("ptr_struct_") {
            struct_names.insert(format!("struct_{}", &type_str["ptr_struct_".len()..]));
        }
    }
    for type_strs in func.var_type_candidates.values() {
        for type_str in type_strs {
            if type_str.starts_with("ptr_struct_") {
                struct_names.insert(format!("struct_{}", &type_str["ptr_struct_".len()..]));
            }
        }
    }

    let mut sorted_struct_names: Vec<&String> = struct_names.iter().collect();
    sorted_struct_names.sort();
    for name in &sorted_struct_names {
        let struct_id_str = name.strip_prefix("struct_").unwrap_or("");
        let struct_id = i64::from_str_radix(struct_id_str, 16).ok();

        let fields = struct_id.and_then(|sid| {
            // Direct lookup by canonical struct ID
            func.struct_fields.get(&sid)
                .or_else(|| func.struct_fields.get(&(-sid)))
                .or_else(|| global_struct_fields.get(&sid))
                .or_else(|| global_struct_fields.get(&(-sid)))
                // Bridge ID spaces: canonical struct ID -> register-based base_key
                .or_else(|| {
                    global_canonical_to_reg_key.get(&sid)
                        .and_then(|reg_keys| reg_keys.iter().find_map(|rk|
                            func.struct_fields.get(rk).or_else(|| global_struct_fields.get(rk))
                        ))
                })
                .or_else(|| {
                    global_canonical_to_reg_key.get(&(-sid))
                        .and_then(|reg_keys| reg_keys.iter().find_map(|rk|
                            func.struct_fields.get(rk).or_else(|| global_struct_fields.get(rk))
                        ))
                })
        });

        if let Some(field_list) = fields {
            let mut sorted_fields = field_list.clone();
            sorted_fields.sort_by_key(|(off, _, _)| *off);
            out.push_str(&format!("struct {} {{\n", name));
            for (_offset, field_ident, chunk) in &sorted_fields {
                let field_name = crate::decompile::passes::csh_pass::field_ident_to_name(*field_ident);
                let key = (name.to_string(), field_name.clone());

                // Pick field type from struct_field_type_idx or default to chunk type.
                let field_type_str = if let Some(candidates) = func.struct_field_type_candidates.get(&key) {
                    let idx = func.struct_field_type_idx.get(&key).copied().unwrap_or(0);
                    candidates.get(idx).map(|s| s.as_str()).unwrap_or_else(|| chunk_to_c_type_str(chunk))
                } else if let Some(candidates) = field_usage_types.get(&key) {
                    // First time: build candidates from chunk + usage types
                    candidates.first().map(|s| s.as_str()).unwrap_or_else(|| chunk_to_c_type_str(chunk))
                } else {
                    chunk_to_c_type_str(chunk)
                };

                // Map this field line to a synthetic node for clang_refine
                let current_line = out.lines().count() + 1;
                let struct_hex = name.strip_prefix("struct_").unwrap_or("0");
                let struct_hash: u64 = u64::from_str_radix(struct_hex, 16).unwrap_or(0) & 0x0000_FFFF_FFFF_FFFF;
                let field_node = STRUCT_FIELD_NODE_BASE
                    .wrapping_add(struct_hash << 16)
                    .wrapping_add(*_offset as u64);
                line_map.insert(current_line, field_node);

                out.push_str(&format!("    {} {};\n", field_type_str, field_name));
            }
            out.push_str("};\n");
        } else {
            out.push_str(&format!("struct {};\n", name));
        }
    }

    // Forward-declare called functions.
    all_func_calls.remove(&func.name);
    let mut sorted_funcs: Vec<&String> = all_func_calls.iter().collect();
    sorted_funcs.sort();
    for name in sorted_funcs {
        let sig = lookup_callee_signature(name, &func.callee_signatures, name_to_ident);
        out.push_str(&forward_decl_for(name, sig));
    }

    out.push('\n');

    // Function signature.
    let ret_type = convert_clight_return_type(&func.return_type);
    out.push_str(&ret_type);
    out.push(' ');
    out.push_str(&func.name);
    out.push('(');

    let mut param_names: HashSet<String> = HashSet::new();
    if func.param_regs.is_empty() {
        out.push_str("void");
    } else {
        out.push('\n');
        for (i, (reg, pty)) in func.param_regs.iter().zip(func.param_types.iter()).enumerate() {
            if i > 0 {
                out.push_str(",\n");
            }
            // Choose param type from var_type_candidates if available, else fall back to param_types.
            let ty = if let Some(candidates) = func.var_type_candidates.get(reg) {
                let idx = func.var_decl_idx.get(reg).copied().unwrap_or(0);
                let type_str = candidates.get(idx)
                    .or_else(|| func.var_types.get(reg))
                    .map(|s| s.as_str())
                    .unwrap_or("int_I64");
                xtype_string_to_ctype(type_str)
            } else {
                convert_param_type_from_param(pty)
            };
            let name = param_name_for_reg(*reg);
            let ty_str = ctype_to_c_string(&ty);
            // Map this param line to a synthetic node for clang_refine
            let current_line = out.lines().count() + 1;
            line_map.insert(current_line, PARAM_NODE_BASE.wrapping_add(i as u64));
            out.push_str(&format!("    {} {}", ty_str, name));
            param_names.insert(name);
        }
        out.push('\n');
    }
    out.push_str(")\n{\n");

    // Local variable declarations.
    let mut declared_vars: HashSet<String> = param_names.clone();

    // Declare used registers, using var_decl_idx to select among type candidates for clang-driven refinement.
    let mut decl_line_start = out.lines().count() + 1; // track line numbers for decl nodes
    let mut sorted_used_regs: Vec<RTLReg> = func.used_regs.iter().copied().collect();
    sorted_used_regs.sort();
    for reg in &sorted_used_regs {
        let name = format!("var_{}", reg);
        if declared_vars.insert(name.clone()) {
            let ty = if let Some(candidates) = func.var_type_candidates.get(reg) {
                // Multi-candidate: use var_decl_idx to pick current type
                let idx = func.var_decl_idx.get(reg).copied().unwrap_or(0);
                let type_str = candidates.get(idx)
                    .or_else(|| func.var_types.get(reg))
                    .map(|s| s.as_str())
                    .unwrap_or("int_I64");
                xtype_string_to_ctype(type_str)
            } else if let Some(type_str) = func.var_types.get(reg) {
                xtype_string_to_ctype(type_str)
            } else if func.reg_struct_ids.contains_key(reg) {
                let sid = func.reg_struct_ids[reg];
                let struct_name = format!("struct_{:x}", sid);
                CType::Pointer(Box::new(CType::Struct(struct_name)), TypeQualifiers::none())
            } else {
                CType::long()
            };
            let ty_str = ctype_to_c_string(&ty);
            let decl_text = format!("    {} {};\n", ty_str, name);
            // Map this declaration line to a synthetic node for clang error-driven var_decl_idx refinement.
            let current_line = out.lines().count() + 1;
            let synthetic_node = DECL_NODE_BASE.wrapping_add(*reg);
            line_map.insert(current_line, synthetic_node);
            out.push_str(&decl_text);
        }
    }

    // Declare variables discovered by conversion context
    let mut sorted_ctx_vars: Vec<(&String, &crate::decompile::passes::c_pass::types::CType)> = ctx.var_types.iter().collect();
    sorted_ctx_vars.sort_by_key(|(name, _)| (*name).clone());
    for (var_name, var_type) in sorted_ctx_vars {
        if declared_vars.insert(var_name.clone()) {
            let ty_str = ctype_to_c_string(var_type);
            out.push_str(&format!("    {} {};\n", ty_str, var_name));
        }
    }

    // Declare any remaining referenced variables as `long`
    let mut sorted_var_refs: Vec<&String> = all_var_refs.iter().collect();
    sorted_var_refs.sort();
    for var_name in sorted_var_refs {
        if !all_func_calls.contains(var_name) && declared_vars.insert(var_name.clone()) {
            out.push_str(&format!("    long {};\n", var_name));
        }
    }

    out.push('\n');

    // Statements (track line numbers).
    let preamble_lines = out.lines().count();
    let mut current_line = preamble_lines + 1; // 1-indexed

    for (node, cstmt) in &all_cstmts {
        let stmt_text = print::print_stmt(cstmt);
        let stmt_line_count = stmt_text.lines().count().max(1);
        for l in current_line..current_line + stmt_line_count {
            line_map.insert(l, *node);
        }
        for line in stmt_text.lines() {
            out.push_str("    ");
            out.push_str(line);
            out.push('\n');
        }
        current_line += stmt_line_count;
    }

    out.push_str("}\n");
    (out, line_map)
}

/// Count newlines in a string slice.
fn collect_cstmt_names(
    stmt: &crate::decompile::passes::c_pass::types::CStmt,
    vars: &mut HashSet<String>,
    funcs: &mut HashSet<String>,
) {
    use crate::decompile::passes::c_pass::types::{CBlockItem, CExpr, CStmt};
    match stmt {
        CStmt::Expr(e) => collect_cexpr_names(e, vars, funcs),
        CStmt::Return(Some(e)) => collect_cexpr_names(e, vars, funcs),
        CStmt::If(cond, then_s, else_s) => {
            collect_cexpr_names(cond, vars, funcs);
            collect_cstmt_names(then_s, vars, funcs);
            if let Some(e) = else_s {
                collect_cstmt_names(e, vars, funcs);
            }
        }
        CStmt::While(cond, body) | CStmt::DoWhile(body, cond) => {
            collect_cexpr_names(cond, vars, funcs);
            collect_cstmt_names(body, vars, funcs);
        }
        CStmt::For(_, cond, step, body) => {
            if let Some(c) = cond {
                collect_cexpr_names(c, vars, funcs);
            }
            if let Some(s) = step {
                collect_cexpr_names(s, vars, funcs);
            }
            collect_cstmt_names(body, vars, funcs);
        }
        CStmt::Block(items) => {
            for item in items {
                match item {
                    CBlockItem::Stmt(s) => collect_cstmt_names(s, vars, funcs),
                    CBlockItem::Decl(_) => {}
                }
            }
        }
        CStmt::Sequence(stmts) => {
            for s in stmts {
                collect_cstmt_names(s, vars, funcs);
            }
        }
        CStmt::Labeled(_, inner) => {
            collect_cstmt_names(inner, vars, funcs);
        }
        CStmt::Switch(e, body) => {
            collect_cexpr_names(e, vars, funcs);
            collect_cstmt_names(body, vars, funcs);
        }
        _ => {}
    }
}

fn collect_cexpr_names(
    expr: &crate::decompile::passes::c_pass::types::CExpr,
    vars: &mut HashSet<String>,
    funcs: &mut HashSet<String>,
) {
    use crate::decompile::passes::c_pass::types::CExpr;
    match expr {
        CExpr::Var(name) => { vars.insert(name.clone()); }
        CExpr::Call(func_expr, args) => {
            if let CExpr::Var(name) = func_expr.as_ref() {
                funcs.insert(name.clone());
            } else {
                collect_cexpr_names(func_expr, vars, funcs);
            }
            for a in args {
                collect_cexpr_names(a, vars, funcs);
            }
        }
        CExpr::Unary(_, inner) | CExpr::Cast(_, inner) | CExpr::Paren(inner) => {
            collect_cexpr_names(inner, vars, funcs);
        }
        CExpr::Binary(_, lhs, rhs) => {
            collect_cexpr_names(lhs, vars, funcs);
            collect_cexpr_names(rhs, vars, funcs);
        }
        CExpr::Assign(_, lhs, rhs) => {
            collect_cexpr_names(lhs, vars, funcs);
            collect_cexpr_names(rhs, vars, funcs);
        }
        CExpr::Ternary(c, t, e) => {
            collect_cexpr_names(c, vars, funcs);
            collect_cexpr_names(t, vars, funcs);
            collect_cexpr_names(e, vars, funcs);
        }
        CExpr::Member(inner, _) | CExpr::MemberPtr(inner, _) => {
            collect_cexpr_names(inner, vars, funcs);
        }
        CExpr::Index(arr, idx) => {
            collect_cexpr_names(arr, vars, funcs);
            collect_cexpr_names(idx, vars, funcs);
        }
        CExpr::SizeofExpr(inner) => {
            collect_cexpr_names(inner, vars, funcs);
        }
        CExpr::StmtExpr(stmts, final_expr) => {
            for s in stmts {
                collect_cstmt_names(s, vars, funcs);
            }
            collect_cexpr_names(final_expr, vars, funcs);
        }
        _ => {}
    }
}

/// Extract variable types from ClightStmt trees, preferring pointer types when a variable appears with multiple types.
fn collect_clight_var_types(
    stmt: &ClightStmt,
    var_types: &mut HashMap<u64, crate::decompile::passes::c_pass::types::CType>,
) {
    use crate::decompile::passes::c_pass::types::CType;

    fn collect_expr_types(expr: &ClightExpr, var_types: &mut HashMap<u64, CType>) {
        match expr {
            ClightExpr::Etempvar(id, ty) => {
                let ctype = clight_type_to_ctype(ty);
                let is_new_ptr = matches!(&ctype, CType::Pointer(_, _));
                var_types.entry(*id as u64)
                    .and_modify(|existing| {
                        // Pointer type wins over non-pointer
                        let existing_is_ptr = matches!(existing, CType::Pointer(_, _));
                        if is_new_ptr && !existing_is_ptr {
                            *existing = ctype.clone();
                        }
                    })
                    .or_insert(ctype);
            }
            ClightExpr::Ederef(inner, _) => collect_expr_types(inner, var_types),
            ClightExpr::Eaddrof(inner, _) => collect_expr_types(inner, var_types),
            ClightExpr::Eunop(_, inner, _) => collect_expr_types(inner, var_types),
            ClightExpr::Ebinop(_, lhs, rhs, _) => {
                collect_expr_types(lhs, var_types);
                collect_expr_types(rhs, var_types);
            }
            ClightExpr::Ecast(inner, _) => collect_expr_types(inner, var_types),
            ClightExpr::Efield(inner, _, _) => collect_expr_types(inner, var_types),
            _ => {}
        }
    }

    match stmt {
        ClightStmt::Sassign(lhs, rhs) => {
            collect_expr_types(lhs, var_types);
            collect_expr_types(rhs, var_types);
        }
        ClightStmt::Sset(id, expr) => {
            // The destination variable should be declared with the type of the expression
            let expr_ty = crate::decompile::passes::csh_pass::clight_expr_type(expr);
            let ctype = clight_type_to_ctype(&expr_ty);
            let is_new_ptr = matches!(&ctype, CType::Pointer(_, _));
            var_types.entry(*id as u64)
                .and_modify(|existing| {
                    let existing_is_ptr = matches!(existing, CType::Pointer(_, _));
                    if is_new_ptr && !existing_is_ptr {
                        *existing = ctype.clone();
                    }
                })
                .or_insert(ctype);
            collect_expr_types(expr, var_types);
        }
        ClightStmt::Scall(_, func_expr, args) => {
            collect_expr_types(func_expr, var_types);
            for arg in args { collect_expr_types(arg, var_types); }
        }
        ClightStmt::Sreturn(Some(expr)) => collect_expr_types(expr, var_types),
        ClightStmt::Sifthenelse(cond, then_b, else_b) => {
            collect_expr_types(cond, var_types);
            collect_clight_var_types(then_b, var_types);
            collect_clight_var_types(else_b, var_types);
        }
        ClightStmt::Ssequence(stmts) => {
            for s in stmts { collect_clight_var_types(s, var_types); }
        }
        ClightStmt::Sloop(b1, b2) => {
            collect_clight_var_types(b1, var_types);
            collect_clight_var_types(b2, var_types);
        }
        ClightStmt::Slabel(_, inner) => collect_clight_var_types(inner, var_types),
        ClightStmt::Sswitch(expr, cases) => {
            collect_expr_types(expr, var_types);
            for (_, s) in cases { collect_clight_var_types(s, var_types); }
        }
        _ => {}
    }
}

/// Convert a ClightType to a CType for variable declarations
fn clight_type_to_ctype(ty: &ClightType) -> crate::decompile::passes::c_pass::types::CType {
    use crate::decompile::passes::c_pass::types::{CType, IntSize, FloatSize, Signedness, TypeQualifiers};
    match ty {
        ClightType::Tint(ClightIntSize::I8, ClightSignedness::Signed, _) => CType::Int(IntSize::Char, Signedness::Signed),
        ClightType::Tint(ClightIntSize::I8, ClightSignedness::Unsigned, _) => CType::Int(IntSize::Char, Signedness::Unsigned),
        ClightType::Tint(ClightIntSize::I16, ClightSignedness::Signed, _) => CType::Int(IntSize::Short, Signedness::Signed),
        ClightType::Tint(ClightIntSize::I16, ClightSignedness::Unsigned, _) => CType::Int(IntSize::Short, Signedness::Unsigned),
        ClightType::Tint(ClightIntSize::I32, ClightSignedness::Signed, _) => CType::Int(IntSize::Int, Signedness::Signed),
        ClightType::Tint(ClightIntSize::I32, ClightSignedness::Unsigned, _) => CType::Int(IntSize::Int, Signedness::Unsigned),
        ClightType::Tint(ClightIntSize::IBool, _, _) => CType::Bool,
        ClightType::Tlong(ClightSignedness::Signed, _) => CType::Int(IntSize::Long, Signedness::Signed),
        ClightType::Tlong(ClightSignedness::Unsigned, _) => CType::Int(IntSize::Long, Signedness::Unsigned),
        ClightType::Tfloat(ClightFloatSize::F32, _) => CType::Float(FloatSize::Float),
        ClightType::Tfloat(ClightFloatSize::F64, _) => CType::Float(FloatSize::Double),
        ClightType::Tpointer(inner, _) => {
            let inner_ctype = clight_type_to_ctype(inner);
            CType::Pointer(Box::new(inner_ctype), TypeQualifiers::none())
        }
        ClightType::Tstruct(id, _) => CType::Struct(format!("struct_{:x}", id)),
        ClightType::Tvoid => CType::Void,
        _ => CType::Int(IntSize::Long, Signedness::Signed),
    }
}

fn collect_struct_names_from_ctype(ty: &crate::decompile::passes::c_pass::types::CType, names: &mut HashSet<String>) {
    use crate::decompile::passes::c_pass::types::CType;
    match ty {
        CType::Struct(name) => { names.insert(name.clone()); }
        CType::Pointer(inner, _) | CType::Array(inner, _) | CType::Qualified(inner, _) => {
            collect_struct_names_from_ctype(inner, names);
        }
        _ => {}
    }
}

/// Scan Efield usage patterns in a ClightStmt to build candidate types per (struct_name, field_name).
fn collect_field_usage_types(
    stmt: &ClightStmt,
    usage: &mut HashMap<(String, String), Vec<String>>,
) {
    fn collect_expr(expr: &ClightExpr, usage: &mut HashMap<(String, String), Vec<String>>) {
        match expr {
            // Ecast(Efield(Ederef(...Tstruct...), field_id, _), cast_ty): cast_ty is the actual usage type.
            ClightExpr::Ecast(inner, cast_ty) => {
                if let ClightExpr::Efield(deref_expr, field_id, _field_ty) = inner.as_ref() {
                    if let ClightExpr::Ederef(_, ClightType::Tstruct(struct_id, _)) = deref_expr.as_ref() {
                        let struct_name = format!("struct_{:x}", struct_id);
                        let field_name = crate::decompile::passes::csh_pass::field_ident_to_name(*field_id);
                        let type_str = clight_type_to_c_decl_str(cast_ty);
                        let key = (struct_name, field_name);
                        let types = usage.entry(key).or_default();
                        if !types.contains(&type_str) {
                            types.push(type_str);
                        }
                    }
                }
                collect_expr(inner, usage);
            }
            // Efield(Ederef(...Tstruct...), field_id, field_ty): field_ty is the declared field type.
            ClightExpr::Efield(inner, field_id, field_ty) => {
                if let ClightExpr::Ederef(_, ClightType::Tstruct(struct_id, _)) = inner.as_ref() {
                    let struct_name = format!("struct_{:x}", struct_id);
                    let field_name = crate::decompile::passes::csh_pass::field_ident_to_name(*field_id);
                    let type_str = clight_type_to_c_decl_str(field_ty);
                    let key = (struct_name, field_name);
                    let types = usage.entry(key).or_default();
                    if !types.contains(&type_str) {
                        types.push(type_str);
                    }
                }
                collect_expr(inner, usage);
            }
            ClightExpr::Ederef(inner, _) => collect_expr(inner, usage),
            ClightExpr::Eaddrof(inner, _) => collect_expr(inner, usage),
            ClightExpr::Eunop(_, inner, _) => collect_expr(inner, usage),
            ClightExpr::Ebinop(_, lhs, rhs, _) => {
                collect_expr(lhs, usage);
                collect_expr(rhs, usage);
            }
            _ => {}
        }
    }

    match stmt {
        ClightStmt::Sassign(lhs, rhs) => { collect_expr(lhs, usage); collect_expr(rhs, usage); }
        ClightStmt::Sset(_, expr) => collect_expr(expr, usage),
        ClightStmt::Scall(_, f, args) => {
            collect_expr(f, usage);
            for a in args { collect_expr(a, usage); }
        }
        ClightStmt::Sreturn(Some(e)) => collect_expr(e, usage),
        ClightStmt::Sifthenelse(c, t, e) => {
            collect_expr(c, usage);
            collect_field_usage_types(t, usage);
            collect_field_usage_types(e, usage);
        }
        ClightStmt::Ssequence(ss) => { for s in ss { collect_field_usage_types(s, usage); } }
        ClightStmt::Sloop(a, b) => {
            collect_field_usage_types(a, usage);
            collect_field_usage_types(b, usage);
        }
        ClightStmt::Slabel(_, inner) => collect_field_usage_types(inner, usage),
        ClightStmt::Sswitch(e, cases) => {
            collect_expr(e, usage);
            for (_, s) in cases { collect_field_usage_types(s, usage); }
        }
        _ => {}
    }
}

/// Extract struct pointer requirements from Efield patterns: which registers must be struct pointers and their field types.
fn extract_efield_requirements(
    statements: &HashMap<Node, ClightStmt>,
) -> (HashMap<Ident, Ident>, HashMap<Ident, Vec<(String, String)>>) {
    let mut reg_to_struct: HashMap<Ident, Ident> = HashMap::new();
    let mut struct_fields: HashMap<Ident, Vec<(String, String)>> = HashMap::new();

    fn scan_expr(
        expr: &ClightExpr,
        reg_to_struct: &mut HashMap<Ident, Ident>,
        struct_fields: &mut HashMap<Ident, Vec<(String, String)>>,
    ) {
        match expr {
            // Efield(Ederef(Etempvar(reg, ptr_struct), struct_ty), field_id, field_ty)
            ClightExpr::Efield(inner, field_id, field_ty) => {
                if let ClightExpr::Ederef(ptr_expr, ClightType::Tstruct(struct_id, _)) = inner.as_ref() {
                    // Extract the register from the pointer expression
                    let reg_ident = match ptr_expr.as_ref() {
                        ClightExpr::Etempvar(id, _) => Some(*id),
                        ClightExpr::Ecast(inner2, _) => {
                            if let ClightExpr::Etempvar(id, _) = inner2.as_ref() {
                                Some(*id)
                            } else { None }
                        }
                        _ => None,
                    };
                    if let Some(reg) = reg_ident {
                        reg_to_struct.insert(reg, *struct_id);
                    }
                    // Collect field info
                    let field_name = crate::decompile::passes::csh_pass::field_ident_to_name(*field_id);
                    let field_type = clight_type_to_c_decl_str(field_ty);
                    let fields = struct_fields.entry(*struct_id).or_default();
                    if !fields.iter().any(|(n, _)| n == &field_name) {
                        fields.push((field_name, field_type));
                    }
                }
                scan_expr(inner, reg_to_struct, struct_fields);
            }
            // Also catch Ecast(Efield(...)) which wraps field access in a cast
            ClightExpr::Ecast(inner, _) => scan_expr(inner, reg_to_struct, struct_fields),
            ClightExpr::Ederef(inner, _) => scan_expr(inner, reg_to_struct, struct_fields),
            ClightExpr::Eaddrof(inner, _) => scan_expr(inner, reg_to_struct, struct_fields),
            ClightExpr::Eunop(_, inner, _) => scan_expr(inner, reg_to_struct, struct_fields),
            ClightExpr::Ebinop(_, lhs, rhs, _) => {
                scan_expr(lhs, reg_to_struct, struct_fields);
                scan_expr(rhs, reg_to_struct, struct_fields);
            }
            ClightExpr::Econdition(c, t, f, _) => {
                scan_expr(c, reg_to_struct, struct_fields);
                scan_expr(t, reg_to_struct, struct_fields);
                scan_expr(f, reg_to_struct, struct_fields);
            }
            _ => {}
        }
    }

    fn scan_stmt(
        stmt: &ClightStmt,
        reg_to_struct: &mut HashMap<Ident, Ident>,
        struct_fields: &mut HashMap<Ident, Vec<(String, String)>>,
    ) {
        match stmt {
            ClightStmt::Sassign(lhs, rhs) => { scan_expr(lhs, reg_to_struct, struct_fields); scan_expr(rhs, reg_to_struct, struct_fields); }
            ClightStmt::Sset(_, expr) => scan_expr(expr, reg_to_struct, struct_fields),
            ClightStmt::Scall(_, f, args) => {
                scan_expr(f, reg_to_struct, struct_fields);
                for a in args { scan_expr(a, reg_to_struct, struct_fields); }
            }
            ClightStmt::Sreturn(Some(e)) => scan_expr(e, reg_to_struct, struct_fields),
            ClightStmt::Sifthenelse(c, t, e) => {
                scan_expr(c, reg_to_struct, struct_fields);
                scan_stmt(t, reg_to_struct, struct_fields);
                scan_stmt(e, reg_to_struct, struct_fields);
            }
            ClightStmt::Ssequence(ss) => { for s in ss { scan_stmt(s, reg_to_struct, struct_fields); } }
            ClightStmt::Sloop(a, b) => { scan_stmt(a, reg_to_struct, struct_fields); scan_stmt(b, reg_to_struct, struct_fields); }
            ClightStmt::Slabel(_, inner) => scan_stmt(inner, reg_to_struct, struct_fields),
            ClightStmt::Sswitch(e, cases) => {
                scan_expr(e, reg_to_struct, struct_fields);
                for (_, s) in cases { scan_stmt(s, reg_to_struct, struct_fields); }
            }
            _ => {}
        }
    }

    for stmt in statements.values() {
        scan_stmt(stmt, &mut reg_to_struct, &mut struct_fields);
    }

    (reg_to_struct, struct_fields)
}

/// Convert a ClightType to a C declaration string for struct field types.
fn clight_type_to_c_decl_str(ty: &ClightType) -> String {
    match ty {
        ClightType::Tint(ClightIntSize::I8, ClightSignedness::Signed, _) => "signed char".to_string(),
        ClightType::Tint(ClightIntSize::I8, ClightSignedness::Unsigned, _) => "unsigned char".to_string(),
        ClightType::Tint(ClightIntSize::I16, ClightSignedness::Signed, _) => "short".to_string(),
        ClightType::Tint(ClightIntSize::I16, ClightSignedness::Unsigned, _) => "unsigned short".to_string(),
        ClightType::Tint(ClightIntSize::I32, ClightSignedness::Signed, _) => "int".to_string(),
        ClightType::Tint(ClightIntSize::I32, ClightSignedness::Unsigned, _) => "unsigned int".to_string(),
        ClightType::Tint(ClightIntSize::IBool, _, _) => "int".to_string(),
        ClightType::Tlong(ClightSignedness::Signed, _) => "long".to_string(),
        ClightType::Tlong(ClightSignedness::Unsigned, _) => "unsigned long".to_string(),
        ClightType::Tfloat(ClightFloatSize::F32, _) => "float".to_string(),
        ClightType::Tfloat(ClightFloatSize::F64, _) => "double".to_string(),
        ClightType::Tpointer(inner, _) => format!("{} *", clight_type_to_c_decl_str(inner)),
        ClightType::Tstruct(id, _) => format!("struct struct_{:x}", id),
        ClightType::Tvoid => "void".to_string(),
        _ => "long".to_string(),
    }
}

fn chunk_to_c_type_str(chunk: &MemoryChunk) -> &'static str {
    match chunk {
        MemoryChunk::MBool => "int",
        MemoryChunk::MInt8Signed => "signed char",
        MemoryChunk::MInt8Unsigned => "unsigned char",
        MemoryChunk::MInt16Signed => "short",
        MemoryChunk::MInt16Unsigned => "unsigned short",
        MemoryChunk::MInt32 => "int",
        MemoryChunk::MInt64 => "long",
        MemoryChunk::MFloat32 => "float",
        MemoryChunk::MFloat64 => "double",
        _ => "long",
    }
}

// Fresh CXIndex per call sidesteps the per-instance LLVM bug #25896 race. libclang is not safe to initialize/invoke concurrently (CEGAR selector calls this from rayon workers and the test suite decompiles concurrently), so all libclang access is serialized through a global lock; the per-function clang_cache keeps locked calls low, and it is poison-tolerant so one panicking check does not wedge later ones.
static CLANG_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn run_clang_check(c_code: &str) -> Vec<ClangError> {
    use clang_sys::*;

    let _clang_guard = CLANG_LOCK.lock().unwrap_or_else(|e| e.into_inner());

    let c_code_bytes = c_code.as_bytes();
    let filename = CString::new("check.c").unwrap();
    let contents = match CString::new(c_code) {
        Ok(c) => c,
        Err(_) => return Vec::new(), // null byte in source, skip
    };

    // clang args: parse as C, suppress warnings
    let arg_strs = ["-x", "c", "-w", "-ferror-limit=0"];
    let c_args: Vec<CString> = arg_strs.iter().map(|s| CString::new(*s).unwrap()).collect();
    let c_arg_ptrs: Vec<*const std::os::raw::c_char> =
        c_args.iter().map(|s| s.as_ptr()).collect();

    let mut unsaved = CXUnsavedFile {
        Filename: filename.as_ptr(),
        Contents: contents.as_ptr(),
        Length: c_code_bytes.len() as std::os::raw::c_ulong,
    };

    unsafe {
        let index = clang_createIndex(0, 0);
        if index.is_null() {
            return Vec::new();
        }

        let tu = clang_parseTranslationUnit(
            index,
            filename.as_ptr(),
            c_arg_ptrs.as_ptr(),
            c_arg_ptrs.len() as std::os::raw::c_int,
            &mut unsaved,
            1,
            CXTranslationUnit_None,
        );

        let mut errors = Vec::new();

        if !tu.is_null() {
            let num_diags = clang_getNumDiagnostics(tu);
            for i in 0..num_diags {
                let diag = clang_getDiagnostic(tu, i);
                let severity = clang_getDiagnosticSeverity(diag);

                if severity >= CXDiagnostic_Error {
                    let location = clang_getDiagnosticLocation(diag);
                    let spelling = clang_getDiagnosticSpelling(diag);

                    let mut file = std::ptr::null_mut();
                    let mut line: c_uint = 0;
                    let mut column: c_uint = 0;
                    let mut offset: c_uint = 0;
                    clang_getExpansionLocation(
                        location, &mut file, &mut line, &mut column, &mut offset,
                    );

                    let msg_ptr = clang_getCString(spelling);
                    let msg = if msg_ptr.is_null() {
                        String::new()
                    } else {
                        CStr::from_ptr(msg_ptr).to_string_lossy().into_owned()
                    };
                    clang_disposeString(spelling);

                    errors.push(ClangError {
                        line: line as usize,
                        column: column as usize,
                        message: msg,
                    });
                }

                clang_disposeDiagnostic(diag);
            }
            clang_disposeTranslationUnit(tu);
        }

        clang_disposeIndex(index);
        errors
    }
}


fn xtype_to_c_decl_str(xt: &XType) -> String {
    match xt {
        XType::Xvoid => "void".to_string(),
        XType::Xbool => "int".to_string(),
        XType::Xint8signed => "signed char".to_string(),
        XType::Xint8unsigned => "unsigned char".to_string(),
        XType::Xint16signed => "short".to_string(),
        XType::Xint16unsigned => "unsigned short".to_string(),
        XType::Xint | XType::Xany32 => "int".to_string(),
        XType::Xintunsigned => "unsigned int".to_string(),
        XType::Xlong | XType::Xany64 => "long".to_string(),
        XType::Xlongunsigned => "unsigned long".to_string(),
        XType::Xfloat => "double".to_string(),
        XType::Xsingle => "float".to_string(),
        XType::Xptr => "void *".to_string(),
        XType::Xcharptr => "char *".to_string(),
        XType::Xcharptrptr => "char **".to_string(),
        XType::Xintptr => "int *".to_string(),
        XType::Xfloatptr => "double *".to_string(),
        XType::Xsingleptr => "float *".to_string(),
        XType::Xfuncptr => "void (*)()".to_string(),
        XType::XstructPtr(sid) => format!("struct struct_{:x} *", sid),
    }
}

fn lookup_callee_signature<'a>(
    name: &str,
    sigs: &'a HashMap<Ident, CalleeSignature>,
    name_to_ident: &HashMap<String, Ident>,
) -> Option<&'a CalleeSignature> {
    if let Some(rest) = name.strip_prefix("var_") {
        if let Ok(id) = rest.parse::<Ident>() {
            if let Some(sig) = sigs.get(&id) {
                return Some(sig);
            }
        }
    }
    name_to_ident.get(name).and_then(|id| sigs.get(id))
}

fn forward_decl_for(
    name: &str,
    sig: Option<&CalleeSignature>,
) -> String {
    // K&R-style `<ret> name();` decl: variadic-friendly (printf/fprintf don't error on extras), still gives clang the right return type so `r = call()` yields real ptr/int diagnostics for Wave 1, and per-arg casts via callee_signatures (D11) already run at C-emission.
    match sig {
        Some(sig) => {
            let ret = xtype_to_c_decl_str(&sig.return_type);
            format!("{} {}();\n", ret, name)
        }
        None => format!("long {}();\n", name),
    }
}

fn convert_clight_return_type(ty: &ClightType) -> String {
    match ty {
        ClightType::Tvoid => "void".to_string(),
        ClightType::Tint(..) => "int".to_string(),
        ClightType::Tlong(..) => "long".to_string(),
        ClightType::Tfloat(..) => "double".to_string(),
        ClightType::Tpointer(..) => "void *".to_string(),
        _ => "long".to_string(),
    }
}

fn ctype_to_c_string(ty: &crate::decompile::passes::c_pass::types::CType) -> String {
    use crate::decompile::passes::c_pass::types::*;
    match ty {
        CType::Void => "void".to_string(),
        CType::Bool => "int".to_string(),
        CType::Int(size, sign) => {
            let sign_str = match sign {
                Signedness::Signed => "",
                Signedness::Unsigned => "unsigned ",
            };
            let size_str = match size {
                IntSize::Char => "char",
                IntSize::Short => "short",
                IntSize::Int => "int",
                IntSize::Long => "long",
                IntSize::LongLong => "long long",
            };
            format!("{}{}", sign_str, size_str)
        }
        CType::Float(size) => match size {
            FloatSize::Float => "float".to_string(),
            FloatSize::Double => "double".to_string(),
            FloatSize::LongDouble => "long double".to_string(),
        },
        CType::Pointer(inner, _) => format!("{} *", ctype_to_c_string(inner)),
        CType::Struct(name) => format!("struct {}", name),
        _ => "long".to_string(),
    }
}


// Edge consistency

// Post-processing helpers

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

const MAX_IFTHENELSE_DEPTH: usize = 4;

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

    for node in nodes_to_process {
        if let Some(stmt) = statements.get(&node).cloned() {
            let mut visiting = HashSet::new();
            visiting.insert(node);
            let (inlined, newly_inlined) =
                inline_stmt_recursive_track(&stmt, statements, &preds, &mut visiting, 0);
            // Free absorbed children immediately. Each inlined node has pred_count==1 (its only
            // predecessor is the node we just inlined it into), so it is not referenced elsewhere
            // and its content now lives inside `inlined`. Without this, every node's fully-inlined
            // tree coexists in `statements` until the retain below -- O(n^2) memory on long pred==1
            // chains, which OOMs large functions (e.g. 136803, stuck here at >11G).
            for &n in &newly_inlined {
                statements.remove(&n);
            }
            inlined_nodes.extend(newly_inlined);
            if inlined != stmt {
                statements.insert(node, inlined);
            }
        }
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

fn inline_stmt_recursive_track(
    stmt: &ClightStmt,
    statements: &HashMap<Node, ClightStmt>,
    preds: &HashMap<Node, usize>,
    visiting: &mut HashSet<Node>,
    inline_count: usize,
) -> (ClightStmt, Vec<Node>) {
    let mut inlined = Vec::new();

    let result = match stmt {
        ClightStmt::Sifthenelse(cond, then_box, else_box) => {
            let (then_stmt, then_inlined) =
                inline_body_if_local_track(&**then_box, statements, preds, visiting, inline_count);
            let (else_stmt, else_inlined) =
                inline_body_if_local_track(&**else_box, statements, preds, visiting, inline_count);
            inlined.extend(then_inlined);
            inlined.extend(else_inlined);
            ClightStmt::Sifthenelse(cond.clone(), Box::new(then_stmt), Box::new(else_stmt))
        }
        ClightStmt::Sloop(body_box, incr_box) => {
            let (body_stmt, body_inlined) =
                inline_body_if_local_track(&**body_box, statements, preds, visiting, inline_count);
            let (incr_stmt, incr_inlined) =
                inline_body_if_local_track(&**incr_box, statements, preds, visiting, inline_count);
            inlined.extend(body_inlined);
            inlined.extend(incr_inlined);
            ClightStmt::Sloop(Box::new(body_stmt), Box::new(incr_stmt))
        }
        ClightStmt::Ssequence(stmts) => {
            let mut result_stmts = Vec::new();
            for s in stmts {
                let (inlined_s, s_inlined) =
                    inline_stmt_recursive_track(s, statements, preds, visiting, inline_count);
                result_stmts.push(inlined_s);
                inlined.extend(s_inlined);
            }
            ClightStmt::Ssequence(flatten_sequence(result_stmts))
        }
        ClightStmt::Slabel(lbl, inner) => {
            let (inner_inlined, inner_nodes) =
                inline_stmt_recursive_track(&**inner, statements, preds, visiting, inline_count);
            inlined.extend(inner_nodes);
            ClightStmt::Slabel(*lbl, Box::new(inner_inlined))
        }
        ClightStmt::Sswitch(expr, cases) => {
            let mut new_cases = Vec::new();
            for (label, case_stmt) in cases {
                let (inlined_case, case_inlined) =
                    inline_body_if_local_track(case_stmt, statements, preds, visiting, inline_count);
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
    inline_count: usize,
) -> (ClightStmt, Vec<Node>) {
    match stmt {
        ClightStmt::Sgoto(target_ident) => {
            let target_node = *target_ident as u64;
            let pred_count = preds.get(&target_node).copied().unwrap_or(0);

            if pred_count == 1
                && !visiting.contains(&target_node)
                && inline_count < MAX_IFTHENELSE_DEPTH
            {
                if let Some(target_stmt) = statements.get(&target_node) {
                    if is_trivial_labeled_goto(target_stmt) {
                        return (stmt.clone(), vec![]);
                    }

                    visiting.insert(target_node);
                    let (recursed_stmt, mut recursed_nodes) = inline_stmt_recursive_track(
                        target_stmt, statements, preds, visiting, inline_count + 1,
                    );
                    recursed_nodes.push(target_node);
                    return (recursed_stmt, recursed_nodes);
                }
            }

            (stmt.clone(), vec![])
        }
        _ => inline_stmt_recursive_track(stmt, statements, preds, visiting, inline_count),
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

#[doc(hidden)]
pub fn libclang_concurrent_check(runs: usize) -> Result<(), String> {
    let clean_src = r#"
        int main(void) {
            int x = 1;
            int y = x + 2;
            return y;
        }
    "#;
    let broken_src = r#"
        int main(void) {
            int *p = 0;
            int x = p;
            return x + undefined_symbol;
        }
    "#;

    let clean_results: Vec<usize> = (0..runs)
        .into_par_iter()
        .map(|_| {
            let _ = clang_sys::load();
            run_clang_check(clean_src).len()
        })
        .collect();
    let broken_results: Vec<usize> = (0..runs)
        .into_par_iter()
        .map(|_| {
            let _ = clang_sys::load();
            run_clang_check(broken_src).len()
        })
        .collect();

    let clean_first = clean_results[0];
    if clean_first != 0 {
        return Err(format!("clean source produced {} errors, expected 0", clean_first));
    }
    for (i, &n) in clean_results.iter().enumerate() {
        if n != clean_first {
            return Err(format!("clean run {} returned {} errors, expected {}", i, n, clean_first));
        }
    }
    let broken_first = broken_results[0];
    if broken_first == 0 {
        return Err("broken source produced 0 errors, expected at least one".to_string());
    }
    for (i, &n) in broken_results.iter().enumerate() {
        if n != broken_first {
            return Err(format!("broken run {} returned {} errors, expected {}", i, n, broken_first));
        }
    }
    Ok(())
}
