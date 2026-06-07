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
                // A5: if this exit flows to a function return, tail-duplicate the value assignment + the return into the branch rather than emitting a valueless break, which drops the returned value at the post-loop join.
                if let Some(&(value_node, ret_node)) = info.exit_returns.get(&node) {
                    if let Some(tail) = build_return_tail(statements, value_node, ret_node) {
                        body_stmts.push(replace_break_with(break_stmt, &tail));
                        absorbed_value_nodes.push(value_node);
                        continue;
                    }
                }
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

// Recursion/stack-depth bound for goto-chain inlining (inline_body_if_local_track). It caps how deep a single-predecessor goto chain is followed through ALL statement kinds (Ssequence/Sloop/Sswitch/Sifthenelse/Slabel), not just if-then-else. Termination is already guaranteed by the `visiting` set; this cap exists ONLY to bound native stack depth, since the downstream printer (print.rs) recurses with no depth guard and would stack-overflow on a pathologically deep chain. Corpus max observed chain depth is ~81, so 256 admits every real chain while staying safely bounded.
const MAX_GOTO_INLINE_DEPTH: usize = 256;

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
                && inline_count < MAX_GOTO_INLINE_DEPTH
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
