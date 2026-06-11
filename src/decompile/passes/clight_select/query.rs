

use crate::decompile::passes::clight_pass::is_nonempty_stmt;
use crate::decompile::passes::csh_pass::ident_from_node;
use crate::decompile::elevator::DecompileDB;
use crate::x86::mach::Mreg;
use crate::x86::types::*;
use object::{Object, ObjectSection};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fs;
use std::path::Path;

fn xtype_to_string(xtype: &XType) -> String {
    match xtype {
        XType::Xbool => "int_IBool".to_string(),
        XType::Xint8signed => "int_I8".to_string(),
        XType::Xint8unsigned => "int_I8_unsigned".to_string(),
        XType::Xint16signed => "int_I16".to_string(),
        XType::Xint16unsigned => "int_I16_unsigned".to_string(),
        XType::Xint | XType::Xany32 => "int_I32".to_string(),
        XType::Xintunsigned => "int_I32_unsigned".to_string(),
        XType::Xlong | XType::Xany64 => "int_I64".to_string(),
        XType::Xlongunsigned => "int_I64_unsigned".to_string(),
        XType::Xfloat => "float_F64".to_string(),
        XType::Xsingle => "float_F32".to_string(),
        XType::Xptr => "ptr_I64".to_string(),
        XType::Xcharptr => "ptr_char".to_string(),
        XType::Xcharptrptr => "ptr_ptr_char".to_string(),
        XType::Xintptr => "ptr_int".to_string(),
        XType::Xfloatptr => "ptr_double".to_string(),
        XType::Xsingleptr => "ptr_float".to_string(),
        XType::Xfuncptr => "ptr_func".to_string(),
        XType::Xvoid => "void".to_string(),
        XType::XstructPtr(struct_id) => format!("ptr_struct_{:x}", struct_id),
    }
}

fn xtype_priority(xtype: &XType) -> u8 {
    match xtype {
        XType::Xvoid => 0,
        XType::Xbool => 1,
        XType::Xany32 => 2,
        XType::Xint => 4,
        XType::Xany64 => 5,
        XType::Xintunsigned => 5,
        XType::Xlong => 6,
        XType::Xlongunsigned => 7,
        XType::Xint8signed | XType::Xint8unsigned => 8,
        XType::Xint16signed | XType::Xint16unsigned => 9,
        XType::Xfloat => 10,
        XType::Xsingle => 11,
        XType::Xptr => 12,
        XType::Xintptr | XType::Xfloatptr | XType::Xsingleptr => 12,
        XType::Xcharptr | XType::Xcharptrptr => 13,
        XType::Xfuncptr => 14,
        XType::XstructPtr(_) => 15,
        _ => 0,
    }
}

/// Sort priority for type candidate strings (mirrors xtype_priority).
fn type_str_sort_priority(s: &str) -> u8 {
    if s.starts_with("ptr_struct_") { 15 }
    else if s == "ptr_func" { 14 }
    else if s == "ptr_char" { 13 }
    else if s.starts_with("ptr_") { 12 }
    else if s == "float_F64" { 10 }
    else if s == "float_F32" { 11 }
    else if s.starts_with("int_I8") { 8 }
    else if s.starts_with("int_I16") { 9 }
    else if s == "int_U64" { 7 }
    else if s == "int_I64" { 6 }
    else if s == "int_U32" { 5 }
    else if s == "int_I32" { 4 }
    else { 3 }
}

#[derive(Debug, Clone)]
pub struct CalleeSignature {
    pub param_count: usize,
    pub return_type: XType,
    #[allow(dead_code)]
    pub param_types: Vec<XType>,
}

#[derive(Debug, Clone)]
pub struct FunctionData {
    pub address: Address,
    pub name: String,
    pub entry_node: Node,
    pub return_type: ClightType,
    #[allow(dead_code)]
    pub return_reg: Option<RTLReg>,
    pub param_regs: Vec<RTLReg>,
    pub param_types: Vec<ParamType>,
    pub stack_size: u64,

    pub node_statements: HashMap<Node, Vec<ClightStmt>>,

    pub successors: HashMap<Node, Vec<Node>>,

    pub used_regs: HashSet<RTLReg>,

    pub struct_fields: HashMap<i64, Vec<(i64, Ident, MemoryChunk)>>,

    pub sseq_groups: HashMap<Node, Vec<Node>>,

    pub var_types: HashMap<RTLReg, String>,

    /// All type candidates per register for variable declarations; clang_refine swaps declaration types on type mismatch errors.
    pub var_type_candidates: HashMap<RTLReg, Vec<String>>,

    /// Current declaration type index per register (used by clang_refine).
    pub var_decl_idx: HashMap<RTLReg, usize>,

    pub loop_headers: HashSet<Node>,
    pub switch_heads: HashSet<Node>,

    pub reg_struct_ids: HashMap<RTLReg, usize>,

    /// Per-struct, per-field type candidates for struct body emission, keyed by (struct_name, field_name); clang_refine advances indices to try different field types.
    pub struct_field_type_candidates: HashMap<(String, String), Vec<String>>,
    pub struct_field_type_idx: HashMap<(String, String), usize>,

    pub reg_to_mreg: HashMap<RTLReg, Mreg>,

    // Known callee signatures indexed by function ident (address)
    pub callee_signatures: HashMap<Ident, CalleeSignature>,
}

#[derive(Debug, Clone)]
pub enum ScalarConstant {
    Int32(i32),
    Int64(i64),
    Float32(f32),
    Float64(f64),
}

#[derive(Debug, Clone)]
pub struct GlobalData {
    pub id: usize,
    pub name: String,
    pub is_string: bool,
    pub content: Vec<u8>,
    pub is_pointer: bool,
    pub scalar_value: Option<ScalarConstant>,
}

impl FunctionData {
    pub fn new(
        address: Address,
        name: String,
        param_regs: Vec<RTLReg>,
        param_types: Vec<ParamType>,
        return_reg: Option<RTLReg>,
        stack_size: u64,
        entry_node: Node,
    ) -> Self {
        FunctionData {
            address,
            name,
            entry_node,
            return_type: ClightType::Tvoid,
            return_reg,
            param_regs,
            param_types,
            stack_size,
            node_statements: HashMap::new(),
            successors: HashMap::new(),
            used_regs: HashSet::new(),
            struct_fields: HashMap::new(),
            sseq_groups: HashMap::new(),
            var_types: HashMap::new(),
            var_type_candidates: HashMap::new(),
            var_decl_idx: HashMap::new(),
            struct_field_type_candidates: HashMap::new(),
            struct_field_type_idx: HashMap::new(),
            loop_headers: HashSet::new(),
            switch_heads: HashSet::new(),
            reg_struct_ids: HashMap::new(),
            reg_to_mreg: HashMap::new(),
            callee_signatures: HashMap::new(),
        }
    }
}

/// Per-(function, reg) XType deduped from emit_function_param_type: int beats long-width placeholders, else highest priority wins; shared so extract_functions and extract_callee_signatures agree.
pub(crate) fn build_param_xtypes(db: &DecompileDB) -> HashMap<(Address, RTLReg), XType> {
    let mut param_xtypes: HashMap<(Address, RTLReg), XType> = HashMap::new();
    for (addr, reg, xtype) in db.rel_iter::<(Address, RTLReg, XType)>("emit_function_param_type") {
        param_xtypes
            .entry((*addr, *reg))
            .and_modify(|existing| {
                let dominated_by_int = matches!(
                    (*existing, *xtype),
                    (XType::Xlong | XType::Xlongunsigned, XType::Xint | XType::Xintunsigned)
                );
                if dominated_by_int {
                    *existing = *xtype;
                } else if !matches!(
                    (*existing, *xtype),
                    (XType::Xint | XType::Xintunsigned, XType::Xlong | XType::Xlongunsigned)
                ) {
                    if xtype_priority(xtype) > xtype_priority(existing) {
                        *existing = *xtype;
                    }
                }
            })
            .or_insert(*xtype);
    }
    param_xtypes
}

/// Maps (function, RTLReg) to entry-node Mreg for CC-slot ordering; keeps the smallest mreg explicitly so a broken single-value invariant in reg_rtl doesn't silently let Ascent set order pick the winner.
pub(crate) fn build_rtl_to_mreg_at_entry(db: &DecompileDB) -> HashMap<(Address, RTLReg), Mreg> {
    let mut rtl_to_mreg_at_entry: HashMap<(Address, RTLReg), Mreg> = HashMap::new();
    let mut entry_to_addrs: HashMap<Node, Vec<Address>> = HashMap::new();
    for (a, _, n) in db.rel_iter::<(Address, Symbol, Node)>("emit_function") {
        entry_to_addrs.entry(*n).or_default().push(*a);
    }
    for (node, mreg, rtl_reg) in db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl") {
        if let Some(addrs) = entry_to_addrs.get(node) {
            for &addr in addrs {
                rtl_to_mreg_at_entry
                    .entry((addr, *rtl_reg))
                    .and_modify(|e| {
                        if *mreg < *e {
                            *e = *mreg;
                        }
                    })
                    .or_insert(*mreg);
            }
        }
    }
    rtl_to_mreg_at_entry
}

/// Builds the callee signature map factored out of extract_functions so clight_emit's TR-3 re-selection can rebuild it after the solve, when FunctionData is no longer available.
pub(crate) fn extract_callee_signatures(
    db: &DecompileDB,
    param_xtypes: &HashMap<(Address, RTLReg), XType>,
    rtl_to_mreg_at_entry: &HashMap<(Address, RTLReg), Mreg>,
) -> HashMap<Ident, CalleeSignature> {
    let mut callee_sigs: HashMap<Ident, CalleeSignature> = HashMap::new();

    // Pre-build symbol-to-idents map for O(1) lookup
    let mut symbol_to_idents: HashMap<Symbol, Vec<Ident>> = HashMap::new();
    for (id, sym) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
        symbol_to_idents.entry(*sym).or_default().push(*id);
    }

    // resolved_extern_signature is multi-valued per symbol (one row per call-site signature); group and pick the lexicographically smallest tuple so the chosen signature is identical across runs regardless of Ascent set order.
    {
        let mut by_symbol: BTreeMap<Symbol, Vec<(usize, XType, Arc<Vec<XType>>)>> =
            BTreeMap::new();
        for (name, param_count, ret_type, param_types) in
            db.rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("resolved_extern_signature")
        {
            by_symbol
                .entry(*name)
                .or_default()
                .push((*param_count, *ret_type, param_types.clone()));
        }
        for (name, mut sigs) in by_symbol {
            sigs.sort();
            let (param_count, ret_type, param_types) = sigs.into_iter().next().unwrap();
            if let Some(idents) = symbol_to_idents.get(&name) {
                for &id in idents {
                    callee_sigs.insert(id, CalleeSignature {
                        param_count,
                        return_type: ret_type,
                        param_types: (*param_types).clone(),
                    });
                }
            }
        }
    }

    // emit_function_param_count may be multi-valued; keep the smallest count per address and iterate in sorted address order for a deterministic result.
    let mut param_count_by_addr: BTreeMap<Address, usize> = BTreeMap::new();
    for &(addr, count) in db.rel_iter::<(Address, usize)>("emit_function_param_count") {
        param_count_by_addr
            .entry(addr)
            .and_modify(|c| *c = (*c).min(count))
            .or_insert(count);
    }
    for (addr, count) in param_count_by_addr {
        let ident = addr as Ident;
        if callee_sigs.contains_key(&ident) {
            continue;
        }
        // emit_function_param_type iteration order is non-deterministic and the relation is multi-valued per (addr, reg); take the deduped per-reg type from param_xtypes and order by calling-convention slot so param_types is positional and identical across runs.
        let mut typed: Vec<(RTLReg, XType)> = param_xtypes
            .iter()
            .filter(|((a, _), _)| *a == addr)
            .map(|((_, reg), xt)| (*reg, *xt))
            .collect();
        typed.sort_by(|x, y| {
            let kx = rtl_to_mreg_at_entry
                .get(&(addr, x.0))
                .map(|m| crate::decompile::analysis::signature_pass::param_mreg_sort_key(*m))
                .unwrap_or(usize::MAX);
            let ky = rtl_to_mreg_at_entry
                .get(&(addr, y.0))
                .map(|m| crate::decompile::analysis::signature_pass::param_mreg_sort_key(*m))
                .unwrap_or(usize::MAX);
            kx.cmp(&ky).then(x.0.cmp(&y.0))
        });
        let param_types: Vec<XType> = typed.into_iter().map(|(_, t)| t).collect();

        // emit_function_return_type_xtype may be multi-valued; pick the smallest deterministically instead of relying on iteration order.
        let ret_type = db
            .rel_iter::<(Address, XType)>("emit_function_return_type_xtype")
            .filter(|(a, _)| *a == addr)
            .map(|(_, t)| *t)
            .min()
            .unwrap_or(XType::Xvoid);

        callee_sigs.insert(ident, CalleeSignature {
            param_count: count,
            return_type: ret_type,
            param_types,
        });
    }

    callee_sigs
}

pub fn extract_functions(db: &DecompileDB) -> Result<(Vec<FunctionData>, HashMap<usize, String>), String> {
    let mut functions = Vec::new();
    let mut func_map: HashMap<Address, FunctionData> = HashMap::new();
    let param_xtypes = build_param_xtypes(db);

    // instr_in_function is multi-valued (shared PLT/thunk nodes and GCC hot/cold clones sharing a tail belong to several functions); resolve to the function that actually CONTAINS the node by address: the nearest preceding entry (largest owning address <= node). The old min-address rule handed a hot function's shared tail to its lower-addressed `.cold` clone, leaving the hot body return-less so it was dropped by dead-code elimination (emitted as a bare `int f(void)`). Nearest-preceding is deterministic like min, so node->function stays stable across runs.
    let mut node_to_func: HashMap<Node, Address> = HashMap::new();
    for (node, func) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        node_to_func
            .entry(*node)
            .and_modify(|e| {
                let cand_contains = *func <= *node;
                let cur_contains = *e <= *node;
                let better = match (cand_contains, cur_contains) {
                    (true, true) => *func > *e,   // both contain the node: nearest preceding = larger entry
                    (true, false) => true,        // only candidate contains it
                    (false, true) => false,       // only current contains it
                    (false, false) => *func < *e, // neither contains (shouldn't happen): smaller for stability
                };
                if better {
                    *e = *func;
                }
            })
            .or_insert(*func);
    }

    let mut id_to_name: HashMap<usize, String> = HashMap::new();
    for (id, name) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
        let name_str = name.to_string();
        id_to_name
            .entry(*id)
            .and_modify(|existing| {
                if name.len() < existing.len() {
                    *existing = name_str.clone();
                }
            })
            .or_insert_with(|| name_str);
    }
    // ELF symbols are authoritative: override ident_to_symbol entries.
    for (addr, name, _) in db.rel_iter::<(Address, Symbol, Symbol)>("symbols") {
        let id = *addr as usize;
        id_to_name.insert(id, name.to_string());
    }

    // emit_function_param iteration order is non-deterministic (Ascent set, parallel tuple-insertion order varies across runs). Sort each function's parameter list by the underlying Mreg's calling-convention slot, with the RTLReg as a final tiebreak, so p0/p1/... assignments and call-site argument ordering are stable.
    let rtl_to_mreg_at_entry = build_rtl_to_mreg_at_entry(db);
    let mut func_params: HashMap<Address, Vec<RTLReg>> = HashMap::new();
    for (addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param") {
        let params = func_params.entry(*addr).or_default();
        if !params.contains(reg) {
            params.push(*reg);
        }
    }
    for (addr, params) in func_params.iter_mut() {
        params.sort_by(|a, b| {
            let ka = rtl_to_mreg_at_entry
                .get(&(*addr, *a))
                .map(|m| crate::decompile::analysis::signature_pass::param_mreg_sort_key(*m))
                .unwrap_or(usize::MAX);
            let kb = rtl_to_mreg_at_entry
                .get(&(*addr, *b))
                .map(|m| crate::decompile::analysis::signature_pass::param_mreg_sort_key(*m))
                .unwrap_or(usize::MAX);
            ka.cmp(&kb).then_with(|| a.cmp(b))
        });
    }

    let mut var_is_struct: HashMap<(Address, RTLReg), usize> = HashMap::new();
    for (addr, reg, sid) in db.rel_iter::<(Address, RTLReg, usize)>("emit_var_is_struct") {
        var_is_struct.insert((*addr, *reg), *sid);
    }

    let mut param_struct_by_pos: HashMap<(Address, usize), usize> = HashMap::new();
    for (func_addr, pos, canonical_id) in db.rel_iter::<(Address, usize, usize)>("func_param_struct_type") {
        param_struct_by_pos.insert((*func_addr, *pos), *canonical_id);
    }

    let mut struct_canonical: HashMap<usize, usize> = HashMap::new();
    for (orig, canon) in db.rel_iter::<(usize, usize)>("struct_id_to_canonical") {
        struct_canonical.insert(*orig, *canon);
    }

    let mut param_is_pointer: HashSet<(Address, RTLReg)> = HashSet::new();
    for (addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param_is_pointer") {
        param_is_pointer.insert((*addr, *reg));
    }

    let mut func_return: HashMap<Address, RTLReg> = HashMap::new();
    for (addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_return") {
        func_return.insert(*addr, *reg);
    }

    for (addr, name, entry_node) in db.rel_iter::<(Address, Symbol, Node)>("emit_function") {
        let ident = *addr as usize;
        let final_name = if name.starts_with("FUN_") {
            id_to_name
                .get(&ident)
                .cloned()
                .unwrap_or_else(|| name.to_string())
        } else {
            name.to_string()
        };

        let param_regs: Vec<RTLReg> = func_params.get(addr).cloned().unwrap_or_default();

        let param_types: Vec<ParamType> = param_regs
            .iter()
            .enumerate()
            .map(|(pos, reg)| {
                if let Some(xtype) = param_xtypes.get(&(*addr, *reg)) {
                    if !matches!(xtype,
                        XType::Xptr | XType::Xcharptr | XType::Xcharptrptr | XType::Xintptr |
                        XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr | XType::Xlong |
                        XType::Xlongunsigned | XType::Xany64)
                    {
                        return ParamType::Typed(*xtype);
                    }
                }
                if let Some(sid) = var_is_struct.get(&(*addr, *reg)) {
                    let canonical_id = struct_canonical.get(sid).copied().unwrap_or(*sid);
                    ParamType::StructPointer(canonical_id)
                } else if let Some(&canonical_id) = param_struct_by_pos.get(&(*addr, pos)) {
                    ParamType::StructPointer(canonical_id)
                } else if let Some(xtype) = param_xtypes.get(&(*addr, *reg)) {
                    ParamType::Typed(*xtype)
                } else if param_is_pointer.contains(&(*addr, *reg)) {
                    ParamType::Pointer
                } else {
                    ParamType::Integer
                }
            })
            .collect();

        let return_reg = func_return.get(addr).copied();

        let func_data = FunctionData::new(
            *addr,
            final_name,
            param_regs,
            param_types,
            return_reg,
            0,
            *entry_node,
        );
        func_map.insert(*addr, func_data);
    }

    for (head, member) in db.rel_iter::<(Node, Node)>("emit_sseq") {
        if let (Some(fh), Some(fm)) = (node_to_func.get(head), node_to_func.get(member)) {
            if fh == fm {
                if let Some(func) = func_map.get_mut(fh) {
                    func.sseq_groups
                        .entry(*head)
                        .or_insert_with(Vec::new)
                        .push(*member);
                }
            }
        }
    }

    for func in func_map.values_mut() {
        for (head, members) in func.sseq_groups.iter_mut() {
            if !members.contains(head) {
                members.push(*head);
            }
            members.sort();
            members.dedup();
        }
    }

    let goto_targets: HashSet<Node> = db.rel_iter::<(Address, Node)>("emit_goto_target").map(|(_, target)| *target).collect();

    // emit_clight_stmt is multi-valued: instr_in_function lists a shared node (e.g. a compiler-merged abort/error trampoline reached by `jae`/`jb` bounds-check edges from many functions) under EVERY reaching function. Pushing each node's statement into all of them duplicates one function's whole body into every reacher (observed: function 0x1f460's body emitted into 27 functions, each then starting with a spurious abort()). Resolve each node to the single function that CONTAINS it: the nearest preceding entry by address among the functions that claim it (masking the synthetic bit so split nodes resolve like their real address), and emit the statement only under that owner. This mirrors the node_to_func resolution above and in clight_select/query node_to_func.
    const SYNTH_BIT: u64 = 1u64 << 62;
    let mut node_candidate_addrs: HashMap<Node, Vec<Address>> = HashMap::new();
    for (addr, node, _stmt) in db.rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt") {
        node_candidate_addrs.entry(*node).or_default().push(*addr);
    }
    let mut node_owner: HashMap<Node, Address> = HashMap::new();
    for (node, addrs) in &node_candidate_addrs {
        let real = *node & !SYNTH_BIT;
        // Nearest preceding entry: largest claiming addr <= real; if none precedes, the smallest claimant.
        let owner = addrs
            .iter()
            .filter(|&&a| a <= real)
            .max()
            .copied()
            .or_else(|| addrs.iter().min().copied());
        if let Some(owner) = owner {
            node_owner.insert(*node, owner);
        }
    }

    for (addr, node, stmt) in db.rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt") {
        let is_goto_target = goto_targets.contains(node);
        if !is_nonempty_stmt(stmt) && !is_goto_target {
            continue;
        }
        if node_owner.get(node) != Some(addr) {
            continue;
        }
        if let Some(func) = func_map.get_mut(addr) {
            func.node_statements
                .entry(*node)
                .or_insert_with(Vec::new)
                .push(stmt.clone());
        }
    }
    // Vec index 0 is semantic (UNSAT-fallback candidate); sort to lex-smallest debug form so selection is identical across runs despite non-deterministic Ascent set order.
    for func in func_map.values_mut() {
        for stmts in func.node_statements.values_mut() {
            if stmts.len() > 1 {
                stmts.sort_by_cached_key(|s| format!("{:?}", s));
            }
        }
    }

    for (addr, target) in db.rel_iter::<(Address, Node)>("emit_goto_target") {
        if let Some(func) = func_map.get_mut(addr) {
            let label = ident_from_node(*target);
            if let Some(stmts) = func.node_statements.get_mut(target) {
                let has_label = stmts.iter().any(|s| matches!(s, ClightStmt::Slabel(_, _)));
                if !has_label && !stmts.is_empty() {
                    for stmt in stmts.iter_mut() {
                        *stmt = ClightStmt::Slabel(label, Box::new(stmt.clone()));
                    }
                }
            } else {
                func.node_statements
                    .entry(*target)
                    .or_insert_with(Vec::new)
                    .push(ClightStmt::Slabel(label, Box::new(ClightStmt::Sskip)));
            }
        }
    }

    for (from_node, to_node) in db.rel_iter::<(Node, Node)>("emit_next") {
        if let Some(&func_addr) = node_to_func.get(from_node) {
            if let Some(func) = func_map.get_mut(&func_addr) {
                func.successors
                    .entry(*from_node)
                    .or_insert_with(Vec::new)
                    .push(*to_node);
            }
        }
    }
    // Sort successor lists for determinism (emit_next iteration order from parallel Ascent evaluation is not guaranteed).
    for func in func_map.values_mut() {
        for succs in func.successors.values_mut() {
            succs.sort();
            succs.dedup();
        }
    }

    for (addr, ret_type) in db.rel_iter::<(Address, ClightType)>("emit_function_return_type") {
        if let Some(func) = func_map.get_mut(addr) {
            func.return_type = ret_type.clone();
        }
    }

    for (addr, reg) in db.rel_iter::<(Address, RTLReg)>("rtl_reg_used_in_func") {
        if let Some(func) = func_map.get_mut(addr) {
            func.used_regs.insert(*reg);
        }
    }

    // Also collect registers from Clight statements, since variable coalescing can produce IDs differing from rtl_reg_used_in_func, causing missed type candidates.
    for func in func_map.values_mut() {
        let mut clight_regs: Vec<RTLReg> = Vec::new();
        for stmts in func.node_statements.values() {
            for stmt in stmts {
                clight_regs.extend(collect_stmt_regs(stmt));
            }
        }
        for reg in clight_regs {
            func.used_regs.insert(reg);
        }
    }


    for (addr, head, _) in db.rel_iter::<(Address, Node, Node)>("emit_loop_body") {
        if let Some(func) = func_map.get_mut(addr) {
            func.loop_headers.insert(*head);
        }
    }

    for (addr, head, _) in db.rel_iter::<(Address, Node, RTLReg)>("emit_switch_chain") {
        if let Some(func) = func_map.get_mut(addr) {
            func.switch_heads.insert(*head);
        }
    }

    for (addr, struct_id, fields) in db.rel_iter::<(Address, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>)>("emit_struct_fields") {
        if let Some(func) = func_map.get_mut(addr) {
            func.struct_fields.insert(*struct_id, fields.to_vec());
        }
    }


    // Collect ALL type candidates per register and pick the priority-based best. emit_var_type_candidate iteration order is non-deterministic (Ascent set, boxcar insertion order varies across runs). Group first, then pick the best by priority with a deterministic XType tiebreak so the chosen type is the same every run.
    let mut reg_xtypes: HashMap<RTLReg, Vec<XType>> = HashMap::new();
    for (reg, xtype) in db.rel_iter::<(RTLReg, XType)>("emit_var_type_candidate") {
        reg_xtypes.entry(*reg).or_default().push(xtype.clone());
    }
    let mut reg_all_type_strs: HashMap<RTLReg, Vec<String>> = HashMap::new();
    let mut reg_best_xtype_val: HashMap<RTLReg, XType> = HashMap::new();
    for (reg, mut tys) in reg_xtypes {
        tys.sort();
        tys.dedup();
        let mut strs: Vec<String> = tys.iter().map(xtype_to_string).collect();
        strs.sort();
        strs.dedup();
        reg_all_type_strs.insert(reg, strs);

        let best = tys
            .iter()
            .max_by(|a, b| {
                xtype_priority(a)
                    .cmp(&xtype_priority(b))
                    .then_with(|| a.cmp(b))
            })
            .cloned()
            .expect("non-empty after grouping");
        let best_str = xtype_to_string(&best);
        for func in func_map.values_mut() {
            if func.used_regs.contains(&reg) || func.param_regs.contains(&reg) {
                func.var_types.insert(reg, best_str.clone());
            }
        }
        reg_best_xtype_val.insert(reg, best);
    }

    // Upgrade param types using emit_var_type_candidate (includes XstructPtr from ClightFieldPass) which provides struct pointer info unavailable at signature resolution time. Only upgrade FROM 64-bit generic placeholder types or generic pointer; preserve explicit semantic types: both narrow scalar (Xint for argc, Xint8signed, etc.) AND specific pointer types (Xcharptr, Xcharptrptr, Xfuncptr) from known signatures. Otherwise an XstructPtr candidate from generic load analysis would clobber the right type (e.g. main's int argc -> struct *).
    for func in func_map.values_mut() {
        for (i, reg) in func.param_regs.clone().iter().enumerate() {
            if let Some(best_xtype) = reg_best_xtype_val.get(reg) {
                let current = func.param_types.get(i);
                let should_upgrade = match (current, best_xtype) {
                    // Upgrade from 64-bit register-width placeholders (long/any64/ptr) to struct pointer.
                    (Some(ParamType::Typed(
                        XType::Xlong | XType::Xlongunsigned |
                        XType::Xany64 |
                        XType::Xptr
                    )), XType::XstructPtr(sid)) => Some(ParamType::StructPointer(*sid)),
                    (Some(ParamType::Pointer), XType::XstructPtr(sid)) => Some(ParamType::StructPointer(*sid)),
                    (Some(ParamType::Integer), XType::XstructPtr(sid)) => Some(ParamType::StructPointer(*sid)),
                    // Upgrade Xlong (64-bit generic) to pointer when load analysis says it's a ptr. Xint stays Xint: int->ptr upgrade would clobber explicit `int argc` etc.
                    (Some(ParamType::Typed(XType::Xlong)), XType::Xptr | XType::Xcharptr | XType::Xintptr) => Some(ParamType::Pointer),
                    _ => None,
                };
                if let Some(new_type) = should_upgrade {
                    if i < func.param_types.len() {
                        func.param_types[i] = new_type;
                    }
                }
            }
        }
    }

    // Populate reg_struct_ids BEFORE building candidates so ptr_struct_X candidates exist for struct-pointer regs; otherwise the selector falls back to ptr_int/ptr_char/ptr_void and emits `*(int *)p1` instead of `p1->ofs_0`.
    for (addr, reg, id) in db.rel_iter::<(Address, RTLReg, usize)>("reg_to_struct_id") {
        if let Some(func) = func_map.get_mut(addr) {
            let canonical_id = struct_canonical.get(id).copied().unwrap_or(*id);
            func.reg_struct_ids.insert(*reg, canonical_id);
        }
    }

    // Store all type candidates per register (sorted by priority, best first) and pad with same-size-class alternatives so clang_refine can search across ptr/int within the same width.
    for func in func_map.values_mut() {
        let all_regs: Vec<RTLReg> = func.used_regs.iter().copied()
            .chain(func.param_regs.iter().copied())
            .collect();
        for reg in all_regs {
            let mut candidates: Vec<String> = reg_all_type_strs
                .get(&reg)
                .cloned()
                .unwrap_or_default();

            // Add struct pointer candidate if this register is a known struct base
            if let Some(&sid) = func.reg_struct_ids.get(&reg) {
                let struct_str = format!("ptr_struct_{:x}", sid);
                if !candidates.contains(&struct_str) {
                    candidates.push(struct_str);
                }
            }

            // Determine size class from existing candidates; float registers keep only float types.
            let has_64 = candidates.iter().any(|s|
                s == "int_I64" || s == "int_U64"
                || s.starts_with("ptr_"));
            let has_32 = candidates.iter().any(|s|
                s == "int_I32" || s == "int_U32");
            let has_float = candidates.iter().any(|s|
                s.starts_with("float_"));
            let has_ptr = candidates.iter().any(|s| s.starts_with("ptr_"));

            if !has_float {
                if has_64 || (!has_32 && !has_float) {
                    // Always ensure int_I64 is available for 64-bit registers
                    let s = "int_I64".to_string();
                    if !candidates.contains(&s) {
                        candidates.push(s);
                    }
                    // Add pointer declaration alternatives only when the register has pointer evidence from the pipeline.
                    if has_ptr {
                        for alt in ["ptr_int", "ptr_char", "ptr_void"] {
                            let s = alt.to_string();
                            if !candidates.contains(&s) {
                                candidates.push(s);
                            }
                        }
                    }
                }
                if has_32 && !has_64 {
                    let s = "int_I32".to_string();
                    if !candidates.contains(&s) {
                        candidates.push(s);
                    }
                }
            }

            if candidates.len() > 1 {
                candidates.sort_by(|a, b|
                    type_str_sort_priority(b).cmp(&type_str_sort_priority(a))
                        .then_with(|| a.cmp(b))
                );
                func.var_type_candidates.insert(reg, candidates);
            }
        }
    }

    for (node, mreg, rtl_reg) in db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl") {
        if let Some(&func_addr) = node_to_func.get(node) {
            if let Some(func) = func_map.get_mut(&func_addr) {
                func.reg_to_mreg.insert(*rtl_reg, *mreg);
            }
        }
    }

    // Build callee signature map from extern and internal function signatures
    {
        let callee_sigs = extract_callee_signatures(db, &param_xtypes, &rtl_to_mreg_at_entry);
        for func in func_map.values_mut() {
            func.callee_signatures = callee_sigs.clone();
        }
    }

    // TR-3: only 64-bit non-pointer scalar fields get a pointer alternative; narrower fields can't hold a pointer on LP64, and already-pointer fields need no re-selection. Keys mirror solve.rs::field_key_of_lvalue so candidate and evidence keys always agree.
    for func in func_map.values_mut() {
        let cands = collect_struct_field_type_candidates(
            func.node_statements.values().flat_map(|v| v.iter()),
        );
        if !cands.is_empty() {
            func.struct_field_type_candidates = cands;
        }
    }

    {
        let mut name_to_best_addr: HashMap<String, Address> = HashMap::new();
        for (addr, func) in func_map.iter() {
            let entry = name_to_best_addr.entry(func.name.clone());
            match entry {
                std::collections::hash_map::Entry::Vacant(e) => { e.insert(*addr); }
                std::collections::hash_map::Entry::Occupied(mut e) => {
                    let existing_addr = *e.get();
                    let existing_count = func_map[&existing_addr].node_statements.len();
                    let new_count = func.node_statements.len();
                    // Tie-break on address: without it, equal-count name twins keep whichever HashMap iteration order placed first per run.
                    if new_count > existing_count
                        || (new_count == existing_count && *addr < existing_addr)
                    {
                        e.insert(*addr);
                    }
                }
            }
        }
        let keep_addrs: HashSet<Address> = name_to_best_addr.into_values().collect();
        func_map.retain(|addr, _| keep_addrs.contains(addr));
    }

    let mut addresses: Vec<_> = func_map.keys().copied().collect();
    addresses.sort();

    for addr in addresses {
        if let Some(func) = func_map.remove(&addr) {
            functions.push(func);
        }
    }

    Ok((functions, id_to_name))
}

fn is_valid_ascii_content(bytes: &[u8]) -> bool {
    if bytes.is_empty() {
        return false;
    }
    for &b in bytes {
        if b == 0 {
            return true;
        }
        let is_printable = (b >= 0x20 && b <= 0x7E) || b == b'\n' || b == b'\r' || b == b'\t' || b == 0x1b;
        if !is_printable {
            return false;
        }
    }
    true
}

// A section is "allocated" (gets a runtime address) when SHF_ALLOC is set for ELF; non-allocated sections (.comment, .note.*, .debug_*) live at sh_addr=0 and are never valid pointer targets. For non-ELF formats, fall back to a nonzero load address.
fn section_is_allocated(section: &object::Section) -> bool {
    match section.flags() {
        object::SectionFlags::Elf { sh_flags } => {
            sh_flags & u64::from(object::elf::SHF_ALLOC) != 0
        }
        _ => section.address() != 0,
    }
}

fn is_string_literal(bytes: &[u8]) -> Option<usize> {
    let null_pos = bytes.iter().position(|&b| b == 0)?;

    let str_bytes = &bytes[0..null_pos];

    if str_bytes.is_empty() {
        return None;
    }

    for &b in str_bytes {
        let is_printable = (b >= 0x20 && b <= 0x7E)
            || b == b'\n' || b == b'\r' || b == b'\t'
            || b >= 0x80;
        if !is_printable {
            return None;
        }
    }

    if str_bytes.iter().any(|&b| b >= 0x80) {
        if std::str::from_utf8(str_bytes).is_err() {
            return None;
        }
    }

    Some(null_pos + 1)
}

fn try_read_float32(remaining: &[u8]) -> Option<ScalarConstant> {
    if remaining.len() < 4 { return None; }
    let bytes: [u8; 4] = remaining[..4].try_into().ok()?;
    let val = f32::from_le_bytes(bytes);
    if val.is_finite() { Some(ScalarConstant::Float32(val)) } else { None }
}

fn try_read_float64(remaining: &[u8]) -> Option<ScalarConstant> {
    if remaining.len() < 8 { return None; }
    let bytes: [u8; 8] = remaining[..8].try_into().ok()?;
    let val = f64::from_le_bytes(bytes);
    if val.is_finite() { Some(ScalarConstant::Float64(val)) } else { None }
}

fn resolve_rodata_scalar(
    addr: u64,
    global_chunks: &HashMap<usize, MemoryChunk>,
    id: usize,
    rodata_ranges: &[(u64, u64, Vec<u8>)],
) -> Option<ScalarConstant> {
    let chunk = global_chunks.get(&id)?;

    // Find the rodata section containing this address
    let (sect_start, _sect_end, sect_data) = rodata_ranges
        .iter()
        .find(|(start, end, _)| addr >= *start && addr < *end)?;

    let offset = (addr - sect_start) as usize;
    let remaining = &sect_data[offset..];

    match chunk {
        MemoryChunk::MFloat32 => try_read_float32(remaining),
        // MFloat64 is authoritative: never fall back to f32; the old fallback was wrong because non-finite doubles fail the is_finite gate and inlined a bogus 0.0f. Mixed-width access is already resolved (global_chunks keeps smallest chunk), and a failed read yields None so the global stays a symbol reference.
        MemoryChunk::MFloat64 => try_read_float64(remaining),
        MemoryChunk::MInt32 if remaining.len() >= 4 => {
            let bytes: [u8; 4] = remaining[..4].try_into().ok()?;
            let val = i32::from_le_bytes(bytes);
            Some(ScalarConstant::Int32(val))
        }
        MemoryChunk::MInt64 if remaining.len() >= 8 => {
            let bytes: [u8; 8] = remaining[..8].try_into().ok()?;
            let val = i64::from_le_bytes(bytes);
            Some(ScalarConstant::Int64(val))
        }
        _ => None,
    }
}

pub fn extract_globals(db: &DecompileDB, binary_path: &Path) -> Result<Vec<GlobalData>, String> {
    let mut globals = Vec::new();

    // Globals can have multiple symbols at one address (e.g. glibc weak aliases like __progname_full / program_invocation_name). HashMap::insert with non-deterministic iteration would pick a different alias each run, which then flips the type because known_global_type matches by name. Collect candidates, then pick the lex-smallest name per id so it's stable.
    let mut ident_name_candidates: HashMap<usize, Vec<String>> = HashMap::new();
    for (id, name) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
        ident_name_candidates.entry(*id).or_default().push(name.to_string());
    }
    let mut symbol_name_candidates: HashMap<usize, Vec<String>> = HashMap::new();
    for (addr, name, _) in db.rel_iter::<(Address, Symbol, Symbol)>("symbols") {
        symbol_name_candidates.entry(*addr as usize).or_default().push(name.to_string());
    }
    let mut id_to_name: HashMap<usize, String> = HashMap::new();
    for (id, mut names) in ident_name_candidates {
        names.sort();
        id_to_name.insert(id, names.into_iter().next().unwrap());
    }
    // ELF symbols are authoritative: override ident_to_symbol entries.
    for (id, mut names) in symbol_name_candidates {
        names.sort();
        id_to_name.insert(id, names.into_iter().next().unwrap());
    }

    let global_ptr_ids: std::collections::HashSet<usize> = db.rel_iter::<(Ident,)>("emit_global_is_ptr")
        .map(|(id,)| *id)
        .collect();

    let bin_data = fs::read(binary_path).map_err(|e| format!("Failed to read binary: {}", e))?;
    let obj_file = object::File::parse(&*bin_data).map_err(|e| format!("Failed to parse binary: {}", e))?;


    let func_addrs: HashSet<usize> = {
        let mut addrs = HashSet::new();
        for (addr, _, _) in db.rel_iter::<(Address, Symbol, Node)>("emit_function") {
            addrs.insert(*addr as usize);
        }
        for (addr,) in db.rel_iter::<(Address,)>("is_external_function") {
            addrs.insert(*addr as usize);
        }
        // Pre-build symbol-to-idents map for O(1) lookup
        let mut symbol_to_idents: HashMap<Symbol, Vec<Ident>> = HashMap::new();
        for (id, sym) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
            symbol_to_idents.entry(*sym).or_default().push(*id);
        }
        for (name, _, _, _) in db.rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("resolved_extern_signature") {
            if let Some(idents) = symbol_to_idents.get(name) {
                for &id in idents {
                    addrs.insert(id);
                }
            }
        }
        for (name,) in db.rel_iter::<(Symbol,)>("unknown_extern") {
            if let Some(idents) = symbol_to_idents.get(name) {
                for &id in idents {
                    addrs.insert(id);
                }
            }
        }
        addrs
    };

    // Build map of global load chunk types for rodata constant resolution. A literal in .rodata can be loaded with multiple chunks (e.g. as Float32 and Float64), so the relation carries several rows per id. Pick the smallest chunk by Ord so the resolved scalar value is stable across runs.
    let global_chunks: HashMap<usize, MemoryChunk> = {
        let mut groups: HashMap<usize, Vec<MemoryChunk>> = HashMap::new();
        for (id, chunk) in db.rel_iter::<(Ident, MemoryChunk)>("global_load_chunk") {
            groups.entry(*id).or_default().push(*chunk);
        }
        groups
            .into_iter()
            .map(|(id, mut chunks)| {
                chunks.sort();
                (id, chunks[0])
            })
            .collect()
    };

    // Build set of read-only section address ranges
    let rodata_ranges: Vec<(u64, u64, Vec<u8>)> = obj_file
        .sections()
        .filter(|s| matches!(s.kind(), object::SectionKind::ReadOnlyData | object::SectionKind::ReadOnlyString))
        .filter_map(|s| {
            s.data().ok().map(|d| (s.address(), s.address() + s.size(), d.to_vec()))
        })
        .collect();

    let string_data_map: HashMap<String, String> = db
        .rel_iter::<(String, String, usize)>("string_data")
        .map(|(label, content, _)| (label.clone(), content.clone()))
        .collect();
    let mut string_addr_map: Vec<(u64, String)> = Vec::new();
    for (label, content, _) in db.rel_iter::<(String, String, usize)>("string_data") {
        if let Some(hex) = label.strip_prefix("L_").or_else(|| label.strip_prefix(".L_")) {
            if let Ok(addr) = u64::from_str_radix(hex, 16) {
                string_addr_map.push((addr, content.clone()));
            }
        }
    }
    string_addr_map.sort_by_key(|(addr, _)| *addr);

    for (id,) in db.rel_iter::<(usize,)>("global_var_ref") {
        if func_addrs.contains(id) {
            continue;
        }
        let name = id_to_name
            .get(id)
            .cloned()
            .unwrap_or_else(|| format!("global_{}", id));

        let addr = *id as u64;
        let mut is_string = false;
        let mut content = Vec::new();
        let is_pointer = global_ptr_ids.contains(id);

        // Pointer globals are never string literals; skip all string detection for them.
        if !is_pointer {
            if let Some(str_content) = string_data_map.get(&name) {
                if is_valid_ascii_content(str_content.as_bytes()) {
                    is_string = true;
                    content = str_content.as_bytes().to_vec();
                    content.push(0);
                }
            }

            if !is_string {
                let idx = string_addr_map.partition_point(|(start, _)| *start <= addr);
                if idx > 0 {
                    let (start, str_content) = &string_addr_map[idx - 1];
                    let offset = (addr - start) as usize;
                    if offset == 0 {
                        let candidate = str_content.as_bytes();
                        if is_valid_ascii_content(candidate) {
                            is_string = true;
                            content = candidate.to_vec();
                            content.push(0);
                        }
                    } else if offset < str_content.len() {
                        let candidate = str_content[offset..].as_bytes();
                        if is_valid_ascii_content(candidate) {
                            is_string = true;
                            content = candidate.to_vec();
                            content.push(0);
                        }
                    }
                }
            }
        }

        // Try to resolve scalar constants from .rodata before string detection, since float constants (e.g. 3.0f) start with 0x00 and would be misidentified as empty strings.
        let scalar_value = if !is_string && !is_pointer {
            resolve_rodata_scalar(addr, &global_chunks, *id, &rodata_ranges)
        } else {
            None
        };

        // Pointer globals (GOT / .data.rel.ro / .bss fn-ptr slots) must never be classified as string literals: their file bytes are zero (relocated at load time), so a leading 0x00 byte (or a lone \0, zero-initialized data) does NOT mean "empty string"; emit it as a normal scalar/pointer global instead of "".
        if !is_string && scalar_value.is_none() && !is_pointer {
            for section in obj_file.sections() {
                 // A global_var_ref id is a runtime address, which only loaded (SHF_ALLOC) sections have; non-allocated metadata sections (.comment, .note, .debug_*) sit at sh_addr=0, so a small integer constant that became a global ref would otherwise resolve into their bytes (e.g. .comment's toolchain version string) and render as that substring. Skip them.
                 if !section_is_allocated(&section) {
                     continue;
                 }
                 let sect_addr = section.address();
                 let sect_size = section.size();

                 if addr >= sect_addr && addr < sect_addr + sect_size {
                     if let Ok(data) = section.data() {
                         let offset = (addr - sect_addr) as usize;
                         if offset < data.len() {
                             // Scan to NUL bounded by the section end, not a fixed window: is_string_literal requires a NUL inside the slice, so a >128-byte string under a fixed window would be missed entirely (this was the bug). Cheap on non-strings because is_string_literal bails at the first non-printable byte.
                             let remaining = &data[offset..];
                             if let Some(len) = is_string_literal(remaining) {
                                 is_string = true;
                                 content = remaining[0..len].to_vec();
                             }
                         }
                     }
                     break;
                 }
            }
        }

        globals.push(GlobalData {
            id: *id,
            name,
            is_string,
            content,
            is_pointer,
            scalar_value,
        });
    }

    globals.sort_by_key(|g| g.id);

    Ok(globals)
}

use crate::decompile::passes::c_pass::types::{CType, FloatSize, IntSize, Signedness, StructDef, StructField, TypeQualifiers};
use crate::x86::types::FieldType;
use crate::x86::op::Condition;
use std::sync::Arc;

#[derive(Debug, Clone)]
pub struct PrimaryExitData {
    #[allow(dead_code)]
    pub exit_node: Node,
    #[allow(dead_code)]
    pub condition: Condition,
    #[allow(dead_code)]
    pub args: Arc<Vec<CsharpminorExpr>>,
    #[allow(dead_code)]
    pub inverted: bool,
}

#[derive(Debug, Clone, Default)]
pub struct LoopInfo {
    pub body_nodes: Vec<Node>,
    pub exit_node: Option<Node>,
    pub step_node: Option<Node>,
    pub primary_exit: Option<PrimaryExitData>,
    /// Pre-built break statements for non-primary loop exits, mapping exit_node to ClightStmt (typically Sifthenelse(cond, Sbreak, Sskip)).
    pub break_stmts: HashMap<Node, ClightStmt>,
    /// Non-primary exits whose target flows to a function return (exit_node -> (value_node, ret_node)); select tail-duplicates value_node + ret_node's return into the exit branch instead of a valueless break (A5 dead-return-overwrite fix).
    pub exit_returns: HashMap<Node, (Node, Node)>,
}

// RB-5: loop_exit_branch / emit_break_stmt may carry several rows per (func, header, exit_node); pick deterministically by explicit priority (ascending): (1) fabricated-operand count -- real mreg-backed values beat DEFAULT_VAR sentinels and Mreg::Unknown temporaries; (2) Tvoid-subexpr count -- prefer fully-typed; (3) structural node count -- most direct derivation; (4) full structural order -- total, so tied candidates resolve without consulting Debug output.

use std::cmp::Ordering;

/// Low-6-bit mreg discriminant for fresh_xtl_reg when the backing Mreg is `Unknown` / "RTEMP" (rtl_pass::mreg_discriminant).
const MREG_UNKNOWN_DISCRIMINANT: u64 = 33;

/// True for RTL register ids that do not carry a machine-register-backed value (DEFAULT_VAR sentinel or Unknown/RTEMP-backed temporaries).
fn is_fabricated_operand(reg: RTLReg) -> bool {
    if reg == crate::util::DEFAULT_VAR as RTLReg {
        return true;
    }
    // fresh_xtl_reg encoding: bit 63 | optional namespace bits | (node << 6) | mreg id.
    (reg >> 63) == 1 && (reg & 0x3F) == MREG_UNKNOWN_DISCRIMINANT
}

/// (fabricated-operand count, structural node count) over a Csharpminor expr tree.
fn csharp_expr_stats(e: &CsharpminorExpr) -> (u32, u32) {
    match e {
        CsharpminorExpr::Evar(reg) => (is_fabricated_operand(*reg) as u32, 1),
        CsharpminorExpr::Eaddrof(_) | CsharpminorExpr::Econst(_) => (0, 1),
        CsharpminorExpr::Eunop(_, x) => {
            let (f, s) = csharp_expr_stats(x);
            (f, s + 1)
        }
        CsharpminorExpr::Ebinop(_, l, r) => {
            let (fl, sl) = csharp_expr_stats(l);
            let (fr, sr) = csharp_expr_stats(r);
            (fl + fr, sl + sr + 1)
        }
        CsharpminorExpr::Eload(_, x) => {
            let (f, s) = csharp_expr_stats(x);
            (f, s + 1)
        }
        CsharpminorExpr::Econdition(c, t, f_) => {
            let (fc, sc) = csharp_expr_stats(c);
            let (ft, st) = csharp_expr_stats(t);
            let (ff, sf) = csharp_expr_stats(f_);
            (fc + ft + ff, sc + st + sf + 1)
        }
    }
}

fn csharp_args_stats(args: &[CsharpminorExpr]) -> (u32, u32) {
    args.iter().map(csharp_expr_stats).fold((0, 0), |(fa, sa), (f, s)| (fa + f, sa + s))
}

/// (fabricated, void-typed, size) accumulated over a Clight expr tree.
fn clight_expr_stats(e: &ClightExpr, acc: &mut (u32, u32, u32)) {
    let node_ty = match e {
        ClightExpr::EconstInt(_, ty)
        | ClightExpr::EconstFloat(_, ty)
        | ClightExpr::EconstSingle(_, ty)
        | ClightExpr::EconstLong(_, ty)
        | ClightExpr::Evar(_, ty)
        | ClightExpr::EvarSymbol(_, ty)
        | ClightExpr::Etempvar(_, ty)
        | ClightExpr::Ederef(_, ty)
        | ClightExpr::Eaddrof(_, ty)
        | ClightExpr::Eunop(_, _, ty)
        | ClightExpr::Ebinop(_, _, _, ty)
        | ClightExpr::Ecast(_, ty)
        | ClightExpr::Efield(_, _, ty)
        | ClightExpr::Esizeof(_, ty)
        | ClightExpr::Ealignof(_, ty)
        | ClightExpr::Econdition(_, _, _, ty) => ty,
    };
    if matches!(node_ty, ClightType::Tvoid) {
        acc.1 += 1;
    }
    acc.2 += 1;
    match e {
        ClightExpr::Etempvar(id, _) => {
            if is_fabricated_operand(*id as RTLReg) {
                acc.0 += 1;
            }
        }
        ClightExpr::Ederef(x, _)
        | ClightExpr::Eaddrof(x, _)
        | ClightExpr::Eunop(_, x, _)
        | ClightExpr::Ecast(x, _)
        | ClightExpr::Efield(x, _, _) => clight_expr_stats(x, acc),
        ClightExpr::Ebinop(_, l, r, _) => {
            clight_expr_stats(l, acc);
            clight_expr_stats(r, acc);
        }
        ClightExpr::Econdition(c, t, f, _) => {
            clight_expr_stats(c, acc);
            clight_expr_stats(t, acc);
            clight_expr_stats(f, acc);
        }
        _ => {}
    }
}

/// (fabricated, void-typed, size) accumulated over a Clight stmt tree.
fn clight_stmt_stats(stmt: &ClightStmt, acc: &mut (u32, u32, u32)) {
    acc.2 += 1;
    match stmt {
        ClightStmt::Sskip | ClightStmt::Sbreak | ClightStmt::Scontinue | ClightStmt::Sgoto(_) => {}
        ClightStmt::Sassign(l, r) => {
            clight_expr_stats(l, acc);
            clight_expr_stats(r, acc);
        }
        ClightStmt::Sset(_, e) => clight_expr_stats(e, acc),
        ClightStmt::Scall(_, f, args) => {
            clight_expr_stats(f, acc);
            for a in args {
                clight_expr_stats(a, acc);
            }
        }
        ClightStmt::Sbuiltin(_, _, _, args) => {
            for a in args {
                clight_expr_stats(a, acc);
            }
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss {
                clight_stmt_stats(s, acc);
            }
        }
        ClightStmt::Sifthenelse(c, t, f) => {
            clight_expr_stats(c, acc);
            clight_stmt_stats(t, acc);
            clight_stmt_stats(f, acc);
        }
        ClightStmt::Sloop(b, s) => {
            clight_stmt_stats(b, acc);
            clight_stmt_stats(s, acc);
        }
        ClightStmt::Sreturn(e) => {
            if let Some(e) = e {
                clight_expr_stats(e, acc);
            }
        }
        ClightStmt::Sswitch(e, cases) => {
            clight_expr_stats(e, acc);
            for (_, s) in cases {
                clight_stmt_stats(s, acc);
            }
        }
        ClightStmt::Slabel(_, s) => clight_stmt_stats(s, acc),
    }
}

/// Length-first lexicographic order over slices with an element comparator.
fn cmp_slice<T>(a: &[T], b: &[T], f: impl Fn(&T, &T) -> Ordering) -> Ordering {
    a.len().cmp(&b.len()).then_with(|| {
        for (x, y) in a.iter().zip(b.iter()) {
            let o = f(x, y);
            if o != Ordering::Equal {
                return o;
            }
        }
        Ordering::Equal
    })
}

fn cmp_option<T>(a: &Option<T>, b: &Option<T>, f: impl Fn(&T, &T) -> Ordering) -> Ordering {
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (Some(x), Some(y)) => f(x, y),
    }
}

fn cmp_constant(a: &Constant, b: &Constant) -> Ordering {
    use Constant as C;
    let rank = |c: &C| -> u8 {
        match c {
            C::Ointconst(_) => 0,
            C::Ofloatconst(_) => 1,
            C::Osingleconst(_) => 2,
            C::Olongconst(_) => 3,
            C::Oaddrsymbol(_, _) => 4,
            C::Oaddrstack(_) => 5,
        }
    };
    rank(a).cmp(&rank(b)).then_with(|| match (a, b) {
        (C::Ointconst(x), C::Ointconst(y)) => x.cmp(y),
        (C::Ofloatconst(x), C::Ofloatconst(y)) => x.cmp(y), // F64: Ord via total_cmp
        (C::Osingleconst(x), C::Osingleconst(y)) => x.cmp(y), // F32: Ord via total_cmp
        (C::Olongconst(x), C::Olongconst(y)) => x.cmp(y),
        (C::Oaddrsymbol(ia, oa), C::Oaddrsymbol(ib, ob)) => ia.cmp(ib).then(oa.cmp(ob)),
        (C::Oaddrstack(x), C::Oaddrstack(y)) => x.cmp(y),
        _ => Ordering::Equal, // unreachable: equal ranks imply the same variant
    })
}

/// Total order key for CminorBinop: (variant rank, comparison payload).
fn cminor_binop_key(op: &CminorBinop) -> (u8, u8) {
    use CminorBinop as B;
    match op {
        B::Oadd => (0, 0), B::Osub => (1, 0), B::Omul => (2, 0), B::Odiv => (3, 0),
        B::Odivu => (4, 0), B::Omod => (5, 0), B::Omodu => (6, 0), B::Oand => (7, 0),
        B::Oor => (8, 0), B::Oxor => (9, 0), B::Oshl => (10, 0), B::Oshr => (11, 0),
        B::Oshru => (12, 0), B::Oaddf => (13, 0), B::Osubf => (14, 0), B::Omulf => (15, 0),
        B::Odivf => (16, 0), B::Oaddfs => (17, 0), B::Osubfs => (18, 0), B::Omulfs => (19, 0),
        B::Odivfs => (20, 0), B::Omaxf => (21, 0), B::Ominf => (22, 0), B::Oaddl => (23, 0),
        B::Osubl => (24, 0), B::Omull => (25, 0), B::Odivl => (26, 0), B::Odivlu => (27, 0),
        B::Omodl => (28, 0), B::Omodlu => (29, 0), B::Oandl => (30, 0), B::Oorl => (31, 0),
        B::Oxorl => (32, 0), B::Oshll => (33, 0), B::Oshrl => (34, 0), B::Oshrlu => (35, 0),
        B::Omulhs => (36, 0), B::Omulhu => (37, 0), B::Omullhs => (38, 0), B::Omullhu => (39, 0),
        B::Ocmp(c) => (40, *c as u8), B::Ocmpu(c) => (41, *c as u8),
        B::Ocmpf(c) => (42, *c as u8), B::Ocmpnotf(c) => (43, *c as u8),
        B::Ocmpfs(c) => (44, *c as u8), B::Ocmpnotfs(c) => (45, *c as u8),
        B::Ocmpl(c) => (46, *c as u8), B::Ocmplu(c) => (47, *c as u8),
    }
}

fn cmp_csharp_expr(a: &CsharpminorExpr, b: &CsharpminorExpr) -> Ordering {
    use CsharpminorExpr as E;
    let rank = |e: &E| -> u8 {
        match e {
            E::Evar(_) => 0,
            E::Eaddrof(_) => 1,
            E::Econst(_) => 2,
            E::Eunop(_, _) => 3,
            E::Ebinop(_, _, _) => 4,
            E::Eload(_, _) => 5,
            E::Econdition(_, _, _) => 6,
        }
    };
    rank(a).cmp(&rank(b)).then_with(|| match (a, b) {
        (E::Evar(x), E::Evar(y)) => x.cmp(y),
        (E::Eaddrof(x), E::Eaddrof(y)) => x.cmp(y),
        (E::Econst(x), E::Econst(y)) => cmp_constant(x, y),
        (E::Eunop(oa, xa), E::Eunop(ob, xb)) => {
            // CminorUnop is fieldless: the integer cast is its variant rank.
            (oa.clone() as u8).cmp(&(ob.clone() as u8)).then_with(|| cmp_csharp_expr(xa, xb))
        }
        (E::Ebinop(oa, la, ra), E::Ebinop(ob, lb, rb)) => cminor_binop_key(oa)
            .cmp(&cminor_binop_key(ob))
            .then_with(|| cmp_csharp_expr(la, lb))
            .then_with(|| cmp_csharp_expr(ra, rb)),
        (E::Eload(ca, xa), E::Eload(cb, xb)) => {
            ca.cmp(cb).then_with(|| cmp_csharp_expr(xa, xb))
        }
        (E::Econdition(ca, ta, fa), E::Econdition(cb, tb, fb)) => cmp_csharp_expr(ca, cb)
            .then_with(|| cmp_csharp_expr(ta, tb))
            .then_with(|| cmp_csharp_expr(fa, fb)),
        _ => Ordering::Equal, // unreachable: equal ranks imply the same variant
    })
}

fn cmp_clight_attr(a: &ClightAttr, b: &ClightAttr) -> Ordering {
    a.attr_volatile
        .cmp(&b.attr_volatile)
        .then_with(|| a.attr_alignas.cmp(&b.attr_alignas))
}

fn cmp_clight_type(a: &ClightType, b: &ClightType) -> Ordering {
    use ClightType as T;
    let rank = |t: &T| -> u8 {
        match t {
            T::Tvoid => 0,
            T::Tint(_, _, _) => 1,
            T::Tlong(_, _) => 2,
            T::Tfloat(_, _) => 3,
            T::Tpointer(_, _) => 4,
            T::Tarray(_, _, _) => 5,
            T::Tfunction(_, _, _) => 6,
            T::Tstruct(_, _) => 7,
            T::Tunion(_, _) => 8,
        }
    };
    rank(a).cmp(&rank(b)).then_with(|| match (a, b) {
        (T::Tint(sa, ga, aa), T::Tint(sb, gb, ab)) => (*sa as u8)
            .cmp(&(*sb as u8))
            .then((*ga as u8).cmp(&(*gb as u8)))
            .then_with(|| cmp_clight_attr(aa, ab)),
        (T::Tlong(ga, aa), T::Tlong(gb, ab)) => {
            (*ga as u8).cmp(&(*gb as u8)).then_with(|| cmp_clight_attr(aa, ab))
        }
        (T::Tfloat(fa, aa), T::Tfloat(fb, ab)) => {
            (*fa as u8).cmp(&(*fb as u8)).then_with(|| cmp_clight_attr(aa, ab))
        }
        (T::Tpointer(ta, aa), T::Tpointer(tb, ab)) => {
            cmp_clight_type(ta, tb).then_with(|| cmp_clight_attr(aa, ab))
        }
        (T::Tarray(ta, na, aa), T::Tarray(tb, nb, ab)) => cmp_clight_type(ta, tb)
            .then(na.cmp(nb))
            .then_with(|| cmp_clight_attr(aa, ab)),
        (T::Tfunction(pa, ra, ca), T::Tfunction(pb, rb, cb)) => {
            cmp_slice(pa, pb, cmp_clight_type)
                .then_with(|| cmp_clight_type(ra, rb))
                .then_with(|| ca.cmp(cb)) // CallConv: derived Ord
        }
        (T::Tstruct(ia, aa), T::Tstruct(ib, ab)) | (T::Tunion(ia, aa), T::Tunion(ib, ab)) => {
            ia.cmp(ib).then_with(|| cmp_clight_attr(aa, ab))
        }
        _ => Ordering::Equal, // unreachable: equal ranks imply the same variant
    })
}

fn cmp_clight_expr(a: &ClightExpr, b: &ClightExpr) -> Ordering {
    use ClightExpr as E;
    let rank = |e: &E| -> u8 {
        match e {
            E::EconstInt(_, _) => 0,
            E::EconstFloat(_, _) => 1,
            E::EconstSingle(_, _) => 2,
            E::EconstLong(_, _) => 3,
            E::Evar(_, _) => 4,
            E::EvarSymbol(_, _) => 5,
            E::Etempvar(_, _) => 6,
            E::Ederef(_, _) => 7,
            E::Eaddrof(_, _) => 8,
            E::Eunop(_, _, _) => 9,
            E::Ebinop(_, _, _, _) => 10,
            E::Ecast(_, _) => 11,
            E::Efield(_, _, _) => 12,
            E::Esizeof(_, _) => 13,
            E::Ealignof(_, _) => 14,
            E::Econdition(_, _, _, _) => 15,
        }
    };
    rank(a).cmp(&rank(b)).then_with(|| match (a, b) {
        (E::EconstInt(va, ta), E::EconstInt(vb, tb)) => {
            va.cmp(vb).then_with(|| cmp_clight_type(ta, tb))
        }
        (E::EconstFloat(va, ta), E::EconstFloat(vb, tb)) => va
            .0
            .total_cmp(&vb.0)
            .then_with(|| cmp_clight_type(ta, tb)),
        (E::EconstSingle(va, ta), E::EconstSingle(vb, tb)) => va
            .0
            .total_cmp(&vb.0)
            .then_with(|| cmp_clight_type(ta, tb)),
        (E::EconstLong(va, ta), E::EconstLong(vb, tb)) => {
            va.cmp(vb).then_with(|| cmp_clight_type(ta, tb))
        }
        (E::Evar(ia, ta), E::Evar(ib, tb)) | (E::Etempvar(ia, ta), E::Etempvar(ib, tb)) => {
            ia.cmp(ib).then_with(|| cmp_clight_type(ta, tb))
        }
        (E::EvarSymbol(sa, ta), E::EvarSymbol(sb, tb)) => {
            sa.cmp(sb).then_with(|| cmp_clight_type(ta, tb))
        }
        (E::Ederef(xa, ta), E::Ederef(xb, tb)) | (E::Eaddrof(xa, ta), E::Eaddrof(xb, tb))
        | (E::Ecast(xa, ta), E::Ecast(xb, tb)) => {
            cmp_clight_expr(xa, xb).then_with(|| cmp_clight_type(ta, tb))
        }
        (E::Eunop(oa, xa, ta), E::Eunop(ob, xb, tb)) => (*oa as u8)
            .cmp(&(*ob as u8))
            .then_with(|| cmp_clight_expr(xa, xb))
            .then_with(|| cmp_clight_type(ta, tb)),
        (E::Ebinop(oa, la, ra, ta), E::Ebinop(ob, lb, rb, tb)) => (*oa as u8)
            .cmp(&(*ob as u8))
            .then_with(|| cmp_clight_expr(la, lb))
            .then_with(|| cmp_clight_expr(ra, rb))
            .then_with(|| cmp_clight_type(ta, tb)),
        (E::Efield(xa, ia, ta), E::Efield(xb, ib, tb)) => cmp_clight_expr(xa, xb)
            .then(ia.cmp(ib))
            .then_with(|| cmp_clight_type(ta, tb)),
        (E::Esizeof(ua, ta), E::Esizeof(ub, tb)) | (E::Ealignof(ua, ta), E::Ealignof(ub, tb)) => {
            cmp_clight_type(ua, ub).then_with(|| cmp_clight_type(ta, tb))
        }
        (E::Econdition(ca, xa, ya, ta), E::Econdition(cb, xb, yb, tb)) => cmp_clight_expr(ca, cb)
            .then_with(|| cmp_clight_expr(xa, xb))
            .then_with(|| cmp_clight_expr(ya, yb))
            .then_with(|| cmp_clight_type(ta, tb)),
        _ => Ordering::Equal, // unreachable: equal ranks imply the same variant
    })
}

fn cmp_external_function(a: &ExternalFunction, b: &ExternalFunction) -> Ordering {
    use crate::x86::types::ExternalFunction as F;
    let rank = |f: &F| -> u8 {
        match f {
            F::EFExternal(_, _) => 0,
            F::EFBuiltin(_, _) => 1,
            F::EFRuntime(_, _) => 2,
            F::EFVLoad(_) => 3,
            F::EFVStore(_) => 4,
            F::EFMalloc => 5,
            F::EFFree => 6,
            F::EFMemcpy(_, _) => 7,
            F::EFAnnot(_, _, _) => 8,
            F::EFAnnotVal(_, _, _) => 9,
            F::EFInlineAsm(_, _, _) => 10,
            F::EFDebug(_, _, _) => 11,
        }
    };
    rank(a).cmp(&rank(b)).then_with(|| match (a, b) {
        (F::EFExternal(na, sa), F::EFExternal(nb, sb))
        | (F::EFBuiltin(na, sa), F::EFBuiltin(nb, sb))
        | (F::EFRuntime(na, sa), F::EFRuntime(nb, sb)) => {
            na.cmp(nb).then_with(|| sa.cmp(sb)) // Signature: derived Ord
        }
        (F::EFVLoad(ca), F::EFVLoad(cb)) | (F::EFVStore(ca), F::EFVStore(cb)) => ca.cmp(cb),
        (F::EFMemcpy(xa, ya), F::EFMemcpy(xb, yb)) => xa.cmp(xb).then(ya.cmp(yb)),
        (F::EFAnnot(pa, na, ta), F::EFAnnot(pb, nb, tb)) => {
            pa.cmp(pb).then_with(|| na.cmp(nb)).then_with(|| ta.cmp(tb)) // Vec<Typ>: derived Ord
        }
        (F::EFAnnotVal(pa, na, ta), F::EFAnnotVal(pb, nb, tb)) => {
            pa.cmp(pb).then_with(|| na.cmp(nb)).then(ta.cmp(tb))
        }
        (F::EFInlineAsm(na, sa, ca), F::EFInlineAsm(nb, sb, cb)) => {
            na.cmp(nb).then_with(|| sa.cmp(sb)).then_with(|| ca.cmp(cb))
        }
        (F::EFDebug(pa, ia, ta), F::EFDebug(pb, ib, tb)) => {
            pa.cmp(pb).then(ia.cmp(ib)).then_with(|| ta.cmp(tb))
        }
        _ => Ordering::Equal, // unit variants / unreachable mixed pairs
    })
}

fn cmp_clight_stmt(a: &ClightStmt, b: &ClightStmt) -> Ordering {
    use ClightStmt as S;
    let rank = |s: &S| -> u8 {
        match s {
            S::Sskip => 0,
            S::Sassign(_, _) => 1,
            S::Sset(_, _) => 2,
            S::Scall(_, _, _) => 3,
            S::Sbuiltin(_, _, _, _) => 4,
            S::Ssequence(_) => 5,
            S::Sifthenelse(_, _, _) => 6,
            S::Sloop(_, _) => 7,
            S::Sbreak => 8,
            S::Scontinue => 9,
            S::Sreturn(_) => 10,
            S::Sswitch(_, _) => 11,
            S::Slabel(_, _) => 12,
            S::Sgoto(_) => 13,
        }
    };
    rank(a).cmp(&rank(b)).then_with(|| match (a, b) {
        (S::Sassign(la, ra), S::Sassign(lb, rb)) => {
            cmp_clight_expr(la, lb).then_with(|| cmp_clight_expr(ra, rb))
        }
        (S::Sset(ia, ea), S::Sset(ib, eb)) => ia.cmp(ib).then_with(|| cmp_clight_expr(ea, eb)),
        (S::Scall(ra, fa, aa), S::Scall(rb, fb, ab)) => ra
            .cmp(rb)
            .then_with(|| cmp_clight_expr(fa, fb))
            .then_with(|| cmp_slice(aa, ab, cmp_clight_expr)),
        (S::Sbuiltin(ra, ea, ta, aa), S::Sbuiltin(rb, eb, tb, ab)) => ra
            .cmp(rb)
            .then_with(|| cmp_external_function(ea, eb))
            .then_with(|| cmp_slice(ta, tb, cmp_clight_type))
            .then_with(|| cmp_slice(aa, ab, cmp_clight_expr)),
        (S::Ssequence(sa), S::Ssequence(sb)) => cmp_slice(sa, sb, cmp_clight_stmt),
        (S::Sifthenelse(ca, ta, fa), S::Sifthenelse(cb, tb, fb)) => cmp_clight_expr(ca, cb)
            .then_with(|| cmp_clight_stmt(ta, tb))
            .then_with(|| cmp_clight_stmt(fa, fb)),
        (S::Sloop(ba, sa), S::Sloop(bb, sb)) => {
            cmp_clight_stmt(ba, bb).then_with(|| cmp_clight_stmt(sa, sb))
        }
        (S::Sreturn(ea), S::Sreturn(eb)) => cmp_option(ea, eb, cmp_clight_expr),
        (S::Sswitch(ea, ca), S::Sswitch(eb, cb)) => cmp_clight_expr(ea, eb).then_with(|| {
            cmp_slice(ca, cb, |(la, sa), (lb, sb)| {
                la.cmp(lb).then_with(|| cmp_clight_stmt(sa, sb))
            })
        }),
        (S::Slabel(ia, sa), S::Slabel(ib, sb)) => {
            ia.cmp(ib).then_with(|| cmp_clight_stmt(sa, sb))
        }
        (S::Sgoto(ia), S::Sgoto(ib)) => ia.cmp(ib),
        _ => Ordering::Equal, // unit variants / unreachable mixed pairs
    })
}

/// RB-5 priority order for loop_exit_branch candidates; `Less` is preferred. Dimensions documented above.
fn cmp_exit_branch_cand(
    a: &(Condition, Arc<Vec<CsharpminorExpr>>, bool),
    b: &(Condition, Arc<Vec<CsharpminorExpr>>, bool),
) -> Ordering {
    let (fab_a, size_a) = csharp_args_stats(&a.1);
    let (fab_b, size_b) = csharp_args_stats(&b.1);
    fab_a
        .cmp(&fab_b) // 1. real operands beat fabricated ones
        .then(size_a.cmp(&size_b)) // 3. most direct derivation
        .then_with(|| a.0.cmp(&b.0)) // 4. structural: Condition (derived Ord), ...
        .then_with(|| cmp_slice(&a.1, &b.1, cmp_csharp_expr)) // ... args, ...
        .then_with(|| a.2.cmp(&b.2)) // ... inverted flag
}

/// Priority order for emit_break_stmt candidates at one exit node; `Less` is preferred.
fn cmp_break_stmt_cand(a: &ClightStmt, b: &ClightStmt) -> Ordering {
    let mut ka = (0u32, 0u32, 0u32);
    let mut kb = (0u32, 0u32, 0u32);
    clight_stmt_stats(a, &mut ka);
    clight_stmt_stats(b, &mut kb);
    // (fabricated, void-typed, size) ascending, then the full structural order.
    ka.cmp(&kb).then_with(|| cmp_clight_stmt(a, b))
}

pub fn extract_loop_info(db: &DecompileDB) -> HashMap<Address, HashMap<Node, LoopInfo>> {
    let mut result: HashMap<Address, HashMap<Node, LoopInfo>> = HashMap::new();


    for (func_addr, loop_head, body_node) in db.rel_iter::<(Address, Node, Node)>("emit_loop_body") {
        if body_node != loop_head {
            result
                .entry(*func_addr)
                .or_default()
                .entry(*loop_head)
                .or_insert_with(LoopInfo::default)
                .body_nodes
                .push(*body_node);
        }
    }

    for (func_addr, loop_head, exit_node, _, _, _, _) in db.rel_iter::<(Address, Node, Node, Condition, Arc<Vec<CsharpminorExpr>>, Node, Node)>("emit_loop_exit") {
        // emit_loop_exit is multi-valued for loops with several exit branches; Ascent set order is non-deterministic, so keep the smallest exit node.
        let info = result
            .entry(*func_addr)
            .or_default()
            .entry(*loop_head)
            .or_insert_with(LoopInfo::default);
        info.exit_node = Some(match info.exit_node {
            Some(existing) => existing.min(*exit_node),
            None => *exit_node,
        });
    }

    for (func_addr, loop_header, step_node) in db.rel_iter::<(Address, Node, Node)>("trim_step") {
        let info = result
            .entry(*func_addr)
            .or_default()
            .entry(*loop_header)
            .or_insert_with(LoopInfo::default);
        match info.step_node {
            Some(existing) if *step_node > existing => { info.step_node = Some(*step_node); }
            None => { info.step_node = Some(*step_node); }
            _ => {}
        }
    }

    // Pre-index loop_exit_branch for O(1) lookup; keep the RB-5 cmp_exit_branch_cand minimum per (f, h, en) for a deterministic result.
    let mut exit_branch_index: HashMap<(Address, Node, Node), (Condition, Arc<Vec<CsharpminorExpr>>, bool)> = HashMap::new();
    for (f, h, en, cond, args, _exit_target, _cont_target, inverted) in
        db.rel_iter::<(Address, Node, Node, Condition, Arc<Vec<CsharpminorExpr>>, Node, Node, bool)>("loop_exit_branch")
    {
        let cand = (cond.clone(), args.clone(), *inverted);
        let take = match exit_branch_index.get(&(*f, *h, *en)) {
            Some(existing) => cmp_exit_branch_cand(&cand, existing) == Ordering::Less,
            None => true,
        };
        if take {
            exit_branch_index.insert((*f, *h, *en), cand);
        }
    }

    for (func_addr, loop_header, exit_node) in db.rel_iter::<(Address, Node, Node)>("primary_exit_node") {
        if let Some((cond, args, inverted)) = exit_branch_index.get(&(*func_addr, *loop_header, *exit_node)) {
            let info = result
                .entry(*func_addr)
                .or_default()
                .entry(*loop_header)
                .or_insert_with(LoopInfo::default);
            // primary_exit_node may yield several candidates per loop; keep the one with the smallest exit node so the choice is deterministic across runs.
            let take = match &info.primary_exit {
                Some(existing) => *exit_node < existing.exit_node,
                None => true,
            };
            if take {
                info.primary_exit = Some(PrimaryExitData {
                    exit_node: *exit_node,
                    condition: cond.clone(),
                    args: args.clone(),
                    inverted: *inverted,
                });
            }
        }
    }

    // Populate break_stmts from emit_break_stmt relation (pre-built Sifthenelse(cond, Sbreak, Sskip) for non-primary loop exit branches).
    for (func_addr, loop_header, exit_node, break_stmt) in
        db.rel_iter::<(Address, Node, Node, ClightStmt)>("emit_break_stmt")
    {
        let info = result
            .entry(*func_addr)
            .or_default()
            .entry(*loop_header)
            .or_insert_with(LoopInfo::default);
        // emit_break_stmt may carry several statements per exit node; keep the RB-5 cmp_break_stmt_cand minimum for a deterministic choice.
        let take = match info.break_stmts.get(exit_node) {
            Some(existing) => cmp_break_stmt_cand(break_stmt, existing) == Ordering::Less,
            None => true,
        };
        if take {
            info.break_stmts.insert(*exit_node, break_stmt.clone());
        }
    }

    // Populate exit_returns from loop_exit_to_return (non-primary exits flowing to a function return); select tail-duplicates value_node + ret_node's return into the exit branch rather than the valueless break that drops the returned value (A5).
    for (func_addr, loop_header, exit_node, value_node, ret_node) in
        db.rel_iter::<(Address, Node, Node, Node, Node)>("loop_exit_to_return")
    {
        let info = result
            .entry(*func_addr)
            .or_default()
            .entry(*loop_header)
            .or_insert_with(LoopInfo::default);
        // loop_exit_to_return may carry several (value, ret) pairs per exit node; keep the smallest to avoid non-determinism from parallel Ascent ordering.
        let cand = (*value_node, *ret_node);
        info.exit_returns
            .entry(*exit_node)
            .and_modify(|existing| {
                if cand < *existing {
                    *existing = cand;
                }
            })
            .or_insert(cand);
    }

    // exec_order_key (not raw id) is required: it keeps a synthetic node (addr | 1<<62) immediately after its base, preventing calls from being pushed past exits and eliminated as unreachable.
    for func_map in result.values_mut() {
        for info in func_map.values_mut() {
            info.body_nodes.sort_by_key(|&n| crate::util::exec_order_key(n));
        }
    }

    result
}

// If-then-else structural metadata from the structuring pass.
#[derive(Debug, Clone, Default)]
pub struct IteInfo {
    pub true_body_nodes: Vec<Node>,
    pub false_body_nodes: Vec<Node>,
    pub join_node: Option<Node>,
    pub no_join: bool,
}

pub fn extract_ite_info(db: &DecompileDB) -> HashMap<Address, HashMap<Node, IteInfo>> {
    let mut result: HashMap<Address, HashMap<Node, IteInfo>> = HashMap::new();

    for (func_addr, branch, member) in db.rel_iter::<(Address, Node, Node)>("emit_ifbody_true") {
        result
            .entry(*func_addr)
            .or_default()
            .entry(*branch)
            .or_insert_with(IteInfo::default)
            .true_body_nodes
            .push(*member);
    }

    for (func_addr, branch, member) in db.rel_iter::<(Address, Node, Node)>("emit_ifbody_false") {
        result
            .entry(*func_addr)
            .or_default()
            .entry(*branch)
            .or_insert_with(IteInfo::default)
            .false_body_nodes
            .push(*member);
    }

    for (func_addr, branch, join) in db.rel_iter::<(Address, Node, Node)>("emit_join_point") {
        let info = result
            .entry(*func_addr)
            .or_default()
            .entry(*branch)
            .or_insert_with(IteInfo::default);
        // emit_join_point may yield several joins per branch; Ascent set order is non-deterministic, so keep the smallest join node.
        info.join_node = Some(match info.join_node {
            Some(existing) => existing.min(*join),
            None => *join,
        });
    }

    for (func_addr, branch) in db.rel_iter::<(Address, Node)>("emit_scond_no_join") {
        result
            .entry(*func_addr)
            .or_default()
            .entry(*branch)
            .or_insert_with(IteInfo::default)
            .no_join = true;
    }

    // exec_order_key places a synthetic node (addr | 1<<62) immediately after its base; a raw id sort would push all synthetic members after all real ones, tearing fused stores out of position.
    for func_map in result.values_mut() {
        for info in func_map.values_mut() {
            info.true_body_nodes.sort_by_key(|&n| crate::util::exec_order_key(n));
            info.false_body_nodes.sort_by_key(|&n| crate::util::exec_order_key(n));
        }
    }

    result
}

#[derive(Debug, Clone)]
pub struct ExtractedStruct {
    pub struct_id: usize,
    #[allow(dead_code)]
    pub layout_hash: u64,
    #[allow(dead_code)]
    pub is_canonical: bool,
    pub definition: StructDef,
}

fn fieldtype_to_ctype(field_type: &FieldType) -> CType {
    match field_type {
        FieldType::Scalar(chunk) => chunk_to_ctype(*chunk, chunk_size(chunk)),
        FieldType::Pointer(inner) => {
            CType::Pointer(Box::new(fieldtype_to_ctype(inner)), TypeQualifiers::none())
        }
        FieldType::StructPointer(struct_id) => {
            let struct_name = format!("struct_{:x}", struct_id);
            CType::Pointer(Box::new(CType::Struct(struct_name)), TypeQualifiers::none())
        }
        FieldType::Array(elem, size) => {
            CType::Array(Box::new(fieldtype_to_ctype(elem)), Some(*size))
        }
        FieldType::EmbeddedStruct(struct_id) => {
            CType::Struct(format!("struct_{:x}", struct_id))
        }
        FieldType::Union(variants) => {
            // SR-2: layout advance is the MAX variant size; pick the first max-size variant so printed width == advance (a smaller variant first would shift all later fields).
            let max_size = variants.iter().map(|v| v.size(8)).max().unwrap_or(4);
            variants
                .iter()
                .find(|v| v.size(8) == max_size)
                .map(fieldtype_to_ctype)
                .unwrap_or(CType::Int(IntSize::Int, Signedness::Signed))
        }
        FieldType::OpaqueBlob(size) => {
            CType::Array(Box::new(CType::Int(IntSize::Char, Signedness::Unsigned)), Some(*size))
        }
        FieldType::Unknown => CType::Int(IntSize::Int, Signedness::Signed),
    }
}

fn chunk_size(chunk: &MemoryChunk) -> usize {
    match chunk {
        MemoryChunk::MBool | MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned => 1,
        MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned => 2,
        MemoryChunk::MInt32 | MemoryChunk::MFloat32 | MemoryChunk::MAny32 => 4,
        MemoryChunk::MInt64 | MemoryChunk::MFloat64 | MemoryChunk::MAny64 => 8,
        MemoryChunk::Unknown => 4,
    }
}

fn build_fields_with_padding(
    field_tuples: &[(usize, i64, FieldType, usize)]
) -> Vec<StructField> {
    let mut offset_map: BTreeMap<i64, &(usize, i64, FieldType, usize)> = BTreeMap::new();
    for entry in field_tuples {
        let (idx, offset, _, _) = entry;
        match offset_map.get(offset) {
            Some(existing) if existing.0 >= *idx => {}
            _ => { offset_map.insert(*offset, entry); }
        }
    }

    let mut fields = Vec::new();
    let mut current_end: i64 = 0;
    
    for (_offset, (_idx, offset, field_type, field_name)) in &offset_map {
        if *offset > current_end {
            let pad_size = (*offset - current_end) as usize;
            match pad_size {
                1 => fields.push(StructField::new(
                    format!("uc_{:x}", current_end),
                    CType::Int(IntSize::Char, Signedness::Unsigned),
                )),
                2 => fields.push(StructField::new(
                    format!("s_{:x}", current_end),
                    CType::Int(IntSize::Short, Signedness::Signed),
                )),
                4 => fields.push(StructField::new(
                    format!("i_{:x}", current_end),
                    CType::Int(IntSize::Int, Signedness::Signed),
                )),
                _ => fields.push(StructField::new(
                    format!("_pad_{:x}", current_end),
                    CType::Array(
                        Box::new(CType::Int(IntSize::Char, Signedness::Unsigned)),
                        Some(pad_size),
                    ),
                )),
            }
        }
        
        let name = crate::decompile::analysis::struct_recovery_pass::field_ident_to_name(*field_name);
        let ty = fieldtype_to_ctype(field_type);
        fields.push(StructField::new(name, ty));
        
        current_end = *offset + field_type.size(8) as i64;
    }
    
    fields
}

pub fn extract_struct_definitions(db: &DecompileDB) -> Vec<ExtractedStruct> {
    let mut structs = Vec::new();
    let mut seen_struct_ids = HashSet::new();

    // Pre-collect efield-detected fields per struct ID (merging across functions); these come from ClightFieldPass and may contain fields not in struct_recovery. reg_to_struct_id may emit multiple sids per reg, so pick the smallest so the same reg resolves to the same canonical id every run.
    let reg_to_canonical_ids: HashMap<u64, usize> = {
        let mut groups: HashMap<u64, Vec<usize>> = HashMap::new();
        for &(_, reg, sid) in db.rel_iter::<(u64, u64, usize)>("reg_to_struct_id") {
            groups.entry(reg).or_default().push(sid);
        }
        groups
            .into_iter()
            .map(|(reg, mut sids)| {
                sids.sort();
                (reg, sids[0])
            })
            .collect()
    };

    // Collect (struct_id, field_offset, field_name, chunk) across all emit_struct_fields tuples. Iteration over the Ascent relation and over `Arc<Vec<...>>` entries is in a non-deterministic order when multiple func_addrs contribute the same field; sort before dedup-by-(struct_id, offset) so the (name, chunk) winner is stable.
    let mut efield_collected: Vec<(usize, i64, Ident, MemoryChunk)> = Vec::new();
    for (_func_addr, base_offset, fields) in
        db.rel_iter::<(u64, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>)>("emit_struct_fields")
    {
        let reg = *base_offset as u64;
        let struct_id = reg_to_canonical_ids.get(&reg)
            .copied()
            .unwrap_or_else(|| base_offset.unsigned_abs() as usize);
        for (field_offset, field_name, chunk) in fields.iter() {
            efield_collected.push((struct_id, *field_offset, *field_name, chunk.clone()));
        }
    }
    efield_collected.sort();
    let mut efield_extra_fields: HashMap<usize, BTreeMap<i64, (Ident, MemoryChunk)>> = HashMap::new();
    for (struct_id, field_offset, field_name, chunk) in efield_collected {
        efield_extra_fields
            .entry(struct_id)
            .or_default()
            .entry(field_offset)
            .or_insert((field_name, chunk));
    }

    for (layout_hash, canonical_id, _field_count, _total_size) in db.rel_iter::<(u64, usize, usize, usize)>("global_struct_catalog") {
        if seen_struct_ids.contains(canonical_id) {
            continue;
        }
        seen_struct_ids.insert(*canonical_id);

        let mut field_tuples: Vec<_> = db.rel_iter::<(usize, usize, i64, FieldType, Ident)>("emit_struct_field")
            .filter(|(sid, _, _, _, _)| *sid == *canonical_id)
            .map(|(_, idx, offset, field_type, field_name)| (*idx, *offset, field_type.clone(), *field_name))
            .collect();

        // Merge efield-detected fields that aren't in the canonical definition
        if let Some(efield_fields) = efield_extra_fields.get(canonical_id) {
            let existing_offsets: HashSet<i64> = field_tuples.iter().map(|(_, off, _, _)| *off).collect();
            let next_idx = field_tuples.len();
            for (idx, (offset, (field_name, chunk))) in efield_fields.iter().enumerate() {
                if !existing_offsets.contains(offset) {
                    field_tuples.push((next_idx + idx, *offset, FieldType::Scalar(chunk.clone()), *field_name));
                }
            }
        }

        field_tuples.sort_by_key(|(_idx, offset, _, _)| *offset);

        let struct_name = format!("struct_{:x}", canonical_id);
        let struct_fields = build_fields_with_padding(&field_tuples);

        let definition = StructDef::new_struct(struct_name, struct_fields);

        structs.push(ExtractedStruct {
            struct_id: *canonical_id,
            layout_hash: *layout_hash,
            is_canonical: true,
            definition,
        });
    }

    if structs.is_empty() {
        for (struct_id, _field_count, _total_size) in db.rel_iter::<(usize, usize, usize)>("emit_struct_def") {
            if seen_struct_ids.contains(struct_id) {
                continue;
            }
            seen_struct_ids.insert(*struct_id);

            let mut field_tuples: Vec<_> = db.rel_iter::<(usize, usize, i64, FieldType, Ident)>("emit_struct_field")
                .filter(|(sid, _, _, _, _)| *sid == *struct_id)
                .map(|(_, idx, offset, field_type, field_name)| (*idx, *offset, field_type.clone(), *field_name))
                .collect();
            
            field_tuples.sort_by_key(|(_idx, offset, _, _)| *offset);

            let struct_name = format!("struct_{:x}", struct_id);
            let struct_fields = build_fields_with_padding(&field_tuples);

            let layout_hash = compute_field_hash(&field_tuples);
            let definition = StructDef::new_struct(struct_name, struct_fields);

            structs.push(ExtractedStruct {
                struct_id: *struct_id,
                layout_hash,
                is_canonical: true,
                definition,
            });
        }
    }

    // Generate struct definitions from emit_struct_fields for efield-detected structs not matched to canonical struct_recovery IDs (register-based IDs from ClightFieldPass).
    for (struct_id, field_map) in &efield_extra_fields {
        if seen_struct_ids.contains(struct_id) {
            continue;
        }
        let struct_name = format!("struct_{:x}", struct_id);
        let field_tuples: Vec<(usize, i64, FieldType, usize)> = field_map
            .iter()
            .enumerate()
            .map(|(idx, (offset, (field_name, chunk)))| {
                (idx, *offset, FieldType::Scalar(chunk.clone()), *field_name)
            })
            .collect();

        let struct_fields = build_fields_with_padding(&field_tuples);
        let layout_hash = compute_field_hash(&field_tuples);
        let definition = StructDef::new_struct(struct_name, struct_fields);

        seen_struct_ids.insert(*struct_id);
        structs.push(ExtractedStruct {
            struct_id: *struct_id,
            layout_hash,
            is_canonical: false,
            definition,
        });
    }

    structs.sort_by_key(|s| s.struct_id);
    structs
}

fn compute_field_hash(fields: &[(usize, i64, FieldType, usize)]) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut hasher = DefaultHasher::new();
    for (idx, offset, ty, _name) in fields {
        idx.hash(&mut hasher);
        offset.hash(&mut hasher);
        ty.to_type_string().hash(&mut hasher);
    }
    hasher.finish()
}

pub fn extract_struct_layout_map(db: &DecompileDB) -> HashMap<usize, Vec<(i64, String, MemoryChunk)>> {
    let mut layouts = HashMap::new();
    
    let id_to_name: HashMap<usize, String> = db.rel_iter::<(Ident, Symbol)>("ident_to_symbol")
        .map(|(id, name)| (*id, name.to_string()))
        .collect();
    
    let canonical_ids: HashSet<usize> = db.rel_iter::<(u64, usize)>("emit_canonical_struct_id")
        .map(|(_hash, id)| *id)
        .collect();
    
    for (global_ident, struct_id, fields) in db.rel_iter::<(Ident, usize, Arc<Vec<(i64, Ident, MemoryChunk)>>)>("emit_global_struct_fields") {
        let _global_name = id_to_name
            .get(&(*global_ident as usize))
            .cloned()
            .unwrap_or_else(|| format!("global_{:x}", global_ident));
        
        let mapped_fields: Vec<(i64, String, MemoryChunk)> = fields.iter().map(|(offset, field_ident, chunk)| {
            let field_name = id_to_name
                .get(&(*field_ident as usize))
                .cloned()
                .unwrap_or_else(|| format!("field_{:x}", offset));
            (*offset, field_name, *chunk)
        }).collect();
        
        layouts.insert(*struct_id, mapped_fields);
    }

    layouts
}

fn chunk_to_ctype(chunk: MemoryChunk, size: usize) -> CType {
    match chunk {
        // SR-2: MBool must map to unsigned char (1 byte), not CType::Bool which renders as "int" (4 bytes) and would shift every later field of the struct.
        MemoryChunk::MBool => CType::Int(IntSize::Char, Signedness::Unsigned),
        MemoryChunk::MInt8Signed => CType::Int(IntSize::Char, Signedness::Signed),
        MemoryChunk::MInt8Unsigned => CType::Int(IntSize::Char, Signedness::Unsigned),
        MemoryChunk::MInt16Signed => CType::Int(IntSize::Short, Signedness::Signed),
        MemoryChunk::MInt16Unsigned => CType::Int(IntSize::Short, Signedness::Unsigned),
        MemoryChunk::MInt32 | MemoryChunk::MAny32 => CType::Int(IntSize::Int, Signedness::Signed),
        MemoryChunk::MInt64 | MemoryChunk::MAny64 => CType::Int(IntSize::Long, Signedness::Signed),
        MemoryChunk::MFloat32 => CType::Float(crate::decompile::passes::c_pass::types::FloatSize::Float),
        MemoryChunk::MFloat64 => CType::Float(crate::decompile::passes::c_pass::types::FloatSize::Double),
        MemoryChunk::Unknown => match size {
            1 => CType::Int(IntSize::Char, Signedness::Unsigned),
            2 => CType::Int(IntSize::Short, Signedness::Signed),
            4 => CType::Int(IntSize::Int, Signedness::Signed),
            8 => CType::Int(IntSize::Long, Signedness::Signed),
            _ => CType::Int(IntSize::Int, Signedness::Signed),
        },
    }
}

// TR-3: struct-field pointer-type selection helpers are shared between solver input (FunctionData.struct_field_type_candidates) and emission-side recomputation; the emission side must recompute because struct_field_type_idx has no path out of select.rs today, and scanning the SELECTED statements with SELECTED types can only be more precise than the solver's all-candidates scan.

/// (struct_name, field_name) key of a field-access lvalue. Mirror of solve.rs::field_key_of_lvalue.
pub(crate) fn clight_field_key_of_lvalue(e: &ClightExpr) -> Option<(String, String)> {
    if let ClightExpr::Efield(base, fid, _) = e {
        if let ClightExpr::Ederef(_, ClightType::Tstruct(sid, _)) = base.as_ref() {
            let struct_name = format!("struct_{:x}", sid);
            let field_name = crate::decompile::passes::csh_pass::field_ident_to_name(*fid);
            return Some((struct_name, field_name));
        }
    }
    None
}

/// (struct, field) key of a field-access value, possibly cast-wrapped. Mirror of solve.rs::field_key_of_expr.
pub(crate) fn clight_field_key_of_expr(e: &ClightExpr) -> Option<(String, String)> {
    match e {
        ClightExpr::Ecast(inner, _) => clight_field_key_of_expr(inner),
        _ => clight_field_key_of_lvalue(e),
    }
}

pub(crate) fn xtype_is_ptr_class(xt: &XType) -> bool {
    matches!(
        xt,
        XType::Xptr
            | XType::Xcharptr
            | XType::Xcharptrptr
            | XType::Xintptr
            | XType::Xfloatptr
            | XType::Xsingleptr
            | XType::Xfuncptr
            | XType::XstructPtr(_)
    )
}

/// True if a stored value carries a pointer (explicitly or implicitly via TR-3 ptr_regs, cast-wrapping, pointer arithmetic, or pointer-typed load/field). Mirror of solve.rs::clight_value_is_ptr.
pub(crate) fn clight_value_is_ptr(e: &ClightExpr, ptr_regs: &HashSet<RTLReg>) -> bool {
    match e {
        ClightExpr::Eaddrof(..) | ClightExpr::EvarSymbol(..) => true,
        ClightExpr::Etempvar(id, ct) => {
            matches!(ct, ClightType::Tpointer(..)) || ptr_regs.contains(&(*id as RTLReg))
        }
        ClightExpr::Evar(_, ct) => matches!(ct, ClightType::Tpointer(..)),
        ClightExpr::Ecast(inner, ct) => {
            matches!(ct, ClightType::Tpointer(..)) || clight_value_is_ptr(inner, ptr_regs)
        }
        // Pointer arithmetic: p+n propagates the pointer; p-q is a pointer only when rhs is not itself a pointer (pointer difference is an integer).
        ClightExpr::Ebinop(ClightBinaryOp::Oadd, l, r, _) => {
            clight_value_is_ptr(l, ptr_regs) || clight_value_is_ptr(r, ptr_regs)
        }
        ClightExpr::Ebinop(ClightBinaryOp::Osub, l, r, _) => {
            clight_value_is_ptr(l, ptr_regs) && !clight_value_is_ptr(r, ptr_regs)
        }
        ClightExpr::Ederef(_, ct) | ClightExpr::Efield(_, _, ct) => {
            matches!(ct, ClightType::Tpointer(..))
        }
        _ => false,
    }
}

/// Records (struct, field) keys with pointer evidence: ptr-valued store in, out-flow to ptr-selected register, or passed to ptr-typed callee param. Mirror of solve.rs::scan_field_ptr_stores; callee_sigs passed explicitly because SelectedFunction does not carry it.
pub(crate) fn scan_field_ptr_evidence(
    stmt: &ClightStmt,
    ptr_regs: &HashSet<RTLReg>,
    callee_sigs: &HashMap<Ident, CalleeSignature>,
    name_to_ident: &HashMap<String, Ident>,
    out: &mut HashSet<(String, String)>,
) {
    match stmt {
        ClightStmt::Sassign(lhs, rhs) => {
            if clight_value_is_ptr(rhs, ptr_regs) {
                if let Some(key) = clight_field_key_of_lvalue(lhs) {
                    out.insert(key);
                }
            }
        }
        ClightStmt::Sset(id, e) => {
            // Out-flow: the field's value lands in a register selected as a pointer.
            if ptr_regs.contains(&(*id as RTLReg)) {
                if let Some(key) = clight_field_key_of_expr(e) {
                    out.insert(key);
                }
            }
        }
        ClightStmt::Scall(_, f, args) => {
            // Arg-flow: the field is passed where the callee expects a pointer.
            let callee = crate::decompile::passes::clight_select::select::callee_ident_from_expr(
                f,
                name_to_ident,
            );
            if let Some(sig) = callee.and_then(|id| callee_sigs.get(&id)) {
                for (i, a) in args.iter().enumerate() {
                    if let Some(pt) = sig.param_types.get(i) {
                        if xtype_is_ptr_class(pt) {
                            if let Some(key) = clight_field_key_of_expr(a) {
                                out.insert(key);
                            }
                        }
                    }
                }
            }
        }
        ClightStmt::Sifthenelse(_, a, b) | ClightStmt::Sloop(a, b) => {
            scan_field_ptr_evidence(a, ptr_regs, callee_sigs, name_to_ident, out);
            scan_field_ptr_evidence(b, ptr_regs, callee_sigs, name_to_ident, out);
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss {
                scan_field_ptr_evidence(s, ptr_regs, callee_sigs, name_to_ident, out);
            }
        }
        ClightStmt::Slabel(_, inner) => {
            scan_field_ptr_evidence(inner, ptr_regs, callee_sigs, name_to_ident, out)
        }
        ClightStmt::Sswitch(_, cases) => {
            for (_, s) in cases {
                scan_field_ptr_evidence(s, ptr_regs, callee_sigs, name_to_ident, out);
            }
        }
        _ => {}
    }
}

/// True when an expression is float-valued in the selected program.
fn clight_value_is_float(e: &ClightExpr, float_regs: &HashSet<RTLReg>) -> bool {
    match e {
        ClightExpr::EconstFloat(..) | ClightExpr::EconstSingle(..) => true,
        ClightExpr::Etempvar(id, ct) => {
            matches!(ct, ClightType::Tfloat(..)) || float_regs.contains(&(*id as RTLReg))
        }
        ClightExpr::Ecast(_, ct)
        | ClightExpr::Evar(_, ct)
        | ClightExpr::Ederef(_, ct)
        | ClightExpr::Efield(_, _, ct)
        | ClightExpr::Ebinop(_, _, _, ct)
        | ClightExpr::Eunop(_, _, ct)
        | ClightExpr::Econdition(_, _, _, ct) => matches!(ct, ClightType::Tfloat(..)),
        _ => false,
    }
}

/// Widens float_regs to a fixpoint for the TR-3 conflict veto: from_relations can refine a variable to double after solver selection, so a register may be float in the printed C without being float-SELECTED; the veto must account for this. Never use for positive pointer evidence.
pub(crate) fn widen_float_regs_by_defs<'a>(
    stmts: impl Iterator<Item = &'a ClightStmt> + Clone,
    float_regs: &mut HashSet<RTLReg>,
) {
    fn walk(s: &ClightStmt, float_regs: &mut HashSet<RTLReg>, grew: &mut bool) {
        match s {
            ClightStmt::Sset(id, e) => {
                let reg = *id as RTLReg;
                if !float_regs.contains(&reg) && clight_value_is_float(e, float_regs) {
                    float_regs.insert(reg);
                    *grew = true;
                }
            }
            ClightStmt::Ssequence(ss) => {
                for s in ss {
                    walk(s, float_regs, grew);
                }
            }
            ClightStmt::Sifthenelse(_, a, b) | ClightStmt::Sloop(a, b) => {
                walk(a, float_regs, grew);
                walk(b, float_regs, grew);
            }
            ClightStmt::Slabel(_, inner) => walk(inner, float_regs, grew),
            ClightStmt::Sswitch(_, cases) => {
                for (_, s) in cases {
                    walk(s, float_regs, grew);
                }
            }
            _ => {}
        }
    }
    loop {
        let mut grew = false;
        for s in stmts.clone() {
            walk(s, float_regs, &mut grew);
        }
        if !grew {
            break;
        }
    }
}

/// Widens ptr_regs to a fixpoint for the TR-3 veto only: counts retype-candidate fields (`evidenced`) as pointer-valued because patching them to `void *` turns their loads into pointers in the printed C, making integer-looking arithmetic become pointer arithmetic. Never use for positive pointer evidence -- that would let a candidate field justify itself.
pub(crate) fn widen_ptr_regs_by_defs<'a>(
    stmts: impl Iterator<Item = &'a ClightStmt> + Clone,
    ptr_regs: &mut HashSet<RTLReg>,
    evidenced: &HashSet<(String, String)>,
) {
    fn value_is_ptr_veto(
        e: &ClightExpr,
        regs: &HashSet<RTLReg>,
        evidenced: &HashSet<(String, String)>,
    ) -> bool {
        // A retype-candidate field load will become pointer-typed once patched.
        if let Some(k) = clight_field_key_of_expr(e) {
            if evidenced.contains(&k) {
                return true;
            }
        }
        // Remaining arms mirror clight_value_is_ptr with veto-aware recursion.
        match e {
            ClightExpr::Eaddrof(..) | ClightExpr::EvarSymbol(..) => true,
            ClightExpr::Etempvar(id, ct) => {
                matches!(ct, ClightType::Tpointer(..)) || regs.contains(&(*id as RTLReg))
            }
            ClightExpr::Evar(_, ct) => matches!(ct, ClightType::Tpointer(..)),
            ClightExpr::Ecast(inner, ct) => {
                matches!(ct, ClightType::Tpointer(..))
                    || value_is_ptr_veto(inner, regs, evidenced)
            }
            ClightExpr::Ebinop(ClightBinaryOp::Oadd, l, r, _) => {
                value_is_ptr_veto(l, regs, evidenced) || value_is_ptr_veto(r, regs, evidenced)
            }
            ClightExpr::Ebinop(ClightBinaryOp::Osub, l, r, _) => {
                value_is_ptr_veto(l, regs, evidenced) && !value_is_ptr_veto(r, regs, evidenced)
            }
            ClightExpr::Ederef(_, ct) | ClightExpr::Efield(_, _, ct) => {
                matches!(ct, ClightType::Tpointer(..))
            }
            _ => false,
        }
    }
    fn walk(
        s: &ClightStmt,
        ptr_regs: &mut HashSet<RTLReg>,
        evidenced: &HashSet<(String, String)>,
        grew: &mut bool,
    ) {
        match s {
            ClightStmt::Sset(id, e) => {
                let reg = *id as RTLReg;
                if !ptr_regs.contains(&reg) && value_is_ptr_veto(e, ptr_regs, evidenced) {
                    ptr_regs.insert(reg);
                    *grew = true;
                }
            }
            ClightStmt::Ssequence(ss) => {
                for s in ss {
                    walk(s, ptr_regs, evidenced, grew);
                }
            }
            ClightStmt::Sifthenelse(_, a, b) | ClightStmt::Sloop(a, b) => {
                walk(a, ptr_regs, evidenced, grew);
                walk(b, ptr_regs, evidenced, grew);
            }
            ClightStmt::Slabel(_, inner) => walk(inner, ptr_regs, evidenced, grew),
            ClightStmt::Sswitch(_, cases) => {
                for (_, s) in cases {
                    walk(s, ptr_regs, evidenced, grew);
                }
            }
            _ => {}
        }
    }
    loop {
        let mut grew = false;
        for s in stmts.clone() {
            walk(s, ptr_regs, evidenced, &mut grew);
        }
        if !grew {
            break;
        }
    }
}

/// Records (struct, field) keys whose usage contradicts a pointer retype: float store/load context, or the field used as an integer offset next to a pointer (f1+f2 or ptr+field). Retyping a contested field moves the type error rather than fixing it; keeping `long` is neutral. These shapes come from layout-merged structs; the honest fix is SR-2 overlap-aware recovery.
pub(crate) fn scan_field_ptr_conflicts(
    stmt: &ClightStmt,
    ptr_regs: &HashSet<RTLReg>,
    float_regs: &HashSet<RTLReg>,
    callee_sigs: &HashMap<Ident, CalleeSignature>,
    name_to_ident: &HashMap<String, Ident>,
    out: &mut HashSet<(String, String)>,
) {
    fn walk_expr(
        e: &ClightExpr,
        ptr_regs: &HashSet<RTLReg>,
        float_regs: &HashSet<RTLReg>,
        out: &mut HashSet<(String, String)>,
    ) {
        match e {
            ClightExpr::Ecast(inner, ct) => {
                if matches!(ct, ClightType::Tfloat(..)) {
                    if let Some(k) = clight_field_key_of_expr(inner) {
                        out.insert(k);
                    }
                }
                walk_expr(inner, ptr_regs, float_regs, out);
            }
            ClightExpr::Ebinop(op, l, r, _) => {
                let lk = clight_field_key_of_expr(l);
                let rk = clight_field_key_of_expr(r);
                // Field paired directly with a float operand: float context.
                if let Some(k) = &lk {
                    if clight_value_is_float(r, float_regs) {
                        out.insert(k.clone());
                    }
                }
                if let Some(k) = &rk {
                    if clight_value_is_float(l, float_regs) {
                        out.insert(k.clone());
                    }
                }
                if matches!(op, ClightBinaryOp::Oadd) {
                    // f1 + f2: pointers cannot be added -- both are integers.
                    if let (Some(k1), Some(k2)) = (&lk, &rk) {
                        out.insert(k1.clone());
                        out.insert(k2.clone());
                    }
                    // ptr + field: the field is the byte offset, an integer.
                    if let Some(k) = &lk {
                        if clight_value_is_ptr(r, ptr_regs) {
                            out.insert(k.clone());
                        }
                    }
                    if let Some(k) = &rk {
                        if clight_value_is_ptr(l, ptr_regs) {
                            out.insert(k.clone());
                        }
                    }
                }
                walk_expr(l, ptr_regs, float_regs, out);
                walk_expr(r, ptr_regs, float_regs, out);
            }
            ClightExpr::Ederef(inner, _)
            | ClightExpr::Eaddrof(inner, _)
            | ClightExpr::Eunop(_, inner, _)
            | ClightExpr::Efield(inner, _, _) => walk_expr(inner, ptr_regs, float_regs, out),
            ClightExpr::Econdition(c, t, f, _) => {
                walk_expr(c, ptr_regs, float_regs, out);
                walk_expr(t, ptr_regs, float_regs, out);
                walk_expr(f, ptr_regs, float_regs, out);
            }
            _ => {}
        }
    }

    match stmt {
        ClightStmt::Sassign(lhs, rhs) => {
            if clight_value_is_float(rhs, float_regs) {
                if let Some(key) = clight_field_key_of_lvalue(lhs) {
                    out.insert(key);
                }
            }
            walk_expr(lhs, ptr_regs, float_regs, out);
            walk_expr(rhs, ptr_regs, float_regs, out);
        }
        ClightStmt::Sset(id, e) => {
            if float_regs.contains(&(*id as RTLReg)) {
                if let Some(key) = clight_field_key_of_expr(e) {
                    out.insert(key);
                }
            }
            walk_expr(e, ptr_regs, float_regs, out);
        }
        ClightStmt::Scall(_, f, args) => {
            let callee = crate::decompile::passes::clight_select::select::callee_ident_from_expr(
                f,
                name_to_ident,
            );
            let sig = callee.and_then(|id| callee_sigs.get(&id));
            for (i, a) in args.iter().enumerate() {
                if let Some(sig) = sig {
                    if let Some(pt) = sig.param_types.get(i) {
                        if matches!(pt, XType::Xfloat | XType::Xsingle) {
                            if let Some(key) = clight_field_key_of_expr(a) {
                                out.insert(key);
                            }
                        }
                    }
                }
                walk_expr(a, ptr_regs, float_regs, out);
            }
        }
        ClightStmt::Sifthenelse(c, a, b) => {
            walk_expr(c, ptr_regs, float_regs, out);
            scan_field_ptr_conflicts(a, ptr_regs, float_regs, callee_sigs, name_to_ident, out);
            scan_field_ptr_conflicts(b, ptr_regs, float_regs, callee_sigs, name_to_ident, out);
        }
        ClightStmt::Sloop(a, b) => {
            scan_field_ptr_conflicts(a, ptr_regs, float_regs, callee_sigs, name_to_ident, out);
            scan_field_ptr_conflicts(b, ptr_regs, float_regs, callee_sigs, name_to_ident, out);
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss {
                scan_field_ptr_conflicts(s, ptr_regs, float_regs, callee_sigs, name_to_ident, out);
            }
        }
        ClightStmt::Slabel(_, inner) => {
            scan_field_ptr_conflicts(inner, ptr_regs, float_regs, callee_sigs, name_to_ident, out)
        }
        ClightStmt::Sswitch(e, cases) => {
            walk_expr(e, ptr_regs, float_regs, out);
            for (_, s) in cases {
                scan_field_ptr_conflicts(s, ptr_regs, float_regs, callee_sigs, name_to_ident, out);
            }
        }
        ClightStmt::Sreturn(Some(e)) => walk_expr(e, ptr_regs, float_regs, out),
        _ => {}
    }
}

/// Default type string of a struct field, restricted to the retypeable class (64-bit non-pointer scalars); narrower fields can't hold a pointer on LP64 and already-pointer fields need no re-selection.
fn field_default_type_str(ty: &ClightType) -> Option<String> {
    match ty {
        ClightType::Tlong(ClightSignedness::Signed, _) => Some("long".to_string()),
        ClightType::Tlong(ClightSignedness::Unsigned, _) => Some("unsigned long".to_string()),
        ClightType::Tfloat(ClightFloatSize::F64, _) => Some("double".to_string()),
        _ => None,
    }
}

fn collect_field_defaults_expr(
    e: &ClightExpr,
    out: &mut BTreeMap<(String, String), BTreeSet<String>>,
) {
    if let ClightExpr::Efield(base, fid, fty) = e {
        if let ClightExpr::Ederef(_, ClightType::Tstruct(sid, _)) = base.as_ref() {
            if let Some(default) = field_default_type_str(fty) {
                let key = (
                    format!("struct_{:x}", sid),
                    crate::decompile::passes::csh_pass::field_ident_to_name(*fid),
                );
                out.entry(key).or_default().insert(default);
            }
        }
    }
    match e {
        ClightExpr::Ederef(inner, _)
        | ClightExpr::Eaddrof(inner, _)
        | ClightExpr::Ecast(inner, _)
        | ClightExpr::Eunop(_, inner, _)
        | ClightExpr::Efield(inner, _, _) => collect_field_defaults_expr(inner, out),
        ClightExpr::Ebinop(_, l, r, _) => {
            collect_field_defaults_expr(l, out);
            collect_field_defaults_expr(r, out);
        }
        ClightExpr::Econdition(c, t, f, _) => {
            collect_field_defaults_expr(c, out);
            collect_field_defaults_expr(t, out);
            collect_field_defaults_expr(f, out);
        }
        _ => {}
    }
}

fn collect_field_defaults_stmt(
    s: &ClightStmt,
    out: &mut BTreeMap<(String, String), BTreeSet<String>>,
) {
    match s {
        ClightStmt::Sassign(l, r) => {
            collect_field_defaults_expr(l, out);
            collect_field_defaults_expr(r, out);
        }
        ClightStmt::Sset(_, e) => collect_field_defaults_expr(e, out),
        ClightStmt::Scall(_, f, args) => {
            collect_field_defaults_expr(f, out);
            for a in args {
                collect_field_defaults_expr(a, out);
            }
        }
        ClightStmt::Sbuiltin(_, _, _, args) => {
            for a in args {
                collect_field_defaults_expr(a, out);
            }
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss {
                collect_field_defaults_stmt(s, out);
            }
        }
        ClightStmt::Sifthenelse(c, a, b) => {
            collect_field_defaults_expr(c, out);
            collect_field_defaults_stmt(a, out);
            collect_field_defaults_stmt(b, out);
        }
        ClightStmt::Sloop(a, b) => {
            collect_field_defaults_stmt(a, out);
            collect_field_defaults_stmt(b, out);
        }
        ClightStmt::Sreturn(Some(e)) => collect_field_defaults_expr(e, out),
        ClightStmt::Sswitch(e, cases) => {
            collect_field_defaults_expr(e, out);
            for (_, st) in cases {
                collect_field_defaults_stmt(st, out);
            }
        }
        ClightStmt::Slabel(_, inner) => collect_field_defaults_stmt(inner, out),
        _ => {}
    }
}

/// Per-(struct, field) type candidates: sorted defaults then pointer alternative. Only retypeable-class fields (see field_default_type_str) get an entry; shared between solver input and emission-side recomputation.
pub(crate) fn collect_struct_field_type_candidates<'a>(
    stmts: impl Iterator<Item = &'a ClightStmt>,
) -> HashMap<(String, String), Vec<String>> {
    let mut seen: BTreeMap<(String, String), BTreeSet<String>> = BTreeMap::new();
    for s in stmts {
        collect_field_defaults_stmt(s, &mut seen);
    }
    seen.into_iter()
        .map(|(key, defaults)| {
            let mut cands: Vec<String> = defaults.into_iter().collect();
            cands.push("void *".to_string());
            (key, cands)
        })
        .collect()
}

/// Pick rule for a pointer-evidenced field: prefer struct pointer, else first pointer candidate. Same rule applied inline by solve.rs::infer_select_program.
pub(crate) fn pick_field_ptr_candidate(cands: &[String]) -> Option<usize> {
    cands
        .iter()
        .position(|c| c.contains('*') && c.contains("struct"))
        .or_else(|| cands.iter().position(|c| c.contains('*')))
}

/// Parses a pointer candidate string ("void *" or "struct NAME *") back into a CType.
fn parse_field_type_candidate(s: &str) -> Option<CType> {
    if s == "void *" {
        return Some(CType::Pointer(Box::new(CType::Void), TypeQualifiers::none()));
    }
    if let Some(name) = s.strip_prefix("struct ").and_then(|r| r.strip_suffix(" *")) {
        return Some(CType::Pointer(
            Box::new(CType::Struct(name.to_string())),
            TypeQualifiers::none(),
        ));
    }
    None
}

/// Applies TR-3 field-type selection; only 8-byte scalar fields (long/ulong/double) may become pointers, preserving layout. Returns patch count. MANIFOLD_TR3_TRACE=1 logs each patch.
pub fn apply_struct_field_type_selection(
    structs: &mut [ExtractedStruct],
    selection: &HashMap<(String, String), String>,
) -> usize {
    if selection.is_empty() {
        return 0;
    }
    let trace = std::env::var("MANIFOLD_TR3_TRACE").is_ok();
    let mut patched = 0usize;
    for ex in structs.iter_mut() {
        let Some(sname) = ex.definition.name.clone() else { continue };
        for field in ex.definition.fields.iter_mut() {
            let Some(fname) = field.name.clone() else { continue };
            let Some(want) = selection.get(&(sname.clone(), fname)) else { continue };
            let eligible = matches!(
                field.ty,
                CType::Int(IntSize::Long, _) | CType::Float(FloatSize::Double)
            );
            if !eligible {
                continue;
            }
            if let Some(new_ty) = parse_field_type_candidate(want) {
                if trace {
                    eprintln!(
                        "[clight-emit] TR3: field {}.{} retyped {:?} -> {}",
                        sname,
                        field.name.as_deref().unwrap_or("?"),
                        field.ty,
                        want
                    );
                }
                field.ty = new_ty;
                patched += 1;
            }
        }
    }
    patched
}


/// Collect all register IDs (from Etempvar) used in a statement.
pub fn collect_stmt_regs(stmt: &ClightStmt) -> Vec<RTLReg> {
    let mut regs = Vec::new();
    fn collect_expr_regs(expr: &ClightExpr, regs: &mut Vec<RTLReg>) {
        match expr {
            ClightExpr::Etempvar(id, _) => {
                let reg = *id as RTLReg;
                if !regs.contains(&reg) { regs.push(reg); }
            }
            ClightExpr::Ederef(inner, _) | ClightExpr::Eaddrof(inner, _)
            | ClightExpr::Eunop(_, inner, _) | ClightExpr::Ecast(inner, _)
            | ClightExpr::Efield(inner, _, _) => collect_expr_regs(inner, regs),
            ClightExpr::Ebinop(_, lhs, rhs, _) => {
                collect_expr_regs(lhs, regs);
                collect_expr_regs(rhs, regs);
            }
            _ => {}
        }
    }
    fn collect_stmt_regs_inner(stmt: &ClightStmt, regs: &mut Vec<RTLReg>) {
        match stmt {
            ClightStmt::Sassign(lhs, rhs) => { collect_expr_regs(lhs, regs); collect_expr_regs(rhs, regs); }
            ClightStmt::Sset(id, expr) => { let r = *id as RTLReg; if !regs.contains(&r) { regs.push(r); } collect_expr_regs(expr, regs); }
            ClightStmt::Scall(_, f, args) => { collect_expr_regs(f, regs); for a in args { collect_expr_regs(a, regs); } }
            ClightStmt::Sreturn(Some(e)) => collect_expr_regs(e, regs),
            ClightStmt::Sifthenelse(c, t, e) => { collect_expr_regs(c, regs); collect_stmt_regs_inner(t, regs); collect_stmt_regs_inner(e, regs); }
            ClightStmt::Ssequence(ss) => { for s in ss { collect_stmt_regs_inner(s, regs); } }
            ClightStmt::Sloop(a, b) => { collect_stmt_regs_inner(a, regs); collect_stmt_regs_inner(b, regs); }
            ClightStmt::Slabel(_, inner) => collect_stmt_regs_inner(inner, regs),
            ClightStmt::Sswitch(e, cases) => { collect_expr_regs(e, regs); for (_, s) in cases { collect_stmt_regs_inner(s, regs); } }
            _ => {}
        }
    }
    collect_stmt_regs_inner(stmt, &mut regs);
    regs
}

fn patch_clight_stmt_types(stmt: &mut ClightStmt, reg_types: &HashMap<RTLReg, ClightType>) {
    match stmt {
        ClightStmt::Sassign(lhs, rhs) => {
            retype_expr(lhs, reg_types);
            retype_expr(rhs, reg_types);
        }
        ClightStmt::Sset(_, expr) => retype_expr(expr, reg_types),
        ClightStmt::Scall(_, func, args) => {
            retype_expr(func, reg_types);
            for arg in args {
                retype_expr(arg, reg_types);
            }
        }
        ClightStmt::Sbuiltin(_, _, _, args) => {
            for arg in args {
                retype_expr(arg, reg_types);
            }
        }
        ClightStmt::Ssequence(stmts) => {
            for s in stmts {
                patch_clight_stmt_types(s, reg_types);
            }
        }
        ClightStmt::Sifthenelse(cond, then_b, else_b) => {
            retype_expr(cond, reg_types);
            patch_clight_stmt_types(then_b, reg_types);
            patch_clight_stmt_types(else_b, reg_types);
        }
        ClightStmt::Sloop(body1, body2) => {
            patch_clight_stmt_types(body1, reg_types);
            patch_clight_stmt_types(body2, reg_types);
        }
        ClightStmt::Sreturn(Some(expr)) => retype_expr(expr, reg_types),
        ClightStmt::Sswitch(expr, cases) => {
            retype_expr(expr, reg_types);
            for (_, s) in cases {
                patch_clight_stmt_types(s, reg_types);
            }
        }
        ClightStmt::Slabel(_, inner) => patch_clight_stmt_types(inner, reg_types),
        _ => {}
    }
}

fn retype_expr(expr: &mut ClightExpr, reg_types: &HashMap<RTLReg, ClightType>) {
    retype_expr_ctx(expr, reg_types, false);
}

fn retype_expr_ctx(expr: &mut ClightExpr, reg_types: &HashMap<RTLReg, ClightType>, in_deref_context: bool) {
    match expr {
        ClightExpr::Etempvar(id, ty) => {
             if let Some(new_ty) = reg_types.get(&(*id as u64)) {
                 // Don't override a pointer type with a non-pointer when inside a deref
                 if in_deref_context && is_pointer_type(ty) && !is_pointer_type(new_ty) {
                     return;
                 }
                 *ty = new_ty.clone();
             }
        }
        ClightExpr::Ederef(inner, elem_ty) => {
            retype_expr_ctx(inner, reg_types, true);
            let inner_ty = clight_expr_type(inner);
            if let ClightType::Tpointer(pointed_ty, _) = inner_ty {
                *elem_ty = (*pointed_ty).clone();
            }
        }
        ClightExpr::Eaddrof(inner, _) => retype_expr_ctx(inner, reg_types, false),
        ClightExpr::Eunop(_, inner, _) => retype_expr_ctx(inner, reg_types, false),
        ClightExpr::Ebinop(op, lhs, rhs, ty) => {
             retype_expr_ctx(lhs, reg_types, in_deref_context);
             retype_expr_ctx(rhs, reg_types, false);
             *ty = infer_binop_type(*op, &clight_expr_type(lhs), &clight_expr_type(rhs));
        }
        ClightExpr::Ecast(inner, _target_ty) => {
            retype_expr_ctx(inner, reg_types, false);
        }
        ClightExpr::Efield(inner, _, _) => retype_expr_ctx(inner, reg_types, false),
        _ => {}
    }
}

fn infer_binop_type(op: ClightBinaryOp, lhs_ty: &ClightType, rhs_ty: &ClightType) -> ClightType {
    if is_float_type(lhs_ty) || is_float_type(rhs_ty) {
         if matches!(lhs_ty, ClightType::Tfloat(ClightFloatSize::F64, _)) 
            || matches!(rhs_ty, ClightType::Tfloat(ClightFloatSize::F64, _)) {
             return default_float_type();
         }
         return default_single_type();
    }
    
    if is_pointer_type(lhs_ty) && is_integral_type(rhs_ty) && matches!(op, ClightBinaryOp::Oadd | ClightBinaryOp::Osub) {
        return lhs_ty.clone();
    }
    if is_integral_type(lhs_ty) && is_pointer_type(rhs_ty) && matches!(op, ClightBinaryOp::Oadd) {
        return rhs_ty.clone();
    }
    
    match op {
        ClightBinaryOp::Oeq | ClightBinaryOp::One | ClightBinaryOp::Olt | ClightBinaryOp::Ogt | ClightBinaryOp::Ole | ClightBinaryOp::Oge => {
            return default_bool_type();
        }
        _ => {}
    }

    if matches!(lhs_ty, ClightType::Tlong(_, _)) || matches!(rhs_ty, ClightType::Tlong(_, _)) {
        return default_long_type();
    }
    
    default_int_type()
}

fn is_float_type(ty: &ClightType) -> bool {
    matches!(ty, ClightType::Tfloat(_, _))
}

#[cfg(test)]
mod tr3_tests {
    use super::*;

    fn tlong() -> ClightType {
        ClightType::Tlong(ClightSignedness::Signed, ClightAttr::default())
    }
    fn tstruct(sid: usize) -> ClightType {
        ClightType::Tstruct(sid, ClightAttr::default())
    }
    fn field_store(sid: usize, ofs: i64, fty: ClightType, rhs: ClightExpr) -> ClightStmt {
        ClightStmt::Sassign(
            ClightExpr::Efield(
                Box::new(ClightExpr::Ederef(
                    Box::new(ClightExpr::Etempvar(1, tlong())),
                    tstruct(sid),
                )),
                ofs as Ident,
                fty,
            ),
            rhs,
        )
    }

    #[test]
    fn pick_prefers_struct_ptr_then_any_ptr() {
        let cands = vec!["long".to_string(), "void *".to_string()];
        assert_eq!(pick_field_ptr_candidate(&cands), Some(1));
        let cands = vec![
            "long".to_string(),
            "void *".to_string(),
            "struct struct_7 *".to_string(),
        ];
        assert_eq!(pick_field_ptr_candidate(&cands), Some(2));
        let cands = vec!["long".to_string(), "double".to_string()];
        assert_eq!(pick_field_ptr_candidate(&cands), None);
    }

    #[test]
    fn parse_candidate_roundtrip() {
        assert_eq!(
            parse_field_type_candidate("void *"),
            Some(CType::Pointer(Box::new(CType::Void), TypeQualifiers::none()))
        );
        assert_eq!(
            parse_field_type_candidate("struct struct_7 *"),
            Some(CType::Pointer(
                Box::new(CType::Struct("struct_7".to_string())),
                TypeQualifiers::none()
            ))
        );
        assert_eq!(parse_field_type_candidate("long"), None);
    }

    #[test]
    fn collect_only_64bit_scalar_fields() {
        // long field at offset 8 of struct 1: eligible.
        let s1 = field_store(1, 8, tlong(), ClightExpr::Etempvar(2, tlong()));
        // int field: not eligible (a pointer cannot fit).
        let s2 = field_store(
            1,
            0,
            ClightType::Tint(ClightIntSize::I32, ClightSignedness::Signed, ClightAttr::default()),
            ClightExpr::Etempvar(2, tlong()),
        );
        // already-pointer field: no re-selection needed.
        let s3 = field_store(
            2,
            0,
            ClightType::Tpointer(Arc::new(ClightType::Tvoid), ClightAttr::default()),
            ClightExpr::Etempvar(2, tlong()),
        );
        let stmts = vec![s1, s2, s3];
        let cands = collect_struct_field_type_candidates(stmts.iter());
        assert_eq!(cands.len(), 1);
        let c = cands.get(&("struct_1".to_string(), "ofs_8".to_string())).unwrap();
        assert_eq!(c[0], "long");
        assert_eq!(c.last().unwrap(), "void *");
    }

    #[test]
    fn evidence_from_ptr_selected_reg_store_and_outflow() {
        let mut ptr_regs: HashSet<RTLReg> = HashSet::new();
        ptr_regs.insert(7);
        let sigs: HashMap<Ident, CalleeSignature> = HashMap::new();
        let names: HashMap<String, Ident> = HashMap::new();
        let mut out: HashSet<(String, String)> = HashSet::new();

        // In-flow: ptr-selected reg 7 stored into struct_1.ofs_8 (plain long types).
        let store = field_store(1, 8, tlong(), ClightExpr::Etempvar(7, tlong()));
        scan_field_ptr_evidence(&store, &ptr_regs, &sigs, &names, &mut out);
        assert!(out.contains(&("struct_1".to_string(), "ofs_8".to_string())));

        // Out-flow: field value lands in ptr-selected reg 7.
        let load = ClightStmt::Sset(
            7,
            ClightExpr::Efield(
                Box::new(ClightExpr::Ederef(
                    Box::new(ClightExpr::Etempvar(1, tlong())),
                    tstruct(3),
                )),
                8 as Ident,
                tlong(),
            ),
        );
        scan_field_ptr_evidence(&load, &ptr_regs, &sigs, &names, &mut out);
        assert!(out.contains(&("struct_3".to_string(), "ofs_8".to_string())));

        // Non-pointer store: no evidence.
        let mut out2: HashSet<(String, String)> = HashSet::new();
        let store_int = field_store(5, 0, tlong(), ClightExpr::Etempvar(9, tlong()));
        scan_field_ptr_evidence(&store_int, &ptr_regs, &sigs, &names, &mut out2);
        assert!(out2.is_empty());
    }

    #[test]
    fn apply_patches_only_8byte_scalars() {
        let selection: HashMap<(String, String), String> = [
            (("struct_1".to_string(), "ofs_8".to_string()), "void *".to_string()),
            (("struct_1".to_string(), "ofs_0".to_string()), "void *".to_string()),
        ]
        .into_iter()
        .collect();
        let def = StructDef::new_struct(
            "struct_1",
            vec![
                StructField::new("ofs_0", CType::Int(IntSize::Int, Signedness::Signed)),
                StructField::new("ofs_8", CType::Int(IntSize::Long, Signedness::Signed)),
            ],
        );
        let mut structs = vec![ExtractedStruct {
            struct_id: 1,
            layout_hash: 0,
            is_canonical: true,
            definition: def,
        }];
        let patched = apply_struct_field_type_selection(&mut structs, &selection);
        assert_eq!(patched, 1, "only the 8-byte field may be retyped");
        assert_eq!(
            structs[0].definition.fields[1].ty,
            CType::Pointer(Box::new(CType::Void), TypeQualifiers::none())
        );
        // 4-byte field untouched (layout preserved).
        assert_eq!(
            structs[0].definition.fields[0].ty,
            CType::Int(IntSize::Int, Signedness::Signed)
        );
    }
}
