

use crate::decompile::passes::clight_pass::is_nonempty_stmt;
use crate::decompile::passes::csh_pass::ident_from_node;
use crate::decompile::elevator::DecompileDB;
use crate::x86::mach::Mreg;
use crate::x86::types::*;
use object::{Object, ObjectSection};
use std::collections::{BTreeMap, HashMap, HashSet};
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
        XType::Xany64 => 3,
        XType::Xint => 4,
        XType::Xintunsigned => 5,
        XType::Xlong => 6,
        XType::Xlongunsigned => 7,
        XType::Xint8signed | XType::Xint8unsigned => 8,
        XType::Xint16signed | XType::Xint16unsigned => 9,
        XType::Xfloat => 10,
        XType::Xsingle => 11,
        XType::Xptr => 12,
        XType::Xintptr | XType::Xfloatptr | XType::Xsingleptr => 12,
        XType::Xcharptr => 13,
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

pub fn extract_functions(db: &DecompileDB) -> Result<(Vec<FunctionData>, HashMap<usize, String>), String> {
    let mut functions = Vec::new();
    let mut func_map: HashMap<Address, FunctionData> = HashMap::new();
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

    let mut node_to_func: HashMap<Node, Address> = HashMap::new();
    for (node, func) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        node_to_func.insert(*node, *func);
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

    let mut func_params: HashMap<Address, Vec<RTLReg>> = HashMap::new();
    for (addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param") {
        let params = func_params.entry(*addr).or_default();
        if !params.contains(reg) {
            params.push(*reg);
        }
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
                        XType::Xptr | XType::Xcharptr | XType::Xintptr |
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

    for (addr, node, stmt) in db.rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt") {
        let is_goto_target = goto_targets.contains(node);
        if !is_nonempty_stmt(stmt) && !is_goto_target {
            continue;
        }
        if let Some(func) = func_map.get_mut(addr) {
            func.node_statements
                .entry(*node)
                .or_insert_with(Vec::new)
                .push(stmt.clone());
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


    // Collect ALL type candidates per register and pick the priority-based best.
    let mut reg_all_type_strs: HashMap<RTLReg, Vec<String>> = HashMap::new();
    let mut reg_best_xtype: HashMap<RTLReg, u8> = HashMap::new();
    let mut reg_best_xtype_val: HashMap<RTLReg, XType> = HashMap::new();
    for (reg, xtype) in db.rel_iter::<(RTLReg, XType)>("emit_var_type_candidate") {
        let type_str = xtype_to_string(xtype);
        let strs = reg_all_type_strs.entry(*reg).or_default();
        if !strs.contains(&type_str) {
            strs.push(type_str.clone());
        }
        let prio = xtype_priority(xtype);
        let prev_prio = reg_best_xtype.get(reg).copied().unwrap_or(0);
        if prio >= prev_prio {
            for func in func_map.values_mut() {
                if func.used_regs.contains(reg) || func.param_regs.contains(reg) {
                    func.var_types.insert(*reg, type_str.clone());
                }
            }
            reg_best_xtype.insert(*reg, prio);
            reg_best_xtype_val.insert(*reg, xtype.clone());
        }
    }

    // Upgrade param types using emit_var_type_candidate (includes XstructPtr from ClightFieldPass), which provides struct pointer info unavailable at signature resolution time.
    for func in func_map.values_mut() {
        for (i, reg) in func.param_regs.clone().iter().enumerate() {
            if let Some(best_xtype) = reg_best_xtype_val.get(reg) {
                let current = func.param_types.get(i);
                let should_upgrade = match (current, best_xtype) {
                    // Upgrade non-struct to struct pointer
                    (Some(ParamType::Typed(_)), XType::XstructPtr(sid)) => Some(ParamType::StructPointer(*sid)),
                    (Some(ParamType::Pointer), XType::XstructPtr(sid)) => Some(ParamType::StructPointer(*sid)),
                    (Some(ParamType::Integer), XType::XstructPtr(sid)) => Some(ParamType::StructPointer(*sid)),
                    // Upgrade int to pointer
                    (Some(ParamType::Typed(XType::Xlong | XType::Xint)), XType::Xptr | XType::Xcharptr | XType::Xintptr) => Some(ParamType::Pointer),
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
                        for alt in ["ptr_int", "ptr_char"] {
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
                candidates.sort_by(|a, b| type_str_sort_priority(b).cmp(&type_str_sort_priority(a)));
                func.var_type_candidates.insert(reg, candidates);
            }
        }
    }

    // No post-hoc type patching; statement candidates from clight_pass already have context-sensitive types from Phase 1+2.

    for (addr, reg, id) in db.rel_iter::<(Address, RTLReg, usize)>("reg_to_struct_id") {
        if let Some(func) = func_map.get_mut(addr) {
            let canonical_id = struct_canonical.get(id).copied().unwrap_or(*id);
            func.reg_struct_ids.insert(*reg, canonical_id);
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
        let mut callee_sigs: HashMap<Ident, CalleeSignature> = HashMap::new();

        // Pre-build symbol-to-idents map for O(1) lookup
        let mut symbol_to_idents: HashMap<Symbol, Vec<Ident>> = HashMap::new();
        for (id, sym) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
            symbol_to_idents.entry(*sym).or_default().push(*id);
        }

        for (name, param_count, ret_type, param_types) in
            db.rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("resolved_extern_signature")
        {
            if let Some(idents) = symbol_to_idents.get(name) {
                for &id in idents {
                    callee_sigs.insert(id, CalleeSignature {
                        param_count: *param_count,
                        return_type: *ret_type,
                        param_types: (**param_types).clone(),
                    });
                }
            }
        }

        for &(addr, count) in db.rel_iter::<(Address, usize)>("emit_function_param_count") {
            let ident = addr as Ident;
            if callee_sigs.contains_key(&ident) {
                continue;
            }
            let mut param_types = Vec::new();
            for &(a, _reg, ref xtype) in db.rel_iter::<(Address, RTLReg, XType)>("emit_function_param_type") {
                if a == addr {
                    param_types.push(*xtype);
                }
            }
            let ret_type = db.rel_iter::<(Address, XType)>("emit_function_return_type_xtype")
                .find(|(a, _)| *a == addr)
                .map(|(_, t)| *t)
                .unwrap_or(XType::Xvoid);

            callee_sigs.insert(ident, CalleeSignature {
                param_count: count,
                return_type: ret_type,
                param_types,
            });
        }

        for func in func_map.values_mut() {
            func.callee_signatures = callee_sigs.clone();
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
                    if new_count > existing_count {
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
        // x86-64 movss loads are sometimes lifted as MFloat64; fall back to MFloat32
        MemoryChunk::MFloat64 => {
            try_read_float64(remaining).or_else(|| try_read_float32(remaining))
        }
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

    let mut id_to_name: HashMap<usize, String> = HashMap::new();
    for (id, name) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
        id_to_name.insert(*id, name.to_string());
    }
    for (addr, name, _) in db.rel_iter::<(Address, Symbol, Symbol)>("symbols") {
        let id = *addr as usize;
        id_to_name.entry(id).or_insert_with(|| name.to_string());
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

    // Build map of global load chunk types for rodata constant resolution
    let global_chunks: HashMap<usize, MemoryChunk> = db
        .rel_iter::<(Ident, MemoryChunk)>("global_load_chunk")
        .map(|(id, chunk)| (*id, *chunk))
        .collect();

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

        // Try to resolve scalar constants from .rodata before string detection, since float constants (e.g. 3.0f) start with 0x00 and would be misidentified as empty strings.
        let scalar_value = if !is_string && !is_pointer {
            resolve_rodata_scalar(addr, &global_chunks, *id, &rodata_ranges)
        } else {
            None
        };

        if !is_string && scalar_value.is_none() {
            for section in obj_file.sections() {
                 let sect_addr = section.address();
                 let sect_size = section.size();

                 if addr >= sect_addr && addr < sect_addr + sect_size {
                     if let Ok(data) = section.data() {
                         let offset = (addr - sect_addr) as usize;
                         if offset < data.len() {
                             let remaining = &data[offset..];
                             if !remaining.is_empty() && remaining[0] == 0 {
                                 is_string = true;
                                 content = vec![0];
                             } else {
                                 let check_len = std::cmp::min(remaining.len(), 128);
                                 let chunk = &remaining[0..check_len];
                                 if let Some(len) = is_string_literal(chunk) {
                                     is_string = true;
                                     content = chunk[0..len].to_vec();
                                 }
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

#[derive(Debug, Clone, Default)]
pub struct IfThenElseInfo {
    pub if_branch_nodes: Vec<Node>,
    pub else_branch_nodes: Vec<Node>,
    pub merge_node: Node,
}

pub fn extract_ifthenelse_bodies(
    db: &DecompileDB,
) -> HashMap<Address, HashMap<Node, IfThenElseInfo>> {
    let mut result: HashMap<Address, HashMap<Node, IfThenElseInfo>> = HashMap::new();

    for (func, branch, node, is_if) in db.rel_iter::<(Address, Node, Node, bool)>("emit_ifthenelse_body") {
        let info = result
            .entry(*func)
            .or_default()
            .entry(*branch)
            .or_insert_with(IfThenElseInfo::default);

        if *is_if {
            info.if_branch_nodes.push(*node);
        } else {
            info.else_branch_nodes.push(*node);
        }
    }

    for (func, branch, merge) in db.rel_iter::<(Address, Node, Node)>("ifthenelse_merge_point") {
        if let Some(func_map) = result.get_mut(func) {
            if let Some(info) = func_map.get_mut(branch) {
                info.merge_node = *merge;
            }
        }
    }

    result
}

use crate::decompile::passes::c_pass::types::{CType, IntSize, Signedness, StructDef, StructField, TypeQualifiers};
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
        result
            .entry(*func_addr)
            .or_default()
            .entry(*loop_head)
            .or_insert_with(LoopInfo::default)
            .exit_node = Some(*exit_node);
    }

    for (func_addr, loop_header, step_node) in db.rel_iter::<(Address, Node, Node)>("suppress_step") {
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

    // Pre-index loop_exit_branch for O(1) lookup
    let mut exit_branch_index: HashMap<(Address, Node, Node), (Condition, Arc<Vec<CsharpminorExpr>>, bool)> = HashMap::new();
    for (f, h, en, cond, args, _exit_target, _cont_target, inverted) in
        db.rel_iter::<(Address, Node, Node, Condition, Arc<Vec<CsharpminorExpr>>, Node, Node, bool)>("loop_exit_branch")
    {
        exit_branch_index.insert((*f, *h, *en), (cond.clone(), args.clone(), *inverted));
    }

    for (func_addr, loop_header, exit_node) in db.rel_iter::<(Address, Node, Node)>("primary_exit_node") {
        if let Some((cond, args, inverted)) = exit_branch_index.get(&(*func_addr, *loop_header, *exit_node)) {
            let info = result
                .entry(*func_addr)
                .or_default()
                .entry(*loop_header)
                .or_insert_with(LoopInfo::default);
            info.primary_exit = Some(PrimaryExitData {
                exit_node: *exit_node,
                condition: cond.clone(),
                args: args.clone(),
                inverted: *inverted,
            });
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
        info.break_stmts.insert(*exit_node, break_stmt.clone());
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
            variants.first().map(|v| fieldtype_to_ctype(v))
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

    // Pre-collect efield-detected fields per struct ID (merging across functions); these come from ClightFieldPass and may contain fields not in struct_recovery.
    let reg_to_canonical_ids: HashMap<u64, usize> = db
        .rel_iter::<(u64, u64, usize)>("reg_to_struct_id")
        .map(|&(_, reg, sid)| (reg, sid))
        .collect();

    let mut efield_extra_fields: HashMap<usize, BTreeMap<i64, (Ident, MemoryChunk)>> = HashMap::new();
    for (_func_addr, base_offset, fields) in
        db.rel_iter::<(u64, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>)>("emit_struct_fields")
    {
        let reg = *base_offset as u64;
        let struct_id = reg_to_canonical_ids.get(&reg)
            .copied()
            .unwrap_or_else(|| base_offset.unsigned_abs() as usize);

        let entry = efield_extra_fields.entry(struct_id).or_default();
        for (field_offset, field_name, chunk) in fields.iter() {
            entry.entry(*field_offset).or_insert((*field_name, chunk.clone()));
        }
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

    if structs.is_empty() {
        let canonical_ids: HashSet<usize> = db
            .rel_iter::<(u64, usize)>("emit_canonical_struct_id")
            .map(|(_hash, id)| *id)
            .collect();

        let mut seen_hashes = HashSet::new();
        for (struct_id, fields) in db.rel_iter::<(usize, Arc<Vec<(i64, usize, MemoryChunk)>>)>("emit_inferred_struct_layout") {
            let layout_hash = crate::decompile::analysis::struct_recovery_pass::compute_layout_hash_from_tuples(fields);
            
            let is_canonical = canonical_ids.contains(struct_id);
            if !is_canonical {
                continue;
            }

            if seen_hashes.contains(&layout_hash) {
                continue;
            }
            seen_hashes.insert(layout_hash);

            let struct_name = format!("struct_{:x}", struct_id);
            let struct_fields: Vec<StructField> = fields
                .iter()
                .map(|(offset, size, chunk)| {
                    let field_name = db.rel_iter::<(u64, i64, String, MemoryChunk)>("struct_field")
                        .find(|(sid, off, _, _)| *sid == (*struct_id as u64) && *off == *offset)
                        .map(|(_, _, name, _)| name.clone())
                        .unwrap_or_else(|| format!("field_{:x}", offset));

                    let field_type = chunk_to_ctype(*chunk, *size);
                    StructField::new(field_name, field_type)
                })
                .collect();

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
    
    for (struct_id, fields) in db.rel_iter::<(usize, Arc<Vec<(i64, usize, MemoryChunk)>>)>("emit_inferred_struct_layout") {
        if !canonical_ids.is_empty() && !canonical_ids.contains(struct_id) {
            continue;
        }
        let mapped_fields = fields.iter().map(|(offset, _size, chunk)| {
             let field_name = db.rel_iter::<(u64, i64, String, MemoryChunk)>("struct_field")
                    .find(|(sid, off, _, _)| *sid == (*struct_id as u64) && *off == *offset)
                    .map(|(_, _, name, _)| name.clone())
                    .unwrap_or_else(|| format!("field_{:x}", offset));
             
             (*offset, field_name, *chunk)
        }).collect();
        layouts.insert(*struct_id, mapped_fields);
    }
    
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
        MemoryChunk::MBool => CType::Bool,
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
