
use log::info;
use std::collections::{HashMap, BTreeMap, HashSet};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::x86::mach::Mreg;
use crate::x86::op::{Addressing, Operation};
use crate::x86::types::*;
use ascent::ascent_par;


fn chunk_byte_size(chunk: &MemoryChunk) -> usize {
    match chunk {
        MemoryChunk::MBool | MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned => 1,
        MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned => 2,
        MemoryChunk::MInt32 | MemoryChunk::MFloat32 | MemoryChunk::MAny32 => 4,
        MemoryChunk::MInt64 | MemoryChunk::MFloat64 | MemoryChunk::MAny64 => 8,
        MemoryChunk::Unknown => 4,
    }
}

const MAX_STACK_STRUCT_SIZE: i64 = 1024;
const STRUCT_KEEP_RATIO: f64 = 1.0;


// Pointer/stack/global struct detection via load/store offset analysis
ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct StructRecoveryProgram;

    relation rtl_inst(Node, RTLInst);
    relation ltl_inst(Node, LTLInst);
    relation reg_rtl(Node, Mreg, RTLReg);
    relation instr_in_function(Node, Address);
    relation is_ptr(RTLReg);
    relation emit_var_type_candidate(RTLReg, XType);
    relation call_target_func(Node, Address);
    relation call_arg_mapping(Node, usize, RTLReg);
    relation emit_function(Address, Symbol, Node);
    relation known_extern_signature(Symbol, usize, XType, Arc<Vec<XType>>);
    relation string_data(String, String, usize);
    relation ident_to_symbol(Ident, Symbol);
    relation stack_var(Address, Address, i64, RTLReg);
    relation stack_var_chunk(Address, i64, MemoryChunk);
    relation is_global_array(Ident, usize, usize);


    // (base_ptr_reg, offset, chunk, value_reg, func)
    relation ptr_deref(RTLReg, i64, MemoryChunk, RTLReg, Address);

    ptr_deref(base_reg, *ofs, *chunk, *dst, *func) <--
        rtl_inst(node, ?RTLInst::Iload(chunk, Addressing::Aindexed(ofs), args, dst)),
        if args.len() >= 1,
        let base_reg = args[0],
        is_ptr(&base_reg),
        instr_in_function(node, func);

    ptr_deref(base_reg, *ofs, *chunk, *src, *func) <--
        rtl_inst(node, ?RTLInst::Istore(chunk, Addressing::Aindexed(ofs), args, src)),
        if args.len() >= 1,
        let base_reg = args[0],
        is_ptr(&base_reg),
        instr_in_function(node, func);

    ptr_deref(base_reg, *ofs, *chunk, *dst, *func) <--
        rtl_inst(node, ?RTLInst::Iload(chunk, Addressing::Aindexed2(ofs), args, dst)),
        if args.len() >= 1,
        let base_reg = args[0],
        is_ptr(&base_reg),
        instr_in_function(node, func);

    ptr_deref(base_reg, *ofs, *chunk, *src, *func) <--
        rtl_inst(node, ?RTLInst::Istore(chunk, Addressing::Aindexed2(ofs), args, src)),
        if args.len() >= 1,
        let base_reg = args[0],
        is_ptr(&base_reg),
        instr_in_function(node, func);


    #[local] relation call_site(Node, Symbol);
    #[local] relation call_arg(Node, usize, RTLReg);

    call_site(node, *sym) <--
        call_target_func(node, callee),
        emit_function(callee, sym, _);

    call_arg(call_node, *pos, *reg) <--
        call_arg_mapping(call_node, pos, reg);

    #[local] relation ptr_has_offset(RTLReg, i64);
    ptr_has_offset(reg, ofs) <-- ptr_deref(reg, ofs, _, _, _);

    #[local] relation ptr_has_multiple_offsets(RTLReg);
    ptr_has_multiple_offsets(reg) <--
        ptr_has_offset(reg, a),
        ptr_has_offset(reg, b),
        if a != b;

    // Reject if ptr passed to extern expecting scalar
    #[local] relation ptr_rejected_as_struct(RTLReg);

    ptr_rejected_as_struct(arg_reg) <--
        call_site(node, func_name),
        call_arg(node, arg_idx, arg_reg),
        known_extern_signature(func_name, _, _, params),
        if *arg_idx < params.len(),
        if matches!(params[*arg_idx],
            XType::Xint | XType::Xintunsigned |
            XType::Xlong | XType::Xlongunsigned |
            XType::Xfloat | XType::Xsingle |
            XType::Xbool | XType::Xint8signed | XType::Xint8unsigned |
            XType::Xint16signed | XType::Xint16unsigned);

    // Reject if variable-indexed access (likely array)
    #[local] relation ptr_has_variable_index(RTLReg);

    ptr_has_variable_index(base_reg) <--
        rtl_inst(_, ?RTLInst::Iload(_, Addressing::Aindexed2scaled(_, _), args, _)),
        if args.len() >= 1,
        let base_reg = args[0],
        is_ptr(&base_reg);

    ptr_has_variable_index(base_reg) <--
        rtl_inst(_, ?RTLInst::Istore(_, Addressing::Aindexed2scaled(_, _), args, _)),
        if args.len() >= 1,
        let base_reg = args[0],
        is_ptr(&base_reg);

    relation ptr_is_struct_candidate(RTLReg);
    ptr_is_struct_candidate(reg) <--
        ptr_has_multiple_offsets(reg),
        !ptr_rejected_as_struct(reg),
        !ptr_has_variable_index(reg);

    #[local] relation ptr_is_data(RTLReg);
    ptr_is_data(reg) <--
        is_ptr(reg),
        ptr_has_offset(reg, _),
        !ptr_has_multiple_offsets(reg);

    ptr_is_data(reg) <--
        is_ptr(reg),
        ptr_has_offset(reg, _),
        ptr_rejected_as_struct(reg);


    relation struct_field_type(RTLReg, i64, MemoryChunk, XType);

    struct_field_type(base_reg, ofs, chunk, xtype) <--
        ptr_deref(base_reg, ofs, chunk, value_reg, _),
        ptr_is_struct_candidate(base_reg),
        emit_var_type_candidate(value_reg, xtype);


    #[local] relation string_symbol(String);
    string_symbol(label.clone()) <-- string_data(label, _, _);

    #[local] relation is_charptr_from_string(RTLReg);
    is_charptr_from_string(rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Oindirectsymbol(sym_id), _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg),
        ident_to_symbol(sym_id, label),
        string_symbol(label.to_string());

    #[local] relation data_ptr_chunk(RTLReg, MemoryChunk);
    data_ptr_chunk(reg, chunk) <--
        ptr_is_data(reg),
        ptr_deref(reg, 0, chunk, _, _);

    relation refined_ptr_type(RTLReg, XType);

    refined_ptr_type(reg, XType::Xcharptr) <-- is_charptr_from_string(reg);

    refined_ptr_type(reg, XType::Xcharptr) <--
        data_ptr_chunk(reg, chunk),
        if matches!(chunk, MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned | MemoryChunk::MBool),
        !is_charptr_from_string(reg);

    refined_ptr_type(reg, XType::Xintptr) <--
        data_ptr_chunk(reg, chunk),
        if matches!(chunk, MemoryChunk::MInt32 | MemoryChunk::MAny32),
        !is_charptr_from_string(reg);

    refined_ptr_type(reg, XType::Xfloatptr) <--
        data_ptr_chunk(reg, ?MemoryChunk::MFloat64),
        !is_charptr_from_string(reg);

    refined_ptr_type(reg, XType::Xsingleptr) <--
        data_ptr_chunk(reg, ?MemoryChunk::MFloat32),
        !is_charptr_from_string(reg);


    // Stack struct detection via LEA base offsets
    #[local] relation stack_lea_base(Address, i64);

    stack_lea_base(*func, *base_ofs) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Olea(Addressing::Ainstack(base_ofs)), _, _)),
        instr_in_function(node, func);

    stack_lea_base(*func, *base_ofs) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Oleal(Addressing::Ainstack(base_ofs)), _, _)),
        instr_in_function(node, func);

    relation stack_lea_reg(Address, i64, RTLReg);

    stack_lea_reg(*func, *base_ofs, *dst) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Olea(Addressing::Ainstack(base_ofs)), _, dst)),
        instr_in_function(node, func);

    stack_lea_reg(*func, *base_ofs, *dst) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Oleal(Addressing::Ainstack(base_ofs)), _, dst)),
        instr_in_function(node, func);

    // (func, base_ofs, field_ofs, chunk, value_rtl_reg)
    relation stack_struct_field(Address, i64, i64, MemoryChunk, RTLReg);

    stack_struct_field(*func, *base_ofs, *ofs - *base_ofs, *chunk, *rtl_reg) <--
        stack_lea_base(func, base_ofs),
        stack_var(func, _, ofs, rtl_reg),
        stack_var_chunk(func, ofs, chunk),
        if *ofs >= *base_ofs && *ofs < *base_ofs + MAX_STACK_STRUCT_SIZE;

    relation stack_is_struct_candidate(Address, i64);

    stack_is_struct_candidate(func, base_ofs) <--
        stack_struct_field(func, base_ofs, a, _, _),
        stack_struct_field(func, base_ofs, b, _, _),
        if a != b;


    // Global struct detection via constant-offset accesses
    relation global_deref(Ident, i64, MemoryChunk, RTLReg);

    global_deref(*ident, *ofs, *chunk, *dst) <--
        rtl_inst(_, ?RTLInst::Iload(chunk, Addressing::Aglobal(ident, ofs), _, dst));

    global_deref(*ident, *ofs, *chunk, *src) <--
        rtl_inst(_, ?RTLInst::Istore(chunk, Addressing::Aglobal(ident, ofs), _, src));

    #[local] relation global_has_offset(Ident, i64);
    global_has_offset(ident, ofs) <-- global_deref(ident, ofs, _, _);

    #[local] relation global_has_multiple_offsets(Ident);
    global_has_multiple_offsets(ident) <--
        global_has_offset(ident, a),
        global_has_offset(ident, b),
        if a != b;

    #[local] relation global_has_variable_index(Ident);

    global_has_variable_index(*ident) <--
        rtl_inst(_, ?RTLInst::Iload(_, Addressing::Abasedscaled(_, ident, _), _, _));
    global_has_variable_index(*ident) <--
        rtl_inst(_, ?RTLInst::Istore(_, Addressing::Abasedscaled(_, ident, _), _, _));
    global_has_variable_index(*ident) <--
        rtl_inst(_, ?RTLInst::Iload(_, Addressing::Abased(ident, _), _, _));
    global_has_variable_index(*ident) <--
        rtl_inst(_, ?RTLInst::Istore(_, Addressing::Abased(ident, _), _, _));

    relation global_is_struct_candidate(Ident);

    global_is_struct_candidate(ident) <--
        global_has_multiple_offsets(ident),
        !is_global_array(ident, _, _),
        !global_has_variable_index(ident);
}


pub struct StructRecoveryPass;

impl IRPass for StructRecoveryPass {
    fn name(&self) -> &'static str { "struct_recovery" }

    fn run(&self, db: &mut DecompileDB) {
        // Enrich is_ptr for param registers used as indexed load/store bases (missed by Datalog due to physical register reuse); only params to avoid ptr_deref explosion
        {
            use crate::x86::op::Addressing;
            let existing_ptrs: std::collections::HashSet<RTLReg> = db
                .rel_iter::<(RTLReg,)>("is_ptr")
                .map(|&(r,)| r)
                .collect();
            let param_regs: std::collections::HashSet<RTLReg> = db
                .rel_iter::<(Address, RTLReg)>("emit_function_param_candidate")
                .map(|&(_, reg)| reg)
                .collect();
            let new_ptrs: Vec<RTLReg> = db.rel_iter::<(Node, RTLInst)>("rtl_inst")
                .filter_map(|&(_, ref inst)| {
                    let (addr_mode, args) = match inst {
                        RTLInst::Iload(_, addr, args, _) => (addr, args),
                        RTLInst::Istore(_, addr, args, _) => (addr, args),
                        _ => return None,
                    };
                    if !matches!(addr_mode,
                        Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _))
                    {
                        return None;
                    }
                    args.first().copied()
                        .filter(|r| param_regs.contains(r) && !existing_ptrs.contains(r))
                })
                .collect();
            for base_rtl in new_ptrs {
                db.rel_push("is_ptr", (base_rtl,));
            }
        }

        let mut prog = StructRecoveryProgram::default();
        prog.swap_db_fields(db);
        // Do not clear emit_var_type_candidate; upstream data needed for struct_field_type
        prog.run();
        prog.swap_db_fields(db);

        post_process_structs(db);

        // Post-Datalog: push Xptr for non-param registers used at 2+ offsets (can't add to is_ptr pre-Datalog due to ptr_deref explosion)
        {
            use crate::x86::op::Addressing;
            let existing_ptrs: std::collections::HashSet<RTLReg> = db
                .rel_iter::<(RTLReg,)>("is_ptr")
                .map(|&(r,)| r)
                .collect();
            let mut base_offsets: HashMap<RTLReg, HashSet<i64>> = HashMap::new();
            for &(_, ref inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
                let (addr_mode, args) = match inst {
                    RTLInst::Iload(_, addr, args, _) => (addr, args),
                    RTLInst::Istore(_, addr, args, _) => (addr, args),
                    _ => continue,
                };
                let ofs = match addr_mode {
                    Addressing::Aindexed(ofs) => *ofs,
                    Addressing::Aindexed2(ofs) => *ofs,
                    Addressing::Aindexed2scaled(_, ofs) => *ofs,
                    _ => continue,
                };
                if let Some(&base) = args.first() {
                    if !existing_ptrs.contains(&base) {
                        base_offsets.entry(base).or_default().insert(ofs);
                    }
                }
            }
            for (base_rtl, offsets) in &base_offsets {
                if offsets.len() >= 2 {
                    db.rel_push("emit_var_type_candidate", (*base_rtl, XType::Xptr));
                }
            }
        }

        // Post-Datalog: push Xfuncptr for registers used as indirect call targets.
        {
            let funcptr_regs: Vec<RTLReg> = db.rel_iter::<(Node, RTLInst)>("rtl_inst")
                .filter_map(|&(_, ref inst)| match inst {
                    RTLInst::Icall(_, either::Either::Left(reg), _, _, _) => Some(*reg),
                    RTLInst::Itailcall(_, either::Either::Left(reg), _) => Some(*reg),
                    _ => None,
                })
                .collect();
            for reg in funcptr_regs {
                db.rel_push("emit_var_type_candidate", (reg, XType::Xfuncptr));
            }
        }
    }

    fn inputs(&self) -> &'static [&'static str] {
        &[
            "rtl_inst", "ltl_inst", "reg_rtl",
            "instr_in_function", "is_ptr", "emit_var_type_candidate",
            "call_target_func", "call_arg_mapping",
            "emit_function", "known_extern_signature",
            "string_data", "ident_to_symbol",
            "stack_var", "stack_var_chunk",
            "is_global_array",
            "emit_function_param_candidate", "func_has_param_at_position",
            "emit_function_return",
        ]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "emit_var_type_candidate",
            "emit_struct_field", "emit_var_is_struct_candidate",
            "global_struct_catalog", "emit_canonical_struct_id",
            "struct_id_to_canonical", "emit_struct_def",
            "reg_to_struct_id",
            "func_param_struct_type_candidate", "func_return_struct_type",
            "ptr_deref", "ptr_is_struct_candidate",
            "struct_field_type", "refined_ptr_type",
            "stack_struct_field", "stack_is_struct_candidate", "stack_lea_reg",
            "global_deref", "global_is_struct_candidate",
        ]
    }
}


#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct InferredField {
    offset: i64,
    chunk: MemoryChunk,
}

#[derive(Debug, Clone)]
struct CandidateStruct {
    ptr_regs: Vec<(Address, RTLReg)>,
    fields: Vec<InferredField>,
    access_count: usize,
}

// Returns None if fields overlap or form a uniform-stride array
fn try_build_layout(accesses: &[(i64, MemoryChunk)]) -> Option<Vec<InferredField>> {
    let mut field_map: BTreeMap<i64, MemoryChunk> = BTreeMap::new();
    for &(ofs, chunk) in accesses {
        let entry = field_map.entry(ofs).or_insert(chunk);
        if chunk_byte_size(&chunk) > chunk_byte_size(entry) {
            *entry = chunk;
        }
    }

    let fields: Vec<InferredField> = field_map
        .into_iter()
        .map(|(offset, chunk)| InferredField { offset, chunk })
        .collect();

    if fields.len() < 2 {
        return None;
    }

    let sorted: Vec<(i64, usize)> = fields.iter()
        .map(|f| (f.offset, chunk_byte_size(&f.chunk)))
        .collect();
    if check_field_overlap(&sorted) {
        return None;
    }

    let offset_chunks: Vec<(i64, MemoryChunk)> = fields.iter()
        .map(|f| (f.offset, f.chunk))
        .collect();
    if is_uniform_stride(&offset_chunks) {
        return None;
    }

    Some(fields)
}

fn post_process_structs(db: &mut DecompileDB) {
    let struct_candidates: Vec<RTLReg> = db
        .rel_iter::<(RTLReg,)>("ptr_is_struct_candidate")
        .map(|&(r,)| r)
        .collect();

    let ptr_derefs: Vec<(RTLReg, i64, MemoryChunk, RTLReg, Address)> = db
        .rel_iter::<(RTLReg, i64, MemoryChunk, RTLReg, Address)>("ptr_deref")
        .cloned()
        .collect();

    let struct_field_types: Vec<(RTLReg, i64, MemoryChunk, XType)> = db
        .rel_iter::<(RTLReg, i64, MemoryChunk, XType)>("struct_field_type")
        .cloned()
        .collect();

    let refined_ptrs: Vec<(RTLReg, XType)> = db
        .rel_iter::<(RTLReg, XType)>("refined_ptr_type")
        .cloned()
        .collect();

    let existing_types: HashMap<RTLReg, XType> = db
        .rel_iter::<(RTLReg, XType)>("emit_var_type_candidate")
        .map(|&(r, t)| (r, t))
        .collect();

    let stack_candidates: Vec<(Address, i64)> = db
        .rel_iter::<(Address, i64)>("stack_is_struct_candidate")
        .cloned()
        .collect();

    let stack_fields: Vec<(Address, i64, i64, MemoryChunk, RTLReg)> = db
        .rel_iter::<(Address, i64, i64, MemoryChunk, RTLReg)>("stack_struct_field")
        .cloned()
        .collect();

    let stack_lea_regs: Vec<(Address, i64, RTLReg)> = db
        .rel_iter::<(Address, i64, RTLReg)>("stack_lea_reg")
        .cloned()
        .collect();

    let global_candidates: Vec<(Ident,)> = db
        .rel_iter::<(Ident,)>("global_is_struct_candidate")
        .cloned()
        .collect();

    let global_derefs: Vec<(Ident, i64, MemoryChunk, RTLReg)> = db
        .rel_iter::<(Ident, i64, MemoryChunk, RTLReg)>("global_deref")
        .cloned()
        .collect();

    let mut layout_access_count: HashMap<Vec<InferredField>, usize> = HashMap::new();
    let mut layout_ptr_regs: HashMap<Vec<InferredField>, Vec<(Address, RTLReg)>> = HashMap::new();

    let mut field_xtype_map: HashMap<(RTLReg, i64), Vec<XType>> = HashMap::new();
    for &(base, ofs, _, xtype) in &struct_field_types {
        field_xtype_map.entry((base, ofs)).or_default().push(xtype);
    }

    let candidate_set: HashSet<RTLReg> = struct_candidates.iter().copied().collect();
    let mut ptr_deref_map: HashMap<RTLReg, Vec<(i64, MemoryChunk, RTLReg, Address)>> = HashMap::new();
    for &(base, ofs, chunk, val, func) in &ptr_derefs {
        if candidate_set.contains(&base) {
            ptr_deref_map.entry(base).or_default().push((ofs, chunk, val, func));
        }
    }

    for &ptr_reg in &struct_candidates {
        let accesses = match ptr_deref_map.get(&ptr_reg) {
            Some(a) => a,
            None => continue,
        };

        let ofs_chunks: Vec<(i64, MemoryChunk)> = accesses.iter()
            .map(|&(ofs, chunk, _, _)| (ofs, chunk))
            .collect();

        if let Some(fields) = try_build_layout(&ofs_chunks) {
            let func = accesses.first().map(|a| a.3).unwrap_or(0);
            layout_ptr_regs.entry(fields.clone()).or_default().push((func, ptr_reg));
            *layout_access_count.entry(fields).or_insert(0) += accesses.len();
        }
    }

    let mut stack_field_map: HashMap<(Address, i64), Vec<(i64, MemoryChunk, RTLReg)>> = HashMap::new();
    for &(func, base_ofs, field_ofs, chunk, rtl_reg) in &stack_fields {
        stack_field_map.entry((func, base_ofs)).or_default().push((field_ofs, chunk, rtl_reg));
    }

    let mut stack_lea_map: HashMap<(Address, i64), Vec<RTLReg>> = HashMap::new();
    for &(func, base_ofs, reg) in &stack_lea_regs {
        stack_lea_map.entry((func, base_ofs)).or_default().push(reg);
    }

    for &(func, base_ofs) in &stack_candidates {
        let fields_data = match stack_field_map.get(&(func, base_ofs)) {
            Some(f) => f,
            None => continue,
        };

        let ofs_chunks: Vec<(i64, MemoryChunk)> = fields_data.iter()
            .map(|&(field_ofs, chunk, _)| (field_ofs, chunk))
            .collect();

        if let Some(fields) = try_build_layout(&ofs_chunks) {
            if let Some(lea_regs) = stack_lea_map.get(&(func, base_ofs)) {
                for &reg in lea_regs {
                    layout_ptr_regs.entry(fields.clone()).or_default().push((func, reg));
                }
            }

            if let Some(lea_regs) = stack_lea_map.get(&(func, base_ofs)) {
                for &lea_reg in lea_regs {
                    for &(field_ofs, _, rtl_reg) in fields_data {
                        if let Some(&xtype) = existing_types.get(&rtl_reg) {
                            field_xtype_map.entry((lea_reg, field_ofs)).or_default().push(xtype);
                        }
                    }
                }
            }

            *layout_access_count.entry(fields).or_insert(0) += fields_data.len();
        }
    }

    let global_candidate_set: HashSet<Ident> = global_candidates.iter().map(|&(id,)| id).collect();

    let mut global_deref_map: HashMap<Ident, Vec<(i64, MemoryChunk, RTLReg)>> = HashMap::new();
    for &(ident, ofs, chunk, val_reg) in &global_derefs {
        if global_candidate_set.contains(&ident) {
            global_deref_map.entry(ident).or_default().push((ofs, chunk, val_reg));
        }
    }

    for &(ident,) in &global_candidates {
        let accesses = match global_deref_map.get(&ident) {
            Some(a) => a,
            None => continue,
        };

        let ofs_chunks: Vec<(i64, MemoryChunk)> = accesses.iter()
            .map(|&(ofs, chunk, _)| (ofs, chunk))
            .collect();

        if let Some(fields) = try_build_layout(&ofs_chunks) {
            for &(ofs, _, val_reg) in accesses {
                if let Some(&xtype) = existing_types.get(&val_reg) {
                    field_xtype_map.entry((val_reg, ofs)).or_default().push(xtype);
                }
            }

            *layout_access_count.entry(fields).or_insert(0) += accesses.len();
        }
    }

    // Rank by access count, keep top fraction
    let mut candidates: Vec<CandidateStruct> = layout_access_count
        .into_iter()
        .map(|(fields, access_count)| {
            let ptr_regs = layout_ptr_regs.remove(&fields).unwrap_or_default();
            CandidateStruct { ptr_regs, fields, access_count }
        })
        .collect();

    candidates.sort_by(|a, b| b.access_count.cmp(&a.access_count));

    let cutoff = if candidates.is_empty() { 0 }
    else if candidates.len() <= 5 { candidates.len() }
    else { std::cmp::max(1, (candidates.len() as f64 * STRUCT_KEEP_RATIO) as usize) };
    candidates.truncate(cutoff);

    let mut next_struct_id: usize = 1;
    let mut hash_to_canonical: HashMap<u64, usize> = HashMap::new();
    let mut struct_fields_map: HashMap<usize, Vec<InferredField>> = HashMap::new();
    let mut var_struct_map: Vec<(Address, RTLReg, usize)> = Vec::new();
    let mut id_to_canonical: HashMap<usize, usize> = HashMap::new();

    for candidate in &candidates {
        let layout_hash = compute_layout_hash(&candidate.fields);
        let canonical_id = *hash_to_canonical.entry(layout_hash).or_insert_with(|| {
            let id = next_struct_id;
            next_struct_id += 1;
            struct_fields_map.insert(id, candidate.fields.clone());
            id
        });
        id_to_canonical.insert(canonical_id, canonical_id);
        for &(func, reg) in &candidate.ptr_regs {
            var_struct_map.push((func, reg, canonical_id));
        }
    }

    let mut field_type_info: HashMap<(usize, i64), Vec<XType>> = HashMap::new();

    for candidate in &candidates {
        let layout_hash = compute_layout_hash(&candidate.fields);
        let struct_id = hash_to_canonical[&layout_hash];
        for &(_func, ptr_reg) in &candidate.ptr_regs {
            for field in &candidate.fields {
                if let Some(xtypes) = field_xtype_map.get(&(ptr_reg, field.offset)) {
                    field_type_info
                        .entry((struct_id, field.offset))
                        .or_default()
                        .extend(xtypes);
                }
            }
        }
    }

    let mut emit_struct_field: Vec<(usize, usize, i64, FieldType, Ident)> = Vec::new();
    for (&struct_id, fields) in &struct_fields_map {
        for (field_idx, field) in fields.iter().enumerate() {
            let field_type = if let Some(xtypes) = field_type_info.get(&(struct_id, field.offset)) {
                xtype_to_field_type(pick_best_xtype(xtypes))
            } else {
                FieldType::Scalar(field.chunk)
            };
            let field_name = make_field_ident(field.offset, field.chunk);
            emit_struct_field.push((struct_id, field_idx, field.offset, field_type, field_name));
        }
    }

    let esf: ascent::boxcar::Vec<_> = emit_struct_field.into_iter().collect();
    db.rel_set("emit_struct_field", esf);

    let evis: ascent::boxcar::Vec<_> = var_struct_map.iter().cloned().collect();
    db.rel_set("emit_var_is_struct_candidate", evis);

    let mut gsc_vec: Vec<(u64, usize, usize, usize)> = Vec::new();
    for (&layout_hash, &canonical_id) in &hash_to_canonical {
        if let Some(fields) = struct_fields_map.get(&canonical_id) {
            gsc_vec.push((layout_hash, canonical_id, fields.len(), compute_total_size(fields)));
        }
    }
    let gsc: ascent::boxcar::Vec<_> = gsc_vec.into_iter().collect();
    db.rel_set("global_struct_catalog", gsc);

    let ecsi: ascent::boxcar::Vec<_> = hash_to_canonical.iter().map(|(&h, &id)| (h, id)).collect();
    db.rel_set("emit_canonical_struct_id", ecsi);

    let sitc: ascent::boxcar::Vec<_> = id_to_canonical.iter().map(|(&id, &c)| (id, c)).collect();
    db.rel_set("struct_id_to_canonical", sitc);

    let mut esd_vec: Vec<(usize, usize, usize)> = Vec::new();
    for (&struct_id, fields) in &struct_fields_map {
        esd_vec.push((struct_id, fields.len(), compute_total_size(fields)));
    }
    let esd: ascent::boxcar::Vec<_> = esd_vec.into_iter().collect();
    db.rel_set("emit_struct_def", esd);

    let mut reg_struct_id: HashMap<RTLReg, usize> = HashMap::new();
    for &(_, reg, sid) in &var_struct_map {
        reg_struct_id.insert(reg, sid);
    }

    // Push reg->canonical struct ID mapping to DB for ClightFieldPass and clight_select bridging
    let rtsi: ascent::boxcar::Vec<_> = var_struct_map.iter().map(|&(addr, reg, sid)| (addr, reg, sid)).collect();
    db.rel_set("reg_to_struct_id", rtsi);

    let abi_regs = &crate::x86::abi::abi_config().int_arg_regs;

    let func_entry_nodes: HashSet<Address> = db
        .rel_iter::<(Address, RTLReg)>("emit_function_param_candidate")
        .map(|&(func, _)| func)
        .collect();
    let mut entry_mreg_to_rtl: HashMap<(Address, Mreg), RTLReg> = HashMap::new();
    for &(node, mreg, rtl) in db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl") {
        if func_entry_nodes.contains(&node) {
            entry_mreg_to_rtl.insert((node, mreg), rtl);
        }
    }

    let param_positions: HashSet<(Address, usize)> = db
        .rel_iter::<(Address, usize)>("func_has_param_at_position")
        .cloned()
        .collect();

    let mut fpst: Vec<(Address, usize, usize)> = Vec::new();
    for &(func, param_reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param_candidate") {
        if let Some(&sid) = reg_struct_id.get(&param_reg) {
            for (pos, abi_mreg) in abi_regs.iter().enumerate() {
                if param_positions.contains(&(func, pos)) {
                    if let Some(&rtl) = entry_mreg_to_rtl.get(&(func, *abi_mreg)) {
                        if rtl == param_reg {
                            fpst.push((func, pos, sid));
                            break;
                        }
                    }
                }
            }
        }
    }
    let fpst_bv: ascent::boxcar::Vec<_> = fpst.into_iter().collect();
    db.rel_set("func_param_struct_type_candidate", fpst_bv);

    let mut frst: Vec<(Address, usize)> = Vec::new();
    for &(func, ret_reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_return") {
        if let Some(&sid) = reg_struct_id.get(&ret_reg) {
            frst.push((func, sid));
        }
    }
    let frst_bv: ascent::boxcar::Vec<_> = frst.into_iter().collect();
    db.rel_set("func_return_struct_type", frst_bv);

    for &(reg, xtype) in &refined_ptrs {
        if let Some(existing) = existing_types.get(&reg) {
            if matches!(existing, XType::Xcharptr | XType::Xintptr | XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr) {
                continue;
            }
        }
        db.rel_push("emit_var_type_candidate", (reg, xtype));
    }

    for &(_, reg, sid) in &var_struct_map {
        db.rel_push("emit_var_type_candidate", (reg, XType::XstructPtr(sid)));
    }

    if db.trace_enabled {
        let struct_count = struct_fields_map.len();
        let field_count: usize = struct_fields_map.values().map(|f| f.len()).sum();
        let stack_count = stack_candidates.len();
        let global_count = global_candidates.len();
        info!(
            "[struct_recovery] emitted {} structs with {} total fields (sources: {} ptr, {} stack, {} global candidates)",
            struct_count, field_count,
            struct_candidates.len(), stack_count, global_count
        );
    }
}


fn is_uniform_stride(offsets: &[(i64, MemoryChunk)]) -> bool {
    if offsets.len() < 3 {
        return false;
    }
    let first_chunk = offsets[0].1;
    if !offsets.iter().all(|(_, c)| *c == first_chunk) {
        return false;
    }
    let stride = offsets[1].0 - offsets[0].0;
    if stride <= 0 {
        return false;
    }
    let expected_stride = chunk_byte_size(&first_chunk) as i64;
    if stride != expected_stride {
        return false;
    }
    for i in 1..offsets.len() {
        if offsets[i].0 - offsets[i - 1].0 != stride {
            return false;
        }
    }
    true
}

fn check_field_overlap(sorted_fields: &[(i64, usize)]) -> bool {
    for i in 0..sorted_fields.len() - 1 {
        let (ofs, size) = sorted_fields[i];
        let (next_ofs, _) = sorted_fields[i + 1];
        if ofs + size as i64 > next_ofs {
            return true;
        }
    }
    false
}

fn compute_layout_hash(fields: &[InferredField]) -> u64 {
    let mut hasher = DefaultHasher::new();
    for field in fields {
        field.offset.hash(&mut hasher);
        chunk_byte_size(&field.chunk).hash(&mut hasher);
        field.chunk.hash(&mut hasher);
    }
    hasher.finish()
}

fn compute_total_size(fields: &[InferredField]) -> usize {
    if fields.is_empty() { return 0; }
    let first = &fields[0];
    let last = &fields[fields.len() - 1];
    let span = (last.offset - first.offset) as usize;
    span + chunk_byte_size(&last.chunk)
}

fn pick_best_xtype(xtypes: &[XType]) -> XType {
    if xtypes.is_empty() { return XType::Xint; }
    let mut counts: HashMap<XType, usize> = HashMap::new();
    for &xt in xtypes {
        *counts.entry(xt).or_insert(0) += 1;
    }
    counts.into_iter().max_by_key(|(_, c)| *c).map(|(xt, _)| xt).unwrap_or(XType::Xint)
}

pub use crate::decompile::passes::csh_pass::{make_field_ident, field_ident_to_name};

pub fn compute_layout_hash_from_tuples(fields: &[(i64, usize, MemoryChunk)]) -> u64 {
    let mut sorted: Vec<_> = fields.to_vec();
    sorted.sort_by_key(|(ofs, _, _)| *ofs);
    let mut hasher = DefaultHasher::new();
    for (offset, size, chunk) in &sorted {
        offset.hash(&mut hasher);
        size.hash(&mut hasher);
        chunk.hash(&mut hasher);
    }
    hasher.finish()
}

fn xtype_to_field_type(xtype: XType) -> FieldType {
    match xtype {
        XType::Xbool => FieldType::Scalar(MemoryChunk::MBool),
        XType::Xint8signed => FieldType::Scalar(MemoryChunk::MInt8Signed),
        XType::Xint8unsigned => FieldType::Scalar(MemoryChunk::MInt8Unsigned),
        XType::Xint16signed => FieldType::Scalar(MemoryChunk::MInt16Signed),
        XType::Xint16unsigned => FieldType::Scalar(MemoryChunk::MInt16Unsigned),
        XType::Xint | XType::Xintunsigned => FieldType::Scalar(MemoryChunk::MInt32),
        XType::Xlong | XType::Xlongunsigned => FieldType::Scalar(MemoryChunk::MInt64),
        XType::Xfloat => FieldType::Scalar(MemoryChunk::MFloat64),
        XType::Xsingle => FieldType::Scalar(MemoryChunk::MFloat32),
        XType::Xptr => FieldType::Pointer(Box::new(FieldType::Unknown)),
        XType::Xcharptr => FieldType::Pointer(Box::new(FieldType::Scalar(MemoryChunk::MInt8Signed))),
        XType::Xintptr => FieldType::Pointer(Box::new(FieldType::Scalar(MemoryChunk::MInt32))),
        XType::Xfloatptr => FieldType::Pointer(Box::new(FieldType::Scalar(MemoryChunk::MFloat64))),
        XType::Xsingleptr => FieldType::Pointer(Box::new(FieldType::Scalar(MemoryChunk::MFloat32))),
        XType::Xfuncptr => FieldType::Pointer(Box::new(FieldType::Unknown)),
        XType::XstructPtr(sid) => FieldType::StructPointer(sid),
        XType::Xany32 => FieldType::Scalar(MemoryChunk::MAny32),
        XType::Xany64 => FieldType::Scalar(MemoryChunk::MAny64),
        XType::Xvoid => FieldType::Unknown,
    }
}
