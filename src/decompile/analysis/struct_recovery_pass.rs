use log::info;
use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use crate::decompile::elevator::config::CONFIG;
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::mreg::Mreg;
use crate::x86::op::{Addressing, Operation};
use crate::x86::types::*;
use ascent::ascent_par;

pub fn chunk_byte_size(chunk: &MemoryChunk) -> usize {
    match chunk {
        MemoryChunk::MBool | MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned => 1,
        MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned => 2,
        MemoryChunk::MInt32 | MemoryChunk::MFloat32 | MemoryChunk::MAny32 => 4,
        MemoryChunk::MInt64 | MemoryChunk::MFloat64 | MemoryChunk::MAny64 => 8,
        MemoryChunk::Unknown => 4,
    }
}

fn max_refined_struct_xtype<'a>(
    inp: impl Iterator<Item = (&'a XType,)>,
) -> impl Iterator<Item = XType> {
    inp.map(|(&xtype,)| xtype)
        .max_by_key(|xtype| {
            (
                crate::decompile::passes::clight_pass::xtype_refine_priority(xtype),
                *xtype,
            )
        })
        .into_iter()
}

fn struct_indexed_offset(addressing: &Addressing) -> Option<i64> {
    match addressing {
        Addressing::Aindexed(offset)
        | Addressing::Aindexed2(offset)
        | Addressing::Aindexed2scaled(_, offset) => Some(*offset),
        _ => None,
    }
}

fn majority_struct_xtype<'a>(
    inp: impl Iterator<Item = (&'a XType,)>,
) -> impl Iterator<Item = XType> {
    let mut counts: BTreeMap<XType, usize> = BTreeMap::new();
    for (&xtype,) in inp {
        *counts.entry(xtype).or_default() += 1;
    }
    counts
        .into_iter()
        .max_by(|left, right| left.1.cmp(&right.1).then_with(|| right.0.cmp(&left.0)))
        .map(|(xtype, _)| xtype)
        .into_iter()
}

fn widest_struct_chunk<'a>(
    inp: impl Iterator<Item = (&'a MemoryChunk,)>,
) -> impl Iterator<Item = MemoryChunk> {
    inp.map(|(&chunk,)| chunk)
        .max_by(|left, right| {
            chunk_byte_size(left)
                .cmp(&chunk_byte_size(right))
                .then_with(|| left.cmp(right))
        })
        .into_iter()
}

fn uniform_struct_layout<'a>(
    inp: impl Iterator<Item = (&'a i64, &'a MemoryChunk)>,
) -> impl Iterator<Item = bool> {
    let mut fields: Vec<(i64, MemoryChunk)> =
        inp.map(|(&offset, &chunk)| (offset, chunk)).collect();
    fields.sort_unstable();
    std::iter::once(is_uniform_stride(&fields))
}

fn struct_fields_overlap(left_offset: i64, left_chunk: MemoryChunk, right_offset: i64) -> bool {
    left_offset
        .checked_add(chunk_byte_size(&left_chunk) as i64)
        .is_none_or(|left_end| left_end > right_offset)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum StructLayoutSource {
    Pointer(RTLReg),
    Stack(Address, i64),
    Global(Ident),
}

ascent_par! {
    struct StructLayoutProgram;

    // The final flag records whether an access is a load.  When at least one
    // load exists at an offset, store-only chunks are ignored because lowered
    // sub-register stores often carry the full source-register width.
    relation layout_access(StructLayoutSource, i64, MemoryChunk, bool);

    #[local] relation layout_has_load(StructLayoutSource, i64);
    layout_has_load(source, offset) <--
        layout_access(source, offset, _, true);

    #[local] relation layout_chunk(StructLayoutSource, i64, MemoryChunk);
    layout_chunk(source, offset, chunk) <--
        layout_access(source, offset, chunk, true);
    layout_chunk(source, offset, chunk) <--
        layout_access(source, offset, chunk, false),
        !layout_has_load(source, offset);

    relation selected_layout_field(StructLayoutSource, i64, MemoryChunk);
    selected_layout_field(source, offset, selected) <--
        layout_chunk(source, offset, _),
        agg selected = widest_struct_chunk(chunk)
            in layout_chunk(source, offset, chunk);

    #[local] relation layout_field_count(StructLayoutSource, usize);
    layout_field_count(source, count) <--
        selected_layout_field(source, _, _),
        agg count = ascent::aggregators::count()
            in selected_layout_field(source, _, _);

    #[local] lattice layout_next_offset_min(StructLayoutSource, i64, ascent::Dual<i64>);
    layout_next_offset_min(source, offset, ascent::Dual(i64::MAX)) <--
        selected_layout_field(source, offset, _);
    layout_next_offset_min(source, left, ascent::Dual(*right)) <--
        selected_layout_field(source, left, _),
        selected_layout_field(source, right, _),
        if left < right;

    #[local] relation layout_next_offset(StructLayoutSource, i64, i64);
    layout_next_offset(source, left, next.0) <--
        layout_next_offset_min(source, left, next),
        if next.0 != i64::MAX;

    #[local] relation layout_has_overlap(StructLayoutSource);
    layout_has_overlap(source) <--
        selected_layout_field(source, left, chunk),
        layout_next_offset(source, left, right),
        if struct_fields_overlap(*left, *chunk, *right);

    #[local] relation layout_is_uniform_array(StructLayoutSource);
    layout_is_uniform_array(source) <--
        selected_layout_field(source, _, _),
        agg uniform = uniform_struct_layout(offset, chunk)
            in selected_layout_field(source, offset, chunk),
        if uniform;

    relation valid_struct_layout(StructLayoutSource);
    valid_struct_layout(source) <--
        layout_field_count(source, count),
        if *count >= 2,
        !layout_has_overlap(source),
        !layout_is_uniform_array(source);
}

ascent_par! {
    struct StructFieldTypeVoteProgram;

    relation field_type_evidence(usize, i64, usize, XType);
    relation selected_field_type(usize, i64, XType);

    selected_field_type(struct_id, offset, selected) <--
        field_type_evidence(struct_id, offset, _, _),
        agg selected = majority_struct_xtype(xtype)
            in field_type_evidence(struct_id, offset, _, xtype);
}

// SR-4: cap is a false-folding guard -- raising it folds more unrelated locals into fake fields; bound the window by observed deref extent (stack_lea_used_for_access) before raising.

// Pointer/stack/global struct detection via load/store offset analysis
ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct StructRecoveryProgram;

    relation rtl_inst(Node, RTLInst);
    relation op_produces_ptr(Node, RTLReg);
    relation ltl_inst(Node, LTLInst);
    relation reg_rtl(Node, Mreg, RTLReg);
    relation instr_in_function(Node, Address);
    relation is_ptr(RTLReg);
    relation emit_var_type_candidate(RTLReg, XType);
    relation emit_function_param_candidate(Address, RTLReg);
    relation call_target_func(Node, Address);
    relation call_arg_mapping(Node, usize, RTLReg);
    relation emit_function(Address, Symbol, Node);
    relation known_extern_signature(Symbol, usize, XType, Arc<Vec<XType>>);
    relation string_data(String, String, usize);
    relation ident_to_symbol(Ident, Symbol);
    relation stack_var(Address, Address, i64, RTLReg);
    relation stack_var_chunk(Address, i64, MemoryChunk);
    relation is_global_array(Ident, usize, usize);

    // Parameter bases missed by upstream physical-register reuse are still a
    // structural fact: the fresh parameter value itself is the first operand
    // of an indexed memory access.  Derive is_ptr before ptr_deref consumes it.
    is_ptr(base) <--
        emit_function_param_candidate(_, base),
        rtl_inst(_, ?RTLInst::Iload(_, addressing, args, _)),
        if struct_indexed_offset(addressing).is_some(),
        if args.first() == Some(base);
    is_ptr(base) <--
        emit_function_param_candidate(_, base),
        rtl_inst(_, ?RTLInst::Istore(_, addressing, args, _)),
        if struct_indexed_offset(addressing).is_some(),
        if args.first() == Some(base);

    // Non-parameter bases used at two distinct indexed offsets carry pointer
    // evidence too.  This remains a type candidate rather than an is_ptr fact,
    // preserving the guard against exploding ptr_deref during this pass.
    #[local] relation indexed_base_offset(RTLReg, i64);
    indexed_base_offset(base, offset) <--
        rtl_inst(_, ?RTLInst::Iload(_, addressing, args, _)),
        if !args.is_empty(),
        if let Some(offset) = struct_indexed_offset(addressing),
        let base = args[0];
    indexed_base_offset(base, offset) <--
        rtl_inst(_, ?RTLInst::Istore(_, addressing, args, _)),
        if !args.is_empty(),
        if let Some(offset) = struct_indexed_offset(addressing),
        let base = args[0];

    #[local] relation indexed_base_has_multiple_offsets(RTLReg);
    indexed_base_has_multiple_offsets(base) <--
        indexed_base_offset(base, left),
        indexed_base_offset(base, right),
        if left != right;

    emit_var_type_candidate(base, XType::Xptr) <--
        indexed_base_has_multiple_offsets(base),
        !is_ptr(base);

    emit_var_type_candidate(*reg, XType::Xfuncptr) <--
        rtl_inst(_, ?RTLInst::Icall(_, either::Either::Left(reg), _, _, _));
    emit_var_type_candidate(*reg, XType::Xfuncptr) <--
        rtl_inst(_, ?RTLInst::Itailcall(_, either::Either::Left(reg), _));


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

    // Load-evidence subset of ptr_deref; sub-register store chunks are width-unreliable upstream.
    relation ptr_deref_load(RTLReg, i64, MemoryChunk);

    ptr_deref_load(base_reg, *ofs, *chunk) <--
        rtl_inst(_, ?RTLInst::Iload(chunk, Addressing::Aindexed(ofs), args, _)),
        if args.len() >= 1,
        let base_reg = args[0],
        is_ptr(&base_reg);


    #[local] relation call_site(Node, Symbol);
    #[local] relation call_arg(Node, usize, RTLReg);

    call_site(node, *sym) <--
        call_target_func(node, callee),
        emit_function(callee, sym, _);

    call_arg(call_node, *pos, *reg) <--
        call_arg_mapping(call_node, pos, reg);

    #[local] relation ptr_has_offset(RTLReg, i64);
    ptr_has_offset(reg, ofs) <-- ptr_deref(reg, ofs, _, _, _);

    // Promote as struct on: 2+ distinct offsets (StructLayoutProgram and
    // ptr_has_variable_index reject uniform-stride 3+ as arrays), OR 2 offsets
    // with differing chunks (can't be array); replacing the former 3-way
    // self-join, this also recovers two-field structs and is O(n^2) not O(n^3).
    #[local] relation ptr_has_multiple_offsets(RTLReg);
    ptr_has_multiple_offsets(reg) <--
        ptr_has_offset(reg, a),
        ptr_has_offset(reg, b),
        if a != b;
    ptr_has_multiple_offsets(reg) <--
        ptr_deref(reg, a, chunk_a, _, _),
        ptr_deref(reg, b, chunk_b, _, _),
        if a != b,
        if chunk_a != chunk_b;

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

    // Plain Aindexed2 is [r1+r2+ofs] with r2 a runtime index, so the deref is array-indexed (p[i]), not a constant-offset struct field.
    ptr_has_variable_index(base_reg) <--
        rtl_inst(_, ?RTLInst::Iload(_, Addressing::Aindexed2(_), args, _)),
        if args.len() >= 1,
        let base_reg = args[0],
        is_ptr(&base_reg);

    ptr_has_variable_index(base_reg) <--
        rtl_inst(_, ?RTLInst::Istore(_, Addressing::Aindexed2(_), args, _)),
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
        rtl_inst(node, ?RTLInst::Iop(Operation::Olea(Addressing::Ainstack(base_ofs)), _, dst)),
        op_produces_ptr(node, dst),
        stack_var(func, node, *base_ofs, _),
        instr_in_function(node, func);

    stack_lea_base(*func, *base_ofs) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Oleal(Addressing::Ainstack(base_ofs)), _, dst)),
        op_produces_ptr(node, dst),
        stack_var(func, node, *base_ofs, _),
        instr_in_function(node, func);

    relation stack_lea_reg(Address, i64, RTLReg);

    stack_lea_reg(*func, *base_ofs, *dst) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Olea(Addressing::Ainstack(base_ofs)), _, dst)),
        op_produces_ptr(node, dst),
        stack_var(func, node, *base_ofs, _),
        instr_in_function(node, func);

    stack_lea_reg(*func, *base_ofs, *dst) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Oleal(Addressing::Ainstack(base_ofs)), _, dst)),
        op_produces_ptr(node, dst),
        stack_var(func, node, *base_ofs, _),
        instr_in_function(node, func);

    // (func, base_ofs, field_ofs, chunk, value_rtl_reg)
    relation stack_struct_field(Address, i64, i64, MemoryChunk, RTLReg);

    // Guard: only count stack LEAs actually used as a load/store base, else +/-1024 slots fold into fake structs.
    #[local] relation stack_lea_used_for_access(Address, i64, i64);
    stack_lea_used_for_access(*func, *base_ofs, *inner_ofs) <--
        stack_lea_reg(func, base_ofs, lea_dst),
        rtl_inst(node, ?RTLInst::Iload(_, Addressing::Aindexed(inner_ofs), args, _)),
        instr_in_function(node, func),
        if args.len() >= 1 && args[0] == *lea_dst;
    stack_lea_used_for_access(*func, *base_ofs, *inner_ofs) <--
        stack_lea_reg(func, base_ofs, lea_dst),
        rtl_inst(node, ?RTLInst::Istore(_, Addressing::Aindexed(inner_ofs), args, _)),
        instr_in_function(node, func),
        if args.len() >= 1 && args[0] == *lea_dst;

    // STRUCTREC-2: bind the proven inner offset and require the stack_var to BE the accessed target (ofs == base_ofs + inner_ofs); membership is the structural equality, not the address-magnitude window. The 1024 cap stays only as a defensive bound.
    stack_struct_field(*func, *base_ofs, *inner_ofs, *chunk, *rtl_reg) <--
        stack_lea_base(func, base_ofs),
        stack_lea_used_for_access(func, base_ofs, inner_ofs),
        stack_var(func, _, ofs, rtl_reg),
        if *ofs == *base_ofs + *inner_ofs,
        if *inner_ofs >= 0 && *inner_ofs < CONFIG.struct_recovery.max_stack_struct_size,
        stack_var_chunk(func, ofs, chunk);

    // Same promotion policy as ptr_has_multiple_offsets.
    relation stack_is_struct_candidate(Address, i64);

    // 3+ distinct field offsets, counted via aggregation; the former 3-way self-join was O(fields^3) (minutes on date/touch). Distinct-project first since stack_struct_field repeats an offset across chunks/regs.
    #[local] relation stack_distinct_field_ofs(Address, i64, i64);
    stack_distinct_field_ofs(*func, *base_ofs, *fofs) <--
        stack_struct_field(func, base_ofs, fofs, _, _);
    #[local] relation stack_field_ofs_count(Address, i64, usize);
    stack_field_ofs_count(func, base_ofs, count) <--
        stack_distinct_field_ofs(func, base_ofs, _),
        agg count = ascent::aggregators::count() in stack_distinct_field_ofs(func, base_ofs, _);
    stack_is_struct_candidate(func, base_ofs) <--
        stack_field_ofs_count(func, base_ofs, count),
        if *count >= 3;
    stack_is_struct_candidate(func, base_ofs) <--
        stack_struct_field(func, base_ofs, a, chunk_a, _),
        stack_struct_field(func, base_ofs, b, chunk_b, _),
        if a != b,
        if chunk_a != chunk_b;
    // SR-1: two-field uniform-chunk stack struct requires the LEA'd pointer to be used at 2+ distinct inner offsets; bare address-taking (scanf(&x)-style) stays unpromoted.
    stack_is_struct_candidate(func, base_ofs) <--
        stack_field_ofs_count(func, base_ofs, count),
        if *count >= 2,
        stack_lea_used_for_access(func, base_ofs, o1),
        stack_lea_used_for_access(func, base_ofs, o2),
        if o1 != o2;


    // Global struct detection via constant-offset accesses
    relation global_deref(Ident, i64, MemoryChunk, RTLReg);

    global_deref(*ident, *ofs, *chunk, *dst) <--
        rtl_inst(_, ?RTLInst::Iload(chunk, Addressing::Aglobal(ident, ofs), _, dst));

    global_deref(*ident, *ofs, *chunk, *src) <--
        rtl_inst(_, ?RTLInst::Istore(chunk, Addressing::Aglobal(ident, ofs), _, src));

    // RIP-relative field accesses resolve to separate SUB_/L_ idents; fold them back via global_array_pass-produced interior_to_base_ident or the same global never shows two offsets on one base.
    relation interior_to_base_ident(Ident, Ident, i64);

    global_deref(*base, int_ofs + ofs, *chunk, *dst) <--
        interior_to_base_ident(int_id, base, int_ofs),
        rtl_inst(_, ?RTLInst::Iload(chunk, Addressing::Aglobal(acc_id, ofs), _, dst)),
        if acc_id == int_id;

    global_deref(*base, int_ofs + ofs, *chunk, *src) <--
        interior_to_base_ident(int_id, base, int_ofs),
        rtl_inst(_, ?RTLInst::Istore(chunk, Addressing::Aglobal(acc_id, ofs), _, src)),
        if acc_id == int_id;

    // Load-evidence subset: sub-register stores are lifted at full register width upstream, so prefer load chunks per offset to get the real access width.
    relation global_deref_load(Ident, i64, MemoryChunk);

    global_deref_load(*ident, *ofs, *chunk) <--
        rtl_inst(_, ?RTLInst::Iload(chunk, Addressing::Aglobal(ident, ofs), _, _));

    global_deref_load(*base, int_ofs + ofs, *chunk) <--
        interior_to_base_ident(int_id, base, int_ofs),
        rtl_inst(_, ?RTLInst::Iload(chunk, Addressing::Aglobal(acc_id, ofs), _, _)),
        if acc_id == int_id;

    #[local] relation global_has_offset(Ident, i64);
    global_has_offset(ident, ofs) <-- global_deref(ident, ofs, _, _);

    // Promote on 2+ distinct offsets; constant-only int pairs are layout-identical to two-field structs at binary level so struct is the best reading. Arrays vetoed by !is_global_array + !global_has_variable_index.
    #[local] relation global_has_multiple_offsets(Ident);
    #[local] relation global_offset_count(Ident, usize);
    global_offset_count(ident, count) <--
        global_has_offset(ident, _),
        agg count = ascent::aggregators::count() in global_has_offset(ident, _);
    global_has_multiple_offsets(ident) <--
        global_offset_count(ident, count),
        if *count >= 2;

    #[local] relation global_has_variable_index(Ident);

    global_has_variable_index(*ident) <--
        rtl_inst(_, ?RTLInst::Iload(_, Addressing::Abasedscaled(_, ident, _), _, _));
    global_has_variable_index(*ident) <--
        rtl_inst(_, ?RTLInst::Istore(_, Addressing::Abasedscaled(_, ident, _), _, _));
    global_has_variable_index(*ident) <--
        rtl_inst(_, ?RTLInst::Iload(_, Addressing::Abased(ident, _), _, _));
    global_has_variable_index(*ident) <--
        rtl_inst(_, ?RTLInst::Istore(_, Addressing::Abased(ident, _), _, _));

    // PIE `lea sym(%rip),%r` + scaled access through %r: variable indexing vetoes struct even when !is_global_array alone wouldn't fire.
    relation global_access_ev(Ident, i64, MemoryChunk, bool, bool);

    global_has_variable_index(ident) <--
        global_access_ev(ident, _, _, _, is_var),
        if *is_var;

    relation global_is_struct_candidate(Ident);

    global_is_struct_candidate(ident) <--
        global_has_multiple_offsets(ident),
        !is_global_array(ident, _, _),
        !global_has_variable_index(ident);

    relation selected_emit_var_type(RTLReg, XType);
    selected_emit_var_type(reg, selected) <--
        emit_var_type_candidate(reg, _),
        agg selected = max_refined_struct_xtype(xtype)
            in emit_var_type_candidate(reg, xtype);
}

pub struct StructRecoveryPass;

impl IRPass for StructRecoveryPass {
    fn name(&self) -> &'static str {
        "struct_recovery"
    }

    fn run(&self, db: &mut DecompileDB) {
        let mut prog = StructRecoveryProgram::default();
        prog.swap_db_fields(db);
        // Do not clear emit_var_type_candidate; upstream data needed for struct_field_type
        prog.run();
        prog.swap_db_fields(db);

        post_process_structs(db);

        // Diagnostic hook (env-gated, like CF4_TRACE) for struct-recovery work.
        if std::env::var("SR_DUMP").is_ok() {
            for t in db.rel_iter::<(Ident, Ident, i64)>("interior_to_base_ident") {
                eprintln!("[SR] interior_to_base_ident {:x?}", t);
            }
            for t in db.rel_iter::<(Ident, i64, MemoryChunk, RTLReg)>("global_deref") {
                eprintln!("[SR] global_deref {:x?}", t);
            }
            for t in db.rel_iter::<(Ident,)>("global_is_struct_candidate") {
                eprintln!("[SR] global_is_struct_candidate {:x?}", t);
            }
            for t in db.rel_iter::<(u64, usize, usize, usize)>("global_struct_catalog") {
                eprintln!("[SR] global_struct_catalog {:x?}", t);
            }
            for t in db.rel_iter::<(usize, usize, i64, FieldType, Ident)>("emit_struct_field") {
                eprintln!("[SR] emit_struct_field {:x?}", t);
            }
            // SR-4 incidence probe: how close do stack-struct windows come to the CONFIG.struct_recovery.max_stack_struct_size cap?
            {
                let mut max_field_ofs: i64 = 0;
                let mut windows_near_cap: std::collections::HashSet<(Address, i64)> =
                    std::collections::HashSet::new();
                let mut total_windows: std::collections::HashSet<(Address, i64)> =
                    std::collections::HashSet::new();
                for &(func, base, fofs, _, _) in
                    db.rel_iter::<(Address, i64, i64, MemoryChunk, RTLReg)>("stack_struct_field")
                {
                    total_windows.insert((func, base));
                    if fofs > max_field_ofs {
                        max_field_ofs = fofs;
                    }
                    if fofs
                        > CONFIG.struct_recovery.max_stack_struct_size
                            - CONFIG.struct_recovery.near_cap_probe_margin
                    {
                        windows_near_cap.insert((func, base));
                    }
                }
                eprintln!(
                    "[SR] stack-window summary: {} windows, max field ofs {}, {} windows within 128B of the {} cap",
                    total_windows.len(), max_field_ofs, windows_near_cap.len(), CONFIG.struct_recovery.max_stack_struct_size
                );
            }
        }
    }

    fn inputs(&self) -> &'static [&'static str] {
        &[
            "rtl_inst",
            "op_produces_ptr",
            "ltl_inst",
            "reg_rtl",
            "instr_in_function",
            "is_ptr",
            "emit_var_type_candidate",
            "call_target_func",
            "call_arg_mapping",
            "emit_function",
            "known_extern_signature",
            "string_data",
            "ident_to_symbol",
            "stack_var",
            "stack_var_chunk",
            "is_global_array",
            "interior_to_base_ident",
            "global_access_ev",
            // Exact initialized pointer slots override narrower field-type
            // votes in post_process_structs.
            "pointer_in_data",
            "code_pointer_in_data",
            "emit_function_param_candidate",
            "func_has_param_at_position",
            "emit_function_return",
        ]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "is_ptr",
            "emit_var_type_candidate",
            "emit_struct_field",
            "emit_var_is_struct_candidate",
            "global_struct_catalog",
            "emit_canonical_struct_id",
            "struct_id_to_canonical",
            "emit_struct_def",
            "reg_to_struct_id",
            "func_param_struct_type_candidate",
            "func_return_struct_type",
            "ptr_deref",
            "ptr_deref_load",
            "ptr_is_struct_candidate",
            "struct_field_type",
            "refined_ptr_type",
            "stack_struct_field",
            "stack_is_struct_candidate",
            "stack_lea_reg",
            "global_deref",
            "global_deref_load",
            "global_is_struct_candidate",
            "emit_global_struct_fields",
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
}

/// Canonical struct fields whose exact image slot carries a relocation.
/// Relocations are object-layout authority: whatever access/type votes said,
/// that field must hold at least one target pointer's bits.
fn relocated_global_struct_fields(
    global_layouts: &[(Ident, Vec<InferredField>)],
    hash_to_canonical: &HashMap<u64, usize>,
    relocation_slots: &HashSet<Address>,
    pointer_size: usize,
) -> HashSet<(usize, i64)> {
    let mut result = HashSet::new();
    for (ident, fields) in global_layouts {
        let Some(&struct_id) = hash_to_canonical.get(&compute_layout_hash(fields)) else {
            continue;
        };
        let Ok(base) = Address::try_from(*ident) else {
            continue;
        };
        for (index, field) in fields.iter().enumerate() {
            let Ok(offset) = u64::try_from(field.offset) else {
                continue;
            };
            let pointer_end = field.offset.saturating_add(pointer_size as i64);
            if fields
                .get(index + 1)
                .is_some_and(|next| next.offset < pointer_end)
            {
                continue;
            }
            if base
                .checked_add(offset)
                .is_some_and(|slot| relocation_slots.contains(&slot))
            {
                result.insert((struct_id, field.offset));
            }
        }
    }
    result
}

fn enforce_relocation_field_width(
    inferred: FieldType,
    has_relocation: bool,
    pointer_size: usize,
) -> FieldType {
    if !has_relocation || inferred.size(pointer_size) >= pointer_size {
        return inferred;
    }
    let chunk = if pointer_size == 4 {
        MemoryChunk::MInt32
    } else {
        MemoryChunk::MInt64
    };
    FieldType::Scalar(chunk)
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
        .rel_iter::<(RTLReg, XType)>("selected_emit_var_type")
        .copied()
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

    let relocation_slots: HashSet<Address> = db
        .rel_iter::<(Address, Address)>("pointer_in_data")
        .chain(db.rel_iter::<(Address, Address)>("code_pointer_in_data"))
        .map(|(slot, _)| *slot)
        .collect();

    let mut field_xtype_map: HashMap<(RTLReg, i64), Vec<XType>> = HashMap::new();
    for &(base, ofs, _, xtype) in &struct_field_types {
        field_xtype_map.entry((base, ofs)).or_default().push(xtype);
    }

    let candidate_set: HashSet<RTLReg> = struct_candidates.iter().copied().collect();
    let stack_candidate_set: HashSet<(Address, i64)> = stack_candidates.iter().copied().collect();
    let global_candidate_set: HashSet<Ident> = global_candidates.iter().map(|&(id,)| id).collect();

    let mut layout_program = StructLayoutProgram::default();
    for &(base, offset, chunk, _, _) in &ptr_derefs {
        if candidate_set.contains(&base) {
            layout_program.layout_access.push((
                StructLayoutSource::Pointer(base),
                offset,
                chunk,
                false,
            ));
        }
    }
    for &(base, offset, chunk) in db.rel_iter::<(RTLReg, i64, MemoryChunk)>("ptr_deref_load") {
        if candidate_set.contains(&base) {
            layout_program.layout_access.push((
                StructLayoutSource::Pointer(base),
                offset,
                chunk,
                true,
            ));
        }
    }
    for &(func, base_offset, field_offset, chunk, _) in &stack_fields {
        if stack_candidate_set.contains(&(func, base_offset)) {
            layout_program.layout_access.push((
                StructLayoutSource::Stack(func, base_offset),
                field_offset,
                chunk,
                false,
            ));
        }
    }
    for &(ident, offset, chunk, _) in &global_derefs {
        if global_candidate_set.contains(&ident) {
            layout_program.layout_access.push((
                StructLayoutSource::Global(ident),
                offset,
                chunk,
                false,
            ));
        }
    }
    for &(ident, offset, chunk) in db.rel_iter::<(Ident, i64, MemoryChunk)>("global_deref_load") {
        if global_candidate_set.contains(&ident) {
            layout_program.layout_access.push((
                StructLayoutSource::Global(ident),
                offset,
                chunk,
                true,
            ));
        }
    }
    layout_program.run();

    let valid_sources: HashSet<StructLayoutSource> = layout_program
        .valid_struct_layout
        .iter()
        .map(|&(source,)| source)
        .collect();
    let mut fields_by_source: BTreeMap<StructLayoutSource, Vec<InferredField>> = BTreeMap::new();
    for &(source, offset, chunk) in &layout_program.selected_layout_field {
        if valid_sources.contains(&source) {
            fields_by_source
                .entry(source)
                .or_default()
                .push(InferredField { offset, chunk });
        }
    }
    for fields in fields_by_source.values_mut() {
        fields.sort_unstable();
    }

    let mut recovered_layouts: std::collections::BTreeSet<Vec<InferredField>> =
        std::collections::BTreeSet::new();
    let mut layout_ptr_regs: HashMap<
        Vec<InferredField>,
        std::collections::BTreeSet<(Address, RTLReg)>,
    > = HashMap::new();

    let mut ptr_funcs: HashMap<RTLReg, std::collections::BTreeSet<Address>> = HashMap::new();
    for &(base, _, _, _, func) in &ptr_derefs {
        if candidate_set.contains(&base) {
            ptr_funcs.entry(base).or_default().insert(func);
        }
    }

    for (&ptr_reg, funcs) in &ptr_funcs {
        let Some(fields) = fields_by_source.get(&StructLayoutSource::Pointer(ptr_reg)) else {
            continue;
        };
        recovered_layouts.insert(fields.clone());
        for &func in funcs {
            layout_ptr_regs
                .entry(fields.clone())
                .or_default()
                .insert((func, ptr_reg));
        }
    }

    let mut stack_field_map: HashMap<(Address, i64), Vec<(i64, MemoryChunk, RTLReg)>> =
        HashMap::new();
    for &(func, base_ofs, field_ofs, chunk, rtl_reg) in &stack_fields {
        stack_field_map
            .entry((func, base_ofs))
            .or_default()
            .push((field_ofs, chunk, rtl_reg));
    }
    let mut stack_lea_map: HashMap<(Address, i64), std::collections::BTreeSet<RTLReg>> =
        HashMap::new();
    for &(func, base_ofs, reg) in &stack_lea_regs {
        stack_lea_map
            .entry((func, base_ofs))
            .or_default()
            .insert(reg);
    }

    for &(func, base_ofs) in &stack_candidates {
        let fields_data = match stack_field_map.get(&(func, base_ofs)) {
            Some(f) => f,
            None => continue,
        };
        let Some(fields) = fields_by_source.get(&StructLayoutSource::Stack(func, base_ofs)) else {
            continue;
        };
        recovered_layouts.insert(fields.clone());

        if let Some(lea_regs) = stack_lea_map.get(&(func, base_ofs)) {
            for &reg in lea_regs {
                layout_ptr_regs
                    .entry(fields.clone())
                    .or_default()
                    .insert((func, reg));
            }
        }

        if let Some(lea_regs) = stack_lea_map.get(&(func, base_ofs)) {
            for &lea_reg in lea_regs {
                for &(field_ofs, _, rtl_reg) in fields_data {
                    if let Some(&xtype) = existing_types.get(&rtl_reg) {
                        field_xtype_map
                            .entry((lea_reg, field_ofs))
                            .or_default()
                            .push(xtype);
                    }
                }
            }
        }
    }

    let mut global_deref_map: HashMap<Ident, Vec<(i64, MemoryChunk, RTLReg)>> = HashMap::new();
    for &(ident, ofs, chunk, val_reg) in &global_derefs {
        if global_candidate_set.contains(&ident) {
            global_deref_map
                .entry(ident)
                .or_default()
                .push((ofs, chunk, val_reg));
        }
    }
    // ident -> recovered layout, for the global-side struct binding below.
    let mut global_layouts: Vec<(Ident, Vec<InferredField>)> = Vec::new();

    for &(ident,) in &global_candidates {
        let accesses = match global_deref_map.get(&ident) {
            Some(a) => a,
            None => continue,
        };
        let Some(fields) = fields_by_source.get(&StructLayoutSource::Global(ident)) else {
            continue;
        };
        recovered_layouts.insert(fields.clone());

        for &(ofs, _, val_reg) in accesses {
            if let Some(&xtype) = existing_types.get(&val_reg) {
                field_xtype_map
                    .entry((val_reg, ofs))
                    .or_default()
                    .push(xtype);
            }
        }
        global_layouts.push((ident, fields.clone()));
    }

    let candidates: Vec<CandidateStruct> = recovered_layouts
        .into_iter()
        .map(|fields| {
            let ptr_regs = layout_ptr_regs
                .remove(&fields)
                .unwrap_or_default()
                .into_iter()
                .collect();
            CandidateStruct { ptr_regs, fields }
        })
        .collect();

    let mut hash_to_canonical: HashMap<u64, usize> = HashMap::new();
    let mut struct_fields_map: HashMap<usize, Vec<InferredField>> = HashMap::new();
    let mut var_struct_map: Vec<(Address, RTLReg, usize)> = Vec::new();
    let mut id_to_canonical: HashMap<usize, usize> = HashMap::new();

    for candidate in &candidates {
        let layout_hash = compute_layout_hash(&candidate.fields);
        let canonical_id = layout_hash_to_struct_id(layout_hash);
        hash_to_canonical.insert(layout_hash, canonical_id);
        struct_fields_map
            .entry(canonical_id)
            .or_insert_with(|| candidate.fields.clone());
        id_to_canonical.insert(canonical_id, canonical_id);
        for &(func, reg) in &candidate.ptr_regs {
            var_struct_map.push((func, reg, canonical_id));
        }
    }

    let pointer_size = db.abi().pointer_size;
    let relocated_fields = relocated_global_struct_fields(
        &global_layouts,
        &hash_to_canonical,
        &relocation_slots,
        pointer_size,
    );

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

    let mut field_vote = StructFieldTypeVoteProgram::default();
    for (&(struct_id, offset), xtypes) in &field_type_info {
        for (occurrence, &xtype) in xtypes.iter().enumerate() {
            field_vote
                .field_type_evidence
                .push((struct_id, offset, occurrence, xtype));
        }
    }
    field_vote.run();
    let selected_field_types: HashMap<(usize, i64), XType> = field_vote
        .selected_field_type
        .iter()
        .map(|&(struct_id, offset, xtype)| ((struct_id, offset), xtype))
        .collect();

    let mut emit_struct_field: Vec<(usize, usize, i64, FieldType, Ident)> = Vec::new();
    let mut sorted_struct_ids: Vec<usize> = struct_fields_map.keys().copied().collect();
    sorted_struct_ids.sort();
    for struct_id in sorted_struct_ids {
        let fields = &struct_fields_map[&struct_id];
        for (field_idx, field) in fields.iter().enumerate() {
            let inferred = if let Some(&best) = selected_field_types.get(&(struct_id, field.offset))
            {
                xtype_to_field_type(best)
            } else {
                FieldType::Scalar(field.chunk)
            };
            let field_type = enforce_relocation_field_width(
                inferred,
                relocated_fields.contains(&(struct_id, field.offset)),
                pointer_size,
            );
            let field_name = make_field_ident(field.offset, field.chunk);
            emit_struct_field.push((struct_id, field_idx, field.offset, field_type, field_name));
        }
    }

    for row in emit_struct_field {
        db.rel_push("emit_struct_field", row);
    }

    for &row in &var_struct_map {
        db.rel_push("emit_var_is_struct_candidate", row);
    }

    let mut gsc_vec: Vec<(u64, usize, usize, usize)> = Vec::new();
    for (&layout_hash, &canonical_id) in &hash_to_canonical {
        if let Some(fields) = struct_fields_map.get(&canonical_id) {
            gsc_vec.push((
                layout_hash,
                canonical_id,
                fields.len(),
                compute_total_size(fields),
            ));
        }
    }
    for row in gsc_vec {
        db.rel_push("global_struct_catalog", row);
    }

    for (&layout_hash, &canonical_id) in &hash_to_canonical {
        db.rel_push("emit_canonical_struct_id", (layout_hash, canonical_id));
    }

    for (&id, &canonical_id) in &id_to_canonical {
        db.rel_push("struct_id_to_canonical", (id, canonical_id));
    }

    let mut esd_vec: Vec<(usize, usize, usize)> = Vec::new();
    for (&struct_id, fields) in &struct_fields_map {
        esd_vec.push((struct_id, fields.len(), compute_total_size(fields)));
    }
    for row in esd_vec {
        db.rel_push("emit_struct_def", row);
    }

    let mut reg_struct_id: HashMap<RTLReg, usize> = HashMap::new();
    for &(_, reg, sid) in &var_struct_map {
        reg_struct_id.insert(reg, sid);
    }

    // Push reg->canonical struct ID mapping to DB for ClightFieldPass and clight_select bridging
    for &(addr, reg, sid) in &var_struct_map {
        db.rel_push("reg_to_struct_id", (addr, reg, sid));
    }

    // Global ident -> struct binding: pure constant-offset globals carry no XstructPtr register, so without emit_global_struct_fields the definition is unreferenced and pruned at emission.
    {
        let mut egsf: Vec<(Ident, usize, Arc<Vec<(i64, Ident, MemoryChunk)>>)> = Vec::new();
        for (ident, fields) in &global_layouts {
            let layout_hash = compute_layout_hash(fields);
            if let Some(&sid) = hash_to_canonical.get(&layout_hash) {
                let field_tuples: Arc<Vec<(i64, Ident, MemoryChunk)>> = Arc::new(
                    fields
                        .iter()
                        .map(|f| (f.offset, make_field_ident(f.offset, f.chunk), f.chunk))
                        .collect(),
                );
                egsf.push((*ident, sid, field_tuples));
            }
        }
        for row in egsf {
            db.rel_push("emit_global_struct_fields", row);
        }
    }

    let abi_regs = &db.abi().int_arg_regs;

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
    for row in fpst {
        db.rel_push("func_param_struct_type_candidate", row);
    }

    for &(reg, xtype) in &refined_ptrs {
        if let Some(existing) = existing_types.get(&reg) {
            if matches!(
                existing,
                XType::Xcharptr
                    | XType::Xcharptrptr
                    | XType::Xintptr
                    | XType::Xfloatptr
                    | XType::Xsingleptr
                    | XType::Xfuncptr
            ) {
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
    if offsets.len() < CONFIG.struct_recovery.min_uniform_stride_fields {
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

fn compute_layout_hash(fields: &[InferredField]) -> u64 {
    let mut hasher = DefaultHasher::new();
    for field in fields {
        field.offset.hash(&mut hasher);
        chunk_byte_size(&field.chunk).hash(&mut hasher);
        field.chunk.hash(&mut hasher);
    }
    hasher.finish()
}

fn layout_hash_to_struct_id(layout_hash: u64) -> usize {
    let id = layout_hash as usize;
    if id == 0 {
        usize::MAX
    } else {
        id
    }
}

fn compute_total_size(fields: &[InferredField]) -> usize {
    if fields.is_empty() {
        return 0;
    }
    let first = &fields[0];
    let last = &fields[fields.len() - 1];
    let span = (last.offset - first.offset) as usize;
    span + chunk_byte_size(&last.chunk)
}

pub use crate::decompile::passes::csh_pass::{field_ident_to_name, make_field_ident};

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
        XType::Xcharptr => {
            FieldType::Pointer(Box::new(FieldType::Scalar(MemoryChunk::MInt8Signed)))
        }
        XType::Xcharptrptr => FieldType::Pointer(Box::new(FieldType::Pointer(Box::new(
            FieldType::Scalar(MemoryChunk::MInt8Signed),
        )))),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stack_lea_width_struct_recovery_uses_rtl_pointer_authority() {
        let mut prog = StructRecoveryProgram::default();
        let func = 0x1000;
        let narrow_node = 0x1010;
        let wide_node = 0x1020;
        let narrow = 0x110;
        let wide = 0x120;
        prog.instr_in_function
            .extend([(narrow_node, func), (wide_node, func)]);
        prog.rtl_inst.extend([
            (
                narrow_node,
                RTLInst::Iop(
                    Operation::Olea(Addressing::Ainstack(8)),
                    Arc::new(vec![]),
                    narrow,
                ),
            ),
            (
                wide_node,
                RTLInst::Iop(
                    Operation::Oleal(Addressing::Ainstack(16)),
                    Arc::new(vec![]),
                    wide,
                ),
            ),
        ]);
        prog.op_produces_ptr.push((wide_node, wide));
        prog.stack_var
            .extend([(func, narrow_node, 8, 0x210), (func, wide_node, 16, 0x220)]);

        prog.run();

        assert!(prog
            .stack_lea_reg
            .iter()
            .any(|fact| fact == &(func, 16, wide)));
        assert!(!prog
            .stack_lea_reg
            .iter()
            .any(|fact| fact == &(func, 8, narrow)));
        assert!(prog.stack_lea_base.iter().any(|fact| fact == &(func, 16)));
        assert!(!prog.stack_lea_base.iter().any(|fact| fact == &(func, 8)));
    }

    #[test]
    fn pointer_seed_and_residual_type_evidence_are_declarative() {
        let function = 0x1000;
        let parameter = 100;
        let multi_offset_base = 200;
        let indirect_callee = 300;
        let mut prog = StructRecoveryProgram::default();
        prog.emit_function_param_candidate
            .push((function, parameter));
        prog.rtl_inst.push((
            1,
            RTLInst::Iload(
                MemoryChunk::MInt32,
                Addressing::Aindexed(0),
                Arc::new(vec![parameter]),
                101,
            ),
        ));
        prog.rtl_inst.push((
            2,
            RTLInst::Iload(
                MemoryChunk::MInt32,
                Addressing::Aindexed(0),
                Arc::new(vec![multi_offset_base]),
                201,
            ),
        ));
        prog.rtl_inst.push((
            3,
            RTLInst::Iload(
                MemoryChunk::MInt32,
                Addressing::Aindexed(8),
                Arc::new(vec![multi_offset_base]),
                202,
            ),
        ));
        prog.rtl_inst.push((
            4,
            RTLInst::Icall(
                None,
                either::Either::Left(indirect_callee),
                Arc::new(vec![]),
                None,
                5,
            ),
        ));

        prog.run();

        assert!(prog.is_ptr.iter().any(|row| row == &(parameter,)));
        assert!(!prog.is_ptr.iter().any(|row| row == &(multi_offset_base,)));
        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| row == &(multi_offset_base, XType::Xptr)));
        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| row == &(indirect_callee, XType::Xfuncptr)));
    }

    #[test]
    fn layout_hash_is_the_struct_identity() {
        let fields = vec![
            InferredField {
                offset: 0,
                chunk: MemoryChunk::MInt32,
            },
            InferredField {
                offset: 8,
                chunk: MemoryChunk::MInt64,
            },
        ];
        let layout_hash = compute_layout_hash(&fields);

        assert_eq!(layout_hash_to_struct_id(layout_hash), layout_hash as usize);
        assert_ne!(layout_hash_to_struct_id(layout_hash), 0);
    }

    #[test]
    fn field_type_majority_vote_is_order_independent() {
        let mut prog = StructFieldTypeVoteProgram::default();
        for (occurrence, xtype) in [XType::Xptr, XType::Xint, XType::Xptr, XType::Xint]
            .into_iter()
            .enumerate()
        {
            prog.field_type_evidence.push((1, 8, occurrence, xtype));
        }

        prog.run();

        assert!(prog
            .selected_field_type
            .iter()
            .any(|row| row == &(1, 8, XType::Xint)));
    }

    #[test]
    fn exact_global_relocation_widens_a_narrow_field_to_pointer_width() {
        let base = 0xe090_usize;
        let fields = vec![
            InferredField {
                offset: 0,
                chunk: MemoryChunk::MAny64,
            },
            InferredField {
                offset: 8,
                chunk: MemoryChunk::MAny64,
            },
        ];
        let layout_hash = compute_layout_hash(&fields);
        let struct_id = layout_hash_to_struct_id(layout_hash);
        let authorities = relocated_global_struct_fields(
            &[(base, fields)],
            &HashMap::from([(layout_hash, struct_id)]),
            &HashSet::from([base as Address + 8]),
            8,
        );

        assert_eq!(authorities, HashSet::from([(struct_id, 8_i64)]));
        assert_eq!(
            enforce_relocation_field_width(
                FieldType::Scalar(MemoryChunk::MInt32),
                authorities.contains(&(struct_id, 8)),
                8,
            ),
            FieldType::Scalar(MemoryChunk::MInt64),
        );
    }

    #[test]
    fn relocation_width_authority_does_not_change_unrelated_or_wide_fields() {
        let base = 0xe090_usize;
        let fields = vec![
            InferredField {
                offset: 0,
                chunk: MemoryChunk::MAny64,
            },
            InferredField {
                offset: 8,
                chunk: MemoryChunk::MAny64,
            },
        ];
        let layout_hash = compute_layout_hash(&fields);
        let struct_id = layout_hash_to_struct_id(layout_hash);
        // A relocation in padding/not at a selected field cannot type either
        // declaration member.
        let authorities = relocated_global_struct_fields(
            &[(base, fields)],
            &HashMap::from([(layout_hash, struct_id)]),
            &HashSet::from([base as Address + 4]),
            8,
        );
        assert!(authorities.is_empty());

        let narrow = FieldType::Scalar(MemoryChunk::MInt32);
        assert_eq!(
            enforce_relocation_field_width(narrow.clone(), false, 8),
            narrow,
        );
        let already_wide = FieldType::Scalar(MemoryChunk::MInt64);
        assert_eq!(
            enforce_relocation_field_width(already_wide.clone(), true, 8),
            already_wide,
        );
        let already_pointer = FieldType::Pointer(Box::new(FieldType::Unknown));
        assert_eq!(
            enforce_relocation_field_width(already_pointer.clone(), true, 8),
            already_pointer,
        );

        let pass = StructRecoveryPass;
        assert!(pass.inputs().contains(&"op_produces_ptr"));
        assert!(pass.inputs().contains(&"pointer_in_data"));
        assert!(pass.inputs().contains(&"code_pointer_in_data"));
    }

    #[test]
    fn layout_selection_is_load_preferred_and_rejects_arrays_and_overlap() {
        let load_preferred = StructLayoutSource::Pointer(10);
        let valid_struct = StructLayoutSource::Pointer(20);
        let uniform_array = StructLayoutSource::Pointer(30);
        let overlap = StructLayoutSource::Pointer(40);
        let mut prog = StructLayoutProgram::default();

        // A widened store at offset zero must not override the byte load.  If
        // it did, the field would overlap the offset-four field.
        prog.layout_access
            .push((load_preferred, 0, MemoryChunk::MInt64, false));
        prog.layout_access
            .push((load_preferred, 0, MemoryChunk::MInt8Unsigned, true));
        prog.layout_access
            .push((load_preferred, 4, MemoryChunk::MInt32, false));

        prog.layout_access
            .push((valid_struct, 0, MemoryChunk::MInt32, false));
        prog.layout_access
            .push((valid_struct, 8, MemoryChunk::MInt64, false));

        for offset in [0, 4, 8] {
            prog.layout_access
                .push((uniform_array, offset, MemoryChunk::MInt32, true));
        }

        prog.layout_access
            .push((overlap, 0, MemoryChunk::MInt64, true));
        prog.layout_access
            .push((overlap, 4, MemoryChunk::MInt32, true));

        prog.run();

        assert!(prog
            .selected_layout_field
            .iter()
            .any(|row| row == &(load_preferred, 0, MemoryChunk::MInt8Unsigned)));
        assert!(prog
            .valid_struct_layout
            .iter()
            .any(|row| row == &(load_preferred,)));
        assert!(prog
            .valid_struct_layout
            .iter()
            .any(|row| row == &(valid_struct,)));
        assert!(!prog
            .valid_struct_layout
            .iter()
            .any(|row| row == &(uniform_array,)));
        assert!(!prog
            .valid_struct_layout
            .iter()
            .any(|row| row == &(overlap,)));
    }
}
