
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::declare_io_from;

use std::sync::Arc;
use crate::x86::mach::Mreg;
use crate::x86::op::{Addressing, Condition, Operation};
use crate::x86::types::*;
use ascent::ascent_par;
use either::Either;


/// Map a memory chunk to the XType of the value loaded/stored.
fn chunk_xtype(chunk: &MemoryChunk) -> XType {
    match chunk {
        MemoryChunk::MBool => XType::Xbool,
        MemoryChunk::MInt8Signed => XType::Xint8signed,
        MemoryChunk::MInt8Unsigned => XType::Xint8unsigned,
        MemoryChunk::MInt16Signed => XType::Xint16signed,
        MemoryChunk::MInt16Unsigned => XType::Xint16unsigned,
        MemoryChunk::MInt32 | MemoryChunk::MAny32 => XType::Xint,
        MemoryChunk::MInt64 | MemoryChunk::MAny64 => XType::Xany64,
        MemoryChunk::MFloat32 => XType::Xsingle,
        MemoryChunk::MFloat64 => XType::Xfloat,
        // Xany64 is a width floor; Xlong would falsely claim signed-64.
        MemoryChunk::Unknown => XType::Xany64,
    }
}

/// Map an operation to its output register's XType, returning None for unclassified operations.
fn op_output_xtype(op: &Operation) -> Option<XType> {
    use Operation::*;
    match op {
        // Signed 32-bit
        Odiv | Omod | Oshr | Oshrimm(_) | Oshrximm(_) |
        Odivimm(_) | Omodimm(_) |
        Ocast32signed | Omulhs => Some(XType::Xint),

        // Unsigned 32-bit
        Odivu | Omodu | Oshru | Oshruimm(_) |
        Odivuimm(_) | Omoduimm(_) |
        Ocast32unsigned | Omulhu => Some(XType::Xintunsigned),

        // Ambiguous 32-bit (add/sub/mul/logic -- same for signed and unsigned)
        Oadd | Osub | Omul | Oaddimm(_) | Omulimm(_) |
        Oand | Oor | Oxor | Onot | Oneg |
        Oandimm(_) | Oorimm(_) | Oxorimm(_) |
        Oshl | Oshlimm(_) | Olowlong |
        Ointconst(_) | Ointoffloat | Ointofsingle => Some(XType::Xint),

        // 64-bit LEA produces a pointer, not a 32-bit int
        Oleal(_) => Some(XType::Xptr),

        // Signed 64-bit
        Odivl | Omodl | Oshrl | Oshrlimm(_) | Oshrxlimm(_) |
        Odivlimm(_) | Omodlimm(_) |
        Omullhs => Some(XType::Xlong),

        // Unsigned 64-bit
        Odivlu | Omodlu | Oshrlu | Oshrluimm(_) |
        Odivluimm(_) | Omodluimm(_) |
        Omullhu => Some(XType::Xlongunsigned),

        // Ambiguous 64-bit
        Oaddl | Osubl | Omull | Oaddlimm(_) | Omullimm(_) |
        Oandl | Oorl | Oxorl | Onotl | Onegl |
        Oandlimm(_) | Oorlimm(_) | Oxorlimm(_) |
        Oshll | Oshllimm(_) |
        Olongconst(_) |
        Olongoffloat | Olongofsingle => Some(XType::Xlong),

        // Pointer (address computation)
        Olea(_) | Oindirectsymbol(_) => Some(XType::Xptr),

        // Sub-int casts
        Ocast8signed => Some(XType::Xint8signed),
        Ocast8unsigned => Some(XType::Xint8unsigned),
        Ocast16signed => Some(XType::Xint16signed),
        Ocast16unsigned => Some(XType::Xint16unsigned),

        // Float (double precision)
        Onegf | Oabsf | Oaddf | Osubf | Omulf |
        Ofloatofint | Ofloatoflong |
        Osingleoffloat => Some(XType::Xfloat),

        // Float (single precision)
        Onegfs | Oabsfs | Oaddfs | Osubfs | Omulfs |
        Osingleofint | Osingleoflong |
        Ofloatofsingle => Some(XType::Xsingle),

        // Comparison result (boolean)
        Ocmp(_) => Some(XType::Xbool),

        _ => None,
    }
}

/// Map a comparison condition to the XType of its operands.
fn cond_operand_xtype(cond: &Condition) -> Option<XType> {
    match cond {
        // Signed 32-bit comparison
        Condition::Ccomp(_) | Condition::Ccompimm(_, _) => Some(XType::Xint),
        // Unsigned 32-bit comparison
        Condition::Ccompu(_) | Condition::Ccompuimm(_, _) => Some(XType::Xintunsigned),
        // Signed 64-bit comparison
        Condition::Ccompl(_) => Some(XType::Xlong),
        Condition::Ccomplimm(_, 0) => Some(XType::Xany64),  // possible NULL check
        Condition::Ccomplimm(_, _) => Some(XType::Xlong),
        // Unsigned 64-bit comparison
        Condition::Ccomplu(_) => Some(XType::Xlongunsigned),
        Condition::Ccompluimm(_, 0) => Some(XType::Xany64), // possible NULL check
        Condition::Ccompluimm(_, _) => Some(XType::Xlongunsigned),
        // Float comparison
        Condition::Ccompf(_) | Condition::Cnotcompf(_) => Some(XType::Xfloat),
        // Single comparison
        Condition::Ccompfs(_) | Condition::Cnotcompfs(_) => Some(XType::Xsingle),
        _ => None,
    }
}

/// Returns true if the operation consumes floating-point (double) operands.
fn is_float_op(op: &Operation) -> bool {
    use Operation::*;
    matches!(op,
        Onegf | Oabsf | Oaddf | Osubf | Omulf | Odivf | Omaxf | Ominf |
        Osingleoffloat | Ointoffloat | Olongoffloat |
        Onegfs | Oabsfs | Oaddfs | Osubfs | Omulfs | Odivfs |
        Ofloatofsingle | Ointofsingle | Olongofsingle
    )
}

/// Returns true if the condition compares floating-point operands.
fn is_float_cond(cond: &Condition) -> bool {
    matches!(cond,
        Condition::Ccompf(_) | Condition::Cnotcompf(_) |
        Condition::Ccompfs(_) | Condition::Cnotcompfs(_)
    )
}


ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct TypePassProgram;

    // Input relations (swapped from DecompileDB)

    relation emit_var_type_candidate(RTLReg, XType);
    relation alias_edge(RTLReg, RTLReg);
    relation stack_var_chunk(Address, i64, MemoryChunk);
    relation stack_var(Address, Address, i64, RTLReg);
    relation ltl_inst(Node, LTLInst);
    relation rtl_inst(Node, RTLInst);
    relation reg_rtl(Node, Mreg, RTLReg);

    relation func_param_position_type(Address, usize, XType);
    relation emit_function(Address, Symbol, Node);
    relation emit_function_return_type_xtype_candidate(Address, XType);
    relation emit_function_return(Address, RTLReg);
    relation call_target_func(Node, Address);

    relation string_data(String, String, usize);
    relation ident_to_symbol(Ident, Symbol);

    relation known_func_param_is_ptr(Symbol, usize);
    relation known_func_returns_ptr(Symbol);
    relation known_func_returns_long(Symbol);
    relation known_func_returns_int(Symbol);
    relation known_func_returns_float(Symbol);
    relation known_func_returns_single(Symbol);
    relation known_extern_signature(Symbol, usize, XType, Arc<Vec<XType>>);

    relation call_site(Node, Symbol);
    relation call_arg(Node, usize, RTLReg);
    relation call_return_reg(Node, RTLReg);
    relation call_arg_mapping(Node, usize, RTLReg);

    // Derive call_site from call_target_func + emit_function (internal calls)
    call_site(node, *name) <--
        call_target_func(node, target),
        emit_function(target, name, _);

    // Derive call_arg from call_arg_mapping
    call_arg(node, pos, reg) <--
        call_arg_mapping(node, pos, reg);


    // 1. Direct type emission from instructions -- each instruction encodes width and signedness, emitting concrete types directly

    // From operations: op encodes the full output type
    emit_var_type_candidate(rtl_reg, xtype) <--
        ltl_inst(node, ?LTLInst::Lop(op, _, dst_mreg)),
        if let Some(xtype) = op_output_xtype(op),
        reg_rtl(node, *dst_mreg, rtl_reg);

    // From load chunks: chunk encodes the loaded value's type
    emit_var_type_candidate(rtl_reg, chunk_xtype(chunk)) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, _, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    // From store chunks: chunk encodes the stored value's type
    emit_var_type_candidate(rtl_reg, chunk_xtype(chunk)) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, _, _, src_mreg)),
        reg_rtl(node, *src_mreg, rtl_reg);

    // From stack variable chunks
    emit_var_type_candidate(rtl_reg, chunk_xtype(chunk)) <--
        stack_var(func, _, ofs, rtl_reg),
        stack_var_chunk(func, ofs, chunk);

    // From comparison operands: condition encodes operand type
    emit_var_type_candidate(rtl_reg, xtype) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ocmp(cond), args, _)),
        if let Some(xtype) = cond_operand_xtype(cond),
        for mreg in args.iter(),
        reg_rtl(node, *mreg, rtl_reg);

    // 2. MOVSD upgrade: MAny64 -> Xfloat when the register is used in float arithmetic.
    emit_var_type_candidate(rtl_reg, XType::Xfloat) <--
        emit_var_type_candidate(rtl_reg, ?XType::Xany64),
        rtl_inst(_, ?RTLInst::Iop(op, args, _)),
        if is_float_op(op),
        if args.contains(&rtl_reg);

    // Also upgrade when the register is the destination of a float operation
    emit_var_type_candidate(rtl_reg, XType::Xfloat) <--
        emit_var_type_candidate(rtl_reg, ?XType::Xany64),
        rtl_inst(_, ?RTLInst::Iop(op, _, dst)),
        if is_float_op(op),
        if dst == rtl_reg;

    // Also upgrade when the register is used in a float comparison
    emit_var_type_candidate(rtl_reg, XType::Xfloat) <--
        emit_var_type_candidate(rtl_reg, ?XType::Xany64),
        rtl_inst(_, ?RTLInst::Iop(Operation::Ocmp(cond), args, _)),
        if is_float_cond(cond),
        if args.contains(&rtl_reg);


    // 3. Pointer evidence (no is_not_ptr -- pointers are a subtype of 8-byte int, no conflict)

    relation is_ptr(RTLReg);
    relation is_char_ptr(RTLReg);
    relation must_be_ptr(RTLReg);

    // Pointer-producing operations
    relation op_produces_ptr(Node, RTLReg);
    relation base_addr_usage(Node, RTLReg, i64);

    is_ptr(reg) <-- op_produces_ptr(_, reg);
    is_ptr(reg) <-- base_addr_usage(_, reg, _);

    must_be_ptr(reg) <--
        call_site(node, func_name),
        call_arg(node, arg_idx, reg),
        known_func_param_is_ptr(func_name, arg_idx);

    must_be_ptr(ret_reg) <--
        call_site(node, func_name),
        call_return_reg(node, ret_reg),
        known_func_returns_ptr(func_name);

    must_be_ptr(rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Oindirectsymbol(_), _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    must_be_ptr(callee_rtl) <--
        ltl_inst(node, ?LTLInst::Lcall(Either::Left(mreg))),
        reg_rtl(node, *mreg, callee_rtl);

    must_be_ptr(callee_rtl) <--
        ltl_inst(node, ?LTLInst::Ltailcall(Either::Left(mreg))),
        reg_rtl(node, *mreg, callee_rtl);

    is_ptr(reg) <-- must_be_ptr(reg);

    // From extern signatures
    is_ptr(arg_reg) <--
        call_site(node, func_name),
        call_arg(node, arg_idx, arg_reg),
        known_extern_signature(func_name, _, _, params),
        if *arg_idx < params.len(),
        if matches!(params[*arg_idx], XType::Xptr | XType::Xcharptr | XType::Xcharptrptr | XType::Xintptr |
            XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr | XType::XstructPtr(_));

    is_ptr(ret_reg) <--
        call_site(node, func_name),
        call_return_reg(node, ret_reg),
        known_extern_signature(func_name, _, ret_type, _),
        if matches!(ret_type, XType::Xptr | XType::Xcharptr | XType::Xcharptrptr | XType::Xintptr |
            XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr | XType::XstructPtr(_));

    is_ptr(ret_reg) <--
        call_site(node, func_name),
        call_return_reg(node, ret_reg),
        known_func_returns_ptr(func_name);

    // From internal function signatures
    relation internal_func_signature(Symbol, usize, XType);

    internal_func_signature(*name, *pos, *xtype) <--
        func_param_position_type(func_start, pos, xtype),
        emit_function(func_start, name, _);

    is_ptr(arg_reg) <--
        call_site(node, func_name),
        call_arg(node, arg_idx, arg_reg),
        internal_func_signature(func_name, arg_idx, xtype),
        if matches!(xtype, XType::Xptr | XType::Xcharptr | XType::Xcharptrptr | XType::Xintptr |
            XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr | XType::XstructPtr(_));

    // From load/store base address
    is_ptr(base_rtl) <--
        ltl_inst(node, ?LTLInst::Lload(_, addr, args, dst)),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        if base_mreg != *dst,
        reg_rtl(node, base_mreg, base_rtl);

    is_ptr(base_rtl) <--
        ltl_inst(node, ?LTLInst::Lstore(_, addr, args, src)),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        if base_mreg != *src,
        reg_rtl(node, base_mreg, base_rtl);

    is_ptr(base_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Oindirectsymbol(_), _, dst_mreg)),
        reg_rtl(node, *dst_mreg, base_rtl);

    // Char pointer from byte load/store
    is_char_ptr(base_rtl) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, addr, args, _)),
        if matches!(chunk, MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned | MemoryChunk::MBool),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        reg_rtl(node, base_mreg, base_rtl);

    is_char_ptr(base_rtl) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, addr, args, _)),
        if matches!(chunk, MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned | MemoryChunk::MBool),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        reg_rtl(node, base_mreg, base_rtl);

    // String literal -> char pointer
    relation string_symbol(String);
    string_symbol(label.clone()) <-- string_data(label, _, _);

    is_char_ptr(rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Oindirectsymbol(sym_id), _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg),
        ident_to_symbol(sym_id, label),
        string_symbol(label.to_string());

    // Pointer element type (for typed pointer derivation)
    relation ptr_element_type(RTLReg, XType);
    relation has_ptr_element_conflict(RTLReg);

    ptr_element_type(base_rtl, XType::Xint) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, addr, args, _)),
        if matches!(chunk, MemoryChunk::MInt32 | MemoryChunk::MAny32),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        reg_rtl(node, base_mreg, base_rtl);

    ptr_element_type(base_rtl, XType::Xfloat) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, addr, args, _)),
        if matches!(chunk, MemoryChunk::MFloat64),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        reg_rtl(node, base_mreg, base_rtl);

    ptr_element_type(base_rtl, XType::Xsingle) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, addr, args, _)),
        if matches!(chunk, MemoryChunk::MFloat32),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        reg_rtl(node, base_mreg, base_rtl);

    ptr_element_type(base_rtl, XType::Xint) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, addr, args, _)),
        if matches!(chunk, MemoryChunk::MInt32 | MemoryChunk::MAny32),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        reg_rtl(node, base_mreg, base_rtl);

    ptr_element_type(base_rtl, XType::Xfloat) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, addr, args, _)),
        if matches!(chunk, MemoryChunk::MFloat64),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        reg_rtl(node, base_mreg, base_rtl);

    ptr_element_type(base_rtl, XType::Xsingle) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, addr, args, _)),
        if matches!(chunk, MemoryChunk::MFloat32),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        reg_rtl(node, base_mreg, base_rtl);

    // From extern signatures
    ptr_element_type(arg_reg, XType::Xint) <--
        call_site(node, func_name),
        call_arg(node, arg_idx, arg_reg),
        known_extern_signature(func_name, _, _, params),
        if *arg_idx < params.len(),
        if params[*arg_idx] == XType::Xintptr;

    ptr_element_type(arg_reg, XType::Xfloat) <--
        call_site(node, func_name),
        call_arg(node, arg_idx, arg_reg),
        known_extern_signature(func_name, _, _, params),
        if *arg_idx < params.len(),
        if params[*arg_idx] == XType::Xfloatptr;

    ptr_element_type(arg_reg, XType::Xsingle) <--
        call_site(node, func_name),
        call_arg(node, arg_idx, arg_reg),
        known_extern_signature(func_name, _, _, params),
        if *arg_idx < params.len(),
        if params[*arg_idx] == XType::Xsingleptr;

    // ptr_element_type alias propagation lives here (is_ptr/is_char_ptr live in rtl_pass).
    ptr_element_type(b, ty) <-- ptr_element_type(a, ty), alias_edge(a, b);
    ptr_element_type(a, ty) <-- ptr_element_type(b, ty), alias_edge(a, b);

    has_ptr_element_conflict(reg) <-- ptr_element_type(reg, a), ptr_element_type(reg, b), if a != b;

    relation has_int_ptr_type(RTLReg);
    relation has_float_ptr_type(RTLReg);
    relation has_single_ptr_type(RTLReg);

    has_int_ptr_type(reg) <-- is_ptr(reg), ptr_element_type(reg, ?XType::Xint), !has_ptr_element_conflict(reg);
    has_float_ptr_type(reg) <-- is_ptr(reg), ptr_element_type(reg, ?XType::Xfloat), !has_ptr_element_conflict(reg);
    has_single_ptr_type(reg) <-- is_ptr(reg), ptr_element_type(reg, ?XType::Xsingle), !has_ptr_element_conflict(reg);


    // 4. Pointer deref: tracks what a pointer dereferences to

    relation ptr_deref(RTLReg, RTLReg);
    // Directed relations: track store sources and load destinations separately
    relation ptr_store(RTLReg, RTLReg); // ptr_store(ptr, src) -- *ptr = src
    relation ptr_load(RTLReg, RTLReg);  // ptr_load(ptr, dst) -- dst = *ptr
    // Chunked variants: store->load propagation verifies same access width.
    relation ptr_store_chunk(RTLReg, RTLReg, MemoryChunk);
    relation ptr_load_chunk(RTLReg, RTLReg, MemoryChunk);

    // Load: dst = *p
    ptr_deref(base_rtl, dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lload(_, addr, args, dst_mreg)),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        if base_mreg != *dst_mreg,
        reg_rtl(node, base_mreg, base_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl);

    ptr_load(base_rtl, dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lload(_, addr, args, dst_mreg)),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        if base_mreg != *dst_mreg,
        reg_rtl(node, base_mreg, base_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl);

    ptr_load_chunk(base_rtl, dst_rtl, *chunk) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, addr, args, dst_mreg)),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        if base_mreg != *dst_mreg,
        reg_rtl(node, base_mreg, base_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl);

    // Store: *p = src
    ptr_deref(base_rtl, src_rtl) <--
        ltl_inst(node, ?LTLInst::Lstore(_, addr, args, src_mreg)),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        if base_mreg != *src_mreg,
        reg_rtl(node, base_mreg, base_rtl),
        reg_rtl(node, *src_mreg, src_rtl);

    ptr_store(base_rtl, src_rtl) <--
        ltl_inst(node, ?LTLInst::Lstore(_, addr, args, src_mreg)),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        if base_mreg != *src_mreg,
        reg_rtl(node, base_mreg, base_rtl),
        reg_rtl(node, *src_mreg, src_rtl);

    ptr_store_chunk(base_rtl, src_rtl, *chunk) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, addr, args, src_mreg)),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        if base_mreg != *src_mreg,
        reg_rtl(node, base_mreg, base_rtl),
        reg_rtl(node, *src_mreg, src_rtl);

    // Aliased pointers share deref targets (invariance for mutable pointers)
    ptr_deref(q, x) <-- ptr_deref(p, x), alias_edge(p, q);
    ptr_deref(p, x) <-- ptr_deref(q, x), alias_edge(p, q);
    ptr_store(q, x) <-- ptr_store(p, x), alias_edge(p, q);
    ptr_store(p, x) <-- ptr_store(q, x), alias_edge(p, q);
    ptr_load(q, x) <-- ptr_load(p, x), alias_edge(p, q);
    ptr_load(p, x) <-- ptr_load(q, x), alias_edge(p, q);
    ptr_store_chunk(q, x, c) <-- ptr_store_chunk(p, x, c), alias_edge(p, q);
    ptr_store_chunk(p, x, c) <-- ptr_store_chunk(q, x, c), alias_edge(p, q);
    ptr_load_chunk(q, x, c) <-- ptr_load_chunk(p, x, c), alias_edge(p, q);
    ptr_load_chunk(p, x, c) <-- ptr_load_chunk(q, x, c), alias_edge(p, q);

    // Store->load type propagation; matching chunk guard prevents width mismatch pollution.
    emit_var_type_candidate(dst, ty) <--
        emit_var_type_candidate(src, ty),
        ptr_store_chunk(p, src, chunk),
        ptr_load_chunk(p, dst, chunk);


    // 6. Emit type candidates from known function signatures (extern and internal) into emit_var_type_candidate

    // Extern call arg: emit param type as candidate
    emit_var_type_candidate(arg_reg, params[*arg_idx].clone()) <--
        call_site(node, func_name),
        call_arg(node, arg_idx, arg_reg),
        known_extern_signature(func_name, _, _, params),
        if *arg_idx < params.len(),
        if params[*arg_idx] != XType::Xany32 && params[*arg_idx] != XType::Xany64;

    // Extern call return: emit return type as candidate
    emit_var_type_candidate(ret_reg, *ret_type) <--
        call_site(node, func_name),
        call_return_reg(node, ret_reg),
        known_extern_signature(func_name, _, ret_type, _),
        if *ret_type != XType::Xvoid && *ret_type != XType::Xany32 && *ret_type != XType::Xany64;

    // Internal function arg: emit param type as candidate
    emit_var_type_candidate(arg_reg, *xtype) <--
        call_site(node, func_name),
        call_arg(node, arg_idx, arg_reg),
        internal_func_signature(func_name, arg_idx, xtype),
        if *xtype != XType::Xany32 && *xtype != XType::Xany64;

    // Internal function return types
    relation internal_func_return_type(Symbol, XType);

    internal_func_return_type(*name, *xtype) <--
        emit_function_return_type_xtype_candidate(func_start, xtype),
        emit_function(func_start, name, _);

    // Internal call return: emit return type as candidate
    emit_var_type_candidate(ret_reg, *xtype) <--
        call_site(node, func_name),
        call_return_reg(node, ret_reg),
        internal_func_return_type(func_name, xtype),
        if *xtype != XType::Xvoid && *xtype != XType::Xany32 && *xtype != XType::Xany64;

    // Internal pointer-returning functions: propagate is_ptr to call return registers
    is_ptr(ret_reg) <--
        call_site(node, func_name),
        call_return_reg(node, ret_reg),
        internal_func_return_type(func_name, xtype),
        if matches!(xtype, XType::Xptr | XType::Xcharptr | XType::Xcharptrptr | XType::Xintptr |
            XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr | XType::XstructPtr(_));

    // Function's own return register: emit return type as candidate
    emit_var_type_candidate(ret_reg, *xtype) <--
        emit_function_return(func_start, ret_reg),
        emit_function_return_type_xtype_candidate(func_start, xtype),
        if *xtype != XType::Xvoid && *xtype != XType::Xany32 && *xtype != XType::Xany64;


    // 7. Pointer subtype emission from pointer evidence (base types come from section 1 instructions)

    emit_var_type_candidate(reg, XType::Xcharptr) <-- is_char_ptr(reg);
    emit_var_type_candidate(reg, XType::Xintptr) <-- has_int_ptr_type(reg);
    emit_var_type_candidate(reg, XType::Xfloatptr) <-- has_float_ptr_type(reg);
    emit_var_type_candidate(reg, XType::Xsingleptr) <-- has_single_ptr_type(reg);
    emit_var_type_candidate(reg, XType::Xptr) <-- is_ptr(reg);

    // Disabled: bidirectional int/ptr pollution causes every int to become ptr candidate
    // emit_var_type_candidate(reg, XType::Xlong) <-- emit_var_type_candidate(reg, XType::Xptr);
    // emit_var_type_candidate(reg, XType::Xint) <-- emit_var_type_candidate(reg, XType::Xptr);
    // emit_var_type_candidate(reg, XType::Xptr) <-- emit_var_type_candidate(reg, XType::Xint);
    // emit_var_type_candidate(reg, XType::Xptr) <-- emit_var_type_candidate(reg, XType::Xlong);

    // 7b. Pointer arithmetic propagation: add/sub on a known pointer produces a pointer (Olea/Oleal/Oaddl/Osubl)
    is_ptr(dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Olea(addr), args, dst_mreg)),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        reg_rtl(node, args[0], src_rtl),
        is_ptr(src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl);

    is_ptr(dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Oleal(addr), args, dst_mreg)),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        reg_rtl(node, args[0], src_rtl),
        is_ptr(src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl);

    // Oaddl(ptr, offset) -> result is ptr
    is_ptr(dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Oaddl, args, dst_mreg)),
        if !args.is_empty(),
        reg_rtl(node, args[0], src_rtl),
        is_ptr(src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl);

    // Osubl(ptr, offset) -> result is ptr (negative indexing)
    is_ptr(dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Osubl, args, dst_mreg)),
        if !args.is_empty(),
        reg_rtl(node, args[0], src_rtl),
        is_ptr(src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl);

    // Oaddlimm(ptr, const) -> result is ptr
    is_ptr(dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Oaddlimm(_), args, dst_mreg)),
        if !args.is_empty(),
        reg_rtl(node, args[0], src_rtl),
        is_ptr(src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl);

    // Osel(cond, typ): conditional select -- if either operand is ptr, result is ptr
    is_ptr(dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Osel(_, _), args, dst_mreg)),
        if args.len() >= 2,
        reg_rtl(node, args[0], src_rtl),
        is_ptr(src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl);

    is_ptr(dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Osel(_, _), args, dst_mreg)),
        if args.len() >= 2,
        reg_rtl(node, args[1], src_rtl),
        is_ptr(src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl);

    // Omove of a pointer -> result is ptr (register-register copy)
    op_produces_ptr(node, dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Omove, args, dst_mreg)),
        if !args.is_empty(),
        reg_rtl(node, args[0], src_rtl),
        is_ptr(src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl);

    // 8. Function pointer detection: registers used as indirect call targets
    emit_var_type_candidate(*callee_reg, XType::Xfuncptr) <--
        rtl_inst(_, ?RTLInst::Icall(_, Either::Left(callee_reg), _, _, _));

    emit_var_type_candidate(*callee_reg, XType::Xfuncptr) <--
        rtl_inst(_, ?RTLInst::Itailcall(_, Either::Left(callee_reg), _));

    // 9. Global pointer type detection via dereference evidence, call constraints, and known sigs.
    relation global_addr_reg(Ident, RTLReg);
    relation emit_global_is_ptr(Ident);
    relation emit_global_is_char_ptr(Ident);
    #[local] relation global_value_reg(Ident, RTLReg);

    // Propagate global address register through aliases (may discover more via type_pass context)
    global_addr_reg(*ident, b) <-- global_addr_reg(ident, a), alias_edge(a, b);
    global_addr_reg(*ident, a) <-- global_addr_reg(ident, b), alias_edge(a, b);

    // Via Oindirectsymbol (PIC binaries): track the value register loaded from a global
    global_value_reg(*ident, loaded_rtl) <--
        global_addr_reg(ident, addr_rtl),
        ltl_inst(node, ?LTLInst::Lload(chunk, Addressing::Aindexed(0), args, dst_mreg)),
        if matches!(chunk, MemoryChunk::MAny64 | MemoryChunk::MInt64),
        if !args.is_empty(),
        reg_rtl(node, args[0], base_rtl),
        if *addr_rtl == *base_rtl,
        reg_rtl(node, *dst_mreg, loaded_rtl);

    // Via direct Aglobal addressing: track the value register
    global_value_reg(*ident, loaded_rtl) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, Addressing::Aglobal(ident, 0), _, dst_mreg)),
        if matches!(chunk, MemoryChunk::MAny64 | MemoryChunk::MInt64),
        reg_rtl(node, *dst_mreg, loaded_rtl);

    global_value_reg(*ident, loaded_rtl) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, Addressing::Abased(ident, 0), _, dst_mreg)),
        if matches!(chunk, MemoryChunk::MAny64 | MemoryChunk::MInt64),
        reg_rtl(node, *dst_mreg, loaded_rtl);

    // Propagate global value reg through aliases
    global_value_reg(*ident, b) <-- global_value_reg(ident, a), alias_edge(a, b);
    global_value_reg(*ident, a) <-- global_value_reg(ident, b), alias_edge(a, b);

    // A global is a pointer if its loaded value is dereferenced (used as memory base)
    emit_global_is_ptr(*ident) <--
        global_value_reg(ident, loaded_rtl),
        ptr_deref(loaded_rtl, _);

    // Also mark as pointer if the loaded value has must_be_ptr evidence (strong call constraint)
    emit_global_is_ptr(*ident) <--
        global_value_reg(ident, loaded_rtl),
        must_be_ptr(loaded_rtl);

    // A global is a pointer if passed as a call argument to a known pointer parameter
    emit_global_is_ptr(*ident) <--
        global_value_reg(ident, loaded_rtl),
        call_arg(node, arg_idx, loaded_rtl),
        call_site(node, func_name),
        known_extern_signature(func_name, _, _, params),
        if *arg_idx < params.len(),
        if matches!(params[*arg_idx], XType::Xptr | XType::Xcharptr | XType::Xcharptrptr | XType::Xintptr |
            XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr | XType::XstructPtr(_));

    emit_global_is_ptr(*ident) <--
        global_value_reg(ident, loaded_rtl),
        call_arg(node, arg_idx, loaded_rtl),
        call_site(node, func_name),
        internal_func_signature(func_name, arg_idx, xtype),
        if matches!(xtype, XType::Xptr | XType::Xcharptr | XType::Xcharptrptr | XType::Xintptr |
            XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr | XType::XstructPtr(_));

    emit_global_is_ptr(*ident) <--
        global_value_reg(ident, loaded_rtl),
        call_arg(node, arg_idx, loaded_rtl),
        call_site(node, func_name),
        known_func_param_is_ptr(func_name, arg_idx);

    // A global is a char pointer if its loaded value is used to load/store bytes
    emit_global_is_char_ptr(*ident) <--
        global_value_reg(ident, loaded_rtl),
        is_char_ptr(loaded_rtl);

    // A global is a char pointer if passed as a char* argument
    emit_global_is_char_ptr(*ident) <--
        global_value_reg(ident, loaded_rtl),
        call_arg(node, arg_idx, loaded_rtl),
        call_site(node, func_name),
        known_extern_signature(func_name, _, _, params),
        if *arg_idx < params.len(),
        if params[*arg_idx] == XType::Xcharptr;
}

pub struct TypePass;

impl IRPass for TypePass {
    fn name(&self) -> &'static str { "type" }

    fn run(&self, db: &mut DecompileDB) {
        let mut prog = TypePassProgram::default();
        prog.swap_db_fields(db);

        prog.run();

        prog.swap_db_fields(db);
    }

    declare_io_from!(TypePassProgram);
}
