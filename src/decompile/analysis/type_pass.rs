use crate::declare_io_from;
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;

use crate::mreg::Mreg;
use crate::x86::op::{Addressing, Comparison, Condition, Operation};
use crate::x86::types::*;
use ascent::ascent_par;
use either::Either;
use std::sync::Arc;

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

/// Interpret a value view at the decoder's physical memory width. A stack
/// get/set's `Typ` describes the promoted value, not the accessed object:
/// loading one byte into EAX is still a one-byte access. Preserve an explicit
/// chunk's interpretation only when its width agrees with the machine.
fn storage_chunk_at_width(view: MemoryChunk, bytes: usize) -> MemoryChunk {
    if view != MemoryChunk::Unknown
        && crate::decompile::analysis::struct_recovery_pass::chunk_byte_size(&view) == bytes
    {
        return view;
    }
    match bytes {
        1 => MemoryChunk::MInt8Unsigned,
        2 => MemoryChunk::MInt16Unsigned,
        4 => MemoryChunk::MAny32,
        8 => MemoryChunk::MAny64,
        // An aggregate/vector access is not evidence for a narrower scalar.
        _ => MemoryChunk::Unknown,
    }
}

/// Map an operation to its output register's XType, returning None for unclassified operations.
fn op_output_xtype(op: &Operation) -> Option<XType> {
    use Operation::*;
    match op {
        // Signed 32-bit
        Odiv | Omod | Oshr | Oshrimm(_) | Oshrximm(_) | Odivimm(_) | Omodimm(_) | Ocast32signed
        | Omulhs => Some(XType::Xint),

        // Unsigned 32-bit
        Odivu | Omodu | Oshru | Oshruimm(_) | Odivuimm(_) | Omoduimm(_) | Ocast32unsigned
        | Omulhu => Some(XType::Xintunsigned),

        // Ambiguous 32-bit (add/sub/mul/logic, same for signed and unsigned)
        Oadd | Osub | Omul | Oaddimm(_) | Omulimm(_) | Oand | Oor | Oxor | Onot | Oneg
        | Oandimm(_) | Oorimm(_) | Oxorimm(_) | Oshl | Oshlimm(_) | Olowlong | Ointconst(_)
        | Ointoffloat | Ointofsingle => Some(XType::Xint),

        // 64-bit LEA gets an integer-width floor (Xlong) only: gcc emits lea for plain integer arithmetic too, so forcing Xptr broke branchless selects; use-based is_ptr supplies Xptr in section 7.
        Oleal(_) => Some(XType::Xlong),

        // Signed 64-bit
        Odivl | Omodl | Oshrl | Oshrlimm(_) | Oshrxlimm(_) | Odivlimm(_) | Omodlimm(_)
        | Omullhs => Some(XType::Xlong),

        // Unsigned 64-bit
        Odivlu | Omodlu | Oshrlu | Oshrluimm(_) | Odivluimm(_) | Omodluimm(_) | Omullhu => {
            Some(XType::Xlongunsigned)
        }

        // Ambiguous 64-bit
        Oaddl | Osubl | Omull | Oaddlimm(_) | Omullimm(_) | Oandl | Oorl | Oxorl | Onotl
        | Onegl | Oandlimm(_) | Oorlimm(_) | Oxorlimm(_) | Oshll | Oshllimm(_) | Olongconst(_)
        | Olongoffloat | Olongofsingle => Some(XType::Xlong),

        // 32-bit LEA gets an integer-width floor (Xint) only, for the same reason as Oleal; pointerness is decided by use-based is_ptr evidence in section 7.
        Olea(_) => Some(XType::Xint),

        // Oindirectsymbol loads a symbol's address (e.g. GOT entry): unconditionally a pointer.
        Oindirectsymbol(_) => Some(XType::Xptr),

        // Sub-int casts
        Ocast8signed => Some(XType::Xint8signed),
        Ocast8unsigned => Some(XType::Xint8unsigned),
        Ocast16signed => Some(XType::Xint16signed),
        Ocast16unsigned => Some(XType::Xint16unsigned),

        // Float (double precision). Ofloatofsingle is CVTSS2SD (f32->f64) per asm_pass; the previous grouping had single<->double conversions swapped.
        Onegf | Oabsf | Oaddf | Osubf | Omulf | Odivf | Omaxf | Ominf | Ofloatofint
        | Ofloatoflong | Ofloatofsingle => Some(XType::Xfloat),

        // Float (single precision). Osingleoffloat is CVTSD2SS (f64 -> f32).
        Onegfs | Oabsfs | Oaddfs | Osubfs | Omulfs | Odivfs | Osingleofint | Osingleoflong
        | Osingleoffloat => Some(XType::Xsingle),

        // A comparison/flag result is 0 or 1, but _Bool is a claim about every
        // value of the destination web, proven by the must-analysis below.

        _ => None,
    }
}

fn test_flags_operand_xtype(width: usize) -> Option<XType> {
    match width {
        1 | 2 | 4 => Some(XType::Xintunsigned),
        8 => Some(XType::Xlongunsigned),
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
        // Only equality against zero can be a pointer/null test.  Relational
        // comparisons such as `cmpq $0, slot; jle` are signed 64-bit integer
        // evidence even though the immediate happens to be zero.
        Condition::Ccomplimm(Comparison::Ceq | Comparison::Cne, 0) => Some(XType::Xany64),
        Condition::Ccomplimm(_, _) => Some(XType::Xlong),
        // Unsigned 64-bit comparison
        Condition::Ccomplu(_) => Some(XType::Xlongunsigned),
        Condition::Ccompluimm(Comparison::Ceq | Comparison::Cne, 0) => Some(XType::Xany64),
        Condition::Ccompluimm(_, _) => Some(XType::Xlongunsigned),
        // Float comparison
        Condition::Ccompf(_) | Condition::Cnotcompf(_) => Some(XType::Xfloat),
        // Single comparison
        Condition::Ccompfs(_) | Condition::Cnotcompfs(_) => Some(XType::Xsingle),
        _ => None,
    }
}

/// Returns true if the operation CONSUMES f64 operands; direction-aware: Ointoffloat/Olongoffloat/Osingleoffloat have f64 args but non-f64 dsts, while int->float and single-precision ops must be excluded.
fn op_consumes_f64(op: &Operation) -> bool {
    use Operation::*;
    matches!(
        op,
        Onegf
            | Oabsf
            | Oaddf
            | Osubf
            | Omulf
            | Odivf
            | Omaxf
            | Ominf
            | Ointoffloat
            | Olongoffloat
            | Osingleoffloat
    )
}

/// Returns true if the condition compares f64 operands; single-precision compares excluded for the same width reason as op_consumes_f64.
fn is_f64_cond(cond: &Condition) -> bool {
    matches!(cond, Condition::Ccompf(_) | Condition::Cnotcompf(_))
}

/// True for a 32-bit integer comparison, positive counter-evidence that a value is an int rather than a pointer; the 64-bit forms are excluded since they apply to pointers too.
fn is_int_cmp_cond(cond: &Condition) -> bool {
    matches!(
        cond,
        Condition::Ccomp(_)
            | Condition::Ccompu(_)
            | Condition::Ccompimm(_, _)
            | Condition::Ccompuimm(_, _)
    )
}

// A compare-against-zero, excluded from hard-int evidence because a 32-bit cmp reg,0 could be a NULL check on a truncated value.
fn is_null_cmp_cond(cond: &Condition) -> bool {
    matches!(
        cond,
        Condition::Ccompimm(Comparison::Ceq, 0)
            | Condition::Ccompuimm(Comparison::Ceq, 0)
            | Condition::Ccompimm(Comparison::Cne, 0)
            | Condition::Ccompuimm(Comparison::Cne, 0)
    )
}

// Any pointer-flavored XType, used to single out candidates that must not forward across a register-reuse move into a hard-int destination.
fn is_pointer_xtype(xt: &XType) -> bool {
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

// Operations whose result is always 0 or 1.
fn bool_producing_operation(op: &Operation) -> bool {
    crate::x86::types::is_boolean_operation(op)
        || matches!(
            op,
            Operation::Ointconst(0 | 1)
                | Operation::Olongconst(0 | 1)
                | Operation::Oandimm(1)
                | Operation::Oandlimm(1)
        )
}

// Unary operations that map {0, 1} onto {0, 1}.
fn bool_transfer_operation(op: &Operation) -> bool {
    matches!(
        op,
        Operation::Omove
            | Operation::Oxorimm(1)
            | Operation::Oxorlimm(1)
            | Operation::Ocast8signed
            | Operation::Ocast8unsigned
            | Operation::Ocast16signed
            | Operation::Ocast16unsigned
            | Operation::Ocast32signed
            | Operation::Ocast32unsigned
    )
}

// An RTL definition whose value is 0 or 1 whenever its input is.
fn rtl_bool_definition(inst: &RTLInst) -> bool {
    matches!(inst, RTLInst::Iop(op, args, _)
        if bool_producing_operation(op) || (bool_transfer_operation(op) && args.len() == 1))
}

// Every register an RTL instruction writes, including each half of a split
// builtin result.
fn rtl_defined_registers(inst: &RTLInst) -> Vec<RTLReg> {
    fn collect(arg: &BuiltinArg<RTLReg>, out: &mut Vec<RTLReg>) {
        match arg {
            BuiltinArg::BA(reg) => out.push(*reg),
            BuiltinArg::BASplitLong(a, b) | BuiltinArg::BAAddPtr(a, b) => {
                collect(a, out);
                collect(b, out);
            }
            _ => {}
        }
    }
    match inst {
        RTLInst::Iop(_, _, dst) | RTLInst::Iload(_, _, _, dst) => vec![*dst],
        RTLInst::Icall(_, _, _, Some(dst), _) => vec![*dst],
        RTLInst::Ibuiltin(_, _, result) => {
            let mut out = Vec::new();
            collect(result, &mut out);
            out
        }
        _ => Vec::new(),
    }
}

fn rtl_reads_register(inst: &RTLInst, reg: RTLReg) -> bool {
    crate::decompile::passes::rtl_optimize_pass::inst_def_use(inst).1.contains(&reg)
}

// A pointer XType that names its pointee. Generic Xptr (void*/unknown) names
// none; recovered record identities are assigned after this pass, while a C
// library record (FILE, DIR) is named exactly by its library contract.
fn is_precise_pointer_xtype(xt: &XType) -> bool {
    match xt {
        XType::Xcharptr
        | XType::Xcharptrptr
        | XType::Xintptr
        | XType::Xfloatptr
        | XType::Xsingleptr
        | XType::Xfuncptr => true,
        XType::XstructPtr(id) => crate::x86::types::libc_record(*id).is_some(),
        _ => false,
    }
}

// A bare floating XType, i.e. a value the machine must keep in a float
// register. The pointer-to-float types are NOT floating: those values live in
// general-purpose registers like any other pointer.
fn is_float_xtype(xt: &XType) -> bool {
    matches!(xt, XType::Xfloat | XType::Xsingle)
}

ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct TypePassProgram;

    // Input relations (swapped from DecompileDB)

    relation emit_var_type_candidate(RTLReg, XType);
    relation alias_edge(RTLReg, RTLReg);
    relation stack_var(Address, Address, i64, RTLReg);
    relation mach_imm_stack_init(Address, i64, i64, Typ);
    relation decoded_stack_read_bytes(Address, Symbol, i64, usize);
    relation decoded_stack_write_bytes(Address, Symbol, i64, usize);
    relation ltl_inst(Node, LTLInst);
    relation rtl_inst(Node, RTLInst);
    relation reg_rtl(Node, Mreg, RTLReg);
    relation web_class_gpr(RTLReg);
    relation web_class_fp(RTLReg);

    relation func_param_position_type(Address, usize, XType);
    relation emit_function(Address, Symbol, Node);
    relation main_function(Address);
    relation abi_int_arg_position(Mreg, usize);
    relation emit_function_return_type_xtype_candidate(Address, XType);
    relation emit_function_return(Address, RTLReg);
    relation func_returns_float(Address);
    relation call_target_func(Node, Address);

    relation string_data(String, String, usize);
    relation ident_to_symbol(Ident, Symbol);

    relation known_func_param_is_ptr(Symbol, usize);
    relation known_func_returns_ptr(Symbol);
    relation known_func_returns_long(Symbol);
    relation known_extern_signature(Symbol, usize, XType, Arc<Vec<XType>>);

    relation call_site(Node, Symbol);
    relation call_arg(Node, usize, RTLReg);
    // Machine reaching definitions (def, register, use).
    relation reg_def_used(Address, Mreg, Address);
    relation reg_use(Address, Mreg);
    relation renderable_stack_addr_result(Node, i64, RTLReg);
    // (symbol, format parameter index, scanf family) from the ABI knowledge.
    relation known_format_function(Symbol, usize, bool);
    relation call_return_reg(Node, RTLReg);
    relation call_arg_mapping(Node, usize, RTLReg);
    relation abi_shared_arg_slots(bool);

    // `main` has a platform-defined interface even before the later signature
    // reconciliation pass commits prototypes.  Seed argv at the entry ABI
    // register and carry that exact value fact across alias edges and retained
    // verbatim moves.  This
    // lets an early scaled `argv[i]` load recover `char *` without guessing
    // from the address scale or waiting until interface selection, by which
    // point the load's statement/type candidates have already been built.
    #[local] relation main_argv_value(RTLReg);
    main_argv_value(reg) <--
        main_function(func),
        func_param_position_type(func, ?1usize, _),
        abi_int_arg_position(mreg, ?1usize),
        reg_rtl(func, mreg, reg);
    main_argv_value(dst) <-- main_argv_value(src), alias_edge(src, dst);
    main_argv_value(src) <-- main_argv_value(dst), alias_edge(src, dst);
    main_argv_value(*dst) <--
        rtl_inst(_, ?RTLInst::Iop(Operation::Omove, args, dst)),
        if args.len() == 1,
        main_argv_value(args[0]);

    emit_var_type_candidate(reg, XType::Xcharptrptr) <-- main_argv_value(reg);
    must_be_ptr(reg) <-- main_argv_value(reg);

    // The RTL call itself is the closest, already-reconciled source of call
    // ABI types. Symbol-resolution joins can miss PLT aliases even when RTL
    // already carries an exact Signature. Keep this value-local: an argument
    // type applies to this fresh RTL value, not to the physical register at
    // every call site.
    #[local] relation embedded_call_arg_type(RTLReg, XType);
    #[local] relation embedded_call_result_type(RTLReg, XType);

    embedded_call_arg_type(*arg, xtype) <--
        rtl_inst(_, ?RTLInst::Icall(Some(sig), _, args, _, _)),
        for (pos, arg) in args.iter().enumerate(),
        if pos < sig.sig_args.len(),
        let xtype = sig.sig_args[pos];

    embedded_call_arg_type(*arg, xtype) <--
        rtl_inst(_, ?RTLInst::Itailcall(Some(sig), _, args)),
        for (pos, arg) in args.iter().enumerate(),
        if pos < sig.sig_args.len(),
        let xtype = sig.sig_args[pos];

    embedded_call_result_type(*reg, sig.sig_res) <--
        rtl_inst(_, ?RTLInst::Icall(Some(sig), _, _, Some(reg), _));

    // Derive call_site from call_target_func + emit_function (internal calls)
    call_site(node, *name) <--
        call_target_func(node, target),
        emit_function(target, name, _);

    // Derive call_arg from call_arg_mapping
    call_arg(node, pos, reg) <--
        call_arg_mapping(node, pos, reg);

    // Format-directed variadic types (C11 7.21.6.1/7.21.6.2). A conversion
    // specification names the type the callee reads for each variadic
    // argument, so for a constant format it is prototype evidence about the
    // caller's value. Library calls are by NAME in RTL (call_site only covers
    // by-address targets), and a name the binary defines itself is not the
    // library function.
    #[local] relation extern_call_name(Node, Symbol);
    extern_call_name(node, *name) <--
        rtl_inst(node, ?RTLInst::Icall(_, Either::Right(Either::Right(name)), _, _, _)),
        !emit_function(_, name, _);
    extern_call_name(node, *name) <--
        rtl_inst(node, ?RTLInst::Itailcall(_, Either::Right(Either::Right(name)), _)),
        !emit_function(_, name, _);

    #[local] relation string_value(RTLReg, String);
    string_value(*dst, content.clone()) <--
        rtl_inst(_, ?RTLInst::Iop(Operation::Oindirectsymbol(sym_id), _, dst)),
        ident_to_symbol(sym_id, label),
        string_data(label.to_string(), content, _);

    #[local] relation format_arg_type(Node, usize, XType);
    format_arg_type(*node, *format_index + 1 + offset, xtype) <--
        extern_call_name(node, name),
        known_format_function(name, format_index, scanf),
        call_arg(node, format_index, format_reg),
        string_value(format_reg, content),
        for (offset, xtype) in crate::decompile::analysis::format_string::format_argument_types(content, *scanf);

    emit_var_type_candidate(*arg_reg, *xtype) <--
        format_arg_type(node, position, xtype),
        call_arg(node, position, arg_reg);

    // Interprocedural value binding (C11 6.5.2.2): a call assigns each
    // argument to the callee's parameter and its returned value to the call
    // result, so a PRECISE pointee named on either side names the other.
    // Generic Xptr names no pointee and does not travel; a hard 32-bit
    // integer destination is never retyped as a pointer.
    #[local] relation callee_param_reg(Address, usize, RTLReg);
    callee_param_reg(*func, *pos, *reg) <--
        func_param_position_type(func, pos, _),
        abi_int_arg_position(mreg, pos),
        reg_rtl(func, mreg, reg);

    #[local] relation call_value_binding(RTLReg, RTLReg);
    call_value_binding(*arg, *param) <--
        call_target_func(node, callee),
        call_arg(node, pos, arg),
        callee_param_reg(callee, pos, param);
    call_value_binding(*returned, *result) <--
        call_target_func(node, callee),
        call_return_reg(node, result),
        emit_function_return(callee, returned);

    emit_var_type_candidate(*to, *xtype) <--
        call_value_binding(from, to),
        emit_var_type_candidate(from, xtype),
        if is_precise_pointer_xtype(xtype),
        !hard_int32(*to);
    emit_var_type_candidate(*from, *xtype) <--
        call_value_binding(from, to),
        emit_var_type_candidate(to, xtype),
        if is_precise_pointer_xtype(xtype),
        !hard_int32(*from);
    is_ptr(*arg_reg) <--
        format_arg_type(node, position, xtype),
        if is_pointer_xtype(xtype),
        call_arg(node, position, arg_reg);


    // 1. Direct type emission from instructions; each instruction encodes width and signedness, emitting concrete types directly

    // From operations: op encodes the full output type
    emit_var_type_candidate(rtl_reg, xtype) <--
        ltl_inst(node, ?LTLInst::Lop(op, _, dst_mreg)),
        if let Some(xtype) = op_output_xtype(op),
        reg_rtl(node, *dst_mreg, rtl_reg);

    // Expansion instructions have no LTL row.  Their final RTL operation is
    // nevertheless the same exact width/type authority as a physical Lop.
    emit_var_type_candidate(*dst, xtype) <--
        rtl_inst(_, ?RTLInst::Iop(op, _, dst)),
        if let Some(xtype) = op_output_xtype(op);

    // From load chunks, suppressed when the value demonstrably holds a float: an xmm spill/reload uses a generic-width chunk, so tagging it Xint pollutes the float candidate with a truncating sibling.
    emit_var_type_candidate(rtl_reg, chunk_xtype(chunk)) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, _, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg),
        !value_float_type(rtl_reg, _);

    // Synthetic/fused loads are born only in RTL.  Without this rule their
    // destination has no width candidate and the selector's scalar fallback
    // can truncate an exact 64-bit value to int.
    emit_var_type_candidate(*dst, chunk_xtype(chunk)) <--
        rtl_inst(_, ?RTLInst::Iload(chunk, _, _, dst)),
        !value_float_type(*dst, _);

    // From store chunks, width-preserving only (a sub-word store narrows the cell, not the source); integer chunks are suppressed when the stored value demonstrably holds a float.
    emit_var_type_candidate(rtl_reg, chunk_xtype(chunk)) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, _, _, src_mreg)),
        if matches!(chunk, MemoryChunk::MFloat32 | MemoryChunk::MFloat64),
        reg_rtl(node, *src_mreg, rtl_reg);
    emit_var_type_candidate(rtl_reg, chunk_xtype(chunk)) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, _, _, src_mreg)),
        if matches!(chunk, MemoryChunk::MInt32 | MemoryChunk::MAny32 | MemoryChunk::MInt64 | MemoryChunk::MAny64),
        reg_rtl(node, *src_mreg, rtl_reg),
        !value_float_type(rtl_reg, _);
    emit_var_type_candidate(*src, chunk_xtype(chunk)) <--
        rtl_inst(_, ?RTLInst::Istore(chunk, _, _, src)),
        if matches!(chunk, MemoryChunk::MFloat32 | MemoryChunk::MFloat64);
    emit_var_type_candidate(*src, chunk_xtype(chunk)) <--
        rtl_inst(_, ?RTLInst::Istore(chunk, _, _, src)),
        if matches!(chunk, MemoryChunk::MInt32 | MemoryChunk::MAny32 | MemoryChunk::MInt64 | MemoryChunk::MAny64),
        !value_float_type(*src, _);

    // Attach each stack-access chunk to the canonical produced by structural
    // stack reaching-definitions. A frame offset is only a storage coordinate:
    // compilers may reuse it for unrelated lifetimes, and stack adjustment can
    // make one lifetime appear at more than one offset. stack_var carries the
    // already-canonicalized def-use web at each access, so it is the identity
    // type evidence must follow.
    #[local] relation stack_web_chunk(RTLReg, MemoryChunk);

    // Separate physical accesses from promoted value views at their producer.
    // The bool is the operand role (false = read, true = write). Joining by
    // access site and role associates the decoded width with the LTL event;
    // stack_var already supplies its structural web and normalized coordinate.
    // No raw BP/SP displacement is compared to a rebased stack coordinate.
    #[local] relation stack_value_view(Node, i64, bool, MemoryChunk);
    #[local] relation stack_memory_view(Node, i64, bool, MemoryChunk);
    #[local] relation decoded_stack_access(Node, bool, Symbol, i64, usize);
    #[local] relation conflicting_stack_access(Node, bool);
    #[local] relation stack_storage_chunk(Node, i64, bool, MemoryChunk);

    decoded_stack_access(*node, false, *base, *ofs, *width) <--
        decoded_stack_read_bytes(node, base, ofs, width);
    decoded_stack_access(*node, true, *base, *ofs, *width) <--
        decoded_stack_write_bytes(node, base, ofs, width);
    conflicting_stack_access(*node, *write) <--
        decoded_stack_access(node, write, base, ofs, width),
        decoded_stack_access(node, write, other_base, other_ofs, other_width),
        if (base, ofs, width) != (other_base, other_ofs, other_width);

    stack_memory_view(*node, *ofs, false, *chunk) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, Addressing::Ainstack(ofs), _, _));
    stack_memory_view(*node, *ofs, true, *chunk) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, Addressing::Ainstack(ofs), _, _));
    stack_value_view(node, ofs, write, chunk) <--
        stack_memory_view(node, ofs, write, chunk);
    stack_value_view(*node, *ofs, false, chunk) <--
        ltl_inst(node, ?LTLInst::Lgetstack(_, ofs, typ, _)),
        let chunk = crate::decompile::passes::rtl_pass::typ_to_chunk(*typ);
    stack_value_view(*node, *ofs, true, chunk) <--
        ltl_inst(node, ?LTLInst::Lsetstack(_, _, ofs, typ)),
        let chunk = crate::decompile::passes::rtl_pass::typ_to_chunk(*typ);
    stack_value_view(*node, *ofs, true, chunk) <--
        mach_imm_stack_init(node, ofs, _, typ),
        let chunk = crate::decompile::passes::rtl_pass::typ_to_chunk(*typ);

    // Decoder evidence wins over every value-level alternative of the same
    // event, including a simultaneous Lstore(byte) and Lsetstack(Tint).
    stack_storage_chunk(*node, *ofs, *write, storage_chunk_at_width(*view, *width)) <--
        stack_value_view(node, ofs, write, view),
        decoded_stack_access(node, write, _, _, width),
        !conflicting_stack_access(node, write);
    // Synthetic memory operations can lack a decoded event. Their explicit
    // MemoryChunk is an access width; a promoted get/set Typ is not.
    stack_storage_chunk(node, ofs, write, chunk) <--
        stack_memory_view(node, ofs, write, chunk),
        !decoded_stack_access(node, write, _, _, _);
    stack_storage_chunk(*node, *ofs, *write, MemoryChunk::Unknown) <--
        stack_value_view(node, ofs, write, _),
        conflicting_stack_access(node, write);
    stack_storage_chunk(*node, *ofs, *write, MemoryChunk::Unknown) <--
        stack_value_view(node, ofs, write, _),
        !decoded_stack_access(node, write, _, _, _),
        !stack_memory_view(node, ofs, write, _);

    // Only physical storage evidence authorizes a concrete declaration in
    // selection. An unknown event poisons a would-be narrow scalar proposal,
    // rather than silently disappearing when other events have known widths.
    relation type_recovery_storage_chunk(RTLReg, MemoryChunk);
    // Point- and role-preserving handoff for selection's typed evidence graph.
    // Consumers needing a value type must not reinterpret these as value defs.
    relation type_storage_access(Address, Node, RTLReg, i64, bool, MemoryChunk);
    type_storage_access(func, node, reg, ofs, write, chunk) <--
        stack_storage_chunk(node, ofs, write, chunk),
        stack_var(func, node, ofs, reg);
    type_recovery_storage_chunk(reg, chunk) <--
        type_storage_access(_, _, reg, _, _, chunk);

    stack_web_chunk(reg, chunk) <--
        type_recovery_storage_chunk(reg, chunk),
        if *chunk != MemoryChunk::Unknown;
    // Keep legacy value-type hypotheses when an event has no precise storage
    // interpretation. They remain candidates, never physical-width evidence.
    stack_web_chunk(reg, view) <--
        stack_value_view(node, ofs, write, view),
        stack_storage_chunk(node, ofs, write, ?MemoryChunk::Unknown),
        stack_var(_, node, ofs, reg);

    // Suppress a narrow candidate only when a wider access belongs to the same
    // value web. A wider access in another lifetime at the same coordinate is
    // irrelevant to this value.
    #[local] relation stack_web_has_wider_chunk(RTLReg, MemoryChunk);
    stack_web_has_wider_chunk(rtl_reg, *chunk) <--
        stack_web_chunk(rtl_reg, chunk),
        stack_web_chunk(rtl_reg, wider),
        if crate::decompile::passes::rtl_pass::chunk_size_bits(wider)
            > crate::decompile::passes::rtl_pass::chunk_size_bits(chunk);

    emit_var_type_candidate(rtl_reg, chunk_xtype(chunk)) <--
        stack_web_chunk(rtl_reg, chunk),
        !stack_web_has_wider_chunk(rtl_reg, chunk),
        !value_float_type(rtl_reg, _);

    // From comparison operands: condition encodes operand type
    emit_var_type_candidate(rtl_reg, xtype) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ocmp(cond), args, _)),
        if let Some(xtype) = cond_operand_xtype(cond),
        for mreg in args.iter(),
        reg_rtl(node, *mreg, rtl_reg);
    emit_var_type_candidate(*arg, xtype.clone()) <--
        rtl_inst(_, ?RTLInst::Iop(Operation::Ocmp(cond), args, _)),
        if let Some(xtype) = cond_operand_xtype(cond),
        for arg in args.iter();
    emit_var_type_candidate(*arg, xtype.clone()) <--
        rtl_inst(_, ?RTLInst::Icond(cond, args, _, _)),
        if let Some(xtype) = cond_operand_xtype(cond),
        for arg in args.iter();

    // Otestflags truncates both operands to the decoded TEST width before its
    // unsigned bit operations.  Make that width explicit in C typing so a
    // mask carried in a canonical 64-bit register cannot turn the expression
    // into pointer arithmetic or a signed right shift.
    emit_var_type_candidate(*arg, xtype.clone()) <--
        rtl_inst(_, ?RTLInst::Iop(Operation::Otestflags(_, width, _), args, _)),
        if let Some(xtype) = test_flags_operand_xtype(*width),
        for arg in args.iter();

    // Apply embedded exact types without requiring a second symbol lookup.
    // Unknown-width placeholders remain non-constraints, matching the older
    // symbol-derived rules below.
    emit_var_type_candidate(reg, *xtype) <--
        embedded_call_arg_type(reg, xtype),
        if !matches!(xtype, XType::Xvoid | XType::Xany32 | XType::Xany64);

    emit_var_type_candidate(reg, *xtype) <--
        embedded_call_result_type(reg, xtype),
        if !matches!(xtype, XType::Xvoid | XType::Xany32 | XType::Xany64);

    // RC-2 float/register-class brake: a value web the machine only ever keeps
    // in general-purpose registers is an integer or a pointer, so no float
    // candidate may be born on it or forwarded onto it. This is a hard
    // architectural fact, unlike the width-based evidence the rules below
    // infer, and it must apply at birth: a float candidate that reaches the C
    // lifting wins its node outright, because select_type_from_candidates
    // prefers float over int whenever no pointer candidate is present, and the
    // single statement candidate it bakes leaves the selector nothing to
    // choose from. A web with BOTH classes is two merged values, not one float
    // value; it is deliberately left alone here and reported by the adequacy
    // audit instead.
    #[local] relation web_gpr_only(RTLReg);
    web_gpr_only(reg) <-- web_class_gpr(reg), !web_class_fp(reg);

    // 2. MOVSD upgrade (TR-2): MAny64 -> Xfloat only when the value demonstrably flows into an f64-consuming position or is produced by an f64-producing op; direction-blind and flow-blind old rules wrongly floated cvttsd2si dsts and missed values reaching float ops only through copies.

    #[local] relation f64_copy_edge(RTLReg, RTLReg);
    f64_copy_edge(args[0], *dst) <--
        rtl_inst(_, ?RTLInst::Iop(Operation::Omove, args, dst)),
        if args.len() == 1;

    // Propagate candidates across an Iop(Omove): a forwarded spill/reload is not a stack_var and would otherwise get no candidate at all, defaulting to int and truncating a 64-bit pointer.
    emit_var_type_candidate(*dst, xt.clone()) <--
        rtl_inst(_, ?RTLInst::Iop(Operation::Omove, args, dst)),
        if args.len() == 1,
        let src = args[0],
        emit_var_type_candidate(src, xt),
        if !is_pointer_xtype(xt),
        if !is_float_xtype(xt),
        // _Bool is a VALUE-domain claim proven per web below; a copy's
        // destination may have other definitions outside {0, 1}.
        if *xt != XType::Xbool;

    // _Bool value webs (C11 6.3.1.2): declaring a byte web _Bool preserves
    // every value exactly when EVERY value stored into it is 0 or 1. The
    // claim is per DEFINITION, via machine reaching definitions: a reused
    // register (clang's `xor al,0xff; and al,1` for `!b`) may hold a
    // non-boolean intermediate that never reaches the store. A value is
    // refuted when its defining operation is not a 0/1 producer or transfer,
    // when a transfer's reaching input is refuted or unknown, or when it is
    // read from a refuted web. Refutation is the least fixpoint; its
    // complement over byte webs is the claim, so `b = !b` cycles stay _Bool.
    #[local] relation ltl_bool_producer(Node, Mreg);
    ltl_bool_producer(*node, *dst) <--
        ltl_inst(node, ?LTLInst::Lop(op, _, dst)),
        if bool_producing_operation(op);
    #[local] relation ltl_bool_transfer(Node, Mreg, Mreg);
    ltl_bool_transfer(*node, *dst, args[0]) <--
        ltl_inst(node, ?LTLInst::Lop(op, args, dst)),
        if bool_transfer_operation(op),
        if args.len() == 1;
    #[local] relation ltl_stack_read(Node, Mreg, RTLReg);
    ltl_stack_read(*node, *dst, *web) <--
        ltl_inst(node, ?LTLInst::Lgetstack(_, ofs, _, dst)),
        stack_var(_, node, ofs, web);
    ltl_stack_read(*node, *dst, *web) <--
        ltl_inst(node, ?LTLInst::Lload(_, Addressing::Ainstack(ofs), _, dst)),
        stack_var(_, node, ofs, web);
    #[local] relation ltl_stack_write(Node, Mreg, RTLReg);
    ltl_stack_write(*node, *src, *web) <--
        ltl_inst(node, ?LTLInst::Lsetstack(src, _, ofs, _)),
        stack_var(_, node, ofs, web);
    ltl_stack_write(*node, *src, *web) <--
        ltl_inst(node, ?LTLInst::Lstore(_, Addressing::Ainstack(ofs), _, src)),
        stack_var(_, node, ofs, web);
    #[local] relation use_has_reaching_def(Node, Mreg);
    use_has_reaching_def(*used, *mreg) <-- reg_def_used(_, mreg, used);

    #[local] relation def_may_exceed_bool(Node, Mreg);
    #[local] relation web_may_exceed_bool(RTLReg);
    def_may_exceed_bool(*def, *mreg) <--
        reg_def_used(def, mreg, _),
        !ltl_bool_producer(*def, *mreg),
        !ltl_bool_transfer(*def, *mreg, _),
        !ltl_stack_read(*def, *mreg, _);
    def_may_exceed_bool(*node, *dst) <--
        ltl_bool_transfer(node, dst, src),
        reg_def_used(def, src, node),
        def_may_exceed_bool(def, src);
    def_may_exceed_bool(*node, *dst) <--
        ltl_bool_transfer(node, dst, src),
        !use_has_reaching_def(*node, *src);
    def_may_exceed_bool(*node, *dst) <--
        ltl_stack_read(node, dst, web),
        web_may_exceed_bool(web);
    web_may_exceed_bool(*web) <--
        ltl_stack_write(node, src, web),
        reg_def_used(def, src, node),
        def_may_exceed_bool(def, src);
    web_may_exceed_bool(*web) <--
        ltl_stack_write(node, src, web),
        !use_has_reaching_def(*node, *src);
    web_may_exceed_bool(*web) <--
        mach_imm_stack_init(node, ofs, value, _),
        if *value != 0 && *value != 1,
        stack_var(_, node, ofs, web);
    // A slot whose address is materialized can be written through that
    // address -- passed, stored or returned -- which no stack write above
    // observes.
    web_may_exceed_bool(*web) <--
        renderable_stack_addr_result(node, ofs, _),
        stack_var(func, node, ofs, _),
        stack_var(func, _, ofs, web);

    // Positive evidence: a computed boolean store, or both constants. A byte
    // only ever initialised to 0 is not thereby a flag.
    #[local] relation web_bool_evidence(RTLReg);
    #[local] relation ltl_constant_def(Node, Mreg);
    ltl_constant_def(*node, *dst) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ointconst(_) | Operation::Olongconst(_), _, dst));
    web_bool_evidence(*web) <--
        ltl_stack_write(node, src, web),
        reg_def_used(def, src, node),
        ltl_bool_producer(def, src),
        !ltl_constant_def(*def, *src);
    web_bool_evidence(*web) <--
        ltl_stack_write(node, src, web),
        reg_def_used(def, src, node),
        ltl_bool_transfer(def, src, _);
    #[local] relation web_bool_constant(RTLReg, i64);
    web_bool_constant(*web, *value) <--
        mach_imm_stack_init(node, ofs, value, _),
        if *value == 0 || *value == 1,
        stack_var(_, node, ofs, web);
    web_bool_evidence(*web) <--
        web_bool_constant(web, 0),
        web_bool_constant(web, 1);

    // Only byte storage can be a C _Bool object; an int-sized flag is an int.
    #[local] relation web_wider_than_byte(RTLReg);
    web_wider_than_byte(*reg) <--
        stack_web_chunk(reg, chunk),
        if !matches!(chunk, MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned | MemoryChunk::MBool);
    emit_var_type_candidate(*reg, XType::Xbool) <--
        stack_web_chunk(reg, chunk),
        if matches!(chunk, MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned | MemoryChunk::MBool),
        !web_wider_than_byte(*reg),
        web_bool_evidence(reg),
        !web_may_exceed_bool(*reg);

    // A register web is one C variable for ALL of its values, so a comparison
    // makes it _Bool only when no value the web can hold exceeds {0, 1}: gcc's
    // `setle al; movzx eax, al; add eax, 1` is one web holding 1 or 2. It is
    // refuted by an explicit definition that is not a 0/1 producer or
    // transfer, by a transfer of a refuted web, and by a read that a refuted
    // definition reaches -- parameters enter as definitions at the function
    // start -- or that no definition reaches. Stack webs are also written by
    // stores, so their claim is the stack analysis above.
    #[local] relation stack_web(RTLReg);
    stack_web(*web) <-- stack_var(_, _, _, web);
    #[local] relation ltl_read_web(Node, Mreg, RTLReg);
    ltl_read_web(*node, *mreg, *web) <--
        reg_use(node, mreg),
        reg_rtl(node, mreg, web),
        rtl_inst(node, inst),
        if rtl_reads_register(inst, *web);
    #[local] relation reg_web_may_exceed_bool(RTLReg);
    reg_web_may_exceed_bool(web) <--
        rtl_inst(_, inst),
        if !rtl_bool_definition(inst),
        for web in rtl_defined_registers(inst);
    reg_web_may_exceed_bool(*dst) <--
        rtl_inst(_, ?RTLInst::Iop(op, args, dst)),
        if bool_transfer_operation(op),
        if args.len() == 1,
        reg_web_may_exceed_bool(args[0]);
    reg_web_may_exceed_bool(*web) <--
        ltl_read_web(node, mreg, web),
        reg_def_used(def, mreg, node),
        def_may_exceed_bool(def, mreg);
    reg_web_may_exceed_bool(*web) <--
        ltl_read_web(node, mreg, web),
        !use_has_reaching_def(*node, *mreg);
    emit_var_type_candidate(*dst, XType::Xbool) <--
        rtl_inst(_, ?RTLInst::Iop(op, _, dst)),
        if is_boolean_operation(op),
        !stack_web(*dst),
        !reg_web_may_exceed_bool(*dst);

    // A move joins two DISTINCT value webs, so a float candidate crossing it
    // must still answer to the destination's own register file. Forwarding it
    // onto a web the machine only ever keeps in general-purpose registers is
    // how a mis-resolved float reaches a plainly integral value such as an
    // `argc` copy, and the C lifting then bakes the float spelling into the
    // only statement candidate it builds for that node.
    emit_var_type_candidate(*dst, xt.clone()) <--
        rtl_inst(_, ?RTLInst::Iop(Operation::Omove, args, dst)),
        if args.len() == 1,
        let src = args[0],
        emit_var_type_candidate(src, xt),
        if is_float_xtype(xt),
        !web_gpr_only(*dst);

    // Forward a POINTER candidate across a move only when the destination is not hard 32-bit-int, or the integer half of a reused register gets mistyped void* and its arithmetic corrupted.
    emit_var_type_candidate(*dst, xt.clone()) <--
        rtl_inst(_, ?RTLInst::Iop(Operation::Omove, args, dst)),
        if args.len() == 1,
        let src = args[0],
        emit_var_type_candidate(src, xt),
        if is_pointer_xtype(xt),
        !hard_int32(*dst);

    // Operand positions that consume an f64 value.
    #[local] relation f64_use_reg(RTLReg);
    f64_use_reg(*arg) <--
        rtl_inst(_, ?RTLInst::Iop(op, args, _)),
        if op_consumes_f64(op),
        for arg in args.iter();
    f64_use_reg(*arg) <--
        rtl_inst(_, ?RTLInst::Iop(Operation::Ocmp(cond), args, _)),
        if is_f64_cond(cond),
        for arg in args.iter();
    f64_use_reg(*arg) <--
        rtl_inst(_, ?RTLInst::Icond(cond, args, _, _)),
        if is_f64_cond(cond),
        for arg in args.iter();

    #[local] relation flows_to_f64_use(RTLReg);
    flows_to_f64_use(reg) <-- f64_use_reg(reg);
    flows_to_f64_use(src) <-- f64_copy_edge(src, dst), flows_to_f64_use(dst);

    #[local] relation holds_f64_value(RTLReg);
    holds_f64_value(dst) <--
        rtl_inst(_, ?RTLInst::Iop(op, _, dst)),
        if is_float_operation(op);
    holds_f64_value(dst) <-- f64_copy_edge(src, dst), holds_f64_value(src);

    // RC-1 float/pointer brake: suppress a bare-float candidate on a register with pointer evidence, since opening the Z3 float axis renders the pointer as double; genuine floats are never is_ptr.
    emit_var_type_candidate(reg, XType::Xfloat) <--
        emit_var_type_candidate(reg, ?XType::Xany64),
        flows_to_f64_use(reg), !is_ptr(reg), !web_gpr_only(reg);
    emit_var_type_candidate(reg, XType::Xfloat) <--
        emit_var_type_candidate(reg, ?XType::Xany64),
        holds_f64_value(reg), !is_ptr(reg), !web_gpr_only(reg);

    // 2b. Float VALUE web: value_float_type carries the precise Xsingle/Xfloat a value reg holds, propagated over verbatim Omove copies only, never across arithmetic that could reinterpret bits.
    #[local] relation value_float_type(RTLReg, XType);
    value_float_type(dst, XType::Xfloat) <--
        rtl_inst(_, ?RTLInst::Iop(op, _, dst)),
        if is_float_operation(op);
    value_float_type(dst, XType::Xsingle) <--
        rtl_inst(_, ?RTLInst::Iop(op, _, dst)),
        if crate::x86::types::is_single_operation(op);
    value_float_type(rtl_reg, XType::Xfloat) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, _, _, dst_mreg)),
        if matches!(chunk, MemoryChunk::MFloat64),
        reg_rtl(node, *dst_mreg, rtl_reg);
    value_float_type(rtl_reg, XType::Xsingle) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, _, _, dst_mreg)),
        if matches!(chunk, MemoryChunk::MFloat32),
        reg_rtl(node, *dst_mreg, rtl_reg);
    // Synthetic RTL loads carry no ltl_inst, so derive the same float evidence directly from rtl_inst, whose dst is the post-lowering value reg the backend consumes.
    value_float_type(*dst, XType::Xfloat) <--
        rtl_inst(_, ?RTLInst::Iload(chunk, _, _, dst)),
        if matches!(chunk, MemoryChunk::MFloat64);
    value_float_type(*dst, XType::Xsingle) <--
        rtl_inst(_, ?RTLInst::Iload(chunk, _, _, dst)),
        if matches!(chunk, MemoryChunk::MFloat32);
    // A floating conditional also supplies definitive value-class evidence,
    // beyond the generic candidate emitted for every Icond above.
    value_float_type(*arg, XType::Xsingle) <--
        rtl_inst(_, ?RTLInst::Icond(cond, args, _, _)),
        if matches!(cond, Condition::Ccompfs(_) | Condition::Cnotcompfs(_)),
        for arg in args.iter();
    value_float_type(*arg, XType::Xfloat) <--
        rtl_inst(_, ?RTLInst::Icond(cond, args, _, _)),
        if matches!(cond, Condition::Ccompf(_) | Condition::Cnotcompf(_)),
        for arg in args.iter();
    // Verbatim-copy propagation in both directions: src and dst of an Omove are the same value, so floatness of either end carries to the other.
    value_float_type(dst, xt) <-- f64_copy_edge(src, dst), value_float_type(src, xt);
    value_float_type(src, xt) <-- f64_copy_edge(src, dst), value_float_type(dst, xt);

    // A stack def-use web accessed with a float chunk holds a floating value,
    // so its canonical keeps float-ness across a non-forwarded spill/reload.
    // The web key prevents a reused frame coordinate from floating unrelated
    // lifetimes. LOOSE candidate.
    value_float_type(rtl_reg, XType::Xsingle) <--
        stack_web_chunk(rtl_reg, ?MemoryChunk::MFloat32);
    value_float_type(rtl_reg, XType::Xfloat) <--
        stack_web_chunk(rtl_reg, ?MemoryChunk::MFloat64);

    // A value reg with float evidence gets the float candidate so the solver keeps only float types, except on a pointer-evidenced register, where the bare-float candidate is suppressed, or a general-purpose-only web, which architecturally holds no float.
    emit_var_type_candidate(reg, xt) <-- value_float_type(reg, xt), !is_ptr(reg), !web_gpr_only(reg);


    // 3. Pointer evidence (no is_not_ptr; pointers are a subtype of 8-byte int, no conflict)

    relation is_ptr(RTLReg);
    relation is_char_ptr(RTLReg);
    relation must_be_ptr(RTLReg);

    // A concrete pointer slot in an embedded call signature is hard ABI
    // evidence. In particular it vetoes hard_int32 pollution before pointer
    // candidates propagate through an Omove value edge.
    must_be_ptr(reg) <--
        embedded_call_arg_type(reg, xtype),
        if is_pointer_xtype(xtype);

    must_be_ptr(reg) <--
        embedded_call_result_type(reg, xtype),
        if is_pointer_xtype(xtype);

    // HARD 32-bit-int evidence on a value-web node: a 32-bit compare operand is never a pointer, so it stops is_ptr propagating in; must_be_ptr is excluded so a hard pointer constraint wins.
    relation hard_int32(RTLReg);
    hard_int32(rtl_arg) <--
        ltl_inst(addr, ?LTLInst::Lcond(cond, mregs, _, _)),
        if is_int_cmp_cond(cond),
        if !is_null_cmp_cond(cond),
        for mreg in mregs.iter(),
        reg_rtl(addr, *mreg, rtl_arg),
        !must_be_ptr(rtl_arg);

    // Positively type a hard-int register as a 32-bit int, or a register that is only ever a compare operand carries no candidate at all and falls to the Xany64 void* default.
    emit_var_type_candidate(reg, XType::Xint) <-- hard_int32(reg);

    // HARD integer evidence: the destination of a float->int conversion is definitionally an integer, so suppress its Xptr candidate; must_be_ptr is excluded so a genuine constraint still wins.
    relation hard_int_conv_dest(RTLReg);
    hard_int_conv_dest(rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(op, _, dst_mreg)),
        if matches!(op, Operation::Olongoffloat | Operation::Olongofsingle |
            Operation::Ointoffloat | Operation::Ointofsingle),
        reg_rtl(node, *dst_mreg, rtl_reg),
        !must_be_ptr(rtl_reg);

    // Pointer-producing operations
    relation op_produces_ptr(Node, RTLReg);
    relation canonical_exact_stack_addr_ptr_result(Node, RTLReg);

    is_ptr(reg) <-- op_produces_ptr(_, reg);

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
        rtl_inst(_, ?RTLInst::Icall(_, Either::Left(callee_rtl), _, _, _));

    must_be_ptr(callee_rtl) <--
        rtl_inst(_, ?RTLInst::Itailcall(_, Either::Left(callee_rtl), _));

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

    // RTL load/store base address, for synthetic/fused derefs carrying no ltl_inst; without it a pointer misses is_ptr and a spurious float candidate survives into a (double)ptr variant.
    is_ptr(base) <--
        rtl_inst(_, ?RTLInst::Iload(_, addr, args, dst)),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base = args[0],
        if base != *dst;

    is_ptr(base) <--
        rtl_inst(_, ?RTLInst::Istore(_, addr, args, src)),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base = args[0],
        if base != *src;

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

    // The int element type from a 32-bit store is suppressed when the stored value holds a float, since a mis-resolved movss chunk would type the pointer int* and truncate the store.
    ptr_element_type(base_rtl, XType::Xint) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, addr, args, src_mreg)),
        if matches!(chunk, MemoryChunk::MInt32 | MemoryChunk::MAny32),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base_mreg = args[0],
        reg_rtl(node, *src_mreg, src_rtl),
        !value_float_type(src_rtl, _),
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

    // Float element type from the STORED VALUE: when the chunk was mis-resolved to an integer width but the value is float, the pointer still points at a float, recovering float*/double* out-params.
    ptr_element_type(base_rtl, xt) <--
        ptr_store(base_rtl, src_rtl),
        value_float_type(src_rtl, xt);

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
    relation ptr_store(RTLReg, RTLReg); // ptr_store(ptr, src): *ptr = src
    relation ptr_load(RTLReg, RTLReg);  // ptr_load(ptr, dst): dst = *ptr
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

    // Dereferencing `char **` yields `char *`, including scaled argv-style
    // loads.  Keep this as a candidate: the pointer-depth fact is structural,
    // while the selector remains responsible for resolving competing uses.
    emit_var_type_candidate(*dst, XType::Xcharptr) <--
        rtl_inst(_, ?RTLInst::Iload(_, addr, args, dst)),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        let base = args[0],
        emit_var_type_candidate(base, ?XType::Xcharptrptr);

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

    // Store->load type propagation under a matching chunk guard; a bare-float candidate is not propagated onto a pointer-evidenced loaded value, but still flows to non-ptr loads.
    emit_var_type_candidate(dst, ty) <--
        emit_var_type_candidate(src, ty),
        ptr_store_chunk(p, src, chunk),
        ptr_load_chunk(p, dst, chunk),
        if !matches!(ty, XType::Xfloat | XType::Xsingle | XType::Xbool);
    emit_var_type_candidate(dst, ty) <--
        emit_var_type_candidate(src, ty),
        ptr_store_chunk(p, src, chunk),
        ptr_load_chunk(p, dst, chunk),
        if matches!(ty, XType::Xfloat | XType::Xsingle),
        !is_ptr(dst);


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

    // Internal function arg: never forward a bare-float param type across the integer-arg boundary, since call_arg carries only integer-register args and a spurious float opens the Z3 float axis.
    emit_var_type_candidate(arg_reg, *xtype) <--
        call_site(node, func_name),
        call_arg(node, arg_idx, arg_reg),
        internal_func_signature(func_name, arg_idx, xtype),
        if *xtype != XType::Xany32 && *xtype != XType::Xany64,
        if !matches!(xtype, XType::Xfloat | XType::Xsingle);

    emit_var_type_candidate(arg_reg, *xtype) <--
        abi_shared_arg_slots(true),
        call_site(node, func_name),
        call_arg(node, arg_idx, arg_reg),
        internal_func_signature(func_name, arg_idx, xtype),
        if matches!(xtype, XType::Xfloat | XType::Xsingle);

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

    // BUG1a: re-derive the float RETURN-TYPE candidate here, where value_float_type is available, since at rtl time the reloaded return reg has none and the ladder falls to Xany64/long.
    emit_function_return_type_xtype_candidate(func_start, *xt) <--
        func_returns_float(func_start),
        emit_function_return(func_start, ret_reg),
        value_float_type(ret_reg, xt),
        if matches!(xt, XType::Xfloat | XType::Xsingle);


    // 7. Pointer subtype emission from pointer evidence (base types come from section 1 instructions)

    emit_var_type_candidate(reg, XType::Xcharptr) <-- is_char_ptr(reg);
    emit_var_type_candidate(reg, XType::Xintptr) <-- has_int_ptr_type(reg);
    emit_var_type_candidate(reg, XType::Xfloatptr) <-- has_float_ptr_type(reg);
    emit_var_type_candidate(reg, XType::Xsingleptr) <-- has_single_ptr_type(reg);
    // Suppress the bare void* candidate on a register with hard 32-bit-int or float->int-conversion evidence unless it is must_be_ptr, since Xptr would outrank the int candidate.
    emit_var_type_candidate(reg, XType::Xptr) <-- is_ptr(reg), !hard_int32(reg), !hard_int_conv_dest(reg), !must_be_ptr(reg);
    emit_var_type_candidate(reg, XType::Xptr) <-- is_ptr(reg), must_be_ptr(reg);

    // Disabled: bidirectional int/ptr pollution causes every int to become ptr candidate

    // 7b. Pointer arithmetic propagation: add/sub on a known pointer produces a pointer, each gated !hard_int32 so an integer expression lowered to an Olea is not made a pointer.
    // Reverse affine evidence remains a LOOSE candidate: when an independently
    // proven pointer result is `base + constant` (or base + scaled index), the
    // first LEA operand is a pointer candidate too.  Do not promote it to
    // `is_ptr`: recovered call signatures can be imperfect, and the selector
    // must retain the integer/float alternatives.  This closes the one-way
    // gap without treating a bare LEA as pointer evidence.
    emit_var_type_candidate(src_rtl, XType::Xptr) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Olea(addr), args, dst_mreg)),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        reg_rtl(node, args[0], src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl),
        must_be_ptr(dst_rtl),
        !hard_int32(src_rtl);

    is_ptr(dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Olea(addr), args, dst_mreg)),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        reg_rtl(node, args[0], src_rtl),
        is_ptr(src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl),
        !hard_int32(dst_rtl);

    is_ptr(dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Oleal(addr), args, dst_mreg)),
        if matches!(addr, Addressing::Aindexed(_) | Addressing::Aindexed2(_) | Addressing::Aindexed2scaled(_, _)),
        if !args.is_empty(),
        reg_rtl(node, args[0], src_rtl),
        is_ptr(src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl),
        !hard_int32(dst_rtl);

    // An exact stack-address operation is a hard pointer only when RTL proved
    // from the decoded destination that its result width matches the target
    // ABI. Consume the base authority rather than the broader
    // `op_produces_ptr` closure: the latter also propagates through Omove via
    // `is_ptr` and would create a negation cycle with hard integer evidence.
    must_be_ptr(dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(op, args, dst_mreg)),
        if matches!(op, Operation::Olea(Addressing::Ainstack(_)) | Operation::Oleal(Addressing::Ainstack(_))),
        if args.is_empty(),
        reg_rtl(node, *dst_mreg, dst_rtl),
        canonical_exact_stack_addr_ptr_result(node, dst_rtl);

    // Oaddl(ptr, offset) -> result is ptr
    is_ptr(dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Oaddl, args, dst_mreg)),
        if !args.is_empty(),
        reg_rtl(node, args[0], src_rtl),
        is_ptr(src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl),
        !hard_int32(dst_rtl);

    // Osubl(ptr, offset) -> result is ptr (negative indexing)
    is_ptr(dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Osubl, args, dst_mreg)),
        if !args.is_empty(),
        reg_rtl(node, args[0], src_rtl),
        is_ptr(src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl),
        !hard_int32(dst_rtl);

    // Oaddlimm(ptr, const) -> result is ptr
    is_ptr(dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Oaddlimm(_), args, dst_mreg)),
        if !args.is_empty(),
        reg_rtl(node, args[0], src_rtl),
        is_ptr(src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl),
        !hard_int32(dst_rtl);

    // Osel(cond, typ): conditional select; if either operand is ptr, result is ptr
    is_ptr(dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Osel(_, _), args, dst_mreg)),
        if args.len() >= 2,
        reg_rtl(node, args[0], src_rtl),
        is_ptr(src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl),
        !hard_int32(dst_rtl);

    is_ptr(dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Osel(_, _), args, dst_mreg)),
        if args.len() >= 2,
        reg_rtl(node, args[1], src_rtl),
        is_ptr(src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl),
        !hard_int32(dst_rtl);

    // Omove of a pointer yields a pointer, except into a destination with hard 32-bit-int evidence, the bridge by which a reused register's pointer half contaminated its integer half.
    op_produces_ptr(node, dst_rtl) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Omove, args, dst_mreg)),
        if !args.is_empty(),
        reg_rtl(node, args[0], src_rtl),
        is_ptr(src_rtl),
        reg_rtl(node, *dst_mreg, dst_rtl),
        !hard_int32(dst_rtl);

    // 8. Function pointer detection: registers used as indirect call targets
    emit_var_type_candidate(*callee_reg, XType::Xfuncptr) <--
        rtl_inst(_, ?RTLInst::Icall(_, Either::Left(callee_reg), _, _, _));

    emit_var_type_candidate(*callee_reg, XType::Xfuncptr) <--
        rtl_inst(_, ?RTLInst::Itailcall(_, Either::Left(callee_reg), _));

    // 9. Global pointer type detection via dereference evidence, call constraints, and known sigs.
    relation global_addr_reg(Ident, RTLReg);
    relation emit_global_is_ptr(Ident);
    relation emit_global_is_char_ptr(Ident);
    // Ground-truth pointer evidence from ELF relocations: a data slot relocated to a data target is unconditionally a pointer, which the access-based signals miss for never-dereferenced tables.
    relation pointer_in_data(Address, Address);
    #[local] relation global_value_reg(Ident, RTLReg);
    // Integer counter-evidence: the loaded value participates in an integer comparison or non-pointer arithmetic, fed from the same global_value_reg so it weighs against the pointer signals.
    #[local] relation global_used_as_int(Ident);
    // Unambiguous pointer evidence: the loaded value is dereferenced as a memory base or carries a hard call/indirect-call constraint, outranking integer counter-evidence.
    #[local] relation global_ptr_evidence_strong(Ident);
    // Veto: with int counter-evidence and no strong pointer evidence, the weak pointer signals must not upgrade the global, so a contested counter stays its recovered scalar.
    #[local] relation global_ptr_vetoed(Ident);

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

    // Integer counter-evidence: loaded value is an operand of a 32-bit integer comparison (via Ocmp).
    global_used_as_int(*ident) <--
        global_value_reg(ident, loaded_rtl),
        ltl_inst(node, ?LTLInst::Lop(Operation::Ocmp(cond), args, _)),
        if is_int_cmp_cond(cond),
        for mreg in args.iter(),
        reg_rtl(node, *mreg, loaded_rtl);

    // Integer counter-evidence: loaded value is an operand of a 32-bit integer comparison (via Icond).
    global_used_as_int(*ident) <--
        global_value_reg(ident, loaded_rtl),
        rtl_inst(_, ?RTLInst::Icond(cond, args, _, _)),
        if is_int_cmp_cond(cond),
        if args.contains(loaded_rtl);

    // Integer counter-evidence: the loaded value is an operand of a 32-bit subtract whose counterpart is provably not a pointer, so this is integer subtraction, not pointer difference.
    global_used_as_int(*ident) <--
        global_value_reg(ident, loaded_rtl),
        rtl_inst(_, ?RTLInst::Iop(Operation::Osub, args, _)),
        if args.len() == 2,
        if args[0] == *loaded_rtl,
        let other = args[1],
        !is_ptr(other);

    global_used_as_int(*ident) <--
        global_value_reg(ident, loaded_rtl),
        rtl_inst(_, ?RTLInst::Iop(Operation::Osub, args, _)),
        if args.len() == 2,
        if args[1] == *loaded_rtl,
        let other = args[0],
        !is_ptr(other);

    // Strong pointer evidence: the loaded value is actually dereferenced as a memory base.
    global_ptr_evidence_strong(*ident) <--
        global_value_reg(ident, loaded_rtl),
        ptr_deref(loaded_rtl, _);

    // Strong pointer evidence: the loaded value carries a hard call/indirect-call pointer constraint.
    global_ptr_evidence_strong(*ident) <--
        global_value_reg(ident, loaded_rtl),
        must_be_ptr(loaded_rtl);

    // Veto the weak pointer signals when int counter-evidence holds and strong ptr evidence does not.
    global_ptr_vetoed(*ident) <--
        global_used_as_int(ident),
        !global_ptr_evidence_strong(ident);

    // A global is a pointer if its loaded value is dereferenced (used as memory base)
    emit_global_is_ptr(*ident) <--
        global_value_reg(ident, loaded_rtl),
        ptr_deref(loaded_rtl, _);

    // Also mark as pointer if the loaded value has must_be_ptr evidence (strong call constraint)
    emit_global_is_ptr(*ident) <--
        global_value_reg(ident, loaded_rtl),
        must_be_ptr(loaded_rtl);

    // Relocation ground truth: a data slot relocated to a STRING target is a string pointer; restricted to string targets so a relocation to internal-struct data keeps its baseline recovery.
    emit_global_is_ptr(*slot as usize) <--
        pointer_in_data(slot, target),
        string_data(label, _, _),
        if label.strip_prefix("L_").or_else(|| label.strip_prefix(".L_"))
            .and_then(|h| u64::from_str_radix(h, 16).ok()) == Some(*target);

    // A global is a pointer if passed as a call argument to a known pointer parameter; a weak signal, vetoed under dominant integer counter-evidence.
    emit_global_is_ptr(*ident) <--
        global_value_reg(ident, loaded_rtl),
        call_arg(node, arg_idx, loaded_rtl),
        call_site(node, func_name),
        known_extern_signature(func_name, _, _, params),
        if *arg_idx < params.len(),
        if matches!(params[*arg_idx], XType::Xptr | XType::Xcharptr | XType::Xcharptrptr | XType::Xintptr |
            XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr | XType::XstructPtr(_)),
        !global_ptr_vetoed(ident);

    emit_global_is_ptr(*ident) <--
        global_value_reg(ident, loaded_rtl),
        call_arg(node, arg_idx, loaded_rtl),
        call_site(node, func_name),
        internal_func_signature(func_name, arg_idx, xtype),
        if matches!(xtype, XType::Xptr | XType::Xcharptr | XType::Xcharptrptr | XType::Xintptr |
            XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr | XType::XstructPtr(_)),
        !global_ptr_vetoed(ident);

    emit_global_is_ptr(*ident) <--
        global_value_reg(ident, loaded_rtl),
        call_arg(node, arg_idx, loaded_rtl),
        call_site(node, func_name),
        known_func_param_is_ptr(func_name, arg_idx),
        !global_ptr_vetoed(ident);

    // A global is a char pointer if its loaded value is used to load/store bytes; a weak signal, vetoed under dominant integer counter-evidence.
    emit_global_is_char_ptr(*ident) <--
        global_value_reg(ident, loaded_rtl),
        is_char_ptr(loaded_rtl),
        !global_ptr_vetoed(ident);

    // A global is a char pointer if passed as a char* argument.
    emit_global_is_char_ptr(*ident) <--
        global_value_reg(ident, loaded_rtl),
        call_arg(node, arg_idx, loaded_rtl),
        call_site(node, func_name),
        known_extern_signature(func_name, _, _, params),
        if *arg_idx < params.len(),
        if params[*arg_idx] == XType::Xcharptr,
        !global_ptr_vetoed(ident);
}

pub struct TypePass;

impl IRPass for TypePass {
    fn name(&self) -> &'static str {
        "type"
    }

    fn run(&self, db: &mut DecompileDB) {
        let mut prog = TypePassProgram::default();
        prog.swap_db_fields(db);

        prog.run();

        prog.swap_db_fields(db);
    }

    declare_io_from!(TypePassProgram);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn synthetic_ids<const N: usize>() -> [u64; N] {
        std::array::from_fn(|index| index as u64 + 1)
    }

    #[test]
    fn synthetic_rtl_instructions_publish_their_exact_value_widths() {
        let [load_node, const_node, store_node] = synthetic_ids();
        let [loaded, constant, base] = [101, 102, 103];
        let mut prog = TypePassProgram::default();
        prog.rtl_inst.extend([
            (
                load_node,
                RTLInst::Iload(
                    MemoryChunk::MAny64,
                    Addressing::Aglobal(0x4000, 0),
                    Arc::new(vec![]),
                    loaded,
                ),
            ),
            (
                const_node,
                RTLInst::Iop(Operation::Olongconst(7), Arc::new(vec![]), constant),
            ),
            (
                store_node,
                RTLInst::Istore(
                    MemoryChunk::MAny64,
                    Addressing::Aindexed(0),
                    Arc::new(vec![base]),
                    loaded,
                ),
            ),
        ]);

        prog.run();

        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (loaded, XType::Xany64)));
        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (constant, XType::Xlong)));
    }

    #[test]
    fn direct_conditional_operands_keep_the_encoded_compare_width() {
        let mut prog = TypePassProgram::default();
        let signed_relational = 201;
        let unsigned_relational = 202;
        let possible_null = 203;

        prog.rtl_inst.extend([
            (
                10,
                RTLInst::Icond(
                    Condition::Ccomplimm(Comparison::Cle, 0),
                    Arc::new(vec![signed_relational]),
                    Either::Right(20),
                    Either::Right(30),
                ),
            ),
            (
                11,
                RTLInst::Icond(
                    Condition::Ccompluimm(Comparison::Cgt, 0),
                    Arc::new(vec![unsigned_relational]),
                    Either::Right(20),
                    Either::Right(30),
                ),
            ),
            (
                12,
                RTLInst::Icond(
                    Condition::Ccomplimm(Comparison::Ceq, 0),
                    Arc::new(vec![possible_null]),
                    Either::Right(20),
                    Either::Right(30),
                ),
            ),
        ]);

        prog.run();

        for expected in [
            (signed_relational, XType::Xlong),
            (unsigned_relational, XType::Xlongunsigned),
            (possible_null, XType::Xany64),
        ] {
            assert!(
                prog.emit_var_type_candidate
                    .iter()
                    .any(|row| *row == expected),
                "missing direct-condition type {expected:?}: {:?}",
                prog.emit_var_type_candidate
            );
        }
        assert!(!prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (signed_relational, XType::Xany64)));
    }

    #[test]
    fn direct_relocation_load_does_not_bypass_conflict_checked_pointer_proof() {
        let [exact_node, adjacent_node, narrow_node] = synthetic_ids();
        let [exact, adjacent, narrow] = [201, 202, 203];
        let base = 0x4000_usize;
        let slot = base as Address + 8;
        let mut prog = TypePassProgram::default();
        prog.pointer_in_data.push((slot, 0x5000));
        prog.rtl_inst.extend([
            (
                exact_node,
                RTLInst::Iload(
                    MemoryChunk::MInt64,
                    Addressing::Aglobal(base, 8),
                    Arc::new(vec![]),
                    exact,
                ),
            ),
            (
                adjacent_node,
                RTLInst::Iload(
                    MemoryChunk::MInt64,
                    Addressing::Aglobal(base, 0),
                    Arc::new(vec![]),
                    adjacent,
                ),
            ),
            (
                narrow_node,
                RTLInst::Iload(
                    MemoryChunk::MInt32,
                    Addressing::Aglobal(base, 8),
                    Arc::new(vec![]),
                    narrow,
                ),
            ),
        ]);

        prog.run();

        for value in [exact, adjacent, narrow] {
            assert!(!prog.must_be_ptr.iter().any(|row| *row == (value,)));
        }
        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (exact, XType::Xany64)));
    }

    #[test]
    fn reused_stack_offset_does_not_share_float_type_between_value_webs() {
        let mut prog = TypePassProgram::default();
        let func = 0x1000;
        let offset = 24;
        let float_store = 0x1010;
        let int_store = 0x1020;
        let float_web = 100;
        let int_web = 200;

        // The compiler reuses one frame coordinate for two non-overlapping
        // lifetimes. stack_var's canonical differs because stack def-use found
        // no path on which the first store reaches the second lifetime.
        prog.stack_var.push((func, float_store, offset, float_web));
        prog.stack_var.push((func, int_store, offset, int_web));
        prog.ltl_inst.push((
            float_store,
            LTLInst::Lsetstack(Mreg::X0, Slot::Local, offset, Typ::Tfloat),
        ));
        prog.ltl_inst.push((
            int_store,
            LTLInst::Lsetstack(Mreg::AX, Slot::Local, offset, Typ::Tint),
        ));

        prog.run();

        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (float_web, XType::Xfloat)));
        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (int_web, XType::Xint)));
        assert!(!prog.emit_var_type_candidate.iter().any(|(reg, xtype)| {
            *reg == int_web && matches!(xtype, XType::Xfloat | XType::Xsingle)
        }));
    }

    #[test]
    fn stack_float_type_follows_one_value_web_across_offset_rebasing() {
        let mut prog = TypePassProgram::default();
        let func = 0x2000;
        let store = 0x2010;
        let reload = 0x2020;
        let web = 300;

        // stack_def_used can pair accesses whose apparent coordinate changes
        // across a stack adjustment. The shared canonical, not either offset,
        // is the lifetime identity.
        prog.stack_var.push((func, store, 16, web));
        prog.stack_var.push((func, reload, 24, web));
        prog.ltl_inst.push((
            store,
            LTLInst::Lsetstack(Mreg::X0, Slot::Local, 16, Typ::Tfloat),
        ));
        prog.ltl_inst.push((
            reload,
            LTLInst::Lgetstack(Slot::Local, 24, Typ::Tany64, Mreg::X1),
        ));

        prog.run();

        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (web, XType::Xfloat)));
    }

    #[test]
    fn immediate_stack_initialization_keeps_its_point_local_width() {
        let mut prog = TypePassProgram::default();
        let func = 0x3000;
        let init = 0x3010;
        let web = 400;

        prog.stack_var.push((func, init, 32, web));
        prog.mach_imm_stack_init.push((init, 32, 0, Typ::Tany64));

        prog.run();

        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (web, XType::Xany64)));
    }

    #[test]
    fn byte_storage_is_not_widened_by_promoted_stack_get_and_set() {
        let mut prog = TypePassProgram::default();
        let (func, store, reload, web, offset) = (1, 7, 3, 101, -20);
        prog.stack_var
            .extend([(func, store, offset, web), (func, reload, offset, web)]);
        prog.decoded_stack_write_bytes
            .push((store, "RBP", offset, 1));
        prog.decoded_stack_read_bytes
            .push((reload, "RBP", offset, 1));
        prog.ltl_inst.extend([
            (
                store,
                LTLInst::Lstore(
                    MemoryChunk::MInt8Unsigned,
                    Addressing::Ainstack(offset),
                    Arc::new(vec![]),
                    Mreg::DX,
                ),
            ),
            (
                store,
                LTLInst::Lsetstack(Mreg::DX, Slot::Local, offset, Typ::Tint),
            ),
            (
                reload,
                LTLInst::Lgetstack(Slot::Local, offset, Typ::Tint, Mreg::AX),
            ),
        ]);
        prog.run();
        assert!(prog
            .type_recovery_storage_chunk
            .iter()
            .any(|row| *row == (web, MemoryChunk::MInt8Unsigned)));
        assert!(!prog
            .type_recovery_storage_chunk
            .iter()
            .any(|(reg, chunk)| *reg == web && *chunk != MemoryChunk::MInt8Unsigned));
        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (web, XType::Xint8unsigned)));
        assert!(!prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (web, XType::Xint)));
    }

    #[test]
    fn physical_storage_width_follows_the_access_across_coordinate_rebasing() {
        let mut prog = TypePassProgram::default();
        let (func, node, web) = (1, 9, 101);
        prog.stack_var.push((func, node, 24, web));
        // Raw RSP displacement and the normalized LTL coordinate differ.
        prog.decoded_stack_read_bytes.push((node, "RSP", 88, 2));
        prog.ltl_inst.push((
            node,
            LTLInst::Lgetstack(Slot::Local, 24, Typ::Tlong, Mreg::AX),
        ));
        prog.run();
        assert!(prog
            .type_recovery_storage_chunk
            .iter()
            .any(|row| *row == (web, MemoryChunk::MInt16Unsigned)));
        assert!(!prog
            .type_recovery_storage_chunk
            .iter()
            .any(|(reg, chunk)| *reg == web && *chunk != MemoryChunk::MInt16Unsigned));
        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (web, XType::Xint16unsigned)));
    }

    #[test]
    fn actual_wide_access_still_prevents_a_narrow_stack_object_hypothesis() {
        let mut prog = TypePassProgram::default();
        let (func, store, reload, web, offset) = (1, 8, 2, 101, -24);
        prog.stack_var
            .extend([(func, store, offset, web), (func, reload, offset, web)]);
        prog.decoded_stack_write_bytes
            .push((store, "RBP", offset, 8));
        prog.decoded_stack_read_bytes
            .push((reload, "RBP", offset, 1));
        prog.ltl_inst.extend([
            (
                store,
                LTLInst::Lsetstack(Mreg::DX, Slot::Local, offset, Typ::Tany64),
            ),
            (
                reload,
                LTLInst::Lgetstack(Slot::Local, offset, Typ::Tint, Mreg::AX),
            ),
        ]);
        prog.run();
        assert!(prog
            .type_recovery_storage_chunk
            .iter()
            .any(|row| *row == (web, MemoryChunk::MInt8Unsigned)));
        assert!(prog
            .type_recovery_storage_chunk
            .iter()
            .any(|row| *row == (web, MemoryChunk::MAny64)));
        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (web, XType::Xany64)));
        assert!(!prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (web, XType::Xint8unsigned)));
    }

    #[test]
    fn conflicting_decoded_accesses_do_not_authorize_a_storage_width() {
        let mut prog = TypePassProgram::default();
        let (func, node, web) = (1, 9, 101);
        prog.stack_var.push((func, node, -8, web));
        prog.decoded_stack_read_bytes
            .extend([(node, "RBP", -8, 1), (node, "RBP", -8, 2)]);
        prog.ltl_inst.push((
            node,
            LTLInst::Lgetstack(Slot::Local, -8, Typ::Tint, Mreg::AX),
        ));
        prog.run();
        assert!(prog
            .type_recovery_storage_chunk
            .iter()
            .any(|row| *row == (web, MemoryChunk::Unknown)));
        assert!(!prog
            .type_recovery_storage_chunk
            .iter()
            .any(|(reg, chunk)| *reg == web && *chunk != MemoryChunk::Unknown));
        // A fallback C candidate is not a claim of four-byte physical storage.
        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (web, XType::Xint)));
    }

    #[test]
    fn unknown_access_is_not_hidden_by_another_known_byte_access() {
        let mut prog = TypePassProgram::default();
        let (func, store, reload, web, offset) = (1, 8, 2, 101, -24);
        prog.stack_var
            .extend([(func, store, offset, web), (func, reload, offset, web)]);
        prog.ltl_inst.extend([
            (
                store,
                LTLInst::Lstore(
                    MemoryChunk::MInt8Unsigned,
                    Addressing::Ainstack(offset),
                    Arc::new(vec![]),
                    Mreg::DX,
                ),
            ),
            (
                reload,
                LTLInst::Lgetstack(Slot::Local, offset, Typ::Tint, Mreg::AX),
            ),
        ]);
        prog.run();
        assert!(prog
            .type_recovery_storage_chunk
            .iter()
            .any(|row| *row == (web, MemoryChunk::MInt8Unsigned)));
        assert!(prog
            .type_recovery_storage_chunk
            .iter()
            .any(|row| *row == (web, MemoryChunk::Unknown)));
    }

    #[test]
    fn narrow_storage_does_not_narrow_the_value_being_stored() {
        let mut prog = TypePassProgram::default();
        let (func, node, web, source, offset) = (1, 9, 101, 102, -8);
        prog.stack_var.push((func, node, offset, web));
        prog.decoded_stack_write_bytes
            .push((node, "RBP", offset, 1));
        prog.reg_rtl.push((node, Mreg::AX, source));
        prog.ltl_inst.push((
            node,
            LTLInst::Lstore(
                MemoryChunk::MInt8Unsigned,
                Addressing::Ainstack(offset),
                Arc::new(vec![]),
                Mreg::AX,
            ),
        ));
        prog.run();
        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (web, XType::Xint8unsigned)));
        assert!(!prog
            .emit_var_type_candidate
            .iter()
            .any(|(reg, _)| *reg == source));
    }

    #[test]
    fn embedded_rtl_call_signature_types_arguments_and_result() {
        let mut prog = TypePassProgram::default();
        let sig = Signature {
            sig_args: Arc::new(vec![XType::Xptr, XType::Xint]),
            sig_res: XType::Xcharptr,
            sig_cc: CallConv::default(),
        };
        prog.rtl_inst.push((
            10,
            RTLInst::Icall(
                Some(sig.clone()),
                Either::Right(Either::Right("callee")),
                Arc::new(vec![101, 102]),
                Some(103),
                11,
            ),
        ));
        prog.rtl_inst.push((
            20,
            RTLInst::Itailcall(
                Some(sig),
                Either::Right(Either::Right("callee")),
                Arc::new(vec![201, 202]),
            ),
        ));
        // Indirect target and post-call result are distinct even when the
        // machine ABI uses the same architectural register for both.
        prog.rtl_inst.push((
            30,
            RTLInst::Icall(None, Either::Left(301), Arc::new(vec![]), Some(302), 31),
        ));
        prog.rtl_inst.push((
            40,
            RTLInst::Itailcall(None, Either::Left(401), Arc::new(vec![])),
        ));

        prog.run();

        for expected in [
            (101, XType::Xptr),
            (102, XType::Xint),
            (103, XType::Xcharptr),
            (201, XType::Xptr),
            (202, XType::Xint),
        ] {
            assert!(
                prog.emit_var_type_candidate
                    .iter()
                    .any(|row| *row == expected),
                "missing embedded call type {expected:?}: {:?}",
                prog.emit_var_type_candidate
            );
        }
        for reg in [101, 103, 201] {
            assert!(prog.must_be_ptr.iter().any(|row| *row == (reg,)));
        }
        assert!(prog.must_be_ptr.iter().any(|row| row == &(301,)));
        assert!(prog.must_be_ptr.iter().any(|row| row == &(401,)));
        assert!(!prog.must_be_ptr.iter().any(|row| row == &(302,)));
        assert!(!prog.must_be_ptr.iter().any(|row| *row == (102,)));
        assert!(!prog.must_be_ptr.iter().any(|row| *row == (202,)));
    }

    #[test]
    fn proven_pointer_lea_result_adds_only_a_base_candidate() {
        let mut prog = TypePassProgram::default();
        let lea_node = 10;
        let call_node = 20;
        let base = 100;
        let result = 101;
        prog.ltl_inst.push((
            lea_node,
            LTLInst::Lop(
                Operation::Olea(Addressing::Aindexed(-32)),
                Arc::new(vec![Mreg::R15]),
                Mreg::SI,
            ),
        ));
        prog.reg_rtl.push((lea_node, Mreg::R15, base));
        prog.reg_rtl.push((lea_node, Mreg::SI, result));
        prog.call_site.push((call_node, "consume"));
        prog.call_arg.push((call_node, 0, result));
        prog.known_func_param_is_ptr.push(("consume", 0));

        prog.run();

        assert!(prog.must_be_ptr.iter().any(|row| *row == (result,)));
        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (base, XType::Xptr)));
        assert!(!prog.is_ptr.iter().any(|row| *row == (base,)));
    }

    #[test]
    fn stack_lea_width_only_rtl_pointer_authority_is_hard_pointer() {
        let mut prog = TypePassProgram::default();
        let narrow_node = 0x40;
        let wide_node = 0x50;
        let narrow = 0x140;
        let wide = 0x150;

        prog.ltl_inst.extend([
            (
                narrow_node,
                LTLInst::Lop(
                    Operation::Olea(Addressing::Ainstack(16)),
                    Arc::new(vec![]),
                    Mreg::AX,
                ),
            ),
            (
                wide_node,
                LTLInst::Lop(
                    Operation::Oleal(Addressing::Ainstack(24)),
                    Arc::new(vec![]),
                    Mreg::DX,
                ),
            ),
        ]);
        prog.reg_rtl
            .extend([(narrow_node, Mreg::AX, narrow), (wide_node, Mreg::DX, wide)]);
        prog.canonical_exact_stack_addr_ptr_result
            .push((wide_node, wide));

        prog.run();

        assert!(prog.must_be_ptr.iter().any(|fact| fact == &(wide,)));
        assert!(!prog.must_be_ptr.iter().any(|fact| fact == &(narrow,)));
        assert!(!prog.is_ptr.iter().any(|fact| fact == &(narrow,)));
    }

    #[test]
    fn char_pointer_pointer_load_adds_char_pointer_candidate() {
        let mut prog = TypePassProgram::default();
        let node = 30;
        let base = 200;
        let index = 201;
        let dst = 202;
        prog.emit_var_type_candidate
            .push((base, XType::Xcharptrptr));
        prog.rtl_inst.push((
            node,
            RTLInst::Iload(
                MemoryChunk::MAny64,
                Addressing::Aindexed2scaled(8, 0),
                Arc::new(vec![base, index]),
                dst,
            ),
        ));

        prog.run();

        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (dst, XType::Xcharptr)));
    }

    #[test]
    fn main_argv_type_reaches_an_entry_copy_and_scaled_load() {
        let mut prog = TypePassProgram::default();
        let [entry] = synthetic_ids();
        let incoming_argv = 300;
        let saved_argv = 301;
        let index = 302;
        let loaded_arg = 303;

        prog.main_function.push((entry,));
        prog.func_param_position_type.push((entry, 1, XType::Xptr));
        prog.abi_int_arg_position.push((Mreg::SI, 1));
        prog.reg_rtl.push((entry, Mreg::SI, incoming_argv));
        // The optimizer may retain this copy rather than collapse it into an
        // alias edge when the destination machine register is reused later.
        prog.rtl_inst.push((
            entry + 1,
            RTLInst::Iop(Operation::Omove, Arc::new(vec![incoming_argv]), saved_argv),
        ));
        prog.rtl_inst.push((
            entry + 2,
            RTLInst::Iload(
                MemoryChunk::MAny64,
                Addressing::Aindexed2scaled(8, 0),
                Arc::new(vec![saved_argv, index]),
                loaded_arg,
            ),
        ));

        prog.run();

        for reg in [incoming_argv, saved_argv] {
            assert!(prog
                .emit_var_type_candidate
                .iter()
                .any(|row| *row == (reg, XType::Xcharptrptr)));
            assert!(prog.must_be_ptr.iter().any(|row| *row == (reg,)));
        }
        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (loaded_arg, XType::Xcharptr)));
    }

    #[test]
    fn main_without_a_second_parameter_does_not_seed_argv() {
        let mut prog = TypePassProgram::default();
        let [entry] = synthetic_ids();
        let unused_si = 400;
        prog.main_function.push((entry,));
        prog.abi_int_arg_position.push((Mreg::SI, 1));
        prog.reg_rtl.push((entry, Mreg::SI, unused_si));

        prog.run();

        assert!(!prog
            .emit_var_type_candidate
            .iter()
            .any(|row| *row == (unused_si, XType::Xcharptrptr)));
        assert!(!prog.must_be_ptr.iter().any(|row| *row == (unused_si,)));
    }
}
