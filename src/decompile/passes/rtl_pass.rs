

use crate::decompile::elevator::DecompileDB;
use crate::run_pass;

use std::sync::Arc;
use crate::decompile::passes::cminor_pass::*;
use crate::decompile::passes::csh_pass::*;
use crate::x86::asm::{Ireg, TestCond};
use crate::x86::mach::Mreg;
use crate::x86::op::{Addressing, Comparison, Condition, Operation};
use crate::x86::types::*;
use ascent::ascent_par;
use either::Either;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use crate::util::DEFAULT_VAR;
use crate::decompile::passes::asm_pass::transl_addressing_rev;
use crate::decompile::passes::pass::IRPass;
use log::info;
use rayon::prelude::*;

const ENDBR64_LEN: u64 = 4;

ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct RTLPassProgram;

    relation arch_bit(i64);
    relation arg_constrained_as_ptr(Node, RTLReg);
    relation block_in_function(Node, Address);
    relation call_arg_struct_ptr(Node, usize, usize);
    relation emit_clight_stmt(Address, Node, ClightStmt);
    relation emit_goto_target(Address, Node);
    relation emit_loop_body(Address, Node, Node);
    relation emit_loop_exit(Address, Node, Node, Condition, Arc<Vec<CsharpminorExpr>>, Node, Node);
    relation emit_switch_chain(Address, Node, RTLReg);
    relation func_param_struct_type_candidate(Address, usize, usize);
    relation func_return_struct_type(Address, usize);
    relation func_span(Symbol, Address, Address);
    relation global_struct_catalog(u64, usize, usize, usize);
    relation instr_in_function(Node, Address);
    relation is_external_function(Address);
    relation known_extern_signature(Symbol, usize, XType, Arc<Vec<XType>>);
    relation known_varargs_function(Symbol, usize);

    relation known_func_param_is_ptr(Symbol, usize);
    relation known_func_returns_float(Symbol);
    relation known_func_returns_int(Symbol);
    relation known_func_returns_long(Symbol);
    relation known_func_returns_ptr(Symbol);
    relation known_func_returns_single(Symbol);
    relation main_function(Address);
    relation reg_def_used(Address, Mreg, Address);
    relation string_data(String, String, usize);
    relation struct_field(u64, i64, String, MemoryChunk);
    relation struct_id_to_canonical(usize, usize);
    relation symbol_resolved_addr(Symbol, Address);

    relation block(Address);
    relation block_boundaries(Address, Address, Address);
    relation block_in_function(Node, Address);
    relation code_in_block(Address, Address);
    relation ddisasm_cfg_edge(Address, Address, Symbol);
    relation emit_var_type_candidate(RTLReg, XType);
    relation instr_in_function(Node, Address);
    relation instruction(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize);
    relation ireg_hold_type(String, Typ);
    relation is_not_ptr(RTLReg);
    relation is_ptr(RTLReg);
    relation is_char_ptr(RTLReg);
    relation known_extern_signature(Symbol, usize, XType, Arc<Vec<XType>>);
    relation known_varargs_function(Symbol, usize);

    relation ltl_inst(Node, LTLInst);
    relation ltl_succ(Node, Node);
    relation rtl_next(Node, Node);
    relation mach_imm_indirect_store(Address, i64, Typ, Mreg, i64);
    relation mach_imm_stack_init(Address, i64, i64, Typ);
    relation arith_load_op(Address, Operation, MemoryChunk, Mreg, i64, Mreg);
    relation arith_store_reg(Address, Operation, MemoryChunk, Mreg, i64, Mreg);
    relation arith_store_imm(Address, Operation, MemoryChunk, Mreg, i64);
    relation arith_store_abs_reg(Address, Operation, MemoryChunk, Ident, i64, Mreg);
    relation arith_store_abs_imm(Address, Operation, MemoryChunk, Ident, i64);
    relation flags_and_jump_pair(Address, Address, &'static str);
    relation next(Address, Address);
    relation op_immediate(Symbol, i64, usize);
    relation op_produces_data(Node, RTLReg);
    relation op_produces_ptr(Node, RTLReg);
    relation padd(Address, Symbol, Symbol);
    relation pcmp(Address, Symbol, Symbol);
    relation pdiv(Address, Symbol, Symbol);
    relation pidiv(Address, Symbol, Symbol);
    relation pudiv(Address, Symbol, Symbol);
    relation pjcc(Address, TestCond, Symbol);
    relation plabel(Address, Symbol);
    relation plea(Address, Symbol, Symbol);
    relation psub(Address, Symbol, Symbol);
    relation reg_def(Address, Mreg);
    relation reg_def_used(Address, Mreg, Address);
    relation reg_use(Address, Mreg);
    relation trim_instruction(Address);
    relation stack_def_used(Address, Symbol, i64, Address, Symbol, i64);
    relation symbols(Address, Symbol, Symbol);

    relation base_addr_usage(Node, RTLReg, i64);
    relation op_produces_int(Node, RTLReg);
    relation op_produces_long(Node, RTLReg);
    relation op_produces_float(Node, RTLReg);
    relation op_produces_single(Node, RTLReg);
    relation op_produces_bool(Node, RTLReg);
    relation op_produces_int8signed(Node, RTLReg);
    relation op_produces_int8unsigned(Node, RTLReg);
    relation op_produces_int16signed(Node, RTLReg);
    relation op_produces_int16unsigned(Node, RTLReg);
    relation is_int(RTLReg);
    relation is_long(RTLReg);
    relation is_float(RTLReg);
    relation is_single(RTLReg);
    relation is_bool(RTLReg);
    relation is64bit(RTLReg);
    relation is32bit(RTLReg);
    relation is_int8signed(RTLReg);
    relation is_int8unsigned(RTLReg);
    relation is_int16signed(RTLReg);
    relation is_int16unsigned(RTLReg);
    relation is_signed(RTLReg);
    relation is_unsigned(RTLReg);
    relation must_be_ptr(RTLReg);
    relation has_ptr_type(RTLReg);
    relation has_char_ptr_type(RTLReg);
    relation has_float_type(RTLReg);
    relation has_single_type(RTLReg);
    relation has_long_type(RTLReg);
    relation has_int_type(RTLReg);
    relation has_subint_type(RTLReg);


    relation head(Node);
    relation ltl_missing_prev(Node, Node);
    relation plt_block(Address, Symbol);
    relation plt_entry(Address, Symbol);
    relation func_stacksz(Address, Address, Symbol, u64);
    relation call_has_known_signature(Node, Symbol, usize, XType);
    relation function_entry_count(Address, Node, i64);

    relation rtl_inst_candidate(Node, RTLInst);
    relation emit_function(Address, Symbol, Node);
    relation rtl_succ_candidate(Node, Node);

    relation rtl_edge_negated(Node, Node);
    // Addresses with a real LTL operation (not just a label/branch fallback)
    relation has_ltl_op(Node);
    relation is_arg_reg(Mreg);
    relation is_xmm_arg_reg(Mreg);
    relation is_caller_saved(Mreg);
    relation ltl_inst_uses_mreg(Node, Mreg);
    relation ltl_node(Node);
    relation orphan_ltl_node(Node);
    relation ltl_builtin_unconverted(Node, Symbol, Arc<Vec<BuiltinArg<Mreg>>>, BuiltinArg<Mreg>);
    relation function_call(Address, Address);
    relation is_call_or_tailcall(Node);
    relation is_call_clobbered(Node, Mreg);
    relation call_args_collected_candidate(Node, Args);
    relation op_arg_mapping(Node, usize, RTLReg);
    relation op_args_collected(Node, Args);
    relation load_arg_mapping(Node, usize, RTLReg);
    relation load_args_collected(Node, Args);
    relation store_arg_mapping(Node, usize, RTLReg);
    relation store_args_collected(Node, Args);
    relation cond_arg_mapping(Node, usize, RTLReg);
    relation cond_args_collected(Node, Args);
    relation global_var_ref(usize);
    relation global_load_chunk(Ident, MemoryChunk);
    relation emit_global_is_ptr(Ident);
    relation emit_global_is_char_ptr(Ident);
    relation global_addr_reg(Ident, RTLReg);
    relation base_ident_to_symbol(Ident, Symbol);
    relation ident_to_symbol(Ident, Symbol);
    relation arg_reg_used(Address, Mreg);
    relation arg_reg_defined(Address, Mreg);
    relation comparison_operand(Node, Condition, RTLReg);
    relation rtl_reg_used_in_func(Address, RTLReg);
    relation func_has_div_instr(Address);
    relation ltl_lstore_has_regvar(Node, Mreg, RTLReg);
    relation ltl_lstore_has_edge(Node, Node);
    relation temp_cmp_reg(Address, RTLReg);
    relation temp_cmp_mreg_args(Address, usize, Mreg);
    relation temp_cmp_args_rtl(Address, usize, RTLReg);
    relation call_returns_value(Address, Mreg);
    relation ax_value_addr(Address, Address);
    relation func_ax_def(Address, Address, RTLReg);
    relation func_broken_xtl(Address, RTLReg);
    relation stack_mem_add_imm(Address, i64, i64, usize);
    relation stack_mem_sub_imm(Address, i64, i64, usize);

    // SP-indexed load/store detection: loads/stores with 2 mregs where mregs[0] == SP
    #[local] relation sp_indexed_load(Node);
    #[local] relation sp_indexed_store(Node);


    ltl_inst_uses_mreg(addr, mreg) <--
        ltl_inst(addr, ?LTLInst::Lop(_, args, _)),
        for mreg in args.iter();

    ltl_inst_uses_mreg(addr, mreg) <--
        ltl_inst(addr, ?LTLInst::Lload(_, _, args, _)),
        for mreg in args.iter();

    ltl_inst_uses_mreg(addr, mreg) <--
        ltl_inst(addr, ?LTLInst::Lstore(_, _, args, _)),
        for mreg in args.iter();

    ltl_inst_uses_mreg(addr, src) <--
        ltl_inst(addr, ?LTLInst::Lstore(_, _, _, src));

    ltl_inst_uses_mreg(addr, reg) <--
        ltl_inst(addr, ?LTLInst::Lcall(Either::Left(reg)));

    ltl_inst_uses_mreg(addr, reg) <--
        ltl_inst(addr, ?LTLInst::Ltailcall(Either::Left(reg)));

    ltl_inst_uses_mreg(addr, mreg) <--
        ltl_inst(addr, ?LTLInst::Lbuiltin(_, args, _)),
        for arg in args.iter(),
        if let BuiltinArg::BA(mreg) = arg;

    ltl_inst_uses_mreg(addr, mreg) <--
        ltl_inst(addr, ?LTLInst::Lbuiltin(_, args, _)),
        for arg in args.iter(),
        if matches!(arg, BuiltinArg::BASplitLong(_, _) | BuiltinArg::BAAddPtr(_, _)),
        let mregs = extract_builtin_arg_regs(arg),
        for mreg in mregs.iter();

    ltl_inst_uses_mreg(addr, mreg) <--
        ltl_inst(addr, ?LTLInst::Lcond(_, args, _, _)),
        for mreg in args.iter();

    ltl_inst_uses_mreg(addr, arg) <--
        ltl_inst(addr, ?LTLInst::Ljumptable(arg, _));

    ltl_inst_uses_mreg(addr, Mreg::AX) <--
        ltl_inst(addr, LTLInst::Lreturn);

    ltl_inst_uses_mreg(addr, src) <--
        ltl_inst(addr, ?LTLInst::Lsetstack(src, _, _, _));


    is_call_or_tailcall(*addr) <-- ltl_inst(addr, ?LTLInst::Lcall(_));
    is_call_or_tailcall(*addr) <-- ltl_inst(addr, ?LTLInst::Ltailcall(_));
    is_call_or_tailcall(*addr) <--
        ltl_inst(addr, ?LTLInst::Lbranch(Either::Right(target))),
        emit_function(_, _, target);

    is_call_clobbered(n, r) <-- is_call_or_tailcall(n), is_caller_saved(r);


    call_args_collected_candidate(call_addr, args) <--
        ltl_inst(call_addr, ?LTLInst::Lcall(_)),
        agg args = build_call_args(pos, reg) in call_arg_mapping(call_addr, pos, reg);


    op_arg_mapping(addr, pos, arg_rtl) <--
        ltl_inst(addr, ?LTLInst::Lop(_, mregs, _)),
        for (pos, arg) in mregs.iter().enumerate(),
        reg_rtl(addr, *arg, arg_rtl);


    op_args_collected(addr, args) <--
        ltl_inst(addr, ?LTLInst::Lop(_, mregs, _)),
        if !mregs.is_empty(),
        agg args = build_call_args(pos, reg) in op_arg_mapping(addr, pos, reg);

    op_args_collected(addr, Arc::new(vec![])) <--
        ltl_inst(addr, ?LTLInst::Lop(_, mregs, _)),
        if !mregs.is_empty(),
        !op_arg_mapping(addr, _, _);


    // Detect SP-indexed loads (2 mregs where mregs[0] is SP)
    sp_indexed_load(addr) <--
        ltl_inst(addr, ?LTLInst::Lload(_, _, mregs, _)),
        if mregs.len() == 2,
        if mregs[0] == Mreg::SP;

    // Detect SP-indexed stores (2 mregs where mregs[0] is SP)
    sp_indexed_store(addr) <--
        ltl_inst(addr, ?LTLInst::Lstore(_, _, mregs, _)),
        if mregs.len() == 2,
        if mregs[0] == Mreg::SP;

    load_arg_mapping(addr, pos, arg_rtl) <--
        ltl_inst(addr, ?LTLInst::Lload(_, _, mregs, _)),
        !sp_indexed_load(addr),
        for (pos, arg) in mregs.iter().enumerate(),
        reg_rtl(addr, *arg, arg_rtl);

    load_args_collected(addr, args) <--
        ltl_inst(addr, ?LTLInst::Lload(_, _, mregs, _)),
        if mregs.len() > 1,
        !sp_indexed_load(addr),
        agg args = build_call_args(pos, reg) in load_arg_mapping(addr, pos, reg);

    load_args_collected(addr, Arc::new(vec![])) <--
        ltl_inst(addr, ?LTLInst::Lload(_, _, mregs, _)),
        if mregs.len() > 1,
        !sp_indexed_load(addr),
        !load_arg_mapping(addr, _, _);


    store_arg_mapping(addr, pos, arg_rtl) <--
        ltl_inst(addr, ?LTLInst::Lstore(_, _, mregs, _)),
        !sp_indexed_store(addr),
        for (pos, arg) in mregs.iter().enumerate(),
        reg_rtl(addr, *arg, arg_rtl);

    store_args_collected(addr, args) <--
        ltl_inst(addr, ?LTLInst::Lstore(_, _, mregs, _)),
        if !mregs.is_empty(),
        !sp_indexed_store(addr),
        agg args = build_call_args(pos, reg) in store_arg_mapping(addr, pos, reg);

    store_args_collected(addr, Arc::new(vec![])) <--
        ltl_inst(addr, ?LTLInst::Lstore(_, _, mregs, _)),
        if !mregs.is_empty(),
        !sp_indexed_store(addr),
        !store_arg_mapping(addr, _, _);


    cond_arg_mapping(addr, pos, arg_rtl) <--
        ltl_inst(addr, ?LTLInst::Lcond(_, mregs, _, _)),
        for (pos, arg) in mregs.iter().enumerate(),
        reg_rtl(addr, *arg, arg_rtl);

    cond_args_collected(addr, args) <--
        ltl_inst(addr, ?LTLInst::Lcond(_, mregs, _, _)),
        if !mregs.is_empty(),
        agg args = build_call_args(pos, reg) in cond_arg_mapping(addr, pos, reg);

    cond_args_collected(addr, Arc::new(vec![])) <--
        ltl_inst(addr, ?LTLInst::Lcond(_, mregs, _, _)),
        if !mregs.is_empty(),
        !cond_arg_mapping(addr, _, _);

    call_args_collected_candidate(call_addr, args) <--
        ltl_inst(call_addr, ?LTLInst::Ltailcall(_)),
        agg args = build_call_args(pos, reg) in call_arg_mapping(call_addr, pos, reg);

    call_args_collected_candidate(call_addr, Arc::new(vec![])) <--
        ltl_inst(call_addr, ?LTLInst::Lcall(_)),
        !call_arg_mapping(call_addr, _, _);

    call_args_collected_candidate(call_addr, Arc::new(vec![])) <--
        ltl_inst(call_addr, ?LTLInst::Ltailcall(_)),
        !call_arg_mapping(call_addr, _, _);


    ident_to_symbol(ident, *name) <-- base_ident_to_symbol(ident, name);

    base_ident_to_symbol(ident, *name) <--
        symbols(addr, name, _),
        !plt_block(addr, _),
        !plt_entry(addr, _),
        let ident = *addr as Ident;

    base_ident_to_symbol(ident, clean_name) <--
        plt_entry(addr, sym),
        let ident = *addr as Ident,
        let clean_name = strip_version_suffix(sym);

    base_ident_to_symbol(ident, clean_name) <--
        plt_block(addr, sym),
        let ident = *addr as Ident,
        let clean_name = strip_version_suffix(sym);

    global_var_ref(ident) <--
        ltl_inst(_, ?LTLInst::Lop(Operation::Oindirectsymbol(ident), _, _));

    global_var_ref(ident) <--
        ltl_inst(_, ?LTLInst::Lload(_, Addressing::Aglobal(ident, _), _, _));

    global_var_ref(ident) <--
        ltl_inst(_, ?LTLInst::Lstore(_, Addressing::Aglobal(ident, _), _, _));

    global_var_ref(ident) <--
        ltl_inst(_, ?LTLInst::Lload(_, Addressing::Abased(ident, _), _, _));

    global_var_ref(ident) <--
        ltl_inst(_, ?LTLInst::Lstore(_, Addressing::Abased(ident, _), _, _));

    global_var_ref(ident) <--
        ltl_inst(_, ?LTLInst::Lload(_, Addressing::Abasedscaled(_, ident, _), _, _));

    global_var_ref(ident) <--
        ltl_inst(_, ?LTLInst::Lstore(_, Addressing::Abasedscaled(_, ident, _), _, _));

    global_var_ref(ident) <--
        ltl_inst(_, ?LTLInst::Lcall(Either::Right(Either::Right(name_sym)))),
        ident_to_symbol(ident, name),
        if name == name_sym;

    global_var_ref(ident) <--
        ltl_inst(_, ?LTLInst::Ltailcall(Either::Right(Either::Right(name_sym)))),
        ident_to_symbol(ident, name),
        if name == name_sym;

    // Track memory chunk type used when loading from each global (for rodata constant inlining)
    global_load_chunk(*ident, chunk.clone()) <--
        ltl_inst(_, ?LTLInst::Lload(chunk, Addressing::Aglobal(ident, _), _, _));

    global_load_chunk(*ident, chunk.clone()) <--
        ltl_inst(_, ?LTLInst::Lload(chunk, Addressing::Abased(ident, _), _, _));

    global_load_chunk(*ident, chunk.clone()) <--
        ltl_inst(_, ?LTLInst::Lload(chunk, Addressing::Abasedscaled(_, ident, _), _, _));

    // Store chunks via direct addressing (also inform global type inference)
    global_load_chunk(*ident, chunk.clone()) <--
        ltl_inst(_, ?LTLInst::Lstore(chunk, Addressing::Aglobal(ident, _), _, _));

    global_load_chunk(*ident, chunk.clone()) <--
        ltl_inst(_, ?LTLInst::Lstore(chunk, Addressing::Abased(ident, _), _, _));

    global_load_chunk(*ident, chunk.clone()) <--
        ltl_inst(_, ?LTLInst::Lstore(chunk, Addressing::Abasedscaled(_, ident, _), _, _));

    // Track RTL register holding address of a global (from Oindirectsymbol, used in PIC binaries)
    global_addr_reg(*ident, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Oindirectsymbol(ident), _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    // Propagate global address register through aliases
    global_addr_reg(*ident, b) <-- global_addr_reg(ident, a), alias_edge(a, b);
    global_addr_reg(*ident, a) <-- global_addr_reg(ident, b), alias_edge(a, b);

    // When a global address register is used as base for a load at offset 0, track the chunk
    global_load_chunk(*ident, chunk.clone()) <--
        global_addr_reg(ident, addr_rtl),
        ltl_inst(node, ?LTLInst::Lload(chunk, Addressing::Aindexed(0), args, _)),
        if !args.is_empty(),
        reg_rtl(node, args[0], base_rtl),
        if *addr_rtl == *base_rtl;

    // When a global address register is used as base for a store at offset 0, track the chunk
    global_load_chunk(*ident, chunk.clone()) <--
        global_addr_reg(ident, addr_rtl),
        ltl_inst(node, ?LTLInst::Lstore(chunk, Addressing::Aindexed(0), args, _)),
        if !args.is_empty(),
        reg_rtl(node, args[0], base_rtl),
        if *addr_rtl == *base_rtl;

    // Note: emit_global_is_ptr/emit_global_is_char_ptr are computed in type_pass.rs (more precise).

    function_call(caller_func, callee_func) <--
        ltl_inst(caller, ?LTLInst::Lcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Left(callee_addr) = target,
        instr_in_function(caller, caller_func),
        instr_in_function(callee_addr, callee_func);

    function_call(caller_func, callee_func) <--
        ltl_inst(caller, ?LTLInst::Ltailcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Left(callee_addr) = target,
        instr_in_function(caller, caller_func),
        instr_in_function(callee_addr, callee_func);

    function_call(caller_func, callee_func) <--
        ltl_inst(caller, ?LTLInst::Lbranch(Either::Right(callee_node))),
        emit_function(callee_func, _, callee_node),
        instr_in_function(caller, caller_func);


    ltl_node(addr) <--
        ltl_inst(addr, _);

    orphan_ltl_node(addr) <--
        ltl_node(addr),
        !ltl_succ(_, addr),
        !ltl_succ(addr, _);


    is_ptr(reg) <--
        op_produces_ptr(_, reg);

    is_not_ptr(reg) <--
        op_produces_data(_, reg);


    comparison_operand(addr, cond.clone(), rtl_arg) <--
        ltl_inst(addr, ?LTLInst::Lcond(cond, mregs, _, _)),
        for mreg in mregs.iter(),
        reg_rtl(addr, *mreg, rtl_arg);


    reg_xtl(head_addr, mreg, arg_id) <--
        ltl_inst(head_addr, ?LTLInst::Lop(_, mregs, _)),
        for mreg in mregs.iter(),
        reg_def_used(defaddr, *mreg, *head_addr),
        !load_overwrites_base(defaddr, mreg),
        reg_xtl(defaddr, *mreg, arg_id);

    reg_xtl(head_addr, mreg, arg_id) <--
        ltl_inst(head_addr, ?LTLInst::Lop(_, mregs, _)),
        for mreg in mregs.iter(),
        reg_def_used(defaddr, *mreg, *head_addr),
        load_overwrites_base(defaddr, mreg),
        is_def(defaddr, arg_id),
        reg_xtl(defaddr, *mreg, arg_id);

    reg_xtl(head_addr, mreg, id) <--
        ltl_inst(head_addr, ?LTLInst::Lbuiltin(_, args, _)),
        for builtin_arg in args,
        if let BuiltinArg::BA(mreg) = builtin_arg,
        reg_def_used(defaddr, *mreg, *head_addr),
        !load_overwrites_base(defaddr, mreg),
        reg_xtl(defaddr, *mreg, id);

    reg_xtl(head_addr, mreg, id) <--
        ltl_inst(head_addr, ?LTLInst::Lbuiltin(_, args, _)),
        for builtin_arg in args,
        if let BuiltinArg::BA(mreg) = builtin_arg,
        reg_def_used(defaddr, *mreg, *head_addr),
        load_overwrites_base(defaddr, mreg),
        is_def(defaddr, id),
        reg_xtl(defaddr, *mreg, id);

    reg_xtl(head_addr, mreg, arg_id) <--
        ltl_inst(head_addr, ?LTLInst::Lload(_, _, mregs, _)),
        for mreg in mregs.iter(),
        reg_def_used(defaddr, *mreg, *head_addr),
        !load_overwrites_base(head_addr, mreg),
        !load_overwrites_base(defaddr, mreg),
        reg_xtl(defaddr, *mreg, arg_id);

    reg_xtl(head_addr, mreg, arg_id) <--
        ltl_inst(head_addr, ?LTLInst::Lload(_, _, mregs, _)),
        for mreg in mregs.iter(),
        reg_def_used(defaddr, *mreg, *head_addr),
        !load_overwrites_base(head_addr, mreg),
        load_overwrites_base(defaddr, mreg),
        is_def(defaddr, arg_id),
        reg_xtl(defaddr, *mreg, arg_id);

    reg_xtl(addr, Mreg::from(reg_str.to_string()), arg_id) <--
        pcmp(addr, sym1, sym2),
        op_register(sym1, reg_str),
        reg_def_used(addr, Mreg::from(reg_str.to_string()), *addr),
        reg_xtl(*addr, Mreg::from(reg_str.to_string()), arg_id);

    reg_xtl(addr, Mreg::from(reg_str.to_string()), arg_id) <--
        pcmp(addr, sym1, sym2),
        op_register(sym2, reg_str),
        reg_def_used(addr, Mreg::from(reg_str.to_string()), *addr),
        reg_xtl(*addr, Mreg::from(reg_str.to_string()), arg_id);

    reg_xtl(head_addr, *src, srcid) <--
        ltl_inst(head_addr, ?LTLInst::Lstore(mc, adrs, args, src)),
        reg_def_used(defaddr, *src, *head_addr),
        !load_overwrites_base(defaddr, src),
        reg_xtl(defaddr, *src, srcid);

    reg_xtl(head_addr, *src, srcid) <--
        ltl_inst(head_addr, ?LTLInst::Lstore(mc, adrs, args, src)),
        reg_def_used(defaddr, *src, *head_addr),
        load_overwrites_base(defaddr, src),
        is_def(defaddr, srcid),
        reg_xtl(defaddr, *src, srcid);

    reg_xtl(head_addr, *src, srcid) <--
        ltl_inst(head_addr, ?LTLInst::Lsetstack(src, _, _, _)),
        reg_def_used(defaddr, *src, *head_addr),
        !load_overwrites_base(defaddr, src),
        reg_xtl(defaddr, *src, srcid);

    reg_xtl(head_addr, *src, srcid) <--
        ltl_inst(head_addr, ?LTLInst::Lsetstack(src, _, _, _)),
        reg_def_used(defaddr, *src, *head_addr),
        load_overwrites_base(defaddr, src),
        is_def(defaddr, srcid),
        reg_xtl(defaddr, *src, srcid);


    reg_xtl(head_addr, mreg, arg_id) <--
        ltl_inst(head_addr, ?LTLInst::Lcond(_, args, _, _)),
        for mreg in args.iter(),
        reg_def_used(defaddr, *mreg, *head_addr),
        !load_overwrites_base(defaddr, mreg),
        reg_xtl(defaddr, *mreg, arg_id);

    reg_xtl(head_addr, mreg, arg_id) <--
        ltl_inst(head_addr, ?LTLInst::Lcond(_, args, _, _)),
        for mreg in args.iter(),
        reg_def_used(defaddr, *mreg, *head_addr),
        load_overwrites_base(defaddr, mreg),
        is_def(defaddr, arg_id),
        reg_xtl(defaddr, *mreg, arg_id);

    reg_xtl(addr, arg, arg_id) <--
        ltl_inst(addr, ?LTLInst::Ljumptable(arg, _)),
        reg_def_used(defaddr, *arg, *addr),
        !load_overwrites_base(defaddr, arg),
        reg_xtl(defaddr, *arg, arg_id);

    reg_xtl(addr, arg, arg_id) <--
        ltl_inst(addr, ?LTLInst::Ljumptable(arg, _)),
        reg_def_used(defaddr, *arg, *addr),
        load_overwrites_base(defaddr, arg),
        is_def(defaddr, arg_id),
        reg_xtl(defaddr, *arg, arg_id);


    reg_xtl(addr, mreg, callee_id) <--
        ltl_inst(addr, ?LTLInst::Lcall(Either::Left(mreg))),
        reg_def_used(defaddr, *mreg, *addr),
        !load_overwrites_base(defaddr, mreg),
        reg_xtl(defaddr, *mreg, callee_id);

    reg_xtl(addr, mreg, callee_id) <--
        ltl_inst(addr, ?LTLInst::Lcall(Either::Left(mreg))),
        reg_def_used(defaddr, *mreg, *addr),
        load_overwrites_base(defaddr, mreg),
        is_def(defaddr, callee_id),
        reg_xtl(defaddr, *mreg, callee_id);

    reg_xtl(addr, mreg, callee_id) <--
        ltl_inst(addr, ?LTLInst::Ltailcall(Either::Left(mreg))),
        reg_def_used(defaddr, *mreg, *addr),
        !load_overwrites_base(defaddr, mreg),
        reg_xtl(defaddr, *mreg, callee_id);

    reg_xtl(addr, mreg, callee_id) <--
        ltl_inst(addr, ?LTLInst::Ltailcall(Either::Left(mreg))),
        reg_def_used(defaddr, *mreg, *addr),
        load_overwrites_base(defaddr, mreg),
        is_def(defaddr, callee_id),
        reg_xtl(defaddr, *mreg, callee_id);


    rtl_inst_candidate(addr, inst) <--
        mach_imm_stack_init(addr, ofs, imm_val, typ),
        instr_in_function(addr, func_start),
        stack_var(func_start, addr, ofs, rtl_reg),
        let op = match typ {
            Typ::Tint => Operation::Ointconst(*imm_val),
            Typ::Tlong | Typ::Tany64 => Operation::Olongconst(*imm_val),
            _ => Operation::Ointconst(*imm_val),
        },
        let inst = RTLInst::Iop(op, Arc::new(vec![]), *rtl_reg);

    rtl_inst_candidate(addr, inst) <--
        mach_imm_stack_init(addr, ofs, imm_val, typ),
        instr_in_function(addr, func_start),
        !stack_xtl(func_start, addr, ofs, _),
        let rtl_reg = fresh_xtl_reg(*addr, Mreg::BP),
        let op = match typ {
            Typ::Tint => Operation::Ointconst(*imm_val),
            Typ::Tlong | Typ::Tany64 => Operation::Olongconst(*imm_val),
            _ => Operation::Ointconst(*imm_val),
        },
        let inst = RTLInst::Iop(op, Arc::new(vec![]), rtl_reg);

    reg_xtl(addr, base_mreg, arg_id) <--
        mach_imm_indirect_store(addr, _, _, base_mreg, _),
        reg_def_used(defaddr, *base_mreg, *addr),
        !load_overwrites_base(defaddr, base_mreg),
        reg_xtl(defaddr, *base_mreg, arg_id);

    reg_xtl(addr, base_mreg, arg_id) <--
        mach_imm_indirect_store(addr, _, _, base_mreg, _),
        reg_def_used(defaddr, *base_mreg, *addr),
        load_overwrites_base(defaddr, base_mreg),
        is_def(defaddr, arg_id),
        reg_xtl(defaddr, *base_mreg, arg_id);

    rtl_succ_candidate(src, dst) <-- rtl_next(src, dst), !rtl_edge_negated(src, dst);

    has_ltl_op(addr) <-- ltl_inst(addr, ?LTLInst::Lop(_, _, _));
    has_ltl_op(addr) <-- ltl_inst(addr, ?LTLInst::Lload(_, _, _, _));
    has_ltl_op(addr) <-- ltl_inst(addr, ?LTLInst::Lstore(_, _, _, _));
    has_ltl_op(addr) <-- ltl_inst(addr, ?LTLInst::Lcall(_));
    has_ltl_op(addr) <-- ltl_inst(addr, ?LTLInst::Ltailcall(_));
    has_ltl_op(addr) <-- ltl_inst(addr, ?LTLInst::Lcond(_, _, _, _));
    has_ltl_op(addr) <-- ltl_inst(addr, ?LTLInst::Lbuiltin(_, _, _));
    has_ltl_op(addr) <-- ltl_inst(addr, ?LTLInst::Lgetstack(_, _, _, _));
    has_ltl_op(addr) <-- ltl_inst(addr, ?LTLInst::Lsetstack(_, _, _, _));
    has_ltl_op(addr) <-- ltl_inst(addr, ?LTLInst::Ljumptable(_, _));
    has_ltl_op(addr) <-- ltl_inst(addr, ?LTLInst::Lreturn);

    rtl_inst_candidate(addr, iop_inst) <--
        mach_imm_indirect_store(addr, imm_val, typ, _base_mreg, _disp),
        let fresh_reg = fresh_xtl_reg(*addr, Mreg::DI),
        let op = match typ {
            Typ::Tint => Operation::Ointconst(*imm_val),
            Typ::Tlong | Typ::Tany64 => Operation::Olongconst(*imm_val),
            _ => Operation::Ointconst(*imm_val),
        },
        let iop_inst = RTLInst::Iop(op, Arc::new(vec![]), fresh_reg);
    
    rtl_inst_candidate(synthetic_addr, istore_inst) <--
        mach_imm_indirect_store(addr, _imm_val, typ, base_mreg, disp),
        reg_xtl(addr, *base_mreg, base_rtl),
        let fresh_reg = fresh_xtl_reg(*addr, Mreg::DI),
        let synthetic_addr = *addr | (1u64 << 62),
        let mc = match typ {
            Typ::Tint => MemoryChunk::MInt32,
            Typ::Tlong | Typ::Tany64 => MemoryChunk::MInt64,
            _ => MemoryChunk::MInt32,
        },
        let addressing = Addressing::Aindexed(*disp),
        let istore_inst = RTLInst::Istore(mc, addressing, Arc::new(vec![*base_rtl]), fresh_reg);
    

    rtl_edge_negated(addr, next) <--
        mach_imm_indirect_store(addr, _, _, _, _),
        next(addr, next);

    rtl_succ_candidate(addr, synthetic_addr), instr_in_function(addr, func_start) <--
        mach_imm_indirect_store(addr, _, _, _, _),
        instr_in_function(addr, func_start),
        let synthetic_addr = *addr | (1u64 << 62);

    rtl_succ_candidate(synthetic_addr, next), instr_in_function(synthetic_addr, func_start) <--
        mach_imm_indirect_store(addr, _, _, _, _),
        instr_in_function(addr, func_start),
        let synthetic_addr = *addr | (1u64 << 62),
        next(addr, next);

    // reg_xtl for arith addresses: chains from reg_def_used definition site when no real ltl op exists.
    reg_xtl(*addr, *base_mreg, arg_id) <--
        arith_load_op(addr, _, _, base_mreg, _, _),
        !has_ltl_op(addr),
        reg_def_used(defaddr, *base_mreg, *addr),
        reg_xtl(defaddr, *base_mreg, arg_id);

    reg_xtl(*addr, *dst_mreg, arg_id) <--
        arith_load_op(addr, _, _, _, _, dst_mreg),
        !has_ltl_op(addr),
        reg_def_used(defaddr, *dst_mreg, *addr),
        reg_xtl(defaddr, *dst_mreg, arg_id);

    reg_xtl(*addr, *base_mreg, arg_id) <--
        arith_store_reg(addr, _, _, base_mreg, _, _),
        !has_ltl_op(addr),
        reg_def_used(defaddr, *base_mreg, *addr),
        reg_xtl(defaddr, *base_mreg, arg_id);

    reg_xtl(*addr, *src_mreg, arg_id) <--
        arith_store_reg(addr, _, _, _, _, src_mreg),
        !has_ltl_op(addr),
        reg_def_used(defaddr, *src_mreg, *addr),
        reg_xtl(defaddr, *src_mreg, arg_id);

    reg_xtl(*addr, *base_mreg, arg_id) <--
        arith_store_imm(addr, _, _, base_mreg, _),
        !has_ltl_op(addr),
        reg_def_used(defaddr, *base_mreg, *addr),
        reg_xtl(defaddr, *base_mreg, arg_id);

    reg_xtl(*addr, *src_mreg, arg_id) <--
        arith_store_abs_reg(addr, _, _, _, _, src_mreg),
        !has_ltl_op(addr),
        reg_def_used(defaddr, *src_mreg, *addr),
        reg_xtl(defaddr, *src_mreg, arg_id);

    // arith_load_op: memory-source arithmetic (e.g. add [mem], reg); only fires without a real ltl op.
    rtl_inst_candidate(addr, load_inst) <--
        arith_load_op(addr, _op, chunk, base_mreg, disp, _dst_mreg),
        !has_ltl_op(addr),
        reg_xtl(addr, *base_mreg, base_rtl),
        let temp = fresh_xtl_reg(*addr, Mreg::from("RTEMP")),
        let load_inst = RTLInst::Iload(*chunk, Addressing::Aindexed(*disp), Arc::new(vec![*base_rtl]), temp);

    rtl_inst_candidate(synthetic_addr, op_inst) <--
        arith_load_op(addr, op, _chunk, _base_mreg, _disp, dst_mreg),
        !has_ltl_op(addr),
        reg_xtl(addr, *dst_mreg, dst_rtl),
        let temp = fresh_xtl_reg(*addr, Mreg::from("RTEMP")),
        let synthetic_addr = *addr | (1u64 << 62),
        let op_inst = RTLInst::Iop(op.clone(), Arc::new(vec![*dst_rtl, temp]), *dst_rtl);

    rtl_edge_negated(addr, next) <--
        arith_load_op(addr, _, _, _, _, _),
        !has_ltl_op(addr),
        next(addr, next);

    rtl_succ_candidate(addr, synthetic_addr), instr_in_function(addr, func_start) <--
        arith_load_op(addr, _, _, _, _, _),
        !has_ltl_op(addr),
        instr_in_function(addr, func_start),
        let synthetic_addr = *addr | (1u64 << 62);

    rtl_succ_candidate(synthetic_addr, next), instr_in_function(synthetic_addr, func_start) <--
        arith_load_op(addr, _, _, _, _, _),
        !has_ltl_op(addr),
        instr_in_function(addr, func_start),
        let synthetic_addr = *addr | (1u64 << 62),
        next(addr, next);

    // arith_store_reg: memory-dest arithmetic with register source; only fires without a real ltl op.
    rtl_inst_candidate(addr, load_inst) <--
        arith_store_reg(addr, _op, chunk, base_mreg, disp, _src_mreg),
        !has_ltl_op(addr),
        reg_xtl(addr, *base_mreg, base_rtl),
        let temp = fresh_xtl_reg(*addr, Mreg::from("RTEMP")),
        let load_inst = RTLInst::Iload(*chunk, Addressing::Aindexed(*disp), Arc::new(vec![*base_rtl]), temp);

    rtl_inst_candidate(synth1, op_inst) <--
        arith_store_reg(addr, op, _chunk, _base_mreg, _disp, src_mreg),
        !has_ltl_op(addr),
        reg_xtl(addr, *src_mreg, src_rtl),
        let temp = fresh_xtl_reg(*addr, Mreg::from("RTEMP")),
        let temp2 = fresh_xtl_reg(*addr | (1u64 << 62), Mreg::from("RTEMP")),
        let synth1 = *addr | (1u64 << 62),
        let op_inst = RTLInst::Iop(op.clone(), Arc::new(vec![temp, *src_rtl]), temp2);

    rtl_inst_candidate(synth2, store_inst) <--
        arith_store_reg(addr, _op, chunk, base_mreg, disp, _src_mreg),
        !has_ltl_op(addr),
        reg_xtl(addr, *base_mreg, base_rtl),
        let temp2 = fresh_xtl_reg(*addr | (1u64 << 62), Mreg::from("RTEMP")),
        let synth2 = *addr | (1u64 << 63),
        let store_inst = RTLInst::Istore(*chunk, Addressing::Aindexed(*disp), Arc::new(vec![*base_rtl]), temp2);

    rtl_edge_negated(addr, next) <--
        arith_store_reg(addr, _, _, _, _, _),
        !has_ltl_op(addr),
        next(addr, next);

    rtl_succ_candidate(addr, synth1), instr_in_function(addr, func_start) <--
        arith_store_reg(addr, _, _, _, _, _),
        !has_ltl_op(addr),
        instr_in_function(addr, func_start),
        let synth1 = *addr | (1u64 << 62);

    rtl_succ_candidate(synth1, synth2), instr_in_function(synth1, func_start) <--
        arith_store_reg(addr, _, _, _, _, _),
        !has_ltl_op(addr),
        instr_in_function(addr, func_start),
        let synth1 = *addr | (1u64 << 62),
        let synth2 = *addr | (1u64 << 63);

    rtl_succ_candidate(synth2, next), instr_in_function(synth2, func_start) <--
        arith_store_reg(addr, _, _, _, _, _),
        !has_ltl_op(addr),
        instr_in_function(addr, func_start),
        let synth2 = *addr | (1u64 << 63),
        next(addr, next);

    // arith_store_imm: memory-dest arithmetic with immediate; only fires without a real ltl op.
    rtl_inst_candidate(addr, load_inst) <--
        arith_store_imm(addr, _op, chunk, base_mreg, disp),
        !has_ltl_op(addr),
        reg_xtl(addr, *base_mreg, base_rtl),
        let temp = fresh_xtl_reg(*addr, Mreg::from("RTEMP")),
        let load_inst = RTLInst::Iload(*chunk, Addressing::Aindexed(*disp), Arc::new(vec![*base_rtl]), temp);

    rtl_inst_candidate(synth1, op_inst) <--
        arith_store_imm(addr, op, _chunk, _base_mreg, _disp),
        !has_ltl_op(addr),
        let temp = fresh_xtl_reg(*addr, Mreg::from("RTEMP")),
        let temp2 = fresh_xtl_reg(*addr | (1u64 << 62), Mreg::from("RTEMP")),
        let synth1 = *addr | (1u64 << 62),
        let op_inst = RTLInst::Iop(op.clone(), Arc::new(vec![temp]), temp2);

    rtl_inst_candidate(synth2, store_inst) <--
        arith_store_imm(addr, _op, chunk, base_mreg, disp),
        !has_ltl_op(addr),
        reg_xtl(addr, *base_mreg, base_rtl),
        let temp2 = fresh_xtl_reg(*addr | (1u64 << 62), Mreg::from("RTEMP")),
        let synth2 = *addr | (1u64 << 63),
        let store_inst = RTLInst::Istore(*chunk, Addressing::Aindexed(*disp), Arc::new(vec![*base_rtl]), temp2);

    rtl_edge_negated(addr, next) <--
        arith_store_imm(addr, _, _, _, _),
        !has_ltl_op(addr),
        next(addr, next);

    rtl_succ_candidate(addr, synth1), instr_in_function(addr, func_start) <--
        arith_store_imm(addr, _, _, _, _),
        !has_ltl_op(addr),
        instr_in_function(addr, func_start),
        let synth1 = *addr | (1u64 << 62);

    rtl_succ_candidate(synth1, synth2), instr_in_function(synth1, func_start) <--
        arith_store_imm(addr, _, _, _, _),
        !has_ltl_op(addr),
        instr_in_function(addr, func_start),
        let synth1 = *addr | (1u64 << 62),
        let synth2 = *addr | (1u64 << 63);

    rtl_succ_candidate(synth2, next), instr_in_function(synth2, func_start) <--
        arith_store_imm(addr, _, _, _, _),
        !has_ltl_op(addr),
        instr_in_function(addr, func_start),
        let synth2 = *addr | (1u64 << 63),
        next(addr, next);

    // arith_store_abs_reg: read-modify-write at absolute (global) address with register source.
    rtl_inst_candidate(addr, load_inst) <--
        arith_store_abs_reg(addr, _op, chunk, ident, offset, _src_mreg),
        !has_ltl_op(addr),
        let temp = fresh_xtl_reg(*addr, Mreg::from("RTEMP")),
        let load_inst = RTLInst::Iload(*chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), temp);

    rtl_inst_candidate(synth1, op_inst) <--
        arith_store_abs_reg(addr, op, _chunk, _ident, _offset, src_mreg),
        !has_ltl_op(addr),
        reg_xtl(addr, *src_mreg, src_rtl),
        let temp = fresh_xtl_reg(*addr, Mreg::from("RTEMP")),
        let temp2 = fresh_xtl_reg(*addr | (1u64 << 62), Mreg::from("RTEMP")),
        let synth1 = *addr | (1u64 << 62),
        let op_inst = RTLInst::Iop(op.clone(), Arc::new(vec![temp, *src_rtl]), temp2);

    rtl_inst_candidate(synth2, store_inst) <--
        arith_store_abs_reg(addr, _op, chunk, ident, offset, _src_mreg),
        !has_ltl_op(addr),
        let temp2 = fresh_xtl_reg(*addr | (1u64 << 62), Mreg::from("RTEMP")),
        let synth2 = *addr | (1u64 << 63),
        let store_inst = RTLInst::Istore(*chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), temp2);

    rtl_edge_negated(addr, next) <--
        arith_store_abs_reg(addr, _, _, _, _, _),
        !has_ltl_op(addr),
        next(addr, next);

    rtl_succ_candidate(addr, synth1), instr_in_function(addr, func_start) <--
        arith_store_abs_reg(addr, _, _, _, _, _),
        !has_ltl_op(addr),
        instr_in_function(addr, func_start),
        let synth1 = *addr | (1u64 << 62);

    rtl_succ_candidate(synth1, synth2), instr_in_function(synth1, func_start) <--
        arith_store_abs_reg(addr, _, _, _, _, _),
        !has_ltl_op(addr),
        instr_in_function(addr, func_start),
        let synth1 = *addr | (1u64 << 62),
        let synth2 = *addr | (1u64 << 63);

    rtl_succ_candidate(synth2, next), instr_in_function(synth2, func_start) <--
        arith_store_abs_reg(addr, _, _, _, _, _),
        !has_ltl_op(addr),
        instr_in_function(addr, func_start),
        let synth2 = *addr | (1u64 << 63),
        next(addr, next);

    // arith_store_abs_imm: read-modify-write at absolute (global) address with immediate source.
    rtl_inst_candidate(addr, load_inst) <--
        arith_store_abs_imm(addr, _op, chunk, ident, offset),
        !has_ltl_op(addr),
        let temp = fresh_xtl_reg(*addr, Mreg::from("RTEMP")),
        let load_inst = RTLInst::Iload(*chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), temp);

    rtl_inst_candidate(synth1, op_inst) <--
        arith_store_abs_imm(addr, op, _chunk, _ident, _offset),
        !has_ltl_op(addr),
        let temp = fresh_xtl_reg(*addr, Mreg::from("RTEMP")),
        let temp2 = fresh_xtl_reg(*addr | (1u64 << 62), Mreg::from("RTEMP")),
        let synth1 = *addr | (1u64 << 62),
        let op_inst = RTLInst::Iop(op.clone(), Arc::new(vec![temp]), temp2);

    rtl_inst_candidate(synth2, store_inst) <--
        arith_store_abs_imm(addr, _op, chunk, ident, offset),
        !has_ltl_op(addr),
        let temp2 = fresh_xtl_reg(*addr | (1u64 << 62), Mreg::from("RTEMP")),
        let synth2 = *addr | (1u64 << 63),
        let store_inst = RTLInst::Istore(*chunk, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), temp2);

    rtl_edge_negated(addr, next) <--
        arith_store_abs_imm(addr, _, _, _, _),
        !has_ltl_op(addr),
        next(addr, next);

    rtl_succ_candidate(addr, synth1), instr_in_function(addr, func_start) <--
        arith_store_abs_imm(addr, _, _, _, _),
        !has_ltl_op(addr),
        instr_in_function(addr, func_start),
        let synth1 = *addr | (1u64 << 62);

    rtl_succ_candidate(synth1, synth2), instr_in_function(synth1, func_start) <--
        arith_store_abs_imm(addr, _, _, _, _),
        !has_ltl_op(addr),
        instr_in_function(addr, func_start),
        let synth1 = *addr | (1u64 << 62),
        let synth2 = *addr | (1u64 << 63);

    rtl_succ_candidate(synth2, next), instr_in_function(synth2, func_start) <--
        arith_store_abs_imm(addr, _, _, _, _),
        !has_ltl_op(addr),
        instr_in_function(addr, func_start),
        let synth2 = *addr | (1u64 << 63),
        next(addr, next);

    reg_xtl(addr, dst, fresh_dst_id), is_def(addr, fresh_dst_id) <--
        ltl_inst(addr, ?LTLInst::Lgetstack(_, _ofs, _, dst)),
        let fresh_dst_id = fresh_xtl_reg(*addr, *dst);

    ltl_inst(addr, LTLInst::Lsetstack(*src, slot, *ofs, *typ)) <--
        ltl_inst(addr, ?LTLInst::Lstore(mc, Addressing::Ainstack(ofs), args, src)),
        if args.len() == 0,
        let slot = Slot::Local,
        instruction(addr, _, _, _, src_reg, _, _, _, _, _),
        op_register(src_reg, src_reg_str),
        ireg_hold_type(src_reg_str.to_string(), typ);


    rtl_reg_used_in_func(func_start, *reg_rtl) <--
        reg_rtl(addr, mreg, reg_rtl),
        instr_in_function(addr, func_start);


    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lop(op, mregs, dst_reg)),
        if mregs.is_empty(),
        reg_rtl(addr, *dst_reg, dst_rtl),
        let inst = RTLInst::Iop(op.clone(), Arc::new(vec![]), *dst_rtl);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lop(op, mregs, dst_reg)),
        if mregs.is_empty(),
        !reg_xtl(addr, *dst_reg, _),
        let dst_rtl = fresh_xtl_reg(*addr, *dst_reg),
        let inst = RTLInst::Iop(op.clone(), Arc::new(vec![]), dst_rtl);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lop(op, mregs, dst_reg)),
        if !mregs.is_empty(),
        reg_rtl(addr, *dst_reg, dst_rtl),
        op_args_collected(addr, args),
        let inst = RTLInst::Iop(op.clone(), args.clone(), *dst_rtl);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lop(op, mregs, dst_reg)),
        if !mregs.is_empty(),
        !reg_xtl(addr, *dst_reg, _),
        let dst_rtl = fresh_xtl_reg(*addr, *dst_reg),
        op_args_collected(addr, args),
        let inst = RTLInst::Iop(op.clone(), args.clone(), dst_rtl);

    reg_def_site(addr, Mreg::AX) <--
        pdiv(addr, _, _);

    reg_def_site(addr, Mreg::DX) <--
        pdiv(addr, _, _);

    func_has_div_instr(func_start) <--
        instr_in_function(addr, func_start),
        pdiv(addr, _, _);


    // Signed division (IDIV): quotient in AX, remainder in DX
    rtl_inst_candidate(addr, RTLInst::Iop(Operation::Odiv, args.clone(), *quot_rtl)) <--
        pidiv(addr, _, divisor_sym),
        op_register(divisor_sym, divisor_reg_str),
        let divisor_mreg = Mreg::from(divisor_reg_str.to_string()),
        reg_def_used(ax_def_addr, Mreg::AX, addr),
        reg_rtl(ax_def_addr, Mreg::AX, ax_rtl),
        reg_def_used(div_def_addr, divisor_mreg, addr),
        reg_rtl(div_def_addr, divisor_mreg, divisor_rtl),
        reg_rtl(addr, Mreg::AX, quot_rtl),
        let args = Arc::new(vec![*ax_rtl, *divisor_rtl]);

    rtl_inst_candidate(synthetic_addr, RTLInst::Iop(Operation::Omod, args.clone(), *rem_rtl)) <--
        pidiv(addr, _, divisor_sym),
        op_register(divisor_sym, divisor_reg_str),
        let divisor_mreg = Mreg::from(divisor_reg_str.to_string()),
        reg_def_used(ax_def_addr, Mreg::AX, addr),
        reg_rtl(ax_def_addr, Mreg::AX, ax_rtl),
        reg_def_used(div_def_addr, divisor_mreg, addr),
        reg_rtl(div_def_addr, divisor_mreg, divisor_rtl),
        reg_rtl(addr, Mreg::DX, rem_rtl),
        let synthetic_addr = *addr | (1u64 << 62),
        let args = Arc::new(vec![*ax_rtl, *divisor_rtl]);

    // Unsigned division (DIV): quotient in AX, remainder in DX
    rtl_inst_candidate(addr, RTLInst::Iop(Operation::Odivu, args.clone(), *quot_rtl)) <--
        pudiv(addr, _, divisor_sym),
        op_register(divisor_sym, divisor_reg_str),
        let divisor_mreg = Mreg::from(divisor_reg_str.to_string()),
        reg_def_used(ax_def_addr, Mreg::AX, addr),
        reg_rtl(ax_def_addr, Mreg::AX, ax_rtl),
        reg_def_used(div_def_addr, divisor_mreg, addr),
        reg_rtl(div_def_addr, divisor_mreg, divisor_rtl),
        reg_rtl(addr, Mreg::AX, quot_rtl),
        let args = Arc::new(vec![*ax_rtl, *divisor_rtl]);

    rtl_inst_candidate(synthetic_addr, RTLInst::Iop(Operation::Omodu, args.clone(), *rem_rtl)) <--
        pudiv(addr, _, divisor_sym),
        op_register(divisor_sym, divisor_reg_str),
        let divisor_mreg = Mreg::from(divisor_reg_str.to_string()),
        reg_def_used(ax_def_addr, Mreg::AX, addr),
        reg_rtl(ax_def_addr, Mreg::AX, ax_rtl),
        reg_def_used(div_def_addr, divisor_mreg, addr),
        reg_rtl(div_def_addr, divisor_mreg, divisor_rtl),
        reg_rtl(addr, Mreg::DX, rem_rtl),
        let synthetic_addr = *addr | (1u64 << 62),
        let args = Arc::new(vec![*ax_rtl, *divisor_rtl]);

    rtl_edge_negated(addr, next_addr) <--
        pdiv(addr, _, divisor_sym),
        op_register(divisor_sym, _),
        next(addr, next_addr);

    rtl_succ_candidate(addr, synthetic_addr), instr_in_function(synthetic_addr, func_start) <--
        pdiv(addr, _, divisor_sym),
        op_register(divisor_sym, _),
        instr_in_function(addr, func_start),
        let synthetic_addr = *addr | (1u64 << 62);

    rtl_succ_candidate(synthetic_addr, next_addr), instr_in_function(synthetic_addr, func_start) <--
        pdiv(addr, _, divisor_sym),
        op_register(divisor_sym, _),
        instr_in_function(addr, func_start),
        let synthetic_addr = *addr | (1u64 << 62),
        next(addr, next_addr);

    // Signed division (IDIV) with stack-based divisor
    rtl_inst_candidate(addr, RTLInst::Iop(Operation::Odiv, args.clone(), *quot_rtl)) <--
        pidiv(addr, _, divisor_sym),
        op_indirect(divisor_sym, reg1, reg2, reg3, mult, disp, sz),
        if reg2.ends_with("BP"),
        instr_in_function(addr, func_start),
        reg_def_used(ax_def_addr, Mreg::AX, addr),
        reg_rtl(ax_def_addr, Mreg::AX, ax_rtl),
        stack_var(func_start, addr, disp, divisor_rtl),
        reg_rtl(addr, Mreg::AX, quot_rtl),
        let args = Arc::new(vec![*ax_rtl, *divisor_rtl]);

    rtl_inst_candidate(synthetic_addr, RTLInst::Iop(Operation::Omod, args.clone(), *rem_rtl)) <--
        pidiv(addr, _, divisor_sym),
        op_indirect(divisor_sym, reg1, reg2, reg3, mult, disp, sz),
        if reg2.ends_with("BP"),
        instr_in_function(addr, func_start),
        reg_def_used(ax_def_addr, Mreg::AX, addr),
        reg_rtl(ax_def_addr, Mreg::AX, ax_rtl),
        stack_var(func_start, addr, disp, divisor_rtl),
        reg_rtl(addr, Mreg::DX, rem_rtl),
        let synthetic_addr = *addr | (1u64 << 62),
        let args = Arc::new(vec![*ax_rtl, *divisor_rtl]);

    // Unsigned division (DIV) with stack-based divisor
    rtl_inst_candidate(addr, RTLInst::Iop(Operation::Odivu, args.clone(), *quot_rtl)) <--
        pudiv(addr, _, divisor_sym),
        op_indirect(divisor_sym, reg1, reg2, reg3, mult, disp, sz),
        if reg2.ends_with("BP"),
        instr_in_function(addr, func_start),
        reg_def_used(ax_def_addr, Mreg::AX, addr),
        reg_rtl(ax_def_addr, Mreg::AX, ax_rtl),
        stack_var(func_start, addr, disp, divisor_rtl),
        reg_rtl(addr, Mreg::AX, quot_rtl),
        let args = Arc::new(vec![*ax_rtl, *divisor_rtl]);

    rtl_inst_candidate(synthetic_addr, RTLInst::Iop(Operation::Omodu, args.clone(), *rem_rtl)) <--
        pudiv(addr, _, divisor_sym),
        op_indirect(divisor_sym, reg1, reg2, reg3, mult, disp, sz),
        if reg2.ends_with("BP"),
        instr_in_function(addr, func_start),
        reg_def_used(ax_def_addr, Mreg::AX, addr),
        reg_rtl(ax_def_addr, Mreg::AX, ax_rtl),
        stack_var(func_start, addr, disp, divisor_rtl),
        reg_rtl(addr, Mreg::DX, rem_rtl),
        let synthetic_addr = *addr | (1u64 << 62),
        let args = Arc::new(vec![*ax_rtl, *divisor_rtl]);

    rtl_edge_negated(addr, next_addr) <--
        pdiv(addr, _, divisor_sym),
        op_indirect(divisor_sym, _, reg2, _, _, _, _),
        if reg2.ends_with("BP"),
        next(addr, next_addr);

    rtl_succ_candidate(addr, synthetic_addr), instr_in_function(synthetic_addr, func_start) <--
        pdiv(addr, _, divisor_sym),
        op_indirect(divisor_sym, _, reg2, _, _, _, _),
        if reg2.ends_with("BP"),
        instr_in_function(addr, func_start),
        let synthetic_addr = *addr | (1u64 << 62);

    rtl_succ_candidate(synthetic_addr, next_addr), instr_in_function(synthetic_addr, func_start) <--
        pdiv(addr, _, divisor_sym),
        op_indirect(divisor_sym, _, reg2, _, _, _, _),
        if reg2.ends_with("BP"),
        instr_in_function(addr, func_start),
        let synthetic_addr = *addr | (1u64 << 62),
        next(addr, next_addr);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lload(chunk, addressing, mregs, dst_reg)),
        if mregs.is_empty(),
        reg_rtl(addr, *dst_reg, dst_rtl),
        let inst = RTLInst::Iload(*chunk, addressing.clone(), Arc::new(vec![]), *dst_rtl);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lload(chunk, addressing, mregs, dst_reg)),
        if mregs.len() == 1,
        let arg_mreg = mregs[0],
        if arg_mreg != *dst_reg,
        reg_rtl(addr, *dst_reg, dst_rtl),
        reg_rtl(addr, arg_mreg, arg_rtl),
        let inst = RTLInst::Iload(*chunk, addressing.clone(), Arc::new(vec![*arg_rtl]), *dst_rtl);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lload(chunk, addressing, mregs, dst_reg)),
        if mregs.len() == 1,
        let arg_mreg = mregs[0],
        if arg_mreg == *dst_reg,
        is_def(addr, def_xtl),
        reg_xtl(addr, *dst_reg, def_xtl),
        xtl_canonical(def_xtl, dst_rtl),
        load_overwrite_use_id(addr, dst_reg, src_xtl),
        xtl_canonical(src_xtl, arg_rtl),
        let inst = RTLInst::Iload(*chunk, addressing.clone(), Arc::new(vec![*arg_rtl]), *dst_rtl);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lload(chunk, addressing, mregs, dst_reg)),
        if mregs.len() > 1,
        if *addressing != Addressing::Aindexed(0),
        !sp_indexed_load(addr),
        reg_rtl(addr, *dst_reg, dst_rtl),
        load_args_collected(addr, args),
        let inst = RTLInst::Iload(*chunk, addressing.clone(), args.clone(), *dst_rtl);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lload(chunk, addressing, mregs, dst_reg)),
        if mregs.len() > 1,
        if *addressing == Addressing::Aindexed(0),
        !sp_indexed_load(addr),
        reg_rtl(addr, *dst_reg, dst_rtl),
        reg_rtl(addr, mregs[0], base_rtl),
        let inst = RTLInst::Iload(*chunk, addressing.clone(), Arc::new(vec![*base_rtl]), *dst_rtl);

    // SP-indexed load: expand [SP, idx] to Olea(Ainstack(ofs)) + Iload(Aindexed2scaled(scale, 0)).
    rtl_inst_candidate(addr, lea_inst), op_produces_ptr(addr, sp_addr_rtl) <--
        ltl_inst(addr, ?LTLInst::Lload(_, addressing, mregs, _)),
        if mregs.len() == 2 && mregs[0] == Mreg::SP,
        if let Addressing::Aindexed2scaled(_, ofs) | Addressing::Aindexed2(ofs) = addressing,
        let sp_addr_rtl = fresh_xtl_reg(*addr, Mreg::SP) | FRESH_NS_SP_BASE,
        let lea_inst = RTLInst::Iop(Operation::Olea(Addressing::Ainstack(*ofs)), Arc::new(vec![]), sp_addr_rtl);

    rtl_inst_candidate(synth, load_inst) <--
        ltl_inst(addr, ?LTLInst::Lload(chunk, addressing, mregs, dst_reg)),
        if mregs.len() == 2 && mregs[0] == Mreg::SP,
        if let Addressing::Aindexed2scaled(scale, _) = addressing,
        reg_rtl(addr, *dst_reg, dst_rtl),
        reg_rtl(addr, mregs[1], idx_rtl),
        let sp_addr_rtl = fresh_xtl_reg(*addr, Mreg::SP) | FRESH_NS_SP_BASE,
        let synth = *addr | (1u64 << 62),
        let load_inst = RTLInst::Iload(*chunk, Addressing::Aindexed2scaled(*scale, 0), Arc::new(vec![sp_addr_rtl, *idx_rtl]), *dst_rtl);

    rtl_inst_candidate(synth, load_inst) <--
        ltl_inst(addr, ?LTLInst::Lload(chunk, addressing, mregs, dst_reg)),
        if mregs.len() == 2 && mregs[0] == Mreg::SP,
        if let Addressing::Aindexed2(ofs) = addressing,
        reg_rtl(addr, *dst_reg, dst_rtl),
        reg_rtl(addr, mregs[1], idx_rtl),
        let sp_addr_rtl = fresh_xtl_reg(*addr, Mreg::SP) | FRESH_NS_SP_BASE,
        let synth = *addr | (1u64 << 62),
        let load_inst = RTLInst::Iload(*chunk, Addressing::Aindexed2(0), Arc::new(vec![sp_addr_rtl, *idx_rtl]), *dst_rtl);

    // SP-indexed load: edge rewiring -- redirect addr's successors through the synthetic node
    rtl_edge_negated(addr, next) <--
        sp_indexed_load(addr),
        ltl_succ(addr, next);

    rtl_succ_candidate(addr, synth) <--
        sp_indexed_load(addr),
        let synth = *addr | (1u64 << 62);

    rtl_succ_candidate(synth, next), instr_in_function(synth, func_start) <--
        sp_indexed_load(addr),
        ltl_succ(addr, next),
        instr_in_function(addr, func_start),
        let synth = *addr | (1u64 << 62);

    // SP-indexed store: Aindexed2scaled/Aindexed2 with [SP, idx] -> expand similarly
    rtl_inst_candidate(addr, lea_inst), op_produces_ptr(addr, sp_addr_rtl) <--
        ltl_inst(addr, ?LTLInst::Lstore(_, addressing, mregs, _)),
        if mregs.len() == 2 && mregs[0] == Mreg::SP,
        if let Addressing::Aindexed2scaled(_, ofs) | Addressing::Aindexed2(ofs) = addressing,
        let sp_addr_rtl = fresh_xtl_reg(*addr, Mreg::SP) | FRESH_NS_SP_BASE,
        let lea_inst = RTLInst::Iop(Operation::Olea(Addressing::Ainstack(*ofs)), Arc::new(vec![]), sp_addr_rtl);

    rtl_inst_candidate(synth, store_inst) <--
        ltl_inst(addr, ?LTLInst::Lstore(chunk, addressing, mregs, src_reg)),
        if mregs.len() == 2 && mregs[0] == Mreg::SP,
        if let Addressing::Aindexed2scaled(scale, _) = addressing,
        reg_rtl(addr, *src_reg, src_rtl),
        reg_rtl(addr, mregs[1], idx_rtl),
        let sp_addr_rtl = fresh_xtl_reg(*addr, Mreg::SP) | FRESH_NS_SP_BASE,
        let synth = *addr | (1u64 << 62),
        let store_inst = RTLInst::Istore(*chunk, Addressing::Aindexed2scaled(*scale, 0), Arc::new(vec![sp_addr_rtl, *idx_rtl]), *src_rtl);

    rtl_inst_candidate(synth, store_inst) <--
        ltl_inst(addr, ?LTLInst::Lstore(chunk, addressing, mregs, src_reg)),
        if mregs.len() == 2 && mregs[0] == Mreg::SP,
        if let Addressing::Aindexed2(ofs) = addressing,
        reg_rtl(addr, *src_reg, src_rtl),
        reg_rtl(addr, mregs[1], idx_rtl),
        let sp_addr_rtl = fresh_xtl_reg(*addr, Mreg::SP) | FRESH_NS_SP_BASE,
        let synth = *addr | (1u64 << 62),
        let store_inst = RTLInst::Istore(*chunk, Addressing::Aindexed2(0), Arc::new(vec![sp_addr_rtl, *idx_rtl]), *src_rtl);

    // SP-indexed store: edge rewiring
    rtl_edge_negated(addr, next) <--
        sp_indexed_store(addr),
        ltl_succ(addr, next);

    rtl_succ_candidate(addr, synth) <--
        sp_indexed_store(addr),
        let synth = *addr | (1u64 << 62);

    rtl_succ_candidate(synth, next), instr_in_function(synth, func_start) <--
        sp_indexed_store(addr),
        ltl_succ(addr, next),
        instr_in_function(addr, func_start),
        let synth = *addr | (1u64 << 62);

    ltl_lstore_has_regvar(addr, src_reg, src_rtl) <--
        ltl_inst(addr, ?LTLInst::Lstore(_chunk, _addressing, _mregs, src_reg)),
        reg_xtl(addr, *src_reg, src_rtl);

    ltl_lstore_has_edge(addr, next_addr) <--
        ltl_inst(addr, ?LTLInst::Lstore(_chunk, _addressing, _mregs, _src_reg)),
        ltl_succ(addr, next_addr);


    temp_cmp_mreg_args(addr, pos, mreg) <--
        instruction(addr, _, mnem, dst, src, _, _, _, _, _),
        if mnem.starts_with("CMP"),
        op_indirect(dst, _, base_str, _, _, disp, _),
        let addrmode = Addrmode {
             base: Some(Ireg::from(base_str)),
             index: None,
             disp: Displacement::from(*disp), 
        },
        let res = transl_addressing_rev(addrmode, None),
        if res.is_ok(),
        let (_, mreg_vec) = res.unwrap(),
        for (pos, mreg) in mreg_vec.into_iter().enumerate();

    temp_cmp_mreg_args(addr, pos, mreg) <--
        instruction(addr, _, mnem, dst, src, _, _, _, _, _),
        if mnem.starts_with("CMP"),
        op_immediate(dst, _, _),
        op_indirect(src, _, base_str, _, _, disp, _),
        let addrmode = Addrmode {
             base: Some(Ireg::from(base_str)),
             index: None,
             disp: Displacement::from(*disp), 
        },
        let res = transl_addressing_rev(addrmode, None),
        if res.is_ok(),
        let (_, mreg_vec) = res.unwrap(),
        for (pos, mreg) in mreg_vec.into_iter().enumerate();

    temp_cmp_args_rtl(addr, pos, rtl_reg) <--
        temp_cmp_mreg_args(addr, pos, mreg),
        reg_rtl(addr, mreg, rtl_reg);

    ltl_inst_uses_mreg(addr, mreg) <--
        temp_cmp_mreg_args(addr, _, mreg);

    reg_rtl(next_addr, mreg, rtl_reg) <--
        instruction(addr, _, mnem, _, _, _, _, _, _, _),
        if mnem.starts_with("CMP"),
        next(addr, next_addr),
        reg_rtl(addr, mreg, rtl_reg);

    temp_cmp_reg(addr, fresh_reg) <--
        instruction(addr, _, mnem, dst, src, _, _, _, _, _),
        if mnem.starts_with("CMP"),
        op_indirect(dst, _, base_str, _, _, disp, _),
        op_immediate(src, _, _),
        let fresh_reg = fresh_xtl_reg(*addr, Mreg::from("RTEMP"));

    rtl_inst_candidate(addr, RTLInst::Iload(chunk, addressing.clone(), mreg_args, *fresh_reg)) <--
        instruction(addr, _, mnem, dst, src, _, _, _, _, _),
        if mnem.starts_with("CMP"),
        op_indirect(dst, _, base_str, _, _, disp, _),
        op_immediate(src, _, _),
        temp_cmp_reg(addr, fresh_reg),
        let addrmode = Addrmode {
             base: Some(Ireg::from(base_str)),
             index: None,
             disp: Displacement::from(*disp), 
        },
        let res = transl_addressing_rev(addrmode, None),
        if res.is_ok(),
        let (addressing, _) = res.unwrap(),
        agg mreg_args = build_call_args(pos, rtl_reg) in temp_cmp_args_rtl(addr, pos, rtl_reg),
        let chunk = if mnem.ends_with("L") { MemoryChunk::MInt32 } 
                   else if mnem.ends_with("Q") { MemoryChunk::MInt64 }
                   else { MemoryChunk::MInt32 };

    rtl_inst_candidate(*next_addr, RTLInst::Icond(cond, args.clone(), Either::Right(*target_addr), Either::Right(*next_addr))) <--
        instruction(addr, _, mnem, dst, src, _, _, _, _, _),
        if mnem.starts_with("CMP"),
        op_indirect(dst, _, _, _, _, _, _),
        op_immediate(src, imm_sym, _),
        let imm_val = *imm_sym as i64,
        next(addr, next_addr),
        pjcc(next_addr, test_cond, lbl),
        temp_cmp_reg(addr, fresh_reg),
        symbol_resolved_addr(*lbl, target_addr),
        instr_in_function(target_addr, target_func_start),
        instr_in_function(next_addr, my_func_start),
        if target_func_start == my_func_start,
        
        let cond = match test_cond {
             TestCond::CondG  => Condition::Ccompimm(Comparison::Cgt, imm_val),
             TestCond::CondL  => Condition::Ccompimm(Comparison::Clt, imm_val),
             TestCond::CondGe => Condition::Ccompimm(Comparison::Cge, imm_val),
             TestCond::CondLe => Condition::Ccompimm(Comparison::Cle, imm_val),
             TestCond::CondE  => Condition::Ccompimm(Comparison::Ceq, imm_val),
             TestCond::CondNe => Condition::Ccompimm(Comparison::Cne, imm_val),
             TestCond::CondA  => Condition::Ccompuimm(Comparison::Cgt, imm_val),
             TestCond::CondB  => Condition::Ccompuimm(Comparison::Clt, imm_val),
             TestCond::CondAe => Condition::Ccompuimm(Comparison::Cge, imm_val),
             TestCond::CondBe => Condition::Ccompuimm(Comparison::Cle, imm_val),
             _ => Condition::Ccomp(Comparison::Unknown) 
        },
        let args = Arc::new(vec![*fresh_reg]);

    temp_cmp_reg(addr, fresh_reg) <--
        instruction(addr, _, mnem, dst, src, _, _, _, _, _),
        if mnem.starts_with("CMP"),
        op_immediate(dst, _, _),
        op_indirect(src, _, base_str, _, _, disp, _),
        let fresh_reg = fresh_xtl_reg(*addr, Mreg::from("RTEMP"));

    rtl_inst_candidate(addr, RTLInst::Iload(chunk, addressing.clone(), mreg_args, *fresh_reg)) <--
        instruction(addr, _, mnem, dst, src, _, _, _, _, _),
        if mnem.starts_with("CMP"),
        op_immediate(dst, _, _),
        op_indirect(src, _, base_str, _, _, disp, _),
        temp_cmp_reg(addr, fresh_reg),
        let addrmode = Addrmode {
             base: Some(Ireg::from(base_str)),
             index: None,
             disp: Displacement::from(*disp), 
        },
        let res = transl_addressing_rev(addrmode, None),
        if res.is_ok(),
        let (addressing, _) = res.unwrap(),
        agg mreg_args = build_call_args(pos, rtl_reg) in temp_cmp_args_rtl(addr, pos, rtl_reg),
        let chunk = if mnem.ends_with("L") { MemoryChunk::MInt32 } 
                   else if mnem.ends_with("Q") { MemoryChunk::MInt64 }
                   else { MemoryChunk::MInt32 };

    rtl_inst_candidate(*next_addr, RTLInst::Icond(cond, args.clone(), Either::Right(*target_addr), Either::Right(*next_addr))) <--
        instruction(addr, _, mnem, dst, src, _, _, _, _, _),
        if mnem.starts_with("CMP"),
        op_immediate(dst, imm_sym, _),
        op_indirect(src, _, _, _, _, _, _),
        let imm_val = *imm_sym as i64,
        next(addr, next_addr),
        pjcc(next_addr, test_cond, lbl),
        temp_cmp_reg(addr, fresh_reg),
        symbol_resolved_addr(*lbl, target_addr),
        instr_in_function(target_addr, target_func_start),
        instr_in_function(next_addr, my_func_start),
        if target_func_start == my_func_start,

        let cond = match test_cond {
             TestCond::CondG  => Condition::Ccompimm(Comparison::Clt, imm_val),
             TestCond::CondL  => Condition::Ccompimm(Comparison::Cgt, imm_val),
             TestCond::CondGe => Condition::Ccompimm(Comparison::Cle, imm_val),
             TestCond::CondLe => Condition::Ccompimm(Comparison::Cge, imm_val),
             TestCond::CondE  => Condition::Ccompimm(Comparison::Ceq, imm_val),
             TestCond::CondNe => Condition::Ccompimm(Comparison::Cne, imm_val),
             TestCond::CondA  => Condition::Ccompuimm(Comparison::Clt, imm_val), 
             TestCond::CondB  => Condition::Ccompuimm(Comparison::Cgt, imm_val),
             TestCond::CondAe => Condition::Ccompuimm(Comparison::Cle, imm_val),
             TestCond::CondBe => Condition::Ccompuimm(Comparison::Cge, imm_val),
             _ => Condition::Ccomp(Comparison::Unknown) 
        },
        let args = Arc::new(vec![*fresh_reg]);

    rtl_inst_candidate(*jcc_addr, RTLInst::Icond(cond, args.clone(), Either::Right(*target_addr), Either::Right(*fallthrough))) <--
        instruction(addr, _, mnem, dst, src, _, _, _, _, _),
        if mnem.starts_with("CMP"),
        op_immediate(dst, imm_sym, _),
        op_indirect(src, _, _, _, _, _, _),
        let imm_val = *imm_sym as i64,
        flags_and_jump_pair(addr, jcc_addr, _),
        pjcc(jcc_addr, test_cond, lbl),
        temp_cmp_reg(addr, fresh_reg),
        symbol_resolved_addr(*lbl, target_addr),
        instr_in_function(target_addr, target_func_start),
        instr_in_function(jcc_addr, my_func_start),
        if target_func_start == my_func_start,
        next(jcc_addr, fallthrough),
        let cond = match test_cond {
             TestCond::CondG  => Condition::Ccompimm(Comparison::Clt, imm_val),
             TestCond::CondL  => Condition::Ccompimm(Comparison::Cgt, imm_val),
             TestCond::CondGe => Condition::Ccompimm(Comparison::Cle, imm_val),
             TestCond::CondLe => Condition::Ccompimm(Comparison::Cge, imm_val),
             TestCond::CondE  => Condition::Ccompimm(Comparison::Ceq, imm_val),
             TestCond::CondNe => Condition::Ccompimm(Comparison::Cne, imm_val),
             TestCond::CondA  => Condition::Ccompuimm(Comparison::Clt, imm_val),
             TestCond::CondB  => Condition::Ccompuimm(Comparison::Cgt, imm_val),
             TestCond::CondAe => Condition::Ccompuimm(Comparison::Cle, imm_val),
             TestCond::CondBe => Condition::Ccompuimm(Comparison::Cge, imm_val),
             _ => Condition::Ccomp(Comparison::Unknown)
        },
        let args = Arc::new(vec![*fresh_reg]);

    temp_cmp_reg(addr, fresh_reg) <--
        pcmp(addr, r1, r2),
        op_register(r1, _),
        op_indirect(r2, _, _, _, _, _, _),
        let fresh_reg = fresh_xtl_reg(*addr, Mreg::from("RTEMP"));

    temp_cmp_mreg_args(addr, pos, mreg) <--
        pcmp(addr, r1, r2),
        op_register(r1, _),
        op_indirect(r2, _, base_str, _, _, disp, _),
        let addrmode = Addrmode {
             base: Some(Ireg::from(base_str)),
             index: None,
             disp: Displacement::from(*disp),
        },
        let res = transl_addressing_rev(addrmode, None),
        if res.is_ok(),
        let (_, mreg_vec) = res.unwrap(),
        for (pos, mreg) in mreg_vec.into_iter().enumerate();

    rtl_inst_candidate(addr, RTLInst::Iload(chunk, addressing.clone(), mreg_args, *fresh_reg)) <--
        pcmp(addr, r1, r2),
        op_register(r1, _),
        op_indirect(r2, _, base_str, _, _, disp, sz),
        temp_cmp_reg(addr, fresh_reg),
        let addrmode = Addrmode {
             base: Some(Ireg::from(base_str)),
             index: None,
             disp: Displacement::from(*disp),
        },
        let res = transl_addressing_rev(addrmode, None),
        if res.is_ok(),
        let (addressing, _) = res.unwrap(),
        agg mreg_args = build_call_args(pos, rtl_reg) in temp_cmp_args_rtl(addr, pos, rtl_reg),
        let chunk = match *sz { 1 => MemoryChunk::MInt8Unsigned, 2 => MemoryChunk::MInt16Unsigned, 8 => MemoryChunk::MInt64, _ => MemoryChunk::MInt32 };

    rtl_inst_candidate(*jcc_addr, RTLInst::Icond(cond, Arc::new(vec![*reg_rtl, *fresh_reg]), Either::Right(*target_addr), Either::Right(*fallthrough))) <--
        pcmp(addr, r1, r2),
        op_register(r1, reg_str),
        op_indirect(r2, _, _, _, _, _, _),
        temp_cmp_reg(addr, fresh_reg),
        let mreg = Mreg::from(reg_str),
        reg_rtl(addr, mreg, reg_rtl),
        next(addr, jcc_addr),
        pjcc(jcc_addr, test_cond, lbl),
        symbol_resolved_addr(*lbl, target_addr),
        instr_in_function(target_addr, target_func_start),
        instr_in_function(jcc_addr, my_func_start),
        if target_func_start == my_func_start,
        next(jcc_addr, fallthrough),
        let cond = condition_for_testcond(*test_cond);

    rtl_inst_candidate(*jcc_addr, RTLInst::Icond(cond, Arc::new(vec![*reg_rtl, *fresh_reg]), Either::Right(*target_addr), Either::Right(*fallthrough))) <--
        pcmp(addr, r1, r2),
        op_register(r1, reg_str),
        op_indirect(r2, _, _, _, _, _, _),
        temp_cmp_reg(addr, fresh_reg),
        let mreg = Mreg::from(reg_str),
        reg_rtl(addr, mreg, reg_rtl),
        flags_and_jump_pair(addr, jcc_addr, _),
        pjcc(jcc_addr, test_cond, lbl),
        symbol_resolved_addr(*lbl, target_addr),
        instr_in_function(target_addr, target_func_start),
        instr_in_function(jcc_addr, my_func_start),
        if target_func_start == my_func_start,
        next(jcc_addr, fallthrough),
        let cond = condition_for_testcond(*test_cond);

    temp_cmp_reg(addr, fresh_reg) <--
        pcmp(addr, r1, r2),
        op_indirect(r1, _, _, _, _, _, _),
        op_register(r2, _),
        let fresh_reg = fresh_xtl_reg(*addr, Mreg::from("RTEMP"));

    temp_cmp_mreg_args(addr, pos, mreg) <--
        pcmp(addr, r1, r2),
        op_indirect(r1, _, base_str, _, _, disp, _),
        op_register(r2, _),
        let addrmode = Addrmode {
             base: Some(Ireg::from(base_str)),
             index: None,
             disp: Displacement::from(*disp),
        },
        let res = transl_addressing_rev(addrmode, None),
        if res.is_ok(),
        let (_, mreg_vec) = res.unwrap(),
        for (pos, mreg) in mreg_vec.into_iter().enumerate();

    rtl_inst_candidate(addr, RTLInst::Iload(chunk, addressing.clone(), mreg_args, *fresh_reg)) <--
        pcmp(addr, r1, r2),
        op_indirect(r1, _, base_str, _, _, disp, sz),
        op_register(r2, _),
        temp_cmp_reg(addr, fresh_reg),
        let addrmode = Addrmode {
             base: Some(Ireg::from(base_str)),
             index: None,
             disp: Displacement::from(*disp),
        },
        let res = transl_addressing_rev(addrmode, None),
        if res.is_ok(),
        let (addressing, _) = res.unwrap(),
        agg mreg_args = build_call_args(pos, rtl_reg) in temp_cmp_args_rtl(addr, pos, rtl_reg),
        let chunk = match *sz { 1 => MemoryChunk::MInt8Unsigned, 2 => MemoryChunk::MInt16Unsigned, 8 => MemoryChunk::MInt64, _ => MemoryChunk::MInt32 };

    rtl_inst_candidate(*jcc_addr, RTLInst::Icond(cond, Arc::new(vec![*fresh_reg, *reg_rtl]), Either::Right(*target_addr), Either::Right(*fallthrough))) <--
        pcmp(addr, r1, r2),
        op_indirect(r1, _, _, _, _, _, _),
        op_register(r2, reg_str),
        temp_cmp_reg(addr, fresh_reg),
        let mreg = Mreg::from(reg_str),
        reg_rtl(addr, mreg, reg_rtl),
        next(addr, jcc_addr),
        pjcc(jcc_addr, test_cond, lbl),
        symbol_resolved_addr(*lbl, target_addr),
        instr_in_function(target_addr, target_func_start),
        instr_in_function(jcc_addr, my_func_start),
        if target_func_start == my_func_start,
        next(jcc_addr, fallthrough),
        let cond = condition_for_testcond(*test_cond);

    rtl_inst_candidate(*jcc_addr, RTLInst::Icond(cond, Arc::new(vec![*fresh_reg, *reg_rtl]), Either::Right(*target_addr), Either::Right(*fallthrough))) <--
        pcmp(addr, r1, r2),
        op_indirect(r1, _, _, _, _, _, _),
        op_register(r2, reg_str),
        temp_cmp_reg(addr, fresh_reg),
        let mreg = Mreg::from(reg_str),
        reg_rtl(addr, mreg, reg_rtl),
        flags_and_jump_pair(addr, jcc_addr, _),
        pjcc(jcc_addr, test_cond, lbl),
        symbol_resolved_addr(*lbl, target_addr),
        instr_in_function(target_addr, target_func_start),
        instr_in_function(jcc_addr, my_func_start),
        if target_func_start == my_func_start,
        next(jcc_addr, fallthrough),
        let cond = condition_for_testcond(*test_cond);

    rtl_inst_candidate(*jcc_addr, RTLInst::Icond(cond, args.clone(), Either::Right(*target_addr), Either::Right(*fallthrough))) <--
        instruction(addr, _, mnem, dst, src, _, _, _, _, _),
        if mnem.starts_with("CMP"),
        op_indirect(dst, _, _, _, _, _, _),
        op_immediate(src, imm_sym, _),
        let imm_val = *imm_sym as i64,
        flags_and_jump_pair(addr, jcc_addr, _),
        pjcc(jcc_addr, test_cond, lbl),
        temp_cmp_reg(addr, fresh_reg),
        symbol_resolved_addr(*lbl, target_addr),
        instr_in_function(target_addr, target_func_start),
        instr_in_function(jcc_addr, my_func_start),
        if target_func_start == my_func_start,
        next(jcc_addr, fallthrough),
        let cond = match test_cond {
             TestCond::CondG  => Condition::Ccompimm(Comparison::Cgt, imm_val),
             TestCond::CondL  => Condition::Ccompimm(Comparison::Clt, imm_val),
             TestCond::CondGe => Condition::Ccompimm(Comparison::Cge, imm_val),
             TestCond::CondLe => Condition::Ccompimm(Comparison::Cle, imm_val),
             TestCond::CondE  => Condition::Ccompimm(Comparison::Ceq, imm_val),
             TestCond::CondNe => Condition::Ccompimm(Comparison::Cne, imm_val),
             TestCond::CondA  => Condition::Ccompuimm(Comparison::Cgt, imm_val),
             TestCond::CondB  => Condition::Ccompuimm(Comparison::Clt, imm_val),
             TestCond::CondAe => Condition::Ccompuimm(Comparison::Cge, imm_val),
             TestCond::CondBe => Condition::Ccompuimm(Comparison::Cle, imm_val),
             _ => Condition::Ccomp(Comparison::Unknown)
        },
        let args = Arc::new(vec![*fresh_reg]);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lstore(chunk, addressing, mregs, src_reg)),
        if !mregs.is_empty(),
        !sp_indexed_store(addr),
        reg_rtl(addr, *src_reg, src_rtl),
        store_args_collected(addr, args),
        let inst = RTLInst::Istore(*chunk, addressing.clone(), args.clone(), *src_rtl);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lstore(chunk, addressing, mregs, src_reg)),
        if mregs.is_empty(),
        reg_rtl(addr, *src_reg, src_rtl),
        let inst = RTLInst::Istore(*chunk, addressing.clone(), Arc::new(vec![]), *src_rtl);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lcall(callee)),
        if let Either::Left(mreg) = callee,
        reg_rtl(addr, *mreg, callee_rtl),
        call_args_collected_candidate(addr, args),
        call_return_reg(addr, _ret_rtl),
        reg_rtl(addr, Mreg::AX, final_ret),
        next(addr, next_addr),
        let inferred_sig = crate::decompile::passes::rtl_pass::infer_signature_from_args(&args, true),
        let inst = RTLInst::Icall(Some(inferred_sig), Either::Left(*callee_rtl), args.clone(), Some(*final_ret), *next_addr);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lcall(callee)),
        if let Either::Left(mreg) = callee,
        reg_rtl(addr, *mreg, callee_rtl),
        call_args_collected_candidate(addr, args),
        !call_return_reg(addr, _),
        next(addr, next_addr),
        let inferred_sig = crate::decompile::passes::rtl_pass::infer_signature_from_args(&args, false),
        let inst = RTLInst::Icall(Some(inferred_sig), Either::Left(*callee_rtl), args.clone(), None, *next_addr);

    // Fallback: indirect Lcall with missing reg_rtl; create fresh RTL reg for callee target.
    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lcall(callee)),
        if let Either::Left(mreg) = callee,
        !reg_rtl(addr, *mreg, _),
        call_args_collected_candidate(addr, args),
        call_return_reg(addr, _ret_rtl),
        reg_rtl(addr, Mreg::AX, final_ret),
        next(addr, next_addr),
        let fresh_callee = fresh_xtl_reg(*addr, *mreg),
        let inferred_sig = crate::decompile::passes::rtl_pass::infer_signature_from_args(&args, true),
        let inst = RTLInst::Icall(Some(inferred_sig), Either::Left(fresh_callee), args.clone(), Some(*final_ret), *next_addr);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lcall(callee)),
        if let Either::Left(mreg) = callee,
        !reg_rtl(addr, *mreg, _),
        call_args_collected_candidate(addr, args),
        !call_return_reg(addr, _),
        next(addr, next_addr),
        let fresh_callee = fresh_xtl_reg(*addr, *mreg),
        let inferred_sig = crate::decompile::passes::rtl_pass::infer_signature_from_args(&args, false),
        let inst = RTLInst::Icall(Some(inferred_sig), Either::Left(fresh_callee), args.clone(), None, *next_addr);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Left(target_addr) = target,
        call_args_collected_candidate(addr, args),
        call_return_reg(addr, _ret_rtl),
        reg_rtl(addr, Mreg::AX, final_ret),
        next(addr, next_addr),
        emit_function_signature_candidate(target_addr, sig),
        let inst = RTLInst::Icall(Some(sig.clone()), Either::Right(target.clone()), args.clone(), Some(*final_ret), *next_addr);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Left(target_addr) = target,
        call_args_collected_candidate(addr, args),
        !call_return_reg(addr, _),
        next(addr, next_addr),
        emit_function_signature_candidate(target_addr, sig),
        let inst = RTLInst::Icall(Some(sig.clone()), Either::Right(target.clone()), args.clone(), None, *next_addr);


    reg_xtl(call_addr, x0, ret_rtl), call_return_reg(call_addr, ret_rtl) <--
        ltl_inst(call_addr, ?LTLInst::Lcall(_)),
        next(call_addr, next_addr),
        let x0 = Mreg::X0,
        ltl_inst_uses_mreg(next_addr, x0),
        !call_returns_value(call_addr, _),
        let ret_rtl = fresh_xtl_reg(*call_addr, x0);

    reg_xtl(call_addr, mreg, ret_rtl), call_return_reg(call_addr, ret_rtl) <--
        call_has_known_signature(call_addr, _name, _count, ret_type),
        if *ret_type != XType::Xvoid,
        !call_returns_value(call_addr, _),
        let mreg = if matches!(ret_type, XType::Xfloat | XType::Xsingle) {
            Mreg::X0
        } else {
            Mreg::AX
        },
        let ret_rtl = fresh_xtl_reg(*call_addr, mreg);

    reg_def_site(addr, *dst) <--
        ltl_inst(addr, ?LTLInst::Lload(_, _, _, dst));

    reg_def_site(addr, *dst) <--
        ltl_inst(addr, ?LTLInst::Lgetstack(_, _, _, dst));

    reg_def_site(addr, *dst) <--
        ltl_inst(addr, ?LTLInst::Lop(_, _, dst));

    reg_def_site(*addr, *mreg) <--
        reg_def(addr, mreg),
        if *mreg != Mreg::SP,
        !ltl_inst(addr, _),
        !trim_instruction(addr);


    reg_def_site(*call_addr, *reg) <--
        ltl_inst(call_addr, ?LTLInst::Lcall(_)),
        is_caller_saved(reg),
        reg_def_used(*call_addr, *reg, _);


    return_val_used(*call_addr, 0u64, Mreg::AX, *use_addr, 0i64) <--
        ltl_inst(call_addr, ?LTLInst::Lcall(_)),
        reg_def_used(*call_addr, Mreg::AX, use_addr),
        instr_in_function(call_addr, func_start),
        instr_in_function(use_addr, func_start);

    call_returns_value(*call_addr, Mreg::AX) <--
        ltl_inst(call_addr, ?LTLInst::Lcall(_)),
        reg_def_used(*call_addr, Mreg::AX, use_addr),
        instr_in_function(call_addr, func_start),
        instr_in_function(use_addr, func_start);

    // XMM0 return value detection for float-returning functions
    call_returns_value(*call_addr, Mreg::X0) <--
        ltl_inst(call_addr, ?LTLInst::Lcall(_)),
        reg_def_used(*call_addr, Mreg::X0, use_addr),
        instr_in_function(call_addr, func_start),
        instr_in_function(use_addr, func_start);

    reg_xtl(call_addr, mreg, ret_rtl), call_return_reg(call_addr, ret_rtl) <--
        call_returns_value(call_addr, mreg),
        let ret_rtl = fresh_xtl_reg(*call_addr, *mreg);

    reg_xtl(addr, mreg, id), is_def(addr, id) <--
        reg_def_site(addr, mreg),
        let id = fresh_xtl_reg(*addr, *mreg);
    
    // Lbranch addresses reg_def butno ltl op
    reg_def_site(*addr, *mreg) <--
        arith_load_op(addr, _, _, _, _, _),
        !has_ltl_op(addr),
        reg_def(addr, mreg),
        if *mreg != Mreg::SP,
        !trim_instruction(addr);

    reg_def_site(*addr, *mreg) <--
        arith_store_reg(addr, _, _, _, _, _),
        !has_ltl_op(addr),
        reg_def(addr, mreg),
        if *mreg != Mreg::SP,
        !trim_instruction(addr);

    reg_def_site(*addr, *mreg) <--
        arith_store_imm(addr, _, _, _, _),
        !has_ltl_op(addr),
        reg_def(addr, mreg),
        if *mreg != Mreg::SP,
        !trim_instruction(addr);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Ltailcall(callee)),
        if let Either::Left(mreg) = callee,
        reg_rtl(addr, *mreg, callee_rtl),
        call_args_collected_candidate(addr, args),
        let default_sig = Signature { sig_args: Arc::new(vec![]), sig_res: XType::Xint, sig_cc: CallConv::default() },
        let inst = RTLInst::Itailcall(Some(default_sig), Either::Left(*callee_rtl), args.clone());

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Ltailcall(callee)),
        if let Either::Left(mreg) = callee,
        reg_rtl(addr, *mreg, callee_rtl),
        !call_args_collected_candidate(addr, _),
        let default_sig = Signature { sig_args: Arc::new(vec![]), sig_res: XType::Xint, sig_cc: CallConv::default() },
        let inst = RTLInst::Itailcall(Some(default_sig), Either::Left(*callee_rtl), Arc::new(vec![]));

    // Fallback: indirect Ltailcall with missing reg_rtl (mirrors Lcall fallback above).
    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Ltailcall(callee)),
        if let Either::Left(mreg) = callee,
        !reg_rtl(addr, *mreg, _),
        call_args_collected_candidate(addr, args),
        let fresh_callee = fresh_xtl_reg(*addr, *mreg),
        let inferred_sig = crate::decompile::passes::rtl_pass::infer_signature_from_args(&args, true),
        let inst = RTLInst::Itailcall(Some(inferred_sig), Either::Left(fresh_callee), args.clone());

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Ltailcall(callee)),
        if let Either::Left(mreg) = callee,
        !reg_rtl(addr, *mreg, _),
        !call_args_collected_candidate(addr, _),
        let fresh_callee = fresh_xtl_reg(*addr, *mreg),
        let default_sig = Signature { sig_args: Arc::new(vec![]), sig_res: XType::Xint, sig_cc: CallConv::default() },
        let inst = RTLInst::Itailcall(Some(default_sig), Either::Left(fresh_callee), Arc::new(vec![]));

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Ltailcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Left(target_addr) = target,
        call_args_collected_candidate(addr, args),
        emit_function_signature_candidate(target_addr, sig),
        let inst = RTLInst::Itailcall(Some(sig.clone()), Either::Right(target.clone()), args.clone());

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Ltailcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Left(target_addr) = target,
        !call_args_collected_candidate(addr, _),
        emit_function_signature_candidate(target_addr, sig),
        let inst = RTLInst::Itailcall(Some(sig.clone()), Either::Right(target.clone()), Arc::new(vec![]));

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Ltailcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Right(symbol) = target,
        call_args_collected_candidate(addr, args),
        known_extern_signature(symbol, _, ret_type, known_params),
        let sig = Signature { sig_args: known_params.clone(), sig_res: *ret_type, sig_cc: CallConv::default() },
        let inst = RTLInst::Itailcall(Some(sig), Either::Right(target.clone()), args.clone());

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Ltailcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Right(symbol) = target,
        call_args_collected_candidate(addr, args),
        !known_extern_signature(symbol, _, _, _),
        let inferred_sig = crate::decompile::passes::rtl_pass::infer_signature_from_args(&args, true),
        let inst = RTLInst::Itailcall(Some(inferred_sig), Either::Right(target.clone()), args.clone());

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Ltailcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Right(symbol) = target,
        !call_args_collected_candidate(addr, _),
        known_extern_signature(symbol, _, ret_type, _known_params),
        let sig = Signature { sig_args: Arc::new(vec![]), sig_res: *ret_type, sig_cc: CallConv::default() },
        let inst = RTLInst::Itailcall(Some(sig), Either::Right(target.clone()), Arc::new(vec![]));

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Ltailcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Right(symbol) = target,
        !call_args_collected_candidate(addr, _),
        !known_extern_signature(symbol, _, _, _),
        let default_sig = Signature { sig_args: Arc::new(vec![]), sig_res: XType::Xint, sig_cc: CallConv::default() },
        let inst = RTLInst::Itailcall(Some(default_sig), Either::Right(target.clone()), Arc::new(vec![]));

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Ltailcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Left(target_addr) = target,
        call_args_collected_candidate(addr, args),
        !emit_function_signature_candidate(target_addr, _),
        let inferred_sig = crate::decompile::passes::rtl_pass::infer_signature_from_args(&args, true),
        let inst = RTLInst::Itailcall(Some(inferred_sig), Either::Right(target.clone()), args.clone());

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Ltailcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Left(target_addr) = target,
        !call_args_collected_candidate(addr, _),
        !emit_function_signature_candidate(target_addr, _),
        let default_sig = Signature { sig_args: Arc::new(vec![]), sig_res: XType::Xint, sig_cc: CallConv::default() },
        let inst = RTLInst::Itailcall(Some(default_sig), Either::Right(target.clone()), Arc::new(vec![]));


    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Left(target_addr) = target,
        call_args_collected_candidate(addr, args),
        call_return_reg(addr, _ret_rtl),
        reg_rtl(addr, Mreg::AX, final_ret),
        next(addr, next_addr),
        !emit_function_signature_candidate(target_addr, _),
        let inferred_sig = crate::decompile::passes::rtl_pass::infer_signature_from_args(&args, true),
        let inst = RTLInst::Icall(Some(inferred_sig), Either::Right(target.clone()), args.clone(), Some(*final_ret), *next_addr);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Left(target_addr) = target,
        call_args_collected_candidate(addr, args),
        !call_return_reg(addr, _),
        next(addr, next_addr),
        !emit_function_signature_candidate(target_addr, _),
        let inferred_sig = crate::decompile::passes::rtl_pass::infer_signature_from_args(&args, false),
        let inst = RTLInst::Icall(Some(inferred_sig), Either::Right(target.clone()), args.clone(), None, *next_addr);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Right(symbol) = target,
        call_args_collected_candidate(addr, args),
        call_return_reg(addr, _ret_rtl),
        reg_rtl(addr, Mreg::AX, final_ret),
        next(addr, next_addr),
        known_extern_signature(symbol, _, ret_type, known_params),
        let sig = Signature { sig_args: known_params.clone(), sig_res: *ret_type, sig_cc: CallConv::default() },
        let inst = RTLInst::Icall(Some(sig), Either::Right(target.clone()), args.clone(), Some(*final_ret), *next_addr);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Right(symbol) = target,
        call_args_collected_candidate(addr, args),
        call_return_reg(addr, _ret_rtl),
        reg_rtl(addr, Mreg::AX, final_ret),
        next(addr, next_addr),
        !known_extern_signature(symbol, _, _, _),
        let inferred_sig = crate::decompile::passes::rtl_pass::infer_signature_from_args(&args, true),
        let inst = RTLInst::Icall(Some(inferred_sig), Either::Right(target.clone()), args.clone(), Some(*final_ret), *next_addr);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Right(symbol) = target,
        !call_return_reg(addr, _),
        call_args_collected_candidate(addr, args),
        next(addr, next_addr),
        known_extern_signature(symbol, _, _, known_params),
        let sig = Signature { sig_args: known_params.clone(), sig_res: XType::Xvoid, sig_cc: CallConv::default() },
        let inst = RTLInst::Icall(Some(sig), Either::Right(target.clone()), args.clone(), None, *next_addr);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lcall(callee)),
        if let Either::Right(target) = callee,
        if let Either::Right(symbol) = target,
        !call_return_reg(addr, _),
        call_args_collected_candidate(addr, args),
        next(addr, next_addr),
        !known_extern_signature(symbol, _, _, _),
        let inferred_sig = crate::decompile::passes::rtl_pass::infer_signature_from_args(&args, false),
        let inst = RTLInst::Icall(Some(inferred_sig), Either::Right(target.clone()), args.clone(), None, *next_addr);

    ltl_builtin_unconverted(addr, name_sym, Arc::new(args.clone()), result.clone()) <--
        ltl_inst(addr, ?LTLInst::Lbuiltin(name, args, result)),
        let name_sym = Box::leak(name.clone().into_boxed_str()) as Symbol;


    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lbranch(target)),
        let inst = RTLInst::Ibranch(target.clone());

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lcond(cond, mregs, target_true, target_false)),
        if mregs.len() > 0,
        cond_args_collected(addr, args),
        let inst = RTLInst::Icond(cond.clone(), args.clone(), target_true.clone(), target_false.clone());

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lcond(cond, mregs, target_true, target_false)),
        if mregs.is_empty(),
        let inst = RTLInst::Icond(cond.clone(), Arc::new(vec![]), target_true.clone(), target_false.clone());

    rtl_inst_candidate(addr, inst) <--
        pcmp(addr, sym1, sym2),
        op_register(sym1, reg_str),
        let reg1 = Mreg::from(reg_str.to_string()),
        op_indirect(sym2, reg_1, reg_2, reg_3, mult, disp, sz),
        if reg_2.ends_with("BP"),
        instr_in_function(addr, func_start),
        next(addr, jcc_addr),
        pjcc(jcc_addr, testcond, target_sym),
        symbol_resolved_addr(*target_sym, target_addr),
        next(jcc_addr, fallthrough),
        let raw_cond = crate::x86::types::condition_for_testcond(*testcond),
        let cond = crate::decompile::passes::rtl_pass::adjust_condition_size(raw_cond, *sz),
        stack_var(func_start, addr, *disp, arg_rtl),
        reg_rtl(addr, reg1, reg_rtl2),
        let inst = RTLInst::Icond(cond, Arc::new(vec![*reg_rtl2, *arg_rtl]), Either::Right(*target_addr), Either::Right(*fallthrough));

    rtl_inst_candidate(addr, inst) <--
        pcmp(addr, sym1, sym2),
        op_indirect(sym1, reg_1, reg_2, reg_3, mult, disp, sz),
        if reg_2.ends_with("BP"),
        op_register(sym2, reg_str),
        let reg1 = Mreg::from(reg_str.to_string()),
        instr_in_function(addr, func_start),
        next(addr, jcc_addr),
        pjcc(jcc_addr, testcond, target_sym),
        symbol_resolved_addr(*target_sym, target_addr),
        next(jcc_addr, fallthrough),
        let raw_cond = crate::x86::types::condition_for_testcond(*testcond),
        let cond = crate::decompile::passes::rtl_pass::adjust_condition_size(raw_cond, *sz),
        stack_var(func_start, addr, *disp, arg_rtl),
        reg_rtl(addr, reg1, reg_rtl2),
        let inst = RTLInst::Icond(cond, Arc::new(vec![*arg_rtl, *reg_rtl2]), Either::Right(*target_addr), Either::Right(*fallthrough));

    rtl_inst_candidate(addr, inst) <--
        pcmp(addr, sym1, sym2),
        op_indirect(sym1, reg_1a, reg_2a, reg_3a, mult_a, disp_a, sz_a),
        if reg_2a.ends_with("BP"),
        op_indirect(sym2, reg_1, reg_2, reg_3, mult, disp, sz),
        if reg_2.ends_with("BP"),
        instr_in_function(addr, func_start),
        next(addr, jcc_addr),
        pjcc(jcc_addr, testcond, target_sym),
        symbol_resolved_addr(*target_sym, target_addr),
        next(jcc_addr, fallthrough),
        let raw_cond = crate::x86::types::condition_for_testcond(*testcond),
        let cond = crate::decompile::passes::rtl_pass::adjust_condition_size(raw_cond, *sz),
        stack_var(func_start, addr, *disp_a, arg_rtl1),
        stack_var(func_start, addr, *disp, arg_rtl2),
        let inst = RTLInst::Icond(cond, Arc::new(vec![*arg_rtl1, *arg_rtl2]), Either::Right(*target_addr), Either::Right(*fallthrough));

    rtl_inst_candidate(addr, inst) <--
        pcmp(addr, sym1, sym2),
        op_indirect(sym1, reg_1, reg_2, reg_3, mult, disp, sz),
        if reg_2.ends_with("BP"),
        op_immediate(sym2, imm_val, _),
        instr_in_function(addr, func_start),
        next(addr, jcc_addr),
        pjcc(jcc_addr, testcond, target_sym),
        symbol_resolved_addr(*target_sym, target_addr),
        next(jcc_addr, fallthrough),
        let raw_cond = crate::x86::types::condition_for_testcond(*testcond),
        let sized_cond = crate::decompile::passes::rtl_pass::adjust_condition_size(raw_cond, *sz),
        let cond_with_imm = match sized_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, *imm_val),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, *imm_val),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, *imm_val),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, *imm_val),
            _ => sized_cond.clone(),
        },
        stack_var(func_start, addr, *disp, arg_rtl),
        let inst = RTLInst::Icond(cond_with_imm, Arc::new(vec![*arg_rtl]), Either::Right(*target_addr), Either::Right(*fallthrough));

    rtl_inst_candidate(addr, inst) <--
        pcmp(addr, sym1, sym2),
        op_immediate(sym1, imm_val, _),
        op_indirect(sym2, reg_1, reg_2, reg_3, mult, disp, sz),
        if reg_2.ends_with("BP"),
        instr_in_function(addr, func_start),
        next(addr, jcc_addr),
        pjcc(jcc_addr, testcond, target_sym),
        symbol_resolved_addr(*target_sym, target_addr),
        next(jcc_addr, fallthrough),
        let raw_cond = crate::x86::types::condition_for_testcond(*testcond),
        let sized_cond = crate::decompile::passes::rtl_pass::adjust_condition_size(raw_cond, *sz),
        let cond_with_imm = match sized_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, *imm_val),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, *imm_val),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, *imm_val),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, *imm_val),
            _ => sized_cond.clone(),
        },
        stack_var(func_start, addr, *disp, arg_rtl),
        let inst = RTLInst::Icond(cond_with_imm, Arc::new(vec![*arg_rtl]), Either::Right(*target_addr), Either::Right(*fallthrough));

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Ljumptable(arg_reg, targets)),
        reg_rtl(addr, *arg_reg, arg_rtl),
        let inst = RTLInst::Ijumptable(*arg_rtl, Arc::new(targets.clone()));


    ax_value_addr(ret_addr, def_addr) <--
        ltl_inst(ret_addr, ?LTLInst::Lreturn),
        reg_def_used(def_addr, Mreg::AX, ret_addr);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lreturn),
        ax_value_addr(addr, axaddr),
        reg_rtl(addr, Mreg::AX, ret_rtl),
        let inst = RTLInst::Ireturn(*ret_rtl);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lreturn),
        !ax_value_addr(addr, _),
        let void_reg = crate::decompile::passes::rtl_pass::fresh_xtl_reg(*addr, Mreg::AX),
        let inst = RTLInst::Ireturn(void_reg);

    func_ax_def(func_start, addr, rtl_reg) <--
        instr_in_function(addr, func_start),
        reg_def_site(addr, Mreg::AX),
        reg_rtl(addr, Mreg::AX, rtl_reg);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lgetstack(slot, ofs, typ, dst)),
        reg_rtl(addr, *dst, dst_rtl),
        instr_in_function(addr, func_start),
        stack_var(func_start, addr, ofs, rtl_reg),
        let inst = RTLInst::Iop(Operation::Omove, Arc::new(vec![*rtl_reg]), *dst_rtl);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lgetstack(slot, ofs, typ, dst)),
        reg_rtl(addr, *dst, dst_rtl),
        instr_in_function(addr, func_start),
        !stack_var(func_start, addr, ofs, _),
        let fresh_src = fresh_xtl_reg(*addr, Mreg::BP) | FRESH_NS_STACK_SRC,
        let inst = RTLInst::Iop(Operation::Omove, Arc::new(vec![fresh_src]), *dst_rtl);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lgetstack(slot, ofs, typ, dst)),
        !reg_rtl(addr, dst, _),
        instr_in_function(addr, func_start),
        stack_var(func_start, addr, ofs, rtl_reg),
        let fresh_dst = fresh_xtl_reg(*addr, *dst) | FRESH_NS_REG_DST,
        let inst = RTLInst::Iop(Operation::Omove, Arc::new(vec![*rtl_reg]), fresh_dst);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lgetstack(slot, ofs, typ, dst)),
        !reg_rtl(addr, dst, _),
        instr_in_function(addr, func_start),
        !stack_var(func_start, addr, ofs, _),
        let fresh_src = fresh_xtl_reg(*addr, Mreg::BP) | FRESH_NS_STACK_SRC,
        let fresh_dst = fresh_xtl_reg(*addr, *dst) | FRESH_NS_REG_DST,
        let inst = RTLInst::Iop(Operation::Omove, Arc::new(vec![fresh_src]), fresh_dst);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lsetstack(src, slot, ofs, typ)),
        instr_in_function(addr, func_start),
        reg_def_used(defaddr, *src, *addr),
        reg_rtl(defaddr, *src, src_rtl),
        stack_var(func_start, addr, ofs, stack_rtl),
        let inst = RTLInst::Iop(Operation::Omove, Arc::new(vec![*src_rtl]), *stack_rtl);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lsetstack(src, slot, ofs, typ)),
        instr_in_function(addr, func_start),
        !reg_def_used(_, src, addr),
        is_arg_reg(src),
        func_param_validated(func_start, src),
        reg_rtl(func_start, *src, src_rtl),
        stack_var(func_start, addr, ofs, stack_rtl),
        let inst = RTLInst::Iop(Operation::Omove, Arc::new(vec![*src_rtl]), *stack_rtl);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lsetstack(src, slot, ofs, typ)),
        instr_in_function(addr, func_start),
        reg_rtl(addr, *src, src_rtl),
        !stack_var(func_start, addr, ofs, _),
        let fresh_stack = fresh_xtl_reg(*addr, Mreg::BP),
        let inst = RTLInst::Iop(Operation::Omove, Arc::new(vec![*src_rtl]), fresh_stack);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lsetstack(src, slot, ofs, typ)),
        instr_in_function(addr, func_start),
        !reg_def_used(_, src, addr),
        is_arg_reg(src),
        !func_param_validated(func_start, src),
        reg_rtl(addr, *src, src_rtl),
        stack_var(func_start, addr, ofs, stack_rtl),
        let inst = RTLInst::Iop(Operation::Omove, Arc::new(vec![*src_rtl]), *stack_rtl);

    rtl_inst_candidate(addr, inst) <--
        ltl_inst(addr, ?LTLInst::Lsetstack(src, slot, ofs, typ)),
        instr_in_function(addr, func_start),
        !reg_def_used(_, src, addr),
        !is_arg_reg(src),
        reg_rtl(addr, *src, src_rtl),
        stack_var(func_start, addr, ofs, stack_rtl),
        let inst = RTLInst::Iop(Operation::Omove, Arc::new(vec![*src_rtl]), *stack_rtl);


    func_broken_xtl(func_start, x) <--
        reg_xtl(addr, mreg, x),
        instr_in_function(addr, func_start),
        !func_param_validated(func_start, mreg);


    rtl_inst_candidate(addr, inst), reg_xtl(addr, dst_mreg, dst_rtl), op_produces_ptr(addr, dst_rtl) <--
        plea(addr, dst_sym, src_addr),
        op_register(dst_sym, dst_str),
        op_indirect(src_addr, _, base_str, _, _scale, disp, _),
        if (*base_str).ends_with("BP"),
        let dst_mreg = Mreg::from(dst_str.to_string()),
        let dst_rtl = fresh_xtl_reg(*addr, dst_mreg),
        let inst = RTLInst::Iop(Operation::Olea(Addressing::Ainstack(*disp)), Arc::new(vec![]), dst_rtl);

    ltl_inst(addr, ltl) <--
        plea(addr, dst_sym, src_addr),
        op_register(dst_sym, dst_str),
        op_indirect(src_addr, _, base_str, _, _scale, disp, _),
        if (*base_str).ends_with("BP"),
        let dst_mreg = Mreg::from(dst_str.to_string()),
        let ltl = LTLInst::Lop(Operation::Olea(Addressing::Ainstack(*disp)), Arc::new(vec![]), dst_mreg);


    stack_mem_add_imm(addr, disp, imm_val, sz) <--
        padd(addr, dst_sym, src_sym),
        op_indirect(dst_sym, _, base_str, _, _, disp, sz),
        if (*base_str).ends_with("BP"),
        op_immediate(src_sym, imm_val, _);

    stack_mem_sub_imm(addr, disp, imm_val, sz) <--
        psub(addr, dst_sym, src_sym),
        op_indirect(dst_sym, _, base_str, _, _, disp, sz),
        if (*base_str).ends_with("BP"),
        op_immediate(src_sym, imm_val, _);

    stack_xtl(func_start, addr, disp, rtl_reg) <--
        stack_mem_add_imm(addr, disp, _, _),
        instr_in_function(addr, func_start),
        let rtl_reg = fresh_xtl_reg(*addr, Mreg::BP);

    stack_xtl(func_start, addr, disp, rtl_reg) <--
        stack_mem_sub_imm(addr, disp, _, _),
        instr_in_function(addr, func_start),
        let rtl_reg = fresh_xtl_reg(*addr, Mreg::BP);

    stack_xtl(func_start, addr, ofs, rtl_reg) <--
        ltl_inst(addr, ?LTLInst::Lsetstack(_, _, ofs, _)),
        instr_in_function(addr, func_start),
        let rtl_reg = fresh_xtl_reg(*addr, Mreg::BP);

    rtl_inst_candidate(addr, inst) <--
        stack_mem_add_imm(addr, disp, imm_val, sz),
        if *sz == 8,
        instr_in_function(addr, func_start),
        stack_var(func_start, addr, disp, stack_rtl),
        let inst = RTLInst::Iop(Operation::Oaddlimm(*imm_val), Arc::new(vec![*stack_rtl]), *stack_rtl);

    rtl_inst_candidate(addr, inst) <--
        stack_mem_add_imm(addr, disp, imm_val, sz),
        if *sz == 4,
        instr_in_function(addr, func_start),
        stack_var(func_start, addr, disp, stack_rtl),
        let inst = RTLInst::Iop(Operation::Oaddimm(*imm_val), Arc::new(vec![*stack_rtl]), *stack_rtl);

    rtl_inst_candidate(addr, inst) <--
        stack_mem_sub_imm(addr, disp, imm_val, sz),
        if *sz == 8,
        instr_in_function(addr, func_start),
        stack_var(func_start, addr, disp, stack_rtl),
        let inst = RTLInst::Iop(Operation::Oaddlimm(-*imm_val), Arc::new(vec![*stack_rtl]), *stack_rtl);

    rtl_inst_candidate(addr, inst) <--
        stack_mem_sub_imm(addr, disp, imm_val, sz),
        if *sz == 4,
        instr_in_function(addr, func_start),
        stack_var(func_start, addr, disp, stack_rtl),
        let inst = RTLInst::Iop(Operation::Oaddimm(-*imm_val), Arc::new(vec![*stack_rtl]), *stack_rtl);


    relation reg_xtl(Node, Mreg, RTLReg);
    relation reg_def_site(Node, Mreg);
    relation is_def(Node, RTLReg);
    relation reg_rtl(Node, Mreg, RTLReg);

    relation alias_edge(RTLReg, RTLReg);

    #[local] lattice xtl_canonical_lat(RTLReg, ascent::Dual<RTLReg>);

    // Seed: each id maps to itself
    xtl_canonical_lat(a, ascent::Dual(*a)) <-- reg_xtl(_, _, a);
    xtl_canonical_lat(a, ascent::Dual(*a)) <-- is_def(_, a);
    xtl_canonical_lat(a, ascent::Dual(*a)) <-- stack_xtl(_, _, _, a);
    xtl_canonical_lat(a, ascent::Dual(*a)) <-- alias_edge(a, _);
    xtl_canonical_lat(b, ascent::Dual(*b)) <-- alias_edge(_, b);

    // Propagate min canonical through alias edges
    xtl_canonical_lat(b, *canonical) <-- alias_edge(a, b), xtl_canonical_lat(a, canonical);
    xtl_canonical_lat(a, *canonical) <-- alias_edge(a, b), xtl_canonical_lat(b, canonical);

    // Project lattice to regular relation
    relation xtl_canonical(RTLReg, RTLReg);
    xtl_canonical(id, canonical.0) <-- xtl_canonical_lat(id, canonical);

    relation is_early_arg_use(Address, Node);

    #[local] relation param_reg_used_early(Address, Mreg);

    relation return_val_used(Address, Address, Mreg, Address, i64);
    relation call_return_reg(Node, RTLReg);


    relation asm_effective_def(Address, Mreg);
    asm_effective_def(addr, reg) <-- reg_def(addr, reg), !trim_instruction(addr);
    asm_effective_def(addr, Mreg::AX) <--
        unrefinedinstruction(addr, _, _, "CALL", _, _, _, _, _, _);

    asm_effective_def(addr, reg) <--
        unrefinedinstruction(addr, _, _, "CALL", _, _, _, _, _, _),
        is_caller_saved(reg);

    // Lbuiltin results are effective defs even at trimmed addresses (e.g. VLA alloca replaces trimmed MOV RSP)
    asm_effective_def(addr, *dst_reg) <--
        ltl_inst(addr, ?LTLInst::Lbuiltin(_, _, BuiltinArg::BA(dst_reg))),
        if *dst_reg != Mreg::Unknown;

    reg_use(addr, Mreg::AX) <--
        ltl_inst(addr, ?LTLInst::Lreturn);

    relation block_last_insn(Address, Address);
    block_last_insn(block_start, last_insn) <--
        block_boundaries(block_start, last_insn, _);

    relation asm_block_next(Address, Address);
    asm_block_next(src_block, dst) <--
        ddisasm_cfg_edge(src, dst, edge_type),
        if *edge_type != "call" && *edge_type != "indirect" && *edge_type != "indirect_call",
        code_in_block(src, src_block);

    relation block_last_def(Address, Address, Mreg);

    block_last_def(next_addr, def_addr, reg) <--
        asm_effective_def(def_addr, reg),
        next(def_addr, next_addr),
        code_in_block(def_addr, blk),
        code_in_block(next_addr, blk);

    block_last_def(next_addr, def_addr, reg) <--
        block_last_def(curr_addr, def_addr, reg),
        !asm_effective_def(curr_addr, reg),
        next(curr_addr, next_addr),
        code_in_block(curr_addr, blk),
        code_in_block(next_addr, blk);

    relation last_def_in_block(Address, Address, Mreg);

    last_def_in_block(block, last_insn, reg) <--
        block_last_insn(block, last_insn),
        asm_effective_def(last_insn, reg);

    last_def_in_block(block, def_addr, reg) <--
        block_last_insn(block, last_insn),
        block_last_def(last_insn, def_addr, reg),
        !asm_effective_def(last_insn, reg);

    relation asm_defined_in_block(Address, Mreg);
    asm_defined_in_block(block, reg) <--
        asm_effective_def(ea, reg),
        code_in_block(ea, block);

    relation live_var_def(Address, Mreg, Address);
    live_var_def(block, reg, def_addr) <--
        last_def_in_block(block, def_addr, reg);

    relation live_var_used(Address, Mreg, Address);
    live_var_used(block, reg, use_addr) <--
        reg_use(use_addr, reg),
        !trim_instruction(use_addr),
        code_in_block(use_addr, block),
        !block_last_def(use_addr, _, reg);

    relation live_var_at_block_end(Address, Address, Mreg);

    live_var_at_block_end(prev_block, use_block, reg) <--
        live_var_used(use_block, reg, _),
        asm_block_next(prev_block, use_block);

    live_var_at_block_end(prev_block, use_block, reg) <--
        live_var_at_block_end(mid_block, use_block, reg),
        !asm_defined_in_block(mid_block, reg),
        asm_block_next(prev_block, mid_block);

    reg_def_used(def_addr, reg, use_addr) <--
        reg_use(use_addr, reg),
        !trim_instruction(use_addr),
        block_last_def(use_addr, def_addr, reg);

    reg_def_used(def_addr, reg, use_addr) <--
        live_var_at_block_end(def_block, use_block, reg),
        live_var_def(def_block, reg, def_addr),
        live_var_used(use_block, reg, use_addr);

    param_reg_used_early(*func_start, *mreg) <--
        instr_in_function(use_addr, func_start),
        function_entry_count(func_start, use_addr, count),
        if *count < FUNC_ARG_DIST as i64,
        reg_use(use_addr, mreg),
        !trim_instruction(use_addr),
        is_arg_reg(mreg);

    reg_def_used(*func_start, *mreg, *use_addr) <--
        param_reg_used_early(func_start, mreg),
        instr_in_function(use_addr, func_start),
        function_entry_count(func_start, use_addr, count),
        if *count < FUNC_ARG_DIST as i64,
        reg_use(use_addr, mreg),
        !trim_instruction(use_addr),
        !block_last_def(use_addr, _, mreg);

    is_early_arg_use(func_start, addr) <--
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST as i64;

    relation stack_xtl(Address, Address, i64, RTLReg);
    relation stack_var(Address, Address, i64, RTLReg);

    stack_var(func_start, use_addr, ofs, canonical.0) <--
        stack_xtl(func_start, use_addr, ofs, xtl_id),
        xtl_canonical_lat(xtl_id, canonical);

    relation unrefinedinstruction(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize);
    relation symbol_table(Address, usize, Symbol, Symbol, Symbol, usize, Symbol, usize, Symbol);
    relation op_indirect(Symbol, &'static str, &'static str, &'static str, i64, i64, usize);
    relation op_register(Symbol, &'static str);

    relation global_symbol(Address, Symbol);
    global_symbol(addr, name) <--
        symbol_table(addr, _size, _type, _binding, _section_type, _section_idx, _section_name, _name_idx, name),
        if *_binding == "GLOBAL" || *_binding == "LOCAL",
        if *_type == "OBJECT",
        if *addr > 0;

    relation rip_relative_access(Address, Size, i64);
    rip_relative_access(addr, size, disp) <--
        unrefinedinstruction(addr, size, _, _, op1, _, _, _, _, _),
        op_indirect(op1, _, base_reg, _, disp, _, _),
        if is_rip(base_reg);

    rip_relative_access(addr, size, disp) <--
        unrefinedinstruction(addr, size, _, _, _, op2, _, _, _, _),
        op_indirect(op2, _, base_reg, _, disp, _, _),
        if is_rip(base_reg);

    rip_relative_access(addr, size, disp) <--
        unrefinedinstruction(addr, size, _, _, op1, _, _, _, _, _),
        op_indirect(op1, _, base_reg, _, _, disp, _),
        if is_rip(base_reg);

    rip_relative_access(addr, size, disp) <--
        unrefinedinstruction(addr, size, _, _, _, op2, _, _, _, _),
        op_indirect(op2, _, base_reg, _, _, disp, _),
        if is_rip(base_reg);

    global_symbol(target_addr, name_sym) <--
        rip_relative_access(addr, size, disp),
        let target_addr = (*addr as i64 + *size as i64 + *disp) as Address,
        !symbol_table(target_addr, _, _, _, _, _, _, _, _),
        !plt_entry(target_addr, _),
        let name_string = format!("SUB_{:x}", target_addr),
        let name_sym = Box::leak(name_string.into_boxed_str()) as &'static str;

    symbols(addr, name, name) <--
        global_symbol(addr, name);

    relation stack_var_chunk(Address, i64, MemoryChunk);

    relation ltl_use(Node, Mreg);
    relation param_alias_source(Address, Mreg);

    reg_rtl(node, mreg, *canonical) <--
        reg_xtl(node, mreg, xtl_id),
        xtl_canonical(xtl_id, canonical);

    relation load_overwrites_base(Node, Mreg);
    load_overwrites_base(addr, *dst_reg) <--
        ltl_inst(addr, ?LTLInst::Lload(_, _, args, dst_reg)),
        for src in args.iter(),
        if src == dst_reg;

    relation load_overwrite_use_id(Node, Mreg, RTLReg);
    load_overwrite_use_id(addr, *src, use_id) <--
        load_overwrites_base(addr, src),
        let use_id = fresh_xtl_reg(*addr, *src) | (1u64 << 62);

    reg_xtl(addr, *src, use_id) <--
        load_overwrite_use_id(addr, src, use_id);

    // Merge use-side IDs only at the same node; defs kill values so def/use IDs must not alias (alias_edge handles def-to-use).
    alias_edge(id1, id2) <--
        reg_xtl(node, mreg, id1),
        reg_xtl(node, mreg, id2),
        if id1 != id2,
        !load_overwrites_base(node, mreg),
        !is_def(node, id1),
        !is_def(node, id2);

    // Block-level dominator computation for back-edge detection.
    // Entry block of each function: the block containing the function start address.
    #[local] relation func_entry_block(Address, Address);
    func_entry_block(func, entry_block) <--
        block_in_function(entry_block, func),
        code_in_block(func, entry_block);

    // Block reachability from the entry block (within a function).
    #[local] relation block_reachable_from_entry(Address, Address);
    block_reachable_from_entry(func, entry_block) <--
        func_entry_block(func, entry_block);
    block_reachable_from_entry(func, next_block) <--
        block_reachable_from_entry(func, blk),
        asm_block_next(blk, next_block),
        block_in_function(next_block, func);

    // path_avoiding(func, block, d): block is reachable from entry without passing through d.
    #[local] relation block_path_avoiding(Address, Address, Address);
    block_path_avoiding(func, entry_block, d) <--
        func_entry_block(func, entry_block),
        block_reachable_from_entry(func, d),
        if *entry_block != *d;
    block_path_avoiding(func, next_block, d) <--
        block_path_avoiding(func, blk, d),
        asm_block_next(blk, next_block),
        block_in_function(next_block, func),
        if *next_block != *d;

    // Block dominance: d dominates b iff no path from entry to b avoids d.
    #[local] relation block_dom(Address, Address, Address);
    block_dom(func, blk, blk) <--
        block_reachable_from_entry(func, blk);
    block_dom(func, blk, d) <--
        block_reachable_from_entry(func, blk),
        block_reachable_from_entry(func, d),
        !block_path_avoiding(func, blk, d);

    // Back-edge: ltl_succ (src, dst) where dst's block dominates src's block in the same function.
    #[local] relation is_loop_back_edge(Address, Address);
    is_loop_back_edge(src, dst) <--
        rtl_next(src, dst),
        code_in_block(src, src_block),
        code_in_block(dst, dst_block),
        if *src_block != *dst_block,
        instr_in_function(src, func),
        block_dom(func, src_block, dst_block);
    // Intra-block back-edge: dst <= src within the same block (backward jump).
    is_loop_back_edge(src, dst) <--
        rtl_next(src, dst),
        code_in_block(src, blk),
        code_in_block(dst, blk),
        if *dst <= *src;

    // Forward reachability: transitive closure of rtl_next excluding back-edges, scoped per function.
    #[local] relation forward_reachable(Address, Address, Address);
    forward_reachable(func, src, dst) <--
        rtl_next(src, dst),
        instr_in_function(src, func),
        instr_in_function(dst, func),
        !is_loop_back_edge(src, dst);
    forward_reachable(func, src, dst) <--
        forward_reachable(func, src, mid),
        rtl_next(mid, dst),
        instr_in_function(dst, func),
        !is_loop_back_edge(mid, dst);

    relation has_intervening_def(Address, Address, Mreg);
    has_intervening_def(def_addr, use_addr, mreg) <--
        reg_def_used(def_addr, mreg, use_addr),
        reg_def_site(mid_addr, mreg),
        if *mid_addr != *def_addr && *mid_addr != *use_addr,
        instr_in_function(def_addr, func),
        instr_in_function(mid_addr, func),
        forward_reachable(func, def_addr, mid_addr),
        forward_reachable(func, mid_addr, use_addr);

    has_intervening_def(def_addr, use_addr, mreg) <--
        reg_def_used(def_addr, mreg, use_addr),
        is_call_clobbered(mid_addr, mreg),
        if *mid_addr != *def_addr && *mid_addr != *use_addr,
        instr_in_function(def_addr, func),
        instr_in_function(mid_addr, func),
        forward_reachable(func, def_addr, mid_addr),
        forward_reachable(func, mid_addr, use_addr);

    relation param_live_block(Address, Address, Mreg);

    param_live_block(func_start, entry_block, mreg) <--
        func_param_validated(func_start, mreg),
        code_in_block(func_start, entry_block);

    param_live_block(func_start, succ_block, mreg) <--
        param_live_block(func_start, curr_block, mreg),
        asm_block_next(curr_block, succ_block),
        !asm_defined_in_block(curr_block, mreg);

    alias_edge(def_id, use_id) <--
        reg_def_used(defaddr, mreg, useaddr),
        is_def(defaddr, def_id),
        reg_xtl(defaddr, mreg, def_id),
        load_overwrite_use_id(useaddr, mreg, use_id),
        if def_id != use_id,
        !has_intervening_def(defaddr, useaddr, mreg);

    alias_edge(def_id, use_id) <--
        reg_def_used(defaddr, mreg, useaddr),
        load_overwrites_base(defaddr, mreg),
        is_def(defaddr, def_id),
        reg_xtl(defaddr, mreg, def_id),
        reg_xtl(useaddr, mreg, use_id),
        if def_id != use_id,
        !has_intervening_def(defaddr, useaddr, mreg),
        !load_overwrites_base(useaddr, mreg);

    alias_edge(def_id, use_id) <--
        reg_def_used(defaddr, mreg, useaddr),
        !load_overwrites_base(defaddr, mreg),
        is_def(defaddr, def_id),
        reg_xtl(defaddr, mreg, def_id),
        reg_xtl(useaddr, mreg, use_id),
        if def_id != use_id,
        !has_intervening_def(defaddr, useaddr, mreg),
        !load_overwrites_base(useaddr, mreg);

    relation param_still_live(Address, Address, Mreg);
    param_still_live(func_start, use_addr, mreg) <--
        func_param_validated(func_start, mreg),
        instr_in_function(use_addr, func_start),
        function_entry_count(func_start, use_addr, count),
        if *count < FUNC_ARG_DIST as i64,
        code_in_block(use_addr, block),
        param_live_block(func_start, block, mreg),
        !block_last_def(use_addr, _, mreg);

    param_alias_source(useaddr, mreg) <-- arg_reg_has_external_def(useaddr, mreg);
    param_alias_source(useaddr, mreg) <-- arg_reg_used_no_def(useaddr, mreg);
    param_alias_source(useaddr, mreg) <-- arg_reg_used_very_early(useaddr, mreg);

    param_alias_source(use_addr, mreg) <--
        param_still_live(func_start, use_addr, mreg),
        reg_xtl(use_addr, mreg, _),
        !asm_effective_def(use_addr, mreg);

    alias_edge(def_id, use_id) <--
        param_alias_source(useaddr, mreg),
        instr_in_function(useaddr, func_start),
        func_param_validated(func_start, mreg),
        reg_xtl(func_start, mreg, def_id),
        reg_xtl(useaddr, mreg, use_id),
        if def_id != use_id;

    reg_xtl(*useaddr, *reg, param_id) <--
        reg_def_used(defaddr, reg, useaddr),
        if *reg != Mreg::SP,
        instr_in_function(useaddr, func_start),
        is_early_arg_use(func_start, useaddr),
        is_arg_reg(reg),
        !instr_in_function(defaddr, func_start),
        func_arg_reg_used(func_start, reg),
        reg_xtl(func_start, reg, param_id),
        param_still_live(func_start, useaddr, reg);

    reg_xtl(*use_addr, *mreg, param_id) <--
        func_param_validated(func_start, mreg),
        reg_xtl(func_start, mreg, param_id),
        param_still_live(func_start, use_addr, mreg),
        reg_use(use_addr, mreg),
        !reg_def_site(use_addr, mreg);

    reg_xtl(*useaddr, *reg, def_id) <--
        reg_def_used(defaddr, reg, useaddr),
        if *reg != Mreg::SP,
        !is_arg_reg(reg),
        !return_val_used(defaddr, _, reg, useaddr, _),
        !load_overwrites_base(useaddr, reg),
        !has_intervening_def(defaddr, useaddr, reg),
        reg_xtl(defaddr, reg, def_id),
        is_def(defaddr, def_id);

    reg_xtl(*useaddr, *reg, rtl_reg) <--
        reg_def_used(defaddr, reg, useaddr),
        if *reg != Mreg::SP,
        !is_arg_reg(reg),
        !return_val_used(defaddr, _, reg, useaddr, _),
        !load_overwrites_base(useaddr, reg),
        has_intervening_def(defaddr, useaddr, reg),
        let rtl_reg = fresh_xtl_reg(*useaddr, *reg);

    reg_xtl(node, Mreg::AX, rtl_reg) <--
        call_return_reg(node, rtl_reg);

    reg_xtl(*use_addr, *mreg, ret_rtl) <--
        return_val_used(call_addr, _, mreg, use_addr, _),
        call_return_reg(call_addr, ret_rtl);


    reg_xtl(node, Mreg::AX, fresh) <--
        ltl_inst(node, ?LTLInst::Lreturn),
        let fresh = fresh_xtl_reg(*node, Mreg::AX);

    reg_xtl(*useaddr, *reg, rtl_reg) <--
        reg_def_used(defaddr, reg, useaddr),
        if *reg != Mreg::SP,
        is_arg_reg(reg),
        instr_in_function(useaddr, func_start),
        !is_early_arg_use(func_start, useaddr),
        let rtl_reg = fresh_xtl_reg(*useaddr, *reg);

    reg_xtl(*useaddr, *reg, rtl_reg) <--
        reg_def_used(defaddr, reg, useaddr),
        if *reg != Mreg::SP,
        is_arg_reg(reg),
        instr_in_function(useaddr, func_start),
        !instr_in_function(defaddr, func_start),
        !func_arg_reg_used(func_start, reg),
        let rtl_reg = fresh_xtl_reg(*useaddr, *reg);

    reg_xtl(*useaddr, *reg, rtl_reg) <--
        reg_def_used(defaddr, reg, useaddr),
        if *reg != Mreg::SP,
        is_arg_reg(reg),
        instr_in_function(useaddr, func_start),
        is_early_arg_use(func_start, useaddr),
        instr_in_function(defaddr, func_start),
        let rtl_reg = fresh_xtl_reg(*useaddr, *reg);

    reg_def_site(defaddr, dst_reg) <--
        ltl_inst(defaddr, ?LTLInst::Lop(_, _, dst_reg));

    reg_def_site(defaddr, *dst_reg) <--
        ltl_inst(defaddr, ?LTLInst::Lload(_, _, _, dst_reg));

    reg_def_site(defaddr, *dst_reg) <--
        ltl_inst(defaddr, ?LTLInst::Lgetstack(_, _, _, dst_reg));

    reg_def_site(defaddr, *dst_reg) <--
        ltl_inst(defaddr, ?LTLInst::Lbuiltin(_, _, BuiltinArg::BA(dst_reg))),
        if *dst_reg != Mreg::Unknown;

    reg_xtl(defaddr, dst_reg, rtl_reg), is_def(defaddr, rtl_reg) <--
        reg_def_site(defaddr, dst_reg),
        let rtl_reg = fresh_xtl_reg(*defaddr, *dst_reg);

    ltl_use(addr, src_reg) <--
        ltl_inst(addr, ?LTLInst::Lop(_, srcs, _)),
        for src_reg in srcs.iter();

    ltl_use(addr, arg_reg) <--
        ltl_inst(addr, ?LTLInst::Lload(_, _, args, _)),
        for arg_reg in args.iter();

    ltl_use(addr, src_reg) <--
        ltl_inst(addr, ?LTLInst::Lstore(_, _, _, src_reg));

    ltl_use(addr, arg_reg) <--
        ltl_inst(addr, ?LTLInst::Lstore(_, _, args, _)),
        for arg_reg in args.iter();

    ltl_use(addr, arg_reg) <--
        ltl_inst(addr, ?LTLInst::Lcond(_, args, _, _)),
        for arg_reg in args.iter();

    reg_xtl(addr, *reg, fresh_id) <--
        ltl_use(addr, reg),
        if *reg != Mreg::SP,
        let fresh_id = fresh_xtl_reg(*addr, *reg);

    ltl_use(addr, src) <--
        ltl_inst(addr, ?LTLInst::Lsetstack(src, _, _, _));

    ltl_use(addr, reg) <--
        ltl_inst(addr, ?LTLInst::Ljumptable(reg, _));

    ltl_use(addr, reg) <--
        ltl_inst(addr, ?LTLInst::Lcall(tgt)),
        if let Either::Left(reg) = tgt;

    ltl_use(addr, reg) <--
        ltl_inst(addr, ?LTLInst::Ltailcall(tgt)),
        if let Either::Left(reg) = tgt;

    ltl_use(addr, arg_reg) <--
        ltl_inst(addr, ?LTLInst::Lbuiltin(_, args, _)),
        for arg in args.iter(),
        if let BuiltinArg::BA(arg_reg) = arg;


    stack_xtl(func_start, addr, ofs, rtlreg) <--
        mach_imm_stack_init(addr, ofs, _, _),
        instr_in_function(addr, func_start),
        let rtlreg = fresh_xtl_reg(*addr, Mreg::BP);

    // Propagate stack_xtl through def-use chains, joining on def offset and emitting use offset.
    stack_xtl(func_start, use_addr, use_ofs, rtlreg) <--
        stack_xtl(func_start, def_addr, def_ofs, rtlreg),
        instr_in_function(def_addr, func_start),
        stack_def_used(def_addr, _, def_ofs, use_addr, _, use_ofs),
        instr_in_function(use_addr, func_start);

    stack_xtl(func_start, addr, ofs, rtlreg) <--
        ltl_inst(addr, ?LTLInst::Lgetstack(_, ofs, _, _)),
        instr_in_function(addr, func_start),
        !stack_def_used(_, _, _, addr, _, ofs),
        let rtlreg = fresh_xtl_reg(*addr, Mreg::BP);

    stack_xtl(func_start, addr, ofs, rtlreg) <--
        ltl_inst(addr, ?LTLInst::Lload(_, Addressing::Ainstack(ofs), _, _)),
        instr_in_function(addr, func_start),
        !stack_def_used(_, _, _, addr, _, ofs),
        let rtlreg = fresh_xtl_reg(*addr, Mreg::BP);

    stack_xtl(func_start, addr, ofs, rtlreg) <--
        ltl_inst(addr, ?LTLInst::Lop(Operation::Olea(Addressing::Ainstack(ofs)), _, _)),
        instr_in_function(addr, func_start),
        let rtlreg = fresh_xtl_reg(*addr, Mreg::BP);


    alias_edge(rtlreg1, rtlreg2) <--
        stack_xtl(func_start, use_addr, ofs, rtlreg1),
        stack_xtl(func_start, use_addr, ofs, rtlreg2),
        if rtlreg1 != rtlreg2;

    stack_var_chunk(*func, ofs, chunk) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, Addressing::Ainstack(ofs), _, _)),
        instr_in_function(node, func);

    stack_var_chunk(*func, ofs, chunk) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, Addressing::Ainstack(ofs), _, _)),
        instr_in_function(node, func);

    stack_var_chunk(*func, ofs, chunk) <--
        ltl_inst(node, ?LTLInst::Lgetstack(_, ofs, typ, _)),
        let chunk = typ_to_chunk(*typ),
        instr_in_function(node, func);

    stack_var_chunk(*func, ofs, chunk) <--
        ltl_inst(node, ?LTLInst::Lsetstack(_, _, ofs, typ)),
        let chunk = typ_to_chunk(*typ),
        instr_in_function(node, func);


    relation plt_function(Address, Symbol);
    relation is_external_address(Address);

    plt_function(addr, clean_name_sym) <--
        plt_entry(addr, raw_name),
        let clean_name = raw_name.split('@').next().unwrap_or(raw_name),
        let clean_name_sym = Box::leak(clean_name.to_string().into_boxed_str()) as Symbol;

    plt_function(addr, clean_name_sym) <--
        plt_block(addr, raw_name),
        let clean_name = raw_name.split('@').next().unwrap_or(raw_name),
        let clean_name_sym = Box::leak(clean_name.to_string().into_boxed_str()) as Symbol;

    is_external_address(addr) <--
        plt_function(addr, _);


    relation is_external_call(Node, Symbol);
    relation external_call_site(Node, Address, Symbol);

    external_call_site(call_site, target, *name) <--
        ltl_inst(call_site, ?LTLInst::Lcall(Either::Right(Either::Left(target)))),
        plt_function(target, name);


    external_call_site(call_site, target, *name) <--
        ltl_inst(call_site, ?LTLInst::Lcall(Either::Right(Either::Left(target)))),
        let offset_target = target + ENDBR64_LEN,
        plt_function(offset_target, name);

    external_call_site(call_site, target, *name) <--
        ltl_inst(call_site, ?LTLInst::Lcall(Either::Right(Either::Left(target)))),
        if *target >= ENDBR64_LEN,
        let offset_target = target - ENDBR64_LEN,
        plt_function(offset_target, name);

    external_call_site(call_site, target, *name) <--
        ltl_inst(call_site, ?LTLInst::Ltailcall(Either::Right(Either::Left(target)))),
        plt_function(target, name);

    external_call_site(call_site, target, *name) <--
        ltl_inst(call_site, ?LTLInst::Ltailcall(Either::Right(Either::Left(target)))),
        let offset_target = target + ENDBR64_LEN,
        plt_function(offset_target, name);

    external_call_site(call_site, target, *name) <--
        ltl_inst(call_site, ?LTLInst::Ltailcall(Either::Right(Either::Left(target)))),
        if *target >= ENDBR64_LEN,
        let offset_target = target - ENDBR64_LEN,
        plt_function(offset_target, name);

    external_call_site(call_site, target, *name) <--
        ltl_inst(call_site, ?LTLInst::Lcall(Either::Right(Either::Left(target)))),
        base_ident_to_symbol(target_id, name),
        if *target as usize == *target_id,
        known_extern_signature(name, _, _, _);

    is_external_call(call_site, *name) <--
        external_call_site(call_site, _, name);

    relation call_site(Node, Symbol);
    relation call_arg(Node, usize, RTLReg);

    call_site(node, *name) <--
        external_call_site(node, _, name);

    call_site(call_addr, *name) <--
        ltl_inst(call_addr, ?LTLInst::Lcall(Either::Right(Either::Left(target)))),
        emit_function(target, name, _);

    call_arg(node, pos, reg) <--
        call_arg_mapping(node, pos, reg);


    ident_to_symbol(id, *name) <-- base_ident_to_symbol(id, name);
    ident_to_symbol(target_id, *name) <--
        external_call_site(_, target, name),
        let target_id = *target as usize;


    relation resolved_extern_signature(Symbol, usize, XType, Arc<Vec<XType>>);

    resolved_extern_signature(*name, *count, *ret, params.clone()) <--
        plt_function(_, name),
        known_extern_signature(name, count, ret, params);

    call_has_known_signature(call_site, *name, *param_count, *ret_type) <--
        external_call_site(call_site, _, name),
        known_extern_signature(name, param_count, ret_type, _);

    // Also match symbol-based calls (Right(Right(name))) against known signatures
    call_has_known_signature(call_site, *name, *param_count, *ret_type) <--
        ltl_inst(call_site, ?LTLInst::Lcall(Either::Right(Either::Right(name)))),
        known_extern_signature(name, param_count, ret_type, _);

    call_has_known_signature(call_site, *name, *param_count, *ret_type) <--
        ltl_inst(call_site, ?LTLInst::Ltailcall(Either::Right(Either::Right(name)))),
        known_extern_signature(name, param_count, ret_type, _);

    relation unknown_extern(Symbol);

    unknown_extern(*name) <--
        plt_function(_, name),
        !known_extern_signature(name, _, _, _);

    relation extern_call_arg_type(Node, usize, XType);
    relation extern_call_return_type(Node, XType);
    
    extern_call_arg_type(call_site, pos, *param_type) <--
        is_external_call(call_site, name),
        known_extern_signature(name, _, _, params),
        for (pos, param_type) in params.iter().enumerate();
    
    extern_call_return_type(call_site, *ret_type) <--
        is_external_call(call_site, name),
        known_extern_signature(name, _, ret_type, _);

    
    relation should_decompile_function(Address);
    
    should_decompile_function(func_start) <--
        emit_function(func_start, _, _),
        !is_external_address(func_start);


    relation function_entry_dist(Address, Node, i64);
    relation call_arg_mapping(Node, usize, RTLReg);
    relation call_arg_position_allowed(Node, usize);
    relation call_arg_type(Node, usize, XType);

    call_arg_type(call_addr, pos, xtype) <--
        ltl_inst(call_addr, ?LTLInst::Lcall(_)),
        call_arg_mapping(call_addr, pos, rtl_reg),
        emit_var_type_candidate(rtl_reg, xtype);

    relation call_target_func(Node, Address);

    call_target_func(call_addr, *target) <--
        ltl_inst(call_addr, ?LTLInst::Lcall(Either::Right(Either::Left(target))));

    call_target_func(call_addr, *target) <--
        ltl_inst(call_addr, ?LTLInst::Ltailcall(Either::Right(Either::Left(target))));

    relation func_param_position_type(Address, usize, XType);

    func_param_position_type(func_start, 0, xtype) <--
        func_has_param_at_position(func_start, 0),
        func_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::DI, rtl_reg),
        emit_var_type_candidate(rtl_reg, xtype);

    func_param_position_type(func_start, 1, xtype) <--
        func_has_param_at_position(func_start, 1),
        func_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::SI, rtl_reg),
        emit_var_type_candidate(rtl_reg, xtype);

    func_param_position_type(func_start, 2, xtype) <--
        func_has_param_at_position(func_start, 2),
        func_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::DX, rtl_reg),
        emit_var_type_candidate(rtl_reg, xtype);

    func_param_position_type(func_start, 3, xtype) <--
        func_has_param_at_position(func_start, 3),
        func_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::CX, rtl_reg),
        emit_var_type_candidate(rtl_reg, xtype);

    func_param_position_type(func_start, 4, xtype) <--
        func_has_param_at_position(func_start, 4),
        func_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::R8, rtl_reg),
        emit_var_type_candidate(rtl_reg, xtype);

    func_param_position_type(func_start, 5, xtype) <--
        func_has_param_at_position(func_start, 5),
        func_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::R9, rtl_reg),
        emit_var_type_candidate(rtl_reg, xtype);

    func_param_position_type(func_start, 0, XType::Xint) <--
        func_has_param_at_position(func_start, 0),
        func_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::DI, rtl_reg),
        !emit_var_type_candidate(rtl_reg, _);

    func_param_position_type(func_start, 1, XType::Xint) <--
        func_has_param_at_position(func_start, 1),
        func_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::SI, rtl_reg),
        !emit_var_type_candidate(rtl_reg, _);

    func_param_position_type(func_start, 2, XType::Xint) <--
        func_has_param_at_position(func_start, 2),
        func_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::DX, rtl_reg),
        !emit_var_type_candidate(rtl_reg, _);

    func_param_position_type(func_start, 3, XType::Xint) <--
        func_has_param_at_position(func_start, 3),
        func_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::CX, rtl_reg),
        !emit_var_type_candidate(rtl_reg, _);

    func_param_position_type(func_start, 4, XType::Xint) <--
        func_has_param_at_position(func_start, 4),
        func_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::R8, rtl_reg),
        !emit_var_type_candidate(rtl_reg, _);

    func_param_position_type(func_start, 5, XType::Xint) <--
        func_has_param_at_position(func_start, 5),
        func_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::R9, rtl_reg),
        !emit_var_type_candidate(rtl_reg, _);

    // Integer-only param count, used as offset for float param positions
    relation emit_function_int_param_count(Address, usize);

    emit_function_int_param_count(target_addr, count) <--
        func_param_validated(target_addr, _),
        agg count = ascent::aggregators::count() in func_param_validated(target_addr, _);

    emit_function_int_param_count(target_addr, 0) <--
        func_stacksz(target_addr, _, _, _),
        !func_param_validated(target_addr, _);

    // Float param position types appended after integer params
    func_param_position_type(func_start, *int_count + 0, xtype) <--
        func_float_param_validated(func_start, Mreg::X0, 0),
        emit_function_int_param_count(func_start, int_count),
        func_float_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::X0, rtl_reg),
        emit_var_type_candidate(rtl_reg, xtype);
    func_param_position_type(func_start, *int_count + 0, XType::Xfloat) <--
        func_float_param_validated(func_start, Mreg::X0, 0),
        emit_function_int_param_count(func_start, int_count),
        func_float_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::X0, rtl_reg),
        !emit_var_type_candidate(rtl_reg, _);

    func_param_position_type(func_start, *int_count + 1, xtype) <--
        func_float_param_validated(func_start, Mreg::X1, 1),
        emit_function_int_param_count(func_start, int_count),
        func_float_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::X1, rtl_reg),
        emit_var_type_candidate(rtl_reg, xtype);
    func_param_position_type(func_start, *int_count + 1, XType::Xfloat) <--
        func_float_param_validated(func_start, Mreg::X1, 1),
        emit_function_int_param_count(func_start, int_count),
        func_float_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::X1, rtl_reg),
        !emit_var_type_candidate(rtl_reg, _);

    func_param_position_type(func_start, *int_count + 2, xtype) <--
        func_float_param_validated(func_start, Mreg::X2, 2),
        emit_function_int_param_count(func_start, int_count),
        func_float_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::X2, rtl_reg),
        emit_var_type_candidate(rtl_reg, xtype);
    func_param_position_type(func_start, *int_count + 2, XType::Xfloat) <--
        func_float_param_validated(func_start, Mreg::X2, 2),
        emit_function_int_param_count(func_start, int_count),
        func_float_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::X2, rtl_reg),
        !emit_var_type_candidate(rtl_reg, _);

    func_param_position_type(func_start, *int_count + 3, xtype) <--
        func_float_param_validated(func_start, Mreg::X3, 3),
        emit_function_int_param_count(func_start, int_count),
        func_float_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::X3, rtl_reg),
        emit_var_type_candidate(rtl_reg, xtype);
    func_param_position_type(func_start, *int_count + 3, XType::Xfloat) <--
        func_float_param_validated(func_start, Mreg::X3, 3),
        emit_function_int_param_count(func_start, int_count),
        func_float_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::X3, rtl_reg),
        !emit_var_type_candidate(rtl_reg, _);

    func_param_position_type(func_start, *int_count + 4, xtype) <--
        func_float_param_validated(func_start, Mreg::X4, 4),
        emit_function_int_param_count(func_start, int_count),
        func_float_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::X4, rtl_reg),
        emit_var_type_candidate(rtl_reg, xtype);
    func_param_position_type(func_start, *int_count + 4, XType::Xfloat) <--
        func_float_param_validated(func_start, Mreg::X4, 4),
        emit_function_int_param_count(func_start, int_count),
        func_float_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::X4, rtl_reg),
        !emit_var_type_candidate(rtl_reg, _);

    func_param_position_type(func_start, *int_count + 5, xtype) <--
        func_float_param_validated(func_start, Mreg::X5, 5),
        emit_function_int_param_count(func_start, int_count),
        func_float_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::X5, rtl_reg),
        emit_var_type_candidate(rtl_reg, xtype);
    func_param_position_type(func_start, *int_count + 5, XType::Xfloat) <--
        func_float_param_validated(func_start, Mreg::X5, 5),
        emit_function_int_param_count(func_start, int_count),
        func_float_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::X5, rtl_reg),
        !emit_var_type_candidate(rtl_reg, _);

    func_param_position_type(func_start, *int_count + 6, xtype) <--
        func_float_param_validated(func_start, Mreg::X6, 6),
        emit_function_int_param_count(func_start, int_count),
        func_float_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::X6, rtl_reg),
        emit_var_type_candidate(rtl_reg, xtype);
    func_param_position_type(func_start, *int_count + 6, XType::Xfloat) <--
        func_float_param_validated(func_start, Mreg::X6, 6),
        emit_function_int_param_count(func_start, int_count),
        func_float_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::X6, rtl_reg),
        !emit_var_type_candidate(rtl_reg, _);

    func_param_position_type(func_start, *int_count + 7, xtype) <--
        func_float_param_validated(func_start, Mreg::X7, 7),
        emit_function_int_param_count(func_start, int_count),
        func_float_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::X7, rtl_reg),
        emit_var_type_candidate(rtl_reg, xtype);
    func_param_position_type(func_start, *int_count + 7, XType::Xfloat) <--
        func_float_param_validated(func_start, Mreg::X7, 7),
        emit_function_int_param_count(func_start, int_count),
        func_float_arg_used_undefined(func_start, rtl_reg),
        reg_xtl(func_start, Mreg::X7, rtl_reg),
        !emit_var_type_candidate(rtl_reg, _);

    relation func_param_types(Address, Arc<Vec<XType>>);

    func_param_types(func_start, param_types) <--
        func_param_position_type(func_start, _, _),
        agg param_types = build_xtype_vec(pos, xtype) in func_param_position_type(func_start, pos, xtype);

    // For internal functions matching known externs, use known sig to avoid false variadic params.
    relation func_has_known_extern_sig(Address);

    // Only suppress inferred sigs for variadic functions; non-variadic may be custom implementations.
    func_has_known_extern_sig(func_start) <--
        emit_function(func_start, name, _),
        known_varargs_function(name, _);

    relation emit_function_signature_candidate(Address, Signature);

    // When a known varargs extern signature exists, prefer it over inferred signature.
    emit_function_signature_candidate(func_start, sig) <--
        emit_function(func_start, name, _),
        known_varargs_function(name, _),
        known_extern_signature(name, _, ret_type, known_params),
        let sig = Signature { sig_args: known_params.clone(), sig_res: *ret_type, sig_cc: CallConv::default() };

    emit_function_signature_candidate(func_start, sig) <--
        emit_function(func_start, _, _),
        !func_has_known_extern_sig(func_start),
        func_param_types(func_start, param_types),
        emit_function_return_type_xtype_candidate(func_start, ret_type),
        let sig = Signature { sig_args: param_types.clone(), sig_res: *ret_type, sig_cc: CallConv::default() };

    emit_function_signature_candidate(func_start, sig) <--
        emit_function(func_start, _, _),
        !func_has_known_extern_sig(func_start),
        func_param_types(func_start, param_types),
        !emit_function_return_type_xtype_candidate(func_start, _),
        let sig = Signature { sig_args: param_types.clone(), sig_res: XType::Xvoid, sig_cc: CallConv::default() };

    emit_function_signature_candidate(func_start, sig) <--
        emit_function(func_start, _, _),
        !func_has_known_extern_sig(func_start),
        !func_param_types(func_start, _),
        emit_function_return_type_xtype_candidate(func_start, ret_type),
        let sig = Signature { sig_args: Arc::new(vec![]), sig_res: *ret_type, sig_cc: CallConv::default() };

    emit_function_signature_candidate(func_start, sig) <--
        emit_function(func_start, _, _),
        !func_has_known_extern_sig(func_start),
        !func_param_types(func_start, _),
        !emit_function_return_type_xtype_candidate(func_start, _),
        let sig = Signature { sig_args: Arc::new(vec![]), sig_res: XType::Xvoid, sig_cc: CallConv::default() };


    call_arg_position_allowed(call_addr, pos) <--
        call_has_arg_at_position(call_addr, pos),
        !call_has_known_signature(call_addr, _, _, _);

    call_arg_position_allowed(call_addr, pos) <--
        call_has_arg_at_position(call_addr, pos),
        call_has_known_signature(call_addr, name, _, _),
        known_varargs_function(name, _);

    call_arg_position_allowed(call_addr, pos) <--
        call_has_arg_at_position(call_addr, pos),
        call_has_known_signature(call_addr, name, sig_arg_count, _),
        !known_varargs_function(name, _),
        if pos < sig_arg_count;

    call_arg_mapping(*call_addr, pos, rtl_reg) <--
        call_arg_setup_detected(defaddr, dst_reg, call_addr),
        reg_rtl(defaddr, dst_reg, rtl_reg),
        if let Some(pos) = arg_reg_position(dst_reg),
        call_arg_position_allowed(call_addr, pos),
        instr_in_function(defaddr, _func_start);

    call_arg_mapping(*call_addr, pos, rtl_reg) <--
        tailcall_arg_setup_detected(defaddr, dst_reg, call_addr),
        reg_rtl(defaddr, dst_reg, rtl_reg),
        if let Some(pos) = arg_reg_position(dst_reg),
        call_arg_position_allowed(call_addr, pos),
        instr_in_function(defaddr, _func_start);


    relation arg_setup_candidate(Node, Mreg, Node);
    relation call_clobbers_arg_reg(Node, Mreg, Node);
    relation is_call_instruction(Node);

    is_call_instruction(addr) <-- ltl_inst(addr, ?LTLInst::Lcall(_));
    is_call_instruction(addr) <-- ltl_inst(addr, ?LTLInst::Ltailcall(_));
    is_call_instruction(addr) <--
        ltl_inst(addr, ?LTLInst::Lbranch(Either::Right(target))),
        emit_function(_, _, target);

    lattice call_backward_reach(Node, Node, ascent::Dual<i64>);

    call_backward_reach(call_addr, call_addr, ascent::Dual(0)) <--
        is_call_instruction(call_addr);

    call_backward_reach(call_addr, prev, ascent::Dual(steps.0 + 1)) <--
        call_backward_reach(call_addr, curr, steps),
        if steps.0 < 128,
        next(prev, curr),
        instr_in_function(call_addr, func_start),
        instr_in_function(prev, func_start);

    call_backward_reach(call_addr, prev, ascent::Dual(steps.0 + 1)) <--
        call_backward_reach(call_addr, curr, steps),
        if steps.0 < 128,
        ltl_succ(prev, curr),
        instr_in_function(call_addr, func_start),
        instr_in_function(prev, func_start);

    // Pre-filtered: only call-to-call backward reachability (much smaller than full reach)
    relation call_to_call_backward(Node, Node);
    call_to_call_backward(call_addr, between_call) <--
        call_backward_reach(call_addr, between_call, _),
        is_call_instruction(between_call),
        if *call_addr != *between_call;

    arg_setup_candidate(*defaddr, *dst_reg, *call_addr) <--
        ltl_inst(defaddr, ?LTLInst::Lop(_, _, dst_reg)),
        is_arg_reg(dst_reg),
        call_backward_reach(call_addr, defaddr, _),
        instr_in_function(defaddr, func_start),
        instr_min_order(func_start, defaddr, def_order),
        instr_min_order(func_start, call_addr, call_order),
        if *call_order > *def_order && (*call_order - *def_order) < 128;

    arg_setup_candidate(*defaddr, *dst_reg, *call_addr) <--
        ltl_inst(defaddr, ?LTLInst::Lgetstack(_slot, _ofs, _typ, dst_reg)),
        is_arg_reg(dst_reg),
        call_backward_reach(call_addr, defaddr, _),
        instr_in_function(defaddr, func_start),
        instr_min_order(func_start, defaddr, def_order),
        instr_min_order(func_start, call_addr, call_order),
        if *call_order > *def_order && (*call_order - *def_order) < 128;

    arg_setup_candidate(*defaddr, *dst_reg, *call_addr) <--
        ltl_inst(defaddr, ?LTLInst::Lload(_, _, _, dst_reg)),
        is_arg_reg(dst_reg),
        call_backward_reach(call_addr, defaddr, _),
        instr_in_function(defaddr, func_start),
        instr_min_order(func_start, defaddr, def_order),
        instr_min_order(func_start, call_addr, call_order),
        if *call_order > *def_order && (*call_order - *def_order) < 128;

    call_clobbers_arg_reg(defaddr, mreg, call_addr) <--
        arg_setup_candidate(defaddr, mreg, call_addr),
        call_to_call_backward(call_addr, between_call),
        call_backward_reach(between_call, defaddr, _),
        instr_in_function(defaddr, func_start),
        instr_min_order(func_start, defaddr, def_order),
        instr_min_order(func_start, between_call, between_order),
        instr_min_order(func_start, call_addr, call_order),
        if *between_order > *def_order && *between_order < *call_order;

    call_clobbers_arg_reg(defaddr, mreg, call_addr) <--
        float_arg_setup_candidate(defaddr, mreg, call_addr),
        call_to_call_backward(call_addr, between_call),
        call_backward_reach(between_call, defaddr, _),
        instr_in_function(defaddr, func_start),
        instr_min_order(func_start, defaddr, def_order),
        instr_min_order(func_start, between_call, between_order),
        instr_min_order(func_start, call_addr, call_order),
        if *between_order > *def_order && *between_order < *call_order;

    // Kill arg setup when a closer redefinition of the same register exists
    call_clobbers_arg_reg(defaddr, mreg, call_addr) <--
        arg_setup_candidate(defaddr, mreg, call_addr),
        arg_setup_candidate(other_def, mreg, call_addr),
        instr_in_function(defaddr, func_start),
        instr_min_order(func_start, defaddr, def_order),
        instr_min_order(func_start, other_def, other_order),
        if *other_order > *def_order && *defaddr != *other_def;

    call_clobbers_arg_reg(defaddr, mreg, call_addr) <--
        float_arg_setup_candidate(defaddr, mreg, call_addr),
        float_arg_setup_candidate(other_def, mreg, call_addr),
        instr_in_function(defaddr, func_start),
        instr_min_order(func_start, defaddr, def_order),
        instr_min_order(func_start, other_def, other_order),
        if *other_order > *def_order && *defaddr != *other_def;

    relation call_arg_setup_detected(Node, Mreg, Node);

    call_arg_setup_detected(defaddr, mreg, call_addr) <--
        arg_setup_candidate(defaddr, mreg, call_addr),
        ltl_inst(call_addr, ?LTLInst::Lcall(_)),
        !call_clobbers_arg_reg(defaddr, mreg, call_addr);

    relation tailcall_arg_setup_detected(Node, Mreg, Node);

    tailcall_arg_setup_detected(defaddr, mreg, call_addr) <--
        arg_setup_candidate(defaddr, mreg, call_addr),
        ltl_inst(call_addr, ?LTLInst::Ltailcall(_)),
        !call_clobbers_arg_reg(defaddr, mreg, call_addr);

    tailcall_arg_setup_detected(defaddr, mreg, call_addr) <--
        arg_setup_candidate(defaddr, mreg, call_addr),
        ltl_inst(call_addr, ?LTLInst::Lbranch(Either::Right(target))),
        emit_function(_, _, target),
        !call_clobbers_arg_reg(defaddr, mreg, call_addr);

    // Call arg positions use max-evidence approach instead of requiring consecutive regs
    relation call_has_arg_evidence(Node, usize);

    call_has_arg_evidence(call_addr, 0) <--
        call_arg_setup_detected(_, Mreg::DI, call_addr);
    call_has_arg_evidence(call_addr, 0) <--
        tailcall_arg_setup_detected(_, Mreg::DI, call_addr);

    call_has_arg_evidence(call_addr, 1) <--
        call_arg_setup_detected(_, Mreg::SI, call_addr);
    call_has_arg_evidence(call_addr, 1) <--
        tailcall_arg_setup_detected(_, Mreg::SI, call_addr);

    call_has_arg_evidence(call_addr, 2) <--
        call_arg_setup_detected(_, Mreg::DX, call_addr);
    call_has_arg_evidence(call_addr, 2) <--
        tailcall_arg_setup_detected(_, Mreg::DX, call_addr);

    call_has_arg_evidence(call_addr, 3) <--
        call_arg_setup_detected(_, Mreg::CX, call_addr);
    call_has_arg_evidence(call_addr, 3) <--
        tailcall_arg_setup_detected(_, Mreg::CX, call_addr);

    call_has_arg_evidence(call_addr, 4) <--
        call_arg_setup_detected(_, Mreg::R8, call_addr);
    call_has_arg_evidence(call_addr, 4) <--
        tailcall_arg_setup_detected(_, Mreg::R8, call_addr);

    call_has_arg_evidence(call_addr, 5) <--
        call_arg_setup_detected(_, Mreg::R9, call_addr);
    call_has_arg_evidence(call_addr, 5) <--
        tailcall_arg_setup_detected(_, Mreg::R9, call_addr);

    relation call_max_arg_position(Node, usize);

    call_max_arg_position(call_addr, max_pos) <--
        call_has_arg_evidence(call_addr, _),
        agg max_pos = ascent::aggregators::max(pos) in call_has_arg_evidence(call_addr, pos);

    relation call_has_arg_at_position(Node, usize);

    call_has_arg_at_position(call_addr, 0) <--
        call_max_arg_position(call_addr, _max_pos);
    call_has_arg_at_position(call_addr, 1) <--
        call_max_arg_position(call_addr, max_pos), if *max_pos >= 1;
    call_has_arg_at_position(call_addr, 2) <--
        call_max_arg_position(call_addr, max_pos), if *max_pos >= 2;
    call_has_arg_at_position(call_addr, 3) <--
        call_max_arg_position(call_addr, max_pos), if *max_pos >= 3;
    call_has_arg_at_position(call_addr, 4) <--
        call_max_arg_position(call_addr, max_pos), if *max_pos >= 4;
    call_has_arg_at_position(call_addr, 5) <--
        call_max_arg_position(call_addr, max_pos), if *max_pos >= 5;

    // Float arg setup detection at call sites (XMM0-XMM7, independent from integer args)
    relation float_arg_setup_candidate(Node, Mreg, Node);

    float_arg_setup_candidate(*defaddr, *dst_reg, *call_addr) <--
        ltl_inst(defaddr, ?LTLInst::Lop(_, _, dst_reg)),
        is_xmm_arg_reg(dst_reg),
        call_backward_reach(call_addr, defaddr, _),
        instr_in_function(defaddr, func_start),
        instr_min_order(func_start, defaddr, def_order),
        instr_min_order(func_start, call_addr, call_order),
        if *call_order > *def_order && (*call_order - *def_order) < 64;

    float_arg_setup_candidate(*defaddr, *dst_reg, *call_addr) <--
        ltl_inst(defaddr, ?LTLInst::Lgetstack(_slot, _ofs, _typ, dst_reg)),
        is_xmm_arg_reg(dst_reg),
        call_backward_reach(call_addr, defaddr, _),
        instr_in_function(defaddr, func_start),
        instr_min_order(func_start, defaddr, def_order),
        instr_min_order(func_start, call_addr, call_order),
        if *call_order > *def_order && (*call_order - *def_order) < 64;

    float_arg_setup_candidate(*defaddr, *dst_reg, *call_addr) <--
        ltl_inst(defaddr, ?LTLInst::Lload(_, _, _, dst_reg)),
        is_xmm_arg_reg(dst_reg),
        call_backward_reach(call_addr, defaddr, _),
        instr_in_function(defaddr, func_start),
        instr_min_order(func_start, defaddr, def_order),
        instr_min_order(func_start, call_addr, call_order),
        if *call_order > *def_order && (*call_order - *def_order) < 64;

    relation call_float_arg_setup_detected(Node, Mreg, Node);

    call_float_arg_setup_detected(defaddr, mreg, call_addr) <--
        float_arg_setup_candidate(defaddr, mreg, call_addr),
        ltl_inst(call_addr, ?LTLInst::Lcall(_)),
        !call_clobbers_arg_reg(defaddr, mreg, call_addr);

    call_float_arg_setup_detected(defaddr, mreg, call_addr) <--
        float_arg_setup_candidate(defaddr, mreg, call_addr),
        ltl_inst(call_addr, ?LTLInst::Ltailcall(_)),
        !call_clobbers_arg_reg(defaddr, mreg, call_addr);

    relation call_has_float_arg_evidence(Node, usize);

    call_has_float_arg_evidence(call_addr, 0) <--
        call_float_arg_setup_detected(_, Mreg::X0, call_addr);
    call_has_float_arg_evidence(call_addr, 1) <--
        call_float_arg_setup_detected(_, Mreg::X1, call_addr);
    call_has_float_arg_evidence(call_addr, 2) <--
        call_float_arg_setup_detected(_, Mreg::X2, call_addr);
    call_has_float_arg_evidence(call_addr, 3) <--
        call_float_arg_setup_detected(_, Mreg::X3, call_addr);
    call_has_float_arg_evidence(call_addr, 4) <--
        call_float_arg_setup_detected(_, Mreg::X4, call_addr);
    call_has_float_arg_evidence(call_addr, 5) <--
        call_float_arg_setup_detected(_, Mreg::X5, call_addr);
    call_has_float_arg_evidence(call_addr, 6) <--
        call_float_arg_setup_detected(_, Mreg::X6, call_addr);
    call_has_float_arg_evidence(call_addr, 7) <--
        call_float_arg_setup_detected(_, Mreg::X7, call_addr);

    relation call_float_arg_max_position(Node, usize);

    call_float_arg_max_position(call_addr, max_pos) <--
        call_has_float_arg_evidence(call_addr, _),
        agg max_pos = ascent::aggregators::max(pos) in call_has_float_arg_evidence(call_addr, pos);

    relation call_has_float_arg_at_position(Node, usize);

    call_has_float_arg_at_position(call_addr, 0) <--
        call_float_arg_max_position(call_addr, max_pos);
    call_has_float_arg_at_position(call_addr, 1) <--
        call_float_arg_max_position(call_addr, max_pos), if *max_pos >= 1;
    call_has_float_arg_at_position(call_addr, 2) <--
        call_float_arg_max_position(call_addr, max_pos), if *max_pos >= 2;
    call_has_float_arg_at_position(call_addr, 3) <--
        call_float_arg_max_position(call_addr, max_pos), if *max_pos >= 3;
    call_has_float_arg_at_position(call_addr, 4) <--
        call_float_arg_max_position(call_addr, max_pos), if *max_pos >= 4;
    call_has_float_arg_at_position(call_addr, 5) <--
        call_float_arg_max_position(call_addr, max_pos), if *max_pos >= 5;
    call_has_float_arg_at_position(call_addr, 6) <--
        call_float_arg_max_position(call_addr, max_pos), if *max_pos >= 6;
    call_has_float_arg_at_position(call_addr, 7) <--
        call_float_arg_max_position(call_addr, max_pos), if *max_pos >= 7;

    relation call_float_arg_mapping(Node, usize, RTLReg);

    call_float_arg_mapping(*call_addr, pos, rtl_reg) <--
        call_float_arg_setup_detected(defaddr, dst_reg, call_addr),
        reg_rtl(defaddr, dst_reg, rtl_reg),
        if let Some(pos) = xmm_arg_reg_position(dst_reg),
        call_has_float_arg_at_position(call_addr, pos);

    relation call_float_args_collected(Node, Args);

    call_float_args_collected(call_addr, args) <--
        ltl_inst(call_addr, ?LTLInst::Lcall(_)),
        agg args = build_call_args(pos, reg) in call_float_arg_mapping(call_addr, pos, reg);

    call_float_args_collected(call_addr, args) <--
        ltl_inst(call_addr, ?LTLInst::Ltailcall(_)),
        agg args = build_call_args(pos, reg) in call_float_arg_mapping(call_addr, pos, reg);

    call_float_args_collected(call_addr, Arc::new(vec![])) <--
        ltl_inst(call_addr, ?LTLInst::Lcall(_)),
        !call_float_arg_mapping(call_addr, _, _);

    call_float_args_collected(call_addr, Arc::new(vec![])) <--
        ltl_inst(call_addr, ?LTLInst::Ltailcall(_)),
        !call_float_arg_mapping(call_addr, _, _);


    function_entry_dist(addr, node, 0) <-- emit_function(addr, _, node);

    function_entry_dist(func, next_node, new_dist) <--
        function_entry_dist(func, curr_node, dist),
        next(curr_node, next_node),
        instr_in_function(next_node, func),
        if *dist < FUNC_ARG_DIST,
        let new_dist = dist + 1;


    function_entry_count(func, node, min_dist) <--
        function_entry_dist(func, node, _),
        agg min_dist = ascent::aggregators::min(d) in function_entry_dist(func, node, d);

    lattice instr_order_in_func(Address, Node, ascent::Dual<i64>);

    instr_order_in_func(func, node, ascent::Dual(0)) <-- emit_function(func, _, node);

    instr_order_in_func(func, next_node, ascent::Dual(order.0 + 1)) <--
        instr_order_in_func(func, curr_node, order),
        next(curr_node, next_node),
        instr_in_function(next_node, func);

    instr_order_in_func(func, succ_node, ascent::Dual(order.0 + 1)) <--
        instr_order_in_func(func, curr_node, order),
        ltl_succ(curr_node, succ_node),
        instr_in_function(succ_node, func);

    relation instr_min_order(Address, Node, i64);

    instr_min_order(func, node, min_order) <--
        instr_order_in_func(func, node, order),
        let min_order = order.0;
    

    relation arg_reg_used_early_in_func(Address, Address, Mreg);
    relation func_float_arg_used_undefined(Address, RTLReg);
    relation emit_function_float_param(Address, RTLReg);

    func_float_arg_used_undefined(func_start, id), reg_xtl(func_start, mreg, id) <--
        func_float_param_validated(func_start, mreg, _),
        let id = fresh_xtl_reg(*func_start, *mreg);

    emit_function_float_param(func_start, *canonical) <--
        func_float_arg_used_undefined(func_start, v),
        xtl_canonical(v, canonical);

    arg_reg_used_early_in_func(func_start, addr, *reg) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lop(_, srcs, _)),
        for reg in srcs.iter(),
        is_arg_reg(reg),
        reg_def_used(defaddr, reg, addr),
        !instr_in_function(defaddr, func_start);

    arg_reg_used_early_in_func(func_start, addr, *reg) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lop(_, srcs, _)),
        for reg in srcs.iter(),
        is_arg_reg(reg),
        !reg_def_used(_, reg, addr);

    arg_reg_used_early_in_func(func_start, addr, *arg) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lload(_, _, args, _)),
        for arg in args.iter(),
        is_arg_reg(arg),
        !reg_def_used(_, arg, addr);

    arg_reg_used_early_in_func(func_start, addr, *arg) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lload(_, _, args, _)),
        for arg in args.iter(),
        is_arg_reg(arg),
        reg_def_used(defaddr, arg, addr),
        !instr_in_function(defaddr, func_start);

    arg_reg_used_early_in_func(func_start, addr, *src) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lsetstack(src, _, _, _)),
        is_arg_reg(src),
        reg_def_used(defaddr, src, addr),
        !instr_in_function(defaddr, func_start);

    arg_reg_used_early_in_func(func_start, addr, *src) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lsetstack(src, _, _, _)),
        is_arg_reg(src),
        !reg_def_used(_, src, addr);

    relation arg_reg_has_external_def(Address, Mreg);

    arg_reg_has_external_def(func_start, *mreg) <--
        is_arg_reg(mreg),
        instr_in_function(use_addr, func_start),
        function_entry_count(func_start, use_addr, count),
        if *count < FUNC_ARG_DIST,
        reg_def_used(def_addr, mreg, use_addr),
        !instr_in_function(def_addr, func_start);

    relation arg_reg_used_very_early(Address, Mreg);
    relation arg_reg_has_internal_def_before_early_use(Address, Mreg);

    arg_reg_has_internal_def_before_early_use(func_start, *mreg) <--
        is_arg_reg(mreg),
        instr_in_function(early_use_addr, func_start),
        function_entry_count(func_start, early_use_addr, count),
        if *count < FUNC_ARG_DIST,
        reg_use(early_use_addr, mreg),
        reg_def_used(def_addr, mreg, early_use_addr),
        instr_in_function(def_addr, func_start),
        if *def_addr != *func_start;

    // Per-use check: this specific early use has an internal (non-func_start) def reaching it
    #[local] relation arg_reg_use_has_internal_def(Address, Address, Mreg);

    arg_reg_use_has_internal_def(func_start, early_use_addr, *mreg) <--
        is_arg_reg(mreg),
        instr_in_function(early_use_addr, func_start),
        function_entry_count(func_start, early_use_addr, count),
        if *count < FUNC_ARG_DIST,
        reg_use(early_use_addr, mreg),
        reg_def_used(def_addr, mreg, early_use_addr),
        instr_in_function(def_addr, func_start),
        if *def_addr != *func_start;

    arg_reg_used_very_early(func_start, *mreg) <--
        is_arg_reg(mreg),
        instr_in_function(early_addr, func_start),
        function_entry_count(func_start, early_addr, count),
        if *count < FUNC_ARG_DIST,
        reg_use(early_addr, mreg),
        !arg_reg_use_has_internal_def(func_start, early_addr, mreg);

    relation arg_reg_used_no_def(Address, Mreg);

    arg_reg_used_no_def(func_start, mreg) <--
        is_arg_reg(mreg),
        instr_in_function(use_addr, func_start),
        function_entry_count(func_start, use_addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst_uses_mreg(use_addr, mreg),
        !reg_def_used(_, mreg, use_addr);

    relation arg_reg_spilled_to_stack(Address, Mreg);

    arg_reg_spilled_to_stack(func_start, *src) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lsetstack(src, _slot, _ofs, _typ)),
        is_arg_reg(src),
        reg_def_used(defaddr, src, addr),
        !instr_in_function(defaddr, func_start);

    arg_reg_spilled_to_stack(func_start, *src) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lsetstack(src, _slot, _ofs, _typ)),
        is_arg_reg(src),
        !reg_def_used(_, src, addr);

    arg_reg_spilled_to_stack(func_start, *src) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lstore(_, Addressing::Ainstack(_), _, src)),
        is_arg_reg(src),
        reg_def_used(defaddr, src, addr),
        !instr_in_function(defaddr, func_start);

    arg_reg_spilled_to_stack(func_start, *src) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lstore(_, Addressing::Ainstack(_), _, src)),
        is_arg_reg(src),
        !reg_def_used(_, src, addr);

    arg_reg_spilled_to_stack(func_start, *src) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lstore(_, Addressing::Aindexed(ofs), args, src)),
        if *ofs < 0,   
        for arg in args.iter(),
        if *arg == Mreg::BP,
        is_arg_reg(src),
        reg_def_used(defaddr, src, addr),
        !instr_in_function(defaddr, func_start);

    arg_reg_spilled_to_stack(func_start, *src) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lstore(_, Addressing::Aindexed(ofs), args, src)),
        if *ofs < 0,
        for arg in args.iter(),
        if *arg == Mreg::BP,
        is_arg_reg(src),
        !reg_def_used(_, src, addr);

    relation arg_reg_copied_early(Address, Mreg, Mreg);
    relation arg_reg_used_via_copy(Address, Mreg);

    arg_reg_copied_early(func_start, *src, *dst) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lop(Operation::Omove, srcs, dst)),
        if srcs.len() == 1,
        for src in srcs.iter(),
        is_arg_reg(src),
        !is_arg_reg(dst),
        if *dst != Mreg::SP && *dst != Mreg::BP,
        reg_def_used(defaddr, src, addr),
        !instr_in_function(defaddr, func_start);

    arg_reg_copied_early(func_start, *src, *dst) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lop(Operation::Omove, srcs, dst)),
        if srcs.len() == 1,
        for src in srcs.iter(),
        is_arg_reg(src),
        !is_arg_reg(dst),
        if *dst != Mreg::SP && *dst != Mreg::BP,
        !reg_def_used(_, src, addr);

    arg_reg_used_via_copy(func_start, *arg_reg) <--
        arg_reg_copied_early(func_start, arg_reg, dst_reg),
        instr_in_function(use_addr, func_start),
        function_entry_count(func_start, use_addr, count),
        if *count < 512,   
        reg_use(use_addr, dst_reg);

    relation func_arg_reg_used(Address, Mreg);

    func_arg_reg_used(func_start, mreg) <--
        arg_reg_used_early_in_func(func_start, _, mreg);

    func_arg_reg_used(func_start, mreg) <--
        arg_reg_has_external_def(func_start, mreg);

    func_arg_reg_used(func_start, mreg) <--
        arg_reg_used_no_def(func_start, mreg);

    func_arg_reg_used(func_start, mreg) <--
        arg_reg_used_very_early(func_start, mreg);

    func_arg_reg_used(func_start, mreg) <--
        arg_reg_spilled_to_stack(func_start, mreg);

    func_arg_reg_used(func_start, mreg) <--
        arg_reg_used_via_copy(func_start, mreg);


    relation is_float_arg_reg(Mreg);

    is_float_arg_reg(Mreg::X0);
    is_float_arg_reg(Mreg::X1);
    is_float_arg_reg(Mreg::X2);
    is_float_arg_reg(Mreg::X3);
    is_float_arg_reg(Mreg::X4);
    is_float_arg_reg(Mreg::X5);
    is_float_arg_reg(Mreg::X6);
    is_float_arg_reg(Mreg::X7);

    relation func_float_param_used(Address, Mreg);

    func_float_param_used(func_start, *mreg) <--
        is_float_arg_reg(mreg),
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst_uses_mreg(addr, mreg),
        !reg_def_used(_, mreg, addr);

    func_float_param_used(func_start, *mreg) <--
        is_float_arg_reg(mreg),
        instr_in_function(use_addr, func_start),
        function_entry_count(func_start, use_addr, count),
        if *count < FUNC_ARG_DIST,
        reg_def_used(def_addr, mreg, use_addr),
        !instr_in_function(def_addr, func_start);

    relation func_float_param_validated(Address, Mreg, usize);

    func_float_param_validated(func_start, Mreg::X0, 0) <--
        func_float_param_used(func_start, Mreg::X0);

    func_float_param_validated(func_start, Mreg::X1, 1) <--
        func_float_param_used(func_start, Mreg::X1),
        func_float_param_validated(func_start, Mreg::X0, 0);

    func_float_param_validated(func_start, Mreg::X2, 2) <--
        func_float_param_used(func_start, Mreg::X2),
        func_float_param_validated(func_start, Mreg::X1, 1);

    func_float_param_validated(func_start, Mreg::X3, 3) <--
        func_float_param_used(func_start, Mreg::X3),
        func_float_param_validated(func_start, Mreg::X2, 2);

    func_float_param_validated(func_start, Mreg::X4, 4) <--
        func_float_param_used(func_start, Mreg::X4),
        func_float_param_validated(func_start, Mreg::X3, 3);

    func_float_param_validated(func_start, Mreg::X5, 5) <--
        func_float_param_used(func_start, Mreg::X5),
        func_float_param_validated(func_start, Mreg::X4, 4);

    func_float_param_validated(func_start, Mreg::X6, 6) <--
        func_float_param_used(func_start, Mreg::X6),
        func_float_param_validated(func_start, Mreg::X5, 5);

    func_float_param_validated(func_start, Mreg::X7, 7) <--
        func_float_param_used(func_start, Mreg::X7),
        func_float_param_validated(func_start, Mreg::X6, 6);

    relation emit_function_float_param_count(Address, usize);

    emit_function_float_param_count(func_start, count) <--
        func_float_param_validated(func_start, _, _),
        agg count = ascent::aggregators::count() in func_float_param_validated(func_start, _, _);

    emit_function_float_param_count(func_start, 0) <--
        emit_function(func_start, _, _),
        !func_float_param_validated(func_start, _, _);


    relation stack_passed_param(Address, i64);

    stack_passed_param(func_start, *ofs) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < 512,
        ltl_inst(addr, ?LTLInst::Lload(_, Addressing::Aindexed(ofs), args, _)),
        for arg in args.iter(),
        if *arg == Mreg::BP && *ofs > 0;

    relation emit_function_stack_param_count(Address, usize);

    emit_function_stack_param_count(func_start, count) <--
        stack_passed_param(func_start, _),
        agg count = ascent::aggregators::count() in stack_passed_param(func_start, _);

    emit_function_stack_param_count(func_start, 0) <--
        emit_function(func_start, _, _),
        !stack_passed_param(func_start, _);


    relation param_struct_field_access(Address, Mreg, i64, u8);

    param_struct_field_access(func_start, *param_reg, *ofs, size) <--
        func_param_validated(func_start, param_reg),
        instr_in_function(addr, func_start),
        ltl_inst(addr, ?LTLInst::Lload(chunk, Addressing::Aindexed(ofs), args, _)),
        if args.len() > 0 && args[0] == *param_reg,   
        let size = chunk_size_bits(chunk);

    param_struct_field_access(func_start, *param_reg, *ofs, size) <--
        func_param_validated(func_start, param_reg),
        arg_reg_copied_early(func_start, param_reg, copy_dst),
        instr_in_function(addr, func_start),
        ltl_inst(addr, ?LTLInst::Lload(chunk, Addressing::Aindexed(ofs), args, _)),
        if args.len() > 0 && args[0] == *copy_dst,
        let size = chunk_size_bits(chunk);

    param_struct_field_access(func_start, *param_reg, *ofs, size) <--
        func_param_validated(func_start, param_reg),
        instr_in_function(addr, func_start),
        ltl_inst(addr, ?LTLInst::Lstore(chunk, Addressing::Aindexed(ofs), args, _)),
        for arg in args.iter(),
        if *arg == *param_reg,
        let size = chunk_size_bits(chunk);

    param_struct_field_access(func_start, *param_reg, *ofs, size) <--
        func_param_validated(func_start, param_reg),
        arg_reg_copied_early(func_start, param_reg, copy_dst),
        instr_in_function(addr, func_start),
        ltl_inst(addr, ?LTLInst::Lstore(chunk, Addressing::Aindexed(ofs), args, _)),
        for arg in args.iter(),
        if *arg == *copy_dst,
        let size = chunk_size_bits(chunk);

    relation param_is_struct_pointer(Address, Mreg);

    param_is_struct_pointer(func_start, mreg) <--
        param_struct_field_access(func_start, mreg, ofs1, _),
        param_struct_field_access(func_start, mreg, ofs2, _),
        if ofs1 != ofs2;

    param_is_struct_pointer(func_start, mreg) <--
        param_struct_field_access(func_start, mreg, _, _),
        param_used_in_deref(func_start, mreg);

    relation dx_has_non_div_use(Address);

    dx_has_non_div_use(func_start) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lop(_, args, _)),
        for arg in args.iter(),
        if *arg == Mreg::DX,
        !pdiv(addr, _, _);

    dx_has_non_div_use(func_start) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lstore(_, _, _, src)),
        if *src == Mreg::DX,
        !pdiv(addr, _, _);

    dx_has_non_div_use(func_start) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lload(_, _, args, _)),
        for arg in args.iter(),
        if *arg == Mreg::DX;

    dx_has_non_div_use(func_start) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lcond(_, args, _, _)),
        for arg in args.iter(),
        if *arg == Mreg::DX;

    dx_has_non_div_use(func_start) <--
        arg_reg_copied_early(func_start, ?Mreg::DX, _);

    relation dx_used_only_in_div(Address);

    dx_used_only_in_div(func_start) <--
        func_arg_reg_used(func_start, Mreg::DX),
        !arg_reg_spilled_to_stack(func_start, Mreg::DX),
        !dx_has_non_div_use(func_start),
        func_has_div_instr(func_start);

    // CX filter: suppress CX as param evidence when it's only used as shift/rotate count
    relation func_has_shift_instr(Address);

    func_has_shift_instr(func_start) <--
        instr_in_function(addr, func_start),
        ltl_inst(addr, ?LTLInst::Lop(op, args, _)),
        for arg in args.iter(),
        if *arg == Mreg::CX,
        if is_shift_or_rotate_op(op);

    relation cx_has_non_shift_use(Address);

    cx_has_non_shift_use(func_start) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lop(op, args, _)),
        for arg in args.iter(),
        if *arg == Mreg::CX,
        if !is_shift_or_rotate_op(op);

    cx_has_non_shift_use(func_start) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lstore(_, _, _, src)),
        if *src == Mreg::CX;

    cx_has_non_shift_use(func_start) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lload(_, _, args, _)),
        for arg in args.iter(),
        if *arg == Mreg::CX;

    cx_has_non_shift_use(func_start) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lcond(_, args, _, _)),
        for arg in args.iter(),
        if *arg == Mreg::CX;

    cx_has_non_shift_use(func_start) <--
        arg_reg_copied_early(func_start, ?Mreg::CX, _);

    relation cx_used_only_in_shift(Address);

    cx_used_only_in_shift(func_start) <--
        func_arg_reg_used(func_start, Mreg::CX),
        !arg_reg_spilled_to_stack(func_start, Mreg::CX),
        !cx_has_non_shift_use(func_start),
        func_has_shift_instr(func_start);

    // Scratch register filter: reg defined before use in entry block is not a parameter.
    relation arg_reg_first_action_is_def(Address, Mreg);
    #[local] relation arg_reg_used_strictly_before(Address, Mreg, Address);

    // There exists a use of mreg at use_addr that is strictly before def_addr (by entry count)
    arg_reg_used_strictly_before(func_start, *mreg, *def_addr) <--
        is_arg_reg(mreg),
        instr_in_function(use_addr, func_start),
        function_entry_count(func_start, use_addr, use_count),
        if *use_count < FUNC_ARG_DIST,
        reg_use(use_addr, mreg),
        instr_in_function(def_addr, func_start),
        function_entry_count(func_start, def_addr, def_count),
        if *def_count < FUNC_ARG_DIST,
        asm_effective_def(def_addr, mreg),
        if use_count < def_count;

    // The register's first action in the entry block is a definition (no use precedes it)
    arg_reg_first_action_is_def(func_start, *mreg) <--
        is_arg_reg(mreg),
        instr_in_function(def_addr, func_start),
        function_entry_count(func_start, def_addr, def_count),
        if *def_count < FUNC_ARG_DIST,
        asm_effective_def(def_addr, mreg),
        !arg_reg_spilled_to_stack(func_start, mreg),
        !arg_reg_used_strictly_before(func_start, mreg, def_addr);

    // Func param positions use max-evidence: all positions up to max are filled per ABI
    relation func_has_param_evidence(Address, usize);

    func_has_param_evidence(func_start, 0) <--
        func_arg_reg_used(func_start, Mreg::DI);

    func_has_param_evidence(func_start, 1) <--
        func_arg_reg_used(func_start, Mreg::SI),
        !arg_reg_first_action_is_def(func_start, Mreg::SI);

    func_has_param_evidence(func_start, 2) <--
        func_arg_reg_used(func_start, Mreg::DX),
        !dx_used_only_in_div(func_start),
        !arg_reg_first_action_is_def(func_start, Mreg::DX);

    func_has_param_evidence(func_start, 3) <--
        func_arg_reg_used(func_start, Mreg::CX),
        !cx_used_only_in_shift(func_start),
        !arg_reg_first_action_is_def(func_start, Mreg::CX);

    func_has_param_evidence(func_start, 4) <--
        func_arg_reg_used(func_start, Mreg::R8),
        !arg_reg_first_action_is_def(func_start, Mreg::R8);

    func_has_param_evidence(func_start, 5) <--
        func_arg_reg_used(func_start, Mreg::R9),
        !arg_reg_first_action_is_def(func_start, Mreg::R9);

    relation func_max_param_position(Address, usize);

    func_max_param_position(func_start, max_pos) <--
        func_has_param_evidence(func_start, _),
        agg max_pos = ascent::aggregators::max(pos) in func_has_param_evidence(func_start, pos);

    relation func_has_param_at_position(Address, usize);

    func_has_param_at_position(func_start, 0) <--
        func_max_param_position(func_start, _max_pos);

    func_has_param_at_position(func_start, 1) <--
        func_max_param_position(func_start, max_pos),
        if *max_pos >= 1;

    func_has_param_at_position(func_start, 2) <--
        func_max_param_position(func_start, max_pos),
        if *max_pos >= 2;

    func_has_param_at_position(func_start, 3) <--
        func_max_param_position(func_start, max_pos),
        if *max_pos >= 3;

    func_has_param_at_position(func_start, 4) <--
        func_max_param_position(func_start, max_pos),
        if *max_pos >= 4;

    func_has_param_at_position(func_start, 5) <--
        func_max_param_position(func_start, max_pos),
        if *max_pos >= 5;

    relation func_param_validated(Address, Mreg);

    func_param_validated(func_start, Mreg::DI) <--
        func_has_param_at_position(func_start, 0);

    func_param_validated(func_start, Mreg::SI) <--
        func_has_param_at_position(func_start, 1);

    func_param_validated(func_start, Mreg::DX) <--
        func_has_param_at_position(func_start, 2);

    func_param_validated(func_start, Mreg::CX) <--
        func_has_param_at_position(func_start, 3);

    func_param_validated(func_start, Mreg::R8) <--
        func_has_param_at_position(func_start, 4);

    func_param_validated(func_start, Mreg::R9) <--
        func_has_param_at_position(func_start, 5);

    relation param_register_width(Address, Mreg, u8);

    param_register_width(func_start, *src, width) <--
        arg_reg_spilled_to_stack(func_start, src),
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lstore(chunk, Addressing::Ainstack(_), _, store_src)),
        if *store_src == *src,
        let width = chunk_size_bits(chunk);

    param_register_width(func_start, *src, width) <--
        arg_reg_spilled_to_stack(func_start, src),
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lstore(chunk, Addressing::Aindexed(ofs), args, store_src)),
        if *ofs < 0,
        for arg in args.iter(),
        if *arg == Mreg::BP,
        if *store_src == *src,
        let width = chunk_size_bits(chunk);

    param_register_width(func_start, *src, width) <--
        arg_reg_spilled_to_stack(func_start, src),
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < FUNC_ARG_DIST,
        ltl_inst(addr, ?LTLInst::Lsetstack(set_src, _slot, _ofs, typ)),
        if *set_src == *src,
        let width = match typ { 
            crate::x86::types::Typ::Tint | crate::x86::types::Typ::Tany32 => 32,
            crate::x86::types::Typ::Tlong | crate::x86::types::Typ::Tany64 => 64,
            crate::x86::types::Typ::Tfloat => 64,
            crate::x86::types::Typ::Tsingle => 32,
            _ => 64
        };

    relation param_inferred_type_is_int32(Address, Mreg);

    param_inferred_type_is_int32(func_start, mreg) <--
        param_register_width(func_start, mreg, 32);

    relation param_inferred_type_is_int64_or_ptr(Address, Mreg);

    param_inferred_type_is_int64_or_ptr(func_start, mreg) <--
        param_register_width(func_start, mreg, 64);

    relation func_arg_used_undefined(Address, RTLReg);

    func_arg_used_undefined(func_start, id), reg_xtl(func_start, mreg, id) <--
        func_param_validated(func_start, mreg),
        let id = fresh_xtl_reg(*func_start, *mreg);


    relation param_used_in_deref(Address, Mreg);

    // Only check base register (args[0]) for pointer not index
    param_used_in_deref(func_start, *arg_reg) <--
        func_param_validated(func_start, arg_reg),
        instr_in_function(addr, func_start),
        ltl_inst(addr, ?LTLInst::Lload(_, _, args, _)),
        if !args.is_empty() && args[0] == *arg_reg;

    param_used_in_deref(func_start, *arg_reg) <--
        func_param_validated(func_start, arg_reg),
        arg_reg_copied_early(func_start, arg_reg, copy_dst),
        instr_in_function(addr, func_start),
        ltl_inst(addr, ?LTLInst::Lload(_, _, args, _)),
        if !args.is_empty() && args[0] == *copy_dst;

    param_used_in_deref(func_start, *arg_reg) <--
        func_param_validated(func_start, arg_reg),
        instr_in_function(addr, func_start),
        ltl_inst(addr, ?LTLInst::Lstore(_, _, args, _)),
        if !args.is_empty() && args[0] == *arg_reg;

    param_used_in_deref(func_start, *arg_reg) <--
        func_param_validated(func_start, arg_reg),
        arg_reg_copied_early(func_start, arg_reg, copy_dst),
        instr_in_function(addr, func_start),
        ltl_inst(addr, ?LTLInst::Lstore(_, _, args, _)),
        if !args.is_empty() && args[0] == *copy_dst;

    relation param_used_in_lea(Address, Mreg);

    // Only check base register (srcs[0]) for lea pointer evidence
    param_used_in_lea(func_start, *src_reg) <--
        func_param_validated(func_start, src_reg),
        instr_in_function(addr, func_start),
        ltl_inst(addr, ?LTLInst::Lop(op, srcs, _)),
        if matches!(op, Operation::Olea(_) | Operation::Oleal(_)),
        if !srcs.is_empty() && srcs[0] == *src_reg;

    relation param_used_in_null_check(Address, Mreg);

    param_used_in_null_check(func_start, *arg_reg) <--
        func_param_validated(func_start, arg_reg),
        instr_in_function(addr, func_start),
        ltl_inst(addr, ?LTLInst::Lop(op, srcs, _)),
        if is_null_comparison_op(op),
        for reg in srcs.iter(),
        if *reg == *arg_reg;

    relation param_used_in_arithmetic(Address, Mreg);

    param_used_in_arithmetic(func_start, *arg_reg) <--
        func_param_validated(func_start, arg_reg),
        instr_in_function(addr, func_start),
        ltl_inst(addr, ?LTLInst::Lop(op, srcs, _)),
        if is_arithmetic_op(op),
        for reg in srcs.iter(),
        if *reg == *arg_reg;

    relation param_type_evidence_pointer(Address, Mreg);

    param_type_evidence_pointer(func_start, mreg) <--
        param_used_in_deref(func_start, mreg);

    param_type_evidence_pointer(func_start, mreg) <--
        param_used_in_lea(func_start, mreg);

    param_type_evidence_pointer(func_start, mreg) <--
        param_used_in_null_check(func_start, mreg);

    relation param_inferred_type_is_pointer(Address, Mreg);
    relation param_inferred_type_is_integer(Address, Mreg);

    param_inferred_type_is_pointer(func_start, mreg) <--
        func_param_validated(func_start, mreg),
        param_type_evidence_pointer(func_start, mreg);

    param_inferred_type_is_integer(func_start, mreg) <--
        func_param_validated(func_start, mreg),
        !param_type_evidence_pointer(func_start, mreg);

    relation emit_function_param_candidate(Address, RTLReg);
    relation emit_function_param_is_pointer_candidate(Address, RTLReg);
    relation emit_function_return(Address, RTLReg);
    relation emit_function_has_return_candidate(Address);
    relation emit_function_void_candidate(Address);
    relation emit_function_return_type_candidate(Address, ClightType);

    emit_function(func_start, *name, func_start) <--
        func_stacksz(func_start, _func_end, name, stacksize);

    emit_function_param_candidate(func_start, *canonical) <--
        func_stacksz(func_start, _func_end, name, stacksize),
        func_arg_used_undefined(func_start, v),
        xtl_canonical(v, canonical);

    emit_function_param_candidate(func_start, *canonical) <--
        func_float_arg_used_undefined(func_start, v),
        xtl_canonical(v, canonical);

    emit_function_param_is_pointer_candidate(func_start, *canonical) <--
        emit_function_param_candidate(func_start, canonical),
        func_arg_used_undefined(func_start, raw_v),
        xtl_canonical(raw_v, canonical),
        reg_xtl(func_start, mreg, raw_v),
        param_inferred_type_is_pointer(func_start, mreg);


    relation function_return_point_reg(Address, Node, RTLReg);   

    function_return_point_reg(func_start, addr, rtl_reg) <--
        emit_function(func_start, _, entry_node),
        instr_in_function(addr, func_start),
        ltl_inst(addr, LTLInst::Lreturn),
        ax_value_addr(addr, defaddr),
        reg_rtl(defaddr, Mreg::AX, rtl_reg);

    emit_function_return(func_start, min_ret) <--
        function_return_point_reg(func_start, _, _),
        agg min_ret = ascent::aggregators::min(ret) in function_return_point_reg(func_start, _, ret);

    emit_function_has_return_candidate(addr) <--
        emit_function_return(addr, _);

    relation emit_function_param_type_candidate(Address, RTLReg, XType);

    emit_function_param_type_candidate(func_start, param_rtl, xtype) <--
        emit_function_param_candidate(func_start, param_rtl),
        emit_var_type_candidate(param_rtl, xtype);

    emit_function_param_type_candidate(func_start, param_rtl, XType::Xfloat) <--
        emit_function_float_param(func_start, param_rtl),
        !emit_var_type_candidate(param_rtl, _);

    relation emit_function_return_type_xtype_candidate(Address, XType);

    emit_function_return_type_xtype_candidate(func_start, xtype) <--
        emit_function_return(func_start, ret_rtl),
        emit_var_type_candidate(ret_rtl, xtype);

    emit_function_return_type_xtype_candidate(callee_func, xtype) <--
        ltl_inst(call_addr, ?LTLInst::Lcall(Either::Right(Either::Left(callee_func)))),
        call_return_reg(call_addr, ret_rtl),
        emit_var_type_candidate(ret_rtl, xtype),
        if *xtype != XType::Xvoid,
        !emit_function_return(callee_func, _);

    emit_function_return_type_candidate(func_start, clight_ty) <--
        emit_function_return_type_xtype_candidate(func_start, xtype),
        let clight_ty = clight_type_from_xtype(xtype);


    relation called_address(Address);

    called_address(target) <--
        ltl_inst(_caller, ?LTLInst::Lcall(Either::Right(Either::Left(target)))),
        instr_in_function(target, _);

    called_address(target2) <--
        ltl_inst(_caller2, ?LTLInst::Ltailcall(Either::Right(Either::Left(target2)))),
        instr_in_function(target2, _);

    emit_function(func_entry, *sym_name, func_entry) <--
        called_address(func_entry),
        !func_stacksz(func_entry, _, _, _),
        !plt_entry(func_entry, _),
        !plt_block(func_entry, _),
        symbols(func_entry, sym_name, _);

    emit_function(func_entry, func_name, func_entry) <--
        called_address(func_entry),
        !func_stacksz(func_entry, _, _, _),
        !plt_entry(func_entry, _),
        !plt_block(func_entry, _),
        !symbols(func_entry, _, _),
        let func_name = Box::leak(format!("FUN_{:x}", func_entry).into_boxed_str()) as Symbol;

    emit_function(addr, *sym_name, addr) <--
        symbols(addr, sym_name, _),
        instr_in_function(addr, addr),
        !func_stacksz(addr, _, _, _),
        !called_address(addr),
        !plt_entry(addr, _),
        !plt_block(addr, _);

    relation undiscovered_func_call(Address, Address);

    undiscovered_func_call(discovered_tgt, call_location) <--
        called_address(discovered_tgt),
        !func_stacksz(discovered_tgt, _, _, _),
        ltl_inst(call_location, ?LTLInst::Lcall(Either::Right(Either::Left(call_tgt)))),
        if *discovered_tgt == *call_tgt;

    undiscovered_func_call(discovered_tgt2, call_location2) <--
        called_address(discovered_tgt2),
        !func_stacksz(discovered_tgt2, _, _, _),
        ltl_inst(call_location2, ?LTLInst::Ltailcall(Either::Right(Either::Left(call_tgt2)))),
        if *discovered_tgt2 == *call_tgt2;

    emit_function_void_candidate(undiscov_addr2) <--
        called_address(undiscov_addr2),
        !func_stacksz(undiscov_addr2, _, _, _),
        instr_in_function(ret_point2, undiscov_addr2),
        ltl_inst(ret_point2, ?LTLInst::Lreturn),
        !reg_rtl(ret_point2, Mreg::AX, _);


    relation func_is_variadic(Address);
    relation func_arg_reg_spill_count(Address, usize);

    func_arg_reg_spill_count(func_start, count) <--
        arg_reg_spilled_to_stack(func_start, _),
        agg count = ascent::aggregators::count() in arg_reg_spilled_to_stack(func_start, _);

    func_is_variadic(func_start) <--
        func_arg_reg_spill_count(func_start, count),
        if *count >= 5;


    relation is_stack_canary_related(Address);

    is_stack_canary_related(addr) <--
        instr_in_function(addr, func_start),
        if func_start.abs_diff(*addr) < 32,   
        ltl_inst(addr, ?LTLInst::Lload(_, Addressing::Ainstack(ofs), _, _)),
        if *ofs == -8;   

    is_stack_canary_related(addr) <--
        ltl_inst(ret_addr, ?LTLInst::Lreturn),
        instr_in_function(ret_addr, func_start),
        instr_in_function(addr, func_start),
        if ret_addr.abs_diff(*addr) < 32,   
        ltl_inst(addr, ?LTLInst::Lop(op, _, _)),
        if matches!(op, Operation::Osub | Operation::Osubl);

    is_stack_canary_related(addr) <--
        instr_in_function(addr, func_start),
        function_entry_count(func_start, addr, count),
        if *count < 16,   
        ltl_inst(addr, ?LTLInst::Lload(_, _, _, dst)),
        ltl_succ(addr, store_addr),
        ltl_inst(store_addr, ?LTLInst::Lstore(_, Addressing::Ainstack(ofs), _, src)),
        if *src == *dst && *ofs == -8;

    relation emit_function_param_count_candidate(Address, usize);

    // Total param count includes both register and stack-passed params
    emit_function_param_count_candidate(target_addr, reg_count + *stack_count) <--
        emit_function_param_candidate(target_addr, _),
        agg reg_count = ascent::aggregators::count() in emit_function_param_candidate(target_addr, _),
        emit_function_stack_param_count(target_addr, stack_count);

    emit_function_param_count_candidate(target_addr, *stack_count) <--
        emit_function(target_addr, _, _),
        !emit_function_param_candidate(target_addr, _),
        emit_function_stack_param_count(target_addr, stack_count);


    is_ptr(reg) <-- op_produces_ptr(_, reg);
    is_ptr(reg) <-- base_addr_usage(_, reg, _);
    is_not_ptr(reg) <-- op_produces_data(_, reg);

    is_not_ptr(reg) <--
        comparison_operand(_, cond, reg),
        if matches!(cond, Condition::Ccomp(_) | Condition::Ccompu(_)
            | Condition::Ccompimm(_, _) | Condition::Ccompuimm(_, _)),
        if !is_null_comparison_cond(cond);

    must_be_ptr(reg) <-- arg_constrained_as_ptr(_, reg);
    must_be_ptr(ret_reg) <--
        call_site(node, func_name),
        call_return_reg(node, ret_reg),
        known_func_returns_ptr(func_name);
    must_be_ptr(rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Oindirectsymbol(_), _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);


    arg_constrained_as_ptr(node, arg_reg) <--
        call_site(node, func_name),
        call_arg(node, arg_idx, arg_reg),
        known_func_param_is_ptr(func_name, arg_idx);

    is_ptr(reg) <-- arg_constrained_as_ptr(_, reg);

    is_char_ptr(arg_reg) <--
        call_site(node, func_name),
        call_arg(node, arg_idx, arg_reg),
        known_extern_signature(func_name, _, _, params),
        if *arg_idx < params.len(),
        if matches!(params[*arg_idx], XType::Xcharptr);

    is_ptr(ret_reg) <--
        call_site(node, func_name),
        call_return_reg(node, ret_reg),
        known_func_returns_ptr(func_name);

    is_char_ptr(ret_reg) <--
        call_site(node, func_name),
        call_return_reg(node, ret_reg),
        known_extern_signature(func_name, _, ret_type, _),
        if matches!(ret_type, XType::Xcharptr);

    is_ptr(b) <--
        is_ptr(a),
        alias_edge(a, b),
        !is_not_ptr(b);

    is_ptr(a) <--
        is_ptr(b),
        alias_edge(a, b),
        !is_not_ptr(a);

    is_not_ptr(b) <--
        is_not_ptr(a),
        alias_edge(a, b),
        !must_be_ptr(b);

    is_not_ptr(a) <--
        is_not_ptr(b),
        alias_edge(a, b),
        !must_be_ptr(a);

    is_char_ptr(b) <--
        is_char_ptr(a),
        alias_edge(a, b),
        !is_not_ptr(b);

    is_char_ptr(a) <--
        is_char_ptr(b),
        alias_edge(a, b),
        !is_not_ptr(a);


    is_int(reg) <-- op_produces_int(_, reg);
    is_long(reg) <-- op_produces_long(_, reg);
    is_float(reg) <-- op_produces_float(_, reg);
    is_single(reg) <-- op_produces_single(_, reg);
    is_bool(reg) <-- op_produces_bool(_, reg);
    is_int8signed(reg) <-- op_produces_int8signed(_, reg);
    is_int8unsigned(reg) <-- op_produces_int8unsigned(_, reg);
    is_int16signed(reg) <-- op_produces_int16signed(_, reg);
    is_int16unsigned(reg) <-- op_produces_int16unsigned(_, reg);

    is64bit(reg) <-- op_produces_float(_, reg);
    is64bit(reg) <-- op_produces_long(_, reg);
    is32bit(reg) <-- op_produces_int(_, reg);
    is32bit(reg) <-- op_produces_single(_, reg);


    op_produces_data(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(op, _, dst_mreg)),
        if (is_int_operation(op) || is_long_operation(op)) && !is_pointer_operation(op),
        reg_rtl(node, *dst_mreg, rtl_reg);


    op_produces_int8signed(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ocast8signed, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_int8unsigned(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ocast8unsigned, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_int16signed(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ocast16signed, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_int16unsigned(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ocast16unsigned, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_long(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ocast32signed, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_long(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ocast32unsigned, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_int(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(op, _, dst_mreg)),
        if is_int_operation(op) && !matches!(op,
            Operation::Ocast8signed | Operation::Ocast8unsigned |
            Operation::Ocast16signed | Operation::Ocast16unsigned),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_long(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(op, _, dst_mreg)),
        if is_long_operation(op) && !matches!(op,
            Operation::Ocast32signed | Operation::Ocast32unsigned |
            Operation::Oleal(_)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_float(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(op, _, dst_mreg)),
        if is_float_operation(op),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_single(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(op, _, dst_mreg)),
        if is_single_operation(op),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_bool(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(op, _, dst_mreg)),
        if is_boolean_operation(op),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_ptr(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Olea(_), _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_ptr(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Oleal(_), _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_ptr(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Oindirectsymbol(_), _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_int(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ointconst(_), _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_long(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Olongconst(_), _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_float(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ofloatconst(_), _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_single(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Osingleconst(_), _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_int(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ointoffloat, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_int(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ointofsingle, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_long(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Olongoffloat, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_long(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Olongofsingle, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_float(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ofloatofint, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_float(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ofloatoflong, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_float(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ofloatofsingle, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_single(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Osingleoffloat, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_single(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Osingleofint, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_single(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Osingleoflong, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_long(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Omakelong, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_int(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Olowlong, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_int(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ohighlong, _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);


    op_produces_int(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, _, _, src_mreg)),
        if matches!(chunk, MemoryChunk::MInt32 | MemoryChunk::MAny32),
        reg_rtl(node, *src_mreg, rtl_reg);

    op_produces_long(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, _, _, src_mreg)),
        if matches!(chunk, MemoryChunk::MInt64 | MemoryChunk::MAny64),
        reg_rtl(node, *src_mreg, rtl_reg);

    op_produces_float(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, _, _, src_mreg)),
        if matches!(chunk, MemoryChunk::MFloat64),
        reg_rtl(node, *src_mreg, rtl_reg);

    op_produces_single(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, _, _, src_mreg)),
        if matches!(chunk, MemoryChunk::MFloat32),
        reg_rtl(node, *src_mreg, rtl_reg);

    op_produces_int8signed(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, _, _, src_mreg)),
        if matches!(chunk, MemoryChunk::MInt8Signed),
        reg_rtl(node, *src_mreg, rtl_reg);

    op_produces_int8unsigned(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, _, _, src_mreg)),
        if matches!(chunk, MemoryChunk::MInt8Unsigned | MemoryChunk::MBool),
        reg_rtl(node, *src_mreg, rtl_reg);

    op_produces_int16signed(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, _, _, src_mreg)),
        if matches!(chunk, MemoryChunk::MInt16Signed),
        reg_rtl(node, *src_mreg, rtl_reg);

    op_produces_int16unsigned(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lstore(chunk, _, _, src_mreg)),
        if matches!(chunk, MemoryChunk::MInt16Unsigned),
        reg_rtl(node, *src_mreg, rtl_reg);

    op_produces_int(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, _, _, dst_mreg)),
        if matches!(chunk, MemoryChunk::MInt32 | MemoryChunk::MAny32),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_long(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, _, _, dst_mreg)),
        if matches!(chunk, MemoryChunk::MInt64 | MemoryChunk::MAny64),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_float(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, _, _, dst_mreg)),
        if matches!(chunk, MemoryChunk::MFloat64),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_single(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, _, _, dst_mreg)),
        if matches!(chunk, MemoryChunk::MFloat32),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_int8signed(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, _, _, dst_mreg)),
        if matches!(chunk, MemoryChunk::MInt8Signed),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_int8unsigned(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, _, _, dst_mreg)),
        if matches!(chunk, MemoryChunk::MInt8Unsigned | MemoryChunk::MBool),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_int16signed(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, _, _, dst_mreg)),
        if matches!(chunk, MemoryChunk::MInt16Signed),
        reg_rtl(node, *dst_mreg, rtl_reg);

    op_produces_int16unsigned(node, rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lload(chunk, _, _, dst_mreg)),
        if matches!(chunk, MemoryChunk::MInt16Unsigned),
        reg_rtl(node, *dst_mreg, rtl_reg);


    is_unsigned(rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(op, _, dst_mreg)),
        if is_unsigned_operation(op),
        reg_rtl(node, *dst_mreg, rtl_reg);

    is_signed(rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(op, _, dst_mreg)),
        if is_signed_operation(op),
        reg_rtl(node, *dst_mreg, rtl_reg);

    is_unsigned(rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(op, args, _)),
        if is_unsigned_operation(op),
        for mreg in args.iter(),
        reg_rtl(node, *mreg, rtl_reg);

    is_signed(rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(op, args, _)),
        if is_signed_operation(op),
        for mreg in args.iter(),
        reg_rtl(node, *mreg, rtl_reg);


    relation zero_int_const_reg(RTLReg);

    zero_int_const_reg(rtl_reg) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Ointconst(0), _, dst_mreg)),
        reg_rtl(node, *dst_mreg, rtl_reg);

    zero_int_const_reg(b) <-- zero_int_const_reg(a), alias_edge(a, b);
    zero_int_const_reg(a) <-- zero_int_const_reg(b), alias_edge(a, b);

    relation has_float_int_zero_conflict(RTLReg);
    has_float_int_zero_conflict(reg) <-- zero_int_const_reg(reg), is_int(reg), is_float(reg);
    has_float_int_zero_conflict(reg) <-- zero_int_const_reg(reg), is_long(reg), is_float(reg);
    has_float_int_zero_conflict(reg) <-- zero_int_const_reg(reg), is_int(reg), is_single(reg);
    has_float_int_zero_conflict(reg) <-- zero_int_const_reg(reg), is_long(reg), is_single(reg);


    relation has_type_conflict(RTLReg);
    has_type_conflict(reg) <-- is_ptr(reg), is_not_ptr(reg);
    relation has_float_ptr_conflict(RTLReg);
    has_float_ptr_conflict(reg) <-- is_float(reg), is_ptr(reg);
    has_float_ptr_conflict(reg) <-- is_float(reg), must_be_ptr(reg);
    has_float_ptr_conflict(reg) <-- is_single(reg), is_ptr(reg);
    has_float_ptr_conflict(reg) <-- is_single(reg), must_be_ptr(reg);
    has_long_type(reg) <-- has_type_conflict(reg);
    has_long_type(reg) <-- has_float_ptr_conflict(reg);

    has_ptr_type(reg) <-- is_ptr(reg), !is_not_ptr(reg);
    has_ptr_type(reg) <-- must_be_ptr(reg), !has_type_conflict(reg);
    has_char_ptr_type(reg) <-- is_char_ptr(reg), !is_not_ptr(reg);
    has_char_ptr_type(reg) <-- is_char_ptr(reg), must_be_ptr(reg), !has_type_conflict(reg);
    has_float_type(reg) <-- is_float(reg), !has_float_int_zero_conflict(reg);
    has_single_type(reg) <-- is_single(reg), !has_float_int_zero_conflict(reg);
    has_long_type(reg) <-- is_long(reg);
    has_int_type(reg) <-- is_int(reg);
    has_subint_type(reg) <-- is_int8signed(reg);
    has_subint_type(reg) <-- is_int8unsigned(reg);
    has_subint_type(reg) <-- is_int16signed(reg);
    has_subint_type(reg) <-- is_int16unsigned(reg);

    emit_var_type_candidate(reg, XType::Xcharptr) <--
        has_char_ptr_type(reg);

    emit_var_type_candidate(reg, XType::Xptr) <--
        has_ptr_type(reg),
        !has_char_ptr_type(reg);

    emit_var_type_candidate(reg, XType::Xsingle) <--
        has_single_type(reg),
        !has_ptr_type(reg),
        !has_float_ptr_conflict(reg);

    emit_var_type_candidate(reg, XType::Xfloat) <--
        has_float_type(reg),
        !has_ptr_type(reg),
        !has_single_type(reg),
        !has_float_ptr_conflict(reg);

    emit_var_type_candidate(reg, XType::Xint8signed) <--
        is_int8signed(reg),
        !has_ptr_type(reg),
        !has_float_type(reg),
        !has_single_type(reg);

    emit_var_type_candidate(reg, XType::Xint8unsigned) <--
        is_int8unsigned(reg),
        !has_ptr_type(reg),
        !has_float_type(reg),
        !has_single_type(reg),
        !is_int8signed(reg);

    emit_var_type_candidate(reg, XType::Xint16signed) <--
        is_int16signed(reg),
        !has_ptr_type(reg),
        !has_float_type(reg),
        !has_single_type(reg);

    emit_var_type_candidate(reg, XType::Xint16unsigned) <--
        is_int16unsigned(reg),
        !has_ptr_type(reg),
        !has_float_type(reg),
        !has_single_type(reg),
        !is_int16signed(reg);

    emit_var_type_candidate(reg, XType::Xbool) <--
        is_bool(reg),
        !has_ptr_type(reg),
        !has_float_type(reg),
        !has_single_type(reg),
        !has_long_type(reg),
        !has_int_type(reg),
        !has_subint_type(reg);


    emit_var_type_candidate(reg, XType::Xlongunsigned) <--
        has_long_type(reg),
        is_unsigned(reg),
        !is_signed(reg),
        !has_ptr_type(reg),
        !has_float_type(reg),
        !has_single_type(reg),
        !has_subint_type(reg);

    emit_var_type_candidate(reg, XType::Xlong) <--
        has_long_type(reg),
        !has_ptr_type(reg),
        !has_float_type(reg),
        !has_single_type(reg),
        !has_subint_type(reg),
        !is_unsigned(reg);

    emit_var_type_candidate(reg, XType::Xlong) <--
        has_long_type(reg),
        is_unsigned(reg),
        is_signed(reg),
        !has_ptr_type(reg),
        !has_float_type(reg),
        !has_single_type(reg),
        !has_subint_type(reg);

    emit_var_type_candidate(reg, XType::Xintunsigned) <--
        has_int_type(reg),
        !has_long_type(reg),
        is_unsigned(reg),
        !is_signed(reg),
        !has_ptr_type(reg),
        !has_float_type(reg),
        !has_single_type(reg),
        !has_subint_type(reg);

    emit_var_type_candidate(reg, XType::Xint) <--
        has_int_type(reg),
        !has_long_type(reg),
        !has_ptr_type(reg),
        !has_float_type(reg),
        !has_single_type(reg),
        !has_subint_type(reg),
        !is_unsigned(reg);

    emit_var_type_candidate(reg, XType::Xint) <--
        has_int_type(reg),
        !has_long_type(reg),
        is_unsigned(reg),
        is_signed(reg),
        !has_ptr_type(reg),
        !has_float_type(reg),
        !has_single_type(reg),
        !has_subint_type(reg);

    relation single_def_const(RTLReg, Constant);

    single_def_const(dst_rtl, cst) <--
        rtl_inst_candidate(_, ?RTLInst::Iop(op, args, dst_rtl)),
        if args.is_empty(),
        if let Some(cst) = crate::decompile::passes::cminor_pass::constant_from_operation(op);

    #[local] relation var_used(RTLReg);

    var_used(*reg) <--
        rtl_inst_candidate(_, ?RTLInst::Iop(_, args, _)),
        for reg in args.iter();

    var_used(*reg) <--
        rtl_inst_candidate(_, ?RTLInst::Iload(_, _, args, _)),
        for reg in args.iter();

    var_used(*reg) <--
        rtl_inst_candidate(_, ?RTLInst::Istore(_, _, args, _)),
        for reg in args.iter();
    var_used(*src) <--
        rtl_inst_candidate(_, ?RTLInst::Istore(_, _, _, src));

    var_used(*reg) <--
        rtl_inst_candidate(_, ?RTLInst::Icall(_, callee, _, _, _)),
        if let Either::Left(reg) = callee;
    var_used(*reg) <--
        rtl_inst_candidate(_, ?RTLInst::Icall(_, _, args, _, _)),
        for reg in args.iter();

    var_used(*reg) <--
        rtl_inst_candidate(_, ?RTLInst::Itailcall(_, callee, _)),
        if let Either::Left(reg) = callee;
    var_used(*reg) <--
        rtl_inst_candidate(_, ?RTLInst::Itailcall(_, _, args)),
        for reg in args.iter();

    var_used(*reg) <--
        rtl_inst_candidate(_, ?RTLInst::Icond(_, args, _, _)),
        for reg in args.iter();

    var_used(*reg) <--
        rtl_inst_candidate(_, ?RTLInst::Ijumptable(reg, _));

    var_used(*reg) <--
        rtl_inst_candidate(_, ?RTLInst::Ireturn(reg));

    relation dead_def(RTLReg);
    dead_def(*dst) <--
        rtl_inst_candidate(_, ?RTLInst::Icall(_, _, _, Some(dst), _)),
        !var_used(*dst);

}

pub fn convert_and_push_builtins(db: &mut DecompileDB) {
    let reg_rtl_map: HashMap<(Node, Mreg), RTLReg> = db
        .rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl")
        .map(|(n, m, r)| ((*n, *m), *r))
        .collect();

    let builtin_data: Vec<_> = db
        .rel_iter::<(Node, Symbol, Arc<Vec<BuiltinArg<Mreg>>>, BuiltinArg<Mreg>)>("ltl_builtin_unconverted")
        .cloned()
        .collect();
    let converted = convert_ltl_builtins_to_rtl(&builtin_data, &reg_rtl_map);
    for (node, inst) in converted {
        db.rel_push("rtl_inst_candidate", (node, inst));
    }
}

pub(crate) fn trim_direct_call_args_to_callee_arity(db: &mut DecompileDB) {
    let callee_arity: HashMap<Address, usize> = db
        .rel_iter::<(Address, Signature)>("emit_function_signature_candidate")
        .fold(HashMap::new(), |mut acc, (addr, sig)| {
            acc.entry(*addr)
                .and_modify(|curr| *curr = (*curr).max(sig.sig_args.len()))
                .or_insert(sig.sig_args.len());
            acc
        });

    let call_targets: HashMap<Node, Address> = db
        .rel_iter::<(Node, Address)>("call_target_func")
        .map(|(call_node, target)| (*call_node, *target))
        .collect();

    let filtered_mapping: Vec<(Node, usize, RTLReg)> = db
        .rel_iter::<(Node, usize, RTLReg)>("call_arg_mapping")
        .filter_map(|&(node, pos, reg)| {
            if let Some(&target) = call_targets.get(&node) {
                if let Some(&arity) = callee_arity.get(&target) {
                    if pos >= arity {
                        return None;
                    }
                }
            }
            Some((node, pos, reg))
        })
        .collect();

    db.rel_set(
        "call_arg_mapping",
        filtered_mapping
            .iter()
            .copied()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "call_arg",
        filtered_mapping
            .iter()
            .copied()
            .collect::<ascent::boxcar::Vec<_>>(),
    );

    let mut normalized_mapping: HashMap<(Node, usize), RTLReg> = HashMap::new();
    for (node, pos, reg) in filtered_mapping {
        if let Some(&target) = call_targets.get(&node) {
            if let Some(&arity) = callee_arity.get(&target) {
                debug_assert!(pos < arity);
            }
        }
        normalized_mapping
            .entry((node, pos))
            .and_modify(|curr| *curr = (*curr).max(reg))
            .or_insert(reg);
    }

    let mut args_by_call: HashMap<Node, Vec<(usize, RTLReg)>> = HashMap::new();
    for (&(node, pos), &reg) in &normalized_mapping {
        args_by_call.entry(node).or_default().push((pos, reg));
    }
    let rebuild_args = |node: Node| -> Option<Arc<Vec<RTLReg>>> {
        let mut pairs = args_by_call.get(&node)?.clone();
        pairs.sort_by_key(|(pos, _)| *pos);
        Some(Arc::new(pairs.into_iter().map(|(_, reg)| reg).collect()))
    };

    let mut call_nodes: HashSet<Node> = db
        .rel_iter::<(Node, Arc<Vec<RTLReg>>)>("call_args_collected_candidate")
        .map(|(node, _)| *node)
        .collect();
    call_nodes.extend(args_by_call.keys().copied());

    let mut existing_call_args: HashMap<Node, Arc<Vec<RTLReg>>> = HashMap::new();
    for &(node, ref args) in db.rel_iter::<(Node, Arc<Vec<RTLReg>>)>("call_args_collected_candidate") {
        let should_replace = existing_call_args
            .get(&node)
            .map(|curr| curr.len() < args.len())
            .unwrap_or(true);
        if should_replace {
            existing_call_args.insert(node, args.clone());
        }
    }

    let new_call_args: ascent::boxcar::Vec<(Node, Arc<Vec<RTLReg>>)> = call_nodes
        .into_iter()
        .map(|node| {
            let args = rebuild_args(node)
                .or_else(|| existing_call_args.get(&node).cloned())
                .unwrap_or_else(|| Arc::new(vec![]));
            (node, args)
        })
        .collect();
    db.rel_set("call_args_collected_candidate", new_call_args);

    let mut rebuilt_args: HashMap<Node, Arc<Vec<RTLReg>>> = db
        .rel_iter::<(Node, Arc<Vec<RTLReg>>)>("call_args_collected_candidate")
        .map(|(node, args)| (*node, args.clone()))
        .collect();

    // Merge float args after integer args for each call node
    for &(call_node, ref float_args) in db.rel_iter::<(Node, Arc<Vec<RTLReg>>)>("call_float_args_collected") {
        if !float_args.is_empty() {
            let int_args = rebuilt_args.entry(call_node).or_insert_with(|| Arc::new(vec![]));
            let mut combined = (**int_args).clone();
            combined.extend_from_slice(float_args);
            *int_args = Arc::new(combined);
        }
    }

    let new_rtl_inst: ascent::boxcar::Vec<(Node, RTLInst)> = db
        .rel_iter::<(Node, RTLInst)>("rtl_inst_candidate")
        .map(|(node, inst)| {
            let replacement_args = rebuilt_args.get(node);
            let patched = match inst {
                RTLInst::Icall(sig, callee, args, dst, next) => {
                    RTLInst::Icall(
                        sig.clone(),
                        callee.clone(),
                        replacement_args.cloned().unwrap_or_else(|| args.clone()),
                        *dst,
                        *next,
                    )
                }
                RTLInst::Itailcall(sig, callee, args) => {
                    RTLInst::Itailcall(
                        sig.clone(),
                        callee.clone(),
                        replacement_args.cloned().unwrap_or_else(|| args.clone()),
                    )
                }
                _ => inst.clone(),
            };
            (*node, patched)
        })
        .collect();
    db.rel_set("rtl_inst_candidate", new_rtl_inst);
}

pub(crate) const FUNC_ARG_DIST: i64 = 256;

const ARG_REGS: [Mreg; 6] = [Mreg::DI, Mreg::SI, Mreg::DX, Mreg::CX, Mreg::R8, Mreg::R9];

#[inline]
pub(crate) fn arg_reg_position(reg: &Mreg) -> Option<usize> {
    ARG_REGS.iter().position(|r| r == reg)
}

const XMM_ARG_REGS: [Mreg; 8] = [
    Mreg::X0, Mreg::X1, Mreg::X2, Mreg::X3,
    Mreg::X4, Mreg::X5, Mreg::X6, Mreg::X7,
];

#[inline]
pub(crate) fn xmm_arg_reg_position(reg: &Mreg) -> Option<usize> {
    XMM_ARG_REGS.iter().position(|r| r == reg)
}

#[inline]
fn is_shift_or_rotate_op(op: &Operation) -> bool {
    matches!(op,
        Operation::Oshl | Operation::Oshr | Operation::Oshru |
        Operation::Oshll | Operation::Oshrl | Operation::Oshrlu
    )
}

#[inline]
pub fn infer_signature_from_args(args: &[RTLReg], has_return: bool) -> Signature {
    let sig_args: Vec<XType> = args.iter().map(|_| XType::Xlong).collect();
    let sig_res = if has_return { XType::Xint } else { XType::Xvoid };
    Signature {
        sig_args: Arc::new(sig_args),
        sig_res,
        sig_cc: CallConv::default(),
    }
}

fn mreg_discriminant(reg: Mreg) -> u64 {
    match reg {
        Mreg::AX => 0, Mreg::BX => 1, Mreg::CX => 2, Mreg::DX => 3,
        Mreg::SI => 4, Mreg::DI => 5, Mreg::BP => 6,
        Mreg::R8 => 7, Mreg::R9 => 8, Mreg::R10 => 9, Mreg::R11 => 10,
        Mreg::R12 => 11, Mreg::R13 => 12, Mreg::R14 => 13, Mreg::R15 => 14,
        Mreg::X0 => 15, Mreg::X1 => 16, Mreg::X2 => 17, Mreg::X3 => 18,
        Mreg::X4 => 19, Mreg::X5 => 20, Mreg::X6 => 21, Mreg::X7 => 22,
        Mreg::X8 => 23, Mreg::X9 => 24, Mreg::X10 => 25, Mreg::X11 => 26,
        Mreg::X12 => 27, Mreg::X13 => 28, Mreg::X14 => 29, Mreg::X15 => 30,
        Mreg::FP0 => 31, Mreg::SP => 32, Mreg::Unknown => 33,
    }
}

pub fn build_call_args<'a>(
    inp: impl Iterator<Item = (&'a usize, &'a RTLReg)>,
) -> impl Iterator<Item = Args> {
    let mut pairs: Vec<(usize, RTLReg)> = inp.map(|(pos, reg)| (*pos, *reg)).collect();
    pairs.sort_by_key(|(pos, _)| *pos);
    pairs.dedup_by_key(|(pos, _)| *pos);

    let args: Vec<RTLReg> = pairs.into_iter().map(|(_, reg)| reg).collect();
    std::iter::once(Arc::new(args))
}

pub(crate) fn fresh_xtl_reg(node: Node, reg: Mreg) -> RTLReg {
    let mreg_id = mreg_discriminant(reg);
    (1u64 << 63) | (node << 6) | (mreg_id & 0x3F)
}

pub(crate) const FRESH_NS_STACK_SRC: u64 = 1 << 54;
pub(crate) const FRESH_NS_REG_DST: u64   = 1 << 55;
pub(crate) const FRESH_NS_SP_BASE: u64   = 1 << 56;
pub(crate) const FRESH_NS_STACK_PARAM: u64 = 1 << 57;

pub(crate) fn fresh_stack_param_reg(func_addr: Node, stack_idx: usize) -> RTLReg {
    (1u64 << 63) | FRESH_NS_STACK_PARAM | (func_addr << 6) | ((stack_idx as u64) & 0x3F)
}

pub fn convert_builtin_arg(
    node: Node,
    arg: &BuiltinArg<Mreg>,
    reg_rtl_map: &HashMap<(Node, Mreg), RTLReg>,
) -> BuiltinArg<RTLReg> {
    match arg {
        BuiltinArg::BA(mreg) => {
            BuiltinArg::BA(reg_rtl_map.get(&(node, *mreg)).copied().unwrap_or(DEFAULT_VAR as u64))
        }
        BuiltinArg::BAInt(z) => BuiltinArg::BAInt(*z),
        BuiltinArg::BALong(z) => BuiltinArg::BALong(*z),
        BuiltinArg::BAFloat(f) => BuiltinArg::BAFloat(*f),
        BuiltinArg::BASingle(f) => BuiltinArg::BASingle(*f),
        BuiltinArg::BALoadStack(chunk, ptrofs) => BuiltinArg::BALoadStack(*chunk, *ptrofs),
        BuiltinArg::BAAddrStack(ptrofs) => BuiltinArg::BAAddrStack(*ptrofs),
        BuiltinArg::BALoadGlobal(chunk, ident, ptrofs) => {
            BuiltinArg::BALoadGlobal(*chunk, ident.clone(), *ptrofs)
        }
        BuiltinArg::BAAddrGlobal(ident, ptrofs) => BuiltinArg::BAAddrGlobal(ident.clone(), *ptrofs),
        BuiltinArg::BASplitLong(a, b) => BuiltinArg::BASplitLong(
            Box::new(convert_builtin_arg(node, a, reg_rtl_map)),
            Box::new(convert_builtin_arg(node, b, reg_rtl_map)),
        ),
        BuiltinArg::BAAddPtr(a, b) => BuiltinArg::BAAddPtr(
            Box::new(convert_builtin_arg(node, a, reg_rtl_map)),
            Box::new(convert_builtin_arg(node, b, reg_rtl_map)),
        ),
    }
}

pub fn convert_ltl_builtins_to_rtl(
    builtin_data: &Vec<(Node, Symbol, Arc<Vec<BuiltinArg<Mreg>>>, BuiltinArg<Mreg>)>,
    reg_rtl_map: &HashMap<(Node, Mreg), RTLReg>,
) -> Vec<(Node, RTLInst)> {
    builtin_data
        .iter()
        .map(|(addr, name, args, result)| {
            let args_rtl: Vec<BuiltinArg<RTLReg>> = args
                .iter()
                .map(|arg| convert_builtin_arg(*addr, arg, reg_rtl_map))
                .collect();
            let result_rtl = convert_builtin_arg(*addr, result, reg_rtl_map);
            let inst = RTLInst::Ibuiltin(name.to_string(), args_rtl, result_rtl);
            (*addr, inst)
        })
        .collect()
}

pub(crate) fn adjust_condition_size(cond: Condition, size: usize) -> Condition {
    match (cond, size) {
        (Condition::Ccompl(c), 4) => Condition::Ccomp(c),
        (Condition::Ccomplu(c), 4) => Condition::Ccompu(c),
        (Condition::Ccomp(c), 8) => Condition::Ccompl(c),
        (Condition::Ccompu(c), 8) => Condition::Ccomplu(c),
        (c, _) => c,
    }
}

pub(crate) fn extract_builtin_arg_regs(arg: &BuiltinArg<Mreg>) -> Vec<Mreg> {
    match arg {
        BuiltinArg::BA(reg) => vec![*reg],
        BuiltinArg::BASplitLong(a, b) => {
            let mut regs = extract_builtin_arg_regs(a.as_ref());
            regs.extend(extract_builtin_arg_regs(b.as_ref()));
            regs
        }
        BuiltinArg::BAAddPtr(a, b) => {
            let mut regs = extract_builtin_arg_regs(a.as_ref());
            regs.extend(extract_builtin_arg_regs(b.as_ref()));
            regs
        }
        _ => vec![],
    }
}


pub fn is_rip(reg: &str) -> bool {
    reg.to_uppercase().ends_with("IP")
}

pub fn typ_to_chunk(typ: Typ) -> MemoryChunk {
    match typ {
        Typ::Tint => MemoryChunk::MInt32,
        Typ::Tlong => MemoryChunk::MInt64,
        Typ::Tfloat => MemoryChunk::MFloat64,
        Typ::Tsingle => MemoryChunk::MFloat32,
        Typ::Tany32 => MemoryChunk::MAny32,
        Typ::Tany64 => MemoryChunk::MAny64,
        Typ::Unknown => MemoryChunk::Unknown,
    }
}


pub fn is_arithmetic_op(op: &Operation) -> bool {
    matches!(op,
        Operation::Oadd | Operation::Osub | Operation::Omul | Operation::Odiv |
        Operation::Odivu | Operation::Omod | Operation::Omodu |
        Operation::Oand | Operation::Oor | Operation::Oxor |
        Operation::Oshl | Operation::Oshr | Operation::Oshru |
        Operation::Oneg | Operation::Onot |
        Operation::Oaddl | Operation::Osubl | Operation::Omull | Operation::Odivl |
        Operation::Odivlu | Operation::Omodl | Operation::Omodlu |
        Operation::Oandl | Operation::Oorl | Operation::Oxorl |
        Operation::Oshll | Operation::Oshrl | Operation::Oshrlu |
        Operation::Onegl | Operation::Onotl |
        Operation::Oaddimm(_) | Operation::Omulimm(_) | Operation::Oandimm(_) | Operation::Oorimm(_) |
        Operation::Oxorimm(_) | Operation::Oshlimm(_) | Operation::Oshrimm(_) |
        Operation::Oshruimm(_) | Operation::Oaddlimm(_) | Operation::Omullimm(_) |
        Operation::Oandlimm(_) | Operation::Oorlimm(_) | Operation::Oxorlimm(_) |
        Operation::Oshllimm(_) | Operation::Oshrlimm(_) | Operation::Oshrluimm(_) |
        Operation::Omulhs | Operation::Omulhu | Operation::Omullhs | Operation::Omullhu |
        Operation::Oshrximm(_) | Operation::Oshrxlimm(_) |
        Operation::Ororimm(_) | Operation::Ororlimm(_) |
        Operation::Oshldimm(_) |
        Operation::Odivimm(_) | Operation::Odivuimm(_) |
        Operation::Omodimm(_) | Operation::Omoduimm(_) |
        Operation::Odivlimm(_) | Operation::Odivluimm(_) |
        Operation::Omodlimm(_) | Operation::Omodluimm(_)
    )
}

#[inline]
pub fn is_null_comparison_cond(cond: &Condition) -> bool {
    matches!(cond,
        Condition::Ccompimm(Comparison::Ceq, 0) | Condition::Ccompuimm(Comparison::Ceq, 0) |
        Condition::Ccompimm(Comparison::Cne, 0) | Condition::Ccompuimm(Comparison::Cne, 0) |
        Condition::Ccomplimm(Comparison::Ceq, 0) | Condition::Ccompluimm(Comparison::Ceq, 0) |
        Condition::Ccomplimm(Comparison::Cne, 0) | Condition::Ccompluimm(Comparison::Cne, 0)
    )
}

pub fn is_null_comparison_op(op: &Operation) -> bool {
    matches!(op,
        Operation::Ocmp(Condition::Ccompimm(Comparison::Ceq, 0)) |
        Operation::Ocmp(Condition::Ccompuimm(Comparison::Ceq, 0)) |
        Operation::Ocmp(Condition::Ccompimm(Comparison::Cne, 0)) |
        Operation::Ocmp(Condition::Ccompuimm(Comparison::Cne, 0)) |
        Operation::Ocmp(Condition::Ccomplimm(Comparison::Ceq, 0)) |
        Operation::Ocmp(Condition::Ccompluimm(Comparison::Ceq, 0)) |
        Operation::Ocmp(Condition::Ccomplimm(Comparison::Cne, 0)) |
        Operation::Ocmp(Condition::Ccompluimm(Comparison::Cne, 0))
    )
}

pub fn chunk_size_bits(chunk: &MemoryChunk) -> u8 {
    match chunk {
        MemoryChunk::MBool | MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned => 8,
        MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned => 16,
        MemoryChunk::MInt32 | MemoryChunk::MAny32 | MemoryChunk::MFloat32 => 32,
        MemoryChunk::MInt64 | MemoryChunk::MAny64 | MemoryChunk::MFloat64 => 64,
        MemoryChunk::Unknown => 64,  
    }
}

pub(crate) fn build_xtype_vec<'a>(
    inp: impl Iterator<Item = (&'a usize, &'a XType)>,
) -> impl Iterator<Item = Arc<Vec<XType>>> {
    let mut pairs: Vec<(usize, XType)> = inp.map(|(pos, reg)| (*pos, *reg)).collect();
    pairs.sort_by_key(|(pos, _)| *pos);

    let args: Vec<XType> = pairs.into_iter().map(|(_, reg)| reg).collect();
    std::iter::once(Arc::new(args))
}

fn seed_initial_rtl_next(db: &mut DecompileDB) {
    let seeded = ascent::boxcar::Vec::new();
    for &(src, dst) in db.rel_iter::<(Node, Node)>("ltl_succ") {
        seeded.push((src, dst));
    }
    db.rel_set("rtl_next", seeded);
}

fn collect_sorted_rtl_next(db: &DecompileDB) -> Vec<(Node, Node)> {
    let mut next: Vec<(Node, Node)> = db.rel_iter::<(Node, Node)>("rtl_next").cloned().collect();
    next.sort_unstable();
    next.dedup();
    next
}


pub struct RTLPass;

#[derive(Debug, Default, Clone, Copy)]
struct RtlOptStats {
    copies: usize,
    dead: usize,
    nops: usize,
    inline_temps: usize,
    zero_rewrites: usize,
}

impl RtlOptStats {
    fn accumulate(&mut self, other: Self) {
        self.copies += other.copies;
        self.dead += other.dead;
        self.nops += other.nops;
        self.inline_temps += other.inline_temps;
        self.zero_rewrites += other.zero_rewrites;
    }

    fn has_changes(self) -> bool {
        self.copies > 0
            || self.dead > 0
            || self.nops > 0
            || self.inline_temps > 0
            || self.zero_rewrites > 0
    }
}

fn optimize_rtl_candidates(db: &mut DecompileDB) -> Option<RtlOptStats> {
    let mut ctx = PassContext::load(db);
    if ctx.functions.is_empty() {
        return None;
    }

    let var_types = std::mem::take(&mut ctx.var_types);

    let func_regs: HashMap<Address, HashSet<RTLReg>> = ctx.functions.iter()
        .map(|(&addr, func)| {
            let mut regs = HashSet::new();
            for inst in func.inst.values() {
                collect_inst_regs(inst, &mut regs);
            }
            regs.extend(func.params.iter());
            (addr, regs)
        })
        .collect();

    let per_func_var_types: HashMap<Address, HashMap<RTLReg, XType>> = func_regs.iter()
        .map(|(&addr, regs)| {
            let ft: HashMap<RTLReg, XType> = regs.iter()
                .filter_map(|&reg| var_types.get(&reg).map(|&ty| (reg, ty)))
                .collect();
            (addr, ft)
        })
        .collect();
    let per_func_var_types = std::sync::Mutex::new(per_func_var_types);

    let results: Vec<_> = ctx.functions.par_iter_mut()
        .map(|(&func_addr, func)| {
            let mut func_var_types = per_func_var_types.lock().unwrap()
                .remove(&func_addr).unwrap_or_default();

            let zero_rewrites = self_zero_rewrite(func);

            let mut copies = 0usize;
            let mut dead = 0usize;
            loop {
                let du = DefUseInfo::build(func);
                let liveness = LivenessInfo::build(func, &du);

                let (c, copy_subst) = copy_propagation(func, &du, &liveness);
                for (&dst, &src) in &copy_subst {
                    if let Some(&ty) = func_var_types.get(&dst) {
                        func_var_types.entry(src).or_insert(ty);
                    }
                }
                let d = dead_store_elimination(func, &du, &liveness);

                if c == 0 && d == 0 {
                    break;
                }
                copies += c;
                dead += d;
            }

            let nops = nop_collapse(func);

            let du = DefUseInfo::build(func);
            let liveness = LivenessInfo::build(func, &du);
            let inlines = find_inline_temps(func, &du, &liveness);

            (
                RtlOptStats {
                    copies,
                    dead,
                    nops,
                    inline_temps: inlines.len(),
                    zero_rewrites,
                },
                inlines,
                func_var_types,
            )
        })
        .collect();

    let mut stats = RtlOptStats::default();
    let mut merged_var_types = var_types;

    for (func_stats, inlines, func_vt) in results {
        stats.accumulate(func_stats);
        ctx.inline_temps.extend(inlines);
        merged_var_types.extend(func_vt);
    }

    ctx.var_types = merged_var_types;
    ctx.write_back(db);
    Some(stats)
}

impl IRPass for RTLPass {
    fn name(&self) -> &'static str { "rtl" }

    fn run(&self, db: &mut DecompileDB) {
        seed_initial_rtl_next(db);
        run_pass!(db, RTLPassProgram);
        trim_direct_call_args_to_callee_arity(db);
        convert_and_push_builtins(db);

        if let Some(stats) = optimize_rtl_candidates(db) {
            if stats.has_changes() {
                info!(
                    "rtl: {} copies propagated, {} dead stores, {} nops collapsed, {} inline temps, {} zero rewrites",
                    stats.copies,
                    stats.dead,
                    stats.nops,
                    stats.inline_temps,
                    stats.zero_rewrites,
                );
            }
        }
    }

    fn inputs(&self) -> &'static [&'static str] {
        static INPUTS: std::sync::LazyLock<Vec<&'static str>> = std::sync::LazyLock::new(|| {
            let rtl_inputs = RTLPassProgram::inputs_only();
            let own = &[
                "rtl_inst_candidate",
                "rtl_succ_candidate",
                "rtl_next",
                "instr_in_function",
                "emit_function",
                "emit_function_param_candidate",
                "emit_var_type_candidate",
            ];
            let mut combined: Vec<&'static str> = rtl_inputs.iter().copied().collect();
            for &s in own {
                if !combined.contains(&s) {
                    combined.push(s);
                }
            }
            combined
        });
        &INPUTS
    }

    fn outputs(&self) -> &'static [&'static str] {
        static OUTPUTS: std::sync::LazyLock<Vec<&'static str>> = std::sync::LazyLock::new(|| {
            let rtl_outputs = RTLPassProgram::rule_outputs();
            let own = &[
                "rtl_inst",
                "rtl_next",
                "rtl_succ",
                "instr_in_function",
                "emit_inline_temp",
            ];
            let mut combined: Vec<&'static str> = rtl_outputs.iter().copied().collect();
            for &s in own {
                if !combined.contains(&s) {
                    combined.push(s);
                }
            }
            combined
        });
        &OUTPUTS
    }
}


pub(crate) struct FunctionCFG {
    #[allow(dead_code)]
    pub(crate) func_addr: Address,
    pub(crate) entry: Node,
    pub(crate) nodes: BTreeSet<Node>,
    pub(crate) inst: BTreeMap<Node, RTLInst>,
    pub(crate) succs: HashMap<Node, Vec<Node>>,
    pub(crate) preds: HashMap<Node, Vec<Node>>,
    pub(crate) params: HashSet<RTLReg>,
}


struct PassContext {
    functions: BTreeMap<Address, FunctionCFG>,
    var_types: HashMap<RTLReg, XType>,
    inline_temps: HashSet<RTLReg>,
}

impl PassContext {
    fn load(db: &DecompileDB) -> Self {
        let rtl_insts: Vec<(Node, RTLInst)> = db
            .rel_iter::<(Node, RTLInst)>("rtl_inst_candidate")
            .cloned()
            .collect();
        let rtl_succs: Vec<(Node, Node)> = db
            .rel_iter::<(Node, Node)>("rtl_succ_candidate")
            .cloned()
            .collect();
        let instr_in_func: Vec<(Node, Address)> = db
            .rel_iter::<(Node, Address)>("instr_in_function")
            .cloned()
            .collect();
        let emit_funcs: Vec<(Address, Symbol, Node)> = db
            .rel_iter::<(Address, Symbol, Node)>("emit_function")
            .cloned()
            .collect();
        let emit_params: Vec<(Address, RTLReg)> = db
            .rel_iter::<(Address, RTLReg)>("emit_function_param_candidate")
            .cloned()
            .collect();
        let var_types: HashMap<RTLReg, XType> = db
            .rel_iter::<(RTLReg, XType)>("emit_var_type_candidate")
            .cloned()
            .collect();

        let node_to_func: HashMap<Node, Address> = instr_in_func.iter()
            .map(|&(n, f)| (n, f))
            .collect();

        let func_entries: HashMap<Address, Node> = emit_funcs.iter()
            .map(|&(addr, _, entry)| (addr, entry))
            .collect();

        let mut func_params: HashMap<Address, HashSet<RTLReg>> = HashMap::new();
        for &(addr, reg) in &emit_params {
            func_params.entry(addr).or_default().insert(reg);
        }

        let mut func_node_candidates: HashMap<Address, HashMap<Node, Vec<RTLInst>>> = HashMap::new();
        for (node, inst) in &rtl_insts {
            if let Some(&func) = node_to_func.get(node) {
                func_node_candidates.entry(func).or_default()
                    .entry(*node).or_default().push(inst.clone());
            }
        }

        let mut reg_usage_count: HashMap<RTLReg, usize> = HashMap::new();
        for (_, inst) in &rtl_insts {
            let mut regs = HashSet::new();
            collect_inst_regs(inst, &mut regs);
            for reg in regs {
                *reg_usage_count.entry(reg).or_insert(0) += 1;
            }
        }

        let mut func_insts: HashMap<Address, BTreeMap<Node, RTLInst>> = HashMap::new();
        for (func, node_candidates) in func_node_candidates {
            let insts = func_insts.entry(func).or_default();
            for (node, candidates) in node_candidates {
                if candidates.len() == 1 {
                    insts.insert(node, candidates.into_iter().next().unwrap());
                } else {
                    let best = candidates.into_iter().max_by_key(|inst| {
                        let mut regs = HashSet::new();
                        collect_inst_regs(inst, &mut regs);
                        let score: usize = regs.iter()
                            .map(|r| reg_usage_count.get(r).copied().unwrap_or(0))
                            .sum();
                        let arg_bonus = match inst {
                            RTLInst::Iop(_, args, _) if !args.is_empty() => 1,
                            RTLInst::Iload(_, _, args, _) if !args.is_empty() => 1,
                            RTLInst::Icond(_, args, _, _) if !args.is_empty() => 1,
                            _ => 0,
                        };
                        score + arg_bonus
                    }).unwrap();
                    insts.insert(node, best);
                }
            }
        }

        let mut func_succs: HashMap<Address, HashMap<Node, Vec<Node>>> = HashMap::new();
        for &(src, dst) in &rtl_succs {
            if let Some(&func) = node_to_func.get(&src) {
                func_succs.entry(func).or_default()
                    .entry(src).or_default().push(dst);
            }
        }

        let mut functions = BTreeMap::new();
        for (&func_addr, insts) in &func_insts {
            let entry = match func_entries.get(&func_addr) {
                Some(&e) => e,
                None => continue,
            };
            let nodes: BTreeSet<Node> = insts.keys().copied().collect();

            let raw_succs = func_succs.remove(&func_addr).unwrap_or_default();
            let mut succs: HashMap<Node, Vec<Node>> = HashMap::new();
            for (src, dsts) in raw_succs {
                if nodes.contains(&src) {
                    succs.insert(src, dsts);
                }
            }

            let nodes_vec: Vec<Node> = nodes.iter().copied().collect();
            for (i, &node) in nodes_vec.iter().enumerate() {
                if succs.contains_key(&node) {
                    continue;
                }
                let inst = match insts.get(&node) {
                    Some(inst) => inst,
                    None => continue,
                };
                let needs_fallthrough = matches!(inst,
                    RTLInst::Inop | RTLInst::Iop(..) | RTLInst::Iload(..)
                    | RTLInst::Istore(..) | RTLInst::Icall(..) | RTLInst::Ibuiltin(..)
                );
                if needs_fallthrough {
                    if let Some(&next_node) = nodes_vec.get(i + 1) {
                        succs.entry(node).or_default().push(next_node);
                    }
                }
                match inst {
                    RTLInst::Ibranch(Either::Right(target)) => {
                        if !succs.contains_key(&node) {
                            if let Some(&dst) = nodes.range(*target..).next() {
                                succs.entry(node).or_default().push(dst);
                            }
                        }
                    }
                    _ => {}
                }
            }

            let mut preds: HashMap<Node, Vec<Node>> = HashMap::new();
            for (&src, dsts) in &succs {
                for &dst in dsts {
                    if nodes.contains(&dst) {
                        preds.entry(dst).or_default().push(src);
                    }
                }
            }

            functions.insert(func_addr, FunctionCFG {
                func_addr,
                entry,
                nodes,
                inst: insts.clone(),
                succs,
                preds,
                params: func_params.remove(&func_addr).unwrap_or_default(),
            });
        }

        PassContext { functions, var_types, inline_temps: HashSet::new() }
    }

    fn write_back(self, db: &mut DecompileDB) {
        let new_insts = ascent::boxcar::Vec::<(Node, RTLInst)>::new();
        let new_succs = ascent::boxcar::Vec::<(Node, Node)>::new();
        let mut live_regs: HashSet<RTLReg> = HashSet::new();

        for (_func_addr, func) in &self.functions {
            for (&node, inst) in &func.inst {
                new_insts.push((node, inst.clone()));
                collect_inst_regs(inst, &mut live_regs);
            }
            for (&src, dsts) in &func.succs {
                if func.inst.contains_key(&src) {
                    for &dst in dsts {
                        new_succs.push((src, dst));
                    }
                }
            }
        }

        let new_sdc = ascent::boxcar::Vec::<(RTLReg, Constant)>::new();
        for (_func_addr, func) in &self.functions {
            for (_, inst) in &func.inst {
                if let RTLInst::Iop(op, args, dst) = inst {
                    if args.is_empty() {
                        if let Some(cst) = crate::decompile::passes::cminor_pass::constant_from_operation(op) {
                            new_sdc.push((*dst, cst));
                        }
                    }
                }
            }
        }
        db.rel_set("single_def_const", new_sdc);

        db.rel_set("rtl_next", new_succs.clone());
        db.rel_set("rtl_inst", new_insts);
        db.rel_set("rtl_succ", new_succs);

        let inline_vec = ascent::boxcar::Vec::<RTLReg>::new();
        for &reg in &self.inline_temps {
            if live_regs.contains(&reg) {
                inline_vec.push(reg);
            }
        }
        db.rel_set("emit_inline_temp", inline_vec);
    }
}

pub(crate) fn collect_inst_regs(inst: &RTLInst, regs: &mut HashSet<RTLReg>) {
    match inst {
        RTLInst::Inop => {}
        RTLInst::Iop(_, args, dst) => {
            for &a in args.iter() { regs.insert(a); }
            regs.insert(*dst);
        }
        RTLInst::Iload(_, _, args, dst) => {
            for &a in args.iter() { regs.insert(a); }
            regs.insert(*dst);
        }
        RTLInst::Istore(_, _, args, src) => {
            for &a in args.iter() { regs.insert(a); }
            regs.insert(*src);
        }
        RTLInst::Icall(_, callee, args, dst, _) => {
            if let Either::Left(r) = callee { regs.insert(*r); }
            for &a in args.iter() { regs.insert(a); }
            if let Some(d) = dst { regs.insert(*d); }
        }
        RTLInst::Itailcall(_, callee, args) => {
            if let Either::Left(r) = callee { regs.insert(*r); }
            for &a in args.iter() { regs.insert(a); }
        }
        RTLInst::Ibuiltin(_, args, res) => {
            collect_builtin_arg_regs(args, regs);
            collect_single_builtin_arg_regs(res, regs);
        }
        RTLInst::Icond(_, args, _, _) => {
            for &a in args.iter() { regs.insert(a); }
        }
        RTLInst::Ijumptable(reg, _) => { regs.insert(*reg); }
        RTLInst::Ibranch(_) => {}
        RTLInst::Ireturn(reg) => { regs.insert(*reg); }
    }
}

fn collect_builtin_arg_regs(args: &[BuiltinArg<RTLReg>], regs: &mut HashSet<RTLReg>) {
    for arg in args {
        collect_single_builtin_arg_regs(arg, regs);
    }
}

fn collect_single_builtin_arg_regs(arg: &BuiltinArg<RTLReg>, regs: &mut HashSet<RTLReg>) {
    match arg {
        BuiltinArg::BA(r) => { regs.insert(*r); }
        BuiltinArg::BASplitLong(a, b) | BuiltinArg::BAAddPtr(a, b) => {
            collect_single_builtin_arg_regs(a, regs);
            collect_single_builtin_arg_regs(b, regs);
        }
        _ => {}
    }
}


pub(crate) struct DefUseInfo {
    node_def: HashMap<Node, RTLReg>,
    node_uses: HashMap<Node, Vec<RTLReg>>,
    defs: HashMap<RTLReg, Vec<Node>>,
    uses: HashMap<RTLReg, Vec<Node>>,
}

impl DefUseInfo {
    pub(crate) fn build(func: &FunctionCFG) -> Self {
        let mut node_def: HashMap<Node, RTLReg> = HashMap::new();
        let mut node_uses: HashMap<Node, Vec<RTLReg>> = HashMap::new();
        let mut defs: HashMap<RTLReg, Vec<Node>> = HashMap::new();
        let mut uses: HashMap<RTLReg, Vec<Node>> = HashMap::new();

        for (&node, inst) in &func.inst {
            let (def, used) = inst_def_use(inst);
            if let Some(d) = def {
                node_def.insert(node, d);
                defs.entry(d).or_default().push(node);
            }
            node_uses.insert(node, used.clone());
            for u in used {
                uses.entry(u).or_default().push(node);
            }
        }

        DefUseInfo { node_def, node_uses, defs, uses }
    }
}

pub(crate) fn inst_def_use(inst: &RTLInst) -> (Option<RTLReg>, Vec<RTLReg>) {
    match inst {
        RTLInst::Inop => (None, vec![]),
        RTLInst::Iop(_, args, dst) => (Some(*dst), args.iter().copied().collect()),
        RTLInst::Iload(_, _, args, dst) => (Some(*dst), args.iter().copied().collect()),
        RTLInst::Istore(_, _, args, src) => {
            let mut used: Vec<RTLReg> = args.iter().copied().collect();
            used.push(*src);
            (None, used)
        }
        RTLInst::Icall(_, callee, args, dst, _) => {
            let mut used: Vec<RTLReg> = args.iter().copied().collect();
            if let Either::Left(r) = callee { used.push(*r); }
            (dst.as_ref().copied(), used)
        }
        RTLInst::Itailcall(_, callee, args) => {
            let mut used: Vec<RTLReg> = args.iter().copied().collect();
            if let Either::Left(r) = callee { used.push(*r); }
            (None, used)
        }
        RTLInst::Ibuiltin(_, args, res) => {
            let mut used = Vec::new();
            for a in args { collect_ba_uses(a, &mut used); }
            let def = match res {
                BuiltinArg::BA(r) => Some(*r),
                _ => None,
            };
            (def, used)
        }
        RTLInst::Icond(_, args, _, _) => (None, args.iter().copied().collect()),
        RTLInst::Ijumptable(reg, _) => (None, vec![*reg]),
        RTLInst::Ibranch(_) => (None, vec![]),
        RTLInst::Ireturn(reg) => (None, vec![*reg]),
    }
}

fn collect_ba_uses(arg: &BuiltinArg<RTLReg>, out: &mut Vec<RTLReg>) {
    match arg {
        BuiltinArg::BA(r) => out.push(*r),
        BuiltinArg::BASplitLong(a, b) | BuiltinArg::BAAddPtr(a, b) => {
            collect_ba_uses(a, out);
            collect_ba_uses(b, out);
        }
        _ => {}
    }
}


pub(crate) struct LivenessInfo {
    pub(crate) live_in: HashMap<Node, HashSet<RTLReg>>,
    pub(crate) live_out: HashMap<Node, HashSet<RTLReg>>,
}

impl LivenessInfo {
    pub(crate) fn build(func: &FunctionCFG, du: &DefUseInfo) -> Self {
        let mut live_in: HashMap<Node, HashSet<RTLReg>> = HashMap::new();
        let mut live_out: HashMap<Node, HashSet<RTLReg>> = HashMap::new();

        for &node in &func.nodes {
            live_in.insert(node, HashSet::new());
            live_out.insert(node, HashSet::new());
        }

        let mut worklist: VecDeque<Node> = func.nodes.iter().copied().collect();
        let mut in_worklist: HashSet<Node> = func.nodes.iter().copied().collect();

        while let Some(node) = worklist.pop_front() {
            in_worklist.remove(&node);

            let mut new_out = HashSet::new();
            if let Some(succs) = func.succs.get(&node) {
                for &s in succs {
                    if let Some(s_in) = live_in.get(&s) {
                        new_out.extend(s_in);
                    }
                }
            }

            let mut new_in = new_out.clone();
            if let Some(&def) = du.node_def.get(&node) {
                new_in.remove(&def);
            }
            if let Some(used) = du.node_uses.get(&node) {
                for &u in used {
                    new_in.insert(u);
                }
            }

            let old_in = match live_in.get(&node) {
                Some(li) => li,
                None => continue,
            };
            if &new_in != old_in {
                live_in.insert(node, new_in);
                live_out.insert(node, new_out);
                if let Some(preds) = func.preds.get(&node) {
                    for &p in preds {
                        if func.nodes.contains(&p) && in_worklist.insert(p) {
                            worklist.push_back(p);
                        }
                    }
                }
            } else if live_out.get(&node).map_or(true, |o| o != &new_out) {
                live_out.insert(node, new_out);
            }
        }

        LivenessInfo { live_in, live_out }
    }
}


fn reachable_from(func: &FunctionCFG, node: Node) -> HashSet<Node> {
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    if let Some(succs) = func.succs.get(&node) {
        for &s in succs {
            if visited.insert(s) {
                queue.push_back(s);
            }
        }
    }
    while let Some(n) = queue.pop_front() {
        if let Some(succs) = func.succs.get(&n) {
            for &s in succs {
                if visited.insert(s) {
                    queue.push_back(s);
                }
            }
        }
    }
    visited
}

fn src_not_redefined_on_paths_to_uses(
    func: &FunctionCFG,
    du: &DefUseInfo,
    copy_node: Node,
    src: RTLReg,
    dst_uses: &[Node],
) -> bool {
    let src_def_nodes = match du.defs.get(&src) {
        Some(defs) => defs,
        None => return true,
    };

    let redefs: Vec<Node> = src_def_nodes.iter()
        .filter(|&&n| n != copy_node)
        .copied()
        .collect();
    if redefs.is_empty() {
        return true;
    }

    let forward = reachable_from(func, copy_node);

    let reachable_redefs: Vec<Node> = redefs.iter()
        .filter(|n| forward.contains(n))
        .copied()
        .collect();
    if reachable_redefs.is_empty() {
        return true;
    }

    let mut backward = HashSet::new();
    let mut queue = VecDeque::new();
    for &u in dst_uses {
        if backward.insert(u) {
            queue.push_back(u);
        }
    }
    while let Some(node) = queue.pop_front() {
        if let Some(preds) = func.preds.get(&node) {
            for &p in preds {
                if backward.insert(p) {
                    queue.push_back(p);
                }
            }
        }
    }

    !reachable_redefs.iter().any(|n| backward.contains(n))
}

pub(crate) fn self_zero_rewrite(func: &mut FunctionCFG) -> usize {
    let mut count = 0;
    for (_node, inst) in func.inst.iter_mut() {
        let rewrite = match inst {
            RTLInst::Iop(op, args, dst) if args.len() == 2 && args[0] == args[1] => {
                match op {
                    Operation::Oxor | Operation::Osub => {
                        Some(RTLInst::Iop(Operation::Ointconst(0), Arc::new(vec![]), *dst))
                    }
                    Operation::Oxorl | Operation::Osubl => {
                        Some(RTLInst::Iop(Operation::Olongconst(0), Arc::new(vec![]), *dst))
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        if let Some(new_inst) = rewrite {
            *inst = new_inst;
            count += 1;
        }
    }
    count
}

pub(crate) fn copy_propagation(
    func: &mut FunctionCFG,
    du: &DefUseInfo,
    _liveness: &LivenessInfo,
) -> (usize, HashMap<RTLReg, RTLReg>) {
    let mut candidates: Vec<(Node, RTLReg, RTLReg)> = Vec::new();

    for (&node, inst) in &func.inst {
        if let RTLInst::Iop(Operation::Omove, args, dst) = inst {
            if args.len() == 1 && args[0] != *dst {
                let src = args[0];
                candidates.push((node, src, *dst));
            }
        }
    }

    let mut subst: HashMap<RTLReg, RTLReg> = HashMap::new();
    let mut dead_nodes: HashSet<Node> = HashSet::new();

    for (copy_node, src, dst) in &candidates {
        let src = *src;
        let dst = *dst;

        if func.params.contains(&dst) {
            continue;
        }

        let dst_defs = du.defs.get(&dst).map_or(0, |d| d.len());
        if dst_defs != 1 {
            continue;
        }

        let dst_uses = match du.uses.get(&dst) {
            Some(u) => u,
            None => {
                continue;
            }
        };

        let mut safe = true;
        for &use_node in dst_uses {
            if use_node == *copy_node {
                safe = false;
                break;
            }
        }
        if !safe { continue; }

        let reachable = reachable_from(func, *copy_node);
        for &use_node in dst_uses {
            if !reachable.contains(&use_node) {
                safe = false;
                break;
            }
        }
        if !safe { continue; }

        safe = src_not_redefined_on_paths_to_uses(func, du, *copy_node, src, dst_uses);

        if safe {
            subst.insert(dst, src);
            dead_nodes.insert(*copy_node);
        }
    }

    if subst.is_empty() {
        return (0, HashMap::new());
    }

    let mut resolved: HashMap<RTLReg, RTLReg> = HashMap::new();
    for (&dst, &src) in &subst {
        let mut target = src;
        let mut visited = HashSet::new();
        visited.insert(dst);
        while let Some(&next) = subst.get(&target) {
            if !visited.insert(next) {
                break;
            }
            target = next;
        }
        resolved.insert(dst, target);
    }

    let count = resolved.len();

    for (&node, inst) in func.inst.iter_mut() {
        if dead_nodes.contains(&node) {
            continue;
        }
        *inst = subst_in_inst(inst, &resolved);
    }

    for &node in &dead_nodes {
        if let Some(inst) = func.inst.get_mut(&node) {
            *inst = RTLInst::Inop;
        }
    }

    (count, resolved)
}

pub(crate) fn subst_in_inst(inst: &RTLInst, map: &HashMap<RTLReg, RTLReg>) -> RTLInst {
    match inst {
        RTLInst::Inop => RTLInst::Inop,
        RTLInst::Iop(op, args, dst) => {
            let new_args = subst_args(args, map);
            RTLInst::Iop(op.clone(), new_args, *dst)
        }
        RTLInst::Iload(chunk, addr, args, dst) => {
            let new_args = subst_args(args, map);
            RTLInst::Iload(*chunk, addr.clone(), new_args, *dst)
        }
        RTLInst::Istore(chunk, addr, args, src) => {
            let new_args = subst_args(args, map);
            let new_src = map.get(src).copied().unwrap_or(*src);
            RTLInst::Istore(*chunk, addr.clone(), new_args, new_src)
        }
        RTLInst::Icall(sig, callee, args, dst, next) => {
            let new_callee = match callee {
                Either::Left(r) => Either::Left(map.get(r).copied().unwrap_or(*r)),
                other => other.clone(),
            };
            let new_args = subst_args(args, map);
            RTLInst::Icall(sig.clone(), new_callee, new_args, *dst, *next)
        }
        RTLInst::Itailcall(sig, callee, args) => {
            let new_callee = match callee {
                Either::Left(r) => Either::Left(map.get(r).copied().unwrap_or(*r)),
                other => other.clone(),
            };
            let new_args = subst_args(args, map);
            RTLInst::Itailcall(sig.clone(), new_callee, new_args)
        }
        RTLInst::Ibuiltin(name, args, res) => {
            let new_args: Vec<_> = args.iter().map(|a| subst_ba(a, map)).collect();
            RTLInst::Ibuiltin(name.clone(), new_args, res.clone())
        }
        RTLInst::Icond(cond, args, ifso, ifnot) => {
            let new_args = subst_args(args, map);
            RTLInst::Icond(cond.clone(), new_args, ifso.clone(), ifnot.clone())
        }
        RTLInst::Ijumptable(reg, targets) => {
            let new_reg = map.get(reg).copied().unwrap_or(*reg);
            RTLInst::Ijumptable(new_reg, targets.clone())
        }
        RTLInst::Ibranch(target) => RTLInst::Ibranch(target.clone()),
        RTLInst::Ireturn(reg) => {
            let new_reg = map.get(reg).copied().unwrap_or(*reg);
            RTLInst::Ireturn(new_reg)
        }
    }
}

pub(crate) fn subst_args(args: &Args, map: &HashMap<RTLReg, RTLReg>) -> Args {
    Arc::new(args.iter().map(|r| map.get(r).copied().unwrap_or(*r)).collect())
}

pub(crate) fn subst_ba(ba: &BuiltinArg<RTLReg>, map: &HashMap<RTLReg, RTLReg>) -> BuiltinArg<RTLReg> {
    match ba {
        BuiltinArg::BA(r) => BuiltinArg::BA(map.get(r).copied().unwrap_or(*r)),
        BuiltinArg::BASplitLong(a, b) => BuiltinArg::BASplitLong(
            Box::new(subst_ba(a, map)),
            Box::new(subst_ba(b, map)),
        ),
        BuiltinArg::BAAddPtr(a, b) => BuiltinArg::BAAddPtr(
            Box::new(subst_ba(a, map)),
            Box::new(subst_ba(b, map)),
        ),
        other => other.clone(),
    }
}


pub(crate) fn dead_store_elimination(
    func: &mut FunctionCFG,
    du: &DefUseInfo,
    liveness: &LivenessInfo,
) -> usize {
    let mut count = 0;

    let dead_nodes: Vec<Node> = func.inst.iter()
        .filter_map(|(&node, inst)| {
            let def_reg = du.node_def.get(&node)?;

            if func.params.contains(def_reg) {
                return None;
            }

            let live_out = liveness.live_out.get(&node)?;
            if live_out.contains(def_reg) {
                return None;
            }

            match inst {
                RTLInst::Iop(_, _, _) => Some(node),
                RTLInst::Iload(_, _, _, _) => Some(node),
                _ => None,
            }
        })
        .collect();

    for node in &dead_nodes {
        if let Some(inst) = func.inst.get_mut(node) {
            *inst = RTLInst::Inop;
            count += 1;
        }
    }

    let dead_call_nodes: Vec<Node> = func.inst.iter()
        .filter_map(|(&node, inst)| {
            if let RTLInst::Icall(_, _, _, Some(dst), _) = inst {
                if func.params.contains(dst) {
                    return None;
                }
                let live_out = liveness.live_out.get(&node)?;
                if !live_out.contains(dst) {
                    return Some(node);
                }
            }
            None
        })
        .collect();

    for node in dead_call_nodes {
        if let Some(RTLInst::Icall(sig, callee, args, _, next)) = func.inst.get(&node).cloned() {
            func.inst.insert(node, RTLInst::Icall(sig, callee, args, None, next));
            count += 1;
        }
    }

    count
}


pub(crate) fn nop_collapse(func: &mut FunctionCFG) -> usize {
    let nop_nodes: Vec<Node> = func.inst.iter()
        .filter(|(&node, inst)| {
            matches!(inst, RTLInst::Inop) && node != func.entry
        })
        .map(|(&node, _)| node)
        .collect();

    if nop_nodes.is_empty() {
        return 0;
    }

    let nop_set: HashSet<Node> = nop_nodes.iter().copied().collect();

    let mut nop_target: HashMap<Node, Node> = HashMap::new();
    for &nop in &nop_nodes {
        let mut target = nop;
        let mut visited = HashSet::new();
        visited.insert(nop);
        loop {
            let succs = func.succs.get(&target);
            match succs.and_then(|s| if s.len() == 1 { Some(s[0]) } else { None }) {
                Some(next) if nop_set.contains(&next) && visited.insert(next) => {
                    target = next;
                }
                Some(next) if nop_set.contains(&next) => {
                    break;
                }
                Some(next) => {
                    nop_target.insert(nop, next);
                    break;
                }
                None => {
                    break;
                }
            }
        }
    }

    if nop_target.is_empty() {
        return 0;
    }

    let mut count = 0;

    for (&_pred, succs) in func.succs.iter_mut() {
        for succ in succs.iter_mut() {
            if let Some(&target) = nop_target.get(succ) {
                *succ = target;
            }
        }
    }

    for inst in func.inst.values_mut() {
        retarget_inst(inst, &nop_target);
    }

    for (&nop, _) in &nop_target {
        func.inst.remove(&nop);
        func.succs.remove(&nop);
        func.nodes.remove(&nop);
        count += 1;
    }

    loop {
        if !matches!(func.inst.get(&func.entry), Some(RTLInst::Inop)) {
            break;
        }
        let succs = func.succs.get(&func.entry);
        match succs.and_then(|s| if s.len() == 1 { Some(s[0]) } else { None }) {
            Some(target) if target != func.entry => {
                let old_entry = func.entry;
                func.entry = target;
                func.inst.remove(&old_entry);
                func.succs.remove(&old_entry);
                func.nodes.remove(&old_entry);
                count += 1;
            }
            _ => break,
        }
    }

    let mut preds: HashMap<Node, Vec<Node>> = HashMap::new();
    for (&src, dsts) in &func.succs {
        if func.inst.contains_key(&src) {
            for &dst in dsts {
                preds.entry(dst).or_default().push(src);
            }
        }
    }
    func.preds = preds;

    count
}

fn retarget_inst(inst: &mut RTLInst, nop_target: &HashMap<Node, Node>) {
    match inst {
        RTLInst::Icond(_, _, ifso, ifnot) => {
            retarget_either(ifso, nop_target);
            retarget_either(ifnot, nop_target);
        }
        RTLInst::Ibranch(target) => {
            retarget_either(target, nop_target);
        }
        RTLInst::Icall(_, _, _, _, next) => {
            if let Some(&target) = nop_target.get(next) {
                *next = target;
            }
        }
        RTLInst::Ijumptable(_, targets) => {
            let new_targets: Vec<Node> = targets.iter()
                .map(|n| nop_target.get(n).copied().unwrap_or(*n))
                .collect();
            if new_targets != **targets {
                *targets = Arc::new(new_targets);
            }
        }
        _ => {}
    }
}

pub(crate) fn retarget_either(target: &mut Either<Symbol, Node>, nop_target: &HashMap<Node, Node>) {
    if let Either::Right(node) = target {
        if let Some(&new_node) = nop_target.get(node) {
            *node = new_node;
        }
    }
}


pub(crate) fn find_inline_temps(
    func: &FunctionCFG,
    du: &DefUseInfo,
    liveness: &LivenessInfo,
) -> HashSet<RTLReg> {
    let mut result = HashSet::new();

    for (&reg, def_nodes) in &du.defs {
        if def_nodes.len() != 1 { continue; }
        let def_node = def_nodes[0];

        let use_node = match du.uses.get(&reg) {
            Some(u) => {
                let mut distinct: Vec<Node> = u.clone();
                distinct.sort_unstable();
                distinct.dedup();
                if distinct.len() != 1 { continue; }
                distinct[0]
            }
            _ => continue,
        };

        if func.params.contains(&reg) { continue; }

        let inst = match func.inst.get(&def_node) {
            Some(i) => i,
            None => continue,
        };
        // Only inline Iop temps; Iload is unsafe without aliasing/intervening store checks.
        let def_args: Vec<RTLReg> = match inst {
            RTLInst::Iop(_, args, _) => args.iter().copied().collect(),
            _ => continue,
        };

        let use_live_in = match liveness.live_in.get(&use_node) {
            Some(li) => li,
            None => continue,
        };
        if !def_args.iter().all(|a| use_live_in.contains(a)) {
            continue;
        }

        let reachable = reachable_from(func, def_node);
        if !reachable.contains(&use_node) {
            continue;
        }

        result.insert(reg);
    }

    result
}
