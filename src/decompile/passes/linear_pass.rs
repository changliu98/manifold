// Linear to LTL: resolves symbols, builds control-flow graph, and classifies branch targets.

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::{declare_io_from, run_pass};

use std::sync::Arc;
use crate::x86::mach::Mreg;
use crate::x86::op::Condition;
use crate::x86::types::*;
use ascent::ascent_par;
use either::Either;
use std::collections::HashMap;
use std::collections::HashSet;
use log::info;
use std::sync::{Mutex, OnceLock};


ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct LinearPassProgram;

    relation arch_bit(i64);
    relation arg_constrained_as_ptr(Node, RTLReg);
    relation base_ident_to_symbol(Ident, Symbol);
    relation block_in_function(Node, Address);
    relation call_arg_struct_ptr(Node, usize, usize);
    relation call_return_reg(Node, RTLReg);
    relation emit_clight_stmt(Address, Node, ClightStmt);
    relation emit_function_return_type_candidate(Address, ClightType);
    relation emit_goto_target(Address, Node);
    relation emit_ifthenelse_body(Address, Node, Node, bool);
    relation emit_loop_body(Address, Node, Node);
    relation emit_loop_exit(Address, Node, Node, Condition, Arc<Vec<CsharpminorExpr>>, Node, Node);
    relation emit_switch_chain(Address, Node, RTLReg);
    relation func_param_struct_type_candidate(Address, usize, usize);
    relation func_return_struct_type(Address, usize);
    relation func_span(Symbol, Address, Address);
    relation global_struct_catalog(u64, usize, usize, usize);
    relation ident_to_symbol(Ident, Symbol);
    relation ifthenelse_merge_point(Address, Node, Node);
    relation instr_in_function(Node, Address);
    relation is_external_function(Address);
    relation known_extern_signature(Symbol, usize, XType, Arc<Vec<XType>>);
    relation known_func_param_is_ptr(Symbol, usize);
    relation known_func_returns_float(Symbol);
    relation known_func_returns_int(Symbol);
    relation known_func_returns_long(Symbol);
    relation known_func_returns_ptr(Symbol);
    relation known_func_returns_single(Symbol);
    relation main_function(Address);
    relation reg_def_used(Address, Mreg, Address);
    relation reg_rtl(Node, Mreg, RTLReg);
    relation reg_xtl(Node, Mreg, RTLReg);
    relation stack_var(Address, Address, i64, RTLReg);
    relation string_data(String, String, usize);
    relation struct_field(u64, i64, String, MemoryChunk);
    relation struct_id_to_canonical(usize, usize);

    relation block_boundaries(Address, Address, Address);
    relation block_in_function(Node, Address);
    relation code_in_block(Address, Address);
    relation emit_function(Address, Symbol, Node);
    relation instr_in_function(Node, Address);
    relation instruction(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize);
    relation linear_inst(Address, LinearInst);
    relation next(Address, Address);
    relation plt_block(Address, Symbol);
    relation plt_entry(Address, Symbol);


    relation ddisasm_cfg_edge(Address, Address, Symbol);
    relation ddisasm_function_entry(Address);

    relation ltl_inst(Node, LTLInst);
    relation ltl_succ(Node, Node);
    #[local]
    #[ds(ascent_byods_rels::trrel)]
    relation ltl_reachable_tc(Node, Node);
    relation ltl_reachable(Node, Node);
    relation is_function_entry(Address);
    relation emit_sseq(Node, Node);
    relation emit_function_has_return_candidate(Address);

    relation is_local_block(Address);
    relation intra_function_edge(Address, Address);
    relation has_tailcall(Node);
    relation linear_has_executable_code(Node);
    relation ltl_branch_candidate(Node, Node);
    relation label_classified(Node);
    relation lcond_real_fallthrough(Node, Node);
    relation ltl_fallthrough(Node, Node);
    relation ltl_branch_target(Node, Node);
    relation ltl_jumptable_index(Node, usize);
    relation ltl_jumptable_target(Node, Node);
    relation ltl_non_trampoline(Node);
    relation ltl_branch_edge(Node, Node);
    #[local]
    #[ds(ascent_byods_rels::trrel)]
    relation ltl_branch_path(Node, Node);
    relation ltl_branch_cycle(Node);
    relation ltl_canonical_node(Node, Node);
    relation ltl_call_direct_target(Node, Node);
    relation ltl_tailcall_target(Node, Node);
    relation call_return_site(Node, Node);
    relation call_to_callee(Node, Address);
    relation call_to_external(Node, Symbol);
    relation call_targets_noreturn(Node);
    relation indirect_call_target(Node, Address);
    relation call_may_target(Node, Address);
    relation function_return_point(Address, Node);
    relation function_noreturn(Address);
    relation is_known_noreturn_function(Symbol);
    relation return_may_reach(Node, Node);
    relation ltl_intra_function_edge(Node, Node, Address);


    is_function_entry(addr) <--
        ddisasm_function_entry(addr);

    is_local_block(addr) <--
        block_in_function(addr, func),
        !ddisasm_function_entry(*addr),
        if *addr != *func;

    intra_function_edge(src, dst) <--
        ddisasm_cfg_edge(src, dst, edge_type),
        if *edge_type != "indirect" && *edge_type != "indirect_call",
        block_in_function(src, func),
        block_in_function(dst, func2),
        if func == func2;


    has_tailcall(n) <--
        linear_inst(n, inst),
        if match inst {
            LinearInst::Ltailcall(_) => true,
            _ => false,
        };

    linear_has_executable_code(n) <--
        linear_inst(n, inst),
        if match inst {
            LinearInst::Lop(_, _, _) => true,
            LinearInst::Lload(_, _, _, _) => true,
            LinearInst::Lstore(_, _, _, _) => true,
            LinearInst::Lcall(_) => true,
            LinearInst::Ltailcall(_) => true,
            LinearInst::Lbuiltin(_, _, _) => true,
            LinearInst::Lcond(_, _, _) => true,
            LinearInst::Ljumptable(_, _) => true,
            LinearInst::Lgetstack(_, _, _, _) => true,
            LinearInst::Lsetstack(_, _, _, _) => true,
            LinearInst::Lreturn => true,
            LinearInst::Lgoto(_) => true,
            LinearInst::Llabel(_) => false,
        };

    ltl_inst(addr, inst) <--
        ltl_branch_candidate(addr, target),
        let inst = LTLInst::Lbranch(Either::Right(*target));

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Lgetstack(slot, z, typ, mreg)),
        let inst = LTLInst::Lgetstack(*slot, *z, typ.clone(), *mreg);

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Lsetstack(mreg, slot, z, typ)),
        let inst = LTLInst::Lsetstack(*mreg, *slot, *z, typ.clone());

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Lop(op, srcs, dst)),
        let inst = LTLInst::Lop(op.clone(), srcs.clone(), *dst);

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Lload(chunk, addrmode, srcs, dst)),
        let inst = LTLInst::Lload(chunk.clone(), addrmode.clone(), srcs.clone(), *dst);

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Lstore(chunk, addrmode, srcs, dst)),
        let inst = LTLInst::Lstore(chunk.clone(), addrmode.clone(), srcs.clone(), *dst);

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Lcall(Either::Left(reg))),
        let inst = LTLInst::Lcall(Either::Left(*reg));

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Lcall(Either::Right(Either::Right(addr_val)))),
        let inst = LTLInst::Lcall(Either::Right(Either::Left(*addr_val)));

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Lcall(Either::Right(Either::Left(sym)))),
        let target_opt = crate::decompile::passes::linear_pass::resolve_symbol_addr_call(sym),
        if let Some(target_addr) = target_opt,
        let inst = LTLInst::Lcall(Either::Right(Either::Left(target_addr)));

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Lcall(Either::Right(Either::Left(sym)))),
        let target_opt = crate::decompile::passes::linear_pass::resolve_symbol_addr_call(sym),
        if target_opt.is_none(),
        let inst = LTLInst::Lcall(Either::Right(Either::Right(sym.clone())));

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Ltailcall(Either::Left(reg))),
        let inst = LTLInst::Ltailcall(Either::Left(*reg));

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Ltailcall(Either::Right(Either::Right(addr_val)))),
        let inst = LTLInst::Ltailcall(Either::Right(Either::Left(*addr_val)));

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Ltailcall(Either::Right(Either::Left(sym)))),
        let target_opt = crate::decompile::passes::linear_pass::resolve_symbol_addr_call(sym),
        if let Some(target_addr) = target_opt,
        let inst = LTLInst::Ltailcall(Either::Right(Either::Left(target_addr)));

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Ltailcall(Either::Right(Either::Left(sym)))),
        let target_opt = crate::decompile::passes::linear_pass::resolve_symbol_addr_call(sym),
        if target_opt.is_none(),
        let inst = LTLInst::Ltailcall(Either::Right(Either::Right(sym.clone())));

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Lbuiltin(name, args, res)),
        let inst = LTLInst::Lbuiltin(name.clone(), args.clone(), res.clone());

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Lreturn),
        let inst = LTLInst::Lreturn;

    ltl_inst(n, inst) <--
        block_in_function(n, _),
        next(n, next_node),
        !linear_inst(n, _),
        let inst = LTLInst::Lbranch(Either::Right(*next_node));


    label_classified(n) <--
        linear_inst(n, linearinst),
        if match linearinst {
            LinearInst::Llabel(_) => true,
            _ => false,
        },
        is_local_block(n);

    ltl_branch_candidate(n, *fallthrough) <--
        linear_inst(n, linearinst),
        if match linearinst {
            LinearInst::Llabel(_) => true,
            _ => false,
        },
        is_local_block(n),
        !linear_has_executable_code(n),
        next(n, fallthrough);

    ltl_branch_candidate(n, *fallthrough_blk) <--
        linear_inst(n, linearinst),
        if match linearinst {
            LinearInst::Llabel(_) => true,
            _ => false,
        },
        is_local_block(n),
        !linear_has_executable_code(n),
        !next(n, _),
        code_in_block(n, block),
        ddisasm_cfg_edge(block, fallthrough_blk, edge_type),
        if *edge_type == "fallthrough";

    label_classified(n) <--
        linear_inst(n, linearinst),
        if match linearinst {
            LinearInst::Llabel(_) => true,
            _ => false,
        },
        !is_local_block(n),
        is_function_entry(n);

    ltl_branch_candidate(n, *fallthrough) <--
        linear_inst(n, linearinst),
        if match linearinst {
            LinearInst::Llabel(_) => true,
            _ => false,
        },
        !is_local_block(n),
        is_function_entry(n),
        !linear_has_executable_code(n),
        next(n, fallthrough);

    ltl_branch_candidate(n, *fallthrough_blk) <--
        linear_inst(n, linearinst),
        if match linearinst {
            LinearInst::Llabel(_) => true,
            _ => false,
        },
        !is_local_block(n),
        is_function_entry(n),
        !linear_has_executable_code(n),
        !next(n, _),
        code_in_block(n, block),
        ddisasm_cfg_edge(block, fallthrough_blk, edge_type),
        if *edge_type == "fallthrough";


    ltl_branch_candidate(addr, target_addr) <--
        linear_inst(addr, ?LinearInst::Lgoto(target_sym)),
        let target_opt = crate::decompile::passes::linear_pass::resolve_symbol_addr_call(target_sym),
        if let Some(target_addr) = target_opt;

    ltl_inst(addr, ltlinst) <--
        linear_inst(addr, ?LinearInst::Lgoto(target_sym)),
        if crate::decompile::passes::linear_pass::resolve_symbol_addr_call(target_sym).is_none(),
        let ltlinst = LTLInst::Lbranch(Either::Left(target_sym.clone()));


    lcond_real_fallthrough(cmp_addr, real_ft) <--
        linear_inst(cmp_addr, ?LinearInst::Lcond(_, _, _)),
        next(cmp_addr, jcc_addr),
        next(jcc_addr, real_ft);
    
    lcond_real_fallthrough(cmp_addr, real_ft) <--
        linear_inst(cmp_addr, ?LinearInst::Lcond(_, _, _)),
        next(cmp_addr, jcc_addr),
        !next(jcc_addr, _),
        code_in_block(jcc_addr, block),
        ddisasm_cfg_edge(block, fallthrough_blk, edge_type),
        if *edge_type == "fallthrough",
        let real_ft = *fallthrough_blk;

    lcond_real_fallthrough(cmp_addr, real_ft) <--
        linear_inst(cmp_addr, ?LinearInst::Lcond(_, _, _)),
        next(cmp_addr, jcc_addr),
        instruction(jcc_addr, size, _, _, _, _, _, _, _, _),
        let real_ft = ((*jcc_addr as i64) + (*size as i64)) as Address;

    ltl_inst(addr, ltlinst) <--
        linear_inst(addr, ?LinearInst::Lcond(cond, args, target_sym)),
        lcond_real_fallthrough(addr, fallthrough),
        let target_opt = crate::decompile::passes::linear_pass::resolve_symbol_addr_call(target_sym),
        if let Some(target_addr) = target_opt,
        ltl_canonical_node(target_addr, canon_target),
        ltl_canonical_node(*fallthrough, canon_fallthrough),
        let ltlinst = LTLInst::Lcond(cond.clone(), args.clone(), Either::Right(*canon_target), Either::Right(*canon_fallthrough));

    ltl_inst(addr, ltlinst) <--
        linear_inst(addr, ?LinearInst::Lcond(cond, args, target_sym)),
        !next(addr, _),
        code_in_block(addr, block),
        ddisasm_cfg_edge(block, fallthrough_blk, edge_type),
        if *edge_type == "fallthrough",
        let target_opt = crate::decompile::passes::linear_pass::resolve_symbol_addr_call(target_sym),
        if let Some(target_addr) = target_opt,
        ltl_canonical_node(target_addr, canon_target),
        ltl_canonical_node(*fallthrough_blk, canon_fallthrough),
        let ltlinst = LTLInst::Lcond(cond.clone(), args.clone(), Either::Right(*canon_target), Either::Right(*canon_fallthrough));

    ltl_inst(addr, ltlinst) <--
        linear_inst(addr, ?LinearInst::Lcond(cond, args, target_sym)),
        lcond_real_fallthrough(addr, fallthrough),
        if crate::decompile::passes::linear_pass::resolve_symbol_addr_call(target_sym).is_none(),
        ltl_canonical_node(*fallthrough, canon_fallthrough),
        let ltlinst = LTLInst::Lcond(cond.clone(), args.clone(), Either::Left(target_sym.clone()), Either::Right(*canon_fallthrough));

    ltl_inst(addr, ltlinst) <--
        linear_inst(addr, ?LinearInst::Ljumptable(arg, targets)),
        let mut addrs = Vec::new(),
        if { for sym in targets.iter() { if let Some(a) = crate::decompile::passes::linear_pass::resolve_symbol_addr_call(sym) { addrs.push(a); } } !addrs.is_empty() },
        let ltlinst = LTLInst::Ljumptable(*arg, addrs);

    ltl_inst(addr, ltlinst) <--
        linear_inst(addr, ?LinearInst::Ljumptable(arg, targets)),
        if { let any_resolved = targets.iter().any(|sym| crate::decompile::passes::linear_pass::resolve_symbol_addr_call(sym).is_some()); !any_resolved },
        next(addr, fallthrough),
        let ltlinst = LTLInst::Lbranch(Either::Right(*fallthrough));

    ltl_fallthrough(src, dst) <--
        ltl_inst(src, ltlinst),
        if crate::decompile::passes::linear_pass::has_fallthrough(&ltlinst, *src),
        next(src, ft),
        ltl_canonical_node(ft, dst),
        ltl_inst(dst, _);

    ltl_branch_target(src, dst) <--
        ltl_inst(src, ltlinst),
        if let LTLInst::Lbranch(Either::Right(target)) = ltlinst,
        let src_addr = *src,
        if *target != src_addr,
        ltl_canonical_node(*target, dst),
        ltl_inst(dst, _);

    ltl_jumptable_index(src, idx) <--
        ltl_inst(src, ltlinst),
        if let LTLInst::Ljumptable(_, targets) = ltlinst,
        if !targets.is_empty(),
        let idx = 0usize;

    ltl_jumptable_index(src, next_idx) <--
        ltl_jumptable_index(src, idx),
        ltl_inst(src, ltlinst),
        if let LTLInst::Ljumptable(_, targets) = ltlinst,
        let next_idx = idx + 1,
        if next_idx < targets.len();

    ltl_jumptable_target(src, dst) <--
        ltl_jumptable_index(src, idx),
        ltl_inst(src, ltlinst),
        if let LTLInst::Ljumptable(_, targets) = ltlinst,
        if let Some(target) = targets.get(*idx),
        ltl_canonical_node(*target, dst),
        ltl_inst(dst, _);

    ltl_non_trampoline(n) <--
        ltl_inst(n, inst),
        if match inst {
            LTLInst::Lbranch(Either::Right(t)) => *t == *n,
            LTLInst::Lbranch(Either::Left(_)) => true,
            _ => true,
        };

    ltl_branch_edge(src, dst) <--
        ltl_branch_candidate(src, dst),
        if *src != *dst;

    ltl_branch_path(src, dst) <-- ltl_branch_edge(src, dst);

    ltl_branch_cycle(n) <-- ltl_branch_path(n, m), ltl_branch_path(m, n);

    ltl_canonical_node(n, n) <--
        ltl_non_trampoline(n);

    ltl_canonical_node(n, n) <--
        ltl_branch_cycle(n);

    ltl_canonical_node(n, n) <--
        ltl_inst(n, inst),
        if let LTLInst::Lbranch(Either::Right(t)) = inst,
        if *t != *n,
        !ltl_branch_cycle(n),
        !block_in_function(*t, _);

    ltl_canonical_node(n, n) <--
        ltl_inst(n, inst),
        if let LTLInst::Lbranch(Either::Right(t)) = inst,
        if *t != *n,
        !ltl_branch_cycle(n),
        block_in_function(*t, _),
        !linear_inst(*t, _),
        !next(*t, _);

    ltl_canonical_node(n, canon) <--
        ltl_inst(n, inst),
        if let LTLInst::Lbranch(Either::Right(t)) = inst,
        if *t != *n,
        !ltl_branch_cycle(n),
        ltl_canonical_node(*t, canon);

    ltl_canonical_node(target_addr, target_addr) <--
        linear_inst(addr, ?LinearInst::Lcond(_, _, target_sym)),
        let target_opt = crate::decompile::passes::linear_pass::resolve_symbol_addr_call(target_sym),
        if let Some(target_addr) = target_opt;

    ltl_canonical_node(ft, ft) <--
        lcond_real_fallthrough(_, ft);

    ltl_call_direct_target(src, dst) <--
        ltl_inst(src, ltlinst),
        if let LTLInst::Lcall(Either::Right(target)) = ltlinst,
        if let Either::Left(dst_addr) = target,
        let dst = *dst_addr;

    ltl_tailcall_target(src, dst) <--
        ltl_inst(src, ltlinst),
        if let LTLInst::Ltailcall(Either::Right(target)) = ltlinst,
        if let Either::Left(dst_addr) = target,
        let dst = *dst_addr;


    ltl_succ(src, dst) <--
        ltl_fallthrough(src, dst),
        if *src != *dst;

    ltl_succ(src, dst) <--
        ltl_branch_target(src, dst);

    ltl_succ(src, dst) <--
        ltl_inst(src, ?LTLInst::Lcond(_, _, ifso, ifnot)),
        if let Either::Right(dst_addr) = ifso,
        let dst = *dst_addr;

    ltl_succ(src, dst) <--
        ltl_inst(src, ?LTLInst::Lcond(_, _, ifso, ifnot)),
        if let Either::Right(dst_addr) = ifnot,
        let dst = *dst_addr;

    ltl_succ(src, dst) <--
        ltl_jumptable_target(src, dst);

    ltl_succ(src, dst) <--
        ltl_call_direct_target(src, dst);

    ltl_succ(src, dst) <--
        ltl_tailcall_target(src, dst);

    ltl_reachable_tc(x, y) <-- ltl_succ(x, y);
    ltl_reachable(x, y) <-- ltl_reachable_tc(x, y);


    call_targets_noreturn(call_site) <--
        call_to_callee(call_site, callee),
        function_noreturn(callee);

    call_targets_noreturn(call_site) <--
        ltl_inst(call_site, ?LTLInst::Lcall(Either::Right(Either::Right(symbol)))),
        is_known_noreturn_function(symbol);

    call_targets_noreturn(call_site) <--
        call_to_external(call_site, symbol),
        is_known_noreturn_function(symbol);

    call_targets_noreturn(call_site) <--
        call_to_callee(call_site, callee_addr),
        plt_entry(callee_addr, name),
        is_known_noreturn_function(name);

    call_targets_noreturn(call_site) <--
        call_to_callee(call_site, callee_addr),
        plt_block(callee_addr, name),
        is_known_noreturn_function(name);

    call_return_site(call_site, ret_addr) <--
        ltl_inst(call_site, ?LTLInst::Lcall(Either::Right(_))),
        !call_targets_noreturn(call_site),
        next(call_site, next_inst),
        ltl_canonical_node(next_inst, ret_addr),
        ltl_inst(ret_addr, _);

    call_return_site(call_site, ret_addr) <--
        ltl_inst(call_site, ?LTLInst::Lcall(Either::Left(_))),
        next(call_site, next_inst),
        ltl_canonical_node(next_inst, ret_addr),
        ltl_inst(ret_addr, _);

    call_to_callee(call_site, callee) <--
        ltl_inst(call_site, ?LTLInst::Lcall(Either::Right(Either::Left(callee))));

    call_to_callee(call_site, addr) <--
        ltl_inst(call_site, ?LTLInst::Lcall(Either::Right(Either::Right(symbol)))),
        if let Some(addr) = crate::decompile::passes::linear_pass::resolve_symbol_addr_call(symbol);

    call_to_callee(call_site, callee_addr) <--
        ltl_inst(call_site, ?LTLInst::Lcall(Either::Right(Either::Right(symbol)))),
        plt_entry(callee_addr, sym_name),
        if sym_name == symbol || crate::decompile::passes::cminor_pass::strip_version_suffix(sym_name) == *symbol;

    call_to_callee(call_site, callee_addr) <--
        ltl_inst(call_site, ?LTLInst::Lcall(Either::Right(Either::Right(symbol)))),
        plt_block(callee_addr, sym_name),
        if sym_name == symbol || crate::decompile::passes::cminor_pass::strip_version_suffix(sym_name) == *symbol;

    call_to_external(call_site, *symbol) <--
        ltl_inst(call_site, ?LTLInst::Lcall(Either::Right(Either::Right(symbol)))),
        if crate::decompile::passes::linear_pass::resolve_symbol_addr_call(symbol).is_none();

    call_may_target(call_site, callee) <--
        call_to_callee(call_site, callee);

    call_may_target(call_site, target) <--
        indirect_call_target(call_site, target);

    function_return_point(func, ret_inst) <--
        instr_in_function(ret_inst, func),
        ltl_inst(ret_inst, ?LTLInst::Lreturn);

    emit_function_has_return_candidate(func) <--
        function_return_point(func, _);

    function_noreturn(func) <--
        emit_function(func, _, _),
        !emit_function_has_return_candidate(func);


    function_noreturn(func) <--
        emit_function(func, name, _),
        is_known_noreturn_function(name.clone());

    function_noreturn(func) <--
        emit_function(func, name, _),
        is_known_noreturn_function(name);


    return_may_reach(ret_inst, ret_addr) <--
        function_return_point(callee, ret_inst),
        call_may_target(call_site, callee),
        call_return_site(call_site, ret_addr);


    ltl_succ(call_site, callee_entry) <--
        call_may_target(call_site, callee_entry);

    ltl_succ(ret_inst, ret_addr) <--
        return_may_reach(ret_inst, ret_addr);


    ltl_intra_function_edge(src, dst, func) <--
        ltl_succ(src, dst),
        block_in_function(src, func),
        block_in_function(dst, func2),
        if func == func2;


    emit_sseq(start, start) <--
        block_boundaries(func, start, end);

    emit_sseq(head, next) <--
        emit_sseq(head, current),
        ltl_fallthrough(current, next),
        ltl_inst(current, inst),
        if let LTLInst::Lbranch(Either::Right(t)) = inst,
        if *t == *current;

    emit_sseq(head, next) <--
        emit_sseq(head, current),
        ltl_fallthrough(current, next),
        ltl_inst(current, inst),
        if let LTLInst::Lgetstack(..) = inst;

    emit_sseq(head, next) <--
        emit_sseq(head, current),
        ltl_fallthrough(current, next),
        ltl_inst(current, inst),
        if let LTLInst::Lsetstack(..) = inst;

    emit_sseq(head, next) <--
        emit_sseq(head, current),
        ltl_fallthrough(current, next),
        ltl_inst(current, inst),
        if let LTLInst::Lop(..) = inst;

    emit_sseq(head, next) <--
        emit_sseq(head, current),
        ltl_fallthrough(current, next),
        ltl_inst(current, inst),
        if let LTLInst::Lload(..) = inst;

    emit_sseq(head, next) <--
        emit_sseq(head, current),
        ltl_fallthrough(current, next),
        ltl_inst(current, inst),
        if let LTLInst::Lstore(..) = inst;

    emit_sseq(head, next) <--
        emit_sseq(head, current),
        ltl_fallthrough(current, next),
        ltl_inst(current, inst),
        if let LTLInst::Lbuiltin(..) = inst;

    emit_sseq(head, next) <--
        emit_sseq(head, current),
        ltl_fallthrough(current, next),
        ltl_inst(current, inst),
        if let LTLInst::Lcall(..) = inst;


}

pub struct LinearPass;

impl IRPass for LinearPass {
    fn name(&self) -> &'static str { "linear" }

    fn run(&self, db: &mut DecompileDB) {
        run_pass!(db, LinearPassProgram);

        let linear_lcond_count = db.rel_iter::<(Address, LinearInst)>("linear_inst")
            .filter(|(_, inst)| matches!(inst, LinearInst::Lcond(..)))
            .count();
        let ltl_lcond_count = db.rel_iter::<(Node, LTLInst)>("ltl_inst")
            .filter(|(_, inst)| matches!(inst, LTLInst::Lcond(..)))
            .count();
        if linear_lcond_count != ltl_lcond_count {
            info!("[LinearPass] Lcond conversion: {}/{} linear Lcond converted to LTL Lcond ({} diff)",
                ltl_lcond_count, linear_lcond_count, (linear_lcond_count as isize) - (ltl_lcond_count as isize));
        }
    }

    declare_io_from!(LinearPassProgram);
}


static UNRESOLVED_SYMBOLS_LOGGED: OnceLock<Mutex<HashSet<Symbol>>> = OnceLock::new();

// Deduplicated set of unresolved symbols to avoid repeated log spam.
fn unresolved_symbols_store() -> &'static Mutex<HashSet<Symbol>> {
    UNRESOLVED_SYMBOLS_LOGGED.get_or_init(|| Mutex::new(HashSet::new()))
}

// Global symbol-to-address mapping, populated from op_immediate data during pipeline setup.
static OP_IMMEDIATE_MAP: OnceLock<HashMap<&'static str, Address>> = OnceLock::new();

// Initialize the symbol-to-address mapping table (called once during pipeline setup).
pub fn init_op_immediate_map(entries: &[(&'static str, i64, usize)]) {
    OP_IMMEDIATE_MAP.get_or_init(|| {
        let mut map = HashMap::new();
        for (sym, addr, _) in entries.iter() {
            if *addr >= 0 {
                map.insert(*sym, *addr as Address);
            }
        }
        map
    });
}

// Look up a symbol's concrete address in the global mapping.
pub fn resolve_symbol_addr(sym: &Symbol) -> Option<Address> {
    OP_IMMEDIATE_MAP.get().and_then(|map| map.get(sym)).copied()
}

// Resolve symbol address, logging once per unresolved symbol.
pub fn resolve_symbol_addr_call(sym: &Symbol) -> Option<Address> {
    if let Some(addr) = resolve_symbol_addr(sym) {
        Some(addr)
    } else {
        let mut guard = unresolved_symbols_store().lock().unwrap();
        guard.insert(sym.clone());
        None
    }
}

// Returns true if the instruction can fall through to the next sequential address.
pub(crate) fn has_fallthrough(inst: &LTLInst, src: Node) -> bool {
    match inst {
        LTLInst::Lbranch(Either::Right(target)) => *target == src,
        LTLInst::Lbranch(Either::Left(_)) => false,
        LTLInst::Lcond(..) | LTLInst::Lcall(..) => true,
        LTLInst::Ljumptable(..) | LTLInst::Ltailcall(..) | LTLInst::Lreturn => false,
        _ => true,
    }
}
