// Linear to LTL: resolves symbols, builds control-flow graph, and classifies branch targets.

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::{declare_io_from, run_pass};

use crate::mreg::Mreg;
use crate::x86::op::Condition;
use crate::x86::types::*;
use ascent::ascent_par;
use ascent::lattice::set::Set;
use either::Either;
use log::info;
use std::sync::Arc;

ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct LinearPassProgram;

    relation arch_bit(i64);
    relation arg_constrained_as_ptr(Node, RTLReg);
    relation base_ident_to_symbol(Ident, Symbol);
    relation block_in_function(Node, Address);
    relation call_return_reg(Node, RTLReg);
    relation emit_clight_stmt(Address, Node, ClightStmt);
    relation emit_function_return_type_candidate(Address, ClightType);
    relation emit_goto_target(Address, Node);
    relation emit_loop_body(Address, Node, Node);
    relation emit_loop_exit(Address, Node, Node, Condition, Arc<Vec<CsharpminorExpr>>, Node, Node);
    relation emit_switch_chain(Address, Node, RTLReg);
    relation fde_function_start(Address);
    relation func_param_struct_type_candidate(Address, usize, usize);
    relation func_span(Symbol, Address, Address);
    relation global_struct_catalog(u64, usize, usize, usize);
    relation ident_to_symbol(Ident, Symbol);
    relation instr_in_function(Node, Address);
    relation is_external_function(Address);
    relation known_extern_signature(Symbol, usize, XType, Arc<Vec<XType>>);
    relation known_func_param_is_ptr(Symbol, usize);
    relation known_func_returns_long(Symbol);
    relation known_func_returns_ptr(Symbol);
    relation mach_imm_stack_init(Address, i64, i64, Typ);
    // The no-linear-op side-effect class (fused mem-arith RMW, immediate indirect/absolute stores, mem-source loads) surfaces as a bare label+Lbranch, so threading gotos past it would drop the update.
    relation node_unlowered_side_effect(Address);
    relation main_function(Address);
    relation reg_def_used(Address, Mreg, Address);
    relation reg_rtl(Node, Mreg, RTLReg);
    relation reg_xtl(Node, Mreg, RTLReg);
    relation stack_var(Address, Address, i64, RTLReg);
    relation string_data(String, String, usize);
    relation struct_id_to_canonical(usize, usize);
    relation symbol_resolved_addr(Symbol, Address);

    relation jumptable_target_sym(Address, usize, Symbol);
    relation jumptable_target_resolved(Address, usize, Address);
    relation jumptable_has_resolved(Address);

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
    relation is_function_entry(Address);
    relation emit_sseq(Node, Node);
    relation emit_function_has_return_candidate(Address);

    relation is_local_block(Address);
    relation linear_has_executable_code(Node);
    relation ltl_branch_candidate(Node, Node);
    relation lcond_real_fallthrough(Node, Node);
    // Produced by asm_pass: this Lcond sits at a secondary jcc's own address (not at its compare), so its fall-through is next(addr) rather than skip-one-paired-jcc.
    relation mcond_at_jcc(Address);
    relation cond_delegated_origin(Address);
    relation ltl_fallthrough(Node, Node);
    relation ltl_branch_target(Node, Node);
    relation ltl_jumptable_index(Node, usize);
    relation ltl_jumptable_target(Node, Node);
    relation ltl_non_trampoline(Node);
    relation ltl_branch_edge(Node, Node);
    #[local]
    lattice ltl_branch_targets_at(Node, Set<Node>);
    relation ltl_branch_cycle(Node);
    relation ltl_canonical_node(Node, Node);
    relation ltl_call_direct_target(Node, Node);
    relation ltl_tailcall_target(Node, Node);
    relation call_return_site(Node, Node);
    relation call_to_callee(Node, Address);
    relation call_to_external(Node, Symbol);
    relation known_noreturn_call_site(Node);
    relation trim_instruction(Address);
    relation intrinsic_noreturn_call_site(Node);
    relation call_targets_noreturn(Node);
    relation indirect_call_target(Node, Address);
    relation call_may_target(Node, Address);
    relation function_return_point(Address, Node);
    relation function_has_ltl_body(Address);
    relation function_block_has_ltl(Address, Node);
    relation function_has_uncovered_block(Address);
    relation function_ltl_internal_succ(Address, Node, Node);
    relation function_unknown_terminal(Address, Node);
    relation function_unresolved_control(Address, Node);
    relation function_has_intrinsic_noreturn(Address);
    relation function_has_tailcall(Address);
    relation function_noreturn(Address);
    relation is_known_noreturn_function(Symbol);
    relation return_may_reach(Node, Node);


    is_function_entry(addr) <--
        ddisasm_function_entry(addr);

    is_local_block(addr) <--
        block_in_function(addr, func),
        !ddisasm_function_entry(*addr),
        if *addr != *func;

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
        symbol_resolved_addr(*sym, target_addr),
        !plt_block(*target_addr, _),
        !plt_entry(*target_addr, _),
        let inst = LTLInst::Lcall(Either::Right(Either::Left(*target_addr)));

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Lcall(Either::Right(Either::Left(sym)))),
        !symbol_resolved_addr(*sym, _),
        let inst = LTLInst::Lcall(Either::Right(Either::Right(sym.clone())));

    // PLT/external symbol: keep the symbol form so RTL picks up the known extern signature.
    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Lcall(Either::Right(Either::Left(sym)))),
        symbol_resolved_addr(*sym, target_addr),
        plt_block(*target_addr, _),
        let inst = LTLInst::Lcall(Either::Right(Either::Right(sym.clone())));

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Lcall(Either::Right(Either::Left(sym)))),
        symbol_resolved_addr(*sym, target_addr),
        plt_entry(*target_addr, _),
        let inst = LTLInst::Lcall(Either::Right(Either::Right(sym.clone())));

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Ltailcall(Either::Left(reg))),
        let inst = LTLInst::Ltailcall(Either::Left(*reg));

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Ltailcall(Either::Right(Either::Right(addr_val)))),
        let inst = LTLInst::Ltailcall(Either::Right(Either::Left(*addr_val)));

    // Same PLT-aware split as Lcall above: internal symbols resolve to addresses; PLT/external symbols stay as symbols so the known extern signature applies.
    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Ltailcall(Either::Right(Either::Left(sym)))),
        symbol_resolved_addr(*sym, target_addr),
        !plt_block(*target_addr, _),
        !plt_entry(*target_addr, _),
        let inst = LTLInst::Ltailcall(Either::Right(Either::Left(*target_addr)));

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Ltailcall(Either::Right(Either::Left(sym)))),
        !symbol_resolved_addr(*sym, _),
        let inst = LTLInst::Ltailcall(Either::Right(Either::Right(sym.clone())));

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Ltailcall(Either::Right(Either::Left(sym)))),
        symbol_resolved_addr(*sym, target_addr),
        plt_block(*target_addr, _),
        let inst = LTLInst::Ltailcall(Either::Right(Either::Right(sym.clone())));

    ltl_inst(addr, inst) <--
        linear_inst(addr, ?LinearInst::Ltailcall(Either::Right(Either::Left(sym)))),
        symbol_resolved_addr(*sym, target_addr),
        plt_entry(*target_addr, _),
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
        !known_noreturn_call_site(n),
        let inst = LTLInst::Lbranch(Either::Right(*next_node));

    // Retained side effects are not necessarily block leaders.  Give every
    // interior member of this class its own LTL point as well: merely making
    // it self-canonical does not stop a predecessor from threading past a
    // node that has no ltl_inst at all.
    ltl_inst(n, inst) <--
        node_unlowered_side_effect(n),
        next(n, next_node),
        !linear_inst(n, _),
        !known_noreturn_call_site(n),
        let inst = LTLInst::Lbranch(Either::Right(*next_node));


    ltl_branch_candidate(n, *fallthrough) <--
        linear_inst(n, linearinst),
        if match linearinst {
            LinearInst::Llabel(_) => true,
            _ => false,
        },
        is_local_block(n),
        !linear_has_executable_code(n),
        !known_noreturn_call_site(n),
        next(n, fallthrough);

    ltl_branch_candidate(n, *fallthrough_blk) <--
        linear_inst(n, linearinst),
        if match linearinst {
            LinearInst::Llabel(_) => true,
            _ => false,
        },
        is_local_block(n),
        !linear_has_executable_code(n),
        !known_noreturn_call_site(n),
        !next(n, _),
        code_in_block(n, block),
        ddisasm_cfg_edge(block, fallthrough_blk, edge_type),
        if *edge_type == "fallthrough";

    ltl_branch_candidate(n, *fallthrough) <--
        linear_inst(n, linearinst),
        if match linearinst {
            LinearInst::Llabel(_) => true,
            _ => false,
        },
        !is_local_block(n),
        is_function_entry(n),
        !linear_has_executable_code(n),
        !known_noreturn_call_site(n),
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
        !known_noreturn_call_site(n),
        !next(n, _),
        code_in_block(n, block),
        ddisasm_cfg_edge(block, fallthrough_blk, edge_type),
        if *edge_type == "fallthrough";


    ltl_branch_candidate(addr, *target_addr) <--
        linear_inst(addr, ?LinearInst::Lgoto(target_sym)),
        symbol_resolved_addr(*target_sym, target_addr);

    ltl_inst(addr, ltlinst) <--
        linear_inst(addr, ?LinearInst::Lgoto(target_sym)),
        !symbol_resolved_addr(*target_sym, _),
        let ltlinst = LTLInst::Lbranch(Either::Left(target_sym.clone()));


    lcond_real_fallthrough(cmp_addr, real_ft) <--
        linear_inst(cmp_addr, ?LinearInst::Lcond(_, _, _)),
        !mcond_at_jcc(cmp_addr),
        next(cmp_addr, jcc_addr),
        next(jcc_addr, real_ft);

    lcond_real_fallthrough(cmp_addr, real_ft) <--
        linear_inst(cmp_addr, ?LinearInst::Lcond(_, _, _)),
        !mcond_at_jcc(cmp_addr),
        next(cmp_addr, jcc_addr),
        !next(jcc_addr, _),
        code_in_block(jcc_addr, block),
        ddisasm_cfg_edge(block, fallthrough_blk, edge_type),
        if *edge_type == "fallthrough",
        let real_ft = *fallthrough_blk;

    // LINEAR-1: dropped the address-arithmetic fall-through rule, which fabricated a phantom edge at a section/block tail; rule 1 already covers every real next instruction.

    // An Lcond placed AT a secondary jcc's own address (mcond_at_jcc, see asm_pass secondary_flags_consumer): its fall-through is simply its next instruction - there is no paired jcc to skip over.
    lcond_real_fallthrough(addr, real_ft) <--
        linear_inst(addr, ?LinearInst::Lcond(_, _, _)),
        mcond_at_jcc(addr),
        next(addr, real_ft);

    // A compare that delegated its Mcond to its shadowed jcc (asm_pass
    // shadowed_safe) carries no instruction of its own; give it an explicit
    // fallthrough so its physical predecessors thread through it into the
    // shadow instead of losing their successor.
    ltl_inst(addr, ltlinst) <--
        cond_delegated_origin(addr),
        !linear_inst(addr, _),
        next(addr, ft),
        let ltlinst = LTLInst::Lbranch(Either::Right(*ft));

    ltl_inst(addr, ltlinst) <--
        linear_inst(addr, ?LinearInst::Lcond(cond, args, target_sym)),
        lcond_real_fallthrough(addr, fallthrough),
        symbol_resolved_addr(*target_sym, target_addr),
        ltl_canonical_node(*target_addr, canon_target),
        ltl_canonical_node(*fallthrough, canon_fallthrough),
        let ltlinst = LTLInst::Lcond(cond.clone(), args.clone(), Either::Right(*canon_target), Either::Right(*canon_fallthrough));

    ltl_inst(addr, ltlinst) <--
        linear_inst(addr, ?LinearInst::Lcond(cond, args, target_sym)),
        !next(addr, _),
        code_in_block(addr, block),
        ddisasm_cfg_edge(block, fallthrough_blk, edge_type),
        if *edge_type == "fallthrough",
        symbol_resolved_addr(*target_sym, target_addr),
        ltl_canonical_node(*target_addr, canon_target),
        ltl_canonical_node(*fallthrough_blk, canon_fallthrough),
        let ltlinst = LTLInst::Lcond(cond.clone(), args.clone(), Either::Right(*canon_target), Either::Right(*canon_fallthrough));

    ltl_inst(addr, ltlinst) <--
        linear_inst(addr, ?LinearInst::Lcond(cond, args, target_sym)),
        lcond_real_fallthrough(addr, fallthrough),
        !symbol_resolved_addr(*target_sym, _),
        ltl_canonical_node(*fallthrough, canon_fallthrough),
        let ltlinst = LTLInst::Lcond(cond.clone(), args.clone(), Either::Left(target_sym.clone()), Either::Right(*canon_fallthrough));

    jumptable_target_sym(*addr, i, *sym) <--
        linear_inst(addr, ?LinearInst::Ljumptable(_, targets)),
        for (i, sym) in targets.iter().enumerate();

    jumptable_target_resolved(*addr, *i, *target_addr) <--
        jumptable_target_sym(addr, i, sym),
        symbol_resolved_addr(sym, target_addr);

    jumptable_has_resolved(addr) <--
        jumptable_target_resolved(addr, _, _);

    ltl_inst(addr, ltlinst) <--
        linear_inst(addr, ?LinearInst::Ljumptable(arg, _)),
        jumptable_has_resolved(addr),
        agg addrs = crate::decompile::passes::linear_pass::build_jumptable_addrs(idx, target_addr) in jumptable_target_resolved(addr, idx, target_addr),
        let ltlinst = LTLInst::Ljumptable(*arg, addrs);

    ltl_inst(addr, ltlinst) <--
        linear_inst(addr, ?LinearInst::Ljumptable(_, _)),
        !jumptable_has_resolved(addr),
        next(addr, fallthrough),
        let ltlinst = LTLInst::Lbranch(Either::Right(*fallthrough));

    ltl_fallthrough(src, dst) <--
        ltl_inst(src, ltlinst),
        if crate::decompile::passes::linear_pass::has_fallthrough(&ltlinst, *src),
        !call_targets_noreturn(src),
        next(src, ft),
        ltl_canonical_node(ft, dst),
        ltl_inst(dst, _);

    // Do not reintroduce a global ltl_fallthrough skip-over for missing-ltl_inst addresses: the SP-indexed-load synth case is now handled scoped in rtl_pass.rs (sp_synth_skip_to_ltl); the global form broke loop-detection across many unrelated tests.

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

    ltl_branch_targets_at(src, Set::singleton(*dst)) <--
        ltl_branch_edge(src, dst);

    ltl_branch_targets_at(src, downstream.clone()) <--
        ltl_branch_edge(src, next),
        ltl_branch_targets_at(next, downstream);

    ltl_branch_cycle(n) <--
        ltl_branch_targets_at(n, targets),
        if targets.contains(n);

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

    // A node with an immediate-to-stack store (mach_imm_stack_init, e.g. `movl $imm,-off(rbp)`) has a real side effect but no linear_inst, so it must be its own canonical node: branch targets must not be threaded past it, which would drop the store and leave the stack slot use-before-def.
    ltl_canonical_node(n, n) <--
        mach_imm_stack_init(n, _, _, _);

    // Same hazard for the whole no-linear-op side-effect class: it surfaces as a bare label+Lbranch, so keep it self-canonical or threading drops the update.
    ltl_canonical_node(n, n) <--
        node_unlowered_side_effect(n);

    ltl_canonical_node(n, canon) <--
        ltl_inst(n, inst),
        if let LTLInst::Lbranch(Either::Right(t)) = inst,
        if *t != *n,
        !ltl_branch_cycle(n),
        !mach_imm_stack_init(n, _, _, _),
        !node_unlowered_side_effect(n),
        ltl_canonical_node(*t, canon);

    ltl_canonical_node(*target_addr, *target_addr) <--
        linear_inst(_, ?LinearInst::Lcond(_, _, target_sym)),
        symbol_resolved_addr(*target_sym, target_addr);

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


    intrinsic_noreturn_call_site(call_site) <--
        known_noreturn_call_site(call_site);

    intrinsic_noreturn_call_site(call_site) <--
        ltl_inst(call_site, ?LTLInst::Lcall(Either::Right(Either::Right(symbol)))),
        is_known_noreturn_function(symbol);

    intrinsic_noreturn_call_site(call_site) <--
        call_to_external(call_site, symbol),
        is_known_noreturn_function(symbol);

    intrinsic_noreturn_call_site(call_site) <--
        call_to_callee(call_site, callee_addr),
        plt_entry(callee_addr, name),
        is_known_noreturn_function(name);

    intrinsic_noreturn_call_site(call_site) <--
        call_to_callee(call_site, callee_addr),
        plt_block(callee_addr, name),
        is_known_noreturn_function(name);

    call_targets_noreturn(call_site) <--
        intrinsic_noreturn_call_site(call_site);

    call_targets_noreturn(call_site) <--
        call_to_callee(call_site, callee),
        function_noreturn(callee);

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

    call_to_callee(call_site, *addr) <--
        ltl_inst(call_site, ?LTLInst::Lcall(Either::Right(Either::Right(symbol)))),
        symbol_resolved_addr(*symbol, addr);

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
        !symbol_resolved_addr(*symbol, _);

    call_may_target(call_site, callee) <--
        call_to_callee(call_site, callee);

    call_may_target(call_site, target) <--
        indirect_call_target(call_site, target);

    function_return_point(func, ret_inst) <--
        instr_in_function(ret_inst, func),
        ltl_inst(ret_inst, ?LTLInst::Lreturn);

    emit_function_has_return_candidate(func) <--
        function_return_point(func, _);

    // Absence of a return is meaningful only for a completely represented
    // control-flow body.  Merely seeing one lowered instruction is not enough:
    // a missing return/tail instruction at another block would otherwise turn
    // a partial lift into a permanent noreturn fact.
    function_has_ltl_body(func) <--
        instr_in_function(node, func),
        ltl_inst(node, _);

    function_block_has_ltl(func, block) <--
        block_in_function(block, func),
        code_in_block(node, block),
        ltl_inst(node, _);

    // A block every instruction of which an explained recovery removed is covered too: the
    // canary-failure `call __stack_chk_fail` block, canary bookkeeping, VLA size arithmetic.
    // What those instructions did is accounted for, and the canary path never returns. Counting
    // that block as unknown code made every stack-protected function open, so no frame-escape
    // or callee summary ever applied to one.
    #[local] relation block_has_unexplained_code(Address, Address);
    block_has_unexplained_code(func, block) <--
        block_in_function(block, func),
        code_in_block(node, block),
        !trim_instruction(node);

    function_has_uncovered_block(func) <--
        block_in_function(block, func),
        !function_block_has_ltl(func, block),
        block_has_unexplained_code(func, block);

    // Function-bounded skip walk over instructions that carry no LTL form.
    // Such an instruction has no control-flow effect of its own -- a prologue
    // push the Stacking reversal drops is still a straight-line step -- so the
    // LTL-level fallthrough successor is the next instruction that does carry
    // one. Without the walk the chain breaks at the dropped instruction and the
    // ordinary instruction before it is mistaken for unexplained control flow,
    // which is what stopped xalloc_die from being recognized as noreturn.
    #[local] relation ltl_fallthrough_skip(Address, Node, Node);
    ltl_fallthrough_skip(*func, *src, *dst) <--
        instr_in_function(src, func),
        next(src, dst),
        instr_in_function(dst, func);
    ltl_fallthrough_skip(*func, *src, *dst) <--
        ltl_fallthrough_skip(func, src, mid),
        !ltl_inst(mid, _),
        next(mid, dst),
        instr_in_function(dst, func);

    // Local CFG edges used only to prove that an LTL node is not an unknown
    // terminal.  Calls use their structural next edge without consulting
    // function_noreturn, avoiding a negative recursive dependency.
    function_ltl_internal_succ(func, src, dst) <--
        instr_in_function(src, func),
        ltl_inst(src, inst),
        if crate::decompile::passes::linear_pass::has_fallthrough(inst, *src),
        ltl_fallthrough_skip(func, src, next_node),
        ltl_canonical_node(*next_node, dst),
        ltl_inst(dst, _),
        instr_in_function(dst, func);

    // The early ABI pass can prove a raw call site noreturn even when the call
    // itself was intentionally trimmed from LTL.  Its immediate structural
    // predecessor therefore has an explained sink, not an unknown terminal.
    function_ltl_internal_succ(func, src, sink) <--
        instr_in_function(src, func),
        ltl_inst(src, inst),
        if crate::decompile::passes::linear_pass::has_fallthrough(inst, *src),
        next(src, sink),
        known_noreturn_call_site(sink),
        instr_in_function(sink, func);

    function_ltl_internal_succ(func, src, dst) <--
        instr_in_function(src, func),
        ltl_branch_target(src, dst),
        instr_in_function(dst, func);

    // A branch whose target carries no LTL form -- the entry endbr64 branching
    // into a dropped prologue push is the common shape -- still transfers
    // control; its effective LTL target is the next instruction that does carry
    // one. Deliberately scoped to this analysis rather than fixed in
    // ltl_branch_target: the note above records that giving the REAL CFG a
    // global skip-over broke loop detection, and nothing here feeds the CFG.
    function_ltl_internal_succ(func, src, dst) <--
        instr_in_function(src, func),
        ltl_inst(src, ltlinst),
        if let LTLInst::Lbranch(Either::Right(target)) = ltlinst,
        if *target != *src,
        !ltl_inst(*target, _),
        ltl_fallthrough_skip(func, target, mid),
        ltl_canonical_node(*mid, dst),
        ltl_inst(dst, _),
        instr_in_function(dst, func);

    function_ltl_internal_succ(func, src, dst) <--
        instr_in_function(src, func),
        ltl_inst(src, ?LTLInst::Lcond(_, _, ifso, _)),
        if let Either::Right(dst) = ifso,
        ltl_inst(dst, _),
        instr_in_function(dst, func);

    function_ltl_internal_succ(func, src, dst) <--
        instr_in_function(src, func),
        ltl_inst(src, ?LTLInst::Lcond(_, _, _, ifnot)),
        if let Either::Right(dst) = ifnot,
        ltl_inst(dst, _),
        instr_in_function(dst, func);

    function_ltl_internal_succ(func, src, dst) <--
        instr_in_function(src, func),
        ltl_jumptable_target(src, dst),
        instr_in_function(dst, func);

    // Reachable code only. Alignment padding sitting after a call that never
    // returns is not control flow the analysis failed to explain, it is dead
    // bytes inside the function span, and letting it veto the classification
    // is what kept every gnulib die-style wrapper from being recognized.
    // Control does not fall out of a noreturn call, so that edge is excluded
    // from the walk rather than assumed away.
    #[local] relation function_ltl_entry(Address, Node);
    function_ltl_entry(*func, *func) <-- func_span(_, func, _), ltl_inst(func, _);
    function_ltl_entry(*func, *dst) <--
        func_span(_, func, _),
        !ltl_inst(func, _),
        ltl_fallthrough_skip(func, func, dst),
        ltl_inst(dst, _);

    #[local] relation function_has_ltl_entry(Address);
    function_has_ltl_entry(*func) <-- function_ltl_entry(func, _);

    #[local] relation function_ltl_reachable(Address, Node);
    function_ltl_reachable(*func, *entry) <-- function_ltl_entry(func, entry);
    function_ltl_reachable(*func, *dst) <--
        function_ltl_reachable(func, src),
        !intrinsic_noreturn_call_site(src),
        function_ltl_internal_succ(func, src, dst);

    function_unknown_terminal(func, node) <--
        instr_in_function(node, func),
        ltl_inst(node, inst),
        !function_ltl_internal_succ(func, node, _),
        if !matches!(inst, LTLInst::Lreturn | LTLInst::Ltailcall(_)),
        !intrinsic_noreturn_call_site(node),
        function_ltl_reachable(func, node);

    // No entry could be established, so reachability proves nothing; keep the
    // original conservative reading rather than classify on missing evidence.
    function_unknown_terminal(func, node) <--
        instr_in_function(node, func),
        ltl_inst(node, inst),
        !function_ltl_internal_succ(func, node, _),
        if !matches!(inst, LTLInst::Lreturn | LTLInst::Ltailcall(_)),
        !intrinsic_noreturn_call_site(node),
        !function_has_ltl_entry(func);

    function_unresolved_control(func, node) <--
        instr_in_function(node, func),
        ltl_inst(node, ?LTLInst::Lbranch(Either::Left(_)));

    function_unresolved_control(func, node) <--
        instr_in_function(node, func),
        ltl_inst(node, ?LTLInst::Lcond(_, _, ifso, ifnot)),
        if matches!(ifso, Either::Left(_)) || matches!(ifnot, Either::Left(_));

    function_unresolved_control(func, node) <--
        instr_in_function(node, func),
        linear_inst(node, ?LinearInst::Ljumptable(_, _)),
        !jumptable_has_resolved(node);

    function_has_intrinsic_noreturn(func) <--
        instr_in_function(node, func),
        intrinsic_noreturn_call_site(node);

    // A tail-call-only wrapper returns through its callee even though it has no
    // Lreturn of its own, so it must not be classified as noreturn.
    function_has_tailcall(func) <--
        instr_in_function(node, func),
        ltl_inst(node, ?LTLInst::Ltailcall(_));

    // emit_function is not populated until rtl_pass. func_span is the
    // structural function inventory already available here, so use it to cut
    // false call fallthrough before building the LTL CFG.
    function_noreturn(func) <--
        func_span(_, func, _),
        function_has_ltl_body(func),
        function_has_intrinsic_noreturn(func),
        !function_has_uncovered_block(func),
        !emit_function_has_return_candidate(func),
        !function_has_tailcall(func),
        !function_unknown_terminal(func, _),
        !function_unresolved_control(func, _);

    // An FDE start is authoritative function evidence, but only after function
    // inference independently produced the same func_span (an FDE may also
    // describe a cold fragment). A completely covered, closed CFG with no
    // return, tail call, unresolved edge, or unexplained terminal cannot
    // return even when it contains no already-known noreturn callee -- the
    // canonical case is a function whose only reachable region is a cycle.
    function_noreturn(func) <--
        fde_function_start(func),
        func_span(_, func, _),
        function_has_ltl_body(func),
        !function_has_uncovered_block(func),
        !emit_function_has_return_candidate(func),
        !function_has_tailcall(func),
        !function_unknown_terminal(func, _),
        !function_unresolved_control(func, _);

    // A function whose declared symbol is itself a known-noreturn name is noreturn (a binary defining exit/abort directly).
    function_noreturn(func) <--
        func_span(name, func, _),
        is_known_noreturn_function(name);


    return_may_reach(ret_inst, ret_addr) <--
        function_return_point(callee, ret_inst),
        call_may_target(call_site, callee),
        call_return_site(call_site, ret_addr);


    ltl_succ(call_site, callee_entry) <--
        call_may_target(call_site, callee_entry);

    ltl_succ(ret_inst, ret_addr) <--
        return_may_reach(ret_inst, ret_addr);


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

    // A call continues the block sequence ONLY if it can return; a noreturn call terminates it, since the fallthrough successor is dead code.
    emit_sseq(head, next) <--
        emit_sseq(head, current),
        ltl_fallthrough(current, next),
        ltl_inst(current, inst),
        if let LTLInst::Lcall(..) = inst,
        !call_targets_noreturn(current);


}

pub struct LinearPass;

impl IRPass for LinearPass {
    fn name(&self) -> &'static str {
        "linear"
    }

    fn run(&self, db: &mut DecompileDB) {
        run_pass!(db, LinearPassProgram);

        let linear_lcond_count = db
            .rel_iter::<(Address, LinearInst)>("linear_inst")
            .filter(|(_, inst)| matches!(inst, LinearInst::Lcond(..)))
            .count();
        let ltl_lcond_count = db
            .rel_iter::<(Node, LTLInst)>("ltl_inst")
            .filter(|(_, inst)| matches!(inst, LTLInst::Lcond(..)))
            .count();
        if linear_lcond_count != ltl_lcond_count {
            info!("[LinearPass] Lcond conversion: {}/{} linear Lcond converted to LTL Lcond ({} diff)",
                ltl_lcond_count, linear_lcond_count, (linear_lcond_count as isize) - (ltl_lcond_count as isize));
        }
    }

    declare_io_from!(LinearPassProgram);
}

#[cfg(test)]
mod tests {
    use super::{LinearPass, LinearPassProgram};
    use crate::decompile::passes::pass::IRPass;
    use crate::decompile::passes::rtl_pass::RTLPass;
    use crate::x86::op::{Comparison, Condition};
    use crate::x86::types::{LTLInst, LinearInst};
    use either::Either;
    use std::collections::HashSet;
    use std::sync::Arc;

    #[test]
    fn linear_is_the_only_noreturn_producer() {
        let linear = LinearPass;
        let rtl = RTLPass;

        assert!(linear.outputs().contains(&"function_noreturn"));
        assert!(!rtl.outputs().contains(&"function_noreturn"));
    }

    #[test]
    fn branch_cycles_use_point_keyed_reachable_sets() {
        let mut prog = LinearPassProgram::default();
        // Deliberately nonmonotonic identifiers: cycle membership follows only
        // these edges, never numeric order.
        prog.ltl_branch_candidate.push((90, 10));
        prog.ltl_branch_candidate.push((10, 70));
        prog.ltl_branch_candidate.push((70, 90));
        prog.ltl_branch_candidate.push((70, 5));
        prog.ltl_branch_candidate.push((40, 30));
        prog.ltl_branch_candidate.push((9, 9));

        prog.run();

        let cycles: HashSet<_> = prog.ltl_branch_cycle.iter().map(|(n,)| *n).collect();
        assert_eq!(cycles, HashSet::from([10, 70, 90]));
    }

    #[test]
    fn condition_fallthrough_keeps_rtl_only_memory_read_node() {
        let mut prog = LinearPassProgram::default();
        // Deliberately nonmonotonic identifiers: the two next edges, not node
        // magnitude, establish compare -> jcc -> memory-read fallthrough.
        let cmp = 0x900;
        let jcc = 0x100;
        let memory_read = 0x700;
        let after_read = 0x200;
        let taken = 0x800;
        let func = 0x500;

        prog.linear_inst.push((
            cmp,
            LinearInst::Lcond(
                Condition::Ccompimm(Comparison::Ceq, 5),
                Arc::new(vec![]),
                "taken",
            ),
        ));
        prog.linear_inst.push((after_read, LinearInst::Lreturn));
        prog.linear_inst.push((taken, LinearInst::Lreturn));
        prog.symbol_resolved_addr.push(("taken", taken));
        prog.next.push((cmp, jcc));
        prog.next.push((jcc, memory_read));
        prog.next.push((memory_read, after_read));
        prog.block_in_function.push((memory_read, func));
        prog.node_unlowered_side_effect.push((memory_read,));

        prog.run();

        assert!(prog.ltl_inst.iter().any(|(node, inst)| {
            *node == cmp
                && matches!(
                    inst,
                    LTLInst::Lcond(_, _, Either::Right(t), Either::Right(f))
                        if *t == taken && *f == memory_read
                )
        }));
        assert!(!prog.ltl_inst.iter().any(|(node, inst)| {
            *node == cmp
                && matches!(
                    inst,
                    LTLInst::Lcond(_, _, _, Either::Right(f)) if *f == after_read
                )
        }));
        assert!(prog
            .ltl_canonical_node
            .iter()
            .any(|fact| fact == &(memory_read, memory_read)));
        assert!(!prog
            .ltl_canonical_node
            .iter()
            .any(|fact| fact == &(memory_read, after_read)));
    }

    #[test]
    fn interior_unlowered_side_effect_gets_an_ltl_point() {
        let mut prog = LinearPassProgram::default();
        // Deliberately omit block_in_function(event): an interior instruction
        // is retained because of its side effect, not because it starts a
        // block.  Structural next is the only fallthrough evidence required.
        let event = 0x900;
        let next = 0x100;
        prog.next.push((event, next));
        prog.node_unlowered_side_effect.push((event,));

        prog.run();

        assert!(prog.ltl_inst.iter().any(|(node, inst)| {
            *node == event && matches!(inst, LTLInst::Lbranch(Either::Right(dst)) if *dst == next)
        }));
        assert!(prog
            .ltl_canonical_node
            .iter()
            .any(|fact| fact == &(event, event)));
    }

    #[test]
    fn trimmed_known_noreturn_call_does_not_become_fallthrough() {
        let mut prog = LinearPassProgram::default();

        prog.block_in_function.push((0x01, 0x01));
        prog.block_in_function.push((0x10, 0x01));
        prog.block_in_function.push((0x20, 0x01));
        prog.block_in_function.push((0x30, 0x01));
        prog.block_in_function.push((0x40, 0x01));
        prog.ddisasm_function_entry.push((0x01,));
        prog.known_noreturn_call_site.push((0x10,));
        prog.known_noreturn_call_site.push((0x30,));
        prog.linear_inst
            .push((0x10, LinearInst::Llabel("L_10".into())));
        prog.linear_inst.push((0x20, LinearInst::Lreturn));
        prog.linear_inst.push((0x40, LinearInst::Lreturn));
        prog.next.push((0x10, 0x20));
        prog.next.push((0x30, 0x40));

        prog.run();

        assert!(prog
            .call_targets_noreturn
            .iter()
            .any(|fact| fact == &(0x10,)));
        assert!(prog
            .call_targets_noreturn
            .iter()
            .any(|fact| fact == &(0x30,)));
        assert!(!prog.ltl_inst.iter().any(|(node, _)| *node == 0x10));
        assert!(!prog.ltl_inst.iter().any(|(node, _)| *node == 0x30));
        assert!(prog
            .ltl_inst
            .iter()
            .any(|fact| fact == &(0x20, LTLInst::Lreturn)));
    }

    #[test]
    fn known_noreturn_call_keeps_call_but_not_fallthrough() {
        let mut prog = LinearPassProgram::default();

        prog.known_noreturn_call_site.push((0x10,));
        prog.linear_inst
            .push((0x10, LinearInst::Lcall(Either::Right(Either::Right(0x100)))));
        prog.linear_inst.push((0x20, LinearInst::Lreturn));
        prog.next.push((0x10, 0x20));

        prog.linear_inst
            .push((0x30, LinearInst::Lcall(Either::Right(Either::Right(0x200)))));
        prog.linear_inst.push((0x40, LinearInst::Lreturn));
        prog.next.push((0x30, 0x40));

        prog.run();

        assert!(prog
            .ltl_inst
            .iter()
            .any(|(node, inst)| { *node == 0x10 && matches!(inst, LTLInst::Lcall(_)) }));
        assert!(!prog
            .ltl_fallthrough
            .iter()
            .any(|fact| fact == &(0x10, 0x20)));
        assert!(prog
            .ltl_fallthrough
            .iter()
            .any(|fact| fact == &(0x30, 0x40)));
    }

    #[test]
    fn structural_noreturn_function_cuts_internal_call_fallthrough() {
        let mut prog = LinearPassProgram::default();

        let callee = 0x100;
        let callee_exit_call = 0x110;
        let call_site = 0x10;
        let return_site = 0x20;

        prog.func_span.push(("die", callee, 0x120));
        prog.instr_in_function.push((callee_exit_call, callee));
        prog.block_in_function.push((callee, callee));
        prog.code_in_block.push((callee_exit_call, callee));
        prog.is_known_noreturn_function.push(("exit",));
        prog.linear_inst.push((
            callee_exit_call,
            LinearInst::Lcall(Either::Right(Either::Left("exit"))),
        ));

        prog.linear_inst.push((
            call_site,
            LinearInst::Lcall(Either::Right(Either::Right(callee))),
        ));
        prog.linear_inst.push((return_site, LinearInst::Lreturn));
        prog.next.push((call_site, return_site));

        prog.run();

        assert!(prog.function_noreturn.iter().any(|fact| fact == &(callee,)));
        assert!(prog
            .call_targets_noreturn
            .iter()
            .any(|fact| fact == &(call_site,)));
        assert!(!prog
            .ltl_fallthrough
            .iter()
            .any(|fact| fact == &(call_site, return_site)));
        assert!(!prog
            .call_return_site
            .iter()
            .any(|(node, _)| *node == call_site));
    }

    // The shape of every gnulib die-style wrapper in a stripped binary: the
    // entry endbr64 lowers to a branch into the prologue push, which carries no
    // LTL form at all. Before the skip walk that broke the successor chain and
    // the entry looked like unexplained control flow, so the function was never
    // classified noreturn and every caller kept a fallthrough edge that does
    // not exist.
    #[test]
    fn a_branch_into_a_dropped_prologue_still_reaches_its_ltl_successor() {
        let mut prog = LinearPassProgram::default();

        let callee = 0x100;
        let dropped = 0x104;
        let body = 0x105;
        let exit_call = 0x110;
        let call_site = 0x10;
        let return_site = 0x20;

        prog.func_span.push(("die", callee, 0x120));
        for addr in [callee, dropped, body, exit_call] {
            prog.instr_in_function.push((addr, callee));
        }
        prog.block_in_function.push((callee, callee));
        for addr in [callee, body, exit_call] {
            prog.code_in_block.push((addr, callee));
        }
        // The entry branches into `dropped`, which carries no LTL form at all.
        prog.ltl_inst
            .push((callee, LTLInst::Lbranch(Either::Right(dropped))));
        prog.ltl_canonical_node.push((callee, callee));
        prog.next.push((callee, dropped));
        prog.next.push((dropped, body));
        prog.ltl_inst
            .push((body, LTLInst::Lbranch(Either::Right(exit_call))));
        prog.ltl_canonical_node.push((body, body));
        prog.next.push((body, exit_call));
        prog.is_known_noreturn_function.push(("exit",));
        prog.linear_inst.push((
            exit_call,
            LinearInst::Lcall(Either::Right(Either::Left("exit"))),
        ));
        prog.ltl_canonical_node.push((exit_call, exit_call));

        prog.linear_inst.push((
            call_site,
            LinearInst::Lcall(Either::Right(Either::Right(callee))),
        ));
        prog.linear_inst.push((return_site, LinearInst::Lreturn));
        prog.next.push((call_site, return_site));

        prog.run();

        assert!(
            !prog
                .function_unknown_terminal
                .iter()
                .any(|fact| fact == &(callee, callee)),
            "the entry branch must reach its LTL successor across the dropped instruction"
        );
        assert!(prog.function_noreturn.iter().any(|fact| fact == &(callee,)));
        assert!(!prog
            .ltl_fallthrough
            .iter()
            .any(|fact| fact == &(call_site, return_site)));
    }

    // Alignment padding after the noreturn call is inside the function span but
    // is not reachable: control does not fall out of a call that never returns.
    // Counting it as unexplained control flow vetoed the classification.
    #[test]
    fn padding_after_a_noreturn_call_does_not_veto_the_classification() {
        let mut prog = LinearPassProgram::default();

        let callee = 0x100;
        let exit_call = 0x110;
        let padding = 0x118;
        let call_site = 0x10;
        let return_site = 0x20;

        prog.func_span.push(("die", callee, 0x120));
        for addr in [callee, exit_call, padding] {
            prog.instr_in_function.push((addr, callee));
        }
        prog.block_in_function.push((callee, callee));
        for addr in [callee, exit_call, padding] {
            prog.code_in_block.push((addr, callee));
        }
        prog.ltl_inst
            .push((callee, LTLInst::Lbranch(Either::Right(exit_call))));
        prog.ltl_canonical_node.push((callee, callee));
        prog.next.push((callee, exit_call));
        prog.is_known_noreturn_function.push(("exit",));
        prog.linear_inst.push((
            exit_call,
            LinearInst::Lcall(Either::Right(Either::Left("exit"))),
        ));
        prog.ltl_canonical_node.push((exit_call, exit_call));
        // Padding: has an LTL form, sits in the span, and has no successor of
        // its own because the next instruction belongs to the next function.
        prog.next.push((exit_call, padding));
        prog.ltl_inst
            .push((padding, LTLInst::Lbranch(Either::Right(0x120))));
        prog.ltl_canonical_node.push((padding, padding));

        prog.linear_inst.push((
            call_site,
            LinearInst::Lcall(Either::Right(Either::Right(callee))),
        ));
        prog.linear_inst.push((return_site, LinearInst::Lreturn));
        prog.next.push((call_site, return_site));

        prog.run();

        assert!(
            !prog
                .function_unknown_terminal
                .iter()
                .any(|fact| fact == &(callee, padding)),
            "unreachable padding must not count as unexplained control flow"
        );
        assert!(prog.function_noreturn.iter().any(|fact| fact == &(callee,)));
    }

    #[test]
    fn uncovered_block_prevents_structural_noreturn() {
        let mut prog = LinearPassProgram::default();

        let func = 0x100;
        let covered_block = 0x110;
        let uncovered_block = 0x120;
        let exit_call = 0x111;
        let unlifted = 0x121;
        prog.func_span.push(("partial", func, 0x130));
        prog.block_in_function.push((covered_block, func));
        prog.block_in_function.push((uncovered_block, func));
        prog.code_in_block.push((exit_call, covered_block));
        prog.code_in_block.push((unlifted, uncovered_block));
        prog.instr_in_function.push((exit_call, func));
        prog.instr_in_function.push((unlifted, func));
        prog.is_known_noreturn_function.push(("exit",));
        prog.linear_inst.push((
            exit_call,
            LinearInst::Lcall(Either::Right(Either::Left("exit"))),
        ));

        prog.run();

        assert!(prog
            .function_has_uncovered_block
            .iter()
            .any(|fact| fact == &(func,)));
        assert!(!prog.function_noreturn.iter().any(|fact| fact == &(func,)));
    }

    #[test]
    fn unexplained_terminal_prevents_structural_noreturn() {
        let mut prog = LinearPassProgram::default();

        let func = 0x100;
        let exit_block = 0x110;
        let unknown_block = 0x120;
        let exit_call = 0x111;
        let unknown_call = 0x121;
        prog.func_span.push(("partial_terminal", func, 0x130));
        for (block, node) in [(exit_block, exit_call), (unknown_block, unknown_call)] {
            prog.block_in_function.push((block, func));
            prog.code_in_block.push((node, block));
            prog.instr_in_function.push((node, func));
        }
        prog.is_known_noreturn_function.push(("exit",));
        prog.linear_inst.push((
            exit_call,
            LinearInst::Lcall(Either::Right(Either::Left("exit"))),
        ));
        prog.linear_inst.push((
            unknown_call,
            LinearInst::Lcall(Either::Right(Either::Left("unknown_target"))),
        ));

        prog.run();

        assert!(prog
            .function_unknown_terminal
            .iter()
            .any(|fact| fact == &(func, unknown_call)));
        assert!(!prog.function_noreturn.iter().any(|fact| fact == &(func,)));
    }

    #[test]
    fn tailcall_only_function_is_not_structurally_noreturn() {
        let mut prog = LinearPassProgram::default();

        let func = 0x100;
        let tailcall = 0x110;
        prog.func_span.push(("forwarder", func, 0x120));
        prog.instr_in_function.push((tailcall, func));
        prog.linear_inst.push((
            tailcall,
            LinearInst::Ltailcall(Either::Right(Either::Left("target"))),
        ));

        prog.run();

        assert!(prog
            .function_has_tailcall
            .iter()
            .any(|fact| fact == &(func,)));
        assert!(!prog.function_noreturn.iter().any(|fact| fact == &(func,)));
    }

    #[test]
    fn returned_function_is_not_structurally_noreturn() {
        let mut prog = LinearPassProgram::default();

        let func = 0x100;
        let ret = 0x110;
        prog.func_span.push(("returns", func, 0x120));
        prog.instr_in_function.push((ret, func));
        prog.linear_inst.push((ret, LinearInst::Lreturn));

        prog.run();

        assert!(prog
            .emit_function_has_return_candidate
            .iter()
            .any(|fact| fact == &(func,)));
        assert!(!prog.function_noreturn.iter().any(|fact| fact == &(func,)));
    }

    #[test]
    fn fde_function_with_closed_cfg_and_no_exit_is_noreturn() {
        let mut prog = LinearPassProgram::default();

        let func = 0x100;
        prog.fde_function_start.push((func,));
        prog.func_span.push(("spin", func, 0x120));
        prog.block_in_function.push((func, func));
        prog.code_in_block.push((func, func));
        prog.instr_in_function.push((func, func));
        prog.ltl_inst
            .push((func, LTLInst::Lbranch(Either::Right(func))));
        prog.ltl_branch_target.push((func, func));

        prog.run();

        assert!(prog.function_noreturn.iter().any(|fact| fact == &(func,)));
    }

    #[test]
    fn closed_cfg_without_fde_evidence_is_not_promoted() {
        let mut prog = LinearPassProgram::default();

        let func = 0x100;
        prog.func_span.push(("heuristic_spin", func, 0x120));
        prog.block_in_function.push((func, func));
        prog.code_in_block.push((func, func));
        prog.instr_in_function.push((func, func));
        prog.ltl_inst
            .push((func, LTLInst::Lbranch(Either::Right(func))));
        prog.ltl_branch_target.push((func, func));

        prog.run();

        assert!(!prog.function_noreturn.iter().any(|fact| fact == &(func,)));
    }

    #[test]
    fn inventory_only_function_is_not_structurally_noreturn() {
        let mut prog = LinearPassProgram::default();

        let func = 0x100;
        prog.func_span.push(("unlifted", func, 0x120));

        prog.run();

        assert!(!prog
            .function_has_ltl_body
            .iter()
            .any(|fact| fact == &(func,)));
        assert!(!prog.function_noreturn.iter().any(|fact| fact == &(func,)));
    }
}

// Ascent aggregator: collects jumptable target addresses sorted by index.
pub fn build_jumptable_addrs<'a>(
    inp: impl Iterator<Item = (&'a usize, &'a Address)>,
) -> impl Iterator<Item = Vec<Address>> {
    let mut pairs: Vec<(usize, Address)> = inp.map(|(idx, addr)| (*idx, *addr)).collect();
    pairs.sort_by_key(|(idx, _)| *idx);
    let addrs: Vec<Address> = pairs.into_iter().map(|(_, addr)| addr).collect();
    std::iter::once(addrs)
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
