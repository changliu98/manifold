

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::{declare_io_from, run_pass};

use std::sync::Arc;
use std::collections::HashMap;
use crate::decompile::passes::cminor_pass::*;
use crate::decompile::passes::csh_pass::*;

use crate::x86::mach::Mreg;
use crate::x86::op::{Comparison, Condition};
use crate::x86::types::*;
use log::debug;
use ascent::ascent_par;
use either::Either;


ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct ClightPassProgram;

    relation addr_to_func_ident(Address, Ident);
    relation arch_bit(i64);
    relation arg_constrained_as_ptr(Node, RTLReg);
    relation base_ident_to_symbol(Ident, Symbol);
    relation block_in_function(Node, Address);
    relation block_span(Node, Node);
    relation builtin_func_type(Symbol, Arc<Vec<XType>>, XType);
    relation call_arg_struct_ptr(Node, usize, usize);
    relation call_return_reg(Node, RTLReg);
    relation cminor_stmt(Node, CminorStmt);
    relation code_in_block(Address, Address);
    relation emit_function(Address, Symbol, Node);
    relation emit_function_has_return(Address);
    relation emit_function_param(Address, RTLReg);
    relation emit_function_return(Address, RTLReg);
    relation emit_function_return_type(Address, ClightType);
    relation emit_function_void(Address);
    relation emit_reg_type(RTLReg, ClightType);
    relation emit_sseq(Node, Node);
    relation emit_var_type_candidate(RTLReg, XType);
    relation func_param_struct_type(Address, usize, usize);
    relation func_return_struct_type(Address, usize);
    relation func_span(Symbol, Address, Address);
    relation global_struct_catalog(u64, usize, usize, usize);
    relation ident_to_symbol(Ident, Symbol);
    relation instr_in_function(Node, Address);
    relation is_external_function(Address);
    relation is_ptr(RTLReg);
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
    relation rtl_inst(Node, RTLInst);
    relation rtl_succ(Node, Node);
    relation next(Address, Address);
    relation stack_var(Address, Address, i64, RTLReg);
    relation string_data(String, String, usize);
    relation struct_field(u64, i64, String, MemoryChunk);
    relation struct_id_to_canonical(usize, usize);

    relation branch_compares_const(Node, RTLReg, i64, Comparison);
    relation cminor_succ(Node, Node);
    relation csharp_stmt(Node, CsharpminorStmt);
    relation emit_loop_body(Address, Node, Node);
    relation emit_loop_exit(Address, Node, Node, Condition, Arc<Vec<CsharpminorExpr>>, Node, Node);
    relation emit_switch_chain(Address, Node, RTLReg);
    relation func_entry_node(Address, Node);
    relation has_csharp_stmt(Node);
    relation loop_body(Address, Node, Node);
    relation loop_exit_branch(Address, Node, Node, Condition, Arc<Vec<CsharpminorExpr>>, Node, Node, bool);
    relation loop_head(Address, Node);
    relation primary_exit_node(Address, Node, Node);
    relation switch_chain_member(Address, Node, Node, RTLReg, i64, Node);
    relation ternary_false_assignment(Address, Node, RTLReg, CsharpminorExpr, Node);
    relation ternary_true_assignment(Address, Node, RTLReg, CsharpminorExpr, Node);
    relation valid_loop(Address, Node);
    relation valid_switch_chain(Address, Node, RTLReg);
    relation valid_ternary(Address, Node, RTLReg, CsharpminorExpr, CsharpminorExpr, Node);

    relation clight_dead_var(Address, Ident);
    relation clight_efield_info(Address, Node, i64, i64, Ident, MemoryChunk);
    relation clight_stmt_without_field(Node, ClightStmt);
    relation clight_stmt_dead_without_field(Address, Node, ClightStmt);
    relation clight_stmt_for_func_raw(Address, Node, ClightStmt);
    relation clight_stmt_raw(Node, ClightStmt);
    relation clight_succ(Node, Node);
    relation clight_var_read(Address, Ident);
    relation clight_var_write(Address, Ident);
    relation efield_to_struct(Node, i64, i64, Ident, MemoryChunk);
    relation eligible_node_for_sseq(Node);
    relation emit_clight_stmt_without_field(Address, Node, ClightStmt);
    relation emit_goto_target(Address, Node);
    relation emit_next(Node, Node);
    relation emit_struct_fields(Address, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>);
    relation linear_succ_sseq(Node, Node);
    relation node_nonempty(Node);
    relation sseq_has_pred(Node);
    relation sseq_head(Node);
    relation valid_next(Node);

    // Sstore type divergence: primary type + sign-flipped variants for ambiguous chunks
    relation sstore_clight_type(Node, ClightType);

    sstore_clight_type(node, clight_type_from_chunk(&chunk)) <--
        csharp_stmt(node, ?CsharpminorStmt::Sstore(chunk, _, _));

    sstore_clight_type(node, ClightType::Tint(ClightIntSize::I8, ClightSignedness::Unsigned, default_attr())) <--
        csharp_stmt(node, ?CsharpminorStmt::Sstore(chunk, _, _)),
        if let MemoryChunk::MInt8Signed = chunk;

    sstore_clight_type(node, ClightType::Tint(ClightIntSize::I8, ClightSignedness::Signed, default_attr())) <--
        csharp_stmt(node, ?CsharpminorStmt::Sstore(chunk, _, _)),
        if let MemoryChunk::MInt8Unsigned = chunk;

    sstore_clight_type(node, ClightType::Tint(ClightIntSize::I16, ClightSignedness::Unsigned, default_attr())) <--
        csharp_stmt(node, ?CsharpminorStmt::Sstore(chunk, _, _)),
        if let MemoryChunk::MInt16Signed = chunk;

    sstore_clight_type(node, ClightType::Tint(ClightIntSize::I16, ClightSignedness::Signed, default_attr())) <--
        csharp_stmt(node, ?CsharpminorStmt::Sstore(chunk, _, _)),
        if let MemoryChunk::MInt16Unsigned = chunk;

    sstore_clight_type(node, ClightType::Tint(ClightIntSize::I32, ClightSignedness::Unsigned, default_attr())) <--
        csharp_stmt(node, ?CsharpminorStmt::Sstore(chunk, _, _)),
        if matches!(chunk, MemoryChunk::MInt32 | MemoryChunk::MAny32);


    clight_stmt_raw(node, stmt) <--
        clight_stmt_without_field(node, s),
        if let Some(stmt) = check_clight_stmt(s);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        is_ptr(dst),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]),
        let var_type_variants = build_var_type_map_variants(&all_var_types, &vars_used),
        for var_types in var_type_variants.iter(),
        let out_expr = clight_expr_from_csharp_with_multi_types(&expr, var_types),
        let dst_ident = ident_from_reg(*dst),
        let target_ty = pointer_to(default_int_type()),
        let casted_expr = rewrite_deref_for_pointer_dest(out_expr, target_ty),
        let stmt = ClightStmt::Sset(dst_ident, casted_expr);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        emit_var_type_candidate(*dst, dst_xtype),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]),
        let var_type_variants = build_var_type_map_variants(&all_var_types, &vars_used),
        for var_types in var_type_variants.iter(),
        let out_expr = clight_expr_from_csharp_with_multi_types(&expr, var_types),
        let dst_ident = ident_from_reg(*dst),
        let target_ty = clight_type_from_xtype(&dst_xtype),
        let casted_expr = cast_expr_to_type(out_expr, target_ty),
        let stmt = ClightStmt::Sset(dst_ident, casted_expr);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        !is_ptr(dst),
        !emit_var_type_candidate(*dst, _),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]),
        let var_type_variants = build_var_type_map_variants(&all_var_types, &vars_used),
        for var_types in var_type_variants.iter(),
        let out_expr = clight_expr_from_csharp_with_multi_types(&expr, var_types),
        let dst_ident = ident_from_reg(*dst),
        let target_ty = clight_expr_type(&out_expr),
        let casted_expr = cast_expr_to_type(out_expr, target_ty),
        let stmt = ClightStmt::Sset(dst_ident, casted_expr);

    // When dst has no type candidates, emit a long-cast variant to prevent ptr-to-int conversion errors.
    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        !is_ptr(dst),
        !emit_var_type_candidate(*dst, _),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]),
        let var_type_variants = build_var_type_map_variants(&all_var_types, &vars_used),
        for var_types in var_type_variants.iter(),
        let out_expr = clight_expr_from_csharp_with_multi_types(&expr, var_types),
        let dst_ident = ident_from_reg(*dst),
        let long_expr = cast_expr_to_type(out_expr, default_long_type()),
        let stmt = ClightStmt::Sset(dst_ident, long_expr);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sstore(chunk, addr, value)),
        sstore_clight_type(node, ty),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let mut all_exprs = vec![addr.clone()],
        let _ = all_exprs.push(value.clone()),
        let vars_used = extract_vars_from_csharp_exprs(&all_exprs),
        let var_type_variants = build_var_type_map_variants(&all_var_types, &vars_used),
        for var_types in var_type_variants.iter(),
        let addr_expr = clight_expr_from_csharp_with_multi_types(&addr, var_types),
        if !matches!(addr_expr, ClightExpr::EconstInt(0, _) | ClightExpr::EconstLong(0, _)),
        let pointer_ty = pointer_to(ty.clone()),
        let lhs_addr = rewrite_expr_as_pointer(addr_expr.clone(), pointer_ty),
        if !matches!(&lhs_addr, ClightExpr::Ecast(inner, _) if matches!(inner.as_ref(), ClightExpr::EconstInt(0, _) | ClightExpr::EconstLong(0, _))),
        let lhs = ClightExpr::Ederef(Box::new(lhs_addr), ty.clone()),
        let rhs = clight_expr_from_csharp_with_multi_types(&value, var_types),
        let rhs_casted = cast_expr_to_type(rhs, ty.clone()),
        let stmt = ClightStmt::Sassign(lhs.clone(), rhs_casted.clone());

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Left(expr), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        emit_function_return(func_addr, ret_reg),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let mut all_exprs = vec![expr.clone()],
        let _ = all_exprs.extend_from_slice(args.as_slice()),
        let vars_used = extract_vars_from_csharp_exprs(&all_exprs),
        let var_types = filter_and_build_multi_var_type_map(&all_var_types, &vars_used),
        let dst_ident = Some(ident_from_reg(*ret_reg)),
        let ret_ident = ident_from_reg(*ret_reg),
        let raw_func_expr = clight_expr_from_csharp_with_multi_types(&expr, &var_types),
        let crude_sig = resolve_signature(&sig),
        let resolved_sig = refine_indirect_call_signature(&crude_sig, args.as_slice(), &all_var_types, &None),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Ecast(Box::new(raw_func_expr.clone()), func_ty.clone()),
        let raw_args = clight_exprs_from_csharp_with_multi_types(args.as_slice(), &var_types),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(dst_ident, func_expr, call_args),
        let ret_expr = ClightExpr::Etempvar(ret_ident, default_int_type()),
        let ret_stmt = ClightStmt::Sreturn(Some(ret_expr)),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Right(Either::Left(addr)), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        emit_function_return(func_addr, ret_reg),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = extract_vars_from_csharp_exprs(args.as_slice()),
        let var_types = filter_and_build_multi_var_type_map(&all_var_types, &vars_used),
        let dst_ident = Some(ident_from_reg(*ret_reg)),
        let ret_ident = ident_from_reg(*ret_reg),
        addr_to_func_ident(addr, func_ident),
        let resolved_sig = resolve_signature(&sig),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Evar(*func_ident, func_ty.clone()),
        let raw_args = clight_exprs_from_csharp_with_multi_types(args.as_slice(), &var_types),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(dst_ident, func_expr, call_args),
        let ret_expr = ClightExpr::Etempvar(ret_ident, default_int_type()),
        let ret_stmt = ClightStmt::Sreturn(Some(ret_expr)),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Right(Either::Left(addr)), args)),
        !addr_to_func_ident(addr, _),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        emit_function_return(func_addr, ret_reg),
        let dst_ident = Some(ident_from_reg(*ret_reg)),
        let ret_ident = ident_from_reg(*ret_reg),
        let func_ident = *addr as Ident,
        let resolved_sig = resolve_signature(&sig),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Evar(func_ident, func_ty.clone()),
        let raw_args = clight_exprs_from_csharp(args.as_slice()),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(dst_ident, func_expr, call_args),
        let ret_expr = ClightExpr::Etempvar(ret_ident, default_int_type()),
        let ret_stmt = ClightStmt::Sreturn(Some(ret_expr)),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Left(expr), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        emit_function_void(func_addr),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let raw_func_expr = clight_expr_from_csharp(&expr),
        let crude_sig = resolve_signature(&sig),
        let resolved_sig = refine_indirect_call_signature(&crude_sig, args.as_slice(), &all_var_types, &None),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Ecast(Box::new(raw_func_expr.clone()), func_ty.clone()),
        let raw_args = clight_exprs_from_csharp(args.as_slice()),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(None, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(None),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Right(Either::Left(addr)), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        emit_function_void(func_addr),
        addr_to_func_ident(addr, func_ident),
        let resolved_sig = resolve_signature(&sig),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Evar(*func_ident, func_ty.clone()),
        let raw_args = clight_exprs_from_csharp(args.as_slice()),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(None, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(None),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Right(Either::Left(addr)), args)),
        !addr_to_func_ident(addr, _),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        emit_function_void(func_addr),
        let func_ident = *addr as Ident,
        let resolved_sig = resolve_signature(&sig),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Evar(func_ident, func_ty.clone()),
        let raw_args = clight_exprs_from_csharp(args.as_slice()),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(None, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(None),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Right(Either::Right(sym)), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        emit_function_return(func_addr, ret_reg),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = extract_vars_from_csharp_exprs(args.as_slice()),
        let var_types = filter_and_build_multi_var_type_map(&all_var_types, &vars_used),
        let dst_ident = Some(ident_from_reg(*ret_reg)),
        let ret_ident = ident_from_reg(*ret_reg),
        let resolved_sig = resolve_signature(&sig),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::EvarSymbol(sym.to_string(), func_ty.clone()),
        let raw_args = clight_exprs_from_csharp_with_multi_types(args.as_slice(), &var_types),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(dst_ident, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(Some(ClightExpr::Etempvar(ret_ident, default_int_type()))),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Right(Either::Right(sym)), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        emit_function_void(func_addr),
        let resolved_sig = resolve_signature(&sig),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::EvarSymbol(sym.to_string(), func_ty.clone()),
        let raw_args = clight_exprs_from_csharp(args.as_slice()),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(None, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(None),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Left(expr), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        !emit_function_return(func_addr, _),
        !emit_function_void(func_addr),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let raw_func_expr = clight_expr_from_csharp(&expr),
        let crude_sig = resolve_signature(&sig),
        let resolved_sig = refine_indirect_call_signature(&crude_sig, args.as_slice(), &all_var_types, &None),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Ecast(Box::new(raw_func_expr), func_ty),
        let raw_args = clight_exprs_from_csharp(args.as_slice()),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(None, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(None),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Right(Either::Left(addr)), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        !emit_function_return(func_addr, _),
        !emit_function_void(func_addr),
        addr_to_func_ident(addr, func_ident),
        let resolved_sig = resolve_signature(&sig),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Evar(*func_ident, func_ty),
        let raw_args = clight_exprs_from_csharp(args.as_slice()),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(None, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(None),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Right(Either::Left(addr)), args)),
        !addr_to_func_ident(addr, _),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        !emit_function_return(func_addr, _),
        !emit_function_void(func_addr),
        let func_ident = *addr as Ident,
        let resolved_sig = resolve_signature(&sig),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Evar(func_ident, func_ty),
        let raw_args = clight_exprs_from_csharp(args.as_slice()),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(None, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(None),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Right(Either::Right(sym)), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        !emit_function_return(func_addr, _),
        !emit_function_void(func_addr),
        let resolved_sig = resolve_signature(&sig),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::EvarSymbol(sym.to_string(), func_ty),
        let raw_args = clight_exprs_from_csharp(args.as_slice()),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(None, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(None),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Scall(dst, sig, Either::Left(expr), args)),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let mut all_exprs = vec![expr.clone()],
        let _ = all_exprs.extend_from_slice(args.as_slice()),
        let vars_used = extract_vars_from_csharp_exprs(&all_exprs),
        let var_types = filter_and_build_multi_var_type_map(&all_var_types, &vars_used),
        let crude_sig = resolve_signature(&sig),
        let resolved_sig = refine_indirect_call_signature(&crude_sig, args.as_slice(), &all_var_types, dst),
        let dst_ident = if resolved_sig.sig_res == XType::Xvoid { None } else { dst.clone().map(ident_from_reg) },
        let raw_func_expr = clight_expr_from_csharp_with_multi_types(&expr, &var_types),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Ecast(Box::new(raw_func_expr.clone()), func_ty.clone()),
        let raw_args = clight_exprs_from_csharp_with_multi_types(args.as_slice(), &var_types),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let stmt = ClightStmt::Scall(dst_ident, func_expr, call_args);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Scall(dst, sig, Either::Right(Either::Left(addr)), args)),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = extract_vars_from_csharp_exprs(args.as_slice()),
        let var_types = filter_and_build_multi_var_type_map(&all_var_types, &vars_used),
        addr_to_func_ident(addr, func_ident),
        let resolved_sig = resolve_signature(&sig),
        let dst_ident = if resolved_sig.sig_res == XType::Xvoid { None } else { dst.clone().map(ident_from_reg) },
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Evar(*func_ident, func_ty.clone()),
        let raw_args = clight_exprs_from_csharp_with_multi_types(args.as_slice(), &var_types),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let stmt = ClightStmt::Scall(dst_ident, func_expr, call_args);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Scall(dst, sig, Either::Right(Either::Left(addr)), args)),
        !addr_to_func_ident(addr, _),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = extract_vars_from_csharp_exprs(args.as_slice()),
        let var_types = filter_and_build_multi_var_type_map(&all_var_types, &vars_used),
        let func_ident = *addr as Ident,
        let resolved_sig = resolve_signature(&sig),
        let dst_ident = if resolved_sig.sig_res == XType::Xvoid { None } else { dst.clone().map(ident_from_reg) },
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Evar(func_ident, func_ty.clone()),
        let raw_args = clight_exprs_from_csharp_with_multi_types(args.as_slice(), &var_types),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let stmt = ClightStmt::Scall(dst_ident, func_expr, call_args);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Scall(dst, sig, Either::Right(Either::Right(sym)), args)),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = extract_vars_from_csharp_exprs(args.as_slice()),
        let var_types = filter_and_build_multi_var_type_map(&all_var_types, &vars_used),
        let resolved_sig = resolve_signature(&sig),
        let dst_ident = if resolved_sig.sig_res == XType::Xvoid { None } else { dst.clone().map(ident_from_reg) },
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::EvarSymbol(sym.to_string(), func_ty.clone()),
        let raw_args = clight_exprs_from_csharp_with_multi_types(args.as_slice(), &var_types),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let stmt = ClightStmt::Scall(dst_ident, func_expr, call_args);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sbuiltin(dst, name, args, res)),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = extract_vars_from_builtin_args(&args),
        let var_types = filter_and_build_multi_var_type_map(&all_var_types, &vars_used),
        let (effective_dst_init, effective_name_init) = match name.as_str() {
            "__builtin_hlt" => {
                (None, "__builtin_unreachable".to_string())
            }
            _ => {
                let dst_ident = dst
                    .clone()
                    .map(ident_from_reg)
                    .or_else(|| match &res {
                        BuiltinArg::BA(CsharpminorExpr::Evar(reg)) => {
                            Some(ident_from_reg(*reg))
                        }
                        _ => None,
                    });
                (dst_ident, name.clone())
            }
        },
        let effective_args_init = if let Some(dst_reg) = dst {
            args.iter().filter(|arg| match arg {
                 BuiltinArg::BA(CsharpminorExpr::Evar(r)) => r != dst_reg,
                 _ => true
            }).cloned().collect::<Vec<_>>()
        } else {
            args.clone()
        },
        let effective_name = effective_name_init,
        let effective_dst = effective_dst_init,
        let converted_args = clight_builtin_args_with_multi_types(&effective_args_init, &var_types),
        let stmt = ClightStmt::Scall(effective_dst, ClightExpr::EvarSymbol(effective_name, default_void_ptr_type()), converted_args);

    // Flat Scond (not lifted by structuring_pass): convert to Sifthenelse with gotos
    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Scond(cond, exprs, ifso, ifnot)),
        !valid_switch_chain(_, node, _),
        !valid_ternary(_, node, _, _, _, _),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = extract_vars_from_csharp_exprs(exprs.as_slice()),
        let var_types = filter_and_build_multi_var_type_map(&all_var_types, &vars_used),
        let condition_opt = crate::decompile::passes::clight_pass::clight_condition_expr_with_types(&cond, exprs.as_slice(), &var_types),
        if let Some(condition) = condition_opt,
        let then_stmt = ClightStmt::Sgoto(ident_from_node(*ifso)),
        let else_stmt = ClightStmt::Sgoto(ident_from_node(*ifnot)),
        let stmt = ClightStmt::Sifthenelse(condition.clone(), Box::new(then_stmt), Box::new(else_stmt));

    // Compound Sifthenelse (lifted by structuring_pass): recursively convert bodies
    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sifthenelse(cond, args, then_body, else_body)),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        agg func_syms = collect_func_symbols(ident, sym) in ident_to_symbol(ident, sym),
        let vars_used = extract_vars_from_csharp_exprs(args.as_slice()),
        let var_types = filter_and_build_multi_var_type_map(&all_var_types, &vars_used),
        if let Some(condition) = crate::decompile::passes::clight_pass::clight_condition_expr_with_types(&cond, args.as_slice(), &var_types),
        let then_clight = crate::decompile::passes::clight_pass::convert_csharp_stmt_to_clight(then_body, &all_var_types, &func_syms),
        let else_clight = crate::decompile::passes::clight_pass::convert_csharp_stmt_to_clight(else_body, &all_var_types, &func_syms),
        let stmt = ClightStmt::Sifthenelse(condition, Box::new(then_clight), Box::new(else_clight));

    clight_stmt_without_field(head, stmt) <--
        valid_switch_chain(func, head, reg),
        agg cases = collect_switch_cases(val, target) in switch_chain_member(func, head, _, reg, val, target),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let var_types = filter_and_build_multi_var_type_map(&all_var_types, &[ *reg ]),
        let discr = ClightExpr::Etempvar(ident_from_reg(*reg), var_types.get(reg).map(|types| select_type_from_candidates(types, None)).unwrap_or_else(default_int_type)),
        let table = {
             let mut entries = Vec::new();
             for (val, target) in &cases {
                 let goto_stmt = ClightStmt::Sgoto(ident_from_node(*target));
                 entries.push((Some(*val as Z), goto_stmt));
             }
             entries
        },
        let stmt = ClightStmt::Sswitch(discr, table);

    clight_stmt_without_field(branch, stmt) <--
        valid_ternary(func, branch, var, true_expr, false_expr, _merge),
        csharp_stmt(branch, ?CsharpminorStmt::Scond(cond, args, _, _)),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = extract_vars_from_csharp_exprs(&[true_expr.clone(), false_expr.clone()]),
        let var_types = filter_and_build_multi_var_type_map(&all_var_types, &vars_used),
        let condition_opt = crate::decompile::passes::clight_pass::clight_condition_expr_with_types(&cond, args.as_slice(), &var_types),
        if let Some(condition) = condition_opt,
        let true_clight = clight_expr_from_csharp_with_multi_types(&true_expr, &var_types),
        let false_clight = clight_expr_from_csharp_with_multi_types(&false_expr, &var_types),
        let var_ident = ident_from_reg(*var),
        let then_stmt = ClightStmt::Sset(var_ident, true_clight),
        let else_stmt = ClightStmt::Sset(var_ident, false_clight),
        let stmt = ClightStmt::Sifthenelse(condition, Box::new(then_stmt), Box::new(else_stmt));


    clight_stmt_dead_without_field(func, node, stmt) <--
        valid_switch_chain(func, head, _),
        switch_chain_member(func, head, node, _, _, _),
        clight_stmt_without_field(node, stmt),
        if *node != *head; 
        
    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sjumptable(expr, targets)),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]),
        let var_types = filter_and_build_multi_var_type_map(&all_var_types, &vars_used),
        let discr = clight_expr_from_csharp_with_multi_types(&expr, &var_types),
        let table = {
            let mut entries = Vec::new();
            for (idx, target) in targets.iter().enumerate() {
                let goto_stmt = ClightStmt::Sgoto(ident_from_node(*target));
                entries.push((Some(idx as Z), goto_stmt));
            }
            entries
        },
        let stmt = ClightStmt::Sswitch(discr.clone(), table);

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sjump(target)),
        if *node != *target,
        let stmt = ClightStmt::Sgoto(ident_from_node(*target));

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sjump(target)),
        if *node == *target,
        let stmt = ClightStmt::Sskip;

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sreturn(result)),
        agg all_var_types = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty),
        let vars_used = extract_vars_from_csharp_exprs(&[result.clone()]),
        let var_types = filter_and_build_multi_var_type_map(&all_var_types, &vars_used),
        let converted = clight_expr_from_csharp_with_multi_types(&result, &var_types),
        let stmt = ClightStmt::Sreturn(Some(converted.clone()));

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Snop),
        let stmt = ClightStmt::Sskip;

    // Structured control flow leaf variants; compound construction (Sloop, Sifthenelse) is deferred to the select phase.
    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sbreak),
        let stmt = ClightStmt::Sbreak;

    clight_stmt_without_field(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Scontinue),
        let stmt = ClightStmt::Scontinue;

    emit_goto_target(func, *ifso) <--
        csharp_stmt(src, ?CsharpminorStmt::Scond(_, _, ifso, _)),
        instr_in_function(src, func);
    emit_goto_target(func, *ifnot) <--
        csharp_stmt(src, ?CsharpminorStmt::Scond(_, _, _, ifnot)),
        instr_in_function(src, func);
    emit_goto_target(func, *target) <--
        csharp_stmt(src, ?CsharpminorStmt::Sjump(target)),
        instr_in_function(src, func);

    has_csharp_stmt(node) <-- csharp_stmt(node, _);

    clight_stmt_raw(target, stmt) <--
        emit_goto_target(_, target),
        !has_csharp_stmt(target),
        let stmt = ClightStmt::Sskip;


    efield_to_struct(node, base_off, field_off, field_name, chunk) <--
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        if let CsharpminorExpr::Eload(chunk, addr) = expr.clone(),
        if let Some((base_off, field_off)) = extract_struct_field_info(&expr),
        let field_name = generate_field_name(field_off);

    efield_to_struct(node, base_off, field_off, field_name, chunk) <--
        cminor_stmt(node, ?CminorStmt::Sassign(dst, expr)),
        if let Some(csharp_expr) = csharp_expr_from_cminor(expr),
        if let CsharpminorExpr::Eload(chunk, addr) = csharp_expr.clone(),
        if let Some((base_off, field_off)) = extract_struct_field_info(&csharp_expr),
        let field_name = generate_field_name(field_off);

    efield_to_struct(node, base_off, field_off, field_name, chunk) <--
        csharp_stmt(node, ?CsharpminorStmt::Sstore(chunk, addr, value)),
        if let Some((base_off, field_off)) = extract_struct_field_info(&CsharpminorExpr::Eload(chunk.clone(), Box::new(addr.clone()))),
        let field_name = generate_field_name(field_off);

    efield_to_struct(node, base_off, field_off, field_name, chunk) <--
        csharp_stmt(node, ?CsharpminorStmt::Sstore(_, _, value)),
        if let Some((base_off, field_off)) = extract_struct_field_info(&value),
        if let CsharpminorExpr::Eload(chunk, _) = value,
        let field_name = generate_field_name(field_off);

    efield_to_struct(node, base_off, field_off, field_name, chunk) <--
        cminor_stmt(node, ?CminorStmt::Sstore(chunk, addr, args, _src)),
        if let Some(addr_expr) = addressing_to_csharp_expr(addr, args.as_slice()),
        let synthetic_load = CsharpminorExpr::Eload(chunk.clone(), Box::new(addr_expr.clone())),
        if let Some((base_off, field_off)) = extract_struct_field_info(&synthetic_load),
        let field_name = generate_field_name(field_off);

    efield_to_struct(node, base_off, field_off, field_name, chunk) <--
        csharp_stmt(node, ?CsharpminorStmt::Scall(_, _, _, args)),
        for arg in args,
        if let CsharpminorExpr::Eload(chunk, addr) = arg,
        if let Some((base_off, field_off)) = extract_struct_field_info(&CsharpminorExpr::Eload(chunk.clone(), addr.clone())),
        let field_name = generate_field_name(field_off);


    clight_stmt_for_func_raw(addr, node, labeled_stmt) <--
        instr_in_function(node, addr),
        clight_stmt_raw(node, stmt),
        if !matches!(stmt, ClightStmt::Slabel(_, _)),
        let labeled_stmt = ClightStmt::Slabel(ident_from_node(*node), Box::new(stmt.clone()));

    clight_stmt_for_func_raw(addr, node, stmt) <--
        instr_in_function(node, addr),
        clight_stmt_raw(node, stmt),
        if matches!(stmt, ClightStmt::Slabel(_, _));


    clight_var_read(addr, var_id) <--
        clight_stmt_for_func_raw(addr, _, stmt),
        for var_id in extract_var_reads_from_stmt(stmt);

    clight_var_write(addr, var_id) <--
        clight_stmt_for_func_raw(addr, _, stmt),
        for var_id in extract_var_writes_from_stmt(stmt);

    clight_dead_var(addr, var_id) <--
        clight_var_write(addr, var_id),
        !clight_var_read(addr, var_id),
        emit_function(addr, _, _),
        let var_id_u64 = *var_id as u64,
        !emit_function_param(addr, var_id_u64);

    clight_stmt_dead_without_field(addr, node, stmt) <--
        clight_stmt_for_func_raw(addr, node, stmt),
        if let ClightStmt::Sset(id, expr) = &stmt,
        clight_dead_var(addr, id),
        if matches!(expr, ClightExpr::EconstInt(_, _)
                        | ClightExpr::EconstLong(_, _)
                        | ClightExpr::EconstFloat(_, _)
                        | ClightExpr::EconstSingle(_, _)
                        | ClightExpr::Evar(_, _)
                        | ClightExpr::Etempvar(_, _)
                        | ClightExpr::Esizeof(_, _)
                        | ClightExpr::Ealignof(_, _)
                        | ClightExpr::EvarSymbol(_, _));



    emit_clight_stmt_without_field(addr, node, stmt) <--
        clight_stmt_for_func_raw(addr, node, stmt),
        !clight_stmt_dead_without_field(addr, node, stmt);


    eligible_node_for_sseq(node) <--
        clight_stmt_without_field(node, stmt),
        if is_groupable_stmt(stmt);

    linear_succ_sseq(n1, n2) <--
        cminor_succ(n1, n2),
        eligible_node_for_sseq(n1),
        eligible_node_for_sseq(n2),
        code_in_block(n1, b),
        code_in_block(n2, b);

    sseq_has_pred(n2) <-- linear_succ_sseq(_, n2);

    sseq_head(n) <-- eligible_node_for_sseq(n), !sseq_has_pred(n);

    emit_sseq(head, head) <-- sseq_head(head);
    emit_sseq(head, next) <-- emit_sseq(head, curr), linear_succ_sseq(curr, next);


    node_nonempty(node) <--
        emit_clight_stmt_without_field(_, node, stmt),
        if is_nonempty_stmt(stmt);

    valid_next(node) <-- node_nonempty(node);

    clight_succ(src, dst) <--
        cminor_succ(src, dst),
        valid_next(src),
        valid_next(dst);

    clight_succ(src, final_dst) <--
        cminor_succ(src, mid),
        valid_next(src),
        !valid_next(mid),
        clight_succ(mid, final_dst);

    clight_succ(mid, final_dst) <--
        cminor_succ(mid, final_dst),
        !valid_next(mid),
        valid_next(final_dst);

    clight_succ(mid, final_dst) <--
        cminor_succ(mid, next),
        !valid_next(mid),
        !valid_next(next),
        clight_succ(next, final_dst);

    emit_next(src, dst) <-- clight_succ(src, dst);

    #[local] relation has_cminor_stmt(Node);
    has_cminor_stmt(*node) <-- cminor_stmt(node, _);

    clight_succ(src, dst) <--
        next(src, dst),
        valid_next(src),
        valid_next(dst),
        !has_cminor_stmt(src);

    #[local] relation next_clight(Node, Node);
    next_clight(mid, final_dst) <--
        next(mid, final_dst),
        !valid_next(mid),
        valid_next(final_dst);

    next_clight(mid, final_dst) <--
        next(mid, next_mid),
        !valid_next(mid),
        !valid_next(next_mid),
        next_clight(next_mid, final_dst);

    clight_succ(src, final_dst) <--
        next(src, mid),
        valid_next(src),
        !valid_next(mid),
        !has_cminor_stmt(src),
        next_clight(mid, final_dst);

    clight_succ(src, final_dst) <--
        cminor_succ(src, mid),
        valid_next(src),
        !valid_next(mid),
        next_clight(mid, final_dst);


    clight_efield_info(func_addr, node_val, base_offset, field_offset, field_name, chunk) <--
        instr_in_function(node_val, func_addr),
        efield_to_struct(node_val, base_offset, field_offset, field_name, chunk);

    emit_struct_fields(func_addr, base_offset, fields) <--
        clight_efield_info(func_addr, _, base_offset, _, _, _),
        agg fields = collect_unique_struct_fields(field_offset, field_name, chunk) in clight_efield_info(func_addr, _, base_offset, field_offset, field_name, chunk);

    // NOTE: XstructPtr type candidates are emitted by ClightFieldPass using canonical struct IDs; emitting here would use register-based IDs causing "no member named" errors.


}

pub struct ClightPass;

impl IRPass for ClightPass {
    fn name(&self) -> &'static str { "clight" }

    fn run(&self, db: &mut DecompileDB) {
        run_pass!(db, ClightPassProgram);
    }

    declare_io_from!(ClightPassProgram);
}

pub struct ClightFieldPass;

impl IRPass for ClightFieldPass {
    fn name(&self) -> &'static str { "clight_field" }

    fn run(&self, db: &mut DecompileDB) {
        rewrite_clight_stmts_with_struct_fields(db);
    }

    fn inputs(&self) -> &'static [&'static str] {
        &["emit_struct_fields", "instr_in_function", "clight_stmt_without_field", "emit_clight_stmt_without_field", "clight_stmt_dead_without_field", "mach_imm_stack_init"]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &["clight_stmt", "emit_clight_stmt", "clight_stmt_dead"]
    }
}


pub type VarTypeMap = HashMap<RTLReg, ClightType>;
pub type MultiVarTypeMap = HashMap<RTLReg, Vec<ClightType>>;

pub(crate) fn is_nonempty_stmt(stmt: &ClightStmt) -> bool {
    match stmt {
        ClightStmt::Sskip => false,
        ClightStmt::Slabel(_, inner) => is_nonempty_stmt(inner),
        ClightStmt::Ssequence(stmts) => stmts.iter().any(is_nonempty_stmt),
        ClightStmt::Sloop(a, b) => is_nonempty_stmt(a) || is_nonempty_stmt(b),
        ClightStmt::Sifthenelse(_, t, e) => is_nonempty_stmt(t) || is_nonempty_stmt(e),
        ClightStmt::Sswitch(_, cases) => cases.iter().any(|(_, s)| is_nonempty_stmt(s)),
        _ => true,
    }
}

pub(crate) fn is_groupable_stmt(stmt: &ClightStmt) -> bool {
    matches!(
        stmt,
        ClightStmt::Sset(_, _)
            | ClightStmt::Sassign(_, _)
            | ClightStmt::Scall(_, _, _)
            | ClightStmt::Sbuiltin(_, _, _, _)
    )
}

pub fn collect_switch_cases<'a>(
    inp: impl Iterator<Item = (&'a i64, &'a Node)>,
) -> impl Iterator<Item = Vec<(i64, Node)>> {
    let mut pairs: Vec<(i64, Node)> = inp
        .map(|(val, target)| (*val, *target))
        .filter(|(val, target)| !(*val == i64::MIN && *target == 0))
        .collect();
    // Sort by full tuple so dedup_by_key picks the smallest target when a val has duplicates.
    pairs.sort();
    pairs.dedup_by_key(|(val, _)| *val);
    std::iter::once(pairs)
}


pub(crate) fn refine_indirect_call_signature(
    crude_sig: &Signature,
    args: &[CsharpminorExpr],
    all_var_types: &[(RTLReg, XType)],
    dst: &Option<RTLReg>,
) -> Signature {
    let refined_args: Vec<XType> = args
        .iter()
        .enumerate()
        .map(|(i, expr)| {
            if let CsharpminorExpr::Evar(reg) = expr {
                best_xtype_for_reg(reg, all_var_types)
                    .unwrap_or_else(|| {
                        crude_sig.sig_args.get(i).cloned().unwrap_or(XType::Xlong)
                    })
            } else {
                crude_sig.sig_args.get(i).cloned().unwrap_or(XType::Xlong)
            }
        })
        .collect();

    let refined_ret = if crude_sig.sig_res == XType::Xvoid {
        XType::Xvoid
    } else if let Some(dst_reg) = dst {
        best_xtype_for_reg(dst_reg, all_var_types)
            .unwrap_or(crude_sig.sig_res.clone())
    } else {
        XType::Xvoid
    };

    Signature {
        sig_args: Arc::new(refined_args),
        sig_res: refined_ret,
        sig_cc: crude_sig.sig_cc,
    }
}

fn best_xtype_for_reg(reg: &RTLReg, all_var_types: &[(RTLReg, XType)]) -> Option<XType> {
    all_var_types
        .iter()
        .filter(|(r, _)| r == reg)
        .max_by_key(|(_, xty)| xtype_refine_priority(xty))
        .map(|(_, xty)| xty.clone())
}

pub(crate) fn xtype_refine_priority(xtype: &XType) -> u8 {
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
        XType::Xptr | XType::Xintptr | XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr => 12,
        XType::XstructPtr(_) => 13,
        XType::Xcharptr | XType::Xcharptrptr => 14,
        _ => 0,
    }
}


pub(crate) fn extract_vars_from_csharp_exprs(exprs: &[CsharpminorExpr]) -> Vec<RTLReg> {
    let mut vars = Vec::new();
    for expr in exprs {
        extract_vars_from_csharp_expr(expr, &mut vars);
    }
    vars
}

pub(crate) fn extract_vars_from_builtin_args(args: &[BuiltinArg<CsharpminorExpr>]) -> Vec<RTLReg> {
    let mut vars = Vec::new();
    for arg in args {
        match arg {
            BuiltinArg::BA(expr) => extract_vars_from_csharp_expr(expr, &mut vars),
            BuiltinArg::BASplitLong(lo, hi) | BuiltinArg::BAAddPtr(lo, hi) => {
                 if let BuiltinArg::BA(lo_expr) = lo.as_ref() {
                    extract_vars_from_csharp_expr(lo_expr, &mut vars);
                 }
                 if let BuiltinArg::BA(hi_expr) = hi.as_ref() {
                    extract_vars_from_csharp_expr(hi_expr, &mut vars);
                 }
            }
            _ => {}
        }
    }
    vars
}

pub(crate) fn default_void_ptr_type() -> ClightType {
    pointer_to(ClightType::Tvoid)
}

fn extract_vars_from_csharp_expr(expr: &CsharpminorExpr, vars: &mut Vec<RTLReg>) {
    match expr {
        CsharpminorExpr::Evar(v) => {
            if !vars.contains(v) {
                vars.push(*v);
            }
        }
        CsharpminorExpr::Ebinop(_, left, right) => {
            extract_vars_from_csharp_expr(left, vars);
            extract_vars_from_csharp_expr(right, vars);
        }
        CsharpminorExpr::Eunop(_, arg) => extract_vars_from_csharp_expr(arg, vars),
        CsharpminorExpr::Eload(_, addr) => extract_vars_from_csharp_expr(addr, vars),
        CsharpminorExpr::Eaddrof(_) | CsharpminorExpr::Econst(_) => {}
        CsharpminorExpr::Econdition(cond, true_val, false_val) => {
            extract_vars_from_csharp_expr(cond, vars);
            extract_vars_from_csharp_expr(true_val, vars);
            extract_vars_from_csharp_expr(false_val, vars);
        }
    }
}

pub(crate) fn extract_vars_from_cminor_exprs(exprs: &[CminorExpr]) -> Vec<RTLReg> {
    let mut vars = Vec::new();
    for expr in exprs {
        extract_vars_from_cminor_expr(expr, &mut vars);
    }
    vars
}

fn extract_vars_from_cminor_expr(expr: &CminorExpr, vars: &mut Vec<RTLReg>) {
    match expr {
        CminorExpr::Evar(v) | CminorExpr::Eunop(_, v) => {
            if !vars.contains(v) {
                vars.push(*v);
            }
        }
        CminorExpr::Ebinop(_, left, right) => {
            if !vars.contains(left) {
                vars.push(*left);
            }
            if !vars.contains(right) {
                vars.push(*right);
            }
        }
        CminorExpr::Eop(_, args)
        | CminorExpr::Eload(_, _, args)
        | CminorExpr::Eexternal(_, _, args) => {
            for arg in args.iter() {
                if !vars.contains(arg) {
                    vars.push(*arg);
                }
            }
        }
        CminorExpr::Econst(_) => {}
    }
}

pub(crate) fn collect_all_var_types<'a>(
    input: impl Iterator<Item = (&'a RTLReg, &'a XType)>,
) -> impl Iterator<Item = Vec<(RTLReg, XType)>> {
    let mut pairs: Vec<(RTLReg, XType)> = input.map(|(reg, xty)| (*reg, xty.clone())).collect();
    pairs.sort();
    std::iter::once(pairs)
}

pub(crate) fn collect_func_symbols<'a>(
    input: impl Iterator<Item = (&'a Ident, &'a Symbol)>,
) -> impl Iterator<Item = Vec<(Ident, Symbol)>> {
    let mut pairs: Vec<(Ident, Symbol)> = input.map(|(id, sym)| (*id, sym.clone())).collect();
    // ident_to_symbol is multi-valued; sort so downstream `.find()` picks a deterministic symbol.
    pairs.sort();
    std::iter::once(pairs)
}

/// Aggregator: collect all (base_off, field_off, field_name, chunk) tuples into a FieldInfo.
pub(crate) fn collect_all_field_info<'a>(
    input: impl Iterator<Item = (&'a i64, &'a i64, &'a Ident, &'a MemoryChunk)>,
) -> impl Iterator<Item = FieldInfo> {
    // Sort so or_insert's first-wins is deterministic on duplicate (base_off, field_off) keys.
    let mut tuples: Vec<(i64, i64, Ident, MemoryChunk)> = input
        .map(|(b, f, n, c)| (*b, *f, *n, c.clone()))
        .collect();
    tuples.sort();
    let mut fi = FieldInfo::new();
    for (base_off, field_off, field_name, chunk) in tuples {
        fi.entry((base_off, field_off))
            .or_insert((field_name, chunk));
    }
    std::iter::once(fi)
}


pub(crate) fn filter_and_build_var_type_map(
    all_pairs: &[(RTLReg, XType)],
    vars_used: &[RTLReg],
) -> VarTypeMap {
    let mut map = VarTypeMap::new();
    for (reg, xty) in all_pairs {
        if vars_used.contains(reg) {
            let new_ty = clight_type_from_xtype(xty);
            map.entry(*reg)
                .and_modify(|existing| {
                    *existing =
                        merge_clight_types(existing, &new_ty)
                })
                .or_insert(new_ty);
        }
    }
    map
}

pub(crate) fn filter_and_build_multi_var_type_map(
    all_pairs: &[(RTLReg, XType)],
    vars_used: &[RTLReg],
) -> MultiVarTypeMap {
    let mut map = MultiVarTypeMap::new();
    for (reg, xty) in all_pairs {
        if vars_used.contains(reg) {
            let new_ty = clight_type_from_xtype(xty);
            let types = map.entry(*reg).or_default();
            if !types.contains(&new_ty) {
                types.push(new_ty);
            }
        }
    }
    map
}

/// Returns 1 or 2 MultiVarTypeMaps, splitting pointer vs integer preferences when cross-class candidates exist.
pub(crate) fn build_var_type_map_variants(
    all_pairs: &[(RTLReg, XType)],
    vars_used: &[RTLReg],
) -> Vec<MultiVarTypeMap> {
    let base = filter_and_build_multi_var_type_map(all_pairs, vars_used);

    // Check if any variable has cross-class candidates (pointer AND non-pointer)
    let has_conflict = base.values().any(|types| {
        let has_ptr = types.iter().any(|t| is_pointer_type(t));
        let has_non_ptr = types.iter().any(|t| !is_pointer_type(t) && !matches!(t, ClightType::Tfloat(_, _)));
        has_ptr && has_non_ptr
    });

    if !has_conflict {
        return vec![base];
    }

    // Build pointer-preferred variant: for conflicted vars, keep only pointer types
    let mut ptr_preferred = MultiVarTypeMap::new();
    let mut int_preferred = MultiVarTypeMap::new();
    for (reg, types) in &base {
        let has_ptr = types.iter().any(|t| is_pointer_type(t));
        let has_non_ptr = types.iter().any(|t| !is_pointer_type(t) && !matches!(t, ClightType::Tfloat(_, _)));
        if has_ptr && has_non_ptr {
            // Conflicted: split
            let ptr_types: Vec<_> = types.iter().filter(|t| is_pointer_type(t)).cloned().collect();
            let int_types: Vec<_> = types.iter().filter(|t| !is_pointer_type(t)).cloned().collect();
            if !ptr_types.is_empty() {
                ptr_preferred.insert(*reg, ptr_types);
            }
            if !int_types.is_empty() {
                int_preferred.insert(*reg, int_types);
            } else {
                int_preferred.insert(*reg, types.clone());
            }
        } else {
            ptr_preferred.insert(*reg, types.clone());
            int_preferred.insert(*reg, types.clone());
        }
    }

    vec![ptr_preferred, int_preferred]
}

/// Select the best type from multiple candidates, preferring hint-matching candidates and falling back to merge_clight_types.
pub(crate) fn select_type_from_candidates(
    types: &[ClightType],
    hint: Option<&ClightType>,
) -> ClightType {
    if types.is_empty() {
        return hint.cloned().unwrap_or_else(default_int_type);
    }
    if types.len() == 1 {
        return types[0].clone();
    }

    // If we have a hint, find the best matching candidate
    if let Some(hint_ty) = hint {
        let hint_is_ptr = is_pointer_type(hint_ty);
        let hint_is_float = matches!(hint_ty, ClightType::Tfloat(_, _));

        // Exact match
        if let Some(exact) = types.iter().find(|t| *t == hint_ty) {
            return exact.clone();
        }

        // Same class match (pointer hint -> any pointer candidate, float hint -> any float)
        if hint_is_ptr {
            if let Some(ptr_ty) = types.iter().find(|t| is_pointer_type(t)) {
                return ptr_ty.clone();
            }
        }
        if hint_is_float {
            if let Some(float_ty) = types.iter().find(|t| matches!(t, ClightType::Tfloat(_, _))) {
                return float_ty.clone();
            }
        }

        // Integer hint -> prefer non-pointer non-float
        if !hint_is_ptr && !hint_is_float {
            if let Some(int_ty) = types.iter().find(|t| !is_pointer_type(t) && !matches!(t, ClightType::Tfloat(_, _))) {
                return int_ty.clone();
            }
        }
    }

    // No hint: prefer non-pointer non-float (integer is safer for arithmetic contexts)
    if let Some(int_ty) = types.iter().find(|t| !is_pointer_type(t) && !matches!(t, ClightType::Tfloat(_, _))) {
        return int_ty.clone();
    }

    // Fall back to merge
    let mut result = types[0].clone();
    for ty in &types[1..] {
        result = merge_clight_types(&result, ty);
    }
    result
}

// Recursively convert a CsharpminorStmt tree to a ClightStmt for nested structured bodies.
pub(crate) fn convert_csharp_stmt_to_clight(
    stmt: &CsharpminorStmt,
    all_var_type_pairs: &[(RTLReg, XType)],
    func_symbols: &[(Ident, Symbol)],
) -> ClightStmt {
    match stmt {
        CsharpminorStmt::Sset(dst, expr) => {
            let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]);
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            let out_expr = clight_expr_from_csharp_with_multi_types(expr, &var_types);
            let dst_ident = ident_from_reg(*dst);
            ClightStmt::Sset(dst_ident, out_expr)
        }
        CsharpminorStmt::Sstore(chunk, addr, value) => {
            let vars_used = extract_vars_from_csharp_exprs(&[addr.clone(), value.clone()]);
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            let addr_expr = clight_expr_from_csharp_with_multi_types(addr, &var_types);
            let value_expr = clight_expr_from_csharp_with_multi_types(value, &var_types);
            let deref = ClightExpr::Ederef(Box::new(addr_expr), clight_type_from_chunk(chunk));
            ClightStmt::Sassign(deref, value_expr)
        }
        CsharpminorStmt::Scall(dst, _sig, callee, args) => {
            let callee_expr = match callee {
                Either::Right(Either::Right(sym)) => {
                    ClightExpr::EvarSymbol(sym.to_string(), default_void_ptr_type())
                }
                Either::Right(Either::Left(addr)) => {
                    let ident = *addr as Ident;
                    let name = func_symbols.iter()
                        .find(|(id, _)| *id == ident)
                        .map(|(_, sym)| sym.to_string())
                        .unwrap_or_else(|| format!("sub_{:x}", addr));
                    ClightExpr::EvarSymbol(name, default_void_ptr_type())
                }
                Either::Left(expr) => {
                    let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]);
                    let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
                    clight_expr_from_csharp_with_multi_types(expr, &var_types)
                }
            };
            let vars_used = extract_vars_from_csharp_exprs(args.as_slice());
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            let converted_args: Vec<ClightExpr> = args
                .iter()
                .map(|a| clight_expr_from_csharp_with_multi_types(a, &var_types))
                .collect();
            let dst_ident = dst.map(|r| ident_from_reg(r));
            ClightStmt::Scall(dst_ident, callee_expr, converted_args)
        }
        CsharpminorStmt::Scond(cond, args, ifso, ifnot) => {
            let vars_used = extract_vars_from_csharp_exprs(args.as_slice());
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            if let Some(condition) = clight_condition_expr_with_types(cond, args.as_slice(), &var_types) {
                let then_stmt = ClightStmt::Sgoto(ident_from_node(*ifso));
                let else_stmt = ClightStmt::Sgoto(ident_from_node(*ifnot));
                ClightStmt::Sifthenelse(condition, Box::new(then_stmt), Box::new(else_stmt))
            } else {
                ClightStmt::Sskip
            }
        }
        CsharpminorStmt::Sjump(target) => {
            if stmt == &CsharpminorStmt::Sjump(*target) && *target != 0 {
                ClightStmt::Sgoto(ident_from_node(*target))
            } else {
                ClightStmt::Sskip
            }
        }
        CsharpminorStmt::Sreturn(result) => {
            let vars_used = extract_vars_from_csharp_exprs(&[result.clone()]);
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            let converted = clight_expr_from_csharp_with_multi_types(result, &var_types);
            ClightStmt::Sreturn(Some(converted))
        }
        CsharpminorStmt::Sifthenelse(cond, args, then_body, else_body) => {
            let vars_used = extract_vars_from_csharp_exprs(args.as_slice());
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            if let Some(condition) = clight_condition_expr_with_types(cond, args.as_slice(), &var_types) {
                let then_clight = convert_csharp_stmt_to_clight(then_body, all_var_type_pairs, func_symbols);
                let else_clight = convert_csharp_stmt_to_clight(else_body, all_var_type_pairs, func_symbols);
                ClightStmt::Sifthenelse(condition, Box::new(then_clight), Box::new(else_clight))
            } else {
                ClightStmt::Sskip
            }
        }
        CsharpminorStmt::Sloop(body) => {
            let body_clight = convert_csharp_stmt_to_clight(body, all_var_type_pairs, func_symbols);
            ClightStmt::Sloop(Box::new(body_clight), Box::new(ClightStmt::Sskip))
        }
        CsharpminorStmt::Sbreak => ClightStmt::Sbreak,
        CsharpminorStmt::Scontinue => ClightStmt::Scontinue,
        CsharpminorStmt::Sseq(stmts) => {
            // Detect structuring-pass Sseq([Sjumptable(expr, targets), case_body_0..N]) and build Sswitch with inline case bodies.
            if let Some(CsharpminorStmt::Sjumptable(expr, targets)) = stmts.first() {
                if stmts.len() == 1 + targets.len() {
                    let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]);
                    let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
                    let discr = clight_expr_from_csharp_with_multi_types(expr, &var_types);
                    let table: ClightLabeledStatements = stmts[1..]
                        .iter()
                        .enumerate()
                        .map(|(idx, case_body)| {
                            let body_clight = convert_csharp_stmt_to_clight(case_body, all_var_type_pairs, func_symbols);
                            (Some(idx as Z), body_clight)
                        })
                        .collect();
                    return ClightStmt::Sswitch(discr, table);
                }
            }
            let clight_stmts: Vec<ClightStmt> = stmts
                .iter()
                .map(|s| convert_csharp_stmt_to_clight(s, all_var_type_pairs, func_symbols))
                .collect();
            ClightStmt::Ssequence(clight_stmts)
        }
        CsharpminorStmt::Snop => ClightStmt::Sskip,
        CsharpminorStmt::Stailcall(_, callee, args) => {
            // Convert tailcall to regular call + return for the recursive converter
            let callee_expr = match callee {
                Either::Right(Either::Right(sym)) => {
                    ClightExpr::EvarSymbol(sym.to_string(), default_void_ptr_type())
                }
                Either::Right(Either::Left(addr)) => {
                    let ident = *addr as Ident;
                    let name = func_symbols.iter()
                        .find(|(id, _)| *id == ident)
                        .map(|(_, sym)| sym.to_string())
                        .unwrap_or_else(|| format!("sub_{:x}", addr));
                    ClightExpr::EvarSymbol(name, default_void_ptr_type())
                }
                Either::Left(expr) => {
                    let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]);
                    let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
                    clight_expr_from_csharp_with_multi_types(expr, &var_types)
                }
            };
            let vars_used = extract_vars_from_csharp_exprs(args.as_slice());
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            let converted_args: Vec<ClightExpr> = args
                .iter()
                .map(|a| clight_expr_from_csharp_with_multi_types(a, &var_types))
                .collect();
            ClightStmt::Scall(None, callee_expr, converted_args)
        }
        CsharpminorStmt::Sbuiltin(dst, name, args, res) => {
            let dst_ident = dst
                .as_ref()
                .map(|r| ident_from_reg(*r))
                .or_else(|| match res {
                    BuiltinArg::BA(CsharpminorExpr::Evar(reg)) => Some(ident_from_reg(*reg)),
                    _ => None,
                });
            let effective_name = if name == "__builtin_hlt" {
                "__builtin_unreachable".to_string()
            } else {
                name.clone()
            };
            let effective_args: Vec<_> = if let Some(dst_reg) = dst {
                args.iter().filter(|arg| match arg {
                    BuiltinArg::BA(CsharpminorExpr::Evar(r)) => r != dst_reg,
                    _ => true,
                }).cloned().collect()
            } else {
                args.clone()
            };
            let vars_used = extract_vars_from_builtin_args(&effective_args);
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            let converted_args = clight_builtin_args_with_multi_types(&effective_args, &var_types);
            ClightStmt::Scall(dst_ident, ClightExpr::EvarSymbol(effective_name, default_void_ptr_type()), converted_args)
        }
        CsharpminorStmt::Scond(cond, args, ifso, ifnot) => {
            let vars_used = extract_vars_from_csharp_exprs(args.as_slice());
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            if let Some(condition) = clight_condition_expr_with_types(cond, args.as_slice(), &var_types) {
                let then_stmt = ClightStmt::Sgoto(ident_from_node(*ifso));
                let else_stmt = ClightStmt::Sgoto(ident_from_node(*ifnot));
                ClightStmt::Sifthenelse(condition, Box::new(then_stmt), Box::new(else_stmt))
            } else {
                ClightStmt::Sskip
            }
        }
        CsharpminorStmt::Sjumptable(expr, targets) => {
            let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]);
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            let discr = clight_expr_from_csharp_with_multi_types(expr, &var_types);
            let table: ClightLabeledStatements = targets
                .iter()
                .enumerate()
                .map(|(idx, target)| {
                    let goto_stmt = ClightStmt::Sgoto(ident_from_node(*target));
                    (Some(idx as Z), goto_stmt)
                })
                .collect();
            ClightStmt::Sswitch(discr, table)
        }
        CsharpminorStmt::Sloophead(_) => ClightStmt::Sskip,
    }
}

pub(crate) fn is_trivial_cminor_stmt(stmt: &CminorStmt) -> bool {
    matches!(stmt, CminorStmt::Snop | CminorStmt::Sjump(_))
}

pub(crate) fn is_modifying_binop(op: &CminorBinop) -> bool {
    matches!(
        op,
        CminorBinop::Oadd
            | CminorBinop::Osub
            | CminorBinop::Omul
            | CminorBinop::Odiv
            | CminorBinop::Odivu
            | CminorBinop::Omod
            | CminorBinop::Omodu
            | CminorBinop::Oand
            | CminorBinop::Oor
            | CminorBinop::Oxor
            | CminorBinop::Oshl
            | CminorBinop::Oshr
            | CminorBinop::Oshru
            | CminorBinop::Oaddl
            | CminorBinop::Osubl
            | CminorBinop::Omull
            | CminorBinop::Odivl
            | CminorBinop::Odivlu
            | CminorBinop::Omodl
            | CminorBinop::Omodlu
            | CminorBinop::Oandl
            | CminorBinop::Oorl
            | CminorBinop::Oxorl
            | CminorBinop::Oshll
            | CminorBinop::Oshrl
            | CminorBinop::Oshrlu
            | CminorBinop::Omulhs
            | CminorBinop::Omulhu
            | CminorBinop::Omullhs
            | CminorBinop::Omullhu
    )
}

fn is_long_cminor_binop(op: &CminorBinop) -> bool {
    matches!(
        op,
        CminorBinop::Oaddl
            | CminorBinop::Osubl
            | CminorBinop::Omull
            | CminorBinop::Odivl
            | CminorBinop::Odivlu
            | CminorBinop::Omodl
            | CminorBinop::Omodlu
            | CminorBinop::Oandl
            | CminorBinop::Oorl
            | CminorBinop::Oxorl
            | CminorBinop::Oshll
            | CminorBinop::Oshrl
            | CminorBinop::Oshrlu
            | CminorBinop::Omullhs
            | CminorBinop::Omullhu
            | CminorBinop::Ocmpl(_)
            | CminorBinop::Ocmplu(_)
    )
}

pub(crate) fn is_increment_decrement_op(op: &CminorBinop) -> bool {
    matches!(
        op,
        CminorBinop::Oadd | CminorBinop::Osub | CminorBinop::Oaddl | CminorBinop::Osubl
    )
}

pub(crate) fn extract_self_modifying_reg(dst: &RTLReg, expr: &CminorExpr) -> Option<RTLReg> {
    match expr {
        CminorExpr::Ebinop(op, arg1, arg2) if is_modifying_binop(op) => {
            if arg1 == dst || arg2 == dst {
                Some(*dst)
            } else {
                None
            }
        }
        CminorExpr::Eop(_, args) if args.contains(dst) => Some(*dst),
        _ => None,
    }
}

pub(crate) fn invert_comparison(comp: &Comparison) -> Comparison {
    match comp {
        Comparison::Ceq => Comparison::Cne,
        Comparison::Cne => Comparison::Ceq,
        Comparison::Clt => Comparison::Cge,
        Comparison::Cle => Comparison::Cgt,
        Comparison::Cgt => Comparison::Cle,
        Comparison::Cge => Comparison::Clt,
        Comparison::Unknown => Comparison::Unknown,
    }
}

pub(crate) fn invert_condition(cond: &Condition) -> Condition {
    match cond {
        Condition::Ccomp(c) => Condition::Ccomp(invert_comparison(c)),
        Condition::Ccompu(c) => Condition::Ccompu(invert_comparison(c)),
        Condition::Ccompl(c) => Condition::Ccompl(invert_comparison(c)),
        Condition::Ccomplu(c) => Condition::Ccomplu(invert_comparison(c)),
        Condition::Ccompf(c) => Condition::Ccompf(invert_comparison(c)),
        Condition::Ccompfs(c) => Condition::Ccompfs(invert_comparison(c)),
        Condition::Ccompimm(c, imm) => Condition::Ccompimm(invert_comparison(c), *imm),
        Condition::Ccompuimm(c, imm) => Condition::Ccompuimm(invert_comparison(c), *imm),
        Condition::Ccomplimm(c, imm) => Condition::Ccomplimm(invert_comparison(c), *imm),
        Condition::Ccompluimm(c, imm) => Condition::Ccompluimm(invert_comparison(c), *imm),
        Condition::Cmaskzero(m) => Condition::Cmasknotzero(*m),
        Condition::Cmasknotzero(m) => Condition::Cmaskzero(*m),
        Condition::Cnotcompf(c) => Condition::Ccompf(*c),
        Condition::Cnotcompfs(c) => Condition::Ccompfs(*c),
    }
}


pub type FieldInfo = HashMap<(i64, i64), (Ident, MemoryChunk)>;


pub(crate) fn generate_field_name(offset: i64) -> Ident {
    offset as Ident
}

fn extract_field_access(
    addr: &CsharpminorExpr,
    chunk: &MemoryChunk,
    field_info: &FieldInfo,
) -> Option<(ClightExpr, Ident, ClightType)> {
    let synthetic_load = CsharpminorExpr::Eload(chunk.clone(), Box::new(addr.clone()));
    let (base_off, field_off) = extract_struct_field_info(&synthetic_load)?;

    let (field_name, _) = field_info.get(&(base_off, field_off))?;

    let base_expr = extract_base_expr_for_field(addr, field_off)?;

    let field_ty = clight_type_from_chunk(chunk);

    let struct_id = base_off.unsigned_abs() as Ident;
    let struct_ty = ClightType::Tstruct(struct_id, default_attr());
    let struct_ptr_ty = pointer_to(struct_ty.clone());

    let typed_base = cast_expr_to_type(base_expr, struct_ptr_ty);
    // Efield expects a struct lvalue, so dereference the pointer: ptr->field == (*ptr).field
    let deref_base = ClightExpr::Ederef(Box::new(typed_base), struct_ty);

    Some((deref_base, *field_name, field_ty))
}

fn extract_base_expr_for_field(addr: &CsharpminorExpr, _field_offset: i64) -> Option<ClightExpr> {
    let (flattened, _accumulated) = flatten_binop_chain(addr);

    match flattened.as_ref() {
        CsharpminorExpr::Ebinop(op, base, _k)
            if matches!(
                op,
                CminorBinop::Oadd | CminorBinop::Oaddl | CminorBinop::Osub | CminorBinop::Osubl
            ) =>
        {
            Some(clight_expr_from_csharp_inner(
                base,
                &HashMap::new(),
                &HashMap::new(),
                None,
            ))
        }
        CsharpminorExpr::Evar(reg) => Some(ClightExpr::Etempvar(
            ident_from_reg(*reg),
            pointer_to(default_int_type()),
        )),
        CsharpminorExpr::Econst(Constant::Oaddrstack(ofs)) => {
            Some(ClightExpr::EconstLong(*ofs, default_long_type()))
        }
        CsharpminorExpr::Econst(Constant::Ointconst(v)) => Some(ClightExpr::EconstInt(
            *v as i32,
            pointer_to(default_int_type()),
        )),
        CsharpminorExpr::Econst(Constant::Olongconst(v)) => {
            Some(ClightExpr::EconstLong(*v, pointer_to(default_int_type())))
        }
        _ => None,
    }
}

pub(crate) fn extract_constant_offset(expr: &CsharpminorExpr) -> Option<i64> {
    match expr {
        CsharpminorExpr::Econst(cst) => match cst {
            Constant::Ointconst(v) => Some(*v),
            Constant::Olongconst(v) => Some(*v),
            _ => None,
        },
        _ => None,
    }
}

fn flatten_binop_chain(expr: &CsharpminorExpr) -> (Box<CsharpminorExpr>, i64) {
    match expr {
        CsharpminorExpr::Ebinop(op, base, k)
            if matches!(
                op,
                CminorBinop::Oadd | CminorBinop::Oaddl | CminorBinop::Osub | CminorBinop::Osubl
            ) =>
        {
            if let Some(delta) = extract_constant_offset(k) {
                let offset = if matches!(op, CminorBinop::Osub | CminorBinop::Osubl) {
                    -delta
                } else {
                    delta
                };

                let (flattened_base, base_offset) = flatten_binop_chain(base);
                (flattened_base, base_offset + offset)
            } else {
                (Box::new(expr.clone()), 0)
            }
        }
        _ => (Box::new(expr.clone()), 0),
    }
}

fn is_valid_field_offset(offset: i64, chunk: &MemoryChunk) -> bool {
    const MAX_FIELD_SPAN: i64 = 2048;

    if offset < 0 || offset >= MAX_FIELD_SPAN {
        return false;
    }

    match chunk {
        MemoryChunk::MBool | MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned => {
            true
        }
        MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned => {
            offset % 2 == 0
        }
        MemoryChunk::MInt32 | MemoryChunk::MFloat32 => {
            offset % 4 == 0
        }
        MemoryChunk::MInt64 | MemoryChunk::MFloat64 => {
            offset % 4 == 0
        }
        MemoryChunk::MAny32 | MemoryChunk::MAny64 | MemoryChunk::Unknown => {
            offset % 4 == 0
        }
    }
}

pub fn extract_struct_field_info(expr: &CsharpminorExpr) -> Option<(i64, i64)> {
    fn abs_i64(x: i64) -> i64 {
        if x < 0 {
            -x
        } else {
            x
        }
    }
    match expr {
        CsharpminorExpr::Eload(chunk, addr) => {
            let (flattened_addr, accumulated_offset) = flatten_binop_chain(addr);

            match flattened_addr.as_ref() {
                CsharpminorExpr::Ebinop(op, base, k)
                    if matches!(
                        op,
                        CminorBinop::Oadd
                            | CminorBinop::Oaddl
                            | CminorBinop::Osub
                            | CminorBinop::Osubl
                    ) && extract_constant_offset(k).is_some() =>
                {
                    let delta = extract_constant_offset(k).unwrap();
                    let offset = if matches!(op, CminorBinop::Osub | CminorBinop::Osubl) {
                        -delta
                    } else {
                        delta
                    };

                    match base.as_ref() {
                        CsharpminorExpr::Econst(Constant::Ointconst(v)) => {
                            let field = abs_i64(offset);
                            if is_valid_field_offset(field, chunk) {
                                return Some((*v, field));
                            }
                        }
                        CsharpminorExpr::Econst(Constant::Olongconst(v)) => {
                            let field = abs_i64(offset);
                            if is_valid_field_offset(field, chunk) {
                                return Some((*v, field));
                            }
                        }
                        CsharpminorExpr::Econst(Constant::Oaddrstack(base_ofs)) => {
                            let abs_base = abs_i64((*base_ofs) as i64);
                            let base_bucket = (abs_base / 64) * 64;
                            let field = abs_i64((abs_base - base_bucket) + offset);
                            if is_valid_field_offset(field, chunk) {
                                return Some((base_bucket, field));
                            }
                        }
                        CsharpminorExpr::Evar(reg) => {
                            let base_key = (*reg) as i64;
                            let field = abs_i64(offset);
                            if is_valid_field_offset(field, chunk) {
                                return Some((base_key, field));
                            }
                        }
                        _ => {
                            let field = abs_i64(offset);
                            if is_valid_field_offset(field, chunk) {
                                return Some((0, field));
                            }
                        }
                    }
                }
                _ if accumulated_offset != 0 => match flattened_addr.as_ref() {
                    CsharpminorExpr::Econst(Constant::Ointconst(v)) => {
                        let field = abs_i64(accumulated_offset);
                        if is_valid_field_offset(field, chunk) {
                            return Some((*v, field));
                        }
                    }
                    CsharpminorExpr::Econst(Constant::Olongconst(v)) => {
                        let field = abs_i64(accumulated_offset);
                        if is_valid_field_offset(field, chunk) {
                            return Some((*v, field));
                        }
                    }
                    CsharpminorExpr::Econst(Constant::Oaddrstack(base_ofs)) => {
                        let abs_base = abs_i64((*base_ofs) as i64);
                        let base_bucket = (abs_base / 64) * 64;
                        let field = abs_i64((abs_base - base_bucket) + accumulated_offset);
                        if is_valid_field_offset(field, chunk) {
                            return Some((base_bucket, field));
                        }
                    }
                    CsharpminorExpr::Evar(reg) => {
                        let base_key = (*reg) as i64;
                        let field = abs_i64(accumulated_offset);
                        if is_valid_field_offset(field, chunk) {
                            return Some((base_key, field));
                        }
                    }
                    _ => {}
                },
                CsharpminorExpr::Econst(Constant::Oaddrstack(ofs)) => {
                    let abs_ofs = abs_i64((*ofs) as i64);
                    let base_bucket = (abs_ofs / 64) * 64;
                    let field = abs_ofs - base_bucket;
                    if is_valid_field_offset(field, chunk) {
                        return Some((base_bucket, field));
                    }
                }
                _ => {}
            }
            None
        }
        _ => None,
    }
}

fn is_zero_constant(expr: &CsharpminorExpr) -> bool {
    match expr {
        CsharpminorExpr::Econst(c) => match c {
            Constant::Ointconst(0) | Constant::Olongconst(0) => true,
            Constant::Ofloatconst(f) if f.as_f64() == 0.0 => true,
            Constant::Osingleconst(f) if f.as_f32() == 0.0 => true,
            Constant::Oaddrsymbol(0, 0) => true,
            Constant::Oaddrstack(0) => true,
            _ => false,
        },
        _ => false,
    }
}

pub fn op_requires_int_operands(op: &CminorBinop) -> bool {
    matches!(
        op,
        CminorBinop::Oxor
            | CminorBinop::Oxorl
            | CminorBinop::Oand
            | CminorBinop::Oandl
            | CminorBinop::Oor
            | CminorBinop::Oorl
            | CminorBinop::Oshl
            | CminorBinop::Oshll
            | CminorBinop::Oshr
            | CminorBinop::Oshrl
            | CminorBinop::Oshru
            | CminorBinop::Oshrlu
            | CminorBinop::Omul
            | CminorBinop::Omull
            | CminorBinop::Odiv
            | CminorBinop::Odivu
            | CminorBinop::Odivl
            | CminorBinop::Odivlu
            | CminorBinop::Omod
            | CminorBinop::Omodu
            | CminorBinop::Omodl
            | CminorBinop::Omodlu
            | CminorBinop::Omulhs
            | CminorBinop::Omulhu
            | CminorBinop::Omullhs
            | CminorBinop::Omullhu
    )
}

pub fn coerce_ptr_to_long(expr: ClightExpr) -> ClightExpr {
    let ty = clight_expr_type(&expr);
    if is_pointer_type(&ty) {
        ClightExpr::Ecast(Box::new(expr), default_long_type())
    } else {
        expr
    }
}

pub fn clight_binop_from_cminor(op: &CminorBinop) -> Option<ClightBinaryOp> {
    use CminorBinop::*;

    match op {
        Oadd | Oaddf | Oaddfs | Oaddl => Some(ClightBinaryOp::Oadd),
        Osub | Osubf | Osubfs | Osubl => Some(ClightBinaryOp::Osub),
        Omul | Omulf | Omulfs | Omull => Some(ClightBinaryOp::Omul),
        Odiv | Odivu | Odivf | Odivfs | Odivl | Odivlu => Some(ClightBinaryOp::Odiv),
        Omod | Omodu | Omodl | Omodlu => Some(ClightBinaryOp::Omod),
        Omulhs | Omulhu | Omullhs | Omullhu => Some(ClightBinaryOp::Omul),
        Oand | Oandl => Some(ClightBinaryOp::Oand),
        Oor | Oorl => Some(ClightBinaryOp::Oor),
        Oxor | Oxorl => Some(ClightBinaryOp::Oxor),
        Oshl | Oshll => Some(ClightBinaryOp::Oshl),
        Oshr | Oshrl => Some(ClightBinaryOp::Oshr),
        Oshru | Oshrlu => Some(ClightBinaryOp::Oshr),
        Ocmp(cond) => Some(clight_cmp_from_condition(cond)),
        Ocmpu(cond) => Some(clight_cmp_from_condition(cond)),
        Ocmpf(cond) => Some(clight_cmp_from_condition(cond)),
        Ocmpnotf(cond) => Some(clight_cmp_from_condition(cond)),
        Ocmpfs(cond) => Some(clight_cmp_from_condition(cond)),
        Ocmpnotfs(cond) => Some(clight_cmp_from_condition(cond)),
        Ocmpl(cond) => Some(clight_cmp_from_condition(cond)),
        Ocmplu(cond) => Some(clight_cmp_from_condition(cond)),
        _ => None,
    }
}

fn get_inner_type_size(ty: &ClightType) -> Option<i64> {
    match ty {
        ClightType::Tint(ClightIntSize::I8, _, _) => Some(1),
        ClightType::Tint(ClightIntSize::I16, _, _) => Some(2),
        ClightType::Tint(ClightIntSize::I32, _, _) => Some(4),
        ClightType::Tint(ClightIntSize::IBool, _, _) => Some(1),
        ClightType::Tlong(_, _) => Some(8),
        ClightType::Tfloat(ClightFloatSize::F32, _) => Some(4),
        ClightType::Tfloat(ClightFloatSize::F64, _) => Some(8),
        ClightType::Tpointer(_, _) => Some(crate::x86::abi::abi_config().pointer_size as i64),
        ClightType::Tarray(inner, len, _) => get_inner_type_size(inner).map(|s| s * (*len as i64)),
        ClightType::Tfunction(_, _, _) => Some(1),
        ClightType::Tvoid => Some(1),
        _ => None,
    }
}

fn get_const_val(expr: &ClightExpr) -> Option<i64> {
    match expr {
        ClightExpr::EconstInt(v, _) => Some(*v as i64),
        ClightExpr::EconstLong(v, _) => Some(*v),
        _ => None,
    }
}

fn make_const_val(val: i64, orig_ty: &ClightType) -> ClightExpr {
    if matches!(orig_ty, ClightType::Tlong(_, _)) {
        ClightExpr::EconstLong(val, orig_ty.clone())
    } else {
        ClightExpr::EconstInt(val as i32, orig_ty.clone())
    }
}

fn try_unscale_expr(expr: ClightExpr, ptr_ty: &ClightType) -> ClightExpr {
    if let ClightType::Tpointer(inner, _) = ptr_ty {
        if let Some(size) = get_inner_type_size(inner) {
            if size > 1 {
                if let ClightExpr::Ebinop(ClightBinaryOp::Omul, l, r, _) = &expr {
                    if let Some(c) = get_const_val(l) {
                        if c == size {
                            return *r.clone();
                        }
                    }
                    if let Some(c) = get_const_val(r) {
                        if c == size {
                            return *l.clone();
                        }
                    }
                }

                if let Some(c) = get_const_val(&expr) {
                    if c % size == 0 && c != 0 {
                        return make_const_val(c / size, &clight_expr_type(&expr));
                    }
                }
            }
        }
    }
    expr
}

pub fn build_binop_expr(
    op: &CminorBinop,
    lhs_expr: ClightExpr,
    rhs_expr: ClightExpr,
) -> ClightExpr {
    let lhs_ty = clight_expr_type(&lhs_expr);
    let rhs_ty = clight_expr_type(&rhs_expr);

    let (lhs_final, rhs_final) = if op_requires_int_operands(op) {
        (coerce_ptr_to_long(lhs_expr), coerce_ptr_to_long(rhs_expr))
    } else if matches!(op, CminorBinop::Osub | CminorBinop::Osubl)
        && is_integral_type(&lhs_ty)
        && is_pointer_type(&rhs_ty)
    {
        (lhs_expr, coerce_ptr_to_long(rhs_expr))
    } else if is_pointer_type(&lhs_ty) && is_pointer_type(&rhs_ty) {
        match op {
            CminorBinop::Oadd | CminorBinop::Oaddl | CminorBinop::Osub | CminorBinop::Osubl => {
                (coerce_ptr_to_long(lhs_expr), coerce_ptr_to_long(rhs_expr))
            }
            _ => (lhs_expr, rhs_expr),
        }
    } else {
        (lhs_expr, rhs_expr)
    };

    let final_lhs_ty = clight_expr_type(&lhs_final);
    let final_rhs_ty = clight_expr_type(&rhs_final);

    let (lhs_scaled, rhs_scaled) = if matches!(
        op,
        CminorBinop::Oadd | CminorBinop::Oaddl | CminorBinop::Osub | CminorBinop::Osubl
    ) {
        if is_pointer_type(&final_lhs_ty) && is_integral_type(&final_rhs_ty) {
            let rewritten_rhs = try_unscale_expr(rhs_final.clone(), &final_lhs_ty);
            (lhs_final, rewritten_rhs)
        } else if matches!(op, CminorBinop::Oadd | CminorBinop::Oaddl)
            && is_integral_type(&final_lhs_ty)
            && is_pointer_type(&final_rhs_ty)
        {
            let rewritten_lhs = try_unscale_expr(lhs_final.clone(), &final_rhs_ty);
            (rewritten_lhs, rhs_final)
        } else {
            (lhs_final, rhs_final)
        }
    } else {
        (lhs_final, rhs_final)
    };

    let result_ty = match op {
        CminorBinop::Oaddf | CminorBinop::Osubf | CminorBinop::Omulf | CminorBinop::Odivf
        | CminorBinop::Omaxf | CminorBinop::Ominf => {
            default_float_type()
        }
        CminorBinop::Oaddfs | CminorBinop::Osubfs | CminorBinop::Omulfs | CminorBinop::Odivfs => {
            default_single_type()
        }
        CminorBinop::Oaddl
        | CminorBinop::Osubl
        | CminorBinop::Omull
        | CminorBinop::Odivl
        | CminorBinop::Odivlu
        | CminorBinop::Omodl
        | CminorBinop::Omodlu
        | CminorBinop::Oandl
        | CminorBinop::Oorl
        | CminorBinop::Oxorl
        | CminorBinop::Oshll
        | CminorBinop::Oshrl
        | CminorBinop::Oshrlu
        | CminorBinop::Omullhs
        | CminorBinop::Omullhu => default_long_type(),
        CminorBinop::Ocmp(_)
        | CminorBinop::Ocmpu(_)
        | CminorBinop::Ocmpf(_)
        | CminorBinop::Ocmpnotf(_)
        | CminorBinop::Ocmpfs(_)
        | CminorBinop::Ocmpnotfs(_)
        | CminorBinop::Ocmpl(_)
        | CminorBinop::Ocmplu(_) => default_bool_type(),
        CminorBinop::Oadd | CminorBinop::Osub
            if is_pointer_type(&final_lhs_ty) && is_integral_type(&final_rhs_ty) =>
        {
            final_lhs_ty.clone()
        }
        CminorBinop::Oadd if is_integral_type(&final_lhs_ty) && is_pointer_type(&final_rhs_ty) => {
            final_rhs_ty.clone()
        }
        _ => {
            if matches!(final_lhs_ty, ClightType::Tlong(_, _))
                || matches!(final_rhs_ty, ClightType::Tlong(_, _))
            {
                default_long_type()
            } else {
                default_int_type()
            }
        }
    };

    let binop = clight_binop_from_cminor(op).unwrap_or(ClightBinaryOp::Oadd);
    let expr = ClightExpr::Ebinop(binop, Box::new(lhs_scaled), Box::new(rhs_scaled), result_ty.clone());
    // Cnotcompf/Cnotcompfs: wrap in logical NOT to preserve unordered (NaN) semantics
    if matches!(op, CminorBinop::Ocmpnotf(_) | CminorBinop::Ocmpnotfs(_)) {
        ClightExpr::Eunop(ClightUnaryOp::Onotbool, Box::new(expr), result_ty)
    } else {
        expr
    }
}

pub(crate) fn clight_expr_from_csharp(expr: &CsharpminorExpr) -> ClightExpr {
    clight_expr_from_csharp_inner(expr, &HashMap::new(), &HashMap::new(), None)
}

pub(crate) fn clight_expr_from_csharp_with_types(
    expr: &CsharpminorExpr,
    var_types: &VarTypeMap,
) -> ClightExpr {
    // Convert VarTypeMap to MultiVarTypeMap for backward compat
    let multi: MultiVarTypeMap = var_types.iter().map(|(k, v)| (*k, vec![v.clone()])).collect();
    clight_expr_from_csharp_inner(expr, &HashMap::new(), &multi, None)
}

pub(crate) fn clight_expr_from_csharp_with_multi_types(
    expr: &CsharpminorExpr,
    var_types: &MultiVarTypeMap,
) -> ClightExpr {
    clight_expr_from_csharp_inner(expr, &HashMap::new(), var_types, None)
}

pub(crate) fn clight_expr_from_csharp_with_multi_types_and_fields(
    expr: &CsharpminorExpr,
    var_types: &MultiVarTypeMap,
    field_info: &FieldInfo,
) -> ClightExpr {
    clight_expr_from_csharp_inner(expr, field_info, var_types, None)
}

fn clight_expr_from_csharp_inner(
    expr: &CsharpminorExpr,
    field_info: &FieldInfo,
    var_types: &MultiVarTypeMap,
    type_hint: Option<&ClightType>,
) -> ClightExpr {
    match expr {
        CsharpminorExpr::Evar(reg) => {
            let ty = if let Some(types) = var_types.get(reg) {
                select_type_from_candidates(types, type_hint)
            } else {
                type_hint.cloned().unwrap_or_else(default_int_type)
            };
            ClightExpr::Etempvar(ident_from_reg(*reg), ty)
        }

        CsharpminorExpr::Eaddrof(ident) => {
            let inner = ClightExpr::Evar(*ident, default_int_type());

            ClightExpr::Eaddrof(Box::new(inner), pointer_to(default_int_type()))
        }
        CsharpminorExpr::Econst(cst) => match cst {
            Constant::Ointconst(value) => {
                let narrowed =
                    i32::try_from(*value).unwrap_or((*value as u32) as i32);

                ClightExpr::EconstInt(narrowed, default_int_type())
            }
            Constant::Ofloatconst(f) => {
                ClightExpr::EconstFloat(ClightFloat64::from(f.as_f64()), default_float_type())
            }
            Constant::Osingleconst(f) => {
                ClightExpr::EconstSingle(ClightFloat32::from(f.as_f32()), default_single_type())
            }
            Constant::Olongconst(value) => {
                normalize_const_expr(ClightExpr::EconstLong(*value, default_long_type()))
            }
            Constant::Oaddrsymbol(ident, ofs) => {
                if *ident == 0 {
                    let offset_val = *ofs;
                    match i32::try_from(offset_val) {
                        Ok(int_val) => ClightExpr::EconstInt(int_val, default_int_type()),
                        Err(_) => ClightExpr::EconstLong(offset_val, default_long_type()),
                    }
                } else {
                    let base = ClightExpr::Eaddrof(
                        Box::new(ClightExpr::Evar(*ident, default_int_type())),
                        pointer_to(default_int_type()),
                    );
                    if *ofs == 0 {
                        base
                    } else {
                        let offset_expr =
                            normalize_const_expr(ClightExpr::EconstLong(*ofs, default_long_type()));
                        ClightExpr::Ebinop(
                            ClightBinaryOp::Oadd,
                            Box::new(base),
                            Box::new(offset_expr),
                            pointer_to(default_int_type()),
                        )
                    }
                }
            }
            Constant::Oaddrstack(ofs) => {
                let offset_val = *ofs;
                ClightExpr::EconstLong(offset_val, default_long_type())
            }
        },
        CsharpminorExpr::Eunop(op, inner) => {
            let inner_expr = clight_expr_from_csharp_inner(inner, field_info, var_types, None);
            match op {
                CminorUnop::Ocast8unsigned => ClightExpr::Ecast(
                    Box::new(inner_expr),
                    ClightType::Tint(
                        ClightIntSize::I8,
                        ClightSignedness::Unsigned,
                        default_attr(),
                    ),
                ),
                CminorUnop::Ocast8signed => ClightExpr::Ecast(
                    Box::new(inner_expr),
                    ClightType::Tint(ClightIntSize::I8, ClightSignedness::Signed, default_attr()),
                ),
                CminorUnop::Ocast16unsigned => ClightExpr::Ecast(
                    Box::new(inner_expr),
                    ClightType::Tint(
                        ClightIntSize::I16,
                        ClightSignedness::Unsigned,
                        default_attr(),
                    ),
                ),
                CminorUnop::Ocast16signed => ClightExpr::Ecast(
                    Box::new(inner_expr),
                    ClightType::Tint(ClightIntSize::I16, ClightSignedness::Signed, default_attr()),
                ),
                CminorUnop::Ointoffloat | CminorUnop::Ointofsingle => {
                    ClightExpr::Ecast(Box::new(inner_expr), default_int_type())
                }
                CminorUnop::Ofloatofint | CminorUnop::Ofloatofsingle => {
                    ClightExpr::Ecast(Box::new(inner_expr), default_float_type())
                }
                CminorUnop::Olongofint | CminorUnop::Olongofsingle | CminorUnop::Olongoffloat => {
                    ClightExpr::Ecast(Box::new(inner_expr), default_long_type())
                }
                CminorUnop::Osingleoffloat | CminorUnop::Osingleofint | CminorUnop::Osingleofintu
                | CminorUnop::Osingleoflong | CminorUnop::Osingleoflongu => {
                    ClightExpr::Ecast(Box::new(inner_expr), default_single_type())
                }
                CminorUnop::Ofloatoflong | CminorUnop::Ofloatoflongu | CminorUnop::Ofloatofintu => {
                    ClightExpr::Ecast(Box::new(inner_expr), default_float_type())
                }
                CminorUnop::Ointoflong => {
                    ClightExpr::Ecast(Box::new(inner_expr), default_int_type())
                }
                CminorUnop::Olongofintu => {
                    ClightExpr::Ecast(Box::new(inner_expr), default_long_type())
                }
                CminorUnop::Ointuoffloat | CminorUnop::Ointuofsingle => {
                    ClightExpr::Ecast(
                        Box::new(inner_expr),
                        ClightType::Tint(ClightIntSize::I32, ClightSignedness::Unsigned, default_attr()),
                    )
                }
                CminorUnop::Olonguoffloat | CminorUnop::Olonguofsingle => {
                    ClightExpr::Ecast(
                        Box::new(inner_expr),
                        ClightType::Tlong(ClightSignedness::Unsigned, default_attr()),
                    )
                }
                _ => {
                    if let Some(unop) = clight_unop_from_cminor(op) {
                        let coerced_inner = match unop {
                            ClightUnaryOp::Oneg | ClightUnaryOp::Onotint => {
                                coerce_ptr_to_long(inner_expr)
                            }
                            _ => inner_expr,
                        };
                        let result_ty = clight_expr_type(&coerced_inner);

                        ClightExpr::Eunop(unop, Box::new(coerced_inner), result_ty)
                    } else {
                        inner_expr
                    }
                }
            }
        }
        CsharpminorExpr::Ebinop(op, lhs, rhs) => {
            let is_add_or_sub = matches!(op,
                CminorBinop::Oaddl | CminorBinop::Osubl |
                CminorBinop::Oadd | CminorBinop::Osub
            );
            // Propagate pointer hint from parent to LHS (base) and integer hint to RHS (offset) for add/sub
            let (lhs_hint, rhs_hint) = if is_add_or_sub && type_hint.map_or(false, |h| is_pointer_type(h)) {
                (type_hint.cloned(), if is_long_cminor_binop(op) { Some(default_long_type()) } else { None })
            } else if is_long_cminor_binop(op) {
                (Some(default_long_type()), Some(default_long_type()))
            } else {
                (None, None)
            };
            let lhs_expr = clight_expr_from_csharp_inner(lhs, field_info, var_types, lhs_hint.as_ref());
            let rhs_expr = clight_expr_from_csharp_inner(rhs, field_info, var_types, rhs_hint.as_ref());
            // Downgrade Oaddl/Osubl to Oadd/Osub for pointer operands so build_binop_expr produces pointer result type (ptr+int=ptr in C).
            let effective_op = match op {
                CminorBinop::Oaddl
                    if is_pointer_type(&clight_expr_type(&lhs_expr))
                        || is_pointer_type(&clight_expr_type(&rhs_expr)) =>
                {
                    &CminorBinop::Oadd
                }
                CminorBinop::Osubl
                    if is_pointer_type(&clight_expr_type(&lhs_expr)) =>
                {
                    &CminorBinop::Osub
                }
                _ => op,
            };
            build_binop_expr(effective_op, lhs_expr, rhs_expr)
        }
        CsharpminorExpr::Eload(chunk, addr) => {
            if !field_info.is_empty() {
                if let Some((base_expr, field_id, field_ty)) =
                    extract_field_access(addr, chunk, field_info)
                {
                    return ClightExpr::Efield(Box::new(base_expr), field_id, field_ty);
                }
            }

            if let CsharpminorExpr::Econst(Constant::Oaddrsymbol(ident, ofs)) = addr.as_ref() {
                if *ident != 0 && *ofs == 0 {
                    let ty = clight_type_from_chunk(chunk);
                    return ClightExpr::Evar(*ident, ty);
                }
            }

            let elem_ty = clight_type_from_chunk(chunk);
            let ptr_hint = pointer_to(elem_ty.clone());
            let addr_expr = clight_expr_from_csharp_inner(addr, field_info, var_types, Some(&ptr_hint));

            if matches!(
                &addr_expr,
                ClightExpr::EconstInt(0, _) | ClightExpr::EconstLong(0, _)
            ) {
                debug!("[DEBUG] Skipped NULL deref from Eload, returning zero constant instead of placeholder: {:?}", addr_expr);
                let ty = clight_type_from_chunk(chunk);
                return match ty {
                    ClightType::Tfloat(ClightFloatSize::F64, _) => {
                        ClightExpr::EconstFloat(ClightFloat64(0.0), ty)
                    }
                    ClightType::Tfloat(ClightFloatSize::F32, _) => {
                        ClightExpr::EconstSingle(ClightFloat32(0.0), ty)
                    }
                    _ => ClightExpr::EconstInt(0, ty),
                };
            }

            let ty = clight_type_from_chunk(chunk);
            let pointer_ty = pointer_to(ty.clone());

            if let ClightExpr::Ebinop(ClightBinaryOp::Oadd, ref base, ref offset, _) = addr_expr {
                let base_ty = clight_expr_type(base);
                let offset_ty = clight_expr_type(offset);

                if !is_pointer_type(&base_ty) && !is_pointer_type(&offset_ty) {
                    let char_ptr_ty = pointer_to(ClightType::Tint(
                        ClightIntSize::I8,
                        ClightSignedness::Signed,
                        default_attr(),
                    ));
                    let base_as_char_ptr = ClightExpr::Ecast(base.clone(), char_ptr_ty.clone());
                    let byte_addr = ClightExpr::Ebinop(
                        ClightBinaryOp::Oadd,
                        Box::new(base_as_char_ptr),
                        offset.clone(),
                        char_ptr_ty,
                    );
                    let typed_ptr = ClightExpr::Ecast(Box::new(byte_addr), pointer_ty);
                    return ClightExpr::Ederef(Box::new(typed_ptr), ty);
                }
            }

            if let ClightExpr::Etempvar(id, ref var_ty) = addr_expr {
                if is_pointer_type(var_ty) {
                    let ptraddr = ClightExpr::Etempvar(id, pointer_ty.clone());
                    return ClightExpr::Ederef(Box::new(ptraddr), ty);
                }
            }
            if let ClightExpr::Evar(id, ref var_ty) = addr_expr {
                if is_pointer_type(var_ty) {
                    let ptraddr = ClightExpr::Evar(id, pointer_ty.clone());
                    return ClightExpr::Ederef(Box::new(ptraddr), ty);
                }
            }

            let ptraddr = cast_expr_to_type(addr_expr.clone(), pointer_ty);

            if let ClightExpr::Ecast(inner, _) = &ptraddr {
                if matches!(
                    inner.as_ref(),
                    ClightExpr::EconstInt(0, _) | ClightExpr::EconstLong(0, _)
                ) {
                    debug!("[DEBUG] Skipped NULL deref from Eload with Ecast(0), returning zero constant instead of placeholder");
                    return match ty.clone() {
                        ClightType::Tfloat(ClightFloatSize::F64, _) => {
                            ClightExpr::EconstFloat(ClightFloat64(0.0), ty.clone())
                        }
                        ClightType::Tfloat(ClightFloatSize::F32, _) => {
                            ClightExpr::EconstSingle(ClightFloat32(0.0), ty.clone())
                        }
                        _ => ClightExpr::EconstInt(0, ty.clone()),
                    };
                }
            }

            ClightExpr::Ederef(Box::new(ptraddr), ty)
        }
        CsharpminorExpr::Econdition(cond, true_val, false_val) => {
            let cond_expr = clight_expr_from_csharp_inner(cond, field_info, var_types, None);
            let true_expr = clight_expr_from_csharp_inner(true_val, field_info, var_types, type_hint);
            let false_expr = clight_expr_from_csharp_inner(false_val, field_info, var_types, type_hint);
            let ty = type_hint.cloned().unwrap_or_else(default_int_type);
            ClightExpr::Econdition(Box::new(cond_expr), Box::new(true_expr), Box::new(false_expr), ty)
        }
    }
}

pub(crate) fn clight_exprs_from_csharp(exprs: &[CsharpminorExpr]) -> Vec<ClightExpr> {
    exprs.iter().map(clight_expr_from_csharp).collect()
}

pub(crate) fn clight_exprs_from_csharp_with_types(
    exprs: &[CsharpminorExpr],
    var_types: &VarTypeMap,
) -> Vec<ClightExpr> {
    exprs
        .iter()
        .map(|e| clight_expr_from_csharp_with_types(e, var_types))
        .collect()
}

pub(crate) fn clight_exprs_from_csharp_with_multi_types(
    exprs: &[CsharpminorExpr],
    var_types: &MultiVarTypeMap,
) -> Vec<ClightExpr> {
    exprs
        .iter()
        .map(|e| clight_expr_from_csharp_with_multi_types(e, var_types))
        .collect()
}

pub(crate) fn clight_expr_from_builtin_arg_with_types(
    arg: &BuiltinArg<CsharpminorExpr>,
    var_types: &VarTypeMap,
) -> ClightExpr {
    match arg {
        BuiltinArg::BA(expr) => clight_expr_from_csharp_with_types(expr, var_types),
        BuiltinArg::BAInt(v) => {
            let narrowed = i32::try_from(*v).unwrap_or(if *v >= 0 { i32::MAX } else { i32::MIN });
            ClightExpr::EconstInt(narrowed, default_int_type())
        }
        BuiltinArg::BALong(v) => {
            normalize_const_expr(ClightExpr::EconstLong(*v, default_long_type()))
        }
        BuiltinArg::BAFloat(v) => {
            ClightExpr::EconstFloat(ClightFloat64::from(v.as_f64()), default_float_type())
        }
        BuiltinArg::BASingle(v) => {
            ClightExpr::EconstSingle(ClightFloat32::from(v.as_f32()), default_single_type())
        }
        BuiltinArg::BALoadStack(_, ofs) | BuiltinArg::BAAddrStack(ofs) => {
            let offset = *ofs;
            normalize_const_expr(ClightExpr::EconstLong(offset, default_long_type()))
        }
        BuiltinArg::BALoadGlobal(_, ident, ofs) | BuiltinArg::BAAddrGlobal(ident, ofs) => {
            if *ident == 0 {
                let addr_val = *ofs;
                match i32::try_from(addr_val) {
                    Ok(int_val) => ClightExpr::EconstInt(int_val, default_int_type()),
                    Err(_) => ClightExpr::EconstLong(addr_val, default_long_type()),
                }
            } else {
                let base = ClightExpr::Eaddrof(
                    Box::new(ClightExpr::Evar(*ident, default_int_type())),
                    pointer_to(default_int_type()),
                );
                if *ofs == 0 {
                    base
                } else {
                    let offset = *ofs;
                    ClightExpr::Ebinop(
                        ClightBinaryOp::Oadd,
                        Box::new(base),
                        Box::new(normalize_const_expr(ClightExpr::EconstLong(
                            offset,
                            default_long_type(),
                        ))),
                        pointer_to(default_int_type()),
                    )
                }
            }
        }
        BuiltinArg::BASplitLong(lo, hi) | BuiltinArg::BAAddPtr(lo, hi) => {
            let lo_expr = clight_expr_from_builtin_arg_with_types(lo, var_types);
            let hi_expr = clight_expr_from_builtin_arg_with_types(hi, var_types);
            ClightExpr::Ebinop(
                ClightBinaryOp::Oadd,
                Box::new(lo_expr),
                Box::new(hi_expr),
                default_long_type(),
            )
        }
    }
}

pub(crate) fn clight_builtin_args_with_types(
    args: &[BuiltinArg<CsharpminorExpr>],
    var_types: &VarTypeMap,
) -> Vec<ClightExpr> {
    args.iter()
        .map(|arg| clight_expr_from_builtin_arg_with_types(arg, var_types))
        .collect()
}

pub(crate) fn clight_builtin_args_with_multi_types(
    args: &[BuiltinArg<CsharpminorExpr>],
    var_types: &MultiVarTypeMap,
) -> Vec<ClightExpr> {
    args.iter()
        .map(|arg| {
            match arg {
                BuiltinArg::BA(expr) => clight_expr_from_csharp_with_multi_types(expr, var_types),
                other => {
                    // Non-expression builtin args don't use var types, delegate to existing
                    let empty = VarTypeMap::new();
                    clight_expr_from_builtin_arg_with_types(other, &empty)
                }
            }
        })
        .collect()
}

pub(crate) fn clight_cmp_from_condition(cond: &Comparison) -> ClightBinaryOp {
    match cond {
        Comparison::Ceq => ClightBinaryOp::Oeq,
        Comparison::Cne => ClightBinaryOp::One,
        Comparison::Clt => ClightBinaryOp::Olt,
        Comparison::Cle => ClightBinaryOp::Ole,
        Comparison::Cgt => ClightBinaryOp::Ogt,
        Comparison::Cge => ClightBinaryOp::Oge,
        Comparison::Unknown => ClightBinaryOp::One,
    }
}

/// Returns true if any sub-expression is an Etempvar/Evar with pointer type, detecting implicit pointer inference despite Tlong annotation.
fn expr_contains_pointer_var(expr: &ClightExpr) -> bool {
    match expr {
        ClightExpr::Etempvar(_, ty) | ClightExpr::Evar(_, ty) => is_pointer_type(ty),
        ClightExpr::Eunop(_, inner, _) | ClightExpr::Ecast(inner, _)
        | ClightExpr::Ederef(inner, _) | ClightExpr::Eaddrof(inner, _)
        | ClightExpr::Efield(inner, _, _) => expr_contains_pointer_var(inner),
        ClightExpr::Ebinop(_, lhs, rhs, _) => {
            expr_contains_pointer_var(lhs) || expr_contains_pointer_var(rhs)
        }
        ClightExpr::Econdition(c, t, f, _) => {
            expr_contains_pointer_var(c) || expr_contains_pointer_var(t) || expr_contains_pointer_var(f)
        }
        _ => false,
    }
}

pub(crate) fn check_clight_stmt(stmt: &ClightStmt) -> Option<ClightStmt> {
    match stmt {
        ClightStmt::Sassign(lhs, rhs) => {
            if expr_has_bad_binop(lhs) || expr_has_bad_binop(rhs) {
                return None;
            }
            let lhs_ty = clight_expr_type(lhs);
            let rhs_ty = clight_expr_type(rhs);

            if is_function_pointer_type(&lhs_ty)
                || is_function_pointer_type(&rhs_ty)
                || is_function_type(&lhs_ty)
                || is_function_type(&rhs_ty)
            {
                return None;
            }

            if lhs_ty == rhs_ty || clight_cast_supported(&rhs_ty, &lhs_ty) {
                Some(stmt.clone())
            } else if !make_binarith_check(&lhs_ty, &rhs_ty) {
                let cast_rhs = ClightExpr::Ecast(Box::new(rhs.clone()), lhs_ty);
                Some(ClightStmt::Sassign(lhs.clone(), cast_rhs))
            } else {
                let cast_rhs = ClightExpr::Ecast(Box::new(rhs.clone()), lhs_ty);
                Some(ClightStmt::Sassign(lhs.clone(), cast_rhs))
            }
        }
        ClightStmt::Sset(_id, expr) => {
            if expr_has_bad_binop(expr) {
                None
            } else {
                let expr_ty = clight_expr_type(expr);

                if !is_function_pointer_type(&expr_ty) && !is_function_type(&expr_ty) {
                    Some(stmt.clone())
                } else {
                    None
                }
            }
        }
        ClightStmt::Scall(dst, func_expr, args) => {
            let func_ty = clight_expr_type(func_expr);
            let func_ok = is_function_type(&func_ty) || is_function_pointer_type(&func_ty);
            let args_ok = args.iter().all(|arg| {
                let arg_ty = clight_expr_type(arg);
                !is_function_pointer_type(&arg_ty) && !is_function_type(&arg_ty)
            });
            if func_ok && args_ok {
                Some(stmt.clone())
            } else if !func_ok {
                let default_fn_ty = ClightType::Tfunction(
                    Arc::new(vec![]),
                    Arc::new(ClightType::Tint(ClightIntSize::I32, ClightSignedness::Signed, default_attr())),
                    CallConv::default(),
                );
                let fn_ptr_ty = pointer_to(default_fn_ty);
                let cast_func = ClightExpr::Ecast(Box::new(func_expr.clone()), fn_ptr_ty);
                Some(ClightStmt::Scall(dst.clone(), cast_func, args.clone()))
            } else {
                None
            }
        }
        ClightStmt::Sreturn(Some(expr)) => {
            let expr_ty = clight_expr_type(expr);

            if !is_function_pointer_type(&expr_ty) && !is_function_type(&expr_ty) {
                Some(stmt.clone())
            } else {
                None
            }
        }
        ClightStmt::Sreturn(None) => Some(stmt.clone()),
        ClightStmt::Sifthenelse(cond, then_stmt, else_stmt) => {
            if expr_has_bad_binop(cond) {
                None
            } else {
                let then_valid = check_clight_stmt(then_stmt);
                let else_valid = check_clight_stmt(else_stmt);
                match (then_valid, else_valid) {
                    (Some(t), Some(e)) => Some(ClightStmt::Sifthenelse(cond.clone(), Box::new(t), Box::new(e))),
                    _ => None,
                }
            }
        }
        ClightStmt::Sloop(body, exit) => {
            let body_checked = check_clight_stmt(body)?;
            let exit_checked = check_clight_stmt(exit)?;
            Some(ClightStmt::Sloop(Box::new(body_checked), Box::new(exit_checked)))
        }
        ClightStmt::Ssequence(stmts) => {
            let checked: Vec<_> = stmts.iter().filter_map(check_clight_stmt).collect();
            if checked.len() == stmts.len() {
                Some(ClightStmt::Ssequence(checked))
            } else {
                None
            }
        }
        ClightStmt::Slabel(label, inner) => {
            check_clight_stmt(inner).map(|s| ClightStmt::Slabel(label.clone(), Box::new(s)))
        }
        ClightStmt::Sswitch(expr, _) => {
            if !expr_has_bad_binop(expr) {
                Some(stmt.clone())
            } else {
                None
            }
        }
        _ => Some(stmt.clone()),
    }
}

fn force_int_type_for_32bit_cmp(expr: ClightExpr) -> ClightExpr {
    let ty = clight_expr_type(&expr);
    if !matches!(ty, ClightType::Tpointer(_, _)) {
        return expr;
    }
    match expr {
        ClightExpr::Etempvar(id, _) => ClightExpr::Etempvar(id, default_int_type()),
        ClightExpr::Evar(id, _) => ClightExpr::Evar(id, default_int_type()),
        other => ClightExpr::Ecast(Box::new(other), default_int_type()),
    }
}

pub(crate) fn clight_condition_expr_with_types(
    cond: &Condition,
    args: &[CsharpminorExpr],
    var_types: &MultiVarTypeMap,
) -> Option<ClightExpr> {
    match cond {
        Condition::Ccomp(comp)
        | Condition::Ccompu(comp)
        | Condition::Ccompl(comp)
        | Condition::Ccomplu(comp)
        | Condition::Ccompf(comp)
        | Condition::Ccompfs(comp) => {
            if args.len() >= 2 {
                let lhs = clight_expr_from_csharp_with_multi_types(&args[0], var_types);
                let rhs = clight_expr_from_csharp_with_multi_types(&args[1], var_types);
                let (lhs, rhs) = if matches!(cond, Condition::Ccomp(_) | Condition::Ccompu(_)) {
                    (force_int_type_for_32bit_cmp(lhs), force_int_type_for_32bit_cmp(rhs))
                } else {
                    (lhs, rhs)
                };
                let lhs_ty = clight_expr_type(&lhs);
                let rhs_ty0 = clight_expr_type(&rhs);
                let is_zero_lit = |e: &ClightExpr| {
                    matches!(
                        e,
                        ClightExpr::EconstInt(0, _) | ClightExpr::EconstLong(0, _)
                    )
                };
                let mut lhs_final = lhs.clone();
                let mut rhs_final = match (lhs_ty.clone(), rhs_ty0.clone(), &rhs) {
                    (ClightType::Tpointer(_, _), _, ClightExpr::EconstInt(0, _))
                    | (ClightType::Tpointer(_, _), _, ClightExpr::EconstLong(0, _)) => {
                        ClightExpr::Ecast(
                            Box::new(ClightExpr::EconstInt(0, default_int_type())),
                            lhs_ty.clone(),
                        )
                    }
                    (_, ClightType::Tpointer(_, _), _) if is_zero_lit(&lhs) => {
                        ClightExpr::Ecast(
                            Box::new(ClightExpr::EconstInt(0, default_int_type())),
                            rhs_ty0.clone(),
                        )
                    }
                    _ => {
                        if matches!(lhs_ty, ClightType::Tpointer(_, _))
                            && is_zero_constant(&args[1])
                        {
                            ClightExpr::Ecast(
                                Box::new(ClightExpr::EconstInt(0, default_int_type())),
                                lhs_ty.clone(),
                            )
                        } else if matches!(rhs_ty0, ClightType::Tpointer(_, _))
                            && is_zero_constant(&args[0])
                        {
                            ClightExpr::Ecast(
                                Box::new(ClightExpr::EconstInt(0, default_int_type())),
                                rhs_ty0.clone(),
                            )
                        } else {
                            rhs.clone()
                        }
                    }
                };
                let rhs_final_ty = clight_expr_type(&rhs_final);
                if (matches!(lhs_ty, ClightType::Tpointer(_, _))
                    && is_integral_type(&rhs_final_ty)
                    && !is_zero_lit(&rhs_final))
                    || (is_integral_type(&lhs_ty)
                        && matches!(rhs_final_ty, ClightType::Tpointer(_, _))
                        && !is_zero_lit(&lhs_final))
                {
                    let cast_long = |e: ClightExpr| match e {
                        ClightExpr::EconstInt(v, _) => normalize_const_expr(
                            ClightExpr::EconstLong(v as i64, default_long_type()),
                        ),
                        ClightExpr::EconstLong(v, _) => {
                            normalize_const_expr(ClightExpr::EconstLong(v, default_long_type()))
                        }
                        other => ClightExpr::Ecast(Box::new(other), default_long_type()),
                    };
                    lhs_final = cast_long(lhs_final);
                    rhs_final = cast_long(rhs_final);
                    debug!("[NORMALIZE][PTR_INT_CMP] forced pointer-int comparison to long-long (non-zero integral). lhs_ty={:?} rhs_ty={:?}", lhs_ty, rhs_ty0);
                }
                Some(ClightExpr::Ebinop(
                    clight_cmp_from_condition(comp),
                    Box::new(lhs_final),
                    Box::new(rhs_final),
                    default_bool_type(),
                ))
            } else if args.len() == 1 {
                let lhs = clight_expr_from_csharp_with_multi_types(&args[0], var_types);
                let lhs_ty = clight_expr_type(&lhs);
                let zero_expr = if matches!(lhs_ty, ClightType::Tpointer(_, _)) {
                    ClightExpr::Ecast(
                        Box::new(ClightExpr::EconstInt(0, default_int_type())),
                        lhs_ty.clone(),
                    )
                } else {
                    ClightExpr::EconstInt(0, default_int_type())
                };
                Some(ClightExpr::Ebinop(
                    clight_cmp_from_condition(comp),
                    Box::new(lhs),
                    Box::new(zero_expr),
                    default_bool_type(),
                ))
            } else {
                Some(ClightExpr::EconstInt(1, default_bool_type()))
            }
        }
        Condition::Ccompimm(comp, imm) | Condition::Ccompuimm(comp, imm) => {
            if !args.is_empty() {
                let lhs = clight_expr_from_csharp_with_multi_types(&args[0], var_types);
                let lhs_final = force_int_type_for_32bit_cmp(lhs);
                let rhs_final = normalize_const_expr(
                    ClightExpr::EconstInt(*imm as i32, default_int_type()),
                );
                Some(ClightExpr::Ebinop(
                    clight_cmp_from_condition(comp),
                    Box::new(lhs_final),
                    Box::new(rhs_final),
                    default_bool_type(),
                ))
            } else {
                Some(ClightExpr::EconstInt(1, default_bool_type()))
            }
        }
        Condition::Ccomplimm(comp, imm) | Condition::Ccompluimm(comp, imm) => {
            if !args.is_empty() {
                let lhs = clight_expr_from_csharp_with_multi_types(&args[0], var_types);
                let lhs_ty = clight_expr_type(&lhs);
                let mut lhs_final = lhs.clone();
                let rhs_final = if *imm == 0 {
                    if matches!(lhs_ty, ClightType::Tpointer(_, _)) {
                        ClightExpr::Ecast(
                            Box::new(ClightExpr::EconstLong(0, default_long_type())),
                            lhs_ty.clone(),
                        )
                    } else {
                        ClightExpr::EconstLong(0, default_long_type())
                    }
                } else {
                    if matches!(lhs_ty, ClightType::Tpointer(_, _)) {
                        let lhs_cast =
                            ClightExpr::Ecast(Box::new(lhs_final.clone()), default_long_type());
                        lhs_final = lhs_cast;
                    }
                    normalize_const_expr(ClightExpr::EconstLong(*imm, default_long_type()))
                };
                Some(ClightExpr::Ebinop(
                    clight_cmp_from_condition(comp),
                    Box::new(lhs_final),
                    Box::new(rhs_final),
                    default_bool_type(),
                ))
            } else {
                Some(ClightExpr::EconstInt(1, default_bool_type()))
            }
        }
        Condition::Cmaskzero(mask) => {
            if !args.is_empty() {
                let value = clight_expr_from_csharp_with_multi_types(&args[0], var_types);

                let masked = ClightExpr::Ebinop(
                    ClightBinaryOp::Oand,
                    Box::new(value),
                    Box::new(normalize_const_expr(ClightExpr::EconstLong(
                        *mask,
                        default_long_type(),
                    ))),
                    default_long_type(),
                );
                Some(ClightExpr::Ebinop(
                    ClightBinaryOp::Oeq,
                    Box::new(masked),
                    Box::new(ClightExpr::EconstInt(0, default_int_type())),
                    default_bool_type(),
                ))
            } else {
                Some(ClightExpr::EconstInt(1, default_bool_type()))
            }
        }
        Condition::Cmasknotzero(mask) => {
            if !args.is_empty() {
                let value = clight_expr_from_csharp_with_multi_types(&args[0], var_types);
                let masked = ClightExpr::Ebinop(
                    ClightBinaryOp::Oand,
                    Box::new(value),
                    Box::new(normalize_const_expr(ClightExpr::EconstLong(
                        *mask,
                        default_long_type(),
                    ))),
                    default_long_type(),
                );
                Some(ClightExpr::Ebinop(
                    ClightBinaryOp::One,
                    Box::new(masked),
                    Box::new(ClightExpr::EconstInt(0, default_int_type())),
                    default_bool_type(),
                ))
            } else {
                Some(ClightExpr::EconstInt(1, default_bool_type()))
            }
        }
        Condition::Cnotcompf(comp) => {
            let inner =
                clight_condition_expr_with_types(&Condition::Ccompf(*comp), args, var_types)?;
            Some(ClightExpr::Eunop(
                ClightUnaryOp::Onotbool,
                Box::new(inner),
                default_bool_type(),
            ))
        }
        Condition::Cnotcompfs(comp) => {
            let inner =
                clight_condition_expr_with_types(&Condition::Ccompfs(*comp), args, var_types)?;
            Some(ClightExpr::Eunop(
                ClightUnaryOp::Onotbool,
                Box::new(inner),
                default_bool_type(),
            ))
        }
    }
}


fn extract_base_ident_clight(expr: &ClightExpr) -> Option<Ident> {
    match expr {
        ClightExpr::Etempvar(ident, _) => Some(*ident),
        ClightExpr::Ecast(inner, _) => extract_base_ident_clight(inner),
        _ => None,
    }
}

fn extract_const_offset_clight(expr: &ClightExpr) -> Option<i64> {
    match expr {
        ClightExpr::EconstInt(v, _) => Some(*v as i64),
        ClightExpr::EconstLong(v, _) => Some(*v),
        ClightExpr::Ecast(inner, _) => extract_const_offset_clight(inner),
        _ => None,
    }
}

fn extract_deref_field_pattern(inner: &ClightExpr) -> Option<(Ident, i64)> {
    let stripped = match inner {
        ClightExpr::Ecast(e, _) => e.as_ref(),
        other => other,
    };
    match stripped {
        ClightExpr::Ebinop(ClightBinaryOp::Oadd, lhs, rhs, _) => {
            let base_ident = extract_base_ident_clight(lhs)?;
            let offset = extract_const_offset_clight(rhs)?;
            Some((base_ident, offset.abs()))
        }
        ClightExpr::Etempvar(ident, _) => Some((*ident, 0)),
        _ => None,
    }
}

/// Rewrite Ederef patterns matching (base_off, field_off) with Efield, producing struct-field-rewritten statement variants.
pub(crate) fn rewrite_stmt_with_efield(
    stmt: &ClightStmt,
    base_off: i64,
    field_off: i64,
    field_name: Ident,
    chunk: &MemoryChunk,
) -> Option<ClightStmt> {
    fn rewrite_expr(
        expr: &ClightExpr,
        base_off: i64,
        field_off: i64,
        field_name: Ident,
        chunk: &MemoryChunk,
    ) -> (ClightExpr, bool) {
        match expr {
            ClightExpr::Ederef(inner, deref_ty) => {
                if let Some((base_ident, offset)) = extract_deref_field_pattern(inner) {
                    let base_key = base_ident as i64;
                    if base_key == base_off && offset == field_off {
                        let field_ty = deref_ty.clone();
                        let struct_id = base_key.unsigned_abs() as Ident;
                        let struct_ty = ClightType::Tstruct(struct_id, default_attr());
                        let struct_ptr_ty = pointer_to(struct_ty.clone());
                        let ptr_expr = ClightExpr::Etempvar(base_ident, struct_ptr_ty);
                        let proper_field_id = make_field_ident(field_off, chunk.clone());
                        let deref_expr = ClightExpr::Ederef(Box::new(ptr_expr), struct_ty);
                        return (ClightExpr::Efield(Box::new(deref_expr), proper_field_id, field_ty), true);
                    }
                }
                let (inner2, changed) = rewrite_expr(inner, base_off, field_off, field_name, chunk);
                (ClightExpr::Ederef(Box::new(inner2), deref_ty.clone()), changed)
            }
            ClightExpr::Ecast(inner, ty) => {
                let (inner2, changed) = rewrite_expr(inner, base_off, field_off, field_name, chunk);
                (ClightExpr::Ecast(Box::new(inner2), ty.clone()), changed)
            }
            ClightExpr::Ebinop(op, lhs, rhs, ty) => {
                let (lhs2, c1) = rewrite_expr(lhs, base_off, field_off, field_name, chunk);
                let (rhs2, c2) = rewrite_expr(rhs, base_off, field_off, field_name, chunk);
                (ClightExpr::Ebinop(op.clone(), Box::new(lhs2), Box::new(rhs2), ty.clone()), c1 || c2)
            }
            ClightExpr::Eunop(op, inner, ty) => {
                let (inner2, changed) = rewrite_expr(inner, base_off, field_off, field_name, chunk);
                (ClightExpr::Eunop(op.clone(), Box::new(inner2), ty.clone()), changed)
            }
            ClightExpr::Efield(inner, id, ty) => {
                let (inner2, changed) = rewrite_expr(inner, base_off, field_off, field_name, chunk);
                (ClightExpr::Efield(Box::new(inner2), *id, ty.clone()), changed)
            }
            ClightExpr::Eaddrof(inner, ty) => {
                let (inner2, changed) = rewrite_expr(inner, base_off, field_off, field_name, chunk);
                (ClightExpr::Eaddrof(Box::new(inner2), ty.clone()), changed)
            }
            other => (other.clone(), false),
        }
    }

    fn rewrite_inner(
        stmt: &ClightStmt,
        base_off: i64,
        field_off: i64,
        field_name: Ident,
        chunk: &MemoryChunk,
    ) -> (ClightStmt, bool) {
        match stmt {
            ClightStmt::Sset(id, expr) => {
                let (expr2, changed) = rewrite_expr(expr, base_off, field_off, field_name, chunk);
                (ClightStmt::Sset(*id, expr2), changed)
            }
            ClightStmt::Sassign(lhs, rhs) => {
                let (lhs2, c1) = rewrite_expr(lhs, base_off, field_off, field_name, chunk);
                let (rhs2, c2) = rewrite_expr(rhs, base_off, field_off, field_name, chunk);
                (ClightStmt::Sassign(lhs2, rhs2), c1 || c2)
            }
            ClightStmt::Scall(ret, f, args) => {
                let (f2, cf) = rewrite_expr(f, base_off, field_off, field_name, chunk);
                let mut any_changed = cf;
                let args2: Vec<_> = args.iter().map(|a| {
                    let (a2, c) = rewrite_expr(a, base_off, field_off, field_name, chunk);
                    any_changed |= c;
                    a2
                }).collect();
                (ClightStmt::Scall(*ret, f2, args2), any_changed)
            }
            ClightStmt::Sreturn(Some(e)) => {
                let (e2, changed) = rewrite_expr(e, base_off, field_off, field_name, chunk);
                (ClightStmt::Sreturn(Some(e2)), changed)
            }
            ClightStmt::Sifthenelse(c, t, e) => {
                let (c2, cc) = rewrite_expr(c, base_off, field_off, field_name, chunk);
                let (t2, ct) = rewrite_inner(t, base_off, field_off, field_name, chunk);
                let (e2, ce) = rewrite_inner(e, base_off, field_off, field_name, chunk);
                (ClightStmt::Sifthenelse(c2, Box::new(t2), Box::new(e2)), cc || ct || ce)
            }
            ClightStmt::Slabel(id, inner) => {
                let (inner2, changed) = rewrite_inner(inner, base_off, field_off, field_name, chunk);
                (ClightStmt::Slabel(*id, Box::new(inner2)), changed)
            }
            ClightStmt::Ssequence(ss) => {
                let mut any = false;
                let ss2: Vec<_> = ss.iter().map(|s| {
                    let (s2, c) = rewrite_inner(s, base_off, field_off, field_name, chunk);
                    any |= c;
                    s2
                }).collect();
                (ClightStmt::Ssequence(ss2), any)
            }
            other => (other.clone(), false),
        }
    }

    let (rewritten, changed) = rewrite_inner(stmt, base_off, field_off, field_name, chunk);
    if changed { Some(rewritten) } else { None }
}

fn rewrite_clight_expr_fields(expr: &ClightExpr, field_info: &FieldInfo, reg_to_canonical: &HashMap<Ident, Ident>) -> ClightExpr {
    match expr {
        ClightExpr::Ederef(inner, deref_ty) => {
            if let Some((base_ident, offset)) = extract_deref_field_pattern(inner) {
                let base_key = base_ident as i64;
                // Try direct byte offset first, then rescale by pointee size to recover original byte offset for field_info lookup.
                let lookup = field_info.get(&(base_key, offset)).map(|v| (offset, v))
                    .or_else(|| {
                        let elem_size = get_inner_type_size(deref_ty)?;
                        if elem_size > 1 {
                            let byte_offset = offset * elem_size;
                            field_info.get(&(base_key, byte_offset)).map(|v| (byte_offset, v))
                        } else {
                            None
                        }
                    });
                if let Some((field_offset, (_field_ident, chunk))) = lookup {
                    let field_ty = deref_ty.clone();
                    // Use canonical struct ID if available, else fall back to register-based
                    let struct_id = reg_to_canonical.get(&base_ident)
                        .copied()
                        .unwrap_or_else(|| base_key.unsigned_abs() as Ident);
                    let struct_ty = ClightType::Tstruct(struct_id, default_attr());
                    let struct_ptr_ty = pointer_to(struct_ty.clone());
                    let ptr_expr = ClightExpr::Etempvar(base_ident, struct_ptr_ty);
                    let proper_field_id = make_field_ident(field_offset, chunk.clone());
                    let deref_expr = ClightExpr::Ederef(Box::new(ptr_expr), struct_ty);
                    return ClightExpr::Efield(Box::new(deref_expr), proper_field_id, field_ty);
                }
            }
            ClightExpr::Ederef(
                Box::new(rewrite_clight_expr_fields(inner, field_info, reg_to_canonical)),
                deref_ty.clone(),
            )
        }
        ClightExpr::Ebinop(op, lhs, rhs, ty) => ClightExpr::Ebinop(
            op.clone(),
            Box::new(rewrite_clight_expr_fields(lhs, field_info, reg_to_canonical)),
            Box::new(rewrite_clight_expr_fields(rhs, field_info, reg_to_canonical)),
            ty.clone(),
        ),
        ClightExpr::Eunop(op, inner, ty) => ClightExpr::Eunop(
            op.clone(),
            Box::new(rewrite_clight_expr_fields(inner, field_info, reg_to_canonical)),
            ty.clone(),
        ),
        ClightExpr::Ecast(inner, ty) => ClightExpr::Ecast(
            Box::new(rewrite_clight_expr_fields(inner, field_info, reg_to_canonical)),
            ty.clone(),
        ),
        ClightExpr::Efield(inner, ident, ty) => ClightExpr::Efield(
            Box::new(rewrite_clight_expr_fields(inner, field_info, reg_to_canonical)),
            *ident,
            ty.clone(),
        ),
        ClightExpr::Eaddrof(inner, ty) => ClightExpr::Eaddrof(
            Box::new(rewrite_clight_expr_fields(inner, field_info, reg_to_canonical)),
            ty.clone(),
        ),
        ClightExpr::Econdition(cond, t, f, ty) => ClightExpr::Econdition(
            Box::new(rewrite_clight_expr_fields(cond, field_info, reg_to_canonical)),
            Box::new(rewrite_clight_expr_fields(t, field_info, reg_to_canonical)),
            Box::new(rewrite_clight_expr_fields(f, field_info, reg_to_canonical)),
            ty.clone(),
        ),
        other => other.clone(),
    }
}

fn rewrite_clight_stmt_fields(stmt: &ClightStmt, field_info: &FieldInfo, reg_to_canonical: &HashMap<Ident, Ident>) -> ClightStmt {
    match stmt {
        ClightStmt::Sassign(lhs, rhs) => ClightStmt::Sassign(
            rewrite_clight_expr_fields(lhs, field_info, reg_to_canonical),
            rewrite_clight_expr_fields(rhs, field_info, reg_to_canonical),
        ),
        ClightStmt::Sset(ident, expr) => ClightStmt::Sset(
            *ident,
            rewrite_clight_expr_fields(expr, field_info, reg_to_canonical),
        ),

        ClightStmt::Scall(ret, func, args) => ClightStmt::Scall(
            *ret,
            rewrite_clight_expr_fields(func, field_info, reg_to_canonical),
            args.iter().map(|a| rewrite_clight_expr_fields(a, field_info, reg_to_canonical)).collect(),
        ),
        ClightStmt::Sbuiltin(ret, ef, tys, args) => ClightStmt::Sbuiltin(
            *ret,
            ef.clone(),
            tys.clone(),
            args.iter().map(|a| rewrite_clight_expr_fields(a, field_info, reg_to_canonical)).collect(),
        ),
        ClightStmt::Sreturn(Some(expr)) => ClightStmt::Sreturn(
            Some(rewrite_clight_expr_fields(expr, field_info, reg_to_canonical)),
        ),
        ClightStmt::Sifthenelse(cond, then_s, else_s) => ClightStmt::Sifthenelse(
            rewrite_clight_expr_fields(cond, field_info, reg_to_canonical),
            Box::new(rewrite_clight_stmt_fields(then_s, field_info, reg_to_canonical)),
            Box::new(rewrite_clight_stmt_fields(else_s, field_info, reg_to_canonical)),
        ),
        ClightStmt::Ssequence(stmts) => ClightStmt::Ssequence(
            stmts.iter().map(|s| rewrite_clight_stmt_fields(s, field_info, reg_to_canonical)).collect(),
        ),
        ClightStmt::Sloop(body, cont) => ClightStmt::Sloop(
            Box::new(rewrite_clight_stmt_fields(body, field_info, reg_to_canonical)),
            Box::new(rewrite_clight_stmt_fields(cont, field_info, reg_to_canonical)),
        ),
        ClightStmt::Slabel(ident, inner) => ClightStmt::Slabel(
            *ident,
            Box::new(rewrite_clight_stmt_fields(inner, field_info, reg_to_canonical)),
        ),
        ClightStmt::Sswitch(expr, cases) => ClightStmt::Sswitch(
            rewrite_clight_expr_fields(expr, field_info, reg_to_canonical),
            cases.iter().map(|(label, s)| (label.clone(), rewrite_clight_stmt_fields(s, field_info, reg_to_canonical))).collect(),
        ),
        other => other.clone(),
    }
}

/// Infer struct layouts from mach_imm_stack_init when emit_struct_fields is empty.
fn infer_struct_fields_from_stack_inits(db: &mut DecompileDB) {
    let existing_fields: usize = db
        .rel_iter::<(Address, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>)>("emit_struct_fields")
        .count();
    if existing_fields > 0 {
        return;
    }

    let node_to_func: HashMap<u64, u64> = {
        let mut groups: HashMap<u64, u64> = HashMap::new();
        for (n, f) in db.rel_iter::<(Node, Address)>("instr_in_function") {
            groups.entry(*n)
                .and_modify(|curr| *curr = (*curr).min(*f))
                .or_insert(*f);
        }
        groups
    };

    let mut func_inits: HashMap<u64, Vec<(i64, Typ)>> = HashMap::new();
    for (addr, ofs, _val, typ) in db.rel_iter::<(Address, i64, i64, Typ)>("mach_imm_stack_init") {
        if let Some(&func) = node_to_func.get(addr) {
            func_inits.entry(func).or_default().push((*ofs, typ.clone()));
        }
    }

    let mut new_fields: Vec<(u64, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>)> = Vec::new();

    for (func_addr, inits) in &func_inits {
        let mut offsets: Vec<i64> = inits.iter().map(|(ofs, _)| *ofs).collect();
        offsets.sort();
        offsets.dedup();

        if offsets.len() < 4 {
            continue;
        }

        let deltas: Vec<i64> = offsets.windows(2).map(|w| w[1] - w[0]).collect();

        if deltas.iter().all(|d| *d == 4) {
            for fields_per_struct in 2..=4 {
                let struct_size = 4 * fields_per_struct as i64;
                if offsets.len() % fields_per_struct != 0 {
                    continue;
                }
                let num_structs = offsets.len() / fields_per_struct;
                if num_structs < 2 {
                    continue;
                }

                let base_ofs = offsets[0];
                let mut valid = true;
                for s in 0..num_structs {
                    for f in 0..fields_per_struct {
                        let expected = base_ofs + (s as i64) * struct_size + (f as i64) * 4;
                        if offsets[s * fields_per_struct + f] != expected {
                            valid = false;
                            break;
                        }
                    }
                    if !valid {
                        break;
                    }
                }

                if valid {
                    let fields: Vec<(i64, Ident, MemoryChunk)> = (0..fields_per_struct)
                        .map(|f| {
                            let field_offset = (f as i64) * 4;
                            let field_name = generate_field_name(field_offset);
                            (field_offset, field_name, MemoryChunk::MInt32)
                        })
                        .collect();

                    let fields_arc = Arc::new(fields);
                    for s in 0..num_structs {
                        let instance_base = base_ofs + (s as i64) * struct_size;
                        new_fields.push((*func_addr, instance_base, fields_arc.clone()));
                    }
                    break;
                }
            }
        }
    }

    for (func_addr, base_off, fields) in &new_fields {
        db.rel_push("emit_struct_fields", (*func_addr, *base_off, fields.clone()));
    }
}

fn rewrite_clight_stmts_with_struct_fields(db: &mut DecompileDB) {
    infer_struct_fields_from_stack_inits(db);

    let mut func_field_info: HashMap<u64, FieldInfo> = HashMap::new();
    for (func_addr, base_off, fields) in
        db.rel_iter::<(Address, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>)>("emit_struct_fields")
    {
        let fi = func_field_info.entry(*func_addr).or_default();
        for (field_off, field_name, chunk) in fields.iter() {
            fi.insert((*base_off, *field_off), (*field_name, chunk.clone()));
        }
    }

    // Build reg-to-canonical struct ID mapping so Tstruct IDs in expressions match XstructPtr IDs in declarations.
    // Use min-aggregation on sid to make selection deterministic when a reg has multiple canonical IDs across addresses.
    let reg_to_canonical: HashMap<Ident, Ident> = {
        let mut groups: HashMap<Ident, Ident> = HashMap::new();
        for &(_, reg, sid) in db.rel_iter::<(Address, RTLReg, usize)>("reg_to_struct_id") {
            groups.entry(reg as Ident)
                .and_modify(|curr| *curr = (*curr).min(sid as Ident))
                .or_insert(sid as Ident);
        }
        groups
    };

    if func_field_info.is_empty() {
        // No struct fields -- copy clight_stmt_without_field directly to clight_stmt
        let pass_through: ascent::boxcar::Vec<_> = db
            .rel_iter::<(Node, ClightStmt)>("clight_stmt_without_field")
            .map(|(n, s)| (*n, s.clone()))
            .collect();
        db.rel_set("clight_stmt", pass_through);

        let pass_through_emit: ascent::boxcar::Vec<_> = db
            .rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt_without_field")
            .map(|(a, n, s)| (*a, *n, s.clone()))
            .collect();
        db.rel_set("emit_clight_stmt", pass_through_emit);

        let pass_through_dead: ascent::boxcar::Vec<_> = db
            .rel_iter::<(Address, Node, ClightStmt)>("clight_stmt_dead_without_field")
            .map(|(a, n, s)| (*a, *n, s.clone()))
            .collect();
        db.rel_set("clight_stmt_dead", pass_through_dead);
        return;
    }

    let node_to_func: HashMap<u64, u64> = {
        let mut groups: HashMap<u64, u64> = HashMap::new();
        for (n, f) in db.rel_iter::<(Node, Address)>("instr_in_function") {
            groups.entry(*n)
                .and_modify(|curr| *curr = (*curr).min(*f))
                .or_insert(*f);
        }
        groups
    };

    // Struct construction synthesis: detect mach_imm_stack_init struct initialization, synthesize field assignments, and rewrite Oaddrstack to address-of.
    let struct_construction = synthesize_struct_construction(db, &node_to_func, &func_field_info);

    let new_clight_stmt: ascent::boxcar::Vec<_> = db
        .rel_iter::<(Node, ClightStmt)>("clight_stmt_without_field")
        .flat_map(|(node, stmt)| {
            // Apply Oaddrstack rewrite if this node has one
            let stmt = if let Some(rewritten) = struct_construction.rewritten_stmts.get(node) {
                rewritten.clone()
            } else {
                stmt.clone()
            };
            if let Some(fi) = node_to_func.get(node).and_then(|fa| func_field_info.get(fa)) {
                let rewritten = rewrite_clight_stmt_fields(&stmt, fi, &reg_to_canonical);
                let mut results = vec![(*node, rewritten.clone())];
                if rewritten != stmt {
                    results.push((*node, stmt));
                }
                results
            } else {
                vec![(*node, stmt)]
            }
        })
        .chain(struct_construction.new_stmts.iter().map(|(node, stmt)| (*node, stmt.clone())))
        .collect();
    db.rel_set("clight_stmt", new_clight_stmt);

    let new_emit: ascent::boxcar::Vec<_> = db
        .rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt_without_field")
        .flat_map(|(addr, node, stmt)| {
            let stmt = if let Some(rewritten) = struct_construction.rewritten_stmts.get(node) {
                rewritten.clone()
            } else {
                stmt.clone()
            };
            if let Some(fi) = func_field_info.get(addr) {
                let rewritten = rewrite_clight_stmt_fields(&stmt, fi, &reg_to_canonical);
                // For Sset where field rewriting changed type from integral to pointer, emit an additional cast-back candidate for integer-typed declarations.
                let extra = match (&stmt, &rewritten) {
                    (ClightStmt::Sset(_, orig_expr), ClightStmt::Sset(id, new_expr)) => {
                        let orig_ty = clight_expr_type(orig_expr);
                        let new_ty = clight_expr_type(new_expr);
                        if is_integral_type(&orig_ty) && !is_integral_type(&new_ty) {
                            Some((*addr, *node, ClightStmt::Sset(*id,
                                ClightExpr::Ecast(Box::new(new_expr.clone()), orig_ty))))
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                let mut results = vec![(*addr, *node, rewritten.clone())];
                // Keep original non-field candidate as fallback for when struct pointer declaration fails (e.g., register reuse with integer ops).
                if rewritten != stmt {
                    results.push((*addr, *node, stmt));
                }
                if let Some(e) = extra {
                    results.push(e);
                }
                results
            } else {
                vec![(*addr, *node, stmt)]
            }
        })
        .chain(struct_construction.new_emit_stmts.iter().map(|(a, n, s)| (*a, *n, s.clone())))
        .collect();
    db.rel_set("emit_clight_stmt", new_emit);

    let new_dead: ascent::boxcar::Vec<_> = db
        .rel_iter::<(Address, Node, ClightStmt)>("clight_stmt_dead_without_field")
        .map(|(addr, node, stmt)| {
            if let Some(fi) = func_field_info.get(addr) {
                (*addr, *node, rewrite_clight_stmt_fields(stmt, fi, &reg_to_canonical))
            } else {
                (*addr, *node, stmt.clone())
            }
        })
        .collect();
    db.rel_set("clight_stmt_dead", new_dead);

    // Push XstructPtr type candidates for registers upgraded to struct pointer types, using canonical struct IDs when available.
    let mut seen_struct_regs: std::collections::HashSet<(RTLReg, usize)> = std::collections::HashSet::new();
    for (_func_addr, fi) in &func_field_info {
        for (&(base_key, _field_off), _) in fi {
            let reg = base_key as u64 as RTLReg;
            let struct_id = reg_to_canonical.get(&(reg as Ident))
                .copied()
                .unwrap_or_else(|| base_key.unsigned_abs() as Ident);
            if seen_struct_regs.insert((reg, struct_id)) {
                db.rel_push("emit_var_type_candidate", (reg, XType::XstructPtr(struct_id)));
            }
        }
    }

}

/// Result of struct construction synthesis.
struct StructConstructionResult {
    /// New clight_stmt entries for field assignments (node -> stmt).
    new_stmts: Vec<(u64, ClightStmt)>,
    /// New emit_clight_stmt entries (func_addr, node, stmt).
    new_emit_stmts: Vec<(u64, u64, ClightStmt)>,
    /// Rewritten existing stmts: Oaddrstack -> Eaddrof (node -> new stmt).
    rewritten_stmts: HashMap<u64, ClightStmt>,
}

fn synthesize_struct_construction(
    db: &DecompileDB,
    node_to_func: &HashMap<u64, u64>,
    _func_field_info: &HashMap<u64, FieldInfo>,
) -> StructConstructionResult {
    let mut result = StructConstructionResult {
        new_stmts: Vec::new(),
        new_emit_stmts: Vec::new(),
        rewritten_stmts: HashMap::new(),
    };

    // Collect mach_imm_stack_init per function: (node_addr, stack_offset, imm_value, type)
    let mut func_stack_inits: HashMap<u64, Vec<(u64, i64, i64, Typ)>> = HashMap::new();
    for (addr, ofs, val, typ) in db.rel_iter::<(Address, i64, i64, Typ)>("mach_imm_stack_init") {
        if let Some(&func) = node_to_func.get(addr) {
            func_stack_inits.entry(func).or_default().push((*addr, *ofs, *val, typ.clone()));
        }
    }

    if func_stack_inits.is_empty() {
        return result;
    }

    // Collect all known struct layouts from emit_struct_fields for matching against stack init patterns.
    let mut known_layouts: HashMap<Vec<(i64, MemoryChunk)>, (Ident, Vec<(i64, Ident, MemoryChunk)>)> = HashMap::new();
    for (_func_addr, base_off, fields) in
        db.rel_iter::<(Address, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>)>("emit_struct_fields")
    {
        let mut layout: Vec<(i64, MemoryChunk)> = fields.iter()
            .map(|(off, _, chunk)| (*off, chunk.clone()))
            .collect();
        layout.sort_by_key(|(off, _)| *off);
        let struct_id = base_off.unsigned_abs() as Ident;
        known_layouts.entry(layout).or_insert((struct_id, fields.to_vec()));
    }

    if known_layouts.is_empty() {
        return result;
    }

    let mut sorted_funcs: Vec<u64> = func_stack_inits.keys().copied().collect();
    sorted_funcs.sort();
    for func_addr_val in sorted_funcs {
        let func_addr = &func_addr_val;
        let inits = &func_stack_inits[func_addr];
        // Sort inits by full tuple so ties at the same offset resolve deterministically.
        let mut sorted = inits.clone();
        sorted.sort();

        // Find Oaddrstack bases: Sset(var, EconstLong(negative_val)) matching a mach_imm_stack_init cluster base.
        let init_offsets: std::collections::BTreeSet<i64> = sorted.iter().map(|(_, ofs, _, _)| *ofs).collect();

        let mut stmts_for_func: Vec<(Node, ClightStmt)> = db.rel_iter::<(Node, ClightStmt)>("clight_stmt_without_field")
            .filter(|(n, _)| node_to_func.get(n) == Some(func_addr))
            .map(|(n, s)| (*n, s.clone()))
            .collect();
        stmts_for_func.sort_by_key(|(n, _)| *n);
        for (node_val, stmt_val) in &stmts_for_func {
            let node = node_val;
            let stmt = stmt_val;
            let (var_id, base_ofs) = match stmt {
                ClightStmt::Sset(var_id, expr) => {
                    if let Some(ofs) = extract_stack_offset_from_expr(expr) {
                        if init_offsets.contains(&ofs) {
                            (*var_id, ofs)
                        } else {
                            continue;
                        }
                    } else {
                        continue;
                    }
                }
                _ => continue,
            };

            // Collect mach_imm_stack_init stores that belong to this struct region
            let matching: Vec<_> = sorted.iter()
                .filter(|(_, ofs, _, _)| *ofs >= base_ofs && *ofs < base_ofs + 256)
                .collect();

            if matching.is_empty() { continue; }

            // Build layout for matching against known structs
            let mut layout: Vec<(i64, MemoryChunk)> = matching.iter()
                .map(|(_, ofs, _, typ)| {
                    let rel_ofs = ofs - base_ofs;
                    let chunk = typ_to_chunk(typ);
                    (rel_ofs, chunk)
                })
                .collect();
            layout.sort_by_key(|(off, _)| *off);

            let (struct_id, _matched_fields) = match known_layouts.get(&layout) {
                Some(info) => info.clone(),
                None => continue, // No matching struct known
            };

            let struct_ty = ClightType::Tstruct(struct_id, default_attr());
            // Use var_id as the struct local variable identifier (it holds the address)
            let struct_local_id = var_id;

            // Generate field assignment statements for each mach_imm_stack_init store
            for (init_addr, ofs, val, typ) in &matching {
                let rel_ofs = *ofs - base_ofs;
                let chunk = typ_to_chunk(typ);
                let field_id = make_field_ident(rel_ofs, chunk);
                let field_ty = typ_to_clight_type(typ);
                let val_expr = match typ {
                    Typ::Tlong | Typ::Tany64 => ClightExpr::EconstLong(*val, default_long_type()),
                    _ => ClightExpr::EconstInt(*val as i32, default_int_type()),
                };

                let lhs = ClightExpr::Efield(
                    Box::new(ClightExpr::Evar(struct_local_id, struct_ty.clone())),
                    field_id,
                    field_ty,
                );
                let stmt = ClightStmt::Sassign(lhs, val_expr);
                result.new_stmts.push((*init_addr, stmt.clone()));
                result.new_emit_stmts.push((*func_addr, *init_addr, stmt));
            }

            // Rewrite the Oaddrstack Sset: var = -16 -> var = &struct_local
            let addrof_expr = ClightExpr::Eaddrof(
                Box::new(ClightExpr::Evar(struct_local_id, struct_ty.clone())),
                pointer_to(struct_ty),
            );
            let rewritten = ClightStmt::Sset(var_id, addrof_expr);
            result.rewritten_stmts.insert(*node, rewritten);
        }

        // Fallback: generate struct fields from init stores when no Oaddrstack references base.
        if result.new_stmts.iter().all(|(a, _)| !sorted.iter().any(|(sa, _, _, _)| sa == a)) {
            let mut offsets: Vec<i64> = sorted.iter().map(|(_, ofs, _, _)| *ofs).collect();
            offsets.sort();
            offsets.dedup();

            for (layout, (struct_id, fields)) in &known_layouts {
                let struct_size: i64 = layout.iter().map(|(off, chunk)| {
                    off + match chunk {
                        MemoryChunk::MInt32 => 4,
                        MemoryChunk::MInt64 => 8,
                        MemoryChunk::MFloat32 => 4,
                        MemoryChunk::MFloat64 => 8,
                        _ => 4,
                    }
                }).max().unwrap_or(0);
                let field_count = layout.len();
                if field_count == 0 || struct_size == 0 { continue; }

                let min_ofs = offsets.first().copied().unwrap_or(0);
                let mut instance_idx = 0;
                let mut field_idx = 0;
                let mut matched_count = 0;

                for &ofs in &offsets {
                    let expected_ofs = min_ofs + (instance_idx as i64) * struct_size + layout[field_idx].0;
                    if ofs == expected_ofs {
                        matched_count += 1;
                        field_idx += 1;
                        if field_idx >= field_count {
                            field_idx = 0;
                            instance_idx += 1;
                        }
                    }
                }

                if matched_count < offsets.len() || instance_idx < 2 { continue; }

                let struct_ty = ClightType::Tstruct(*struct_id, default_attr());
                let struct_var_id = min_ofs.unsigned_abs() as Ident;

                for s in 0..instance_idx {
                    let base_ofs = min_ofs + (s as i64) * struct_size;
                    for (field_off, field_name, _chunk) in fields {
                        let target_ofs = base_ofs + field_off;
                        if let Some((init_addr, _, val, typ)) = sorted.iter().find(|(_, ofs, _, _)| *ofs == target_ofs) {
                            let field_ty = typ_to_clight_type(typ);
                            let val_expr = match typ {
                                Typ::Tlong | Typ::Tany64 => ClightExpr::EconstLong(*val, default_long_type()),
                                _ => ClightExpr::EconstInt(*val as i32, default_int_type()),
                            };

                            let lhs = ClightExpr::Efield(
                                Box::new(ClightExpr::Evar(struct_var_id, struct_ty.clone())),
                                *field_name,
                                field_ty,
                            );
                            let stmt = ClightStmt::Sassign(lhs, val_expr);
                            result.new_stmts.push((*init_addr, stmt.clone()));
                            result.new_emit_stmts.push((*func_addr, *init_addr, stmt));
                        }
                    }
                }
                break;
            }
        }
    }

    result
}

fn extract_stack_offset_from_expr(expr: &ClightExpr) -> Option<i64> {
    match expr {
        ClightExpr::EconstLong(v, _) if *v < 0 => Some(*v),
        ClightExpr::EconstInt(v, _) if *v < 0 => Some(*v as i64),
        ClightExpr::Ecast(inner, _) => extract_stack_offset_from_expr(inner),
        _ => None,
    }
}

fn typ_to_chunk(typ: &Typ) -> MemoryChunk {
    match typ {
        Typ::Tint => MemoryChunk::MInt32,
        Typ::Tlong | Typ::Tany64 => MemoryChunk::MInt64,
        Typ::Tfloat => MemoryChunk::MFloat64,
        Typ::Tsingle => MemoryChunk::MFloat32,
        _ => MemoryChunk::MInt32,
    }
}

fn typ_to_clight_type(typ: &Typ) -> ClightType {
    match typ {
        Typ::Tint => default_int_type(),
        Typ::Tlong | Typ::Tany64 => default_long_type(),
        Typ::Tfloat => default_float_type(),
        Typ::Tsingle => default_single_type(),
        _ => default_int_type(),
    }
}
