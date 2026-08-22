use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::{declare_io_from, run_pass};

use crate::decompile::passes::cminor_pass::*;
use crate::decompile::passes::csh_pass::*;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use crate::mreg::Mreg;
use crate::x86::op::{Addressing, Comparison, Condition, Operation};
use crate::x86::types::*;
use ascent::ascent_par;
use ascent::lattice::set::Set;
use either::Either;
use log::debug;

ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct ClightPassProgram;

    relation addr_to_func_ident(Address, Ident);
    relation abi_pointer_size(i64);
    relation arch_bit(i64);
    relation arg_constrained_as_ptr(Node, RTLReg);
    relation base_ident_to_symbol(Ident, Symbol);
    relation block_in_function(Node, Address);
    relation call_return_reg(Node, RTLReg);
    relation cminor_stmt(Node, CminorStmt);
    relation code_in_block(Address, Address);
    relation emit_function(Address, Symbol, Node);
    relation emit_function_param(Address, RTLReg);
    relation emit_function_return(Address, RTLReg);
    relation emit_function_return_type(Address, ClightType);
    relation emit_function_void(Address);
    relation emit_global_is_char_ptr(Ident);
    relation emit_global_is_ptr(Ident);
    // Clight-only straight-line groups.  Keep these separate from LinearPass's
    // legacy emit_sseq relation: DecompileDB relations are shared by name, so
    // reusing that name unions two different IRs and can make an old Linear
    // head absorb live Clight statements.
    relation emit_clight_sseq(Node, Node);
    relation emit_clight_sseq_edge(Node, Node, Node);
    relation emit_var_type_candidate(RTLReg, XType);
    relation all_var_types_global(Arc<Vec<(RTLReg, XType)>>);
    relation func_param_struct_type(Address, usize, usize);
    relation func_span(Symbol, Address, Address);
    relation global_symbol(Address, Symbol);
    relation global_struct_catalog(u64, usize, usize, usize);
    relation ident_to_symbol(Ident, Symbol);
    relation instr_in_function(Node, Address);
    relation is_external_function(Address);
    relation is_ptr(RTLReg);
    relation known_extern_signature(Symbol, usize, XType, Arc<Vec<XType>>);
    relation known_func_param_is_ptr(Symbol, usize);
    relation known_func_returns_long(Symbol);
    relation known_func_returns_ptr(Symbol);
    relation known_global_type(Symbol, XType);
    relation main_function(Address);
    relation reg_def_used(Address, Mreg, Address);
    relation reg_rtl(Node, Mreg, RTLReg);
    relation reg_xtl(Node, Mreg, RTLReg);
    relation rtl_inst(Node, RTLInst);
    relation rtl_succ(Node, Node);
    relation next(Address, Address);
    relation stack_var(Address, Address, i64, RTLReg);
    relation mach_imm_stack_init(Address, i64, i64, Typ);
    relation string_data(String, String, usize);
    relation struct_id_to_canonical(usize, usize);

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
    relation clight_stmt(Node, ClightStmt);
    relation clight_stmt_dead(Address, Node, ClightStmt);
    relation clight_stmt_for_func_raw(Address, Node, ClightStmt);
    relation clight_stmt_raw(Node, ClightStmt);
    relation clight_succ(Node, Node);
    relation clight_var_read(Address, Ident);
    relation clight_var_write(Address, Ident);
    relation efield_to_struct(Node, i64, i64, Ident, MemoryChunk);
    relation eligible_node_for_sseq(Node);
    relation emit_clight_stmt(Address, Node, ClightStmt);
    relation emit_goto_target(Address, Node);
    relation emit_next(Node, Node);
    lattice clight_function_owners(Node, Set<Address>);
    relation clight_targeted_nop_owner(Address, Node);
    relation emit_struct_fields(Address, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>);
    relation linear_succ_sseq(Node, Node);
    relation node_nonempty(Node);
    relation sseq_has_pred(Node);
    relation sseq_head(Node);
    relation valid_next(Node);

    // Data lookup tables: each (mov_addr, table_base, entry_count, entry_scale, index_reg_str) recovered by the disassembly pass, with values stored in data_lookup_table_value. Used to lift a clang-style table-load `mov disp(,%idx,scale), %dst` into a Sswitch.
    relation data_lookup_table(Node, u64, usize, i64, &'static str);
    relation data_lookup_table_value(Node, usize, i64);

    // Closed-form switches: clang -O1 collapses dense switches into arithmetic + cmov. ClosedFormSwitchPass (analysis layer) emits closed_form_switch / closed_form_switch_case at the csharp_stmt level; the rule below lowers them to Sswitch.
    relation closed_form_switch(Node, RTLReg, RTLReg, bool, i64);
    relation closed_form_switch_case(Node, i64, i64);

    // Gate: nodes whose Sset we will replace with a Sswitch (data lookup or closed-form).
    relation data_lookup_node(Node);
    data_lookup_node(node) <-- data_lookup_table(node, _, _, _, _);
    data_lookup_node(node) <-- closed_form_switch(node, _, _, _, _);

    // A register carrying a float candidate; used to suppress the truncating dst = (int)<float> Sset arm that the Z3 selector cannot veto, since int<->float casts are class-silent.
    relation reg_float_candidate(RTLReg);
    reg_float_candidate(*reg) <--
        emit_var_type_candidate(reg, xt),
        if matches!(xt, XType::Xfloat | XType::Xsingle);

    // Definition-local direct-global-load candidates carry the authoritative
    // object declaration type on Evar. Do not feed that type into
    // emit_var_type_candidate(dst, ...): RTL registers are reused across a
    // function, so one object load is not evidence that every lifetime of dst
    // is a pointer. The strict selector can combine this uncast statement with
    // the destination's independently recovered int/long declaration.
    clight_stmt(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        if let CsharpminorExpr::Eload(_, addr) = expr,
        if let CsharpminorExpr::Econst(Constant::Oaddrsymbol(ident, ofs)) = addr.as_ref(),
        if *ofs == 0,
        let global_addr = *ident as Address,
        global_symbol(global_addr, raw_name),
        known_global_type(known_name, global_type),
        if raw_name.split('@').next().unwrap_or(raw_name) == *known_name,
        let stmt = ClightStmt::Sset(
            ident_from_reg(*dst),
            ClightExpr::Evar(*ident, clight_type_from_xtype(global_type)),
        );

    // Header-only object types (notably environ/__environ: char **) have the
    // emitter's highest declaration precedence but no ABI XType fact. Mirror
    // that same shared parser in a definition-local candidate.
    clight_stmt(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        if let CsharpminorExpr::Eload(_, addr) = expr,
        if let CsharpminorExpr::Econst(Constant::Oaddrsymbol(ident, ofs)) = addr.as_ref(),
        if *ofs == 0,
        let global_addr = *ident as Address,
        global_symbol(global_addr, raw_name),
        if let Some(global_type) = header_global_clight_type(raw_name),
        let stmt = ClightStmt::Sset(
            ident_from_reg(*dst),
            ClightExpr::Evar(*ident, global_type),
        );

    // Recovered global declarations are just as authoritative as ABI-known
    // ones. Both generic and char-pointer statements may be candidates; the
    // exact audit sees the emitter-matching char* declaration and ranks it.
    clight_stmt(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        if let CsharpminorExpr::Eload(_, addr) = expr,
        if let CsharpminorExpr::Econst(Constant::Oaddrsymbol(ident, ofs)) = addr.as_ref(),
        if *ofs == 0,
        let global_addr = *ident as Address,
        global_symbol(global_addr, _),
        emit_global_is_ptr(*ident),
        let stmt = ClightStmt::Sset(
            ident_from_reg(*dst),
            ClightExpr::Evar(*ident, clight_type_from_xtype(&XType::Xptr)),
        );

    clight_stmt(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        if let CsharpminorExpr::Eload(_, addr) = expr,
        if let CsharpminorExpr::Econst(Constant::Oaddrsymbol(ident, ofs)) = addr.as_ref(),
        if *ofs == 0,
        let global_addr = *ident as Address,
        global_symbol(global_addr, _),
        emit_global_is_char_ptr(*ident),
        let stmt = ClightStmt::Sset(
            ident_from_reg(*dst),
            ClightExpr::Evar(*ident, clight_type_from_xtype(&XType::Xcharptr)),
        );

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


    // collect_all_var_types aggregates the whole emit_var_type_candidate relation and does not depend on any node, so materialize it once here instead of recomputing it inside every per-statement rule below.
    all_var_types_global(Arc::new(pairs)) <--
        agg pairs = collect_all_var_types(reg, xty) in emit_var_type_candidate(reg, xty);

    // Integer-register-to-float instructions consume bits, not a C scalar
    // category.  If the same value is also proven pointer-shaped (for example
    // by a dereference), the direct spelling `(double)p` is invalid C.  Add a
    // monotone alternative that makes the machine's integer interpretation
    // explicit: `(double)(long)p` (or the operation's exact integer width and
    // signedness).  The conversion may be nested after copy folding -- for
    // example as one operand of a comparison whose destination is boolean --
    // so gate on the expression tree, not on the destination's type. Numeric
    // source variants remain byte-for-byte unchanged, and the helper returns
    // None unless bridge mode actually changed the expression.
    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        if csharp_expr_has_integer_float_conversion(expr),
        if !matches!(expr, CsharpminorExpr::Econdition(_, _, _)),
        !data_lookup_node(node),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]),
        let var_type_variants = build_var_type_map_variants(all_var_types, &vars_used),
        for var_types in var_type_variants.iter(),
        if let Some(bridged_expr) = clight_expr_from_csharp_with_integer_float_bridge(
            &expr,
            var_types,
            *ptr_size,
        ),
        let stmt = ClightStmt::Sset(ident_from_reg(*dst), bridged_expr);

    clight_stmt_raw(node, stmt) <--
        clight_stmt(node, s),
        if let Some(stmt) = check_clight_stmt(s);

    // Statement-level cmov: lift `Sset(dst, Econdition(cond,t,f))` to `Sifthenelse(cond, Sset(dst,t), Sset(dst,f))` so tests matching `if (...)...else...` succeed instead of seeing a ternary.
    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        if let CsharpminorExpr::Econdition(cond, true_val, false_val) = expr,
        !data_lookup_node(node),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_csharp_exprs(&[(**cond).clone(), (**true_val).clone(), (**false_val).clone()]),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &vars_used),
        let cond_clight = clight_expr_from_csharp_with_multi_types(cond, &var_types, *ptr_size),
        let true_clight = clight_expr_from_csharp_with_multi_types(true_val, &var_types, *ptr_size),
        let false_clight = clight_expr_from_csharp_with_multi_types(false_val, &var_types, *ptr_size),
        let dst_ident = ident_from_reg(*dst),
        let then_stmt = ClightStmt::Sset(dst_ident, true_clight),
        let else_stmt = ClightStmt::Sset(dst_ident, false_clight),
        let stmt = ClightStmt::Sifthenelse(cond_clight, Box::new(then_stmt), Box::new(else_stmt));

    // Data lookup table: rewrite a table load as a Sswitch assigning the known constant table[k] per case, recovering the dense switch clang -O1 collapsed into a constant table load.
    clight_stmt(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        data_lookup_table(node, _table_base, _entry_count, entry_scale, _idx_reg),
        if let CsharpminorExpr::Eload(_chunk, addr_expr) = expr,
        if let Some(idx_reg) = data_lookup_extract_index(addr_expr),
        all_var_types_global(all_var_types),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &[idx_reg]),
        let discr_expr = ClightExpr::Etempvar(
            ident_from_reg(idx_reg),
            var_types.get(&idx_reg).map(|types| select_type_from_candidates(types, None)).unwrap_or_else(default_int_type),
        ),
        let dst_ident = ident_from_reg(*dst),
        agg cases_sorted = collect_data_lookup_values(idx, val) in data_lookup_table_value(node, idx, val),
        if !cases_sorted.is_empty(),
        let table = build_data_lookup_switch_cases(&cases_sorted, dst_ident, *entry_scale),
        let stmt = ClightStmt::Sswitch(discr_expr.clone(), table);

    // Closed-form switch: at `node` the Sset writes the cmov/closed-form value to dst_reg. Replace with Sswitch on disc_reg using cases from ClosedFormSwitchPass.
    clight_stmt(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sset(_, _)),
        closed_form_switch(node, disc_reg, dst_reg, has_default, default_val),
        all_var_types_global(all_var_types),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &[*disc_reg, *dst_reg]),
        let discr_expr = ClightExpr::Etempvar(
            ident_from_reg(*disc_reg),
            var_types.get(disc_reg).map(|types| select_type_from_candidates(types, None)).unwrap_or_else(default_int_type),
        ),
        let dst_ident = ident_from_reg(*dst_reg),
        let dst_ty = var_types.get(dst_reg).map(|types| select_type_from_candidates(types, None)).unwrap_or_else(default_int_type),
        agg cases_sorted = collect_data_lookup_values_i64(case_idx, case_val) in closed_form_switch_case(node, case_idx, case_val),
        if !cases_sorted.is_empty(),
        let table = build_closed_form_switch_cases(&cases_sorted, dst_ident, *has_default, *default_val, &dst_ty),
        let stmt = ClightStmt::Sswitch(discr_expr.clone(), table);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        is_ptr(dst),
        if !matches!(expr, CsharpminorExpr::Econdition(_, _, _)),
        !data_lookup_node(node),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]),
        let var_type_variants = build_var_type_map_variants(all_var_types, &vars_used),
        for var_types in var_type_variants.iter(),
        let out_expr = clight_expr_from_csharp_with_multi_types(&expr, var_types, *ptr_size),
        let dst_ident = ident_from_reg(*dst),
        let target_ty = pointer_to(default_int_type()),
        let casted_expr = rewrite_deref_for_pointer_dest(out_expr, target_ty),
        let stmt = ClightStmt::Sset(dst_ident, casted_expr);

    // Sset whose destination has NO float candidate: emit a cast-to-candidate arm for every integer/pointer candidate.
    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        emit_var_type_candidate(*dst, dst_xtype),
        !reg_float_candidate(dst),
        if !matches!(expr, CsharpminorExpr::Econdition(_, _, _)),
        !data_lookup_node(node),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]),
        let var_type_variants = build_var_type_map_variants(all_var_types, &vars_used),
        for var_types in var_type_variants.iter(),
        let out_expr = clight_expr_from_csharp_with_multi_types(&expr, var_types, *ptr_size),
        let dst_ident = ident_from_reg(*dst),
        let target_ty = clight_type_from_xtype(&dst_xtype),
        let casted_expr = cast_expr_to_type(out_expr, target_ty),
        let stmt = ClightStmt::Sset(dst_ident, casted_expr);

    // Sset whose destination HAS a float candidate: drop the float->int truncating arm, since the int candidate is a stray sibling and the selector cannot veto the truncation.
    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        emit_var_type_candidate(*dst, dst_xtype),
        reg_float_candidate(dst),
        if !matches!(expr, CsharpminorExpr::Econdition(_, _, _)),
        !data_lookup_node(node),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]),
        let var_type_variants = build_var_type_map_variants(all_var_types, &vars_used),
        for var_types in var_type_variants.iter(),
        let out_expr = clight_expr_from_csharp_with_multi_types(&expr, var_types, *ptr_size),
        let dst_ident = ident_from_reg(*dst),
        let target_ty = clight_type_from_xtype(&dst_xtype),
        if !(is_integral_type(&target_ty)
             && matches!(clight_expr_type(&out_expr), ClightType::Tfloat(_, _))),
        let casted_expr = cast_expr_to_type(out_expr, target_ty),
        let stmt = ClightStmt::Sset(dst_ident, casted_expr);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        !is_ptr(dst),
        !emit_var_type_candidate(*dst, _),
        if !matches!(expr, CsharpminorExpr::Econdition(_, _, _)),
        !data_lookup_node(node),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]),
        let var_type_variants = build_var_type_map_variants(all_var_types, &vars_used),
        for var_types in var_type_variants.iter(),
        let out_expr = clight_expr_from_csharp_with_multi_types(&expr, var_types, *ptr_size),
        let dst_ident = ident_from_reg(*dst),
        let target_ty = clight_expr_type(&out_expr),
        let casted_expr = cast_expr_to_type(out_expr, target_ty),
        let stmt = ClightStmt::Sset(dst_ident, casted_expr);

    // When dst has no type candidates, emit a long-cast variant to prevent ptr-to-int conversion errors.
    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Sset(dst, expr)),
        !is_ptr(dst),
        !emit_var_type_candidate(*dst, _),
        if !matches!(expr, CsharpminorExpr::Econdition(_, _, _)),
        !data_lookup_node(node),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]),
        let var_type_variants = build_var_type_map_variants(all_var_types, &vars_used),
        for var_types in var_type_variants.iter(),
        let out_expr = clight_expr_from_csharp_with_multi_types(&expr, var_types, *ptr_size),
        let dst_ident = ident_from_reg(*dst),
        let long_expr = cast_expr_to_type(out_expr, default_long_type()),
        let stmt = ClightStmt::Sset(dst_ident, long_expr);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Sstore(chunk, addr, value)),
        sstore_clight_type(node, ty),
        all_var_types_global(all_var_types),
        let mut all_exprs = vec![addr.clone()],
        let _ = all_exprs.push(value.clone()),
        let vars_used = extract_vars_from_csharp_exprs(&all_exprs),
        let var_type_variants = build_var_type_map_variants(all_var_types, &vars_used),
        for var_types in var_type_variants.iter(),
        let addr_expr = clight_expr_from_csharp_with_multi_types(&addr, var_types, *ptr_size),
        if !matches!(addr_expr, ClightExpr::EconstInt(0, _) | ClightExpr::EconstLong(0, _)),
        let pointer_ty = pointer_to(ty.clone()),
        let lhs_addr = rewrite_expr_as_pointer(addr_expr.clone(), pointer_ty, *ptr_size),
        if !matches!(&lhs_addr, ClightExpr::Ecast(inner, _) if matches!(inner.as_ref(), ClightExpr::EconstInt(0, _) | ClightExpr::EconstLong(0, _))),
        let lhs = ClightExpr::Ederef(Box::new(lhs_addr), ty.clone()),
        let rhs = clight_expr_from_csharp_with_multi_types(&value, var_types, *ptr_size),
        let rhs_casted = cast_expr_to_type(rhs, ty.clone()),
        let stmt = ClightStmt::Sassign(lhs.clone(), rhs_casted.clone());

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Left(expr), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        emit_function_return(func_addr, ret_reg),
        all_var_types_global(all_var_types),
        let mut all_exprs = vec![expr.clone()],
        let _ = all_exprs.extend_from_slice(args.as_slice()),
        let vars_used = extract_vars_from_csharp_exprs(&all_exprs),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &vars_used),
        let dst_ident = Some(ident_from_reg(*ret_reg)),
        let ret_ident = ident_from_reg(*ret_reg),
        let raw_func_expr = clight_expr_from_csharp_with_multi_types(&expr, &var_types, *ptr_size),
        let crude_sig = resolve_signature(&sig),
        let resolved_sig = refine_indirect_call_signature(&crude_sig, args.as_slice(), all_var_types, &None),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Ecast(Box::new(raw_func_expr.clone()), func_ty.clone()),
        let raw_args = clight_exprs_from_csharp_with_multi_types(args.as_slice(), &var_types, *ptr_size),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(dst_ident, func_expr, call_args),
        let ret_expr = ClightExpr::Etempvar(ret_ident, default_int_type()),
        let ret_stmt = ClightStmt::Sreturn(Some(ret_expr)),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Right(Either::Left(addr)), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        emit_function_return(func_addr, ret_reg),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_csharp_exprs(args.as_slice()),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &vars_used),
        let dst_ident = Some(ident_from_reg(*ret_reg)),
        let ret_ident = ident_from_reg(*ret_reg),
        addr_to_func_ident(addr, func_ident),
        let resolved_sig = resolve_signature(&sig),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Evar(*func_ident, func_ty.clone()),
        let raw_args = clight_exprs_from_csharp_with_multi_types(args.as_slice(), &var_types, *ptr_size),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(dst_ident, func_expr, call_args),
        let ret_expr = ClightExpr::Etempvar(ret_ident, default_int_type()),
        let ret_stmt = ClightStmt::Sreturn(Some(ret_expr)),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
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
        let raw_args = clight_exprs_from_csharp(args.as_slice(), *ptr_size),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(dst_ident, func_expr, call_args),
        let ret_expr = ClightExpr::Etempvar(ret_ident, default_int_type()),
        let ret_stmt = ClightStmt::Sreturn(Some(ret_expr)),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Left(expr), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        emit_function_void(func_addr),
        all_var_types_global(all_var_types),
        let raw_func_expr = clight_expr_from_csharp(&expr, *ptr_size),
        let crude_sig = resolve_signature(&sig),
        let resolved_sig = refine_indirect_call_signature(&crude_sig, args.as_slice(), all_var_types, &None),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Ecast(Box::new(raw_func_expr.clone()), func_ty.clone()),
        let raw_args = clight_exprs_from_csharp(args.as_slice(), *ptr_size),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(None, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(None),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Right(Either::Left(addr)), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        emit_function_void(func_addr),
        addr_to_func_ident(addr, func_ident),
        let resolved_sig = resolve_signature(&sig),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Evar(*func_ident, func_ty.clone()),
        let raw_args = clight_exprs_from_csharp(args.as_slice(), *ptr_size),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(None, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(None),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Right(Either::Left(addr)), args)),
        !addr_to_func_ident(addr, _),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        emit_function_void(func_addr),
        let func_ident = *addr as Ident,
        let resolved_sig = resolve_signature(&sig),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Evar(func_ident, func_ty.clone()),
        let raw_args = clight_exprs_from_csharp(args.as_slice(), *ptr_size),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(None, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(None),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Right(Either::Right(sym)), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        emit_function_return(func_addr, ret_reg),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_csharp_exprs(args.as_slice()),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &vars_used),
        let dst_ident = Some(ident_from_reg(*ret_reg)),
        let ret_ident = ident_from_reg(*ret_reg),
        let resolved_sig = resolve_signature(&sig),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::EvarSymbol(sym.to_string(), func_ty.clone()),
        let raw_args = clight_exprs_from_csharp_with_multi_types(args.as_slice(), &var_types, *ptr_size),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(dst_ident, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(Some(ClightExpr::Etempvar(ret_ident, default_int_type()))),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Right(Either::Right(sym)), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        emit_function_void(func_addr),
        let resolved_sig = resolve_signature(&sig),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::EvarSymbol(sym.to_string(), func_ty.clone()),
        let raw_args = clight_exprs_from_csharp(args.as_slice(), *ptr_size),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(None, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(None),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Left(expr), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        !emit_function_return(func_addr, _),
        !emit_function_void(func_addr),
        all_var_types_global(all_var_types),
        let raw_func_expr = clight_expr_from_csharp(&expr, *ptr_size),
        let crude_sig = resolve_signature(&sig),
        let resolved_sig = refine_indirect_call_signature(&crude_sig, args.as_slice(), all_var_types, &None),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Ecast(Box::new(raw_func_expr), func_ty),
        let raw_args = clight_exprs_from_csharp(args.as_slice(), *ptr_size),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(None, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(None),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Right(Either::Left(addr)), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        !emit_function_return(func_addr, _),
        !emit_function_void(func_addr),
        addr_to_func_ident(addr, func_ident),
        let resolved_sig = resolve_signature(&sig),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Evar(*func_ident, func_ty),
        let raw_args = clight_exprs_from_csharp(args.as_slice(), *ptr_size),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(None, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(None),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
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
        let raw_args = clight_exprs_from_csharp(args.as_slice(), *ptr_size),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(None, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(None),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Stailcall(sig, Either::Right(Either::Right(sym)), args)),
        instr_in_function(node, func_addr),
        emit_function(func_addr, _, _),
        !emit_function_return(func_addr, _),
        !emit_function_void(func_addr),
        let resolved_sig = resolve_signature(&sig),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::EvarSymbol(sym.to_string(), func_ty),
        let raw_args = clight_exprs_from_csharp(args.as_slice(), *ptr_size),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let call_stmt = ClightStmt::Scall(None, func_expr, call_args),
        let ret_stmt = ClightStmt::Sreturn(None),
        let stmt = ClightStmt::Ssequence(vec![call_stmt, ret_stmt]);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Scall(dst, sig, Either::Left(expr), args)),
        all_var_types_global(all_var_types),
        let mut all_exprs = vec![expr.clone()],
        let _ = all_exprs.extend_from_slice(args.as_slice()),
        let vars_used = extract_vars_from_csharp_exprs(&all_exprs),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &vars_used),
        let crude_sig = resolve_signature(&sig),
        let resolved_sig = refine_indirect_call_signature(&crude_sig, args.as_slice(), all_var_types, dst),
        let dst_ident = if resolved_sig.sig_res == XType::Xvoid { None } else { dst.clone().map(ident_from_reg) },
        let raw_func_expr = clight_expr_from_csharp_with_multi_types(&expr, &var_types, *ptr_size),
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Ecast(Box::new(raw_func_expr.clone()), func_ty.clone()),
        let raw_args = clight_exprs_from_csharp_with_multi_types(args.as_slice(), &var_types, *ptr_size),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let stmt = ClightStmt::Scall(dst_ident, func_expr, call_args);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Scall(dst, sig, Either::Right(Either::Left(addr)), args)),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_csharp_exprs(args.as_slice()),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &vars_used),
        addr_to_func_ident(addr, func_ident),
        let resolved_sig = resolve_signature(&sig),
        let dst_ident = if resolved_sig.sig_res == XType::Xvoid { None } else { dst.clone().map(ident_from_reg) },
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Evar(*func_ident, func_ty.clone()),
        let raw_args = clight_exprs_from_csharp_with_multi_types(args.as_slice(), &var_types, *ptr_size),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let stmt = ClightStmt::Scall(dst_ident, func_expr, call_args);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Scall(dst, sig, Either::Right(Either::Left(addr)), args)),
        !addr_to_func_ident(addr, _),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_csharp_exprs(args.as_slice()),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &vars_used),
        let func_ident = *addr as Ident,
        let resolved_sig = resolve_signature(&sig),
        let dst_ident = if resolved_sig.sig_res == XType::Xvoid { None } else { dst.clone().map(ident_from_reg) },
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::Evar(func_ident, func_ty.clone()),
        let raw_args = clight_exprs_from_csharp_with_multi_types(args.as_slice(), &var_types, *ptr_size),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let stmt = ClightStmt::Scall(dst_ident, func_expr, call_args);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Scall(dst, sig, Either::Right(Either::Right(sym)), args)),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_csharp_exprs(args.as_slice()),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &vars_used),
        let resolved_sig = resolve_signature(&sig),
        let dst_ident = if resolved_sig.sig_res == XType::Xvoid { None } else { dst.clone().map(ident_from_reg) },
        let func_ty = clight_function_pointer_type(&resolved_sig),
        let func_expr = ClightExpr::EvarSymbol(sym.to_string(), func_ty.clone()),
        let raw_args = clight_exprs_from_csharp_with_multi_types(args.as_slice(), &var_types, *ptr_size),
        let call_args = cast_call_args_to_signature_with_node(raw_args, &sig),
        let stmt = ClightStmt::Scall(dst_ident, func_expr, call_args);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Sbuiltin(dst, name, args, res)),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_builtin_args(&args),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &vars_used),
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
        let converted_args = clight_builtin_args_with_multi_types(&effective_args_init, &var_types, *ptr_size),
        let stmt = ClightStmt::Scall(effective_dst, ClightExpr::EvarSymbol(effective_name, default_void_ptr_type()), converted_args);

    // Goto-chain threading: a forwarding block is a node whose whole statement is a lone unconditional jump, excluding entry/loop/switch anchors.
    #[local] relation fwd(Node, Node);
    fwd(*node, *target) <--
        csharp_stmt(node, ?CsharpminorStmt::Sjump(target)),
        if *node != *target,
        !func_entry_node(_, node),
        !emit_loop_body(_, node, _),
        !emit_switch_chain(_, node, _);

    // Resolve each forwarding chain to its terminal target; a purely cyclic chain has no terminal and yields no fact, so it is left intact.
    #[local] relation goto_chain_end(Node, Node);
    goto_chain_end(*n, *f) <-- fwd(n, f), !fwd(f, _);
    goto_chain_end(*n, *f) <-- fwd(n, m), goto_chain_end(m, f);

    // Every node used as a branch/jump destination, so final_goto is total over the targets we thread on.
    #[local] relation goto_dst(Node);
    goto_dst(*a) <-- csharp_stmt(_, ?CsharpminorStmt::Scond(_, _, a, _));
    goto_dst(*b) <-- csharp_stmt(_, ?CsharpminorStmt::Scond(_, _, _, b));
    goto_dst(*t) <-- csharp_stmt(_, ?CsharpminorStmt::Sjump(t));

    // final_goto(orig, dst): single-valued, total over goto_dst; the chain end if orig forwards, else orig itself.
    #[local] relation final_goto(Node, Node);
    final_goto(*n, *f) <-- goto_chain_end(n, f);
    final_goto(*n, *n) <-- goto_dst(n), !goto_chain_end(n, _);

    // Flat Scond (not lifted by structuring_pass): convert to Sifthenelse with gotos threaded to their chain ends
    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Scond(cond, exprs, ifso, ifnot)),
        !valid_switch_chain(_, node, _),
        !valid_ternary(_, node, _, _, _, _),
        final_goto(ifso, ifso_final),
        final_goto(ifnot, ifnot_final),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_csharp_exprs(exprs.as_slice()),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &vars_used),
        let condition_opt = crate::decompile::passes::clight_pass::clight_condition_expr_with_types(&cond, exprs.as_slice(), &var_types, *ptr_size),
        if let Some(condition) = condition_opt,
        let then_stmt = ClightStmt::Sgoto(ident_from_node(*ifso_final)),
        let else_stmt = ClightStmt::Sgoto(ident_from_node(*ifnot_final)),
        let stmt = ClightStmt::Sifthenelse(condition.clone(), Box::new(then_stmt), Box::new(else_stmt));

    // Compound Sifthenelse (lifted by structuring_pass): recursively convert bodies
    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Sifthenelse(cond, args, then_body, else_body)),
        all_var_types_global(all_var_types),
        agg func_syms = collect_func_symbols(ident, sym) in ident_to_symbol(ident, sym),
        let vars_used = extract_vars_from_csharp_exprs(args.as_slice()),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &vars_used),
        if let Some(condition) = crate::decompile::passes::clight_pass::clight_condition_expr_with_types(&cond, args.as_slice(), &var_types, *ptr_size),
        let then_clight = crate::decompile::passes::clight_pass::convert_csharp_stmt_to_clight(then_body, all_var_types, &func_syms, *ptr_size),
        let else_clight = crate::decompile::passes::clight_pass::convert_csharp_stmt_to_clight(else_body, all_var_types, &func_syms, *ptr_size),
        let stmt = ClightStmt::Sifthenelse(condition, Box::new(then_clight), Box::new(else_clight));

    // Top-level Sseq node (tail_dup_pass's duplicated cross-jump tail): convert each member into a flat sequence, with no instr_in_function gate since synthetic nodes are absent from it.
    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Sseq(stmts)),
        all_var_types_global(all_var_types),
        agg func_syms = collect_func_symbols(ident, sym) in ident_to_symbol(ident, sym),
        let stmt = ClightStmt::Ssequence(
            stmts.iter()
                .map(|s| crate::decompile::passes::clight_pass::convert_csharp_stmt_to_clight(s, all_var_types, &func_syms, *ptr_size))
                .collect::<Vec<_>>()
        );

    clight_stmt(head, stmt) <--
        valid_switch_chain(func, head, reg),
        agg cases = collect_switch_cases(val, target) in switch_chain_member(func, head, _, reg, val, target),
        all_var_types_global(all_var_types),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &[ *reg ]),
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

    clight_stmt(branch, stmt) <--
        abi_pointer_size(ptr_size),
        valid_ternary(func, branch, var, true_expr, false_expr, _merge),
        csharp_stmt(branch, ?CsharpminorStmt::Scond(cond, args, _, _)),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_csharp_exprs(&[true_expr.clone(), false_expr.clone()]),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &vars_used),
        let condition_opt = crate::decompile::passes::clight_pass::clight_condition_expr_with_types(&cond, args.as_slice(), &var_types, *ptr_size),
        if let Some(condition) = condition_opt,
        let true_clight = clight_expr_from_csharp_with_multi_types(&true_expr, &var_types, *ptr_size),
        let false_clight = clight_expr_from_csharp_with_multi_types(&false_expr, &var_types, *ptr_size),
        let var_ident = ident_from_reg(*var),
        let then_stmt = ClightStmt::Sset(var_ident, true_clight),
        let else_stmt = ClightStmt::Sset(var_ident, false_clight),
        let stmt = ClightStmt::Sifthenelse(condition, Box::new(then_stmt), Box::new(else_stmt));


    // CF-6 duplicate-dispatch suppression, node-keyed and edge-aware: a member is subsumed only when every inbound edge comes from the head or another subsumed member, or the external edge dangles.
    #[local] relation chain_member_node(Address, Node, Node);
    chain_member_node(func, head, node) <--
        valid_switch_chain(func, head, _),
        switch_chain_member(func, head, node, _, _, _),
        if *node != *head;

    #[local] relation chain_node(Address, Node, Node);
    chain_node(func, head, head) <-- valid_switch_chain(func, head, _);
    chain_node(func, head, m) <-- chain_member_node(func, head, m);

    #[local] relation chain_member_tainted(Address, Node, Node);
    chain_member_tainted(func, head, m) <--
        chain_member_node(func, head, m),
        cminor_succ(p, m),
        !chain_node(func, head, p);
    chain_member_tainted(func, head, m) <--
        chain_member_node(func, head, m),
        cminor_succ(p, m),
        chain_member_tainted(func, head, p);

    #[local] relation clight_node_dead(Address, Node);
    clight_node_dead(func, node) <--
        chain_member_node(func, head, node),
        !chain_member_tainted(func, head, node);
    clight_node_dead(addr, node) <--
        clight_stmt_dead(addr, node, _);

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Sjumptable(expr, targets)),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &vars_used),
        let discr = clight_expr_from_csharp_with_multi_types(&expr, &var_types, *ptr_size),
        let table = {
            let mut entries = Vec::new();
            for (idx, target) in targets.iter().enumerate() {
                let goto_stmt = ClightStmt::Sgoto(ident_from_node(*target));
                entries.push((Some(idx as Z), goto_stmt));
            }
            entries
        },
        let stmt = ClightStmt::Sswitch(discr.clone(), table);

    clight_stmt(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sjump(target)),
        if *node != *target,
        final_goto(target, target_final),
        let stmt = ClightStmt::Sgoto(ident_from_node(*target_final));

    clight_stmt(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sjump(target)),
        if *node == *target,
        let stmt = ClightStmt::Sskip;

    clight_stmt(node, stmt) <--
        abi_pointer_size(ptr_size),
        csharp_stmt(node, ?CsharpminorStmt::Sreturn(result)),
        instr_in_function(node, func_addr),
        !emit_function_void(func_addr),
        all_var_types_global(all_var_types),
        let vars_used = extract_vars_from_csharp_exprs(&[result.clone()]),
        let var_types = filter_and_build_multi_var_type_map(all_var_types, &vars_used),
        let converted = clight_expr_from_csharp_with_multi_types(&result, &var_types, *ptr_size),
        let stmt = ClightStmt::Sreturn(Some(converted.clone()));

    // A return in a void function carries no value (e.g. deregister_tm_clones after the static tail is folded away): emit a bare `return;` so the result type stays void and no undefined return-value expression is materialized.
    clight_stmt(node, ClightStmt::Sreturn(None)) <--
        csharp_stmt(node, ?CsharpminorStmt::Sreturn(_)),
        instr_in_function(node, func_addr),
        emit_function_void(func_addr);

    // A no-op that is an explicit branch destination still owns its outgoing
    // CFG edge.  Materialize the edge when it is single-valued instead of
    // relying on the eventual C layout to put the successor immediately after
    // the label.  This is especially important after copy propagation turns a
    // return-register move into Snop: the return remains the structural
    // successor even when unrelated regions are laid out between the nodes.
    #[local] relation cminor_succ_fanout(Node);
    cminor_succ_fanout(*node) <--
        cminor_succ(node, a),
        cminor_succ(node, b),
        if a != b;

    #[local] relation targeted_nop_succ(Node, Node);
    targeted_nop_succ(*node, *succ) <--
        csharp_stmt(node, ?CsharpminorStmt::Snop),
        !mach_imm_stack_init(node, _, _, _),
        emit_goto_target(_, node),
        cminor_succ(node, succ),
        !cminor_succ_fanout(node);

    clight_stmt(node, stmt) <--
        targeted_nop_succ(node, succ),
        let stmt = ClightStmt::Sgoto(ident_from_node(*succ));

    clight_stmt(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Snop),
        !mach_imm_stack_init(node, _, _, _),
        !targeted_nop_succ(node, _),
        let stmt = ClightStmt::Sskip;

    // Structured control flow leaf variants; compound construction (Sloop, Sifthenelse) is deferred to the select phase.
    clight_stmt(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Sbreak),
        let stmt = ClightStmt::Sbreak;

    clight_stmt(node, stmt) <--
        csharp_stmt(node, ?CsharpminorStmt::Scontinue),
        let stmt = ClightStmt::Scontinue;

    #[local] relation exact_goto_edge(Address, Node, Node);
    exact_goto_edge(func, *src, *ifso) <--
        csharp_stmt(src, ?CsharpminorStmt::Scond(_, _, ifso, _)),
        instr_in_function(src, func);
    exact_goto_edge(func, *src, *ifnot) <--
        csharp_stmt(src, ?CsharpminorStmt::Scond(_, _, _, ifnot)),
        instr_in_function(src, func);
    exact_goto_edge(func, *src, *target) <--
        csharp_stmt(src, ?CsharpminorStmt::Sjump(target)),
        instr_in_function(src, func);
    exact_goto_edge(func, *src, *target) <--
        csharp_stmt(src, ?CsharpminorStmt::Sjumptable(_, targets)),
        instr_in_function(src, func),
        for target in targets.iter();

    emit_goto_target(func, target) <-- exact_goto_edge(func, _, target);

    // A recovered closed-form switch emits an explicit goto for every case,
    // even though those edges no longer come from one Csharpminor jump-table
    // statement. Register each structural case target just like an ordinary
    // branch target so loop assembly preserves its label and can inline the
    // selected case body instead of leaving a dangling empty label.
    emit_goto_target(*func, *target) <--
        switch_chain_member(func, _, _, _, _, target);

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

    // Resolve synthetic duplicated-tail nodes to their base address's function, or without a func owner their statement is dropped and the branch arm emits empty.
    clight_stmt_for_func_raw(addr, node, labeled_stmt) <--
        clight_stmt_raw(node, stmt),
        if (*node & ((1u64 << 62) | (1u64 << 63))) != 0,
        let base = *node & !((1u64 << 62) | (1u64 << 63)),
        instr_in_function(base, addr),
        if !matches!(stmt, ClightStmt::Slabel(_, _)),
        let labeled_stmt = ClightStmt::Slabel(ident_from_node(*node), Box::new(stmt.clone()));

    clight_stmt_for_func_raw(addr, node, stmt) <--
        clight_stmt_raw(node, stmt),
        if (*node & ((1u64 << 62) | (1u64 << 63))) != 0,
        let base = *node & !((1u64 << 62) | (1u64 << 63)),
        instr_in_function(base, addr),
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

    clight_stmt_dead(addr, node, stmt) <--
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



    emit_clight_stmt(addr, node, stmt) <--
        clight_stmt_for_func_raw(addr, node, stmt),
        !clight_node_dead(addr, node);


    eligible_node_for_sseq(node) <--
        clight_stmt(node, stmt),
        if is_groupable_stmt(stmt);

    // Build straight-line groups from the Clight-visible CFG rather than the
    // raw Cminor edge.  clight_succ structurally forwards across nodes whose
    // selected statement is empty, so register-only setup nodes do not split a
    // sequence of observable calls/assignments.  A forwarded edge is admitted
    // only when it is unambiguous at both ends: grouping across a fork or join
    // would make one path's statement execute on another path.
    #[local] relation clight_succ_forks(Node);
    clight_succ_forks(src) <--
        valid_next(src),
        clight_succ(src, dst1),
        clight_succ(src, dst2),
        if *dst1 != *dst2;

    #[local] relation clight_succ_joins(Node);
    clight_succ_joins(dst) <--
        clight_succ(src1, dst),
        clight_succ(src2, dst),
        valid_next(src1),
        valid_next(src2),
        valid_next(dst),
        if *src1 != *src2;

    linear_succ_sseq(n1, n2) <--
        clight_succ(n1, n2),
        valid_next(n1),
        valid_next(n2),
        eligible_node_for_sseq(n1),
        eligible_node_for_sseq(n2),
        code_in_block(n1, b),
        code_in_block(n2, b),
        !clight_succ_forks(n1),
        !clight_succ_joins(n2);

    sseq_has_pred(n2) <-- linear_succ_sseq(_, n2);

    sseq_head(n) <-- eligible_node_for_sseq(n), !sseq_has_pred(n);

    emit_clight_sseq(head, head) <-- sseq_head(head);
    emit_clight_sseq(head, next) <--
        emit_clight_sseq(head, curr),
        linear_succ_sseq(curr, next);
    emit_clight_sseq_edge(head, curr, next) <--
        emit_clight_sseq(head, curr),
        linear_succ_sseq(curr, next);


    node_nonempty(node) <--
        emit_clight_stmt(_, node, stmt),
        if is_nonempty_stmt(stmt);

    valid_next(node) <-- node_nonempty(node);
    // An exact branch/switch target is a control-flow anchor even when its own
    // selected statement is empty.  Forwarding through it would erase the
    // destination that the emitted goto must name.
    valid_next(node) <-- emit_goto_target(_, node);

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

    // A discovered function can start with parameter/register setup that is
    // intentionally absent from Cminor.  Cshminor resolves that raw entry to
    // the first active Cminor node; retain the structural entry edge here so
    // Clight ownership and final statement ordering can enter the recovered
    // body instead of leaving every semantic statement disconnected.
    emit_next(raw_entry, resolved_entry) <--
        emit_function(func, _, raw_entry),
        func_entry_node(func, resolved_entry),
        if raw_entry != resolved_entry;

    // Function membership at the semantic Clight CFG, after external calls and
    // PLT transfers have been lifted.  A node keeps every entry that can reach
    // it; the point-keyed Set lattice joins shared tails without materializing
    // an O(functions * nodes) pairwise reachability relation.  In particular,
    // machine-level lazy resolver paths that are no longer successors of a
    // lifted external call are not part of the recovered C function body.
    clight_function_owners(*entry, Set::singleton(*func)) <--
        emit_function(func, _, entry);
    // A no-op or selected-away node named by an exact branch remains a
    // function-local control anchor even though it has no data effect.  Keep
    // this provenance separate from semantic statement ownership: seeding the
    // lattice here would propagate through emit_next and admit downstream
    // regions that the compressed Clight CFG intentionally excludes.
    clight_targeted_nop_owner(*func, *target) <--
        exact_goto_edge(func, src, target),
        clight_function_owners(src, owners),
        if owners.0.contains(func);
    // Walk only through a transparent no-op prefix and include its first live
    // Cminor frontier.  The recursion cannot continue from a non-Snop node, so
    // this control slice does not become general function ownership.
    clight_targeted_nop_owner(*func, *dst) <--
        clight_targeted_nop_owner(func, src),
        csharp_stmt(src, ?CsharpminorStmt::Snop),
        cminor_succ(src, dst);
    clight_targeted_nop_owner(*func, *dst) <--
        clight_targeted_nop_owner(func, src),
        !has_csharp_stmt(src),
        emit_next(src, dst);
    clight_function_owners(*dst, owners.clone()) <--
        clight_function_owners(src, owners),
        emit_next(src, dst);

    #[local] relation has_cminor_stmt(Node);
    has_cminor_stmt(*node) <-- cminor_stmt(node, _);

    clight_succ(src, dst) <--
        next(src, dst),
        valid_next(src),
        valid_next(dst),
        !has_cminor_stmt(src);

    // A trimmed node whose control flow DIVERTS from address order must not have edges forwarded through it by adjacency, which would fabricate a successor the program does not have.
    #[local] relation diverts_from_next(Node);
    diverts_from_next(mid) <--
        cminor_succ(mid, t),
        next(mid, n),
        if *t != *n;

    #[local] relation next_clight(Node, Node);
    next_clight(mid, final_dst) <--
        next(mid, final_dst),
        !valid_next(mid),
        !diverts_from_next(mid),
        valid_next(final_dst);

    next_clight(mid, final_dst) <--
        next(mid, next_mid),
        !valid_next(mid),
        !diverts_from_next(mid),
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
        agg fields_raw = collect_unique_struct_fields(field_offset, field_name, chunk) in clight_efield_info(func_addr, _, base_offset, field_offset, field_name, chunk),
        let fields = segregate_overlapping_fields(&fields_raw);

    // NOTE: XstructPtr type candidates are emitted by ClightFieldPass using canonical struct IDs; emitting here would use register-based IDs causing "no member named" errors.


}

pub struct ClightPass;

impl IRPass for ClightPass {
    fn name(&self) -> &'static str {
        "clight"
    }

    fn run(&self, db: &mut DecompileDB) {
        run_pass!(db, ClightPassProgram);
        // Diagnostic (env-gated, like CF3_DUMP): print CFG edges touching one
        // masked instruction address, at the relations ownership flows over.
        if let Ok(want) = std::env::var("CF3_EDGE_DUMP") {
            if let Ok(addr) = u64::from_str_radix(want.trim_start_matches("0x"), 16) {
                let mask = !((1u64 << 62) | (1u64 << 63));
                for rel in ["emit_next", "cminor_succ", "rtl_succ", "clight_succ"] {
                    for (src, dst) in db.rel_iter::<(Node, Node)>(rel) {
                        if (*src & mask) == addr || (*dst & mask) == addr {
                            eprintln!("[EDGE-{rel}] {src:#x} -> {dst:#x}");
                        }
                    }
                }
            }
        }
    }

    declare_io_from!(ClightPassProgram);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn synthetic_ids<const N: usize>() -> [u64; N] {
        std::array::from_fn(|index| index as u64 + 1)
    }

    fn groupable_set(id: Ident, value: i32) -> ClightStmt {
        ClightStmt::Sset(id, ClightExpr::EconstInt(value, default_int_type()))
    }

    fn add_groupable_node(
        prog: &mut ClightPassProgram,
        func: Address,
        block: Address,
        node: Node,
        id: Ident,
    ) {
        let stmt = groupable_set(id, id as i32);
        prog.clight_stmt.push((node, stmt.clone()));
        prog.emit_clight_stmt.push((func, node, stmt));
        prog.code_in_block.push((node, block));
    }

    #[test]
    fn nested_integer_to_float_conversion_gets_pointer_bridge_candidate() {
        let node = 0x5ea6;
        let float_value = 0x8000_0000_005e_900f;
        let pointer_shaped_integer = 0x8000_0000_005e_9e03;
        let boolean_dst = 0x8000_0000_005e_a600;
        let expr = CsharpminorExpr::Ebinop(
            CminorBinop::Ocmpf(Comparison::Cgt),
            Box::new(CsharpminorExpr::Evar(float_value)),
            Box::new(CsharpminorExpr::Eunop(
                CminorUnop::Ofloatofint,
                Box::new(CsharpminorExpr::Evar(pointer_shaped_integer)),
            )),
        );
        let mut prog = ClightPassProgram::default();
        prog.abi_pointer_size.push((8,));
        prog.csharp_stmt
            .push((node, CsharpminorStmt::Sset(boolean_dst, expr)));
        prog.emit_var_type_candidate.extend([
            (float_value, XType::Xfloat),
            (pointer_shaped_integer, XType::Xcharptr),
            (boolean_dst, XType::Xint),
        ]);

        prog.run();

        assert!(
            prog.clight_stmt.iter().any(|(got_node, stmt)| {
                *got_node == node
                    && matches!(
                        stmt,
                        ClightStmt::Sset(
                            _,
                            ClightExpr::Ebinop(
                                ClightBinaryOp::Ogt,
                                _,
                                rhs,
                                _
                            )
                        ) if matches!(
                            rhs.as_ref(),
                            ClightExpr::Ecast(integer_bridge, ClightType::Tfloat(..))
                                if matches!(
                                    integer_bridge.as_ref(),
                                    ClightExpr::Ecast(_, ClightType::Tint(ClightIntSize::I32, ..))
                                )
                        )
                    )
            }),
            "a folded conversion inside a boolean comparison must retain its integer bridge"
        );
    }

    #[test]
    fn clight_function_ownership_is_cfg_structural_and_multivalued() {
        let mut prog = ClightPassProgram::default();
        let func_a = 0x9000;
        let func_b = 0x1000;
        let entry_a = 40;
        let entry_b = 900;
        let a_only = 7;
        let b_only = 901;
        let shared_tail = 3;
        let disconnected = 2;

        prog.emit_function.push((func_a, "FUN_A", entry_a));
        prog.emit_function.push((func_b, "FUN_B", entry_b));
        prog.emit_next.extend([
            (entry_a, a_only),
            (a_only, shared_tail),
            (entry_b, b_only),
            (b_only, shared_tail),
        ]);

        prog.run();

        let owners = |node| {
            prog.clight_function_owners
                .iter()
                .find_map(|entry| {
                    let fact = entry.read().unwrap();
                    (fact.0 == node).then_some(fact.1 .0.clone())
                })
                .unwrap_or_default()
        };
        assert_eq!(owners(entry_a), std::collections::BTreeSet::from([func_a]));
        assert_eq!(owners(a_only), std::collections::BTreeSet::from([func_a]));
        assert_eq!(owners(entry_b), std::collections::BTreeSet::from([func_b]));
        assert_eq!(owners(b_only), std::collections::BTreeSet::from([func_b]));
        assert_eq!(
            owners(shared_tail),
            std::collections::BTreeSet::from([func_a, func_b])
        );
        assert!(owners(disconnected).is_empty());
    }

    #[test]
    fn trimmed_function_entry_reaches_first_semantic_node() {
        let mut prog = ClightPassProgram::default();
        let func = 0x9000;
        let raw_entry = 0x9000;
        let semantic_entry = 0x9010;
        let tail = 0x9020;

        prog.emit_function.push((func, "FUN_9000", raw_entry));
        prog.func_entry_node.push((func, semantic_entry));
        prog.emit_next.push((semantic_entry, tail));

        prog.run();

        assert!(prog
            .emit_next
            .iter()
            .any(|fact| fact == &(raw_entry, semantic_entry)));

        let owners = |node| {
            prog.clight_function_owners
                .iter()
                .find_map(|entry| {
                    let fact = entry.read().unwrap();
                    (fact.0 == node).then_some(fact.1 .0.clone())
                })
                .unwrap_or_default()
        };
        assert_eq!(owners(raw_entry), std::collections::BTreeSet::from([func]));
        assert_eq!(
            owners(semantic_entry),
            std::collections::BTreeSet::from([func])
        );
        assert_eq!(owners(tail), std::collections::BTreeSet::from([func]));
    }

    #[test]
    fn exact_targeted_nop_has_nonpropagating_control_ownership() {
        let mut prog = ClightPassProgram::default();
        let func = 0x9000;
        let entry = 0x9000;
        let targeted_nop = 0x9010;
        let second_nop = 0x9020;
        let live_frontier = 0x9030;
        let beyond_frontier = 0x9040;
        let unowned_source = 0xa000;
        let unrelated_nop = 0xa010;

        prog.emit_function.push((func, "FUN_9000", entry));
        prog.csharp_stmt.extend([
            (entry, CsharpminorStmt::Sjump(targeted_nop)),
            (targeted_nop, CsharpminorStmt::Snop),
            (second_nop, CsharpminorStmt::Snop),
            (live_frontier, CsharpminorStmt::Sbreak),
            (beyond_frontier, CsharpminorStmt::Sbreak),
            (unowned_source, CsharpminorStmt::Sjump(unrelated_nop)),
            (unrelated_nop, CsharpminorStmt::Snop),
        ]);
        prog.instr_in_function
            .extend([(entry, func), (unowned_source, func)]);
        prog.cminor_succ.extend([
            (targeted_nop, second_nop),
            (second_nop, live_frontier),
            (live_frontier, beyond_frontier),
        ]);

        prog.run();

        assert!(prog
            .clight_targeted_nop_owner
            .iter()
            .any(|fact| fact == &(func, targeted_nop)));
        assert!(!prog
            .clight_targeted_nop_owner
            .iter()
            .any(|fact| fact == &(func, unrelated_nop)));
        assert!(prog
            .clight_targeted_nop_owner
            .iter()
            .any(|fact| fact == &(func, second_nop)));
        assert!(prog
            .clight_targeted_nop_owner
            .iter()
            .any(|fact| fact == &(func, live_frontier)));
        assert!(!prog
            .clight_targeted_nop_owner
            .iter()
            .any(|fact| fact == &(func, beyond_frontier)));

        let owners = |node| {
            prog.clight_function_owners
                .iter()
                .find_map(|entry| {
                    let fact = entry.read().unwrap();
                    (fact.0 == node).then_some(fact.1 .0.clone())
                })
                .unwrap_or_default()
        };
        assert_eq!(owners(entry), std::collections::BTreeSet::from([func]));
        assert!(owners(targeted_nop).is_empty());
        assert!(owners(unrelated_nop).is_empty());
    }

    #[test]
    fn sseq_bridges_empty_nodes_without_using_node_order() {
        let mut prog = ClightPassProgram::default();
        let func = 0x1000;
        let block = 0x1010;
        // Deliberately non-monotonic node IDs: structural CFG edges, not
        // address ordering, must determine the sequence.
        let head = 0x300;
        let empty = 0x100;
        let tail = 0x200;

        add_groupable_node(&mut prog, func, block, head, 1);
        add_groupable_node(&mut prog, func, block, tail, 2);
        prog.cminor_succ.push((head, empty));
        prog.cminor_succ.push((empty, tail));

        prog.run();

        assert!(prog.clight_succ.iter().any(|edge| edge == &(head, tail)));
        assert!(prog
            .linear_succ_sseq
            .iter()
            .any(|edge| edge == &(head, tail)));
        assert!(prog
            .emit_clight_sseq
            .iter()
            .any(|member| member == &(head, tail)));
        assert!(prog
            .emit_clight_sseq_edge
            .iter()
            .any(|edge| edge == &(head, head, tail)));
    }

    #[test]
    fn sseq_does_not_cross_forwarded_branch() {
        let mut prog = ClightPassProgram::default();
        let func = 0x1000;
        let block = 0x1010;
        let head = 0x500;
        let empty_branch = 0x100;
        let left = 0x400;
        let right = 0x200;

        add_groupable_node(&mut prog, func, block, head, 1);
        add_groupable_node(&mut prog, func, block, left, 2);
        add_groupable_node(&mut prog, func, block, right, 3);
        prog.cminor_succ.push((head, empty_branch));
        prog.cminor_succ.push((empty_branch, left));
        prog.cminor_succ.push((empty_branch, right));

        prog.run();

        assert!(prog.clight_succ.iter().any(|edge| edge == &(head, left)));
        assert!(prog.clight_succ.iter().any(|edge| edge == &(head, right)));
        assert!(!prog.linear_succ_sseq.iter().any(|(src, _)| *src == head));
    }

    #[test]
    fn sseq_does_not_cross_forwarded_join() {
        let mut prog = ClightPassProgram::default();
        let func = 0x1000;
        let block = 0x1010;
        let left = 0x500;
        let right = 0x200;
        let empty_join = 0x100;
        let tail = 0x400;

        add_groupable_node(&mut prog, func, block, left, 1);
        add_groupable_node(&mut prog, func, block, right, 2);
        add_groupable_node(&mut prog, func, block, tail, 3);
        prog.cminor_succ.push((left, empty_join));
        prog.cminor_succ.push((right, empty_join));
        prog.cminor_succ.push((empty_join, tail));

        prog.run();

        assert!(prog.clight_succ.iter().any(|edge| edge == &(left, tail)));
        assert!(prog.clight_succ.iter().any(|edge| edge == &(right, tail)));
        assert!(!prog.linear_succ_sseq.iter().any(|(_, dst)| *dst == tail));
    }

    #[test]
    fn opaque_escaped_slot_keeps_storage_up_to_the_frame_top() {
        let mut db = DecompileDB::default();
        let func: Address = 0x1000;
        let local: RTLReg = 0x8000_0000_0000_1234;
        db.rel_push("func_stacksz", (func, 0x1200_u64, "scratch", 280_u64));
        db.rel_push("slot_escaped_canonical", (func, 0_i64, local));

        size_opaque_escaped_frame_buffers(&mut db);

        assert_eq!(
            db.stack_struct_buffers
                .get(&func)
                .and_then(|buffers| buffers.get(&local)),
            Some(&280),
        );
    }

    #[test]
    fn indexed_prefix_and_address_taken_buffer_share_one_backing_object() {
        let mut db = DecompileDB::default();
        let func: Address = 0x2000;
        let lea_node: Node = 0x2010;
        let load_node: Node = 0x2020;
        let buffer_node: Node = 0x2030;
        let address_reg: RTLReg = 0x7100;
        let index_reg: RTLReg = 0x7200;
        let load_reg: RTLReg = 0x7300;
        let prefix_local: RTLReg = 0x8100;
        let buffer_local: RTLReg = 0x8200;

        db.rel_push("func_stacksz", (func, 0x2100_u64, "indexed", 64_u64));
        for node in [lea_node, load_node] {
            db.rel_push("instr_in_function", (node, func));
        }
        db.rel_push(
            "rtl_inst",
            (
                lea_node,
                RTLInst::Iop(
                    Operation::Olea(Addressing::Ainstack(15)),
                    Arc::new(Vec::new()),
                    address_reg,
                ),
            ),
        );
        db.rel_push(
            "rtl_inst",
            (
                load_node,
                RTLInst::Iload(
                    MemoryChunk::MInt8Unsigned,
                    Addressing::Aindexed2(0),
                    Arc::new(vec![address_reg, index_reg]),
                    load_reg,
                ),
            ),
        );
        db.rel_push("stack_var", (func, lea_node, 15_i64, prefix_local));
        db.rel_push("stack_var", (func, buffer_node, 16_i64, buffer_local));
        db.stack_struct_buffers
            .entry(func)
            .or_default()
            .insert(buffer_local, 48);

        size_indexed_stack_arrays(&mut db);

        assert_eq!(
            db.stack_struct_buffers
                .get(&func)
                .and_then(|buffers| buffers.get(&prefix_local)),
            Some(&49),
        );
        assert!(!db
            .stack_struct_buffers
            .get(&func)
            .is_some_and(|buffers| buffers.contains_key(&buffer_local)));
        assert!(!db
            .stack_array_buffers
            .get(&func)
            .is_some_and(|arrays| arrays.contains_key(&prefix_local)));
        assert!(db
            .rel_iter::<(Address, RTLReg, RTLReg, usize)>("stack_buffer_alias")
            .any(|alias| alias == &(func, buffer_local, prefix_local, 1)));
    }

    #[test]
    fn directly_accessed_prefix_is_not_folded_into_a_buffer() {
        let mut db = DecompileDB::default();
        let func: Address = 0x3000;
        let lea_node: Node = 0x3010;
        let load_node: Node = 0x3020;
        let buffer_node: Node = 0x3030;
        let address_reg: RTLReg = 0x9100;
        let prefix_local: RTLReg = 0xa100;
        let buffer_local: RTLReg = 0xa200;

        db.rel_push("func_stacksz", (func, 0x3100_u64, "indexed", 64_u64));
        for node in [lea_node, load_node] {
            db.rel_push("instr_in_function", (node, func));
        }
        db.rel_push(
            "rtl_inst",
            (
                lea_node,
                RTLInst::Iop(
                    Operation::Olea(Addressing::Ainstack(15)),
                    Arc::new(Vec::new()),
                    address_reg,
                ),
            ),
        );
        db.rel_push(
            "rtl_inst",
            (
                load_node,
                RTLInst::Iload(
                    MemoryChunk::MInt8Unsigned,
                    Addressing::Aindexed2(0),
                    Arc::new(vec![address_reg, 0x9200]),
                    0x9300,
                ),
            ),
        );
        db.rel_push("stack_var", (func, lea_node, 15_i64, prefix_local));
        db.rel_push("stack_var", (func, buffer_node, 16_i64, buffer_local));
        db.rel_push("stack_var_chunk", (func, 15_i64, MemoryChunk::MInt32));
        db.stack_struct_buffers
            .entry(func)
            .or_default()
            .insert(buffer_local, 48);

        size_indexed_stack_arrays(&mut db);

        assert_eq!(
            db.stack_struct_buffers
                .get(&func)
                .and_then(|buffers| buffers.get(&buffer_local)),
            Some(&48),
        );
        assert_eq!(
            db.rel_iter::<(Address, RTLReg, RTLReg, usize)>("stack_buffer_alias")
                .count(),
            0,
        );
    }

    #[test]
    fn field_pass_sizes_opaque_storage_without_struct_fields() {
        let mut db = DecompileDB::default();
        db.target_abi = Some(crate::abi::AbiConfig::sysv_x86_64());
        let func: Address = 0x1000;
        let local: RTLReg = 0x8000_0000_0000_1234;
        db.rel_push("func_stacksz", (func, 0x1200_u64, "scratch", 280_u64));
        db.rel_push("slot_escaped_canonical", (func, 0_i64, local));

        ClightFieldPass.run(&mut db);

        assert_eq!(
            db.stack_struct_buffers
                .get(&func)
                .and_then(|buffers| buffers.get(&local)),
            Some(&280),
        );
    }

    #[test]
    fn escaped_frame_storage_is_bounded_by_the_next_modeled_slot() {
        let mut db = DecompileDB::default();
        let [func, func_end, overlapping_func, overlap_end, overlap_node, accessed_interior_func, accessed_end, ambiguous_func, ambiguous_end, ambiguous_node, scalar, interior, bottom, other_local] =
            synthetic_ids();
        db.rel_push("func_stacksz", (func, func_end, "mixed", 64_u64));
        db.rel_push("slot_escaped_canonical", (func, 0_i64, scalar));
        db.rel_push("stack_var_chunk", (func, 0_i64, MemoryChunk::MInt32));
        db.rel_push("slot_escaped_canonical", (func, 32_i64, interior));
        db.rel_push(
            "func_stacksz",
            (overlapping_func, overlap_end, "overlap", 64_u64),
        );
        db.rel_push("slot_escaped_canonical", (overlapping_func, 0_i64, bottom));
        db.rel_push(
            "stack_var",
            (overlapping_func, overlap_node, 48_i64, other_local),
        );
        db.rel_push(
            "func_stacksz",
            (
                accessed_interior_func,
                accessed_end,
                "interior_access",
                64_u64,
            ),
        );
        db.rel_push(
            "slot_escaped_canonical",
            (accessed_interior_func, 0_i64, bottom),
        );
        db.rel_push(
            "stack_var_chunk",
            (accessed_interior_func, 56_i64, MemoryChunk::MInt64),
        );
        db.rel_push(
            "func_stacksz",
            (ambiguous_func, ambiguous_end, "ambiguous", 64_u64),
        );
        db.rel_push("slot_escaped_canonical", (ambiguous_func, 0_i64, bottom));
        db.rel_push(
            "stack_var",
            (ambiguous_func, ambiguous_node, 0_i64, other_local),
        );
        // An incoming stack argument sits above this frame and is not widened.
        db.rel_push("slot_escaped_canonical", (ambiguous_func, 72_i64, interior));

        size_opaque_escaped_frame_buffers(&mut db);

        let sized = |func: Address, local: RTLReg| -> Option<i64> {
            db.stack_struct_buffers
                .get(&func)
                .and_then(|buffers| buffers.get(&local))
                .copied()
        };
        // A directly accessed slot has real width evidence and stays scalar,
        // while the slot above it owns the frame up to its top.
        assert_eq!(sized(func, scalar), None);
        assert_eq!(sized(func, interior), Some(32));
        // A separately modeled local ends the region rather than vetoing it.
        assert_eq!(sized(overlapping_func, bottom), Some(48));
        assert_eq!(sized(accessed_interior_func, bottom), Some(56));
        // Two canonical locals at one offset make the slot model ambiguous.
        assert_eq!(sized(ambiguous_func, bottom), None);
        assert_eq!(sized(ambiguous_func, interior), None);

        let pass = ClightFieldPass;
        for input in [
            "func_stacksz",
            "slot_escaped_canonical",
            "escaped_stack_region_field",
            "slot_escaped_region_canonical",
            "pmov",
            "op_indirect",
            "stack_var",
            "stack_var_chunk",
        ] {
            assert!(pass.inputs().contains(&input));
        }
    }

    #[test]
    fn escaped_mixed_region_initializer_keeps_exact_memory_width() {
        let mut db = DecompileDB::default();
        let func: Address = 0x1000;
        let init: Address = 0x1010;
        let base_ofs = 16_i64;
        let base_local: RTLReg = 0x7100;
        let byte_local: RTLReg = 0x7200;

        db.rel_push(
            "escaped_stack_region_field",
            (func, base_ofs, 0_i64, MemoryChunk::MInt32),
        );
        db.rel_push(
            "escaped_stack_region_field",
            (func, base_ofs, 8_i64, MemoryChunk::MInt8Unsigned),
        );
        db.rel_push("slot_escaped_canonical", (func, base_ofs, base_local));
        db.rel_push(
            "slot_escaped_region_canonical",
            (func, base_ofs, base_local),
        );
        db.rel_push(
            "slot_escaped_region_canonical",
            (func, base_ofs + 8, byte_local),
        );
        db.rel_push("pmov", (init, "mem_dst", "imm_src"));
        db.rel_push(
            "op_indirect",
            ("mem_dst", "", "RSP", "NONE", 1_i64, 24_i64, 1_usize),
        );

        let func_stack_inits =
            HashMap::from([(func, vec![(init, base_ofs + 8, 1_i64, Typ::Tint)])]);
        let mut result = StructConstructionResult {
            new_stmts: Vec::new(),
            new_emit_stmts: Vec::new(),
            rewritten_stmts: HashMap::new(),
            stack_buffers: Vec::new(),
        };
        synthesize_escaped_stack_region_construction(&db, &func_stack_inits, &mut result);

        assert_eq!(result.stack_buffers, vec![(func, base_local as Ident, 9)]);
        assert_eq!(result.new_stmts.len(), 1);
        let ClightStmt::Sassign(ClightExpr::Ederef(_, field_ty), _) = &result.new_stmts[0].1 else {
            panic!("expected an exact-width raw buffer assignment");
        };
        assert_eq!(
            field_ty,
            &ClightType::Tint(
                ClightIntSize::I8,
                ClightSignedness::Unsigned,
                default_attr(),
            )
        );
    }

    #[test]
    fn jumptable_target_is_preserved_as_empty_emit_next_anchor() {
        let mut prog = ClightPassProgram::default();
        let func = 0x1000;
        let source = 0x1100;
        let jump = 0x1110;
        let target = 0x1080;
        let after = 0x1120;

        prog.csharp_stmt.push((
            jump,
            CsharpminorStmt::Sjumptable(CsharpminorExpr::Evar(1), Arc::new(vec![target])),
        ));
        prog.instr_in_function.push((jump, func));
        prog.emit_clight_stmt
            .push((func, source, ClightStmt::Sreturn(None)));
        prog.emit_clight_stmt
            .push((func, after, ClightStmt::Sreturn(None)));
        prog.cminor_succ.push((source, target));
        prog.cminor_succ.push((target, after));

        prog.run();

        assert!(prog
            .emit_goto_target
            .iter()
            .any(|fact| fact == &(func, target)));
        assert!(prog.valid_next.iter().any(|fact| fact == &(target,)));
        assert!(prog.emit_next.iter().any(|fact| fact == &(source, target)));
        assert!(prog.emit_next.iter().any(|fact| fact == &(target, after)));
    }

    #[test]
    fn closed_form_switch_case_is_registered_as_a_goto_target() {
        let mut prog = ClightPassProgram::default();
        let func = 0x1000;
        let head = 0x1100;
        let member = 0x1110;
        let target = 0x1200;

        prog.switch_chain_member
            .push((func, head, member, 7, 3, target));

        prog.run();

        assert!(prog
            .emit_goto_target
            .iter()
            .any(|fact| fact == &(func, target)));
        assert!(prog.valid_next.iter().any(|fact| fact == &(target,)));
    }

    #[test]
    fn targeted_nop_materializes_its_unique_cfg_successor() {
        let mut prog = ClightPassProgram::default();
        let func = 0x1000;
        let source = 0x9000;
        let anchor = 0x0100;
        let successor = 0x0200;

        prog.csharp_stmt
            .push((source, CsharpminorStmt::Sjump(anchor)));
        prog.csharp_stmt.push((anchor, CsharpminorStmt::Snop));
        prog.instr_in_function.push((source, func));
        prog.cminor_succ.push((anchor, successor));

        prog.run();

        let expected = ClightStmt::Sgoto(ident_from_node(successor));
        assert!(prog
            .clight_stmt
            .iter()
            .any(|fact| fact == &(anchor, expected.clone())));
        assert!(!prog
            .clight_stmt
            .iter()
            .any(|fact| fact == &(anchor, ClightStmt::Sskip)));
    }

    #[test]
    fn missing_exact_target_keeps_function_local_forwarding_ownership() {
        let mut prog = ClightPassProgram::default();
        let [func, source, missing, successor] = synthetic_ids();

        prog.emit_function.push((func, "f", source));
        prog.csharp_stmt
            .push((source, CsharpminorStmt::Sjump(missing)));
        prog.instr_in_function.push((source, func));
        prog.emit_clight_stmt
            .push((func, source, ClightStmt::Sgoto(ident_from_node(missing))));
        prog.emit_clight_stmt
            .push((func, successor, ClightStmt::Sreturn(None)));
        prog.cminor_succ.push((source, missing));
        prog.emit_next.push((missing, successor));

        prog.run();

        assert!(prog
            .clight_targeted_nop_owner
            .iter()
            .any(|fact| fact == &(func, missing)));
        assert!(prog
            .clight_targeted_nop_owner
            .iter()
            .any(|fact| fact == &(func, successor)));
    }

    #[test]
    fn semantic_exact_target_keeps_function_local_control_ownership() {
        let mut prog = ClightPassProgram::default();
        let [func, source, target] = synthetic_ids();

        prog.emit_function.push((func, "g", source));
        prog.csharp_stmt
            .push((source, CsharpminorStmt::Sjump(target)));
        prog.csharp_stmt
            .push((target, CsharpminorStmt::Sseq(vec![CsharpminorStmt::Snop])));
        prog.instr_in_function.push((source, func));

        prog.run();

        assert!(prog
            .clight_targeted_nop_owner
            .iter()
            .any(|fact| fact == &(func, target)));
    }

    #[test]
    fn recovered_immediate_stack_init_does_not_emit_a_nop_placeholder() {
        let mut prog = ClightPassProgram::default();
        let func = 0x1000;
        let source = 0x9000;
        let init = 0x0100;
        let successor = 0x0200;

        prog.csharp_stmt
            .push((source, CsharpminorStmt::Sjump(init)));
        // Structuring can eliminate the point-local SSA name, but the field
        // pass will materialize the observable escaped-memory store at init.
        prog.csharp_stmt.push((init, CsharpminorStmt::Snop));
        prog.mach_imm_stack_init.push((init, 24, 1, Typ::Tint));
        prog.instr_in_function.push((source, func));
        prog.cminor_succ.push((init, successor));

        prog.run();

        assert!(prog
            .emit_goto_target
            .iter()
            .any(|fact| fact == &(func, init)));
        assert!(!prog.clight_stmt.iter().any(|(node, _)| *node == init));
    }

    #[test]
    fn indexed_address_of_local_preserves_struct_base_identity() {
        let [local, index] = synthetic_ids();
        let index_term = CsharpminorExpr::Ebinop(
            CminorBinop::Omull,
            Box::new(CsharpminorExpr::Evar(index)),
            Box::new(CsharpminorExpr::Econst(Constant::Olongconst(8))),
        );
        let load = CsharpminorExpr::Eload(
            MemoryChunk::MInt32,
            Box::new(CsharpminorExpr::Ebinop(
                CminorBinop::Oaddl,
                Box::new(CsharpminorExpr::Eaddrof(local as Ident)),
                Box::new(index_term),
            )),
        );
        assert_eq!(
            extract_struct_field_info(&load),
            Some((local as i64, 0)),
            "an address-taken frame object is the indexed aggregate base, not an anonymous scalar"
        );

        let int_ty = default_int_type();
        let int_ptr_ty = pointer_to(int_ty.clone());
        let clight_addr = ClightExpr::Ebinop(
            ClightBinaryOp::Oadd,
            Box::new(ClightExpr::Eaddrof(
                Box::new(ClightExpr::Evar(local as Ident, int_ty)),
                int_ptr_ty.clone(),
            )),
            Box::new(ClightExpr::Ebinop(
                ClightBinaryOp::Omul,
                Box::new(ClightExpr::Etempvar(index as Ident, default_long_type())),
                Box::new(ClightExpr::EconstLong(8, default_long_type())),
                default_long_type(),
            )),
            int_ptr_ty,
        );
        assert_eq!(
            extract_deref_field_pattern(&clight_addr, 8),
            Some((local as Ident, 0))
        );
    }
}

pub struct ClightFieldPass;

impl IRPass for ClightFieldPass {
    fn name(&self) -> &'static str {
        "clight_field"
    }

    fn run(&self, db: &mut DecompileDB) {
        rewrite_clight_stmts_with_struct_fields(db);
    }

    fn inputs(&self) -> &'static [&'static str] {
        &[
            "emit_struct_fields",
            "emit_struct_field",
            "instr_in_function",
            "clight_stmt",
            "emit_clight_stmt",
            "clight_stmt_dead",
            "mach_imm_stack_init",
            "global_struct_catalog",
            "emit_function",
            "reg_rtl",
            "call_arg_mapping",
            "call_target_func",
            "reg_to_struct_id",
            "rtl_inst",
            "stack_var",
            "stack_var_chunk",
            "slot_escaped_canonical",
            "escaped_stack_region_field",
            // Both were read by the escaped-region sizing below without being
            // declared, which leaves them empty in a parallel sub-db and sizes
            // an escaped object from the caller's own accesses alone.
            "escaped_stack_region_caller_field",
            "escaped_stack_region_extent",
            "slot_escaped_region_canonical",
            "pmov",
            "op_indirect",
            "func_stacksz",
        ]
    }

    fn outputs(&self) -> &'static [&'static str] {
        // emit_struct_fields is read-modify-write: infer_struct_fields_from_stack_inits pushes rows and SR-2 rel_sets the pruned copy; declaring it an output persists both through parallel-stage sub-dbs.
        &[
            "clight_stmt",
            "emit_clight_stmt",
            "clight_stmt_dead",
            "reg_to_struct_id",
            "emit_struct_fields",
            "stack_buffer_alias",
        ]
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
                    .unwrap_or_else(|| crude_sig.sig_args.get(i).cloned().unwrap_or(XType::Xlong))
            } else {
                crude_sig.sig_args.get(i).cloned().unwrap_or(XType::Xlong)
            }
        })
        .collect();

    let refined_ret = if crude_sig.sig_res == XType::Xvoid {
        XType::Xvoid
    } else if let Some(dst_reg) = dst {
        best_xtype_for_reg(dst_reg, all_var_types).unwrap_or(crude_sig.sig_res.clone())
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

/// Extract the discriminant register from the address expression of an Eload used as a data lookup table. The address is `Ebinop(Oaddl, table_base_const, Ebinop(scale_op, Evar(idx), scale_const))` or related shapes. Returns the idx RTLReg.
pub(crate) fn data_lookup_extract_index(addr_expr: &CsharpminorExpr) -> Option<RTLReg> {
    fn find_evar(e: &CsharpminorExpr) -> Option<RTLReg> {
        match e {
            CsharpminorExpr::Evar(r) => Some(*r),
            CsharpminorExpr::Ebinop(_, lhs, rhs) => find_evar(lhs).or_else(|| find_evar(rhs)),
            CsharpminorExpr::Eunop(_, inner) => find_evar(inner),
            _ => None,
        }
    }

    if let CsharpminorExpr::Ebinop(_, lhs, rhs) = addr_expr {
        let lhs_is_addr = matches!(
            lhs.as_ref(),
            CsharpminorExpr::Econst(Constant::Oaddrsymbol(_, _))
        );
        let rhs_is_addr = matches!(
            rhs.as_ref(),
            CsharpminorExpr::Econst(Constant::Oaddrsymbol(_, _))
        );
        if lhs_is_addr {
            return find_evar(rhs);
        }
        if rhs_is_addr {
            return find_evar(lhs);
        }
    }
    find_evar(addr_expr)
}

/// Ascent aggregator: collect data lookup table values sorted by index.
pub fn collect_data_lookup_values<'a>(
    inp: impl Iterator<Item = (&'a usize, &'a i64)>,
) -> impl Iterator<Item = Vec<(usize, i64)>> {
    let mut pairs: Vec<(usize, i64)> = inp.map(|(i, v)| (*i, *v)).collect();
    pairs.sort_by_key(|(i, _)| *i);
    pairs.dedup_by_key(|(i, _)| *i);
    std::iter::once(pairs)
}

/// CLOSED-4: build a switch-case constant at the correct width, emitting EconstLong for a 64-bit entry or an out-of-i32-range value rather than truncating.
fn switch_case_const(val: i64, entry_is_64bit: bool) -> ClightExpr {
    if entry_is_64bit {
        return ClightExpr::EconstLong(val, default_long_type());
    }
    match i32::try_from(val) {
        Ok(i) => ClightExpr::EconstInt(i, default_int_type()),
        Err(_) => ClightExpr::EconstLong(val, default_long_type()),
    }
}

/// Build the ClightLabeledStatements list for a data lookup table switch: `case k: dst = table[k]; break;` for each index k.
pub(crate) fn build_data_lookup_switch_cases(
    cases_sorted: &[(usize, i64)],
    dst_ident: Ident,
    entry_scale: i64,
) -> ClightLabeledStatements {
    let entry_is_64bit = entry_scale >= 8;
    let mut entries = Vec::with_capacity(cases_sorted.len());
    for (idx, val) in cases_sorted {
        let set_stmt = ClightStmt::Sset(dst_ident, switch_case_const(*val, entry_is_64bit));
        // case k: { dst = val_k; break; }
        let case_body = ClightStmt::Ssequence(vec![set_stmt, ClightStmt::Sbreak]);
        entries.push((Some(*idx as Z), case_body));
    }
    entries
}

/// Aggregator for closed-form switch cases (the index/key is already an i64 here).
pub fn collect_data_lookup_values_i64<'a>(
    inp: impl Iterator<Item = (&'a i64, &'a i64)>,
) -> impl Iterator<Item = Vec<(i64, i64)>> {
    let mut pairs: Vec<(i64, i64)> = inp.map(|(i, v)| (*i, *v)).collect();
    pairs.sort_by_key(|(i, _)| *i);
    pairs.dedup_by_key(|(i, _)| *i);
    std::iter::once(pairs)
}

/// Build the ClightLabeledStatements for a closed-form switch (one case per disc value plus optional default), emitting EconstLong when dst_ty is 64-bit or a value is out of i32 range.
pub(crate) fn build_closed_form_switch_cases(
    cases_sorted: &[(i64, i64)],
    dst_ident: Ident,
    has_default: bool,
    default_val: i64,
    dst_ty: &ClightType,
) -> ClightLabeledStatements {
    let dst_is_64bit = matches!(dst_ty, ClightType::Tlong(_, _) | ClightType::Tpointer(_, _));
    let mut entries: ClightLabeledStatements = Vec::with_capacity(cases_sorted.len() + 1);
    for (case_idx, case_val) in cases_sorted {
        let set_stmt = ClightStmt::Sset(dst_ident, switch_case_const(*case_val, dst_is_64bit));
        let case_body = ClightStmt::Ssequence(vec![set_stmt, ClightStmt::Sbreak]);
        entries.push((Some(*case_idx as Z), case_body));
    }
    if has_default {
        let set_stmt = ClightStmt::Sset(dst_ident, switch_case_const(default_val, dst_is_64bit));
        let default_body = ClightStmt::Ssequence(vec![set_stmt, ClightStmt::Sbreak]);
        // CompCert ClightLabeledStatements uses None as the default case.
        entries.push((None, default_body));
    }
    entries
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

fn csharp_expr_has_integer_float_conversion(expr: &CsharpminorExpr) -> bool {
    match expr {
        CsharpminorExpr::Eunop(op, inner) => {
            matches!(
                op,
                CminorUnop::Ofloatofint
                    | CminorUnop::Ofloatofintu
                    | CminorUnop::Ofloatoflong
                    | CminorUnop::Ofloatoflongu
                    | CminorUnop::Osingleofint
                    | CminorUnop::Osingleofintu
                    | CminorUnop::Osingleoflong
                    | CminorUnop::Osingleoflongu
            ) || csharp_expr_has_integer_float_conversion(inner)
        }
        CsharpminorExpr::Ebinop(_, left, right) => {
            csharp_expr_has_integer_float_conversion(left)
                || csharp_expr_has_integer_float_conversion(right)
        }
        CsharpminorExpr::Eload(_, addr) => csharp_expr_has_integer_float_conversion(addr),
        CsharpminorExpr::Econdition(cond, true_value, false_value) => {
            csharp_expr_has_integer_float_conversion(cond)
                || csharp_expr_has_integer_float_conversion(true_value)
                || csharp_expr_has_integer_float_conversion(false_value)
        }
        CsharpminorExpr::Evar(_) | CsharpminorExpr::Eaddrof(_) | CsharpminorExpr::Econst(_) => {
            false
        }
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

/// SR-2: restrict aggregated field evidence to a non-overlapping layout, since build_fields_with_padding silently rebases intersecting extents and corrupts ->ofs_N byte offsets.
pub(crate) fn segregate_overlapping_fields(
    fields: &[(i64, Ident, MemoryChunk)],
) -> Arc<Vec<(i64, Ident, MemoryChunk)>> {
    use crate::decompile::analysis::struct_recovery_pass::chunk_byte_size;
    // Negative offsets indicate a mid-object base register, which build_fields_with_padding rebases while Efield rewrites do not, so emit only the 0-based subset and keep the rest raw derefs.
    let mut sorted: Vec<&(i64, Ident, MemoryChunk)> = fields.iter().filter(|f| f.0 >= 0).collect();
    sorted.sort();
    let mut per_offset: Vec<(i64, Ident, MemoryChunk)> = Vec::with_capacity(sorted.len());
    for f in sorted {
        match per_offset.last_mut() {
            Some(prev) if prev.0 == f.0 => {
                let wider = chunk_byte_size(&f.2) > chunk_byte_size(&prev.2);
                if wider {
                    *prev = f.clone();
                }
                // Equal width: keep prev (smallest (name, chunk) - sort order above).
            }
            _ => per_offset.push(f.clone()),
        }
    }
    // Cross-offset extent overlap: ascending scan, keep-first.
    let mut kept: Vec<(i64, Ident, MemoryChunk)> = Vec::with_capacity(per_offset.len());
    let mut prev_end: Option<i64> = None;
    for f in per_offset {
        let size = chunk_byte_size(&f.2) as i64;
        if prev_end.map_or(true, |e| f.0 >= e) {
            prev_end = Some(f.0 + size);
            kept.push(f);
        }
        // else: starts inside the previous kept field's extent - segregated out.
    }
    Arc::new(kept)
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
        let has_non_ptr = types
            .iter()
            .any(|t| !is_pointer_type(t) && !matches!(t, ClightType::Tfloat(_, _)));
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
        let has_non_ptr = types
            .iter()
            .any(|t| !is_pointer_type(t) && !matches!(t, ClightType::Tfloat(_, _)));
        if has_ptr && has_non_ptr {
            // Conflicted: split
            let ptr_types: Vec<_> = types
                .iter()
                .filter(|t| is_pointer_type(t))
                .cloned()
                .collect();
            let int_types: Vec<_> = types
                .iter()
                .filter(|t| !is_pointer_type(t))
                .cloned()
                .collect();
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

    // A float candidate alongside only integer candidates wins: Tfloat comes from real floating evidence while the integer sibling is usually a width-floor placeholder, and preferring int forced truncating casts.
    let has_ptr_candidate = types.iter().any(is_pointer_type);
    let hint_is_ptr_outer = hint.map_or(false, is_pointer_type);
    if !has_ptr_candidate && !hint_is_ptr_outer {
        if let Some(float_ty) = types.iter().find(|t| matches!(t, ClightType::Tfloat(_, _))) {
            return float_ty.clone();
        }
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
            if let Some(int_ty) = types
                .iter()
                .find(|t| !is_pointer_type(t) && !matches!(t, ClightType::Tfloat(_, _)))
            {
                return int_ty.clone();
            }
        }
    }

    // No hint: prefer non-pointer non-float (integer is safer for arithmetic contexts)
    if let Some(int_ty) = types
        .iter()
        .find(|t| !is_pointer_type(t) && !matches!(t, ClightType::Tfloat(_, _)))
    {
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
    ptr_size: i64,
) -> ClightStmt {
    match stmt {
        CsharpminorStmt::Sset(dst, expr) => {
            let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]);
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            let out_expr = clight_expr_from_csharp_with_multi_types(expr, &var_types, ptr_size);
            let dst_ident = ident_from_reg(*dst);
            ClightStmt::Sset(dst_ident, out_expr)
        }
        CsharpminorStmt::Sstore(chunk, addr, value) => {
            let vars_used = extract_vars_from_csharp_exprs(&[addr.clone(), value.clone()]);
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            let addr_expr = clight_expr_from_csharp_with_multi_types(addr, &var_types, ptr_size);
            let value_expr = clight_expr_from_csharp_with_multi_types(value, &var_types, ptr_size);
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
                    let name = func_symbols
                        .iter()
                        .find(|(id, _)| *id == ident)
                        .map(|(_, sym)| sym.to_string())
                        .unwrap_or_else(|| format!("sub_{:x}", addr));
                    ClightExpr::EvarSymbol(name, default_void_ptr_type())
                }
                Either::Left(expr) => {
                    let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]);
                    let var_types =
                        filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
                    clight_expr_from_csharp_with_multi_types(expr, &var_types, ptr_size)
                }
            };
            let vars_used = extract_vars_from_csharp_exprs(args.as_slice());
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            let converted_args: Vec<ClightExpr> = args
                .iter()
                .map(|a| clight_expr_from_csharp_with_multi_types(a, &var_types, ptr_size))
                .collect();
            let dst_ident = dst.map(|r| ident_from_reg(r));
            ClightStmt::Scall(dst_ident, callee_expr, converted_args)
        }
        CsharpminorStmt::Scond(cond, args, ifso, ifnot) => {
            let vars_used = extract_vars_from_csharp_exprs(args.as_slice());
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            if let Some(condition) =
                clight_condition_expr_with_types(cond, args.as_slice(), &var_types, ptr_size)
            {
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
            let converted = clight_expr_from_csharp_with_multi_types(result, &var_types, ptr_size);
            ClightStmt::Sreturn(Some(converted))
        }
        CsharpminorStmt::Sifthenelse(cond, args, then_body, else_body) => {
            let vars_used = extract_vars_from_csharp_exprs(args.as_slice());
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            if let Some(condition) =
                clight_condition_expr_with_types(cond, args.as_slice(), &var_types, ptr_size)
            {
                let then_clight = convert_csharp_stmt_to_clight(
                    then_body,
                    all_var_type_pairs,
                    func_symbols,
                    ptr_size,
                );
                let else_clight = convert_csharp_stmt_to_clight(
                    else_body,
                    all_var_type_pairs,
                    func_symbols,
                    ptr_size,
                );
                ClightStmt::Sifthenelse(condition, Box::new(then_clight), Box::new(else_clight))
            } else {
                ClightStmt::Sskip
            }
        }
        CsharpminorStmt::Sloop(body) => {
            let body_clight =
                convert_csharp_stmt_to_clight(body, all_var_type_pairs, func_symbols, ptr_size);
            ClightStmt::Sloop(Box::new(body_clight), Box::new(ClightStmt::Sskip))
        }
        CsharpminorStmt::Sbreak => ClightStmt::Sbreak,
        CsharpminorStmt::Scontinue => ClightStmt::Scontinue,
        CsharpminorStmt::Sseq(stmts) => {
            // Detect structuring-pass Sseq([Sjumptable(expr, targets), case_body_0..N]) and build Sswitch with inline case bodies.
            if let Some(CsharpminorStmt::Sjumptable(expr, targets)) = stmts.first() {
                if stmts.len() == 1 + targets.len() {
                    let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]);
                    let var_types =
                        filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
                    let discr =
                        clight_expr_from_csharp_with_multi_types(expr, &var_types, ptr_size);
                    let table: ClightLabeledStatements = stmts[1..]
                        .iter()
                        .enumerate()
                        .map(|(idx, case_body)| {
                            let body_clight = convert_csharp_stmt_to_clight(
                                case_body,
                                all_var_type_pairs,
                                func_symbols,
                                ptr_size,
                            );
                            (Some(idx as Z), body_clight)
                        })
                        .collect();
                    return ClightStmt::Sswitch(discr, table);
                }
            }
            let clight_stmts: Vec<ClightStmt> = stmts
                .iter()
                .map(|s| {
                    convert_csharp_stmt_to_clight(s, all_var_type_pairs, func_symbols, ptr_size)
                })
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
                    let name = func_symbols
                        .iter()
                        .find(|(id, _)| *id == ident)
                        .map(|(_, sym)| sym.to_string())
                        .unwrap_or_else(|| format!("sub_{:x}", addr));
                    ClightExpr::EvarSymbol(name, default_void_ptr_type())
                }
                Either::Left(expr) => {
                    let vars_used = extract_vars_from_csharp_exprs(&[expr.clone()]);
                    let var_types =
                        filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
                    clight_expr_from_csharp_with_multi_types(expr, &var_types, ptr_size)
                }
            };
            let vars_used = extract_vars_from_csharp_exprs(args.as_slice());
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            let converted_args: Vec<ClightExpr> = args
                .iter()
                .map(|a| clight_expr_from_csharp_with_multi_types(a, &var_types, ptr_size))
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
                args.iter()
                    .filter(|arg| match arg {
                        BuiltinArg::BA(CsharpminorExpr::Evar(r)) => r != dst_reg,
                        _ => true,
                    })
                    .cloned()
                    .collect()
            } else {
                args.clone()
            };
            let vars_used = extract_vars_from_builtin_args(&effective_args);
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            let converted_args =
                clight_builtin_args_with_multi_types(&effective_args, &var_types, ptr_size);
            ClightStmt::Scall(
                dst_ident,
                ClightExpr::EvarSymbol(effective_name, default_void_ptr_type()),
                converted_args,
            )
        }
        CsharpminorStmt::Scond(cond, args, ifso, ifnot) => {
            let vars_used = extract_vars_from_csharp_exprs(args.as_slice());
            let var_types = filter_and_build_multi_var_type_map(all_var_type_pairs, &vars_used);
            if let Some(condition) =
                clight_condition_expr_with_types(cond, args.as_slice(), &var_types, ptr_size)
            {
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
            let discr = clight_expr_from_csharp_with_multi_types(expr, &var_types, ptr_size);
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
        // OF-set <-> OF-clear is an exact logical negation (the flag is a single bit).
        Condition::Coverflow => Condition::Cnotoverflow,
        Condition::Cnotoverflow => Condition::Coverflow,
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
    ptr_size: i64,
) -> Option<(ClightExpr, Ident, ClightType)> {
    let synthetic_load = CsharpminorExpr::Eload(chunk.clone(), Box::new(addr.clone()));
    let (base_off, field_off) = extract_struct_field_info(&synthetic_load)?;

    let (field_name, _) = field_info.get(&(base_off, field_off))?;

    let base_expr = extract_base_expr_for_field(addr, field_off, ptr_size)?;

    let field_ty = clight_type_from_chunk(chunk);

    let struct_id = base_off.unsigned_abs() as Ident;
    let struct_ty = ClightType::Tstruct(struct_id, default_attr());
    let struct_ptr_ty = pointer_to(struct_ty.clone());

    let typed_base = cast_expr_to_type(base_expr, struct_ptr_ty);
    // Efield expects a struct lvalue, so dereference the pointer: ptr->field == (*ptr).field
    let deref_base = ClightExpr::Ederef(Box::new(typed_base), struct_ty);

    Some((deref_base, *field_name, field_ty))
}

fn extract_base_expr_for_field(
    addr: &CsharpminorExpr,
    _field_offset: i64,
    ptr_size: i64,
) -> Option<ClightExpr> {
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
                ptr_size,
                IntegerFloatCastMode::Direct,
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
        MemoryChunk::MBool | MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned => true,
        MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned => offset % 2 == 0,
        MemoryChunk::MInt32 | MemoryChunk::MFloat32 => offset % 4 == 0,
        MemoryChunk::MInt64 | MemoryChunk::MFloat64 => offset % 4 == 0,
        MemoryChunk::MAny32 | MemoryChunk::MAny64 | MemoryChunk::Unknown => offset % 4 == 0,
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
    fn local_base_key(expr: &CsharpminorExpr) -> Option<i64> {
        match expr {
            CsharpminorExpr::Evar(reg) => Some(*reg as i64),
            CsharpminorExpr::Eaddrof(ident) => Some(*ident as i64),
            _ => None,
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
                        base if local_base_key(base).is_some() => {
                            // No abs: a NEGATIVE offset off a pointer base is a before-pointer access, never a struct field, so it keeps its raw *(p + k) deref form rather than forging a bogus +field.
                            let base_key = local_base_key(base).unwrap();
                            if is_valid_field_offset(offset, chunk) {
                                return Some((base_key, offset));
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
                    base if local_base_key(base).is_some() => {
                        // No abs: negative pointer-base offset is not a struct field (see above).
                        let base_key = local_base_key(base).unwrap();
                        let field = accumulated_offset;
                        if is_valid_field_offset(field, chunk) {
                            return Some((base_key, field));
                        }
                    }
                    // base + idx*scale + ofs: a non-negative ofs is a correct forward field offset, but a negative one must NOT be abs()'d into a positive field, which flips out[i-1] to out[i+1].
                    CsharpminorExpr::Ebinop(op, lhs, rhs)
                        if matches!(op, CminorBinop::Oadd | CminorBinop::Oaddl) =>
                    {
                        let base_key = match (lhs.as_ref(), rhs.as_ref()) {
                            (base, other)
                                if local_base_key(base).is_some()
                                    && !matches!(other, CsharpminorExpr::Econst(_)) =>
                            {
                                local_base_key(base)
                            }
                            (other, base)
                                if local_base_key(base).is_some()
                                    && !matches!(other, CsharpminorExpr::Econst(_)) =>
                            {
                                local_base_key(base)
                            }
                            _ => None,
                        };
                        if let Some(base_key) = base_key {
                            if is_valid_field_offset(accumulated_offset, chunk) {
                                return Some((base_key, accumulated_offset));
                            }
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
                // Bare `Evar(reg)` (no Ebinop) is an offset-0 load; treat as field 0 keyed by the reg so `*out=x` emits `out->ofs_0=x` and `cur->value; cur->next` recovers both offset 0 and 8.
                base if local_base_key(base).is_some() => {
                    let base_key = local_base_key(base).unwrap();
                    if is_valid_field_offset(0, chunk) {
                        return Some((base_key, 0));
                    }
                }
                // base + idx*scale with no constant offset is field 0 keyed by base, with the runtime index staying inside the base sub-expression so the offset-0 access is correct.
                CsharpminorExpr::Ebinop(op, lhs, rhs)
                    if matches!(op, CminorBinop::Oadd | CminorBinop::Oaddl) =>
                {
                    let base_key = match (lhs.as_ref(), rhs.as_ref()) {
                        (base, other)
                            if local_base_key(base).is_some()
                                && !matches!(other, CsharpminorExpr::Econst(_)) =>
                        {
                            local_base_key(base)
                        }
                        (other, base)
                            if local_base_key(base).is_some()
                                && !matches!(other, CsharpminorExpr::Econst(_)) =>
                        {
                            local_base_key(base)
                        }
                        _ => None,
                    };
                    if let Some(base_key) = base_key {
                        if is_valid_field_offset(0, chunk) {
                            return Some((base_key, 0));
                        }
                    }
                    // `Oaddrstack(ofs) + idx*scale` (clang -O1 SP-indexed load): treat stack offset as a field in a bucket-0 stack-base struct so the load emits field-access instead of `*(int *)(-N + idx*S)`.
                    let stack_base = match (lhs.as_ref(), rhs.as_ref()) {
                        (CsharpminorExpr::Econst(Constant::Oaddrstack(ofs)), other)
                        | (other, CsharpminorExpr::Econst(Constant::Oaddrstack(ofs)))
                            if !matches!(other, CsharpminorExpr::Econst(_)) =>
                        {
                            Some(*ofs as i64)
                        }
                        _ => None,
                    };
                    if let Some(ofs) = stack_base {
                        let abs_base = abs_i64(ofs);
                        let base_bucket = (abs_base / 64) * 64;
                        let field = abs_i64(abs_base - base_bucket);
                        if is_valid_field_offset(field, chunk) {
                            return Some((base_bucket, field));
                        }
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
        // CLIGHT-3: high-mul ops are not a plain multiply, so return None and let build_binop_expr's special case lower them faithfully instead of aliasing to Omul.
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

fn get_inner_type_size(ty: &ClightType, ptr_size: i64) -> Option<i64> {
    match ty {
        ClightType::Tint(ClightIntSize::I8, _, _) => Some(1),
        ClightType::Tint(ClightIntSize::I16, _, _) => Some(2),
        ClightType::Tint(ClightIntSize::I32, _, _) => Some(4),
        ClightType::Tint(ClightIntSize::IBool, _, _) => Some(1),
        ClightType::Tlong(_, _) => Some(8),
        ClightType::Tfloat(ClightFloatSize::F32, _) => Some(4),
        ClightType::Tfloat(ClightFloatSize::F64, _) => Some(8),
        // Pointer width is a target property; the caller threads it from abi_pointer_size.
        ClightType::Tpointer(_, _) => Some(ptr_size),
        ClightType::Tarray(inner, len, _) => {
            get_inner_type_size(inner, ptr_size).map(|s| s * (*len as i64))
        }
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

fn try_unscale_expr(expr: ClightExpr, ptr_ty: &ClightType, ptr_size: i64) -> ClightExpr {
    if let ClightType::Tpointer(inner, _) = ptr_ty {
        if let Some(size) = get_inner_type_size(inner, ptr_size) {
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

                // idx << log2(size)  is also `idx * size` for power-of-two sizes.
                if let ClightExpr::Ebinop(ClightBinaryOp::Oshl, l, r, _) = &expr {
                    if let Some(k) = get_const_val(r) {
                        if (0..63).contains(&k) && (1i64 << k) == size {
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

// Build (T*)((char*)base + offset): byte-unit pointer arithmetic scaled exactly once, for a byte offset try_unscale_expr could not reduce to an element index.
fn rebase_ptr_byte_add(
    op: ClightBinaryOp,
    base: ClightExpr,
    offset: ClightExpr,
    target_ptr_ty: ClightType,
    base_is_lhs: bool,
) -> ClightExpr {
    let char_ptr_ty = pointer_to(ClightType::Tint(
        ClightIntSize::I8,
        ClightSignedness::Signed,
        default_attr(),
    ));
    let base_as_char_ptr = ClightExpr::Ecast(Box::new(base), char_ptr_ty.clone());
    let byte_addr = if base_is_lhs {
        ClightExpr::Ebinop(
            op,
            Box::new(base_as_char_ptr),
            Box::new(offset),
            char_ptr_ty,
        )
    } else {
        ClightExpr::Ebinop(
            op,
            Box::new(offset),
            Box::new(base_as_char_ptr),
            char_ptr_ty,
        )
    };
    ClightExpr::Ecast(Box::new(byte_addr), target_ptr_ty)
}

// True when ptr_ty's pointee is larger than a byte, so C would scale ptr + n; byte/void/unknown pointees need no rebasing.
fn pointee_scales(ptr_ty: &ClightType, ptr_size: i64) -> bool {
    match ptr_ty {
        ClightType::Tpointer(inner, _) => {
            get_inner_type_size(inner, ptr_size).map_or(false, |s| s > 1)
        }
        _ => false,
    }
}

pub fn build_binop_expr(
    op: &CminorBinop,
    lhs_expr: ClightExpr,
    rhs_expr: ClightExpr,
    ptr_size: i64,
) -> ClightExpr {
    let lhs_ty = clight_expr_type(&lhs_expr);
    let rhs_ty = clight_expr_type(&rhs_expr);

    // CLIGHT-3: lower high-mul faithfully as the high half of a wider product with correct signedness, rather than aliasing it to a wrong-valued plain multiply.
    match op {
        CminorBinop::Omulhs | CminorBinop::Omulhu => {
            let signed = matches!(op, CminorBinop::Omulhs);
            let wide_ty = if signed {
                default_long_type()
            } else {
                default_ulong_type()
            };
            let narrow_ty = if signed {
                default_int_type()
            } else {
                default_uint_type()
            };
            let l = cast_expr_to_type(coerce_ptr_to_long(lhs_expr), wide_ty.clone());
            let r = cast_expr_to_type(coerce_ptr_to_long(rhs_expr), wide_ty.clone());
            let product = ClightExpr::Ebinop(
                ClightBinaryOp::Omul,
                Box::new(l),
                Box::new(r),
                wide_ty.clone(),
            );
            let shifted = ClightExpr::Ebinop(
                ClightBinaryOp::Oshr,
                Box::new(product),
                Box::new(ClightExpr::EconstInt(32, default_int_type())),
                wide_ty,
            );
            return ClightExpr::Ecast(Box::new(shifted), narrow_ty);
        }
        CminorBinop::Omullhs | CminorBinop::Omullhu => {
            // 128-bit high-mul: widen both operands to __int128, multiply, take the high half with >> 64, narrow back; unlike the prior opaque builtin this recompiles and computes the right value.
            let signed = matches!(op, CminorBinop::Omullhs);
            let res_ty = if signed {
                default_long_type()
            } else {
                default_ulong_type()
            };
            let wide_ty = if signed {
                default_int128_type()
            } else {
                default_uint128_type()
            };
            let l = cast_expr_to_type(coerce_ptr_to_long(lhs_expr), wide_ty.clone());
            let r = cast_expr_to_type(coerce_ptr_to_long(rhs_expr), wide_ty.clone());
            let product = ClightExpr::Ebinop(
                ClightBinaryOp::Omul,
                Box::new(l),
                Box::new(r),
                wide_ty.clone(),
            );
            let shifted = ClightExpr::Ebinop(
                ClightBinaryOp::Oshr,
                Box::new(product),
                Box::new(ClightExpr::EconstInt(64, default_int_type())),
                wide_ty,
            );
            return ClightExpr::Ecast(Box::new(shifted), res_ty);
        }
        _ => {}
    }

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

    // Pointer +/- integral is byte-addressed in Cminor; when try_unscale_expr cannot recover an element index, re-base through char* so a larger-than-byte pointee does not scale the offset twice.
    let binop_op = clight_binop_from_cminor(op).unwrap_or(ClightBinaryOp::Oadd);
    if matches!(
        op,
        CminorBinop::Oadd | CminorBinop::Oaddl | CminorBinop::Osub | CminorBinop::Osubl
    ) {
        if is_pointer_type(&final_lhs_ty) && is_integral_type(&final_rhs_ty) {
            let rewritten_rhs = try_unscale_expr(rhs_final.clone(), &final_lhs_ty, ptr_size);
            if rewritten_rhs == rhs_final && pointee_scales(&final_lhs_ty, ptr_size) {
                return rebase_ptr_byte_add(
                    binop_op,
                    lhs_final,
                    rhs_final,
                    final_lhs_ty.clone(),
                    true,
                );
            }
        } else if matches!(op, CminorBinop::Oadd | CminorBinop::Oaddl)
            && is_integral_type(&final_lhs_ty)
            && is_pointer_type(&final_rhs_ty)
        {
            let rewritten_lhs = try_unscale_expr(lhs_final.clone(), &final_rhs_ty, ptr_size);
            if rewritten_lhs == lhs_final && pointee_scales(&final_rhs_ty, ptr_size) {
                return rebase_ptr_byte_add(
                    binop_op,
                    rhs_final,
                    lhs_final,
                    final_rhs_ty.clone(),
                    false,
                );
            }
        }
    }

    let (lhs_scaled, rhs_scaled) = if matches!(
        op,
        CminorBinop::Oadd | CminorBinop::Oaddl | CminorBinop::Osub | CminorBinop::Osubl
    ) {
        if is_pointer_type(&final_lhs_ty) && is_integral_type(&final_rhs_ty) {
            let rewritten_rhs = try_unscale_expr(rhs_final.clone(), &final_lhs_ty, ptr_size);
            (lhs_final, rewritten_rhs)
        } else if matches!(op, CminorBinop::Oadd | CminorBinop::Oaddl)
            && is_integral_type(&final_lhs_ty)
            && is_pointer_type(&final_rhs_ty)
        {
            let rewritten_lhs = try_unscale_expr(lhs_final.clone(), &final_rhs_ty, ptr_size);
            (rewritten_lhs, rhs_final)
        } else {
            (lhs_final, rhs_final)
        }
    } else {
        (lhs_final, rhs_final)
    };

    // CLIGHT-1/2: ClightBinaryOp has no unsigned variants, so coerce integral operands to unsigned at this single point; pointer operands are left alone to avoid truncating an address.
    let to_unsigned = |e: ClightExpr, target: ClightType| -> ClightExpr {
        let ety = clight_expr_type(&e);
        if matches!(ety, ClightType::Tlong(_, _)) {
            // A 64-bit operand cannot narrow to 32-bit unsigned (cast_expr_to_type refuses truncation), so cast to unsigned long and perform the operation unsigned at full width.
            cast_expr_to_type(e, default_ulong_type())
        } else if is_integral_type(&ety) {
            cast_expr_to_type(e, target)
        } else {
            e
        }
    };
    let (lhs_scaled, rhs_scaled, unsigned_result_ty) = match op {
        CminorBinop::Odivu | CminorBinop::Omodu => (
            to_unsigned(lhs_scaled, default_uint_type()),
            to_unsigned(rhs_scaled, default_uint_type()),
            Some(default_uint_type()),
        ),
        CminorBinop::Oshru => (
            to_unsigned(lhs_scaled, default_uint_type()),
            rhs_scaled,
            Some(default_uint_type()),
        ),
        CminorBinop::Odivlu | CminorBinop::Omodlu => (
            to_unsigned(lhs_scaled, default_ulong_type()),
            to_unsigned(rhs_scaled, default_ulong_type()),
            Some(default_ulong_type()),
        ),
        CminorBinop::Oshrlu => (
            to_unsigned(lhs_scaled, default_ulong_type()),
            rhs_scaled,
            Some(default_ulong_type()),
        ),
        CminorBinop::Ocmpu(_) => (
            to_unsigned(lhs_scaled, default_uint_type()),
            to_unsigned(rhs_scaled, default_uint_type()),
            None,
        ),
        CminorBinop::Ocmplu(_) => (
            to_unsigned(lhs_scaled, default_ulong_type()),
            to_unsigned(rhs_scaled, default_ulong_type()),
            None,
        ),
        _ => (lhs_scaled, rhs_scaled, None),
    };

    let result_ty = match op {
        CminorBinop::Oaddf
        | CminorBinop::Osubf
        | CminorBinop::Omulf
        | CminorBinop::Odivf
        | CminorBinop::Omaxf
        | CminorBinop::Ominf => default_float_type(),
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

    // Unsigned arithmetic ops need an unsigned result type to match their coerced operands; comparison ops keep their bool result (override is None).
    let result_ty = unsigned_result_ty.unwrap_or(result_ty);

    let binop = clight_binop_from_cminor(op).unwrap_or(ClightBinaryOp::Oadd);
    let expr = ClightExpr::Ebinop(
        binop,
        Box::new(lhs_scaled),
        Box::new(rhs_scaled),
        result_ty.clone(),
    );
    // Cnotcompf/Cnotcompfs: wrap in logical NOT to preserve unordered (NaN) semantics
    if matches!(op, CminorBinop::Ocmpnotf(_) | CminorBinop::Ocmpnotfs(_)) {
        ClightExpr::Eunop(ClightUnaryOp::Onotbool, Box::new(expr), result_ty)
    } else {
        expr
    }
}

pub(crate) fn clight_expr_from_csharp(expr: &CsharpminorExpr, ptr_size: i64) -> ClightExpr {
    clight_expr_from_csharp_inner(
        expr,
        &HashMap::new(),
        &HashMap::new(),
        None,
        ptr_size,
        IntegerFloatCastMode::Direct,
    )
}

pub(crate) fn clight_expr_from_csharp_with_types(
    expr: &CsharpminorExpr,
    var_types: &VarTypeMap,
    ptr_size: i64,
) -> ClightExpr {
    // Convert VarTypeMap to MultiVarTypeMap for backward compat
    let multi: MultiVarTypeMap = var_types
        .iter()
        .map(|(k, v)| (*k, vec![v.clone()]))
        .collect();
    clight_expr_from_csharp_inner(
        expr,
        &HashMap::new(),
        &multi,
        None,
        ptr_size,
        IntegerFloatCastMode::Direct,
    )
}

pub(crate) fn clight_expr_from_csharp_with_multi_types(
    expr: &CsharpminorExpr,
    var_types: &MultiVarTypeMap,
    ptr_size: i64,
) -> ClightExpr {
    clight_expr_from_csharp_inner(
        expr,
        &HashMap::new(),
        var_types,
        None,
        ptr_size,
        IntegerFloatCastMode::Direct,
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum IntegerFloatCastMode {
    Direct,
    BridgePointerOperand,
}

/// Build the additional legal-C spelling for an integer-register-to-float
/// conversion whose recovered source annotation is pointer-shaped.  `None`
/// means the bridge mode made no change, which keeps ordinary numeric
/// conversions from doubling the candidate set.
fn clight_expr_from_csharp_with_integer_float_bridge(
    expr: &CsharpminorExpr,
    var_types: &MultiVarTypeMap,
    ptr_size: i64,
) -> Option<ClightExpr> {
    let direct = clight_expr_from_csharp_inner(
        expr,
        &HashMap::new(),
        var_types,
        None,
        ptr_size,
        IntegerFloatCastMode::Direct,
    );
    let bridged = clight_expr_from_csharp_inner(
        expr,
        &HashMap::new(),
        var_types,
        None,
        ptr_size,
        IntegerFloatCastMode::BridgePointerOperand,
    );
    (bridged != direct).then_some(bridged)
}

fn integer_float_operand(
    inner: ClightExpr,
    integer_type: ClightType,
    mode: IntegerFloatCastMode,
) -> ClightExpr {
    if mode == IntegerFloatCastMode::BridgePointerOperand
        && is_pointer_type(&clight_expr_type(&inner))
    {
        ClightExpr::Ecast(Box::new(inner), integer_type)
    } else {
        inner
    }
}

fn clight_expr_from_csharp_inner(
    expr: &CsharpminorExpr,
    field_info: &FieldInfo,
    var_types: &MultiVarTypeMap,
    type_hint: Option<&ClightType>,
    ptr_size: i64,
    integer_float_cast_mode: IntegerFloatCastMode,
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
                let narrowed = i32::try_from(*value).unwrap_or((*value as u32) as i32);

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
            let inner_expr = clight_expr_from_csharp_inner(
                inner,
                field_info,
                var_types,
                None,
                ptr_size,
                integer_float_cast_mode,
            );
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
                CminorUnop::Ofloatofint => ClightExpr::Ecast(
                    Box::new(integer_float_operand(
                        inner_expr,
                        default_int_type(),
                        integer_float_cast_mode,
                    )),
                    default_float_type(),
                ),
                CminorUnop::Ofloatofsingle => {
                    ClightExpr::Ecast(Box::new(inner_expr), default_float_type())
                }
                CminorUnop::Olongofint | CminorUnop::Olongofsingle | CminorUnop::Olongoffloat => {
                    ClightExpr::Ecast(Box::new(inner_expr), default_long_type())
                }
                CminorUnop::Osingleoffloat => {
                    ClightExpr::Ecast(Box::new(inner_expr), default_single_type())
                }
                CminorUnop::Osingleofint => ClightExpr::Ecast(
                    Box::new(integer_float_operand(
                        inner_expr,
                        default_int_type(),
                        integer_float_cast_mode,
                    )),
                    default_single_type(),
                ),
                CminorUnop::Osingleofintu => ClightExpr::Ecast(
                    Box::new(integer_float_operand(
                        inner_expr,
                        default_uint_type(),
                        integer_float_cast_mode,
                    )),
                    default_single_type(),
                ),
                CminorUnop::Osingleoflong => ClightExpr::Ecast(
                    Box::new(integer_float_operand(
                        inner_expr,
                        default_long_type(),
                        integer_float_cast_mode,
                    )),
                    default_single_type(),
                ),
                CminorUnop::Osingleoflongu => ClightExpr::Ecast(
                    Box::new(integer_float_operand(
                        inner_expr,
                        default_ulong_type(),
                        integer_float_cast_mode,
                    )),
                    default_single_type(),
                ),
                CminorUnop::Ofloatoflong => ClightExpr::Ecast(
                    Box::new(integer_float_operand(
                        inner_expr,
                        default_long_type(),
                        integer_float_cast_mode,
                    )),
                    default_float_type(),
                ),
                CminorUnop::Ofloatoflongu => ClightExpr::Ecast(
                    Box::new(integer_float_operand(
                        inner_expr,
                        default_ulong_type(),
                        integer_float_cast_mode,
                    )),
                    default_float_type(),
                ),
                CminorUnop::Ofloatofintu => ClightExpr::Ecast(
                    Box::new(integer_float_operand(
                        inner_expr,
                        default_uint_type(),
                        integer_float_cast_mode,
                    )),
                    default_float_type(),
                ),
                CminorUnop::Ointoflong => {
                    ClightExpr::Ecast(Box::new(inner_expr), default_int_type())
                }
                CminorUnop::Olongofintu => {
                    ClightExpr::Ecast(Box::new(inner_expr), default_long_type())
                }
                CminorUnop::Ointuoffloat | CminorUnop::Ointuofsingle => ClightExpr::Ecast(
                    Box::new(inner_expr),
                    ClightType::Tint(
                        ClightIntSize::I32,
                        ClightSignedness::Unsigned,
                        default_attr(),
                    ),
                ),
                CminorUnop::Olonguoffloat | CminorUnop::Olonguofsingle => ClightExpr::Ecast(
                    Box::new(inner_expr),
                    ClightType::Tlong(ClightSignedness::Unsigned, default_attr()),
                ),
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
            let is_add_or_sub = matches!(
                op,
                CminorBinop::Oaddl | CminorBinop::Osubl | CminorBinop::Oadd | CminorBinop::Osub
            );
            // Propagate pointer hint from parent to LHS (base) and integer hint to RHS (offset) for add/sub
            let (lhs_hint, rhs_hint) =
                if is_add_or_sub && type_hint.map_or(false, |h| is_pointer_type(h)) {
                    (
                        type_hint.cloned(),
                        if is_long_cminor_binop(op) {
                            Some(default_long_type())
                        } else {
                            None
                        },
                    )
                } else if is_long_cminor_binop(op) {
                    (Some(default_long_type()), Some(default_long_type()))
                } else {
                    (None, None)
                };
            let lhs_expr = clight_expr_from_csharp_inner(
                lhs,
                field_info,
                var_types,
                lhs_hint.as_ref(),
                ptr_size,
                integer_float_cast_mode,
            );
            let rhs_expr = clight_expr_from_csharp_inner(
                rhs,
                field_info,
                var_types,
                rhs_hint.as_ref(),
                ptr_size,
                integer_float_cast_mode,
            );
            // Downgrade Oaddl/Osubl to Oadd/Osub for pointer operands so build_binop_expr produces pointer result type (ptr+int=ptr in C).
            let effective_op = match op {
                CminorBinop::Oaddl
                    if is_pointer_type(&clight_expr_type(&lhs_expr))
                        || is_pointer_type(&clight_expr_type(&rhs_expr)) =>
                {
                    &CminorBinop::Oadd
                }
                CminorBinop::Osubl if is_pointer_type(&clight_expr_type(&lhs_expr)) => {
                    &CminorBinop::Osub
                }
                _ => op,
            };
            build_binop_expr(effective_op, lhs_expr, rhs_expr, ptr_size)
        }
        CsharpminorExpr::Eload(chunk, addr) => {
            if !field_info.is_empty() {
                if let Some((base_expr, field_id, field_ty)) =
                    extract_field_access(addr, chunk, field_info, ptr_size)
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
            let addr_expr = clight_expr_from_csharp_inner(
                addr,
                field_info,
                var_types,
                Some(&ptr_hint),
                ptr_size,
                integer_float_cast_mode,
            );

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
            let cond_expr = clight_expr_from_csharp_inner(
                cond,
                field_info,
                var_types,
                None,
                ptr_size,
                integer_float_cast_mode,
            );
            let true_expr = clight_expr_from_csharp_inner(
                true_val,
                field_info,
                var_types,
                type_hint,
                ptr_size,
                integer_float_cast_mode,
            );
            let false_expr = clight_expr_from_csharp_inner(
                false_val,
                field_info,
                var_types,
                type_hint,
                ptr_size,
                integer_float_cast_mode,
            );
            let ty = type_hint.cloned().unwrap_or_else(default_int_type);
            ClightExpr::Econdition(
                Box::new(cond_expr),
                Box::new(true_expr),
                Box::new(false_expr),
                ty,
            )
        }
    }
}

pub(crate) fn clight_exprs_from_csharp(
    exprs: &[CsharpminorExpr],
    ptr_size: i64,
) -> Vec<ClightExpr> {
    exprs
        .iter()
        .map(|e| clight_expr_from_csharp(e, ptr_size))
        .collect()
}

pub(crate) fn clight_exprs_from_csharp_with_multi_types(
    exprs: &[CsharpminorExpr],
    var_types: &MultiVarTypeMap,
    ptr_size: i64,
) -> Vec<ClightExpr> {
    exprs
        .iter()
        .map(|e| clight_expr_from_csharp_with_multi_types(e, var_types, ptr_size))
        .collect()
}

pub(crate) fn clight_expr_from_builtin_arg_with_types(
    arg: &BuiltinArg<CsharpminorExpr>,
    var_types: &VarTypeMap,
    ptr_size: i64,
) -> ClightExpr {
    match arg {
        BuiltinArg::BA(expr) => clight_expr_from_csharp_with_types(expr, var_types, ptr_size),
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
            let lo_expr = clight_expr_from_builtin_arg_with_types(lo, var_types, ptr_size);
            let hi_expr = clight_expr_from_builtin_arg_with_types(hi, var_types, ptr_size);
            ClightExpr::Ebinop(
                ClightBinaryOp::Oadd,
                Box::new(lo_expr),
                Box::new(hi_expr),
                default_long_type(),
            )
        }
    }
}

pub(crate) fn clight_builtin_args_with_multi_types(
    args: &[BuiltinArg<CsharpminorExpr>],
    var_types: &MultiVarTypeMap,
    ptr_size: i64,
) -> Vec<ClightExpr> {
    args.iter()
        .map(|arg| {
            match arg {
                BuiltinArg::BA(expr) => {
                    clight_expr_from_csharp_with_multi_types(expr, var_types, ptr_size)
                }
                other => {
                    // Non-expression builtin args don't use var types, delegate to existing
                    let empty = VarTypeMap::new();
                    clight_expr_from_builtin_arg_with_types(other, &empty, ptr_size)
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

// cmov defense-in-depth: REPAIR a ptr-vs-int binop by casting both operands to long rather than dropping the statement; bottom-up, and genuine ptr-vs-ptr operands are untouched.
fn repair_bad_binop(expr: &ClightExpr) -> ClightExpr {
    match expr {
        ClightExpr::Ebinop(op, lhs, rhs, ty) => {
            let lhs_r = repair_bad_binop(lhs);
            let rhs_r = repair_bad_binop(rhs);
            let strict = matches!(
                op,
                ClightBinaryOp::Omul
                    | ClightBinaryOp::Odiv
                    | ClightBinaryOp::Omod
                    | ClightBinaryOp::Oand
                    | ClightBinaryOp::Oor
                    | ClightBinaryOp::Oxor
                    | ClightBinaryOp::Oshl
                    | ClightBinaryOp::Oshr
                    | ClightBinaryOp::Oeq
                    | ClightBinaryOp::One
                    | ClightBinaryOp::Olt
                    | ClightBinaryOp::Ogt
                    | ClightBinaryOp::Ole
                    | ClightBinaryOp::Oge
            );
            let lhs_ty = clight_expr_type(&lhs_r);
            let rhs_ty = clight_expr_type(&rhs_r);
            let lhs_is_int = matches!(lhs_ty, ClightType::Tint(_, _, _));
            let lhs_is_ptr = is_pointer_type(&lhs_ty);
            let rhs_is_int = matches!(rhs_ty, ClightType::Tint(_, _, _));
            let rhs_is_ptr = is_pointer_type(&rhs_ty);
            let mismatch = (lhs_is_int && rhs_is_ptr) || (lhs_is_ptr && rhs_is_int);
            if strict && mismatch {
                let lhs_fixed = cast_expr_to_type(lhs_r, default_long_type());
                let rhs_fixed = cast_expr_to_type(rhs_r, default_long_type());
                ClightExpr::Ebinop(*op, Box::new(lhs_fixed), Box::new(rhs_fixed), ty.clone())
            } else {
                ClightExpr::Ebinop(*op, Box::new(lhs_r), Box::new(rhs_r), ty.clone())
            }
        }
        ClightExpr::Ecast(inner, ty) => {
            ClightExpr::Ecast(Box::new(repair_bad_binop(inner)), ty.clone())
        }
        ClightExpr::Eunop(op, inner, ty) => {
            ClightExpr::Eunop(*op, Box::new(repair_bad_binop(inner)), ty.clone())
        }
        ClightExpr::Ederef(inner, ty) => {
            ClightExpr::Ederef(Box::new(repair_bad_binop(inner)), ty.clone())
        }
        ClightExpr::Eaddrof(inner, ty) => {
            ClightExpr::Eaddrof(Box::new(repair_bad_binop(inner)), ty.clone())
        }
        ClightExpr::Efield(inner, id, ty) => {
            ClightExpr::Efield(Box::new(repair_bad_binop(inner)), *id, ty.clone())
        }
        ClightExpr::Econdition(c, t, f, ty) => ClightExpr::Econdition(
            Box::new(repair_bad_binop(c)),
            Box::new(repair_bad_binop(t)),
            Box::new(repair_bad_binop(f)),
            ty.clone(),
        ),
        other => other.clone(),
    }
}

pub(crate) fn check_clight_stmt(stmt: &ClightStmt) -> Option<ClightStmt> {
    match stmt {
        ClightStmt::Sassign(lhs, rhs) => {
            // Repair int<->ptr binop mismatches rather than dropping the assignment.
            let lhs = repair_bad_binop(lhs);
            let rhs = repair_bad_binop(rhs);
            let lhs_ty = clight_expr_type(&lhs);
            let rhs_ty = clight_expr_type(&rhs);

            if is_function_pointer_type(&lhs_ty)
                || is_function_pointer_type(&rhs_ty)
                || is_function_type(&lhs_ty)
                || is_function_type(&rhs_ty)
            {
                return None;
            }

            if lhs_ty == rhs_ty || clight_cast_supported(&rhs_ty, &lhs_ty) {
                Some(ClightStmt::Sassign(lhs, rhs))
            } else if !make_binarith_check(&lhs_ty, &rhs_ty) {
                let cast_rhs = ClightExpr::Ecast(Box::new(rhs), lhs_ty);
                Some(ClightStmt::Sassign(lhs, cast_rhs))
            } else {
                let cast_rhs = ClightExpr::Ecast(Box::new(rhs), lhs_ty);
                Some(ClightStmt::Sassign(lhs, cast_rhs))
            }
        }
        ClightStmt::Sset(id, expr) => {
            // Repair int<->ptr binop mismatches rather than dropping the assignment.
            let expr = repair_bad_binop(expr);
            let expr_ty = clight_expr_type(&expr);

            if !is_function_pointer_type(&expr_ty) && !is_function_type(&expr_ty) {
                Some(ClightStmt::Sset(*id, expr))
            } else {
                None
            }
        }
        ClightStmt::Scall(dst, func_expr, args) => {
            let func_ty = clight_expr_type(func_expr);
            // A named symbol is a direct function designator, callable as name(...) whatever type the node carries, so treat it as well-formed; only genuine indirect-value callees get the fnptr cast.
            let func_ok = is_function_type(&func_ty)
                || is_function_pointer_type(&func_ty)
                || matches!(func_expr, ClightExpr::EvarSymbol(_, _));
            let args_ok = args.iter().all(|arg| {
                let arg_ty = clight_expr_type(arg);
                !is_function_pointer_type(&arg_ty) && !is_function_type(&arg_ty)
            });
            if func_ok && args_ok {
                Some(stmt.clone())
            } else if !func_ok {
                let default_fn_ty = ClightType::Tfunction(
                    Arc::new(vec![]),
                    Arc::new(ClightType::Tint(
                        ClightIntSize::I32,
                        ClightSignedness::Signed,
                        default_attr(),
                    )),
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
            // Repair a ptr-vs-int condition rather than dropping the whole if-then-else.
            let cond = repair_bad_binop(cond);
            let then_valid = check_clight_stmt(then_stmt);
            let else_valid = check_clight_stmt(else_stmt);
            match (then_valid, else_valid) {
                (Some(t), Some(e)) => Some(ClightStmt::Sifthenelse(cond, Box::new(t), Box::new(e))),
                _ => None,
            }
        }
        ClightStmt::Sloop(body, exit) => {
            let body_checked = check_clight_stmt(body)?;
            let exit_checked = check_clight_stmt(exit)?;
            Some(ClightStmt::Sloop(
                Box::new(body_checked),
                Box::new(exit_checked),
            ))
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
        ClightStmt::Sswitch(expr, cases) => {
            // Repair a ptr-vs-int discriminant rather than dropping the switch.
            let expr = repair_bad_binop(expr);
            Some(ClightStmt::Sswitch(expr, cases.clone()))
        }
        _ => Some(stmt.clone()),
    }
}

fn force_int_type_for_32bit_cmp(expr: ClightExpr, signed: bool) -> ClightExpr {
    let ty = clight_expr_type(&expr);
    // A 64-bit operand of a 32-bit-typed comparison cannot be narrowed, so coerce to signed/unsigned LONG and run the comparison at full width with the correct signedness.
    if matches!(ty, ClightType::Tlong(_, _)) {
        let long_target = if signed {
            default_long_type()
        } else {
            default_ulong_type()
        };
        return cast_expr_to_type(expr, long_target);
    }
    if !matches!(ty, ClightType::Tpointer(_, _)) {
        let target = if signed {
            default_int_type()
        } else {
            default_uint_type()
        };
        // Force signedness by EMITTING A REAL CAST on every integral operand shape: a C comparison follows the operand's declared type, so a retyped-in-place annotation would stay signed.
        return match expr {
            other if is_integral_type(&clight_expr_type(&other)) => {
                cast_expr_to_type(other, target)
            }
            other => other,
        };
    }
    // Pointer: cast to signed/unsigned long (64-bit); truncating to 32-bit would lose address bits.
    let long_ty = if signed {
        default_long_type()
    } else {
        default_ulong_type()
    };
    ClightExpr::Ecast(Box::new(expr), long_ty)
}

// CLIGHT-2: 64-bit sibling of force_int_type_for_32bit_cmp, forcing signed/unsigned long on every operand shape; pointer operands cast to long too, preserving address bits.
fn force_long_type_for_64bit_cmp(expr: ClightExpr, signed: bool) -> ClightExpr {
    let target = if signed {
        default_long_type()
    } else {
        default_ulong_type()
    };
    let ty = clight_expr_type(&expr);
    if is_pointer_type(&ty) || is_integral_type(&ty) {
        cast_expr_to_type(expr, target)
    } else {
        expr
    }
}

fn is_int32_type(ty: &ClightType) -> bool {
    matches!(ty, ClightType::Tint(ClightIntSize::I32, _, _))
}

pub(crate) fn clight_condition_expr_with_types(
    cond: &Condition,
    args: &[CsharpminorExpr],
    var_types: &MultiVarTypeMap,
    ptr_size: i64,
) -> Option<ClightExpr> {
    match cond {
        Condition::Ccomp(comp)
        | Condition::Ccompu(comp)
        | Condition::Ccompl(comp)
        | Condition::Ccomplu(comp)
        | Condition::Ccompf(comp)
        | Condition::Ccompfs(comp) => {
            if args.len() >= 2 {
                let lhs = clight_expr_from_csharp_with_multi_types(&args[0], var_types, ptr_size);
                let rhs = clight_expr_from_csharp_with_multi_types(&args[1], var_types, ptr_size);
                let (lhs, rhs) = if matches!(cond, Condition::Ccomp(_) | Condition::Ccompu(_)) {
                    let signed = matches!(cond, Condition::Ccomp(_));
                    (
                        force_int_type_for_32bit_cmp(lhs, signed),
                        force_int_type_for_32bit_cmp(rhs, signed),
                    )
                } else if matches!(cond, Condition::Ccompl(_) | Condition::Ccomplu(_)) {
                    // CLIGHT-2: 64-bit comparisons also carry signedness on their operands, so coerce toward signed/unsigned long for Ccompl/Ccomplu.
                    let signed = matches!(cond, Condition::Ccompl(_));
                    (
                        force_long_type_for_64bit_cmp(lhs, signed),
                        force_long_type_for_64bit_cmp(rhs, signed),
                    )
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
                    (_, ClightType::Tpointer(_, _), _) if is_zero_lit(&lhs) => ClightExpr::Ecast(
                        Box::new(ClightExpr::EconstInt(0, default_int_type())),
                        rhs_ty0.clone(),
                    ),
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
                let lhs = clight_expr_from_csharp_with_multi_types(&args[0], var_types, ptr_size);
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
                let signed = matches!(cond, Condition::Ccompimm(_, _));
                let imm_ty = if signed {
                    default_int_type()
                } else {
                    default_uint_type()
                };
                let lhs = clight_expr_from_csharp_with_multi_types(&args[0], var_types, ptr_size);
                let lhs_final = force_int_type_for_32bit_cmp(lhs, signed);
                let rhs_final = normalize_const_expr(ClightExpr::EconstInt(*imm as i32, imm_ty));
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
                let signed = matches!(cond, Condition::Ccomplimm(_, _));
                let long_ty = if signed {
                    default_long_type()
                } else {
                    default_ulong_type()
                };
                let lhs = clight_expr_from_csharp_with_multi_types(&args[0], var_types, ptr_size);
                let lhs_ty = clight_expr_type(&lhs);
                let mut lhs_final = lhs.clone();
                let rhs_final = if *imm == 0 {
                    if matches!(lhs_ty, ClightType::Tpointer(_, _)) {
                        ClightExpr::Ecast(
                            Box::new(ClightExpr::EconstLong(0, long_ty.clone())),
                            lhs_ty.clone(),
                        )
                    } else {
                        ClightExpr::EconstLong(0, long_ty.clone())
                    }
                } else {
                    if matches!(lhs_ty, ClightType::Tpointer(_, _)) {
                        let lhs_cast =
                            ClightExpr::Ecast(Box::new(lhs_final.clone()), long_ty.clone());
                        lhs_final = lhs_cast;
                    }
                    normalize_const_expr(ClightExpr::EconstLong(*imm, long_ty.clone()))
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
                let value = clight_expr_from_csharp_with_multi_types(&args[0], var_types, ptr_size);

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
                let value = clight_expr_from_csharp_with_multi_types(&args[0], var_types, ptr_size);
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
            let inner = clight_condition_expr_with_types(
                &Condition::Ccompf(*comp),
                args,
                var_types,
                ptr_size,
            )?;
            Some(ClightExpr::Eunop(
                ClightUnaryOp::Onotbool,
                Box::new(inner),
                default_bool_type(),
            ))
        }
        Condition::Cnotcompfs(comp) => {
            let inner = clight_condition_expr_with_types(
                &Condition::Ccompfs(*comp),
                args,
                var_types,
                ptr_size,
            )?;
            Some(ClightExpr::Eunop(
                ClightUnaryOp::Onotbool,
                Box::new(inner),
                default_bool_type(),
            ))
        }
        // x86 OF from JO/JNO has no portable C expression, so emit a marked opaque builtin rather than inventing a wrong comparison; both CFG successor edges survive regardless.
        Condition::Coverflow => Some(ClightExpr::EvarSymbol(
            "__builtin_overflow".to_string(),
            default_bool_type(),
        )),
        Condition::Cnotoverflow => Some(ClightExpr::Eunop(
            ClightUnaryOp::Onotbool,
            Box::new(ClightExpr::EvarSymbol(
                "__builtin_overflow".to_string(),
                default_bool_type(),
            )),
            default_bool_type(),
        )),
    }
}

fn extract_base_ident_clight(expr: &ClightExpr) -> Option<Ident> {
    match expr {
        ClightExpr::Etempvar(ident, _) => Some(*ident),
        ClightExpr::Ecast(inner, _) => extract_base_ident_clight(inner),
        ClightExpr::Eaddrof(inner, _) => match inner.as_ref() {
            ClightExpr::Evar(ident, _) | ClightExpr::Etempvar(ident, _) => Some(*ident),
            other => extract_base_ident_clight(other),
        },
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

/// Returns true for ClightExpr non-constant index terms (mul or arbitrary runtime expr) so the struct-base matcher can ignore them when recovering clang `base + idx*scale + ofs` field accesses.
fn is_index_term_clight(expr: &ClightExpr) -> bool {
    match expr {
        ClightExpr::EconstInt(..) | ClightExpr::EconstLong(..) => false,
        ClightExpr::Ecast(inner, _) => is_index_term_clight(inner),
        _ => true,
    }
}

/// Byte scale of a pointer base in clight pointer arithmetic, so base + const converts to a true byte offset; defaults to 1 for char*/void*, non-pointer bases, and aggregate pointees.
fn clight_base_ptr_elem_size(expr: &ClightExpr, ptr_size: i64) -> i64 {
    let ty = match expr {
        ClightExpr::Ecast(_, ty) | ClightExpr::Eaddrof(_, ty) => Some(ty),
        ClightExpr::Etempvar(_, ty) | ClightExpr::Evar(_, ty) => Some(ty),
        _ => None,
    };
    match ty {
        Some(ClightType::Tpointer(elem, _)) => {
            get_inner_type_size(elem, ptr_size).unwrap_or(1).max(1)
        }
        _ => 1,
    }
}

/// Build the pointer-to-struct for a recovered field access, preserving any array index so base[idx] is not mis-rendered as base->ofs_0; the trailing constant addend is stripped as the field offset.
fn struct_base_ptr_expr(
    inner: &ClightExpr,
    base_ident: Ident,
    struct_ptr_ty: &ClightType,
) -> ClightExpr {
    let stripped = match inner {
        ClightExpr::Ecast(e, _) => e.as_ref(),
        other => other,
    };
    if let ClightExpr::Ebinop(ClightBinaryOp::Oadd, lhs, rhs, _) = stripped {
        let lhs_is_pure_base = extract_base_ident_clight(lhs).is_some();
        let rhs_is_const = extract_const_offset_clight(rhs).is_some();
        // `base + const`: no index term, keep the clean base-register form.
        if lhs_is_pure_base && rhs_is_const {
            return ClightExpr::Etempvar(base_ident, struct_ptr_ty.clone());
        }
        // Indexed: the struct pointer is the address minus the trailing constant field offset, or the whole sum when there is none.
        let base_sum = if rhs_is_const {
            lhs.as_ref().clone()
        } else {
            stripped.clone()
        };
        return cast_expr_to_type(base_sum, struct_ptr_ty.clone());
    }
    // Bare base register (Etempvar) or any non-additive form: clean base.
    ClightExpr::Etempvar(base_ident, struct_ptr_ty.clone())
}

fn extract_deref_field_pattern(inner: &ClightExpr, ptr_size: i64) -> Option<(Ident, i64)> {
    let stripped = match inner {
        ClightExpr::Ecast(e, _) => e.as_ref(),
        other => other,
    };
    match stripped {
        ClightExpr::Ebinop(ClightBinaryOp::Oadd, lhs, rhs, _) => {
            // 1. `base + const_offset` (the original case).
            if let (Some(base_ident), Some(offset)) = (
                extract_base_ident_clight(lhs),
                extract_const_offset_clight(rhs),
            ) {
                // `(T*)base + n` advances n*sizeof(T) bytes in C; scale the literal by the base pointer's pointee size to recover the true byte field offset (char*/non-ptr -> 1).
                let scale = clight_base_ptr_elem_size(lhs, ptr_size);
                return Some((base_ident, (offset * scale).abs()));
            }
            // (base + idx*scale) + const_offset: scale the displacement by the base pointee size to recover the byte offset, and decline negatives rather than abs() them into a wrong forward field.
            if let Some(offset) = extract_const_offset_clight(rhs) {
                if let ClightExpr::Ebinop(ClightBinaryOp::Oadd, inner_l, inner_r, _) =
                    match lhs.as_ref() {
                        ClightExpr::Ecast(e, _) => e.as_ref(),
                        other => other,
                    }
                {
                    let base_scale = match (
                        extract_base_ident_clight(inner_l),
                        is_index_term_clight(inner_r),
                    ) {
                        (Some(b), true) => Some((b, clight_base_ptr_elem_size(inner_l, ptr_size))),
                        _ => match (
                            is_index_term_clight(inner_l),
                            extract_base_ident_clight(inner_r),
                        ) {
                            (true, Some(b)) => {
                                Some((b, clight_base_ptr_elem_size(inner_r, ptr_size)))
                            }
                            _ => None,
                        },
                    };
                    if let Some((base_ident, scale)) = base_scale {
                        let byte_offset = offset * scale;
                        if byte_offset >= 0 {
                            return Some((base_ident, byte_offset));
                        }
                    }
                }
            }
            // 3. `base + idx*scale` (no const offset; field is implicitly 0). Index preserved in base.
            if is_index_term_clight(rhs) {
                if let Some(base_ident) = extract_base_ident_clight(lhs) {
                    return Some((base_ident, 0));
                }
            }
            if is_index_term_clight(lhs) {
                if let Some(base_ident) = extract_base_ident_clight(rhs) {
                    return Some((base_ident, 0));
                }
            }
            // 4. `EconstInt(stack_ofs) + idx*scale` (clang -O1 SP-indexed load; stack ofs becomes a literal post-select). Treat abs(stack_ofs) as field offset in bucket-0 stack-base struct (mirrors the Oaddrstack branch in extract_struct_field_info).
            let stack_const = match (
                extract_const_offset_clight(lhs),
                extract_const_offset_clight(rhs),
                is_index_term_clight(lhs),
                is_index_term_clight(rhs),
            ) {
                (Some(c), None, _, true) => Some(c),
                (None, Some(c), true, _) => Some(c),
                _ => None,
            };
            if let Some(c) = stack_const {
                let abs_c = c.abs();
                if abs_c < 2048 {
                    let base_bucket = (abs_c / 64) * 64;
                    let field = abs_c - base_bucket;
                    return Some((base_bucket as usize, field));
                }
            }
            None
        }
        ClightExpr::Etempvar(ident, _) => Some((*ident, 0)),
        _ => None,
    }
}

fn rewrite_clight_expr_fields(
    expr: &ClightExpr,
    field_info: &FieldInfo,
    reg_to_canonical: &HashMap<Ident, Ident>,
    ptr_size: i64,
) -> ClightExpr {
    match expr {
        ClightExpr::Ederef(inner, deref_ty) => {
            if let Some((base_ident, offset)) = extract_deref_field_pattern(inner, ptr_size) {
                let base_key = base_ident as i64;
                // extract_deref_field_pattern now returns the true byte offset (pointer scaling applied at the source), so look it up directly. The old rescale-by-deref_ty fallback is redundant and would double-scale; it also used the wrong size (deref type, not the base pointee).
                let lookup = field_info.get(&(base_key, offset)).map(|v| (offset, v));
                if let Some((field_offset, (_field_ident, chunk))) = lookup {
                    // SR-2 width gate: rewriting a deref whose scalar width disagrees with the declared field width would silently change bytes read at recompile; keep raw deref form instead. Unknown/non-scalar deref types always rewrite.
                    let width_ok = match deref_ty {
                        ClightType::Tint(..)
                        | ClightType::Tlong(..)
                        | ClightType::Tfloat(..)
                        | ClightType::Tpointer(..) => {
                            use crate::decompile::analysis::struct_recovery_pass::chunk_byte_size;
                            get_inner_type_size(deref_ty, ptr_size)
                                == Some(chunk_byte_size(chunk) as i64)
                        }
                        _ => true,
                    };
                    if width_ok {
                        let field_ty = deref_ty.clone();
                        // Use canonical struct ID if available, else fall back to register-based
                        let struct_id = reg_to_canonical
                            .get(&base_ident)
                            .copied()
                            .unwrap_or_else(|| base_key.unsigned_abs() as Ident);
                        let struct_ty = ClightType::Tstruct(struct_id, default_attr());
                        let struct_ptr_ty = pointer_to(struct_ty.clone());
                        let ptr_expr = struct_base_ptr_expr(inner, base_ident, &struct_ptr_ty);
                        let proper_field_id = make_field_ident(field_offset, chunk.clone());
                        let deref_expr = ClightExpr::Ederef(Box::new(ptr_expr), struct_ty);
                        return ClightExpr::Efield(Box::new(deref_expr), proper_field_id, field_ty);
                    }
                }
            }
            ClightExpr::Ederef(
                Box::new(rewrite_clight_expr_fields(
                    inner,
                    field_info,
                    reg_to_canonical,
                    ptr_size,
                )),
                deref_ty.clone(),
            )
        }
        ClightExpr::Ebinop(op, lhs, rhs, ty) => ClightExpr::Ebinop(
            op.clone(),
            Box::new(rewrite_clight_expr_fields(
                lhs,
                field_info,
                reg_to_canonical,
                ptr_size,
            )),
            Box::new(rewrite_clight_expr_fields(
                rhs,
                field_info,
                reg_to_canonical,
                ptr_size,
            )),
            ty.clone(),
        ),
        ClightExpr::Eunop(op, inner, ty) => ClightExpr::Eunop(
            op.clone(),
            Box::new(rewrite_clight_expr_fields(
                inner,
                field_info,
                reg_to_canonical,
                ptr_size,
            )),
            ty.clone(),
        ),
        ClightExpr::Ecast(inner, ty) => ClightExpr::Ecast(
            Box::new(rewrite_clight_expr_fields(
                inner,
                field_info,
                reg_to_canonical,
                ptr_size,
            )),
            ty.clone(),
        ),
        ClightExpr::Efield(inner, ident, ty) => ClightExpr::Efield(
            Box::new(rewrite_clight_expr_fields(
                inner,
                field_info,
                reg_to_canonical,
                ptr_size,
            )),
            *ident,
            ty.clone(),
        ),
        ClightExpr::Eaddrof(inner, ty) => ClightExpr::Eaddrof(
            Box::new(rewrite_clight_expr_fields(
                inner,
                field_info,
                reg_to_canonical,
                ptr_size,
            )),
            ty.clone(),
        ),
        ClightExpr::Econdition(cond, t, f, ty) => ClightExpr::Econdition(
            Box::new(rewrite_clight_expr_fields(
                cond,
                field_info,
                reg_to_canonical,
                ptr_size,
            )),
            Box::new(rewrite_clight_expr_fields(
                t,
                field_info,
                reg_to_canonical,
                ptr_size,
            )),
            Box::new(rewrite_clight_expr_fields(
                f,
                field_info,
                reg_to_canonical,
                ptr_size,
            )),
            ty.clone(),
        ),
        other => other.clone(),
    }
}

fn rewrite_clight_stmt_fields(
    stmt: &ClightStmt,
    field_info: &FieldInfo,
    reg_to_canonical: &HashMap<Ident, Ident>,
    ptr_size: i64,
) -> ClightStmt {
    match stmt {
        ClightStmt::Sassign(lhs, rhs) => ClightStmt::Sassign(
            rewrite_clight_expr_fields(lhs, field_info, reg_to_canonical, ptr_size),
            rewrite_clight_expr_fields(rhs, field_info, reg_to_canonical, ptr_size),
        ),
        ClightStmt::Sset(ident, expr) => ClightStmt::Sset(
            *ident,
            rewrite_clight_expr_fields(expr, field_info, reg_to_canonical, ptr_size),
        ),

        ClightStmt::Scall(ret, func, args) => ClightStmt::Scall(
            *ret,
            rewrite_clight_expr_fields(func, field_info, reg_to_canonical, ptr_size),
            args.iter()
                .map(|a| rewrite_clight_expr_fields(a, field_info, reg_to_canonical, ptr_size))
                .collect(),
        ),
        ClightStmt::Sbuiltin(ret, ef, tys, args) => ClightStmt::Sbuiltin(
            *ret,
            ef.clone(),
            tys.clone(),
            args.iter()
                .map(|a| rewrite_clight_expr_fields(a, field_info, reg_to_canonical, ptr_size))
                .collect(),
        ),
        ClightStmt::Sreturn(Some(expr)) => ClightStmt::Sreturn(Some(rewrite_clight_expr_fields(
            expr,
            field_info,
            reg_to_canonical,
            ptr_size,
        ))),
        ClightStmt::Sifthenelse(cond, then_s, else_s) => ClightStmt::Sifthenelse(
            rewrite_clight_expr_fields(cond, field_info, reg_to_canonical, ptr_size),
            Box::new(rewrite_clight_stmt_fields(
                then_s,
                field_info,
                reg_to_canonical,
                ptr_size,
            )),
            Box::new(rewrite_clight_stmt_fields(
                else_s,
                field_info,
                reg_to_canonical,
                ptr_size,
            )),
        ),
        ClightStmt::Ssequence(stmts) => ClightStmt::Ssequence(
            stmts
                .iter()
                .map(|s| rewrite_clight_stmt_fields(s, field_info, reg_to_canonical, ptr_size))
                .collect(),
        ),
        ClightStmt::Sloop(body, cont) => ClightStmt::Sloop(
            Box::new(rewrite_clight_stmt_fields(
                body,
                field_info,
                reg_to_canonical,
                ptr_size,
            )),
            Box::new(rewrite_clight_stmt_fields(
                cont,
                field_info,
                reg_to_canonical,
                ptr_size,
            )),
        ),
        ClightStmt::Slabel(ident, inner) => ClightStmt::Slabel(
            *ident,
            Box::new(rewrite_clight_stmt_fields(
                inner,
                field_info,
                reg_to_canonical,
                ptr_size,
            )),
        ),
        ClightStmt::Sswitch(expr, cases) => ClightStmt::Sswitch(
            rewrite_clight_expr_fields(expr, field_info, reg_to_canonical, ptr_size),
            cases
                .iter()
                .map(|(label, s)| {
                    (
                        label.clone(),
                        rewrite_clight_stmt_fields(s, field_info, reg_to_canonical, ptr_size),
                    )
                })
                .collect(),
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
            groups
                .entry(*n)
                .and_modify(|curr| *curr = (*curr).min(*f))
                .or_insert(*f);
        }
        groups
    };

    use crate::decompile::analysis::struct_recovery_pass::chunk_byte_size;

    // Collect (offset, chunk) per function; multiple inits at one offset reduce to the widest chunk seen.
    let mut func_inits: HashMap<u64, std::collections::BTreeMap<i64, MemoryChunk>> = HashMap::new();
    for (addr, ofs, _val, typ) in db.rel_iter::<(Address, i64, i64, Typ)>("mach_imm_stack_init") {
        if let Some(&func) = node_to_func.get(addr) {
            let chunk = typ_to_chunk(typ);
            let entry = func_inits.entry(func).or_default();
            let pick = match entry.get(ofs) {
                None => chunk,
                Some(prev) => {
                    if chunk_byte_size(&chunk) > chunk_byte_size(prev) {
                        chunk
                    } else {
                        prev.clone()
                    }
                }
            };
            entry.insert(*ofs, pick);
        }
    }

    let mut new_fields: Vec<(u64, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>)> = Vec::new();

    for (func_addr, offset_chunks) in &func_inits {
        // BTreeMap is already sorted by offset.
        let entries: Vec<(i64, MemoryChunk)> =
            offset_chunks.iter().map(|(o, c)| (*o, c.clone())).collect();

        if entries.len() < 2 {
            // Without at least two inits there is no stride to infer.
            continue;
        }

        // Assumes homogeneous array-of-structs layout (uniform field size = stride); mixed-field-size structs would need separate handling.
        let field_size = chunk_byte_size(&entries[0].1) as i64;
        if !matches!(field_size, 1 | 2 | 4 | 8) {
            continue;
        }
        if !entries
            .iter()
            .all(|(_, c)| chunk_byte_size(c) as i64 == field_size)
        {
            continue;
        }
        let chunk = entries[0].1.clone();

        let offsets: Vec<i64> = entries.iter().map(|(o, _)| *o).collect();
        let deltas: Vec<i64> = offsets.windows(2).map(|w| w[1] - w[0]).collect();
        // Adjacent offsets must be exactly field_size apart (packed array of uniform structs has no padding).
        if !deltas.iter().all(|d| *d == field_size) {
            continue;
        }

        // Require N >= 2 copies of a K-field struct so we don't confuse scattered uniform-width locals with an array of structs.
        let max_fields = offsets.len();
        for fields_per_struct in 1..=max_fields {
            let struct_size = field_size * fields_per_struct as i64;
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
                    let expected = base_ofs + (s as i64) * struct_size + (f as i64) * field_size;
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
                        let field_offset = (f as i64) * field_size;
                        let field_name = generate_field_name(field_offset);
                        (field_offset, field_name, chunk.clone())
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

    for (func_addr, base_off, fields) in &new_fields {
        db.rel_push(
            "emit_struct_fields",
            (*func_addr, *base_off, fields.clone()),
        );
    }
}

fn rewrite_clight_stmts_with_struct_fields(db: &mut DecompileDB) {
    // Pointer width for the pointee-size arithmetic below; imperative entry point, so read the target ABI directly.
    let ptr_size = db.abi().pointer_size as i64;
    infer_struct_fields_from_stack_inits(db);

    let mut func_field_info: HashMap<u64, FieldInfo> = HashMap::new();
    for (func_addr, base_off, fields) in
        db.rel_iter::<(Address, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>)>("emit_struct_fields")
    {
        let fi = func_field_info.entry(*func_addr).or_default();
        for (field_off, field_name, chunk) in fields.iter() {
            // emit_struct_fields is multi-valued per (func, base); keep widest chunk (tie-break min name) to avoid relation-order flicker.
            use crate::decompile::analysis::struct_recovery_pass::chunk_byte_size;
            fi.entry((*base_off, *field_off))
                .and_modify(|cur| {
                    let (cur_name, cur_chunk) = cur.clone();
                    let better = chunk_byte_size(chunk) > chunk_byte_size(&cur_chunk)
                        || (chunk_byte_size(chunk) == chunk_byte_size(&cur_chunk)
                            && *field_name < cur_name);
                    if better {
                        *cur = (*field_name, chunk.clone());
                    }
                })
                .or_insert((*field_name, chunk.clone()));
        }
    }

    // Build reg-to-canonical struct ID mapping so Tstruct IDs in expressions match XstructPtr IDs in declarations; min-aggregate on sid for deterministic selection when a reg has multiple canonical IDs across addresses.
    let mut reg_to_canonical: HashMap<Ident, Ident> = {
        let mut groups: HashMap<Ident, Ident> = HashMap::new();
        for &(_, reg, sid) in db.rel_iter::<(Address, RTLReg, usize)>("reg_to_struct_id") {
            groups
                .entry(reg as Ident)
                .and_modify(|curr| *curr = (*curr).min(sid as Ident))
                .or_insert(sid as Ident);
        }
        groups
    };

    // Canonicalize efield-detected struct identity by bucketing unmapped (func, reg) by exact (offset, chunk) shape hash and linking callsite-passing peers via union-find; kept imperative because fresh-ID allocation needs a counter Datalog cannot express directly.
    {
        use crate::decompile::analysis::struct_recovery_pass::{
            chunk_byte_size, compute_layout_hash_from_tuples,
        };
        let mut shape_to_id: HashMap<u64, Ident> = HashMap::new();
        let mut next_id: usize = 1;
        for (h, id, _, _) in db.rel_iter::<(u64, usize, usize, usize)>("global_struct_catalog") {
            shape_to_id.insert(*h, *id as Ident);
            if *id >= next_id {
                next_id = *id + 1;
            }
        }

        // Group all (func, base_reg) -> set of (offset, chunk) for efield-discovered structs.
        let mut reg_fields: HashMap<(u64, i64), std::collections::BTreeSet<(i64, MemoryChunk)>> =
            HashMap::new();
        for (func_addr, base_off, fields) in
            db.rel_iter::<(Address, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>)>("emit_struct_fields")
        {
            let entry = reg_fields.entry((*func_addr, *base_off)).or_default();
            for (field_off, _, chunk) in fields.iter() {
                entry.insert((*field_off, chunk.clone()));
            }
        }

        // Callsite linkage via ABI: a register passed as the N-th argument is the same abstract pointer as the callee's N-th parameter register. Union them so disjoint per-function field-sets merge into one canonical struct.
        let abi_regs = &db.abi().int_arg_regs;
        // Invert emit_function to lookup the function owning a given entry node.
        let mut entry_node_to_func: HashMap<Node, Address> = HashMap::new();
        for (a, _, n) in db.rel_iter::<(Address, Symbol, Node)>("emit_function") {
            // Aliased symbols can share one entry node; min addr wins to keep callsite union edges stable.
            entry_node_to_func
                .entry(*n)
                .and_modify(|cur| {
                    if *a < *cur {
                        *cur = *a
                    }
                })
                .or_insert(*a);
        }
        let mut entry_mreg_to_rtl: HashMap<(Address, Mreg), RTLReg> = HashMap::new();
        for &(node, mreg, rtl) in db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl") {
            if let Some(&func) = entry_node_to_func.get(&node) {
                // reg_rtl is multi-valued per (node, mreg); pick MIN RTLReg so the callee-param representative is stable across parallel-Ascent runs (last-wins flickered union-find classes and efield canonical struct ids).
                entry_mreg_to_rtl
                    .entry((func, mreg))
                    .and_modify(|cur| {
                        if rtl < *cur {
                            *cur = rtl
                        }
                    })
                    .or_insert(rtl);
            }
        }

        // Callee at pos -> RTLReg (per function). One entry per (func, pos) using the first ABI-matching reg.
        let mut callee_param_at: HashMap<(Address, usize), RTLReg> = HashMap::new();
        for &func in entry_node_to_func.values() {
            for (pos, abi_mreg) in abi_regs.iter().enumerate() {
                if let Some(&rtl) = entry_mreg_to_rtl.get(&(func, *abi_mreg)) {
                    callee_param_at.entry((func, pos)).or_insert(rtl);
                }
            }
        }

        // Caller side: which (call_node, pos) carries which RTLReg.
        let mut call_args: Vec<(Node, usize, RTLReg)> = db
            .rel_iter::<(Node, usize, RTLReg)>("call_arg_mapping")
            .map(|t| (t.0, t.1, t.2))
            .collect();
        call_args.sort();

        let mut call_targets: HashMap<Node, Address> = HashMap::new();
        for (n, a) in db.rel_iter::<(Node, Address)>("call_target_func") {
            // Min-wins for indirect calls that map a call node to multiple targets.
            call_targets
                .entry(*n)
                .and_modify(|cur| {
                    if *a < *cur {
                        *cur = *a
                    }
                })
                .or_insert(*a);
        }

        // Union-Find over RTLReg, lazily created as we walk the linkages.
        let mut parent: HashMap<RTLReg, RTLReg> = HashMap::new();
        fn ufind(parent: &mut HashMap<RTLReg, RTLReg>, r: RTLReg) -> RTLReg {
            let p = *parent.entry(r).or_insert(r);
            if p == r {
                return r;
            }
            let root = ufind(parent, p);
            parent.insert(r, root);
            root
        }
        fn uunion(parent: &mut HashMap<RTLReg, RTLReg>, a: RTLReg, b: RTLReg) {
            let ra = ufind(parent, a);
            let rb = ufind(parent, b);
            if ra != rb {
                // Keep the smaller as root for determinism.
                let (r, c) = if ra < rb { (ra, rb) } else { (rb, ra) };
                parent.insert(c, r);
            }
        }

        for (call_node, pos, arg_reg) in &call_args {
            if let Some(callee) = call_targets.get(call_node) {
                if let Some(&callee_reg) = callee_param_at.get(&(*callee, *pos)) {
                    uunion(&mut parent, *arg_reg, callee_reg);
                }
            }
        }

        // For each (func, reg) that needs canonicalization, follow the union-find to its root, then aggregate fields per root.
        let mut sorted_keys: Vec<(u64, i64)> = reg_fields.keys().copied().collect();
        sorted_keys.sort();

        // Group keys by union-find root. Regs that aren't in `parent` are their own root.
        let mut root_members: HashMap<RTLReg, Vec<(u64, i64)>> = HashMap::new();
        let mut root_fields: HashMap<RTLReg, std::collections::BTreeMap<i64, MemoryChunk>> =
            HashMap::new();
        for key in &sorted_keys {
            let (_func_addr, base_off) = *key;
            // base_off encodes RTLRegs (high bit set), constants, or stack-offset buckets; only RTLReg-encoded keys belong in the union-find.
            if (base_off as u64) & (1u64 << 63) == 0 {
                continue;
            }
            let reg = base_off as RTLReg;
            let root = ufind(&mut parent, reg);
            root_members.entry(root).or_default().push(*key);
            let entry = root_fields.entry(root).or_default();
            for (off, chunk) in &reg_fields[key] {
                // Widen chunks at the same offset: keep the widest one observed across all members of the equivalence class.
                let cur = entry.get(off).cloned();
                let pick = match cur {
                    None => chunk.clone(),
                    Some(prev) => {
                        if chunk_byte_size(chunk) > chunk_byte_size(&prev) {
                            chunk.clone()
                        } else {
                            prev
                        }
                    }
                };
                entry.insert(*off, pick);
            }
        }

        // Assign canonical IDs per root: prefer existing reg_to_canonical entries (min id) so union with struct_recovery's IDs is preserved; otherwise match by exact-shape hash or allocate a new ID.
        let mut root_to_id: HashMap<RTLReg, Ident> = HashMap::new();
        for (root, members) in &root_members {
            let mut existing_ids: Vec<Ident> = members
                .iter()
                .filter_map(|(_, base_off)| reg_to_canonical.get(&(*base_off as Ident)).copied())
                .collect();
            existing_ids.sort();
            if let Some(&id) = existing_ids.first() {
                root_to_id.insert(*root, id);
            }
        }

        let mut sorted_roots: Vec<RTLReg> = root_members.keys().copied().collect();
        sorted_roots.sort();

        for root in &sorted_roots {
            if root_to_id.contains_key(root) {
                continue;
            }
            let fields = match root_fields.get(root) {
                Some(f) if !f.is_empty() => f,
                _ => continue,
            };
            let tuples: Vec<(i64, usize, MemoryChunk)> = fields
                .iter()
                .map(|(o, c)| (*o, chunk_byte_size(c), c.clone()))
                .collect();
            let h = compute_layout_hash_from_tuples(&tuples);
            if let Some(&existing) = shape_to_id.get(&h) {
                root_to_id.insert(*root, existing);
                continue;
            }
            // No exact match; allocate a new ID and register its hash so subsequent identical shapes reuse it.
            let id = next_id as Ident;
            next_id += 1;
            shape_to_id.insert(h, id);
            root_to_id.insert(*root, id);
        }

        // Push new reg_to_struct_id entries (min sid wins). Iterate sorted roots with min-merge: aliased functions can share a reg-Ident across two roots (fresh regs encode node<<6|mreg), and HashMap-order overwrites flickered canonical ids.
        let mut new_rtsi: Vec<(Address, RTLReg, usize)> = Vec::new();
        for root in &sorted_roots {
            let Some(members) = root_members.get(root) else {
                continue;
            };
            if let Some(&id) = root_to_id.get(root) {
                for &(func_addr, base_off) in members {
                    let reg = base_off as Ident;
                    reg_to_canonical
                        .entry(reg)
                        .and_modify(|cur| *cur = (*cur).min(id))
                        .or_insert(id);
                    new_rtsi.push((func_addr, base_off as RTLReg, id as usize));
                }
            }
        }
        new_rtsi.sort();
        new_rtsi.dedup();
        for tuple in new_rtsi {
            db.rel_push("reg_to_struct_id", tuple);
        }
    }

    // SR-2 cross-row closure: re-segregate the per-canonical-id union at the producer and prune both emit_struct_fields and FieldInfo, so no rewrite references a member the definition lacks.
    {
        use crate::decompile::analysis::struct_recovery_pass::chunk_byte_size;
        use std::collections::{BTreeMap, BTreeSet};

        let cid_of = |base_off: i64, canon: &HashMap<Ident, Ident>| -> Ident {
            canon
                .get(&(base_off as Ident))
                .copied()
                .unwrap_or(base_off.unsigned_abs() as Ident)
        };

        // Recovery-owned extents per canonical id: offset -> (end_of_widest_field, min_name). Name is required at exact-alias offsets because a rewrite is only valid when the efield name matches recovery's member (e.g. ofs_9 aliasing _pad_9 would name a non-existent member).
        let mut recovery_extents: HashMap<Ident, BTreeMap<i64, (i64, Ident)>> = HashMap::new();
        for (sid, _, off, ftype, fname) in
            db.rel_iter::<(usize, usize, i64, FieldType, Ident)>("emit_struct_field")
        {
            let end = *off + ftype.size(8) as i64;
            recovery_extents
                .entry(*sid as Ident)
                .or_default()
                .entry(*off)
                .and_modify(|(e, n)| {
                    *e = (*e).max(end);
                    *n = (*n).min(*fname);
                })
                .or_insert((end, *fname));
        }

        let rows: Vec<(Address, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>)> = db
            .rel_iter::<(Address, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>)>("emit_struct_fields")
            .map(|(a, b, f)| (*a, *b, f.clone()))
            .collect();
        let mut union_fields: HashMap<Ident, BTreeSet<(i64, Ident, MemoryChunk)>> = HashMap::new();
        for (_, base_off, fields) in &rows {
            let entry = union_fields
                .entry(cid_of(*base_off, &reg_to_canonical))
                .or_default();
            for f in fields.iter() {
                entry.insert(f.clone());
            }
        }

        // Segregated union per canonical id: offset -> the one kept (name, chunk).
        let mut kept: HashMap<Ident, BTreeMap<i64, (Ident, MemoryChunk)>> = HashMap::new();
        for (cid, fields) in &union_fields {
            // Rebase guard: with negative-offset recovery fields, build_fields_with_padding shifts the layout while Efield rewrites do not, so refuse all efield members for such ids; raw derefs are correct.
            if recovery_extents
                .get(cid)
                .is_some_and(|r| r.keys().next().is_some_and(|&o| o < 0))
            {
                kept.entry(*cid).or_default();
                continue;
            }
            let mut by_offset: Vec<(i64, Ident, MemoryChunk)> = fields.iter().cloned().collect();
            by_offset.sort_by_key(|(off, name, chunk)| {
                (
                    *off,
                    std::cmp::Reverse(chunk_byte_size(chunk)),
                    *name,
                    *chunk,
                )
            });
            by_offset.dedup_by_key(|f| f.0);
            let recov = recovery_extents.get(cid);
            let mut taken: BTreeMap<i64, i64> = recov
                .map(|r| r.iter().map(|(&o, &(e, _))| (o, e)).collect())
                .unwrap_or_default();
            let k = kept.entry(*cid).or_default();
            for (off, name, chunk) in by_offset {
                if let Some(&(rec_end, rec_name)) = recov.and_then(|r| r.get(&off)) {
                    // Exact alias of a recovery field: only valid if name AND width agree (the emitted member access reads the DEF field's width; a wider efield chunk would silently narrow reads at recompile and break pad math for all following fields).
                    if name == rec_name && chunk_byte_size(&chunk) as i64 == rec_end - off {
                        k.insert(off, (name, chunk));
                    }
                    continue;
                }
                let end = off + chunk_byte_size(&chunk) as i64;
                let prev_overlaps = taken
                    .range(..=off)
                    .next_back()
                    .is_some_and(|(_, &pe)| pe > off);
                let next_overlaps = taken.range(off..).next().is_some_and(|(&ns, _)| ns < end);
                if !prev_overlaps && !next_overlaps {
                    taken.insert(off, end);
                    k.insert(off, (name, chunk));
                }
            }
        }

        // Prune relation rows: a union of subsets of a non-overlapping set is non-overlapping, and the kept (name, chunk) winner always survives in its contributing row.
        let mut dropped = 0usize;
        let pruned: ascent::boxcar::Vec<(Address, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>)> = rows
            .iter()
            .map(|(fa, base, fields)| {
                let k = &kept[&cid_of(*base, &reg_to_canonical)];
                let nf: Vec<(i64, Ident, MemoryChunk)> = fields
                    .iter()
                    .filter(|(off, name, chunk)| {
                        k.get(off).is_some_and(|(kn, kc)| kn == name && kc == chunk)
                    })
                    .cloned()
                    .collect();
                if nf.len() != fields.len() {
                    dropped += fields.len() - nf.len();
                    (*fa, *base, Arc::new(nf))
                } else {
                    (*fa, *base, fields.clone())
                }
            })
            .collect();
        if std::env::var("SR2_TRACE").is_ok() {
            let total_in: usize = rows.iter().map(|(_, _, f)| f.len()).sum();
            eprintln!(
                "[sr2] cross-row segregation: {} canonical ids, {} row fields, {} dropped",
                kept.len(),
                total_in,
                dropped
            );
            let mut srows: Vec<_> = rows
                .iter()
                .map(|(fa, b, f)| (*fa, *b, f.as_ref().clone()))
                .collect();
            srows.sort();
            for (fa, b, f) in &srows {
                eprintln!(
                    "[sr2]   row func={:#x} base={:#x} cid={:#x} fields={:?}",
                    fa,
                    b,
                    cid_of(*b, &reg_to_canonical),
                    f
                );
            }
            let mut scids: Vec<_> = kept.iter().collect();
            scids.sort_by_key(|(cid, _)| **cid);
            for (cid, k) in scids {
                eprintln!(
                    "[sr2]   kept cid={:#x} {:?} recovery_extents={:?}",
                    cid,
                    k,
                    recovery_extents.get(cid)
                );
            }
        }
        if dropped > 0 {
            db.rel_set("emit_struct_fields", pruned);
        }

        for fi in func_field_info.values_mut() {
            fi.retain(|(base, off), nc| {
                match kept
                    .get(&cid_of(*base, &reg_to_canonical))
                    .and_then(|k| k.get(off))
                {
                    Some(kept_nc) => {
                        *nc = *kept_nc;
                        true
                    }
                    None => false,
                }
            });
        }
    }

    // This recovery is independent of struct-field discovery.  Run it before
    // the pass-through fast path so functions with only opaque address-taken
    // frame storage still retain that storage.
    size_opaque_escaped_frame_buffers(db);

    let node_to_func: HashMap<u64, u64> = {
        let mut groups: HashMap<u64, u64> = HashMap::new();
        for (n, f) in db.rel_iter::<(Node, Address)>("instr_in_function") {
            groups
                .entry(*n)
                .and_modify(|curr| *curr = (*curr).min(*f))
                .or_insert(*f);
        }
        groups
    };

    // Escaped stack-region reconstruction is independent of named struct
    // recovery.  In particular, compiler-generated option/state objects often
    // have mixed-width fields but no source-level struct identity.  Synthesize
    // their exact-width stores before taking the field-free pass-through path.
    let struct_construction = synthesize_struct_construction(db, &node_to_func, &func_field_info);

    // Publish every backing object before the field-free fast path.  Runtime
    // indexed stack addresses are a separate source of layout evidence and
    // must see both opaque escaped objects and buffers synthesized from exact
    // field stores.  In particular, a compiler may keep an index anchor one
    // element before a buffer and pre-increment the index; those two addresses
    // still denote one physical frame range and cannot become disjoint C
    // locals.
    for (func, id, size) in &struct_construction.stack_buffers {
        db.stack_struct_buffers
            .entry(*func)
            .or_default()
            .entry(*id as RTLReg)
            .and_modify(|current| *current = (*current).max(*size))
            .or_insert(*size);
    }
    size_indexed_stack_arrays(db);

    if func_field_info.is_empty() && struct_construction.is_empty() {
        // No struct fields; copy clight_stmt directly to clight_stmt
        let pass_through: ascent::boxcar::Vec<_> = db
            .rel_iter::<(Node, ClightStmt)>("clight_stmt")
            .map(|(n, s)| (*n, s.clone()))
            .collect();
        db.rel_set("clight_stmt", pass_through);

        let pass_through_emit: ascent::boxcar::Vec<_> = db
            .rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt")
            .map(|(a, n, s)| (*a, *n, s.clone()))
            .collect();
        db.rel_set("emit_clight_stmt", pass_through_emit);

        let pass_through_dead: ascent::boxcar::Vec<_> = db
            .rel_iter::<(Address, Node, ClightStmt)>("clight_stmt_dead")
            .map(|(a, n, s)| (*a, *n, s.clone()))
            .collect();
        db.rel_set("clight_stmt_dead", pass_through_dead);
        return;
    }

    let new_clight_stmt: ascent::boxcar::Vec<_> = db
        .rel_iter::<(Node, ClightStmt)>("clight_stmt")
        .flat_map(|(node, stmt)| {
            // Apply Oaddrstack rewrite if this node has one
            let stmt = if let Some(rewritten) = struct_construction.rewritten_stmts.get(node) {
                rewritten.clone()
            } else {
                stmt.clone()
            };
            if let Some(fi) = node_to_func
                .get(node)
                .and_then(|fa| func_field_info.get(fa))
            {
                let rewritten = rewrite_clight_stmt_fields(&stmt, fi, &reg_to_canonical, ptr_size);
                let mut results = vec![(*node, rewritten.clone())];
                if rewritten != stmt {
                    results.push((*node, stmt));
                }
                results
            } else {
                vec![(*node, stmt)]
            }
        })
        .chain(
            struct_construction
                .new_stmts
                .iter()
                .map(|(node, stmt)| (*node, stmt.clone())),
        )
        .collect();
    db.rel_set("clight_stmt", new_clight_stmt);

    let new_emit: ascent::boxcar::Vec<_> = db
        .rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt")
        .flat_map(|(addr, node, stmt)| {
            let stmt = if let Some(rewritten) = struct_construction.rewritten_stmts.get(node) {
                rewritten.clone()
            } else {
                stmt.clone()
            };
            if let Some(fi) = func_field_info.get(addr) {
                let rewritten = rewrite_clight_stmt_fields(&stmt, fi, &reg_to_canonical, ptr_size);
                // For Sset where field rewriting changed type from integral to pointer, emit an additional cast-back candidate for integer-typed declarations.
                let extra = match (&stmt, &rewritten) {
                    (ClightStmt::Sset(_, orig_expr), ClightStmt::Sset(id, new_expr)) => {
                        let orig_ty = clight_expr_type(orig_expr);
                        let new_ty = clight_expr_type(new_expr);
                        if is_integral_type(&orig_ty) && !is_integral_type(&new_ty) {
                            Some((
                                *addr,
                                *node,
                                ClightStmt::Sset(
                                    *id,
                                    ClightExpr::Ecast(Box::new(new_expr.clone()), orig_ty),
                                ),
                            ))
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
        .chain(
            struct_construction
                .new_emit_stmts
                .iter()
                .map(|(a, n, s)| (*a, *n, s.clone())),
        )
        .collect();
    db.rel_set("emit_clight_stmt", new_emit);

    let new_dead: ascent::boxcar::Vec<_> = db
        .rel_iter::<(Address, Node, ClightStmt)>("clight_stmt_dead")
        .map(|(addr, node, stmt)| {
            if let Some(fi) = func_field_info.get(addr) {
                (
                    *addr,
                    *node,
                    rewrite_clight_stmt_fields(stmt, fi, &reg_to_canonical, ptr_size),
                )
            } else {
                (*addr, *node, stmt.clone())
            }
        })
        .collect();
    db.rel_set("clight_stmt_dead", new_dead);

    // Push XstructPtr type candidates for registers upgraded to struct pointer types, using canonical struct IDs when available.
    let mut seen_struct_regs: std::collections::HashSet<(RTLReg, usize)> =
        std::collections::HashSet::new();
    for (_func_addr, fi) in &func_field_info {
        for (&(base_key, _field_off), _) in fi {
            let reg = base_key as u64 as RTLReg;
            let struct_id = reg_to_canonical
                .get(&(reg as Ident))
                .copied()
                .unwrap_or_else(|| base_key.unsigned_abs() as Ident);
            if seen_struct_regs.insert((reg, struct_id)) {
                db.rel_push(
                    "emit_var_type_candidate",
                    (reg, XType::XstructPtr(struct_id)),
                );
            }
        }
    }
}

/// Recover opaque, address-taken backing storage in a stack frame.
///
/// A slot whose address escapes into a call but which this function never loads
/// or stores itself carries no evidence at all of its own width: the scalar type
/// on its declaration is a default, not a measurement, so the callee writes past
/// the end of it -- `lstat` filling 144 bytes of `struct stat` into an `int`, or
/// `strtoumax` storing an 8-byte end pointer through a 4-byte out-parameter.
///
/// The evidence that does exist is the frame layout: the storage cannot reach
/// the next offset the frame models, so that gap is its extent, and the frame
/// top bounds the highest slot.  Bounding this way is also what keeps the buffer
/// from swallowing a separately modeled local, since any such local ends it.  A
/// slot with a direct scalar access has real width evidence and keeps its scalar
/// declaration; so does one whose offset two different canonical locals claim,
/// where the slot model itself is ambiguous.
///
/// Offsets here are `Ainstack` displacements, counted upward from the stack
/// pointer, so this frame is `[0, stacksize)` and an offset at or above the top
/// addresses the caller's frame instead.
fn size_opaque_escaped_frame_buffers(db: &mut DecompileDB) {
    let mut directly_accessed: HashMap<Address, HashSet<i64>> = HashMap::new();
    for (func, ofs, _) in db.rel_iter::<(Address, i64, MemoryChunk)>("stack_var_chunk") {
        directly_accessed.entry(*func).or_default().insert(*ofs);
    }

    let mut stack_locals: HashMap<Address, HashSet<(i64, RTLReg)>> = HashMap::new();
    for (func, _, ofs, local) in db.rel_iter::<(Address, Address, i64, RTLReg)>("stack_var") {
        stack_locals
            .entry(*func)
            .or_default()
            .insert((*ofs, *local));
    }

    // Every offset the frame models, from either source: each one starts a
    // different object and so ends the opaque region below it.
    let mut boundaries: HashMap<Address, BTreeSet<i64>> = HashMap::new();
    for (func, offsets) in &directly_accessed {
        boundaries
            .entry(*func)
            .or_default()
            .extend(offsets.iter().copied());
    }
    for (func, locals) in &stack_locals {
        boundaries
            .entry(*func)
            .or_default()
            .extend(locals.iter().map(|(ofs, _)| *ofs));
    }

    let mut frame_sizes: HashMap<Address, u64> = HashMap::new();
    for (func, _, _, size) in db.rel_iter::<(Address, Address, Symbol, u64)>("func_stacksz") {
        if *size == 0 || *size > 1 << 20 {
            continue;
        }
        frame_sizes
            .entry(*func)
            .and_modify(|current| *current = (*current).max(*size))
            .or_insert(*size);
    }

    // An offset inside an escaped region is one of that region's own fields,
    // reached through the base pointer, not the start of a neighbouring object.
    // Such an offset must not cut the region short, and the far end of the
    // furthest field is a floor on how much storage the region needs.
    let mut region_fields: HashMap<(Address, i64), BTreeSet<i64>> = HashMap::new();
    let mut region_extent: HashMap<(Address, i64), i64> = HashMap::new();
    for relation in [
        "escaped_stack_region_field",
        "escaped_stack_region_caller_field",
    ] {
        for (func, base_ofs, field_ofs, chunk) in
            db.rel_iter::<(Address, i64, i64, MemoryChunk)>(relation)
        {
            if *field_ofs < 0 || matches!(chunk, MemoryChunk::Unknown) {
                continue;
            }
            region_fields
                .entry((*func, *base_ofs))
                .or_default()
                .insert(*base_ofs + *field_ofs);
            let end = *field_ofs + memchunk_byte_size(chunk) as i64;
            region_extent
                .entry((*func, *base_ofs))
                .and_modify(|current| *current = (*current).max(end))
                .or_insert(end);
        }
    }

    // The fields observed here are only what the caller itself touched.  What an
    // external callee writes through the pointer is invisible that way, and RTL
    // already derives the region's real extent from the ABI and from the frame
    // -- 144 bytes for a struct stat whatever the caller reads back.  Raising
    // the floor by it is the same statement the field ends make, from better
    // evidence: over-reserving wastes frame bytes, under-reserving is the stack
    // smash, and the other consumer of these regions already sizes them this way.
    for (func, base_ofs, extent) in
        db.rel_iter::<(Address, i64, i64)>("escaped_stack_region_extent")
    {
        region_extent
            .entry((*func, *base_ofs))
            .and_modify(|current| *current = (*current).max(*extent))
            .or_insert(*extent);
    }

    // Whole-slot unification lets a slot's canonical local also be the name of a
    // register-resident value, and such a local is a variable, not storage: it
    // is negated, compared and passed by value, none of which an array
    // declaration can express.  Backing storage reaches RTL only through
    // `Ainstack` addressing, never as an operand, so an operand appearance is
    // exactly the evidence that this local carries a value.
    let mut value_regs: HashSet<RTLReg> = HashSet::new();
    for (_node, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        let (args, defs): (&[RTLReg], [Option<RTLReg>; 2]) = match inst {
            RTLInst::Iop(_, args, dst) => (args, [Some(*dst), None]),
            RTLInst::Iload(_, _, args, dst) => (args, [Some(*dst), None]),
            RTLInst::Istore(_, _, args, src) => (args, [Some(*src), None]),
            RTLInst::Icall(_, callee, args, dst, _) => {
                (args, [*dst, callee.as_ref().left().copied()])
            }
            RTLInst::Itailcall(_, callee, args) => (args, [callee.as_ref().left().copied(), None]),
            RTLInst::Icond(_, args, _, _) => (args, [None, None]),
            RTLInst::Ijumptable(index, _) => (&[], [Some(*index), None]),
            RTLInst::Ireturn(src) => (&[], [Some(*src), None]),
            _ => (&[], [None, None]),
        };
        value_regs.extend(args.iter().copied());
        value_regs.extend(defs.into_iter().flatten());
    }

    let escaped: Vec<(Address, i64, RTLReg)> = db
        .rel_iter::<(Address, i64, RTLReg)>("slot_escaped_canonical")
        .copied()
        .collect();

    // Diagnostic hook (env-gated, like GA_DUMP) for escaped-storage sizing work.
    let trace = std::env::var("ESC_DUMP").is_ok();
    for (func, ofs, local) in escaped {
        let mut reject = |why: &str| {
            if trace {
                eprintln!("[ESC] {func:#x} ofs={ofs} local={local:#x} rejected: {why}");
            }
        };
        // An Ainstack offset counts upward from the stack pointer, so the frame
        // occupies [0, stacksize) and anything at or above the top belongs to
        // the caller: an incoming stack argument, not storage to widen here.
        let Some(frame_top) = frame_sizes
            .get(&func)
            .copied()
            .and_then(|size| i64::try_from(size).ok())
        else {
            reject("no recovered frame size to bound the region");
            continue;
        };
        if ofs < 0 || ofs >= frame_top {
            reject("offset lies outside this function's own frame");
            continue;
        }
        if directly_accessed
            .get(&func)
            .is_some_and(|offsets| offsets.contains(&ofs))
        {
            reject("direct scalar access gives real width evidence");
            continue;
        }
        if stack_locals.get(&func).is_some_and(|locals| {
            locals
                .iter()
                .any(|(inner_ofs, inner_local)| *inner_ofs == ofs && *inner_local != local)
        }) {
            reject("two canonical locals claim this offset");
            continue;
        }
        if value_regs.contains(&local) {
            reject("local carries a value, so it is a variable and not storage");
            continue;
        }
        let own_fields = region_fields.get(&(func, ofs));
        let limit = boundaries
            .get(&func)
            .and_then(|offsets| {
                offsets
                    .range((ofs + 1)..=frame_top)
                    .find(|boundary| !own_fields.is_some_and(|fields| fields.contains(boundary)))
                    .copied()
            })
            .unwrap_or(frame_top);
        let gap = limit - ofs;
        let floor = region_extent.get(&(func, ofs)).copied().unwrap_or(0);
        let Some(size) = Some(gap.max(floor)).filter(|size| *size > 0) else {
            reject("no positive extent below the next modeled offset");
            continue;
        };
        if trace {
            eprintln!("[ESC] {func:#x} ofs={ofs} local={local:#x} sized {size} (limit {limit})");
        }
        db.stack_struct_buffers
            .entry(func)
            .or_default()
            .entry(local)
            .and_modify(|current| *current = (*current).max(size))
            .or_insert(size);
    }
}

/// Give runtime-indexed frame addresses bounded backing storage.
///
/// A positive `Ainstack` displacement is inside the post-allocation frame and
/// extends to the next modeled slot (or the frame top); the older negative
/// frame convention continues to extend to offset zero.  When such an indexed
/// range overlaps or abuts an address-taken byte buffer, both ranges must use
/// one C object.  Keeping them as two locals destroys machine-level aliasing --
/// the common `base - element_size`, pre-increment, load shape then reads an
/// unrelated scalar instead of the buffer.  The coalesced object is byte-sized
/// and `stack_buffer_alias` records the exact offset of every absorbed root.
fn size_indexed_stack_arrays(db: &mut DecompileDB) {
    use std::ops::Bound::{Excluded, Included};

    // node -> function ownership for every real RTL instruction.  Split
    // fragments can transiently publish more than one owner, so consume only
    // singleton ownership instead of choosing by relation iteration order.
    let mut node_funcs: BTreeMap<Node, BTreeSet<Address>> = BTreeMap::new();
    for (n, f) in db.rel_iter::<(Node, Address)>("instr_in_function") {
        node_funcs.entry(*n).or_default().insert(*f);
    }

    // Olea/Oleal(Ainstack(ofs)) base regs.  Retain every observation and use
    // only singleton origins below; an SSA-id collision must not manufacture a
    // frame address.
    let mut lea_base: BTreeMap<RTLReg, BTreeSet<(Address, i64)>> = BTreeMap::new();
    for (node, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        if let RTLInst::Iop(op, args, dst) = inst {
            if args.is_empty() {
                let base_ofs = match op {
                    Operation::Olea(Addressing::Ainstack(o))
                    | Operation::Oleal(Addressing::Ainstack(o)) => Some(*o),
                    _ => None,
                };
                if let Some(o) = base_ofs {
                    if let Some(funcs) = node_funcs.get(node) {
                        let mut funcs = funcs.iter();
                        if let Some(&func) = funcs.next() {
                            if funcs.next().is_none() {
                                lea_base.entry(*dst).or_default().insert((func, o));
                            }
                        }
                    }
                }
            }
        }
    }

    // `stack_var` supplies the canonical local at an offset.  Require both
    // directions to be unique: two locals at one address or one local naming
    // two addresses is an ambiguous layout, not alias evidence.
    let mut slot_locals: BTreeMap<(Address, i64), BTreeSet<RTLReg>> = BTreeMap::new();
    let mut local_offsets: BTreeMap<(Address, RTLReg), BTreeSet<i64>> = BTreeMap::new();
    let mut boundaries: BTreeMap<Address, BTreeSet<i64>> = BTreeMap::new();
    for (func, _node, ofs, reg) in db.rel_iter::<(Address, Address, i64, RTLReg)>("stack_var") {
        slot_locals.entry((*func, *ofs)).or_default().insert(*reg);
        local_offsets.entry((*func, *reg)).or_default().insert(*ofs);
        boundaries.entry(*func).or_default().insert(*ofs);
    }

    let mut frame_tops: BTreeMap<Address, i64> = BTreeMap::new();
    for (func, _, _, size) in db.rel_iter::<(Address, Address, Symbol, u64)>("func_stacksz") {
        let Ok(size) = i64::try_from(*size) else {
            continue;
        };
        if size <= 0 || size > 1 << 20 {
            continue;
        }
        frame_tops
            .entry(*func)
            .and_modify(|current| *current = (*current).max(size))
            .or_insert(size);
    }

    let directly_accessed: HashSet<(Address, i64)> = db
        .rel_iter::<(Address, i64, MemoryChunk)>("stack_var_chunk")
        .map(|(func, ofs, _)| (*func, *ofs))
        .collect();

    // (func, local) -> (frame start, exclusive end, element chunk, count).
    // A base reg used as args[0] of an indexed access is an array base.  The
    // addressing mode already carries any machine scale, while this chunk
    // supplies the declaration width for standalone arrays.
    let mut sized: BTreeMap<(Address, RTLReg), (i64, i64, MemoryChunk, usize)> = BTreeMap::new();
    for (_node, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        let (chunk, addressing, args) = match inst {
            RTLInst::Iload(c, a, args, _) | RTLInst::Istore(c, a, args, _) => (c, a, args),
            _ => continue,
        };
        let indexed = matches!(
            addressing,
            Addressing::Aindexed2scaled(_, _) | Addressing::Aindexed2(_)
        );
        if !indexed || args.is_empty() {
            continue;
        }
        let base = args[0];
        let Some(origins) = lea_base.get(&base) else {
            continue;
        };
        let mut origins = origins.iter();
        let Some(&(func, base_ofs)) = origins.next() else {
            continue;
        };
        if origins.next().is_some() || directly_accessed.contains(&(func, base_ofs)) {
            continue;
        }
        let Some(locals) = slot_locals.get(&(func, base_ofs)) else {
            continue;
        };
        let mut locals = locals.iter();
        let Some(&local) = locals.next() else {
            continue;
        };
        if locals.next().is_some()
            || local_offsets
                .get(&(func, local))
                .is_none_or(|offsets| offsets.len() != 1)
        {
            continue;
        }

        let limit = if base_ofs < 0 {
            0
        } else {
            let Some(&frame_top) = frame_tops.get(&func) else {
                continue;
            };
            if base_ofs >= frame_top {
                continue;
            }
            boundaries
                .get(&func)
                .and_then(|offsets| {
                    offsets
                        .range((Excluded(base_ofs), Included(frame_top)))
                        .next()
                        .copied()
                })
                .unwrap_or(frame_top)
        };
        let byte_size = limit.saturating_sub(base_ofs);
        if byte_size <= 0 || byte_size > 1 << 20 {
            continue;
        }
        let elem = memchunk_byte_size(chunk).max(1);
        let count = ((byte_size as usize) + elem - 1) / elem;
        // Keep the SMALLEST element width seen (most conservative stride) and the largest count for it.
        let e = sized
            .entry((func, local))
            .or_insert((base_ofs, limit, *chunk, count));
        if elem < memchunk_byte_size(&e.2).max(1) {
            *e = (base_ofs, limit, *chunk, count);
        } else if *chunk == e.2 && count > e.3 {
            e.3 = count;
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum RangeKind {
        Indexed,
        ByteBuffer,
    }

    #[derive(Clone, Copy, Debug)]
    struct StorageRange {
        func: Address,
        start: i64,
        end: i64,
        local: RTLReg,
        kind: RangeKind,
    }

    let mut ranges = Vec::new();
    for (&(func, local), &(start, end, _, _)) in &sized {
        ranges.push(StorageRange {
            func,
            start,
            end,
            local,
            kind: RangeKind::Indexed,
        });
    }
    for (&func, buffers) in &db.stack_struct_buffers {
        for (&local, &size) in buffers {
            if size <= 0 || size > 1 << 20 {
                continue;
            }
            let Some(offsets) = local_offsets.get(&(func, local)) else {
                continue;
            };
            let mut offsets = offsets.iter();
            let Some(&start) = offsets.next() else {
                continue;
            };
            if offsets.next().is_some() {
                continue;
            }
            let Some(end) = start.checked_add(size) else {
                continue;
            };
            ranges.push(StorageRange {
                func,
                start,
                end,
                local,
                kind: RangeKind::ByteBuffer,
            });
        }
    }
    ranges.sort_by_key(|range| {
        (
            range.func,
            range.start,
            range.end,
            matches!(range.kind, RangeKind::Indexed),
            range.local,
        )
    });

    fn find_root(parents: &mut [usize], mut node: usize) -> usize {
        while parents[node] != node {
            let parent = parents[node];
            parents[node] = parents[parent];
            node = parents[node];
        }
        node
    }

    let mut parents: Vec<usize> = (0..ranges.len()).collect();
    for left in 0..ranges.len() {
        for right in (left + 1)..ranges.len() {
            if ranges[right].func != ranges[left].func {
                break;
            }
            if ranges[right].start > ranges[left].end {
                break;
            }
            let overlaps =
                ranges[left].start < ranges[right].end && ranges[right].start < ranges[left].end;
            let abuts =
                ranges[left].end == ranges[right].start || ranges[right].end == ranges[left].start;
            if !overlaps
                && !(abuts
                    && (ranges[left].kind == RangeKind::Indexed
                        || ranges[right].kind == RangeKind::Indexed))
            {
                continue;
            }
            let left_root = find_root(&mut parents, left);
            let right_root = find_root(&mut parents, right);
            if left_root != right_root {
                parents[right_root] = left_root;
            }
        }
    }

    let mut components: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for index in 0..ranges.len() {
        let root = find_root(&mut parents, index);
        components.entry(root).or_default().push(index);
    }

    let mut coalesced_indexed = HashSet::new();
    let mut aliases = Vec::new();
    for members in components.values() {
        let has_indexed = members
            .iter()
            .any(|index| ranges[*index].kind == RangeKind::Indexed);
        let has_buffer = members
            .iter()
            .any(|index| ranges[*index].kind == RangeKind::ByteBuffer);
        if !has_indexed || !has_buffer {
            continue;
        }

        let func = ranges[members[0]].func;
        let start = members
            .iter()
            .map(|index| ranges[*index].start)
            .min()
            .unwrap();
        let end = members
            .iter()
            .map(|index| ranges[*index].end)
            .max()
            .unwrap();
        let Some(size) = end
            .checked_sub(start)
            .filter(|size| *size > 0 && *size <= 1 << 20)
        else {
            continue;
        };

        // A local must denote one physical start throughout the component.
        // Otherwise the existing slot model is ambiguous and no coalescing is
        // justified.
        let mut member_starts = BTreeMap::new();
        let mut ambiguous = false;
        for index in members {
            let range = ranges[*index];
            if member_starts
                .insert(range.local, range.start)
                .is_some_and(|old| old != range.start)
            {
                ambiguous = true;
                break;
            }
        }
        if ambiguous {
            continue;
        }

        // Prefer an existing byte-buffer name at the lowest address, then the
        // deterministic smallest local id.  If the indexed prefix begins
        // lower, it necessarily becomes the backing name so every alias offset
        // remains non-negative C array indexing.
        let backing = members
            .iter()
            .map(|index| ranges[*index])
            .filter(|range| range.start == start)
            .min_by_key(|range| (matches!(range.kind, RangeKind::Indexed), range.local))
            .unwrap();

        for index in members {
            let range = ranges[*index];
            match range.kind {
                RangeKind::Indexed => {
                    coalesced_indexed.insert((func, range.local));
                    if let Some(func_arrays) = db.stack_array_buffers.get_mut(&func) {
                        func_arrays.remove(&range.local);
                    }
                }
                RangeKind::ByteBuffer => {
                    if let Some(func_buffers) = db.stack_struct_buffers.get_mut(&func) {
                        func_buffers.remove(&range.local);
                    }
                }
            }
        }

        db.stack_struct_buffers
            .entry(func)
            .or_default()
            .insert(backing.local, size);
        for (local, member_start) in member_starts {
            if local == backing.local {
                continue;
            }
            let Some(offset) = member_start
                .checked_sub(start)
                .and_then(|offset| usize::try_from(offset).ok())
            else {
                continue;
            };
            aliases.push((func, local, backing.local, offset));
        }
        if std::env::var("ESC_DUMP").is_ok() {
            eprintln!(
                "[STACK-ALIAS] {func:#x} [{start}, {end}) -> local={:#x} aliases={}",
                backing.local,
                members.len().saturating_sub(1)
            );
        }
    }

    db.stack_struct_buffers
        .retain(|_, buffers| !buffers.is_empty());
    db.stack_array_buffers
        .retain(|_, buffers| !buffers.is_empty());
    for alias in aliases {
        db.rel_push("stack_buffer_alias", alias);
    }

    for ((func, local), (_, _, chunk, count)) in sized {
        if coalesced_indexed.contains(&(func, local)) {
            continue;
        }
        db.stack_array_buffers
            .entry(func)
            .or_default()
            .entry(local)
            .and_modify(|current| {
                let old_width = memchunk_byte_size(&current.0).max(1);
                let new_width = memchunk_byte_size(&chunk).max(1);
                if new_width < old_width || (new_width == old_width && count > current.1) {
                    *current = (chunk, count);
                }
            })
            .or_insert((chunk, count));
    }
}

/// Byte size of a memory chunk (element width for array sizing).
fn memchunk_byte_size(c: &MemoryChunk) -> usize {
    match c {
        MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned => 1,
        MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned => 2,
        MemoryChunk::MInt32 | MemoryChunk::MFloat32 => 4,
        MemoryChunk::MInt64 | MemoryChunk::MFloat64 | MemoryChunk::MAny64 => 8,
        _ => 1,
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
    /// (func_addr, struct_local_id, struct_size): address-taken stack regions to declare as `unsigned char[struct_size]` so the raw byte-offset store candidates are in-bounds. Drained into db.stack_struct_buffers.
    stack_buffers: Vec<(u64, Ident, i64)>,
}

impl StructConstructionResult {
    fn is_empty(&self) -> bool {
        self.new_stmts.is_empty()
            && self.new_emit_stmts.is_empty()
            && self.rewritten_stmts.is_empty()
            && self.stack_buffers.is_empty()
    }
}

fn unsigned_chunk_for_byte_width(size: usize) -> Option<MemoryChunk> {
    match size {
        1 => Some(MemoryChunk::MInt8Unsigned),
        2 => Some(MemoryChunk::MInt16Unsigned),
        4 => Some(MemoryChunk::MInt32),
        8 => Some(MemoryChunk::MInt64),
        _ => None,
    }
}

/// Recover the exact destination width of each raw immediate MOV.  `Typ` on
/// `mach_imm_stack_init` is a register class and deliberately cannot
/// distinguish byte/word/dword stack stores; the memory operand size can.
fn exact_immediate_stack_init_chunks(db: &DecompileDB) -> HashMap<Address, MemoryChunk> {
    use std::collections::{BTreeMap, BTreeSet};

    let mut operand_sizes: HashMap<Symbol, BTreeSet<usize>> = HashMap::new();
    for (operand, _, _, _, _, _, size) in
        db.rel_iter::<(Symbol, Symbol, Symbol, Symbol, i64, i64, usize)>("op_indirect")
    {
        if unsigned_chunk_for_byte_width(*size).is_some() {
            operand_sizes.entry(*operand).or_default().insert(*size);
        }
    }

    let mut addr_chunks: BTreeMap<Address, BTreeSet<MemoryChunk>> = BTreeMap::new();
    for (addr, dst, _) in db.rel_iter::<(Address, Symbol, Symbol)>("pmov") {
        let Some(sizes) = operand_sizes.get(dst) else {
            continue;
        };
        for size in sizes {
            if let Some(chunk) = unsigned_chunk_for_byte_width(*size) {
                addr_chunks.entry(*addr).or_default().insert(chunk);
            }
        }
    }

    addr_chunks
        .into_iter()
        .filter_map(|(addr, chunks)| {
            (chunks.len() == 1).then(|| (addr, *chunks.iter().next().unwrap()))
        })
        .collect()
}

fn immediate_value_expr(value: i64, chunk: &MemoryChunk) -> ClightExpr {
    if matches!(chunk, MemoryChunk::MInt64 | MemoryChunk::MAny64) {
        ClightExpr::EconstLong(value, default_long_type())
    } else {
        ClightExpr::EconstInt(value as i32, default_int_type())
    }
}

fn raw_stack_buffer_store(
    base_local: Ident,
    buffer_size: i64,
    byte_offset: i64,
    value: i64,
    chunk: &MemoryChunk,
) -> ClightStmt {
    let char_ty = ClightType::Tint(
        ClightIntSize::I8,
        ClightSignedness::Unsigned,
        default_attr(),
    );
    let char_ptr = pointer_to(char_ty.clone());
    let buffer_ty = ClightType::Tarray(Arc::new(char_ty), buffer_size, default_attr());
    let field_ty = clight_type_from_chunk(chunk);
    let byte_addr = ClightExpr::Ebinop(
        ClightBinaryOp::Oadd,
        Box::new(ClightExpr::Ecast(
            Box::new(ClightExpr::Eaddrof(
                Box::new(ClightExpr::Evar(base_local, buffer_ty.clone())),
                pointer_to(buffer_ty),
            )),
            char_ptr.clone(),
        )),
        Box::new(ClightExpr::EconstLong(byte_offset, default_long_type())),
        char_ptr,
    );
    let lhs = ClightExpr::Ederef(
        Box::new(ClightExpr::Ecast(
            Box::new(byte_addr),
            pointer_to(field_ty.clone()),
        )),
        field_ty,
    );
    ClightStmt::Sassign(lhs, immediate_value_expr(value, chunk))
}

/// Materialize initializers into one backing object only when RTL has proven
/// that a pointer to the base escapes and a callee (possibly through wrapper
/// calls) accesses at least two exact constant-offset fields.  This restores C
/// aliasing without guessing a source struct layout.
fn synthesize_escaped_stack_region_construction(
    db: &DecompileDB,
    func_stack_inits: &HashMap<u64, Vec<(u64, i64, i64, Typ)>>,
    result: &mut StructConstructionResult,
) {
    use crate::decompile::analysis::struct_recovery_pass::chunk_byte_size;
    use std::collections::{BTreeMap, BTreeSet};

    if std::env::var("TMPDUMP_ESCAPED").is_ok() {
        for r in [
            "escaped_stack_region_field",
            "escaped_stack_region_caller_field",
        ] {
            for (f, b, o, c) in db.rel_iter::<(Address, i64, i64, MemoryChunk)>(r) {
                eprintln!("TMPDUMP {r} func={f:#x} base={b} fofs={o} chunk={c:?}");
            }
        }
        for (f, b, e) in db.rel_iter::<(Address, i64, i64)>("escaped_stack_region_extent") {
            eprintln!("TMPDUMP extent func={f:#x} base={b} extent={e}");
        }
        for (f, o, l) in db.rel_iter::<(Address, i64, RTLReg)>("slot_escaped_canonical") {
            eprintln!("TMPDUMP slot_escaped_canonical func={f:#x} ofs={o} local={l:#x}");
        }
    }

    let exact_chunks = exact_immediate_stack_init_chunks(db);

    let mut base_locals: BTreeMap<(Address, i64), RTLReg> = BTreeMap::new();
    for (func, ofs, local) in db.rel_iter::<(Address, i64, RTLReg)>("slot_escaped_canonical") {
        base_locals
            .entry((*func, *ofs))
            .and_modify(|current| *current = (*current).min(*local))
            .or_insert(*local);
    }
    for (func, ofs, local) in db.rel_iter::<(Address, i64, RTLReg)>("slot_escaped_region_canonical")
    {
        base_locals
            .entry((*func, *ofs))
            .and_modify(|current| *current = (*current).min(*local))
            .or_insert(*local);
    }

    let mut regions: BTreeMap<(Address, i64), BTreeMap<i64, BTreeSet<MemoryChunk>>> =
        BTreeMap::new();
    for (func, base_ofs, field_ofs, chunk) in
        db.rel_iter::<(Address, i64, i64, MemoryChunk)>("escaped_stack_region_field")
    {
        if *field_ofs < 0 || matches!(chunk, MemoryChunk::Unknown) {
            continue;
        }
        regions
            .entry((*func, *base_ofs))
            .or_default()
            .entry(*field_ofs)
            .or_default()
            .insert(*chunk);
    }

    for ((func, base_ofs), fields) in regions {
        if fields.len() < 2 || !fields.contains_key(&0) {
            continue;
        }
        let Some(&base_local) = base_locals.get(&(func, base_ofs)) else {
            continue;
        };

        let region_size = fields
            .iter()
            .filter_map(|(field_ofs, chunks)| {
                chunks
                    .iter()
                    .map(chunk_byte_size)
                    .max()
                    .and_then(|width| field_ofs.checked_add(width as i64))
            })
            .max()
            .unwrap_or(0);
        if region_size <= 0 || region_size > 1 << 20 {
            continue;
        }
        let uniform_array = fields
            .values()
            .next()
            .filter(|chunks| chunks.len() == 1)
            .and_then(|chunks| chunks.iter().next())
            .is_some_and(|element_chunk| {
                let width = chunk_byte_size(element_chunk) as i64;
                width > 0
                    && fields.values().all(|chunks| {
                        chunks.len() == 1 && chunks.iter().next() == Some(element_chunk)
                    })
                    && fields
                        .keys()
                        .enumerate()
                        .all(|(idx, ofs)| *ofs == idx as i64 * width)
            });
        if !uniform_array {
            result
                .stack_buffers
                .push((func, base_local as Ident, region_size));
        }

        let Some(inits) = func_stack_inits.get(&func) else {
            continue;
        };
        let region_end = match base_ofs.checked_add(region_size) {
            Some(end) => end,
            None => continue,
        };
        for (addr, ofs, value, _) in inits {
            let Some(chunk) = exact_chunks.get(addr) else {
                continue;
            };
            let width = chunk_byte_size(chunk) as i64;
            let Some(store_end) = ofs.checked_add(width) else {
                continue;
            };
            if *ofs < base_ofs || store_end > region_end {
                continue;
            }
            let stmt = raw_stack_buffer_store(
                base_local as Ident,
                region_size,
                *ofs - base_ofs,
                *value,
                chunk,
            );
            result.new_stmts.push((*addr, stmt.clone()));
            result.new_emit_stmts.push((func, *addr, stmt));
        }
    }
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
        stack_buffers: Vec::new(),
    };

    // Collect mach_imm_stack_init per function: (node_addr, stack_offset, imm_value, type)
    let mut func_stack_inits: HashMap<u64, Vec<(u64, i64, i64, Typ)>> = HashMap::new();
    for (addr, ofs, val, typ) in db.rel_iter::<(Address, i64, i64, Typ)>("mach_imm_stack_init") {
        if let Some(&func) = node_to_func.get(addr) {
            func_stack_inits
                .entry(func)
                .or_default()
                .push((*addr, *ofs, *val, typ.clone()));
        }
    }

    synthesize_escaped_stack_region_construction(db, &func_stack_inits, &mut result);

    if func_stack_inits.is_empty() {
        return result;
    }

    // Collect all known struct layouts from emit_struct_fields for matching against stack init patterns.
    let mut known_layouts: HashMap<
        Vec<(i64, MemoryChunk)>,
        (Ident, Vec<(i64, Ident, MemoryChunk)>),
    > = HashMap::new();
    for (_func_addr, base_off, fields) in
        db.rel_iter::<(Address, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>)>("emit_struct_fields")
    {
        // Single-field layouts cause false positives in the fallback matcher (every uniform init run "matches" as 1-field instances); require >=2 fields of evidence.
        if fields.len() < 2 {
            continue;
        }
        let mut layout: Vec<(i64, MemoryChunk)> = fields
            .iter()
            .map(|(off, _, chunk)| (*off, chunk.clone()))
            .collect();
        layout.sort_by_key(|(off, _)| *off);
        let struct_id = base_off.unsigned_abs() as Ident;
        // Min-id wins: or_insert alone flickered the representative id across parallel-Ascent runs, flickering every synthesized field assign.
        known_layouts
            .entry(layout)
            .and_modify(|cur| {
                if struct_id < cur.0 {
                    *cur = (struct_id, fields.to_vec());
                }
            })
            .or_insert((struct_id, fields.to_vec()));
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
        let init_offsets: std::collections::BTreeSet<i64> =
            sorted.iter().map(|(_, ofs, _, _)| *ofs).collect();

        let mut stmts_for_func: Vec<(Node, ClightStmt)> = db
            .rel_iter::<(Node, ClightStmt)>("clight_stmt")
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
            let matching: Vec<_> = sorted
                .iter()
                .filter(|(_, ofs, _, _)| *ofs >= base_ofs && *ofs < base_ofs + 256)
                .collect();

            if matching.is_empty() {
                continue;
            }

            // Build layout for matching against known structs
            let mut layout: Vec<(i64, MemoryChunk)> = matching
                .iter()
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

            // Region size: declare the address-taken stack buffer unsigned char[struct_size] so the byte-offset store is in-bounds and (long)var / &var stay valid via array decay.
            let struct_size: i64 = {
                use crate::decompile::analysis::struct_recovery_pass::chunk_byte_size;
                layout
                    .iter()
                    .map(|(off, chunk)| off + chunk_byte_size(chunk) as i64)
                    .max()
                    .unwrap_or(0)
            };
            if struct_size > 0 {
                result
                    .stack_buffers
                    .push((*func_addr, struct_local_id, struct_size));
            }
            let char_ptr = pointer_to(ClightType::Tint(
                ClightIntSize::I8,
                ClightSignedness::Unsigned,
                default_attr(),
            ));

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

                // Struct field-member form (selected when the decl recovered the struct).
                let lhs = ClightExpr::Efield(
                    Box::new(ClightExpr::Evar(struct_local_id, struct_ty.clone())),
                    field_id,
                    field_ty.clone(),
                );
                let stmt = ClightStmt::Sassign(lhs, val_expr.clone());
                result.new_stmts.push((*init_addr, stmt.clone()));
                result.new_emit_stmts.push((*func_addr, *init_addr, stmt));

                // Raw byte-offset competitor: keep the original memory store available so a region declared as a sized byte buffer still recompiles instead of erroring with member-of-non-struct.
                let byte_addr = ClightExpr::Ebinop(
                    ClightBinaryOp::Oadd,
                    Box::new(ClightExpr::Ecast(
                        Box::new(ClightExpr::Eaddrof(
                            Box::new(ClightExpr::Evar(struct_local_id, struct_ty.clone())),
                            pointer_to(struct_ty.clone()),
                        )),
                        char_ptr.clone(),
                    )),
                    Box::new(ClightExpr::EconstLong(rel_ofs, default_long_type())),
                    char_ptr.clone(),
                );
                let raw_lhs = ClightExpr::Ederef(
                    Box::new(ClightExpr::Ecast(
                        Box::new(byte_addr),
                        pointer_to(field_ty.clone()),
                    )),
                    field_ty,
                );
                let raw_stmt = ClightStmt::Sassign(raw_lhs, val_expr);
                result.new_stmts.push((*init_addr, raw_stmt.clone()));
                result
                    .new_emit_stmts
                    .push((*func_addr, *init_addr, raw_stmt));
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
        if result
            .new_stmts
            .iter()
            .all(|(a, _)| !sorted.iter().any(|(sa, _, _, _)| sa == a))
        {
            let mut offsets: Vec<i64> = sorted.iter().map(|(_, ofs, _, _)| *ofs).collect();
            offsets.sort();
            offsets.dedup();

            // Pick the widest chunk seen at each offset.
            let chunk_at: std::collections::BTreeMap<i64, MemoryChunk> = {
                use crate::decompile::analysis::struct_recovery_pass::chunk_byte_size;
                let mut m: std::collections::BTreeMap<i64, MemoryChunk> =
                    std::collections::BTreeMap::new();
                for (_, ofs, _, typ) in &sorted {
                    let c = typ_to_chunk(typ);
                    m.entry(*ofs)
                        .and_modify(|cur| {
                            if chunk_byte_size(&c) > chunk_byte_size(cur) {
                                *cur = c.clone();
                            }
                        })
                        .or_insert(c);
                }
                m
            };

            // Sort candidates (min struct_id, then layout) for determinism: this loop breaks on first match and HashMap order let different layouts claim the cluster each run.
            let mut layout_candidates: Vec<_> = known_layouts.iter().collect();
            layout_candidates.sort_by(|a, b| (a.1 .0, a.0).cmp(&(b.1 .0, b.0)));
            for (layout, (struct_id, fields)) in layout_candidates {
                let struct_size: i64 = layout
                    .iter()
                    .map(|(off, chunk)| {
                        off + match chunk {
                            MemoryChunk::MInt32 => 4,
                            MemoryChunk::MInt64 => 8,
                            MemoryChunk::MFloat32 => 4,
                            MemoryChunk::MFloat64 => 8,
                            _ => 4,
                        }
                    })
                    .max()
                    .unwrap_or(0);
                let field_count = layout.len();
                if field_count == 0 || struct_size == 0 {
                    continue;
                }

                let min_ofs = offsets.first().copied().unwrap_or(0);
                let mut instance_idx = 0;
                let mut field_idx = 0;
                let mut matched_count = 0;

                for &ofs in &offsets {
                    let expected_ofs =
                        min_ofs + (instance_idx as i64) * struct_size + layout[field_idx].0;
                    // Offset AND chunk must match: offset-only let int inits satisfy long fields, synthesizing field assigns for unrelated locals.
                    if ofs == expected_ofs && chunk_at.get(&ofs) == Some(&layout[field_idx].1) {
                        matched_count += 1;
                        field_idx += 1;
                        if field_idx >= field_count {
                            field_idx = 0;
                            instance_idx += 1;
                        }
                    }
                }

                if matched_count < offsets.len() || instance_idx < 2 {
                    continue;
                }

                let struct_ty = ClightType::Tstruct(*struct_id, default_attr());
                let struct_var_id = min_ofs.unsigned_abs() as Ident;
                // Declare the recovered region `unsigned char[total]` so the raw byte-offset store candidates below are in-bounds across every instance; `(long)var`/`&var` stay valid via array decay.
                let total_size = (instance_idx as i64) * struct_size;
                if total_size > 0 {
                    result
                        .stack_buffers
                        .push((*func_addr, struct_var_id, total_size));
                }
                let char_ptr = pointer_to(ClightType::Tint(
                    ClightIntSize::I8,
                    ClightSignedness::Unsigned,
                    default_attr(),
                ));

                for s in 0..instance_idx {
                    let base_ofs = min_ofs + (s as i64) * struct_size;
                    for (field_off, field_name, _chunk) in fields {
                        let target_ofs = base_ofs + field_off;
                        if let Some((init_addr, _, val, typ)) =
                            sorted.iter().find(|(_, ofs, _, _)| *ofs == target_ofs)
                        {
                            let field_ty = typ_to_clight_type(typ);
                            let val_expr = match typ {
                                Typ::Tlong | Typ::Tany64 => {
                                    ClightExpr::EconstLong(*val, default_long_type())
                                }
                                _ => ClightExpr::EconstInt(*val as i32, default_int_type()),
                            };

                            // Struct field-member form (selected when the decl recovered the struct).
                            let lhs = ClightExpr::Efield(
                                Box::new(ClightExpr::Evar(struct_var_id, struct_ty.clone())),
                                *field_name,
                                field_ty.clone(),
                            );
                            let stmt = ClightStmt::Sassign(lhs, val_expr.clone());
                            result.new_stmts.push((*init_addr, stmt.clone()));
                            result.new_emit_stmts.push((*func_addr, *init_addr, stmt));

                            // Raw byte-offset competitor kept for the selection so a region declared a sized byte buffer rather than this struct still recompiles -- `*(T*)((unsigned char*)&v + ofs) = val` -- instead of "member of non-struct". In-bounds via char[total].
                            let rel_ofs = target_ofs - min_ofs;
                            let byte_addr = ClightExpr::Ebinop(
                                ClightBinaryOp::Oadd,
                                Box::new(ClightExpr::Ecast(
                                    Box::new(ClightExpr::Eaddrof(
                                        Box::new(ClightExpr::Evar(
                                            struct_var_id,
                                            struct_ty.clone(),
                                        )),
                                        pointer_to(struct_ty.clone()),
                                    )),
                                    char_ptr.clone(),
                                )),
                                Box::new(ClightExpr::EconstLong(rel_ofs, default_long_type())),
                                char_ptr.clone(),
                            );
                            let raw_lhs = ClightExpr::Ederef(
                                Box::new(ClightExpr::Ecast(
                                    Box::new(byte_addr),
                                    pointer_to(field_ty.clone()),
                                )),
                                field_ty,
                            );
                            let raw_stmt = ClightStmt::Sassign(raw_lhs, val_expr);
                            result.new_stmts.push((*init_addr, raw_stmt.clone()));
                            result
                                .new_emit_stmts
                                .push((*func_addr, *init_addr, raw_stmt));
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

fn header_global_clight_type(raw_name: &str) -> Option<ClightType> {
    let canonical_name = raw_name.split('@').next().unwrap_or(raw_name);
    let emitted_name =
        crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(
            canonical_name,
        );
    let spelling = crate::decompile::passes::c_pass::header_db::header_db()
        .variables
        .get(emitted_name.as_str())?;
    crate::decompile::passes::c_pass::header_db::canonical_variable_clight_type(spelling)
}

#[cfg(test)]
mod known_global_load_tests {
    use super::*;
    use crate::decompile::passes::clight_emit_pass::ClightSelectPass;
    use crate::decompile::passes::pass::IRPass;

    fn direct_global_load(dst: RTLReg, ident: Ident) -> CsharpminorStmt {
        CsharpminorStmt::Sset(
            dst,
            CsharpminorExpr::Eload(
                MemoryChunk::MAny64,
                Box::new(CsharpminorExpr::Econst(Constant::Oaddrsymbol(ident, 0))),
            ),
        )
    }

    fn has_direct_global_stmt(
        prog: &ClightPassProgram,
        node: Node,
        dst: RTLReg,
        global: Ident,
        want_type: impl Fn(&ClightType) -> bool,
    ) -> bool {
        prog.clight_stmt.iter().any(|(got_node, stmt)| {
            *got_node == node
                && matches!(
                    stmt,
                    ClightStmt::Sset(id, ClightExpr::Evar(got_global, ty))
                        if *id == ident_from_reg(dst)
                            && *got_global == global
                            && want_type(ty)
                )
        })
    }

    #[test]
    fn object_load_adds_authoritative_statement_not_lifetime_type() {
        let global = 0x28200usize;
        let dst = 0x8000_0000_0068_8f09;
        let mut prog = ClightPassProgram::default();
        prog.csharp_stmt
            .push((0x688f, direct_global_load(dst, global)));
        prog.global_symbol
            .push((global as Address, "optarg@GLIBC_2.2.5"));
        prog.known_global_type.push(("optarg", XType::Xcharptr));

        prog.run();

        assert!(has_direct_global_stmt(
            &prog,
            0x688f,
            dst,
            global,
            |ty| matches!(
                ty,
                ClightType::Tpointer(inner, _)
                    if matches!(inner.as_ref(), ClightType::Tint(ClightIntSize::I8, ..))
            ),
        ));
        assert!(
            !prog
                .emit_var_type_candidate
                .iter()
                .any(|(reg, _)| *reg == dst),
            "one load must not type every lifetime of a reused register",
        );
    }

    #[test]
    fn recovered_object_load_adds_emitter_typed_statement() {
        let global = 0x28438usize;
        let dst = 0x8000_0000_006e_1001;
        let mut prog = ClightPassProgram::default();
        prog.csharp_stmt
            .push((0x6e10, direct_global_load(dst, global)));
        prog.global_symbol.push((global as Address, "L_28438"));
        prog.emit_global_is_ptr.push((global,));
        prog.emit_global_is_char_ptr.push((global,));

        prog.run();

        assert!(has_direct_global_stmt(
            &prog,
            0x6e10,
            dst,
            global,
            |ty| matches!(
                ty,
                ClightType::Tpointer(inner, _)
                    if matches!(inner.as_ref(), ClightType::Tint(ClightIntSize::I8, ..))
            ),
        ));
        assert!(
            !prog
                .emit_var_type_candidate
                .iter()
                .any(|(reg, _)| *reg == dst),
            "recovered object facts stay definition-local",
        );
    }

    #[test]
    fn header_only_object_load_adds_char_pointer_pointer_statement() {
        let global = 0x28500usize;
        let dst = 0x8000_0000_006e_2001;
        let mut prog = ClightPassProgram::default();
        prog.csharp_stmt
            .push((0x6e20, direct_global_load(dst, global)));
        prog.global_symbol
            .push((global as Address, "environ@GLIBC_2.2.5"));
        // Conflicting machine-level evidence must remain untouched: the
        // header authority belongs to this definition, not every dst lifetime.
        prog.emit_var_type_candidate.push((dst, XType::Xfloat));

        prog.run();

        assert!(has_direct_global_stmt(
            &prog,
            0x6e20,
            dst,
            global,
            |ty| matches!(
                ty,
                ClightType::Tpointer(inner, _)
                    if matches!(
                        inner.as_ref(),
                        ClightType::Tpointer(char_inner, _)
                            if matches!(
                                char_inner.as_ref(),
                                ClightType::Tint(ClightIntSize::I8, ..)
                            )
                    )
            ),
        ));
        let dst_types: Vec<XType> = prog
            .emit_var_type_candidate
            .iter()
            .filter_map(|(reg, ty)| (*reg == dst).then_some(*ty))
            .collect();
        assert_eq!(dst_types, vec![XType::Xfloat]);
    }

    #[test]
    fn same_named_function_does_not_add_global_destination_type() {
        let function = 0x401000usize;
        let dst = 0x8000_0000_0040_1001;
        let mut prog = ClightPassProgram::default();
        prog.csharp_stmt
            .push((0x401001, direct_global_load(dst, function)));
        prog.known_global_type.push(("__ctype_b_loc", XType::Xptr));

        prog.run();

        assert!(!prog.clight_stmt.iter().any(|(_, stmt)| matches!(
            stmt,
            ClightStmt::Sset(id, ClightExpr::Evar(got_global, _))
                if *id == ident_from_reg(dst) && *got_global == function
        )));
    }

    #[test]
    fn scheduler_copies_object_provenance_to_known_global_consumers() {
        let clight = ClightPass;
        assert!(clight.inputs().contains(&"global_symbol"));
        assert!(clight.inputs().contains(&"known_global_type"));
        assert!(clight.inputs().contains(&"emit_global_is_ptr"));
        assert!(clight.inputs().contains(&"emit_global_is_char_ptr"));

        let select = ClightSelectPass;
        assert!(select.extra_reads().contains(&"global_symbol"));
        assert!(select.extra_reads().contains(&"known_global_type"));
        assert!(select.extra_reads().contains(&"emit_global_is_ptr"));
        assert!(select.extra_reads().contains(&"emit_global_is_char_ptr"));
        assert!(select.extra_reads().contains(&"must_be_ptr"));
        assert!(select.extra_reads().contains(&"code_pointer_in_data"));
    }
}
