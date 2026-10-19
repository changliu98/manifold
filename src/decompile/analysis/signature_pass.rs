use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::decompile::elevator::config::CONFIG;
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::decompile::passes::rtl_pass::fresh_xtl_reg;
use crate::mreg::Mreg;
use crate::run_pass;
use crate::x86::op::{Addressing, Operation};
use crate::x86::types::*;
use ascent::ascent_par;

// Mode aggregator: value with highest count, ties broken by larger value.
pub(crate) fn majority_usize<'a>(
    inp: impl Iterator<Item = (&'a usize,)>,
) -> impl Iterator<Item = usize> {
    let mut counts: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
    for (&v,) in inp {
        *counts.entry(v).or_insert(0) += 1;
    }
    let best = counts
        .into_iter()
        .max_by(|a, b| a.1.cmp(&b.1).then(a.0.cmp(&b.0)));
    best.map(|(v, _)| v).into_iter()
}

// Frequency of the mode returned by majority_usize.
pub(crate) fn mode_freq_usize<'a>(
    inp: impl Iterator<Item = (&'a usize,)>,
) -> impl Iterator<Item = usize> {
    let mut counts: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
    for (&v,) in inp {
        *counts.entry(v).or_insert(0) += 1;
    }
    counts
        .into_iter()
        .max_by(|a, b| a.1.cmp(&b.1).then(a.0.cmp(&b.0)))
        .map(|(_, c)| c)
        .into_iter()
}

pub(crate) fn max_plus_one_usize<'a>(
    inp: impl Iterator<Item = (&'a usize,)>,
) -> impl Iterator<Item = usize> {
    inp.map(|(&v,)| v).max().map(|m| m + 1).into_iter()
}

pub(crate) fn count_items_sig<'a, T: 'a>(
    inp: impl Iterator<Item = (&'a T,)>,
) -> impl Iterator<Item = usize> {
    std::iter::once(inp.count())
}

pub(crate) fn max_usize<'a>(
    inp: impl Iterator<Item = (&'a usize,)>,
) -> impl Iterator<Item = usize> {
    inp.map(|(&v,)| v).max().into_iter()
}

fn max_refined_xtype<'a>(inp: impl Iterator<Item = (&'a XType,)>) -> impl Iterator<Item = XType> {
    inp.map(|(&xtype,)| xtype)
        .max_by_key(|xtype| {
            (
                crate::decompile::passes::clight_pass::xtype_refine_priority(xtype),
                *xtype,
            )
        })
        .into_iter()
}

fn is_exact_signature_value_type(xtype: &XType) -> bool {
    !matches!(xtype, XType::Xvoid | XType::Xany32 | XType::Xany64)
}

fn integer_value_bits(xtype: XType) -> Option<u32> {
    match xtype {
        XType::Xbool => Some(1),
        XType::Xint8signed | XType::Xint8unsigned => Some(8),
        XType::Xint16signed | XType::Xint16unsigned => Some(16),
        XType::Xint | XType::Xintunsigned | XType::Xany32 => Some(32),
        XType::Xlong | XType::Xlongunsigned | XType::Xany64 => Some(64),
        _ => None,
    }
}

/// A subword load/cast hint at the caller describes a value view, not a
/// license to truncate the callee's interface to that storage width. Vote
/// with its integer-promotion carrier. A definition-side narrow parameter
/// remains authoritative; caller-only evidence cannot manufacture one.
fn argument_value_type(xtype: XType) -> XType {
    match xtype {
        XType::Xbool
        | XType::Xint8signed
        | XType::Xint8unsigned
        | XType::Xint16signed
        | XType::Xint16unsigned => XType::Xint,
        _ => xtype,
    }
}

fn signature_addr_preserving_op(op: &Operation) -> bool {
    matches!(
        op,
        Operation::Omove
            | Operation::Olea(_)
            | Operation::Oleal(_)
            | Operation::Oadd
            | Operation::Oaddl
            | Operation::Oaddimm(_)
            | Operation::Oaddlimm(_)
            | Operation::Osub
            | Operation::Osubl
    )
}

fn signature_indexed_offset(addressing: &Addressing) -> Option<i64> {
    match addressing {
        Addressing::Aindexed(offset)
        | Addressing::Aindexed2(offset)
        | Addressing::Aindexed2scaled(_, offset) => Some(*offset),
        _ => None,
    }
}

/// Recover the number of fixed integer-register parameters from a SysV
/// variadic register-save prologue.  A variadic function saves the suffix of
/// GP argument registers that belongs to `...`; the first saved ABI position
/// is therefore the fixed GP-prefix length.  Stay conservative when position
/// zero is also saved (it may be an ordinary fixed-parameter spill) or when
/// the observed saves do not form a complete suffix.
pub(crate) fn variadic_fixed_gp_count_from_spills(
    spilled_positions: &HashSet<usize>,
    max_gp_position: usize,
) -> Option<usize> {
    let first = spilled_positions.iter().copied().min()?;
    if first == 0
        || !(first..=max_gp_position).all(|position| spilled_positions.contains(&position))
    {
        return None;
    }
    Some(first)
}

fn variadic_fixed_gp_count_aggregate<'a>(
    inp: impl Iterator<Item = (&'a usize, &'a usize)>,
) -> impl Iterator<Item = usize> {
    let mut spilled_positions = HashSet::new();
    let mut max_gp_position = None;
    for (&position, &max_position) in inp {
        spilled_positions.insert(position);
        max_gp_position =
            Some(max_gp_position.map_or(max_position, |old: usize| old.max(max_position)));
    }
    max_gp_position
        .and_then(|max_position| {
            variadic_fixed_gp_count_from_spills(&spilled_positions, max_position)
        })
        .into_iter()
}

fn strong_call_arity_consensus(
    mode: usize,
    position_count: usize,
    frequency: usize,
    total: usize,
) -> bool {
    mode > position_count && total >= 2 && frequency.saturating_mul(10) >= total.saturating_mul(6)
}

// Declarative helpers consumed by reconcile_signatures below.
ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct SignatureReconciliationProgram;

    // Input relations (swapped in from the DB).
    relation emit_function(Address, Symbol, Node);
    relation emit_function_param_candidate(Address, RTLReg);
    relation emit_function_param_type_candidate(Address, RTLReg, XType);
    relation func_has_param_evidence(Address, usize);
    relation call_target_func(Node, Address);
    relation func_tailcalls_local(Address, Address);
    relation call_return_reg(Node, RTLReg);
    relation call_arg(Node, usize, RTLReg);
    relation call_has_arg_evidence(Node, usize);
    relation call_args_collected_candidate(Node, Args);
    relation call_float_args_collected(Node, Args);
    relation emit_function_param_count_candidate(Address, usize);
    relation emit_function_float_param_count(Address, usize);
    relation emit_function_stack_param_count(Address, usize);
    relation variadic_fixed_stack_prefix_count(Address, usize);
    relation variadic_fixed_gp_prefix_count(Address, usize);
    relation known_varargs_function(Symbol, usize);
    // Functions inferred variadic by their XMM register save area prologue (test %al,%al; je; movaps xmm0..7 to stack).
    relation func_has_variadic_xmm_prologue(Address);
    relation emit_function_has_return_candidate(Address);
    relation emit_function_void_candidate(Address);
    relation emit_function_return_type_xtype_candidate(Address, XType);
    relation function_return_point_reg(Address, Node, RTLReg);
    relation ax_value_addr(Node, Node);
    relation abi_ret_int_reg(Mreg);
    relation ltl_inst(Node, LTLInst);
    relation reg_def_used(Node, Mreg, Node);
    relation machine_register_write_view(Node, Mreg, u32);
    relation rtl_inst(Node, RTLInst);
    relation emit_var_type_candidate(RTLReg, XType);
    relation op_produces_ptr(Node, RTLReg);
    relation global_addr_reg(Ident, RTLReg);
    relation call_returns_value(Address, Mreg);
    relation known_extern_signature(Symbol, usize, XType, Arc<Vec<XType>>);
    relation known_func_param_is_ptr(Symbol, usize);
    relation abi_int_arg_position(Mreg, usize);
    relation abi_shared_arg_slots(bool);
    relation abi_first_stack_arg_position(usize);
    relation abi_pointer_size(i64);
    relation abi_reg_args_per_function(bool);
    relation func_reg_arg_count(Address, usize);
    relation func_callee_pop_bytes(Address, i64);
    relation func_decorated_arg_bytes(Address, i64);
    relation arg_reg_spilled_to_stack(Address, Mreg);

    // Exact return-value refinement is a mutually recursive value-flow
    // analysis.  Ascent owns the fixpoint: concrete types at structural return
    // values refine the callee, and a refined internal callee in turn types
    // the fresh value produced at each call site.
    #[local] relation signature_return_move_source(RTLReg, RTLReg);
    signature_return_move_source(*dst, args[0]) <--
        rtl_inst(_, ?RTLInst::Iop(Operation::Omove, args, dst)),
        if args.len() == 1;

    // Storage and expression types are different claims. A byte local may
    // feed a full-width arithmetic result; the storage type anywhere on its
    // coalesced web must not truncate that result at the function boundary.
    // Use the producing instruction's decoded register carrier, not the
    // narrower range suggested by a cast or memory chunk. In particular a
    // byte load into EAX defines an integer return carrier, including its
    // sign/zero extension. A narrow C return would let recompilation discard
    // the upper bits even when an original binary caller observes them.
    // Keep at least the integer-promotion carrier for partial GPR writes;
    // projecting the interface onto fewer bits needs caller/ABI evidence.
    #[local] relation signature_produced_value_type(Node, Mreg, XType);
    signature_produced_value_type(*node, *reg, xtype) <--
        machine_register_write_view(node, reg, bits),
        if matches!(reg, Mreg::X86(_)),
        if matches!(*bits, 8 | 16 | 32 | 64),
        let xtype = if *bits == 64 { XType::Xlong } else { XType::Xint };
    signature_produced_value_type(*node, *dst, *xtype) <--
        ltl_inst(node, ?LTLInst::Lop(Operation::Omove, args, dst)),
        if args.len() == 1,
        !machine_register_write_view(node, *dst, _),
        reg_def_used(source, args[0], *node),
        signature_produced_value_type(source, args[0], xtype);

    #[local] relation signature_return_value_type(Address, XType);
    signature_return_value_type(*func, *xtype) <--
        function_return_point_reg(func, ret, _),
        ax_value_addr(ret, definition),
        abi_ret_int_reg(reg),
        signature_produced_value_type(definition, reg, xtype);
    // Preserve the same carrier across internal forwarding boundaries. The
    // positive call-graph fixpoint propagates producer evidence, not guessed
    // candidate types, and an unseeded recursive component invents nothing.
    signature_produced_value_type(*call, *reg, *xtype) <--
        call_target_func(call, target),
        signature_return_value_type(target, xtype),
        abi_ret_int_reg(reg);
    signature_return_value_type(func, xtype) <--
        func_tailcalls_local(func, target),
        signature_return_value_type(target, xtype);
    emit_function_return_type_xtype_candidate(func, xtype) <--
        signature_return_value_type(func, xtype);

    #[local] relation signature_return_needs_narrowing_proof(Address, XType);
    signature_return_needs_narrowing_proof(*func, *candidate) <--
        emit_function_return_type_xtype_candidate(func, candidate),
        signature_return_value_type(func, value),
        if let (Some(candidate_bits), Some(value_bits)) =
            (integer_value_bits(*candidate), integer_value_bits(*value)),
        if candidate_bits < value_bits;

    emit_function_return_type_xtype_candidate(func, xtype) <--
        function_return_point_reg(func, _, return_reg),
        emit_var_type_candidate(return_reg, xtype),
        if is_exact_signature_value_type(xtype);

    emit_function_return_type_xtype_candidate(func, xtype) <--
        function_return_point_reg(func, _, return_reg),
        signature_return_move_source(return_reg, source_reg),
        emit_var_type_candidate(source_reg, xtype),
        if is_exact_signature_value_type(xtype);

    relation signature_internal_call_result_type(RTLReg, XType);
    signature_internal_call_result_type(result_reg, xtype) <--
        call_target_func(call, target),
        call_return_reg(call, result_reg),
        emit_function_return_type_xtype_candidate(target, xtype),
        if is_exact_signature_value_type(xtype);
    emit_var_type_candidate(result_reg, xtype) <--
        signature_internal_call_result_type(result_reg, xtype);

    // Use the selected RTL instruction's argument vector for internal calls.
    // Candidate relations can contain multiple distinct instructions at one
    // node; in that ambiguous case retain the original call_arg mapping rather
    // than selecting a vector by tuple order.
    #[local] relation signature_internal_call_args(Node, Args);
    signature_internal_call_args(node, args.clone()) <--
        call_target_func(node, _),
        rtl_inst(node, ?RTLInst::Icall(_, _, args, _, _));
    signature_internal_call_args(node, args.clone()) <--
        call_target_func(node, _),
        rtl_inst(node, ?RTLInst::Itailcall(_, _, args));

    #[local] relation signature_internal_call_args_ambiguous(Node);
    signature_internal_call_args_ambiguous(node) <--
        signature_internal_call_args(node, left),
        signature_internal_call_args(node, right),
        if left != right;

    relation signature_selected_call_arg(Node, usize, RTLReg);
    signature_selected_call_arg(node, position, *reg) <--
        signature_internal_call_args(node, args),
        !signature_internal_call_args_ambiguous(node),
        for (position, reg) in args.iter().enumerate();
    signature_selected_call_arg(node, position, reg) <--
        call_arg(node, position, reg),
        !signature_internal_call_args(node, _);
    signature_selected_call_arg(node, position, reg) <--
        call_arg(node, position, reg),
        signature_internal_call_args_ambiguous(node);

    relation signature_hard_pointer_reg(RTLReg);
    signature_hard_pointer_reg(reg) <-- op_produces_ptr(_, reg);
    signature_hard_pointer_reg(reg) <-- global_addr_reg(_, reg);
    signature_hard_pointer_reg(reg) <--
        signature_internal_call_result_type(reg, xtype),
        if pointer_like_xtype(xtype);

    #[local] relation signature_call_arg_type_candidate(Node, usize, XType);
    signature_call_arg_type_candidate(node, position, xtype) <--
        signature_selected_call_arg(node, position, reg),
        emit_var_type_candidate(reg, xtype);

    #[local] relation signature_call_arg_pointer_type_candidate(Node, usize, XType);
    signature_call_arg_pointer_type_candidate(node, position, xtype) <--
        signature_selected_call_arg(node, position, reg),
        signature_hard_pointer_reg(reg),
        signature_call_arg_type_candidate(node, position, xtype),
        if pointer_like_xtype(xtype);

    #[local] relation signature_call_arg_pointer_type_selected(Node, usize, XType);
    signature_call_arg_pointer_type_selected(node, position, selected) <--
        signature_call_arg_pointer_type_candidate(node, position, _),
        agg selected = max_refined_xtype(xtype)
            in signature_call_arg_pointer_type_candidate(node, position, xtype);

    #[local] relation signature_call_arg_scalar_type_candidate(Node, usize, XType);
    signature_call_arg_scalar_type_candidate(node, position, argument_value_type(*xtype)) <--
        signature_selected_call_arg(node, position, reg),
        !signature_hard_pointer_reg(reg),
        signature_call_arg_type_candidate(node, position, xtype),
        if !pointer_like_xtype(xtype);

    #[local] relation signature_call_arg_scalar_type_selected(Node, usize, XType);
    signature_call_arg_scalar_type_selected(node, position, selected) <--
        signature_call_arg_scalar_type_candidate(node, position, _),
        agg selected = max_refined_xtype(xtype)
            in signature_call_arg_scalar_type_candidate(node, position, xtype);

    #[local] relation signature_call_arg_any_type_selected(Node, usize, XType);
    signature_call_arg_any_type_selected(node, position, selected) <--
        signature_call_arg_type_candidate(node, position, _),
        agg selected = max_refined_xtype(xtype)
            in signature_call_arg_type_candidate(node, position, xtype);

    relation signature_call_arg_type_at_site(Node, usize, XType);
    signature_call_arg_type_at_site(node, position, xtype) <--
        signature_call_arg_pointer_type_selected(node, position, xtype);
    signature_call_arg_type_at_site(node, position, XType::Xptr) <--
        signature_selected_call_arg(node, position, reg),
        signature_hard_pointer_reg(reg),
        !signature_call_arg_pointer_type_candidate(node, position, _);
    signature_call_arg_type_at_site(node, position, xtype) <--
        signature_call_arg_scalar_type_selected(node, position, xtype);
    signature_call_arg_type_at_site(node, position, xtype) <--
        signature_selected_call_arg(node, position, reg),
        !signature_hard_pointer_reg(reg),
        !signature_call_arg_scalar_type_candidate(node, position, _),
        signature_call_arg_any_type_selected(node, position, xtype);

    // Position p is an integer-REGISTER position of function f. Image-wide for SysV and Win64, where every low ordinal is a register slot; per function on Windows x86-32, where the default cdecl already has position 0 on the stack and only a fastcall/thiscall function claims ECX/EDX. Without this distinction a cdecl stack argument at position 0 is counted as a register argument AND as a stack argument.
    #[local] relation func_int_reg_position(Address, usize);
    func_int_reg_position(f, p) <--
        emit_function(f, _, _),
        abi_int_arg_position(_, p),
        !abi_reg_args_per_function(true);
    func_int_reg_position(f, p) <--
        abi_reg_args_per_function(true),
        func_reg_arg_count(f, n),
        abi_int_arg_position(_, p),
        if *p < *n;

    // Calls that have precise per-position arg_mapping.
    #[local] relation call_precise(Node);
    call_precise(n) <-- call_arg(n, _, _);

    // Per-call integer-position evidence; precise mapping wins.
    #[local] relation call_int_pos(Node, usize);
    call_int_pos(n, p) <-- call_arg(n, p, _);
    // Fall back to call_has_arg_evidence only when no precise mapping exists for this call.
    call_int_pos(n, p) <--
        call_has_arg_evidence(n, p),
        !call_precise(n);

    // A call site is informative if it has any arg evidence for its target.
    #[local] relation call_has_any_arg(Node);
    call_has_any_arg(n) <-- call_int_pos(n, _);

    // Per-(func, pos) call-site support counts.
    #[local] relation call_pos_evidence(Address, Node, usize);
    call_pos_evidence(target, n, p) <--
        call_target_func(n, target),
        call_int_pos(n, p);

    #[local] relation informative_call(Address, Node);
    informative_call(target, n) <--
        call_target_func(n, target),
        call_has_any_arg(n);

    // Number of informative call sites per function
    relation informative_call_count(Address, usize);
    informative_call_count(f, c) <--
        informative_call(f, _),
        agg c = count_items_sig(n) in informative_call(f, n);

    // Number of informative call sites that have evidence for a given position
    #[local] relation call_pos_support(Address, usize, usize);
    call_pos_support(f, p, c) <--
        call_pos_evidence(f, _, p),
        agg c = count_items_sig(n) in call_pos_evidence(f, n, p);

    // Definition-side integer-position evidence.
    #[local] relation def_int_pos(Address, usize);
    def_int_pos(f, p) <-- func_has_param_evidence(f, p);

    // Position confirmed if definition reads it, or informative-call coverage >= threshold. Positions 0..6.
    #[local] relation int_pos_confirmed(Address, usize);

    // (a) definition confirms
    int_pos_confirmed(f, p) <--
        def_int_pos(f, p),
        func_int_reg_position(f, p);

    // A pure-float-param function reads XMM args but no integer arg register, so int regs live across its call sites get back-attributed and fabricate positions the callee never consumes.
    #[local] relation func_pure_float_params(Address);
    func_pure_float_params(f) <--
        emit_function_float_param_count(f, fc),
        if *fc > 0,
        !func_has_param_evidence(f, _);

    // (b) call-site ratio confirms (only with at least one informative call); suppressed for pure-float-param functions, where the definition is authoritative that it reads no int arg reg so caller-side int-reg evidence is leftover state, not a parameter.
    int_pos_confirmed(f, p) <--
        call_pos_support(f, p, c),
        informative_call_count(f, total),
        func_int_reg_position(f, p),
        if *total > 0,
        if (*c as f64) / (*total as f64) >= CONFIG.signature.call_site_confirm_ratio,
        !func_pure_float_params(f);

    // Reconciled int count: max confirmed position + 1. Emits only when some confirmation exists.
    relation reconciled_int_count(Address, usize);
    reconciled_int_count(f, n) <--
        int_pos_confirmed(f, _),
        agg n = max_plus_one_usize(p) in int_pos_confirmed(f, p);

    // Max of def_int_pos for fallback when all call sites failed backward reach.
    relation def_int_count_max(Address, usize);
    def_int_count_max(f, n) <--
        def_int_pos(f, _),
        agg n = max_plus_one_usize(p) in def_int_pos(f, p);

    // Per-call-site arg counts: max int-args + float count (when non-empty).
    #[local] relation call_int_arg_count_raw(Node, usize);
    call_int_arg_count_raw(n, len) <--
        call_args_collected_candidate(n, args),
        let len = args.len();
    #[local] relation call_int_arg_count(Node, usize);
    call_int_arg_count(n, m) <--
        call_int_arg_count_raw(n, _),
        agg m = max_usize(l) in call_int_arg_count_raw(n, l);

    #[local] relation call_float_arg_count(Node, usize);
    call_float_arg_count(n, fc) <--
        call_float_args_collected(n, args),
        let fc = args.len(),
        if fc > 0;

    #[local] relation call_total_arg_count(Node, usize);
    call_total_arg_count(n, ic) <--
        call_int_arg_count(n, ic),
        !call_float_arg_count(n, _);
    call_total_arg_count(n, ic + fc) <--
        call_int_arg_count(n, ic),
        call_float_arg_count(n, fc);
    // Calls with no int args entry but float args present still count floats.
    call_total_arg_count(n, fc) <--
        call_float_arg_count(n, fc),
        !call_int_arg_count(n, _);

    // Sample (target, arg_count) per call; 0 counted for calls with no arg evidence.
    #[local] relation call_site_count_sample(Address, Node, usize);
    call_site_count_sample(target, n, c) <--
        call_target_func(n, target),
        call_total_arg_count(n, c);
    call_site_count_sample(target, n, 0) <--
        call_target_func(n, target),
        !call_total_arg_count(n, _);

    // Total call sites per function (every call_target_func entry).
    relation total_call_sites(Address, usize);
    total_call_sites(f, c) <--
        call_site_count_sample(f, _, _),
        agg c = count_items_sig(n) in call_site_count_sample(f, n, _);

    // Majority mode: arg-count with highest frequency, ties broken by larger value.
    relation call_site_mode(Address, usize);
    call_site_mode(f, m) <--
        call_site_count_sample(f, _, _),
        agg m = majority_usize(c) in call_site_count_sample(f, _, c);

    relation call_site_mode_freq(Address, usize);
    call_site_mode_freq(f, freq) <--
        call_site_count_sample(f, _, _),
        agg freq = mode_freq_usize(c) in call_site_count_sample(f, _, c);

    // has_call_sites: any call_target_func entry for f.
    relation has_call_sites(Address);
    has_call_sites(f) <-- call_target_func(_, f);

    // True when some call site targeting f has its return value consumed.
    relation any_call_uses_return(Address);
    any_call_uses_return(f) <--
        call_target_func(n, f),
        call_returns_value(n, _);

    // Varargs: emit_function listed in known_varargs_function, OR functions whose prologue spills all 8 XMM arg regs (SysV variadic register save area; see func_has_variadic_xmm_prologue in rtl_pass.rs).
    relation is_varargs_fn(Address);
    is_varargs_fn(addr) <--
        emit_function(addr, name, _),
        known_varargs_function(name, _);
    is_varargs_fn(addr) <--
        func_has_variadic_xmm_prologue(addr);
    is_varargs_fn(addr) <-- variadic_fixed_gp_prefix_count(addr, _);

    #[local] relation abi_max_int_arg_position(usize);
    abi_max_int_arg_position(max_position) <--
        abi_int_arg_position(_, _),
        agg max_position = ascent::aggregators::max(position)
            in abi_int_arg_position(_, position);

    #[local] relation variadic_spilled_gp_position(Address, usize, usize);
    variadic_spilled_gp_position(func, position, max_position) <--
        is_varargs_fn(func),
        arg_reg_spilled_to_stack(func, reg),
        abi_int_arg_position(reg, position),
        abi_max_int_arg_position(max_position);

    relation signature_variadic_fixed_gp_count(Address, usize);
    signature_variadic_fixed_gp_count(func, fixed_count) <--
        variadic_fixed_gp_prefix_count(func, fixed_count);
    signature_variadic_fixed_gp_count(func, fixed_count) <--
        variadic_spilled_gp_position(func, _, _),
        !variadic_fixed_gp_prefix_count(func, _),
        agg fixed_count = variadic_fixed_gp_count_aggregate(position, max_position)
            in variadic_spilled_gp_position(func, position, max_position);

    #[local] relation signature_inferred_int_count(Address, usize);
    signature_inferred_int_count(func, count) <--
        emit_function(func, _, _),
        reconciled_int_count(func, count);
    signature_inferred_int_count(func, 0usize) <--
        emit_function(func, _, _),
        !reconciled_int_count(func, _);

    relation signature_effective_int_count(Address, usize);
    signature_effective_int_count(func, fixed_count) <--
        is_varargs_fn(func),
        signature_variadic_fixed_gp_count(func, fixed_count);
    signature_effective_int_count(func, inferred_count) <--
        is_varargs_fn(func),
        !signature_variadic_fixed_gp_count(func, _),
        signature_inferred_int_count(func, inferred_count);
    signature_effective_int_count(func, inferred_count) <--
        emit_function(func, _, _),
        !is_varargs_fn(func),
        signature_inferred_int_count(func, inferred_count);

    #[local] relation signature_float_count(Address, usize);
    signature_float_count(func, count) <--
        emit_function(func, _, _),
        emit_function_float_param_count(func, count);
    signature_float_count(func, 0usize) <--
        emit_function(func, _, _),
        !emit_function_float_param_count(func, _);

    #[local] relation signature_stack_count(Address, usize);
    signature_stack_count(func, count) <--
        emit_function(func, _, _),
        variadic_fixed_stack_prefix_count(func, count);
    signature_stack_count(func, count) <--
        emit_function(func, _, _),
        emit_function_stack_param_count(func, count),
        !variadic_fixed_stack_prefix_count(func, _);
    signature_stack_count(func, 0usize) <--
        emit_function(func, _, _),
        !emit_function_stack_param_count(func, _),
        !variadic_fixed_stack_prefix_count(func, _);

    #[local] relation signature_position_count_base(Address, usize);
    signature_position_count_base(func, count) <--
        abi_shared_arg_slots(true),
        abi_first_stack_arg_position(first_stack),
        signature_effective_int_count(func, int_count),
        signature_stack_count(func, stack_count),
        let stack_end = if *stack_count > 0 {
            *first_stack + *stack_count
        } else {
            0
        },
        let count = (*int_count).max(stack_end);
    signature_position_count_base(func, int_count + float_count + stack_count) <--
        emit_function(func, _, _),
        !abi_shared_arg_slots(true),
        signature_effective_int_count(func, int_count),
        signature_float_count(func, float_count),
        signature_stack_count(func, stack_count);

    #[local] relation signature_func_reg_count(Address, usize);
    signature_func_reg_count(func, count) <--
        emit_function(func, _, _),
        func_reg_arg_count(func, count);
    signature_func_reg_count(func, 0usize) <--
        emit_function(func, _, _),
        !func_reg_arg_count(func, _);

    #[local] relation signature_callee_pop_bytes(Address, i64);
    signature_callee_pop_bytes(func, selected) <--
        func_callee_pop_bytes(func, _),
        agg selected = ascent::aggregators::max(bytes)
            in func_callee_pop_bytes(func, bytes);

    #[local] relation signature_decorated_arg_bytes(Address, i64);
    signature_decorated_arg_bytes(func, selected) <--
        func_decorated_arg_bytes(func, _),
        agg selected = ascent::aggregators::max(bytes)
            in func_decorated_arg_bytes(func, bytes);

    #[local] relation signature_evidenced_arg_slots(Address, usize);
    signature_evidenced_arg_slots(func, slots) <--
        abi_reg_args_per_function(true),
        abi_pointer_size(slot_size),
        if *slot_size > 0,
        signature_decorated_arg_bytes(func, bytes),
        let slots = (*bytes / *slot_size) as usize;
    signature_evidenced_arg_slots(func, slots) <--
        abi_reg_args_per_function(true),
        abi_pointer_size(slot_size),
        if *slot_size > 0,
        signature_callee_pop_bytes(func, bytes),
        !signature_decorated_arg_bytes(func, _),
        signature_func_reg_count(func, reg_count),
        let slots = reg_count.saturating_add((*bytes / *slot_size) as usize);

    #[local] relation signature_position_count_candidate(Address, usize);
    signature_position_count_candidate(func, count) <--
        signature_position_count_base(func, count);
    signature_position_count_candidate(func, count) <--
        signature_position_count_base(func, _),
        signature_evidenced_arg_slots(func, count);

    relation signature_position_count(Address, usize);
    signature_position_count(func, selected) <--
        signature_position_count_candidate(func, _),
        agg selected = max_usize(count)
            in signature_position_count_candidate(func, count);

    #[local] relation signature_strong_call_arity(Address);
    signature_strong_call_arity(func) <--
        call_site_mode(func, mode),
        call_site_mode_freq(func, frequency),
        total_call_sites(func, total),
        signature_position_count(func, position_count),
        // Caller agreement may select among definition-side candidates, but
        // it cannot invent a trailing ABI slot that the analyzed callee never
        // exposed.  Otherwise a stale caller register agrees at every site
        // and turns a one-parameter function into a two-parameter function.
        emit_function_param_count_selected(func, definition_count),
        if mode <= definition_count,
        if strong_call_arity_consensus(*mode, *position_count, *frequency, *total);

    #[local] relation signature_reconciled_param_count_pre_floor(Address, usize);
    signature_reconciled_param_count_pre_floor(func, position_count) <--
        signature_position_count(func, position_count),
        !has_call_sites(func);
    signature_reconciled_param_count_pre_floor(func, position_count) <--
        signature_position_count(func, position_count),
        has_call_sites(func),
        is_varargs_fn(func);
    signature_reconciled_param_count_pre_floor(func, call_count) <--
        has_call_sites(func),
        !is_varargs_fn(func),
        signature_strong_call_arity(func),
        call_site_mode(func, call_count);
    signature_reconciled_param_count_pre_floor(func, position_count) <--
        signature_position_count(func, position_count),
        has_call_sites(func),
        !is_varargs_fn(func),
        !signature_strong_call_arity(func);

    #[local] relation signature_positive_definition_count(Address, usize);
    signature_positive_definition_count(func, count) <--
        emit_function_param_count_selected(func, count),
        if *count > 0;

    relation signature_reconciled_param_count(Address, usize);
    signature_reconciled_param_count(func, count) <--
        signature_reconciled_param_count_pre_floor(func, count),
        if *count > 0;
    signature_reconciled_param_count(func, definition_count) <--
        signature_reconciled_param_count_pre_floor(func, 0),
        !has_call_sites(func),
        signature_positive_definition_count(func, definition_count);
    signature_reconciled_param_count(func, 0usize) <--
        signature_reconciled_param_count_pre_floor(func, 0),
        has_call_sites(func);
    signature_reconciled_param_count(func, 0usize) <--
        signature_reconciled_param_count_pre_floor(func, 0),
        !has_call_sites(func),
        !signature_positive_definition_count(func, _);

    relation signature_confidence(Address, SignatureConfidence);
    signature_confidence(func, SignatureConfidence::DefinitionOnly) <--
        signature_reconciled_param_count(func, _),
        !has_call_sites(func);
    signature_confidence(func, SignatureConfidence::HighConfidence) <--
        signature_reconciled_param_count(func, reconciled_count),
        emit_function_param_count_selected(func, definition_count),
        call_site_mode(func, call_count),
        if reconciled_count == definition_count,
        if definition_count == call_count;
    signature_confidence(func, SignatureConfidence::CallSiteMajority) <--
        signature_reconciled_param_count(func, reconciled_count),
        has_call_sites(func),
        emit_function_param_count_selected(func, definition_count),
        if reconciled_count != definition_count;
    signature_confidence(func, SignatureConfidence::Inferred) <--
        signature_reconciled_param_count(func, reconciled_count),
        has_call_sites(func),
        emit_function_param_count_selected(func, definition_count),
        if reconciled_count == definition_count,
        call_site_mode(func, call_count),
        if definition_count != call_count;
    signature_confidence(func, SignatureConfidence::CallSiteMajority) <--
        signature_reconciled_param_count(func, reconciled_count),
        has_call_sites(func),
        !emit_function_param_count_selected(func, _),
        if *reconciled_count != 0;
    signature_confidence(func, SignatureConfidence::Inferred) <--
        signature_reconciled_param_count(func, 0),
        has_call_sites(func),
        !emit_function_param_count_selected(func, _),
        call_site_mode(func, call_count),
        if *call_count != 0;
    signature_confidence(func, SignatureConfidence::HighConfidence) <--
        signature_reconciled_param_count(func, 0),
        has_call_sites(func),
        !emit_function_param_count_selected(func, _),
        call_site_mode(func, 0);

    // Parameter pointer evidence is another finite transitive closure.  Keep
    // only the base operand of address-preserving operations: the second LEA
    // operand is commonly an integer index and must not acquire pointer type.
    #[local] relation signature_param_root(RTLReg, RTLReg);
    signature_param_root(param, param) <--
        emit_function_param_candidate(_, param);
    signature_param_root(*dst, root) <--
        rtl_inst(_, ?RTLInst::Iop(op, args, dst)),
        if signature_addr_preserving_op(op),
        if !args.is_empty(),
        let base = args[0],
        signature_param_root(base, root);

    relation signature_param_struct_offset(RTLReg, i64);
    signature_param_struct_offset(root, offset) <--
        rtl_inst(_, ?RTLInst::Iload(_, addressing, args, _)),
        if !args.is_empty(),
        if let Some(offset) = signature_indexed_offset(addressing),
        let base = args[0],
        signature_param_root(base, root);
    signature_param_struct_offset(root, offset) <--
        rtl_inst(_, ?RTLInst::Istore(_, addressing, args, _)),
        if !args.is_empty(),
        if let Some(offset) = signature_indexed_offset(addressing),
        let base = args[0],
        signature_param_root(base, root);

    relation signature_param_is_ptr(RTLReg);
    signature_param_is_ptr(root) <--
        signature_param_struct_offset(root, _);

    #[local] relation signature_known_pointer_param(Symbol, usize);
    signature_known_pointer_param(name, position) <--
        known_func_param_is_ptr(name, position);
    signature_known_pointer_param(name, position) <--
        known_extern_signature(name, _, _, params),
        for (position, xtype) in params.iter().enumerate(),
        if pointer_like_xtype(xtype);

    #[local] relation signature_call_args(Symbol, Args);
    signature_call_args(*name, args.clone()) <--
        rtl_inst(_, ?RTLInst::Icall(_, either::Either::Right(either::Either::Right(name)), args, _, _));
    signature_call_args(*name, args.clone()) <--
        rtl_inst(_, ?RTLInst::Itailcall(_, either::Either::Right(either::Either::Right(name)), args));
    signature_call_args(*name, args.clone()) <--
        rtl_inst(_, ?RTLInst::Icall(_, either::Either::Right(either::Either::Left(target)), args, _, _)),
        emit_function(target, name, _);
    signature_call_args(*name, args.clone()) <--
        rtl_inst(_, ?RTLInst::Itailcall(_, either::Either::Right(either::Either::Left(target)), args)),
        emit_function(target, name, _);

    #[local] relation signature_known_pointer_argument(RTLReg);
    signature_known_pointer_argument(*argument) <--
        signature_call_args(name, args),
        for (position, argument) in args.iter().enumerate(),
        signature_known_pointer_param(name, position);

    signature_param_is_ptr(root) <--
        signature_known_pointer_argument(argument),
        signature_param_root(argument, root);

    // main() detection by name only.
    relation is_main_fn(Address);
    is_main_fn(addr) <--
        emit_function(addr, name, _),
        if *name == "main";

    // Return-type ladder. Case 7 (no info -> Xvoid) is implicit: no row emitted, caller reads Xvoid default.
    relation reconciled_return_type(Address, XType);

    // Case 1: definition says void; always wins
    reconciled_return_type(f, XType::Xvoid) <--
        emit_function_void_candidate(f);

    // Case 2: def has_return + explicit xtype
    reconciled_return_type(f, ty) <--
        emit_function_has_return_candidate(f),
        emit_function_return_type_xtype_candidate(f, ty),
        !signature_return_needs_narrowing_proof(f, ty),
        !emit_function_void_candidate(f);

    // Case 3: def has_return but no xtype. The only evidence is "a value was left in the return REGISTER", so the floor is one machine word at the TARGET's width; a fixed Xany64 prints long and claims i386's 4-byte EAX return is 8 bytes.
    reconciled_return_type(f, xt) <--
        emit_function_has_return_candidate(f),
        !emit_function_return_type_xtype_candidate(f, _),
        !emit_function_void_candidate(f),
        abi_pointer_size(psz),
        let xt = word_any_xtype(*psz);

    // Case 4: def xtype present without has_return (unusual but preserves behavior)
    reconciled_return_type(f, ty) <--
        emit_function_return_type_xtype_candidate(f, ty),
        !signature_return_needs_narrowing_proof(f, ty),
        !emit_function_has_return_candidate(f),
        !emit_function_void_candidate(f);

    // Case 5: call sites but none consume return -> Xvoid
    reconciled_return_type(f, XType::Xvoid) <--
        has_call_sites(f),
        !any_call_uses_return(f),
        !emit_function_void_candidate(f),
        !emit_function_has_return_candidate(f),
        !emit_function_return_type_xtype_candidate(f, _);

    // Case 6: call sites and at least one consumes return -> the same target-width machine word as case 3.
    reconciled_return_type(f, xt) <--
        has_call_sites(f),
        any_call_uses_return(f),
        !emit_function_void_candidate(f),
        !emit_function_has_return_candidate(f),
        !emit_function_return_type_xtype_candidate(f, _),
        abi_pointer_size(psz),
        let xt = word_any_xtype(*psz);

    // Deterministic reductions belong in the declarative pass as stratified
    // aggregates, not in HashMap accumulation whose result depends on tuple
    // order.
    relation reconciled_return_type_selected(Address, XType);
    reconciled_return_type_selected(f, selected) <--
        reconciled_return_type(f, _),
        agg selected = max_refined_xtype(xtype) in reconciled_return_type(f, xtype);

    relation emit_function_return_type_xtype_selected(Address, XType);
    emit_function_return_type_xtype_selected(f, selected) <--
        admissible_function_return_type(f, _),
        agg selected = max_refined_xtype(xtype)
            in admissible_function_return_type(f, xtype);

    #[local] relation admissible_function_return_type(Address, XType);
    admissible_function_return_type(f, xtype) <--
        emit_function_return_type_xtype_candidate(f, xtype),
        !signature_return_needs_narrowing_proof(f, xtype);

    relation emit_function_param_type_selected(Address, RTLReg, XType);
    emit_function_param_type_selected(f, reg, selected) <--
        emit_function_param_type_candidate(f, reg, _),
        agg selected = max_refined_xtype(xtype)
            in emit_function_param_type_candidate(f, reg, xtype);

    relation emit_function_param_count_selected(Address, usize);
    emit_function_param_count_selected(f, selected) <--
        emit_function_param_count_candidate(f, _),
        agg selected = max_usize(count)
            in emit_function_param_count_candidate(f, count);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SignatureConfidence {
    KnownExtern,
    HighConfidence,
    CallSiteMajority,
    DefinitionOnly,
    Inferred,
}

#[derive(Debug, Clone)]
pub struct FunctionPrototype {
    pub address: Address,
    pub param_count: usize,
    pub param_types: Vec<XType>,
    pub return_type: XType,
    pub confidence: SignatureConfidence,
    /// True for known varargs callees; param_count is the fixed prefix only.
    pub is_varargs: bool,
}

fn signature_candidates_match_reconciled(
    candidates: &[Signature],
    param_types: &[XType],
    return_type: XType,
) -> bool {
    let [candidate] = candidates else {
        return false;
    };
    candidate.sig_args.as_slice() == param_types && candidate.sig_res == return_type
}

// RTL recognizes the ABI operation before the final fixed prefix is known and
// deliberately leaves this marker argument-less.  Once signature
// reconciliation has selected the function interface, bind it to the actual
// last named parameter required by GCC's `__builtin_next_arg` contract.
fn bind_variadic_next_arg_builtin(inst: &RTLInst, last_named: RTLReg) -> Option<RTLInst> {
    let RTLInst::Ibuiltin(name, args, result) = inst else {
        return None;
    };
    if name != "__builtin_next_arg" || !args.is_empty() {
        return None;
    }
    Some(RTLInst::Ibuiltin(
        name.clone(),
        vec![crate::x86::types::BuiltinArg::BA(last_named)],
        result.clone(),
    ))
}

fn unique_variadic_next_arg_binding(
    candidates: impl IntoIterator<Item = RTLReg>,
) -> Option<RTLReg> {
    let candidates: HashSet<RTLReg> = candidates.into_iter().collect();
    if candidates.len() == 1 {
        candidates.iter().next().copied()
    } else {
        None
    }
}

pub struct SignatureReconciliationPass;

impl IRPass for SignatureReconciliationPass {
    fn name(&self) -> &'static str {
        "signature-reconciliation"
    }

    fn run(&self, db: &mut DecompileDB) {
        reconcile_signatures(db);
    }

    fn inputs(&self) -> &'static [&'static str] {
        &[
            "emit_function",
            "emit_function_param_candidate",
            "emit_function_param_count_candidate",
            "emit_function_param_type_candidate",
            "emit_function_has_return_candidate",
            "emit_function_void_candidate",
            "emit_function_return_type_xtype_candidate",
            "function_return_point_reg",
            "ax_value_addr",
            "abi_ret_int_reg",
            "ltl_inst",
            "machine_register_write_view",
            "emit_function_signature_candidate",
            "call_target_func",
            "func_tailcalls_local",
            "call_return_reg",
            "call_args_collected_candidate",
            "call_float_args_collected",
            "call_returns_value",
            "known_extern_signature",
            "call_site",
            "reg_rtl",
            "reg_def_used",
            "func_param_position_type",
            "reg_xtl",
            "emit_var_type_candidate",
            "call_arg",
            "func_has_param_evidence",
            "call_has_arg_evidence",
            "emit_function_float_param_count",
            "emit_function_stack_param_count",
            "variadic_next_arg_site",
            "variadic_fixed_stack_prefix_count",
            "variadic_fixed_gp_prefix_count",
            "func_has_variadic_xmm_prologue",
            "arg_reg_spilled_to_stack",
            "rtl_inst",
            "op_produces_ptr",
            "global_addr_reg",
            "known_func_param_is_ptr",
            "abi_int_arg_position",
            "abi_shared_arg_slots",
            "abi_first_stack_arg_position",
            "abi_reg_args_per_function",
            "abi_pointer_size",
            // Per-function calling-convention evidence is reduced by the
            // Ascent arity ladder and reused by patch_db's ABI marshalling.
            "func_reg_arg_count",
            "func_callee_pop_bytes",
            "func_decorated_arg_bytes",
        ]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "emit_function_param",
            "emit_function_param_count",
            "emit_function_param_type",
            "emit_function_has_return",
            "emit_function_void",
            "emit_function_return_type_xtype",
            "emit_function_return_type_xtype_candidate",
            "emit_function_return_type",
            "emit_function_signature",
            "emit_var_type_candidate",
            "call_args_collected",
            "emit_var_is_struct",
            "emit_function_param_is_pointer",
            "func_param_struct_type",
            "is_varargs_fn",
            "rtl_inst",
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::{
        bind_variadic_next_arg_builtin, call_site_type_compatible_with_definition,
        signature_candidates_match_reconciled, unique_variadic_next_arg_binding,
        variadic_fixed_gp_count_from_spills, SignatureConfidence, SignatureReconciliationPass,
        SignatureReconciliationProgram,
    };
    use crate::decompile::passes::pass::IRPass;
    use crate::mreg::Mreg;
    use crate::x86::op::{Addressing, Operation};
    use crate::x86::types::LTLInst;
    use crate::x86::types::{CallConv, MemoryChunk, RTLInst, Signature, XType};
    use std::collections::HashSet;
    use std::sync::Arc;

    #[test]
    fn stack_lea_width_signature_uses_rtl_pointer_authority() {
        let mut prog = SignatureReconciliationProgram::default();
        let narrow_node = 0x10;
        let wide_node = 0x20;
        let narrow = 0x110;
        let wide = 0x120;
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

        prog.run();

        assert!(prog
            .signature_hard_pointer_reg
            .iter()
            .any(|fact| fact == &(wide,)));
        assert!(!prog
            .signature_hard_pointer_reg
            .iter()
            .any(|fact| fact == &(narrow,)));
    }

    #[test]
    fn variadic_gp_register_save_suffix_recovers_fixed_prefix() {
        assert_eq!(
            variadic_fixed_gp_count_from_spills(&HashSet::from([1, 2, 3, 4, 5]), 5),
            Some(1)
        );
        assert_eq!(
            variadic_fixed_gp_count_from_spills(&HashSet::from([2, 3, 4, 5]), 5),
            Some(2)
        );
        assert_eq!(
            variadic_fixed_gp_count_from_spills(&HashSet::from([1, 2, 4, 5]), 5),
            None
        );
        assert_eq!(
            variadic_fixed_gp_count_from_spills(&HashSet::from([0, 1, 2, 3, 4, 5]), 5),
            None
        );
    }

    #[test]
    fn gp_only_protocol_pins_the_named_prefix_without_an_xmm_block() {
        let mut program = SignatureReconciliationProgram::default();
        program.emit_function.push((100, "gp_only", 100));
        program.variadic_fixed_gp_prefix_count.push((100, 2));
        program.variadic_fixed_stack_prefix_count.push((100, 0));
        program.reconciled_int_count.push((100, 6));
        program.run();
        assert!(program.is_varargs_fn.iter().any(|r| *r == (100,)));
        assert!(program
            .signature_effective_int_count
            .iter()
            .any(|r| *r == (100, 2)));
        assert!(!program
            .signature_effective_int_count
            .iter()
            .any(|r| *r == (100, 6)));
    }

    #[test]
    fn variadic_next_arg_marker_binds_only_after_signature_selection() {
        let result = 0x1234;
        let last_named = 0x5678;
        let marker = RTLInst::Ibuiltin(
            "__builtin_next_arg".to_string(),
            vec![],
            crate::x86::types::BuiltinArg::BA(result),
        );

        assert_eq!(
            bind_variadic_next_arg_builtin(&marker, last_named),
            Some(RTLInst::Ibuiltin(
                "__builtin_next_arg".to_string(),
                vec![crate::x86::types::BuiltinArg::BA(last_named)],
                crate::x86::types::BuiltinArg::BA(result),
            ))
        );
        assert!(bind_variadic_next_arg_builtin(
            &RTLInst::Ibuiltin(
                "__builtin_next_arg".to_string(),
                vec![crate::x86::types::BuiltinArg::BA(last_named)],
                crate::x86::types::BuiltinArg::BA(result),
            ),
            last_named,
        )
        .is_none());
        assert_eq!(
            unique_variadic_next_arg_binding([last_named, last_named]),
            Some(last_named)
        );
        assert_eq!(
            unique_variadic_next_arg_binding([last_named, result]),
            None,
            "shared CFG owners must agree before the marker is bound"
        );
        assert_eq!(unique_variadic_next_arg_binding([]), None);
    }

    #[test]
    fn variadic_va_start_stack_prefix_overrides_incidental_load_count() {
        let function = 0x6000;
        let mut prog = SignatureReconciliationProgram::default();
        prog.emit_function.push((function, "variadic", function));
        prog.func_has_variadic_xmm_prologue.push((function,));
        prog.reconciled_int_count.push((function, 6));
        prog.emit_function_float_param_count.push((function, 0));
        prog.emit_function_stack_param_count.push((function, 0));
        prog.variadic_fixed_stack_prefix_count.push((function, 1));
        prog.abi_shared_arg_slots.push((false,));

        prog.run();

        assert!(prog
            .signature_stack_count
            .iter()
            .any(|fact| fact == &(function, 1)));
        assert!(!prog
            .signature_stack_count
            .iter()
            .any(|fact| fact == &(function, 0)));
        assert!(prog
            .signature_position_count
            .iter()
            .any(|fact| fact == &(function, 7)));
    }

    #[test]
    fn arity_and_confidence_ladder_is_declarative() {
        let function = 0x1000;
        let mut prog = SignatureReconciliationProgram::default();
        prog.emit_function.push((function, "callee", 1));
        prog.emit_function_param_count_candidate.push((function, 3));
        prog.abi_int_arg_position.push((Mreg::DI, 0));
        prog.abi_first_stack_arg_position.push((6,));
        prog.abi_pointer_size.push((8,));
        prog.func_has_param_evidence.push((function, 0));
        for (call, count) in [(10, 3usize), (20, 3), (30, 2)] {
            prog.call_target_func.push((call, function));
            prog.call_args_collected_candidate
                .push((call, Arc::new((0..count as u64).collect())));
        }

        prog.run();

        assert!(prog
            .signature_reconciled_param_count
            .iter()
            .any(|row| row == &(function, 3)));
        assert!(prog
            .signature_confidence
            .iter()
            .any(|row| row == &(function, SignatureConfidence::HighConfidence)));
    }

    #[test]
    fn caller_consensus_cannot_invent_a_trailing_parameter() {
        let function = 0x1800;
        let mut prog = SignatureReconciliationProgram::default();
        prog.emit_function.push((function, "one_param", 1));
        prog.emit_function_param_count_candidate.push((function, 1));
        prog.abi_int_arg_position.push((Mreg::DI, 0));
        prog.abi_int_arg_position.push((Mreg::SI, 1));
        prog.abi_first_stack_arg_position.push((6,));
        prog.abi_pointer_size.push((8,));
        prog.func_has_param_evidence.push((function, 0));
        for call in [10, 20, 30] {
            prog.call_target_func.push((call, function));
            prog.call_args_collected_candidate
                .push((call, Arc::new(vec![100, 200])));
        }

        prog.run();

        assert!(prog
            .signature_reconciled_param_count
            .iter()
            .any(|row| row == &(function, 1)));
        assert!(prog
            .signature_confidence
            .iter()
            .any(|row| row == &(function, SignatureConfidence::Inferred)));
    }

    #[test]
    fn variadic_call_arguments_do_not_inflate_fixed_arity() {
        let function = 0x2000;
        let call = 40;
        let gp_regs = [Mreg::DI, Mreg::SI, Mreg::DX, Mreg::CX, Mreg::R8, Mreg::R9];
        let mut prog = SignatureReconciliationProgram::default();
        prog.emit_function.push((function, "variadic", 1));
        prog.emit_function_param_count_candidate.push((function, 2));
        prog.abi_first_stack_arg_position.push((6,));
        prog.abi_pointer_size.push((8,));
        prog.func_has_variadic_xmm_prologue.push((function,));
        for (position, reg) in gp_regs.into_iter().enumerate() {
            prog.abi_int_arg_position.push((reg, position));
            if position >= 2 {
                prog.arg_reg_spilled_to_stack.push((function, reg));
            }
        }
        prog.call_target_func.push((call, function));
        prog.call_args_collected_candidate
            .push((call, Arc::new(vec![1, 2, 3, 4, 5])));

        prog.run();

        assert!(prog
            .signature_variadic_fixed_gp_count
            .iter()
            .any(|row| row == &(function, 2)));
        assert!(prog
            .signature_reconciled_param_count
            .iter()
            .any(|row| row == &(function, 2)));
        assert!(prog
            .signature_confidence
            .iter()
            .any(|row| row == &(function, SignatureConfidence::Inferred)));
    }

    #[test]
    fn call_site_votes_once_after_local_type_refinement() {
        let mut prog = SignatureReconciliationProgram::default();
        prog.call_arg.push((0x10, 1, 100));
        prog.call_arg.push((0x20, 1, 200));
        prog.emit_var_type_candidate.push((100, XType::Xint));
        prog.emit_var_type_candidate.push((100, XType::Xptr));
        prog.emit_var_type_candidate.push((200, XType::Xint));
        prog.op_produces_ptr.push((0x01, 100));

        prog.run();

        assert!(prog
            .signature_call_arg_type_at_site
            .iter()
            .any(|row| row == &(0x10, 1, XType::Xptr)));
        assert!(prog
            .signature_call_arg_type_at_site
            .iter()
            .any(|row| row == &(0x20, 1, XType::Xint)));
        assert_eq!(prog.signature_call_arg_type_at_site.len(), 2);
    }

    #[test]
    fn a_callers_storage_view_does_not_narrow_the_callee_value_interface() {
        let mut prog = SignatureReconciliationProgram::default();
        for (position, xtype) in [
            XType::Xint8signed,
            XType::Xint8unsigned,
            XType::Xint16signed,
            XType::Xint16unsigned,
            XType::Xbool,
        ]
        .into_iter()
        .enumerate()
        {
            let reg = position as u64 + 100;
            prog.call_arg.push((10, position, reg));
            prog.emit_var_type_candidate.push((reg, xtype));
        }
        prog.run();
        assert_eq!(prog.signature_call_arg_type_at_site.len(), 5);
        assert!(prog
            .signature_call_arg_type_at_site
            .iter()
            .all(|(_, _, ty)| *ty == XType::Xint));
    }

    #[test]
    fn selected_rtl_call_args_replace_stale_setup_values() {
        let call = 0x40;
        let target = 0x1000;
        let mut prog = SignatureReconciliationProgram::default();
        prog.call_arg.push((call, 0, 100));
        prog.call_arg.push((call, 1, 200));
        prog.call_target_func.push((call, target));
        prog.rtl_inst.push((
            call,
            RTLInst::Icall(
                None,
                either::Either::Right(either::Either::Left(target)),
                Arc::new(vec![100, 300]),
                None,
                0x44,
            ),
        ));

        prog.run();

        let selected: HashSet<_> = prog.signature_selected_call_arg.iter().copied().collect();
        assert_eq!(selected, HashSet::from([(call, 0, 100), (call, 1, 300)]));
    }

    #[test]
    fn exact_internal_pointer_return_overrides_integer_width_floor() {
        let producing_call = 0x20;
        let consuming_call = 0x40;
        let pointer_function = 0x1000;
        let result_reg = 300;
        let mut prog = SignatureReconciliationProgram::default();
        prog.call_target_func
            .push((producing_call, pointer_function));
        prog.call_return_reg.push((producing_call, result_reg));
        prog.emit_function_return_type_xtype_candidate
            .push((pointer_function, XType::Xcharptr));
        prog.call_arg.push((consuming_call, 4, result_reg));
        prog.emit_var_type_candidate.push((result_reg, XType::Xint));
        prog.emit_var_type_candidate
            .push((result_reg, XType::Xcharptr));
        prog.run();

        assert!(prog
            .signature_call_arg_type_at_site
            .iter()
            .any(|row| row == &(consuming_call, 4, XType::Xcharptr)));
    }

    #[test]
    fn returned_arithmetic_value_is_not_truncated_to_a_storage_type() {
        let mut prog = SignatureReconciliationProgram::default();
        let (func, definition, ret, reg) = (1, 30, 4, 101);
        prog.abi_ret_int_reg.push((Mreg::AX,));
        prog.function_return_point_reg.push((func, ret, reg));
        prog.ax_value_addr.push((ret, definition));
        prog.machine_register_write_view
            .push((definition, Mreg::AX, 32));
        prog.emit_function_has_return_candidate.push((func,));
        prog.emit_function_return_type_xtype_candidate
            .push((func, XType::Xint8unsigned));
        prog.ltl_inst.push((
            definition,
            LTLInst::Lop(Operation::Oaddimm(300), Arc::new(vec![Mreg::AX]), Mreg::AX),
        ));
        prog.run();
        assert!(prog
            .reconciled_return_type_selected
            .iter()
            .any(|row| *row == (func, XType::Xint)));
        assert!(prog
            .emit_function_return_type_xtype_selected
            .iter()
            .any(|row| *row == (func, XType::Xint)));
    }

    #[test]
    fn returned_value_evidence_is_declared_to_the_parallel_scheduler() {
        let pass = SignatureReconciliationPass;
        for relation in [
            "function_return_point_reg",
            "ax_value_addr",
            "abi_ret_int_reg",
            "ltl_inst",
            "reg_def_used",
            "call_target_func",
            "func_tailcalls_local",
            "machine_register_write_view",
        ] {
            assert!(
                pass.inputs().contains(&relation),
                "undeclared return-value input: {relation}"
            );
        }
    }

    #[test]
    fn returned_value_type_follows_reaching_definitions_not_address_order() {
        let mut prog = SignatureReconciliationProgram::default();
        let (func, arithmetic, copied, ret, reg) = (1, 90, 3, 20, 101);
        prog.abi_ret_int_reg.push((Mreg::AX,));
        prog.function_return_point_reg.push((func, ret, reg));
        prog.ax_value_addr.push((ret, copied));
        prog.emit_function_has_return_candidate.push((func,));
        prog.emit_function_return_type_xtype_candidate
            .push((func, XType::Xint8unsigned));
        prog.ltl_inst.extend([
            (
                arithmetic,
                LTLInst::Lop(Operation::Oaddlimm(300), Arc::new(vec![Mreg::DX]), Mreg::DX),
            ),
            (
                copied,
                LTLInst::Lop(Operation::Omove, Arc::new(vec![Mreg::DX]), Mreg::AX),
            ),
        ]);
        prog.reg_def_used.push((arithmetic, Mreg::DX, copied));
        prog.machine_register_write_view
            .push((arithmetic, Mreg::DX, 64));
        prog.run();
        assert!(prog
            .reconciled_return_type_selected
            .iter()
            .any(|row| *row == (func, XType::Xlong)));
    }

    #[test]
    fn a_narrow_value_range_does_not_project_the_return_abi_onto_a_byte() {
        let mut prog = SignatureReconciliationProgram::default();
        let (func, arithmetic, narrowed, ret, reg) = (1, 3, 30, 20, 101);
        prog.abi_ret_int_reg.push((Mreg::AX,));
        prog.function_return_point_reg.push((func, ret, reg));
        prog.ax_value_addr.push((ret, narrowed));
        prog.emit_function_has_return_candidate.push((func,));
        prog.emit_function_return_type_xtype_candidate
            .extend([(func, XType::Xint), (func, XType::Xint8unsigned)]);
        prog.ltl_inst.extend([
            (
                arithmetic,
                LTLInst::Lop(Operation::Oaddimm(300), Arc::new(vec![Mreg::AX]), Mreg::AX),
            ),
            (
                narrowed,
                LTLInst::Lop(
                    Operation::Ocast8unsigned,
                    Arc::new(vec![Mreg::AX]),
                    Mreg::AX,
                ),
            ),
        ]);
        prog.reg_def_used.push((arithmetic, Mreg::AX, narrowed));
        prog.machine_register_write_view
            .push((narrowed, Mreg::AX, 32));
        prog.run();
        assert!(prog
            .reconciled_return_type_selected
            .iter()
            .any(|row| *row == (func, XType::Xint)));
    }

    #[test]
    fn returned_value_carriers_propagate_through_calls_and_tailcalls() {
        let mut prog = SignatureReconciliationProgram::default();
        prog.abi_ret_int_reg.push((Mreg::AX,));
        for (func, ret, definition) in [(1, 10, 9), (2, 20, 19)] {
            prog.function_return_point_reg.push((func, ret, 101 + func));
            prog.ax_value_addr.push((ret, definition));
            prog.emit_function_has_return_candidate.push((func,));
            prog.emit_function_return_type_xtype_candidate
                .push((func, XType::Xint8unsigned));
        }
        prog.ltl_inst.push((
            9,
            LTLInst::Lop(Operation::Oaddimm(300), Arc::new(vec![Mreg::AX]), Mreg::AX),
        ));
        prog.call_target_func.push((19, 1));
        prog.machine_register_write_view.push((9, Mreg::AX, 32));
        prog.func_tailcalls_local
            .extend([(3, 2), (4, 3), (3, 4), (5, 6), (6, 5)]);
        prog.run();
        for func in [1, 2, 3, 4] {
            assert!(
                prog.reconciled_return_type_selected
                    .iter()
                    .any(|row| *row == (func, XType::Xint)),
                "function {func}"
            );
        }
        for func in [5, 6] {
            assert!(!prog
                .emit_function_return_type_xtype_selected
                .iter()
                .any(|(f, _)| *f == func));
        }
    }

    #[test]
    fn returned_integer_carriers_do_not_inherit_subword_storage_signedness() {
        for (bits, expected) in [
            (8, XType::Xint),
            (16, XType::Xint),
            (32, XType::Xint),
            (64, XType::Xlong),
        ] {
            let mut prog = SignatureReconciliationProgram::default();
            prog.abi_ret_int_reg.push((Mreg::AX,));
            prog.function_return_point_reg.push((1, 3, 101));
            prog.ax_value_addr.push((3, 9));
            prog.emit_function_has_return_candidate.push((1,));
            prog.emit_function_return_type_xtype_candidate
                .extend([(1, XType::Xint8signed), (1, XType::Xint8unsigned)]);
            prog.machine_register_write_view.push((9, Mreg::AX, bits));
            prog.ltl_inst.push((
                9,
                LTLInst::Lgetstack(
                    crate::x86::types::Slot::Local,
                    -1,
                    crate::x86::types::Typ::Tint,
                    Mreg::AX,
                ),
            ));
            prog.run();
            assert!(
                prog.reconciled_return_type_selected
                    .iter()
                    .any(|row| *row == (1, expected)),
                "{bits} bits: {:?}",
                prog.reconciled_return_type_selected
            );
        }
    }

    #[test]
    fn a_decoded_copy_width_is_not_widened_by_its_source_carrier() {
        let mut prog = SignatureReconciliationProgram::default();
        prog.abi_ret_int_reg.push((Mreg::AX,));
        prog.emit_function_has_return_candidate.push((1,));
        prog.function_return_point_reg.push((1, 3, 101));
        prog.ax_value_addr.push((3, 9));
        prog.machine_register_write_view
            .extend([(7, Mreg::DX, 64), (9, Mreg::AX, 32)]);
        prog.ltl_inst.push((
            9,
            LTLInst::Lop(Operation::Omove, Arc::new(vec![Mreg::DX]), Mreg::AX),
        ));
        prog.reg_def_used.push((7, Mreg::DX, 9));
        prog.run();
        assert!(prog
            .reconciled_return_type_selected
            .iter()
            .any(|row| *row == (1, XType::Xint)));
    }

    #[test]
    fn unrelated_wide_definitions_do_not_change_the_return_interface() {
        let mut prog = SignatureReconciliationProgram::default();
        prog.abi_ret_int_reg.push((Mreg::AX,));
        prog.emit_function_has_return_candidate.push((1,));
        prog.emit_function_return_type_xtype_candidate
            .push((1, XType::Xint8unsigned));
        prog.function_return_point_reg.push((1, 3, 101));
        prog.ax_value_addr.push((3, 9));
        prog.machine_register_write_view.push((2, Mreg::AX, 64));
        prog.run();
        assert!(prog
            .reconciled_return_type_selected
            .iter()
            .any(|row| *row == (1, XType::Xint8unsigned)));
    }

    #[test]
    fn ambiguous_pointer_candidate_does_not_override_scalar_provenance() {
        let mut prog = SignatureReconciliationProgram::default();
        prog.call_arg.push((0x10, 1, 100));
        prog.emit_var_type_candidate
            .push((100, XType::Xlongunsigned));
        prog.emit_var_type_candidate.push((100, XType::Xptr));

        prog.run();

        assert!(prog
            .signature_call_arg_type_at_site
            .iter()
            .any(|row| row == &(0x10, 1, XType::Xlongunsigned)));
        assert_eq!(prog.signature_call_arg_type_at_site.len(), 1);
    }

    #[test]
    fn hard_address_provenance_overrides_an_integer_width_floor() {
        let mut prog = SignatureReconciliationProgram::default();
        prog.call_arg.push((0x10, 1, 100));
        prog.emit_var_type_candidate.push((100, XType::Xint));
        prog.op_produces_ptr.push((0x01, 100));

        prog.run();

        assert!(prog
            .signature_call_arg_type_at_site
            .iter()
            .any(|row| row == &(0x10, 1, XType::Xptr)));
        assert_eq!(prog.signature_call_arg_type_at_site.len(), 1);
    }

    #[test]
    fn call_site_pointer_provenance_is_a_declared_scheduler_input() {
        let pass = SignatureReconciliationPass;
        for input in ["op_produces_ptr", "global_addr_reg"] {
            assert!(pass.inputs().contains(&input));
        }
    }

    #[test]
    fn caller_vote_cannot_change_definition_abi_value_class() {
        assert!(!call_site_type_compatible_with_definition(
            Some(&XType::Xlong),
            &XType::Xfloat,
        ));
        assert!(!call_site_type_compatible_with_definition(
            Some(&XType::Xsingle),
            &XType::Xint,
        ));
        assert!(call_site_type_compatible_with_definition(
            Some(&XType::Xlong),
            &XType::Xlongunsigned,
        ));
        assert!(call_site_type_compatible_with_definition(
            Some(&XType::Xany64),
            &XType::Xptr,
        ));
        assert!(call_site_type_compatible_with_definition(
            None,
            &XType::Xfloat,
        ));
    }

    #[test]
    fn refined_return_type_invalidates_stale_rtl_signature() {
        let stale = Signature {
            sig_args: Arc::new(vec![XType::Xptr, XType::Xptr]),
            sig_res: XType::Xany64,
            sig_cc: CallConv::default(),
        };
        let refined = Signature {
            sig_args: stale.sig_args.clone(),
            sig_res: XType::Xptr,
            sig_cc: CallConv::default(),
        };

        assert!(!signature_candidates_match_reconciled(
            &[stale.clone()],
            refined.sig_args.as_slice(),
            refined.sig_res,
        ));
        assert!(signature_candidates_match_reconciled(
            &[refined.clone()],
            refined.sig_args.as_slice(),
            refined.sig_res,
        ));
        assert!(!signature_candidates_match_reconciled(
            &[stale, refined.clone()],
            refined.sig_args.as_slice(),
            refined.sig_res,
        ));
    }

    #[test]
    fn exact_final_move_source_refines_pointer_return_type() {
        let first_func = 0x1000;
        let second_func = 0x2000;
        let source = 101;
        let return_reg = 102;
        let middle_reg = 103;
        let final_reg = 104;
        let mut prog = SignatureReconciliationProgram::default();
        prog.emit_var_type_candidate.push((source, XType::Xcharptr));
        prog.emit_var_type_candidate
            .push((return_reg, XType::Xany64));
        prog.rtl_inst.push((
            20,
            RTLInst::Iop(Operation::Omove, Arc::new(vec![source]), return_reg),
        ));
        prog.function_return_point_reg
            .push((first_func, 30, return_reg));
        prog.call_target_func.push((40, first_func));
        prog.call_return_reg.push((40, middle_reg));
        prog.function_return_point_reg
            .push((second_func, 50, middle_reg));
        prog.call_target_func.push((60, second_func));
        prog.call_return_reg.push((60, final_reg));

        prog.run();

        assert!(prog
            .emit_function_return_type_xtype_candidate
            .iter()
            .any(|row| row == &(first_func, XType::Xcharptr)));
        assert!(prog
            .emit_function_return_type_xtype_candidate
            .iter()
            .any(|row| row == &(second_func, XType::Xcharptr)));
        assert!(prog
            .emit_var_type_candidate
            .iter()
            .any(|row| row == &(final_reg, XType::Xcharptr)));
    }

    #[test]
    fn parameter_pointer_roots_are_derived_declaratively() {
        let function = 0x1000;
        let dereferenced_param = 201;
        let scalar_index = 202;
        let derived_base = 203;
        let forwarded_param = 204;
        let forwarded_value = 205;
        let mut prog = SignatureReconciliationProgram::default();
        prog.emit_function_param_candidate
            .push((function, dereferenced_param));
        prog.emit_function_param_candidate
            .push((function, forwarded_param));
        prog.rtl_inst.push((
            10,
            RTLInst::Iop(
                Operation::Oadd,
                Arc::new(vec![dereferenced_param, scalar_index]),
                derived_base,
            ),
        ));
        prog.rtl_inst.push((
            11,
            RTLInst::Iload(
                MemoryChunk::MInt32,
                Addressing::Aindexed(8),
                Arc::new(vec![derived_base]),
                300,
            ),
        ));
        prog.rtl_inst.push((
            12,
            RTLInst::Iop(
                Operation::Omove,
                Arc::new(vec![forwarded_param]),
                forwarded_value,
            ),
        ));
        prog.known_func_param_is_ptr.push(("sink", 0));
        prog.rtl_inst.push((
            13,
            RTLInst::Icall(
                None,
                either::Either::Right(either::Either::Right("sink")),
                Arc::new(vec![forwarded_value]),
                None,
                14,
            ),
        ));

        prog.run();

        assert!(prog
            .signature_param_struct_offset
            .iter()
            .any(|row| row == &(dereferenced_param, 8)));
        assert!(prog
            .signature_param_is_ptr
            .iter()
            .any(|row| row == &(dereferenced_param,)));
        assert!(prog
            .signature_param_is_ptr
            .iter()
            .any(|row| row == &(forwarded_param,)));
        assert!(!prog
            .signature_param_is_ptr
            .iter()
            .any(|row| row == &(scalar_index,)));
    }
}

// ABI parameter order; Windows uses shared GP/XMM ordinal slots, and a class bit keeps ties deterministic while class evidence chooses the real one.
pub(crate) fn param_mreg_sort_key(mreg: Mreg, abi: &crate::abi::AbiConfig) -> usize {
    if let Some(pos) = abi.int_arg_regs.iter().position(|r| *r == mreg) {
        return if abi.uses_shared_arg_slots() {
            pos * 2
        } else {
            pos
        };
    }
    if let Some(pos) = abi.float_arg_regs.iter().position(|r| *r == mreg) {
        return if abi.uses_shared_arg_slots() {
            pos * 2 + 1
        } else {
            abi.int_arg_regs.len() + pos
        };
    }
    usize::MAX
}

// Per-position int arg confirmation is in Ascent (int_pos_confirmed / reconciled_int_count).

// Per-function calling-convention evidence keyed by function address, from the relations the loader (decorated names) and asm_pass (RET imm16) derive; empty on every target whose convention is image-wide, where each lookup falls back to the global AbiConfig.
fn per_function_abi(db: &DecompileDB) -> HashMap<Address, crate::abi::FuncAbi> {
    let mut table: HashMap<Address, crate::abi::FuncAbi> = HashMap::new();
    for &(addr, count) in db.rel_iter::<(Address, usize)>("func_reg_arg_count") {
        let entry = table.entry(addr).or_default();
        entry.reg_arg_count = entry.reg_arg_count.max(count);
    }
    // Every RET in one function pops the same amount; take the max so a mis-decoded byte never shrinks it.
    for &(addr, bytes) in db.rel_iter::<(Address, i64)>("func_callee_pop_bytes") {
        let entry = table.entry(addr).or_default();
        entry.callee_pop_bytes = Some(entry.callee_pop_bytes.unwrap_or(0).max(bytes));
    }
    for &(addr, bytes) in db.rel_iter::<(Address, i64)>("func_decorated_arg_bytes") {
        let entry = table.entry(addr).or_default();
        entry.decorated_arg_bytes = Some(entry.decorated_arg_bytes.unwrap_or(0).max(bytes));
    }
    table
}

/// Reduce all type candidates attached to one concrete call argument to one
/// vote for that call site.  Voting over the raw candidate multiset makes a
/// single argument with both its width floor (`Xint`) and hard address
/// evidence (`Xptr`) look like two disagreeing callers, so neither candidate
/// can win a majority.  Address-producing provenance selects the pointer class;
/// without it, a scalar candidate wins over a speculative pointer candidate.
/// Only the resulting type participates in the cross-site prototype vote.
fn pointer_like_xtype(xtype: &XType) -> bool {
    matches!(
        xtype,
        XType::Xptr
            | XType::Xintptr
            | XType::Xfloatptr
            | XType::Xsingleptr
            | XType::Xfuncptr
            | XType::XstructPtr(_)
            | XType::Xcharptr
            | XType::Xcharptrptr
    )
}

/// A caller vote may refine an uncertain declaration, but it must not change
/// the ABI value class established by the callee's own data use.  In
/// particular, an integer/word parameter is carried in a GP register (or an
/// integer-typed stack slot); a speculative float candidate at a call site
/// cannot turn it into an XMM/float parameter.  Width, signedness, and pointer
/// refinements remain within the GP class.
fn call_site_type_compatible_with_definition(definition: Option<&XType>, caller: &XType) -> bool {
    let is_float = |ty: &XType| matches!(ty, XType::Xfloat | XType::Xsingle);
    definition
        .map(|defined| is_float(defined) == is_float(caller))
        .unwrap_or(true)
}

fn reconcile_signatures(db: &mut DecompileDB) {
    let target_abi = db.abi().clone();
    // The no-evidence floor for a register-passed value: one machine word at the target's width.
    let word_any = word_any_xtype(target_abi.pointer_size as i64);
    let func_abi = per_function_abi(db);

    let functions: HashMap<Address, Symbol> = db
        .rel_iter::<(Address, Symbol, Node)>("emit_function")
        .map(|&(addr, name, _)| (addr, name))
        .collect();

    if functions.is_empty() {
        return;
    }

    run_pass!(db, SignatureReconciliationProgram);

    // Consume Ascent helper relations into per-function lookup maps.
    let reconciled_int_count_map: HashMap<Address, usize> = db
        .rel_iter::<(Address, usize)>("reconciled_int_count")
        .map(|&(a, c)| (a, c))
        .collect();
    let effective_int_count_map: HashMap<Address, usize> = db
        .rel_iter::<(Address, usize)>("signature_effective_int_count")
        .copied()
        .collect();
    let reconciled_param_count_map: HashMap<Address, usize> = db
        .rel_iter::<(Address, usize)>("signature_reconciled_param_count")
        .copied()
        .collect();
    let signature_confidence_map: HashMap<Address, SignatureConfidence> = db
        .rel_iter::<(Address, SignatureConfidence)>("signature_confidence")
        .copied()
        .collect();
    let has_call_sites_set: HashSet<Address> = db
        .rel_iter::<(Address,)>("has_call_sites")
        .map(|&(a,)| a)
        .collect();
    let any_call_uses_return_set: HashSet<Address> = db
        .rel_iter::<(Address,)>("any_call_uses_return")
        .map(|&(a,)| a)
        .collect();
    let is_varargs_fn_set: HashSet<Address> = db
        .rel_iter::<(Address,)>("is_varargs_fn")
        .map(|&(a,)| a)
        .collect();
    let is_main_fn_set: HashSet<Address> = db
        .rel_iter::<(Address,)>("is_main_fn")
        .map(|&(a,)| a)
        .collect();
    let reconciled_return_type_map: HashMap<Address, XType> = db
        .rel_iter::<(Address, XType)>("reconciled_return_type_selected")
        .copied()
        .collect();

    let extern_sigs: HashMap<Symbol, (usize, XType, Arc<Vec<XType>>)> = db
        .rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("known_extern_signature")
        .map(|&(name, count, ref ret, ref params)| (name, (count, ret.clone(), params.clone())))
        .collect();

    let def_param_counts: HashMap<Address, usize> = db
        .rel_iter::<(Address, usize)>("emit_function_param_count_selected")
        .copied()
        .collect();

    let mut def_param_types: HashMap<Address, HashMap<RTLReg, XType>> = HashMap::new();
    for &(addr, reg, xtype) in
        db.rel_iter::<(Address, RTLReg, XType)>("emit_function_param_type_selected")
    {
        def_param_types.entry(addr).or_default().insert(reg, xtype);
    }

    let mut rtl_to_mreg: HashMap<(Address, RTLReg), Mreg> = HashMap::new();
    for &(node, ref mreg, rtl_reg) in db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl") {
        rtl_to_mreg.insert((node, rtl_reg), *mreg);
    }

    let mut def_params: HashMap<Address, Vec<RTLReg>> = HashMap::new();
    for &(addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param_candidate") {
        def_params.entry(addr).or_default().push(reg);
    }
    for (addr, params) in def_params.iter_mut() {
        params.sort_by(|a, b| {
            let ka = rtl_to_mreg
                .get(&(*addr, *a))
                .map(|m| param_mreg_sort_key(*m, &target_abi))
                .unwrap_or(usize::MAX);
            let kb = rtl_to_mreg
                .get(&(*addr, *b))
                .map(|m| param_mreg_sort_key(*m, &target_abi))
                .unwrap_or(usize::MAX);
            ka.cmp(&kb).then_with(|| a.cmp(b))
        });
        params.dedup();
    }

    let def_has_return: std::collections::HashSet<Address> = db
        .rel_iter::<(Address,)>("emit_function_has_return_candidate")
        .map(|&(addr,)| addr)
        .collect();
    let def_void: std::collections::HashSet<Address> = db
        .rel_iter::<(Address,)>("emit_function_void_candidate")
        .map(|&(addr,)| addr)
        .collect();
    let def_return_types: HashMap<Address, XType> = db
        .rel_iter::<(Address, XType)>("emit_function_return_type_xtype_selected")
        .copied()
        .collect();

    // RTL builds signature candidates before TypePass can refine value types.
    // Retain the candidate set so reconciliation can detect a stale call ABI
    // even when the refined definition itself needs no other override.
    let def_signature_candidates: HashMap<Address, Vec<Signature>> = {
        let mut map: HashMap<Address, Vec<Signature>> = HashMap::new();
        for &(addr, ref sig) in
            db.rel_iter::<(Address, Signature)>("emit_function_signature_candidate")
        {
            let sigs = map.entry(addr).or_default();
            if !sigs.contains(sig) {
                sigs.push(sig.clone());
            }
        }
        map
    };

    // Diagnostic: trace the return-type ladder inputs for a target function (by name substring), to see why a void-bodied callee whose result is used stays void (X<-void errors).
    if let Ok(target) = std::env::var("MANIFOLD_TRACE_RET") {
        if !target.is_empty() {
            let crv: std::collections::HashSet<Node> = db
                .rel_iter::<(Node, Mreg)>("call_returns_value")
                .map(|&(n, _)| n)
                .collect();
            let ctf: Vec<(Node, Address)> = db
                .rel_iter::<(Node, Address)>("call_target_func")
                .map(|&(n, a)| (n, a))
                .collect();
            for &(addr, ref name, _) in db.rel_iter::<(Address, Symbol, Node)>("emit_function") {
                if !name.contains(target.as_str()) {
                    continue;
                }
                let sites: Vec<Node> = ctf
                    .iter()
                    .filter(|(_, a)| *a == addr)
                    .map(|(n, _)| *n)
                    .collect();
                let sites_used = sites.iter().filter(|n| crv.contains(n)).count();
                eprintln!(
                    "RET-TRACE {} @ {:#x}: void_cand={} has_ret={} xtype={:?} has_calls={} any_uses_ret={} reconciled={:?} | call_target_sites={} sites_with_used_result={}",
                    name, addr,
                    def_void.contains(&addr), def_has_return.contains(&addr), def_return_types.get(&addr),
                    has_call_sites_set.contains(&addr), any_call_uses_return_set.contains(&addr),
                    reconciled_return_type_map.get(&addr),
                    sites.len(), sites_used,
                );
            }
        }
    }

    // call_targets is consumed by patch_db and the call-site arg-type lookup below.
    let call_target_data: Vec<(Node, Address)> = db
        .rel_iter::<(Node, Address)>("call_target_func")
        .copied()
        .collect();
    let call_targets: HashMap<Node, Address> = call_target_data.iter().copied().collect();

    let emit_var_types: HashMap<RTLReg, Vec<XType>> = {
        let mut map: HashMap<RTLReg, Vec<XType>> = HashMap::new();
        for &(reg, ref xtype) in db.rel_iter::<(RTLReg, XType)>("emit_var_type_candidate") {
            let types = map.entry(reg).or_default();
            if !types.contains(xtype) {
                types.push(xtype.clone());
            }
        }
        // Sort candidates so tie-breakers are stable regardless of parallel Ascent tuple order.
        for types in map.values_mut() {
            types.sort();
        }
        map
    };

    let mut call_site_arg_types: HashMap<Address, HashMap<usize, Vec<XType>>> = HashMap::new();
    for &(call_node, pos, xtype) in
        db.rel_iter::<(Node, usize, XType)>("signature_call_arg_type_at_site")
    {
        if let Some(&target_addr) = call_targets.get(&call_node) {
            call_site_arg_types
                .entry(target_addr)
                .or_default()
                .entry(pos)
                .or_default()
                .push(xtype);
        }
    }
    // Sort caller-type vectors so later tie-breaking is independent of source tuple order.
    for pos_map in call_site_arg_types.values_mut() {
        for v in pos_map.values_mut() {
            v.sort();
        }
    }

    // Position-level int-arg evidence lives in the Ascent program above.

    let float_param_counts: HashMap<Address, usize> = db
        .rel_iter::<(Address, usize)>("emit_function_float_param_count")
        .map(|&(addr, count)| (addr, count))
        .collect();

    let mut stack_param_counts: HashMap<Address, usize> = HashMap::new();
    for &(addr, count) in db.rel_iter::<(Address, usize)>("emit_function_stack_param_count") {
        stack_param_counts
            .entry(addr)
            .and_modify(|selected| *selected = (*selected).max(count))
            .or_insert(count);
    }
    // va_start's overflow pointer is definition-side proof of the fixed stack
    // prefix, including named parameters whose values are otherwise unused.
    // It is stricter than tail-walk loads, which may include unnamed args.
    let mut variadic_stack_prefix_counts: HashMap<Address, usize> = HashMap::new();
    for &(addr, count) in db.rel_iter::<(Address, usize)>("variadic_fixed_stack_prefix_count") {
        variadic_stack_prefix_counts
            .entry(addr)
            .and_modify(|selected| *selected = (*selected).max(count))
            .or_insert(count);
    }
    stack_param_counts.extend(variadic_stack_prefix_counts);

    let known_internal_sigs: HashMap<&str, (usize, XType, Vec<XType>)> = [(
        "main",
        (2, XType::Xint, vec![XType::Xint, XType::Xcharptrptr]),
    )]
    .into_iter()
    .collect();

    let param_is_ptr: HashSet<RTLReg> = db
        .rel_iter::<(RTLReg,)>("signature_param_is_ptr")
        .map(|&(reg,)| reg)
        .collect();
    let mut param_struct_offsets: HashMap<RTLReg, HashSet<i64>> = HashMap::new();
    for &(reg, offset) in db.rel_iter::<(RTLReg, i64)>("signature_param_struct_offset") {
        param_struct_offsets.entry(reg).or_default().insert(offset);
    }

    let mut prototypes: Vec<FunctionPrototype> = Vec::new();

    for (&func_addr, &func_name) in &functions {
        // Varargs detection: declarative via SignatureReconciliationProgram.
        let is_va = is_varargs_fn_set.contains(&func_addr);
        if is_va {
            if let Some((param_count, ret_type, param_types)) = extern_sigs.get(func_name) {
                // Variadic internal function: force known param count to avoid materializing register dumps.
                prototypes.push(FunctionPrototype {
                    address: func_addr,
                    param_count: *param_count,
                    param_types: (**param_types).clone(),
                    return_type: *ret_type,
                    confidence: SignatureConfidence::KnownExtern,
                    is_varargs: true,
                });
                continue;
            }
            // Varargs known but no extern sig: fall through, remember is_va so call sites keep extra args.
        }

        // main's signature: the classic `int main(int argc, char **argv)`, upgraded to the 3-arg `int main(int, char **argv, char **envp)` when the body's own recovered evidence shows a third register parameter (ABI-4: the hardcoded 2-arg form could not reconcile envp-using mains).
        if is_main_fn_set.contains(&func_addr) {
            if let Some((param_count, ret_type, param_types)) = known_internal_sigs.get(func_name) {
                let detected_int = reconciled_int_count_map
                    .get(&func_addr)
                    .copied()
                    .unwrap_or(0);
                let (main_count, main_types) = if detected_int >= 3 {
                    (3, vec![XType::Xint, XType::Xcharptrptr, XType::Xcharptrptr])
                } else {
                    (*param_count, param_types.clone())
                };
                prototypes.push(FunctionPrototype {
                    address: func_addr,
                    param_count: main_count,
                    param_types: main_types,
                    return_type: *ret_type,
                    confidence: SignatureConfidence::HighConfidence,
                    is_varargs: is_va,
                });
                continue;
            }
        }

        let def_count = def_param_counts.get(&func_addr).copied().unwrap_or(0);
        let reconciled_int = effective_int_count_map
            .get(&func_addr)
            .copied()
            .unwrap_or_else(|| {
                reconciled_int_count_map
                    .get(&func_addr)
                    .copied()
                    .unwrap_or(0)
            });
        let float_count = float_param_counts.get(&func_addr).copied().unwrap_or(0);
        let stack_count = stack_param_counts.get(&func_addr).copied().unwrap_or(0);
        let func_reg_args = func_abi.get(&func_addr).map_or(0, |abi| abi.reg_arg_count);
        let reconciled_count = reconciled_param_count_map
            .get(&func_addr)
            .copied()
            .unwrap_or(def_count);
        let confidence = signature_confidence_map
            .get(&func_addr)
            .copied()
            .unwrap_or(SignatureConfidence::Inferred);

        let existing_types = def_param_types.get(&func_addr);
        let existing_params = def_params.get(&func_addr);
        // TR-5: stack params are keyed by fresh_stack_param_reg, not by register webs, so positions >= stack_base must be looked up via fresh_stack_param_reg rather than existing_params.get(i).
        // Stack arguments begin after this function's own register arguments; func_reg_args is 0 unless its convention evidence claims ECX/EDX, so no other target's ordinals move.
        let stack_base = if target_abi.uses_shared_arg_slots() {
            target_abi.first_stack_arg_position()
        } else {
            (reconciled_int + float_count).max(func_reg_args)
        };
        let pos_reg = |i: usize| -> Option<RTLReg> {
            if i >= stack_base && i < stack_base + stack_count {
                return Some(crate::decompile::passes::rtl_pass::fresh_stack_param_reg(
                    func_addr,
                    i - stack_base,
                ));
            }
            existing_params.and_then(|params| params.get(i).copied())
        };
        let mut param_types = Vec::with_capacity(reconciled_count);
        for i in 0..reconciled_count {
            let mut resolved_type: Option<XType> = None;

            // Priority 1: Definition type from emit_function_param_type
            if let Some(reg) = pos_reg(i) {
                if let Some(types) = existing_types {
                    if let Some(xtype) = types.get(&reg) {
                        resolved_type = Some(xtype.clone());
                    }
                }
            }

            // Priority 1.5: Definition-side emit_var_type (struct/ptr refinements), upgrading to pointer or struct pointer based on RTL load/store base usage.
            if resolved_type.is_none()
                || matches!(
                    resolved_type,
                    Some(
                        XType::Xint
                            | XType::Xintunsigned
                            | XType::Xlong
                            | XType::Xlongunsigned
                            | XType::Xany32
                            | XType::Xany64
                            | XType::Xptr
                    )
                )
            {
                if let Some(reg) = pos_reg(i) {
                    if let Some(xtypes) = emit_var_types.get(&reg) {
                        // Pick the most specific type from candidates (prefer struct ptr > ptr > specific int > generic int)
                        let best = xtypes.iter().max_by_key(|t| match t {
                            XType::XstructPtr(_) => 5,
                            XType::Xcharptr
                            | XType::Xcharptrptr
                            | XType::Xintptr
                            | XType::Xfloatptr
                            | XType::Xsingleptr
                            | XType::Xfuncptr => 4,
                            XType::Xptr => 3,
                            XType::Xint8signed
                            | XType::Xint8unsigned
                            | XType::Xint16signed
                            | XType::Xint16unsigned => 2,
                            XType::Xfloat | XType::Xsingle => 2,
                            _ => 1,
                        });
                        if let Some(best_type) = best {
                            resolved_type = Some(best_type.clone());
                        }
                    }
                    // Consult the value-flow-accurate param_is_ptr lift even when emit_var_type candidates exist, but only to raise a still-scalar type, never to downgrade recovered ptr/struct/float.
                    let is_scalar = matches!(
                        resolved_type,
                        None | Some(
                            XType::Xint
                                | XType::Xintunsigned
                                | XType::Xlong
                                | XType::Xlongunsigned
                                | XType::Xany32
                                | XType::Xany64
                        )
                    );
                    if is_scalar && param_is_ptr.contains(&reg) {
                        // Check if it's a struct pointer (multiple offsets)
                        if let Some(offsets) = param_struct_offsets.get(&reg) {
                            if offsets.len() > 1 {
                                // Multiple emit_var_is_struct_candidate facts may match; take min sid for determinism under parallel Ascent.
                                let struct_id = db
                                    .rel_iter::<(Address, RTLReg, usize)>(
                                        "emit_var_is_struct_candidate",
                                    )
                                    .filter(|&&(_, r, _)| r == reg)
                                    .map(|&(_, _, sid)| sid)
                                    .min();
                                if let Some(sid) = struct_id {
                                    resolved_type = Some(XType::XstructPtr(sid));
                                } else {
                                    resolved_type = Some(XType::Xintptr);
                                }
                            } else {
                                resolved_type = Some(XType::Xintptr);
                            }
                        } else {
                            resolved_type = Some(XType::Xptr);
                        }
                    }
                }
            }

            // Priority 1.6: refine float WIDTH from the value web (Xsingle present, Xfloat absent means 32-bit), since rtl's fallback hardcodes Xfloat for a register-resident single-precision param.
            if matches!(resolved_type, Some(XType::Xfloat)) {
                if let Some(reg) = pos_reg(i) {
                    if let Some(xtypes) = emit_var_types.get(&reg) {
                        let has_single = xtypes.contains(&XType::Xsingle);
                        let has_double = xtypes.contains(&XType::Xfloat);
                        if has_single && !has_double {
                            resolved_type = Some(XType::Xsingle);
                        }
                    }
                }
            }

            // Priority 2: Call-site majority vote, upgrading generic int placeholders only.
            if resolved_type.is_none()
                || matches!(
                    resolved_type,
                    Some(
                        XType::Xint
                            | XType::Xintunsigned
                            | XType::Xlong
                            | XType::Xlongunsigned
                            | XType::Xany32
                            | XType::Xany64
                    )
                )
            {
                if let Some(pos_types) = call_site_arg_types.get(&func_addr) {
                    if let Some(caller_types) = pos_types.get(&i) {
                        if !caller_types.is_empty() {
                            let mut type_counts: HashMap<&XType, usize> = HashMap::new();
                            for t in caller_types {
                                *type_counts.entry(t).or_insert(0) += 1;
                            }
                            let should_override = match resolved_type.as_ref() {
                                None => true,
                                Some(current) => matches!(
                                    current,
                                    XType::Xint
                                        | XType::Xintunsigned
                                        | XType::Xlong
                                        | XType::Xlongunsigned
                                        | XType::Xany32
                                        | XType::Xany64
                                ),
                            };
                            if let Some((&best_type, &best_count)) =
                                type_counts.iter().max_by_key(|(ty, count)| (**count, **ty))
                            {
                                if best_count * 2 > caller_types.len() {
                                    if should_override
                                        && call_site_type_compatible_with_definition(
                                            resolved_type.as_ref(),
                                            best_type,
                                        )
                                    {
                                        resolved_type = Some(best_type.clone());
                                    }
                                }
                            }
                            if should_override
                                && matches!(
                                    resolved_type,
                                    None | Some(
                                        XType::Xint
                                            | XType::Xintunsigned
                                            | XType::Xlong
                                            | XType::Xlongunsigned
                                            | XType::Xany32
                                            | XType::Xany64
                                    )
                                )
                            {
                                if let Some(best_ptr) = caller_types.iter().max_by_key(|t| {
                                    (
                                        match t {
                                            XType::XstructPtr(_) => 6,
                                            XType::Xcharptr => 5,
                                            XType::Xcharptrptr
                                            | XType::Xintptr
                                            | XType::Xfloatptr
                                            | XType::Xsingleptr
                                            | XType::Xfuncptr => 4,
                                            XType::Xptr => 3,
                                            _ => 0,
                                        },
                                        **t,
                                    )
                                }) {
                                    if matches!(
                                        best_ptr,
                                        XType::XstructPtr(_)
                                            | XType::Xcharptr
                                            | XType::Xcharptrptr
                                            | XType::Xintptr
                                            | XType::Xfloatptr
                                            | XType::Xsingleptr
                                            | XType::Xfuncptr
                                            | XType::Xptr
                                    ) {
                                        // Frequency-gate the pointer upgrade like the int vote: require a pointer-class majority across caller sites, counting every pointer class so a majority spread across Xptr+Xcharptr still upgrades.
                                        let ptr_count = caller_types
                                            .iter()
                                            .filter(|t| {
                                                matches!(
                                                    t,
                                                    XType::XstructPtr(_)
                                                        | XType::Xcharptr
                                                        | XType::Xcharptrptr
                                                        | XType::Xintptr
                                                        | XType::Xfloatptr
                                                        | XType::Xsingleptr
                                                        | XType::Xfuncptr
                                                        | XType::Xptr
                                                )
                                            })
                                            .count();
                                        if ptr_count * 2 > caller_types.len() {
                                            resolved_type = Some(best_ptr.clone());
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // Default to the machine-word floor at the TARGET's width, not Xint (which would lie about ptrs/longs).
            param_types.push(resolved_type.unwrap_or(word_any));
        }

        // No name-based 'this' upgrade: an _ZN prefix also covers namespaced free functions and static members; a genuine 'this' is already recovered structurally at Priority 1.5 via param_is_ptr.

        let def_ret_type = def_return_types.get(&func_addr);

        // reconciled_return_type: Ascent-derived. Absent row defaults to Xvoid.
        let return_type = reconciled_return_type_map
            .get(&func_addr)
            .cloned()
            .unwrap_or(XType::Xvoid);

        let count_changed = reconciled_count != def_count;
        let current_param_types: Vec<XType> = (0..reconciled_count)
            .map(|i| {
                existing_params
                    .and_then(|params| params.get(i))
                    .and_then(|reg| existing_types.and_then(|types| types.get(reg)))
                    .cloned()
                    .unwrap_or(word_any)
            })
            .collect();
        let param_types_changed = current_param_types != param_types;
        let ret_type_changed = match def_ret_type {
            Some(dt) => *dt != return_type,
            None => return_type != XType::Xvoid,
        };
        let void_override = return_type == XType::Xvoid
            && (def_has_return.contains(&func_addr) || def_return_types.contains_key(&func_addr));
        let signature_stale = !signature_candidates_match_reconciled(
            def_signature_candidates
                .get(&func_addr)
                .map(Vec::as_slice)
                .unwrap_or(&[]),
            &param_types,
            return_type,
        );

        if count_changed
            || param_types_changed
            || ret_type_changed
            || void_override
            || signature_stale
        {
            prototypes.push(FunctionPrototype {
                address: func_addr,
                param_count: reconciled_count,
                param_types,
                return_type,
                confidence,
                is_varargs: is_va,
            });
        }
    }

    if prototypes.is_empty() {
        return;
    }

    log::info!(
        "SignatureReconciliation: patching {} function prototypes",
        prototypes.len()
    );

    patch_db(db, &prototypes);
}

fn patch_db(db: &mut DecompileDB, prototypes: &[FunctionPrototype]) {
    let target_abi = db.abi().clone();
    let first_stack_position = target_abi.first_stack_arg_position();
    // Where register slots belong to individual functions (Windows x86-32), a function's own convention evidence decides how many leading positions are registers; every other target keeps the image-wide count.
    let func_abi = per_function_abi(db);
    let reg_arg_limit = |address: Address| -> usize {
        if target_abi.reg_args_are_per_function() {
            func_abi.get(&address).map_or(0, |abi| abi.reg_arg_count)
        } else {
            first_stack_position
        }
    };
    let register_for_position = |limit: usize, position: usize, xtype: &XType| -> Option<Mreg> {
        if position >= limit {
            return None;
        }
        if target_abi.uses_shared_arg_slots() && matches!(xtype, XType::Xfloat | XType::Xsingle) {
            target_abi.float_arg_regs.get(position).copied()
        } else {
            target_abi.int_arg_regs.get(position).copied()
        }
    };
    let proto_map: HashMap<Address, &FunctionPrototype> =
        prototypes.iter().map(|p| (p.address, p)).collect();

    let call_targets: HashMap<Node, Address> = db
        .rel_iter::<(Node, Address)>("call_target_func")
        .map(|&(call_node, target)| (call_node, target))
        .collect();

    let rtl_to_mreg: HashMap<(Address, RTLReg), Mreg> = db
        .rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl")
        .map(|&(node, ref mreg, rtl_reg)| ((node, rtl_reg), *mreg))
        .collect();

    {
        let mut existing_params: HashMap<Address, Vec<RTLReg>> = HashMap::new();
        for &(addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param_candidate") {
            let params = existing_params.entry(addr).or_default();
            if !params.contains(&reg) {
                params.push(reg);
            }
        }
        for (addr, params) in existing_params.iter_mut() {
            params.sort_by(|a, b| {
                let ka = rtl_to_mreg
                    .get(&(*addr, *a))
                    .map(|m| param_mreg_sort_key(*m, &target_abi))
                    .unwrap_or(usize::MAX);
                let kb = rtl_to_mreg
                    .get(&(*addr, *b))
                    .map(|m| param_mreg_sort_key(*m, &target_abi))
                    .unwrap_or(usize::MAX);
                ka.cmp(&kb).then_with(|| a.cmp(b))
            });
        }

        let mut new_params: Vec<(Address, RTLReg)> = Vec::new();

        for &(addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param_candidate") {
            if !proto_map.contains_key(&addr) {
                new_params.push((addr, reg));
            }
        }

        for proto in prototypes {
            let existing = existing_params
                .get(&proto.address)
                .cloned()
                .unwrap_or_default();
            let current_count = existing.len();

            for (i, &reg) in existing.iter().enumerate() {
                if i < proto.param_count {
                    new_params.push((proto.address, reg));
                }
            }

            if proto.param_count > current_count {
                let limit = reg_arg_limit(proto.address);
                for i in current_count..proto.param_count {
                    let xtype = proto.param_types.get(i).cloned().unwrap_or(XType::Xany64);
                    let synthetic_reg = if let Some(mreg) = register_for_position(limit, i, &xtype)
                    {
                        fresh_xtl_reg(proto.address, mreg)
                    } else {
                        crate::decompile::passes::rtl_pass::fresh_stack_param_reg(
                            proto.address,
                            i - limit,
                        )
                    };
                    new_params.push((proto.address, synthetic_reg));

                    db.rel_push(
                        "emit_function_param_type_candidate",
                        (proto.address, synthetic_reg, xtype),
                    );
                }
            }
        }

        db.rel_set(
            "emit_function_param",
            new_params.into_iter().collect::<ascent::boxcar::Vec<_>>(),
        );
    }

    {
        // Read from emit_function_param, just written by block 1, so synthetic regs added when growing param_count get types too; the candidate relation only had the pre-widening reg set.
        let mut effective_params: HashMap<Address, Vec<RTLReg>> = HashMap::new();
        for &(addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param") {
            let params = effective_params.entry(addr).or_default();
            if !params.contains(&reg) {
                params.push(reg);
            }
        }
        for (addr, params) in effective_params.iter_mut() {
            params.sort_by(|a, b| {
                let ka = rtl_to_mreg
                    .get(&(*addr, *a))
                    .map(|m| param_mreg_sort_key(*m, &target_abi))
                    .unwrap_or(usize::MAX);
                let kb = rtl_to_mreg
                    .get(&(*addr, *b))
                    .map(|m| param_mreg_sort_key(*m, &target_abi))
                    .unwrap_or(usize::MAX);
                ka.cmp(&kb).then_with(|| a.cmp(b))
            });
        }

        let mut new_param_types: Vec<(Address, RTLReg, XType)> = db
            .rel_iter::<(Address, RTLReg, XType)>("emit_function_param_type_candidate")
            .filter(|&&(addr, _, _)| !proto_map.contains_key(&addr))
            .cloned()
            .collect();

        for proto in prototypes {
            if let Some(params) = effective_params.get(&proto.address) {
                for (i, &reg) in params.iter().enumerate().take(proto.param_count) {
                    let xtype = proto.param_types.get(i).cloned().unwrap_or(XType::Xany64);
                    new_param_types.push((proto.address, reg, xtype));
                }
            }
        }

        db.rel_set(
            "emit_function_param_type",
            new_param_types
                .into_iter()
                .collect::<ascent::boxcar::Vec<_>>(),
        );
    }

    {
        let known_param_regs: HashSet<(Address, RTLReg)> = {
            let mut set = HashSet::new();
            let existing_params: HashMap<Address, Vec<RTLReg>> = {
                let mut m: HashMap<Address, Vec<RTLReg>> = HashMap::new();
                // Read from emit_function_param (just written) to include synthetic regs added when widening param_count beyond original evidence.
                for &(addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param") {
                    m.entry(addr).or_default().push(reg);
                }
                for (addr, params) in m.iter_mut() {
                    params.sort_by_key(|reg| {
                        rtl_to_mreg
                            .get(&(*addr, *reg))
                            .map(|mreg| param_mreg_sort_key(*mreg, &target_abi))
                            .unwrap_or(usize::MAX)
                    });
                    params.dedup();
                }
                m
            };
            for proto in prototypes {
                // Suppress struct/pointer overrides for prototypes whose param types come from a known signature (KnownExtern, e.g. printf; HighConfidence, e.g. main(int, char**)); otherwise downstream type-priority logic in clight_select treats var_is_struct as winning.
                if matches!(
                    proto.confidence,
                    SignatureConfidence::KnownExtern | SignatureConfidence::HighConfidence
                ) {
                    if let Some(params) = existing_params.get(&proto.address) {
                        for &reg in params.iter().take(proto.param_count) {
                            set.insert((proto.address, reg));
                        }
                    }
                }
            }
            set
        };
        if !known_param_regs.is_empty() {
            let known_addrs: HashSet<Address> = known_param_regs.iter().map(|(a, _)| *a).collect();

            let new_struct: Vec<(Address, RTLReg, usize)> = db
                .rel_iter::<(Address, RTLReg, usize)>("emit_var_is_struct_candidate")
                .filter(|&&(addr, reg, _)| !known_param_regs.contains(&(addr, reg)))
                .cloned()
                .collect();
            db.rel_set(
                "emit_var_is_struct",
                new_struct.into_iter().collect::<ascent::boxcar::Vec<_>>(),
            );

            let new_ptr: Vec<(Address, RTLReg)> = db
                .rel_iter::<(Address, RTLReg)>("emit_function_param_is_pointer_candidate")
                .filter(|&&(addr, reg)| !known_param_regs.contains(&(addr, reg)))
                .cloned()
                .collect();
            db.rel_set(
                "emit_function_param_is_pointer",
                new_ptr.into_iter().collect::<ascent::boxcar::Vec<_>>(),
            );

            let new_param_struct: Vec<(Address, usize, usize)> = db
                .rel_iter::<(Address, usize, usize)>("func_param_struct_type_candidate")
                .filter(|&&(addr, _, _)| !known_addrs.contains(&addr))
                .cloned()
                .collect();
            db.rel_set(
                "func_param_struct_type",
                new_param_struct
                    .into_iter()
                    .collect::<ascent::boxcar::Vec<_>>(),
            );
        }
    }

    {
        let mut count_map: HashMap<Address, usize> = HashMap::new();
        for &(addr, count) in db.rel_iter::<(Address, usize)>("emit_function_param_count_candidate")
        {
            if !proto_map.contains_key(&addr) {
                let entry = count_map.entry(addr).or_insert(0);
                *entry = (*entry).max(count);
            }
        }
        for proto in prototypes {
            count_map.insert(proto.address, proto.param_count);
        }
        let new_counts: Vec<(Address, usize)> = count_map.into_iter().collect();
        db.rel_set(
            "emit_function_param_count",
            new_counts.into_iter().collect::<ascent::boxcar::Vec<_>>(),
        );
    }

    {
        let mut new_sigs: Vec<(Address, Signature)> = db
            .rel_iter::<(Address, Signature)>("emit_function_signature_candidate")
            .filter(|&&(addr, _)| !proto_map.contains_key(&addr))
            .cloned()
            .collect();
        for proto in prototypes {
            let sig = Signature {
                sig_args: Arc::new(proto.param_types.clone()),
                sig_res: proto.return_type.clone(),
                sig_cc: CallConv::default(),
            };
            new_sigs.push((proto.address, sig));
        }
        db.rel_set(
            "emit_function_signature",
            new_sigs.into_iter().collect::<ascent::boxcar::Vec<_>>(),
        );
    }

    {
        let mut new_ret: Vec<(Address, XType)> = db
            .rel_iter::<(Address, XType)>("emit_function_return_type_xtype_candidate")
            .filter(|&&(addr, _)| !proto_map.contains_key(&addr))
            .cloned()
            .collect();
        for proto in prototypes {
            if proto.return_type != XType::Xvoid {
                new_ret.push((proto.address, proto.return_type.clone()));
            }
        }
        db.rel_set(
            "emit_function_return_type_xtype",
            new_ret.into_iter().collect::<ascent::boxcar::Vec<_>>(),
        );
    }

    {
        use crate::decompile::passes::csh_pass::clight_type_from_xtype;
        let mut new_ret_ct: Vec<(Address, crate::x86::types::ClightType)> = db
            .rel_iter::<(Address, ClightType)>("emit_function_return_type_candidate")
            .filter(|&&(addr, _)| !proto_map.contains_key(&addr))
            .cloned()
            .collect();
        for proto in prototypes {
            if proto.return_type != XType::Xvoid {
                new_ret_ct.push((proto.address, clight_type_from_xtype(&proto.return_type)));
            }
        }
        db.rel_set(
            "emit_function_return_type",
            new_ret_ct.into_iter().collect::<ascent::boxcar::Vec<_>>(),
        );
    }

    {
        let mut new_void: Vec<(Address,)> = db
            .rel_iter::<(Address,)>("emit_function_void_candidate")
            .filter(|&&(addr,)| !proto_map.contains_key(&addr))
            .cloned()
            .collect();
        for proto in prototypes {
            if proto.return_type == XType::Xvoid {
                new_void.push((proto.address,));
            }
        }
        db.rel_set(
            "emit_function_void",
            new_void.into_iter().collect::<ascent::boxcar::Vec<_>>(),
        );
    }

    // reg->rtl and def-at-use maps, shared by the (dead) call_args_collected reconciliation and the Icall/Itailcall argument-arity reconciliation in the rtl_inst patch below.
    let reg_rtl_map: HashMap<(Node, Mreg), RTLReg> = db
        .rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl")
        .map(|&(addr, ref mreg, rtl)| ((addr, *mreg), rtl))
        .collect();
    let mut reg_def_at_use: HashMap<(Mreg, Address), Address> = HashMap::new();
    for &(def_addr, ref mreg, use_addr) in db.rel_iter::<(Address, Mreg, Address)>("reg_def_used") {
        reg_def_at_use.insert((*mreg, use_addr), def_addr);
    }

    {
        let mut new_call_args: Vec<(Node, Arc<Vec<RTLReg>>)> = Vec::new();
        let mut patched_calls: std::collections::HashSet<Node> = std::collections::HashSet::new();

        for &(call_node, ref args) in db.rel_iter::<(Node, Args)>("call_args_collected_candidate") {
            let target = match call_targets.get(&call_node) {
                Some(&t) => t,
                None => {
                    new_call_args.push((call_node, args.clone()));
                    continue;
                }
            };

            let proto = match proto_map.get(&target) {
                Some(p) => p,
                None => {
                    new_call_args.push((call_node, args.clone()));
                    continue;
                }
            };

            if args.len() == proto.param_count {
                new_call_args.push((call_node, args.clone()));
                continue;
            }

            if args.len() > proto.param_count {
                // Truncate unconditionally: Signature/FuncDef/FuncDecl model only fixed-arity sigs.
                let trimmed: Vec<RTLReg> = args.iter().take(proto.param_count).cloned().collect();
                new_call_args.push((call_node, Arc::new(trimmed)));
                patched_calls.insert(call_node);
                continue;
            }

            let mut widened = args.as_ref().clone();
            let limit = reg_arg_limit(target);
            for i in args.len()..proto.param_count {
                let xtype = proto.param_types.get(i).unwrap_or(&XType::Xany64);
                let Some(mreg) = register_for_position(limit, i, xtype) else {
                    break;
                };

                if let Some(&rtl) = reg_rtl_map.get(&(call_node, mreg)) {
                    widened.push(rtl);
                    continue;
                }

                if let Some(&def_addr) = reg_def_at_use.get(&(mreg, call_node)) {
                    if let Some(&rtl) = reg_rtl_map.get(&(def_addr, mreg)) {
                        widened.push(rtl);
                        continue;
                    }
                }

                let synthetic = fresh_xtl_reg(call_node, mreg);
                widened.push(synthetic);
            }
            new_call_args.push((call_node, Arc::new(widened)));
            patched_calls.insert(call_node);
        }

        if !patched_calls.is_empty() {
            log::info!(
                "SignatureReconciliation: widened args at {} call sites",
                patched_calls.len()
            );
            db.rel_set(
                "call_args_collected",
                new_call_args
                    .into_iter()
                    .collect::<ascent::boxcar::Vec<_>>(),
            );
        }
    }

    // Patch rtl_inst Icall sigs to reconciled return/param types; otherwise
    // stale Xvoid guesses make clight drop the dst reg and DCE the call.  This
    // is also the first point where a variadic function's exact last-named
    // parameter is known, so bind RTL's argument-less `__builtin_next_arg`
    // marker here.
    {
        let mut new_insts: Vec<(Node, RTLInst)> = Vec::new();
        let mut patched_insts: usize = 0;
        let mut refined_call_result_types: HashSet<(RTLReg, XType)> = HashSet::new();

        // A real instruction can belong to more than one inferred function
        // when functions share a CFG tail.  Keep the exact recognition-side
        // owners instead of collapsing `instr_in_function` through unordered
        // HashMap iteration.  A marker is bindable only when every applicable
        // owner agrees on the same last-named value.
        let mut next_arg_functions: HashMap<Node, HashSet<Address>> = HashMap::new();
        for &(func, node, _) in db.rel_iter::<(Address, Node, Mreg)>("variadic_next_arg_site") {
            next_arg_functions.entry(node).or_default().insert(func);
        }
        let mut reconciled_params: HashMap<Address, Vec<RTLReg>> = HashMap::new();
        for &(addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param") {
            let params = reconciled_params.entry(addr).or_default();
            if !params.contains(&reg) {
                params.push(reg);
            }
        }
        for (addr, params) in reconciled_params.iter_mut() {
            params.sort_by(|a, b| {
                let ka = rtl_to_mreg
                    .get(&(*addr, *a))
                    .map(|m| param_mreg_sort_key(*m, &target_abi))
                    .unwrap_or(usize::MAX);
                let kb = rtl_to_mreg
                    .get(&(*addr, *b))
                    .map(|m| param_mreg_sort_key(*m, &target_abi))
                    .unwrap_or(usize::MAX);
                ka.cmp(&kb).then_with(|| a.cmp(b))
            });
        }

        // Reconcile a call's argument list to the callee's reconciled arity, since cminor builds Scall directly from Icall.args and clang checks it against the already-reconciled declaration.
        let reconcile_args =
            |call_node: Node, args: &Args, param_types: &[XType], reg_limit: usize| -> Args {
                let param_count = param_types.len();
                if args.len() == param_count {
                    return args.clone();
                }
                if args.len() > param_count {
                    // Only fixed-arity signatures are modeled; drop the extra collected args.
                    return Arc::new(args.iter().take(param_count).cloned().collect());
                }
                let mut widened = args.as_ref().clone();
                for i in args.len()..param_count {
                    if let Some(mreg) = register_for_position(reg_limit, i, &param_types[i]) {
                        if let Some(&rtl) = reg_rtl_map.get(&(call_node, mreg)) {
                            widened.push(rtl);
                            continue;
                        }
                        if let Some(&def_addr) = reg_def_at_use.get(&(mreg, call_node)) {
                            if let Some(&rtl) = reg_rtl_map.get(&(def_addr, mreg)) {
                                widened.push(rtl);
                                continue;
                            }
                        }
                        widened.push(fresh_xtl_reg(call_node, mreg));
                    } else {
                        // Stack-passed parameters, beyond whatever leading positions this callee takes in registers.
                        widened.push(crate::decompile::passes::rtl_pass::fresh_stack_param_reg(
                            call_node,
                            i - reg_limit,
                        ));
                    }
                }
                Arc::new(widened)
            };

        for &(node, ref inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
            match inst {
                RTLInst::Ibuiltin(name, args, _)
                    if name == "__builtin_next_arg" && args.is_empty() =>
                {
                    let mut binding_candidates: Vec<RTLReg> = Vec::new();
                    if let Some(functions) = next_arg_functions.get(&node) {
                        for func in functions {
                            let Some(proto) = proto_map.get(func).copied() else {
                                continue;
                            };
                            if !proto.is_varargs || proto.param_count == 0 {
                                continue;
                            }
                            if let Some(last_named) = reconciled_params
                                .get(func)
                                .and_then(|params| params.get(proto.param_count - 1))
                            {
                                binding_candidates.push(*last_named);
                            }
                        }
                    }
                    let unique_binding = unique_variadic_next_arg_binding(binding_candidates);
                    let bound = unique_binding
                        .and_then(|last_named| bind_variadic_next_arg_builtin(inst, last_named));
                    if let Some(bound) = bound {
                        new_insts.push((node, bound));
                        patched_insts += 1;
                    } else {
                        log::warn!(
                            "SignatureReconciliation: could not bind variadic next-arg marker at {node:#x}"
                        );
                        new_insts.push((node, inst.clone()));
                    }
                }
                RTLInst::Icall(sig_opt, callee, args, dst, succ) => {
                    let target = match callee {
                        either::Either::Right(either::Either::Left(addr)) => Some(*addr),
                        _ => None,
                    };
                    let proto = target.and_then(|t| proto_map.get(&t).copied());
                    if let Some(proto) = proto {
                        if let Some(dst_reg) = dst {
                            if !matches!(
                                proto.return_type,
                                XType::Xvoid | XType::Xany32 | XType::Xany64
                            ) {
                                refined_call_result_types.insert((*dst_reg, proto.return_type));
                            }
                        }
                        // Variadic callees keep their full (tail-bearing) arg list; only fixed-arity calls are reconciled to the prototype count.
                        let new_args = if proto.is_varargs {
                            args.clone()
                        } else {
                            reconcile_args(
                                node,
                                args,
                                &proto.param_types,
                                reg_arg_limit(proto.address),
                            )
                        };
                        // Type the variadic tail at its natural 64-bit width; an untyped tail slot defaults to int and truncates a pointer vararg.
                        let mut sig_args = proto.param_types.clone();
                        if proto.is_varargs {
                            while sig_args.len() < new_args.len() {
                                sig_args.push(XType::Xany64);
                            }
                        }
                        let new_sig = Signature {
                            sig_args: Arc::new(sig_args),
                            sig_res: proto.return_type,
                            sig_cc: sig_opt
                                .as_ref()
                                .map(|s| s.sig_cc.clone())
                                .unwrap_or_default(),
                        };
                        let sig_changed = sig_opt
                            .as_ref()
                            .map(|s| {
                                s.sig_res != new_sig.sig_res
                                    || s.sig_args.as_slice() != new_sig.sig_args.as_slice()
                            })
                            .unwrap_or(true);
                        let args_changed = new_args.as_slice() != args.as_slice();
                        if sig_changed || args_changed {
                            let new_inst = RTLInst::Icall(
                                Some(new_sig),
                                callee.clone(),
                                new_args,
                                *dst,
                                *succ,
                            );
                            new_insts.push((node, new_inst));
                            patched_insts += 1;
                            continue;
                        }
                    }
                    new_insts.push((node, inst.clone()));
                }
                RTLInst::Itailcall(sig_opt, callee, args) => {
                    let target = match callee {
                        either::Either::Right(either::Either::Left(addr)) => Some(*addr),
                        _ => None,
                    };
                    let proto = target.and_then(|t| proto_map.get(&t).copied());
                    if let Some(proto) = proto {
                        // Variadic callees keep their full (tail-bearing) arg list; only fixed-arity calls are reconciled to the prototype count.
                        let new_args = if proto.is_varargs {
                            args.clone()
                        } else {
                            reconcile_args(
                                node,
                                args,
                                &proto.param_types,
                                reg_arg_limit(proto.address),
                            )
                        };
                        // Type the variadic tail at its natural 64-bit width; an untyped tail slot defaults to int and truncates a pointer vararg.
                        let mut sig_args = proto.param_types.clone();
                        if proto.is_varargs {
                            while sig_args.len() < new_args.len() {
                                sig_args.push(XType::Xany64);
                            }
                        }
                        let new_sig = Signature {
                            sig_args: Arc::new(sig_args),
                            sig_res: proto.return_type,
                            sig_cc: sig_opt
                                .as_ref()
                                .map(|s| s.sig_cc.clone())
                                .unwrap_or_default(),
                        };
                        let sig_changed = sig_opt
                            .as_ref()
                            .map(|s| {
                                s.sig_res != new_sig.sig_res
                                    || s.sig_args.as_slice() != new_sig.sig_args.as_slice()
                            })
                            .unwrap_or(true);
                        let args_changed = new_args.as_slice() != args.as_slice();
                        if sig_changed || args_changed {
                            let new_inst =
                                RTLInst::Itailcall(Some(new_sig), callee.clone(), new_args);
                            new_insts.push((node, new_inst));
                            patched_insts += 1;
                            continue;
                        }
                    }
                    new_insts.push((node, inst.clone()));
                }
                _ => {
                    new_insts.push((node, inst.clone()));
                }
            }
        }
        if patched_insts > 0 {
            log::info!(
                "SignatureReconciliation: patched {} call signatures/builtin bindings in rtl_inst",
                patched_insts
            );
            db.rel_set(
                "rtl_inst",
                new_insts.into_iter().collect::<ascent::boxcar::Vec<_>>(),
            );
        }
        if !refined_call_result_types.is_empty() {
            let mut all_types: HashSet<(RTLReg, XType)> = db
                .rel_iter::<(RTLReg, XType)>("emit_var_type_candidate")
                .copied()
                .collect();
            all_types.extend(refined_call_result_types);
            db.rel_set(
                "emit_var_type_candidate",
                all_types.into_iter().collect::<ascent::boxcar::Vec<_>>(),
            );
        }
    }
}
