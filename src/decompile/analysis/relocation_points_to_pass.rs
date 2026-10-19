use crate::declare_io_from;
use crate::decompile::analysis::global_array_pass::{count_items, max_i64, min_i64};
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::decompile::passes::rtl_optimize_pass::inst_def_use;
use crate::mreg::Mreg;
use crate::run_pass;
use crate::util::DEFAULT_VAR;
use crate::x86::op::{Addressing, Operation};
use crate::x86::types::*;
use ascent::ascent_par;
use ascent::lattice::set::Set;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Bound::{Excluded, Included};
use std::sync::Arc;

/// Resolve a direct symbolic memory operand to its exact byte coordinate.
fn direct_global_slot(addressing: &Addressing) -> Option<Address> {
    let (ident, offset) = match addressing {
        Addressing::Aglobal(ident, offset) | Addressing::Abased(ident, offset) => (*ident, *offset),
        _ => return None,
    };
    Address::try_from(ident).ok()?.checked_add_signed(offset)
}

fn chunk_is_pointer_sized_integer(chunk: &MemoryChunk, pointer_bytes: i64) -> bool {
    matches!(
        (pointer_bytes, chunk),
        (4, MemoryChunk::MInt32 | MemoryChunk::MAny32)
            | (8, MemoryChunk::MInt64 | MemoryChunk::MAny64)
    )
}

fn known_chunk_byte_size(chunk: &MemoryChunk) -> Option<usize> {
    match chunk {
        MemoryChunk::MBool | MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned => Some(1),
        MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned => Some(2),
        MemoryChunk::MInt32 | MemoryChunk::MFloat32 | MemoryChunk::MAny32 => Some(4),
        MemoryChunk::MInt64 | MemoryChunk::MFloat64 | MemoryChunk::MAny64 => Some(8),
        MemoryChunk::Unknown => None,
    }
}

fn checked_access_end(offset: i64, width: usize) -> Option<i64> {
    offset.checked_add(i64::try_from(width).ok()?)
}

fn signed_ranges_may_overlap(a_start: i64, a_width: usize, b_start: i64, b_width: usize) -> bool {
    let Some(a_end) = checked_access_end(a_start, a_width) else {
        return true;
    };
    let Some(b_end) = checked_access_end(b_start, b_width) else {
        return true;
    };
    a_start < b_end && b_start < a_end
}

fn initialized_range_covers(
    range_start: Address,
    bytes: &Arc<Vec<u8>>,
    target: Address,
    extent: usize,
) -> bool {
    let Some(range_end) = range_start.checked_add(bytes.len() as u64) else {
        return false;
    };
    let Some(target_end) = target.checked_add(extent as u64) else {
        return false;
    };
    target >= range_start && target_end <= range_end
}

fn exact_array_count(max_end: i64, width: usize) -> Option<usize> {
    let max_end = usize::try_from(max_end).ok()?;
    if width == 0 || max_end % width != 0 {
        return None;
    }
    let count = max_end / width;
    (count >= 2).then_some(count)
}

fn rtl_inst_uses(inst: &RTLInst, value: RTLReg) -> bool {
    inst_def_use(inst).1.contains(&value)
}

/// Uses which cannot mutate through `value` and cannot derive an untracked
/// alias. Calls are deliberately excluded: their effects are summarized
/// separately, and an unproved summary becomes Unknown.
fn parameter_use_is_closed(inst: &RTLInst, value: RTLReg) -> bool {
    match inst {
        RTLInst::Iop(Operation::Omove, args, _) => args.len() == 1 && args[0] == value,
        RTLInst::Iload(_, _, _, _) => true,
        RTLInst::Istore(_, Addressing::Aindexed(_), args, src) => {
            args.len() == 1 && args[0] == value && *src != value
        }
        RTLInst::Icond(_, _, _, _) | RTLInst::Ijumptable(_, _) => true,
        // Returning the address creates an alias in the caller.  Until that
        // alias is transported back into caller stack provenance, treating
        // the parameter as preserved is unsound.
        RTLInst::Ireturn(returned) => *returned != value,
        _ => false,
    }
}

/// Caller-stack uses admit an ordinary call argument because the corresponding
/// callee effect is handled by the call transfer rules below. An indirect call
/// target or an argument omitted from the finalized Icall is rejected in
/// Datalog.
fn stack_use_is_locally_closed(inst: &RTLInst, value: RTLReg) -> bool {
    match inst {
        RTLInst::Icall(_, _, args, _, _) | RTLInst::Itailcall(_, _, args) => args.contains(&value),
        _ => parameter_use_is_closed(inst, value),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct ParamFieldState {
    position: usize,
    field: i64,
    target: Option<Address>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct StackFieldState {
    base: i64,
    field: i64,
    target: Option<Address>,
}

fn param_field_state(position: usize, field: i64, target: Option<Address>) -> Set<ParamFieldState> {
    Set::singleton(ParamFieldState {
        position,
        field,
        target,
    })
}

fn stack_field_state(base: i64, field: i64, target: Option<Address>) -> Set<StackFieldState> {
    Set::singleton(StackFieldState {
        base,
        field,
        target,
    })
}

// Exact relocation points-to analysis over the finalized RTL graph.
//
// Every value origin is a `Known | Unknown` set lattice. A recognized arm can
// therefore never become a MUST fact merely because an unrecognized arm was
// omitted. Callee effects are summarized at every reachable return, and both
// callee and caller memory states are point-keyed `(function, node)` lattices
// whose values contain the sparse field facts.
ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct RelocationPointsToPassProgram;

    relation abi_int_arg_position(Mreg, usize);
    relation abi_pointer_size(i64);
    relation arg_reg_param_live_at(Address, Address, Mreg);
    relation canonical_exact_stack_addr_ptr_result(Node, RTLReg);
    relation code_pointer_in_data(Address, Address);
    relation def_reaches_call(Address, Address, Mreg);
    relation exact_frame_stack_lea(Address, Node, i64);
    relation frame_stack_write_bytes(Address, Address, i64, usize);
    relation func_param_validated(Address, Mreg);
    relation function_symbol(Address, Symbol);
    relation function_has_ltl_body(Address);
    relation function_has_uncovered_block(Address);
    relation function_unknown_terminal(Address, Node);
    relation function_unresolved_control(Address, Node);
    relation instr_in_function(Node, Address);
    relation main_function(Address);
    relation pointer_in_data(Address, Address);
    relation reg_rtl(Node, Mreg, RTLReg);
    relation rtl_function_entry(Address, Node);
    relation rtl_inst(Node, RTLInst);
    relation rtl_succ(Node, Node);
    relation slot_escaped_canonical(Address, i64, RTLReg);
    relation unknown_reg_value_reaches_use(Address, Address, Mreg);
    relation unnormalized_frame_stack_write(Address, Address);
    relation xtl_canonical(RTLReg, RTLReg);
    relation rtl_value_canonical(RTLReg, RTLReg);
    relation must_be_ptr(RTLReg);

    // `xtl_canonical` describes values which participated in the physical
    // XTL/SSA alias graph.  Final RTL also contains private temporaries created
    // while expanding one machine event into several semantic operations
    // (wide SIMD lanes are one example).  Those values deliberately have no
    // physical-register alias edge, but they are still ordinary, distinct RTL
    // values.  Complete the canonical map at the finalized-RTL boundary: keep
    // the settled XTL representative when one exists, otherwise publish the
    // value's identity.  The negative fallback is stratified over the complete
    // XTL relation, so it can never add a competing identity to an aliased web.
    #[local] relation finalized_rtl_value(RTLReg);
    finalized_rtl_value(dst) <-- rtl_inst(_, ?RTLInst::Iop(_, _, dst));
    finalized_rtl_value(dst) <-- rtl_inst(_, ?RTLInst::Iload(_, _, _, dst));
    finalized_rtl_value(dst) <--
        rtl_inst(_, ?RTLInst::Icall(_, _, _, Some(dst), _));
    finalized_rtl_value(dst) <--
        rtl_inst(_, ?RTLInst::Ibuiltin(_, _, BuiltinArg::BA(dst)));
    finalized_rtl_value(*raw) <--
        rtl_inst(_, inst),
        let def_uses = inst_def_use(inst),
        for raw in def_uses.1.iter();

    rtl_value_canonical(raw, canonical) <--
        finalized_rtl_value(raw),
        xtl_canonical(raw, canonical);
    rtl_value_canonical(*raw, *raw) <--
        finalized_rtl_value(raw),
        !xtl_canonical(raw, _);

    #[local] relation closed_function(Address);
    closed_function(func) <--
        function_has_ltl_body(func),
        !function_has_uncovered_block(func),
        !function_unknown_terminal(func, _),
        !function_unresolved_control(func, _);

    #[local] relation relocation_cfg_edge(Node, Node);
    relocation_cfg_edge(src, dst) <-- rtl_succ(src, dst);

    #[local] lattice relocation_cfg_owners(Node, Set<Address>);
    relocation_cfg_owners(*entry, Set::singleton(*func)) <--
        rtl_function_entry(func, entry);
    relocation_cfg_owners(*dst, Set::singleton(*func)) <--
        relocation_cfg_owners(src, owners),
        for func in owners.0.iter(),
        relocation_cfg_edge(src, dst),
        instr_in_function(dst, func);

    // This is a function-ownership projection of the point-keyed lattice, not
    // a point-to-point reachability relation.  It keeps disconnected finalized
    // RTL islands out of every semantic seed and is also consumed by the later
    // access-shape pass.
    relation relocation_reachable_node(Address, Node);
    relocation_reachable_node(*func, *node) <--
        relocation_cfg_owners(node, owners),
        for func in owners.0.iter();

    #[local] relation function_has_reachable_tailcall(Address);
    function_has_reachable_tailcall(func) <--
        relocation_reachable_node(func, node),
        rtl_inst(node, ?RTLInst::Itailcall(_, _, _));

    #[local] relation closed_summary_function(Address);
    closed_summary_function(func) <--
        closed_function(func),
        !function_has_reachable_tailcall(func);

    // Normalize all finalized definitions and moves to settled RTL webs. The
    // move edge is indexed by its source; recursive rules never scan all Iops.
    #[local] relation final_def(Address, Node, RTLReg);
    final_def(*func, *node, *canonical) <--
        rtl_inst(node, ?RTLInst::Iop(_, _, dst)),
        relocation_reachable_node(func, node),
        rtl_value_canonical(dst, canonical);
    final_def(*func, *node, *canonical) <--
        rtl_inst(node, ?RTLInst::Iload(_, _, _, dst)),
        relocation_reachable_node(func, node),
        rtl_value_canonical(dst, canonical);
    final_def(*func, *node, *canonical) <--
        rtl_inst(node, ?RTLInst::Icall(_, _, _, Some(dst), _)),
        relocation_reachable_node(func, node),
        rtl_value_canonical(dst, canonical);
    final_def(*func, *node, *canonical) <--
        rtl_inst(node, ?RTLInst::Ibuiltin(_, _, BuiltinArg::BA(dst))),
        relocation_reachable_node(func, node),
        rtl_value_canonical(dst, canonical);

    #[local] relation final_move(Address, Node, RTLReg, RTLReg);
    final_move(*func, *node, *src_canonical, *dst_canonical) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Omove, args, dst)),
        if args.len() == 1,
        relocation_reachable_node(func, node),
        rtl_value_canonical(&args[0], src_canonical),
        rtl_value_canonical(dst, dst_canonical);

    #[local] relation final_move_def(Address, Node, RTLReg);
    final_move_def(func, node, dst) <-- final_move(func, node, _, dst);

    #[local] relation final_value_use(Address, Node, RTLReg);
    final_value_use(*func, *node, *canonical) <--
        rtl_inst(node, inst),
        relocation_reachable_node(func, node),
        let def_uses = inst_def_use(inst),
        for raw in def_uses.1.iter(),
        rtl_value_canonical(raw, canonical);

    #[local] relation relocation_slot_target(Address, Address);
    relocation_slot_target(slot, target) <-- pointer_in_data(slot, target);
    relocation_slot_target(slot, target) <-- code_pointer_in_data(slot, target);

    #[local] relation direct_relocation_def(Address, Node, RTLReg, Address);
    direct_relocation_def(*func, *node, *canonical, *target) <--
        rtl_inst(node, ?RTLInst::Iload(chunk, addressing, args, dst)),
        if args.is_empty(),
        if let Some(slot) = direct_global_slot(addressing),
        relocation_slot_target(slot, target),
        abi_pointer_size(pointer_bytes),
        if chunk_is_pointer_sized_integer(chunk, *pointer_bytes),
        relocation_reachable_node(func, node),
        rtl_value_canonical(dst, canonical);

    // RTL's physical reaching-definition analysis is the authority for
    // undefined/live-in/trimmed arms.  Mapping its observer through reg_rtl
    // binds that missing arm to the finalized canonical web.  A validated ABI
    // parameter which is structurally still live at this use is not missing:
    // the upstream observer intentionally reports all entry-live values and
    // cannot itself distinguish a parameter from an unresolved live-in.
    #[local] relation validated_param_live_at(Address, Node, Mreg);
    validated_param_live_at(func, node, mreg) <--
        func_param_validated(func, mreg),
        arg_reg_param_live_at(func, node, mreg);

    #[local] relation unknown_final_value(Address, Node, RTLReg);
    unknown_final_value(*func, *node, *canonical) <--
        unknown_reg_value_reaches_use(func, node, mreg),
        !validated_param_live_at(func, node, mreg),
        relocation_reachable_node(func, node),
        reg_rtl(node, mreg, canonical);

    // Base relocation values. Every non-move finalized definition which is not
    // a recognized relocation contributes Unknown to its canonical web.
    #[local] lattice direct_value_origins(Address, RTLReg, Set<Option<Address>>);
    direct_value_origins(*func, *value, Set::singleton(Some(*target))) <--
        direct_relocation_def(func, _, value, target);
    direct_value_origins(*func, *value, Set::singleton(None)) <--
        final_def(func, node, value),
        !final_move_def(func, node, value),
        !direct_relocation_def(func, node, value, _);
    direct_value_origins(func, value, Set::singleton(None)) <--
        unknown_final_value(func, _, value);
    direct_value_origins(*func, *dst, origins.clone()) <--
        direct_value_origins(func, src, origins),
        final_move(func, _, src, dst);

    #[local] relation direct_origin_member(Address, RTLReg, Option<Address>);
    direct_origin_member(*func, *value, *origin) <--
        direct_value_origins(func, value, origins),
        for origin in origins.0.iter();

    #[local] relation direct_origin_conflict(Address, RTLReg);
    direct_origin_conflict(func, value) <-- direct_origin_member(func, value, ?None);
    direct_origin_conflict(func, value) <--
        direct_origin_member(func, value, ?Some(left)),
        direct_origin_member(func, value, ?Some(right)),
        if left != right;

    #[local] relation direct_exact_target(Address, RTLReg, Address);
    direct_exact_target(func, value, target) <--
        direct_origin_member(func, value, ?Some(target)),
        !direct_origin_conflict(func, value);

    // Consume the upstream exact stack-coordinate and canonical-pointer
    // authorities together. A final definition at that node is required, so a
    // dead candidate cannot survive RTL optimization into this proof.
    #[local] relation exact_stack_seed(Address, Node, RTLReg, i64);
    exact_stack_seed(*func, *node, *canonical, *offset) <--
        exact_frame_stack_lea(func, node, offset),
        canonical_exact_stack_addr_ptr_result(node, canonical),
        final_def(func, node, canonical);

    #[local] lattice stack_value_origins(Address, RTLReg, Set<Option<i64>>);
    stack_value_origins(*func, *value, Set::singleton(Some(*offset))) <--
        exact_stack_seed(func, _, value, offset);
    stack_value_origins(*func, *value, Set::singleton(None)) <--
        final_def(func, node, value),
        !final_move_def(func, node, value),
        !exact_stack_seed(func, node, value, _);
    stack_value_origins(func, value, Set::singleton(None)) <--
        unknown_final_value(func, _, value);
    stack_value_origins(*func, *dst, origins.clone()) <--
        stack_value_origins(func, src, origins),
        final_move(func, _, src, dst);

    #[local] relation stack_origin_member(Address, RTLReg, Option<i64>);
    stack_origin_member(*func, *value, *origin) <--
        stack_value_origins(func, value, origins),
        for origin in origins.0.iter();
    #[local] relation stack_may_carrier(Address, RTLReg, i64);
    stack_may_carrier(func, value, offset) <--
        stack_origin_member(func, value, ?Some(offset));
    #[local] relation stack_origin_conflict(Address, RTLReg);
    stack_origin_conflict(func, value) <-- stack_origin_member(func, value, ?None);
    stack_origin_conflict(func, value) <--
        stack_origin_member(func, value, ?Some(left)),
        stack_origin_member(func, value, ?Some(right)),
        if left != right;
    #[local] relation exact_stack_address_value(Address, RTLReg, i64);
    exact_stack_address_value(func, value, offset) <--
        stack_origin_member(func, value, ?Some(offset)),
        !stack_origin_conflict(func, value);

    // Parameter origins likewise carry Unknown for every competing finalized
    // definition. `may` is used only to find possible side effects; `exact` is
    // required for loads/stores which publish a precise summary.
    #[local] relation function_param_position(Address, usize);
    function_param_position(func, position) <--
        func_param_validated(func, mreg),
        abi_int_arg_position(mreg, position);

    #[local] lattice param_value_origins(Address, RTLReg, Set<Option<usize>>);
    param_value_origins(*func, *canonical, Set::singleton(Some(*position))) <--
        func_param_validated(func, mreg),
        abi_int_arg_position(mreg, position),
        reg_rtl(func, mreg, raw),
        rtl_value_canonical(raw, canonical);
    param_value_origins(*func, *value, Set::singleton(None)) <--
        final_def(func, node, value),
        !final_move_def(func, node, value);
    param_value_origins(func, value, Set::singleton(None)) <--
        unknown_final_value(func, _, value);
    param_value_origins(*func, *dst, origins.clone()) <--
        param_value_origins(func, src, origins),
        final_move(func, _, src, dst);

    #[local] relation param_origin_member(Address, RTLReg, Option<usize>);
    param_origin_member(*func, *value, *origin) <--
        param_value_origins(func, value, origins),
        for origin in origins.0.iter();
    #[local] relation param_origin_conflict(Address, RTLReg);
    param_origin_conflict(func, value) <-- param_origin_member(func, value, ?None);
    param_origin_conflict(func, value) <--
        param_origin_member(func, value, ?Some(left)),
        param_origin_member(func, value, ?Some(right)),
        if left != right;
    #[local] relation param_may_carrier(Address, usize, RTLReg);
    param_may_carrier(func, position, value) <--
        param_origin_member(func, value, ?Some(position));
    #[local] relation param_exact_carrier(Address, usize, RTLReg);
    param_exact_carrier(func, position, value) <--
        param_origin_member(func, value, ?Some(position)),
        !param_origin_conflict(func, value);

    #[local] relation param_unclosed_use(Address, usize, Node);
    param_unclosed_use(*func, *position, *node) <--
        param_may_carrier(func, position, value),
        final_value_use(func, node, value),
        rtl_inst(node, inst),
        if !parameter_use_is_closed(inst, *value);
    // The final Icall can omit a physically reaching ABI value after an
    // incomplete arity inference.  Such an observation is an escape/effect,
    // even though the selected argument vector no longer mentions it.
    param_unclosed_use(*func, *position, *call) <--
        param_may_carrier(func, position, value),
        final_call_node(func, call),
        def_reaches_call(call, def, mreg),
        reg_rtl(def, mreg, value);

    #[local] relation param_direct_store(Address, usize, Node, i64, MemoryChunk, RTLReg);
    param_direct_store(*func, *position, *store, *offset, *chunk, *src_canonical) <--
        rtl_inst(store, ?RTLInst::Istore(chunk, Addressing::Aindexed(offset), args, src)),
        if args.len() == 1,
        relocation_reachable_node(func, store),
        rtl_value_canonical(&args[0], base_canonical),
        param_may_carrier(func, position, base_canonical),
        rtl_value_canonical(src, src_canonical);

    #[local] relation param_store_exact_target(Address, usize, Node, i64, Address);
    param_store_exact_target(*func, *position, *store, *offset, *target) <--
        rtl_inst(store, ?RTLInst::Istore(chunk, Addressing::Aindexed(offset), args, src)),
        if args.len() == 1 && *offset >= 0,
        relocation_reachable_node(func, store),
        rtl_value_canonical(&args[0], base_canonical),
        param_exact_carrier(func, position, base_canonical),
        rtl_value_canonical(src, src_canonical),
        abi_pointer_size(pointer_bytes),
        if chunk_is_pointer_sized_integer(chunk, *pointer_bytes),
        direct_exact_target(func, src_canonical, target);

    #[local] relation callee_field_candidate(Address, usize, i64);
    callee_field_candidate(func, position, field) <--
        param_store_exact_target(func, position, _, field, _);

    #[local] relation param_memory_effect(Address, usize);
    param_memory_effect(func, position) <-- param_direct_store(func, position, _, _, _, _);
    param_memory_effect(func, position) <-- param_unclosed_use(func, position, _);

    #[local] relation callee_param_preserves(Address, usize);
    callee_param_preserves(func, position) <--
        closed_summary_function(func),
        function_param_position(func, position),
        !param_memory_effect(func, position);

    #[local] relation param_field_write_target(Address, Node, usize, i64, Address);
    param_field_write_target(func, store, position, field, target) <--
        param_store_exact_target(func, position, store, field, target);

    #[local] relation param_field_write_unknown(Address, Node, usize, i64);
    param_field_write_unknown(*func, *store, *position, *field) <--
        callee_field_candidate(func, position, field),
        param_direct_store(func, position, store, store_offset, chunk, _),
        if let Some(store_width) = known_chunk_byte_size(chunk),
        abi_pointer_size(pointer_bytes),
        if let Ok(field_width) = usize::try_from(*pointer_bytes),
        if signed_ranges_may_overlap(*store_offset, store_width, *field, field_width),
        !param_store_exact_target(func, position, store, field, _);
    param_field_write_unknown(*func, *store, *position, *field) <--
        callee_field_candidate(func, position, field),
        param_direct_store(func, position, store, _, chunk, _),
        if known_chunk_byte_size(chunk).is_none();
    param_field_write_unknown(*func, *node, *position, *field) <--
        callee_field_candidate(func, position, field),
        param_unclosed_use(func, position, node),
        !param_field_write_target(func, node, position, field, _);

    #[local] relation param_field_write(Address, Node, usize, i64);
    param_field_write(func, node, position, field) <--
        param_field_write_target(func, node, position, field, _);
    param_field_write(func, node, position, field) <--
        param_field_write_unknown(func, node, position, field);

    // All callee field facts live inside one set-valued lattice per CFG point.
    #[local] lattice callee_field_states(Address, Node, Set<ParamFieldState>);
    callee_field_states(*func, *entry, param_field_state(*position, *field, None)) <--
        callee_field_candidate(func, position, field),
        rtl_function_entry(func, entry),
        !param_field_write(func, entry, position, field);
    callee_field_states(*func, *node, param_field_state(*position, *field, Some(*target))) <--
        param_field_write_target(func, node, position, field, target),
        relocation_cfg_owners(node, owners),
        if owners.0.contains(func);
    callee_field_states(*func, *node, param_field_state(*position, *field, None)) <--
        param_field_write_unknown(func, node, position, field),
        relocation_cfg_owners(node, owners),
        if owners.0.contains(func);
    callee_field_states(*func, *dst, Set::singleton(*fact)) <--
        callee_field_states(func, src, states),
        for fact in states.0.iter(),
        let position = fact.position,
        let field = fact.field,
        relocation_cfg_edge(src, dst),
        relocation_reachable_node(func, dst),
        !param_field_write(func, dst, &position, &field);

    #[local] relation reachable_return_node(Address, Node);
    reachable_return_node(*func, *node) <--
        rtl_inst(node, ?RTLInst::Ireturn(_)),
        relocation_reachable_node(func, node);
    #[local] relation reachable_return_count(Address, usize);
    reachable_return_count(func, count) <--
        reachable_return_node(func, _),
        agg count = count_items(node) in reachable_return_node(func, node);

    #[local] relation callee_return_field_state(Address, Node, usize, i64, Option<Address>);
    callee_return_field_state(*func, *node, position, field, fact.target) <--
        reachable_return_node(func, node),
        callee_field_states(func, node, states),
        for fact in states.0.iter(),
        let position = fact.position,
        let field = fact.field;
    #[local] relation callee_return_target(Address, Node, usize, i64, Address);
    callee_return_target(func, node, position, field, target) <--
        callee_return_field_state(func, node, position, field, ?Some(target));
    #[local] relation callee_return_target_count(Address, usize, i64, Address, usize);
    callee_return_target_count(func, position, field, target, count) <--
        callee_return_target(func, _, position, field, target),
        agg count = count_items(node) in callee_return_target(func, node, position, field, target);
    #[local] relation callee_return_target_disagrees(Address, usize, i64, Address);
    callee_return_target_disagrees(func, position, field, *target) <--
        callee_return_target(func, _, position, field, target),
        callee_return_field_state(func, _, position, field, observed),
        if *observed != Some(*target);

    #[local] relation callee_field_write_summary(Address, usize, i64, Address);
    callee_field_write_summary(func, position, field, target) <--
        closed_summary_function(func),
        reachable_return_count(func, return_count),
        callee_return_target_count(func, position, field, target, target_count),
        !param_unclosed_use(func, position, _),
        if return_count == target_count,
        !callee_return_target_disagrees(func, position, field, target);

    // Reader summary: a returned value has a parameter-field origin only when
    // every competing definition is represented and every real return agrees.
    #[local] relation param_field_load_def(Address, Node, RTLReg, usize, i64);
    param_field_load_def(*func, *load, *dst_canonical, *position, *offset) <--
        rtl_inst(load, ?RTLInst::Iload(chunk, Addressing::Aindexed(offset), args, dst)),
        if args.len() == 1 && *offset >= 0,
        relocation_reachable_node(func, load),
        rtl_value_canonical(&args[0], base_canonical),
        param_exact_carrier(func, position, base_canonical),
        abi_pointer_size(pointer_bytes),
        if chunk_is_pointer_sized_integer(chunk, *pointer_bytes),
        rtl_value_canonical(dst, dst_canonical);

    #[local] lattice field_value_origins(Address, RTLReg, Set<Option<(usize, i64)>>);
    field_value_origins(*func, *value, Set::singleton(Some((*position, *field)))) <--
        param_field_load_def(func, _, value, position, field);
    field_value_origins(*func, *value, Set::singleton(None)) <--
        final_def(func, node, value),
        !final_move_def(func, node, value),
        !param_field_load_def(func, node, value, _, _);
    field_value_origins(func, value, Set::singleton(None)) <--
        unknown_final_value(func, _, value);
    field_value_origins(*func, *dst, origins.clone()) <--
        field_value_origins(func, src, origins),
        final_move(func, _, src, dst);

    #[local] relation field_origin_member(Address, RTLReg, Option<(usize, i64)>);
    field_origin_member(*func, *value, *origin) <--
        field_value_origins(func, value, origins),
        for origin in origins.0.iter();
    #[local] relation field_origin_conflict(Address, RTLReg);
    field_origin_conflict(func, value) <-- field_origin_member(func, value, ?None);
    field_origin_conflict(func, value) <--
        field_origin_member(func, value, ?Some(left)),
        field_origin_member(func, value, ?Some(right)),
        if left != right;
    #[local] relation exact_field_value(Address, RTLReg, usize, i64);
    exact_field_value(func, value, position, field) <--
        field_origin_member(func, value, ?Some((position, field))),
        !field_origin_conflict(func, value);

    #[local] relation exact_return_field(Address, Node, usize, i64);
    exact_return_field(*func, *node, *position, *field) <--
        reachable_return_node(func, node),
        rtl_inst(node, ?RTLInst::Ireturn(raw)),
        rtl_value_canonical(raw, canonical),
        exact_field_value(func, canonical, position, field);
    #[local] relation exact_return_field_count(Address, usize, i64, usize);
    exact_return_field_count(func, position, field, count) <--
        exact_return_field(func, _, position, field),
        agg count = count_items(node) in exact_return_field(func, node, position, field);
    #[local] relation param_field_return(Address, usize, i64);
    param_field_return(func, position, field) <--
        closed_summary_function(func),
        callee_param_preserves(func, position),
        !param_unclosed_use(func, position, _),
        reachable_return_count(func, return_count),
        exact_return_field_count(func, position, field, field_count),
        if return_count == field_count;

    // Final call sites only.  The selected RTL instruction is authoritative for
    // both target and positional arguments; optimizer-retained mapping rows are
    // deliberately ignored.
    #[local] relation final_call_node(Address, Node);
    final_call_node(*caller, *call) <--
        rtl_inst(call, ?RTLInst::Icall(_, _, _, _, _)),
        relocation_reachable_node(caller, call);
    #[local] relation final_internal_call(Address, Node, Address);
    final_internal_call(*caller, *call, *callee) <--
        rtl_inst(call, ?RTLInst::Icall(_, either::Either::Right(either::Either::Left(callee)), _, _, _)),
        relocation_reachable_node(caller, call);
    #[local] relation final_call_arg(Address, Node, usize, RTLReg);
    final_call_arg(*caller, *call, position, *canonical) <--
        rtl_inst(call, ?RTLInst::Icall(_, _, args, _, _)),
        relocation_reachable_node(caller, call),
        for (position, raw) in args.iter().enumerate(),
        if *raw != DEFAULT_VAR as RTLReg,
        rtl_value_canonical(raw, canonical);

    #[local] relation call_may_stack_arg(Node, usize, Address, i64);
    call_may_stack_arg(*call, *position, *caller, *base_offset) <--
        final_call_arg(caller, call, position, argument),
        stack_may_carrier(caller, argument, base_offset),
        slot_escaped_canonical(caller, base_offset, _);

    #[local] relation call_stack_arg(Node, usize, Address, i64);
    call_stack_arg(*call, *position, *caller, *base_offset) <--
        final_call_arg(caller, call, position, argument),
        exact_stack_address_value(caller, argument, base_offset),
        slot_escaped_canonical(caller, base_offset, _);

    #[local] relation stack_field_reader(Address, Node, i64, i64);
    stack_field_reader(*caller, *call, *base_offset, *field_offset) <--
        call_stack_arg(call, position, caller, base_offset),
        final_internal_call(caller, call, callee),
        param_field_return(callee, position, field_offset);

    #[local] relation tracked_stack_field(Address, i64, i64);
    tracked_stack_field(caller, base_offset, field_offset) <--
        stack_field_reader(caller, _, base_offset, field_offset);

    #[local] relation stack_field_write_target(Address, Node, i64, i64, Address);
    stack_field_write_target(*caller, *call, *base_offset, *field_offset, *target) <--
        tracked_stack_field(caller, base_offset, field_offset),
        call_stack_arg(call, position, caller, base_offset),
        final_internal_call(caller, call, callee),
        callee_field_write_summary(callee, position, field_offset, target);

    #[local] relation stack_field_write_unknown(Address, Node, i64, i64);
    stack_field_write_unknown(*caller, *call, *base_offset, *field_offset) <--
        tracked_stack_field(caller, base_offset, field_offset),
        call_stack_arg(call, position, caller, base_offset),
        final_internal_call(caller, call, callee),
        !callee_field_write_summary(callee, position, field_offset, _),
        !callee_param_preserves(callee, position);
    // A conflicted carrier may name this stack object on one arm, but cannot
    // perform a strong update for it.
    stack_field_write_unknown(*caller, *call, *base_offset, *field_offset) <--
        tracked_stack_field(caller, base_offset, field_offset),
        call_may_stack_arg(call, position, caller, base_offset),
        !call_stack_arg(call, position, caller, base_offset);
    stack_field_write_unknown(*caller, *call, *base_offset, *field_offset) <--
        tracked_stack_field(caller, base_offset, field_offset),
        call_may_stack_arg(call, _, caller, base_offset),
        final_call_node(caller, call),
        !final_internal_call(caller, call, _);

    // Direct caller stores and unclosed address uses have the same strong
    // update semantics as callee effects.
    #[local] relation local_may_store(Address, Node, i64, i64, MemoryChunk, RTLReg);
    local_may_store(*caller, *store, *base, *offset, *chunk, *src_canonical) <--
        rtl_inst(store, ?RTLInst::Istore(chunk, Addressing::Aindexed(offset), args, src)),
        if args.len() == 1,
        relocation_reachable_node(caller, store),
        rtl_value_canonical(&args[0], base_canonical),
        stack_may_carrier(caller, base_canonical, base),
        rtl_value_canonical(src, src_canonical);

    #[local] relation local_direct_store(Address, Node, i64, i64, MemoryChunk, RTLReg);
    local_direct_store(*caller, *store, *base, *offset, *chunk, *src_canonical) <--
        rtl_inst(store, ?RTLInst::Istore(chunk, Addressing::Aindexed(offset), args, src)),
        if args.len() == 1,
        relocation_reachable_node(caller, store),
        rtl_value_canonical(&args[0], base_canonical),
        exact_stack_address_value(caller, base_canonical, base),
        rtl_value_canonical(src, src_canonical);

    stack_field_write_target(*caller, *store, *base, *field, *target) <--
        tracked_stack_field(caller, base, field),
        local_direct_store(caller, store, base, field, chunk, src),
        abi_pointer_size(pointer_bytes),
        if chunk_is_pointer_sized_integer(chunk, *pointer_bytes),
        direct_exact_target(caller, src, target);
    stack_field_write_unknown(*caller, *store, *base, *field) <--
        tracked_stack_field(caller, base, field),
        local_may_store(caller, store, base, store_offset, chunk, _),
        if let Some(store_width) = known_chunk_byte_size(chunk),
        abi_pointer_size(pointer_bytes),
        if let Ok(field_width) = usize::try_from(*pointer_bytes),
        if signed_ranges_may_overlap(*store_offset, store_width, *field, field_width),
        !stack_field_write_target(caller, store, base, field, _);
    stack_field_write_unknown(*caller, *store, *base, *field) <--
        tracked_stack_field(caller, base, field),
        local_may_store(caller, store, base, _, chunk, _),
        if known_chunk_byte_size(chunk).is_none();

    // Decoder/frame-coordinate facts cover direct SP/FP stores which have no
    // stack-address RTL operand.  They may kill a tracked field; only the
    // value-explicit rule above is allowed to establish a Known target.
    stack_field_write_unknown(*caller, *write, *base, *field) <--
        tracked_stack_field(caller, base, field),
        frame_stack_write_bytes(caller, write, write_offset, write_width),
        relocation_reachable_node(caller, write),
        if let Some(field_offset) = base.checked_add(*field),
        abi_pointer_size(pointer_bytes),
        if let Ok(field_width) = usize::try_from(*pointer_bytes),
        if signed_ranges_may_overlap(*write_offset, *write_width, field_offset, field_width),
        !stack_field_write_target(caller, write, base, field, _);
    stack_field_write_unknown(*caller, *write, *base, *field) <--
        tracked_stack_field(caller, base, field),
        unnormalized_frame_stack_write(caller, write),
        relocation_reachable_node(caller, write),
        !stack_field_write_target(caller, write, base, field, _);

    #[local] relation local_unclosed_use(Address, Node, i64);
    local_unclosed_use(*caller, *node, *base) <--
        stack_may_carrier(caller, value, base),
        final_value_use(caller, node, value),
        rtl_inst(node, inst),
        if !stack_use_is_locally_closed(inst, *value);
    local_unclosed_use(*caller, *call, *base) <--
        stack_may_carrier(caller, value, base),
        final_call_node(caller, call),
        rtl_inst(call, inst),
        if rtl_inst_uses(inst, *value),
        !final_call_arg(caller, call, _, value);
    // A selected argument does not make a simultaneous indirect-target role
    // harmless: executing through the stack-derived value is an escape.
    local_unclosed_use(*caller, *call, *base) <--
        rtl_inst(call, ?RTLInst::Icall(_, either::Either::Left(raw_target), _, _, _)),
        relocation_reachable_node(caller, call),
        rtl_value_canonical(raw_target, target),
        stack_may_carrier(caller, target, base);
    // Structural ABI setup can be real even when arity trimming omitted the
    // value from the final argument vector.
    local_unclosed_use(*caller, *call, *base) <--
        final_call_node(caller, call),
        def_reaches_call(call, def, mreg),
        reg_rtl(def, mreg, value),
        stack_may_carrier(caller, value, base),
        !final_call_arg(caller, call, _, value);

    // Escapes persist beyond the instruction that creates them.  Until alias
    // return/global transport is represented, any such escape vetoes a later
    // MUST read even if an exact write follows it.
    #[local] relation caller_stack_escape(Address, i64);
    caller_stack_escape(caller, base) <-- local_unclosed_use(caller, _, base);
    caller_stack_escape(*caller, *base) <--
        call_may_stack_arg(call, position, caller, base),
        final_internal_call(caller, call, callee),
        param_unclosed_use(callee, position, _);
    caller_stack_escape(*caller, *base) <--
        call_may_stack_arg(call, _, caller, base),
        final_call_node(caller, call),
        !final_internal_call(caller, call, _);
    caller_stack_escape(*caller, *base) <--
        call_may_stack_arg(call, _, caller, base),
        final_internal_call(caller, call, callee),
        !closed_summary_function(callee);
    stack_field_write_unknown(*caller, *node, *base, *field) <--
        tracked_stack_field(caller, base, field),
        local_unclosed_use(caller, node, base),
        !stack_field_write_target(caller, node, base, field, _);

    #[local] relation stack_field_write(Address, Node, i64, i64);
    stack_field_write(caller, node, base, field) <--
        stack_field_write_target(caller, node, base, field, _);
    stack_field_write(caller, node, base, field) <--
        stack_field_write_unknown(caller, node, base, field);

    #[local] lattice caller_field_states(Address, Node, Set<StackFieldState>);
    caller_field_states(*caller, *entry, stack_field_state(*base, *field, None)) <--
        tracked_stack_field(caller, base, field),
        rtl_function_entry(caller, entry),
        !stack_field_write(caller, entry, base, field);
    caller_field_states(*caller, *node, stack_field_state(*base, *field, Some(*target))) <--
        stack_field_write_target(caller, node, base, field, target),
        relocation_cfg_owners(node, owners),
        if owners.0.contains(caller);
    caller_field_states(*caller, *node, stack_field_state(*base, *field, None)) <--
        stack_field_write_unknown(caller, node, base, field),
        relocation_cfg_owners(node, owners),
        if owners.0.contains(caller);
    caller_field_states(*caller, *dst, Set::singleton(*fact)) <--
        caller_field_states(caller, src, states),
        for fact in states.0.iter(),
        let base = fact.base,
        let field = fact.field,
        relocation_cfg_edge(src, dst),
        relocation_reachable_node(caller, dst),
        !stack_field_write(caller, dst, &base, &field);

    #[local] relation reader_state_member(Address, Node, i64, i64, Option<Address>);
    reader_state_member(*caller, *call, *base, *field, fact.target) <--
        stack_field_reader(caller, call, base, field),
        caller_field_states(caller, call, states),
        for fact in states.0.iter(),
        if fact.base == *base && fact.field == *field;
    #[local] relation reader_state_conflict(Address, Node, i64, i64);
    reader_state_conflict(caller, call, base, field) <--
        reader_state_member(caller, call, base, field, ?None);
    reader_state_conflict(caller, call, base, field) <--
        reader_state_member(caller, call, base, field, ?Some(left)),
        reader_state_member(caller, call, base, field, ?Some(right)),
        if left != right;
    #[local] relation exact_call_result_target(Address, Node, Address);
    exact_call_result_target(caller, call, target) <--
        reader_state_member(caller, call, base, field, ?Some(target)),
        closed_summary_function(caller),
        !caller_stack_escape(caller, base),
        !reader_state_conflict(caller, call, base, field);

    #[local] relation exact_call_result_def(Address, Node, RTLReg, Address);
    exact_call_result_def(*caller, *call, *canonical, *target) <--
        exact_call_result_target(caller, call, target),
        rtl_inst(call, ?RTLInst::Icall(_, _, _, Some(dst), _)),
        relocation_reachable_node(caller, call),
        rtl_value_canonical(dst, canonical);

    // First settle pointer origins which are local to one function.  This
    // stratum is also the authority used to inspect call arguments below: an
    // interprocedural conclusion must never justify itself through the same
    // call-interface aggregate.
    #[local] lattice local_pointer_value_origins(Address, RTLReg, Set<Option<Address>>);
    local_pointer_value_origins(*func, *value, Set::singleton(Some(*target))) <--
        direct_exact_target(func, value, target);
    local_pointer_value_origins(*func, *value, Set::singleton(Some(*target))) <--
        exact_call_result_def(func, _, value, target);
    local_pointer_value_origins(*func, *value, Set::singleton(None)) <--
        final_def(func, node, value),
        !final_move_def(func, node, value),
        !direct_relocation_def(func, node, value, _),
        !exact_call_result_def(func, node, value, _);
    local_pointer_value_origins(func, value, Set::singleton(None)) <--
        unknown_final_value(func, _, value);
    local_pointer_value_origins(*func, *dst, origins.clone()) <--
        local_pointer_value_origins(func, src, origins),
        final_move(func, _, src, dst);

    #[local] relation local_pointer_origin_member(Address, RTLReg, Option<Address>);
    local_pointer_origin_member(*func, *value, *origin) <--
        local_pointer_value_origins(func, value, origins),
        for origin in origins.0.iter();
    #[local] relation local_pointer_origin_conflict(Address, RTLReg);
    local_pointer_origin_conflict(func, value) <--
        local_pointer_origin_member(func, value, ?None);
    local_pointer_origin_conflict(func, value) <--
        local_pointer_origin_member(func, value, ?Some(left)),
        local_pointer_origin_member(func, value, ?Some(right)),
        if left != right;
    #[local] relation local_relocation_pointer_target(Address, RTLReg, Address);
    local_relocation_pointer_target(func, value, target) <--
        local_pointer_origin_member(func, value, ?Some(target)),
        !local_pointer_origin_conflict(func, value);

    // A callee parameter may inherit an exact pointer target only through a
    // closed call interface.  Every finalized direct Icall/Itailcall
    // contributes one observation for every validated callee position:
    // singleton Known for an exact local argument, Unknown for a scalar,
    // conflicted, or omitted argument.  The set lattice unions observations,
    // so one bad caller permanently vetoes the MUST conclusion without any
    // pairwise call-site relation.
    #[local] relation final_internal_invocation(Address, Node, Address);
    final_internal_invocation(caller, call, callee) <--
        final_internal_call(caller, call, callee);
    final_internal_invocation(*caller, *call, *callee) <--
        rtl_inst(call, ?RTLInst::Itailcall(_, either::Either::Right(either::Either::Left(callee)), _)),
        relocation_reachable_node(caller, call);

    #[local] relation final_internal_invocation_arg(Address, Node, usize, RTLReg);
    final_internal_invocation_arg(caller, call, position, argument) <--
        final_internal_call(caller, call, _),
        final_call_arg(caller, call, position, argument);
    final_internal_invocation_arg(*caller, *call, position, *canonical) <--
        rtl_inst(call, ?RTLInst::Itailcall(_, either::Either::Right(either::Either::Left(_)), args)),
        relocation_reachable_node(caller, call),
        for (position, raw) in args.iter().enumerate(),
        if *raw != DEFAULT_VAR as RTLReg,
        rtl_value_canonical(raw, canonical);

    #[local] relation callee_param_call_observation(Address, usize, Node, Option<Address>);
    callee_param_call_observation(*callee, *position, *call, Some(*target)) <--
        final_internal_invocation(caller, call, callee),
        function_param_position(callee, position),
        final_internal_invocation_arg(caller, call, position, argument),
        local_relocation_pointer_target(caller, argument, target);
    callee_param_call_observation(*callee, *position, *call, None) <--
        final_internal_invocation(caller, call, callee),
        function_param_position(callee, position),
        !final_internal_invocation_arg(caller, call, position, _);
    callee_param_call_observation(*callee, *position, *call, None) <--
        final_internal_invocation(caller, call, callee),
        function_param_position(callee, position),
        final_internal_invocation_arg(caller, call, position, argument),
        !local_relocation_pointer_target(caller, argument, _);

    #[local] lattice callee_param_call_origins(Address, usize, Set<Option<Address>>);
    callee_param_call_origins(*callee, *position, Set::singleton(*origin)) <--
        callee_param_call_observation(callee, position, _, origin);
    #[local] relation callee_param_call_origin_member(Address, usize, Option<Address>);
    callee_param_call_origin_member(*callee, *position, *origin) <--
        callee_param_call_origins(callee, position, origins),
        for origin in origins.0.iter();
    #[local] relation callee_param_call_origin_conflict(Address, usize);
    callee_param_call_origin_conflict(callee, position) <--
        callee_param_call_origin_member(callee, position, ?None);
    callee_param_call_origin_conflict(callee, position) <--
        callee_param_call_origin_member(callee, position, ?Some(left)),
        callee_param_call_origin_member(callee, position, ?Some(right)),
        if left != right;

    // Absence of a recovered symbol is intentionally conservative: stripped
    // internal helpers qualify, while named/export-visible functions do not.
    // Any materialized function address likewise admits an unenumerated
    // indirect caller and vetoes call-interface closure.
    #[local] relation function_address_materialized(Address);
    function_address_materialized(func) <-- code_pointer_in_data(_, func);
    function_address_materialized(func) <--
        rtl_inst(_, ?RTLInst::Iop(Operation::Oindirectsymbol(ident), _, _)),
        if let Ok(func) = Address::try_from(*ident);
    #[local] relation function_has_finalized_internal_invocation(Address);
    function_has_finalized_internal_invocation(callee) <--
        final_internal_invocation(_, _, callee);
    #[local] relation closed_call_interface(Address);
    closed_call_interface(callee) <--
        closed_summary_function(callee),
        function_has_finalized_internal_invocation(callee),
        !function_symbol(callee, _),
        !main_function(callee),
        !function_address_materialized(callee);

    #[local] relation callee_param_exact_target(Address, usize, Address);
    callee_param_exact_target(callee, position, target) <--
        closed_call_interface(callee),
        callee_param_call_origin_member(callee, position, ?Some(target)),
        !callee_param_call_origin_conflict(callee, position);

    // Unified final pointer state.  Local origins retain all competing
    // definitions; a closed call-interface proof can add a parameter origin,
    // and ordinary finalized moves carry either kind forward.
    #[local] lattice pointer_value_origins(Address, RTLReg, Set<Option<Address>>);
    pointer_value_origins(*func, *value, Set::singleton(*origin)) <--
        local_pointer_origin_member(func, value, origin);
    pointer_value_origins(*callee, *value, Set::singleton(Some(*target))) <--
        callee_param_exact_target(callee, position, target),
        param_exact_carrier(callee, position, value);
    pointer_value_origins(*func, *dst, origins.clone()) <--
        pointer_value_origins(func, src, origins),
        final_move(func, _, src, dst);

    #[local] relation pointer_origin_member(Address, RTLReg, Option<Address>);
    pointer_origin_member(*func, *value, *origin) <--
        pointer_value_origins(func, value, origins),
        for origin in origins.0.iter();
    #[local] relation pointer_origin_conflict(Address, RTLReg);
    pointer_origin_conflict(func, value) <-- pointer_origin_member(func, value, ?None);
    pointer_origin_conflict(func, value) <--
        pointer_origin_member(func, value, ?Some(left)),
        pointer_origin_member(func, value, ?Some(right)),
        if left != right;

    relation relocation_pointer_target(Address, RTLReg, Address);
    relocation_pointer_target(func, value, target) <--
        pointer_origin_member(func, value, ?Some(target)),
        !pointer_origin_conflict(func, value);

    // `must_be_ptr` is globally keyed, so a contextual exact fact can be
    // projected only when every reachable owner of this value agrees.  This
    // also rejects a shared-tail value that is exact in one function and
    // scalar/unknown in another.
    #[local] relation value_owner_context(RTLReg, Address);
    value_owner_context(value, func) <-- final_def(func, _, value);
    value_owner_context(value, func) <-- final_value_use(func, _, value);
    #[local] relation value_owner_count(RTLReg, usize);
    value_owner_count(value, count) <--
        value_owner_context(value, _),
        agg count = count_items(func) in value_owner_context(value, func);
    #[local] relation exact_value_owner_target_count(RTLReg, Address, usize);
    exact_value_owner_target_count(value, target, count) <--
        relocation_pointer_target(_, value, target),
        agg count = count_items(func) in relocation_pointer_target(func, value, target);
    must_be_ptr(value) <--
        value_owner_count(value, owner_count),
        exact_value_owner_target_count(value, _, exact_count),
        if owner_count == exact_count;
}

// Infer a logical array only after the exact points-to facts have settled and
// GlobalArrayPass has retained the initialized object image. The Ascent half
// derives access-shape candidates; the wrapper below validates physical
// ownership with sorted interval indexes before publishing them.
ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct RelocationArrayPassProgram;

    relation global_var_ref(Ident);
    relation relocation_reachable_node(Address, Node);
    relation relocation_pointer_target(Address, RTLReg, Address);
    relation retained_initialized_data_range(Address, Arc<Vec<u8>>);
    relation rtl_inst(Node, RTLInst);
    relation rtl_value_canonical(RTLReg, RTLReg);
    // Scheduler-visible raw superset only.  RelocationArrayPass restores the
    // pre-pass extent inventory before logical-layout validation, validates a
    // symbol-less byte fragment independently, and replaces both of these
    // relations before the sub-DB is merged.  In particular, this temporary
    // row must never certify relocation_target_array as a typed layout.
    relation relocation_target_storage_fragment(Ident, usize);
    relation global_storage_extent(Ident, usize);

    #[local] relation relocation_target_access(Address, i64, usize);
    relocation_target_access(*target, *offset, width) <--
        rtl_inst(node, ?RTLInst::Iload(chunk, Addressing::Aindexed(offset), args, _)),
        if args.len() == 1 && *offset >= 0,
        if let Some(width) = known_chunk_byte_size(chunk),
        relocation_reachable_node(func, node),
        rtl_value_canonical(&args[0], canonical),
        relocation_pointer_target(func, canonical, target);
    relocation_target_access(*target, *offset, width) <--
        rtl_inst(node, ?RTLInst::Istore(chunk, Addressing::Aindexed(offset), args, _)),
        if args.len() == 1 && *offset >= 0,
        if let Some(width) = known_chunk_byte_size(chunk),
        relocation_reachable_node(func, node),
        rtl_value_canonical(&args[0], canonical),
        relocation_pointer_target(func, canonical, target);

    #[local] relation target_access_width(Address, usize);
    target_access_width(target, width) <-- relocation_target_access(target, _, width);
    #[local] relation target_access_width_count(Address, usize);
    target_access_width_count(target, count) <--
        target_access_width(target, _),
        agg count = count_items(width) in target_access_width(target, width);
    #[local] relation target_single_width(Address, usize);
    target_single_width(target, width) <--
        target_access_width(target, width),
        target_access_width_count(target, count),
        if *count == 1 && matches!(*width, 1 | 2 | 4 | 8);

    #[local] relation target_distinct_offset(Address, i64);
    target_distinct_offset(target, offset) <-- relocation_target_access(target, offset, _);
    #[local] relation target_offset_count(Address, usize);
    target_offset_count(target, count) <--
        target_distinct_offset(target, _),
        agg count = count_items(offset) in target_distinct_offset(target, offset);
    #[local] relation target_min_offset(Address, i64);
    target_min_offset(target, minimum) <--
        target_distinct_offset(target, _),
        agg minimum = min_i64(offset) in target_distinct_offset(target, offset);
    #[local] relation target_access_end(Address, i64);
    target_access_end(*target, end) <--
        relocation_target_access(target, offset, width),
        if let Some(end) = checked_access_end(*offset, *width);
    #[local] relation target_max_end(Address, i64);
    target_max_end(target, maximum) <--
        target_access_end(target, _),
        agg maximum = max_i64(end) in target_access_end(target, end);
    #[local] relation target_bad_alignment(Address);
    target_bad_alignment(*target) <--
        relocation_target_access(target, offset, _),
        target_single_width(target, width),
        if *offset % (*width as i64) != 0;

    #[local] relation target_array_candidate(Address, usize, usize, usize);
    target_array_candidate(*target, *width, count, extent) <--
        target_single_width(target, width),
        target_offset_count(target, offset_count),
        if *offset_count >= 2,
        target_min_offset(target, minimum),
        if *minimum == 0,
        target_max_end(target, maximum),
        if let Some(count) = exact_array_count(*maximum, *width),
        let extent = count * *width,
        !target_bad_alignment(target);

    #[local] relation target_extent_initialized(Address, usize);
    target_extent_initialized(*target, *extent) <--
        target_array_candidate(target, _, _, extent),
        retained_initialized_data_range(start, bytes),
        if initialized_range_covers(*start, bytes, *target, *extent);

    relation relocation_target_array(Ident, usize, usize);
    relocation_target_array(target_ident, *width, *count) <--
        target_array_candidate(target, width, count, extent),
        target_extent_initialized(target, extent),
        if let Ok(target_ident) = Ident::try_from(*target);

    // Make the imperative publication visible to scheduler metadata.  The
    // wrapper snapshots the old inventory and replaces this raw superset with
    // exactly `prior U validated` before the sub-DB is merged.
    global_var_ref(ident) <-- relocation_target_array(ident, _, _);

    // This pass is the second producer of the shared logical-layout superset.
    // The wrapper replaces both relations with the same validated rows.
    relation is_global_array(Ident, usize, usize);
    is_global_array(ident, width, count) <--
        relocation_target_array(ident, width, count);

    relocation_target_storage_fragment(ident, extent) <--
        relocation_target_array(ident, width, count),
        if let Some(extent) = width.checked_mul(*count);
    global_storage_extent(ident, extent) <--
        relocation_target_storage_fragment(ident, extent);
}

fn initialized_ranges_cover(
    ranges: &[(Address, Arc<Vec<u8>>)],
    start: Address,
    extent: usize,
) -> bool {
    ranges
        .iter()
        .any(|(range_start, bytes)| initialized_range_covers(*range_start, bytes, start, extent))
}

fn relocation_slots_overlap(
    sorted_slots: &[Address],
    start: Address,
    extent: usize,
    pointer_width: usize,
) -> bool {
    let Some(end) = start.checked_add(extent as u64) else {
        return true;
    };
    let first = sorted_slots.partition_point(|slot| {
        slot.checked_add(pointer_width as u64)
            .is_some_and(|slot_end| slot_end <= start)
    });
    sorted_slots.get(first).is_some_and(|slot| {
        slot.checked_add(pointer_width as u64)
            .is_none_or(|slot_end| *slot < end && start < slot_end)
    })
}

#[derive(Debug, Clone, Copy)]
struct PhysicalInterval {
    start: Address,
    end: Address,
    owner: Ident,
}

#[derive(Debug, Clone, Copy)]
struct LayoutCandidate {
    owner: Ident,
    start: Address,
    end: Address,
    width: usize,
    count: usize,
}

fn expire_intervals<T>(active: &mut BTreeMap<Address, Vec<T>>, at: Address) {
    while active.first_key_value().is_some_and(|(end, _)| *end <= at) {
        active.pop_first();
    }
}

/// Return candidate indexes which overlap either a different known physical
/// owner or another inferred candidate.  The start-event sweep sees containing
/// intervals no matter how deeply they are nested; the former immediate-
/// predecessor lookup missed those cases.  Work is O((C + G) log(C + G) + K),
/// where K is the number of actual interval overlaps inspected.
fn cross_owner_overlap_rejections(
    candidates: &[LayoutCandidate],
    known: &[PhysicalInterval],
) -> BTreeSet<usize> {
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    enum EventKind {
        Known,
        Candidate,
    }

    let mut events: Vec<(Address, EventKind, usize)> = known
        .iter()
        .enumerate()
        .map(|(index, interval)| (interval.start, EventKind::Known, index))
        .chain(
            candidates
                .iter()
                .enumerate()
                .map(|(index, candidate)| (candidate.start, EventKind::Candidate, index)),
        )
        .collect();
    events.sort_unstable();

    let mut active_known: BTreeMap<Address, Vec<(usize, Ident)>> = BTreeMap::new();
    let mut active_candidates: BTreeMap<Address, Vec<(usize, Ident)>> = BTreeMap::new();
    let mut rejected = BTreeSet::new();

    for (start, kind, index) in events {
        expire_intervals(&mut active_known, start);
        expire_intervals(&mut active_candidates, start);
        match kind {
            EventKind::Known => {
                let interval = known[index];
                for active in active_candidates.values().flatten() {
                    if active.1 != interval.owner {
                        rejected.insert(active.0);
                    }
                }
                active_known
                    .entry(interval.end)
                    .or_default()
                    .push((index, interval.owner));
            }
            EventKind::Candidate => {
                let candidate = candidates[index];
                if active_known
                    .values()
                    .flatten()
                    .any(|active| active.1 != candidate.owner)
                {
                    rejected.insert(index);
                }
                for active in active_candidates.values().flatten() {
                    if active.1 != candidate.owner {
                        rejected.insert(index);
                        rejected.insert(active.0);
                    }
                }
                active_candidates
                    .entry(candidate.end)
                    .or_default()
                    .push((index, candidate.owner));
            }
        }
    }
    rejected
}

/// Validate logical layout independently from physical ownership.  A pointer
/// to an interior subrange never licenses typing the enclosing object as a
/// homogeneous array.  Exact object extents are bounds and must agree with the
/// observed logical extent; they are never used to invent trailing elements.
fn validate_relocation_layouts(
    db: &DecompileDB,
    raw: &BTreeSet<(Ident, usize, usize)>,
    prior_layouts: &BTreeSet<(Ident, usize, usize)>,
) -> BTreeSet<(Ident, usize, usize)> {
    let initialized: Vec<(Address, Arc<Vec<u8>>)> = db
        .rel_iter::<(Address, Arc<Vec<u8>>)>("retained_initialized_data_range")
        .cloned()
        .collect();
    let pointer_widths: BTreeSet<usize> = db
        .rel_iter::<(i64,)>("abi_pointer_size")
        .filter_map(|(width,)| usize::try_from(*width).ok())
        .collect();
    let Some(&pointer_width) = pointer_widths.first().filter(|_| pointer_widths.len() == 1) else {
        return BTreeSet::new();
    };
    let mut relocation_slots: Vec<Address> = db
        .rel_iter::<(Address, Address)>("pointer_in_data")
        .chain(db.rel_iter::<(Address, Address)>("code_pointer_in_data"))
        .map(|(slot, _)| *slot)
        .collect();
    relocation_slots.sort_unstable();
    relocation_slots.dedup();

    let global_refs: BTreeSet<Address> = db
        .rel_iter::<(Ident,)>("global_var_ref")
        .filter_map(|(ident,)| Address::try_from(*ident).ok())
        .collect();
    let interior_targets: BTreeSet<Ident> = db
        .rel_iter::<(Ident, Ident, i64)>("interior_to_base_ident")
        .map(|(interior, _, _)| *interior)
        .collect();
    let mut extents_by_owner: BTreeMap<Ident, BTreeSet<usize>> = BTreeMap::new();
    for (owner, extent) in db.rel_iter::<(Ident, usize)>("global_storage_extent") {
        if *extent > 0 {
            extents_by_owner.entry(*owner).or_default().insert(*extent);
        }
    }
    // symbol_size contains data OBJECT symbols only.  Keep every distinct size
    // for overlap rejection; a candidate rooted at an ambiguously sized object
    // is rejected below rather than choosing one.
    for (address, extent, _) in db.rel_iter::<(Address, usize, Symbol)>("symbol_size") {
        if *extent > 0 {
            if let Ok(owner) = Ident::try_from(*address) {
                extents_by_owner.entry(owner).or_default().insert(*extent);
            }
        }
    }

    let mut known_intervals: Vec<PhysicalInterval> = extents_by_owner
        .iter()
        .flat_map(|(owner, extents)| {
            let start = Address::try_from(*owner).ok();
            extents.iter().filter_map(move |extent| {
                let start = start?;
                Some(PhysicalInterval {
                    start,
                    end: start.checked_add(*extent as u64)?,
                    owner: *owner,
                })
            })
        })
        .collect();
    known_intervals.sort_unstable_by_key(|interval| (interval.start, interval.end, interval.owner));

    let mut prior_by_owner: BTreeMap<Ident, BTreeSet<(usize, usize)>> = BTreeMap::new();
    for (owner, width, count) in prior_layouts {
        prior_by_owner
            .entry(*owner)
            .or_default()
            .insert((*width, *count));
    }

    let mut candidates = Vec::new();
    for &(target_ident, width, target_count) in raw {
        if width == 0 || target_count < 2 {
            continue;
        }
        let Some(target_extent) = width.checked_mul(target_count) else {
            continue;
        };
        let Ok(target_start) = Address::try_from(target_ident) else {
            continue;
        };

        if interior_targets.contains(&target_ident) {
            continue;
        }
        // Section bytes prove only that the observed prefix is initialized;
        // they do not prove where this object ends.  Publishing a declaration
        // therefore requires one authoritative physical extent which agrees
        // exactly with the logical access extent.
        let Some(extents) = extents_by_owner.get(&target_ident) else {
            continue;
        };
        if extents.len() != 1 || extents.first().copied() != Some(target_extent) {
            continue;
        }
        if !initialized_ranges_cover(&initialized, target_start, target_extent) {
            continue;
        }
        let Some(end) = target_start.checked_add(target_extent as u64) else {
            continue;
        };
        if relocation_slots_overlap(
            &relocation_slots,
            target_start,
            target_extent,
            pointer_width,
        ) {
            continue;
        }
        if global_refs
            .range((Excluded(target_start), Excluded(end)))
            .next()
            .is_some()
        {
            continue;
        }
        if prior_by_owner
            .get(&target_ident)
            .is_some_and(|layouts| !layouts.contains(&(width, target_count)))
        {
            continue;
        }
        candidates.push(LayoutCandidate {
            owner: target_ident,
            start: target_start,
            end,
            width,
            count: target_count,
        });
    }

    // A single physical owner cannot simultaneously receive conflicting
    // logical layouts from different raw target paths.
    let mut layouts_by_owner: BTreeMap<Ident, BTreeSet<(usize, usize)>> = BTreeMap::new();
    for candidate in &candidates {
        layouts_by_owner
            .entry(candidate.owner)
            .or_default()
            .insert((candidate.width, candidate.count));
    }
    let overlap_rejections = cross_owner_overlap_rejections(&candidates, &known_intervals);
    let mut validated = BTreeSet::new();
    for (index, candidate) in candidates.into_iter().enumerate() {
        if overlap_rejections.contains(&index)
            || layouts_by_owner
                .get(&candidate.owner)
                .is_some_and(|layouts| layouts.len() != 1)
        {
            continue;
        }
        validated.insert((candidate.owner, candidate.width, candidate.count));
    }
    validated
}

fn synthetic_label_address(label: &str) -> Option<Address> {
    label
        .strip_prefix("L_")
        .or_else(|| label.strip_prefix(".L_"))
        .and_then(|hex| Address::from_str_radix(hex, 16).ok())
}

fn exact_targets_for_raw_value(
    func: Address,
    raw: RTLReg,
    canonical_by_raw: &BTreeMap<RTLReg, BTreeSet<RTLReg>>,
    targets_by_value: &BTreeMap<(Address, RTLReg), BTreeSet<Address>>,
) -> BTreeSet<Address> {
    let mut targets = BTreeSet::new();
    if let Some(canonicals) = canonical_by_raw.get(&raw) {
        for canonical in canonicals {
            if let Some(exact) = targets_by_value.get(&(func, *canonical)) {
                targets.extend(exact.iter().copied());
            }
        }
    } else if let Some(exact) = targets_by_value.get(&(func, raw)) {
        targets.extend(exact.iter().copied());
    }
    targets
}

fn mark_raw_value_targets(
    func: Address,
    raw: RTLReg,
    canonical_by_raw: &BTreeMap<RTLReg, BTreeSet<RTLReg>>,
    targets_by_value: &BTreeMap<(Address, RTLReg), BTreeSet<Address>>,
    unsupported: &mut BTreeSet<Address>,
) {
    unsupported.extend(exact_targets_for_raw_value(
        func,
        raw,
        canonical_by_raw,
        targets_by_value,
    ));
}

/// Targets with an address use that the fixed-offset array certificate did not
/// represent.  A dynamic/negative/unknown-width dereference could reach beyond
/// the proposed fragment, while arithmetic, a builtin, or an external call can
/// create an alias whose accesses are not in relocation_target_access.  Direct
/// internal calls and returns remain admissible because the preceding exact
/// points-to pass transports only closed call interfaces.
fn unsupported_relocation_target_uses(db: &DecompileDB) -> BTreeSet<Address> {
    let mut canonical_by_raw: BTreeMap<RTLReg, BTreeSet<RTLReg>> = BTreeMap::new();
    for (raw, canonical) in db.rel_iter::<(RTLReg, RTLReg)>("rtl_value_canonical") {
        canonical_by_raw.entry(*raw).or_default().insert(*canonical);
    }

    let mut targets_by_value: BTreeMap<(Address, RTLReg), BTreeSet<Address>> = BTreeMap::new();
    for (func, value, target) in
        db.rel_iter::<(Address, RTLReg, Address)>("relocation_pointer_target")
    {
        targets_by_value
            .entry((*func, *value))
            .or_default()
            .insert(*target);
    }

    let mut owners_by_node: BTreeMap<Node, BTreeSet<Address>> = BTreeMap::new();
    for (func, node) in db.rel_iter::<(Address, Node)>("relocation_reachable_node") {
        owners_by_node.entry(*node).or_default().insert(*func);
    }

    let mut unsupported = BTreeSet::new();
    for (node, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        let Some(funcs) = owners_by_node.get(node) else {
            continue;
        };
        match inst {
            RTLInst::Iload(chunk, addressing, args, _)
            | RTLInst::Istore(chunk, addressing, args, _) => {
                let supported = matches!(addressing, Addressing::Aindexed(offset) if *offset >= 0)
                    && args.len() == 1
                    && known_chunk_byte_size(chunk).is_some();
                if supported {
                    continue;
                }
                for func in funcs {
                    for raw in args.iter() {
                        mark_raw_value_targets(
                            *func,
                            *raw,
                            &canonical_by_raw,
                            &targets_by_value,
                            &mut unsupported,
                        );
                    }
                }
            }
            RTLInst::Icall(_, callee, args, _, _) => {
                let direct_internal =
                    matches!(callee, either::Either::Right(either::Either::Left(_)));
                if direct_internal {
                    continue;
                }
                for func in funcs {
                    if let either::Either::Left(raw_target) = callee {
                        mark_raw_value_targets(
                            *func,
                            *raw_target,
                            &canonical_by_raw,
                            &targets_by_value,
                            &mut unsupported,
                        );
                    }
                    for raw in args.iter() {
                        mark_raw_value_targets(
                            *func,
                            *raw,
                            &canonical_by_raw,
                            &targets_by_value,
                            &mut unsupported,
                        );
                    }
                }
            }
            RTLInst::Itailcall(_, callee, args) => {
                let direct_internal =
                    matches!(callee, either::Either::Right(either::Either::Left(_)));
                if direct_internal {
                    continue;
                }
                for func in funcs {
                    if let either::Either::Left(raw_target) = callee {
                        mark_raw_value_targets(
                            *func,
                            *raw_target,
                            &canonical_by_raw,
                            &targets_by_value,
                            &mut unsupported,
                        );
                    }
                    for raw in args.iter() {
                        mark_raw_value_targets(
                            *func,
                            *raw,
                            &canonical_by_raw,
                            &targets_by_value,
                            &mut unsupported,
                        );
                    }
                }
            }
            RTLInst::Iop(operation, args, _)
                if !matches!(operation, Operation::Omove | Operation::Ocmp(_)) =>
            {
                for func in funcs {
                    for raw in args.iter() {
                        mark_raw_value_targets(
                            *func,
                            *raw,
                            &canonical_by_raw,
                            &targets_by_value,
                            &mut unsupported,
                        );
                    }
                }
            }
            RTLInst::Ibuiltin(_, _, _) => {
                let uses = inst_def_use(inst).1;
                for func in funcs {
                    for raw in &uses {
                        mark_raw_value_targets(
                            *func,
                            *raw,
                            &canonical_by_raw,
                            &targets_by_value,
                            &mut unsupported,
                        );
                    }
                }
            }
            _ => {}
        }
    }
    unsupported
}

/// Choose a byte-backed representation fragment for a data-pointer target that
/// lost its ELF object symbol.  The target is an exact address root; its end is
/// the first independent root or initialized section boundary above it.  This
/// is deliberately not a logical-array proof: the wrapper publishes these rows
/// only after typed relocation layouts have been validated against the prior
/// physical inventory.
fn validate_relocation_storage_fragments(
    db: &DecompileDB,
    raw_layouts: &BTreeSet<(Ident, usize, usize)>,
    prior_layouts: &BTreeSet<(Ident, usize, usize)>,
    prior_global_refs: &BTreeSet<Ident>,
    prior_storage_extents: &BTreeSet<(Ident, usize)>,
) -> BTreeSet<(Ident, usize)> {
    let pointer_widths: BTreeSet<usize> = db
        .rel_iter::<(i64,)>("abi_pointer_size")
        .filter_map(|(width,)| usize::try_from(*width).ok())
        .filter(|width| *width > 0)
        .collect();
    let Some(&pointer_width) = pointer_widths.first().filter(|_| pointer_widths.len() == 1) else {
        return BTreeSet::new();
    };

    let initialized: Vec<(Address, Arc<Vec<u8>>)> = db
        .rel_iter::<(Address, Arc<Vec<u8>>)>("retained_initialized_data_range")
        .cloned()
        .collect();
    let data_sections: BTreeSet<(Address, Address)> = db
        .rel_iter::<(Address, Address)>("data_section_range")
        .copied()
        .collect();
    let symbol_addresses: BTreeSet<Address> = db
        .rel_iter::<(Address, Symbol, Symbol)>("symbols")
        .map(|(address, _, _)| *address)
        .collect();

    let mut extents_by_owner: BTreeMap<Ident, BTreeSet<usize>> = BTreeMap::new();
    for (owner, extent) in prior_storage_extents {
        if *extent > 0 {
            extents_by_owner.entry(*owner).or_default().insert(*extent);
        }
    }
    for (address, extent, _) in db.rel_iter::<(Address, usize, Symbol)>("symbol_size") {
        if *extent > 0 {
            if let Ok(owner) = Ident::try_from(*address) {
                extents_by_owner.entry(owner).or_default().insert(*extent);
            }
        }
    }
    let known_intervals: Vec<PhysicalInterval> = extents_by_owner
        .iter()
        .flat_map(|(owner, extents)| {
            let start = Address::try_from(*owner).ok();
            extents.iter().filter_map(move |extent| {
                let start = start?;
                Some(PhysicalInterval {
                    start,
                    end: start.checked_add(*extent as u64)?,
                    owner: *owner,
                })
            })
        })
        .collect();

    let interior_targets: BTreeSet<Ident> = db
        .rel_iter::<(Ident, Ident, i64)>("interior_to_base_ident")
        .map(|(interior, _, _)| *interior)
        .collect();
    let unsupported_targets = unsupported_relocation_target_uses(db);

    let mut relocation_slots: Vec<Address> = db
        .rel_iter::<(Address, Address)>("pointer_in_data")
        .chain(db.rel_iter::<(Address, Address)>("code_pointer_in_data"))
        .map(|(slot, _)| *slot)
        .collect();
    relocation_slots.sort_unstable();
    relocation_slots.dedup();
    let data_pointer_targets: BTreeSet<Address> = db
        .rel_iter::<(Address, Address)>("pointer_in_data")
        .map(|(_, target)| *target)
        .collect();

    let string_ranges: BTreeSet<(Address, Address)> = db
        .rel_iter::<(String, String, usize)>("string_data")
        .filter_map(|(label, _, size)| {
            let start = synthetic_label_address(label)?;
            let extent = size.checked_add(1)?;
            Some((start, start.checked_add(u64::try_from(extent).ok()?)?))
        })
        .collect();

    let mut raw_by_owner: BTreeMap<Ident, BTreeSet<(usize, usize)>> = BTreeMap::new();
    for (owner, width, count) in raw_layouts {
        raw_by_owner
            .entry(*owner)
            .or_default()
            .insert((*width, *count));
    }
    let prior_layout_owners: BTreeSet<Ident> =
        prior_layouts.iter().map(|(owner, _, _)| *owner).collect();

    let mut boundary_roots = symbol_addresses;
    boundary_roots.extend(
        prior_global_refs
            .iter()
            .filter_map(|ident| Address::try_from(*ident).ok()),
    );
    boundary_roots.extend(
        extents_by_owner
            .keys()
            .filter_map(|ident| Address::try_from(*ident).ok()),
    );
    boundary_roots.extend(
        prior_layout_owners
            .iter()
            .filter_map(|ident| Address::try_from(*ident).ok()),
    );
    boundary_roots.extend(relocation_slots.iter().copied());
    boundary_roots.extend(data_pointer_targets.iter().copied());
    boundary_roots.extend(
        raw_by_owner
            .keys()
            .filter_map(|ident| Address::try_from(*ident).ok()),
    );
    boundary_roots.extend(string_ranges.iter().map(|(start, _)| *start));

    let mut validated = BTreeSet::new();
    for (target_ident, layouts) in raw_by_owner {
        if layouts.len() != 1
            || prior_layout_owners.contains(&target_ident)
            || extents_by_owner.contains_key(&target_ident)
            || interior_targets.contains(&target_ident)
        {
            continue;
        }
        let (width, count) = *layouts.first().unwrap();
        let Some(observed_extent) = width.checked_mul(count) else {
            continue;
        };
        let Ok(target) = Address::try_from(target_ident) else {
            continue;
        };
        if observed_extent == 0
            || !data_pointer_targets.contains(&target)
            || unsupported_targets.contains(&target)
            || known_intervals
                .iter()
                .any(|interval| interval.start <= target && target < interval.end)
            || string_ranges
                .iter()
                .any(|(start, end)| *start <= target && target < *end)
        {
            continue;
        }

        let initialized_ends: BTreeSet<Address> = initialized
            .iter()
            .filter_map(|(start, bytes)| {
                let end = start.checked_add(u64::try_from(bytes.len()).ok()?)?;
                (target >= *start && target < end).then_some(end)
            })
            .collect();
        let section_ends: BTreeSet<Address> = data_sections
            .iter()
            .filter_map(|(start, end)| (target >= *start && target < *end).then_some(*end))
            .collect();
        if initialized_ends.len() != 1 || section_ends.len() != 1 {
            continue;
        }
        let outer_end = (*initialized_ends.first().unwrap()).min(*section_ends.first().unwrap());
        let fragment_end = boundary_roots
            .range((Excluded(target), Included(outer_end)))
            .next()
            .copied()
            .unwrap_or(outer_end);
        let Some(extent_u64) = fragment_end.checked_sub(target) else {
            continue;
        };
        let Ok(extent) = usize::try_from(extent_u64) else {
            continue;
        };
        if extent < observed_extent
            || !initialized_ranges_cover(&initialized, target, extent)
            || relocation_slots_overlap(&relocation_slots, target, extent, pointer_width)
        {
            continue;
        }
        validated.insert((target_ident, extent));
    }
    validated
}

pub struct RelocationPointsToPass;

fn run_relocation_points_to_program(db: &mut DecompileDB) {
    let mut prog = RelocationPointsToPassProgram::default();
    prog.swap_db_fields(db);
    prog.run();

    if db.measure_rule_times {
        let pass_name = "RelocationPointsToPassProgram".to_string();
        let summary = format!(
            "=== Rule Times ===\n{}\n\n=== Relation Sizes ===\n{}",
            prog.scc_times_summary(),
            prog.relation_sizes_summary(),
        );
        eprintln!(
            "[RULE_TIMES] pass {}\n{}\n[/RULE_TIMES]",
            pass_name, summary
        );
        db.rule_time_reports.push((pass_name, summary));
    }

    // Diagnostic only: show the exact joins which carry a relocation from a
    // finalized load into a callee parameter field.  Keeping this at the pass
    // boundary makes future gaps attributable without exporting local proof
    // relations into the global DB or changing scheduling/output.
    if std::env::var("RELOCATION_TRACE").is_ok() {
        let mut direct: Vec<_> = prog.direct_exact_target.iter().copied().collect();
        let mut params: Vec<_> = prog.param_exact_carrier.iter().copied().collect();
        let mut stores: Vec<_> = prog.param_direct_store.iter().cloned().collect();
        let mut exact_stores: Vec<_> = prog.param_store_exact_target.iter().copied().collect();
        direct.sort_unstable();
        params.sort_unstable();
        stores.sort_unstable_by_key(|row| (row.0, row.1, row.2, row.3, row.5));
        exact_stores.sort_unstable();
        eprintln!("[relocation-trace] direct exact targets: {direct:#x?}");
        eprintln!("[relocation-trace] exact parameter carriers: {params:#x?}");
        eprintln!("[relocation-trace] direct parameter stores: {stores:#x?}");
        eprintln!("[relocation-trace] exact relocation stores: {exact_stores:#x?}");
    }

    prog.swap_db_fields(db);
}

impl IRPass for RelocationPointsToPass {
    fn name(&self) -> &'static str {
        "relocation_points_to"
    }

    fn run(&self, db: &mut DecompileDB) {
        run_relocation_points_to_program(db);
    }

    declare_io_from!(RelocationPointsToPassProgram);
}

pub struct RelocationArrayPass;

impl IRPass for RelocationArrayPass {
    fn name(&self) -> &'static str {
        "relocation_array"
    }

    fn run(&self, db: &mut DecompileDB) {
        let prior: BTreeSet<(Ident, usize, usize)> = db
            .rel_iter::<(Ident, usize, usize)>("is_global_array")
            .copied()
            .collect();
        let prior_global_refs: BTreeSet<Ident> = db
            .rel_iter::<(Ident,)>("global_var_ref")
            .map(|(ident,)| *ident)
            .collect();
        let prior_storage_extents: BTreeSet<(Ident, usize)> = db
            .rel_iter::<(Ident, usize)>("global_storage_extent")
            .copied()
            .collect();
        run_pass!(db, RelocationArrayPassProgram);
        let raw: BTreeSet<(Ident, usize, usize)> = db
            .rel_iter::<(Ident, usize, usize)>("relocation_target_array")
            .copied()
            .collect();

        // Raw candidates temporarily make global_var_ref a scheduler-visible
        // output.  Physical validation must see only the pre-pass declaration
        // inventory, so restore it before checking object boundaries.
        let restored_global_refs = ascent::boxcar::Vec::new();
        for ident in &prior_global_refs {
            restored_global_refs.push((*ident,));
        }
        db.rel_set("global_var_ref", restored_global_refs);
        // The Ascent rule publishes only the observed prefix so the scheduler
        // knows this pass writes global_storage_extent.  Restore the prior
        // inventory before either validator runs: a raw prefix must not prove
        // its own typed layout or become an exact physical owner by accident.
        let restored_storage_extents = ascent::boxcar::Vec::new();
        for row in &prior_storage_extents {
            restored_storage_extents.push(*row);
        }
        db.rel_set("global_storage_extent", restored_storage_extents);
        let validated = validate_relocation_layouts(db, &raw, &prior);
        let validated_fragments = validate_relocation_storage_fragments(
            db,
            &raw,
            &prior,
            &prior_global_refs,
            &prior_storage_extents,
        );

        let relocation_relation = ascent::boxcar::Vec::new();
        for row in &validated {
            relocation_relation.push(*row);
        }
        db.rel_set("relocation_target_array", relocation_relation);

        let fragment_relation = ascent::boxcar::Vec::new();
        for row in &validated_fragments {
            fragment_relation.push(*row);
        }
        db.rel_set("relocation_target_storage_fragment", fragment_relation);

        let storage_extent_relation = ascent::boxcar::Vec::new();
        for row in prior_storage_extents.union(&validated_fragments) {
            storage_extent_relation.push(*row);
        }
        db.rel_set("global_storage_extent", storage_extent_relation);

        let global_array_relation = ascent::boxcar::Vec::new();
        for row in prior.union(&validated) {
            global_array_relation.push(*row);
        }
        db.rel_set("is_global_array", global_array_relation);

        let global_ref_relation = ascent::boxcar::Vec::new();
        let mut validated_refs: BTreeSet<Ident> =
            validated.iter().map(|(ident, _, _)| *ident).collect();
        validated_refs.extend(validated_fragments.iter().map(|(ident, _)| *ident));
        for ident in prior_global_refs.union(&validated_refs) {
            global_ref_relation.push((*ident,));
        }
        db.rel_set("global_var_ref", global_ref_relation);

        if std::env::var("GA_DUMP").is_ok() {
            for row in &validated {
                eprintln!("[GA] relocation_target_array {:x?}", row);
            }
            for row in &validated_fragments {
                eprintln!("[GA] relocation_target_storage_fragment {:x?}", row);
            }
        }
    }

    fn extra_reads(&self) -> &'static [&'static str] {
        &[
            "pointer_in_data",
            "code_pointer_in_data",
            "interior_to_base_ident",
            "global_storage_extent",
            "abi_pointer_size",
            "global_var_ref",
            "symbol_size",
            "data_section_range",
            "symbols",
            "string_data",
        ]
    }

    declare_io_from!(RelocationArrayPassProgram);
}

#[cfg(test)]
mod tests {
    use super::{
        cross_owner_overlap_rejections, validate_relocation_layouts, LayoutCandidate,
        PhysicalInterval, RelocationArrayPass, RelocationPointsToPass,
    };
    use crate::decompile::elevator::DecompileDB;
    use crate::decompile::passes::pass::IRPass;
    use crate::mreg::Mreg;
    use crate::x86::op::Addressing;
    use crate::x86::types::{MemoryChunk, RTLInst};
    use std::sync::Arc;

    const WRITER: u64 = 0x1800;
    const READER: u64 = 0xb000;
    const CONSUMER: u64 = 0xc000;
    const CALLER: u64 = 0x4100;
    const RELOC_OWNER: usize = 0x6200;
    const RELOC_SLOT: u64 = 0x6208;
    const TARGET: u64 = 0x7100;
    const STACK_BASE: i64 = -32;
    const FIELD: i64 = 8;

    const WRITER_ENTRY: u64 = 0x9000;
    const WRITER_LOAD: u64 = 0x2200;
    const WRITER_STORE: u64 = 0xa000;
    const WRITER_RETURN: u64 = 0x4400;
    const READER_ENTRY: u64 = 0x8500;
    const READER_LOAD: u64 = 0x1200;
    const READER_RETURN: u64 = 0x7600;
    const CALLER_ENTRY: u64 = 0x6800;
    const WRITE_CALL: u64 = 0x3100;
    const READ_CALL: u64 = 0x5700;
    const ACCESS_ZERO: u64 = 0x0500;
    const ACCESS_FOUR: u64 = 0x4900;
    const CALLER_RETURN: u64 = 0x7300;

    const WRITER_PARAM: u64 = 0x101;
    const READER_PARAM: u64 = 0x201;
    const STACK_ADDR: u64 = 0x301;
    const STACK_CELL: u64 = 0x302;
    const DIRECT_PTR: u64 = 0x401;
    const RETURNED_PTR: u64 = 0x501;
    const READER_FIELD_VALUE: u64 = 0x502;
    const CONSUMER_PARAM: u64 = 0x601;
    const CONSUMER_CALL: u64 = 0x5f00;
    const CONSUMER_ENTRY: u64 = 0xc100;

    fn identity(db: &mut DecompileDB, value: u64) {
        db.rel_push("xtl_canonical", (value, value));
    }

    fn fixture() -> DecompileDB {
        let mut db = DecompileDB::default();
        db.rel_push("abi_pointer_size", (8_i64,));
        db.rel_push("pointer_in_data", (RELOC_SLOT, TARGET));
        db.rel_push(
            "retained_initialized_data_range",
            (TARGET - 4, Arc::new(vec![0_u8; 16])),
        );
        db.rel_push("global_storage_extent", (TARGET as usize, 8_usize));
        for (func, entry) in [
            (WRITER, WRITER_ENTRY),
            (READER, READER_ENTRY),
            (CALLER, CALLER_ENTRY),
        ] {
            db.rel_push("rtl_function_entry", (func, entry));
            db.rel_push("function_has_ltl_body", (func,));
        }

        for (node, func) in [
            (WRITER_ENTRY, WRITER),
            (WRITER_LOAD, WRITER),
            (WRITER_STORE, WRITER),
            (WRITER_RETURN, WRITER),
            (READER_ENTRY, READER),
            (READER_LOAD, READER),
            (READER_RETURN, READER),
            (CALLER_ENTRY, CALLER),
            (WRITE_CALL, CALLER),
            (READ_CALL, CALLER),
            (ACCESS_ZERO, CALLER),
            (ACCESS_FOUR, CALLER),
            (CONSUMER_CALL, CALLER),
            (CALLER_RETURN, CALLER),
        ] {
            db.rel_push("instr_in_function", (node, func));
        }
        for edge in [
            (WRITER_ENTRY, WRITER_LOAD),
            (WRITER_LOAD, WRITER_STORE),
            (WRITER_STORE, WRITER_RETURN),
            (READER_ENTRY, READER_LOAD),
            (READER_LOAD, READER_RETURN),
            (CALLER_ENTRY, WRITE_CALL),
            (WRITE_CALL, READ_CALL),
            (READ_CALL, ACCESS_ZERO),
            (ACCESS_ZERO, ACCESS_FOUR),
            (ACCESS_FOUR, CONSUMER_CALL),
            (CONSUMER_CALL, CALLER_RETURN),
        ] {
            db.rel_push("rtl_succ", edge);
        }

        db.rel_push("abi_int_arg_position", (Mreg::DI, 0_usize));
        db.rel_push("func_param_validated", (WRITER, Mreg::DI));
        db.rel_push("func_param_validated", (READER, Mreg::DI));
        db.rel_push("func_param_validated", (CONSUMER, Mreg::DI));
        db.rel_push("reg_rtl", (WRITER, Mreg::DI, WRITER_PARAM));
        db.rel_push("reg_rtl", (READER, Mreg::DI, READER_PARAM));
        db.rel_push("reg_rtl", (CONSUMER, Mreg::DI, CONSUMER_PARAM));

        db.rel_push(
            "rtl_inst",
            (
                WRITER_LOAD,
                RTLInst::Iload(
                    MemoryChunk::MInt64,
                    Addressing::Aglobal(RELOC_OWNER, 8),
                    Arc::new(vec![]),
                    DIRECT_PTR,
                ),
            ),
        );
        db.rel_push(
            "rtl_inst",
            (
                WRITER_STORE,
                RTLInst::Istore(
                    MemoryChunk::MAny64,
                    Addressing::Aindexed(FIELD),
                    Arc::new(vec![WRITER_PARAM]),
                    DIRECT_PTR,
                ),
            ),
        );
        db.rel_push(
            "rtl_inst",
            (
                READER_LOAD,
                RTLInst::Iload(
                    MemoryChunk::MAny64,
                    Addressing::Aindexed(FIELD),
                    Arc::new(vec![READER_PARAM]),
                    READER_FIELD_VALUE,
                ),
            ),
        );
        db.rel_push("rtl_inst", (WRITER_RETURN, RTLInst::Ireturn(DIRECT_PTR)));
        db.rel_push(
            "rtl_inst",
            (READER_RETURN, RTLInst::Ireturn(READER_FIELD_VALUE)),
        );

        db.rel_push("slot_escaped_canonical", (CALLER, STACK_BASE, STACK_CELL));
        db.rel_push("exact_frame_stack_lea", (CALLER, CALLER_ENTRY, STACK_BASE));
        db.rel_push(
            "canonical_exact_stack_addr_ptr_result",
            (CALLER_ENTRY, STACK_ADDR),
        );
        db.rel_push(
            "rtl_inst",
            (
                CALLER_ENTRY,
                RTLInst::Iop(
                    crate::x86::op::Operation::Oleal(Addressing::Ainstack(STACK_BASE)),
                    Arc::new(vec![]),
                    STACK_ADDR,
                ),
            ),
        );
        db.rel_push(
            "rtl_inst",
            (
                WRITE_CALL,
                RTLInst::Icall(
                    None,
                    either::Either::Right(either::Either::Left(WRITER)),
                    Arc::new(vec![STACK_ADDR]),
                    None,
                    READ_CALL,
                ),
            ),
        );
        db.rel_push(
            "rtl_inst",
            (
                READ_CALL,
                RTLInst::Icall(
                    None,
                    either::Either::Right(either::Either::Left(READER)),
                    Arc::new(vec![STACK_ADDR]),
                    Some(RETURNED_PTR),
                    ACCESS_ZERO,
                ),
            ),
        );
        db.rel_push(
            "rtl_inst",
            (
                CONSUMER_CALL,
                RTLInst::Icall(
                    None,
                    either::Either::Right(either::Either::Left(CONSUMER)),
                    Arc::new(vec![RETURNED_PTR]),
                    None,
                    CALLER_RETURN,
                ),
            ),
        );
        db.rel_push("rtl_inst", (CALLER_RETURN, RTLInst::Ireturn(RETURNED_PTR)));

        for (node, offset) in [(ACCESS_ZERO, 0_i64), (ACCESS_FOUR, 4_i64)] {
            db.rel_push(
                "rtl_inst",
                (
                    node,
                    RTLInst::Iload(
                        MemoryChunk::MInt32,
                        Addressing::Aindexed(offset),
                        Arc::new(vec![RETURNED_PTR]),
                        0x800 + node,
                    ),
                ),
            );
        }

        for value in [
            WRITER_PARAM,
            READER_PARAM,
            STACK_ADDR,
            STACK_CELL,
            DIRECT_PTR,
            RETURNED_PTR,
            READER_FIELD_VALUE,
            CONSUMER_PARAM,
        ] {
            identity(&mut db, value);
        }
        db
    }

    fn add_closed_consumer(db: &mut DecompileDB) {
        db.rel_push("rtl_function_entry", (CONSUMER, CONSUMER_ENTRY));
        db.rel_push("function_has_ltl_body", (CONSUMER,));
        db.rel_push("instr_in_function", (CONSUMER_ENTRY, CONSUMER));
        db.rel_push(
            "rtl_inst",
            (CONSUMER_ENTRY, RTLInst::Ireturn(CONSUMER_PARAM)),
        );
    }

    fn recovered(db: &DecompileDB) -> Vec<(usize, usize, usize)> {
        db.rel_iter::<(usize, usize, usize)>("relocation_target_array")
            .cloned()
            .collect()
    }

    fn recovered_fragments(db: &DecompileDB) -> Vec<(usize, usize)> {
        let mut fragments: Vec<_> = db
            .rel_iter::<(usize, usize)>("relocation_target_storage_fragment")
            .copied()
            .collect();
        fragments.sort_unstable();
        fragments
    }

    fn prepare_symbol_less_target(db: &mut DecompileDB, section_end: u64) {
        db.rel_set(
            "global_storage_extent",
            ascent::boxcar::Vec::<(usize, usize)>::new(),
        );
        let start = TARGET - 4;
        let len = usize::try_from(section_end - start).unwrap();
        let initialized: ascent::boxcar::Vec<(u64, Arc<Vec<u8>>)> = ascent::boxcar::Vec::new();
        initialized.push((start, Arc::new(vec![0_u8; len])));
        db.rel_set("retained_initialized_data_range", initialized);
        db.rel_push("data_section_range", (start, section_end));
    }

    fn replace_inst(db: &mut DecompileDB, node: u64, replacement: Option<RTLInst>) {
        let mut facts: Vec<(u64, RTLInst)> = db
            .rel_iter::<(u64, RTLInst)>("rtl_inst")
            .filter(|(existing, _)| *existing != node)
            .cloned()
            .collect();
        if let Some(inst) = replacement {
            facts.push((node, inst));
        }
        facts.sort_by_key(|(node, _)| *node);
        let relation = ascent::boxcar::Vec::new();
        for fact in facts {
            relation.push(fact);
        }
        db.rel_set("rtl_inst", relation);
    }

    fn remove_edge(db: &mut DecompileDB, src: u64, dst: u64) {
        let facts: Vec<(u64, u64)> = db
            .rel_iter::<(u64, u64)>("rtl_succ")
            .filter(|edge| **edge != (src, dst))
            .copied()
            .collect();
        let relation = ascent::boxcar::Vec::new();
        for fact in facts {
            relation.push(fact);
        }
        db.rel_set("rtl_succ", relation);
    }

    fn remove_xtl_canonical(db: &mut DecompileDB, value: u64) {
        let facts: Vec<(u64, u64)> = db
            .rel_iter::<(u64, u64)>("xtl_canonical")
            .filter(|(raw, _)| *raw != value)
            .copied()
            .collect();
        let relation = ascent::boxcar::Vec::new();
        for fact in facts {
            relation.push(fact);
        }
        db.rel_set("xtl_canonical", relation);
    }

    fn insert_between(db: &mut DecompileDB, src: u64, dst: u64, node: u64) {
        remove_edge(db, src, dst);
        db.rel_push("rtl_succ", (src, node));
        db.rel_push("rtl_succ", (node, dst));
    }

    fn run_recovery(db: &mut DecompileDB) {
        RelocationPointsToPass.run(db);
        RelocationArrayPass.run(db);
    }

    #[test]
    fn structurally_transported_relocation_recovers_initialized_extent() {
        let mut db = fixture();
        run_recovery(&mut db);
        assert_eq!(recovered(&db), vec![(TARGET as usize, 4, 2)]);
        assert!(recovered_fragments(&db).is_empty());
        assert!(db
            .rel_iter::<(u64,)>("must_be_ptr")
            .any(|(value,)| *value == RETURNED_PTR));
        assert!(db
            .rel_iter::<(usize,)>("global_var_ref")
            .any(|(ident,)| *ident == TARGET as usize));
        assert!(!db
            .rel_iter::<(u64,)>("must_be_ptr")
            .any(|(value,)| *value == CONSUMER_PARAM));
    }

    #[test]
    fn symbol_less_relocation_target_owns_initialized_byte_suffix() {
        let mut db = fixture();
        prepare_symbol_less_target(&mut db, TARGET + 12);

        run_recovery(&mut db);

        assert!(recovered(&db).is_empty());
        assert_eq!(recovered_fragments(&db), vec![(TARGET as usize, 12)]);
        assert!(db
            .rel_iter::<(usize, usize)>("global_storage_extent")
            .any(|fact| *fact == (TARGET as usize, 12)));
        assert!(db
            .rel_iter::<(usize,)>("global_var_ref")
            .any(|(ident,)| *ident == TARGET as usize));
        assert!(!db
            .rel_iter::<(usize, usize, usize)>("is_global_array")
            .any(|(ident, _, _)| *ident == TARGET as usize));
    }

    #[test]
    fn relocation_fragment_and_storage_extent_are_scheduler_outputs() {
        let pass = RelocationArrayPass;
        assert!(pass
            .outputs()
            .contains(&"relocation_target_storage_fragment"));
        assert!(pass.outputs().contains(&"global_storage_extent"));
    }

    #[test]
    fn next_independent_root_caps_symbol_less_byte_suffix() {
        let mut db = fixture();
        prepare_symbol_less_target(&mut db, TARGET + 12);
        db.rel_push("global_var_ref", ((TARGET + 8) as usize,));

        run_recovery(&mut db);

        assert_eq!(recovered_fragments(&db), vec![(TARGET as usize, 8)]);
        assert!(!db
            .rel_iter::<(usize, usize, usize)>("is_global_array")
            .any(|(ident, _, _)| *ident == TARGET as usize));
    }

    #[test]
    fn root_or_relocation_before_observed_end_vetoes_byte_suffix() {
        let mut rooted = fixture();
        prepare_symbol_less_target(&mut rooted, TARGET + 12);
        rooted.rel_push("global_var_ref", ((TARGET + 4) as usize,));
        run_recovery(&mut rooted);
        assert!(recovered_fragments(&rooted).is_empty());

        let mut relocated = fixture();
        prepare_symbol_less_target(&mut relocated, TARGET + 12);
        relocated.rel_push("pointer_in_data", (TARGET + 4, TARGET + 0x100));
        run_recovery(&mut relocated);
        assert!(recovered_fragments(&relocated).is_empty());
    }

    #[test]
    fn containing_sized_owner_vetoes_symbol_less_byte_suffix() {
        let mut db = fixture();
        prepare_symbol_less_target(&mut db, TARGET + 12);
        db.rel_push("symbol_size", (TARGET - 8, 20_usize, "owner"));

        run_recovery(&mut db);

        assert!(recovered_fragments(&db).is_empty());
    }

    #[test]
    fn dynamic_relocation_target_access_vetoes_byte_suffix() {
        let mut db = fixture();
        prepare_symbol_less_target(&mut db, TARGET + 12);
        let dynamic_access = 0x4a00_u64;
        insert_between(&mut db, ACCESS_FOUR, CONSUMER_CALL, dynamic_access);
        db.rel_push("instr_in_function", (dynamic_access, CALLER));
        db.rel_push(
            "rtl_inst",
            (
                dynamic_access,
                RTLInst::Iload(
                    MemoryChunk::MInt32,
                    Addressing::Aindexed2(0),
                    Arc::new(vec![RETURNED_PTR, 0x9f0]),
                    0x9f1,
                ),
            ),
        );

        run_recovery(&mut db);

        assert!(recovered_fragments(&db).is_empty());
    }

    #[test]
    fn exact_pointer_comparison_does_not_veto_byte_suffix() {
        let mut db = fixture();
        prepare_symbol_less_target(&mut db, TARGET + 12);
        let comparison = 0x4a00_u64;
        insert_between(&mut db, ACCESS_FOUR, CONSUMER_CALL, comparison);
        db.rel_push("instr_in_function", (comparison, CALLER));
        db.rel_push(
            "rtl_inst",
            (
                comparison,
                RTLInst::Iop(
                    crate::x86::op::Operation::Ocmp(crate::x86::op::Condition::Ccomplimm(
                        crate::x86::op::Comparison::Ceq,
                        TARGET as i64,
                    )),
                    Arc::new(vec![RETURNED_PTR]),
                    0x9f1,
                ),
            ),
        );

        run_recovery(&mut db);

        assert_eq!(recovered_fragments(&db), vec![(TARGET as usize, 12)]);
    }

    #[test]
    fn initialized_section_prefix_without_object_extent_is_not_an_array() {
        let mut db = fixture();
        db.rel_set(
            "global_storage_extent",
            ascent::boxcar::Vec::<(usize, usize)>::new(),
        );

        run_recovery(&mut db);

        assert!(recovered(&db).is_empty());
        assert!(!db
            .rel_iter::<(usize,)>("global_var_ref")
            .any(|(ident,)| *ident == TARGET as usize));
    }

    #[test]
    fn finalized_private_temporary_gets_identity_canonicalization() {
        let mut db = fixture();
        // Expansion-only temporaries (for example the upper lane of a wide
        // SIMD copy) have no physical XTL alias node.  Their finalized RTL
        // definition and uses still form one exact value web.
        remove_xtl_canonical(&mut db, DIRECT_PTR);
        run_recovery(&mut db);

        assert_eq!(recovered(&db), vec![(TARGET as usize, 4, 2)]);
        assert!(db
            .rel_iter::<(u64, u64)>("rtl_value_canonical")
            .any(|fact| *fact == (DIRECT_PTR, DIRECT_PTR)));
    }

    #[test]
    fn bypass_path_keeps_unknown_in_may_state() {
        let mut db = fixture();
        // Deliberately non-monotonic IDs: reachability is the CFG edge, never
        // numeric address order.  One entry path bypasses the writer.
        db.rel_push("rtl_succ", (CALLER_ENTRY, READ_CALL));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn intervening_unresolved_call_is_a_strong_unknown_write() {
        let mut db = fixture();
        let unknown_call: u64 = 0x2a00;
        db.rel_push("instr_in_function", (unknown_call, CALLER));
        db.rel_push(
            "rtl_inst",
            (
                unknown_call,
                RTLInst::Icall(
                    None,
                    either::Either::Right(either::Either::Right("unknown")),
                    Arc::new(vec![STACK_ADDR]),
                    None,
                    READ_CALL,
                ),
            ),
        );
        db.rel_push("rtl_succ", (WRITE_CALL, unknown_call));
        db.rel_push("rtl_succ", (unknown_call, READ_CALL));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn separately_modeled_interior_global_vetoes_overlapping_storage() {
        let mut db = fixture();
        db.rel_push("global_var_ref", ((TARGET + 4) as usize,));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn dead_candidate_instruction_cannot_publish_pointer_provenance() {
        let mut db = fixture();
        replace_inst(&mut db, WRITER_LOAD, None);
        db.rel_push(
            "rtl_inst_candidate",
            (
                WRITER_LOAD,
                RTLInst::Iload(
                    MemoryChunk::MInt64,
                    Addressing::Aglobal(RELOC_OWNER, 8),
                    Arc::new(vec![]),
                    DIRECT_PTR,
                ),
            ),
        );
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
        assert!(!db
            .rel_iter::<(u64,)>("must_be_ptr")
            .any(|(value,)| *value == DIRECT_PTR));
    }

    #[test]
    fn disconnected_final_relocation_island_cannot_publish_provenance() {
        let mut db = fixture();
        remove_edge(&mut db, WRITER_ENTRY, WRITER_LOAD);
        db.rel_push("rtl_succ", (WRITER_ENTRY, WRITER_STORE));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
        assert!(!db
            .rel_iter::<(u64,)>("must_be_ptr")
            .any(|(value,)| *value == DIRECT_PTR));
    }

    #[test]
    fn disconnected_scalar_island_does_not_veto_reachable_exact_origin() {
        let mut db = fixture();
        let island = 0x2d10_u64;
        db.rel_push("instr_in_function", (island, WRITER));
        db.rel_push(
            "rtl_inst",
            (
                island,
                RTLInst::Iop(
                    crate::x86::op::Operation::Ointconst(0),
                    Arc::new(vec![]),
                    DIRECT_PTR,
                ),
            ),
        );
        run_recovery(&mut db);
        assert_eq!(recovered(&db), vec![(TARGET as usize, 4, 2)]);
    }

    #[test]
    fn unknown_live_in_arm_blocks_relocation_must_origin() {
        let mut db = fixture();
        db.rel_push(
            "unknown_reg_value_reaches_use",
            (WRITER, WRITER_STORE, Mreg::R10),
        );
        db.rel_push("reg_rtl", (WRITER_STORE, Mreg::R10, DIRECT_PTR));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
        assert!(!db
            .rel_iter::<(u64,)>("must_be_ptr")
            .any(|(value,)| *value == DIRECT_PTR));
    }

    #[test]
    fn validated_live_parameter_is_not_an_unknown_entry_value() {
        let mut db = fixture();
        // The physical reaching-definition observer reports every entry-live
        // register.  Here DI is independently proven to be the writer's
        // validated incoming parameter at the store, so that observer is an
        // explanation of the same value rather than a competing Unknown arm.
        db.rel_push(
            "unknown_reg_value_reaches_use",
            (WRITER, WRITER_STORE, Mreg::DI),
        );
        db.rel_push("arg_reg_param_live_at", (WRITER, WRITER_STORE, Mreg::DI));
        db.rel_push("reg_rtl", (WRITER_STORE, Mreg::DI, WRITER_PARAM));

        run_recovery(&mut db);
        assert_eq!(recovered(&db), vec![(TARGET as usize, 4, 2)]);
    }

    #[test]
    fn unknown_stack_arm_blocks_exact_call_object_identity() {
        let mut db = fixture();
        db.rel_push(
            "unknown_reg_value_reaches_use",
            (CALLER, WRITE_CALL, Mreg::R10),
        );
        db.rel_push("reg_rtl", (WRITE_CALL, Mreg::R10, STACK_ADDR));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn unknown_field_origin_arm_blocks_reader_summary() {
        let mut db = fixture();
        db.rel_push(
            "unknown_reg_value_reaches_use",
            (READER, READER_RETURN, Mreg::R10),
        );
        db.rel_push("reg_rtl", (READER_RETURN, Mreg::R10, READER_FIELD_VALUE));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn scalar_arm_blocks_singleton_pointer_publication() {
        let mut db = fixture();
        let scalar_def = 0x2d00_u64;
        db.rel_push("instr_in_function", (scalar_def, WRITER));
        db.rel_push(
            "rtl_inst",
            (
                scalar_def,
                RTLInst::Iop(
                    crate::x86::op::Operation::Ointconst(0),
                    Arc::new(vec![]),
                    DIRECT_PTR,
                ),
            ),
        );
        db.rel_push("rtl_succ", (WRITER_ENTRY, scalar_def));
        db.rel_push("rtl_succ", (scalar_def, WRITER_STORE));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
        assert!(!db
            .rel_iter::<(u64,)>("must_be_ptr")
            .any(|(value,)| *value == DIRECT_PTR));
    }

    #[test]
    fn nonstack_arm_blocks_exact_stack_object_identity() {
        let mut db = fixture();
        let scalar_def = 0x2e00_u64;
        db.rel_push("instr_in_function", (scalar_def, CALLER));
        db.rel_push(
            "rtl_inst",
            (
                scalar_def,
                RTLInst::Iop(
                    crate::x86::op::Operation::Ointconst(0),
                    Arc::new(vec![]),
                    STACK_ADDR,
                ),
            ),
        );
        db.rel_push("rtl_succ", (CALLER_ENTRY, scalar_def));
        db.rel_push("rtl_succ", (scalar_def, WRITE_CALL));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn writer_store_must_reach_every_return() {
        let mut db = fixture();
        db.rel_push("rtl_succ", (WRITER_ENTRY, WRITER_RETURN));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn incomplete_writer_body_cannot_publish_effect_summary() {
        let mut db = fixture();
        db.rel_push("function_has_uncovered_block", (WRITER,));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn unknown_width_store_is_never_a_pointer_strong_update() {
        let mut db = fixture();
        replace_inst(
            &mut db,
            WRITER_STORE,
            Some(RTLInst::Istore(
                MemoryChunk::Unknown,
                Addressing::Aindexed(FIELD),
                Arc::new(vec![WRITER_PARAM]),
                DIRECT_PTR,
            )),
        );
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn stale_call_mapping_cannot_override_the_selected_scalar_argument() {
        let mut db = fixture();
        let selected_scalar = 0x777_u64;
        identity(&mut db, selected_scalar);
        db.rel_push("call_arg_mapping", (WRITE_CALL, 0_usize, STACK_ADDR));
        replace_inst(
            &mut db,
            WRITE_CALL,
            Some(RTLInst::Icall(
                None,
                either::Either::Right(either::Either::Left(WRITER)),
                Arc::new(vec![selected_scalar]),
                None,
                READ_CALL,
            )),
        );
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn stale_scalar_mapping_cannot_veto_the_selected_stack_argument() {
        let mut db = fixture();
        let stale_scalar = 0x778_u64;
        identity(&mut db, stale_scalar);
        db.rel_push("call_arg_mapping", (WRITE_CALL, 0_usize, stale_scalar));
        run_recovery(&mut db);
        assert_eq!(recovered(&db), vec![(TARGET as usize, 4, 2)]);
    }

    #[test]
    fn stale_internal_target_cannot_override_final_external_callee() {
        let mut db = fixture();
        db.rel_push("call_target_func", (WRITE_CALL, WRITER));
        replace_inst(
            &mut db,
            WRITE_CALL,
            Some(RTLInst::Icall(
                None,
                either::Either::Right(either::Either::Right("external_writer")),
                Arc::new(vec![STACK_ADDR]),
                None,
                READ_CALL,
            )),
        );
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn reachable_tailcall_vetoes_all_return_writer_summary() {
        let mut db = fixture();
        let tail = 0x3300_u64;
        db.rel_push("instr_in_function", (tail, WRITER));
        db.rel_push(
            "rtl_inst",
            (
                tail,
                RTLInst::Itailcall(
                    None,
                    either::Either::Right(either::Either::Right("tail_target")),
                    Arc::new(vec![]),
                ),
            ),
        );
        db.rel_push("rtl_succ", (WRITER_ENTRY, tail));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn incomplete_caller_body_cannot_publish_exact_reader_result() {
        let mut db = fixture();
        db.rel_push("function_unresolved_control", (CALLER, 0xdead_u64));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn direct_frame_store_invalidates_tracked_pointer_cell() {
        let mut db = fixture();
        let write = 0x3200_u64;
        let scalar = 0x779_u64;
        identity(&mut db, scalar);
        db.rel_push("instr_in_function", (write, CALLER));
        db.rel_push(
            "rtl_inst",
            (
                write,
                RTLInst::Istore(
                    MemoryChunk::MInt64,
                    Addressing::Ainstack(STACK_BASE + FIELD),
                    Arc::new(vec![]),
                    scalar,
                ),
            ),
        );
        db.rel_push(
            "frame_stack_write_bytes",
            (CALLER, write, STACK_BASE + FIELD, 8_usize),
        );
        insert_between(&mut db, WRITE_CALL, READ_CALL, write);
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn mixed_stack_carrier_store_is_a_may_write_not_a_strong_update() {
        let mut db = fixture();
        let copy = 0x3210_u64;
        let scalar_def = 0x3220_u64;
        let store = 0x3230_u64;
        let mixed = 0x77a_u64;
        let scalar = 0x77b_u64;
        for value in [mixed, scalar] {
            identity(&mut db, value);
        }
        for node in [copy, scalar_def, store] {
            db.rel_push("instr_in_function", (node, CALLER));
        }
        db.rel_push(
            "rtl_inst",
            (
                copy,
                RTLInst::Iop(
                    crate::x86::op::Operation::Omove,
                    Arc::new(vec![STACK_ADDR]),
                    mixed,
                ),
            ),
        );
        db.rel_push(
            "rtl_inst",
            (
                scalar_def,
                RTLInst::Iop(
                    crate::x86::op::Operation::Ointconst(1),
                    Arc::new(vec![]),
                    mixed,
                ),
            ),
        );
        db.rel_push(
            "rtl_inst",
            (
                store,
                RTLInst::Istore(
                    MemoryChunk::MInt64,
                    Addressing::Aindexed(FIELD),
                    Arc::new(vec![mixed]),
                    scalar,
                ),
            ),
        );
        remove_edge(&mut db, WRITE_CALL, READ_CALL);
        db.rel_push("rtl_succ", (WRITE_CALL, copy));
        db.rel_push("rtl_succ", (WRITE_CALL, scalar_def));
        db.rel_push("rtl_succ", (copy, store));
        db.rel_push("rtl_succ", (scalar_def, store));
        db.rel_push("rtl_succ", (store, READ_CALL));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn returned_parameter_alias_vetoes_later_stack_must_read() {
        let mut db = fixture();
        let identity_func = 0xe000_u64;
        let identity_entry = 0xe100_u64;
        let identity_return = 0xe200_u64;
        let identity_param = 0xe01_u64;
        let identity_call = 0x3240_u64;
        let alias_store = 0x3250_u64;
        let alias = 0xe02_u64;
        let scalar = 0xe03_u64;

        db.rel_push("rtl_function_entry", (identity_func, identity_entry));
        db.rel_push("function_has_ltl_body", (identity_func,));
        db.rel_push("func_param_validated", (identity_func, Mreg::DI));
        db.rel_push("reg_rtl", (identity_func, Mreg::DI, identity_param));
        db.rel_push("instr_in_function", (identity_entry, identity_func));
        db.rel_push("instr_in_function", (identity_return, identity_func));
        db.rel_push("rtl_succ", (identity_entry, identity_return));
        db.rel_push(
            "rtl_inst",
            (identity_return, RTLInst::Ireturn(identity_param)),
        );

        for node in [identity_call, alias_store] {
            db.rel_push("instr_in_function", (node, CALLER));
        }
        db.rel_push(
            "rtl_inst",
            (
                identity_call,
                RTLInst::Icall(
                    None,
                    either::Either::Right(either::Either::Left(identity_func)),
                    Arc::new(vec![STACK_ADDR]),
                    Some(alias),
                    alias_store,
                ),
            ),
        );
        db.rel_push(
            "rtl_inst",
            (
                alias_store,
                RTLInst::Istore(
                    MemoryChunk::MInt64,
                    Addressing::Aindexed(FIELD),
                    Arc::new(vec![alias]),
                    scalar,
                ),
            ),
        );
        remove_edge(&mut db, WRITE_CALL, READ_CALL);
        db.rel_push("rtl_succ", (WRITE_CALL, identity_call));
        db.rel_push("rtl_succ", (identity_call, alias_store));
        db.rel_push("rtl_succ", (alias_store, READ_CALL));
        for value in [identity_param, alias, scalar] {
            identity(&mut db, value);
        }
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn omitted_structural_callee_argument_blocks_preserve_summary() {
        let mut db = fixture();
        let nested = 0x2300_u64;
        db.rel_push("instr_in_function", (nested, READER));
        db.rel_push(
            "rtl_inst",
            (
                nested,
                RTLInst::Icall(
                    None,
                    either::Either::Right(either::Either::Right("mutator")),
                    Arc::new(vec![]),
                    None,
                    READER_LOAD,
                ),
            ),
        );
        db.rel_push("def_reaches_call", (nested, READER, Mreg::DI));
        insert_between(&mut db, READER_ENTRY, READER_LOAD, nested);
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn omitted_structural_caller_argument_is_an_unknown_stack_escape() {
        let mut db = fixture();
        let hidden_call = 0x3260_u64;
        db.rel_push("instr_in_function", (hidden_call, CALLER));
        db.rel_push(
            "rtl_inst",
            (
                hidden_call,
                RTLInst::Icall(
                    None,
                    either::Either::Right(either::Either::Right("hidden_mutator")),
                    Arc::new(vec![]),
                    None,
                    READ_CALL,
                ),
            ),
        );
        db.rel_push("reg_rtl", (CALLER_ENTRY, Mreg::R10, STACK_ADDR));
        db.rel_push("def_reaches_call", (hidden_call, CALLER_ENTRY, Mreg::R10));
        insert_between(&mut db, WRITE_CALL, READ_CALL, hidden_call);
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn indirect_target_role_remains_an_escape_even_when_also_an_argument() {
        let mut db = fixture();
        replace_inst(
            &mut db,
            WRITE_CALL,
            Some(RTLInst::Icall(
                None,
                either::Either::Left(STACK_ADDR),
                Arc::new(vec![STACK_ADDR]),
                None,
                READ_CALL,
            )),
        );
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn contextual_pointer_fact_does_not_hard_type_shared_scalar_owner() {
        let mut db = fixture();
        let other = 0xd000_u64;
        let other_entry = 0xd100_u64;
        db.rel_push("rtl_function_entry", (other, other_entry));
        db.rel_push("function_has_ltl_body", (other,));
        db.rel_push("instr_in_function", (other_entry, other));
        db.rel_push(
            "rtl_inst",
            (
                other_entry,
                RTLInst::Iop(
                    crate::x86::op::Operation::Ointconst(1),
                    Arc::new(vec![]),
                    RETURNED_PTR,
                ),
            ),
        );
        RelocationPointsToPass.run(&mut db);
        assert!(!db
            .rel_iter::<(u64,)>("must_be_ptr")
            .any(|(value,)| *value == RETURNED_PTR));
    }

    #[test]
    fn closed_internal_call_interface_transports_exact_pointer_parameter() {
        let mut db = fixture();
        add_closed_consumer(&mut db);
        run_recovery(&mut db);

        assert!(db
            .rel_iter::<(u64,)>("must_be_ptr")
            .any(|(value,)| *value == CONSUMER_PARAM));
    }

    #[test]
    fn scalar_callsite_vetoes_pointer_parameter_transport() {
        let mut db = fixture();
        add_closed_consumer(&mut db);
        let scalar_def = 0x5f10_u64;
        let scalar_call = 0x5f20_u64;
        let scalar = 0x707_u64;
        for node in [scalar_def, scalar_call] {
            db.rel_push("instr_in_function", (node, CALLER));
        }
        db.rel_push(
            "rtl_inst",
            (
                scalar_def,
                RTLInst::Iop(
                    crate::x86::op::Operation::Ointconst(1),
                    Arc::new(vec![]),
                    scalar,
                ),
            ),
        );
        db.rel_push(
            "rtl_inst",
            (
                scalar_call,
                RTLInst::Icall(
                    None,
                    either::Either::Right(either::Either::Left(CONSUMER)),
                    Arc::new(vec![scalar]),
                    None,
                    CALLER_RETURN,
                ),
            ),
        );
        remove_edge(&mut db, CONSUMER_CALL, CALLER_RETURN);
        db.rel_push("rtl_succ", (CONSUMER_CALL, scalar_def));
        db.rel_push("rtl_succ", (scalar_def, scalar_call));
        db.rel_push("rtl_succ", (scalar_call, CALLER_RETURN));

        run_recovery(&mut db);
        assert!(!db
            .rel_iter::<(u64,)>("must_be_ptr")
            .any(|(value,)| *value == CONSUMER_PARAM));
    }

    #[test]
    fn symbol_visible_callee_vetoes_closed_call_interface() {
        let mut db = fixture();
        add_closed_consumer(&mut db);
        db.rel_push("function_symbol", (CONSUMER, "consumer"));
        run_recovery(&mut db);

        assert!(!db
            .rel_iter::<(u64,)>("must_be_ptr")
            .any(|(value,)| *value == CONSUMER_PARAM));
    }

    #[test]
    fn transported_parameter_still_requires_all_value_owners_to_agree() {
        let mut db = fixture();
        add_closed_consumer(&mut db);
        let other = 0xd000_u64;
        let other_entry = 0xd100_u64;
        db.rel_push("rtl_function_entry", (other, other_entry));
        db.rel_push("function_has_ltl_body", (other,));
        db.rel_push("instr_in_function", (other_entry, other));
        db.rel_push(
            "rtl_inst",
            (
                other_entry,
                RTLInst::Iop(
                    crate::x86::op::Operation::Ointconst(1),
                    Arc::new(vec![]),
                    CONSUMER_PARAM,
                ),
            ),
        );

        RelocationPointsToPass.run(&mut db);
        assert!(!db
            .rel_iter::<(u64,)>("must_be_ptr")
            .any(|(value,)| *value == CONSUMER_PARAM));
    }

    #[test]
    fn interior_target_never_types_the_whole_sized_owner_as_an_array() {
        let mut db = fixture();
        let owner = (TARGET - 8) as usize;
        db.rel_push("interior_to_base_ident", (TARGET as usize, owner, 8_i64));
        db.rel_push("global_storage_extent", (owner, 20_usize));
        db.rel_push(
            "retained_initialized_data_range",
            (owner as u64, Arc::new(vec![0_u8; 20])),
        );
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn exact_sized_owner_is_a_bound_not_an_extent_invention() {
        let mut db = fixture();
        db.rel_push("symbol_size", (TARGET, 16_usize, "target"));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn exact_sized_owner_with_matching_logical_extent_is_admitted() {
        let mut db = fixture();
        db.rel_push("symbol_size", (TARGET, 8_usize, "target"));
        run_recovery(&mut db);
        assert_eq!(recovered(&db), vec![(TARGET as usize, 4, 2)]);
    }

    #[test]
    fn conflicting_exact_owner_extents_are_rejected() {
        let mut db = fixture();
        db.rel_push("symbol_size", (TARGET, 8_usize, "target_a"));
        db.rel_push("symbol_size", (TARGET, 12_usize, "target_b"));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn unreferenced_sized_neighbor_vetoes_cross_object_extent() {
        let mut db = fixture();
        db.rel_push("symbol_size", (TARGET + 4, 4_usize, "neighbor"));
        run_recovery(&mut db);
        assert!(recovered(&db).is_empty());
    }

    #[test]
    fn nested_interval_index_detects_nonadjacent_enclosing_owner() {
        let candidates = vec![LayoutCandidate {
            owner: 50,
            start: 50,
            end: 60,
            width: 1,
            count: 10,
        }];
        let known = vec![
            PhysicalInterval {
                owner: 0,
                start: 0,
                end: 100,
            },
            PhysicalInterval {
                owner: 10,
                start: 10,
                end: 20,
            },
        ];
        assert_eq!(
            cross_owner_overlap_rejections(&candidates, &known),
            [0_usize].into_iter().collect()
        );
    }

    #[test]
    fn one_owner_cannot_receive_conflicting_relocation_layouts() {
        let mut db = DecompileDB::default();
        db.rel_push("abi_pointer_size", (8_i64,));
        db.rel_push(
            "retained_initialized_data_range",
            (TARGET, Arc::new(vec![0_u8; 32])),
        );
        let raw = [
            (TARGET as usize, 4_usize, 2_usize),
            (TARGET as usize, 8_usize, 2_usize),
        ]
        .into_iter()
        .collect();
        assert!(validate_relocation_layouts(&db, &raw, &Default::default()).is_empty());
    }
}
