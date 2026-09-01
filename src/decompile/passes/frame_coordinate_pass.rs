use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::mreg::Mreg;
use crate::x86::types::{Address, Node, Symbol};
use ascent::ascent_par;
use ascent::lattice::set::Set;
use ascent::Dual;

fn shift_stack_offsets(offsets: &Set<i64>, delta: i64) -> Set<i64> {
    Set(offsets
        .iter()
        .filter_map(|offset| offset.checked_add(delta))
        .collect())
}

fn exact_stack_offset(offsets: &Set<i64>) -> Option<i64> {
    (offsets.len() == 1)
        .then(|| offsets.iter().next().copied())
        .flatten()
}

// GCC/Clang stack-clash protection lowers one fixed allocation into a page
// probe loop:
//
//   target = sp - total
//   do { sp -= page; touch *sp; } while (sp != target)
//
// The ordinary MUST lattice must reject the loop header because its SP really
// does differ between iterations.  Once the exact target definition reaches
// the loop comparison, however, the fallthrough edge has one architectural
// state: the entry SP minus `total`.  Return the extra delta to apply after the
// first (ordinary) page subtraction already represented in the loop body.
fn fixed_stack_probe_exit_delta(target_displacement: i64, page_size: i64) -> Option<i64> {
    if target_displacement >= 0 || page_size <= 0 {
        return None;
    }
    let total = target_displacement.checked_neg()?;
    if total < page_size || total > (1 << 20) || total % page_size != 0 {
        return None;
    }
    page_size.checked_sub(total)
}

fn x86_gpr_view_width(reg: &str) -> Option<i64> {
    match reg {
        "RAX" | "RBX" | "RCX" | "RDX" | "RSI" | "RDI" | "RBP" | "RSP" | "R8" | "R9" | "R10"
        | "R11" | "R12" | "R13" | "R14" | "R15" => Some(8),
        "EAX" | "EBX" | "ECX" | "EDX" | "ESI" | "EDI" | "EBP" | "ESP" | "R8D" | "R9D" | "R10D"
        | "R11D" | "R12D" | "R13D" | "R14D" | "R15D" => Some(4),
        "AX" | "BX" | "CX" | "DX" | "SI" | "DI" | "BP" | "SP" | "R8W" | "R9W" | "R10W" | "R11W"
        | "R12W" | "R13W" | "R14W" | "R15W" => Some(2),
        "AL" | "BL" | "CL" | "DL" | "AH" | "BH" | "CH" | "DH" | "SIL" | "DIL" | "BPL" | "SPL"
        | "R8B" | "R9B" | "R10B" | "R11B" | "R12B" | "R13B" | "R14B" | "R15B" => Some(1),
        _ => None,
    }
}

ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct FrameCoordinatePassProgram;

    relation abi_pointer_size(i64);
    relation call_targets_noreturn(Node);
    relation code_in_block(Address, Address);
    relation decoded_stack_write_bytes(Address, Symbol, i64, usize);
    relation decoded_stack_pointer_delta(Address, i64);
    relation ddisasm_cfg_edge(Address, Address, Symbol);
    relation function_has_ltl_body(Address);
    relation function_has_uncovered_block(Address);
    relation function_unknown_terminal(Address, Node);
    relation function_unresolved_control(Address, Node);
    relation instr_in_function(Node, Address);
    relation instruction(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize);
    relation next(Address, Address);
    relation op_indirect(Symbol, &'static str, &'static str, &'static str, i64, i64, usize);
    relation op_immediate(Symbol, i64, usize);
    relation op_register(Symbol, &'static str);
    relation padd(Address, Symbol, Symbol);
    relation pcmp(Address, Symbol, Symbol);
    relation plea(Address, Symbol, Symbol);
    relation ppop(Address, Symbol);
    relation ppush(Address, Symbol);
    relation psub(Address, Symbol, Symbol);
    relation reg_def(Address, Mreg);
    relation settled_block_dom_set(Address, Address, Set<Address>);
    relation stack_delta(Address, i64);

    #[local] relation reachable_frame_node(Address, Address);
    reachable_frame_node(*func, *node) <--
        instr_in_function(node, func),
        code_in_block(node, block),
        settled_block_dom_set(func, block, _);

    // Instruction CFG only. Numeric address/node order never participates in
    // stack-state reachability.
    #[local] relation frame_cfg_step(Address, Address);
    frame_cfg_step(*src, *dst) <--
        next(src, dst),
        code_in_block(src, block),
        code_in_block(dst, block),
        !call_targets_noreturn(src);

    // The two raw operand orders of CMP share one normalized statement: the
    // current full-width SP is compared with the exact full-width target value
    // defined by the preheader LEA.  Mreg alone aliases partial register views,
    // so retain the decoder spellings as width evidence on both operands.
    #[local] relation stack_probe_target_cmp(Address, Mreg, Address);
    stack_probe_target_cmp(*target_def, target_reg, *cmp) <--
        plea(target_def, target_dst, _),
        op_register(target_dst, target_name),
        abi_pointer_size(pointer_width),
        if x86_gpr_view_width(target_name) == Some(*pointer_width),
        let target_reg = Mreg::x86(*target_name),
        pcmp(cmp, left, right),
        op_register(left, left_name),
        op_register(right, right_name),
        if Mreg::x86(*left_name) == Mreg::SP,
        if x86_gpr_view_width(left_name) == Some(*pointer_width),
        if Mreg::x86(*right_name) == target_reg,
        if x86_gpr_view_width(right_name) == Some(*pointer_width);
    stack_probe_target_cmp(*target_def, target_reg, *cmp) <--
        plea(target_def, target_dst, _),
        op_register(target_dst, target_name),
        abi_pointer_size(pointer_width),
        if x86_gpr_view_width(target_name) == Some(*pointer_width),
        let target_reg = Mreg::x86(*target_name),
        pcmp(cmp, left, right),
        op_register(left, left_name),
        op_register(right, right_name),
        if Mreg::x86(*left_name) == target_reg,
        if x86_gpr_view_width(left_name) == Some(*pointer_width),
        if Mreg::x86(*right_name) == Mreg::SP,
        if x86_gpr_view_width(right_name) == Some(*pointer_width);

    // A fixed stack-probe certificate.  The target LEA and the first SUB are
    // adjacent in the preheader/header transition; the SUB, page touch, CMP,
    // and conditional latch are one straight-line probe block.  The latch's
    // backedge is dominance-proven and its other structural successor is the
    // summarized exit.  No address ordering participates in the proof.
    #[local] relation fixed_stack_probe(
        Address, Address, Address, Address, Address, Address, Address, i64
    );
    fixed_stack_probe(
        *func, *target_def, *header, *touch, *cmp, *latch, *exit, exit_delta
    ) <--
        plea(target_def, target_dst, target_mem),
        op_register(target_dst, target_name),
        abi_pointer_size(pointer_width),
        if x86_gpr_view_width(target_name) == Some(*pointer_width),
        let target_reg = Mreg::x86(*target_name),
        if target_reg != Mreg::SP && !target_reg.is_unknown(),
        op_indirect(target_mem, _, target_base, target_index, _, target_disp, target_width),
        if Mreg::x86(*target_base) == Mreg::SP,
        if x86_gpr_view_width(target_base) == Some(*pointer_width),
        if *target_index == "NONE" || target_index.is_empty(),
        if i64::try_from(*target_width).ok() == Some(*pointer_width),
        next(target_def, header),
        psub(header, stack_dst, page_operand),
        op_register(stack_dst, stack_name),
        if Mreg::x86(*stack_name) == Mreg::SP,
        if x86_gpr_view_width(stack_name) == Some(*pointer_width),
        op_immediate(page_operand, page_size, _),
        if *page_size > 0,
        next(header, touch),
        decoded_stack_write_bytes(touch, touch_base, touch_ofs, touch_width),
        if Mreg::x86(*touch_base) == Mreg::SP,
        if *touch_ofs == 0 && *touch_width > 0,
        next(touch, cmp),
        stack_probe_target_cmp(target_def, target_reg, cmp),
        next(cmp, latch),
        !reg_def(header, target_reg),
        !reg_def(touch, target_reg),
        !reg_def(cmp, target_reg),
        !reg_def(latch, target_reg),
        frame_cfg_step(latch, header),
        frame_cfg_step(latch, exit),
        if exit != header,
        code_in_block(header, header_block),
        code_in_block(touch, header_block),
        code_in_block(cmp, header_block),
        code_in_block(latch, latch_block),
        settled_block_dom_set(func, latch_block, latch_dominators),
        if latch_dominators.0.contains(header_block),
        reachable_frame_node(func, target_def),
        reachable_frame_node(func, header),
        reachable_frame_node(func, touch),
        reachable_frame_node(func, cmp),
        reachable_frame_node(func, latch),
        reachable_frame_node(func, exit),
        if let Some(exit_delta) = fixed_stack_probe_exit_delta(*target_disp, *page_size);

    #[local] relation frame_stack_probe_back_edge(Address, Address, Address);
    frame_stack_probe_back_edge(func, *latch, *header) <--
        fixed_stack_probe(func, _, header, _, _, latch, _, _);

    #[local] relation frame_stack_probe_exit_edge(Address, Address, Address, i64);
    frame_stack_probe_exit_edge(func, *latch, *exit, *delta) <--
        fixed_stack_probe(func, _, _, _, _, latch, exit, delta);

    // Public physical bound for downstream frame-address rendering.  This is
    // deliberately not folded into func_stacksz: that legacy relation sums
    // static SUB sites, while a probe loop executes one SUB repeatedly.  The
    // exact target displacement is the allocation contract for this owner,
    // including absorbed tail targets whose symbol span contains no SUB at all.
    relation fixed_stack_probe_allocation(Address, i64);
    fixed_stack_probe_allocation(func, total) <--
        fixed_stack_probe(func, target_def, _, _, _, _, _, _),
        plea(target_def, _, target_mem),
        op_indirect(target_mem, _, _, _, _, target_disp, _),
        if let Some(total) = target_disp.checked_neg(),
        if total > 0 && total <= (1 << 20);

    // Probe-body points intentionally retain no public exact coordinate: their
    // SP differs on every iteration.  The private first-iteration state exists
    // only to calculate the certified exit state below.
    #[local] relation frame_stack_probe_body_node(Address, Address);
    frame_stack_probe_body_node(func, *header) <--
        fixed_stack_probe(func, _, header, _, _, _, _, _);
    frame_stack_probe_body_node(func, *touch) <--
        fixed_stack_probe(func, _, _, touch, _, _, _, _);
    frame_stack_probe_body_node(func, *cmp) <--
        fixed_stack_probe(func, _, _, _, cmp, _, _, _);
    frame_stack_probe_body_node(func, *latch) <--
        fixed_stack_probe(func, _, _, _, _, latch, _, _);
    frame_cfg_step(*src, *dst) <--
        ddisasm_cfg_edge(src, dst, edge_type),
        if *edge_type != "call" && *edge_type != "indirect" && *edge_type != "indirect_call",
        !call_targets_noreturn(src);

    // Point-keyed MUST stack state. Dual<Set> joins by intersection; no
    // pairwise reachability/dominance relation is materialized. Every CFG
    // edge, including a loop backedge, participates: a nonzero loop-carried
    // update must make the header unknown instead of certifying iteration
    // one's address as a fixed local. Balanced cycles remain exact naturally.
    #[local] lattice frame_stack_offset(Address, Address, Dual<Set<i64>>);

    // `stack_delta` by itself is not sufficient proof: POP %rsp both advances
    // the old stack and replaces SP with the popped value. Admit only raw forms
    // whose outgoing SP is old-SP plus this exact constant. LEA is decoded
    // directly because the historical stack_delta relation does not cover it.
    #[local] relation frame_exact_stack_delta(Address, i64);
    frame_exact_stack_delta(node, delta) <-- decoded_stack_pointer_delta(node, delta);
    frame_exact_stack_delta(*node, -*pointer_width) <--
        ppush(node, _),
        abi_pointer_size(pointer_width);
    frame_exact_stack_delta(*node, *pointer_width) <--
        ppop(node, operand),
        op_register(operand, register),
        if Mreg::x86(*register) != Mreg::SP,
        abi_pointer_size(pointer_width);
    frame_exact_stack_delta(*node, *pointer_width) <--
        ppop(node, operand),
        !op_register(operand, _),
        abi_pointer_size(pointer_width);
    frame_exact_stack_delta(*node, *delta) <--
        padd(node, dst, _),
        op_register(dst, dst_name),
        if Mreg::x86(*dst_name) == Mreg::SP,
        if let Some(width) = x86_gpr_view_width(dst_name),
        abi_pointer_size(pointer_width),
        if width == *pointer_width,
        stack_delta(node, delta);
    frame_exact_stack_delta(*node, *delta) <--
        psub(node, dst, _),
        op_register(dst, dst_name),
        if Mreg::x86(*dst_name) == Mreg::SP,
        if let Some(width) = x86_gpr_view_width(dst_name),
        abi_pointer_size(pointer_width),
        if width == *pointer_width,
        stack_delta(node, delta);
    frame_exact_stack_delta(*node, *displacement) <--
        plea(node, dst, memory),
        op_register(dst, dst_name),
        if Mreg::x86(*dst_name) == Mreg::SP,
        if let Some(width) = x86_gpr_view_width(dst_name),
        abi_pointer_size(pointer_width),
        if width == *pointer_width,
        op_indirect(memory, _, base_name, index_name, _, displacement, _),
        if Mreg::x86(*base_name) == Mreg::SP,
        if let Some(base_width) = x86_gpr_view_width(base_name),
        if base_width == *pointer_width,
        if *index_name == "NONE" || index_name.is_empty();

    #[local] relation frame_return_pop_member(Address, Address, i64);
    frame_return_pop_member(*func, *ret, *bytes) <--
        instruction(ret, _, _, "RET", immediate, _, _, _, _, _),
        instr_in_function(ret, func),
        op_immediate(immediate, bytes, _),
        if *bytes >= 0;
    frame_return_pop_member(*func, *ret, 0) <--
        instruction(ret, _, _, "RET", immediate, _, _, _, _, _),
        instr_in_function(ret, func),
        !op_immediate(immediate, _, _);

    #[local] relation frame_callee_pop_conflict(Address);
    frame_callee_pop_conflict(*func) <--
        frame_return_pop_member(func, _, left),
        frame_return_pop_member(func, _, right),
        if left != right;

    #[local] relation frame_exact_callee_pop(Address, i64);
    frame_exact_callee_pop(*func, *bytes) <--
        frame_return_pop_member(func, _, bytes),
        function_has_ltl_body(func),
        !function_has_uncovered_block(func),
        !function_unknown_terminal(func, _),
        !function_unresolved_control(func, _),
        !frame_callee_pop_conflict(func);

    #[local] relation frame_call_local_target(Address, Address);
    frame_call_local_target(*node, callee) <--
        instruction(node, _, _, "CALL", target, _, _, _, _, _),
        op_immediate(target, target_addr, _),
        if let Ok(callee) = u64::try_from(*target_addr),
        instr_in_function(callee, callee);

    #[local] relation frame_call_callee_pop_member(Address, i64);
    frame_call_callee_pop_member(*node, *bytes) <--
        frame_call_local_target(node, callee),
        frame_exact_callee_pop(callee, bytes);

    // A nonzero RET immediate is the only x86-64 evidence which overrides the
    // caller-clean ABI.  A local PLT stub commonly has no ordinary RET body at
    // all; treating that missing summary as an unknown callee-pop poisons a
    // loop backedge after the call and erases otherwise exact frame state.
    #[local] relation frame_call_nonzero_pop_evidence(Address);
    frame_call_nonzero_pop_evidence(*node) <--
        frame_call_local_target(node, callee),
        frame_return_pop_member(callee, _, bytes),
        if *bytes != 0;

    frame_exact_stack_delta(*node, *bytes) <-- frame_call_callee_pop_member(node, bytes);

    // The x86-64 ABIs are caller-clean. A direct nonzero RET-imm fact above
    // overrides that default for unusual hand-written callees. On x86-32,
    // absence of a callee-pop fact does not distinguish cdecl from an
    // unresolved stdcall, so the outgoing state remains unknown rather than
    // assuming zero.
    frame_exact_stack_delta(*node, 0) <--
        instruction(node, _, _, "CALL", _, _, _, _, _, _),
        abi_pointer_size(8),
        !frame_call_nonzero_pop_evidence(node);

    // Raw implicit stack mutators provide a fallback even when Capstone omits
    // an implicit SP reg_def. Any form not admitted above invalidates MUST
    // state rather than silently behaving like a zero delta.
    #[local] relation frame_raw_sp_update(Address);
    frame_raw_sp_update(node) <-- ppush(node, _);
    frame_raw_sp_update(node) <-- ppop(node, _);
    frame_raw_sp_update(*node) <--
        padd(node, dst, _),
        op_register(dst, dst_name),
        if Mreg::x86(*dst_name) == Mreg::SP;
    frame_raw_sp_update(*node) <--
        psub(node, dst, _),
        op_register(dst, dst_name),
        if Mreg::x86(*dst_name) == Mreg::SP;
    frame_raw_sp_update(*node) <--
        plea(node, dst, _),
        op_register(dst, dst_name),
        if Mreg::x86(*dst_name) == Mreg::SP;
    frame_raw_sp_update(*node) <--
        instruction(node, _, _, mnemonic, _, _, _, _, _, _),
        if matches!(
            *mnemonic,
            "ENTER"
                | "LEAVE"
                | "PUSHF"
                | "PUSHFD"
                | "PUSHFQ"
                | "POPF"
                | "POPFD"
                | "POPFQ"
                | "PUSHA"
                | "PUSHAD"
                | "PUSHAW"
                | "PUSHAL"
                | "POPA"
                | "POPAD"
                | "POPAW"
                | "POPAL"
                | "CALL"
        );

    // An instruction which writes SP without a decoder-proven constant delta
    // makes the outgoing coordinate unknown. Absence of an exact transfer is
    // evidence for zero only when the instruction does not define/update SP.
    #[local] relation frame_stack_delta_unknown(Address);
    frame_stack_delta_unknown(*node) <--
        reg_def(node, reg),
        if *reg == Mreg::SP,
        !frame_exact_stack_delta(node, _);
    frame_stack_delta_unknown(*node) <--
        frame_raw_sp_update(node),
        !frame_exact_stack_delta(node, _);
    frame_stack_delta_unknown(*node) <--
        stack_delta(node, _),
        !frame_exact_stack_delta(node, _);

    frame_stack_offset(*func, *entry, Dual(Set::singleton(0))) <--
        reachable_frame_node(func, entry),
        if func == entry;

    frame_stack_offset(*func, *succ, Dual(shift_stack_offsets(&offsets.0, *delta))) <--
        frame_stack_offset(func, node, offsets),
        frame_cfg_step(node, succ),
        reachable_frame_node(func, node),
        reachable_frame_node(func, succ),
        !frame_stack_probe_back_edge(func, node, succ),
        !frame_stack_probe_exit_edge(func, node, succ, _),
        frame_exact_stack_delta(node, delta);

    frame_stack_offset(*func, *succ, Dual(offsets.0.clone())) <--
        frame_stack_offset(func, node, offsets),
        frame_cfg_step(node, succ),
        reachable_frame_node(func, node),
        reachable_frame_node(func, succ),
        !frame_stack_probe_back_edge(func, node, succ),
        !frame_stack_probe_exit_edge(func, node, succ, _),
        !frame_stack_delta_unknown(node),
        !frame_exact_stack_delta(node, _);

    // Keep unknown explicit. Dropping this predecessor entirely would let a
    // known sibling arm become false MUST evidence at a later join.
    frame_stack_offset(*func, *succ, Dual(Set::<i64>::default())) <--
        frame_stack_offset(func, node, _),
        frame_cfg_step(node, succ),
        reachable_frame_node(func, node),
        reachable_frame_node(func, succ),
        !frame_stack_probe_back_edge(func, node, succ),
        !frame_stack_probe_exit_edge(func, node, succ, _),
        frame_stack_delta_unknown(node);

    frame_stack_offset(*func, *succ, Dual(shift_stack_offsets(&offsets.0, *delta))) <--
        frame_stack_offset(func, node, offsets),
        frame_stack_probe_exit_edge(func, node, succ, delta),
        reachable_frame_node(func, node),
        reachable_frame_node(func, succ);

    // A dynamic `and sp, -alignment` before a fixed probe destroys the
    // entry-relative coordinate, correctly making frame_stack_offset unknown.
    // It does not destroy local coordinates after the alignment.  Restart a
    // separate MUST lattice at the certified probe target and use it only for
    // post-probe frame shifts; it is never published as an entry-SP offset.
    #[local] lattice probe_relative_stack_offset(Address, Address, Dual<Set<i64>>);
    probe_relative_stack_offset(*func, *target_def, Dual(Set::singleton(0))) <--
        fixed_stack_probe(func, target_def, _, _, _, _, _, _);

    probe_relative_stack_offset(*func, *succ, Dual(shift_stack_offsets(&offsets.0, *delta))) <--
        probe_relative_stack_offset(func, node, offsets),
        frame_cfg_step(node, succ),
        reachable_frame_node(func, node),
        reachable_frame_node(func, succ),
        !frame_stack_probe_back_edge(func, node, succ),
        !frame_stack_probe_exit_edge(func, node, succ, _),
        frame_exact_stack_delta(node, delta);

    probe_relative_stack_offset(*func, *succ, Dual(offsets.0.clone())) <--
        probe_relative_stack_offset(func, node, offsets),
        frame_cfg_step(node, succ),
        reachable_frame_node(func, node),
        reachable_frame_node(func, succ),
        !frame_stack_probe_back_edge(func, node, succ),
        !frame_stack_probe_exit_edge(func, node, succ, _),
        !frame_stack_delta_unknown(node),
        !frame_exact_stack_delta(node, _);

    probe_relative_stack_offset(*func, *succ, Dual(Set::<i64>::default())) <--
        probe_relative_stack_offset(func, node, _),
        frame_cfg_step(node, succ),
        reachable_frame_node(func, node),
        reachable_frame_node(func, succ),
        !frame_stack_probe_back_edge(func, node, succ),
        !frame_stack_probe_exit_edge(func, node, succ, _),
        frame_stack_delta_unknown(node);

    probe_relative_stack_offset(*func, *succ, Dual(shift_stack_offsets(&offsets.0, *delta))) <--
        probe_relative_stack_offset(func, node, offsets),
        frame_stack_probe_exit_edge(func, node, succ, delta),
        reachable_frame_node(func, node),
        reachable_frame_node(func, succ);
}

pub struct FrameCoordinatePass;

impl IRPass for FrameCoordinatePass {
    fn name(&self) -> &'static str {
        "frame_coordinates"
    }

    fn run(&self, db: &mut DecompileDB) {
        let mut prog = FrameCoordinatePassProgram::default();
        prog.swap_db_fields(db);
        prog.run();

        // Read each final lattice row exactly once. An empty/multi-member Set
        // is ambiguous and deliberately publishes no exact shift.
        let mut state_points = std::collections::BTreeSet::new();
        let mut exact_offsets = std::collections::BTreeMap::new();
        let probe_body_points: std::collections::BTreeSet<_> =
            prog.frame_stack_probe_body_node.iter().copied().collect();
        for row in prog.frame_stack_offset.iter() {
            let row = row
                .read()
                .expect("frame-coordinate lattice row lock poisoned");
            state_points.insert((row.0, row.1));
            if !probe_body_points.contains(&(row.0, row.1)) {
                if let Some(offset) = exact_stack_offset(&row.2 .0) {
                    exact_offsets.insert((row.0, row.1), offset);
                }
            }
        }
        let mut probe_state_points = std::collections::BTreeSet::new();
        let mut probe_exact_offsets = std::collections::BTreeMap::new();
        for row in prog.probe_relative_stack_offset.iter() {
            let row = row
                .read()
                .expect("probe-relative frame-coordinate lattice row lock poisoned");
            probe_state_points.insert((row.0, row.1));
            if !probe_body_points.contains(&(row.0, row.1)) {
                if let Some(offset) = exact_stack_offset(&row.2 .0) {
                    probe_exact_offsets.insert((row.0, row.1), offset);
                }
            }
        }

        let call_sites: std::collections::BTreeSet<Address> = prog
            .instruction
            .iter()
            .filter_map(|(node, _, _, mnemonic, _, _, _, _, _, _)| {
                (*mnemonic == "CALL").then_some(*node)
            })
            .collect();
        let calls_by_function: std::collections::BTreeSet<(Address, Address)> = prog
            .instr_in_function
            .iter()
            .filter_map(|(node, func)| {
                (call_sites.contains(node) && state_points.contains(&(*func, *node)))
                    .then_some((*func, *node))
            })
            .collect();

        // A reachable call with ambiguous stack state makes the inferred body
        // baseline ambiguous for the entire function. Never borrow another
        // call's height and turn the missing state into a synthetic zero shift.
        let invalid_functions: std::collections::BTreeSet<Address> = calls_by_function
            .iter()
            .filter_map(|(func, call)| {
                (!exact_offsets.contains_key(&(*func, *call))).then_some(*func)
            })
            .collect();
        let mut frame_origins = std::collections::BTreeMap::<Address, i64>::new();
        for (func, call) in calls_by_function {
            let Some(offset) = exact_offsets.get(&(func, call)).copied() else {
                continue;
            };
            frame_origins
                .entry(func)
                .and_modify(|origin| *origin = (*origin).max(offset))
                .or_insert(offset);
        }

        let settled_entry_offsets: Vec<_> = exact_offsets
            .iter()
            .map(|(&(func, node), &offset)| (func, node, offset))
            .collect();
        let mut settled = Vec::new();
        for ((func, node), offset) in exact_offsets {
            if invalid_functions.contains(&func) {
                continue;
            }
            let depth = if let Some(origin) = frame_origins.get(&func) {
                // A call-derived origin is the settled body baseline.  Points
                // above it are pre-allocation/post-epilogue coordinates, not a
                // zero-depth spelling of body storage.  Omitting them keeps two
                // physically distinct RSP-relative bytes from sharing one exact
                // frame coordinate.
                if offset > *origin {
                    continue;
                }
                origin.saturating_sub(offset)
            } else {
                0
            };
            settled.push((func, node, depth));
        }

        let probe_calls_by_function: std::collections::BTreeSet<(Address, Address)> = prog
            .instr_in_function
            .iter()
            .filter_map(|(node, func)| {
                (call_sites.contains(node) && probe_state_points.contains(&(*func, *node)))
                    .then_some((*func, *node))
            })
            .collect();
        let probe_invalid_functions: std::collections::BTreeSet<Address> = probe_calls_by_function
            .iter()
            .filter_map(|(func, call)| {
                (!probe_exact_offsets.contains_key(&(*func, *call))).then_some(*func)
            })
            .collect();
        let mut probe_frame_origins = std::collections::BTreeMap::<Address, i64>::new();
        for (func, call) in probe_calls_by_function {
            let Some(offset) = probe_exact_offsets.get(&(func, call)).copied() else {
                continue;
            };
            probe_frame_origins
                .entry(func)
                .and_modify(|origin| *origin = (*origin).max(offset))
                .or_insert(offset);
        }
        for ((func, node), offset) in probe_exact_offsets {
            if probe_invalid_functions.contains(&func) {
                continue;
            }
            let depth = if let Some(origin) = probe_frame_origins.get(&func) {
                if offset > *origin {
                    continue;
                }
                origin.saturating_sub(offset)
            } else {
                0
            };
            settled.push((func, node, depth));
        }

        // Entry-relative and probe-relative coordinates should normalize to the
        // same local depth when both are available.  Any disagreement is a
        // conflict, not a choice: publish only singleton point depths.
        let mut settled_candidates =
            std::collections::BTreeMap::<(Address, Address), std::collections::BTreeSet<i64>>::new(
            );
        for (func, node, depth) in settled {
            settled_candidates
                .entry((func, node))
                .or_default()
                .insert(depth);
        }
        let mut settled: Vec<_> = settled_candidates
            .into_iter()
            .filter_map(|((func, node), depths)| {
                (depths.len() == 1)
                    .then(|| {
                        depths
                            .iter()
                            .next()
                            .copied()
                            .map(|depth| (func, node, depth))
                    })
                    .flatten()
            })
            .collect();
        settled.sort_unstable();

        let summarized_probes: std::collections::BTreeSet<_> = prog
            .fixed_stack_probe
            .iter()
            .map(|row| (row.0, row.1, row.2, row.6))
            .collect();
        if !summarized_probes.is_empty() {
            eprintln!(
                "[frame-coordinates] fixed-stack-probe-certificates={} summarized-exits={}",
                summarized_probes.len(),
                summarized_probes
                    .iter()
                    .map(|(func, _, _, exit)| (*func, *exit))
                    .collect::<std::collections::BTreeSet<_>>()
                    .len(),
            );
        }

        if db.measure_rule_times {
            let pass_name = "FrameCoordinatePassProgram".to_string();
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

        prog.swap_db_fields(db);
        let entry_relation = ascent::boxcar::Vec::new();
        for fact in settled_entry_offsets {
            entry_relation.push(fact);
        }
        db.rel_set("settled_sp_entry_offset", entry_relation);
        let relation = ascent::boxcar::Vec::new();
        for fact in settled {
            relation.push(fact);
        }
        db.rel_set("settled_sp_frame_shift", relation);
    }

    fn inputs(&self) -> &'static [&'static str] {
        FrameCoordinatePassProgram::inputs_only()
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "settled_sp_entry_offset",
            "settled_sp_frame_shift",
            "fixed_stack_probe_allocation",
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::FrameCoordinatePass;
    use crate::decompile::elevator::DecompileDB;
    use crate::decompile::passes::pass::IRPass;
    use crate::mreg::Mreg;
    use ascent::lattice::set::Set;

    #[test]
    fn final_stack_state_rejects_forward_ambiguity() {
        let func = 0x1000_u64;
        let entry = func;
        let left = 0x3010_u64;
        let right = 0x7010_u64;
        let join = 0x2010_u64;
        let mut db = DecompileDB::default();
        db.rel_push("abi_pointer_size", (8_i64,));

        for node in [entry, left, right, join] {
            db.rel_push("instr_in_function", (node, func));
            db.rel_push("code_in_block", (node, node));
        }
        for (block, dominators) in [
            (entry, vec![entry]),
            (left, vec![entry, left]),
            (right, vec![entry, right]),
            (join, vec![entry, join]),
        ] {
            db.rel_push(
                "settled_block_dom_set",
                (func, block, Set(dominators.into_iter().collect())),
            );
        }
        for edge in [
            (entry, left, "branch"),
            (entry, right, "fallthrough"),
            (left, join, "branch"),
            (right, join, "branch"),
        ] {
            db.rel_push("ddisasm_cfg_edge", edge);
        }
        db.rel_push("stack_delta", (left, -8_i64));
        db.rel_push("psub", (left, "left_rsp", "left_size"));
        db.rel_push("op_register", ("left_rsp", "RSP"));

        FrameCoordinatePass.run(&mut db);

        let shifts: std::collections::BTreeSet<_> = db
            .rel_iter::<(u64, u64, i64)>("settled_sp_frame_shift")
            .copied()
            .collect();
        assert!(!shifts.iter().any(|(_, node, _)| *node == join));
    }

    #[test]
    fn nonzero_loop_carried_stack_delta_invalidates_the_header() {
        let func = 0x2000_u64;
        let entry = func;
        let header = 0x7010_u64;
        let latch = 0x3010_u64;
        let exit = 0x5010_u64;
        let mut db = DecompileDB::default();
        db.rel_push("abi_pointer_size", (8_i64,));
        for node in [entry, header, latch, exit] {
            db.rel_push("instr_in_function", (node, func));
            db.rel_push("code_in_block", (node, node));
        }
        for (block, dominators) in [
            (entry, vec![entry]),
            (header, vec![entry, header]),
            (latch, vec![entry, header, latch]),
            (exit, vec![entry, header, latch, exit]),
        ] {
            db.rel_push(
                "settled_block_dom_set",
                (func, block, Set(dominators.into_iter().collect())),
            );
        }
        for edge in [
            (entry, header, "fallthrough"),
            (header, latch, "fallthrough"),
            (latch, header, "branch"),
            (latch, exit, "fallthrough"),
        ] {
            db.rel_push("ddisasm_cfg_edge", edge);
        }
        db.rel_push("stack_delta", (latch, -4096_i64));
        db.rel_push("psub", (latch, "latch_rsp", "probe_size"));
        db.rel_push("op_register", ("latch_rsp", "RSP"));

        FrameCoordinatePass.run(&mut db);

        let shifts: std::collections::BTreeSet<_> = db
            .rel_iter::<(u64, u64, i64)>("settled_sp_frame_shift")
            .copied()
            .collect();
        assert!(!shifts.iter().any(|(_, node, _)| *node == header));
        assert!(!shifts.iter().any(|(_, node, _)| *node == exit));
    }

    #[test]
    fn fixed_page_probe_recovers_local_state_after_dynamic_stack_alignment() {
        let func = 0x8000_u64;
        let align = 0x8008_u64;
        let target = 0x8010_u64;
        let header = 0x8020_u64;
        let touch = 0x8030_u64;
        let cmp = 0x8040_u64;
        let latch = 0x8050_u64;
        let exit = 0x8060_u64;
        let tail_alloc = 0x8070_u64;
        let buffer_lea = 0x8080_u64;
        let call = 0x8090_u64;
        let end = 0x80a0_u64;
        let entry_block = func;
        let probe_block = header;
        let exit_block = exit;
        let mut db = DecompileDB::default();
        db.rel_push("abi_pointer_size", (8_i64,));

        for (node, block) in [
            (func, entry_block),
            (align, entry_block),
            (target, entry_block),
            (header, probe_block),
            (touch, probe_block),
            (cmp, probe_block),
            (latch, probe_block),
            (exit, exit_block),
            (tail_alloc, exit_block),
            (buffer_lea, exit_block),
            (call, exit_block),
            (end, exit_block),
        ] {
            db.rel_push("instr_in_function", (node, func));
            db.rel_push("code_in_block", (node, block));
        }
        for (block, dominators) in [
            (entry_block, vec![entry_block]),
            (probe_block, vec![entry_block, probe_block]),
            (exit_block, vec![entry_block, probe_block, exit_block]),
        ] {
            db.rel_push(
                "settled_block_dom_set",
                (func, block, Set(dominators.into_iter().collect())),
            );
        }

        for edge in [
            (func, align),
            (align, target),
            (target, header),
            (header, touch),
            (touch, cmp),
            (cmp, latch),
            (exit, tail_alloc),
            (tail_alloc, buffer_lea),
            (buffer_lea, call),
            (call, end),
        ] {
            db.rel_push("next", edge);
        }
        for edge in [
            (target, header, "fallthrough"),
            (latch, header, "branch"),
            (latch, exit, "fallthrough"),
        ] {
            db.rel_push("ddisasm_cfg_edge", edge);
        }

        db.rel_push("ppush", (func, "saved_reg"));
        // Models `and rsp, -64`: entry-relative state must remain unknown, but
        // the certified probe target establishes a new local-frame origin.
        db.rel_push("reg_def", (align, Mreg::SP));
        db.rel_push("plea", (target, "target_dst", "target_mem"));
        db.rel_push("op_register", ("target_dst", "R11"));
        db.rel_push(
            "op_indirect",
            ("target_mem", "", "RSP", "NONE", 1_i64, -16384_i64, 8_usize),
        );
        db.rel_push("psub", (header, "probe_rsp", "probe_page"));
        db.rel_push("op_register", ("probe_rsp", "RSP"));
        db.rel_push("op_immediate", ("probe_page", 4096_i64, 8_usize));
        db.rel_push("stack_delta", (header, -4096_i64));
        db.rel_push("decoded_stack_write_bytes", (touch, "RSP", 0_i64, 8_usize));
        db.rel_push("pcmp", (cmp, "cmp_rsp", "cmp_target"));
        db.rel_push("op_register", ("cmp_rsp", "RSP"));
        db.rel_push("op_register", ("cmp_target", "R11"));

        db.rel_push("psub", (tail_alloc, "tail_rsp", "tail_size"));
        db.rel_push("op_register", ("tail_rsp", "RSP"));
        db.rel_push("stack_delta", (tail_alloc, -32_i64));
        db.rel_push(
            "instruction",
            (
                call, 5_usize, "", "CALL", "callee", "", "", "", 0_usize, 0_usize,
            ),
        );

        FrameCoordinatePass.run(&mut db);

        let entry_offsets: std::collections::BTreeSet<_> = db
            .rel_iter::<(u64, u64, i64)>("settled_sp_entry_offset")
            .copied()
            .collect();
        assert!(!entry_offsets
            .iter()
            .any(|(owner, node, _)| *owner == func && [buffer_lea, call].contains(node)));
        for probe_node in [header, touch, cmp, latch] {
            assert!(!entry_offsets
                .iter()
                .any(|(owner, node, _)| (*owner, *node) == (func, probe_node)));
        }

        let shifts: std::collections::BTreeSet<_> = db
            .rel_iter::<(u64, u64, i64)>("settled_sp_frame_shift")
            .copied()
            .collect();
        assert!(shifts.contains(&(func, buffer_lea, 0)));
        assert!(shifts.contains(&(func, call, 0)));
        assert!(!shifts.iter().any(|(_, node, _)| *node == target));
        assert!(db
            .rel_iter::<(u64, i64)>("fixed_stack_probe_allocation")
            .any(|fact| fact == &(func, 16384)));
    }

    #[test]
    fn unknown_stack_definition_contaminates_a_forward_join() {
        let func = 0x4000_u64;
        let entry = func;
        let known = 0x4010_u64;
        let unknown = 0x4020_u64;
        let join = 0x4030_u64;
        let mut db = DecompileDB::default();

        for node in [entry, known, unknown, join] {
            db.rel_push("instr_in_function", (node, func));
            db.rel_push("code_in_block", (node, node));
        }
        for (block, dominators) in [
            (entry, vec![entry]),
            (known, vec![entry, known]),
            (unknown, vec![entry, unknown]),
            (join, vec![entry, join]),
        ] {
            db.rel_push(
                "settled_block_dom_set",
                (func, block, Set(dominators.into_iter().collect())),
            );
        }
        for edge in [
            (entry, known, "branch"),
            (entry, unknown, "fallthrough"),
            (known, join, "branch"),
            (unknown, join, "branch"),
        ] {
            db.rel_push("ddisasm_cfg_edge", edge);
        }
        // No stack_delta accompanies this SP definition, so the unknown arm
        // must remain explicit rather than disappearing from the join.
        db.rel_push("reg_def", (unknown, Mreg::SP));

        FrameCoordinatePass.run(&mut db);

        let shifts: std::collections::BTreeSet<_> = db
            .rel_iter::<(u64, u64, i64)>("settled_sp_frame_shift")
            .copied()
            .collect();
        assert!(!shifts.iter().any(|(_, node, _)| *node == join));
    }

    #[test]
    fn ordinary_push_has_one_exact_pointer_sized_stack_delta() {
        let mut db = DecompileDB::default();
        let func = 0x4800_u64;
        let push = 0x4810_u64;
        let call = 0x4820_u64;
        let end = 0x4830_u64;
        db.rel_push("abi_pointer_size", (8_i64,));
        for node in [func, push, call, end] {
            db.rel_push("instr_in_function", (node, func));
            db.rel_push("code_in_block", (node, func));
        }
        db.rel_push("settled_block_dom_set", (func, func, Set::singleton(func)));
        db.rel_push("next", (func, push));
        db.rel_push("next", (push, call));
        db.rel_push("next", (call, end));
        db.rel_push("ppush", (push, "argument"));
        db.rel_push(
            "instruction",
            (
                call, 1_usize, "", "CALL", "target", "", "", "", 0_usize, 0_usize,
            ),
        );

        FrameCoordinatePass.run(&mut db);

        let entries: std::collections::BTreeSet<_> = db
            .rel_iter::<(u64, u64, i64)>("settled_sp_entry_offset")
            .copied()
            .collect();
        assert!(entries.contains(&(func, push, 0)));
        assert!(entries.contains(&(func, call, -8)));
        assert!(entries.contains(&(func, end, -8)));
    }

    #[test]
    fn pop_rsp_and_leave_invalidate_but_call_preserves_coordinates() {
        let mut db = DecompileDB::default();
        let pop_func = 0x5000_u64;
        let pop_rsp = 0x5010_u64;
        let after_pop = 0x5020_u64;
        let leave_func = 0x6000_u64;
        let leave = 0x6010_u64;
        let after_leave = 0x6020_u64;
        let call_func = 0x7000_u64;
        let call = 0x7010_u64;
        let after_call = 0x7020_u64;
        db.rel_push("abi_pointer_size", (8_i64,));

        for (func, nodes) in [
            (pop_func, vec![pop_func, pop_rsp, after_pop]),
            (leave_func, vec![leave_func, leave, after_leave]),
            (call_func, vec![call_func, call, after_call]),
        ] {
            for node in nodes {
                db.rel_push("instr_in_function", (node, func));
                db.rel_push("code_in_block", (node, node));
                db.rel_push("settled_block_dom_set", (func, node, Set::singleton(node)));
            }
        }
        for edge in [
            (pop_func, pop_rsp, "fallthrough"),
            (pop_rsp, after_pop, "fallthrough"),
            (leave_func, leave, "fallthrough"),
            (leave, after_leave, "fallthrough"),
            (call_func, call, "fallthrough"),
            (call, after_call, "fallthrough"),
        ] {
            db.rel_push("ddisasm_cfg_edge", edge);
        }

        db.rel_push("ppop", (pop_rsp, "pop_rsp"));
        db.rel_push("op_register", ("pop_rsp", "RSP"));
        db.rel_push("stack_delta", (pop_rsp, 8_i64));
        db.rel_push("reg_def", (pop_rsp, Mreg::SP));
        db.rel_push(
            "instruction",
            (
                leave, 1_usize, "", "LEAVE", "NONE", "NONE", "NONE", "NONE", 0_usize, 0_usize,
            ),
        );
        // Capstone reports CALL's transient hardware SP write, but the
        // fallthrough state is restored by the callee's return.
        db.rel_push(
            "instruction",
            (
                call, 1_usize, "", "CALL", "NONE", "NONE", "NONE", "NONE", 0_usize, 0_usize,
            ),
        );
        db.rel_push("reg_def", (call, Mreg::SP));

        FrameCoordinatePass.run(&mut db);

        let shifts: std::collections::BTreeSet<_> = db
            .rel_iter::<(u64, u64, i64)>("settled_sp_frame_shift")
            .copied()
            .collect();
        assert!(!shifts.iter().any(|(_, node, _)| *node == after_pop));
        assert!(!shifts.iter().any(|(_, node, _)| *node == after_leave));
        assert!(shifts.contains(&(call_func, after_call, 0)));
    }

    #[test]
    fn mixed_plain_and_callee_pop_returns_make_call_state_unknown() {
        let caller = 0x8000_u64;
        let call = 0x8010_u64;
        let after_call = 0x8020_u64;
        let callee = 0x9000_u64;
        let plain_ret = 0x9010_u64;
        let pop_ret = 0x9020_u64;
        let mut db = DecompileDB::default();
        db.rel_push("abi_pointer_size", (8_i64,));
        for node in [caller, call, after_call] {
            db.rel_push("instr_in_function", (node, caller));
            db.rel_push("code_in_block", (node, node));
            db.rel_push(
                "settled_block_dom_set",
                (caller, node, Set::singleton(node)),
            );
        }
        db.rel_push("ddisasm_cfg_edge", (caller, call, "fallthrough"));
        db.rel_push("ddisasm_cfg_edge", (call, after_call, "fallthrough"));
        db.rel_push("instr_in_function", (callee, callee));
        db.rel_push("instr_in_function", (plain_ret, callee));
        db.rel_push("instr_in_function", (pop_ret, callee));
        db.rel_push("function_has_ltl_body", (callee,));
        db.rel_push(
            "instruction",
            (
                call, 5_usize, "", "CALL", "callee", "", "", "", 0_usize, 0_usize,
            ),
        );
        db.rel_push("op_immediate", ("callee", callee as i64, 8_usize));
        db.rel_push(
            "instruction",
            (
                plain_ret,
                1_usize,
                "",
                "RET",
                "plain_ret",
                "",
                "",
                "",
                0_usize,
                0_usize,
            ),
        );
        db.rel_push(
            "instruction",
            (
                pop_ret,
                3_usize,
                "",
                "RET",
                "pop_bytes",
                "",
                "",
                "",
                0_usize,
                0_usize,
            ),
        );
        db.rel_push("op_immediate", ("pop_bytes", 8_i64, 2_usize));

        FrameCoordinatePass.run(&mut db);

        assert!(!db
            .rel_iter::<(u64, u64, i64)>("settled_sp_entry_offset")
            .any(|(func, node, _)| *func == caller && *node == after_call));
    }

    #[test]
    fn local_plt_style_call_is_caller_clean_on_x86_64() {
        let caller = 0xa100_u64;
        let call = 0xa110_u64;
        let after_call = 0xa120_u64;
        let local_stub = 0xb100_u64;
        let mut db = DecompileDB::default();
        db.rel_push("abi_pointer_size", (8_i64,));

        for node in [caller, call, after_call] {
            db.rel_push("instr_in_function", (node, caller));
            db.rel_push("code_in_block", (node, node));
            db.rel_push(
                "settled_block_dom_set",
                (caller, node, Set::singleton(node)),
            );
        }
        db.rel_push("ddisasm_cfg_edge", (caller, call, "fallthrough"));
        db.rel_push("ddisasm_cfg_edge", (call, after_call, "fallthrough"));
        db.rel_push("instr_in_function", (local_stub, local_stub));
        db.rel_push(
            "instruction",
            (
                call,
                5_usize,
                "",
                "CALL",
                "local_stub",
                "",
                "",
                "",
                0_usize,
                0_usize,
            ),
        );
        db.rel_push("op_immediate", ("local_stub", local_stub as i64, 8_usize));

        FrameCoordinatePass.run(&mut db);

        assert!(db
            .rel_iter::<(u64, u64, i64)>("settled_sp_entry_offset")
            .any(|fact| *fact == (caller, after_call, 0)));
        assert!(db
            .rel_iter::<(u64, u64, i64)>("settled_sp_frame_shift")
            .any(|fact| *fact == (caller, after_call, 0)));
    }

    #[test]
    fn preallocation_points_do_not_borrow_call_body_baseline() {
        let func = 0xa000_u64;
        let before_alloc = 0xa008_u64;
        let alloc = 0xa010_u64;
        let after_alloc = 0xa018_u64;
        let call = 0xa020_u64;
        let after_call = 0xa028_u64;
        let mut db = DecompileDB::default();
        db.rel_push("abi_pointer_size", (8_i64,));

        for node in [func, before_alloc, alloc, after_alloc, call, after_call] {
            db.rel_push("instr_in_function", (node, func));
            db.rel_push("code_in_block", (node, node));
            db.rel_push("settled_block_dom_set", (func, node, Set::singleton(node)));
        }
        for (src, dst) in [
            (func, before_alloc),
            (before_alloc, alloc),
            (alloc, after_alloc),
            (after_alloc, call),
            (call, after_call),
        ] {
            db.rel_push("ddisasm_cfg_edge", (src, dst, "fallthrough"));
        }
        db.rel_push("stack_delta", (alloc, -32_i64));
        db.rel_push("psub", (alloc, "alloc_rsp", "alloc_size"));
        db.rel_push("op_register", ("alloc_rsp", "RSP"));
        db.rel_push(
            "instruction",
            (
                call, 5_usize, "", "CALL", "callee", "", "", "", 0_usize, 0_usize,
            ),
        );

        FrameCoordinatePass.run(&mut db);

        let shifts: std::collections::BTreeSet<_> = db
            .rel_iter::<(u64, u64, i64)>("settled_sp_frame_shift")
            .copied()
            .collect();
        assert!(!shifts.iter().any(|(_, node, _)| *node == before_alloc));
        assert!(!shifts.iter().any(|(_, node, _)| *node == alloc));
        assert!(shifts.contains(&(func, after_alloc, 0)));
        assert!(shifts.contains(&(func, call, 0)));
        assert!(shifts.contains(&(func, after_call, 0)));
    }
}
