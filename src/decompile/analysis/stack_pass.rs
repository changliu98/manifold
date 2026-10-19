use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::{declare_io_from, run_pass};

use crate::mreg::Mreg;
use crate::x86::types::*;
use ascent::ascent_par;

// ddisasm-style stack def-use analysis: computes def-use chains for stack variables (BaseReg, Offset) with backward propagation that tracks offset/base-register transformations through stack adjustments and moves. Reference: ddisasm use_def_analysis.dl (StackVarDefUse).

ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct StackAnalysisProgram;

    // Input relations
    relation code_in_block(Address, Address);
    relation block_boundaries(Address, Address, Address);
    relation next(Address, Address);
    relation reg_def(Address, Mreg);
    relation stack_def(Address, Symbol, i64);
    relation stack_use(Address, Symbol, i64);
    relation trim_instruction(Address);
    relation ddisasm_cfg_edge(Address, Address, &'static str);
    relation known_noreturn_call_site(Address);
    relation block_in_function(Address, Address);
    relation adjusts_stack(Address, Symbol, i64);
    relation stack_base_move(Address, Symbol, Symbol);
    // Bytes SP sits below the frame's coordinate origin at an instruction, from
    // asm_pass; present only for the instructions inside an outgoing-argument
    // window.  See the settling rule at the bottom of this program.
    relation sp_window_depth(Address, i64);

    // Block topology

    #[local] relation block_instruction_next(Address, Address, Address);
    block_instruction_next(block, before, after) <--
        code_in_block(before, block),
        next(before, after),
        code_in_block(after, block);

    #[local] relation block_last_insn(Address, Address);
    block_last_insn(block_start, last_insn) <--
        block_boundaries(block_start, last_insn, _);

    #[local] relation block_next(Address, Address);
    block_next(src_block, dst) <--
        ddisasm_cfg_edge(src, dst, edge_type),
        if *edge_type != "call" && *edge_type != "indirect" && *edge_type != "indirect_call",
        !known_noreturn_call_site(src),
        code_in_block(src, src_block),
        block_in_function(src_block, func),
        block_in_function(dst, func);

    // Stack modification tracking

    #[local] relation adjusts_stack_in_block(Address, Address, Symbol, i64);
    adjusts_stack_in_block(block, ea, reg, offset) <--
        adjusts_stack(ea, reg, offset),
        code_in_block(ea, block);

    #[local] relation stack_base_reg_move(Address, Address, Symbol, Symbol);
    stack_base_reg_move(block, ea, src, dst) <--
        stack_base_move(ea, src, dst),
        code_in_block(ea, block);

    // A CALL's reg_def(SP) is undone by the callee's RET, so it must not count as a stack-base redefinition (kills spill/reload liveness).
    #[local] relation is_call_insn(Address);
    is_call_insn(addr) <-- ddisasm_cfg_edge(addr, _, "call");
    is_call_insn(addr) <-- ddisasm_cfg_edge(addr, _, "indirect_call");

    // Base register was redefined (not just adjusted) at this address
    #[local] relation base_reg_def(Address, Symbol);
    base_reg_def(addr, "RSP") <--
        reg_def(addr, mreg),
        if *mreg == Mreg::SP,
        !trim_instruction(addr),
        !is_call_insn(addr);
    base_reg_def(addr, "RBP") <--
        reg_def(addr, mreg),
        if *mreg == Mreg::BP,
        !trim_instruction(addr);

    // Block has stack modifications for a given base register
    #[local] relation block_has_stack_mod_for(Address, Symbol);
    block_has_stack_mod_for(block, base) <-- adjusts_stack_in_block(block, _, base, _);
    block_has_stack_mod_for(block, base) <-- stack_base_reg_move(block, _, _, base);

    #[local] relation base_reg_def_in_block(Address, Symbol);
    base_reg_def_in_block(block, base) <--
        base_reg_def(ea, base),
        code_in_block(ea, block);

    // def/used helpers

    #[local] relation defined_in_block(Address, Symbol, i64);
    defined_in_block(block, base, ofs) <--
        stack_def(ea, base, ofs),
        code_in_block(ea, block);

    #[local] relation used_in_block(Address, Address, Symbol, i64);
    used_in_block(block, ea, base, ofs) <--
        stack_use(ea, base, ofs),
        code_in_block(ea, block);

    #[local] relation ref_in_block(Address, Symbol, i64);
    ref_in_block(block, base, ofs) <-- defined_in_block(block, base, ofs);
    ref_in_block(block, base, ofs) <-- used_in_block(block, _, base, ofs);

    // block_last_def: last definition of [base, ofs] visible at each instruction within a block

    #[local] relation block_last_def(Address, Address, Symbol, i64);

    block_last_def(next_addr, ea, base, ofs) <--
        stack_def(ea, base, ofs),
        next(ea, next_addr),
        code_in_block(ea, blk),
        code_in_block(next_addr, blk);

    block_last_def(next_addr, def_addr, base, ofs) <--
        block_last_def(ea, def_addr, base, ofs),
        !stack_def(ea, base, ofs),        // not redefined here
        !base_reg_def(ea, base),          // base reg not clobbered (ea_propagates_def)
        next(ea, next_addr),
        code_in_block(ea, blk),
        code_in_block(next_addr, blk);

    // last_def_in_block: summary of last def visible at the end of each block

    #[local] relation last_def_in_block(Address, Address, Symbol, i64);

    last_def_in_block(block, last_insn, base, ofs) <--
        block_last_insn(block, last_insn),
        stack_def(last_insn, base, ofs);

    last_def_in_block(block, def_addr, base, ofs) <--
        block_last_insn(block, last_insn),
        block_last_def(last_insn, def_addr, base, ofs),
        !stack_def(last_insn, base, ofs),
        !base_reg_def(last_insn, base);

    // live_var_def: a def live at end of its block, eligible for inter-block use pairing

    #[local] relation live_var_def(Address, Symbol, i64, Address);

    live_var_def(block, base, ofs, def_addr) <--
        last_def_in_block(block, def_addr, base, ofs);

    // live_var_used: a use with no intra-block def, starting backward inter-block search. Schema: (Block, LiveBase, LiveOfs, UsedBase, UsedOfs, EA_used, Moves)

    #[local] relation live_var_used(Address, Symbol, i64, Symbol, i64, Address, u32);

    // Base case: used in block with no preceding intra-block def, only for blocks without stack modifications for this base register (blocks with mods use live_var_used_in_block instead).
    live_var_used(block, base, ofs, base, ofs, ea_used, 0) <--
        used_in_block(block, ea_used, base, ofs),
        !block_last_def(ea_used, _, base, ofs),
        !block_has_stack_mod_for(block, base);

    // live_var_used_in_block: per-instruction backward propagation within a block, tracking offset transformations through stack adjustments and base-register moves. Schema: (Block, EA, LiveBase, LiveOfs, UsedBase, UsedOfs, EA_used, Moves)

    #[local] relation live_var_used_in_block(Address, Address, Symbol, i64, Symbol, i64, Address, u32);

    // Moves limit: max blocks with stack modifications a live var can traverse (ddisasm uses 2; prevents infinite loops in pathological CFGs).
    #[local] relation moves_limit(u32);
    moves_limit(2);

    // Base case: a use within this block
    live_var_used_in_block(block, ea_used, base, ofs, base, ofs, ea_used, 0) <--
        used_in_block(block, ea_used, base, ofs);

    // Inter-block entry into per-instruction traversal: when live_var_at_block_end reaches a block with stack mods, enters backward traversal at last instruction (three cases based on last instruction's effect)

    // Entry case 1: last instruction adjusts stack -> transform offset
    live_var_used_in_block(block, last_ea, base, ofs + adj, used_base, used_ofs, ea_used, moves + 1) <--
        block_has_stack_mod_for(block, base),
        live_var_at_block_end(block, use_block, base, ofs),
        live_var_used(use_block, base, ofs, used_base, used_ofs, ea_used, moves),
        moves_limit(mlim),
        if *moves <= *mlim,
        block_last_insn(block, last_ea),
        adjusts_stack_in_block(_, last_ea, base, adj),
        !stack_def(last_ea, base, ofs),
        if *base != "RSP" || ofs + adj >= 0;

    // Entry case 2: last instruction moves base register -> rename
    live_var_used_in_block(block, last_ea, src_base, ofs, used_base, used_ofs, ea_used, moves + 1) <--
        block_has_stack_mod_for(block, dst_base),
        live_var_at_block_end(block, use_block, dst_base, ofs),
        live_var_used(use_block, dst_base, ofs, used_base, used_ofs, ea_used, moves),
        moves_limit(mlim),
        if *moves <= *mlim,
        block_last_insn(block, last_ea),
        stack_base_reg_move(_, last_ea, src_base, dst_base);

    // Entry case 3: last instruction is neutral -> propagate as-is
    live_var_used_in_block(block, last_ea, base, ofs, used_base, used_ofs, ea_used, moves + 1) <--
        block_has_stack_mod_for(block, base),
        live_var_at_block_end(block, use_block, base, ofs),
        live_var_used(use_block, base, ofs, used_base, used_ofs, ea_used, moves),
        moves_limit(mlim),
        if *moves <= *mlim,
        block_last_insn(block, last_ea),
        !adjusts_stack_in_block(_, last_ea, base, _),
        !stack_base_reg_move(_, last_ea, _, base),
        !base_reg_def(last_ea, base),
        !stack_def(last_ea, base, ofs);

    // Backward propagation within block

    // Skip: no modification at this instruction
    live_var_used_in_block(block, ea, base, ofs, used_base, used_ofs, ea_used, moves) <--
        live_var_used_in_block(block, next_ea, base, ofs, used_base, used_ofs, ea_used, moves),
        block_instruction_next(block, ea, next_ea),
        !base_reg_def(ea, base),
        !stack_def(ea, base, ofs);

    // Stack pointer adjustment: transform offset
    live_var_used_in_block(block, ea, base, ofs + adj, used_base, used_ofs, ea_used, moves) <--
        live_var_used_in_block(block, next_ea, base, ofs, used_base, used_ofs, ea_used, moves),
        block_instruction_next(block, ea, next_ea),
        adjusts_stack_in_block(_, ea, base, adj),
        !stack_def(ea, base, ofs),
        if *base != "RSP" || ofs + adj >= 0;

    // Base register move: rename base
    live_var_used_in_block(block, ea, src_base, ofs, used_base, used_ofs, ea_used, moves) <--
        live_var_used_in_block(block, next_ea, dst_base, ofs, used_base, used_ofs, ea_used, moves),
        block_instruction_next(block, ea, next_ea),
        stack_base_reg_move(_, ea, src_base, dst_base);

    // When live_var_used_in_block reaches block start -> becomes inter-block live_var_used
    live_var_used(block, live_base, live_ofs, used_base, used_ofs, ea_used, moves) <--
        live_var_used_in_block(block, ea, live_base, live_ofs, used_base, used_ofs, ea_used, moves),
        if *ea == *block;

    // live_var_at_block_end: backward propagation across blocks, variable is live at end of Block for a use in BlockUsed

    #[local] relation live_var_at_block_end(Address, Address, Symbol, i64);

    // Base case: predecessor of a block with a live use
    live_var_at_block_end(prev_block, use_block, base, ofs) <--
        live_var_used(use_block, base, ofs, _, _, _, _),
        block_next(prev_block, use_block);

    // Recursive: propagate through blocks that don't reference this var and whose base register isn't clobbered (block_propagates_def).
    live_var_at_block_end(prev_block, block_used, base, ofs) <--
        live_var_at_block_end(block, block_used, base, ofs),
        !ref_in_block(block, base, ofs),
        !base_reg_def_in_block(block, base),
        block_next(prev_block, block);

    // live_var_at_prior_used: forward chaining to propagate a def through a found use to reach subsequent uses of the same stack location

    #[local] relation live_var_at_prior_used(Address, Address, Symbol, i64);

    live_var_at_prior_used(ea_used, block_used, base, ofs) <--
        live_var_at_block_end(block, block_used, base, ofs),
        used_in_block(block, ea_used, base, ofs),
        !base_reg_def_in_block(block, base),
        !defined_in_block(block, base, ofs);

    // stack_def_used: final output def-use chains with both def-side and use-side variables

    relation stack_def_used(Address, Symbol, i64, Address, Symbol, i64);

    // The chain is computed in the raw displacements the analysis transforms
    // through stack adjustments; the settling rule at the end restates it.
    #[local] relation stack_def_used_raw(Address, Symbol, i64, Address, Symbol, i64);

    // 1. Intra-block def-use (no adjustment between def and use)
    stack_def_used_raw(def_addr, base, ofs, use_addr, base, ofs) <--
        stack_use(use_addr, base, ofs),
        block_last_def(use_addr, def_addr, base, ofs);

    // 2. Inter-block def-use (explicit def in a predecessor block)
    stack_def_used_raw(def_addr, def_base, def_ofs, ea_used, used_base, used_ofs) <--
        live_var_at_block_end(block, block_used, base, ofs),
        live_var_def(block, base, ofs, def_addr),
        let def_base = *base,
        let def_ofs = *ofs,
        live_var_used(block_used, base, ofs, used_base, used_ofs, ea_used, _);

    // 3. Intra-block def-use through adjustments (def and use in same block, with stack modification between them)
    stack_def_used_raw(def_addr, def_base, def_ofs, ea_used, used_base, used_ofs) <--
        live_var_used_in_block(_, ea, def_base, def_ofs, used_base, used_ofs, ea_used, _),
        next(def_addr, ea),
        code_in_block(def_addr, block),
        code_in_block(ea, block),
        stack_def(def_addr, def_base, def_ofs);

    // 4. Forward propagation: chain def_used through adjacent uses
    stack_def_used_raw(def_addr, def_base, def_ofs, next_ea_used, used_base, used_ofs) <--
        live_var_at_prior_used(ea_used, next_block, base, ofs),
        stack_def_used_raw(def_addr, def_base, def_ofs, ea_used, base, ofs),
        live_var_used(next_block, base, ofs, used_base, used_ofs, next_ea_used, _);

    // A raw displacement names a frame cell only together with the SP state it
    // was taken in, and this analysis deliberately reports each side of a chain
    // at its own displacement: `mov (%rsp),%rax`, two outgoing-argument pushes,
    // `mov 0x10(%rsp),%ecx` is one cell under two numbers.  Every consumer
    // compares these offsets against frame references that asm_pass already
    // states in the frame's own coordinates, so restate them the same way here
    // -- otherwise the use's name lands on whatever object owns that
    // displacement in the settled frame.  In touch that was an escaped struct
    // stat, which swallowed the -d argument and truncated it to a field width.
    // Only an SP base moves; any other base is settled by construction.
    #[local] relation stack_ref_site(Address, Symbol);
    stack_ref_site(*addr, *base) <-- stack_def_used_raw(addr, base, _, _, _, _);
    stack_ref_site(*addr, *base) <-- stack_def_used_raw(_, _, _, addr, base, _);

    #[local] relation stack_ref_shift(Address, Symbol, i64);
    stack_ref_shift(*addr, *base, *depth) <--
        stack_ref_site(addr, base),
        if *base == "RSP",
        sp_window_depth(addr, depth);
    stack_ref_shift(*addr, *base, 0) <--
        stack_ref_site(addr, base),
        if *base != "RSP";
    stack_ref_shift(*addr, *base, 0) <--
        stack_ref_site(addr, base),
        if *base == "RSP",
        !sp_window_depth(*addr, _);

    stack_def_used(*def_addr, *def_base, def_ofs - def_shift, *use_addr, *use_base, use_ofs - use_shift) <--
        stack_def_used_raw(def_addr, def_base, def_ofs, use_addr, use_base, use_ofs),
        stack_ref_shift(def_addr, def_base, def_shift),
        stack_ref_shift(use_addr, use_base, use_shift);
}

pub struct StackAnalysisPass;

impl IRPass for StackAnalysisPass {
    fn name(&self) -> &'static str {
        "stack-analysis"
    }

    fn run(&self, db: &mut DecompileDB) {
        run_pass!(db, StackAnalysisProgram);
    }

    declare_io_from!(StackAnalysisProgram);
}

#[cfg(test)]
mod tests {
    use super::StackAnalysisProgram;

    #[test]
    fn block_flow_stops_only_at_known_noreturn_calls() {
        let mut prog = StackAnalysisProgram::default();

        prog.ddisasm_cfg_edge.push((0x10, 0x20, "fallthrough"));
        prog.ddisasm_cfg_edge.push((0x30, 0x40, "fallthrough"));
        prog.code_in_block.push((0x10, 0x10));
        prog.code_in_block.push((0x30, 0x30));
        prog.block_in_function.push((0x10, 0x1));
        prog.block_in_function.push((0x20, 0x1));
        prog.block_in_function.push((0x30, 0x2));
        prog.block_in_function.push((0x40, 0x2));
        prog.known_noreturn_call_site.push((0x10,));

        prog.run();

        assert!(!prog.block_next.iter().any(|fact| fact == &(0x10, 0x20)));
        assert!(prog.block_next.iter().any(|fact| fact == &(0x30, 0x40)));
    }

    // The option-loop shape every getopt_long main has: a flag cleared before the loop, set
    // again inside one switch arm, and read after the loop exits. Both stores define the one
    // variable the guard reads, so both must reach it.
    fn option_loop_program() -> StackAnalysisProgram {
        let prog = StackAnalysisProgram::default();
        let func = 0x100;

        // B0 0x100 store, 0x104 filler | BH 0x110 header, 0x114 branch
        // BA 0x120 store, 0x124 jump back | BX 0x130, 0x134 branch | BU 0x140 read, 0x144
        let blocks: [(u64, [u64; 2]); 5] = [
            (0x100, [0x100, 0x104]),
            (0x110, [0x110, 0x114]),
            (0x120, [0x120, 0x124]),
            (0x130, [0x130, 0x134]),
            (0x140, [0x140, 0x144]),
        ];
        for (start, insns) in blocks {
            for ea in insns {
                prog.code_in_block.push((ea, start));
                if ea != insns[insns.len() - 1] {
                    prog.next.push((ea, ea + 4));
                }
            }
            prog.block_boundaries
                .push((start, insns[insns.len() - 1], start + 0x10));
            prog.block_in_function.push((start, func));
        }
        prog.next.push((0x104, 0x110));
        prog.next.push((0x114, 0x120));
        prog.next.push((0x124, 0x130));
        prog.next.push((0x134, 0x140));

        for edge in [
            (0x104u64, 0x110u64),
            (0x114, 0x120),
            (0x114, 0x130),
            (0x124, 0x110),
            (0x134, 0x140),
        ] {
            prog.ddisasm_cfg_edge.push((edge.0, edge.1, "branch"));
        }

        prog.stack_def.push((0x100, "RSP", 0x28));
        prog.stack_def.push((0x120, "RSP", 0x28));
        prog.stack_use.push((0x140, "RSP", 0x28));
        prog
    }

    #[test]
    fn a_store_before_a_loop_reaches_a_read_after_it() {
        let mut prog = option_loop_program();
        prog.run();

        assert!(
            prog.stack_def_used
                .iter()
                .any(|fact| fact == &(0x100, "RSP", 0x28, 0x140, "RSP", 0x28)),
            "the store before the loop does not reach the read after it"
        );
    }

    #[test]
    fn a_store_inside_a_loop_reaches_a_read_after_it() {
        let mut prog = option_loop_program();
        prog.run();

        assert!(
            prog.stack_def_used
                .iter()
                .any(|fact| fact == &(0x120, "RSP", 0x28, 0x140, "RSP", 0x28)),
            "the store inside the loop does not reach the read after it"
        );
    }
}
