use log::info;
use std::collections::{BTreeSet, HashMap, HashSet};

use crate::decompile::elevator::config::CONFIG;
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::mreg::Mreg;
use crate::run_pass;
use crate::x86::types::*;
use ascent::ascent_par;

const STACK_ALIGNMENT: i64 = 0x10;
const PAGE_SIZE: i64 = 0x1000;
// The round-up mask of the `(n + mask) & ~mask` alignment idiom; derived from the ABI alignment, not a tuned value.
const STACK_ALIGN_MASK: i64 = STACK_ALIGNMENT - 1;

// Canary detection via Datalog pattern matching on raw x86 instructions
ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct CanaryProgram;

    relation unrefinedinstruction(Address, usize, &'static str, &'static str,
        Symbol, Symbol, Symbol, Symbol, usize, usize);
    relation op_indirect(Symbol, &'static str, &'static str, &'static str, i64, i64, usize);
    relation op_register(Symbol, &'static str);
    relation op_immediate(Symbol, i64, usize);
    relation next(Address, Address);
    relation flags_and_jump_pair(Address, Address, &'static str);
    relation direct_call(Address, Address);
    relation direct_jump(Address, Address);
    relation func_entry(Symbol, Address);
    relation plt_entry(Address, Symbol);
    relation plt_block(Address, Symbol);
    relation block_in_function(Address, Address);
    relation code_in_block(Address, Address);

    relation trim_instruction(Address);

    // CANARY-3: structural function containment from the CFG-BFS block_in_function, recomputed here because consuming asm_pass's instr_in_function would cycle the schedule.
    #[local] relation canary_instr_in_function(Address, Address);
    canary_instr_in_function(addr, func) <--
        block_in_function(blockaddr, func),
        code_in_block(addr, blockaddr);

    // Exported so the imperative VLA trimmer (detect_vla) resolves each alloc's function structurally instead of via the numeric find_func window.
    relation instr_in_function_canary(Address, Address);
    instr_in_function_canary(addr, func) <-- canary_instr_in_function(addr, func);

    #[local] relation prev(Address, Address);
    prev(b, a) <-- next(a, b);

    // Export the functional subset of the raw next relation for the bounded
    // VLA walkers.  Branches and joins have no row, so an imperative consumer
    // cannot accidentally choose one successor/predecessor by tuple order.
    relation canary_unique_next(Address, Address);
    canary_unique_next(a, b) <--
        next(a, b),
        agg count = ascent::aggregators::count() in next(a, _),
        if count == 1;

    relation canary_unique_prev(Address, Address);
    canary_unique_prev(b, a) <--
        next(a, b),
        agg count = ascent::aggregators::count() in next(_, b),
        if count == 1;

    #[local] relation fs_segment_op(Symbol);
    fs_segment_op(op) <--
        op_indirect(op, seg, _, _, _, _, _),
        if *seg == "FS" || *seg == "GS";

    // FS/GS segment instructions indicate TLS canary access
    #[local] relation fs_insn(Address);
    fs_insn(addr) <--
        unrefinedinstruction(addr, _, _, _, op1, _, _, _, _, _),
        fs_segment_op(op1);
    fs_insn(addr) <--
        unrefinedinstruction(addr, _, _, _, _, op2, _, _, _, _),
        fs_segment_op(op2);

    // CANARY-1: trim only FS/GS accesses provably in the canary chain (the confirmed canary_store's load and the fs_check xor/sub); other FS reads are genuine TLS.
    trim_instruction(fs_addr) <-- canary_store(fs_addr, _, _, _);
    trim_instruction(chk) <-- fs_check(chk);

    #[local] relation stack_chk_fail_addr(Address);
    stack_chk_fail_addr(addr) <--
        plt_entry(addr, name), if crate::abi::is_stack_chk_fail(name);
    stack_chk_fail_addr(addr) <--
        func_entry(name, addr), if crate::abi::is_stack_chk_fail(name);
    stack_chk_fail_addr(addr) <--
        plt_block(addr, name), if crate::abi::is_stack_chk_fail(name);

    // FS MOV: canary load from TLS
    #[local] relation fs_mov(Address);
    fs_mov(addr) <--
        fs_insn(addr),
        unrefinedinstruction(addr, _, _, mnem, _, _, _, _, _, _),
        if *mnem == "MOV";

    // ST-1: find the canary store by TRACKING the FS-loaded register forward to its first frame spill, killed by any redefinition, control flow, or a length backstop, instead of requiring fs+1.
    #[local] relation fs_mov_dst(Address, Symbol);
    fs_mov_dst(addr, reg) <--
        fs_mov(addr),
        unrefinedinstruction(addr, _, _, _, _, op2, _, _, _, _),
        op_register(op2, reg);

    #[local] relation insn_redefines(Address, Symbol);
    insn_redefines(addr, reg) <--
        unrefinedinstruction(addr, _, _, _, _, op2, _, _, _, _),
        op_register(op2, reg);

    #[local] relation insn_is_control(Address);
    insn_is_control(addr) <--
        unrefinedinstruction(addr, _, _, mnem, _, _, _, _, _, _),
        if matches!(*mnem, "JMP" | "CALL" | "RET" | "JE" | "JNE" | "JL" | "JLE" | "JG" | "JGE"
            | "JB" | "JBE" | "JA" | "JAE" | "JS" | "JNS" | "JP" | "JNP" | "JO" | "JNO");

    #[local] relation fs_track(Address, Address, Symbol, usize);
    fs_track(a, nxt, reg, 1usize) <--
        fs_mov_dst(a, reg),
        next(a, nxt);
    fs_track(start, nxt, reg, n + 1) <--
        fs_track(start, cur, reg, n),
        if *n < 16,
        !insn_redefines(cur, reg),
        !insn_is_control(cur),
        next(cur, nxt);

    // The slot carries its BASE register: an RSP-space displacement must never match an RBP-space reload (cross-base collision falsely trimmed real value reloads near epilogues).
    #[local] relation canary_store(Address, Address, Symbol, i64);
    canary_store(fs_addr, store_addr, base, disp) <--
        fs_track(fs_addr, store_addr, reg, _),
        unrefinedinstruction(store_addr, _, _, mnem, op1, op2, _, _, _, _),
        if *mnem == "MOV",
        op_register(op1, src_reg),
        if src_reg == reg,
        op_indirect(op2, _, base, _, _, disp, _),
        if (*base == "RBP" && *disp < 0) || *base == "RSP";

    trim_instruction(store_addr) <-- canary_store(_, store_addr, _, _);

    // Determine which function contains each FS instruction (STRUCTURAL CFG containment).
    #[local] relation fs_func(Address, Address);
    fs_func(fs_addr, func) <--
        fs_insn(fs_addr), canary_instr_in_function(fs_addr, func);

    #[local] relation canary_slot(Address, Symbol, i64);
    canary_slot(func, base, disp) <--
        canary_store(fs_addr, _, base, disp), fs_func(fs_addr, func);

    // Canary epilogue: FS SUB/XOR check instruction
    #[local] relation fs_check(Address);
    fs_check(addr) <--
        fs_insn(addr),
        unrefinedinstruction(addr, _, _, mnem, _, _, _, _, _, _),
        if *mnem == "SUB" || *mnem == "XOR";

    trim_instruction(jcc) <--
        fs_check(cmp), flags_and_jump_pair(cmp, jcc, _);

    #[local] relation jcc_fwd(Address, Address, usize);
    jcc_fwd(jcc, jcc, 0usize) <--
        fs_check(cmp), flags_and_jump_pair(cmp, jcc, _);
    jcc_fwd(jcc, nxt, n + 1) <--
        jcc_fwd(jcc, cur, n), next(cur, nxt), if *n < 2;
    // The __stack_chk_fail block is the canary JCC's TAKEN target, not the address-next instruction, so step along the branch edge too (same hop bound).
    jcc_fwd(jcc, tgt, n + 1) <--
        jcc_fwd(jcc, cur, n), direct_jump(cur, tgt), if *n < 2;

    // Suppress __stack_chk_fail calls after canary check JCC
    trim_instruction(call_addr) <--
        jcc_fwd(_, call_addr, n), if *n > 0,
        direct_call(call_addr, target),
        stack_chk_fail_addr(target);

    trim_instruction(call_addr) <--
        jcc_fwd(_, call_addr, n), if *n > 0,
        unrefinedinstruction(call_addr, _, _, mnem, op1, _, _, _, _, _),
        if *mnem == "CALL",
        op_immediate(op1, imm, _),
        let target = *imm as u64,
        stack_chk_fail_addr(target);

    // Suppress canary reload: MOV from [RBP+canary_ofs] before FS check
    #[local] relation fs_check_bwd(Address, Address, usize);
    fs_check_bwd(chk, chk, 0usize) <-- fs_check(chk);
    fs_check_bwd(chk, prv, n + 1) <--
        fs_check_bwd(chk, cur, n), prev(cur, prv), if *n < 4;

    #[local] relation check_canary_ofs(Address, Symbol, i64);
    check_canary_ofs(chk, base, ofs) <--
        fs_check(chk), fs_func(chk, func), canary_slot(func, base, ofs);

    trim_instruction(reload_addr) <--
        fs_check_bwd(chk, reload_addr, n), if *n > 0,
        unrefinedinstruction(reload_addr, _, _, mnem, op1, _, _, _, _, _),
        if *mnem == "MOV",
        op_indirect(op1, _, base, _, _, disp, _),
        check_canary_ofs(chk, base, disp);

    // === VLA Detection ===

    // RSP/ESP register operand
    #[local] relation rsp_op(Symbol);
    rsp_op(op) <-- op_register(op, name), if *name == "RSP" || *name == "ESP";

    // Dynamic alloc: SUB <register>, RSP (size operand is a register, not immediate)
    #[local] relation vla_dynamic_alloc(Address, &'static str);
    vla_dynamic_alloc(addr, size_reg) <--
        unrefinedinstruction(addr, _, _, mnem, op1, op2, _, _, _, _),
        if *mnem == "SUB",
        rsp_op(op2),
        op_register(op1, size_reg),
        if *size_reg != "RSP" && *size_reg != "ESP";

    // ST-2: clang's canonical alloca updates RSP by MOV from a computed register rather than a direct SUB; RBP is excluded, and trims are gated on the FULL pattern matching.
    #[local] relation vla_mov_alloc(Address, &'static str);
    vla_mov_alloc(addr, size_reg) <--
        unrefinedinstruction(addr, _, _, mnem, op1, op2, _, _, _, _),
        if *mnem == "MOV",
        rsp_op(op2),
        op_register(op1, size_reg),
        if *size_reg != "RSP" && *size_reg != "ESP" && *size_reg != "RBP" && *size_reg != "EBP";

    vla_dynamic_alloc(addr, size_reg) <-- vla_mov_alloc(addr, size_reg);

    // Suppress the alloc only when a capture confirmed the alloca pattern; VLA-1, an un-captured sub %reg,%rsp is a genuine dynamic stack adjustment that must survive.
    trim_instruction(addr) <--
        vla_dynamic_alloc(addr, _),
        !vla_mov_alloc(addr, _),
        vla_capture(addr, _, _, _);
    trim_instruction(addr) <--
        vla_mov_alloc(addr, _),
        vla_capture(addr, _, _, _);

    // Forward walk from alloc (up to 30 steps), straight-line only: the alloca sequence (sub/and/mov) contains no branches, and stopping at control flow keeps the walk from crossing a RET into the next function (the raw `next` chain is address order).
    #[local] relation vla_alloc_fwd(Address, Address, usize);
    vla_alloc_fwd(a, a, 0usize) <-- vla_dynamic_alloc(a, _);
    vla_alloc_fwd(start, nxt, n + 1) <--
        vla_alloc_fwd(start, cur, n), next(cur, nxt), if *n < 30,
        !insn_is_control(cur);

    // Candidate captures: MOV RSP -> <non-RSP/RBP register>
    #[local] relation vla_capture_candidate(Address, Address, &'static str, usize);
    vla_capture_candidate(alloc, fwd_addr, result_reg, n) <--
        vla_alloc_fwd(alloc, fwd_addr, n), if *n > 0,
        unrefinedinstruction(fwd_addr, _, _, mnem, op1, op2, _, _, _, _),
        if *mnem == "MOV",
        rsp_op(op1),
        op_register(op2, result_reg),
        if *result_reg != "RSP" && *result_reg != "ESP"
            && *result_reg != "RBP" && *result_reg != "EBP";

    // First (closest) capture per alloc
    #[local] relation vla_capture_step(Address, usize);
    vla_capture_step(alloc, min_n) <--
        vla_capture_candidate(alloc, _, _, _),
        agg min_n = ascent::aggregators::min(n) in vla_capture_candidate(alloc, _, _, n);

    // The resolved capture, carrying size_reg from the alloc
    relation vla_capture(Address, Address, &'static str, &'static str);
    vla_capture(alloc, cap_addr, size_reg, result_reg) <--
        vla_capture_candidate(alloc, cap_addr, result_reg, n),
        vla_capture_step(alloc, n),
        vla_dynamic_alloc(alloc, size_reg);

    relation vla_alloca(Address, Mreg, Mreg);
    vla_alloca(cap_addr, size_mreg, result_mreg) <--
        vla_capture(_, cap_addr, size_reg, result_reg),
        let size_mreg = Mreg::x86(*size_reg),
        let result_mreg = Mreg::x86(*result_reg),
        if size_mreg != Mreg::Unknown,
        if result_mreg != Mreg::Unknown;

    // Suppress everything between alloc and capture (inclusive of capture)
    trim_instruction(mid) <--
        vla_alloc_fwd(alloc, mid, n), if *n > 0,
        vla_capture_step(alloc, cap_n),
        if *n <= *cap_n;

    // Trim JCCs for flag-setting instructions in the trimmed range
    trim_instruction(jcc) <--
        vla_alloc_fwd(alloc, mid, n), if *n > 0,
        vla_capture_step(alloc, cap_n),
        if *n <= *cap_n,
        flags_and_jump_pair(mid, jcc, _);

    // Function containing each alloc (STRUCTURAL CFG containment).
    #[local] relation vla_func(Address, Address);
    vla_func(alloc, func) <--
        vla_dynamic_alloc(alloc, _), canary_instr_in_function(alloc, func);

    // Forward walk from capture (up to 6 steps) for base var detection
    #[local] relation vla_cap_fwd(Address, Address, usize);
    vla_cap_fwd(alloc, nxt, 1usize) <--
        vla_capture(alloc, cap, _, _), next(cap, nxt);
    vla_cap_fwd(alloc, nxt, n + 1) <--
        vla_cap_fwd(alloc, cur, n), next(cur, nxt), if *n < 6;

    // Base var candidate: MOV to [RBP + negative displacement]
    #[local] relation vla_base_candidate(Address, i64, usize);
    vla_base_candidate(alloc, disp, n) <--
        vla_cap_fwd(alloc, fwd, n),
        unrefinedinstruction(fwd, _, _, mnem, _, op2, _, _, _, _),
        if *mnem == "MOV",
        op_indirect(op2, _, base, _, _, disp, _),
        if *base == "RBP" && *disp < 0;

    // First (closest) base var per alloc
    #[local] relation vla_base_min(Address, usize);
    vla_base_min(alloc, min_n) <--
        vla_base_candidate(alloc, _, _),
        agg min_n = ascent::aggregators::min(n) in vla_base_candidate(alloc, _, n);

    // Output: VLA base variable (func_entry, stack displacement)
    relation vla_base_var(Address, i64);
    vla_base_var(func, disp) <--
        vla_base_candidate(alloc, disp, n),
        vla_base_min(alloc, n),
        vla_func(alloc, func);
}

pub struct CanaryVlaPass;

impl IRPass for CanaryVlaPass {
    fn name(&self) -> &'static str {
        "canary-vla"
    }

    fn run(&self, db: &mut DecompileDB) {
        run_pass!(db, CanaryProgram);
        detect_vla(db);
    }

    fn inputs(&self) -> &'static [&'static str] {
        &[
            "unrefinedinstruction",
            "op_indirect",
            "op_register",
            "op_immediate",
            "next",
            "flags_and_jump_pair",
            "direct_call",
            "direct_jump",
            "func_entry",
            "plt_entry",
            "plt_block",
            // CANARY-3: structural CFG containment inputs (CFG-BFS results set pre-pipeline), replacing the former func_entry<=addr windows.
            "block_in_function",
            "code_in_block",
        ]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "trim_instruction",
            "vla_alloca",
            "vla_base_var",
            "vla_capture",
            "canary_unique_next",
            "canary_unique_prev",
            // Structural per-instruction function membership, consumed imperatively by detect_vla in place of the old numeric find_func window.
            "instr_in_function_canary",
        ]
    }

    // direct_jump is read imperatively in detect_vla, so declare it or the scheduler leaves it silently empty in parallel sub-DBs.
    fn extra_reads(&self) -> &'static [&'static str] {
        &["direct_jump"]
    }
}

// VLA trimming: reads Datalog-identified VLA facts and trims alignment/probe boilerplate
type InsnTuple = (
    Address,
    usize,
    &'static str,
    &'static str,
    Symbol,
    Symbol,
    Symbol,
    Symbol,
    usize,
    usize,
);
type OpIndirectTuple = (
    Symbol,
    &'static str,
    &'static str,
    &'static str,
    i64,
    i64,
    usize,
);
type OpRegisterTuple = (Symbol, &'static str);
type OpImmediateTuple = (Symbol, i64, usize);

fn detect_vla(db: &mut DecompileDB) {
    // Sort captures so trim_instruction pushes are deterministic across thread schedules.
    let mut captures: Vec<(Address, Address, &'static str, &'static str)> = db
        .rel_iter::<(Address, Address, &'static str, &'static str)>("vla_capture")
        .copied()
        .collect();
    captures.sort();

    if captures.is_empty() {
        return;
    }

    let insns: HashMap<Address, InsnTuple> = db
        .rel_iter::<InsnTuple>("unrefinedinstruction")
        .map(|t| (t.0, *t))
        .collect();

    let op_indirects: HashMap<Symbol, OpIndirectTuple> = db
        .rel_iter::<OpIndirectTuple>("op_indirect")
        .map(|t| (t.0, *t))
        .collect();

    let op_registers: HashMap<Symbol, &'static str> = db
        .rel_iter::<OpRegisterTuple>("op_register")
        .map(|&(id, name)| (id, name))
        .collect();

    let op_immediates: HashMap<Symbol, i64> = db
        .rel_iter::<OpImmediateTuple>("op_immediate")
        .map(|&(id, val, _)| (id, val))
        .collect();

    let next_map: HashMap<Address, Address> = db
        .rel_iter::<(Address, Address)>("canary_unique_next")
        .copied()
        .collect();
    let prev_map: HashMap<Address, Address> = db
        .rel_iter::<(Address, Address)>("canary_unique_prev")
        .copied()
        .collect();

    let func_entries: HashSet<Address> = db
        .rel_iter::<(Symbol, Address)>("func_entry")
        .map(|&(_, addr)| addr)
        .collect();

    // CANARY-3: structural per-instruction function membership from instr_in_function_canary, replacing the find_func window that misassigned across disjoint branches.
    let instr_func: HashMap<Address, Address> = db
        .rel_iter::<(Address, Address)>("instr_in_function_canary")
        .map(|&(addr, func)| (addr, func))
        .collect();

    let flags_pairs: HashMap<Address, Address> = db
        .rel_iter::<(Address, Address, &'static str)>("flags_and_jump_pair")
        .map(|&(cmp, jcc, _)| (cmp, jcc))
        .collect();

    // CANARY-2: resolved unconditional-jump targets; a probe-loop JMP is trimmed only when this map resolves it back into the recognized probe block.
    let direct_jumps: HashMap<Address, Address> = db
        .rel_iter::<(Address, Address)>("direct_jump")
        .map(|&(src, tgt)| (src, tgt))
        .collect();

    let mut trimmed: BTreeSet<Address> = BTreeSet::new();

    let walk_forward = |start: Address, max_steps: usize| -> Vec<Address> {
        let mut result = Vec::new();
        let mut cur = start;
        for _ in 0..max_steps {
            if let Some(&nxt) = next_map.get(&cur) {
                result.push(nxt);
                cur = nxt;
            } else {
                break;
            }
        }
        result
    };

    let walk_backward = |start: Address, max_steps: usize| -> Vec<Address> {
        let mut result = Vec::new();
        let mut cur = start;
        for _ in 0..max_steps {
            if let Some(&prv) = prev_map.get(&cur) {
                result.push(prv);
                cur = prv;
            } else {
                break;
            }
        }
        result
    };

    let is_rsp_operand = |op_id: Symbol| -> bool {
        if let Some(&name) = op_registers.get(op_id) {
            name == "RSP" || name == "ESP"
        } else {
            false
        }
    };

    let get_reg_name = |op_id: Symbol| -> Option<&'static str> { op_registers.get(op_id).copied() };

    let get_immediate = |op_id: Symbol| -> Option<i64> { op_immediates.get(op_id).copied() };

    // Structural CFG containment lookup (replaces the address-order window).
    let find_func = |addr: Address| -> Option<Address> { instr_func.get(&addr).copied() };

    for &(alloc_addr, cap_addr, _size_reg, result_reg) in &captures {
        let func = match find_func(alloc_addr) {
            Some(f) => f,
            None => continue,
        };

        // Walk backward to find alignment arithmetic (DIV/IDIV/IMUL with stack alignment)
        let backward = walk_backward(alloc_addr, CONFIG.vla.align_scan_back);
        let mut alignment_start = alloc_addr;

        for &prev_addr in backward.iter() {
            if let Some(&(_, _, _, mnem, op1, op2, _, _, _, _)) = insns.get(&prev_addr) {
                if func_entries.contains(&prev_addr) && prev_addr != func {
                    break;
                }

                match mnem {
                    "DIV" | "IDIV" => {
                        alignment_start = prev_addr;
                    }
                    "IMUL" => {
                        if get_immediate(op1) == Some(STACK_ALIGNMENT)
                            || get_immediate(op2) == Some(STACK_ALIGNMENT)
                        {
                            alignment_start = prev_addr;
                        }
                    }
                    _ => {}
                }
            }
        }

        // When alignment_start is a DIV/IDIV, suppress its operand setup (MOV $0,%edx, MOV $ALIGNMENT,%esi within 3 steps) and further-back arithmetic (ADD/SUB with 1/ALIGNMENT, MOV $ALIGNMENT).
        if alignment_start != alloc_addr {
            if let Some(&(_, _, _, align_mnem, align_op1, _, _, _, _, _)) =
                insns.get(&alignment_start)
            {
                if align_mnem == "DIV" || align_mnem == "IDIV" {
                    let div_operand_reg = get_reg_name(align_op1);

                    let close_back =
                        walk_backward(alignment_start, CONFIG.vla.div_operand_scan_back);
                    for &pre_addr in &close_back {
                        if func_entries.contains(&pre_addr) && pre_addr != func {
                            break;
                        }
                        if let Some(&(_, _, _, pm, pm_op1, pm_op2, _, _, _, _)) =
                            insns.get(&pre_addr)
                        {
                            match pm {
                                "MOV" => {
                                    if let Some(imm) = get_immediate(pm_op1) {
                                        let tgt = get_reg_name(pm_op2);
                                        if imm == 0 && matches!(tgt, Some("RDX" | "EDX")) {
                                            trimmed.insert(pre_addr);
                                            alignment_start = pre_addr;
                                        }
                                        if imm == STACK_ALIGNMENT && tgt == div_operand_reg {
                                            trimmed.insert(pre_addr);
                                            alignment_start = pre_addr;
                                        }
                                    }
                                }
                                "XOR" => {
                                    let r1 = get_reg_name(pm_op1);
                                    if r1 == get_reg_name(pm_op2)
                                        && matches!(r1, Some("RDX" | "EDX"))
                                    {
                                        trimmed.insert(pre_addr);
                                        alignment_start = pre_addr;
                                    }
                                }
                                _ => {}
                            }
                        }
                    }

                    let arith_back =
                        walk_backward(alignment_start, CONFIG.vla.align_arith_scan_back);
                    for &pre_addr in &arith_back {
                        if func_entries.contains(&pre_addr) && pre_addr != func {
                            break;
                        }
                        if let Some(&(_, _, _, pm, pm_op1, pm_op2, _, _, _, _)) =
                            insns.get(&pre_addr)
                        {
                            match pm {
                                "ADD" | "SUB" => {
                                    let imm1 = get_immediate(pm_op1);
                                    let imm2 = get_immediate(pm_op2);
                                    if matches!(imm1, Some(1) | Some(STACK_ALIGN_MASK))
                                        || matches!(imm2, Some(1) | Some(STACK_ALIGN_MASK))
                                    {
                                        trimmed.insert(pre_addr);
                                        alignment_start = pre_addr;
                                    }
                                }
                                "MOV" => {
                                    if let Some(imm) = get_immediate(pm_op1) {
                                        if imm == STACK_ALIGNMENT {
                                            trimmed.insert(pre_addr);
                                            alignment_start = pre_addr;
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }

            // Trim the alignment prologue along the structural next chain from alignment_start to the alloc; a visited guard terminates it, and it stops if the chain leaves the function.
            let mut cur = alignment_start;
            trimmed.insert(cur);
            let mut seen: HashSet<Address> = HashSet::new();
            while cur != alloc_addr && seen.insert(cur) {
                match next_map.get(&cur) {
                    Some(&nxt) if find_func(nxt) == Some(func) => {
                        trimmed.insert(nxt);
                        cur = nxt;
                    }
                    _ => break,
                }
            }
        }

        // Stack probe loop (SUB rsp, PAGE_SIZE with CMP/JMP guard); CANARY-2 bounds every walk by structural function membership so it cannot bleed into a neighbour.
        let in_func = |addr: Address| -> bool { find_func(addr) == Some(func) };

        let neighborhood: Vec<Address> = {
            let mut n: Vec<Address> = walk_backward(alloc_addr, CONFIG.vla.probe_scan_back)
                .into_iter()
                .take_while(|&a| in_func(a))
                .collect();
            n.reverse();
            n.push(alloc_addr);
            n.extend(
                walk_forward(alloc_addr, CONFIG.vla.probe_scan_forward)
                    .into_iter()
                    .take_while(|&a| in_func(a)),
            );
            n
        };

        for &probe_addr in &neighborhood {
            if let Some(&(_, _, _, mnem, op1, op2, _, _, _, _)) = insns.get(&probe_addr) {
                if mnem == "SUB" && is_rsp_operand(op2) && get_immediate(op1) == Some(PAGE_SIZE) {
                    trimmed.insert(probe_addr);

                    // Structural probe block: the straight-line region around the SUB confined to func; a JMP is trimmed only if it resolves back into this set, never by address range.
                    let mut probe_block: HashSet<Address> = HashSet::new();
                    probe_block.insert(probe_addr);
                    for &b in walk_backward(probe_addr, CONFIG.vla.probe_block_scan_back)
                        .iter()
                        .take_while(|&&a| in_func(a))
                    {
                        probe_block.insert(b);
                    }
                    let probe_fwd: Vec<Address> =
                        walk_forward(probe_addr, CONFIG.vla.probe_block_scan_forward)
                            .into_iter()
                            .take_while(|&a| in_func(a))
                            .collect();
                    for &f in &probe_fwd {
                        probe_block.insert(f);
                    }

                    for &adj in &probe_fwd {
                        if let Some(&(_, _, _, nm, op1_adj, _, _, _, _, _)) = insns.get(&adj) {
                            match nm {
                                "OR" if is_rsp_operand(op1_adj) || {
                                    op_indirects
                                        .get(op1_adj)
                                        .map_or(false, |&(_, _, base, _, _, _, _)| base == "RSP")
                                } =>
                                {
                                    trimmed.insert(adj);
                                }
                                "JMP" => {
                                    if direct_jumps
                                        .get(&adj)
                                        .map_or(false, |t| probe_block.contains(t))
                                    {
                                        trimmed.insert(adj);
                                    }
                                }
                                _ => {}
                            };
                        }
                    }
                    for &adj in walk_backward(probe_addr, CONFIG.vla.probe_block_scan_back)
                        .iter()
                        .take_while(|&&a| in_func(a))
                    {
                        if let Some(&(_, _, _, nm, op1_adj, op2_adj, _, _, _, _)) = insns.get(&adj)
                        {
                            match nm {
                                "CMP" if is_rsp_operand(op1_adj) || is_rsp_operand(op2_adj) => {
                                    trimmed.insert(adj);
                                    if let Some(&jcc) = flags_pairs.get(&adj) {
                                        trimmed.insert(jcc);
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
        }

        // Trim ADD/SHR/SHL/AND only when AT&T dst (op2) is the captured VLA result reg.
        for &fwd_addr in walk_forward(cap_addr, CONFIG.vla.result_adjust_scan_forward).iter() {
            let Some(&(_, _, _, mnem, _, op2, _, _, _, _)) = insns.get(&fwd_addr) else {
                break;
            };
            if !matches!(mnem, "ADD" | "SHR" | "SHL" | "AND") {
                break;
            }
            if get_reg_name(op2) != Some(result_reg) {
                break;
            }
            trimmed.insert(fwd_addr);
        }
    }

    let canary_count: usize = db.rel_iter::<(Address,)>("trim_instruction").count();

    let vla_alloca_count = db.rel_iter::<(Address, Mreg, Mreg)>("vla_alloca").count();
    if canary_count > 0 || !trimmed.is_empty() || vla_alloca_count > 0 {
        let base_var_count: usize = db.rel_iter::<(Address, i64)>("vla_base_var").count();
        info!(
            "[canary-vla] Suppressing {} canary + {} VLA instructions, {} alloca sites, {} base vars",
            canary_count,
            trimmed.len(),
            vla_alloca_count,
            base_var_count,
        );
    }

    // Append-only: rel_push new trims rather than rel_set to preserve immutable-facts invariant.
    if !trimmed.is_empty() {
        let existing: HashSet<Address> = db
            .rel_iter::<(Address,)>("trim_instruction")
            .map(|&(a,)| a)
            .collect();
        for addr in &trimmed {
            if !existing.contains(addr) {
                db.rel_push("trim_instruction", (*addr,));
            }
        }
    }

    // Bridge next edges across trimmed ranges so downstream passes don't get orphan nodes.
    let alloca_addrs: BTreeSet<Address> = db
        .rel_iter::<(Address, Mreg, Mreg)>("vla_alloca")
        .map(|&(addr, _, _)| addr)
        .collect();

    let all_trimmed: BTreeSet<Address> = db
        .rel_iter::<(Address,)>("trim_instruction")
        .map(|&(a,)| a)
        .collect();

    for &addr in &all_trimmed {
        if let Some(&pred) = prev_map.get(&addr) {
            if !all_trimmed.contains(&pred) {
                let mut cur = addr;
                let mut visited = HashSet::new();
                while visited.insert(cur) {
                    if alloca_addrs.contains(&cur) {
                        db.rel_push("next", (pred, cur));
                        break;
                    }
                    if let Some(&nxt) = next_map.get(&cur) {
                        if !all_trimmed.contains(&nxt) {
                            db.rel_push("next", (pred, nxt));
                            break;
                        }
                        cur = nxt;
                    } else {
                        break;
                    }
                }
            }
        }
    }

    // Bridge FROM alloca nodes TO first non-trimmed successor.
    for &alloca_addr in &alloca_addrs {
        if let Some(&nxt) = next_map.get(&alloca_addr) {
            if all_trimmed.contains(&nxt) && !alloca_addrs.contains(&nxt) {
                let mut cur = nxt;
                let mut visited = HashSet::new();
                while visited.insert(cur) {
                    if let Some(&nxt2) = next_map.get(&cur) {
                        if !all_trimmed.contains(&nxt2) {
                            db.rel_push("next", (alloca_addr, nxt2));
                            break;
                        }
                        cur = nxt2;
                    } else {
                        break;
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unique_cfg_edges_and_alloca_are_derived_by_rules() {
        let mut prog = CanaryProgram::default();
        for edge in [(1, 2), (1, 3), (4, 2), (5, 6)] {
            prog.next.push(edge);
        }
        prog.vla_capture.push((10, 11, "RAX", "RBX"));

        prog.run();

        assert!(!prog.canary_unique_next.iter().any(|row| row.0 == 1));
        assert!(prog.canary_unique_next.iter().any(|row| row == &(4, 2)));
        assert!(prog.canary_unique_next.iter().any(|row| row == &(5, 6)));
        assert!(!prog.canary_unique_prev.iter().any(|row| row.0 == 2));
        assert!(prog.canary_unique_prev.iter().any(|row| row == &(3, 1)));
        assert!(prog.vla_alloca.iter().any(|&(addr, size, result)| {
            addr == 11 && size == Mreg::x86("RAX") && result == Mreg::x86("RBX")
        }));
    }
}
