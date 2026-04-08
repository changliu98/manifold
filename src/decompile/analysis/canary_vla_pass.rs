
use log::info;
use std::collections::{HashMap, HashSet, BTreeSet};

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::run_pass;
use crate::x86::mach::Mreg;
use crate::x86::types::*;
use ascent::ascent_par;

const STACK_ALIGNMENT: i64 = 0x10;
const PAGE_SIZE: i64 = 0x1000;

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
    relation func_entry(Symbol, Address);
    relation plt_entry(Address, Symbol);
    relation plt_block(Address, Symbol);

    relation trim_instruction(Address);

    #[local] relation prev(Address, Address);
    prev(b, a) <-- next(a, b);

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

    trim_instruction(addr) <-- fs_insn(addr);

    #[local] relation stack_chk_fail_addr(Address);
    stack_chk_fail_addr(addr) <--
        plt_entry(addr, name), if name.contains("stack_chk_fail");
    stack_chk_fail_addr(addr) <--
        func_entry(name, addr), if name.contains("stack_chk_fail");
    stack_chk_fail_addr(addr) <--
        plt_block(addr, name), if name.contains("stack_chk_fail");

    #[local] relation func_addr(Address);
    func_addr(f) <-- func_entry(_, f);

    // FS MOV: canary load from TLS
    #[local] relation fs_mov(Address);
    fs_mov(addr) <--
        fs_insn(addr),
        unrefinedinstruction(addr, _, _, mnem, _, _, _, _, _, _),
        if *mnem == "MOV";

    #[local] relation fs_mov_fwd(Address, Address, usize);
    fs_mov_fwd(a, a, 0usize) <-- fs_mov(a);
    fs_mov_fwd(start, nxt, n + 1) <--
        fs_mov_fwd(start, cur, n), next(cur, nxt), if *n < 4;

    // Canary store: MOV to [RBP+disp<0] immediately after FS MOV (n==1 only)
    #[local] relation canary_store(Address, Address, i64);
    canary_store(fs_addr, store_addr, disp) <--
        fs_mov_fwd(fs_addr, store_addr, n), if *n == 1,
        unrefinedinstruction(store_addr, _, _, mnem, _, op2, _, _, _, _),
        if *mnem == "MOV",
        op_indirect(op2, _, base, _, _, disp, _),
        if *base == "RBP" && *disp < 0;

    trim_instruction(store_addr) <-- canary_store(_, store_addr, _);

    // Determine which function contains each FS instruction
    #[local] relation fs_func_le(Address, Address);
    fs_func_le(fs_addr, f) <--
        fs_insn(fs_addr), func_addr(f), if *f <= *fs_addr;

    #[local] relation fs_func(Address, Address);
    fs_func(fs_addr, max_f) <--
        fs_func_le(fs_addr, _),
        agg max_f = ascent::aggregators::max(f) in fs_func_le(fs_addr, f);

    #[local] relation canary_slot(Address, i64);
    canary_slot(func, disp) <--
        canary_store(fs_addr, _, disp), fs_func(fs_addr, func);

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

    #[local] relation check_canary_ofs(Address, i64);
    check_canary_ofs(chk, ofs) <--
        fs_check(chk), fs_func(chk, func), canary_slot(func, ofs);

    trim_instruction(reload_addr) <--
        fs_check_bwd(chk, reload_addr, n), if *n > 0,
        unrefinedinstruction(reload_addr, _, _, mnem, op1, _, _, _, _, _),
        if *mnem == "MOV",
        op_indirect(op1, _, base, _, _, disp, _),
        if *base == "RBP",
        check_canary_ofs(chk, disp);

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

    // Suppress the alloc itself
    trim_instruction(addr) <-- vla_dynamic_alloc(addr, _);

    // Forward walk from alloc (up to 30 steps)
    #[local] relation vla_alloc_fwd(Address, Address, usize);
    vla_alloc_fwd(a, a, 0usize) <-- vla_dynamic_alloc(a, _);
    vla_alloc_fwd(start, nxt, n + 1) <--
        vla_alloc_fwd(start, cur, n), next(cur, nxt), if *n < 30;

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

    // Function containing each alloc (largest func_entry <= alloc addr)
    #[local] relation vla_func_le(Address, Address);
    vla_func_le(alloc, f) <--
        vla_dynamic_alloc(alloc, _), func_addr(f), if *f <= *alloc;

    #[local] relation vla_func(Address, Address);
    vla_func(alloc, max_f) <--
        vla_func_le(alloc, _),
        agg max_f = ascent::aggregators::max(f) in vla_func_le(alloc, f);

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
            "func_entry",
            "plt_entry",
            "plt_block",
        ]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "trim_instruction",
            "vla_alloca",
            "vla_base_var",
            "vla_capture",
        ]
    }
}

// VLA trimming: reads Datalog-identified VLA facts and trims alignment/probe boilerplate
type InsnTuple = (Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize);
type OpIndirectTuple = (Symbol, &'static str, &'static str, &'static str, i64, i64, usize);
type OpRegisterTuple = (Symbol, &'static str);
type OpImmediateTuple = (Symbol, i64, usize);

fn detect_vla(db: &mut DecompileDB) {
    // Read VLA captures identified by Datalog
    let captures: Vec<(Address, Address, &'static str, &'static str)> = db
        .rel_iter::<(Address, Address, &'static str, &'static str)>("vla_capture")
        .copied()
        .collect();

    if captures.is_empty() {
        let alloca_rel: ascent::boxcar::Vec<(Address, Mreg, Mreg)> = Default::default();
        db.rel_set("vla_alloca", alloca_rel);
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
        .rel_iter::<(Address, Address)>("next")
        .map(|&(a, b)| (a, b))
        .collect();

    let prev_map: HashMap<Address, Address> = db
        .rel_iter::<(Address, Address)>("next")
        .map(|&(a, b)| (b, a))
        .collect();

    let func_entries: HashSet<Address> = db
        .rel_iter::<(Symbol, Address)>("func_entry")
        .map(|&(_, addr)| addr)
        .collect();

    let flags_pairs: HashMap<Address, Address> = db
        .rel_iter::<(Address, Address, &'static str)>("flags_and_jump_pair")
        .map(|&(cmp, jcc, _)| (cmp, jcc))
        .collect();

    let mut trimmed: BTreeSet<Address> = BTreeSet::new();
    let mut vla_allocas: Vec<(Address, Mreg, Mreg)> = Vec::new();

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

    let get_reg_name = |op_id: Symbol| -> Option<&'static str> {
        op_registers.get(op_id).copied()
    };

    let get_immediate = |op_id: Symbol| -> Option<i64> {
        op_immediates.get(op_id).copied()
    };

    let find_func = |addr: Address| -> Option<Address> {
        func_entries.iter().copied().filter(|&f| f <= addr).max()
    };

    for &(alloc_addr, cap_addr, size_reg, result_reg) in &captures {
        let func = match find_func(alloc_addr) {
            Some(f) => f,
            None => continue,
        };

        // Convert register names to Mreg for vla_alloca
        let size_mreg = Mreg::from(size_reg);
        let result_mreg = Mreg::from(result_reg);
        if size_mreg != Mreg::Unknown && result_mreg != Mreg::Unknown {
            vla_allocas.push((cap_addr, size_mreg, result_mreg));
        }

        // Walk backward to find alignment arithmetic (DIV/IDIV/IMUL with stack alignment)
        let backward = walk_backward(alloc_addr, 30);
        let mut alignment_start = alloc_addr;

        for &prev_addr in backward.iter() {
            if let Some(&(_, _, _, mnem, op1, op2, _, _, _, _)) = insns.get(&prev_addr) {
                if func_entries.contains(&prev_addr) && prev_addr != func { break; }

                match mnem {
                    "DIV" | "IDIV" => {
                        alignment_start = prev_addr;
                    }
                    "IMUL" => {
                        if get_immediate(op1) == Some(STACK_ALIGNMENT) || get_immediate(op2) == Some(STACK_ALIGNMENT) {
                            alignment_start = prev_addr;
                        }
                    }
                    _ => {}
                }
            }
        }

        // When alignment_start is a DIV/IDIV, suppress its operand setup (MOV $0,%edx, MOV $ALIGNMENT,%esi within 3 steps) and further-back arithmetic (ADD/SUB with 1/ALIGNMENT, MOV $ALIGNMENT).
        if alignment_start != alloc_addr {
            if let Some(&(_, _, _, align_mnem, align_op1, _, _, _, _, _)) = insns.get(&alignment_start) {
                if align_mnem == "DIV" || align_mnem == "IDIV" {
                    let div_operand_reg = get_reg_name(align_op1);

                    let close_back = walk_backward(alignment_start, 3);
                    for &pre_addr in &close_back {
                        if func_entries.contains(&pre_addr) && pre_addr != func { break; }
                        if let Some(&(_, _, _, pm, pm_op1, pm_op2, _, _, _, _)) = insns.get(&pre_addr) {
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
                                    if r1 == get_reg_name(pm_op2) && matches!(r1, Some("RDX" | "EDX")) {
                                        trimmed.insert(pre_addr);
                                        alignment_start = pre_addr;
                                    }
                                }
                                _ => {}
                            }
                        }
                    }

                    let arith_back = walk_backward(alignment_start, 6);
                    for &pre_addr in &arith_back {
                        if func_entries.contains(&pre_addr) && pre_addr != func { break; }
                        if let Some(&(_, _, _, pm, pm_op1, pm_op2, _, _, _, _)) = insns.get(&pre_addr) {
                            match pm {
                                "ADD" | "SUB" => {
                                    let imm1 = get_immediate(pm_op1);
                                    let imm2 = get_immediate(pm_op2);
                                    if matches!(imm1, Some(1) | Some(15)) || matches!(imm2, Some(1) | Some(15)) {
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

            let mut cur = alignment_start;
            trimmed.insert(cur);
            while cur < alloc_addr {
                if let Some(&nxt) = next_map.get(&cur) {
                    trimmed.insert(nxt);
                    cur = nxt;
                } else {
                    break;
                }
            }
        }

        // Stack probe loop: SUB rsp, PAGE_SIZE with CMP/JMP guard
        let neighborhood: Vec<Address> = {
            let mut n: Vec<Address> = walk_backward(alloc_addr, 20);
            n.reverse();
            n.push(alloc_addr);
            n.extend(walk_forward(alloc_addr, 10));
            n
        };

        for &probe_addr in &neighborhood {
            if let Some(&(_, _, _, mnem, op1, op2, _, _, _, _)) = insns.get(&probe_addr) {
                if mnem == "SUB" && is_rsp_operand(op2) && get_immediate(op1) == Some(PAGE_SIZE) {
                    trimmed.insert(probe_addr);
                    for &adj in walk_forward(probe_addr, 3).iter() {
                        if let Some(&(_, _, _, nm, op1_adj, _, _, _, _, _)) = insns.get(&adj) {
                            match nm {
                                "OR" if is_rsp_operand(op1_adj) || {
                                    op_indirects.get(op1_adj).map_or(false, |&(_, _, base, _, _, _, _)| base == "RSP")
                                } => trimmed.insert(adj),
                                "JMP" => trimmed.insert(adj),
                                _ => false,
                            };
                        }
                    }
                    for &adj in walk_backward(probe_addr, 5).iter() {
                        if let Some(&(_, _, _, nm, op1_adj, op2_adj, _, _, _, _)) = insns.get(&adj) {
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

        // Post-capture alignment ops (ADD/SHR/SHL/AND before base var store)
        for &fwd_addr in walk_forward(cap_addr, 6).iter() {
            if let Some(&(_, _, _, mnem, _, _, _, _, _, _)) = insns.get(&fwd_addr) {
                match mnem {
                    "ADD" | "SHR" | "SHL" | "AND" => {
                        trimmed.insert(fwd_addr);
                    }
                    _ => break,
                }
            }
        }
    }

    let canary_count: usize = db.rel_iter::<(Address,)>("trim_instruction").count();

    if canary_count > 0 || !trimmed.is_empty() || !vla_allocas.is_empty() {
        let base_var_count: usize = db.rel_iter::<(Address, i64)>("vla_base_var").count();
        info!(
            "[canary-vla] Suppressing {} canary + {} VLA instructions, {} alloca sites, {} base vars",
            canary_count,
            trimmed.len(),
            vla_allocas.len(),
            base_var_count,
        );
    }

    if !trimmed.is_empty() {
        let existing: Vec<Address> = db.rel_iter::<(Address,)>("trim_instruction")
            .map(|&(a,)| a)
            .collect();

        let combined: ascent::boxcar::Vec<(Address,)> =
            existing.into_iter().map(|a| (a,)).collect();
        for addr in trimmed {
            combined.push((addr,));
        }
        db.rel_set("trim_instruction", combined);
    }

    // Bridge next edges across trimmed ranges so downstream passes don't get orphan nodes.
    let alloca_addrs: BTreeSet<Address> = vla_allocas.iter().map(|&(addr, _, _)| addr).collect();

    let all_trimmed: BTreeSet<Address> = db.rel_iter::<(Address,)>("trim_instruction")
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

    let alloca_rel: ascent::boxcar::Vec<(Address, Mreg, Mreg)> = vla_allocas.into_iter().collect();
    db.rel_set("vla_alloca", alloca_rel);
}
