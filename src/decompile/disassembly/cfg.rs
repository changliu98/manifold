use crate::abi::Arch;
use crate::decompile::disassembly::branch;
use crate::decompile::disassembly::instruction::DecodedInsn;
use crate::decompile::elevator::config::CONFIG;
use crate::decompile::elevator::DecompileDB;
use crate::mreg::Mreg;
use crate::x86::types::*;
use object::{Object, ObjectSection};
use std::collections::{HashMap, HashSet};

// Read a little-endian u64 from the given address using preloaded section data.
fn read_u64_at(section_data: &[(u64, u64, Vec<u8>)], addr: u64) -> Option<u64> {
    for (start, end, data) in section_data {
        if addr >= *start && addr + 8 <= *end {
            let off = (addr - start) as usize;
            return Some(u64::from_le_bytes(data[off..off + 8].try_into().ok()?));
        }
    }
    None
}

// Read a little-endian i32 from the given address using preloaded section data.
fn read_i32_at(section_data: &[(u64, u64, Vec<u8>)], addr: u64) -> Option<i32> {
    for (start, end, data) in section_data {
        if addr >= *start && addr + 4 <= *end {
            let off = (addr - start) as usize;
            return Some(i32::from_le_bytes(data[off..off + 4].try_into().ok()?));
        }
    }
    None
}

// Build CFG edges, direct calls/jumps, and flags-and-jump pairs; AArch64's B.<cond> codes map onto the x86 condition vocabulary so downstream keeps one alphabet.
fn branch_condition(arch: Arch, mnem: &str) -> Option<&'static str> {
    match arch {
        Arch::Aarch64 => Some(match mnem.strip_prefix("B.")? {
            "EQ" => "e",
            "NE" => "ne",
            "LT" => "l",
            "LE" => "le",
            "GT" => "g",
            "GE" => "ge",
            "LO" | "CC" => "b",
            "LS" => "be",
            "HI" => "a",
            "HS" | "CS" => "ae",
            "MI" => "s",
            "PL" => "ns",
            "VS" => "o",
            "VC" => "no",
            _ => return None,
        }),
        // A32 spells the condition on ANY instruction, not only on branches: `MOV.GT` consumes the flags exactly as `B.GT` does, and the arm32 frontend turns that pairing into a select. The decoder publishes the condition as a dotted suffix rather than glued to the stem, since `MOVS`/`MULS` would otherwise be misread as MOV+VS and MUL+LS.
        Arch::Arm32 => {
            let (_, cc) = mnem.split_once('.')?;
            Some(match cc {
                "EQ" => "e",
                "NE" => "ne",
                "LT" => "l",
                "LE" => "le",
                "GT" => "g",
                "GE" => "ge",
                "LO" | "CC" => "b",
                "LS" => "be",
                "HI" => "a",
                "HS" | "CS" => "ae",
                "MI" => "s",
                "PL" => "ns",
                "VS" => "o",
                "VC" => "no",
                _ => return None,
            })
        }
        _ => Some(match mnem {
            "JE" => "e",
            "JNE" => "ne",
            "JL" => "l",
            "JLE" => "le",
            "JG" => "g",
            "JGE" => "ge",
            "JB" => "b",
            "JBE" => "be",
            "JA" => "a",
            "JAE" => "ae",
            "JP" => "p",
            "JNP" => "np",
            "JO" => "o",
            "JNO" => "no",
            "JS" => "s",
            "JNS" => "ns",
            _ => return None,
        }),
    }
}

// Flag definitions whose result downstream can describe. A branch consumes
// the nearest reaching definition regardless of whether the ISA spells it as
// a compare or as a value-producing ALU instruction. On AArch64 only the
// S-suffixed forms write NZCV, hence SUBS/ANDS but not SUB/AND.
fn is_modeled_flags_origin(arch: Arch, mnem: &str) -> bool {
    match arch {
        Arch::Aarch64 => matches!(
            mnem,
            "CMP"
                | "CMN"
                | "TST"
                | "SUBS"
                | "ADDS"
                | "ANDS"
                | "BICS"
                | "CCMP"
                | "CCMN"
                | "FCMP"
                | "FCMPE"
        ),
        // ARM32 writes the flags from CMP/CMN/TST/TEQ and from every S-suffixed data-processing form, which sets them from the RESULT it leaves in its destination; `SUBS Rn,Rn,#1` before a B.NE is the canonical counted loop, and Thumb's 16-bit encodings set flags that way even without an explicit S in the source. This set must stay in step with arm32_asm_pass::sets_flags_from_result, which is what reads the compared value back off the destination operand.
        Arch::Arm32 => matches!(
            mnem,
            "CMP"
                | "CMN"
                | "TST"
                | "TEQ"
                | "VCMP"
                | "VCMPE"
                | "SUBS"
                | "ADDS"
                | "ANDS"
                | "ORRS"
                | "EORS"
                | "BICS"
                | "RSBS"
                | "MOVS"
                | "MVNS"
                | "MULS"
                | "LSLS"
                | "LSRS"
                | "ASRS"
                | "RORS"
                | "ADCS"
                | "SBCS"
        ),
        _ => matches!(
            mnem,
            "CMP"
                | "TEST"
                | "SUB"
                | "AND"
                | "ADD"
                | "OR"
                | "XOR"
                | "NEG"
                | "SHR"
                | "SAR"
                | "INC"
                | "DEC"
        ),
    }
}

// Instructions that overwrite the flags without a downstream model, ending
// the backward walk. NOT is absent because x86 NOT preserves every flag.
fn clobbers_flags(arch: Arch, mnem: &str) -> bool {
    match arch {
        Arch::Aarch64 => matches!(mnem, "NEGS" | "SBCS" | "ADCS" | "FCCMP" | "FCCMPE"),
        // The remaining ARM32 flag writers: forms whose compared value the frontend cannot read back off the destination operand -- the long multiplies write a register PAIR, and RRXS folds in the carry -- so pairing a branch with one would test the wrong value. They end the walk instead.
        Arch::Arm32 => matches!(
            mnem,
            "RSCS" | "MLAS" | "MLSS" | "RRXS" | "UMULLS" | "SMULLS" | "UMLALS" | "SMLALS"
        ),
        _ => matches!(
            mnem,
            "SHL"
                | "SAL"
                | "IMUL"
                | "MUL"
                | "DIV"
                | "IDIV"
                | "ADC"
                | "SBB"
                | "RCL"
                | "RCR"
                | "ROL"
                | "ROR"
                | "BSF"
                | "BSR"
                | "POPCNT"
                | "LZCNT"
                | "TZCNT"
        ),
    }
}

// Control transfers that end the backward walk: deliberately not every transfer, exactly the pre-existing x86 set, which lets the walk cross a conditional branch.
fn terminates_flag_search(arch: Arch, mnem: &str) -> bool {
    match arch {
        Arch::Aarch64 => matches!(mnem, "B" | "BL" | "BLR" | "BR" | "RET" | "BRK"),
        // Deliberately not every ARM32 transfer: like the x86 set, the walk crosses conditional branches, which is what lets one CMP feed a run of if-converted instructions.
        Arch::Arm32 => matches!(
            mnem,
            "B" | "BL" | "BLX" | "BX" | "BXJ" | "BKPT" | "UDF" | "TBB" | "TBH"
        ),
        _ => matches!(mnem, "JMP" | "JMPQ" | "CALL" | "RET" | "HLT" | "INT3"),
    }
}

pub fn build_cfg(
    db: &mut DecompileDB,
    insns: &[DecodedInsn],
    obj: &object::File,
    jump_table_targets: HashMap<u64, JumpTableInfo>,
) {
    if insns.is_empty() {
        return;
    }

    // Pre-compute direct branch targets; the target's operand slot is arch-specific, so it comes from branch::BranchInfo rather than being assumed first.
    let arch = db.abi().arch;
    let op_imm_map = super::build_op_imm_map(db);

    let mut direct_targets: std::collections::HashMap<u64, u64> = std::collections::HashMap::new();
    for (addr, _, _, mnem, op1, op2, op3, op4, _, _) in db.rel_iter::<(
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
    )>("unrefinedinstruction")
    {
        let Some(slot) = branch::direct_target_op(arch, mnem) else {
            continue;
        };
        let op1 = &[*op1, *op2, *op3, *op4][slot];
        if *op1 == "0" {
            continue;
        }
        if let Some(&val) = op_imm_map.get(op1) {
            direct_targets.insert(*addr, val as u64);
        }
    }

    let rip_targets = build_rip_target_map(db, insns, obj);

    let get_target = |addr: u64| -> Option<u64> {
        if let Some(&t) = direct_targets.get(&addr) {
            Some(t)
        } else {
            rip_targets.get(&addr).copied()
        }
    };

    let addr_set: std::collections::HashSet<u64> = insns.iter().map(|d| d.address).collect();

    let block_last_insns: std::collections::HashSet<u64> = db
        .rel_iter::<(Address, Address, Address)>("block_boundaries")
        .map(|(_, last, _)| *last)
        .collect();

    // Pre-build op1 lookup and register/indirect operand sets for indirect branch detection
    let mut addr_to_op1: HashMap<u64, &'static str> = HashMap::new();
    for (addr, _sz, _pfx, _mnem, op1, _op2, _op3, _op4, _, _) in db.rel_iter::<(
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
    )>("unrefinedinstruction")
    {
        addr_to_op1.insert(*addr, *op1);
    }
    let op_register_ids: HashSet<&'static str> = db
        .rel_iter::<(Symbol, &'static str)>("op_register")
        .map(|(id, _)| *id)
        .collect();
    let op_indirect_ids: HashSet<&'static str> = db
        .rel_iter::<(
            Symbol,
            &'static str,
            &'static str,
            &'static str,
            i64,
            i64,
            usize,
        )>("op_indirect")
        .map(|(id, ..)| *id)
        .collect();

    // Only emit inter-block edges to match ddisasm semantics
    let mut cfg_edges: Vec<(u64, u64, &'static str)> = Vec::new();
    let mut direct_calls: Vec<(u64, u64)> = Vec::new();
    let mut direct_jumps: Vec<(u64, u64)> = Vec::new();

    for (i, insn) in insns.iter().enumerate() {
        let next_addr = insn.address + insn.size as u64;

        // A register or memory operand rather than an immediate means the transfer target is computed, not encoded.
        let has_computed_target = || {
            addr_to_op1.get(&insn.address).map_or(false, |op1| {
                *op1 != "0" && (op_register_ids.contains(op1) || op_indirect_ids.contains(op1))
            })
        };
        let push_fallthrough = |edges: &mut Vec<(u64, u64, &'static str)>| {
            if i + 1 < insns.len() && addr_set.contains(&next_addr) {
                edges.push((insn.address, next_addr, "fallthrough"));
            }
        };

        match branch::classify(arch, insn.mnemonic, insn.pc_source).kind {
            // x86 spells both direct and register/memory forms "JMP", so this arm still needs the computed-target check; AArch64 splits them into B and BR.
            branch::BranchKind::UncondJump => {
                if let Some(target) = get_target(insn.address) {
                    cfg_edges.push((insn.address, target, "branch"));
                    direct_jumps.push((insn.address, target));
                } else if let Some(info) = jump_table_targets.get(&insn.address) {
                    let mut unique_targets: Vec<u64> = info.ordered_targets.clone();
                    unique_targets.sort();
                    unique_targets.dedup();
                    for &target in &unique_targets {
                        cfg_edges.push((insn.address, target, "branch"));
                        direct_jumps.push((insn.address, target));
                    }
                } else if has_computed_target() {
                    cfg_edges.push((insn.address, 0, "indirect"));
                }
            }
            branch::BranchKind::IndirectJump => {
                if let Some(info) = jump_table_targets.get(&insn.address) {
                    let mut unique_targets: Vec<u64> = info.ordered_targets.clone();
                    unique_targets.sort();
                    unique_targets.dedup();
                    for &target in &unique_targets {
                        cfg_edges.push((insn.address, target, "branch"));
                        direct_jumps.push((insn.address, target));
                    }
                } else {
                    cfg_edges.push((insn.address, 0, "indirect"));
                }
            }
            branch::BranchKind::Call => {
                if let Some(target) = get_target(insn.address) {
                    cfg_edges.push((insn.address, target, "call"));
                    direct_calls.push((insn.address, target));
                } else if has_computed_target() {
                    cfg_edges.push((insn.address, 0, "indirect_call"));
                }
                push_fallthrough(&mut cfg_edges);
            }
            branch::BranchKind::IndirectCall => {
                cfg_edges.push((insn.address, 0, "indirect_call"));
                push_fallthrough(&mut cfg_edges);
            }
            // Terminal: no successor edge.
            branch::BranchKind::Return | branch::BranchKind::Trap => {}
            branch::BranchKind::CondJump => {
                if let Some(target) = get_target(insn.address) {
                    cfg_edges.push((insn.address, target, "branch"));
                    direct_jumps.push((insn.address, target));
                }
                push_fallthrough(&mut cfg_edges);
            }
            // Fallthrough only at block boundaries (last insn of block to next block).
            branch::BranchKind::None | branch::BranchKind::OpaqueTransfer => {
                if block_last_insns.contains(&insn.address) {
                    push_fallthrough(&mut cfg_edges);
                }
            }
        }
    }

    // Pair each conditional jump with the modeled definition whose flags REACH it.
    //
    // Which instruction produces the flags a jump consumes is a reaching-definition question, so it
    // is answered over the CFG built above. It used to be answered by walking the address-sorted
    // instruction array backward, which is exactly the proxy CLAUDE.md forbids: two instructions
    // on disjoint branches are adjacent in address order, and that walk deliberately crossed
    // conditional branches, so a jump reached by a branch could be paired with a compare that
    // only executes on the path NOT taken -- recovering a condition over the wrong operands.
    //
    // Inside one block address order IS execution order, so the intra-block search below is
    // sound and resolves the overwhelmingly common `cmp; jcc` case exactly as before. Only when
    // a block does not define the flags does this consult the CFG, and there it keeps EVERY
    // reaching origin rather than guessing one, per the high-recall rule for Ascent inputs.
    let mut flags_pairs: Vec<(u64, u64, &'static str)> = Vec::new();
    {
        use std::collections::{BTreeSet, HashMap as Map};

        #[derive(Clone, Copy, PartialEq)]
        enum Effect {
            Origin(u64),
            Kill,
        }
        let effect_of = |d: &DecodedInsn| -> Option<Effect> {
            if is_modeled_flags_origin(arch, d.mnemonic) {
                Some(Effect::Origin(d.address))
            } else if clobbers_flags(arch, d.mnemonic) || terminates_flag_search(arch, d.mnemonic) {
                Some(Effect::Kill)
            } else {
                None
            }
        };

        let insn_block: Map<u64, u64> = db
            .rel_iter::<(Address, Address)>("code_in_block")
            .map(|(a, b)| (*a, *b))
            .collect();

        let mut block_insns: Map<u64, Vec<usize>> = Map::new();
        for (i, d) in insns.iter().enumerate() {
            if let Some(&b) = insn_block.get(&d.address) {
                block_insns.entry(b).or_default().push(i);
            }
        }

        // Predecessors over edges that land on a block LEADER. An edge into the middle of a block
        // (a call's fallthrough) needs no entry here: the intra-block scan already covers that
        // point, and a call kills the flags at it anyway.
        // Ordered: the fixpoint below must not depend on iteration order for its RESULT to be
        // reproducible, and a hash order would make that true only by luck.
        let mut preds: std::collections::BTreeMap<u64, Vec<u64>> =
            std::collections::BTreeMap::new();
        for (src, dst, kind) in &cfg_edges {
            if !matches!(*kind, "branch" | "fallthrough") {
                continue;
            }
            if insn_block.get(dst) != Some(dst) {
                continue;
            }
            if let Some(&sb) = insn_block.get(src) {
                preds.entry(*dst).or_default().push(sb);
            }
        }

        // What each block leaves in the flags at its exit; absent = transparent, so its exit state
        // is whatever reached its entry.
        let block_effect: Map<u64, Effect> = block_insns
            .iter()
            .filter_map(|(&b, idxs)| {
                idxs.iter()
                    .rev()
                    .find_map(|&i| effect_of(&insns[i]))
                    .map(|e| (b, e))
            })
            .collect();

        // Forward fixpoint: in[b] = union of out[pred]; out[b] = its own definition, else in[b].
        let mut flags_in: std::collections::BTreeMap<u64, BTreeSet<u64>> =
            std::collections::BTreeMap::new();
        let out_of =
            |b: u64, flags_in: &std::collections::BTreeMap<u64, BTreeSet<u64>>| -> BTreeSet<u64> {
                match block_effect.get(&b) {
                    Some(Effect::Origin(a)) => BTreeSet::from([*a]),
                    Some(Effect::Kill) => BTreeSet::new(),
                    None => flags_in.get(&b).cloned().unwrap_or_default(),
                }
            };
        // Terminates without an artificial round cap: the values are sets of comparison addresses
        // drawn from a finite pool, they start empty and only ever grow by union, and the transfer
        // is monotone. A cap here would be worse than useless -- truncating the fixpoint would
        // leave the answer dependent on how far it happened to get.
        let mut changed = true;
        while changed {
            changed = false;
            for (&b, ps) in &preds {
                let mut merged = BTreeSet::new();
                for &p in ps {
                    merged.extend(out_of(p, &flags_in));
                }
                if flags_in.get(&b) != Some(&merged) {
                    flags_in.insert(b, merged);
                    changed = true;
                }
            }
        }

        for (i, insn) in insns.iter().enumerate() {
            let Some(cond) = branch_condition(arch, insn.mnemonic) else {
                continue;
            };
            let Some(&b) = insn_block.get(&insn.address) else {
                continue;
            };
            let Some(idxs) = block_insns.get(&b) else {
                continue;
            };

            // Backward within the block first: exact when the block defines the flags itself.
            let mut resolved = false;
            for &j in idxs.iter().rev().skip_while(|&&j| j != i).skip(1) {
                match effect_of(&insns[j]) {
                    Some(Effect::Origin(a)) => {
                        flags_pairs.push((a, insn.address, cond));
                        resolved = true;
                        break;
                    }
                    Some(Effect::Kill) => {
                        resolved = true;
                        break;
                    }
                    None => {}
                }
            }
            if resolved {
                continue;
            }
            // Otherwise the flags come from whatever reaches this block's entry.
            if let Some(reaching) = flags_in.get(&b) {
                for &a in reaching {
                    flags_pairs.push((a, insn.address, cond));
                }
            }
        }
    }

    db.rel_set(
        "ddisasm_cfg_edge",
        cfg_edges.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "direct_call",
        direct_calls.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "direct_jump",
        direct_jumps.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "flags_and_jump_pair",
        flags_pairs.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );

    // Populate jump table relations (targets, implementation addrs, bounds check, index register)
    for (&jmp_addr, info) in &jump_table_targets {
        for (idx, &target) in info.ordered_targets.iter().enumerate() {
            db.rel_push("jump_table_target", (jmp_addr, idx, target));
        }
        for &impl_addr in &info.impl_addrs {
            db.rel_push("jump_table_impl", (impl_addr, jmp_addr));
        }
        if let Some(cmp_addr) = info.cmp_addr {
            db.rel_push("jump_table_cmp", (jmp_addr, cmp_addr));
        }
        if let Some(ref reg) = info.index_reg {
            let reg_str: &'static str = Box::leak(reg.clone().into_boxed_str());
            db.rel_push("jump_table_index_reg", (jmp_addr, reg_str));
        }
    }
}

// Resolve RIP-relative CALL/JMP targets via GOT slot reads and GOT-to-PLT fallback.
fn build_rip_target_map(
    db: &DecompileDB,
    insns: &[DecodedInsn],
    obj: &object::File,
) -> HashMap<u64, u64> {
    let mut result: HashMap<u64, u64> = HashMap::new();

    let addr_set: std::collections::HashSet<u64> = insns.iter().map(|d| d.address).collect();

    let got_to_plt = build_got_to_plt_map(db, obj);

    let section_data: Vec<(u64, u64, Vec<u8>)> = obj
        .sections()
        .filter_map(|s| {
            let data = s.data().ok()?;
            if data.is_empty() {
                return None;
            }
            Some((s.address(), s.address() + data.len() as u64, data.to_vec()))
        })
        .collect();

    let mut rip_op_info: HashMap<&'static str, i64> = HashMap::new();
    for (id, _seg, base, _index, _scale, disp, _) in db.rel_iter::<(
        Symbol,
        &'static str,
        &'static str,
        &'static str,
        i64,
        i64,
        usize,
    )>("op_indirect")
    {
        if *base == "RIP" {
            rip_op_info.insert(*id, *disp);
        }
    }
    if rip_op_info.is_empty() {
        return result;
    }

    for (addr, size, _pfx, mnem, op1, _op2, _op3, _op4, _, _) in db.rel_iter::<(
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
    )>("unrefinedinstruction")
    {
        if !matches!(
            *mnem,
            "CALL"
                | "JMP"
                | "JE"
                | "JNE"
                | "JL"
                | "JLE"
                | "JG"
                | "JGE"
                | "JB"
                | "JBE"
                | "JA"
                | "JAE"
                | "JP"
                | "JNP"
                | "JO"
                | "JNO"
                | "JS"
                | "JNS"
        ) {
            continue;
        }
        if let Some(&disp) = rip_op_info.get(op1) {
            let got_addr = (*addr as i64 + *size as i64 + disp) as u64;

            if let Some(target) = read_u64_at(&section_data, got_addr) {
                if target > 0 && addr_set.contains(&target) {
                    result.insert(*addr, target);
                    continue;
                }
            }

            if let Some(&plt_addr) = got_to_plt.get(&got_addr) {
                result.insert(*addr, plt_addr);
            }
        }
    }

    result
}

// Resolved jump table information for a single indirect JMP.
pub struct JumpTableInfo {
    pub ordered_targets: Vec<u64>,
    pub impl_addrs: Vec<u64>,
    pub cmp_addr: Option<u64>,
    pub index_reg: Option<String>,
}

// Clang data lookup table: switch results loaded from value table, not indirect jump.
pub struct DataLookupTableInfo {
    pub table_base: u64,
    pub entry_count: usize,
    pub entry_scale: i64,               // 4 or 8 (byte width per entry)
    pub values: Vec<i64>,               // the actual data values from the table
    pub mov_addr: u64,                  // address of the MOV instruction
    pub bounds_check_addr: Option<u64>, // address of CMP/AND instruction
    pub index_reg: Option<String>,
}

// Analyze jump tables (switch statements) and return resolved targets per indirect JMP.
pub fn analyze_jump_tables(
    db: &DecompileDB,
    insns: &[DecodedInsn],
    obj: &object::File,
) -> HashMap<u64, JumpTableInfo> {
    let mut result: HashMap<u64, JumpTableInfo> = HashMap::new();

    let addr_set: HashSet<u64> = insns.iter().map(|d| d.address).collect();

    let section_data: Vec<(u64, u64, Vec<u8>)> = obj
        .sections()
        .filter_map(|s| {
            let data = s.data().ok()?;
            if data.is_empty() {
                return None;
            }
            Some((s.address(), s.address() + data.len() as u64, data.to_vec()))
        })
        .collect();

    let op_imm_map = super::build_op_imm_map(db);

    let mut op_reg_map: HashMap<&str, &str> = HashMap::new();
    for (id, reg) in db.rel_iter::<(Symbol, &'static str)>("op_register") {
        op_reg_map.insert(id, reg);
    }

    let mut rip_indirect_map: HashMap<&str, i64> = HashMap::new();
    let mut op_indirect_map: HashMap<&str, (&str, &str, &str, i64, i64)> = HashMap::new();
    for (id, _seg, base, index, scale, disp, _) in db.rel_iter::<(
        Symbol,
        &'static str,
        &'static str,
        &'static str,
        i64,
        i64,
        usize,
    )>("op_indirect")
    {
        if *base == "RIP" {
            rip_indirect_map.insert(*id, *disp);
        }
        op_indirect_map.insert(*id, (*_seg, *base, *index, *scale, *disp));
    }

    let mut insn_by_addr: HashMap<u64, &DecodedInsn> = HashMap::new();
    for insn in insns {
        insn_by_addr.insert(insn.address, insn);
    }

    let mut unrefined_by_addr: HashMap<u64, (usize, &str, &str, &str)> = HashMap::new();
    for (addr, size, _pfx, mnem, op1, op2, _op3, _op4, _, _) in db.rel_iter::<(
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
    )>("unrefinedinstruction")
    {
        unrefined_by_addr.insert(*addr, (*size, *mnem, *op1, *op2));
    }

    let mut df = InsnDataflow::build(db.abi().arch, insns, db, &unrefined_by_addr, &op_imm_map);

    let mut indirect_jmp_sites = 0usize;
    let mut ambiguous: Vec<AmbiguousJump> = Vec::new();

    for insn in insns {
        if insn.mnemonic != "JMP" {
            continue;
        }

        let (_, mnem, op1, op2) = match unrefined_by_addr.get(&insn.address) {
            Some(info) => *info,
            None => continue,
        };

        if mnem != "JMP" {
            continue;
        }

        // Only indirect JMPs (register/memory operand, not RIP-relative); check both op1 and op2 since instruction.rs's operand swap puts single-operand JMP targets into op2 (op1 becomes "0").
        let check_op = |op: &str| -> bool {
            if op == "0" {
                return false;
            }
            if op_reg_map.contains_key(op) {
                return true;
            }
            if let Some(&(_seg, base, _index, _scale, _disp)) = op_indirect_map.get(op) {
                return base != "RIP";
            }
            false
        };
        if !check_op(op1) && !check_op(op2) {
            continue;
        }
        indirect_jmp_sites += 1;

        let info = find_jump_table_info(
            insn.address,
            insns,
            &mut df,
            &unrefined_by_addr,
            &op_imm_map,
            &op_reg_map,
            &rip_indirect_map,
            &op_indirect_map,
            &addr_set,
            &section_data,
            &mut ambiguous,
        );

        if let Some(info) = info {
            result.insert(insn.address, info);
        }
    }

    dump_jump_tables(indirect_jmp_sites, &ambiguous, &result);

    result
}

// One indirect jump declined because two bases reached it equally directly,
// recorded so a decline can be explained rather than merely counted: which
// jump, how many definitions upstream the tie sat, and each base with the
// instruction that materialized it. The defining address is the half that
// makes a decline diagnosable -- it says which path the losing base came in
// on.
struct AmbiguousJump {
    jmp: u64,
    depth: u32,
    bases: Vec<(u64, u64)>,
}

// Deterministic diagnostic dump of what indirect-jump recovery found, so one
// revision's table set can be compared against another's over a whole corpus.
// Reports only; nothing here changes what the pipeline sees. The summary line
// comes last, which is what makes a truncated dump recognizable.
fn dump_jump_tables(
    indirect_jmp_sites: usize,
    ambiguous: &[AmbiguousJump],
    result: &HashMap<u64, JumpTableInfo>,
) {
    if std::env::var_os("MANIFOLD_DUMP_JUMP_TABLES").is_none() {
        return;
    }
    let mut declined: Vec<&AmbiguousJump> = ambiguous.iter().collect();
    declined.sort_by_key(|a| a.jmp);
    for a in declined {
        let competing: Vec<String> = a
            .bases
            .iter()
            .map(|(base, at)| format!("{:x}@{:x}", base, at))
            .collect();
        println!(
            "jump-table-ambiguous {:x} depth {} bases {}",
            a.jmp,
            a.depth,
            competing.join(",")
        );
    }
    let mut sites: Vec<&u64> = result.keys().collect();
    sites.sort();
    for jmp in sites {
        let info = &result[jmp];
        let targets: Vec<String> = info
            .ordered_targets
            .iter()
            .map(|t| format!("{:x}", t))
            .collect();
        println!(
            "jump-table {:x} entries {} impl {} targets {}",
            jmp,
            info.ordered_targets.len(),
            info.impl_addrs.len(),
            targets.join(",")
        );
    }
    println!(
        "jump-table-sites {} resolved {} ambiguous {}",
        indirect_jmp_sites,
        result.len(),
        ambiguous.len()
    );
}

// Instruction-level dataflow substrate for indirect-jump recovery: the control
// flow this stage can already see, plus the registers each instruction reads
// and writes.
//
// Which instruction materializes a jump table's base is a reaching-definition
// question -- the base is whatever the register feeding the jump was last
// assigned along a path that reaches it. It used to be answered by scanning a
// fixed number of instructions backward in address order, which is the
// proximity proxy CLAUDE.md forbids: whether a dispatch was recovered depended
// on how many unrelated instructions the scheduler happened to place in
// between, and a base kept in a callee-saved register across a call sat
// outside any window at all. This walks the CFG instead, so distance never
// enters the answer.
struct InsnDataflow {
    index_of: HashMap<u64, u32>,
    // Predecessors over intraprocedural edges only. A call contributes its
    // fallthrough and never an edge into the callee, and no edge at all enters
    // a function entry, so a walk stays inside the one function that computes
    // the jump target.
    preds: Vec<Vec<u32>>,
    // The fallthrough predecessor, when it is this instruction's only
    // predecessor. Following it yields the straight-line region ending at an
    // instruction: it stops where control flow joins, not after a fixed count.
    linear_pred: Vec<Option<u32>>,
    // The entry of the function each instruction belongs to. Dominance is a
    // question about one function -- whether control can get from that
    // function's entry to a point without crossing some instruction -- so the
    // entry has to be named. Asking instead whether any entry at all is
    // reachable answers a different question and gets it wrong: gcc gives a
    // cold fragment of a function its own frame description, and that fragment
    // jumps back into the warm body, so it reads as a second way in.
    entry_of: Vec<Option<u32>>,
    defs: Vec<Vec<Mreg>>,
    uses: Vec<Vec<Mreg>>,
    // Visit stamps, so a backward walk costs no allocation.
    stamp: Vec<u32>,
    epoch: u32,
    // Answers already computed. Indirect jumps in one function share chains,
    // and each answer is a set, so caching changes nothing but the cost.
    memo: HashMap<(u32, Mreg), Vec<u32>>,
}

impl InsnDataflow {
    fn build(
        arch: Arch,
        insns: &[DecodedInsn],
        db: &DecompileDB,
        unrefined_by_addr: &HashMap<u64, (usize, &str, &str, &str)>,
        op_imm_map: &HashMap<&str, i64>,
    ) -> InsnDataflow {
        let n = insns.len();
        let mut index_of: HashMap<u64, u32> = HashMap::with_capacity(n);
        for (i, d) in insns.iter().enumerate() {
            index_of.insert(d.address, i as u32);
        }

        // A function entry has no predecessor inside its own function: it is
        // reached from another frame, by a call or by a tail jump that already
        // restored the caller's registers. An edge into one is therefore the
        // point where a backward walk would leave the function it is resolving
        // a dispatch in, and keeping it makes the walk answer with a register
        // value some unrelated function computed.
        let entries = function_entry_addrs(db);
        let is_entry: Vec<bool> = insns.iter().map(|d| entries.contains(&d.address)).collect();

        // A call to a function that never returns does not resume at the next
        // instruction; what the linker placed there belongs to some other path.
        // The entry set already cuts the common case -- the abort stub gcc emits
        // for an unreachable path is its own function, and so is whatever
        // follows it -- but a noreturn call inside a function has no entry after
        // it, and an invented edge past one joins two paths that never join.
        let noreturn_entries = noreturn_callee_addrs(db);

        let mut preds: Vec<Vec<u32>> = vec![Vec::new(); n];
        let mut fallthrough_pred: Vec<Option<u32>> = vec![None; n];
        for (i, insn) in insns.iter().enumerate() {
            let kind = branch::classify(arch, insn.mnemonic, insn.pc_source).kind;
            let direct = direct_branch_target(arch, insn, unrefined_by_addr, op_imm_map);
            // A jump continues along its own target; a call resumes at the next
            // instruction and its callee is a separate region, so a call edge
            // is deliberately absent here.
            if matches!(
                kind,
                branch::BranchKind::UncondJump | branch::BranchKind::CondJump
            ) {
                if let Some(target) = direct {
                    if let Some(&j) = index_of.get(&target) {
                        if !is_entry[j as usize] {
                            preds[j as usize].push(i as u32);
                        }
                    }
                }
            }
            let resumes = !matches!(kind, branch::BranchKind::Call)
                || direct.map_or(true, |t| !noreturn_entries.contains(&t));
            if kind.falls_through() && resumes {
                let next = insn.address + insn.size as u64;
                if let Some(&j) = index_of.get(&next) {
                    if !is_entry[j as usize] {
                        preds[j as usize].push(i as u32);
                        fallthrough_pred[j as usize] = Some(i as u32);
                    }
                }
            }
        }

        let linear_pred: Vec<Option<u32>> = (0..n)
            .map(|i| match fallthrough_pred[i] {
                Some(p) if preds[i].len() == 1 => Some(p),
                _ => None,
            })
            .collect();

        let mut defs: Vec<Vec<Mreg>> = vec![Vec::new(); n];
        let mut uses: Vec<Vec<Mreg>> = vec![Vec::new(); n];
        for (addr, reg) in db.rel_iter::<(Address, Mreg)>("reg_def") {
            if let Some(&i) = index_of.get(addr) {
                defs[i as usize].push(*reg);
            }
        }
        for (addr, reg) in db.rel_iter::<(Address, Mreg)>("reg_use") {
            if let Some(&i) = index_of.get(addr) {
                uses[i as usize].push(*reg);
            }
        }
        // A returning call preserves the CFG fallthrough but not the values in
        // caller-saved registers. Treat the ABI clobbers as ordinary
        // definitions at the call so a reaching-definition walk stops there;
        // otherwise table recovery can reuse a base or index computed before
        // an arbitrary callee. Callee-saved registers deliberately remain
        // live across the same edge.
        for (i, insn) in insns.iter().enumerate() {
            if matches!(
                branch::classify(arch, insn.mnemonic, insn.pc_source).kind,
                branch::BranchKind::Call
            ) {
                defs[i].extend(db.abi().caller_saved.iter().copied());
            }
        }
        // Sorted and deduplicated: the walks binary-search these, and every
        // answer they produce must be independent of relation order.
        for v in defs.iter_mut().chain(uses.iter_mut()) {
            v.sort();
            v.dedup();
        }

        InsnDataflow {
            index_of,
            preds,
            linear_pred,
            entry_of: entry_of_each(db, insns),
            defs,
            uses,
            stamp: vec![0; n],
            epoch: 0,
            memo: HashMap::new(),
        }
    }

    // Whether control can arrive at `at` from `entry` without crossing
    // `blocked`. Only the backward edges answer this; blocking one instruction
    // and asking what is still reachable is the whole test.
    fn entry_reaches(&mut self, at: u32, entry: u32, blocked: Option<u32>) -> bool {
        self.epoch += 1;
        let InsnDataflow {
            preds,
            stamp,
            epoch,
            ..
        } = self;
        let epoch = *epoch;
        let mut stack: Vec<u32> = preds[at as usize].clone();
        while let Some(p) = stack.pop() {
            if Some(p) == blocked || stamp[p as usize] == epoch {
                continue;
            }
            stamp[p as usize] = epoch;
            if p == entry {
                return true;
            }
            stack.extend_from_slice(&preds[p as usize]);
        }
        false
    }

    // Whether `def` dominates `at`: every path from the function's entry to
    // `at` crosses it. A definition that does not dominate only reaches on some
    // paths -- around a loop that has already run through `at` once, or past a
    // call that never returns and so joins two pieces of code that never join
    // -- so when two definitions offer different table bases, the one that
    // dominates is the value the dispatch always reads. The question is asked
    // only where the entry can reach `at` at all; a region this stage cannot
    // yet enter, such as a switch arm behind an unresolved indirect jump, has
    // no dominance to speak of and gets no answer.
    fn dominates(&mut self, def: u32, at: u32) -> bool {
        let entry = match self.entry_of[at as usize] {
            Some(e) => e,
            None => return false,
        };
        self.entry_reaches(at, entry, None) && !self.entry_reaches(at, entry, Some(def))
    }

    // Definitions of `reg` that reach the point just before `at`: the first
    // definition on every backward path. Only edges decide whether a
    // definition reaches; no address, index or distance comparison appears.
    // The walk terminates because each instruction is stamped once per query,
    // so no bound on how far back it may look is needed or wanted.
    fn reaching_defs(&mut self, at: u32, reg: Mreg) -> Vec<u32> {
        if let Some(cached) = self.memo.get(&(at, reg)) {
            return cached.clone();
        }
        self.epoch += 1;
        let InsnDataflow {
            preds,
            defs,
            stamp,
            epoch,
            ..
        } = self;
        let epoch = *epoch;
        let mut out: Vec<u32> = Vec::new();
        let mut stack: Vec<u32> = preds[at as usize].clone();
        while let Some(p) = stack.pop() {
            if stamp[p as usize] == epoch {
                continue;
            }
            stamp[p as usize] = epoch;
            if defs[p as usize].binary_search(&reg).is_ok() {
                out.push(p);
            } else {
                stack.extend_from_slice(&preds[p as usize]);
            }
        }
        out.sort();
        self.memo.insert((at, reg), out.clone());
        out
    }
}

// Walk the unique fallthrough chain ending at `at`. This is the structural
// counterpart of a backward instruction window: it may be arbitrarily long,
// but stops immediately at a CFG join, function boundary, or non-fallthrough
// edge. The current instruction is not yielded.
fn linear_predecessors(dataflow: &InsnDataflow, at: u32) -> impl Iterator<Item = u32> + '_ {
    std::iter::successors(dataflow.linear_pred[at as usize], move |&pred| {
        dataflow.linear_pred[pred as usize]
    })
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum StablePointerMode {
    TailTarget,
    AddressBase,
}

struct IndirectTailClassifier<'a> {
    arch: Arch,
    insns: &'a [DecodedInsn],
    operands: &'a HashMap<Address, [Symbol; 4]>,
    op_indirect: &'a HashMap<Symbol, (&'static str, &'static str, &'static str, i64, i64)>,
    abi_args: HashSet<Mreg>,
    dataflow: InsnDataflow,
}

impl IndirectTailClassifier<'_> {
    fn mreg(&self, name: &str) -> Mreg {
        match self.arch {
            Arch::Aarch64 => Mreg::a64(name),
            Arch::Arm32 => Mreg::a32(name),
            _ => Mreg::Unknown,
        }
    }

    fn stem<'a>(&self, mnemonic: &'a str) -> &'a str {
        if self.arch == Arch::Arm32 {
            mnemonic.split_once('.').map_or(mnemonic, |(stem, _)| stem)
        } else {
            mnemonic
        }
    }

    fn meaningful_uses(&self, at: u32) -> Vec<Mreg> {
        self.dataflow.uses[at as usize]
            .iter()
            .copied()
            .filter(|reg| {
                !matches!(
                    reg,
                    Mreg::A64(crate::aarch64::mach::A64Mreg::ZR)
                        | Mreg::A32(crate::arm32::mach::A32Mreg::PC)
                )
            })
            .collect()
    }

    fn is_intrinsic_address_base(&self, reg: Mreg) -> bool {
        reg.is_stack_pointer()
            || matches!(
                reg,
                Mreg::A64(crate::aarch64::mach::A64Mreg::X29)
                    | Mreg::A32(crate::arm32::mach::A32Mreg::R7)
                    | Mreg::A32(crate::arm32::mach::A32Mreg::R11)
                    | Mreg::A32(crate::arm32::mach::A32Mreg::PC)
            )
    }

    fn memory_operand(
        &self,
        at: u32,
    ) -> Option<(&'static str, &'static str, &'static str, i64, i64)> {
        let ids = self.operands.get(&self.insns[at as usize].address)?;
        ids.iter().find_map(|id| self.op_indirect.get(id).copied())
    }

    fn load_address_is_stable(
        &mut self,
        at: u32,
        visiting: &mut HashSet<(StablePointerMode, u32, Mreg)>,
    ) -> bool {
        let Some((_segment, base, index, _scale, _disp)) = self.memory_operand(at) else {
            return false;
        };
        // An indexed function-pointer load is the canonical table dispatch.
        // A compiler may precompute that index into the base; the recursive
        // base check below rejects its multi-register arithmetic too.
        if index != "NONE" && !index.is_empty() {
            return false;
        }
        if matches!(base, "NONE" | "" | "PC" | "R15") {
            return true;
        }
        let base_reg = self.mreg(base);
        if base_reg.is_unknown() {
            return false;
        }
        if self.is_intrinsic_address_base(base_reg) {
            return true;
        }
        self.value_is_stable(StablePointerMode::AddressBase, at, base_reg, visiting)
    }

    fn definition_is_stable(
        &mut self,
        mode: StablePointerMode,
        def: u32,
        visiting: &mut HashSet<(StablePointerMode, u32, Mreg)>,
    ) -> bool {
        let stem = self.stem(self.insns[def as usize].mnemonic);
        let uses = self.meaningful_uses(def);

        let is_copy = match self.arch {
            Arch::Aarch64 => matches!(stem, "MOV" | "ORR"),
            Arch::Arm32 => matches!(stem, "MOV" | "MOVS"),
            _ => false,
        };
        if is_copy {
            return uses.len() == 1 && self.value_is_stable(mode, def, uses[0], visiting);
        }

        let is_load = stem.starts_with("LDR") || matches!(stem, "LDP" | "LDNP");
        if is_load {
            return self.load_address_is_stable(def, visiting);
        }

        // ADR/ADRP materialize a fixed code/data address. ADD/SUB preserve a
        // stable address only in their one-register-plus-immediate form; two
        // register inputs are precisely how a table index/offset is folded in.
        if stem == "ADR" {
            return true;
        }
        if stem == "ADRP" {
            // ADRP alone names only a page, not a callable entry. It is valid
            // address-base evidence for the following LDR/ADD, but never a
            // complete tail target by itself.
            return mode == StablePointerMode::AddressBase;
        }
        if matches!(stem, "ADD" | "SUB") {
            return uses.len() == 1
                && self.value_is_stable(StablePointerMode::AddressBase, def, uses[0], visiting);
        }

        false
    }

    fn value_is_stable(
        &mut self,
        mode: StablePointerMode,
        at: u32,
        reg: Mreg,
        visiting: &mut HashSet<(StablePointerMode, u32, Mreg)>,
    ) -> bool {
        if mode == StablePointerMode::AddressBase && self.is_intrinsic_address_base(reg) {
            return true;
        }
        let key = (mode, at, reg);
        if !visiting.insert(key) {
            return false;
        }
        let defs = self.dataflow.reaching_defs(at, reg);
        let stable = if defs.is_empty() {
            // With no in-function definition, only an ABI argument has a
            // positive pointer-value origin. Arbitrary live-in registers are
            // not guessed to be callees.
            self.abi_args.contains(&reg)
        } else {
            defs.into_iter()
                .all(|def| self.definition_is_stable(mode, def, visiting))
        };
        visiting.remove(&key);
        stable
    }
}

/// Classify register-computed terminal transfers conservatively before the
/// architecture frontends turn them into Mach tail calls. AArch64 BR and ARM
/// BX/BXJ also spell switch dispatch, so a mnemonic alone is insufficient:
/// the target's reaching definitions must prove a stable function-pointer
/// family, while indexed loads and index arithmetic are rejected.
pub fn classify_indirect_tailcalls(db: &mut DecompileDB, insns: &[DecodedInsn]) {
    let arch = db.abi().arch;
    if !matches!(arch, Arch::Aarch64 | Arch::Arm32) {
        return;
    }

    let mut flow_unrefined: HashMap<Address, (usize, &str, &str, &str)> = HashMap::new();
    let mut operands: HashMap<Address, [Symbol; 4]> = HashMap::new();
    for (addr, size, _prefix, mnemonic, op1, op2, op3, op4, _, _) in db.rel_iter::<(
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
    )>("unrefinedinstruction")
    {
        flow_unrefined.insert(*addr, (*size, *mnemonic, *op1, *op2));
        operands.insert(*addr, [*op1, *op2, *op3, *op4]);
    }
    let op_imm = super::build_op_imm_map(db);
    let op_register: HashMap<Symbol, &'static str> = db
        .rel_iter::<(Symbol, &'static str)>("op_register")
        .map(|(id, name)| (*id, *name))
        .collect();
    let op_indirect: HashMap<Symbol, (&'static str, &'static str, &'static str, i64, i64)> = db
        .rel_iter::<(
            Symbol,
            &'static str,
            &'static str,
            &'static str,
            i64,
            i64,
            usize,
        )>("op_indirect")
        .map(|(id, segment, base, index, scale, disp, _)| {
            (*id, (*segment, *base, *index, *scale, *disp))
        })
        .collect();
    let mut owned: HashSet<Address> = db
        .rel_iter::<(Address, Address)>("instr_in_function")
        .map(|(addr, _)| *addr)
        .collect();
    // Architecture frontends publish instr_in_function only after this
    // disassembly-stage classifier runs.  Function inference has already
    // established block ownership, however, and code_in_block is the exact
    // instruction-to-block map consumed by those frontends.  Join the two
    // here so real binaries receive the same ownership evidence as callers
    // that happen to pre-populate instr_in_function.
    let owned_blocks: HashSet<Address> = db
        .rel_iter::<(Node, Address)>("block_in_function")
        .map(|(block, _)| *block)
        .collect();
    owned.extend(
        db.rel_iter::<(Address, Address)>("code_in_block")
            .filter_map(|(addr, block)| owned_blocks.contains(block).then_some(*addr)),
    );
    let table_dispatches: HashSet<Node> = db
        .rel_iter::<(Node, usize, Node)>("jump_table_target")
        .map(|(node, _, _)| *node)
        .collect();

    let dataflow = InsnDataflow::build(arch, insns, db, &flow_unrefined, &op_imm);
    let mut classifier = IndirectTailClassifier {
        arch,
        insns,
        operands: &operands,
        op_indirect: &op_indirect,
        abi_args: db.abi().int_arg_regs.iter().copied().collect(),
        dataflow,
    };
    let mut classified: Vec<(Address, Mreg)> = Vec::new();
    for (idx, insn) in insns.iter().enumerate() {
        if !owned.contains(&insn.address) || table_dispatches.contains(&insn.address) {
            continue;
        }
        let stem = classifier.stem(insn.mnemonic);
        let eligible = match arch {
            Arch::Aarch64 => stem == "BR",
            Arch::Arm32 => {
                matches!(stem, "BX" | "BXJ") && insn.pc_source == branch::PcSource::Computed
            }
            _ => false,
        };
        if !eligible {
            continue;
        }
        let Some(ids) = operands.get(&insn.address) else {
            continue;
        };
        let Some(target) = ids
            .iter()
            .find_map(|id| op_register.get(id).map(|name| classifier.mreg(name)))
            .filter(|reg| !reg.is_unknown())
        else {
            continue;
        };
        if classifier.value_is_stable(
            StablePointerMode::TailTarget,
            idx as u32,
            target,
            &mut HashSet::new(),
        ) {
            classified.push((insn.address, target));
        }
    }
    classified.sort();
    classified.dedup();
    db.rel_set(
        "indirect_tailcall_target",
        classified.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
}

// Every entry accepted by function inference, plus PLT stubs.  Raw FDE starts
// and PE RUNTIME_FUNCTION fragments are only block/range evidence: cold and
// chained fragments are not independent function entries.  Cutting incoming
// edges at those raw boundaries can erase real reaching definitions and make
// an arbitrary ABI argument look like a stable computed target.
fn function_entry_addrs(db: &DecompileDB) -> HashSet<u64> {
    let mut entries: HashSet<u64> = db
        .rel_iter::<(Symbol, Address)>("func_entry")
        .map(|(_, addr)| *addr)
        .collect();
    for (addr, _name) in db.rel_iter::<(Address, Symbol)>("plt_block") {
        entries.insert(*addr);
    }
    entries
}

// For each instruction, the index of its uniquely inferred function entry.
// Function inference already assigned exact blocks by CFG reachability.  Use
// that ownership rather than replaying coarse/nested unwind ranges here; a
// shared block with multiple owners is ambiguous and receives no dominance
// root instead of an arbitrary one.
fn entry_of_each(db: &DecompileDB, insns: &[DecodedInsn]) -> Vec<Option<u32>> {
    let index_of: HashMap<u64, u32> = insns
        .iter()
        .enumerate()
        .map(|(i, d)| (d.address, i as u32))
        .collect();
    let mut block_owners = HashMap::<Address, HashSet<Address>>::new();
    for (block, owner) in db.rel_iter::<(Address, Address)>("block_in_function") {
        block_owners.entry(*block).or_default().insert(*owner);
    }
    let mut instruction_blocks = HashMap::<Address, HashSet<Address>>::new();
    for (addr, block) in db.rel_iter::<(Address, Address)>("code_in_block") {
        instruction_blocks.entry(*addr).or_default().insert(*block);
    }

    insns
        .iter()
        .map(|insn| {
            let blocks = instruction_blocks.get(&insn.address)?;
            let owners: HashSet<Address> = blocks
                .iter()
                .filter_map(|block| block_owners.get(block))
                .flat_map(|owners| owners.iter().copied())
                .collect();
            (owners.len() == 1)
                .then(|| index_of.get(owners.iter().next().unwrap()).copied())
                .flatten()
        })
        .collect()
}

// Entry addresses of callees that never return, so a call to one can be seen
// not to resume. The names come from abi's single always-noreturn list; a
// stripped binary still names its PLT stubs through the dynamic relocations.
fn noreturn_callee_addrs(db: &DecompileDB) -> HashSet<u64> {
    let mut out: HashSet<u64> = HashSet::new();
    for (addr, name) in db.rel_iter::<(Address, Symbol)>("plt_block") {
        if crate::abi::is_always_noreturn(name) {
            out.insert(*addr);
        }
    }
    for (addr, name, _kind) in db.rel_iter::<(Address, Symbol, Symbol)>("symbols") {
        if crate::abi::is_always_noreturn(name) {
            out.insert(*addr);
        }
    }
    out
}

// The PC-relative target a direct branch encodes, or None when it is computed.
fn direct_branch_target(
    arch: Arch,
    insn: &DecodedInsn,
    unrefined_by_addr: &HashMap<u64, (usize, &str, &str, &str)>,
    op_imm_map: &HashMap<&str, i64>,
) -> Option<u64> {
    branch::direct_target_op(arch, insn.mnemonic)?;
    let (_, _, op1, op2) = unrefined_by_addr.get(&insn.address)?;
    op_imm_map
        .get(op1)
        .or_else(|| op_imm_map.get(op2))
        .map(|&v| v as u64)
}

// A table base one instruction materializes: a rip-relative LEA computes it
// into a register, an absolute scaled-index memory operand names it outright
// in its displacement.
struct BaseCandidate {
    base: u64,
    insn: u32,
    index_reg: Option<String>,
}

// Table bases named by one instruction. The absolute form is read off the
// addressing mode rather than off a mnemonic, since the same mode carries a
// table whatever instruction reads it.
fn collect_base_candidates(
    idx: u32,
    depth: u32,
    insns: &[DecodedInsn],
    unrefined_by_addr: &HashMap<u64, (usize, &str, &str, &str)>,
    rip_indirect_map: &HashMap<&str, i64>,
    op_indirect_map: &HashMap<&str, (&str, &str, &str, i64, i64)>,
    out: &mut Vec<(u32, BaseCandidate)>,
) {
    let insn = &insns[idx as usize];
    let (size, mnem, op1, op2) = match unrefined_by_addr.get(&insn.address) {
        Some(info) => *info,
        None => return,
    };
    if mnem == "LEA" {
        if let Some(&disp) = rip_indirect_map.get(op1) {
            out.push((
                depth,
                BaseCandidate {
                    base: (insn.address as i64 + size as i64 + disp) as u64,
                    insn: idx,
                    index_reg: None,
                },
            ));
        }
    }
    for op in [op1, op2] {
        if let Some(&(_seg, base, index, scale, disp)) = op_indirect_map.get(op) {
            if base == "NONE" && index != "NONE" && (scale == 4 || scale == 8) && disp > 0 {
                out.push((
                    depth,
                    BaseCandidate {
                        base: disp as u64,
                        insn: idx,
                        index_reg: Some(index.to_string()),
                    },
                ));
                break;
            }
        }
    }
}

// Read the table at `base`: 4-byte self-relative offsets first, then 8-byte
// absolute addresses. Membership in the decoded instruction set ends the table
// and is the only thing that validates it, which is what makes the entry
// ceiling a safety bound rather than a correctness decision.
fn read_table_targets(
    base: u64,
    max_entries: usize,
    addr_set: &HashSet<u64>,
    section_data: &[(u64, u64, Vec<u8>)],
) -> Option<Vec<u64>> {
    let mut relative: Vec<u64> = Vec::new();
    for i in 0..max_entries {
        let offset = match read_i32_at(section_data, base + i as u64 * 4) {
            Some(v) => v,
            None => break,
        };
        let target = (base as i64 + offset as i64) as u64;
        if !addr_set.contains(&target) {
            break;
        }
        relative.push(target);
    }
    if relative.len() >= 2 {
        return Some(relative);
    }

    let mut absolute: Vec<u64> = Vec::new();
    for i in 0..max_entries {
        let target = match read_u64_at(section_data, base + i as u64 * 8) {
            Some(v) => v,
            None => break,
        };
        if !addr_set.contains(&target) {
            break;
        }
        absolute.push(target);
    }
    if absolute.len() >= 2 {
        return Some(absolute);
    }
    None
}

// Resolve one indirect JMP: the table base by reaching definitions over the
// CFG, the bounds guard on the straight-line path into the dispatch, and the
// targets by reading the table.
fn find_jump_table_info(
    jmp_addr: u64,
    insns: &[DecodedInsn],
    df: &mut InsnDataflow,
    unrefined_by_addr: &HashMap<u64, (usize, &str, &str, &str)>,
    op_imm_map: &HashMap<&str, i64>,
    op_reg_map: &HashMap<&str, &str>,
    rip_indirect_map: &HashMap<&str, i64>,
    op_indirect_map: &HashMap<&str, (&str, &str, &str, i64, i64)>,
    addr_set: &HashSet<u64>,
    section_data: &[(u64, u64, Vec<u8>)],
    ambiguous: &mut Vec<AmbiguousJump>,
) -> Option<JumpTableInfo> {
    let jmp_idx = match df.index_of.get(&jmp_addr) {
        Some(&idx) => idx,
        None => return None,
    };

    // Bases that structurally reach this jump. Start from the registers the
    // jump reads, take their reaching definitions, and expand each definition
    // into the registers it reads in turn. Depth counts definitions crossed,
    // so the base a dispatch actually uses -- one or two assignments from the
    // jump -- ranks ahead of anything further upstream.
    let mut candidates: Vec<(u32, BaseCandidate)> = Vec::new();
    let mut queue: std::collections::VecDeque<(u32, u32)> = std::collections::VecDeque::new();
    let mut chain: HashSet<u32> = HashSet::new();
    chain.insert(jmp_idx);
    for reg in df.uses[jmp_idx as usize].clone() {
        for d in df.reaching_defs(jmp_idx, reg) {
            queue.push_back((d, 1));
        }
    }
    // Breadth first, so every instruction is labelled with its shortest chain
    // distance and the labelling does not depend on visit order.
    while let Some((i, depth)) = queue.pop_front() {
        if !chain.insert(i) {
            continue;
        }
        collect_base_candidates(
            i,
            depth,
            insns,
            unrefined_by_addr,
            rip_indirect_map,
            op_indirect_map,
            &mut candidates,
        );
        for reg in df.uses[i as usize].clone() {
            for d in df.reaching_defs(i, reg) {
                if !chain.contains(&d) {
                    queue.push_back((d, depth + 1));
                }
            }
        }
    }

    // The jump's own operand can name the table outright (`jmp *tbl(,%idx,8)`).
    // It ranks last: a base the dataflow reaches is better evidence than one
    // that merely appears in the addressing mode.
    let mut own: Vec<(u32, BaseCandidate)> = Vec::new();
    collect_base_candidates(
        jmp_idx,
        u32::MAX,
        insns,
        unrefined_by_addr,
        rip_indirect_map,
        op_indirect_map,
        &mut own,
    );
    let jmp_operand_index_reg: Option<String> = own.iter().find_map(|(_, c)| c.index_reg.clone());
    candidates.extend(own);

    if candidates.is_empty() {
        return None;
    }

    // The bounds guard and the region the dispatch occupies both lie on the
    // straight-line path into the jump. Walking unique fallthrough
    // predecessors ends that path where control flow joins, so a guard the
    // scheduler pushed away from the jump is still found while one on a
    // disjoint path still is not. An unconditional jump or a return cannot
    // appear on it at all: neither contributes a fallthrough edge.
    let mut table_bound: Option<usize> = None;
    let mut cmp_addr: Option<u64> = None;
    let mut bounds_index_reg: Option<String> = None;
    let mut bounds_check_fallthrough_idx: Option<u32> = None;
    let mut straight_line: HashSet<u32> = HashSet::new();
    let mut cur = jmp_idx;
    while let Some(prev) = df.linear_pred[cur as usize] {
        cur = prev;
        straight_line.insert(prev);
        let prev_insn = &insns[prev as usize];
        let (_, mnem, op1, op2) = match unrefined_by_addr.get(&prev_insn.address) {
            Some(info) => *info,
            None => continue,
        };

        // A compare or subtract against a small immediate is the switch bound;
        // SUB+JA constrains the index exactly as CMP+JA does, since both set
        // CF and ZF the same way for an unsigned compare. AND with a 2^n-1
        // mask is clang's equivalent, constraining the index to 0..mask.
        let masked = mnem == "AND";
        if matches!(mnem, "CMP" | "SUB" | "AND") && table_bound.is_none() {
            let (imm, reg_op) = if let Some(&imm) = op_imm_map.get(op1) {
                (imm, op2)
            } else if let Some(&imm) = op_imm_map.get(op2) {
                (imm, op1)
            } else {
                continue;
            };
            if imm > 0
                && imm < CONFIG.jump_table.max_bounds_immediate
                && (!masked || (imm & (imm + 1)) == 0)
            {
                table_bound = Some((imm + 1) as usize);
                cmp_addr = Some(prev_insn.address);
                if let Some(&reg_name) = op_reg_map.get(reg_op) {
                    bounds_index_reg = Some(reg_name.to_string());
                }
            }
            continue;
        }

        if matches!(mnem, "JA" | "JAE" | "JB" | "JBE" | "JG" | "JGE")
            && bounds_check_fallthrough_idx.is_none()
            && op_imm_map.contains_key(op1)
        {
            bounds_check_fallthrough_idx = Some(prev + 1);
        }
    }

    let table_bound = table_bound.unwrap_or(CONFIG.jump_table.default_entry_count);
    let max_entries = table_bound.min(CONFIG.jump_table.max_entry_count);

    // Try candidates in chain order, deepest last. The tie-break within one
    // depth only fixes an order for reproducibility; it never decides that
    // anything reaches anything.
    candidates.sort_by_key(|(depth, c)| (*depth, std::cmp::Reverse(c.insn), c.base));

    let mut group_start = 0usize;
    while group_start < candidates.len() {
        let depth = candidates[group_start].0;
        let mut group_end = group_start;
        while group_end < candidates.len() && candidates[group_end].0 == depth {
            group_end += 1;
        }

        // Every distinct base this group offers, with each definition that
        // offers it. Sorted by base, so what follows never depends on the order
        // candidates were collected in.
        let mut resolved: std::collections::BTreeMap<u64, (Vec<u64>, Vec<&BaseCandidate>)> =
            std::collections::BTreeMap::new();
        let mut tried: HashSet<u64> = HashSet::new();
        for (_, cand) in &candidates[group_start..group_end] {
            if let Some(entry) = resolved.get_mut(&cand.base) {
                entry.1.push(cand);
                continue;
            }
            if !tried.insert(cand.base) {
                continue;
            }
            if let Some(targets) =
                read_table_targets(cand.base, max_entries, addr_set, section_data)
            {
                resolved.insert(cand.base, (targets, vec![cand]));
            }
        }

        if resolved.len() > 1 {
            // Two different bases reach this jump equally directly. They are
            // not equally the dispatch's base: one of them is defined on every
            // path into the jump, and the others arrive only on some path --
            // around a loop that has already run through the jump, or past a
            // call that never returns and so joins two pieces of code that
            // never join. Keep a base whose definition dominates the jump; that
            // is a fact about the CFG, not about how near the definition sits.
            let dominating: Vec<u64> = resolved
                .iter()
                .filter(|(_, (_, defs))| defs.iter().any(|c| df.dominates(c.insn, jmp_idx)))
                .map(|(base, _)| *base)
                .collect();
            if dominating.len() != 1 {
                // No definition is on every path, or more than one is: which
                // table the dispatch reads is genuinely unresolved, and a wrong
                // target set corrupts every later stage's CFG. Decline.
                ambiguous.push(AmbiguousJump {
                    jmp: jmp_addr,
                    depth,
                    bases: resolved
                        .iter()
                        .map(|(base, (_, defs))| (*base, insns[defs[0].insn as usize].address))
                        .collect(),
                });
                return None;
            }
            resolved.retain(|base, _| *base == dominating[0]);
        }

        if let Some((_, (ordered_targets, cands))) = resolved.into_iter().next() {
            let cand = cands[0];
            // The dispatch region runs from the bounds branch's fallthrough, or
            // else from the instruction that materializes the base, down to the
            // jump: that run is the lookup, and collapsing it into a switch
            // deletes it. Anything else the chain reached only feeds the index
            // from further upstream -- a load off the frame drags the whole
            // prologue in through RSP -- and is ordinary code that has to
            // survive. It is clamped to the straight-line path so the region
            // never reaches back past a join into code that only sometimes
            // precedes the dispatch.
            let impl_start = bounds_check_fallthrough_idx
                .or_else(|| Some(cand.insn).filter(|i| straight_line.contains(i)))
                .unwrap_or(jmp_idx);
            let impl_addrs = collect_impl_addrs(insns, Some(impl_start as usize), jmp_idx as usize);
            let index_reg = bounds_index_reg
                .clone()
                .or_else(|| cand.index_reg.clone())
                .or_else(|| jmp_operand_index_reg.clone());
            return Some(JumpTableInfo {
                ordered_targets,
                impl_addrs,
                cmp_addr,
                index_reg,
            });
        }

        group_start = group_end;
    }

    None
}

// Addresses of the instructions that implement the lookup, from the start of
// the dispatch region through the JMP. The region is contiguous because it is
// a run of fallthrough edges.
fn collect_impl_addrs(
    insns: &[DecodedInsn],
    first_lea_idx: Option<usize>,
    jmp_idx: usize,
) -> Vec<u64> {
    let start = first_lea_idx.unwrap_or(jmp_idx);
    (start..=jmp_idx).map(|i| insns[i].address).collect()
}

// Next defined data-symbol address after table_base within the same rodata range, used to clamp an unbounded table so it stops at the adjacent object.
fn next_data_symbol_boundary(
    obj: &object::File,
    table_base: u64,
    rodata_ranges: &[(u64, u64, Vec<u8>)],
) -> Option<u64> {
    use object::ObjectSymbol;

    // The rodata range that contains the table base bounds the search.
    let (_, range_end, _) = rodata_ranges
        .iter()
        .find(|(start, end, _)| table_base >= *start && table_base < *end)?;

    let mut boundary: Option<u64> = None;
    for sym in obj.symbols().chain(obj.dynamic_symbols()) {
        // Only defined symbols (those bound to a real section) mark a real boundary.
        if !matches!(sym.section(), object::SymbolSection::Section(_)) {
            continue;
        }
        let addr = sym.address();
        // Must be after the table base and within the same rodata range.
        if addr <= table_base || addr >= *range_end {
            continue;
        }
        boundary = Some(boundary.map_or(addr, |b| b.min(addr)));
    }

    boundary
}

// Detect clang data lookup tables: `mov disp(,%reg,4), %dst` where disp is in rodata.
pub fn analyze_data_lookup_tables(
    db: &DecompileDB,
    insns: &[DecodedInsn],
    obj: &object::File,
) -> Vec<DataLookupTableInfo> {
    let mut results: Vec<DataLookupTableInfo> = Vec::new();

    // Collect rodata section ranges
    let rodata_ranges: Vec<(u64, u64, Vec<u8>)> = obj
        .sections()
        .filter_map(|s| {
            let name = s.name().unwrap_or("");
            if !name.contains("rodata") && !name.contains(".rdata") {
                return None;
            }
            let data = s.data().ok()?;
            if data.is_empty() {
                return None;
            }
            Some((s.address(), s.address() + data.len() as u64, data.to_vec()))
        })
        .collect();

    if rodata_ranges.is_empty() {
        return results;
    }

    let section_data: Vec<(u64, u64, Vec<u8>)> = obj
        .sections()
        .filter_map(|s| {
            let data = s.data().ok()?;
            if data.is_empty() {
                return None;
            }
            Some((s.address(), s.address() + data.len() as u64, data.to_vec()))
        })
        .collect();

    let op_imm_map = super::build_op_imm_map(db);
    let mut op_reg_map: HashMap<&str, &str> = HashMap::new();
    for (id, reg) in db.rel_iter::<(Symbol, &'static str)>("op_register") {
        op_reg_map.insert(id, reg);
    }

    let mut op_indirect_map: HashMap<&str, (&str, &str, &str, i64, i64)> = HashMap::new();
    for (id, _seg, base, index, scale, disp, _) in db.rel_iter::<(
        Symbol,
        &'static str,
        &'static str,
        &'static str,
        i64,
        i64,
        usize,
    )>("op_indirect")
    {
        op_indirect_map.insert(*id, (*_seg, *base, *index, *scale, *disp));
    }

    let mut unrefined_by_addr: HashMap<u64, (usize, &str, &str, &str)> = HashMap::new();
    for (addr, size, _pfx, mnem, op1, op2, _op3, _op4, _, _) in db.rel_iter::<(
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
    )>("unrefinedinstruction")
    {
        unrefined_by_addr.insert(*addr, (*size, *mnem, *op1, *op2));
    }

    let dataflow = InsnDataflow::build(db.abi().arch, insns, db, &unrefined_by_addr, &op_imm_map);

    // Scan for MOV instructions with scaled-index addressing and no base register
    for (i, insn) in insns.iter().enumerate() {
        let (_, mnem, op1, op2) = match unrefined_by_addr.get(&insn.address) {
            Some(info) => *info,
            None => continue,
        };

        if mnem != "MOV" {
            continue;
        }

        // The operand swap in instruction.rs puts the source in op1 and destination in op2 (AT&T-style ordering). Check both op1 and op2 to find the indirect-source operand. Pattern: disp(,%reg,scale) where disp points into rodata.
        let find_table_op = |op: &str| -> Option<(u64, i64, &'static str)> {
            let &(_seg, base, index, sc, disp) = op_indirect_map.get(op)?;
            if base != "NONE" || index == "NONE" || (sc != 4 && sc != 8) || disp <= 0 {
                return None;
            }
            let disp_u64 = disp as u64;
            let in_rodata = rodata_ranges
                .iter()
                .any(|(start, end, _)| disp_u64 >= *start && disp_u64 < *end);
            if !in_rodata {
                return None;
            }
            Some((disp_u64, sc, index))
        };

        let (table_base, scale, _index_str) =
            match find_table_op(op1).or_else(|| find_table_op(op2)) {
                Some(t) => t,
                None => continue,
            };

        // Walk the unique CFG predecessor chain for a bounds check (CMP+JA or
        // AND). Distance and address order are not evidence that a check
        // reaches this load, so there is intentionally no instruction cap.
        let mut bounds_count: Option<usize> = None;
        let mut bounds_addr: Option<u64> = None;
        let mut index_reg: Option<String> = None;

        for idx in linear_predecessors(&dataflow, i as u32).map(|idx| idx as usize) {
            let prev = &insns[idx];
            let (_, prev_mnem, prev_op1, prev_op2) = match unrefined_by_addr.get(&prev.address) {
                Some(info) => *info,
                None => continue,
            };

            match prev_mnem {
                "CMP" => {
                    let imm = op_imm_map
                        .get(prev_op1)
                        .or_else(|| op_imm_map.get(prev_op2));
                    if let Some(&val) = imm {
                        if val > 0 && val < CONFIG.jump_table.max_bounds_immediate {
                            bounds_count = Some((val + 1) as usize);
                            bounds_addr = Some(prev.address);
                            let reg_op = if op_imm_map.contains_key(prev_op1) {
                                prev_op2
                            } else {
                                prev_op1
                            };
                            if let Some(&reg_name) = op_reg_map.get(reg_op) {
                                index_reg = Some(reg_name.to_string());
                            }
                        }
                    }
                    break;
                }
                "AND" => {
                    let imm = op_imm_map
                        .get(prev_op1)
                        .or_else(|| op_imm_map.get(prev_op2));
                    if let Some(&val) = imm {
                        if val > 0
                            && val < CONFIG.jump_table.max_bounds_immediate
                            && (val & (val + 1)) == 0
                        {
                            bounds_count = Some((val + 1) as usize);
                            bounds_addr = Some(prev.address);
                            let reg_op = if op_imm_map.contains_key(prev_op1) {
                                prev_op2
                            } else {
                                prev_op1
                            };
                            if let Some(&reg_name) = op_reg_map.get(reg_op) {
                                index_reg = Some(reg_name.to_string());
                            }
                        }
                    }
                    break;
                }
                // Calls preserve control flow but clobber flags and all
                // caller-saved values, so a check before one cannot justify a
                // table access after it. JMP/RET normally cannot occur on this
                // chain, but remain explicit semantic barriers.
                "JMP" | "CALL" | "RET" => break,
                _ => {}
            }
        }

        // Entry count: trust a recovered static bound (capped), else clamp to the next data-symbol boundary; the read loop also stops at the section end or first unreadable slot.
        let entry_count = match bounds_count {
            Some(n) => n.min(CONFIG.jump_table.max_entry_count),
            None => {
                let symbol_extent = next_data_symbol_boundary(obj, table_base, &rodata_ranges)
                    .map(|boundary| ((boundary - table_base) / scale as u64) as usize)
                    .filter(|&n| n > 0);
                symbol_extent
                    .unwrap_or(CONFIG.jump_table.default_entry_count)
                    .min(CONFIG.jump_table.max_entry_count)
            }
        };

        // Read the table values
        let mut values: Vec<i64> = Vec::new();
        for k in 0..entry_count {
            let entry_addr = table_base + (k as u64 * scale as u64);
            if scale == 4 {
                if let Some(val) = read_i32_at(&section_data, entry_addr) {
                    values.push(val as i64);
                } else {
                    break;
                }
            } else {
                // scale == 8
                if let Some(val) = read_u64_at(&section_data, entry_addr) {
                    values.push(val as i64);
                } else {
                    break;
                }
            }
        }

        if values.len() >= 2 {
            log::debug!(
                "Data lookup table at 0x{:x}: {} entries of {}B at table base 0x{:x}",
                insn.address,
                values.len(),
                scale,
                table_base
            );
            results.push(DataLookupTableInfo {
                table_base,
                entry_count: values.len(),
                entry_scale: scale,
                values,
                mov_addr: insn.address,
                bounds_check_addr: bounds_addr,
                index_reg,
            });
        }
    }

    results
}

// Map GOT slot addresses to PLT stub addresses via dynamic relocations.
fn build_got_to_plt_map(db: &DecompileDB, obj: &object::File) -> HashMap<u64, u64> {
    use object::{ObjectSymbol, ObjectSymbolTable};

    let mut got_to_plt: HashMap<u64, u64> = HashMap::new();

    let mut name_to_plt: HashMap<&'static str, u64> = HashMap::new();
    for (plt_addr, name) in db.rel_iter::<(Address, Symbol)>("plt_block") {
        name_to_plt.insert(*name, *plt_addr);
    }
    if name_to_plt.is_empty() {
        return got_to_plt;
    }

    if let Some(dyn_symtab) = obj.dynamic_symbol_table() {
        if let Some(dyn_relocs) = obj.dynamic_relocations() {
            for (offset, reloc) in dyn_relocs {
                if let object::RelocationTarget::Symbol(sym_idx) = reloc.target() {
                    if let Ok(sym) = dyn_symtab.symbol_by_index(sym_idx) {
                        let sym_name = sym.name().unwrap_or("");
                        if let Some(&plt_addr) = name_to_plt.get(sym_name) {
                            got_to_plt.insert(offset, plt_addr);
                        }
                    }
                }
            }
        }
    }

    got_to_plt
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn x86_logical_results_are_modeled_flags_origins() {
        for mnemonic in ["OR", "XOR"] {
            assert!(is_modeled_flags_origin(Arch::X86_64, mnemonic));
            assert!(!clobbers_flags(Arch::X86_64, mnemonic));
        }
        // NOT is flag-transparent and must not sever an earlier origin.
        assert!(!is_modeled_flags_origin(Arch::X86_64, "NOT"));
        assert!(!clobbers_flags(Arch::X86_64, "NOT"));
    }

    // A dataflow over a hand-built CFG. Only the fields the reaching-definition
    // walk reads are populated, since that walk is what indirect-jump recovery
    // now rests on.
    fn dataflow(preds: Vec<Vec<u32>>, defs: Vec<Vec<Mreg>>) -> InsnDataflow {
        let n = preds.len();
        // Instruction 0 stands for the function entry, which is what the
        // dominance queries here are asked against.
        InsnDataflow {
            index_of: HashMap::new(),
            linear_pred: vec![None; n],
            entry_of: vec![Some(0); n],
            uses: vec![Vec::new(); n],
            stamp: vec![0; n],
            epoch: 0,
            memo: HashMap::new(),
            preds,
            defs,
        }
    }

    // A straight run of `n` instructions, each falling through to the next.
    fn straight_line(n: usize) -> Vec<Vec<u32>> {
        (0..n)
            .map(|i| {
                if i == 0 {
                    Vec::new()
                } else {
                    vec![i as u32 - 1]
                }
            })
            .collect()
    }

    // The property the whole change rests on: how far back a definition sits is
    // not a fact about whether it reaches. cp's option dispatch sets its table
    // base 54 instructions before the jump; the window this replaced was 50.
    #[test]
    fn a_definition_reaches_however_far_back_it_sits() {
        let n = 400;
        let mut defs = vec![Vec::new(); n];
        defs[0] = vec![Mreg::AX];
        let mut df = dataflow(straight_line(n), defs);
        assert_eq!(df.reaching_defs(n as u32 - 1, Mreg::AX), vec![0]);
    }

    #[test]
    fn a_redefinition_kills_the_earlier_one() {
        let n = 400;
        let mut defs = vec![Vec::new(); n];
        defs[0] = vec![Mreg::AX];
        defs[100] = vec![Mreg::AX];
        let mut df = dataflow(straight_line(n), defs);
        assert_eq!(df.reaching_defs(n as u32 - 1, Mreg::AX), vec![100]);
    }

    // A definition on a branch the query point is not reached from must not
    // count, however close it sits in address order.
    #[test]
    fn a_definition_on_a_disjoint_branch_does_not_reach() {
        // 0 forks to 1 and 2; only 1 leads to 3. 4 is reached from 2 alone.
        let preds = vec![vec![], vec![0], vec![0], vec![1], vec![2]];
        let mut defs = vec![Vec::new(); 5];
        defs[0] = vec![Mreg::AX];
        defs[2] = vec![Mreg::AX];
        defs[4] = vec![Mreg::AX];
        let mut df = dataflow(preds, defs);
        assert_eq!(df.reaching_defs(3, Mreg::AX), vec![0]);
    }

    // Both arms of a join contribute, which is what makes an ambiguous base
    // detectable rather than silently resolved to one arm.
    #[test]
    fn every_arm_of_a_join_contributes_its_definition() {
        let preds = vec![vec![], vec![0], vec![0], vec![1, 2]];
        let mut defs = vec![Vec::new(); 4];
        defs[1] = vec![Mreg::AX];
        defs[2] = vec![Mreg::AX];
        let mut df = dataflow(preds, defs);
        assert_eq!(df.reaching_defs(3, Mreg::AX), vec![1, 2]);
    }

    // A dispatch inside a loop is the shape that motivated this; the back edge
    // must not make the walk diverge.
    #[test]
    fn a_back_edge_terminates_the_walk() {
        // 0 enters the loop 1 -> 2 -> 1.
        let preds = vec![vec![], vec![0, 2], vec![1]];
        let mut defs = vec![Vec::new(); 3];
        defs[0] = vec![Mreg::AX];
        let mut df = dataflow(preds, defs);
        assert_eq!(df.reaching_defs(2, Mreg::AX), vec![0]);
    }

    #[test]
    fn an_undefined_register_reaches_nothing() {
        let mut df = dataflow(straight_line(20), vec![Vec::new(); 20]);
        assert!(df.reaching_defs(19, Mreg::AX).is_empty());
    }

    // The cksum shape, as a graph. The dispatch at 4 sits in a loop (1 is the
    // loop head); the base it always reads is defined at 0, before the loop,
    // and an unrelated definition at 5 sits on a path that has already been
    // through the dispatch once and comes back around. Both reach 4; only the
    // one before the loop is on every path into it.
    fn loop_with_a_late_redefinition() -> InsnDataflow {
        //  0 -> 1 -> 2 -> 3 -> 4(jump) ; 4 -> 5 -> 1 closes the loop.
        let preds = vec![vec![], vec![0, 5], vec![1], vec![2], vec![3], vec![4]];
        let mut defs = vec![Vec::new(); 6];
        defs[0] = vec![Mreg::BX];
        defs[5] = vec![Mreg::BX];
        dataflow(preds, defs)
    }

    #[test]
    fn both_definitions_reach_a_dispatch_inside_a_loop() {
        let mut df = loop_with_a_late_redefinition();
        assert_eq!(df.reaching_defs(4, Mreg::BX), vec![0, 5]);
    }

    // Which of them the dispatch always reads is a dominance question, and the
    // answer must not depend on which definition sits nearer the jump.
    #[test]
    fn only_the_definition_on_every_path_dominates() {
        let mut df = loop_with_a_late_redefinition();
        assert!(df.dominates(0, 4));
        assert!(!df.dominates(5, 4));
    }

    // Two arms of a branch both define the register: neither is on every path,
    // so neither dominates and the caller must decline rather than pick one.
    #[test]
    fn neither_arm_of_a_branch_dominates() {
        let preds = vec![vec![], vec![0], vec![0], vec![1, 2]];
        let mut defs = vec![Vec::new(); 4];
        defs[1] = vec![Mreg::BX];
        defs[2] = vec![Mreg::BX];
        let mut df = dataflow(preds, defs);
        assert_eq!(df.reaching_defs(3, Mreg::BX), vec![1, 2]);
        assert!(!df.dominates(1, 3));
        assert!(!df.dominates(2, 3));
    }

    // A region the entry cannot reach -- a switch arm whose only way in is an
    // indirect jump this stage has not resolved -- has no dominance to report,
    // so nothing there is mistaken for a definition on every path.
    #[test]
    fn a_region_the_entry_cannot_reach_dominates_nothing() {
        // 0 is the entry and reaches nothing; 1 -> 2 stands alone.
        let preds = vec![vec![], vec![], vec![1]];
        let mut defs = vec![Vec::new(); 3];
        defs[1] = vec![Mreg::BX];
        let mut df = dataflow(preds, defs);
        assert!(!df.dominates(1, 2));
    }

    // A decoded instruction with just the fields the CFG construction reads.
    fn insn(address: u64, size: usize, mnemonic: &'static str) -> DecodedInsn {
        DecodedInsn {
            address,
            size,
            mnemonic,
            op_str: "",
            pc_source: branch::PcSource::NotWritten,
        }
    }

    // Two consecutive functions: the first ends in a call that does not return,
    // the second starts right after it. `defs` names the register each
    // instruction defines, `calls` the target of each call.
    struct Layout {
        insns: Vec<DecodedInsn>,
        unrefined: HashMap<u64, (usize, &'static str, &'static str, &'static str)>,
        imm: HashMap<&'static str, i64>,
        db: DecompileDB,
    }

    impl Layout {
        fn new(insns: Vec<DecodedInsn>) -> Layout {
            let mut unrefined = HashMap::new();
            for d in &insns {
                unrefined.insert(d.address, (d.size, d.mnemonic, "0", "0"));
            }
            let mut db = DecompileDB::default();
            db.target_abi = Some(crate::abi::AbiConfig::sysv_x86_64());
            Layout {
                insns,
                unrefined,
                imm: HashMap::new(),
                db,
            }
        }

        // Give one instruction a direct branch/call target, encoded the way the
        // operand relations carry it: an immediate operand holding the address.
        fn target(mut self, at: u64, op_id: &'static str, to: u64) -> Layout {
            let e = self.unrefined.get_mut(&at).expect("no such instruction");
            *e = (e.0, e.1, op_id, "0");
            self.imm.insert(op_id, to as i64);
            self
        }

        fn defines(mut self, at: u64, reg: Mreg) -> Layout {
            self.db.rel_push("reg_def", (at as Address, reg));
            self
        }

        fn function_entry(mut self, start: u64, end: u64) -> Layout {
            self.db
                .rel_push("func_entry", ("fixture", start as Address));
            self.db
                .rel_push("block_in_function", (start as Address, start as Address));
            for insn in self
                .insns
                .iter()
                .filter(|insn| insn.address >= start && insn.address < end)
            {
                self.db
                    .rel_push("code_in_block", (insn.address, start as Address));
            }
            self
        }

        fn plt(mut self, at: u64, name: Symbol) -> Layout {
            self.db.rel_push("plt_block", (at as Address, name));
            self
        }

        fn dataflow(&self) -> InsnDataflow {
            InsnDataflow::build(
                Arch::X86_64,
                &self.insns,
                &self.db,
                &self.unrefined,
                &self.imm,
            )
        }
    }

    // The cksum shape. An abort stub sits just before a function's entry, and
    // a call to abort falls through in the classification, so without a
    // boundary the walk leaves the function through its own first instruction
    // and answers with a register some earlier function set.
    #[test]
    fn a_walk_does_not_leave_a_function_through_its_entry() {
        let l = Layout::new(vec![
            insn(0x10, 3, "MOV"),  // earlier function defines BX
            insn(0x13, 5, "CALL"), // ... and ends by calling abort
            insn(0x18, 8, "NOP"),  // alignment padding, up to the entry
            insn(0x20, 3, "MOV"),  // the next function's entry
            insn(0x23, 2, "JMP"),
        ])
        .defines(0x10, Mreg::BX)
        .function_entry(0x20, 0x25);
        let mut df = l.dataflow();
        let at = df.index_of[&0x23];
        assert!(df.reaching_defs(at, Mreg::BX).is_empty());
    }

    #[test]
    fn raw_unwind_fragment_boundary_does_not_cut_reaching_definitions() {
        let mut l = Layout::new(vec![
            insn(0x10, 4, "MOV"),
            insn(0x14, 4, "MOV"),
            insn(0x18, 4, "JMP"),
        ])
        .defines(0x10, Mreg::BX);
        // Raw unwind brackets are range evidence only.  Without an inferred
        // entry and block owner, 0x14 must not become an artificial cut.
        l.db.rel_push("known_function_range", (0x14_u64, 0x1c_u64));
        let mut df = l.dataflow();
        let at = df.index_of[&0x18];
        assert_eq!(df.reaching_defs(at, Mreg::BX), vec![df.index_of[&0x10]]);
    }

    #[test]
    fn shared_block_has_no_arbitrary_dominance_entry() {
        let insns = vec![insn(0x20, 4, "MOV")];
        let mut db = DecompileDB::default();
        db.rel_push("func_entry", ("left", 0x10_u64));
        db.rel_push("func_entry", ("right", 0x18_u64));
        db.rel_push("block_in_function", (0x20_u64, 0x10_u64));
        db.rel_push("block_in_function", (0x20_u64, 0x18_u64));
        db.rel_push("code_in_block", (0x20_u64, 0x20_u64));
        assert_eq!(entry_of_each(&db, &insns), vec![None]);
    }

    // The same boundary must not swallow flow inside one function.
    #[test]
    fn a_walk_still_crosses_instructions_within_one_function() {
        let l = Layout::new(vec![
            insn(0x20, 3, "MOV"),
            insn(0x23, 5, "CALL"),
            insn(0x28, 2, "JMP"),
        ])
        .defines(0x20, Mreg::BX)
        .function_entry(0x20, 0x2a);
        let mut df = l.dataflow();
        let at = df.index_of[&0x28];
        assert_eq!(df.reaching_defs(at, Mreg::BX), vec![0]);
    }

    // A call that never returns does not resume at the next instruction, so a
    // definition before it does not reach code the linker placed after it.
    // This is the boundary available when a binary carries no frame info.
    #[test]
    fn a_call_that_never_returns_has_no_fallthrough() {
        let l = Layout::new(vec![
            insn(0x10, 3, "MOV"),
            insn(0x13, 5, "CALL"),
            insn(0x18, 3, "MOV"),
            insn(0x1b, 2, "JMP"),
        ])
        .defines(0x10, Mreg::BX)
        .target(0x13, "call_op", 0x900)
        .plt(0x900, "abort");
        let mut df = l.dataflow();
        let at = df.index_of[&0x1b];
        assert!(df.reaching_defs(at, Mreg::BX).is_empty());
    }

    // A call that does return keeps its fallthrough, which is what lets a base
    // held in a callee-saved register across a call still be found.
    #[test]
    fn a_call_that_returns_keeps_its_fallthrough() {
        let l = Layout::new(vec![
            insn(0x10, 3, "MOV"),
            insn(0x13, 5, "CALL"),
            insn(0x18, 3, "MOV"),
            insn(0x1b, 2, "JMP"),
        ])
        .defines(0x10, Mreg::BX)
        .target(0x13, "call_op", 0x900)
        .plt(0x900, "getopt_long");
        let mut df = l.dataflow();
        let at = df.index_of[&0x1b];
        assert_eq!(df.reaching_defs(at, Mreg::BX), vec![0]);
    }

    // The same returning call is a definition of every ABI caller-saved
    // register. A value in AX therefore cannot leak through it into table
    // recovery merely because the control-flow edge returns.
    #[test]
    fn a_returning_call_kills_caller_saved_register_values() {
        let l = Layout::new(vec![
            insn(0x10, 3, "MOV"),
            insn(0x13, 5, "CALL"),
            insn(0x18, 2, "JMP"),
        ])
        .defines(0x10, Mreg::AX)
        .target(0x13, "call_op", 0x900)
        .plt(0x900, "getopt_long");
        let mut df = l.dataflow();
        let call = df.index_of[&0x13];
        let at = df.index_of[&0x18];
        assert_eq!(df.reaching_defs(at, Mreg::AX), vec![call]);
    }

    #[test]
    fn a_linear_predecessor_chain_has_no_distance_limit() {
        let n = 400;
        let mut df = dataflow(straight_line(n), vec![Vec::new(); n]);
        df.linear_pred = (0..n)
            .map(|i| if i == 0 { None } else { Some(i as u32 - 1) })
            .collect();
        assert_eq!(linear_predecessors(&df, n as u32 - 1).last(), Some(0));
        assert_eq!(linear_predecessors(&df, n as u32 - 1).count(), n - 1);
    }

    // A tail jump into another function is a call in disguise: following it
    // backward would read the caller's registers as the callee's.
    #[test]
    fn a_tail_jump_is_not_an_edge_into_the_callee() {
        let l = Layout::new(vec![
            insn(0x10, 3, "MOV"),
            insn(0x13, 5, "JMP"),
            insn(0x20, 3, "MOV"),
            insn(0x23, 2, "JMP"),
        ])
        .defines(0x10, Mreg::BX)
        .target(0x13, "jmp_op", 0x20)
        .function_entry(0x20, 0x25);
        let mut df = l.dataflow();
        let at = df.index_of[&0x23];
        assert!(df.reaching_defs(at, Mreg::BX).is_empty());
    }

    #[test]
    fn a_repeated_query_gives_the_same_answer() {
        let n = 50;
        let mut defs = vec![Vec::new(); n];
        defs[3] = vec![Mreg::AX];
        defs[7] = vec![Mreg::DX];
        let mut df = dataflow(straight_line(n), defs);
        let first = df.reaching_defs(40, Mreg::AX);
        let other = df.reaching_defs(40, Mreg::DX);
        assert_eq!(first, vec![3]);
        assert_eq!(other, vec![7]);
        assert_eq!(df.reaching_defs(40, Mreg::AX), first);
    }

    fn control_insn(
        address: Address,
        mnemonic: &'static str,
        pc_source: branch::PcSource,
    ) -> DecodedInsn {
        DecodedInsn {
            address,
            size: 4,
            mnemonic,
            op_str: "",
            pc_source,
        }
    }

    fn raw(
        db: &mut DecompileDB,
        address: Address,
        mnemonic: &'static str,
        op1: Symbol,
        op2: Symbol,
    ) {
        db.rel_push(
            "unrefinedinstruction",
            (
                address, 4usize, "", mnemonic, op1, op2, "", "", 0usize, 0usize,
            ),
        );
    }

    #[test]
    fn aarch64_br_accepts_stable_pointer_origins_and_rejects_indexed_loads() {
        use crate::aarch64::mach::A64Mreg;
        use crate::abi::AbiConfig;

        let mut db = DecompileDB::default();
        db.target_abi = Some(AbiConfig::aapcs64());
        let insns = vec![
            control_insn(0x1000, "LDR", branch::PcSource::NotWritten),
            control_insn(0x1004, "BR", branch::PcSource::NotWritten),
            control_insn(0x2000, "LDRSW", branch::PcSource::NotWritten),
            control_insn(0x2004, "BR", branch::PcSource::NotWritten),
            control_insn(0x3000, "BR", branch::PcSource::NotWritten),
        ];

        raw(&mut db, 0x1000, "LDR", "stable_dst", "stable_mem");
        raw(&mut db, 0x1004, "BR", "stable_target", "");
        raw(&mut db, 0x2000, "LDRSW", "indexed_dst", "indexed_mem");
        raw(&mut db, 0x2004, "BR", "indexed_target", "");
        raw(&mut db, 0x3000, "BR", "incoming_target", "");
        db.rel_push("op_register", ("stable_dst", "X16"));
        db.rel_push("op_register", ("stable_target", "X16"));
        db.rel_push("op_register", ("indexed_dst", "X16"));
        db.rel_push("op_register", ("indexed_target", "X16"));
        db.rel_push("op_register", ("incoming_target", "X0"));
        db.rel_push(
            "op_indirect",
            ("stable_mem", "", "X0", "NONE", 1_i64, 8_i64, 8usize),
        );
        db.rel_push(
            "op_indirect",
            ("indexed_mem", "", "X8", "W0", 4_i64, 0_i64, 4usize),
        );
        db.rel_push("reg_def", (0x1000_u64, Mreg::A64(A64Mreg::X16)));
        db.rel_push("reg_use", (0x1000_u64, Mreg::A64(A64Mreg::X0)));
        db.rel_push("reg_use", (0x1004_u64, Mreg::A64(A64Mreg::X16)));
        db.rel_push("reg_def", (0x2000_u64, Mreg::A64(A64Mreg::X16)));
        db.rel_push("reg_use", (0x2000_u64, Mreg::A64(A64Mreg::X8)));
        db.rel_push("reg_use", (0x2000_u64, Mreg::A64(A64Mreg::X0)));
        db.rel_push("reg_use", (0x2004_u64, Mreg::A64(A64Mreg::X16)));
        db.rel_push("reg_use", (0x3000_u64, Mreg::A64(A64Mreg::X0)));
        for (start, end) in [(0x1000, 0x1008), (0x2000, 0x2008), (0x3000, 0x3004)] {
            db.rel_push("known_function_range", (start, end));
            for insn in insns
                .iter()
                .filter(|insn| insn.address >= start && insn.address < end)
            {
                if start == 0x3000 {
                    db.rel_push("block_in_function", (start, start));
                    db.rel_push("code_in_block", (insn.address, start));
                } else {
                    db.rel_push("instr_in_function", (insn.address, start));
                }
            }
        }

        classify_indirect_tailcalls(&mut db, &insns);

        let classified: HashSet<_> = db
            .rel_iter::<(Address, Mreg)>("indirect_tailcall_target")
            .copied()
            .collect();
        assert!(classified.contains(&(0x1004, Mreg::A64(A64Mreg::X16))));
        assert!(classified.contains(&(0x3000, Mreg::A64(A64Mreg::X0))));
        assert!(!classified.iter().any(|(node, _)| *node == 0x2004));
    }

    #[test]
    fn arm_bx_accepts_an_incoming_target_and_rejects_an_indexed_table_load() {
        use crate::abi::AbiConfig;
        use crate::arm32::mach::A32Mreg;

        let mut db = DecompileDB::default();
        db.target_abi = Some(AbiConfig::aapcs32());
        let insns = vec![
            control_insn(0x1000, "BX", branch::PcSource::Computed),
            control_insn(0x2000, "LDR", branch::PcSource::NotWritten),
            control_insn(0x2004, "BX", branch::PcSource::Computed),
        ];
        raw(&mut db, 0x1000, "BX", "incoming_target", "");
        raw(&mut db, 0x2000, "LDR", "table_dst", "table_mem");
        raw(&mut db, 0x2004, "BX", "table_target", "");
        db.rel_push("op_register", ("incoming_target", "R0"));
        db.rel_push("op_register", ("table_dst", "R3"));
        db.rel_push("op_register", ("table_target", "R3"));
        db.rel_push(
            "op_indirect",
            ("table_mem", "", "PC", "R0", 4_i64, 0_i64, 4usize),
        );
        db.rel_push("reg_use", (0x1000_u64, Mreg::A32(A32Mreg::R0)));
        db.rel_push("reg_def", (0x2000_u64, Mreg::A32(A32Mreg::R3)));
        db.rel_push("reg_use", (0x2000_u64, Mreg::A32(A32Mreg::PC)));
        db.rel_push("reg_use", (0x2000_u64, Mreg::A32(A32Mreg::R0)));
        db.rel_push("reg_use", (0x2004_u64, Mreg::A32(A32Mreg::R3)));
        for (start, end) in [(0x1000, 0x1004), (0x2000, 0x2008)] {
            db.rel_push("known_function_range", (start, end));
            for insn in insns
                .iter()
                .filter(|insn| insn.address >= start && insn.address < end)
            {
                db.rel_push("instr_in_function", (insn.address, start));
            }
        }

        classify_indirect_tailcalls(&mut db, &insns);

        let classified: HashSet<_> = db
            .rel_iter::<(Address, Mreg)>("indirect_tailcall_target")
            .copied()
            .collect();
        assert!(classified.contains(&(0x1000, Mreg::A32(A32Mreg::R0))));
        assert!(!classified.iter().any(|(node, _)| *node == 0x2004));
    }
}
