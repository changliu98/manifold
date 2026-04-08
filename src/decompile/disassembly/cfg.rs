
use std::collections::{HashMap, HashSet};
use object::{Object, ObjectSection};
use crate::decompile::disassembly::instruction::DecodedInsn;
use crate::decompile::elevator::DecompileDB;
use crate::x86::types::*;

// Read a little-endian u64 from the given address using preloaded section data.
fn read_u64_at(section_data: &[(u64, u64, Vec<u8>)], addr: u64) -> Option<u64> {
    for (start, end, data) in section_data {
        if addr >= *start && addr + 8 <= *end {
            let off = (addr - start) as usize;
            return Some(u64::from_le_bytes(
                data[off..off+8].try_into().ok()?
            ));
        }
    }
    None
}

// Read a little-endian i32 from the given address using preloaded section data.
fn read_i32_at(section_data: &[(u64, u64, Vec<u8>)], addr: u64) -> Option<i32> {
    for (start, end, data) in section_data {
        if addr >= *start && addr + 4 <= *end {
            let off = (addr - start) as usize;
            return Some(i32::from_le_bytes(
                data[off..off+4].try_into().ok()?
            ));
        }
    }
    None
}

// Build CFG edges, direct calls/jumps, and flags-and-jump pairs from decoded instructions.
pub fn build_cfg(
    db: &mut DecompileDB,
    insns: &[DecodedInsn],
    obj: &object::File,
    jump_table_targets: HashMap<u64, JumpTableInfo>,
) {
    if insns.is_empty() { return; }

    // Pre-compute direct branch targets from immediate operands
    let op_imm_map = super::build_op_imm_map(db);

    let mut direct_targets: std::collections::HashMap<u64, u64> = std::collections::HashMap::new();
    for (addr, _, _, mnem, op1, _, _, _, _, _) in db.rel_iter::<(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize)>("unrefinedinstruction") {
        if !mnem.starts_with('J') && *mnem != "CALL" && !mnem.starts_with("LOOP") {
            continue;
        }
        if *op1 == "0" { continue; }
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

    let addr_set: std::collections::HashSet<u64> =
        insns.iter().map(|d| d.address).collect();

    let block_last_insns: std::collections::HashSet<u64> = db.rel_iter::<(Address, Address, Address)>("block_boundaries")
        .map(|(_, last, _)| *last)
        .collect();

    // Pre-build op1 lookup and register/indirect operand sets for indirect branch detection
    let mut addr_to_op1: HashMap<u64, &'static str> = HashMap::new();
    for (addr, _sz, _pfx, _mnem, op1, _op2, _op3, _op4, _, _) in db.rel_iter::<(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize)>("unrefinedinstruction") {
        addr_to_op1.insert(*addr, *op1);
    }
    let op_register_ids: HashSet<&'static str> = db.rel_iter::<(Symbol, &'static str)>("op_register")
        .map(|(id, _)| *id)
        .collect();
    let op_indirect_ids: HashSet<&'static str> = db.rel_iter::<(Symbol, &'static str, &'static str, &'static str, i64, i64, usize)>("op_indirect")
        .map(|(id, ..)| *id)
        .collect();

    // Only emit inter-block edges to match ddisasm semantics
    let mut cfg_edges: Vec<(u64, u64, &'static str)> = Vec::new();
    let mut direct_calls: Vec<(u64, u64)> = Vec::new();
    let mut direct_jumps: Vec<(u64, u64)> = Vec::new();

    for (i, insn) in insns.iter().enumerate() {
        let next_addr = insn.address + insn.size as u64;

        match insn.mnemonic {
            "JMP" => {
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
                } else if addr_to_op1.get(&insn.address).map_or(false, |op1| {
                    *op1 != "0" && (op_register_ids.contains(op1) || op_indirect_ids.contains(op1))
                }) {
                    cfg_edges.push((insn.address, 0, "indirect"));
                }
            }
            "CALL" => {
                if let Some(target) = get_target(insn.address) {
                    cfg_edges.push((insn.address, target, "call"));
                    direct_calls.push((insn.address, target));
                } else if addr_to_op1.get(&insn.address).map_or(false, |op1| {
                    *op1 != "0" && (op_register_ids.contains(op1) || op_indirect_ids.contains(op1))
                }) {
                    cfg_edges.push((insn.address, 0, "indirect_call"));
                }
                if i + 1 < insns.len() && addr_set.contains(&next_addr) {
                    cfg_edges.push((insn.address, next_addr, "fallthrough"));
                }
            }
            "RET" | "HLT" | "UD2" | "INT3" => {
            }
            m if matches!(m,
                "JE" | "JNE" | "JL" | "JLE" | "JG" | "JGE"
                | "JB" | "JBE" | "JA" | "JAE" | "JP" | "JNP"
                | "JO" | "JNO" | "JS" | "JNS"
                | "JCXZ" | "JECXZ" | "JRCXZ"
                | "LOOP" | "LOOPE" | "LOOPNE"
            ) => {
                if let Some(target) = get_target(insn.address) {
                    cfg_edges.push((insn.address, target, "branch"));
                    direct_jumps.push((insn.address, target));
                }
                if i + 1 < insns.len() && addr_set.contains(&next_addr) {
                    cfg_edges.push((insn.address, next_addr, "fallthrough"));
                }
            }
            _ => {
                // Fallthrough only at block boundaries (last insn of block to next block)
                if block_last_insns.contains(&insn.address)
                    && i + 1 < insns.len()
                    && addr_set.contains(&next_addr)
                {
                    cfg_edges.push((insn.address, next_addr, "fallthrough"));
                }
            }
        }
    }

    // Pair each conditional jump with its nearest preceding comparison instruction
    let mut flags_pairs: Vec<(u64, u64, &'static str)> = Vec::new();

    let addr_idx: std::collections::HashMap<u64, usize> =
        insns.iter().enumerate().map(|(i, d)| (d.address, i)).collect();

    for insn in insns {
        let cond = match insn.mnemonic {
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
            _ => continue,
        };

        if let Some(&idx) = addr_idx.get(&insn.address) {
            let mut j = idx;
            while j > 0 {
                j -= 1;
                let prev = &insns[j];
                if matches!(prev.mnemonic, "CMP" | "TEST" | "SUB" | "AND") {
                    flags_pairs.push((prev.address, insn.address, cond));
                    break;
                }
                if matches!(prev.mnemonic,
                    "ADD" | "OR" | "XOR"
                    | "NEG" | "NOT" | "SHL" | "SHR" | "SAR" | "SAL"
                    | "INC" | "DEC" | "IMUL" | "MUL" | "DIV" | "IDIV"
                    | "ADC" | "SBB" | "RCL" | "RCR" | "ROL" | "ROR"
                    | "BSF" | "BSR" | "POPCNT" | "LZCNT" | "TZCNT"
                ) {
                    break;
                }
                if matches!(prev.mnemonic, "JMP" | "JMPQ" | "CALL" | "RET"
                    | "HLT" | "INT3") {
                    break;
                }
            }
        }
    }

    db.rel_set("ddisasm_cfg_edge", cfg_edges.into_iter().collect::<ascent::boxcar::Vec<_>>());
    db.rel_set("direct_call", direct_calls.into_iter().collect::<ascent::boxcar::Vec<_>>());
    db.rel_set("direct_jump", direct_jumps.into_iter().collect::<ascent::boxcar::Vec<_>>());
    db.rel_set("flags_and_jump_pair", flags_pairs.into_iter().collect::<ascent::boxcar::Vec<_>>());

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

    let addr_set: std::collections::HashSet<u64> =
        insns.iter().map(|d| d.address).collect();

    let got_to_plt = build_got_to_plt_map(db, obj);

    let section_data: Vec<(u64, u64, Vec<u8>)> = obj.sections()
        .filter_map(|s| {
            let data = s.data().ok()?;
            if data.is_empty() { return None; }
            Some((s.address(), s.address() + data.len() as u64, data.to_vec()))
        })
        .collect();

    let mut rip_op_info: HashMap<&'static str, i64> = HashMap::new();
    for (id, _seg, base, _index, _scale, disp, _) in db.rel_iter::<(Symbol, &'static str, &'static str, &'static str, i64, i64, usize)>("op_indirect") {
        if *base == "RIP" {
            rip_op_info.insert(*id, *disp);
        }
    }
    if rip_op_info.is_empty() {
        return result;
    }

    for (addr, size, _pfx, mnem, op1, _op2, _op3, _op4, _, _) in db.rel_iter::<(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize)>("unrefinedinstruction") {
        if !matches!(*mnem, "CALL" | "JMP"
            | "JE" | "JNE" | "JL" | "JLE" | "JG" | "JGE"
            | "JB" | "JBE" | "JA" | "JAE" | "JP" | "JNP"
            | "JO" | "JNO" | "JS" | "JNS") {
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
    pub entry_scale: i64,         // 4 or 8 (byte width per entry)
    pub values: Vec<i64>,         // the actual data values from the table
    pub mov_addr: u64,            // address of the MOV instruction
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

    let section_data: Vec<(u64, u64, Vec<u8>)> = obj.sections()
        .filter_map(|s| {
            let data = s.data().ok()?;
            if data.is_empty() { return None; }
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
    for (id, _seg, base, index, scale, disp, _) in db.rel_iter::<(Symbol, &'static str, &'static str, &'static str, i64, i64, usize)>("op_indirect") {
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
    for (addr, size, _pfx, mnem, op1, op2, _op3, _op4, _, _) in db.rel_iter::<(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize)>("unrefinedinstruction") {
        unrefined_by_addr.insert(*addr, (*size, *mnem, *op1, *op2));
    }

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

        // Only consider indirect JMPs (register or memory operand, not RIP-relative).
        // Check both op1 and op2: the operand swap in instruction.rs puts single-operand
        // JMP targets into op2 (op1 becomes "0").
        let check_op = |op: &str| -> bool {
            if op == "0" { return false; }
            if op_reg_map.contains_key(op) { return true; }
            if let Some(&(_seg, base, _index, _scale, _disp)) = op_indirect_map.get(op) {
                return base != "RIP";
            }
            false
        };
        if !check_op(op1) && !check_op(op2) {
            continue;
        }

        let info = find_jump_table_info(
            insn.address,
            insns,
            &unrefined_by_addr,
            &op_imm_map,
            &op_reg_map,
            &rip_indirect_map,
            &op_indirect_map,
            &addr_set,
            &section_data,
        );

        if let Some(info) = info {
            result.insert(insn.address, info);
        }
    }

    result
}

// Walk backwards from indirect JMP to find the table base (LEA), bound (CMP), and read targets.
fn find_jump_table_info(
    jmp_addr: u64,
    insns: &[DecodedInsn],
    unrefined_by_addr: &HashMap<u64, (usize, &str, &str, &str)>,
    op_imm_map: &HashMap<&str, i64>,
    op_reg_map: &HashMap<&str, &str>,
    rip_indirect_map: &HashMap<&str, i64>,
    op_indirect_map: &HashMap<&str, (&str, &str, &str, i64, i64)>,
    addr_set: &HashSet<u64>,
    section_data: &[(u64, u64, Vec<u8>)],
) -> Option<JumpTableInfo>
{
    let jmp_idx = match insns.iter().position(|i| i.address == jmp_addr) {
        Some(idx) => idx,
        None => return None,
    };

    let mut table_base: Option<u64> = None;
    let mut table_bound: Option<usize> = None;
    let mut default_target: Option<u64> = None;
    let mut first_lea_idx: Option<usize> = None;
    let mut cmp_addr: Option<u64> = None;
    let mut index_reg: Option<String> = None;
    let mut bounds_check_fallthrough_idx: Option<usize> = None;

    let search_limit = 50.min(jmp_idx);

    for i in 1..=search_limit {
        let idx = jmp_idx - i;
        let prev_insn = &insns[idx];

        let (size, mnem, op1, op2) = match unrefined_by_addr.get(&prev_insn.address) {
            Some(info) => *info,
            None => continue,
        };

        match mnem {
            "LEA" => {
                if let Some(&disp) = rip_indirect_map.get(op1) {
                    let base_addr = (prev_insn.address as i64 + size as i64 + disp) as u64;
                    if table_base.is_none() {
                        table_base = Some(base_addr);
                        first_lea_idx = Some(idx);
                    }
                }
            }
            // Clang -O0 non-PIE pattern: mov table(,%index,scale), %reg; jmp *%reg
            // The absolute table address is the displacement in the memory operand.
            "MOV" => {
                if table_base.is_none() {
                    for op in [op1, op2] {
                        if let Some(&(_seg, base, index, scale, disp)) = op_indirect_map.get(op) {
                            if base == "NONE" && index != "NONE" && (scale == 4 || scale == 8) && disp > 0 {
                                table_base = Some(disp as u64);
                                first_lea_idx = Some(idx);
                                if index_reg.is_none() {
                                    index_reg = Some(index.to_string());
                                }
                                break;
                            }
                        }
                    }
                }
            }
            // SUB+JA is equivalent to CMP+JA for bounds checking (clang -O0 pattern:
            // sub $N,%reg; ja default). Both set CF/ZF the same way for unsigned compare.
            "CMP" | "SUB" => {
                if let Some(&imm) = op_imm_map.get(op1) {
                    if table_bound.is_none() && imm > 0 && imm < 1000 {
                        table_bound = Some((imm + 1) as usize);
                        cmp_addr = Some(prev_insn.address);
                        if let Some(&reg_name) = op_reg_map.get(op2) {
                            index_reg = Some(reg_name.to_string());
                        }
                    }
                } else if let Some(&imm) = op_imm_map.get(op2) {
                    if table_bound.is_none() && imm > 0 && imm < 1000 {
                        table_bound = Some((imm + 1) as usize);
                        cmp_addr = Some(prev_insn.address);
                        if let Some(&reg_name) = op_reg_map.get(op1) {
                            index_reg = Some(reg_name.to_string());
                        }
                    }
                }
            }
            // Clang uses AND with a bitmask to constrain the switch index instead
            // of CMP+JA. E.g., `and $3, %edi` limits the index to 0..3 (4 entries).
            // The mask must be 2^n - 1 (all low bits set) to be a valid bounds constraint.
            "AND" => {
                if table_bound.is_none() {
                    let (imm_op, reg_op) = if op_imm_map.contains_key(op1) {
                        (op1, op2)
                    } else if op_imm_map.contains_key(op2) {
                        (op2, op1)
                    } else {
                        continue;
                    };
                    if let Some(&imm) = op_imm_map.get(imm_op) {
                        // Check that mask is 2^n - 1 (i.e., all low bits set)
                        if imm > 0 && imm < 1000 && (imm & (imm + 1)) == 0 {
                            table_bound = Some((imm + 1) as usize);
                            cmp_addr = Some(prev_insn.address);
                            if let Some(&reg_name) = op_reg_map.get(reg_op) {
                                index_reg = Some(reg_name.to_string());
                            }
                        }
                    }
                }
            }
            "JA" | "JAE" | "JB" | "JBE" | "JG" | "JGE" => {
                if let Some(&target) = op_imm_map.get(op1) {
                    if default_target.is_none() {
                        default_target = Some(target as u64);
                        bounds_check_fallthrough_idx = Some(idx + 1);
                    }
                }
            }
            "JMP" | "CALL" | "RET" => {
                break;
            }
            _ => {}
        }

        if table_base.is_some() && table_bound.is_some() {
            break;
        }
    }

    // Fallback: extract table base from the JMP operand itself.
    // Handles non-PIE pattern: jmp *table_addr(,index,scale) where the absolute
    // table address is embedded as the displacement in the memory operand.
    if table_base.is_none() {
        if let Some((_, _, op1, _)) = unrefined_by_addr.get(&jmp_addr) {
            if let Some(&(_seg, base, index, scale, disp)) = op_indirect_map.get(op1) {
                if base == "NONE" && index != "NONE" && (scale == 4 || scale == 8) && disp > 0 {
                    table_base = Some(disp as u64);
                    if index_reg.is_none() {
                        index_reg = Some(index.to_string());
                    }
                }
            }
        }
    }

    let table_base = match table_base {
        Some(base) => base,
        None => return None,
    };

    let table_bound = table_bound.unwrap_or(256);

    let max_entries = table_bound.min(512);

    // Try 4-byte relative offsets first (most common format)
    let mut ordered_targets: Vec<u64> = Vec::new();

    for i in 0..max_entries {
        let entry_addr = table_base + (i as u64 * 4);
        if let Some(offset) = read_i32_at(section_data, entry_addr) {
            let target = (table_base as i64 + offset as i64) as u64;
            if addr_set.contains(&target) {
                ordered_targets.push(target);
            } else {
                break;
            }
        } else {
            break;
        }
    }

    if ordered_targets.len() >= 2 {
        let impl_start = bounds_check_fallthrough_idx.or(first_lea_idx);
        let impl_addrs = collect_impl_addrs(insns, impl_start, jmp_idx);

        return Some(JumpTableInfo {
            ordered_targets,
            impl_addrs,
            cmp_addr,
            index_reg: index_reg.clone(),
        });
    }

    // Fall back to 8-byte absolute addresses
    ordered_targets.clear();
    for i in 0..max_entries {
        let entry_addr = table_base + (i as u64 * 8);
        if let Some(target) = read_u64_at(section_data, entry_addr) {
            if addr_set.contains(&target) {
                ordered_targets.push(target);
            } else if target > 0 && target < 0x10000 {
                break;
            }
        } else {
            break;
        }
    }

    if ordered_targets.len() >= 2 {
        let impl_start = bounds_check_fallthrough_idx.or(first_lea_idx);
        let impl_addrs = collect_impl_addrs(insns, impl_start, jmp_idx);

        return Some(JumpTableInfo {
            ordered_targets,
            impl_addrs,
            cmp_addr,
            index_reg,
        });
    }

    None
}

// Collect addresses of instructions that implement the jump table lookup (LEA through JMP).
fn collect_impl_addrs(insns: &[DecodedInsn], first_lea_idx: Option<usize>, jmp_idx: usize) -> Vec<u64> {
    let start = first_lea_idx.unwrap_or(jmp_idx);
    (start..=jmp_idx)
        .map(|i| insns[i].address)
        .collect()
}

// Detect clang data lookup tables: `mov disp(,%reg,4), %dst` where disp is in rodata.
pub fn analyze_data_lookup_tables(
    db: &DecompileDB,
    insns: &[DecodedInsn],
    obj: &object::File,
) -> Vec<DataLookupTableInfo> {
    let mut results: Vec<DataLookupTableInfo> = Vec::new();

    // Collect rodata section ranges
    let rodata_ranges: Vec<(u64, u64, Vec<u8>)> = obj.sections()
        .filter_map(|s| {
            let name = s.name().unwrap_or("");
            if !name.contains("rodata") && !name.contains(".rdata") {
                return None;
            }
            let data = s.data().ok()?;
            if data.is_empty() { return None; }
            Some((s.address(), s.address() + data.len() as u64, data.to_vec()))
        })
        .collect();

    if rodata_ranges.is_empty() {
        return results;
    }

    let section_data: Vec<(u64, u64, Vec<u8>)> = obj.sections()
        .filter_map(|s| {
            let data = s.data().ok()?;
            if data.is_empty() { return None; }
            Some((s.address(), s.address() + data.len() as u64, data.to_vec()))
        })
        .collect();

    let op_imm_map = super::build_op_imm_map(db);
    let mut op_reg_map: HashMap<&str, &str> = HashMap::new();
    for (id, reg) in db.rel_iter::<(Symbol, &'static str)>("op_register") {
        op_reg_map.insert(id, reg);
    }

    let mut op_indirect_map: HashMap<&str, (&str, &str, &str, i64, i64)> = HashMap::new();
    for (id, _seg, base, index, scale, disp, _) in db.rel_iter::<(Symbol, &'static str, &'static str, &'static str, i64, i64, usize)>("op_indirect") {
        op_indirect_map.insert(*id, (*_seg, *base, *index, *scale, *disp));
    }

    let mut unrefined_by_addr: HashMap<u64, (usize, &str, &str, &str)> = HashMap::new();
    for (addr, size, _pfx, mnem, op1, op2, _op3, _op4, _, _) in db.rel_iter::<(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize)>("unrefinedinstruction") {
        unrefined_by_addr.insert(*addr, (*size, *mnem, *op1, *op2));
    }

    // Scan for MOV instructions with scaled-index addressing and no base register
    for (i, insn) in insns.iter().enumerate() {
        let (_, mnem, op1, op2) = match unrefined_by_addr.get(&insn.address) {
            Some(info) => *info,
            None => continue,
        };

        if mnem != "MOV" {
            continue;
        }

        // Check if op2 (source for load) is an indirect operand with no base and scaled index
        // Pattern: disp(,%reg,scale) where disp points into rodata
        let (table_base, scale, _index_str) = if let Some(&(_seg, base, index, sc, disp)) = op_indirect_map.get(op2) {
            if base != "NONE" || index == "NONE" || (sc != 4 && sc != 8) || disp <= 0 {
                continue;
            }
            // Check if disp points into a rodata section
            let disp_u64 = disp as u64;
            let in_rodata = rodata_ranges.iter().any(|(start, end, _)| disp_u64 >= *start && disp_u64 < *end);
            if !in_rodata {
                continue;
            }
            (disp_u64, sc, index)
        } else {
            continue;
        };

        // Look backwards for bounds check (CMP+JA or AND)
        let mut bounds_count: Option<usize> = None;
        let mut bounds_addr: Option<u64> = None;
        let mut index_reg: Option<String> = None;
        let search_limit = 20.min(i);

        for j in 1..=search_limit {
            let idx = i - j;
            let prev = &insns[idx];
            let (_, prev_mnem, prev_op1, prev_op2) = match unrefined_by_addr.get(&prev.address) {
                Some(info) => *info,
                None => continue,
            };

            match prev_mnem {
                "CMP" => {
                    let imm = op_imm_map.get(prev_op1).or_else(|| op_imm_map.get(prev_op2));
                    if let Some(&val) = imm {
                        if val > 0 && val < 1000 {
                            bounds_count = Some((val + 1) as usize);
                            bounds_addr = Some(prev.address);
                            let reg_op = if op_imm_map.contains_key(prev_op1) { prev_op2 } else { prev_op1 };
                            if let Some(&reg_name) = op_reg_map.get(reg_op) {
                                index_reg = Some(reg_name.to_string());
                            }
                        }
                    }
                    break;
                }
                "AND" => {
                    let imm = op_imm_map.get(prev_op1).or_else(|| op_imm_map.get(prev_op2));
                    if let Some(&val) = imm {
                        if val > 0 && val < 1000 && (val & (val + 1)) == 0 {
                            bounds_count = Some((val + 1) as usize);
                            bounds_addr = Some(prev.address);
                            let reg_op = if op_imm_map.contains_key(prev_op1) { prev_op2 } else { prev_op1 };
                            if let Some(&reg_name) = op_reg_map.get(reg_op) {
                                index_reg = Some(reg_name.to_string());
                            }
                        }
                    }
                    break;
                }
                "JMP" | "CALL" | "RET" => break,
                _ => {}
            }
        }

        let entry_count = bounds_count.unwrap_or(256).min(512);

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
                insn.address, values.len(), scale, table_base
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
fn build_got_to_plt_map(
    db: &DecompileDB,
    obj: &object::File,
) -> HashMap<u64, u64> {
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

