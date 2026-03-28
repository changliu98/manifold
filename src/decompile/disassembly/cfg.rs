
use std::collections::{HashMap, HashSet};
use object::{Object, ObjectSection};
use crate::decompile::disassembly::instruction::DecodedInsn;
use crate::decompile::elevator::DecompileDB;
use crate::x86::types::*;

// Build CFG edges, direct calls/jumps, and flags-and-jump pairs from decoded instructions.
pub fn build_cfg(
    db: &mut DecompileDB,
    insns: &[DecodedInsn],
    obj: &object::File,
    jump_table_targets: HashMap<u64, JumpTableInfo>,
) {
    if insns.is_empty() { return; }

    // Pre-compute direct branch targets from immediate operands
    let mut op_imm_map: std::collections::HashMap<&str, i64> = std::collections::HashMap::new();
    for (id, val, _) in db.rel_iter::<(Symbol, i64, usize)>("op_immediate") {
        op_imm_map.insert(id, *val);
    }

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
                } else if is_indirect_branch(db, insn) {
                    cfg_edges.push((insn.address, 0, "indirect"));
                }
            }
            "CALL" => {
                if let Some(target) = get_target(insn.address) {
                    cfg_edges.push((insn.address, target, "call"));
                    direct_calls.push((insn.address, target));
                } else if is_indirect_branch(db, insn) {
                    cfg_edges.push((insn.address, 0, "indirect_call"));
                }
                if i + 1 < insns.len() && addr_set.contains(&next_addr) {
                    cfg_edges.push((insn.address, next_addr, "fallthrough"));
                }
            }
            "RET" | "HLT" | "UD2" | "INT3" => {
            }
            m if is_conditional_jump(m) => {
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
        let cond = match jcc_condition(insn.mnemonic) {
            Some(c) => c,
            None => continue,
        };

        if let Some(&idx) = addr_idx.get(&insn.address) {
            let mut j = idx;
            while j > 0 {
                j -= 1;
                let prev = &insns[j];
                if is_comparison(prev.mnemonic) {
                    flags_pairs.push((prev.address, insn.address, cond));
                    break;
                }
                if is_flag_clobbering(prev.mnemonic) {
                    break;
                }
                if is_control_flow(prev.mnemonic) {
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

    let read_u64_at = |addr: u64| -> Option<u64> {
        for (start, end, data) in &section_data {
            if addr >= *start && addr + 8 <= *end {
                let off = (addr - start) as usize;
                return Some(u64::from_le_bytes(
                    data[off..off+8].try_into().ok()?
                ));
            }
        }
        None
    };

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

            if let Some(target) = read_u64_at(got_addr) {
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

    let read_i32_at = |addr: u64| -> Option<i32> {
        for (start, end, data) in &section_data {
            if addr >= *start && addr + 4 <= *end {
                let off = (addr - start) as usize;
                return Some(i32::from_le_bytes(
                    data[off..off+4].try_into().ok()?
                ));
            }
        }
        None
    };

    let read_u64_at = |addr: u64| -> Option<u64> {
        for (start, end, data) in &section_data {
            if addr >= *start && addr + 8 <= *end {
                let off = (addr - start) as usize;
                return Some(u64::from_le_bytes(
                    data[off..off+8].try_into().ok()?
                ));
            }
        }
        None
    };

    let mut op_imm_map: HashMap<&str, i64> = HashMap::new();
    for (id, val, _) in db.rel_iter::<(Symbol, i64, usize)>("op_immediate") {
        op_imm_map.insert(id, *val);
    }

    let mut op_reg_map: HashMap<&str, &str> = HashMap::new();
    for (id, reg) in db.rel_iter::<(Symbol, &'static str)>("op_register") {
        op_reg_map.insert(id, reg);
    }

    let mut rip_indirect_map: HashMap<&str, i64> = HashMap::new();
    for (id, _seg, base, _index, _scale, disp, _) in db.rel_iter::<(Symbol, &'static str, &'static str, &'static str, i64, i64, usize)>("op_indirect") {
        if *base == "RIP" {
            rip_indirect_map.insert(*id, *disp);
        }
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

        let (_, mnem, op1, _) = match unrefined_by_addr.get(&insn.address) {
            Some(info) => *info,
            None => continue,
        };

        if mnem != "JMP" {
            continue;
        }

        // Only consider indirect JMPs (register or memory operand, not RIP-relative)
        let is_reg_indirect = op_reg_map.contains_key(op1);
        let is_mem_indirect = {
            let mut found = false;
            for (id, _seg, base, _index, _scale, _disp, _) in db.rel_iter::<(Symbol, &'static str, &'static str, &'static str, i64, i64, usize)>("op_indirect") {
                if *id == op1 && *base != "RIP" {
                    found = true;
                    break;
                }
            }
            found
        };
        if !is_reg_indirect && !is_mem_indirect {
            continue;
        }

        let info = find_jump_table_info(
            insn.address,
            insns,
            &unrefined_by_addr,
            &op_imm_map,
            &op_reg_map,
            &rip_indirect_map,
            &addr_set,
            &read_i32_at,
            &read_u64_at,
        );

        if let Some(info) = info {
            result.insert(insn.address, info);
        }
    }

    result
}

// Walk backwards from indirect JMP to find the table base (LEA), bound (CMP), and read targets.
fn find_jump_table_info<F1, F2>(
    jmp_addr: u64,
    insns: &[DecodedInsn],
    unrefined_by_addr: &HashMap<u64, (usize, &str, &str, &str)>,
    op_imm_map: &HashMap<&str, i64>,
    op_reg_map: &HashMap<&str, &str>,
    rip_indirect_map: &HashMap<&str, i64>,
    addr_set: &HashSet<u64>,
    read_i32_at: &F1,
    read_u64_at: &F2,
) -> Option<JumpTableInfo>
where
    F1: Fn(u64) -> Option<i32>,
    F2: Fn(u64) -> Option<u64>,
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
            "CMP" => {
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
        if let Some(offset) = read_i32_at(entry_addr) {
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
        if let Some(target) = read_u64_at(entry_addr) {
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

fn is_conditional_jump(mnem: &str) -> bool {
    matches!(mnem,
        "JE" | "JNE" | "JL" | "JLE" | "JG" | "JGE"
        | "JB" | "JBE" | "JA" | "JAE" | "JP" | "JNP"
        | "JO" | "JNO" | "JS" | "JNS"
        | "JCXZ" | "JECXZ" | "JRCXZ"
        | "LOOP" | "LOOPE" | "LOOPNE"
    )
}

// Primary comparison and flag-setting instructions for conditional jumps.
fn is_comparison(mnem: &str) -> bool {
    matches!(mnem, "CMP" | "TEST" | "SUB" | "AND")
}

// Instructions that clobber flags as a side effect, breaking CMP/TEST pairing.
fn is_flag_clobbering(mnem: &str) -> bool {
    matches!(mnem,
        "ADD" | "OR" | "XOR"
        | "NEG" | "NOT" | "SHL" | "SHR" | "SAR" | "SAL"
        | "INC" | "DEC" | "IMUL" | "MUL" | "DIV" | "IDIV"
        | "ADC" | "SBB" | "RCL" | "RCR" | "ROL" | "ROR"
        | "BSF" | "BSR" | "POPCNT" | "LZCNT" | "TZCNT"
    )
}

fn is_control_flow(mnem: &str) -> bool {
    mnem == "JMP" || mnem == "JMPQ" || mnem == "CALL" || mnem == "RET"
        || mnem == "HLT" || mnem == "INT3"
}

// Map conditional jump mnemonics to their condition code strings.
fn jcc_condition(mnem: &str) -> Option<&'static str> {
    match mnem {
        "JE" => Some("e"),
        "JNE" => Some("ne"),
        "JL" => Some("l"),
        "JLE" => Some("le"),
        "JG" => Some("g"),
        "JGE" => Some("ge"),
        "JB" => Some("b"),
        "JBE" => Some("be"),
        "JA" => Some("a"),
        "JAE" => Some("ae"),
        "JP" => Some("p"),
        "JNP" => Some("np"),
        "JO" => Some("o"),
        "JNO" => Some("no"),
        "JS" => Some("s"),
        "JNS" => Some("ns"),
        _ => None,
    }
}

// Check if a branch has an indirect operand (register or memory, not immediate).
fn is_indirect_branch(db: &DecompileDB, insn: &DecodedInsn) -> bool {
    for (addr, _sz, _pfx, _mnem, op1, _op2, _op3, _op4, _, _) in db.rel_iter::<(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize)>("unrefinedinstruction") {
        if *addr != insn.address { continue; }
        if *op1 == "0" { return false; }

        for (id, _reg) in db.rel_iter::<(Symbol, &'static str)>("op_register") {
            if *id == *op1 {
                return true;
            }
        }

        for (id, _seg, _base, _index, _scale, _disp, _) in db.rel_iter::<(Symbol, &'static str, &'static str, &'static str, i64, i64, usize)>("op_indirect") {
            if *id == *op1 {
                return true;
            }
        }
        break;
    }
    false
}
