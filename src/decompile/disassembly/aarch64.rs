// AArch64 decoding into the same DB relations as x86, with two interface facts: operand order is capstone's (destination first), and def/use comes from opcode shape since Arm64Operand has no access field.

use capstone::arch::arm64::{Arm64Operand, Arm64OperandType, Arm64Shift, Arm64Vas};
use capstone::prelude::*;
use object::{Object, ObjectSection};

use crate::aarch64::mach::A64Mreg;
use crate::decompile::disassembly::branch;
use crate::decompile::disassembly::instruction::{is_executable_section, DecodedInsn};
use crate::decompile::disassembly::operand::*;
use crate::decompile::elevator::DecompileDB;
use crate::mreg::Mreg;

// Which explicit operands an instruction writes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DefShape {
    // Operand 0 is the destination. The common case.
    Op0,
    // Operands 0 and 1 are both destinations (load-pair).
    Op0Op1,
    // No register destination: stores, compares (they write only flags), branches.
    None,
}

// Classify by mnemonic, most-specific first, or the broad prefix checks below would shadow several tests.
fn def_shape(mnem: &str) -> DefShape {
    // Load-pair writes two registers; store-pair writes none.
    if matches!(mnem, "LDP" | "LDNP" | "LDPSW") {
        return DefShape::Op0Op1;
    }
    // Compares and test-and-set-flags write only NZCV.
    if matches!(
        mnem,
        "CMP" | "CMN" | "TST" | "CCMP" | "CCMN" | "FCMP" | "FCMPE" | "FCCMP" | "FCCMPE"
    ) {
        return DefShape::None;
    }
    // Branches. BL/BLR additionally write X30, added as an implicit def by the caller.
    if matches!(
        mnem,
        "B" | "BR" | "BL" | "BLR" | "RET" | "CBZ" | "CBNZ" | "TBZ" | "TBNZ" | "BRK" | "SVC"
    ) || mnem.starts_with("B.")
    {
        return DefShape::None;
    }
    // Every store form (STR/STRB/STRH/STUR/STP/STLR/...); the LDR-vs-STR split is the biggest def/use distinction in AArch64 code.
    if mnem.starts_with("ST") {
        return DefShape::None;
    }
    DefShape::Op0
}

// Registers whose writes are not modelled as value definitions.
fn is_discardable_def(r: A64Mreg) -> bool {
    // Writing the zero register discards the result; `SUBS XZR, Xn, Xm` is CMP.
    r == A64Mreg::ZR
}

pub fn disassemble_sections(db: &mut DecompileDB, obj: &object::File) -> Vec<DecodedInsn> {
    let cs = Capstone::new()
        .arm64()
        .mode(arch::arm64::ArchMode::Arm)
        .detail(true)
        .build()
        .expect("Failed to create capstone arm64 engine");

    let mut decoded: Vec<DecodedInsn> = Vec::new();

    let mut op_registers: Vec<(&'static str, &'static str)> = Vec::new();
    let mut op_immediates: Vec<(&'static str, i64, usize)> = Vec::new();
    let mut op_indirects: Vec<(
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        i64,
        i64,
        usize,
    )> = Vec::new();
    let mut op_indirect_extends: Vec<(&'static str, &'static str)> = Vec::new();
    let mut instructions: Vec<(
        u64,
        usize,
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        usize,
        usize,
    )> = Vec::new();
    let mut stack_defs: Vec<(u64, &'static str, i64)> = Vec::new();
    let mut stack_uses: Vec<(u64, &'static str, i64)> = Vec::new();
    let mut reg_defs: Vec<(u64, Mreg)> = Vec::new();
    let mut reg_uses: Vec<(u64, Mreg)> = Vec::new();
    let mut adjusts_stack: Vec<(u64, &'static str, i64)> = Vec::new();
    let mut stack_base_moves: Vec<(u64, &'static str, &'static str)> = Vec::new();
    let mut stack_base_move_offsets: Vec<(u64, &'static str, &'static str, i64)> = Vec::new();
    let mut decoded_memory_writes: Vec<(u64, usize)> = Vec::new();
    let mut decoded_memory_write_unknown: Vec<(u64, &'static str)> = Vec::new();

    for section in obj.sections() {
        if !is_executable_section(&section) {
            continue;
        }
        let data = match section.data() {
            Ok(d) => d,
            Err(_) => continue,
        };
        let base_addr = section.address();

        // Resync sweep. capstone's disasm_all stops at the first word it cannot decode and
        // reports NOTHING after it, so a single literal-pool word, pad or unknown encoding
        // silences the rest of the section -- silently, since the call still succeeds.
        // AArch64 is fixed 4-byte aligned, so stepping one slot and resuming is sound.
        let mut runs: Vec<capstone::Instructions> = Vec::new();
        let mut off = 0usize;
        while off < data.len() {
            let run_start = base_addr + off as u64;
            let Ok(insns) = cs.disasm_all(&data[off..], run_start) else {
                break;
            };
            let consumed = match insns.as_ref().last() {
                Some(last) => (last.address() - run_start) as usize + last.len(),
                None => 0,
            };
            if consumed == 0 {
                off += 4;
                continue;
            }
            runs.push(insns);
            off += consumed;
            if off < data.len() {
                off += 4;
            }
        }

        for insn in runs.iter().flat_map(|r| r.as_ref().iter()) {
            let addr = insn.address();
            let size = insn.len();

            let mnemonic: &'static str = Box::leak(
                insn.mnemonic()
                    .unwrap_or("")
                    .to_ascii_uppercase()
                    .into_boxed_str(),
            );

            let detail = cs
                .insn_detail(insn)
                .expect("insn_detail failed; was detail mode enabled?");
            let arch_detail = detail.arch_detail();
            let a64 = arch_detail.arm64().expect("Not arm64");
            let ops: Vec<_> = a64.operands().collect();
            let writeback = a64.writeback();
            let mem_pos = ops
                .iter()
                .position(|o| matches!(o.op_type, Arm64OperandType::Mem(_)));
            let (memory_write_bytes, memory_write_unknown) = match special_memory_write(mnemonic) {
                Some(classified) => classified,
                None => (fixed_memory_write_bytes(&cs, mnemonic, &ops), None),
            };

            let shape = def_shape(mnemonic);
            // The transferred register of a load is operand 0. A store's last
            // register before memory is the value (exclusive stores put their
            // W-status destination first), so its view gives the access width.
            let transferred_reg = if memory_write_bytes.is_some() || memory_write_unknown.is_some()
            {
                mem_pos.and_then(|p| {
                    ops[..p].iter().rev().find_map(|o| match o.op_type {
                        Arm64OperandType::Reg(r) => Some(capstone_reg_name(&cs, r)),
                        _ => None,
                    })
                })
            } else {
                ops.first().and_then(|o| match o.op_type {
                    Arm64OperandType::Reg(r) => Some(capstone_reg_name(&cs, r)),
                    _ => None,
                })
            };
            let mem_size = access_size(mnemonic, transferred_reg);
            // NOP and the vector-zeroing idioms define nothing worth tracking.
            let is_nop = matches!(mnemonic, "NOP" | "HINT");

            let mut op_ids: [&'static str; 4] = [NO_OP; 4];

            for (i, op) in ops.iter().enumerate() {
                if i >= 4 {
                    break;
                }
                match &op.op_type {
                    Arm64OperandType::Reg(reg_id) => {
                        let id = alloc_op_id();
                        let name = capstone_reg_name(&cs, *reg_id);
                        op_registers.push((id, name));
                        op_ids[i] = id;

                        if is_nop {
                            continue;
                        }
                        let a64reg = A64Mreg::from(name);
                        if a64reg == A64Mreg::Unknown {
                            continue;
                        }
                        let mreg = Mreg::a64(a64reg);
                        let is_def = match shape {
                            DefShape::Op0 => i == 0,
                            DefShape::Op0Op1 => i <= 1,
                            DefShape::None => false,
                        };
                        if is_def && !is_discardable_def(a64reg) {
                            reg_defs.push((addr, mreg));
                        }
                        // A destination is not also a source, and the zero register reads as the constant 0 rather than a value.
                        if !is_def && a64reg != A64Mreg::ZR {
                            reg_uses.push((addr, mreg));
                        }
                    }
                    Arm64OperandType::Imm(val) => {
                        let id = alloc_op_id();
                        op_immediates.push((id, *val, 0));
                        op_ids[i] = id;
                    }
                    Arm64OperandType::Mem(mem) => {
                        let id = alloc_op_id();
                        let base = reg_or_none(&cs, mem.base());
                        let index = reg_or_none(&cs, mem.index());
                        // The scale of an indexed load lives on the operand's shifter ([Xn, Xm, LSL #3]), not inside the memory operand.
                        let scale = match op.shift {
                            Arm64Shift::Lsl(amount) => 1i64 << amount,
                            _ => 1,
                        };
                        let disp = mem.disp() as i64;
                        op_indirects.push((id, "NONE", base, index, scale, disp, mem_size));
                        op_ids[i] = id;

                        // [Xn, Wm, SXTW #2] extends a 32-bit index before scaling; no Addressing variant carries an extension, so record which kind for the frontend's explicit cast.
                        if let Some(ext) = extender_name(op.ext) {
                            op_indirect_extends.push((id, ext));
                        }

                        if is_nop {
                            continue;
                        }
                        // Address arithmetic reads the base and index registers.
                        for r in [base, index] {
                            if r == "NONE" {
                                continue;
                            }
                            let a64reg = A64Mreg::from(r);
                            if a64reg != A64Mreg::Unknown && a64reg != A64Mreg::ZR {
                                reg_uses.push((addr, Mreg::a64(a64reg)));
                            }
                        }
                        // Pre/post-index addressing writes the base back.
                        if writeback && base != "NONE" {
                            let a64reg = A64Mreg::from(base);
                            if a64reg != A64Mreg::Unknown {
                                reg_defs.push((addr, Mreg::a64(a64reg)));
                            }
                        }

                        // Frame-relative access. X29 is the AArch64 frame pointer.
                        if (base == "SP" || base == "X29") && index == "NONE" {
                            if shape == DefShape::None && mnemonic.starts_with("ST") {
                                stack_defs.push((addr, base, disp));
                            } else {
                                stack_uses.push((addr, base, disp));
                            }
                        }
                    }
                    _ => {}
                }
            }

            if let Some(bytes) = memory_write_bytes {
                decoded_memory_writes.push((addr, bytes));
            }
            if let Some(reason) = memory_write_unknown {
                decoded_memory_write_unknown.push((addr, reason));
            }

            if !is_nop {
                // BL/BLR write the link register; capstone reports this only inconsistently and the call-return-address model depends on it.
                if matches!(mnemonic, "BL" | "BLR") {
                    reg_defs.push((addr, Mreg::a64(A64Mreg::X30)));
                }
                // RET reads it (RET with no operand is `RET X30`).
                if mnemonic == "RET" && ops.is_empty() {
                    reg_uses.push((addr, Mreg::a64(A64Mreg::X30)));
                }
            }

            // Stack pointer movement.
            if let Some(delta) = sp_adjustment(mnemonic, &ops, mem_pos, writeback, &cs) {
                adjusts_stack.push((addr, "SP", delta));
            }

            // Frame-pointer establish/teardown matched by SHAPE (<reg> := <reg> + <imm>), since clang spells it several ways and the offset is load-bearing (X29 may sit N bytes above SP).
            if matches!(mnemonic, "MOV" | "ADD") && ops.len() >= 2 {
                if let (Arm64OperandType::Reg(d), Arm64OperandType::Reg(s)) =
                    (&ops[0].op_type, &ops[1].op_type)
                {
                    let offset = match ops.get(2).map(|o| &o.op_type) {
                        None => Some(0),
                        Some(Arm64OperandType::Imm(v)) => Some(*v),
                        // A register or shifted third operand is real arithmetic, not a frame establish.
                        Some(_) => None,
                    };
                    let dst = A64Mreg::from(capstone_reg_name(&cs, *d)).name();
                    let src = A64Mreg::from(capstone_reg_name(&cs, *s)).name();
                    let frame_reg = |r: &str| r == "SP" || r == "X29";
                    if let Some(offset) = offset {
                        if frame_reg(dst) && frame_reg(src) && dst != src {
                            stack_base_move_offsets.push((addr, src, dst, offset));
                            // The offsetless relation means exactly dst := src, which every consumer relies on, so it is emitted only for the genuinely zero-offset case.
                            if offset == 0 {
                                stack_base_moves.push((addr, src, dst));
                            }
                        }
                    }
                }
            }

            instructions.push((
                addr, size, "", mnemonic, op_ids[0], op_ids[1], op_ids[2], op_ids[3], 0, 0,
            ));

            let op_str: &'static str = Box::leak(
                insn.op_str()
                    .unwrap_or("")
                    .to_ascii_uppercase()
                    .into_boxed_str(),
            );

            decoded.push(DecodedInsn {
                address: addr,
                size,
                mnemonic,
                op_str,
                pc_source: branch::PcSource::NotWritten,
            });
        }
    }

    decoded.sort_by_key(|d| d.address);
    instructions.sort_by_key(|t| t.0);

    db.rel_set(
        "unrefinedinstruction",
        instructions.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );

    // AArch64 instructions are all 4 bytes, but a section can end mid-stream, so adjacency is checked rather than assumed.
    let mut nexts: Vec<(u64, u64)> = Vec::with_capacity(decoded.len());
    for w in decoded.windows(2) {
        if w[0].address + w[0].size as u64 == w[1].address {
            nexts.push((w[0].address, w[1].address));
        }
    }
    db.rel_set(
        "next",
        nexts.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );

    db.rel_set(
        "op_register",
        op_registers.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "op_immediate",
        op_immediates
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "op_indirect",
        op_indirects.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "op_indirect_extend",
        op_indirect_extends
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "stack_def",
        stack_defs.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "stack_use",
        stack_uses.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "reg_def",
        reg_defs.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "reg_use",
        reg_uses.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "adjusts_stack",
        adjusts_stack
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "stack_base_move",
        stack_base_moves
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "stack_base_move_offset",
        stack_base_move_offsets
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "decoded_memory_write_bytes",
        decoded_memory_writes
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "decoded_memory_write_unknown",
        decoded_memory_write_unknown
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );

    decoded
}

// Canonical 64-bit name of a register operand, or "NONE"; goes through A64Mreg so a raw-string test like base == "X29" cannot silently never match.
fn reg_or_none(cs: &Capstone, reg: RegId) -> &'static str {
    if reg.0 == 0 {
        return "NONE";
    }
    A64Mreg::from(capstone_reg_name(cs, reg)).name()
}

fn extender_name(ext: capstone::arch::arm64::Arm64Extender) -> Option<&'static str> {
    use capstone::arch::arm64::Arm64Extender::*;
    match ext {
        Sxtw => Some("SXTW"),
        Sxtx => Some("SXTX"),
        Sxtb => Some("SXTB"),
        Sxth => Some("SXTH"),
        Uxtw => Some("UXTW"),
        Uxtx => Some("UXTX"),
        Uxtb => Some("UXTB"),
        Uxth => Some("UXTH"),
        Invalid => None,
    }
}

// How much this instruction moves SP: explicit SUB/ADD SP, plus pre-index and post-index writeback, which are how AArch64 spells push and pop.
fn sp_adjustment(
    mnem: &str,
    ops: &[capstone::arch::arm64::Arm64Operand],
    mem_pos: Option<usize>,
    writeback: bool,
    cs: &Capstone,
) -> Option<i64> {
    if matches!(mnem, "SUB" | "ADD") && ops.len() >= 3 {
        let dst = as_reg_name(cs, &ops[0])?;
        let src = as_reg_name(cs, &ops[1])?;
        if dst == "SP" && src == "SP" {
            if let Arm64OperandType::Imm(v) = ops[2].op_type {
                return Some(if mnem == "SUB" { -v } else { v });
            }
        }
        return None;
    }

    if !writeback {
        return None;
    }
    let mem_pos = mem_pos?;
    let Arm64OperandType::Mem(mem) = &ops[mem_pos].op_type else {
        return None;
    };
    if reg_or_none(cs, mem.base()) != "SP" {
        return None;
    }
    // Post-index carries its delta in a trailing immediate operand; pre-index carries it in the memory operand's displacement.
    match ops.get(mem_pos + 1).map(|o| &o.op_type) {
        Some(Arm64OperandType::Imm(v)) => Some(*v),
        _ => Some(mem.disp() as i64),
    }
}

// Canonical name of an explicit register operand; see reg_or_none.
fn as_reg_name(cs: &Capstone, op: &capstone::arch::arm64::Arm64Operand) -> Option<&'static str> {
    match op.op_type {
        Arm64OperandType::Reg(r) => Some(A64Mreg::from(capstone_reg_name(cs, r)).name()),
        _ => None,
    }
}

// Byte width of a load/store access: capstone carries no operand size, but the mnemonic suffix determines it, falling back to the transferred register's width.
fn access_size(mnem: &str, first_reg: Option<&str>) -> usize {
    // Suffix forms pin the width regardless of register view.
    if mnem.ends_with('B') && mnem.starts_with(['L', 'S', 'C']) {
        return 1;
    }
    if mnem.ends_with('H') && mnem.starts_with(['L', 'S', 'C']) {
        return 2;
    }
    // LDRSW/LDURSW load 4 bytes and sign-extend to 8.
    if mnem.ends_with("SW") {
        return 4;
    }
    // Otherwise the register view decides: Wn/Sn are 4 bytes, Xn/Dn are 8, Qn is 16.
    match first_reg.map(|r| r.as_bytes().first().copied().unwrap_or(b'X')) {
        Some(b'W') | Some(b'S') => 4,
        Some(b'Q') => 16,
        Some(b'H') => 2,
        Some(b'B') => 1,
        _ => 8,
    }
}

fn vector_arrangement_bytes(vas: Arm64Vas) -> Option<usize> {
    Some(match vas {
        Arm64Vas::ARM64_VAS_16B
        | Arm64Vas::ARM64_VAS_8H
        | Arm64Vas::ARM64_VAS_4S
        | Arm64Vas::ARM64_VAS_2D
        | Arm64Vas::ARM64_VAS_1Q => 16,
        Arm64Vas::ARM64_VAS_8B
        | Arm64Vas::ARM64_VAS_4H
        | Arm64Vas::ARM64_VAS_2S
        | Arm64Vas::ARM64_VAS_1D => 8,
        Arm64Vas::ARM64_VAS_4B | Arm64Vas::ARM64_VAS_2H | Arm64Vas::ARM64_VAS_1S => 4,
        Arm64Vas::ARM64_VAS_1H => 2,
        Arm64Vas::ARM64_VAS_1B => 1,
        Arm64Vas::ARM64_VAS_INVALID => return None,
    })
}

fn store_operand_bytes(cs: &Capstone, mnem: &str, op: &Arm64Operand) -> Option<usize> {
    if let Some(bytes) = vector_arrangement_bytes(op.vas) {
        return Some(bytes);
    }
    match op.op_type {
        Arm64OperandType::Reg(reg) => Some(access_size(mnem, Some(capstone_reg_name(cs, reg)))),
        _ => None,
    }
}

fn special_memory_write(mnem: &str) -> Option<(Option<usize>, Option<&'static str>)> {
    if matches!(mnem, "ST64B" | "ST64BV" | "ST64BV0") {
        return Some((Some(64), None));
    }
    if mnem == "STZG" {
        return Some((Some(16), None));
    }
    if mnem == "STZ2G" {
        return Some((Some(32), None));
    }
    if matches!(mnem, "STG" | "ST2G" | "STGM" | "STZGM") {
        return Some((None, Some("memory-tag-store")));
    }
    const SVE_STORES: &[&str] = &[
        "ST1B", "ST1H", "ST1W", "ST1D", "ST1Q", "ST2B", "ST2H", "ST2W", "ST2D", "ST3B", "ST3H",
        "ST3W", "ST3D", "ST4B", "ST4H", "ST4W", "ST4D", "STNT1B", "STNT1H", "STNT1W", "STNT1D",
    ];
    SVE_STORES
        .iter()
        .any(|name| mnem == *name)
        .then_some((None, Some("scalable-vector-store")))
}

/// Fixed data bytes written through an explicit memory operand. SIMD
/// structure stores carry their whole/lane width in each operand's vector
/// arrangement, while atomics name result registers that must not be counted
/// as additional stores.
fn fixed_memory_write_bytes(cs: &Capstone, mnem: &str, ops: &[Arm64Operand]) -> Option<usize> {
    let mem_pos = ops
        .iter()
        .position(|op| matches!(op.op_type, Arm64OperandType::Mem(_)))?;
    let regs: Vec<&Arm64Operand> = ops[..mem_pos]
        .iter()
        .filter(|op| matches!(op.op_type, Arm64OperandType::Reg(_)))
        .collect();

    if mnem.starts_with("ST") {
        let has_status_dest = ["STXR", "STLXR", "STXP", "STLXP"]
            .iter()
            .any(|prefix| mnem.starts_with(prefix));
        let values = &regs[usize::from(has_status_dest).min(regs.len())..];
        return values.iter().try_fold(0usize, |total, op| {
            store_operand_bytes(cs, mnem, op).map(|width| total.saturating_add(width))
        });
    }
    if mnem.starts_with("CASP") {
        let width = store_operand_bytes(cs, mnem, regs.last()?)?;
        return Some(width.saturating_mul(2));
    }
    if mnem.starts_with("CAS") || mnem.starts_with("SWP") {
        return store_operand_bytes(cs, mnem, regs.last()?);
    }
    const LSE_RMW: &[&str] = &[
        "LDADD", "LDCLR", "LDEOR", "LDSET", "LDSMAX", "LDSMIN", "LDUMAX", "LDUMIN",
    ];
    if LSE_RMW.iter().any(|prefix| mnem.starts_with(prefix)) {
        return store_operand_bytes(cs, mnem, regs.last()?);
    }
    None
}

#[cfg(test)]
mod tests {
    use super::{access_size, fixed_memory_write_bytes, special_memory_write};
    use capstone::prelude::*;

    fn decoded_store_width(bytes: &[u8]) -> usize {
        let cs = Capstone::new()
            .arm64()
            .mode(arch::arm64::ArchMode::Arm)
            .detail(true)
            .build()
            .unwrap();
        let insns = cs.disasm_all(bytes, 0).unwrap();
        let insn = insns.iter().next().unwrap();
        let detail = cs.insn_detail(insn).unwrap();
        let arch_detail = detail.arch_detail();
        let a64 = arch_detail.arm64().unwrap();
        let ops: Vec<_> = a64.operands().collect();
        fixed_memory_write_bytes(&cs, &insn.mnemonic().unwrap().to_ascii_uppercase(), &ops).unwrap()
    }

    #[test]
    fn store_and_atomic_write_widths_follow_isa_shapes() {
        assert_eq!(access_size("STR", Some("Q0")), 16);
        assert_eq!(access_size("LDADDB", Some("W0")), 1);
        assert_eq!(access_size("CASALB", Some("W0")), 1);
        assert_eq!(decoded_store_width(&[0x00, 0x70, 0x00, 0x4c]), 16);
        assert_eq!(decoded_store_width(&[0x00, 0x0c, 0x00, 0x0d]), 1);
        assert_eq!(decoded_store_width(&[0x00, 0x80, 0x00, 0x4c]), 32);
        assert_eq!(decoded_store_width(&[0x00, 0x04, 0x00, 0xad]), 32);
        assert_eq!(special_memory_write("ST64B"), Some((Some(64), None)));
        assert_eq!(
            special_memory_write("ST1B"),
            Some((None, Some("scalable-vector-store")))
        );
    }
}
