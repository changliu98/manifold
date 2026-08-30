use crate::decompile::disassembly::branch;
use crate::decompile::disassembly::operand::*;
use crate::decompile::elevator::DecompileDB;
use crate::mreg::Mreg;
use capstone::arch::x86::X86OperandType;
use capstone::prelude::*;
use object::{Object, ObjectSection, SectionFlags, SectionKind};

const SHF_EXECINSTR: u64 = 0x4;

/// EVEX encodes its opmask register in the low three bits of P2.  Capstone's
/// semantic operand list does not expose the mask register, so retain one
/// explicit fact before lowering can mistake a masked EVEX operation for an
/// ordinary VEX three-operand instruction.
fn evex_has_opmask(mnemonic: &str, bytes: &[u8]) -> bool {
    if !mnemonic.starts_with('V') {
        return false;
    }
    let prefix_len = bytes
        .iter()
        .take_while(|byte| {
            matches!(
                **byte,
                0x26 | 0x2e | 0x36 | 0x3e | 0x64 | 0x65 | 0x66 | 0x67 | 0xf0 | 0xf2 | 0xf3
            )
        })
        .count();
    bytes.get(prefix_len) == Some(&0x62)
        && bytes.get(prefix_len + 3).is_some_and(|p2| p2 & 0x07 != 0)
}

// Canonical spelling of the stack/frame registers for the stack FACT relations (stack_def, stack_use, adjusts_stack, stack_base_move): the 32-bit E-names fold onto the 64-bit R-names, since the two spell one register and every consumer (stack_pass, canary_vla_pass, rtl_pass) tests "RSP"/"RBP".
// Deliberately NOT applied to op_register/op_indirect: asm_pass reads operand width from the E-vs-R spelling there (ireg_hold_type: EAX is Tint, RAX is Tany64), so folding those would mis-size 32-bit operands.
fn canonical_stack_reg(name: &str) -> Option<&'static str> {
    match name {
        "RSP" | "ESP" => Some("RSP"),
        "RBP" | "EBP" => Some("RBP"),
        _ => None,
    }
}

// Check whether an operand type is the stack pointer, in either width's spelling.
fn is_rsp_reg(cs: &Capstone, op_type: &X86OperandType) -> bool {
    matches!(op_type, X86OperandType::Reg(reg_id) if {
        let name = cs.reg_name(*reg_id).unwrap_or_default().to_ascii_uppercase();
        name == "RSP" || name == "ESP"
    })
}

/// Capstone 5 leaves the per-operand access field empty for some TEST
/// encodings (notably `test r/m32, r32`).  TEST is architecturally read-only
/// for every explicit operand, so recover that exact fact without guessing
/// access roles for any other instruction.
fn explicit_operand_is_read(mnemonic: &str, capstone_readable: bool) -> bool {
    capstone_readable || mnemonic == "TEST"
}

fn explicit_stack_pointer_delta(
    mnemonic: &str,
    first_operand_size: usize,
    first_operand_is_sp: bool,
) -> Option<i64> {
    match mnemonic {
        "PUSH" if first_operand_size > 0 => i64::try_from(first_operand_size)
            .ok()
            .and_then(|width| width.checked_neg()),
        "POP" if first_operand_size > 0 && !first_operand_is_sp => {
            i64::try_from(first_operand_size).ok()
        }
        "PUSHF" => Some(-2),
        "PUSHFD" => Some(-4),
        "PUSHFQ" => Some(-8),
        "POPF" => Some(2),
        "POPFD" => Some(4),
        "POPFQ" => Some(8),
        _ => None,
    }
}

// Capstone exposes explicit writable memory operands directly. A few string
// operations encode their data-memory destination implicitly; count one
// element's fixed width when no operands were materialized. REP changes the
// dynamic element count, which is not statically knowable, but never the width
// of each architectural write.
fn implicit_data_memory_write_width(mnemonic: &str, num_operands: usize) -> usize {
    match mnemonic {
        // MASKMOV's destination is implicit [RDI], but its two explicit
        // register operands mean an operand-count guard would never see it.
        "MASKMOVQ" => 8,
        "MASKMOVDQU" => 16,
        // Capstone 5 labels STMXCSR's explicit memory operand READ even though
        // the ISA writes the 32-bit control/status register to it.
        "STMXCSR" => 4,
        // Current Capstone exposes string destinations as writable memory
        // operands. Keep a conservative fallback for versions that omit all
        // implicit operands, while not confusing the SSE MOVSD spelling.
        "STOSB" | "MOVSB" | "INSB" => 1,
        "STOSW" | "MOVSW" | "INSW" => 2,
        "STOSD" | "MOVSD" | "INSD" if num_operands == 0 => 4,
        "STOSQ" | "MOVSQ" if num_operands == 0 => 8,
        _ => 0,
    }
}

fn special_memory_write(mnemonic: &str, prefix: &str) -> (Option<usize>, Option<&'static str>) {
    if mnemonic.starts_with("XSAVE") {
        return (None, Some("dynamic-xsave-area"));
    }
    if matches!(mnemonic, "FXSAVE" | "FXSAVE64") {
        return (Some(512), None);
    }
    if matches!(prefix, "REP" | "REPNE")
        && matches!(
            mnemonic,
            "STOSB"
                | "STOSW"
                | "STOSD"
                | "STOSQ"
                | "MOVSB"
                | "MOVSW"
                | "MOVSD"
                | "MOVSQ"
                | "INSB"
                | "INSW"
                | "INSD"
        )
    {
        return (None, Some("dynamic-repeat-count"));
    }
    (None, None)
}

pub fn is_executable_section(section: &object::Section) -> bool {
    match section.flags() {
        SectionFlags::Elf { sh_flags } => sh_flags & SHF_EXECINSTR != 0,
        _ => section.kind() == SectionKind::Text,
    }
}

// Decoded instruction metadata retained for block detection and CFG construction.
#[derive(Debug, Clone)]
pub struct DecodedInsn {
    pub address: u64,
    pub size: usize,
    pub mnemonic: &'static str,
    pub op_str: &'static str,
    /// Where this instruction's new PC comes from, when it writes the PC as a register destination; only A32 ever sets it to anything but NotWritten.
    pub pc_source: crate::decompile::disassembly::branch::PcSource,
}

// Disassemble executable sections into the instruction/operand/register relations, dispatching on target arch.
pub fn disassemble_sections(db: &mut DecompileDB, obj: &object::File) -> Vec<DecodedInsn> {
    match db.abi().arch {
        crate::abi::Arch::Aarch64 => {
            crate::decompile::disassembly::aarch64::disassemble_sections(db, obj)
        }
        crate::abi::Arch::Arm32 => {
            crate::decompile::disassembly::arm32::disassemble_sections(db, obj)
        }
        _ => disassemble_x86_sections(db, obj),
    }
}

fn disassemble_x86_sections(db: &mut DecompileDB, obj: &object::File) -> Vec<DecodedInsn> {
    let cs = {
        let mode = if db.abi().is_64bit() {
            arch::x86::ArchMode::Mode64
        } else {
            arch::x86::ArchMode::Mode32
        };
        Capstone::new()
            .x86()
            .mode(mode)
            .syntax(arch::x86::ArchSyntax::Intel)
            .detail(true)
            .build()
            .expect("Failed to create capstone engine")
    };

    // Bytes one PUSH/POP moves SP by.
    let stack_slot = db.abi().pointer_size as i64;

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
    // Exact writable stack operands retain their byte width and operand role.
    // `stack_def` deliberately expands wide accesses into coarse cells for the
    // legacy def-use analysis, so it cannot answer byte-overlap questions on
    // its own without accidentally joining a read operand's width.
    let mut decoded_stack_write_bytes: Vec<(u64, &'static str, i64, usize)> = Vec::new();
    let mut decoded_stack_read_bytes: Vec<(u64, &'static str, i64, usize)> = Vec::new();
    let mut decoded_stack_write_unresolved: Vec<(u64, &'static str)> = Vec::new();
    let mut decoded_stack_pointer_delta: Vec<(u64, i64)> = Vec::new();
    let mut reg_defs: Vec<(u64, Mreg)> = Vec::new();
    let mut reg_uses: Vec<(u64, Mreg)> = Vec::new();
    let mut adjusts_stack: Vec<(u64, &'static str, i64)> = Vec::new();
    let mut stack_base_moves: Vec<(u64, &'static str, &'static str)> = Vec::new();
    let mut decoded_memory_writes: Vec<(u64, usize)> = Vec::new();
    let mut decoded_memory_write_unknown: Vec<(u64, &'static str)> = Vec::new();
    let mut avx_masked_sites: Vec<(u64,)> = Vec::new();

    for section in obj.sections() {
        if !is_executable_section(&section) {
            continue;
        }
        let data = match section.data() {
            Ok(d) => d,
            Err(_) => continue,
        };
        let base_addr = section.address();

        let insns = cs.disasm_all(data, base_addr).unwrap_or_else(|e| {
            panic!("Disassembly failed at section {:?}: {}", section.name(), e)
        });

        for insn in insns.as_ref() {
            let addr = insn.address();
            let size = insn.len();

            // Strip BND/NOTRACK prefixes (treated as the underlying instruction)
            let mnem_str = insn.mnemonic().unwrap_or("").to_ascii_uppercase();
            let mnem_str = if let Some(rest) = mnem_str.strip_prefix("BND ") {
                rest.to_string()
            } else if let Some(rest) = mnem_str.strip_prefix("NOTRACK ") {
                rest.to_string()
            } else {
                mnem_str
            };
            let mnemonic: &'static str = Box::leak(mnem_str.into_boxed_str());
            if evex_has_opmask(mnemonic, insn.bytes()) {
                avx_masked_sites.push((addr,));
            }

            let prefix: &'static str = {
                let detail = cs.insn_detail(insn).ok();
                let p = detail.as_ref().and_then(|d| {
                    let arch = d.arch_detail();
                    let x86 = arch.x86().unwrap();
                    let pfx = x86.prefix();
                    if pfx[0] != 0 {
                        match pfx[0] as u32 {
                            0xF3 => Some("REP"),
                            0xF2 => Some("REPNE"),
                            0xF0 => Some("LOCK"),
                            _ => None,
                        }
                    } else {
                        None
                    }
                });
                p.unwrap_or("")
            };

            let detail = cs
                .insn_detail(insn)
                .expect("insn_detail failed; was detail mode enabled?");
            let arch_detail = detail.arch_detail();
            let x86_detail = arch_detail.x86().expect("Not x86");
            let ops = x86_detail.operands();

            let mut op_ids: [&'static str; 4] = [NO_OP; 4];
            let num_operands = ops.len();
            let mut first_operand_size = 0_usize;
            let mut first_operand_is_sp = false;
            let mut explicit_memory_write_bytes = 0usize;
            let mut stack_memory_operands: Vec<(&'static str, i64, usize, bool, bool, bool)> =
                Vec::new();
            let stack_write_fact_start = decoded_stack_write_bytes.len();

            let is_nop = mnemonic == "NOP" || mnemonic == "VZEROUPPER" || mnemonic == "VZEROALL";

            let is_xor_self = if mnemonic == "XOR" && num_operands == 2 {
                let ops_vec: Vec<_> = x86_detail.operands().collect();
                match (&ops_vec[0].op_type, &ops_vec[1].op_type) {
                    (X86OperandType::Reg(r1), X86OperandType::Reg(r2)) => r1 == r2,
                    _ => false,
                }
            } else {
                false
            };

            for (i, op) in ops.enumerate() {
                if i >= 4 {
                    break;
                }
                if i == 0 {
                    first_operand_size = op.size as usize;
                    first_operand_is_sp = is_rsp_reg(&cs, &op.op_type);
                }
                match op.op_type {
                    X86OperandType::Reg(reg_id) => {
                        let id = alloc_op_id();
                        let name = capstone_reg_name(&cs, reg_id);
                        op_registers.push((id, name));
                        op_ids[i] = id;

                        let mreg = Mreg::x86(name);
                        if mreg != Mreg::Unknown && !is_nop {
                            if op.access.map_or(false, |a| a.is_writable()) {
                                reg_defs.push((addr, mreg));
                            }
                            if explicit_operand_is_read(
                                mnemonic,
                                op.access.map_or(false, |a| a.is_readable()),
                            ) && !is_xor_self
                            {
                                reg_uses.push((addr, mreg));
                            }
                        }
                    }
                    X86OperandType::Imm(val) => {
                        let id = alloc_op_id();
                        op_immediates.push((id, val, 0));
                        op_ids[i] = id;
                    }
                    X86OperandType::Mem(mem) => {
                        let id = alloc_op_id();
                        let seg = if mem.segment().0 != 0 {
                            capstone_reg_name(&cs, mem.segment())
                        } else {
                            "NONE"
                        };
                        let base = if mem.base().0 != 0 {
                            capstone_reg_name(&cs, mem.base())
                        } else {
                            "NONE"
                        };
                        let index = if mem.index().0 != 0 {
                            capstone_reg_name(&cs, mem.index())
                        } else {
                            "NONE"
                        };
                        let scale = mem.scale() as i64;
                        let disp = mem.disp();
                        // Capstone operand byte width; authoritative access size (B5).
                        op_indirects.push((id, seg, base, index, scale, disp, op.size as usize));
                        op_ids[i] = id;
                        if op.access.map_or(false, |a| a.is_writable()) {
                            explicit_memory_write_bytes =
                                explicit_memory_write_bytes.saturating_add(op.size as usize);
                        }

                        // Memory operand base/index registers count as reg_use
                        if !is_nop {
                            if base != "NONE" && base != "RIP" {
                                let mreg = Mreg::x86(base);
                                if mreg != Mreg::Unknown {
                                    reg_uses.push((addr, mreg));
                                }
                            }
                            if index != "NONE" {
                                let mreg = Mreg::x86(index);
                                if mreg != Mreg::Unknown {
                                    reg_uses.push((addr, mreg));
                                }
                            }
                        }

                        // Stack def/use classification for frame/stack-relative memory accesses, in either width's spelling.
                        if let Some(canon_base) = canonical_stack_reg(base) {
                            if mnemonic != "LEA" {
                                let is_write = op.access.map_or(false, |a| a.is_writable());
                                let is_read = explicit_operand_is_read(
                                    mnemonic,
                                    op.access.map_or(false, |a| a.is_readable()),
                                );
                                let indexed = index != "NONE" && !index.is_empty();
                                stack_memory_operands.push((
                                    base,
                                    disp,
                                    op.size as usize,
                                    is_write,
                                    indexed,
                                    seg == "NONE",
                                ));
                                if indexed {
                                    if is_write {
                                        decoded_stack_write_unresolved.push((addr, base));
                                    }
                                    continue;
                                }
                                // An SSE/AVX access is wider than the 8-byte cell the frame is
                                // tracked in, so record every cell it spans; recording only the
                                // first left the upper halves of every XMM stack move with no
                                // def and no use, which both loses the data and hides the cells
                                // from frame-object recovery.
                                let cells = ((op.size as i64 + 7) / 8).max(1);
                                for cell in 0..cells {
                                    let cell_disp = disp + cell * 8;
                                    // ddisasm: any store to stack is a def (not just MOV)
                                    if is_write {
                                        stack_defs.push((addr, canon_base, cell_disp));
                                    }
                                    if is_read {
                                        stack_uses.push((addr, canon_base, cell_disp));
                                    }
                                }
                                if seg != "NONE" {
                                    if is_write {
                                        decoded_stack_write_unresolved.push((addr, base));
                                    }
                                    continue;
                                }
                                // POP r/m computes an RSP-based destination
                                // after incrementing SP. Its raw displacement
                                // therefore does not name the in-state frame
                                // coordinate used by ordinary memory operands.
                                // Keep it as an opaque frame write until that
                                // post-increment addressing rule is modeled.
                                if is_write && mnemonic == "POP" && canon_base == "RSP" {
                                    decoded_stack_write_unresolved.push((addr, base));
                                } else if is_write {
                                    decoded_stack_write_bytes.push((
                                        addr,
                                        base,
                                        disp,
                                        op.size as usize,
                                    ));
                                }
                                if is_read {
                                    decoded_stack_read_bytes.push((
                                        addr,
                                        base,
                                        disp,
                                        op.size as usize,
                                    ));
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }

            let explicit_stack_delta =
                explicit_stack_pointer_delta(mnemonic, first_operand_size, first_operand_is_sp);
            if let Some(delta) = explicit_stack_delta {
                decoded_stack_pointer_delta.push((addr, delta));
            }

            if explicit_memory_write_bytes == 0 {
                explicit_memory_write_bytes =
                    implicit_data_memory_write_width(mnemonic, num_operands);
            }
            let (fixed_override, unknown_reason) = special_memory_write(mnemonic, prefix);
            if fixed_override.is_some() || unknown_reason.is_some() {
                // Replace any ordinary Capstone-width fact emitted above with
                // the architectural override. Keeping both widths would make
                // one special store look like two distinct memory roles.
                decoded_stack_write_bytes.truncate(stack_write_fact_start);
            }
            if unknown_reason.is_some() && fixed_override.is_none() {
                // A dynamic/scalable obligation must not also enter the fixed
                // denominator as Capstone's address-word size or one REP
                // element. Its total architectural width is not that value.
                explicit_memory_write_bytes = 0;
            } else if let Some(bytes) = fixed_override {
                explicit_memory_write_bytes = bytes;
            }
            if let Some(reason) = unknown_reason {
                decoded_memory_write_unknown.push((addr, reason));
            }
            // Some architectural stores are missing or mislabelled in
            // Capstone's per-operand access flags. Retain their exact stack
            // operand identity here too: fixed-size overrides carry that
            // width, while dynamic writes carry zero and become an explicit
            // downstream veto. Ordinary read-modify-write operands have
            // already entered through `is_write` above.
            if unknown_reason.is_some() {
                for (base, disp, _, _, indexed, exact_segment) in &stack_memory_operands {
                    if *indexed || !*exact_segment {
                        decoded_stack_write_unresolved.push((addr, *base));
                    } else {
                        decoded_stack_write_bytes.push((addr, *base, *disp, 0));
                    }
                }
            } else if let Some(bytes) = fixed_override {
                for (base, disp, _, _, indexed, exact_segment) in &stack_memory_operands {
                    if *indexed || !*exact_segment {
                        decoded_stack_write_unresolved.push((addr, *base));
                    } else {
                        decoded_stack_write_bytes.push((addr, *base, *disp, bytes));
                    }
                }
            } else if explicit_memory_write_bytes > 0
                && !stack_memory_operands
                    .iter()
                    .any(|(_, _, _, write, _, _)| *write)
            {
                for (base, disp, _, _, indexed, exact_segment) in &stack_memory_operands {
                    if *indexed || !*exact_segment {
                        decoded_stack_write_unresolved.push((addr, *base));
                    } else {
                        decoded_stack_write_bytes.push((
                            addr,
                            *base,
                            *disp,
                            explicit_memory_write_bytes,
                        ));
                    }
                }
            }
            // Source-level data-memory effects only. CALL/PUSH control-stack
            // writes are intentionally absent, while a 16-byte vector store
            // contributes all 16 bytes at one node.
            if explicit_memory_write_bytes > 0 {
                decoded_memory_writes.push((addr, explicit_memory_write_bytes));
            }

            // Implicit stack accesses for PUSH/POP
            match mnemonic {
                "PUSH" => {
                    stack_defs.push((addr, "RSP", 0));
                }
                "POP" => {
                    stack_uses.push((addr, "RSP", 0));
                }
                _ => {}
            }

            // Stack pointer modification tracking
            match mnemonic {
                // PUSH/POP move SP by one pointer: 8 on x86-64, 4 on i386.
                "PUSH" => {
                    adjusts_stack.push((addr, "RSP", -stack_slot));
                }
                "POP" => {
                    adjusts_stack.push((addr, "RSP", stack_slot));
                }
                "SUB" => {
                    if num_operands >= 2 {
                        let ops_vec: Vec<_> = x86_detail.operands().collect();
                        if let (Some(dst_op), Some(src_op)) = (ops_vec.get(0), ops_vec.get(1)) {
                            if is_rsp_reg(&cs, &dst_op.op_type) {
                                if let X86OperandType::Imm(imm_val) = src_op.op_type {
                                    adjusts_stack.push((addr, "RSP", -imm_val));
                                }
                            }
                        }
                    }
                }
                "ADD" => {
                    if num_operands >= 2 {
                        let ops_vec: Vec<_> = x86_detail.operands().collect();
                        if let (Some(dst_op), Some(src_op)) = (ops_vec.get(0), ops_vec.get(1)) {
                            if is_rsp_reg(&cs, &dst_op.op_type) {
                                if let X86OperandType::Imm(imm_val) = src_op.op_type {
                                    adjusts_stack.push((addr, "RSP", imm_val));
                                }
                            }
                        }
                    }
                }
                "LEA" => {
                    if num_operands >= 2 {
                        let ops_vec: Vec<_> = x86_detail.operands().collect();
                        if let (Some(dst_op), Some(src_op)) = (ops_vec.get(0), ops_vec.get(1)) {
                            if is_rsp_reg(&cs, &dst_op.op_type) {
                                if let X86OperandType::Mem(mem) = src_op.op_type {
                                    let base_name = if mem.base().0 != 0 {
                                        cs.reg_name(mem.base())
                                            .unwrap_or_default()
                                            .to_ascii_uppercase()
                                    } else {
                                        String::new()
                                    };
                                    let index_id = mem.index().0;
                                    if canonical_stack_reg(&base_name) == Some("RSP")
                                        && index_id == 0
                                    {
                                        adjusts_stack.push((addr, "RSP", mem.disp()));
                                    }
                                }
                            }
                        }
                    }
                }
                _ => {}
            }

            // Stack base register moves (mov rbp, rsp / mov rsp, rbp; and their i386 ebp/esp spellings).
            if mnemonic == "MOV" && num_operands >= 2 {
                let ops_vec: Vec<_> = x86_detail.operands().collect();
                if let (Some(dst_op), Some(src_op)) = (ops_vec.get(0), ops_vec.get(1)) {
                    let stack_reg_of = |op_type: &X86OperandType| match op_type {
                        X86OperandType::Reg(reg_id) => canonical_stack_reg(
                            &cs.reg_name(*reg_id)
                                .unwrap_or_default()
                                .to_ascii_uppercase(),
                        ),
                        _ => None,
                    };
                    if let (Some(dst), Some(src)) =
                        (stack_reg_of(&dst_op.op_type), stack_reg_of(&src_op.op_type))
                    {
                        if dst != src {
                            stack_base_moves.push((addr, src, dst));
                        }
                    }
                }
            }

            // Implicit register def/use from capstone's regs_write/regs_read
            if !is_nop {
                for &reg_id in detail.regs_write() {
                    let name = cs.reg_name(reg_id).unwrap_or_default().to_ascii_uppercase();
                    let mreg = Mreg::x86(name.as_str());
                    if mreg != Mreg::Unknown {
                        reg_defs.push((addr, mreg));
                    }
                }
                for &reg_id in detail.regs_read() {
                    let name = cs.reg_name(reg_id).unwrap_or_default().to_ascii_uppercase();
                    let mreg = Mreg::x86(name.as_str());
                    if mreg != Mreg::Unknown {
                        reg_uses.push((addr, mreg));
                    }
                }
            }

            // Swap op1/op2 to match ddisasm's operand ordering convention
            if num_operands >= 2 {
                op_ids.swap(0, 1);
            }

            instructions.push((
                addr, size, prefix, mnemonic, op_ids[0], op_ids[1], op_ids[2], op_ids[3], 0, 0,
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

    // Populate DB relations
    db.rel_set(
        "unrefinedinstruction",
        instructions.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );

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
        "stack_def",
        stack_defs.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "stack_use",
        stack_uses.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "decoded_stack_write_bytes",
        decoded_stack_write_bytes
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "decoded_stack_read_bytes",
        decoded_stack_read_bytes
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "decoded_stack_write_unresolved",
        decoded_stack_write_unresolved
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "decoded_stack_pointer_delta",
        decoded_stack_pointer_delta
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );

    // Preserve the decoder's immutable definition facts separately from
    // `reg_def`, which later ASM rules augment with synthetic architectural
    // effects (notably x87 FP0).  Point-keyed proofs that feed Mach emission
    // must not recursively depend on those derived definitions.
    db.rel_set(
        "decoded_reg_def",
        reg_defs.iter().copied().collect::<ascent::boxcar::Vec<_>>(),
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
    db.rel_set(
        "avx_masked_site",
        avx_masked_sites
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
    );

    decoded
}

#[cfg(test)]
mod tests {
    use super::{
        evex_has_opmask, explicit_operand_is_read, explicit_stack_pointer_delta,
        implicit_data_memory_write_width, special_memory_write,
    };
    use capstone::prelude::*;

    fn decoded_push_delta(bytes: &[u8]) -> i64 {
        let cs = Capstone::new()
            .x86()
            .mode(arch::x86::ArchMode::Mode64)
            .syntax(arch::x86::ArchSyntax::Intel)
            .detail(true)
            .build()
            .expect("x86-64 Capstone");
        let insns = cs.disasm_all(bytes, 0x1000).expect("one PUSH");
        let insn = insns.iter().next().expect("decoded PUSH");
        let detail = cs.insn_detail(insn).expect("PUSH detail");
        let arch_detail = detail.arch_detail();
        let x86_detail = arch_detail.x86().expect("x86 detail");
        let operand_size = x86_detail.operands().next().expect("PUSH operand").size as usize;
        explicit_stack_pointer_delta("PUSH", operand_size, false).expect("known PUSH delta")
    }

    #[test]
    fn evex_opmask_detection_handles_prefixes_and_k0() {
        assert!(evex_has_opmask("VPADDD", &[0x62, 0xf1, 0x75, 0x09]));
        assert!(evex_has_opmask("VPADDD", &[0x67, 0x62, 0xf1, 0x75, 0x81]));
        assert!(!evex_has_opmask("VPADDD", &[0x62, 0xf1, 0x75, 0x08]));
        assert!(!evex_has_opmask("BOUND", &[0x62, 0x01, 0x02, 0x07]));
        assert!(!evex_has_opmask("VPADDD", &[0xc5, 0xf1, 0xfe, 0x00]));
    }

    #[test]
    fn implicit_string_stores_keep_their_element_width() {
        assert_eq!(implicit_data_memory_write_width("STOSB", 0), 1);
        assert_eq!(implicit_data_memory_write_width("MOVSQ", 0), 8);
        assert_eq!(implicit_data_memory_write_width("MASKMOVDQU", 2), 16);
        assert_eq!(implicit_data_memory_write_width("STMXCSR", 1), 4);
        // Explicit MOVSD operands are handled from Capstone access metadata;
        // the string fallback must not misclassify the SSE spelling.
        assert_eq!(implicit_data_memory_write_width("MOVSD", 2), 0);
        assert_eq!(implicit_data_memory_write_width("CALL", 0), 0);
        assert_eq!(special_memory_write("FXSAVE64", ""), (Some(512), None));
        assert_eq!(
            special_memory_write("XSAVE", ""),
            (None, Some("dynamic-xsave-area"))
        );
        assert_eq!(
            special_memory_write("MOVSB", "REP"),
            (None, Some("dynamic-repeat-count"))
        );
    }

    #[test]
    fn push_delta_uses_architectural_operand_width_not_immediate_encoding_width() {
        assert_eq!(decoded_push_delta(&[0x6a, 0x01]), -8);
        assert_eq!(decoded_push_delta(&[0x66, 0x6a, 0x01]), -2);
    }

    #[test]
    fn scaled_memory_test_recovers_reads_when_capstone_omits_access_metadata() {
        let cs = Capstone::new()
            .x86()
            .mode(arch::x86::ArchMode::Mode64)
            .syntax(arch::x86::ArchSyntax::Intel)
            .detail(true)
            .build()
            .expect("x86-64 Capstone");
        let insns = cs
            .disasm_all(&[0x85, 0x34, 0xb8], 0x401135)
            .expect("TEST instruction");
        let insn = insns.iter().next().expect("one TEST");
        assert_eq!(insn.mnemonic(), Some("test"));
        let detail = cs.insn_detail(insn).expect("TEST detail");
        let arch = detail.arch_detail();
        let operands: Vec<_> = arch.x86().expect("x86 detail").operands().collect();
        assert_eq!(operands.len(), 2);
        assert!(operands.iter().all(|operand| operand.access.is_none()));
        assert!(operands.iter().all(|operand| explicit_operand_is_read(
            "TEST",
            operand.access.map_or(false, |access| access.is_readable()),
        )));
        assert!(!explicit_operand_is_read("MOV", false));
    }
}
