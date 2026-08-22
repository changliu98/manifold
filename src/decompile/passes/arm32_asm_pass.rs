// A32 to Mach: the ARM32 counterpart of asm_pass, mutually exclusive with it and with aarch64_asm_pass at runtime, decomposing A32 into the SHARED Operation/Addressing/Condition alphabet rather than mirroring a CompCert arm backend.

use crate::abi::Arch;
use crate::arm32::mach::A32Mreg;
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::mreg::Mreg;
use crate::x86::op::{Addressing, Comparison, Condition, Operation};
use crate::x86::types::*;
use crate::{declare_io_from, run_pass};
use ascent::aggregators;
use ascent::ascent_par;
use either::Either;
use std::sync::Arc;

// A register operand's Mreg; capstone's alias spellings (FP/IP/R13/R14/R15) are already normalized by A32Mreg::from.
fn mreg_of(name: &str) -> Mreg {
    Mreg::a32(A32Mreg::from(name))
}

fn is_float_reg(name: &str) -> bool {
    A32Mreg::from(name).is_vec()
}

// Comparison and signedness from a condition in the shared shorthand cfg.rs::branch_condition maps A32's condition codes onto. MI/PL/VS/VC are deliberately absent: the shared alphabet has no Comparison for "negative" or "overflowed", and forcing them onto a signed comparison would be wrong.
fn cond_parts(cond: &str) -> Option<(Comparison, bool)> {
    Some(match cond {
        "e" => (Comparison::Ceq, true),
        "ne" => (Comparison::Cne, true),
        "l" => (Comparison::Clt, true),
        "le" => (Comparison::Cle, true),
        "g" => (Comparison::Cgt, true),
        "ge" => (Comparison::Cge, true),
        "b" => (Comparison::Clt, false),
        "be" => (Comparison::Cle, false),
        "a" => (Comparison::Cgt, false),
        "ae" => (Comparison::Cge, false),
        _ => return None,
    })
}

// The shorthand condition that holds exactly when `cond` does not.
fn negate_cond(cond: &str) -> Option<&'static str> {
    Some(match cond {
        "e" => "ne",
        "ne" => "e",
        "l" => "ge",
        "ge" => "l",
        "le" => "g",
        "g" => "le",
        "b" => "ae",
        "ae" => "b",
        "be" => "a",
        "a" => "be",
        _ => return None,
    })
}

// A32 general registers are 32 bits wide, so every comparison lands in the int half of the shared alphabet.
fn cond_reg(cond: &str) -> Option<Condition> {
    let (cmp, signed) = cond_parts(cond)?;
    Some(if signed {
        Condition::Ccomp(cmp)
    } else {
        Condition::Ccompu(cmp)
    })
}

fn cond_imm(cond: &str, imm: i64) -> Option<Condition> {
    let (cmp, signed) = cond_parts(cond)?;
    Some(if signed {
        Condition::Ccompimm(cmp, imm)
    } else {
        Condition::Ccompuimm(cmp, imm)
    })
}

// Three-operand register ALU mnemonic -> shared Operation. All 32-bit: A32 has no 64-bit general register.
fn alu_rrr_op(mnem: &str) -> Option<Operation> {
    Some(match mnem {
        "ADD" | "ADDS" => Operation::Oadd,
        "SUB" | "SUBS" => Operation::Osub,
        "MUL" | "MULS" => Operation::Omul,
        "SDIV" => Operation::Odiv,
        "UDIV" => Operation::Odivu,
        "AND" | "ANDS" => Operation::Oand,
        "ORR" | "ORRS" => Operation::Oor,
        "EOR" | "EORS" => Operation::Oxor,
        "LSL" | "LSLS" => Operation::Oshl,
        "LSR" | "LSRS" => Operation::Oshru,
        "ASR" | "ASRS" => Operation::Oshr,
        _ => return None,
    })
}

// Register-immediate ALU mnemonic -> shared Operation; SUB has no immediate form there, so it folds to Oaddimm with a negated constant.
fn alu_rri_op(mnem: &str, imm: i64) -> Option<Operation> {
    Some(match mnem {
        "ADD" | "ADDS" => Operation::Oaddimm(imm),
        "SUB" | "SUBS" => Operation::Oaddimm(-imm),
        "AND" | "ANDS" => Operation::Oandimm(imm),
        "ORR" | "ORRS" => Operation::Oorimm(imm),
        "EOR" | "EORS" => Operation::Oxorimm(imm),
        "LSL" | "LSLS" => Operation::Oshlimm(imm),
        "LSR" | "LSRS" => Operation::Oshruimm(imm),
        "ASR" | "ASRS" => Operation::Oshrimm(imm),
        "MUL" | "MULS" => Operation::Omulimm(imm),
        // BIC Rd, Rn, #imm clears the immediate's bits, which is AND with its complement.
        "BIC" | "BICS" => Operation::Oandimm(!imm),
        _ => return None,
    })
}

// Two-operand register unary mnemonic -> shared Operation.
fn alu_rr_op(mnem: &str) -> Option<Operation> {
    Some(match mnem {
        "MOV" | "MOVS" => Operation::Omove,
        "MVN" | "MVNS" => Operation::Onot,
        "SXTB" => Operation::Ocast8signed,
        "SXTH" => Operation::Ocast16signed,
        "UXTB" => Operation::Ocast8unsigned,
        "UXTH" => Operation::Ocast16unsigned,
        "VMOV" => Operation::Omove,
        _ => return None,
    })
}

// Access width and signedness -> MemoryChunk, from the mnemonic stem; A32 encodes the width in the opcode rather than in the register name.
fn chunk_of(mnem: &str, reg: &str) -> Option<MemoryChunk> {
    Some(match mnem {
        "LDRB" | "STRB" | "LDRBT" | "STRBT" => MemoryChunk::MInt8Unsigned,
        "LDRSB" => MemoryChunk::MInt8Signed,
        "LDRH" | "STRH" | "LDRHT" | "STRHT" => MemoryChunk::MInt16Unsigned,
        "LDRSH" => MemoryChunk::MInt16Signed,
        "LDR" | "STR" | "LDRT" | "STRT" => MemoryChunk::MInt32,
        "VLDR" | "VSTR" => {
            if A32Mreg::from(reg).is_double() {
                MemoryChunk::MFloat64
            } else {
                MemoryChunk::MFloat32
            }
        }
        _ => return None,
    })
}

fn is_load_mnem(m: &str) -> bool {
    matches!(
        m,
        "LDR" | "LDRB" | "LDRSB" | "LDRH" | "LDRSH" | "LDRT" | "LDRBT" | "LDRHT" | "VLDR"
    )
}

fn is_store_mnem(m: &str) -> bool {
    matches!(
        m,
        "STR" | "STRB" | "STRH" | "STRT" | "STRBT" | "STRHT" | "VSTR"
    )
}

// Addressing mode for a decoded memory operand; every A32 mode lands in the SHARED Addressing set, with [SP, #i] becoming Ainstack so stack analysis sees it as it does x86.
fn addressing_of(
    base: &str,
    index: &str,
    scale: i64,
    disp: i64,
) -> Option<(Addressing, Vec<Mreg>)> {
    if base == "NONE" {
        return None;
    }
    if index == "NONE" {
        if base == "SP" {
            return Some((Addressing::Ainstack(disp), vec![]));
        }
        return Some((Addressing::Aindexed(disp), vec![mreg_of(base)]));
    }
    let args = vec![mreg_of(base), mreg_of(index)];
    if scale <= 1 {
        Some((Addressing::Aindexed2(disp), args))
    } else {
        Some((Addressing::Aindexed2scaled(scale, disp), args))
    }
}

// A register whose value is not a program value. The PC is control state, and SP is the frame anchor the stack pass owns: modelling either as an ordinary Mop destination would put frame arithmetic into the recovered expression tree, which is exactly what x86's asm_pass keeps out.
fn is_modellable(name: &str) -> bool {
    matches!(A32Mreg::from(name), r if r != A32Mreg::PC && r != A32Mreg::SP && r != A32Mreg::Unknown)
}

// A flag-setting instruction that is NOT a compare writes its result to a register and sets the flags from THAT result, so the condition a following branch tests is "destination versus zero" -- `SUBS Rn,Rn,#1` before a B.NE is the canonical counted loop, and it tests Rn-1, not Rn against 1. Thumb's 16-bit encodings set the flags this way with no S in the source at all, which is why capstone's normalized mnemonic rather than the source spelling is what this reads. Must stay in step with cfg.rs::is_comparison, which decides which flag setter a branch is paired with.
fn sets_flags_from_result(mnem: &str) -> bool {
    matches!(
        mnem,
        "SUBS"
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
    )
}

ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct Arm32AsmPassProgram;

    // ---- inputs from the disassembly layer -------------------------------------
    relation unrefinedinstruction(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize);
    relation op_register(Symbol, &'static str);
    relation op_immediate(Symbol, i64, usize);
    relation op_indirect(Symbol, &'static str, &'static str, &'static str, i64, i64, usize);
    relation code_in_block(Address, Address);
    relation code_in_refined_block(Address, Address);
    relation block_in_function(Node, Address);
    relation func_span(Symbol, Address, Address);
    relation symbol_table(Address, usize, &'static str, &'static str, &'static str, usize, &'static str, usize, &'static str);
    relation symbols(Address, Symbol, Symbol);
    relation flags_and_jump_pair(Address, Address, &'static str);
    relation adjusts_stack(Address, Symbol, i64);
    relation trim_instruction(Address);
    relation func_entry(Symbol, Address);

    // ---- A32-specific inputs the decoder publishes -----------------------------
    // One row per register moved by an LDM/STM (or its PUSH/POP alias), already resolved to its own slot.
    relation arm_multi_transfer(Address, bool, &'static str, &'static str, i64, usize);
    // An instruction whose memory offset is measured against an SP it writes back: the prologue/epilogue push and pop. That offset belongs to a different frame origin than the settled-SP references in the body, and it is the callee-save spill CompCert's Stacking emits, so it carries no program-visible memory effect -- only the stack adjustment.
    relation arm_frame_setup(Address);
    // The constant a PC-relative load reads out of a literal pool.
    relation arm_literal_value(Address, i64);
    // An instruction that reaches its target by writing R15; the flag distinguishes a restored return address from a computed one.
    relation arm_pc_transfer(Address, bool);
    // Positive classifier for computed BX/BXJ targets whose CFG-reaching
    // provenance is a stable function pointer, not indexed table arithmetic.
    relation indirect_tailcall_target(Address, Mreg);
    // An instruction whose effect the frontend does not model, kept visible rather than silently dropped.
    relation arm_unmodelled(Address);
    // A shifter attached to a register operand: A32 folds a shift into nearly every data-processing source, and reading such an operand as a plain register would silently drop the shift.
    relation arm_shifted_operand(Symbol, &'static str, i64);
    // An instruction whose first operand is both the source and the destination: Thumb's 16-bit encodings have no room for a third register, so `ADD Rd, Rm` means `Rd := Rd + Rm`.
    relation arm_inplace_dest(Address);

    // ---- outputs consumed downstream -------------------------------------------
    relation instruction(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize);
    relation instr_in_function(Node, Address);
    relation is_external_function(Address);
    relation plt_entry(Address, Symbol);
    relation func_stacksz(Address, Address, Symbol, u64);
    relation jmp_target_in_own_func(Address);
    relation mcond_at_jcc(Address);
    relation node_unlowered_side_effect(Address);
    relation mach_imm_stack_init(Address, i64, i64, Typ);
    relation mach_inst(Address, MachInst);
    relation osel_compare_site(Address, Address);
    // Both an input (the decoder's operand-derived uses) and an output: the rule below adds the uses an Mcond creates.
    relation reg_use(Address, Mreg);

    // SHARED-DERIVATION: restated from asm_pass because that pass is gated off for ARM32. Keep in step.

    instruction(addr, size, prefix, mnemonic, o1, o2, o3, o4, x, y) <--
        unrefinedinstruction(addr, size, prefix, mnemonic, o1, o2, o3, o4, x, y),
        code_in_refined_block(addr, _),
        !trim_instruction(addr);

    // The decoder assigns every real/normalized instruction (including both
    // halves of a split predicated instruction) to a basic block, and function
    // inference assigns blocks by CFG reachability.  Preserve all owners of a
    // shared block.  Do not extend ownership along physical instruction
    // adjacency: it can cross a function boundary.  Synthetic RTL nodes are
    // introduced later and inherit their producer's owner in rtl_pass.
    instr_in_function(addr, func) <--
        block_in_function(blockaddr, func),
        code_in_block(addr, blockaddr);

    plt_entry(addr, name) <--
        symbol_table(addr, _, _, _, _, _, section_name, _, name),
        if *section_name == ".plt" || *section_name == ".plt.got";

    is_external_function(addr) <-- plt_entry(addr, _);

    is_external_function(addr) <--
        symbol_table(addr, _, sym_type, _, _, _, section_name, _, _),
        if *sym_type == "FUNC",
        if *section_name == ".init" || *section_name == ".fini";

    // Frame size: A32 allocates with SUB SP, #N and with the PUSH/STMDB that saves the callee-saved registers, both recorded as negative adjusts_stack deltas.

    #[local] relation frame_alloc(Symbol, Address, i64);
    frame_alloc(func_name, addr, -*delta) <--
        adjusts_stack(addr, "SP", delta),
        if *delta < 0,
        instr_in_function(addr, func),
        func_span(func_name, func, _);

    func_stacksz(start_addr, end_addr, *func_name, stack_size_u64) <--
        func_span(func_name, start_addr, end_addr),
        agg stack_size = aggregators::sum(sz) in frame_alloc(func_name, _, sz),
        let stack_size_u64 = stack_size.max(0) as u64;

    // Control flow

    // BX LR, MOV PC,LR and POP {..,PC} are all returns; the decoder resolved which, since none of them carries a branch mnemonic.
    mach_inst(addr, MachInst::Mreturn) <--
        arm_pc_transfer(addr, true),
        instruction(addr, _, _, _, _, _, _, _, _, _);

    // A B whose target is inside the same function is structured control flow; one that leaves it is a tail call, the same split asm_pass makes for x86 JMP.
    jmp_target_in_own_func(addr) <--
        instruction(addr, _, _, "B", dst, _, _, _, _, _),
        op_immediate(dst, target_addr, _),
        instr_in_function(addr, func),
        instr_in_function(*target_addr as u64, func);

    mach_inst(addr, MachInst::Mgoto(dst)) <--
        instruction(addr, _, _, "B", dst, _, _, _, _, _),
        jmp_target_in_own_func(addr);

    mach_inst(addr, MachInst::Mtailcall(Either::Right(Either::Left(name)))) <--
        instruction(addr, _, _, "B", dst, _, _, _, _, _),
        !jmp_target_in_own_func(addr),
        op_immediate(dst, target_addr, _),
        func_entry(name, *target_addr as u64);

    // BL/BLX with an immediate is a direct call; BLX through a register is indirect.
    mach_inst(addr, MachInst::Mcall(Either::Right(Either::Left(name)))) <--
        instruction(addr, _, _, mnem, dst, _, _, _, _, _),
        if *mnem == "BL" || *mnem == "BLX",
        op_immediate(dst, target_addr, _),
        func_entry(name, *target_addr as u64);

    mach_inst(addr, MachInst::Mcall(Either::Right(Either::Right(*target_addr)))) <--
        instruction(addr, _, _, mnem, dst, _, _, _, _, _),
        if *mnem == "BL" || *mnem == "BLX",
        op_immediate(dst, target_addr, _),
        !func_entry(_, *target_addr as u64);

    mach_inst(addr, MachInst::Mcall(Either::Left(mreg_of(reg)))) <--
        instruction(addr, _, _, "BLX", dst, _, _, _, _, _),
        op_register(dst, reg);

    mach_inst(addr, MachInst::Mtailcall(Either::Left(*target))) <--
        arm_pc_transfer(addr, false),
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        if *mnem == "BX" || *mnem == "BXJ",
        indirect_tailcall_target(addr, target);

    // Conditional branches: A32 sets the flags separately like x86, so the pairing comes from flags_and_jump_pair and the compared operands are read back from the flag setter.

    mcond_at_jcc(br_addr) <--
        flags_and_jump_pair(_, br_addr, _),
        instruction(br_addr, _, _, mnem, _, _, _, _, _, _),
        if mnem.starts_with("B.");

    // Thumb's compare-and-branch carries its own comparison: it tests one register against zero WITHOUT reading the flags, so there is no flag setter to pair it with and the whole condition is recovered from the instruction itself. Its target follows the register, unlike every other ARM32 branch.
    mach_inst(addr, MachInst::Mcond(
        Condition::Ccompimm(cmp, 0),
        Arc::new(vec![mreg_of(rn)]),
        lbl
    )),
    mcond_at_jcc(*addr) <--
        instruction(addr, _, _, mnem, o0, lbl, _, _, _, _),
        if *mnem == "CBZ" || *mnem == "CBNZ",
        op_register(o0, rn),
        if is_modellable(rn),
        let cmp = if *mnem == "CBZ" { Comparison::Ceq } else { Comparison::Cne };

    // CMP Rn, Rm  /  B<cond>
    mach_inst(br_addr, MachInst::Mcond(condition, Arc::new(vec![mreg_of(r1), mreg_of(r2)]), lbl)) <--
        flags_and_jump_pair(cmp_addr, br_addr, cond),
        instruction(br_addr, _, _, br_mnem, lbl, _, _, _, _, _),
        if br_mnem.starts_with("B."),
        instruction(cmp_addr, _, _, "CMP", o1, o2, _, _, _, _),
        op_register(o1, r1),
        op_register(o2, r2),
        if let Some(condition) = cond_reg(cond);

    // CMP Rn, #imm  /  B<cond>
    mach_inst(br_addr, MachInst::Mcond(condition, Arc::new(vec![mreg_of(r1)]), lbl)) <--
        flags_and_jump_pair(cmp_addr, br_addr, cond),
        instruction(br_addr, _, _, br_mnem, lbl, _, _, _, _, _),
        if br_mnem.starts_with("B."),
        instruction(cmp_addr, _, _, "CMP", o1, o2, _, _, _, _),
        op_register(o1, r1),
        op_immediate(o2, imm, _),
        if let Some(condition) = cond_imm(cond, *imm);

    // CMN Rn, #imm compares against the immediate's negation: it is an ADDS that discards its result.
    mach_inst(br_addr, MachInst::Mcond(condition, Arc::new(vec![mreg_of(r1)]), lbl)) <--
        flags_and_jump_pair(cmp_addr, br_addr, cond),
        instruction(br_addr, _, _, br_mnem, lbl, _, _, _, _, _),
        if br_mnem.starts_with("B."),
        instruction(cmp_addr, _, _, "CMN", o1, o2, _, _, _, _),
        op_register(o1, r1),
        op_immediate(o2, imm, _),
        if let Some(condition) = cond_imm(cond, -*imm);

    // <op>S Rd, ... / B<cond>: the flags came from Rd, so the branch tests Rd against zero. Rd is read at the BRANCH's node, where it already holds the result.
    mach_inst(br_addr, MachInst::Mcond(condition, Arc::new(vec![mreg_of(rd)]), lbl)) <--
        flags_and_jump_pair(cmp_addr, br_addr, cond),
        instruction(br_addr, _, _, br_mnem, lbl, _, _, _, _, _),
        if br_mnem.starts_with("B."),
        instruction(cmp_addr, _, _, cmp_mnem, o0, _, _, _, _, _),
        if sets_flags_from_result(cmp_mnem),
        op_register(o0, rd),
        if is_modellable(rd),
        if let Some(condition) = cond_imm(cond, 0);

    // Predication as a select. `MOV<cc> Rd, Rm` writes Rd a value that already sits in Rm, so it IS x86's CMOV: the reversal is Osel between the new value and Rd's prior value. Every other predicated instruction was split into a guard branch plus an unconditional operation back in the decoder, because a conditional memory effect or a conditional computation has no faithful select form.
    // The Osel condition selects the PRESERVE operand (args[0]), so it is the NEGATION of the ARM predicate, exactly as asm_pass negates the cmov predicate.

    // CMP Rn, Rm  /  MOV<cc> Rd, Rm
    mach_inst(mov_addr, MachInst::Mop(
        Operation::Osel(condition, Typ::Tint),
        Arc::new(vec![mreg_of(rd), mreg_of(rs), mreg_of(c1), mreg_of(c2)]),
        mreg_of(rd)
    )),
    osel_compare_site(*mov_addr, *cmp_addr) <--
        flags_and_jump_pair(cmp_addr, mov_addr, cond),
        instruction(mov_addr, _, _, mov_mnem, d, s, _, _, _, _),
        if mov_mnem.starts_with("MOV."),
        op_register(d, rd),
        op_register(s, rs),
        if is_modellable(rd) && is_modellable(rs),
        instruction(cmp_addr, _, _, "CMP", o1, o2, _, _, _, _),
        op_register(o1, c1),
        op_register(o2, c2),
        if let Some(neg) = negate_cond(cond),
        if let Some(condition) = cond_reg(neg);

    // CMP Rn, #imm  /  MOV<cc> Rd, Rm
    mach_inst(mov_addr, MachInst::Mop(
        Operation::Osel(condition, Typ::Tint),
        Arc::new(vec![mreg_of(rd), mreg_of(rs), mreg_of(c1)]),
        mreg_of(rd)
    )),
    osel_compare_site(*mov_addr, *cmp_addr) <--
        flags_and_jump_pair(cmp_addr, mov_addr, cond),
        instruction(mov_addr, _, _, mov_mnem, d, s, _, _, _, _),
        if mov_mnem.starts_with("MOV."),
        op_register(d, rd),
        op_register(s, rs),
        if is_modellable(rd) && is_modellable(rs),
        instruction(cmp_addr, _, _, "CMP", o1, o2, _, _, _, _),
        op_register(o1, c1),
        op_immediate(o2, imm, _),
        if let Some(neg) = negate_cond(cond),
        if let Some(condition) = cond_imm(neg, *imm);

    // An A32 conditional branch has no register operand -- it reads the flags -- but the Mcond built for it reads the registers the flag setter compared. Without a use bound AT the branch, reaching-definition analysis has nothing to resolve those operands against and they come out as never-defined temporaries. asm_pass binds the same use for x86's relocated compare-and-jump.
    reg_use(addr, *m) <--
        mach_inst(addr, ?MachInst::Mcond(_, args, _)),
        for m in args.iter();

    // Data processing

    // Three-register ALU. A shifted source operand is a different computation, so it is excluded here and handled by the scaled-address rule below rather than silently losing the shift.
    mach_inst(addr, MachInst::Mop(op, Arc::new(vec![mreg_of(rn), mreg_of(rm)]), mreg_of(rd))) <--
        instruction(addr, _, _, mnem, o0, o1, o2, _, _, _),
        op_register(o0, rd),
        op_register(o1, rn),
        op_register(o2, rm),
        !arm_shifted_operand(o1, _, _),
        !arm_shifted_operand(o2, _, _),
        if is_modellable(rd) && is_modellable(rn) && is_modellable(rm),
        if let Some(op) = alu_rrr_op(mnem);

    // ADD Rd, Rn, Rm, LSL #k is base-plus-scaled-index arithmetic, which the shared alphabet already carries as a load-effective-address -- the same normalization x86's LEA gets.
    mach_inst(addr, MachInst::Mop(
        Operation::Olea(Addressing::Aindexed2scaled(1 << *sh, 0)),
        Arc::new(vec![mreg_of(rn), mreg_of(rm)]),
        mreg_of(rd)
    )) <--
        instruction(addr, _, _, mnem, o0, o1, o2, _, _, _),
        if *mnem == "ADD" || *mnem == "ADDS",
        op_register(o0, rd),
        op_register(o1, rn),
        op_register(o2, rm),
        !arm_shifted_operand(o1, _, _),
        arm_shifted_operand(o2, "LSL", sh),
        if *sh > 0 && *sh < 32,
        if is_modellable(rd) && is_modellable(rn) && is_modellable(rm);

    // A shift kind the shared alphabet cannot fold into one operation stays visible rather than being read as an unshifted register.
    node_unlowered_side_effect(addr) <--
        instruction(addr, _, _, mnem, o0, _, o2, _, _, _),
        arm_shifted_operand(o2, kind, _),
        if *kind != "LSL",
        op_register(o0, rd),
        if is_modellable(rd),
        if alu_rrr_op(mnem).is_some();

    // Register/immediate ALU.
    mach_inst(addr, MachInst::Mop(op, Arc::new(vec![mreg_of(rn)]), mreg_of(rd))) <--
        instruction(addr, _, _, mnem, o0, o1, o2, _, _, _),
        op_register(o0, rd),
        op_register(o1, rn),
        op_immediate(o2, imm, _),
        !arm_shifted_operand(o1, _, _),
        if is_modellable(rd) && is_modellable(rn),
        if let Some(op) = alu_rri_op(mnem, *imm);

    // The two-operand ALU forms Thumb's 16-bit encodings use: the destination is also the first source, which arm_inplace_dest states and the operand list does not.

    // Rd := Rd <op> Rm
    mach_inst(addr, MachInst::Mop(op, Arc::new(vec![mreg_of(rd), mreg_of(rm)]), mreg_of(rd))) <--
        arm_inplace_dest(addr),
        instruction(addr, _, _, mnem, o0, o1, o2, _, _, _),
        if *o2 == "0",
        op_register(o0, rd),
        op_register(o1, rm),
        !arm_shifted_operand(o1, _, _),
        if is_modellable(rd) && is_modellable(rm),
        if let Some(op) = alu_rrr_op(mnem);

    // Rd := Rd <op> #imm
    mach_inst(addr, MachInst::Mop(op, Arc::new(vec![mreg_of(rd)]), mreg_of(rd))) <--
        arm_inplace_dest(addr),
        instruction(addr, _, _, mnem, o0, o1, o2, _, _, _),
        if *o2 == "0",
        op_register(o0, rd),
        op_immediate(o1, imm, _),
        if is_modellable(rd),
        if let Some(op) = alu_rri_op(mnem, *imm);

    // RSB Rd, Rn, #0 is A32's negate; the general RSB #imm is imm - Rn, which the shared alphabet spells as a negate followed by an add, so only the negate form is modelled here.
    mach_inst(addr, MachInst::Mop(Operation::Oneg, Arc::new(vec![mreg_of(rn)]), mreg_of(rd))) <--
        instruction(addr, _, _, mnem, o0, o1, o2, _, _, _),
        if *mnem == "RSB" || *mnem == "RSBS",
        op_register(o0, rd),
        op_register(o1, rn),
        op_immediate(o2, 0, _),
        if is_modellable(rd) && is_modellable(rn);

    // Two-register unary: MOV/MVN and the sign/zero extensions.
    mach_inst(addr, MachInst::Mop(op, Arc::new(vec![mreg_of(rn)]), mreg_of(rd))) <--
        instruction(addr, _, _, mnem, o0, o1, o2, _, _, _),
        if *o2 == "0",
        op_register(o0, rd),
        op_register(o1, rn),
        !arm_shifted_operand(o1, _, _),
        if is_modellable(rd) && is_modellable(rn),
        if let Some(op) = alu_rr_op(mnem);

    // MOV/MOVW Rd, #imm materializes a constant.
    mach_inst(addr, MachInst::Mop(Operation::Ointconst(*imm), Arc::new(vec![]), mreg_of(rd))) <--
        instruction(addr, _, _, mnem, o0, o1, o2, _, _, _),
        if *mnem == "MOV" || *mnem == "MOVS" || *mnem == "MOVW",
        if *o2 == "0",
        op_register(o0, rd),
        op_immediate(o1, imm, _),
        if is_modellable(rd);

    // MVN Rd, #imm materializes the constant's complement.
    mach_inst(addr, MachInst::Mop(Operation::Ointconst(!*imm), Arc::new(vec![]), mreg_of(rd))) <--
        instruction(addr, _, _, mnem, o0, o1, o2, _, _, _),
        if *mnem == "MVN" || *mnem == "MVNS",
        if *o2 == "0",
        op_register(o0, rd),
        op_immediate(o1, imm, _),
        if is_modellable(rd);

    // MOVT Rd, #imm sets the top halfword of a register the preceding MOVW already loaded; it is a bitwise OR with the shifted immediate, not a fresh constant.
    mach_inst(addr, MachInst::Mop(Operation::Oorimm(*imm << 16), Arc::new(vec![mreg_of(rd)]), mreg_of(rd))) <--
        instruction(addr, _, _, "MOVT", o0, o1, _, _, _, _),
        op_register(o0, rd),
        op_immediate(o1, imm, _),
        if is_modellable(rd);

    // A PC-relative load reads a literal pool word, so it materializes a constant rather than touching memory; the decoder already resolved the value out of the image.
    mach_inst(addr, MachInst::Mop(Operation::Ointconst(*value), Arc::new(vec![]), mreg_of(rd))) <--
        arm_literal_value(addr, value),
        instruction(addr, _, _, mnem, o0, _, _, _, _, _),
        if is_load_mnem(mnem),
        op_register(o0, rd),
        if is_modellable(rd);

    // ADD Rd, SP, #imm is frame-address arithmetic, spelled in the shared alphabet as a load-effective-address over Ainstack. The generic register/immediate rule above cannot also fire, because is_modellable rejects SP as a source.
    mach_inst(addr, MachInst::Mop(Operation::Olea(Addressing::Ainstack(*imm)), Arc::new(vec![]), mreg_of(rd))) <--
        instruction(addr, _, _, "ADD", o0, o1, o2, _, _, _),
        op_register(o0, rd),
        op_register(o1, base),
        if *base == "SP",
        op_immediate(o2, imm, _),
        if is_modellable(rd);

    // Memory

    mach_inst(addr, MachInst::Mload(chunk, addressing, Arc::new(args), mreg_of(rt))) <--
        instruction(addr, _, _, mnem, o0, o1, _, _, _, _),
        if is_load_mnem(mnem),
        !arm_literal_value(addr, _),
        !arm_frame_setup(addr),
        op_register(o0, rt),
        if is_modellable(rt),
        op_indirect(o1, _, base, index, scale, disp, _),
        if let Some(chunk) = chunk_of(mnem, rt),
        if let Some((addressing, args)) = addressing_of(base, index, *scale, *disp);

    mach_inst(addr, MachInst::Mstore(chunk, addressing, Arc::new(args), mreg_of(rt))) <--
        instruction(addr, _, _, mnem, o0, o1, _, _, _, _),
        if is_store_mnem(mnem),
        !arm_frame_setup(addr),
        op_register(o0, rt),
        if is_modellable(rt),
        op_indirect(o1, _, base, index, scale, disp, _),
        if let Some(chunk) = chunk_of(mnem, rt),
        if let Some((addressing, args)) = addressing_of(base, index, *scale, *disp);

    // LDM/STM: one ordinary slot transfer per register, at the offset the addressing mode puts it. PC in a POP list is the return, handled by the Mreturn rule above rather than as a data transfer. The prologue/epilogue push and pop are excluded by arm_frame_setup.
    mach_inst(addr, MachInst::Mload(chunk, addressing, Arc::new(args), mreg_of(reg))) <--
        arm_multi_transfer(addr, true, reg, base, offset, _),
        instruction(addr, _, _, _, _, _, _, _, _, _),
        !arm_frame_setup(addr),
        if is_modellable(reg),
        let chunk = if is_float_reg(reg) { MemoryChunk::MFloat64 } else { MemoryChunk::MInt32 },
        if let Some((addressing, args)) = addressing_of(base, "NONE", 1, *offset);

    mach_inst(addr, MachInst::Mstore(chunk, addressing, Arc::new(args), mreg_of(reg))) <--
        arm_multi_transfer(addr, false, reg, base, offset, _),
        instruction(addr, _, _, _, _, _, _, _, _, _),
        !arm_frame_setup(addr),
        if is_modellable(reg),
        let chunk = if is_float_reg(reg) { MemoryChunk::MFloat64 } else { MemoryChunk::MInt32 },
        if let Some((addressing, args)) = addressing_of(base, "NONE", 1, *offset);

    // Unmodelled: NEON and the shifted-index addressing forms have no scalar lowering here, so flagging them keeps the loss visible downstream instead of silently dropping the computation.
    node_unlowered_side_effect(addr) <--
        arm_unmodelled(addr),
        instruction(addr, _, _, _, _, _, _, _, _, _);

    node_unlowered_side_effect(addr) <--
        instruction(addr, _, _, mnem, _, _, _, _, _, _),
        if is_simd_mnem(mnem);
}

// Genuinely packed SIMD mnemonics, excluding the scalar VFP forms (VMOV/VADD/VCMP on Sn/Dn) and the VLDR/VSTR/VPUSH/VPOP block movers, which are ordinary memory traffic.
fn is_simd_mnem(m: &str) -> bool {
    let stem = m.split('_').next().unwrap_or(m);
    matches!(
        stem,
        "VTBL"
            | "VTBX"
            | "VZIP"
            | "VUZP"
            | "VTRN"
            | "VEXT"
            | "VREV16"
            | "VREV32"
            | "VREV64"
            | "VPADD"
            | "VPADAL"
            | "VPMAX"
            | "VPMIN"
            | "VQADD"
            | "VQSUB"
            | "VSHL"
            | "VSHR"
            | "VSRA"
            | "VSLI"
            | "VSRI"
            | "VMOVL"
            | "VMOVN"
            | "VQMOVN"
            | "VDUP"
            | "VBSL"
            | "VBIT"
            | "VBIF"
            | "VCEQ"
            | "VCGE"
            | "VCGT"
            | "VTST"
            | "VLD1"
            | "VLD2"
            | "VLD3"
            | "VLD4"
            | "VST1"
            | "VST2"
            | "VST3"
            | "VST4"
    )
}

pub struct Arm32AsmPass;

impl IRPass for Arm32AsmPass {
    fn name(&self) -> &'static str {
        "arm32_asm"
    }

    fn run(&self, db: &mut DecompileDB) {
        // Mutually exclusive with asm_pass and aarch64_asm_pass; see the module comment for why running two frontends would corrupt rather than duplicate.
        if db.abi().arch != Arch::Arm32 {
            return;
        }
        run_pass!(db, Arm32AsmPassProgram);
    }

    declare_io_from!(Arm32AsmPassProgram);
}

#[cfg(test)]
mod function_ownership_tests {
    use super::{Arm32AsmPass, Arm32AsmPassProgram};
    use crate::arm32::mach::A32Mreg;
    use crate::decompile::passes::pass::IRPass;
    use crate::mreg::Mreg;
    use crate::x86::types::MachInst;
    use std::collections::BTreeSet;

    fn on_large_stack(test: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(test)
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn arm32_function_ownership_covers_split_nodes_and_shared_blocks() {
        on_large_stack(|| {
            let mut prog = Arm32AsmPassProgram::default();
            let func_a = 0x100;
            let func_b = 0x900;
            // Model the guard/body rows produced by reversing a predicated
            // instruction.  Both are normalized decoder rows in one block.
            let split_guard = 0x701;
            let split_body = 0x702;
            let node_b_cold = 0x080;
            let node_shared = 0x400;
            let unassigned = 0x500;

            prog.block_in_function.push((0xa0, func_a));
            prog.block_in_function.push((0xb0, func_b));
            prog.block_in_function.push((0xc0, func_a));
            prog.block_in_function.push((0xc0, func_b));
            prog.code_in_block.push((split_guard, 0xa0));
            prog.code_in_block.push((split_body, 0xa0));
            prog.code_in_block.push((node_b_cold, 0xb0));
            prog.code_in_block.push((node_shared, 0xc0));
            prog.code_in_block.push((unassigned, 0xd0));

            prog.run();

            let owners = |node| {
                prog.instr_in_function
                    .iter()
                    .filter_map(|(n, f)| (*n == node).then_some(*f))
                    .collect::<BTreeSet<_>>()
            };
            assert_eq!(owners(split_guard), BTreeSet::from([func_a]));
            assert_eq!(owners(split_body), BTreeSet::from([func_a]));
            assert_eq!(owners(node_b_cold), BTreeSet::from([func_b]));
            assert_eq!(owners(node_shared), BTreeSet::from([func_a, func_b]));
            assert!(owners(unassigned).is_empty());
        });
    }

    #[test]
    fn arm32_function_ownership_scheduler_metadata_is_structural() {
        let pass = Arm32AsmPass;
        for relation in ["block_in_function", "code_in_block"] {
            assert!(
                pass.inputs().contains(&relation),
                "missing scheduler input {relation}"
            );
        }
        assert!(pass.outputs().contains(&"instr_in_function"));
        assert!(!pass.inputs().contains(&"next"));
        assert!(!pass.inputs().contains(&"ddisasm_function_entry"));
    }

    #[test]
    fn classified_arm_bx_becomes_a_register_tailcall() {
        on_large_stack(|| {
            let mut prog = Arm32AsmPassProgram::default();
            let branch = 0x700;
            let target = Mreg::A32(A32Mreg::R3);
            prog.instruction
                .push((branch, 4, "", "BX", "target", "", "", "", 0, 0));
            prog.arm_pc_transfer.push((branch, false));
            prog.indirect_tailcall_target.push((branch, target));

            prog.run();

            assert!(prog.mach_inst.iter().any(|(node, inst)| {
                *node == branch
                    && matches!(inst, MachInst::Mtailcall(either::Either::Left(reg)) if *reg == target)
            }));
        });
    }
}
