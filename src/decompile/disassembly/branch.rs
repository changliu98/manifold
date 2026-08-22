// Arch-neutral control-transfer classification: the four facts block/CFG building need, answered per-arch so no shared consumer matches one architecture's mnemonics.

use crate::abi::Arch;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BranchKind {
    // Not a control transfer.
    None,
    // Falls through on one edge, jumps on the other.
    CondJump,
    // Unconditional jump to a known target.
    UncondJump,
    // Unconditional jump through a register or memory (jump tables, tail calls).
    IndirectJump,
    // Call that returns to the following instruction.
    Call,
    // Call through a register or memory.
    IndirectCall,
    // Function return.
    Return,
    // Terminates the block with no successor: traps and undefined instructions.
    Trap,
    // Ends a basic block, but the CFG models it as ordinary fallthrough (x86 SYSCALL resumes at the next instruction).
    OpaqueTransfer,
}

impl BranchKind {
    pub fn is_control_transfer(&self) -> bool {
        !matches!(self, BranchKind::None)
    }

    /// True when execution may continue at the next instruction.
    pub fn falls_through(&self) -> bool {
        matches!(
            self,
            BranchKind::None
                | BranchKind::CondJump
                | BranchKind::Call
                | BranchKind::IndirectCall
                | BranchKind::OpaqueTransfer
        )
    }
}

// Where an instruction's new PC comes from, for the architectures that write the PC as an ordinary register destination. A32 has no branch mnemonic for `MOV PC, LR` or `POP {..,PC}`, so a purely mnemonic-keyed classification would miss both; the decoder, which has the operands, supplies this fact and classify combines it with the mnemonic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum PcSource {
    /// The instruction does not write the PC as a register destination. Always the case on x86 and AArch64, where the PC is not addressable.
    #[default]
    NotWritten,
    /// The written value is the link register or a stack slot restored by the same instruction: the saved return address.
    SavedReturnAddress,
    /// The written value is computed from other registers or loaded from a table.
    Computed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BranchInfo {
    pub kind: BranchKind,
    /// Operand slot holding the PC-relative target: x86 always slot 0, AArch64 slot 1 for CBZ and slot 2 for TBZ.
    pub target_op: Option<usize>,
}

const NOT_A_BRANCH: BranchInfo = BranchInfo {
    kind: BranchKind::None,
    target_op: None,
};

/// Operand slot holding a PC-relative immediate target. A property of the mnemonic alone: an instruction that reaches its target by writing the PC register encodes no target operand, so `PcSource` cannot change the answer.
pub fn direct_target_op(arch: Arch, mnem: &str) -> Option<usize> {
    classify(arch, mnem, PcSource::NotWritten).target_op
}

pub fn classify(arch: Arch, mnem: &str, pc: PcSource) -> BranchInfo {
    match arch {
        Arch::Aarch64 => classify_aarch64(mnem),
        Arch::Arm32 => classify_arm32(mnem, pc),
        _ => classify_x86(mnem),
    }
}

fn info(kind: BranchKind, target_op: Option<usize>) -> BranchInfo {
    BranchInfo { kind, target_op }
}

fn classify_x86(mnem: &str) -> BranchInfo {
    match mnem {
        "JMP" | "JMPQ" => return info(BranchKind::UncondJump, Some(0)),
        "CALL" => return info(BranchKind::Call, Some(0)),
        "RET" => return info(BranchKind::Return, None),
        "INT3" | "HLT" | "UD2" => return info(BranchKind::Trap, None),
        // Jcc including the count-register forms; LOOP/LOOPcc decrement RCX and branch, so both edges live.
        "JE" | "JNE" | "JL" | "JLE" | "JG" | "JGE" | "JB" | "JBE" | "JA" | "JAE" | "JP" | "JNP"
        | "JO" | "JNO" | "JS" | "JNS" | "JCXZ" | "JECXZ" | "JRCXZ" | "LOOP" | "LOOPE"
        | "LOOPNE" => return info(BranchKind::CondJump, Some(0)),
        // Enters the kernel and resumes at the next instruction.
        "SYSCALL" => return info(BranchKind::OpaqueTransfer, None),
        _ => {}
    }
    // Any remaining J-prefixed mnemonic ends a block but contributed no branch edge before this refactor; keep it that way.
    if mnem.starts_with('J') {
        return info(BranchKind::OpaqueTransfer, None);
    }
    NOT_A_BRANCH
}

fn classify_aarch64(mnem: &str) -> BranchInfo {
    match mnem {
        "B" => return info(BranchKind::UncondJump, Some(0)),
        "BL" => return info(BranchKind::Call, Some(0)),
        "BR" => return info(BranchKind::IndirectJump, None),
        "BLR" => return info(BranchKind::IndirectCall, None),
        "RET" => return info(BranchKind::Return, None),
        // Compare-and-branch tests one register against zero.
        "CBZ" | "CBNZ" => return info(BranchKind::CondJump, Some(1)),
        // Test-bit-and-branch takes a bit position before the target.
        "TBZ" | "TBNZ" => return info(BranchKind::CondJump, Some(2)),
        "BRK" | "UDF" => return info(BranchKind::Trap, None),
        // Supervisor/hypervisor calls resume at the next instruction.
        "SVC" | "HVC" | "SMC" => return info(BranchKind::OpaqueTransfer, None),
        _ => {}
    }
    // The B.<cond> family, matched by prefix anchored on the dot so BFI/BIC/BFXIL/BFM/BSL/BIF cannot match.
    if let Some(rest) = mnem.strip_prefix("B.") {
        if !rest.is_empty() {
            return info(BranchKind::CondJump, Some(0));
        }
    }
    NOT_A_BRANCH
}

/// The A32 condition codes as capstone spells them. AL is absent: an AL-suffixed mnemonic is printed bare.
pub const ARM_CONDITION_CODES: [&str; 16] = [
    "EQ", "NE", "CS", "HS", "CC", "LO", "MI", "PL", "VS", "VC", "HI", "LS", "GE", "LT", "GT", "LE",
];

pub fn is_arm_condition(cc: &str) -> bool {
    ARM_CONDITION_CODES.contains(&cc)
}

// A32 mnemonics reach here in the arm32 decoder's normalized spelling: the bare opcode stem, with any condition code as a DOTTED suffix ("B.EQ", "MOV.GT"). The dot is what makes the split unambiguous -- glued, `MOVS` reads as MOV+VS and `MULS` as MUL+LS.
fn classify_arm32(mnem: &str, pc: PcSource) -> BranchInfo {
    let (stem, cond) = match mnem.split_once('.') {
        Some((s, c)) => (s, Some(c)),
        None => (mnem, None),
    };

    match stem {
        // A conditional branch is spelled B.<cond>; unconditional B is the plain stem.
        "B" => {
            return match cond {
                Some(_) => info(BranchKind::CondJump, Some(0)),
                None => info(BranchKind::UncondJump, Some(0)),
            }
        }
        // BL takes an immediate and BLX either an immediate or a register; cfg.rs already downgrades a Call with no immediate operand to an indirect call, exactly as it does for x86 CALL.
        "BL" | "BLX" => return info(BranchKind::Call, Some(0)),
        // BX Rm is a return when Rm is the link register and an indirect jump otherwise; the decoder decides which, since the mnemonic cannot.
        "BX" | "BXJ" => {
            return match pc {
                PcSource::SavedReturnAddress => info(BranchKind::Return, None),
                _ => info(BranchKind::IndirectJump, None),
            }
        }
        // Thumb's compare-and-branch tests one register against zero without reading the flags; the target follows the register.
        "CBZ" | "CBNZ" => return info(BranchKind::CondJump, Some(1)),
        // Thumb's table branches read a jump table indexed by a register and write the PC from it.
        "TBB" | "TBH" => return info(BranchKind::IndirectJump, None),
        "UDF" | "BKPT" | "HLT" | "TRAP" => return info(BranchKind::Trap, None),
        // Supervisor calls resume at the following instruction.
        "SVC" | "SWI" | "HVC" | "SMC" => return info(BranchKind::OpaqueTransfer, None),
        _ => {}
    }

    // No branch mnemonic, but A32 writes R15 as an ordinary destination: MOV PC,LR and POP {..,PC} return, ADD PC,PC,Rn and LDR PC,[PC,Rn,LSL#2] are jump tables.
    match pc {
        PcSource::SavedReturnAddress => info(BranchKind::Return, None),
        PcSource::Computed => info(BranchKind::IndirectJump, None),
        PcSource::NotWritten => NOT_A_BRANCH,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kind(arch: Arch, mnem: &str) -> BranchKind {
        classify(arch, mnem, PcSource::NotWritten).kind
    }

    #[test]
    fn aarch64_data_processing_b_mnemonics_are_not_branches() {
        for m in ["BFI", "BIC", "BFXIL", "BFM", "BFC", "BSL", "BIF", "BICS"] {
            assert_eq!(
                kind(Arch::Aarch64, m),
                BranchKind::None,
                "{m} must not classify as a branch"
            );
        }
    }

    #[test]
    fn aarch64_branch_targets_sit_in_the_right_operand_slot() {
        assert_eq!(direct_target_op(Arch::Aarch64, "B"), Some(0));
        assert_eq!(direct_target_op(Arch::Aarch64, "B.LT"), Some(0));
        assert_eq!(direct_target_op(Arch::Aarch64, "CBZ"), Some(1));
        assert_eq!(direct_target_op(Arch::Aarch64, "TBNZ"), Some(2));
    }

    // The exact set block.rs::is_branch recognized before this module existed.
    #[test]
    fn x86_block_splitting_set_is_unchanged() {
        for m in [
            "JMP",
            "JE",
            "JNE",
            "JRCXZ",
            "JUNKNOWNCC",
            "RET",
            "CALL",
            "LOOP",
            "LOOPE",
            "LOOPNE",
            "INT3",
            "HLT",
            "UD2",
            "SYSCALL",
        ] {
            assert!(
                kind(Arch::X86_64, m).is_control_transfer(),
                "{m} must remain a block terminator"
            );
        }
        for m in [
            "MOV", "ADD", "LEA", "XOR", "CMP", "TEST", "SYSRET", "IRET", "RETF",
        ] {
            assert_eq!(
                kind(Arch::X86_64, m),
                BranchKind::None,
                "{m} was not a block terminator before and must not become one"
            );
        }
    }

    // SYSCALL and unrecognized Jcc split blocks but produced only a fallthrough edge.
    #[test]
    fn x86_opaque_transfers_still_fall_through() {
        for m in ["SYSCALL", "JUNKNOWNCC"] {
            let k = kind(Arch::X86_64, m);
            assert_eq!(k, BranchKind::OpaqueTransfer);
            assert!(k.falls_through());
            assert!(k.is_control_transfer());
        }
    }

    // Widening classify with PcSource must not change the answer for the architectures whose PC is not a register destination.
    #[test]
    fn pc_source_is_inert_on_x86_and_aarch64() {
        for arch in [Arch::X86_64, Arch::X86_32, Arch::Aarch64] {
            for m in ["MOV", "ADD", "LDR", "POP", "RET", "B", "JMP"] {
                for pc in [PcSource::SavedReturnAddress, PcSource::Computed] {
                    assert_eq!(
                        classify(arch, m, pc),
                        classify(arch, m, PcSource::NotWritten),
                        "{arch:?} {m} must ignore PcSource"
                    );
                }
            }
        }
    }

    #[test]
    fn arm32_branch_mnemonics_are_not_confused_with_data_processing() {
        assert_eq!(kind(Arch::Arm32, "B"), BranchKind::UncondJump);
        assert_eq!(kind(Arch::Arm32, "BL"), BranchKind::Call);
        assert_eq!(kind(Arch::Arm32, "BLX"), BranchKind::Call);
        // BLS is "branch if lower or same"; the dotted spelling keeps it apart from BL.
        assert_eq!(kind(Arch::Arm32, "B.LS"), BranchKind::CondJump);
        assert_eq!(kind(Arch::Arm32, "B.LE"), BranchKind::CondJump);
        assert_eq!(kind(Arch::Arm32, "B.NE"), BranchKind::CondJump);
        assert_eq!(direct_target_op(Arch::Arm32, "B.NE"), Some(0));
        // Data processing that merely starts with B, and the flag-setting forms whose glued spelling would end in a condition code.
        for m in ["BIC", "BICS", "BFI", "BFC", "MOVS", "MULS", "SUBS"] {
            assert_eq!(kind(Arch::Arm32, m), BranchKind::None, "{m}");
        }
        assert_eq!(kind(Arch::Arm32, "BKPT"), BranchKind::Trap);
    }

    // The reason classify had to be widened: these carry no branch mnemonic at all.
    #[test]
    fn arm32_pc_writes_are_control_transfers_without_a_branch_mnemonic() {
        // MOV PC, LR and POP {..,PC} and LDR PC,[SP],#4.
        for m in ["MOV", "POP", "LDM", "LDR"] {
            assert_eq!(
                classify(Arch::Arm32, m, PcSource::SavedReturnAddress).kind,
                BranchKind::Return,
                "{m} writing the saved return address to PC is a return"
            );
            assert_eq!(
                classify(Arch::Arm32, m, PcSource::Computed).kind,
                BranchKind::IndirectJump,
                "{m} writing a computed value to PC is an indirect jump"
            );
            assert_eq!(kind(Arch::Arm32, m), BranchKind::None);
        }
        // ADD PC, PC, Rn is the classic A32 jump table.
        assert_eq!(
            classify(Arch::Arm32, "ADD", PcSource::Computed).kind,
            BranchKind::IndirectJump
        );
        // BX LR returns; BX Rn is an indirect jump.
        assert_eq!(
            classify(Arch::Arm32, "BX", PcSource::SavedReturnAddress).kind,
            BranchKind::Return
        );
        assert_eq!(
            classify(Arch::Arm32, "BX", PcSource::Computed).kind,
            BranchKind::IndirectJump
        );
    }
}
