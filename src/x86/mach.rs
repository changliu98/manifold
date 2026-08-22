use crate::x86::asm::{Freg, Ireg};

// x86-64 machine registers (CompCert x86/Machregs.v); declaration order is load-bearing for Mreg's derived Ord.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum X86Mreg {
    AX,
    BX,
    CX,
    DX,
    SI,
    DI,
    BP,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
    X0,
    X1,
    X2,
    X3,
    X4,
    X5,
    X6,
    X7,
    X8,
    X9,
    X10,
    X11,
    X12,
    X13,
    X14,
    X15,
    FP0,
    SP,
    Unknown,
}

impl X86Mreg {
    /// True for an XMM (SSE) register: a value living here is a float bit-pattern.
    pub fn is_xmm(&self) -> bool {
        matches!(
            self,
            X86Mreg::X0
                | X86Mreg::X1
                | X86Mreg::X2
                | X86Mreg::X3
                | X86Mreg::X4
                | X86Mreg::X5
                | X86Mreg::X6
                | X86Mreg::X7
                | X86Mreg::X8
                | X86Mreg::X9
                | X86Mreg::X10
                | X86Mreg::X11
                | X86Mreg::X12
                | X86Mreg::X13
                | X86Mreg::X14
                | X86Mreg::X15
        )
    }
}

impl From<&str> for X86Mreg {
    fn from(s: &str) -> Self {
        match s.to_uppercase().as_str() {
            "MACHREGS.AX" => X86Mreg::AX,
            "MACHREGS.BX" => X86Mreg::BX,
            "MACHREGS.CX" => X86Mreg::CX,
            "MACHREGS.DX" => X86Mreg::DX,
            "MACHREGS.SI" => X86Mreg::SI,
            "MACHREGS.DI" => X86Mreg::DI,
            "MACHREGS.BP" => X86Mreg::BP,
            "MACHREGS.R8" => X86Mreg::R8,
            "MACHREGS.R9" => X86Mreg::R9,
            "MACHREGS.R10" => X86Mreg::R10,
            "MACHREGS.R11" => X86Mreg::R11,
            "MACHREGS.R12" => X86Mreg::R12,
            "MACHREGS.R13" => X86Mreg::R13,
            "MACHREGS.R14" => X86Mreg::R14,
            "MACHREGS.R15" => X86Mreg::R15,
            "MACHREGS.X0" => X86Mreg::X0,
            "MACHREGS.X1" => X86Mreg::X1,
            "MACHREGS.X2" => X86Mreg::X2,
            "MACHREGS.X3" => X86Mreg::X3,
            "MACHREGS.X4" => X86Mreg::X4,
            "MACHREGS.X5" => X86Mreg::X5,
            "MACHREGS.X6" => X86Mreg::X6,
            "MACHREGS.X7" => X86Mreg::X7,
            "MACHREGS.X8" => X86Mreg::X8,
            "MACHREGS.X9" => X86Mreg::X9,
            "MACHREGS.X10" => X86Mreg::X10,
            "MACHREGS.X11" => X86Mreg::X11,
            "MACHREGS.X12" => X86Mreg::X12,
            "MACHREGS.X13" => X86Mreg::X13,
            "MACHREGS.X14" => X86Mreg::X14,
            "MACHREGS.X15" => X86Mreg::X15,
            "MACHREGS.FP0" => X86Mreg::FP0,
            "RAX" | "EAX" | "AX" | "AL" | "AH" => X86Mreg::AX,
            "RBX" | "EBX" | "BX" | "BL" | "BH" => X86Mreg::BX,
            "RCX" | "ECX" | "CX" | "CL" | "CH" => X86Mreg::CX,
            "RDX" | "EDX" | "DX" | "DL" | "DH" => X86Mreg::DX,
            "RSI" | "ESI" | "SI" | "SIL" => X86Mreg::SI,
            "RDI" | "EDI" | "DI" | "DIL" => X86Mreg::DI,
            "RBP" | "EBP" | "BP" | "BPL" => X86Mreg::BP,
            "RSP" | "ESP" | "SP" | "SPL" => X86Mreg::SP,

            "R8" | "R8D" | "R8W" | "R8B" => X86Mreg::R8,
            "R9" | "R9D" | "R9W" | "R9B" => X86Mreg::R9,
            "R10" | "R10D" | "R10W" | "R10B" => X86Mreg::R10,
            "R11" | "R11D" | "R11W" | "R11B" => X86Mreg::R11,
            "R12" | "R12D" | "R12W" | "R12B" => X86Mreg::R12,
            "R13" | "R13D" | "R13W" | "R13B" => X86Mreg::R13,
            "R14" | "R14D" | "R14W" | "R14B" => X86Mreg::R14,
            "R15" | "R15D" | "R15W" | "R15B" => X86Mreg::R15,

            "XMM0" | "YMM0" | "X0" => X86Mreg::X0,
            "XMM1" | "YMM1" | "X1" => X86Mreg::X1,
            "XMM2" | "YMM2" | "X2" => X86Mreg::X2,
            "XMM3" | "YMM3" | "X3" => X86Mreg::X3,
            "XMM4" | "YMM4" | "X4" => X86Mreg::X4,
            "XMM5" | "YMM5" | "X5" => X86Mreg::X5,
            "XMM6" | "YMM6" | "X6" => X86Mreg::X6,
            "XMM7" | "YMM7" | "X7" => X86Mreg::X7,
            "XMM8" | "YMM8" | "X8" => X86Mreg::X8,
            "XMM9" | "YMM9" | "X9" => X86Mreg::X9,
            "XMM10" | "YMM10" | "X10" => X86Mreg::X10,
            "XMM11" | "YMM11" | "X11" => X86Mreg::X11,
            "XMM12" | "YMM12" | "X12" => X86Mreg::X12,
            "XMM13" | "YMM13" | "X13" => X86Mreg::X13,
            "XMM14" | "YMM14" | "X14" => X86Mreg::X14,
            "XMM15" | "YMM15" | "X15" => X86Mreg::X15,
            "FP0" => X86Mreg::FP0,
            _ => X86Mreg::Unknown,
        }
    }
}

impl From<String> for X86Mreg {
    fn from(s: String) -> Self {
        X86Mreg::from(s.as_str())
    }
}

impl From<&String> for X86Mreg {
    fn from(s: &String) -> Self {
        X86Mreg::from(s.as_str())
    }
}

impl From<&&str> for X86Mreg {
    fn from(s: &&str) -> Self {
        X86Mreg::from(*s)
    }
}

impl From<Ireg> for X86Mreg {
    fn from(ireg: Ireg) -> Self {
        match ireg {
            Ireg::RAX => X86Mreg::AX,
            Ireg::RBX => X86Mreg::BX,
            Ireg::RCX => X86Mreg::CX,
            Ireg::RDX => X86Mreg::DX,
            Ireg::RSI => X86Mreg::SI,
            Ireg::RDI => X86Mreg::DI,
            Ireg::RBP => X86Mreg::BP,
            Ireg::RSP => X86Mreg::SP,
            Ireg::R8 => X86Mreg::R8,
            Ireg::R9 => X86Mreg::R9,
            Ireg::R10 => X86Mreg::R10,
            Ireg::R11 => X86Mreg::R11,
            Ireg::R12 => X86Mreg::R12,
            Ireg::R13 => X86Mreg::R13,
            Ireg::R14 => X86Mreg::R14,
            Ireg::R15 => X86Mreg::R15,
            Ireg::RIP => X86Mreg::Unknown,
            Ireg::Unknown => X86Mreg::Unknown,
        }
    }
}

impl From<Freg> for X86Mreg {
    fn from(freg: Freg) -> Self {
        match freg {
            Freg::XMM0 => X86Mreg::X0,
            Freg::XMM1 => X86Mreg::X1,
            Freg::XMM2 => X86Mreg::X2,
            Freg::XMM3 => X86Mreg::X3,
            Freg::XMM4 => X86Mreg::X4,
            Freg::XMM5 => X86Mreg::X5,
            Freg::XMM6 => X86Mreg::X6,
            Freg::XMM7 => X86Mreg::X7,
            Freg::XMM8 => X86Mreg::X8,
            Freg::XMM9 => X86Mreg::X9,
            Freg::XMM10 => X86Mreg::X10,
            Freg::XMM11 => X86Mreg::X11,
            Freg::XMM12 => X86Mreg::X12,
            Freg::XMM13 => X86Mreg::X13,
            Freg::XMM14 => X86Mreg::X14,
            Freg::XMM15 => X86Mreg::X15,
            Freg::Unknown => X86Mreg::Unknown,
        }
    }
}

impl ToString for X86Mreg {
    fn to_string(&self) -> String {
        match self {
            X86Mreg::AX => "Machregs.AX".to_string(),
            X86Mreg::BX => "Machregs.BX".to_string(),
            X86Mreg::CX => "Machregs.CX".to_string(),
            X86Mreg::DX => "Machregs.DX".to_string(),
            X86Mreg::SI => "Machregs.SI".to_string(),
            X86Mreg::DI => "Machregs.DI".to_string(),
            X86Mreg::BP => "Machregs.BP".to_string(),
            X86Mreg::R8 => "Machregs.R8".to_string(),
            X86Mreg::R9 => "Machregs.R9".to_string(),
            X86Mreg::R10 => "Machregs.R10".to_string(),
            X86Mreg::R11 => "Machregs.R11".to_string(),
            X86Mreg::R12 => "Machregs.R12".to_string(),
            X86Mreg::R13 => "Machregs.R13".to_string(),
            X86Mreg::R14 => "Machregs.R14".to_string(),
            X86Mreg::R15 => "Machregs.R15".to_string(),
            X86Mreg::X0 => "Machregs.X0".to_string(),
            X86Mreg::X1 => "Machregs.X1".to_string(),
            X86Mreg::X2 => "Machregs.X2".to_string(),
            X86Mreg::X3 => "Machregs.X3".to_string(),
            X86Mreg::X4 => "Machregs.X4".to_string(),
            X86Mreg::X5 => "Machregs.X5".to_string(),
            X86Mreg::X6 => "Machregs.X6".to_string(),
            X86Mreg::X7 => "Machregs.X7".to_string(),
            X86Mreg::X8 => "Machregs.X8".to_string(),
            X86Mreg::X9 => "Machregs.X9".to_string(),
            X86Mreg::X10 => "Machregs.X10".to_string(),
            X86Mreg::X11 => "Machregs.X11".to_string(),
            X86Mreg::X12 => "Machregs.X12".to_string(),
            X86Mreg::X13 => "Machregs.X13".to_string(),
            X86Mreg::X14 => "Machregs.X14".to_string(),
            X86Mreg::X15 => "Machregs.X15".to_string(),
            X86Mreg::FP0 => "Machregs.FP0".to_string(),
            X86Mreg::SP => "Machregs.SP".to_string(),
            X86Mreg::Unknown => "Machregs.Unknown".to_string(),
        }
    }
}
