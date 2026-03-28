
use crate::x86::asm::{Freg, Ireg};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mreg {
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
impl From<&str> for Mreg {
    fn from(s: &str) -> Self {
        match s.to_uppercase().as_str() {
            "MACHREGS.AX" => Mreg::AX,
            "MACHREGS.BX" => Mreg::BX,
            "MACHREGS.CX" => Mreg::CX,
            "MACHREGS.DX" => Mreg::DX,
            "MACHREGS.SI" => Mreg::SI,
            "MACHREGS.DI" => Mreg::DI,
            "MACHREGS.BP" => Mreg::BP,
            "MACHREGS.R8" => Mreg::R8,
            "MACHREGS.R9" => Mreg::R9,
            "MACHREGS.R10" => Mreg::R10,
            "MACHREGS.R11" => Mreg::R11,
            "MACHREGS.R12" => Mreg::R12,
            "MACHREGS.R13" => Mreg::R13,
            "MACHREGS.R14" => Mreg::R14,
            "MACHREGS.R15" => Mreg::R15,
            "MACHREGS.X0" => Mreg::X0,
            "MACHREGS.X1" => Mreg::X1,
            "MACHREGS.X2" => Mreg::X2,
            "MACHREGS.X3" => Mreg::X3,
            "MACHREGS.X4" => Mreg::X4,
            "MACHREGS.X5" => Mreg::X5,
            "MACHREGS.X6" => Mreg::X6,
            "MACHREGS.X7" => Mreg::X7,
            "MACHREGS.X8" => Mreg::X8,
            "MACHREGS.X9" => Mreg::X9,
            "MACHREGS.X10" => Mreg::X10,
            "MACHREGS.X11" => Mreg::X11,
            "MACHREGS.X12" => Mreg::X12,
            "MACHREGS.X13" => Mreg::X13,
            "MACHREGS.X14" => Mreg::X14,
            "MACHREGS.X15" => Mreg::X15,
            "MACHREGS.FP0" => Mreg::FP0,
            "RAX" | "EAX" | "AX" | "AL" | "AH" => Mreg::AX,
            "RBX" | "EBX" | "BX" | "BL" | "BH" => Mreg::BX,
            "RCX" | "ECX" | "CX" | "CL" | "CH" => Mreg::CX,
            "RDX" | "EDX" | "DX" | "DL" | "DH" => Mreg::DX,
            "RSI" | "ESI" | "SI" | "SIL" => Mreg::SI,
            "RDI" | "EDI" | "DI" | "DIL" => Mreg::DI,
            "RBP" | "EBP" | "BP" | "BPL" => Mreg::BP,
            "RSP" | "ESP" | "SP" | "SPL" => Mreg::SP,

            "R8" | "R8D" | "R8W" | "R8B" => Mreg::R8,
            "R9" | "R9D" | "R9W" | "R9B" => Mreg::R9,
            "R10" | "R10D" | "R10W" | "R10B" => Mreg::R10,
            "R11" | "R11D" | "R11W" | "R11B" => Mreg::R11,
            "R12" | "R12D" | "R12W" | "R12B" => Mreg::R12,
            "R13" | "R13D" | "R13W" | "R13B" => Mreg::R13,
            "R14" | "R14D" | "R14W" | "R14B" => Mreg::R14,
            "R15" | "R15D" | "R15W" | "R15B" => Mreg::R15,

            "XMM0" | "X0" => Mreg::X0,
            "XMM1" | "X1" => Mreg::X1,
            "XMM2" | "X2" => Mreg::X2,
            "XMM3" | "X3" => Mreg::X3,
            "XMM4" | "X4" => Mreg::X4,
            "XMM5" | "X5" => Mreg::X5,
            "XMM6" | "X6" => Mreg::X6,
            "XMM7" | "X7" => Mreg::X7,
            "XMM8" | "X8" => Mreg::X8,
            "XMM9" | "X9" => Mreg::X9,
            "XMM10" | "X10" => Mreg::X10,
            "XMM11" | "X11" => Mreg::X11,
            "XMM12" | "X12" => Mreg::X12,
            "XMM13" | "X13" => Mreg::X13,
            "XMM14" | "X14" => Mreg::X14,
            "XMM15" | "X15" => Mreg::X15,
            "FP0" => Mreg::FP0,
            _ => Mreg::Unknown,
        }
    }
}

impl From<String> for Mreg {
    fn from(s: String) -> Self {
        Mreg::from(s.as_str())
    }
}

impl From<&&str> for Mreg {
    fn from(s: &&str) -> Self {
        Mreg::from(*s)
    }
}

impl From<Ireg> for Mreg {
    fn from(ireg: Ireg) -> Self {
        match ireg {
            Ireg::RAX => Mreg::AX,
            Ireg::RBX => Mreg::BX,
            Ireg::RCX => Mreg::CX,
            Ireg::RDX => Mreg::DX,
            Ireg::RSI => Mreg::SI,
            Ireg::RDI => Mreg::DI,
            Ireg::RBP => Mreg::BP,
            Ireg::RSP => Mreg::SP,
            Ireg::R8 => Mreg::R8,
            Ireg::R9 => Mreg::R9,
            Ireg::R10 => Mreg::R10,
            Ireg::R11 => Mreg::R11,
            Ireg::R12 => Mreg::R12,
            Ireg::R13 => Mreg::R13,
            Ireg::R14 => Mreg::R14,
            Ireg::R15 => Mreg::R15,
            Ireg::RIP => Mreg::Unknown,
            Ireg::Unknown => Mreg::Unknown,
        }
    }
}

impl From<Freg> for Mreg {
    fn from(freg: Freg) -> Self {
        match freg {
            Freg::XMM0 => Mreg::X0,
            Freg::XMM1 => Mreg::X1,
            Freg::XMM2 => Mreg::X2,
            Freg::XMM3 => Mreg::X3,
            Freg::XMM4 => Mreg::X4,
            Freg::XMM5 => Mreg::X5,
            Freg::XMM6 => Mreg::X6,
            Freg::XMM7 => Mreg::X7,
            Freg::XMM8 => Mreg::X8,
            Freg::XMM9 => Mreg::X9,
            Freg::XMM10 => Mreg::X10,
            Freg::XMM11 => Mreg::X11,
            Freg::XMM12 => Mreg::X12,
            Freg::XMM13 => Mreg::X13,
            Freg::XMM14 => Mreg::X14,
            Freg::XMM15 => Mreg::X15,
            Freg::Unknown => Mreg::Unknown,
        }
    }
}

impl PartialOrd for Mreg {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Mreg {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (*self as u32).cmp(&(*other as u32))
    }
}

impl ToString for Mreg {
    fn to_string(&self) -> String {
        match self {
            Mreg::AX => "Machregs.AX".to_string(),
            Mreg::BX => "Machregs.BX".to_string(),
            Mreg::CX => "Machregs.CX".to_string(),
            Mreg::DX => "Machregs.DX".to_string(),
            Mreg::SI => "Machregs.SI".to_string(),
            Mreg::DI => "Machregs.DI".to_string(),
            Mreg::BP => "Machregs.BP".to_string(),
            Mreg::R8 => "Machregs.R8".to_string(),
            Mreg::R9 => "Machregs.R9".to_string(),
            Mreg::R10 => "Machregs.R10".to_string(),
            Mreg::R11 => "Machregs.R11".to_string(),
            Mreg::R12 => "Machregs.R12".to_string(),
            Mreg::R13 => "Machregs.R13".to_string(),
            Mreg::R14 => "Machregs.R14".to_string(),
            Mreg::R15 => "Machregs.R15".to_string(),
            Mreg::X0 => "Machregs.X0".to_string(),
            Mreg::X1 => "Machregs.X1".to_string(),
            Mreg::X2 => "Machregs.X2".to_string(),
            Mreg::X3 => "Machregs.X3".to_string(),
            Mreg::X4 => "Machregs.X4".to_string(),
            Mreg::X5 => "Machregs.X5".to_string(),
            Mreg::X6 => "Machregs.X6".to_string(),
            Mreg::X7 => "Machregs.X7".to_string(),
            Mreg::X8 => "Machregs.X8".to_string(),
            Mreg::X9 => "Machregs.X9".to_string(),
            Mreg::X10 => "Machregs.X10".to_string(),
            Mreg::X11 => "Machregs.X11".to_string(),
            Mreg::X12 => "Machregs.X12".to_string(),
            Mreg::X13 => "Machregs.X13".to_string(),
            Mreg::X14 => "Machregs.X14".to_string(),
            Mreg::X15 => "Machregs.X15".to_string(),
            Mreg::FP0 => "Machregs.FP0".to_string(),
            Mreg::SP => "Machregs.SP".to_string(),
            Mreg::Unknown => "Machregs.Unknown".to_string(),
        }
    }
}
