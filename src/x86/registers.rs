use crate::x86::asm::{Freg, Ireg};
use crate::x86::types::Operand;

impl From<Operand> for Ireg {
    fn from(op: Operand) -> Self {
        match op {
            Operand::Register(reg) => Ireg::from(reg.to_string()),
            Operand::Memory(base, offset) => {
                if offset == "0" {
                    return Ireg::from(*base);
                } else {
                    panic!("Offset is not zero: {}", offset);
                }
            }
            _ => panic!("Not a register {:#?}", op),
        }
    }
}

impl From<Operand> for Freg {
    fn from(op: Operand) -> Self {
        match op {
            Operand::Register(reg) => match &reg[..] {
                "%xmm0" | "%ymm0" => Freg::XMM0,
                "%xmm1" | "%ymm1" => Freg::XMM1,
                "%xmm2" | "%ymm2" => Freg::XMM2,
                "%xmm3" | "%ymm3" => Freg::XMM3,
                "%xmm4" | "%ymm4" => Freg::XMM4,
                "%xmm5" | "%ymm5" => Freg::XMM5,
                "%xmm6" | "%ymm6" => Freg::XMM6,
                "%xmm7" | "%ymm7" => Freg::XMM7,
                "%xmm8" | "%ymm8" => Freg::XMM8,
                "%xmm9" | "%ymm9" => Freg::XMM9,
                "%xmm10" | "%ymm10" => Freg::XMM10,
                "%xmm11" | "%ymm11" => Freg::XMM11,
                "%xmm12" | "%ymm12" => Freg::XMM12,
                "%xmm13" | "%ymm13" => Freg::XMM13,
                "%xmm14" | "%ymm14" => Freg::XMM14,
                "%xmm15" | "%ymm15" => Freg::XMM15,
                _ => panic!("Unknown register: {}", reg),
            },
            _ => panic!("Not a register"),
        }
    }
}
