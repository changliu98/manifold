// Unified cross-arch machine register: the wrapping variant keeps the two register files apart, since x86's X0..X15 (XMM) collide by name with AArch64's GP X0..X30.

use crate::aarch64::mach::A64Mreg;
use crate::arm32::mach::A32Mreg;
use crate::x86::mach::X86Mreg;

// Derived Ord orders X86 < A64 < A32 < Unknown and preserves the old flat-enum x86 order, which clight_select's tie-breaking depends on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Mreg {
    X86(X86Mreg),
    A64(A64Mreg),
    A32(A32Mreg),
    Unknown,
}

/// The register file a machine register belongs to. Every ISA here splits its
/// registers into an integer/address file and a floating/vector file, and the
/// split is architectural: a value the machine keeps in a GPR is an integer or
/// a pointer, never a float, whatever a width-based type guess suggests.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum RegClass {
    Gpr,
    Fp,
}

impl Mreg {
    /// Build an x86 register from a capstone name, a "Machregs.*" string, an Ireg or an Freg; unparseable inputs normalize to the single Mreg::Unknown so caller guards cannot be slipped past.
    pub fn x86<T: Into<X86Mreg>>(v: T) -> Mreg {
        match v.into() {
            X86Mreg::Unknown => Mreg::Unknown,
            r => Mreg::X86(r),
        }
    }

    /// Build an AArch64 register. Normalizes unknowns exactly as `x86` does.
    pub fn a64<T: Into<A64Mreg>>(v: T) -> Mreg {
        match v.into() {
            A64Mreg::Unknown => Mreg::Unknown,
            r => Mreg::A64(r),
        }
    }

    /// Build an ARM32 register. Normalizes unknowns exactly as `x86` does.
    pub fn a32<T: Into<A32Mreg>>(v: T) -> Mreg {
        match v.into() {
            A32Mreg::Unknown => Mreg::Unknown,
            r => Mreg::A32(r),
        }
    }

    /// True for the unknown register in any spelling, so a directly-constructed inner-Unknown cannot be missed.
    pub fn is_unknown(&self) -> bool {
        matches!(
            self,
            Mreg::Unknown
                | Mreg::X86(X86Mreg::Unknown)
                | Mreg::A64(A64Mreg::Unknown)
                | Mreg::A32(A32Mreg::Unknown)
        )
    }

    /// Register file this register belongs to. `None` only for the unknown
    /// register, which is evidence of nothing. x87's FP0 counts as floating
    /// even though it is not an XMM register, and SP / ZR count as general
    /// purpose, so no caller can mistake either for the absence of a class.
    pub fn reg_class(&self) -> Option<RegClass> {
        match self {
            Mreg::X86(X86Mreg::Unknown)
            | Mreg::A64(A64Mreg::Unknown)
            | Mreg::A32(A32Mreg::Unknown) => None,
            Mreg::Unknown => None,
            Mreg::X86(r) => {
                if r.is_xmm() || matches!(r, X86Mreg::FP0) {
                    Some(RegClass::Fp)
                } else {
                    Some(RegClass::Gpr)
                }
            }
            Mreg::A64(r) => {
                if r.is_vec() {
                    Some(RegClass::Fp)
                } else {
                    Some(RegClass::Gpr)
                }
            }
            Mreg::A32(r) => {
                if r.is_vec() {
                    Some(RegClass::Fp)
                } else {
                    Some(RegClass::Gpr)
                }
            }
        }
    }

    pub fn is_stack_pointer(&self) -> bool {
        matches!(
            self,
            Mreg::X86(X86Mreg::SP) | Mreg::A64(A64Mreg::SP) | Mreg::A32(A32Mreg::SP)
        )
    }

    pub fn as_x86(&self) -> Option<X86Mreg> {
        match self {
            Mreg::X86(r) => Some(*r),
            _ => None,
        }
    }

    pub fn as_a64(&self) -> Option<A64Mreg> {
        match self {
            Mreg::A64(r) => Some(*r),
            _ => None,
        }
    }

    pub fn as_a32(&self) -> Option<A32Mreg> {
        match self {
            Mreg::A32(r) => Some(*r),
            _ => None,
        }
    }

    // x86 aliases: expression-position sugar for the existing x86 rules, usable in patterns since all three enums derive Eq.
    pub const AX: Mreg = Mreg::X86(X86Mreg::AX);
    pub const BX: Mreg = Mreg::X86(X86Mreg::BX);
    pub const CX: Mreg = Mreg::X86(X86Mreg::CX);
    pub const DX: Mreg = Mreg::X86(X86Mreg::DX);
    pub const SI: Mreg = Mreg::X86(X86Mreg::SI);
    pub const DI: Mreg = Mreg::X86(X86Mreg::DI);
    pub const BP: Mreg = Mreg::X86(X86Mreg::BP);
    pub const R8: Mreg = Mreg::X86(X86Mreg::R8);
    pub const R9: Mreg = Mreg::X86(X86Mreg::R9);
    pub const R10: Mreg = Mreg::X86(X86Mreg::R10);
    pub const R11: Mreg = Mreg::X86(X86Mreg::R11);
    pub const R12: Mreg = Mreg::X86(X86Mreg::R12);
    pub const R13: Mreg = Mreg::X86(X86Mreg::R13);
    pub const R14: Mreg = Mreg::X86(X86Mreg::R14);
    pub const R15: Mreg = Mreg::X86(X86Mreg::R15);
    pub const X0: Mreg = Mreg::X86(X86Mreg::X0);
    pub const X1: Mreg = Mreg::X86(X86Mreg::X1);
    pub const X2: Mreg = Mreg::X86(X86Mreg::X2);
    pub const X3: Mreg = Mreg::X86(X86Mreg::X3);
    pub const X4: Mreg = Mreg::X86(X86Mreg::X4);
    pub const X5: Mreg = Mreg::X86(X86Mreg::X5);
    pub const X6: Mreg = Mreg::X86(X86Mreg::X6);
    pub const X7: Mreg = Mreg::X86(X86Mreg::X7);
    pub const X8: Mreg = Mreg::X86(X86Mreg::X8);
    pub const X9: Mreg = Mreg::X86(X86Mreg::X9);
    pub const X10: Mreg = Mreg::X86(X86Mreg::X10);
    pub const X11: Mreg = Mreg::X86(X86Mreg::X11);
    pub const X12: Mreg = Mreg::X86(X86Mreg::X12);
    pub const X13: Mreg = Mreg::X86(X86Mreg::X13);
    pub const X14: Mreg = Mreg::X86(X86Mreg::X14);
    pub const X15: Mreg = Mreg::X86(X86Mreg::X15);
    pub const FP0: Mreg = Mreg::X86(X86Mreg::FP0);
    pub const SP: Mreg = Mreg::X86(X86Mreg::SP);
}

impl From<X86Mreg> for Mreg {
    fn from(r: X86Mreg) -> Mreg {
        Mreg::x86(r)
    }
}

// The x86 Asm layer converts its own register types straight into Mreg via `.into()`.
impl From<crate::x86::asm::Ireg> for Mreg {
    fn from(r: crate::x86::asm::Ireg) -> Mreg {
        Mreg::x86(r)
    }
}

impl From<crate::x86::asm::Freg> for Mreg {
    fn from(r: crate::x86::asm::Freg) -> Mreg {
        Mreg::x86(r)
    }
}

impl From<A64Mreg> for Mreg {
    fn from(r: A64Mreg) -> Mreg {
        Mreg::a64(r)
    }
}

impl From<A32Mreg> for Mreg {
    fn from(r: A32Mreg) -> Mreg {
        Mreg::a32(r)
    }
}

impl ToString for Mreg {
    fn to_string(&self) -> String {
        match self {
            Mreg::X86(r) => r.to_string(),
            Mreg::A64(r) => r.to_string(),
            Mreg::A32(r) => r.to_string(),
            Mreg::Unknown => "Machregs.Unknown".to_string(),
        }
    }
}
