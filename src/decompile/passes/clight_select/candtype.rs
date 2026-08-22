//! The candidate type domain: the type spellings the selector ranks, parsed once into an enum.
//!
//! These values used to live in `FunctionData::var_type_candidates` as strings, with every consumer
//! re-decoding them through its own hand-written string match. The matches had drifted apart:
//! `type_str_sort_priority` tested `int_U32` / `int_U64`, spellings `xtype_to_string` never emits,
//! so `int_I32_unsigned` and `int_I64_unsigned` both fell to its catch-all and ranked below every
//! signed integer; `ptr_ptr_char` had no arm in either the ClightType or the CType decoder and
//! silently became `long`. The candidates are now stored as this enum, so every consumer is a total
//! match and no fallback arm exists to fall into. `from_xtype` is the only encoder; `parse` and
//! `label` exist for the serialized forms (dumps, tests) and have no production decode callers.

use crate::x86::types::XType;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Sign {
    Signed,
    Unsigned,
}

/// One candidate type spelling. Bijective with the strings `xtype_to_string` and `render_type`
/// produce, plus `ptr_void`, which only the candidate padding in `extract_functions` adds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum CandType {
    Void,
    Bool,
    I8(Sign),
    I16(Sign),
    I32(Sign),
    I64(Sign),
    F32,
    F64,
    PtrLong,
    PtrVoid,
    PtrChar,
    PtrCharPtr,
    PtrInt,
    PtrDouble,
    PtrFloat,
    PtrFunc,
    PtrStruct(usize),
}

/// The classes `anchor_index` anchors within; a scalar pointer must never anchor onto a struct
/// pointer, so those are distinct.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CandClass {
    StructPtr,
    Ptr,
    Float,
    Int,
}

impl CandType {
    /// Exact inverse of `label`. None for a spelling outside the domain.
    pub fn parse(s: &str) -> Option<CandType> {
        use Sign::{Signed, Unsigned};
        if let Some(rest) = s.strip_prefix("ptr_struct_") {
            return usize::from_str_radix(rest, 16)
                .ok()
                .map(CandType::PtrStruct);
        }
        Some(match s {
            "void" => CandType::Void,
            "int_IBool" => CandType::Bool,
            "int_I8" => CandType::I8(Signed),
            "int_I8_unsigned" => CandType::I8(Unsigned),
            "int_I16" => CandType::I16(Signed),
            "int_I16_unsigned" => CandType::I16(Unsigned),
            "int_I32" => CandType::I32(Signed),
            "int_I32_unsigned" => CandType::I32(Unsigned),
            "int_I64" => CandType::I64(Signed),
            "int_I64_unsigned" => CandType::I64(Unsigned),
            "float_F32" => CandType::F32,
            "float_F64" => CandType::F64,
            "ptr_I64" => CandType::PtrLong,
            "ptr_void" => CandType::PtrVoid,
            "ptr_char" => CandType::PtrChar,
            "ptr_ptr_char" => CandType::PtrCharPtr,
            "ptr_int" => CandType::PtrInt,
            "ptr_double" => CandType::PtrDouble,
            "ptr_float" => CandType::PtrFloat,
            "ptr_func" => CandType::PtrFunc,
            _ => return None,
        })
    }

    /// The candidate spelling; what lands in `var_type_candidates` and every dump.
    pub fn label(&self) -> String {
        use Sign::Unsigned;
        match self {
            CandType::Void => "void".to_string(),
            CandType::Bool => "int_IBool".to_string(),
            CandType::I8(Unsigned) => "int_I8_unsigned".to_string(),
            CandType::I8(_) => "int_I8".to_string(),
            CandType::I16(Unsigned) => "int_I16_unsigned".to_string(),
            CandType::I16(_) => "int_I16".to_string(),
            CandType::I32(Unsigned) => "int_I32_unsigned".to_string(),
            CandType::I32(_) => "int_I32".to_string(),
            CandType::I64(Unsigned) => "int_I64_unsigned".to_string(),
            CandType::I64(_) => "int_I64".to_string(),
            CandType::F32 => "float_F32".to_string(),
            CandType::F64 => "float_F64".to_string(),
            CandType::PtrLong => "ptr_I64".to_string(),
            CandType::PtrVoid => "ptr_void".to_string(),
            CandType::PtrChar => "ptr_char".to_string(),
            CandType::PtrCharPtr => "ptr_ptr_char".to_string(),
            CandType::PtrInt => "ptr_int".to_string(),
            CandType::PtrDouble => "ptr_double".to_string(),
            CandType::PtrFloat => "ptr_float".to_string(),
            CandType::PtrFunc => "ptr_func".to_string(),
            CandType::PtrStruct(sid) => format!("ptr_struct_{:x}", sid),
        }
    }

    /// The signature type a candidate came from; the only encoder into this domain.
    ///
    /// Two mappings are lossy on purpose and are called out here because they are load-bearing:
    /// `Xany32` / `Xany64` are width-only placeholders that collapse onto their concrete sibling's
    /// spelling (see `xtype_priority`, which keeps the rank distinction the spelling cannot), and
    /// `Xptr` becomes `PtrLong`, so a generic pointer declares `long *` on this path while
    /// `wt_audit::xtype_to_clight` gives the same XType `void *` on the parameter path. That second
    /// divergence predates this module and is not resolved here.
    pub fn from_xtype(xtype: &XType) -> CandType {
        use Sign::{Signed, Unsigned};
        match xtype {
            XType::Xvoid => CandType::Void,
            XType::Xbool => CandType::Bool,
            XType::Xint8signed => CandType::I8(Signed),
            XType::Xint8unsigned => CandType::I8(Unsigned),
            XType::Xint16signed => CandType::I16(Signed),
            XType::Xint16unsigned => CandType::I16(Unsigned),
            XType::Xint | XType::Xany32 => CandType::I32(Signed),
            XType::Xintunsigned => CandType::I32(Unsigned),
            XType::Xlong | XType::Xany64 => CandType::I64(Signed),
            XType::Xlongunsigned => CandType::I64(Unsigned),
            XType::Xfloat => CandType::F64,
            XType::Xsingle => CandType::F32,
            XType::Xptr => CandType::PtrLong,
            XType::Xcharptr => CandType::PtrChar,
            XType::Xcharptrptr => CandType::PtrCharPtr,
            XType::Xintptr => CandType::PtrInt,
            XType::Xfloatptr => CandType::PtrDouble,
            XType::Xsingleptr => CandType::PtrFloat,
            XType::Xfuncptr => CandType::PtrFunc,
            XType::XstructPtr(sid) => CandType::PtrStruct(*sid),
        }
    }

    /// Selection priority, best first: the candidate vector is sorted descending on this, and its
    /// head is both the solver's weight-1 prior and `anchor_index`'s tie-break target. Follows
    /// `xtype_priority`, which the string table claimed to mirror and did not.
    pub fn priority(&self) -> u8 {
        use Sign::Unsigned;
        match self {
            CandType::PtrStruct(_) => 15,
            CandType::PtrFunc => 14,
            CandType::PtrChar | CandType::PtrCharPtr => 13,
            CandType::PtrLong
            | CandType::PtrVoid
            | CandType::PtrInt
            | CandType::PtrDouble
            | CandType::PtrFloat => 12,
            CandType::F32 => 11,
            CandType::F64 => 10,
            CandType::I16(_) => 9,
            CandType::I8(_) => 8,
            CandType::I64(Unsigned) => 7,
            CandType::I64(_) => 6,
            CandType::I32(Unsigned) => 5,
            CandType::I32(_) => 4,
            CandType::Bool => 1,
            CandType::Void => 0,
        }
    }

    /// Bit width, for nearest-width anchoring within a class.
    pub fn width(&self) -> u32 {
        match self {
            CandType::Bool | CandType::I8(_) => 8,
            CandType::I16(_) => 16,
            CandType::I32(_) | CandType::F32 => 32,
            CandType::Void
            | CandType::I64(_)
            | CandType::F64
            | CandType::PtrLong
            | CandType::PtrVoid
            | CandType::PtrChar
            | CandType::PtrCharPtr
            | CandType::PtrInt
            | CandType::PtrDouble
            | CandType::PtrFloat
            | CandType::PtrFunc
            | CandType::PtrStruct(_) => 64,
        }
    }

    pub fn class(&self) -> CandClass {
        match self {
            CandType::PtrStruct(_) => CandClass::StructPtr,
            CandType::PtrLong
            | CandType::PtrVoid
            | CandType::PtrChar
            | CandType::PtrCharPtr
            | CandType::PtrInt
            | CandType::PtrDouble
            | CandType::PtrFloat
            | CandType::PtrFunc => CandClass::Ptr,
            CandType::F32 | CandType::F64 => CandClass::Float,
            CandType::Void
            | CandType::Bool
            | CandType::I8(_)
            | CandType::I16(_)
            | CandType::I32(_)
            | CandType::I64(_) => CandClass::Int,
        }
    }

    pub fn is_pointer(&self) -> bool {
        matches!(self.class(), CandClass::Ptr | CandClass::StructPtr)
    }

    pub fn is_float(&self) -> bool {
        matches!(self.class(), CandClass::Float)
    }

    /// The Int anchoring class, which also holds `void` -- `anchor_index` has always bucketed it
    /// there. Callers that mean "an integer spelling" want `is_integer`.
    pub fn is_int(&self) -> bool {
        matches!(self.class(), CandClass::Int)
    }

    /// An `int_*` spelling: the Int class without `void`.
    pub fn is_integer(&self) -> bool {
        self.is_int() && !matches!(self, CandType::Void)
    }

    /// True for a pointer whose pointee is float-typed. These are pointers, not floats: the
    /// float-axis pruning in the solve must not read them as float evidence.
    pub fn is_float_pointee(&self) -> bool {
        matches!(self, CandType::PtrDouble | CandType::PtrFloat)
    }
}

/// Every variant, with both signs and a representative struct id. Cross-consumer tests walk this
/// so a new variant cannot be added without every decoder being checked against it.
pub fn all_variants() -> Vec<CandType> {
    use Sign::{Signed, Unsigned};
    let mut out = vec![
        CandType::Void,
        CandType::Bool,
        CandType::F32,
        CandType::F64,
        CandType::PtrLong,
        CandType::PtrVoid,
        CandType::PtrChar,
        CandType::PtrCharPtr,
        CandType::PtrInt,
        CandType::PtrDouble,
        CandType::PtrFloat,
        CandType::PtrFunc,
        CandType::PtrStruct(0x2a),
    ];
    for sign in [Signed, Unsigned] {
        out.push(CandType::I8(sign));
        out.push(CandType::I16(sign));
        out.push(CandType::I32(sign));
        out.push(CandType::I64(sign));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn label_parse_roundtrip() {
        for candidate in all_variants() {
            let label = candidate.label();
            assert_eq!(
                CandType::parse(&label),
                Some(candidate),
                "{} did not round-trip",
                label
            );
        }
    }

    // The regression this domain exists to prevent: a spelling the encoder produces that a decoder
    // does not recognize falls to a catch-all and silently changes meaning.
    #[test]
    fn every_xtype_spelling_parses() {
        use strum::IntoEnumIterator;
        for xtype in XType::iter() {
            let candidate = CandType::from_xtype(&xtype);
            assert_eq!(
                CandType::parse(&candidate.label()),
                Some(candidate),
                "from_xtype({:?}) does not round-trip through its spelling",
                xtype
            );
        }
    }

    // Unsigned integer candidates must outrank their signed sibling, which the string table
    // inverted by testing spellings nothing produces.
    #[test]
    fn unsigned_outranks_signed() {
        use Sign::{Signed, Unsigned};
        assert!(CandType::I32(Unsigned).priority() > CandType::I32(Signed).priority());
        assert!(CandType::I64(Unsigned).priority() > CandType::I64(Signed).priority());
        assert_eq!(CandType::I32(Unsigned).priority(), 5);
        assert_eq!(CandType::I64(Unsigned).priority(), 7);
    }

    #[test]
    fn pointee_float_is_not_float() {
        assert!(!CandType::PtrDouble.is_float());
        assert!(CandType::PtrDouble.is_pointer());
        assert!(CandType::PtrDouble.is_float_pointee());
        assert!(CandType::F64.is_float());
    }
}
