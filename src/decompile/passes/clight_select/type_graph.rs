//! Structural type terms and role-separated evidence, independent of corpus
//! labels and candidate-ranking policy. A storage access is not an allocation
//! extent, and a register carrier is not a source-language declaration.

use crate::abi::DataModel;
use crate::decompile::passes::c_pass::types::{
    CType, FloatSize, IntSize, Signedness, TypeQualifiers,
};
use crate::decompile::passes::clight_select::candtype::{CandType, Sign};
use crate::x86::types::*;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeTerm {
    Void,
    Bool,
    Integer(IntSize, Sign),
    Float(u16),
    Pointer(Arc<TypeTerm>),
    Array(Arc<TypeTerm>, Option<usize>),
    Record {
        union: bool,
        id: usize,
    },
    Function {
        result: Arc<TypeTerm>,
        arguments: Vec<TypeTerm>,
        variadic: bool,
        unprototyped: bool,
    },
}

impl TypeTerm {
    pub fn pointer(self) -> Self {
        Self::Pointer(Arc::new(self))
    }
    pub fn integer(bits: u32, sign: Sign, model: DataModel) -> Option<Self> {
        Some(Self::Integer(
            match bits {
                8 => IntSize::Char,
                16 => IntSize::Short,
                32 => IntSize::Int,
                64 if model.long_size() == 8 => IntSize::Long,
                64 => IntSize::LongLong,
                128 => IntSize::Int128,
                _ => return None,
            },
            sign,
        ))
    }
    pub fn from_candidate(candidate: CandType, model: DataModel) -> Self {
        let ty = crate::decompile::passes::c_pass::helpers::candtype_to_ctype(candidate, model);
        Self::from_c(&ty, model).expect("candidate has a structural type")
    }
    pub fn from_c(ty: &CType, model: DataModel) -> Option<Self> {
        Some(match ty {
            CType::Void => Self::Void,
            CType::Bool => Self::Bool,
            CType::Int(size, sign) => Self::Integer(
                *size,
                if *sign == Signedness::Unsigned {
                    Sign::Unsigned
                } else {
                    Sign::Signed
                },
            ),
            CType::Float(FloatSize::Float) => Self::Float(32),
            CType::Float(FloatSize::Double) => Self::Float(64),
            CType::Pointer(inner, q) if *q == TypeQualifiers::none() => {
                Self::from_c(inner, model)?.pointer()
            }
            CType::Array(inner, count) => {
                Self::Array(Arc::new(Self::from_c(inner, model)?), *count)
            }
            CType::Struct(name) => Self::Record {
                union: false,
                id: usize::from_str_radix(name.strip_prefix("struct_")?, 16).ok()?,
            },
            CType::Union(name) => Self::Record {
                union: true,
                id: name.strip_prefix("union_")?.parse().ok()?,
            },
            CType::Function(result, arguments, variadic, unprototyped) => Self::Function {
                result: Arc::new(Self::from_c(result, model)?),
                arguments: arguments
                    .iter()
                    .map(|t| Self::from_c(t, model))
                    .collect::<Option<_>>()?,
                variadic: *variadic,
                unprototyped: *unprototyped,
            },
            // Qualifiers are not erased from a commitment: unsupported shapes
            // retain their existing declaration instead of acquiring a guess.
            _ => return None,
        })
    }
    pub fn to_c(&self, model: DataModel) -> CType {
        match self {
            Self::Void => CType::Void,
            Self::Bool => CType::Bool,
            Self::Integer(size, sign) => CType::Int(
                *size,
                if *sign == Sign::Unsigned {
                    Signedness::Unsigned
                } else {
                    Signedness::Signed
                },
            ),
            Self::Float(32) => CType::Float(FloatSize::Float),
            Self::Float(64) => CType::Float(FloatSize::Double),
            Self::Float(_) => unreachable!("unsupported floating type width"),
            Self::Pointer(inner) => {
                CType::Pointer(Box::new(inner.to_c(model)), TypeQualifiers::none())
            }
            Self::Array(inner, count) => CType::Array(Box::new(inner.to_c(model)), *count),
            Self::Record { union: false, id } => CType::Struct(format!("struct_{id:x}")),
            Self::Record { union: true, id } => CType::Union(format!("union_{id}")),
            Self::Function {
                result,
                arguments,
                variadic,
                unprototyped,
            } => CType::Function(
                Box::new(result.to_c(model)),
                arguments.iter().map(|t| t.to_c(model)).collect(),
                *variadic,
                *unprototyped,
            ),
        }
    }
    pub fn to_clight(&self, model: DataModel) -> ClightType {
        let attr = ClightAttr::default();
        let signed = |s| {
            if s == Sign::Unsigned {
                ClightSignedness::Unsigned
            } else {
                ClightSignedness::Signed
            }
        };
        match self {
            Self::Void => ClightType::Tvoid,
            Self::Bool => ClightType::Tint(ClightIntSize::IBool, ClightSignedness::Unsigned, attr),
            Self::Integer(_, s) => match self.object_bytes(model).unwrap() {
                1 => ClightType::Tint(ClightIntSize::I8, signed(*s), attr),
                2 => ClightType::Tint(ClightIntSize::I16, signed(*s), attr),
                4 => ClightType::Tint(ClightIntSize::I32, signed(*s), attr),
                8 => ClightType::Tlong(signed(*s), attr),
                16 => ClightType::Tint128(signed(*s), attr),
                _ => unreachable!("unsupported integer type width"),
            },
            Self::Float(32) => ClightType::Tfloat(ClightFloatSize::F32, attr),
            Self::Float(64) => ClightType::Tfloat(ClightFloatSize::F64, attr),
            Self::Float(_) => unreachable!("unsupported floating type width"),
            Self::Pointer(inner) => ClightType::Tpointer(Arc::new(inner.to_clight(model)), attr),
            Self::Array(inner, count) => ClightType::Tarray(
                Arc::new(inner.to_clight(model)),
                count.unwrap_or(0) as i64,
                attr,
            ),
            Self::Record { union: false, id } => ClightType::Tstruct(*id, attr),
            Self::Record { union: true, id } => ClightType::Tunion(*id, attr),
            Self::Function {
                result,
                arguments,
                variadic,
                unprototyped,
            } => ClightType::Tfunction(
                Arc::new(arguments.iter().map(|t| t.to_clight(model)).collect()),
                Arc::new(result.to_clight(model)),
                CallConv {
                    varargs: if *variadic {
                        Some(arguments.len() as i64)
                    } else {
                        None
                    },
                    unproto: *unprototyped,
                    ..CallConv::default()
                },
            ),
        }
    }
    pub fn is_integer(&self) -> bool {
        matches!(self, Self::Bool | Self::Integer(..))
    }
    pub fn is_pointer(&self) -> bool {
        matches!(self, Self::Pointer(_))
    }
    pub fn object_bytes(&self, model: DataModel) -> Option<usize> {
        match self {
            Self::Bool => Some(1),
            Self::Integer(size, _) => Some(match size {
                IntSize::Char => 1,
                IntSize::Short => 2,
                IntSize::Int => 4,
                IntSize::Long => model.long_size(),
                IntSize::LongLong => 8,
                IntSize::Int128 => 16,
            }),
            Self::Float(bits) => Some(*bits as usize / 8),
            Self::Pointer(_) => Some(model.pointer_size()),
            Self::Array(t, Some(n)) => t.object_bytes(model)?.checked_mul(*n),
            _ => None,
        }
    }
    /// Compatibility adapter only. New structural types keep an exact term
    /// even when the legacy candidate vocabulary cannot encode them.
    pub fn legacy_candidate(&self, model: DataModel) -> Option<CandType> {
        let candidates = [
            CandType::Void,
            CandType::Bool,
            CandType::I8(Sign::Signed),
            CandType::I8(Sign::Unsigned),
            CandType::I16(Sign::Signed),
            CandType::I16(Sign::Unsigned),
            CandType::I32(Sign::Signed),
            CandType::I32(Sign::Unsigned),
            CandType::I64(Sign::Signed),
            CandType::I64(Sign::Unsigned),
            CandType::F32,
            CandType::F64,
            CandType::PtrLong,
            CandType::PtrVoid,
            CandType::PtrChar,
            CandType::PtrCharPtr,
            CandType::PtrInt,
            CandType::PtrFloat,
            CandType::PtrDouble,
            CandType::PtrFunc,
        ];
        if let Self::Pointer(inner) = self {
            if let Self::Record { union: false, id } = inner.as_ref() {
                return Some(CandType::PtrStruct(*id));
            }
        }
        candidates
            .into_iter()
            .find(|c| Self::from_candidate(*c, model) == *self)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeId(pub usize);

/// Admission scope, deliberately distinct from evidence of an original type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeAdmission {
    LegacyFallback,
    EvidenceSupported,
    ValueAndDefinedness,
    ExplicitPointerViews,
}

#[derive(Clone, Debug, Default)]
pub struct TypeArena {
    nodes: Vec<TypeTerm>,
    index: BTreeMap<TypeTerm, TypeId>,
}
impl TypeArena {
    pub fn intern(&mut self, term: TypeTerm) -> TypeId {
        if let Some(id) = self.index.get(&term) {
            return *id;
        }
        let id = TypeId(self.nodes.len());
        self.nodes.push(term.clone());
        self.index.insert(term, id);
        id
    }
    pub fn get(&self, id: TypeId) -> &TypeTerm {
        &self.nodes[id.0]
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Entity {
    Storage(RTLReg),
    Value(RTLReg),
    Access(Node, RTLReg, i64, bool),
    Parameter(usize),
    Return,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Fact {
    Definition {
        node: Node,
        value: RTLReg,
    },
    Access {
        object: RTLReg,
        node: Node,
        offset: i64,
        write: bool,
        chunk: MemoryChunk,
    },
    PointerAccess {
        node: Node,
        base: RTLReg,
        offset: i64,
        write: bool,
        chunk: MemoryChunk,
    },
    Carrier {
        node: Node,
        value: RTLReg,
        bits: u32,
    },
    ValueHint {
        value: RTLReg,
        ty: TypeTerm,
    },
    Interface {
        parameter: Option<usize>,
        value: Option<RTLReg>,
        ty: TypeTerm,
    },
    Layout {
        object: RTLReg,
        ty: TypeTerm,
    },
}
#[derive(Clone, Debug, Default)]
pub struct EvidenceGraph {
    pub entities: BTreeSet<Entity>,
    pub facts: BTreeSet<Fact>,
    pub hypotheses: BTreeMap<RTLReg, BTreeSet<TypeTerm>>,
    pub unknown_storage: BTreeSet<RTLReg>,
    pub unknown_values: BTreeSet<RTLReg>,
    pub fixed: BTreeSet<RTLReg>,
    pub fixed_storage: BTreeSet<RTLReg>,
}

#[cfg(test)]
mod tests {
    use crate::decompile::passes::clight_select::type_graph::*;
    #[test]
    fn recursive_pointer_and_array_terms_do_not_need_spelling_variants() {
        let term = TypeTerm::Array(
            Arc::new(TypeTerm::Integer(IntSize::Short, Sign::Unsigned)),
            Some(7),
        )
        .pointer()
        .pointer();
        assert_eq!(
            TypeTerm::from_c(&term.to_c(DataModel::Lp64), DataModel::Lp64),
            Some(term.clone())
        );
        assert!(term.legacy_candidate(DataModel::Lp64).is_none());
        let mut arena = TypeArena::default();
        let first = arena.intern(term.clone());
        assert_eq!(first, arena.intern(term));
    }
    #[test]
    fn storage_and_value_identities_are_distinct_even_for_the_same_register() {
        assert_ne!(Entity::Storage(17), Entity::Value(17));
        assert_eq!(TypeTerm::Bool.object_bytes(DataModel::Lp64), Some(1));
        assert_eq!(
            TypeTerm::Integer(IntSize::Int, Sign::Signed).object_bytes(DataModel::Lp64),
            Some(4)
        );
    }
}
