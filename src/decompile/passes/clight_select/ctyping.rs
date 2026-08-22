#![allow(dead_code)] // consumed incrementally from P2 (wt audit) onward; see CTYPING_PLAN.md

//! Executable CompCert C-frontend type checker over the Clight AST, transcribed from Ctypes.v/Cop.v/Ctyping.v with arm ORDER preserved; two deviations lean toward gcc.
//!
//! CompCert's Archi.ptr64 is a module constant; here it is a `ptr64` parameter threaded from the target ABI, so one process can check both widths (cf. DecompileDB::target_abi). Only classify_cast, classify_bool and ptrdiff_t branch on it; classify_sub/classify_cmp do not (their ptr64 uses are in sem_sub/cmp_ptr, the semantics, not the classification).

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::x86::types::{
    CallConv, ClightAttr, ClightBinaryOp, ClightExpr, ClightFloatSize, ClightIntSize,
    ClightSignedness, ClightStmt, ClightType, ClightUnaryOp, Ident,
};

use ClightFloatSize::{F32, F64};
use ClightIntSize::{IBool, I16, I32, I8};
use ClightSignedness::{Signed, Unsigned};

// 1.1 Type utilities (Ctypes.v)

pub fn type_int32s() -> ClightType {
    ClightType::Tint(I32, Signed, ClightAttr::default())
}

/// Ctyping.v:33 ptrdiff_t: signed long on ptr64, signed int on ptr32.
pub fn ptrdiff_t(ptr64: bool) -> ClightType {
    if ptr64 {
        ClightType::Tlong(Signed, ClightAttr::default())
    } else {
        ClightType::Tint(I32, Signed, ClightAttr::default())
    }
}

/// Top-level attribute erasure (Ctypes.v remove_attributes).
pub fn remove_attributes(ty: &ClightType) -> ClightType {
    use ClightType::*;
    let a = ClightAttr::default;
    match ty {
        Tvoid => Tvoid,
        Tint(sz, sg, _) => Tint(*sz, *sg, a()),
        Tlong(sg, _) => Tlong(*sg, a()),
        Tint128(sg, _) => Tint128(*sg, a()),
        Tfloat(fs, _) => Tfloat(*fs, a()),
        Tpointer(t, _) => Tpointer(t.clone(), a()),
        Tarray(t, n, _) => Tarray(t.clone(), *n, a()),
        Tfunction(args, res, cc) => Tfunction(args.clone(), res.clone(), *cc),
        Tstruct(id, _) => Tstruct(*id, a()),
        Tunion(id, _) => Tunion(*id, a()),
    }
}

/// Deep attribute erasure, for attr-insensitive structural equality (D4: attrs are ignored throughout).
pub fn erase_attrs(ty: &ClightType) -> ClightType {
    use ClightType::*;
    let a = ClightAttr::default;
    match ty {
        Tvoid => Tvoid,
        Tint(sz, sg, _) => Tint(*sz, *sg, a()),
        Tlong(sg, _) => Tlong(*sg, a()),
        Tint128(sg, _) => Tint128(*sg, a()),
        Tfloat(fs, _) => Tfloat(*fs, a()),
        Tpointer(t, _) => Tpointer(Arc::new(erase_attrs(t)), a()),
        Tarray(t, n, _) => Tarray(Arc::new(erase_attrs(t)), *n, a()),
        Tfunction(args, res, cc) => Tfunction(
            Arc::new(args.iter().map(erase_attrs).collect()),
            Arc::new(erase_attrs(res)),
            *cc,
        ),
        Tstruct(id, _) => Tstruct(*id, a()),
        Tunion(id, _) => Tunion(*id, a()),
    }
}

/// The usual unary conversion (Ctypes.v:266 typeconv): small ints promote to signed int32; arrays and functions decay to pointers; attributes erased.
pub fn typeconv(ty: &ClightType) -> ClightType {
    use ClightType::*;
    match ty {
        Tint(I8 | I16 | IBool, _, _) => type_int32s(),
        Tarray(t, _, _) => Tpointer(t.clone(), ClightAttr::default()),
        Tfunction(..) => Tpointer(Arc::new(ty.clone()), ClightAttr::default()),
        _ => remove_attributes(ty),
    }
}

/// Ctyping.v:181 type_combine -- the merge of two types when both sides must agree (conditional arms). None = incompatible. Attr-insensitive per D4; calling-convention combine reduced to equality of the vararg shape.
pub fn type_combine(t1: &ClightType, t2: &ClightType) -> Option<ClightType> {
    use ClightType::*;
    match (t1, t2) {
        (Tvoid, Tvoid) => Some(Tvoid),
        (Tint(sz1, sg1, _), Tint(sz2, sg2, _)) if sz1 == sz2 && sg1 == sg2 => {
            Some(Tint(*sz1, *sg1, ClightAttr::default()))
        }
        (Tlong(sg1, _), Tlong(sg2, _)) if sg1 == sg2 => Some(Tlong(*sg1, ClightAttr::default())),
        (Tfloat(fs1, _), Tfloat(fs2, _)) if fs1 == fs2 => Some(Tfloat(*fs1, ClightAttr::default())),
        (Tpointer(p1, _), Tpointer(p2, _)) => Some(Tpointer(
            Arc::new(type_combine(p1, p2)?),
            ClightAttr::default(),
        )),
        (Tarray(e1, n1, _), Tarray(e2, n2, _)) if n1 == n2 => Some(Tarray(
            Arc::new(type_combine(e1, e2)?),
            *n1,
            ClightAttr::default(),
        )),
        (Tfunction(a1, r1, cc1), Tfunction(a2, r2, cc2)) => {
            let res = type_combine(r1, r2)?;
            let args = if cc1.unproto {
                a2.as_ref().clone()
            } else if cc2.unproto {
                a1.as_ref().clone()
            } else {
                if a1.len() != a2.len() {
                    return None;
                }
                a1.iter()
                    .zip(a2.iter())
                    .map(|(x, y)| type_combine(x, y))
                    .collect::<Option<Vec<_>>>()?
            };
            if cc1.varargs != cc2.varargs {
                return None;
            }
            Some(Tfunction(Arc::new(args), Arc::new(res), *cc1))
        }
        (Tstruct(id1, _), Tstruct(id2, _)) if id1 == id2 => {
            Some(Tstruct(*id1, ClightAttr::default()))
        }
        (Tunion(id1, _), Tunion(id2, _)) if id1 == id2 => Some(Tunion(*id1, ClightAttr::default())),
        _ => None,
    }
}

fn is_void(ty: &ClightType) -> bool {
    matches!(ty, ClightType::Tvoid)
}

fn is_float(ty: &ClightType) -> bool {
    matches!(ty, ClightType::Tfloat(..))
}

/// Pointer-shaped after decay: pointers, arrays, functions.
fn is_pointerish(ty: &ClightType) -> bool {
    matches!(
        ty,
        ClightType::Tpointer(..) | ClightType::Tarray(..) | ClightType::Tfunction(..)
    )
}

// 1.2 Classification tables (Cop.v)

/// Cop.v:103 classify_cast. Payloads elided except the struct/union id agreement, which wt_cast consumes (gcc deviation: CompCert defers mismatched-id failure to sem_cast; gcc rejects statically).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CastCase {
    Pointer,
    I2I,
    F2F,
    S2S,
    F2S,
    S2F,
    I2F,
    I2S,
    F2I,
    S2I,
    L2L,
    I2L,
    L2I,
    L2F,
    L2S,
    F2L,
    S2L,
    I2Bool,
    L2Bool,
    F2Bool,
    S2Bool,
    Struct { same_id: bool },
    Union { same_id: bool },
    Void,
    Default,
}

pub fn classify_cast(ptr64: bool, tfrom: &ClightType, tto: &ClightType) -> CastCase {
    use CastCase::*;
    use ClightType::*;
    match (tto, tfrom) {
        // To void
        (Tvoid, _) => Void,
        // To int
        (Tint(sz2, _, _), Tint(..)) => match sz2 {
            IBool => I2Bool,
            // On ptr32 an I32 is pointer-width, so the cast is a no-op reinterpretation.
            I32 if !ptr64 => Pointer,
            _ => I2I,
        },
        (Tint(sz2, _, _), Tlong(..)) => {
            if *sz2 == IBool {
                L2Bool
            } else {
                L2I
            }
        }
        (Tint(sz2, _, _), Tfloat(F64, _)) => {
            if *sz2 == IBool {
                F2Bool
            } else {
                F2I
            }
        }
        (Tint(sz2, _, _), Tfloat(F32, _)) => {
            if *sz2 == IBool {
                S2Bool
            } else {
                S2I
            }
        }
        (Tint(sz2, _, _), Tpointer(..) | Tarray(..) | Tfunction(..)) => {
            if ptr64 {
                // like long to int
                if *sz2 == IBool {
                    L2Bool
                } else {
                    L2I
                }
            } else {
                // like int to int
                match sz2 {
                    IBool => I2Bool,
                    I32 => Pointer,
                    _ => I2I,
                }
            }
        }
        // To long
        (Tlong(..), Tlong(..)) => {
            if ptr64 {
                Pointer
            } else {
                L2L
            }
        }
        (Tlong(..), Tint(..)) => I2L,
        (Tlong(..), Tfloat(F64, _)) => F2L,
        (Tlong(..), Tfloat(F32, _)) => S2L,
        (Tlong(..), Tpointer(..) | Tarray(..) | Tfunction(..)) => {
            if ptr64 {
                Pointer
            } else {
                I2L
            }
        }
        // To float
        (Tfloat(F64, _), Tint(..)) => I2F,
        (Tfloat(F32, _), Tint(..)) => I2S,
        (Tfloat(F64, _), Tlong(..)) => L2F,
        (Tfloat(F32, _), Tlong(..)) => L2S,
        (Tfloat(F64, _), Tfloat(F64, _)) => F2F,
        (Tfloat(F32, _), Tfloat(F32, _)) => S2S,
        (Tfloat(F64, _), Tfloat(F32, _)) => S2F,
        (Tfloat(F32, _), Tfloat(F64, _)) => F2S,
        // To pointer
        (Tpointer(..), Tint(..)) => {
            if ptr64 {
                I2L
            } else {
                Pointer
            }
        }
        (Tpointer(..), Tlong(..)) => {
            if ptr64 {
                Pointer
            } else {
                L2I
            }
        }
        (Tpointer(..), Tpointer(..) | Tarray(..) | Tfunction(..)) => Pointer,
        // To struct / union
        (Tstruct(id2, _), Tstruct(id1, _)) => Struct {
            same_id: id1 == id2,
        },
        (Tunion(id2, _), Tunion(id1, _)) => Union {
            same_id: id1 == id2,
        },
        _ => Default,
    }
}

/// Cop.v:393 classify_bool (over typeconv).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoolCase {
    I,
    L,
    F,
    S,
    Default,
}

pub fn classify_bool(ptr64: bool, ty: &ClightType) -> BoolCase {
    use ClightType::*;
    match typeconv(ty) {
        Tint(..) => BoolCase::I,
        Tpointer(..) => {
            if ptr64 {
                BoolCase::L
            } else {
                BoolCase::I
            }
        }
        Tfloat(F64, _) => BoolCase::F,
        Tfloat(F32, _) => BoolCase::S,
        Tlong(..) => BoolCase::L,
        _ => BoolCase::Default,
    }
}

/// Cop.v:455 classify_neg (raw type, no typeconv -- faithful).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NegCase {
    I(ClightSignedness),
    F,
    S,
    L(ClightSignedness),
    Default,
}

pub fn classify_neg(ty: &ClightType) -> NegCase {
    use ClightType::*;
    match ty {
        Tint(I32, Unsigned, _) => NegCase::I(Unsigned),
        Tint(..) => NegCase::I(Signed),
        Tfloat(F64, _) => NegCase::F,
        Tfloat(F32, _) => NegCase::S,
        Tlong(sg, _) => NegCase::L(*sg),
        _ => NegCase::Default,
    }
}

/// Cop.v:522 classify_notint.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NotintCase {
    I(ClightSignedness),
    L(ClightSignedness),
    Default,
}

pub fn classify_notint(ty: &ClightType) -> NotintCase {
    use ClightType::*;
    match ty {
        Tint(I32, Unsigned, _) => NotintCase::I(Unsigned),
        Tint(..) => NotintCase::I(Signed),
        Tlong(sg, _) => NotintCase::L(*sg),
        _ => NotintCase::Default,
    }
}

/// Cop.v:561 classify_binarith -- the usual binary conversions (raw types).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinarithCase {
    I(ClightSignedness),
    L(ClightSignedness),
    F,
    S,
    Default,
}

pub fn classify_binarith(ty1: &ClightType, ty2: &ClightType) -> BinarithCase {
    use BinarithCase::*;
    use ClightType::*;
    match (ty1, ty2) {
        (Tint(I32, Unsigned, _), Tint(..)) => I(Unsigned),
        (Tint(..), Tint(I32, Unsigned, _)) => I(Unsigned),
        (Tint(..), Tint(..)) => I(Signed),
        (Tlong(Signed, _), Tlong(Signed, _)) => L(Signed),
        (Tlong(..), Tlong(..)) => L(Unsigned),
        (Tlong(sg, _), Tint(..)) => L(*sg),
        (Tint(..), Tlong(sg, _)) => L(*sg),
        (Tfloat(F32, _), Tfloat(F32, _)) => S,
        (Tfloat(..), Tfloat(..)) => F,
        (Tfloat(F64, _), Tint(..) | Tlong(..)) => F,
        (Tint(..) | Tlong(..), Tfloat(F64, _)) => F,
        (Tfloat(F32, _), Tint(..) | Tlong(..)) => S,
        (Tint(..) | Tlong(..), Tfloat(F32, _)) => S,
        _ => Default,
    }
}

/// Cop.v:638 classify_add (over typeconv'd operands). The pointer cases carry the element type so type_binop can produce the pointer result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AddCase {
    PI(ClightType),
    PL(ClightType),
    IP(ClightType),
    LP(ClightType),
    Default,
}

pub fn classify_add(ty1: &ClightType, ty2: &ClightType) -> AddCase {
    use ClightType::*;
    match (typeconv(ty1), typeconv(ty2)) {
        (Tpointer(ty, _), Tint(..)) => AddCase::PI(ty.as_ref().clone()),
        (Tpointer(ty, _), Tlong(..)) => AddCase::PL(ty.as_ref().clone()),
        (Tint(..), Tpointer(ty, _)) => AddCase::IP(ty.as_ref().clone()),
        (Tlong(..), Tpointer(ty, _)) => AddCase::LP(ty.as_ref().clone()),
        _ => AddCase::Default,
    }
}

/// Cop.v:706 classify_sub. NOTE no int-minus-pointer case exists: `int - ptr` falls to Default and then to binarith, which rejects pointers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SubCase {
    PI(ClightType),
    PP(ClightType),
    PL(ClightType),
    Default,
}

pub fn classify_sub(ty1: &ClightType, ty2: &ClightType) -> SubCase {
    use ClightType::*;
    match (typeconv(ty1), typeconv(ty2)) {
        (Tpointer(ty, _), Tint(..)) => SubCase::PI(ty.as_ref().clone()),
        (Tpointer(ty, _), Tpointer(..)) => SubCase::PP(ty.as_ref().clone()),
        (Tpointer(ty, _), Tlong(..)) => SubCase::PL(ty.as_ref().clone()),
        _ => SubCase::Default,
    }
}

/// Cop.v:859 classify_shift (over typeconv'd operands).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShiftCase {
    II(ClightSignedness),
    LL(ClightSignedness),
    IL(ClightSignedness),
    LI(ClightSignedness),
    Default,
}

pub fn classify_shift(ty1: &ClightType, ty2: &ClightType) -> ShiftCase {
    use ClightType::*;
    use ShiftCase::*;
    match (typeconv(ty1), typeconv(ty2)) {
        (Tint(I32, Unsigned, _), Tint(..)) => II(Unsigned),
        (Tint(..), Tint(..)) => II(Signed),
        (Tint(I32, Unsigned, _), Tlong(..)) => IL(Unsigned),
        (Tint(..), Tlong(..)) => IL(Signed),
        (Tlong(s, _), Tint(..)) => LI(s),
        (Tlong(s, _), Tlong(..)) => LL(s),
        _ => Default,
    }
}

/// Cop.v:928 classify_cmp (over typeconv'd operands). cmp_default falls back to binarith in comparison_type -- `ptr < float` dies there.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpCase {
    PP,
    PI,
    IP,
    PL,
    LP,
    Default,
}

pub fn classify_cmp(ty1: &ClightType, ty2: &ClightType) -> CmpCase {
    use ClightType::*;
    match (typeconv(ty1), typeconv(ty2)) {
        (Tpointer(..), Tpointer(..)) => CmpCase::PP,
        (Tpointer(..), Tint(..)) => CmpCase::PI,
        (Tint(..), Tpointer(..)) => CmpCase::IP,
        (Tpointer(..), Tlong(..)) => CmpCase::PL,
        (Tlong(..), Tpointer(..)) => CmpCase::LP,
        _ => CmpCase::Default,
    }
}

/// Cop.v:1009 classify_fun: (pointer to) function, carrying the signature.
pub enum FunCase<'a> {
    F(&'a [ClightType], &'a ClightType, CallConv),
    Default,
}

pub fn classify_fun(ty: &ClightType) -> FunCase<'_> {
    use ClightType::*;
    match ty {
        Tfunction(args, res, cc) => FunCase::F(args, res, *cc),
        Tpointer(inner, _) => match inner.as_ref() {
            Tfunction(args, res, cc) => FunCase::F(args, res, *cc),
            _ => FunCase::Default,
        },
        _ => FunCase::Default,
    }
}

/// Cop.v:1023 classify_switch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SwitchCase {
    I,
    L,
    Default,
}

pub fn classify_switch(ty: &ClightType) -> SwitchCase {
    use ClightType::*;
    match ty {
        Tint(..) => SwitchCase::I,
        Tlong(..) => SwitchCase::L,
        _ => SwitchCase::Default,
    }
}

// 1.3 Typing functions (Ctyping.v)

/// Ctyping.v:263 wt_cast = classify_cast is not the default case, plus the gcc-strict struct/union id agreement (module-header deviation note).
pub fn wt_cast(ptr64: bool, from: &ClightType, to: &ClightType) -> bool {
    match classify_cast(ptr64, from, to) {
        CastCase::Default => false,
        CastCase::Struct { same_id } | CastCase::Union { same_id } => same_id,
        _ => true,
    }
}

/// Ctyping.v:266 wt_bool.
pub fn wt_bool(ptr64: bool, ty: &ClightType) -> bool {
    classify_bool(ptr64, ty) != BoolCase::Default
}

fn binarith_result(c: BinarithCase) -> Option<ClightType> {
    use ClightType::*;
    match c {
        BinarithCase::I(sg) => Some(Tint(I32, sg, ClightAttr::default())),
        BinarithCase::L(sg) => Some(Tlong(sg, ClightAttr::default())),
        BinarithCase::F => Some(Tfloat(F64, ClightAttr::default())),
        BinarithCase::S => Some(Tfloat(F32, ClightAttr::default())),
        BinarithCase::Default => None,
    }
}

/// Ctyping.v:80 binarith_type.
pub fn binarith_type(ty1: &ClightType, ty2: &ClightType) -> Option<ClightType> {
    binarith_result(classify_binarith(ty1, ty2))
}

/// Ctyping.v:89 binarith_int_type -- ints/longs only (`% & | ^` reject floats).
pub fn binarith_int_type(ty1: &ClightType, ty2: &ClightType) -> Option<ClightType> {
    match classify_binarith(ty1, ty2) {
        c @ (BinarithCase::I(_) | BinarithCase::L(_)) => binarith_result(c),
        _ => None,
    }
}

/// Ctyping.v:96 shift_op_type.
pub fn shift_op_type(ty1: &ClightType, ty2: &ClightType) -> Option<ClightType> {
    use ClightType::*;
    match classify_shift(ty1, ty2) {
        ShiftCase::II(sg) | ShiftCase::IL(sg) => Some(Tint(I32, sg, ClightAttr::default())),
        ShiftCase::LI(sg) | ShiftCase::LL(sg) => Some(Tlong(sg, ClightAttr::default())),
        ShiftCase::Default => None,
    }
}

/// Ctyping.v:103 comparison_type.
pub fn comparison_type(ty1: &ClightType, ty2: &ClightType) -> Option<ClightType> {
    match classify_cmp(ty1, ty2) {
        CmpCase::Default => match classify_binarith(ty1, ty2) {
            BinarithCase::Default => None,
            _ => Some(type_int32s()),
        },
        _ => Some(type_int32s()),
    }
}

/// Ctyping.v:52 type_unop. None = ill-typed operand.
pub fn type_unop(ptr64: bool, op: ClightUnaryOp, ty: &ClightType) -> Option<ClightType> {
    use ClightType::*;
    match op {
        ClightUnaryOp::Onotbool => match classify_bool(ptr64, ty) {
            BoolCase::Default => None,
            _ => Some(type_int32s()),
        },
        ClightUnaryOp::Onotint => match classify_notint(ty) {
            NotintCase::I(sg) => Some(Tint(I32, sg, ClightAttr::default())),
            NotintCase::L(sg) => Some(Tlong(sg, ClightAttr::default())),
            NotintCase::Default => None,
        },
        ClightUnaryOp::Oneg => match classify_neg(ty) {
            NegCase::I(sg) => Some(Tint(I32, sg, ClightAttr::default())),
            NegCase::F => Some(Tfloat(F64, ClightAttr::default())),
            NegCase::S => Some(Tfloat(F32, ClightAttr::default())),
            NegCase::L(sg) => Some(Tlong(sg, ClightAttr::default())),
            NegCase::Default => None,
        },
        ClightUnaryOp::Oabsfloat => match classify_neg(ty) {
            NegCase::Default => None,
            _ => Some(Tfloat(F64, ClightAttr::default())),
        },
    }
}

/// Ctyping.v:113 type_binop. None = "invalid operands to binary <op>".
pub fn type_binop(
    ptr64: bool,
    op: ClightBinaryOp,
    ty1: &ClightType,
    ty2: &ClightType,
) -> Option<ClightType> {
    use ClightBinaryOp::*;
    use ClightType::*;
    match op {
        Oadd => match classify_add(ty1, ty2) {
            AddCase::PI(ty) | AddCase::IP(ty) | AddCase::PL(ty) | AddCase::LP(ty) => {
                Some(Tpointer(Arc::new(ty), ClightAttr::default()))
            }
            AddCase::Default => binarith_type(ty1, ty2),
        },
        Osub => match classify_sub(ty1, ty2) {
            SubCase::PI(ty) | SubCase::PL(ty) => {
                Some(Tpointer(Arc::new(ty), ClightAttr::default()))
            }
            SubCase::PP(_) => Some(ptrdiff_t(ptr64)),
            SubCase::Default => binarith_type(ty1, ty2),
        },
        Omul | Odiv => binarith_type(ty1, ty2),
        Omod | Oand | Oor | Oxor => binarith_int_type(ty1, ty2),
        Oshl | Oshr => shift_op_type(ty1, ty2),
        Oeq | One | Olt | Ogt | Ole | Oge => comparison_type(ty1, ty2),
    }
}

/// Ctyping.v:143 type_deref: pointer/array/function only.
pub fn type_deref(ty: &ClightType) -> Option<ClightType> {
    use ClightType::*;
    match ty {
        Tpointer(t, _) => Some(t.as_ref().clone()),
        Tarray(t, _, _) => Some(t.as_ref().clone()),
        Tfunction(..) => Some(ty.clone()),
        _ => None,
    }
}

/// Ctyping.v:236 type_conditional over typeconv'd arms. The Err(()) case is a gcc error ("type mismatch in conditional expression", e.g. ptr vs float); the bool flag marks gcc-tolerated ptr/integer mixes (warning under -w, so Warning severity -- CompCert rejects ptr-vs-long, gcc does not).
pub fn type_conditional(ty1: &ClightType, ty2: &ClightType) -> Result<(ClightType, bool), ()> {
    use ClightType::*;
    let (c1, c2) = (typeconv(ty1), typeconv(ty2));
    match (&c1, &c2) {
        (Tint(..) | Tlong(..) | Tfloat(..), Tint(..) | Tlong(..) | Tfloat(..)) => {
            binarith_type(ty1, ty2).map(|t| (t, false)).ok_or(())
        }
        (Tpointer(p1, _), Tpointer(p2, _)) => {
            let t = if is_void(p1) || is_void(p2) {
                Tvoid
            } else {
                type_combine(p1, p2).unwrap_or(Tvoid) // tolerance, as in the spec
            };
            Ok((Tpointer(Arc::new(t), ClightAttr::default()), false))
        }
        (Tpointer(p1, _), Tint(..) | Tlong(..)) => {
            // spec covers ptr/int; ptr/long falls to type_combine (rejected) in CompCert but compiles under gcc -w => tolerated with a warning.
            let warn = matches!(c2, Tlong(..));
            Ok((Tpointer(p1.clone(), ClightAttr::default()), warn))
        }
        (Tint(..) | Tlong(..), Tpointer(p2, _)) => {
            let warn = matches!(c1, Tlong(..));
            Ok((Tpointer(p2.clone(), ClightAttr::default()), warn))
        }
        (a, b) => type_combine(a, b).map(|t| (t, false)).ok_or(()),
    }
}

// 1.4 The Clight wt walker

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    /// The printed C is a gcc error even under -w.
    Error,
    /// wt-relevant but compiles under -w.
    Warning,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WtErrorKind {
    DerefOfScalar,
    MemberOfNonStruct,
    MemberNotFound,
    InvalidBinop,
    InvalidUnop,
    BadCondition,
    BadSwitch,
    BadConditional,
    CondPtrIntMix,
    CallThroughNonFunction,
    ArityTooFew,
    ArityTooMany,
    IncompatibleAssign,
    PtrAsFloat,
    VoidValueUse,
    BadCast,
    AddrofNonLvalue,
    AssignToNonLvalue,
    UnboundTemp,
    ReturnVoidMismatch,
    LiteralAnnotation,
}

impl WtErrorKind {
    /// The gcc diagnostic family this kind lands in -- names match eval/coreutils/error_families.py so P2's audit correlates 1:1.
    pub fn gcc_family(self) -> &'static str {
        use WtErrorKind::*;
        match self {
            DerefOfScalar => "deref-of-scalar",
            MemberOfNonStruct => "member-of-non-struct",
            MemberNotFound => "member-not-found",
            InvalidBinop => "invalid-binop",
            InvalidUnop => "invalid-unop",
            BadCondition => "bad-condition",
            BadSwitch => "bad-switch",
            BadConditional => "bad-conditional",
            CondPtrIntMix => "cond-ptr-int-mix",
            CallThroughNonFunction => "call-through-non-function",
            ArityTooFew => "arity-too-few",
            ArityTooMany => "arity-too-many",
            IncompatibleAssign => "incompatible-types",
            PtrAsFloat => "ptr-float",
            VoidValueUse => "void-expression",
            BadCast => "bad-cast",
            AddrofNonLvalue => "addrof-non-lvalue",
            AssignToNonLvalue => "assign-to-non-lvalue",
            UnboundTemp => "undeclared",
            ReturnVoidMismatch => "return-void-mismatch",
            LiteralAnnotation => "literal-annotation",
        }
    }
}

#[derive(Debug, Clone)]
pub struct WtError {
    pub kind: WtErrorKind,
    pub severity: Severity,
    pub detail: String,
}

impl WtError {
    fn err(kind: WtErrorKind, detail: String) -> Self {
        WtError {
            kind,
            severity: Severity::Error,
            detail,
        }
    }
    fn warn(kind: WtErrorKind, detail: String) -> Self {
        WtError {
            kind,
            severity: Severity::Warning,
            detail,
        }
    }
}

/// Count of Error-severity diagnoses (the number gcc -w would report).
pub fn error_count(errs: &[WtError]) -> usize {
    errs.iter()
        .filter(|e| e.severity == Severity::Error)
        .count()
}

/// The typing environment the walker consults -- what gcc will SEE in the printed C: temp/global decl types (not annotations), composite field layouts, and (optionally) authoritative callee signatures.
pub trait WtEnv {
    /// Declared type of a temp; None = no decl known (the walker recovers with the annotation and reports a Warning -- decl emission is the caller's concern, cf. the var_d family).
    fn temp_type(&self, id: Ident) -> Option<ClightType>;
    /// Type of field `field` in composite `sid`; None = unknown member.
    fn field_type(&self, sid: Ident, field: Ident) -> Option<ClightType>;
    /// Whether composite `sid`'s layout is known -- member-existence is only checkable (MemberNotFound) on known composites.
    fn composite_known(&self, _sid: Ident) -> bool {
        false
    }
    /// Authoritative callee function type, overriding the callee expression's annotation (P2 wires CalleeSignature here). None = use the annotation.
    fn callee_type(&self, _callee: &ClightExpr) -> Option<ClightType> {
        None
    }
    /// Authoritative declaration type of an ident-addressed global.  Machine
    /// load annotations are only access widths and must not override this.
    fn global_ident_type(&self, _id: Ident) -> Option<ClightType> {
        None
    }
    /// Authoritative declaration type of a symbol-addressed global.
    fn global_symbol_type(&self, _name: &str) -> Option<ClightType> {
        None
    }
    /// The enclosing function's return type.
    fn return_type(&self) -> ClightType;
    /// Target pointer width (CompCert's Archi.ptr64). Deliberately has no default: a defaulted true would silently type-check a 32-bit target as 64-bit.
    fn ptr64(&self) -> bool;
}

/// Compact C-ish renderer for diagnostics.
pub fn ty_str(ty: &ClightType) -> String {
    use ClightType::*;
    match ty {
        Tvoid => "void".into(),
        Tint(IBool, _, _) => "_Bool".into(),
        Tint(I8, Signed, _) => "char".into(),
        Tint(I8, Unsigned, _) => "unsigned char".into(),
        Tint(I16, Signed, _) => "short".into(),
        Tint(I16, Unsigned, _) => "unsigned short".into(),
        Tint(I32, Signed, _) => "int".into(),
        Tint(I32, Unsigned, _) => "unsigned int".into(),
        Tlong(Signed, _) => "long".into(),
        Tlong(Unsigned, _) => "unsigned long".into(),
        Tint128(Signed, _) => "__int128".into(),
        Tint128(Unsigned, _) => "unsigned __int128".into(),
        Tfloat(F32, _) => "float".into(),
        Tfloat(F64, _) => "double".into(),
        Tpointer(t, _) => format!("{} *", ty_str(t)),
        Tarray(t, n, _) => format!("{}[{}]", ty_str(t), n),
        Tfunction(args, res, _) => format!(
            "{}({})",
            ty_str(res),
            args.iter().map(ty_str).collect::<Vec<_>>().join(", ")
        ),
        Tstruct(id, _) => format!("struct s{:x}", id),
        Tunion(id, _) => format!("union u{:x}", id),
    }
}

/// An lvalue as the printed C sees it: temps print as ordinary locals, so Etempvar IS addressable/assignable (deviation from CompCert Clight, where temps are not lvalues -- gcc reality wins per D3).
fn is_lvalue_form(e: &ClightExpr) -> bool {
    matches!(
        e,
        ClightExpr::Evar(..)
            | ClightExpr::EvarSymbol(..)
            | ClightExpr::Etempvar(..)
            | ClightExpr::Ederef(..)
            | ClightExpr::Efield(..)
    )
}

/// Value-context compatibility (assignment, argument passing, return): a void source is its own gcc family; ptr->float reads as "pointer value used where a floating-point was expected"; everything else failing wt_cast is the "incompatible types" family.
fn check_value_flow(
    ptr64: bool,
    from: &ClightType,
    to: &ClightType,
    ctx: &str,
    errs: &mut Vec<WtError>,
) {
    if is_void(from) {
        errs.push(WtError::err(
            WtErrorKind::VoidValueUse,
            format!("{}: void value used as {}", ctx, ty_str(to)),
        ));
        return;
    }
    if !wt_cast(ptr64, from, to) {
        let kind = if is_pointerish(from) && is_float(to) {
            WtErrorKind::PtrAsFloat
        } else {
            WtErrorKind::IncompatibleAssign
        };
        errs.push(WtError::err(
            kind,
            format!("{}: {} <- {}", ctx, ty_str(to), ty_str(from)),
        ));
    }
}

/// Bottom-up type synthesis with diagnosis, the executable analogue of Ctyping.v's smart constructors; on an ill-typed node it reports and recovers with the node's annotation, mirroring gcc.
pub fn wt_expr(e: &ClightExpr, env: &dyn WtEnv, errs: &mut Vec<WtError>) -> ClightType {
    use ClightExpr::*;
    match e {
        EconstInt(_, ct) => {
            // check_literal (Ctyping.v:579): Vint carries Tint I32 or Tpointer.
            if !matches!(ct, ClightType::Tint(I32, _, _) | ClightType::Tpointer(..)) {
                errs.push(WtError::warn(
                    WtErrorKind::LiteralAnnotation,
                    format!("int literal annotated {}", ty_str(ct)),
                ));
            }
            ct.clone()
        }
        EconstLong(_, ct) => {
            if !matches!(ct, ClightType::Tlong(..) | ClightType::Tpointer(..)) {
                errs.push(WtError::warn(
                    WtErrorKind::LiteralAnnotation,
                    format!("long literal annotated {}", ty_str(ct)),
                ));
            }
            ct.clone()
        }
        EconstFloat(_, ct) => {
            if !matches!(ct, ClightType::Tfloat(F64, _)) {
                errs.push(WtError::warn(
                    WtErrorKind::LiteralAnnotation,
                    format!("double literal annotated {}", ty_str(ct)),
                ));
            }
            ct.clone()
        }
        EconstSingle(_, ct) => {
            if !matches!(ct, ClightType::Tfloat(F32, _)) {
                errs.push(WtError::warn(
                    WtErrorKind::LiteralAnnotation,
                    format!("single literal annotated {}", ty_str(ct)),
                ));
            }
            ct.clone()
        }
        Etempvar(id, ct) => match env.temp_type(*id) {
            Some(decl) => decl,
            None => {
                errs.push(WtError::warn(
                    WtErrorKind::UnboundTemp,
                    format!("temp {} has no declared type", id),
                ));
                ct.clone()
            }
        },
        Evar(id, ct) => env.global_ident_type(*id).unwrap_or_else(|| ct.clone()),
        EvarSymbol(name, ct) => env.global_symbol_type(name).unwrap_or_else(|| ct.clone()),
        Ederef(inner, ct) => {
            let it = wt_expr(inner, env, errs);
            match type_deref(&it) {
                Some(t) => t,
                None => {
                    errs.push(WtError::err(
                        WtErrorKind::DerefOfScalar,
                        format!("deref of {}", ty_str(&it)),
                    ));
                    ct.clone()
                }
            }
        }
        Eaddrof(inner, _) => {
            let it = wt_expr(inner, env, errs);
            if !is_lvalue_form(inner) {
                errs.push(WtError::err(
                    WtErrorKind::AddrofNonLvalue,
                    format!("& of non-lvalue ({})", ty_str(&it)),
                ));
            }
            ClightType::Tpointer(Arc::new(it), ClightAttr::default())
        }
        Eunop(op, inner, ct) => {
            let it = wt_expr(inner, env, errs);
            match type_unop(env.ptr64(), *op, &it) {
                Some(t) => t,
                None => {
                    errs.push(WtError::err(
                        WtErrorKind::InvalidUnop,
                        format!("{:?} on {}", op, ty_str(&it)),
                    ));
                    ct.clone()
                }
            }
        }
        Ebinop(op, l, r, ct) => {
            let lt = wt_expr(l, env, errs);
            let rt = wt_expr(r, env, errs);
            match type_binop(env.ptr64(), *op, &lt, &rt) {
                Some(t) => t,
                None => {
                    errs.push(WtError::err(
                        WtErrorKind::InvalidBinop,
                        format!("{:?} on ({}, {})", op, ty_str(&lt), ty_str(&rt)),
                    ));
                    ct.clone()
                }
            }
        }
        Ecast(inner, ct) => {
            let it = wt_expr(inner, env, errs);
            if !wt_cast(env.ptr64(), &it, ct) {
                let kind = if is_pointerish(&it) && is_float(ct) {
                    WtErrorKind::PtrAsFloat
                } else {
                    WtErrorKind::BadCast
                };
                errs.push(WtError::err(
                    kind,
                    format!("({}){}", ty_str(ct), ty_str(&it)),
                ));
            }
            ct.clone()
        }
        Efield(base, field, ct) => {
            let bt = wt_expr(base, env, errs);
            match erase_attrs(&bt) {
                ClightType::Tstruct(sid, _) | ClightType::Tunion(sid, _) => {
                    match env.field_type(sid, *field) {
                        Some(t) => t,
                        None => {
                            if env.composite_known(sid) {
                                errs.push(WtError::err(
                                    WtErrorKind::MemberNotFound,
                                    format!("{} has no member {}", ty_str(&bt), field),
                                ));
                            }
                            ct.clone()
                        }
                    }
                }
                other => {
                    errs.push(WtError::err(
                        WtErrorKind::MemberOfNonStruct,
                        format!("member {} of {}", field, ty_str(&other)),
                    ));
                    ct.clone()
                }
            }
        }
        Esizeof(_, ct) | Ealignof(_, ct) => ct.clone(),
        Econdition(c, a, b, ct) => {
            let tc = wt_expr(c, env, errs);
            if !wt_bool(env.ptr64(), &tc) {
                errs.push(WtError::err(
                    WtErrorKind::BadCondition,
                    format!("?: condition has type {}", ty_str(&tc)),
                ));
            }
            let ta = wt_expr(a, env, errs);
            let tb = wt_expr(b, env, errs);
            match type_conditional(&ta, &tb) {
                Ok((t, ptr_int_mix)) => {
                    if ptr_int_mix {
                        errs.push(WtError::warn(
                            WtErrorKind::CondPtrIntMix,
                            format!("?: arms {} / {}", ty_str(&ta), ty_str(&tb)),
                        ));
                    }
                    t
                }
                Err(()) => {
                    errs.push(WtError::err(
                        WtErrorKind::BadConditional,
                        format!("?: arms {} / {}", ty_str(&ta), ty_str(&tb)),
                    ));
                    ct.clone()
                }
            }
        }
    }
}

fn wt_call(
    ret: &Option<Ident>,
    f: &ClightExpr,
    args: &[ClightExpr],
    env: &dyn WtEnv,
    errs: &mut Vec<WtError>,
) {
    let ftype = match env.callee_type(f) {
        Some(t) => t,
        None => wt_expr(f, env, errs),
    };
    let arg_types: Vec<ClightType> = args.iter().map(|a| wt_expr(a, env, errs)).collect();
    match classify_fun(&ftype) {
        FunCase::F(params, res, cc) => {
            // Arity (Ctyping.v:589 check_arguments, gcc-strict per the module header): unprototyped callees check nothing; variadic callees require at least the fixed params; otherwise counts must match.
            if !cc.unproto {
                if args.len() < params.len() {
                    errs.push(WtError::err(
                        WtErrorKind::ArityTooFew,
                        format!("{} args, {} params", args.len(), params.len()),
                    ));
                } else if args.len() > params.len() && cc.varargs.is_none() {
                    errs.push(WtError::err(
                        WtErrorKind::ArityTooMany,
                        format!("{} args, {} params", args.len(), params.len()),
                    ));
                }
                for (i, (at, pt)) in arg_types.iter().zip(params.iter()).enumerate() {
                    check_value_flow(env.ptr64(), at, pt, &format!("arg {}", i), errs);
                }
            }
            if let Some(rid) = ret {
                if is_void(res) {
                    errs.push(WtError::err(
                        WtErrorKind::VoidValueUse,
                        "capturing result of a void call".into(),
                    ));
                } else if let Some(decl) = env.temp_type(*rid) {
                    check_value_flow(env.ptr64(), res, &decl, "call result", errs);
                }
            }
        }
        FunCase::Default => {
            errs.push(WtError::err(
                WtErrorKind::CallThroughNonFunction,
                format!("callee has type {}", ty_str(&ftype)),
            ));
        }
    }
}

/// Walk a statement, reporting every frontend diagnosis (Ctyping.v:458 wt_stmt, adapted to Clight statement forms: no Evalof/lvalue kinds -- Sassign carries the wt_cast obligation, Sset binds temps, conditions are wt_bool).
pub fn wt_stmt(stmt: &ClightStmt, env: &dyn WtEnv, errs: &mut Vec<WtError>) {
    use ClightStmt::*;
    match stmt {
        Sskip | Sbreak | Scontinue | Sgoto(_) => {}
        Sassign(lhs, rhs) => {
            let lt = wt_expr(lhs, env, errs);
            let rt = wt_expr(rhs, env, errs);
            if !is_lvalue_form(lhs) {
                errs.push(WtError::err(
                    WtErrorKind::AssignToNonLvalue,
                    format!("assign to non-lvalue ({})", ty_str(&lt)),
                ));
            }
            // C permits conversion *to* void only in a discarded-value cast;
            // it never permits a void object.  `wt_cast` deliberately models
            // the former, so the Sassign lvalue obligation has to reject the
            // latter explicitly.  Otherwise `*(void *)p = x` looks compatible
            // merely because `x` can be cast to void.
            if is_void(&lt) {
                errs.push(WtError::err(
                    WtErrorKind::VoidValueUse,
                    "assignment to void lvalue".into(),
                ));
            }
            check_value_flow(env.ptr64(), &rt, &lt, "assign", errs);
        }
        Sset(id, e) => {
            let rt = wt_expr(e, env, errs);
            match env.temp_type(*id) {
                Some(decl) => check_value_flow(env.ptr64(), &rt, &decl, "set", errs),
                None => {
                    errs.push(WtError::warn(
                        WtErrorKind::UnboundTemp,
                        format!("set of undeclared temp {}", id),
                    ));
                    if is_void(&rt) {
                        errs.push(WtError::err(
                            WtErrorKind::VoidValueUse,
                            "set from void expression".into(),
                        ));
                    }
                }
            }
        }
        Scall(ret, f, args) => wt_call(ret, f, args, env, errs),
        Sbuiltin(_, _, _, args) => {
            for a in args {
                wt_expr(a, env, errs);
            }
        }
        Ssequence(ss) => {
            for s in ss {
                wt_stmt(s, env, errs);
            }
        }
        Sifthenelse(c, a, b) => {
            let tc = wt_expr(c, env, errs);
            if !wt_bool(env.ptr64(), &tc) {
                errs.push(WtError::err(
                    WtErrorKind::BadCondition,
                    format!("if condition has type {}", ty_str(&tc)),
                ));
            }
            wt_stmt(a, env, errs);
            wt_stmt(b, env, errs);
        }
        Sloop(a, b) => {
            wt_stmt(a, env, errs);
            wt_stmt(b, env, errs);
        }
        Sreturn(ret) => {
            let rt = env.return_type();
            match ret {
                Some(e) => {
                    let et = wt_expr(e, env, errs);
                    if is_void(&rt) {
                        // gcc: warning under -w ("'return' with a value...").
                        errs.push(WtError::warn(
                            WtErrorKind::ReturnVoidMismatch,
                            "return with a value in a void function".into(),
                        ));
                    } else {
                        check_value_flow(env.ptr64(), &et, &rt, "return", errs);
                    }
                }
                None => {
                    if !is_void(&rt) {
                        errs.push(WtError::warn(
                            WtErrorKind::ReturnVoidMismatch,
                            "valueless return in a non-void function".into(),
                        ));
                    }
                }
            }
        }
        Sswitch(e, cases) => {
            let te = wt_expr(e, env, errs);
            if classify_switch(&te) == SwitchCase::Default {
                errs.push(WtError::err(
                    WtErrorKind::BadSwitch,
                    format!("switch on {}", ty_str(&te)),
                ));
            }
            for (_, s) in cases {
                wt_stmt(s, env, errs);
            }
        }
        Slabel(_, inner) => wt_stmt(inner, env, errs),
    }
}

/// Convenience entry point: all diagnoses for one statement.
pub fn wt_check_stmt(stmt: &ClightStmt, env: &dyn WtEnv) -> Vec<WtError> {
    let mut errs = Vec::new();
    wt_stmt(stmt, env, &mut errs);
    errs
}

/// A plain-map environment (tests and simple callers).
pub struct MapEnv {
    pub temps: HashMap<Ident, ClightType>,
    pub globals_by_ident: HashMap<Ident, ClightType>,
    pub globals_by_symbol: HashMap<String, ClightType>,
    pub fields: HashMap<(Ident, Ident), ClightType>,
    pub known_composites: HashSet<Ident>,
    pub ret: Option<ClightType>,
    pub callee: Option<ClightType>,
    pub ptr64: bool,
}

// Hand-written rather than derived: a derived bool would default ptr64 to false, silently checking every default-constructed env against a 32-bit target.
impl Default for MapEnv {
    fn default() -> Self {
        MapEnv {
            temps: HashMap::new(),
            globals_by_ident: HashMap::new(),
            globals_by_symbol: HashMap::new(),
            fields: HashMap::new(),
            known_composites: HashSet::new(),
            ret: None,
            callee: None,
            ptr64: true,
        }
    }
}

impl WtEnv for MapEnv {
    fn temp_type(&self, id: Ident) -> Option<ClightType> {
        self.temps.get(&id).cloned()
    }
    fn field_type(&self, sid: Ident, field: Ident) -> Option<ClightType> {
        self.fields.get(&(sid, field)).cloned()
    }
    fn composite_known(&self, sid: Ident) -> bool {
        self.known_composites.contains(&sid)
    }
    fn callee_type(&self, _callee: &ClightExpr) -> Option<ClightType> {
        self.callee.clone()
    }
    fn global_ident_type(&self, id: Ident) -> Option<ClightType> {
        self.globals_by_ident.get(&id).cloned()
    }
    fn global_symbol_type(&self, name: &str) -> Option<ClightType> {
        self.globals_by_symbol.get(name).cloned()
    }
    fn return_type(&self) -> ClightType {
        self.ret.clone().unwrap_or(ClightType::Tvoid)
    }
    fn ptr64(&self) -> bool {
        self.ptr64
    }
}

// 1.5 Tests

#[cfg(test)]
mod tests {
    use super::*;
    use crate::x86::types::{ClightBinaryOp as B, ClightUnaryOp as U};

    fn a() -> ClightAttr {
        ClightAttr::default()
    }
    fn tint() -> ClightType {
        ClightType::Tint(I32, Signed, a())
    }
    fn tuint() -> ClightType {
        ClightType::Tint(I32, Unsigned, a())
    }
    fn ti8() -> ClightType {
        ClightType::Tint(I8, Signed, a())
    }
    fn tbool() -> ClightType {
        ClightType::Tint(IBool, Signed, a())
    }
    fn tlong() -> ClightType {
        ClightType::Tlong(Signed, a())
    }
    fn tulong() -> ClightType {
        ClightType::Tlong(Unsigned, a())
    }
    fn tf64() -> ClightType {
        ClightType::Tfloat(F64, a())
    }
    fn tf32() -> ClightType {
        ClightType::Tfloat(F32, a())
    }
    fn tptr(t: ClightType) -> ClightType {
        ClightType::Tpointer(Arc::new(t), a())
    }
    fn tarr(t: ClightType, n: i64) -> ClightType {
        ClightType::Tarray(Arc::new(t), n, a())
    }
    fn tstruct(id: Ident) -> ClightType {
        ClightType::Tstruct(id, a())
    }
    fn tunion(id: Ident) -> ClightType {
        ClightType::Tunion(id, a())
    }
    fn tfn(args: Vec<ClightType>, res: ClightType) -> ClightType {
        ClightType::Tfunction(Arc::new(args), Arc::new(res), CallConv::default())
    }
    fn tfn_vararg(args: Vec<ClightType>, res: ClightType, fixed: i64) -> ClightType {
        ClightType::Tfunction(
            Arc::new(args),
            Arc::new(res),
            CallConv {
                varargs: Some(fixed),
                unproto: false,
                structured_ret: false,
            },
        )
    }

    fn tv(id: Ident, t: ClightType) -> ClightExpr {
        ClightExpr::Etempvar(id, t)
    }
    fn c32(v: i32) -> ClightExpr {
        ClightExpr::EconstInt(v, tint())
    }
    fn cf(v: f64) -> ClightExpr {
        ClightExpr::EconstFloat(v.into(), tf64())
    }
    fn deref(e: ClightExpr, ann: ClightType) -> ClightExpr {
        ClightExpr::Ederef(Box::new(e), ann)
    }
    fn bin(op: B, l: ClightExpr, r: ClightExpr, ann: ClightType) -> ClightExpr {
        ClightExpr::Ebinop(op, Box::new(l), Box::new(r), ann)
    }
    fn unop(op: U, e: ClightExpr, ann: ClightType) -> ClightExpr {
        ClightExpr::Eunop(op, Box::new(e), ann)
    }
    fn cast(e: ClightExpr, t: ClightType) -> ClightExpr {
        ClightExpr::Ecast(Box::new(e), t)
    }
    fn field(base: ClightExpr, f: Ident, ann: ClightType) -> ClightExpr {
        ClightExpr::Efield(Box::new(base), f, ann)
    }

    fn env_with(temps: Vec<(Ident, ClightType)>) -> MapEnv {
        MapEnv {
            temps: temps.into_iter().collect(),
            ..Default::default()
        }
    }

    /// Families of Error-severity diagnoses.
    fn err_fams(errs: &[WtError]) -> Vec<&'static str> {
        errs.iter()
            .filter(|e| e.severity == Severity::Error)
            .map(|e| e.kind.gcc_family())
            .collect()
    }

    // ---- 1.1 utilities ----

    #[test]
    fn typeconv_promotions_and_decay() {
        assert_eq!(typeconv(&ti8()), tint());
        assert_eq!(typeconv(&ClightType::Tint(I16, Unsigned, a())), tint());
        assert_eq!(typeconv(&tbool()), tint());
        assert_eq!(typeconv(&tuint()), tuint()); // U32 preserved
        assert_eq!(typeconv(&tarr(tf64(), 4)), tptr(tf64()));
        let f = tfn(vec![tint()], tint());
        assert_eq!(typeconv(&f), tptr(f.clone()));
        assert_eq!(typeconv(&tlong()), tlong());
    }

    #[test]
    fn type_combine_agreement() {
        assert_eq!(type_combine(&tint(), &tint()), Some(tint()));
        assert_eq!(type_combine(&tint(), &tuint()), None);
        assert_eq!(
            type_combine(&tptr(tint()), &tptr(tint())),
            Some(tptr(tint()))
        );
        assert_eq!(type_combine(&tptr(tint()), &tptr(tf64())), None);
        assert_eq!(type_combine(&tstruct(1), &tstruct(1)), Some(tstruct(1)));
        assert_eq!(type_combine(&tstruct(1), &tstruct(2)), None);
        assert_eq!(type_combine(&tint(), &tf64()), None);
    }

    // ---- 1.2 classification tables ----

    #[test]
    fn binarith_all_arms() {
        use BinarithCase::*;
        assert_eq!(classify_binarith(&tuint(), &tint()), I(Unsigned));
        assert_eq!(classify_binarith(&tint(), &tuint()), I(Unsigned));
        assert_eq!(classify_binarith(&ti8(), &tint()), I(Signed));
        assert_eq!(classify_binarith(&tlong(), &tlong()), L(Signed));
        assert_eq!(classify_binarith(&tulong(), &tlong()), L(Unsigned));
        assert_eq!(classify_binarith(&tlong(), &tint()), L(Signed));
        assert_eq!(classify_binarith(&tint(), &tulong()), L(Unsigned));
        assert_eq!(classify_binarith(&tf32(), &tf32()), S);
        assert_eq!(classify_binarith(&tf64(), &tf32()), F);
        assert_eq!(classify_binarith(&tf64(), &tint()), F);
        assert_eq!(classify_binarith(&tlong(), &tf64()), F);
        assert_eq!(classify_binarith(&tf32(), &tint()), S);
        assert_eq!(classify_binarith(&tlong(), &tf32()), S);
        // defaults: any pointer/struct/void operand
        assert_eq!(classify_binarith(&tptr(tint()), &tint()), Default);
        assert_eq!(classify_binarith(&tf64(), &tptr(tint())), Default);
        assert_eq!(classify_binarith(&tstruct(1), &tint()), Default);
        assert_eq!(classify_binarith(&ClightType::Tvoid, &tint()), Default);
    }

    #[test]
    fn cast_table_defaults_and_arms() {
        use CastCase::*;
        // the hard-illegal conversions under -w
        assert_eq!(classify_cast(true, &tf64(), &tptr(tint())), Default); // float -> ptr
        assert_eq!(classify_cast(true, &tptr(tint()), &tf64()), Default); // ptr -> float
        assert_eq!(classify_cast(true, &tstruct(1), &tint()), Default); // struct -> scalar
        assert_eq!(classify_cast(true, &tint(), &tstruct(1)), Default); // scalar -> struct
        assert_eq!(classify_cast(true, &ClightType::Tvoid, &tint()), Default); // void source
                                                                               // anything to void is fine
        assert_eq!(classify_cast(true, &tstruct(1), &ClightType::Tvoid), Void);
        // ptr64 arms
        assert_eq!(classify_cast(true, &tint(), &tptr(tint())), I2L); // int -> ptr
        assert_eq!(classify_cast(true, &tlong(), &tptr(tint())), Pointer); // long -> ptr
        assert_eq!(classify_cast(true, &tptr(tint()), &tlong()), Pointer); // ptr -> long
        assert_eq!(classify_cast(true, &tptr(tint()), &tint()), L2I); // ptr -> int
        assert_eq!(classify_cast(true, &tptr(tint()), &tbool()), L2Bool);
        assert_eq!(classify_cast(true, &tlong(), &tlong()), Pointer); // long -> long (ptr64)
        assert_eq!(
            classify_cast(true, &tarr(tint(), 3), &tptr(tint())),
            Pointer
        );
        // numeric lattice
        assert_eq!(classify_cast(true, &tint(), &ti8()), I2I);
        assert_eq!(classify_cast(true, &tint(), &tbool()), I2Bool);
        assert_eq!(classify_cast(true, &tf64(), &tint()), F2I);
        assert_eq!(classify_cast(true, &tf32(), &tlong()), S2L);
        assert_eq!(classify_cast(true, &tint(), &tf32()), I2S);
        assert_eq!(classify_cast(true, &tf64(), &tf32()), F2S);
        assert_eq!(classify_cast(true, &tf32(), &tf64()), S2F);
        // struct/union id agreement
        assert_eq!(
            classify_cast(true, &tstruct(1), &tstruct(1)),
            Struct { same_id: true }
        );
        assert_eq!(
            classify_cast(true, &tstruct(1), &tstruct(2)),
            Struct { same_id: false }
        );
        assert_eq!(
            classify_cast(true, &tunion(7), &tunion(7)),
            Union { same_id: true }
        );
        assert!(wt_cast(true, &tstruct(1), &tstruct(1)));
        assert!(!wt_cast(true, &tstruct(1), &tstruct(2)));
    }

    // The ptr32 arms of Cop.v:103 classify_cast -- each one the mirror of a ptr64 case asserted above.
    #[test]
    fn cast_arms_ptr32() {
        use CastCase::*;

        // I32 is pointer-width, so int <-> ptr and int -> int at I32 are no-op reinterpretations.
        assert_eq!(classify_cast(false, &tint(), &tptr(tint())), Pointer);
        assert_eq!(classify_cast(false, &tptr(tint()), &tint()), Pointer);
        assert_eq!(classify_cast(false, &tint(), &tint()), Pointer);
        // Narrower int destinations stay real conversions.
        assert_eq!(classify_cast(false, &tint(), &ti8()), I2I);
        assert_eq!(classify_cast(false, &tint(), &tbool()), I2Bool);
        assert_eq!(classify_cast(false, &tptr(tint()), &ti8()), I2I);
        assert_eq!(classify_cast(false, &tptr(tint()), &tbool()), I2Bool);

        // long is now wider than a pointer, so the long arms are real conversions.
        assert_eq!(classify_cast(false, &tlong(), &tlong()), L2L);
        assert_eq!(classify_cast(false, &tptr(tint()), &tlong()), I2L);
        assert_eq!(classify_cast(false, &tlong(), &tptr(tint())), L2I);

        // Width-independent arms are unmoved.
        assert_eq!(
            classify_cast(false, &tarr(tint(), 3), &tptr(tint())),
            Pointer
        );
        assert_eq!(classify_cast(false, &tf64(), &tptr(tint())), Default);
        assert_eq!(classify_cast(false, &tptr(tint()), &tf64()), Default);
        assert_eq!(classify_cast(false, &tf64(), &tint()), F2I);
        assert_eq!(
            classify_cast(false, &tstruct(1), &tstruct(1)),
            Struct { same_id: true }
        );
    }

    #[test]
    fn bool_and_ptrdiff_ptr32() {
        // A pointer tests as an int, not a long.
        assert_eq!(classify_bool(false, &tptr(tint())), BoolCase::I);
        assert_eq!(classify_bool(false, &tarr(tint(), 2)), BoolCase::I);
        // Everything not pointer-shaped is unchanged.
        assert_eq!(classify_bool(false, &tlong()), BoolCase::L);
        assert_eq!(classify_bool(false, &tf32()), BoolCase::S);
        assert_eq!(classify_bool(false, &tstruct(1)), BoolCase::Default);

        // Ctyping.v:33 -- ptrdiff_t is signed int, so ptr - ptr yields int.
        assert_eq!(ptrdiff_t(false), tint());
        assert_eq!(ptrdiff_t(true), tlong());
        assert_eq!(
            type_binop(false, B::Osub, &tptr(tint()), &tptr(tint())),
            Some(tint())
        );
        // !p is still int-typed; the operand just classifies through the int arm.
        assert_eq!(type_unop(false, U::Onotbool, &tptr(tint())), Some(tint()));
    }

    #[test]
    fn bool_neg_notint_arms() {
        assert_eq!(classify_bool(true, &ti8()), BoolCase::I); // via typeconv
        assert_eq!(classify_bool(true, &tptr(tint())), BoolCase::L); // ptr64
        assert_eq!(classify_bool(true, &tf32()), BoolCase::S);
        assert_eq!(classify_bool(true, &tlong()), BoolCase::L);
        assert_eq!(classify_bool(true, &tarr(tint(), 2)), BoolCase::L); // decays to ptr
        assert_eq!(classify_bool(true, &tstruct(1)), BoolCase::Default);
        assert_eq!(classify_bool(true, &ClightType::Tvoid), BoolCase::Default);

        assert_eq!(classify_neg(&tuint()), NegCase::I(Unsigned));
        assert_eq!(classify_neg(&ti8()), NegCase::I(Signed));
        assert_eq!(classify_neg(&tf64()), NegCase::F);
        assert_eq!(classify_neg(&tf32()), NegCase::S);
        assert_eq!(classify_neg(&tulong()), NegCase::L(Unsigned));
        assert_eq!(classify_neg(&tptr(tint())), NegCase::Default);

        assert_eq!(classify_notint(&tuint()), NotintCase::I(Unsigned));
        assert_eq!(classify_notint(&tint()), NotintCase::I(Signed));
        assert_eq!(classify_notint(&tlong()), NotintCase::L(Signed));
        assert_eq!(classify_notint(&tf64()), NotintCase::Default);
        assert_eq!(classify_notint(&tptr(tint())), NotintCase::Default);
    }

    #[test]
    fn add_sub_shift_cmp_arms() {
        assert!(matches!(classify_add(&tptr(tf64()), &tint()), AddCase::PI(t) if t == tf64()));
        assert!(matches!(
            classify_add(&tptr(tint()), &tlong()),
            AddCase::PL(_)
        ));
        assert!(matches!(
            classify_add(&tint(), &tptr(tint())),
            AddCase::IP(_)
        ));
        assert!(matches!(
            classify_add(&tlong(), &tptr(tint())),
            AddCase::LP(_)
        ));
        assert!(matches!(
            classify_add(&tarr(tint(), 4), &tint()),
            AddCase::PI(_)
        )); // decay
        assert!(matches!(
            classify_add(&tptr(tint()), &tptr(tint())),
            AddCase::Default
        ));
        assert!(matches!(classify_add(&tint(), &tint()), AddCase::Default));

        assert!(matches!(
            classify_sub(&tptr(tint()), &tint()),
            SubCase::PI(_)
        ));
        assert!(matches!(
            classify_sub(&tptr(tint()), &tptr(tint())),
            SubCase::PP(_)
        ));
        assert!(matches!(
            classify_sub(&tptr(tint()), &tlong()),
            SubCase::PL(_)
        ));
        assert!(matches!(
            classify_sub(&tint(), &tptr(tint())),
            SubCase::Default
        )); // int - ptr

        assert_eq!(classify_shift(&tuint(), &tint()), ShiftCase::II(Unsigned));
        assert_eq!(classify_shift(&ti8(), &tint()), ShiftCase::II(Signed)); // promoted
        assert_eq!(classify_shift(&tint(), &tlong()), ShiftCase::IL(Signed));
        assert_eq!(classify_shift(&tulong(), &tint()), ShiftCase::LI(Unsigned));
        assert_eq!(classify_shift(&tlong(), &tlong()), ShiftCase::LL(Signed));
        assert_eq!(classify_shift(&tf64(), &tint()), ShiftCase::Default);
        assert_eq!(classify_shift(&tint(), &tptr(tint())), ShiftCase::Default);

        assert_eq!(classify_cmp(&tptr(tint()), &tptr(tf64())), CmpCase::PP);
        assert_eq!(classify_cmp(&tptr(tint()), &tint()), CmpCase::PI);
        assert_eq!(classify_cmp(&tint(), &tptr(tint())), CmpCase::IP);
        assert_eq!(classify_cmp(&tptr(tint()), &tlong()), CmpCase::PL);
        assert_eq!(classify_cmp(&tlong(), &tptr(tint())), CmpCase::LP);
        assert_eq!(classify_cmp(&tint(), &tf64()), CmpCase::Default);
    }

    #[test]
    fn fun_and_switch_arms() {
        let f = tfn(vec![tint()], tf64());
        assert!(matches!(classify_fun(&f), FunCase::F(p, r, _) if p.len() == 1 && *r == tf64()));
        assert!(matches!(classify_fun(&tptr(f)), FunCase::F(..)));
        assert!(matches!(classify_fun(&tptr(tint())), FunCase::Default));
        assert!(matches!(classify_fun(&tlong()), FunCase::Default));

        assert_eq!(classify_switch(&tbool()), SwitchCase::I);
        assert_eq!(classify_switch(&tulong()), SwitchCase::L);
        assert_eq!(classify_switch(&tptr(tint())), SwitchCase::Default);
        assert_eq!(classify_switch(&tf64()), SwitchCase::Default);
    }

    // ---- 1.3 typing functions ----

    #[test]
    fn unop_typing() {
        assert_eq!(type_unop(true, U::Onotbool, &tptr(tint())), Some(tint()));
        assert_eq!(type_unop(true, U::Onotbool, &tstruct(1)), None);
        assert_eq!(type_unop(true, U::Onotint, &tlong()), Some(tlong()));
        assert_eq!(type_unop(true, U::Onotint, &tf64()), None); // ~f
        assert_eq!(type_unop(true, U::Oneg, &tf32()), Some(tf32()));
        assert_eq!(type_unop(true, U::Oneg, &tptr(tint())), None); // -p
        assert_eq!(type_unop(true, U::Oabsfloat, &tint()), Some(tf64()));
        assert_eq!(type_unop(true, U::Oabsfloat, &tptr(tint())), None);
    }

    #[test]
    fn binop_typing() {
        // ptr arithmetic carries the element type
        assert_eq!(
            type_binop(true, B::Oadd, &tptr(tf64()), &tint()),
            Some(tptr(tf64()))
        );
        assert_eq!(
            type_binop(true, B::Osub, &tptr(tint()), &tptr(tint())),
            Some(tlong())
        ); // ptrdiff
        assert_eq!(
            type_binop(true, B::Oadd, &tptr(tint()), &tptr(tint())),
            None
        ); // ptr + ptr
        assert_eq!(type_binop(true, B::Osub, &tint(), &tptr(tint())), None); // int - ptr
                                                                             // binarith_int rejects floats; binarith rejects pointers
        assert_eq!(type_binop(true, B::Omod, &tf64(), &tf64()), None); // f % g
        assert_eq!(type_binop(true, B::Omod, &tptr(tint()), &tlong()), None); // void* % long
        assert_eq!(type_binop(true, B::Oand, &tf32(), &tint()), None);
        assert_eq!(type_binop(true, B::Omul, &tptr(tint()), &tint()), None);
        assert_eq!(type_binop(true, B::Omod, &tlong(), &tint()), Some(tlong()));
        // shifts
        assert_eq!(type_binop(true, B::Oshl, &tf64(), &tint()), None);
        assert_eq!(type_binop(true, B::Oshl, &tlong(), &tint()), Some(tlong()));
        // comparisons: ptr/int fine (gcc warns only), ptr/float dies
        assert_eq!(
            type_binop(true, B::Olt, &tptr(tint()), &tint()),
            Some(tint())
        );
        assert_eq!(type_binop(true, B::Olt, &tptr(tint()), &tf64()), None); // p < 0.5
        assert_eq!(type_binop(true, B::Oeq, &tf64(), &tint()), Some(tint()));
    }

    #[test]
    fn deref_and_conditional_typing() {
        assert_eq!(type_deref(&tptr(tf64())), Some(tf64()));
        assert_eq!(type_deref(&tarr(tint(), 4)), Some(tint()));
        assert!(type_deref(&tfn(vec![], tint())).is_some());
        assert_eq!(type_deref(&tlong()), None);
        assert_eq!(type_deref(&tstruct(1)), None);

        assert_eq!(type_conditional(&tint(), &tf64()), Ok((tf64(), false)));
        assert_eq!(
            type_conditional(&tptr(tint()), &tptr(tint())),
            Ok((tptr(tint()), false))
        );
        // mismatched pointees tolerate to void*
        assert_eq!(
            type_conditional(&tptr(tint()), &tptr(tf64())),
            Ok((tptr(ClightType::Tvoid), false))
        );
        assert_eq!(
            type_conditional(&tptr(tint()), &tint()),
            Ok((tptr(tint()), false))
        );
        // ptr/long mix: gcc-tolerated, flagged
        assert_eq!(
            type_conditional(&tlong(), &tptr(tint())),
            Ok((tptr(tint()), true))
        );
        // ptr vs float: error
        assert!(type_conditional(&tptr(tint()), &tf64()).is_err());
        assert!(type_conditional(&tstruct(1), &tstruct(2)).is_err());
    }

    // ---- 1.4/1.5 walker fixtures: one positive + negative per family ----

    #[test]
    fn walker_deref_of_scalar() {
        let env = env_with(vec![(1, tlong()), (2, tptr(tint()))]);
        // *(long)v1 = 0  -> deref-of-scalar
        let bad = ClightStmt::Sassign(deref(tv(1, tlong()), tint()), c32(0));
        assert_eq!(
            err_fams(&wt_check_stmt(&bad, &env)),
            vec!["deref-of-scalar"]
        );
        // *v2 = 0 -> clean
        let good = ClightStmt::Sassign(deref(tv(2, tptr(tint())), tint()), c32(0));
        assert!(err_fams(&wt_check_stmt(&good, &env)).is_empty());
        // decl-vs-use: annotation says pointer but the DECL is long -> still an error
        let decl_wins = ClightStmt::Sassign(deref(tv(1, tptr(tint())), tint()), c32(0));
        assert_eq!(
            err_fams(&wt_check_stmt(&decl_wins, &env)),
            vec!["deref-of-scalar"]
        );
    }

    #[test]
    fn walker_member_of_non_struct() {
        let mut env = env_with(vec![(1, tlong()), (2, tstruct(5))]);
        env.fields.insert((5, 8), tint());
        env.known_composites.insert(5);
        let bad = ClightStmt::Sset(3, field(tv(1, tstruct(5)), 8, tint()));
        let mut e2 = env_with(vec![(1, tlong()), (3, tint())]);
        e2.fields = env.fields.clone();
        e2.known_composites = env.known_composites.clone();
        assert_eq!(
            err_fams(&wt_check_stmt(&bad, &e2)),
            vec!["member-of-non-struct"]
        );
        // (*p).f with p : struct* -> clean; missing member -> member-not-found
        let mut e3 = env_with(vec![(2, tptr(tstruct(5))), (3, tint())]);
        e3.fields = env.fields.clone();
        e3.known_composites = env.known_composites.clone();
        let good = ClightStmt::Sset(
            3,
            field(deref(tv(2, tptr(tstruct(5))), tstruct(5)), 8, tint()),
        );
        assert!(err_fams(&wt_check_stmt(&good, &e3)).is_empty());
        let missing = ClightStmt::Sset(
            3,
            field(deref(tv(2, tptr(tstruct(5))), tstruct(5)), 99, tint()),
        );
        assert_eq!(
            err_fams(&wt_check_stmt(&missing, &e3)),
            vec!["member-not-found"]
        );
    }

    #[test]
    fn walker_invalid_binop() {
        let env = env_with(vec![
            (1, tf64()),
            (2, tf64()),
            (3, tf64()),
            (4, tptr(tint())),
        ]);
        // v3 = v1 % v2 (floats)
        let modf = ClightStmt::Sset(3, bin(B::Omod, tv(1, tf64()), tv(2, tf64()), tf64()));
        assert!(err_fams(&wt_check_stmt(&modf, &env)).contains(&"invalid-binop"));
        // p < 0.5
        let cmp = ClightStmt::Sifthenelse(
            bin(B::Olt, tv(4, tptr(tint())), cf(0.5), tint()),
            Box::new(ClightStmt::Sskip),
            Box::new(ClightStmt::Sskip),
        );
        assert_eq!(err_fams(&wt_check_stmt(&cmp, &env)), vec!["invalid-binop"]);
        // ptr + ptr
        let pp = ClightStmt::Sset(
            3,
            bin(B::Oadd, tv(4, tptr(tint())), tv(4, tptr(tint())), tlong()),
        );
        assert!(err_fams(&wt_check_stmt(&pp, &env)).contains(&"invalid-binop"));
        // clean: long % int, ptr - ptr
        let env2 = env_with(vec![
            (1, tlong()),
            (2, tint()),
            (3, tlong()),
            (4, tptr(tint())),
        ]);
        let ok1 = ClightStmt::Sset(3, bin(B::Omod, tv(1, tlong()), tv(2, tint()), tlong()));
        assert!(err_fams(&wt_check_stmt(&ok1, &env2)).is_empty());
        let ok2 = ClightStmt::Sset(
            3,
            bin(B::Osub, tv(4, tptr(tint())), tv(4, tptr(tint())), tlong()),
        );
        assert!(err_fams(&wt_check_stmt(&ok2, &env2)).is_empty());
    }

    #[test]
    fn walker_invalid_unop_and_conditions() {
        let env = env_with(vec![
            (1, tptr(tint())),
            (2, tf64()),
            (3, tlong()),
            (4, tstruct(9)),
        ]);
        let negp = ClightStmt::Sset(3, unop(U::Oneg, tv(1, tptr(tint())), tlong()));
        assert!(err_fams(&wt_check_stmt(&negp, &env)).contains(&"invalid-unop"));
        let notf = ClightStmt::Sset(3, unop(U::Onotint, tv(2, tf64()), tlong()));
        assert!(err_fams(&wt_check_stmt(&notf, &env)).contains(&"invalid-unop"));
        // struct condition
        let badif = ClightStmt::Sifthenelse(
            tv(4, tstruct(9)),
            Box::new(ClightStmt::Sskip),
            Box::new(ClightStmt::Sskip),
        );
        assert_eq!(
            err_fams(&wt_check_stmt(&badif, &env)),
            vec!["bad-condition"]
        );
        // pointer condition is fine
        let okif = ClightStmt::Sifthenelse(
            tv(1, tptr(tint())),
            Box::new(ClightStmt::Sskip),
            Box::new(ClightStmt::Sskip),
        );
        assert!(err_fams(&wt_check_stmt(&okif, &env)).is_empty());
    }

    #[test]
    fn walker_switch_and_casts() {
        let env = env_with(vec![(1, tptr(tint())), (2, tf64()), (3, tlong())]);
        let sw = ClightStmt::Sswitch(tv(1, tptr(tint())), vec![(Some(0), ClightStmt::Sskip)]);
        assert_eq!(err_fams(&wt_check_stmt(&sw, &env)), vec!["bad-switch"]);
        let sw_ok = ClightStmt::Sswitch(tv(3, tlong()), vec![(Some(0), ClightStmt::Sskip)]);
        assert!(err_fams(&wt_check_stmt(&sw_ok, &env)).is_empty());
        // (int *)v2 with v2: double -> bad-cast ("cannot convert to a pointer type")
        let badcast = ClightStmt::Sset(3, cast(tv(2, tf64()), tptr(tint())));
        let errs = wt_check_stmt(&badcast, &env);
        assert!(err_fams(&errs).contains(&"bad-cast"));
        // (double)v1 with v1: ptr -> ptr-float
        let p2f = ClightStmt::Sset(2, cast(tv(1, tptr(tint())), tf64()));
        assert!(err_fams(&wt_check_stmt(&p2f, &env)).contains(&"ptr-float"));
        // (long)v1 is fine
        let ok = ClightStmt::Sset(3, cast(tv(1, tptr(tint())), tlong()));
        assert!(err_fams(&wt_check_stmt(&ok, &env)).is_empty());
    }

    #[test]
    fn authoritative_global_type_overrides_stale_load_annotation() {
        let global = 0x28200usize;
        let mut env = env_with(vec![(1, tlong())]);
        env.globals_by_ident.insert(global, tptr(ti8()));

        // The load's MAny64 annotation says `long`, but the declaration gcc
        // sees is `char *optarg`, so the ident-addressed object load must reject
        // the pointer-to-double cast.
        let by_ident = ClightStmt::Sset(1, cast(ClightExpr::Evar(global, tlong()), tf64()));
        assert!(err_fams(&wt_check_stmt(&by_ident, &env)).contains(&"ptr-float"));
    }

    #[test]
    fn walker_void_and_assign_compat() {
        let env = env_with(vec![
            (1, tint()),
            (2, tptr(tint())),
            (3, tf64()),
            (4, tptr(ClightType::Tvoid)),
        ]);
        // assigning a void expression
        let voidcall = ClightExpr::EvarSymbol("g".into(), ClightType::Tvoid);
        let badset = ClightStmt::Sset(1, voidcall.clone());
        assert_eq!(
            err_fams(&wt_check_stmt(&badset, &env)),
            vec!["void-expression"]
        );
        // double -> ptr assignment: incompatible-types
        let f2p = ClightStmt::Sset(2, tv(3, tf64()));
        assert_eq!(
            err_fams(&wt_check_stmt(&f2p, &env)),
            vec!["incompatible-types"]
        );
        // ptr -> double assignment: ptr-float
        let p2f = ClightStmt::Sset(3, tv(2, tptr(tint())));
        assert_eq!(err_fams(&wt_check_stmt(&p2f, &env)), vec!["ptr-float"]);
        // int -> ptr assignment compiles under -w: clean
        let i2p = ClightStmt::Sset(2, tv(1, tint()));
        assert!(err_fams(&wt_check_stmt(&i2p, &env)).is_empty());
        // A conversion to void is legal only when its value is discarded.  A
        // dereferenced void pointer cannot designate an assignable C object.
        let void_lvalue = ClightStmt::Sassign(
            deref(tv(4, tptr(ClightType::Tvoid)), ClightType::Tvoid),
            c32(0),
        );
        assert_eq!(
            err_fams(&wt_check_stmt(&void_lvalue, &env)),
            vec!["void-expression"]
        );
        // struct(1) -> struct(2) by value: incompatible-types
        let env2 = env_with(vec![(1, tstruct(1)), (2, tstruct(2))]);
        let s2s = ClightStmt::Sset(2, tv(1, tstruct(1)));
        assert_eq!(
            err_fams(&wt_check_stmt(&s2s, &env2)),
            vec!["incompatible-types"]
        );
    }

    #[test]
    fn walker_calls() {
        let sig = tfn(vec![tint(), tptr(tint())], tint());
        let callee = ClightExpr::EvarSymbol("f".into(), sig.clone());
        let env = env_with(vec![(1, tint()), (2, tptr(tint())), (9, tint())]);
        // call through a long-typed object
        let badf = ClightExpr::EvarSymbol("g".into(), tlong());
        let bad = ClightStmt::Scall(None, badf, vec![]);
        assert_eq!(
            err_fams(&wt_check_stmt(&bad, &env)),
            vec!["call-through-non-function"]
        );
        // arity
        let toofew = ClightStmt::Scall(None, callee.clone(), vec![c32(1)]);
        assert_eq!(
            err_fams(&wt_check_stmt(&toofew, &env)),
            vec!["arity-too-few"]
        );
        let toomany = ClightStmt::Scall(
            None,
            callee.clone(),
            vec![c32(1), tv(2, tptr(tint())), c32(3)],
        );
        assert_eq!(
            err_fams(&wt_check_stmt(&toomany, &env)),
            vec!["arity-too-many"]
        );
        // vararg callee: extra args fine, fewer than fixed is an error
        let vsig = tfn_vararg(vec![tptr(ti8())], tint(), 1);
        let vcallee = ClightExpr::EvarSymbol("printf".into(), vsig);
        let v_ok = ClightStmt::Scall(
            None,
            vcallee.clone(),
            vec![tv(2, tptr(tint())), c32(1), c32(2)],
        );
        assert!(err_fams(&wt_check_stmt(&v_ok, &env)).is_empty());
        let v_few = ClightStmt::Scall(None, vcallee, vec![]);
        assert_eq!(
            err_fams(&wt_check_stmt(&v_few, &env)),
            vec!["arity-too-few"]
        );
        // capturing a void result
        let vsig2 = tfn(vec![], ClightType::Tvoid);
        let vc = ClightExpr::EvarSymbol("h".into(), vsig2);
        let cap = ClightStmt::Scall(Some(9), vc.clone(), vec![]);
        assert_eq!(
            err_fams(&wt_check_stmt(&cap, &env)),
            vec!["void-expression"]
        );
        let nocap = ClightStmt::Scall(None, vc, vec![]);
        assert!(err_fams(&wt_check_stmt(&nocap, &env)).is_empty());
        // call via function POINTER temp: fine
        let fptr = tptr(sig);
        let env2 = env_with(vec![(4, fptr.clone())]);
        let viaptr = ClightStmt::Scall(
            None,
            tv(4, fptr),
            vec![c32(1), ClightExpr::EconstLong(0, tptr(tint()))],
        );
        assert!(err_fams(&wt_check_stmt(&viaptr, &env2)).is_empty());
        // env override beats the annotation (P2 wires CalleeSignature here)
        let mut env3 = env_with(vec![]);
        env3.callee = Some(tlong());
        let overridden = ClightStmt::Scall(None, callee, vec![c32(1), c32(2)]);
        assert_eq!(
            err_fams(&wt_check_stmt(&overridden, &env3)),
            vec!["call-through-non-function"]
        );
    }

    #[test]
    fn walker_returns_and_addrof() {
        let mut env = env_with(vec![(1, tptr(tint())), (2, tf64())]);
        env.ret = Some(tf64());
        // returning a pointer from a double fn: ptr-float error
        let r = ClightStmt::Sreturn(Some(tv(1, tptr(tint()))));
        assert_eq!(err_fams(&wt_check_stmt(&r, &env)), vec!["ptr-float"]);
        // returning double from double fn: clean
        let ok = ClightStmt::Sreturn(Some(tv(2, tf64())));
        assert!(err_fams(&wt_check_stmt(&ok, &env)).is_empty());
        // return-with-value in void fn / valueless in non-void: warnings, not errors
        let mut venv = env_with(vec![(2, tf64())]);
        venv.ret = Some(ClightType::Tvoid);
        let rv = wt_check_stmt(&ClightStmt::Sreturn(Some(tv(2, tf64()))), &venv);
        assert!(err_fams(&rv).is_empty());
        assert!(rv.iter().any(|e| e.kind == WtErrorKind::ReturnVoidMismatch));
        let rn = wt_check_stmt(&ClightStmt::Sreturn(None), &env);
        assert!(err_fams(&rn).is_empty());
        assert!(rn.iter().any(|e| e.kind == WtErrorKind::ReturnVoidMismatch));
        // & of a non-lvalue
        let addr = ClightStmt::Sset(
            1,
            ClightExpr::Eaddrof(Box::new(bin(B::Oadd, c32(1), c32(2), tint())), tptr(tint())),
        );
        assert!(err_fams(&wt_check_stmt(&addr, &env)).contains(&"addrof-non-lvalue"));
        // &temp is fine in printed C
        let addrt = ClightStmt::Sset(
            1,
            ClightExpr::Eaddrof(Box::new(tv(2, tf64())), tptr(tf64())),
        );
        let errs = wt_check_stmt(&addrt, &env);
        // &double -> int* decl: pointer-to-pointer assign, compiles under -w
        assert!(err_fams(&errs).is_empty());
    }

    #[test]
    fn walker_recovery_is_total_and_localized() {
        // nested breakage: one error per ill-typed node, recovery keeps walking
        let env = env_with(vec![(1, tlong()), (2, tint())]);
        // v2 = *( *(v1) ) : inner deref errors + recovers with its annotation (int*), so the outer deref then succeeds -- exactly one diagnosis.
        let nested = ClightStmt::Sset(2, deref(deref(tv(1, tlong()), tptr(tint())), tint()));
        let errs = wt_check_stmt(&nested, &env);
        assert_eq!(err_fams(&errs), vec!["deref-of-scalar"]);
        // unbound temp: warning + annotation recovery
        let unb = ClightStmt::Sset(2, tv(42, tint()));
        let errs = wt_check_stmt(&unb, &env);
        assert!(err_fams(&errs).is_empty());
        assert!(errs.iter().any(|e| e.kind == WtErrorKind::UnboundTemp));
    }

    #[test]
    fn walker_econdition() {
        let env = env_with(vec![
            (1, tint()),
            (2, tptr(tint())),
            (3, tf64()),
            (4, tlong()),
        ]);
        // c ? ptr : double -> bad-conditional
        let bad = ClightStmt::Sset(
            4,
            ClightExpr::Econdition(
                Box::new(tv(1, tint())),
                Box::new(tv(2, tptr(tint()))),
                Box::new(tv(3, tf64())),
                tlong(),
            ),
        );
        assert_eq!(
            err_fams(&wt_check_stmt(&bad, &env)),
            vec!["bad-conditional"]
        );
        // c ? int : double -> clean (binarith)
        let ok = ClightStmt::Sset(
            3,
            ClightExpr::Econdition(
                Box::new(tv(1, tint())),
                Box::new(tv(1, tint())),
                Box::new(tv(3, tf64())),
                tf64(),
            ),
        );
        assert!(err_fams(&wt_check_stmt(&ok, &env)).is_empty());
    }
}
