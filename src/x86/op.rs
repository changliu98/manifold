use crate::x86::types::{Ident, Typ, Z};
use std::ops::{Add, Div, Mul, Sub};

pub type Ptrofs = i64;

/// Arithmetic operation whose signed x86 overflow flag can be reconstructed
/// from the post-operation result.  Register forms carry the unchanged source
/// as a condition argument; immediate forms carry the decoded constant here.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum OverflowArithmetic {
    Add,
    Sub,
    AddImmediate(i64),
    SubImmediate(i64),
    Neg,
}

/// Boolean result materialized by a SETcc that consumes flags from x86 TEST.
///
/// TEST's zero/sign flags describe the complete width-truncated bitwise AND,
/// while its parity flag describes only that result's low byte.  Keeping this
/// distinction explicit avoids pretending parity is an ordinary comparison or
/// re-reading an operand register after an intervening SETcc has overwritten
/// one of its byte lanes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TestResultCondition {
    Zero,
    NonZero,
    Sign,
    NonSign,
    EvenParity,
    OddParity,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Condition {
    Ccomp(Comparison),
    Ccompu(Comparison),
    Ccompimm(Comparison, i64),
    Ccompuimm(Comparison, i64),
    Ccompl(Comparison),
    Ccomplu(Comparison),
    Ccomplimm(Comparison, i64),
    Ccompluimm(Comparison, i64),
    Ccompf(Comparison),
    Cnotcompf(Comparison),
    Ccompfs(Comparison),
    Cnotcompfs(Comparison),
    Cmaskzero(i64),
    Cmasknotzero(i64),
    // OF tests (JO/JNO) have no faithful CompCert encoding; these opaque variants exist to keep both Jcc edges.
    Coverflow,
    Cnotoverflow,
    // Exact x86 OF tests recovered from a proven flag-producing arithmetic
    // operation.  The width is the decoded operand width in bytes.
    Carithoverflow(OverflowArithmetic, i64),
    Cnarithoverflow(OverflowArithmetic, i64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Comparison {
    Ceq,
    Cne,
    Clt,
    Cle,
    Cgt,
    Cge,
    #[allow(dead_code)]
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Addressing {
    Aindexed(Z),
    Aindexed2(Z),
    Ascaled(Z, Z),
    Aindexed2scaled(Z, Z),
    Aglobal(Ident, Ptrofs),
    Abased(Ident, Ptrofs),
    Abasedscaled(Z, Ident, Ptrofs),
    Ainstack(Ptrofs),
    #[allow(dead_code)]
    Unknown,
}

#[derive(Debug, Clone, Copy)]
pub struct F64(f64);

impl std::hash::Hash for F64 {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.0.to_bits());
    }
}

impl PartialEq for F64 {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bits() == other.0.to_bits()
    }
}

impl PartialOrd for F64 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for F64 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.total_cmp(&other.0)
    }
}

impl Eq for F64 {}

impl From<f64> for F64 {
    fn from(f: f64) -> Self {
        F64(f)
    }
}

impl F64 {
    pub fn as_f64(&self) -> f64 {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct F32(f32);

impl PartialOrd for F32 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for F32 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.total_cmp(&other.0)
    }
}

impl Eq for F32 {}

impl From<f32> for F32 {
    fn from(f: f32) -> Self {
        F32(f)
    }
}

impl F32 {
    pub fn as_f32(&self) -> f32 {
        self.0
    }
}

impl Add for F32 {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        F32(self.0 + other.0)
    }
}

impl Sub for F32 {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        F32(self.0 - other.0)
    }
}

impl Mul for F32 {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        F32(self.0 * other.0)
    }
}

impl Div for F32 {
    type Output = Self;
    fn div(self, other: Self) -> Self {
        F32(self.0 / other.0)
    }
}

impl std::hash::Hash for F32 {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u32(self.0.to_bits());
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Operation {
    Omove,
    Ointconst(i64),
    Olongconst(i64),
    #[allow(dead_code)]
    Ofloatconst(F64),
    #[allow(dead_code)]
    Osingleconst(F32),
    Oindirectsymbol(Ident),
    Ocast8signed,
    Ocast8unsigned,
    Ocast16signed,
    Ocast16unsigned,
    Oneg,
    Oadd,
    Oaddimm(i64),
    Osub,
    Omul,
    Omulimm(i64),
    Omulhs,
    Omulhu,
    Odiv,
    Odivu,
    Omod,
    Omodu,
    Odivimm(i64),
    Odivuimm(i64),
    Omodimm(i64),
    Omoduimm(i64),
    Oand,
    Oandimm(i64),
    Oor,
    Oorimm(i64),
    Oxor,
    Oxorimm(i64),
    Onot,
    Oshl,
    Oshlimm(i64),
    Oshr,
    Oshrimm(i64),
    Oshrximm(i64),
    Oshru,
    Oshruimm(i64),
    Ororimm(i64),
    Oshldimm(i64),
    Olea(Addressing),
    #[allow(dead_code)]
    Omakelong,
    Olowlong,
    #[allow(dead_code)]
    Ohighlong,
    Ocast32signed,
    Ocast32unsigned,
    Onegl,
    Oaddl,
    Oaddlimm(i64),
    Osubl,
    Omull,
    Omullimm(i64),
    Omullhs,
    Omullhu,
    Odivl,
    Odivlu,
    Omodl,
    Omodlu,
    Odivlimm(i64),
    Odivluimm(i64),
    Omodlimm(i64),
    Omodluimm(i64),
    Oandl,
    Oandlimm(i64),
    Oorl,
    Oorlimm(i64),
    Oxorl,
    Oxorlimm(i64),
    Onotl,
    Oshll,
    Oshllimm(i64),
    Oshrl,
    Oshrlimm(i64),
    Oshrxlimm(i64),
    Oshrlu,
    Oshrluimm(i64),
    Ororlimm(i64),
    Oleal(Addressing),
    Onegf,
    Oabsf,
    Oaddf,
    Osubf,
    Omulf,
    Odivf,
    Omaxf,
    Ominf,
    Onegfs,
    Oabsfs,
    Oaddfs,
    Osubfs,
    Omulfs,
    Odivfs,
    Osingleoffloat,
    Ofloatofsingle,
    Ointoffloat,
    Ofloatofint,
    Ointofsingle,
    Osingleofint,
    Olongoffloat,
    Ofloatoflong,
    Olongofsingle,
    Osingleoflong,
    /// Materialize one TEST-derived flag predicate as 0/1.  The two operands
    /// are the already-loaded memory value and the register value captured at
    /// the TEST instruction.  `width` is the TEST operand width in bytes and
    /// `rhs_shift` is eight only for the legacy AH/BH/CH/DH register views.
    Otestflags(TestResultCondition, usize, usize),
    /// Deferred flag capture at Mach/Linear, completed with the original
    /// memory read as operand 2 at RTL. An incomplete expansion stays opaque.
    Oflagselect(crate::decompile::effects::flags::FlagSelect),
    Ocmp(Condition),
    Osel(Condition, Typ),
}
