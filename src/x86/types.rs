
pub type Address = u64;
pub type Size = usize;
pub type Symbol = &'static str;
use crate::x86::asm::{Ireg, TestCond};
use crate::x86::mach::Mreg;
use crate::x86::op::{Addressing, Comparison, Condition, Operation, Ptrofs, F32, F64};
use either::Either;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use strum_macros::EnumString;
pub use crate::decompile::passes::csh_pass::*;
pub type Ident = usize;

pub type MregArgs = Arc<Vec<Mreg>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ParamType {
    Pointer,
    StructPointer(usize),
    Typed(XType),
    Integer,
    #[allow(dead_code)]
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Displacement {
    Const(i64),
    Symbol { ident: Ident, ofs: i64 },
}

impl From<i64> for Displacement {
    fn from(d: i64) -> Self {
        Displacement::Const(d)
    }
}

impl From<(Ident, i64)> for Displacement {
    fn from((ident, ofs): (Ident, i64)) -> Self {
        Displacement::Symbol { ident, ofs }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Addrmode {
    pub base: Option<Ireg>,
    pub index: Option<(Ireg, i64)>,
    pub disp: Displacement,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MachInst {
    Mgetstack(i64, Typ, Mreg),
    Msetstack(Mreg, i64, Typ),
    #[allow(dead_code)]
    Mgetparam(i64, Typ, Mreg),
    Mreturn,
    Mgoto(Symbol),
    Mtailcall(Either<Mreg, Either<Symbol, i64>>),
    Mcall(Either<Mreg, Either<Symbol, i64>>),
    Mstore(MemoryChunk, Addressing, MregArgs, Mreg),
    Mload(MemoryChunk, Addressing, MregArgs, Mreg),
    Mcond(Condition, MregArgs, Symbol),
    Mop(Operation, MregArgs, Mreg),
    Mbuiltin(String, Vec<BuiltinArg<Mreg>>, BuiltinArg<Mreg>),
    Mlabel(String),
}

impl Default for MachInst {
    fn default() -> Self {
        MachInst::Mreturn
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, EnumString)]
pub enum Typ {
    Tint,
    Tfloat,
    Tlong,
    Tsingle,
    Tany32,
    Tany64,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum XType {
    Xbool,
    Xint8signed,
    Xint8unsigned,
    Xint16signed,
    Xint16unsigned,
    Xint,
    Xintunsigned,
    Xfloat,
    Xlong,
    Xlongunsigned,
    Xsingle,
    Xptr,
    Xcharptr,
    Xintptr,
    Xfloatptr,
    Xsingleptr,
    Xfuncptr,
    Xany32,
    Xany64,
    Xvoid,
    XstructPtr(StructId),
}

pub type StructId = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum EdgeType {
    Embed,
    Deref,
    Assign,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FieldType {
    Scalar(MemoryChunk),
    Pointer(Box<FieldType>),
    StructPointer(StructId),
    #[allow(dead_code)]
    EmbeddedStruct(StructId),
    #[allow(dead_code)]
    Array(Box<FieldType>, usize),
    #[allow(dead_code)]
    Union(Vec<FieldType>),
    #[allow(dead_code)]
    OpaqueBlob(usize),
    Unknown,
}

impl FieldType {
    pub fn size(&self, pointer_size: usize) -> usize {
        match self {
            FieldType::Scalar(chunk) => match chunk {
                MemoryChunk::MBool | MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned => 1,
                MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned => 2,
                MemoryChunk::MInt32 | MemoryChunk::MFloat32 | MemoryChunk::MAny32 => 4,
                MemoryChunk::MInt64 | MemoryChunk::MFloat64 | MemoryChunk::MAny64 => 8,
                MemoryChunk::Unknown => 4,
            },
            FieldType::Pointer(_) | FieldType::StructPointer(_) => pointer_size,
            FieldType::EmbeddedStruct(_) => pointer_size,
            FieldType::Array(elem, count) => elem.size(pointer_size) * count,
            FieldType::Union(variants) => variants.iter().map(|v| v.size(pointer_size)).max().unwrap_or(4),
            FieldType::OpaqueBlob(size) => *size,
            FieldType::Unknown => 4,
        }
    }
    
    pub fn to_type_string(&self) -> String {
        match self {
            FieldType::Scalar(chunk) => match chunk {
                MemoryChunk::MBool => "int_IBool".to_string(),
                MemoryChunk::MInt8Signed => "int_I8".to_string(),
                MemoryChunk::MInt8Unsigned => "int_I8_unsigned".to_string(),
                MemoryChunk::MInt16Signed => "int_I16".to_string(), 
                MemoryChunk::MInt16Unsigned => "int_I16_unsigned".to_string(),
                MemoryChunk::MInt32 | MemoryChunk::MAny32 => "int_I32".to_string(),
                MemoryChunk::MInt64 | MemoryChunk::MAny64 => "int_I64".to_string(),
                MemoryChunk::MFloat32 => "float_F32".to_string(),
                MemoryChunk::MFloat64 => "float_F64".to_string(),
                MemoryChunk::Unknown => "int_I32".to_string(),
            },
            FieldType::Pointer(inner) => format!("ptr_{}", inner.to_type_string()),
            FieldType::StructPointer(struct_id) => format!("ptr_struct_{:x}", struct_id),
            FieldType::EmbeddedStruct(struct_id) => format!("struct_{:x}", struct_id),
            FieldType::Array(elem, _) => format!("arr_{}", elem.to_type_string()),
            FieldType::Union(variants) => {
                variants.first().map(|v| v.to_type_string()).unwrap_or_else(|| "int_I32".to_string())
            }
            FieldType::OpaqueBlob(size) => format!("blob_{}", size),
            FieldType::Unknown => "int_I32".to_string(),
        }
    }
}

impl Default for FieldType {
    fn default() -> Self {
        FieldType::Unknown
    }
}

pub type Z = i64;
pub type Positive = i64;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum MemoryChunk {
    MBool,
    MInt8Signed,
    MInt8Unsigned,
    MInt16Signed,
    MInt16Unsigned,
    MInt32,
    MInt64,
    MFloat32,
    MFloat64,
    MAny32,
    MAny64,
    #[allow(dead_code)]
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Signature {
    pub sig_args: Arc<Vec<XType>>,
    pub sig_res: XType,
    pub sig_cc: CallConv,
}
impl Default for Signature {
    fn default() -> Self {
        Signature {
            sig_args: Arc::new(vec![]),
            sig_res: XType::Xvoid,
            sig_cc: CallConv::default(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CallConv {
    pub varargs: Option<i64>,
    pub unproto: bool,
    pub structured_ret: bool,
}
impl Default for CallConv {
    fn default() -> Self {
        CallConv {
            varargs: None,
            unproto: false,
            structured_ret: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[allow(dead_code)]
pub enum ExternalFunction {
    EFExternal(Arc<str>, Signature),
    EFBuiltin(Arc<str>, Signature),
    EFRuntime(Arc<str>, Signature),
    EFVLoad(MemoryChunk),
    EFVStore(MemoryChunk),
    EFMalloc,
    EFFree,
    EFMemcpy(Positive, Positive),
    EFAnnot(Positive, Arc<str>, Vec<Typ>),
    EFAnnotVal(Positive, Arc<str>, Typ),
    EFInlineAsm(Arc<str>, Signature, Vec<String>),
    EFDebug(Positive, Ident, Vec<Typ>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[allow(dead_code)]
pub enum BuiltinArg<T> {
    BA(T),
    BAInt(i64),
    BALong(i64),
    BAFloat(F64),
    BASingle(F32),
    BALoadStack(MemoryChunk, Ptrofs),
    BAAddrStack(Ptrofs),
    BALoadGlobal(MemoryChunk, Ident, Ptrofs),
    BAAddrGlobal(Ident, Ptrofs),
    BASplitLong(Box<BuiltinArg<T>>, Box<BuiltinArg<T>>),
    BAAddPtr(Box<BuiltinArg<T>>, Box<BuiltinArg<T>>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Operand {
    Register(&'static str),
    Immediate(i64),
    Memory(Box<Operand>, &'static str),
    Symbol(&'static str),
}

impl From<&'static str> for Operand {
    fn from(s: &'static str) -> Self {
        if s.starts_with("$") {
            let s = s.replace("$", "");
            Operand::Immediate(s.parse::<i64>().unwrap())
        } else if s.contains("(") {
            let parts: Vec<&str> = s.split('(').collect();
            let offset = parts[0].trim();
            let base = parts[1].trim_end_matches(')');
            Operand::Memory(Box::new(Operand::from(base)), offset)
        } else if s.starts_with("%") {
            Operand::Register(s)
        } else {
            Operand::Symbol(s)
        }
    }
}

pub fn condition_for_testcond(test: TestCond) -> Condition {
    condition_for_testcond_sized(test, false)
}

pub fn condition_for_testcond_sized(test: TestCond, is_64bit: bool) -> Condition {
    match test {
        TestCond::CondE => {
            if is_64bit { Condition::Ccompl(Comparison::Ceq) } else { Condition::Ccomp(Comparison::Ceq) }
        }
        TestCond::CondNe => {
            if is_64bit { Condition::Ccompl(Comparison::Cne) } else { Condition::Ccomp(Comparison::Cne) }
        }
        TestCond::CondB => {
            if is_64bit { Condition::Ccomplu(Comparison::Clt) } else { Condition::Ccompu(Comparison::Clt) }
        }
        TestCond::CondBe => {
            if is_64bit { Condition::Ccomplu(Comparison::Cle) } else { Condition::Ccompu(Comparison::Cle) }
        }
        TestCond::CondA => {
            if is_64bit { Condition::Ccomplu(Comparison::Cgt) } else { Condition::Ccompu(Comparison::Cgt) }
        }
        TestCond::CondAe => {
            if is_64bit { Condition::Ccomplu(Comparison::Cge) } else { Condition::Ccompu(Comparison::Cge) }
        }
        TestCond::CondL => {
            if is_64bit { Condition::Ccompl(Comparison::Clt) } else { Condition::Ccomp(Comparison::Clt) }
        }
        TestCond::CondLe => {
            if is_64bit { Condition::Ccompl(Comparison::Cle) } else { Condition::Ccomp(Comparison::Cle) }
        }
        TestCond::CondG => {
            if is_64bit { Condition::Ccompl(Comparison::Cgt) } else { Condition::Ccomp(Comparison::Cgt) }
        }
        TestCond::CondGe => {
            if is_64bit { Condition::Ccompl(Comparison::Cge) } else { Condition::Ccomp(Comparison::Cge) }
        }
        TestCond::CondNp => Condition::Cmasknotzero(0),
        TestCond::CondP => Condition::Cmaskzero(0),
        TestCond::Unknown => Condition::Ccomp(Comparison::Unknown),
    }
}

pub fn negate_testcond(c: TestCond) -> TestCond {
    match c {
        TestCond::CondE  => TestCond::CondNe,
        TestCond::CondNe => TestCond::CondE,
        TestCond::CondB  => TestCond::CondAe,
        TestCond::CondBe => TestCond::CondA,
        TestCond::CondAe => TestCond::CondB,
        TestCond::CondA  => TestCond::CondBe,
        TestCond::CondL  => TestCond::CondGe,
        TestCond::CondLe => TestCond::CondG,
        TestCond::CondGe => TestCond::CondL,
        TestCond::CondG  => TestCond::CondLe,
        TestCond::CondP  => TestCond::CondNp,
        TestCond::CondNp => TestCond::CondP,
        TestCond::Unknown => TestCond::Unknown,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Slot {
    Local,
    Incoming,
    #[allow(dead_code)]
    Outgoing,
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LinearInst {
    Lgetstack(Slot, Z, Typ, Mreg),
    Lsetstack(Mreg, Slot, Z, Typ),
    Lop(Operation, MregArgs, Mreg),
    Lload(MemoryChunk, Addressing, MregArgs, Mreg),
    Lstore(MemoryChunk, Addressing, MregArgs, Mreg),
    Lcall(Either<Mreg, Either<Symbol, u64>>),
    Ltailcall(Either<Mreg, Either<Symbol, u64>>),
    Lbuiltin(String, Vec<BuiltinArg<Mreg>>, BuiltinArg<Mreg>),
    Llabel(String),
    Lgoto(Symbol),
    Lcond(Condition, MregArgs, Symbol),
    #[allow(dead_code)]
    Ljumptable(Mreg, Vec<Symbol>),
    Lreturn,
}

pub type Node = u64;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LTLInst {
    Lop(Operation, MregArgs, Mreg),
    Lload(MemoryChunk, Addressing, MregArgs, Mreg),
    Lgetstack(Slot, Z, Typ, Mreg),
    Lsetstack(Mreg, Slot, Z, Typ),
    Lstore(MemoryChunk, Addressing, MregArgs, Mreg),
    Lcall(Either<Mreg, Either<u64, Symbol>>),
    Ltailcall(Either<Mreg, Either<u64, Symbol>>),
    Lbuiltin(String, Vec<BuiltinArg<Mreg>>, BuiltinArg<Mreg>),
    Lbranch(Either<Symbol, Node>),
    Lcond(Condition, MregArgs, Either<Symbol, Node>, Either<Symbol, Node>),
    Ljumptable(Mreg, Vec<Node>),
    Lreturn,
}

pub type RTLReg = u64;

pub type Args = Arc<Vec<RTLReg>>;

pub type Targets = Arc<Vec<Node>>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RTLInst {
    Inop,
    Iop(Operation, Args, RTLReg),
    Iload(MemoryChunk, Addressing, Args, RTLReg),
    Istore(MemoryChunk, Addressing, Args, RTLReg),
    Icall(Option<Signature>, Either<RTLReg, Either<u64, Symbol>>, Args, Option<RTLReg>, Node),
    Itailcall(Option<Signature>, Either<RTLReg, Either<u64, Symbol>>, Args),
    Ibuiltin(String, Vec<BuiltinArg<RTLReg>>, BuiltinArg<RTLReg>),
    Icond(Condition, Args, Either<Symbol, Node>, Either<Symbol, Node>),
    Ijumptable(RTLReg, Targets),
    Ibranch(Either<Symbol, Node>),
    Ireturn(RTLReg),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constant {
    Ointconst(i64),
    Ofloatconst(F64),
    Osingleconst(F32),
    Olongconst(i64),
    Oaddrsymbol(Ident, Ptrofs),
    Oaddrstack(Ptrofs),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[allow(dead_code)]
pub enum CminorUnop {
    Ocast8unsigned,
    Ocast8signed,
    Ocast16unsigned,
    Ocast16signed,
    Onegint,
    Onotint,
    Onegf,
    Oabsf,
    Onegfs,
    Oabsfs,
    Osingleoffloat,
    Ofloatofsingle,
    Ointoffloat,
    Ointuoffloat,
    Ofloatofint,
    Ofloatofintu,
    Ointofsingle,
    Ointuofsingle,
    Osingleofint,
    Osingleofintu,
    Onegl,
    Onotl,
    Ointoflong,
    Olongofint,
    Olongofintu,
    Olongoffloat,
    Olonguoffloat,
    Ofloatoflong,
    Ofloatoflongu,
    Olongofsingle,
    Olonguofsingle,
    Osingleoflong,
    Osingleoflongu,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CminorBinop {
    Oadd,
    Osub,
    Omul,
    Odiv,
    Odivu,
    Omod,
    Omodu,
    Oand,
    Oor,
    Oxor,
    Oshl,
    Oshr,
    Oshru,
    Oaddf,
    Osubf,
    Omulf,
    Odivf,
    Oaddfs,
    Osubfs,
    Omulfs,
    Odivfs,
    Omaxf,
    Ominf,
    Oaddl,
    Osubl,
    Omull,
    Odivl,
    Odivlu,
    Omodl,
    Omodlu,
    Oandl,
    Oorl,
    Oxorl,
    Oshll,
    Oshrl,
    Oshrlu,
    Omulhs,
    Omulhu,
    Omullhs,
    Omullhu,
    Ocmp(Comparison),
    Ocmpu(Comparison),
    Ocmpf(Comparison),
    Ocmpnotf(Comparison),
    Ocmpfs(Comparison),
    Ocmpnotfs(Comparison),
    Ocmpl(Comparison),
    Ocmplu(Comparison),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CminorExpr {
    Evar(RTLReg),
    Econst(Constant),
    Eunop(CminorUnop, RTLReg),
    Ebinop(CminorBinop, RTLReg, RTLReg),
    Eop(Operation, Args),
    Eload(MemoryChunk, Addressing, Args),
    #[allow(dead_code)]
    Eexternal(u64, Option<Signature>, Args),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CminorStmt {
    Sassign(RTLReg, CminorExpr),
    Sstore(MemoryChunk, Addressing, Args, RTLReg),
    Scall(
        Option<RTLReg>,
        Option<Signature>,
        Either<RTLReg, Either<u64, Symbol>>,
        Args,
    ),
    Stailcall(
        Option<Signature>,
        Either<RTLReg, Either<u64, Symbol>>,
        Args,
    ),
    Sbuiltin(
        Option<RTLReg>,
        String,
        Vec<BuiltinArg<RTLReg>>,
        BuiltinArg<RTLReg>,
    ),
    Sifthenelse(Condition, Args, Node, Node),
    #[allow(dead_code)]
    Sbranch(Condition, Args, Node, Node),
    Sjumptable(RTLReg, Targets),
    Sjump(Node),
    Sreturn(RTLReg),
    Snop,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CsharpminorExpr {
    Evar(RTLReg),
    #[allow(dead_code)]
    Eaddrof(Ident),
    Econst(Constant),
    Eunop(CminorUnop, Box<CsharpminorExpr>),
    Ebinop(CminorBinop, Box<CsharpminorExpr>, Box<CsharpminorExpr>),
    Eload(MemoryChunk, Box<CsharpminorExpr>),
    Econdition(Box<CsharpminorExpr>, Box<CsharpminorExpr>, Box<CsharpminorExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CsharpminorStmt {
    Sset(RTLReg, CsharpminorExpr),
    Sstore(MemoryChunk, CsharpminorExpr, CsharpminorExpr),
    Scall(
        Option<RTLReg>,
        Option<Signature>,
        Either<CsharpminorExpr, Either<u64, Symbol>>,
        Vec<CsharpminorExpr>,
    ),
    Stailcall(
        Option<Signature>,
        Either<CsharpminorExpr, Either<u64, Symbol>>,
        Vec<CsharpminorExpr>,
    ),
    Sbuiltin(
        Option<RTLReg>,
        String,
        Vec<BuiltinArg<CsharpminorExpr>>,
        BuiltinArg<CsharpminorExpr>,
    ),
    Scond(Condition, Vec<CsharpminorExpr>, Node, Node),
    #[allow(dead_code)]
    Sloophead(Node),
    Sjumptable(CsharpminorExpr, Targets),
    Sjump(Node),
    Sreturn(CsharpminorExpr),
    Sseq(Vec<CsharpminorStmt>),
    Snop,
    // Structured control flow (matching CompCert Csharpminor)
    Sifthenelse(Condition, Vec<CsharpminorExpr>, Box<CsharpminorStmt>, Box<CsharpminorStmt>),
    Sloop(Box<CsharpminorStmt>),
    Sbreak,
    Scontinue,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ClightSignedness {
    Signed,
    Unsigned,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ClightIntSize {
    I8,
    I16,
    I32,
    IBool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ClightFloatSize {
    F32,
    F64,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClightAttr {
    pub attr_volatile: bool,
    pub attr_alignas: Option<u64>,
}

impl Default for ClightAttr {
    fn default() -> Self {
        ClightAttr {
            attr_volatile: false,
            attr_alignas: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ClightType {
    Tvoid,
    Tint(ClightIntSize, ClightSignedness, ClightAttr),
    Tlong(ClightSignedness, ClightAttr),
    Tfloat(ClightFloatSize, ClightAttr),
    Tpointer(Arc<ClightType>, ClightAttr),
    #[allow(dead_code)]
    Tarray(Arc<ClightType>, Z, ClightAttr),
    Tfunction(Arc<Vec<ClightType>>, Arc<ClightType>, CallConv),
    Tstruct(Ident, ClightAttr),
    #[allow(dead_code)]
    Tunion(Ident, ClightAttr),
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ClightUnaryOp {
    Onotbool,
    Onotint,
    Oneg,
    Oabsfloat,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ClightBinaryOp {
    Oadd,
    Osub,
    Omul,
    Odiv,
    Omod,
    Oand,
    Oor,
    Oxor,
    Oshl,
    Oshr,
    Oeq,
    One,
    Olt,
    Ogt,
    Ole,
    Oge,
}

#[derive(Debug, Clone, Copy, Default)]
pub struct ClightFloat64(pub f64);

impl PartialEq for ClightFloat64 {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bits() == other.0.to_bits()
    }
}

impl Eq for ClightFloat64 {}

impl Hash for ClightFloat64 {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl From<f64> for ClightFloat64 {
    fn from(value: f64) -> Self {
        Self(value)
    }
}

impl From<ClightFloat64> for f64 {
    fn from(value: ClightFloat64) -> Self {
        value.0
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct ClightFloat32(pub f32);

impl PartialEq for ClightFloat32 {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bits() == other.0.to_bits()
    }
}

impl Eq for ClightFloat32 {}

impl Hash for ClightFloat32 {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl From<f32> for ClightFloat32 {
    fn from(value: f32) -> Self {
        Self(value)
    }
}

impl From<ClightFloat32> for f32 {
    fn from(value: ClightFloat32) -> Self {
        value.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ClightExpr {
    EconstInt(i32, ClightType),
    EconstFloat(ClightFloat64, ClightType),
    EconstSingle(ClightFloat32, ClightType),
    EconstLong(i64, ClightType),
    Evar(Ident, ClightType),
    EvarSymbol(String, ClightType),
    Etempvar(Ident, ClightType),
    Ederef(Box<ClightExpr>, ClightType),
    Eaddrof(Box<ClightExpr>, ClightType),
    Eunop(ClightUnaryOp, Box<ClightExpr>, ClightType),
    Ebinop(ClightBinaryOp, Box<ClightExpr>, Box<ClightExpr>, ClightType),
    Ecast(Box<ClightExpr>, ClightType),
    Efield(Box<ClightExpr>, Ident, ClightType),
    #[allow(dead_code)]
    Esizeof(ClightType, ClightType),
    #[allow(dead_code)]
    Ealignof(ClightType, ClightType),
    Econdition(Box<ClightExpr>, Box<ClightExpr>, Box<ClightExpr>, ClightType),
}

pub type ClightLabeledStatements = Vec<(Option<Z>, ClightStmt)>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ClightStmt {
    Sskip,
    Sassign(ClightExpr, ClightExpr),
    Sset(Ident, ClightExpr),
    Scall(Option<Ident>, ClightExpr, Vec<ClightExpr>),
    #[allow(dead_code)]
    Sbuiltin(
        Option<Ident>,
        ExternalFunction,
        Vec<ClightType>,
        Vec<ClightExpr>,
    ),
    Ssequence(Vec<ClightStmt>),
    Sifthenelse(ClightExpr, Box<ClightStmt>, Box<ClightStmt>),
    Sloop(Box<ClightStmt>, Box<ClightStmt>),
    Sbreak,
    Scontinue,
    Sreturn(Option<ClightExpr>),
    Sswitch(ClightExpr, ClightLabeledStatements),
    Slabel(Ident, Box<ClightStmt>),
    Sgoto(Ident),
}

pub fn is_long_operation(op: &Operation) -> bool {
    matches!(
        op,
        Operation::Olongconst(_)
            | Operation::Oaddl
            | Operation::Oaddlimm(_)
            | Operation::Osubl
            | Operation::Omull
            | Operation::Omullimm(_)
            | Operation::Omullhs
            | Operation::Omullhu
            | Operation::Odivl
            | Operation::Odivlu
            | Operation::Omodl
            | Operation::Omodlu
            | Operation::Oandl
            | Operation::Oandlimm(_)
            | Operation::Oorl
            | Operation::Oorlimm(_)
            | Operation::Oxorl
            | Operation::Oxorlimm(_)
            | Operation::Onotl
            | Operation::Oshll
            | Operation::Oshllimm(_)
            | Operation::Oshrl
            | Operation::Oshrlimm(_)
            | Operation::Oshrlu
            | Operation::Oshrluimm(_)
            | Operation::Oshrxlimm(_)
            | Operation::Ororlimm(_)
            | Operation::Onegl
            | Operation::Ocast32signed
            | Operation::Ocast32unsigned
            | Operation::Omakelong
            | Operation::Oleal(_)
            | Operation::Olongoffloat
            | Operation::Olongofsingle
    )
}

pub fn is_int_operation(op: &Operation) -> bool {
    matches!(
        op,
        Operation::Ointconst(_)
            | Operation::Oadd
            | Operation::Oaddimm(_)
            | Operation::Osub
            | Operation::Omul
            | Operation::Omulimm(_)
            | Operation::Omulhs
            | Operation::Omulhu
            | Operation::Odiv
            | Operation::Odivu
            | Operation::Omod
            | Operation::Omodu
            | Operation::Oand
            | Operation::Oandimm(_)
            | Operation::Oor
            | Operation::Oorimm(_)
            | Operation::Oxor
            | Operation::Oxorimm(_)
            | Operation::Onot
            | Operation::Oshl
            | Operation::Oshlimm(_)
            | Operation::Oshr
            | Operation::Oshrimm(_)
            | Operation::Oshru
            | Operation::Oshruimm(_)
            | Operation::Oshrximm(_)
            | Operation::Ororimm(_)
            | Operation::Oshldimm(_)
            | Operation::Oneg
            | Operation::Ocast8signed
            | Operation::Ocast8unsigned
            | Operation::Ocast16signed
            | Operation::Ocast16unsigned
            | Operation::Olowlong
            | Operation::Ohighlong
            | Operation::Ointoffloat
            | Operation::Ointofsingle
    )
}

pub fn is_float_operation(op: &Operation) -> bool {
    matches!(
        op,
        Operation::Ofloatconst(_)
            | Operation::Onegf
            | Operation::Oabsf
            | Operation::Oaddf
            | Operation::Osubf
            | Operation::Omulf
            | Operation::Odivf
            | Operation::Omaxf
            | Operation::Ominf
            | Operation::Ofloatofsingle
            | Operation::Ofloatofint
            | Operation::Ofloatoflong
    )
}

pub fn is_single_operation(op: &Operation) -> bool {
    matches!(
        op,
        Operation::Osingleconst(_)
            | Operation::Onegfs
            | Operation::Oabsfs
            | Operation::Oaddfs
            | Operation::Osubfs
            | Operation::Omulfs
            | Operation::Odivfs
            | Operation::Osingleoffloat
            | Operation::Osingleofint
            | Operation::Osingleoflong
    )
}

pub fn is_boolean_operation(op: &Operation) -> bool {
    matches!(op, Operation::Ocmp(_))
}

pub fn is_pointer_operation(op: &Operation) -> bool {
    matches!(
        op,
        Operation::Olea(_) | Operation::Oleal(_) | Operation::Oindirectsymbol(_)
    )
}

/// Convert MemoryChunk to byte width (1, 2, 4, or 8).
pub fn chunk_width(chunk: &MemoryChunk) -> u8 {
    match chunk {
        MemoryChunk::MBool => 1,
        MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned => 1,
        MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned => 2,
        MemoryChunk::MInt32 | MemoryChunk::MAny32 | MemoryChunk::MFloat32 => 4,
        MemoryChunk::MInt64 | MemoryChunk::MAny64 | MemoryChunk::MFloat64 => 8,
        MemoryChunk::Unknown => 0,
    }
}

/// Convert XType to byte width.
pub fn xtype_width(xtype: &XType) -> u8 {
    match xtype {
        XType::Xbool => 1,
        XType::Xint8signed | XType::Xint8unsigned => 1,
        XType::Xint16signed | XType::Xint16unsigned => 2,
        XType::Xint | XType::Xintunsigned | XType::Xsingle | XType::Xany32 => 4,
        XType::Xlong | XType::Xlongunsigned | XType::Xfloat | XType::Xany64 => 8,
        XType::Xptr | XType::Xcharptr | XType::Xintptr
        | XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr | XType::XstructPtr(_) => 8,
        XType::Xvoid => 0,
    }
}

pub fn is_unsigned_operation(op: &Operation) -> bool {
    matches!(
        op,
        Operation::Odivu
            | Operation::Omodu
            | Operation::Oshru
            | Operation::Oshruimm(_)
            | Operation::Omulhu
            | Operation::Ocast8unsigned
            | Operation::Ocast16unsigned
            | Operation::Ocast32unsigned
            | Operation::Odivlu
            | Operation::Omodlu
            | Operation::Oshrlu
            | Operation::Oshrluimm(_)
            | Operation::Omullhu
    )
}

pub fn is_signed_operation(op: &Operation) -> bool {
    matches!(
        op,
        Operation::Odiv
            | Operation::Omod
            | Operation::Oshr
            | Operation::Oshrimm(_)
            | Operation::Oshrximm(_)
            | Operation::Omulhs
            | Operation::Ocast8signed
            | Operation::Ocast16signed
            | Operation::Ocast32signed
            | Operation::Odivl
            | Operation::Omodl
            | Operation::Oshrl
            | Operation::Oshrlimm(_)
            | Operation::Oshrxlimm(_)
            | Operation::Omullhs
    )
}
