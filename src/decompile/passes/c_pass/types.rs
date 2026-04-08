

use std::collections::HashMap;

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct SourceLoc {
    pub file: Option<String>,
    pub line: Option<u32>,
    pub column: Option<u32>,
}

impl SourceLoc {
    pub fn unknown() -> Self {
        Self::default()
    }
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Signedness {
    Signed,
    Unsigned,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntSize {
    Char,
    Short,
    Int,
    Long,
    #[allow(dead_code)]
    LongLong,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FloatSize {
    Float,
    Double,
    #[allow(dead_code)]
    LongDouble,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct TypeQualifiers {
    pub is_const: bool,
    pub is_volatile: bool,
    pub is_restrict: bool,
}

impl TypeQualifiers {
    pub fn none() -> Self {
        Self::default()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum StorageClass {
    #[default]
    Auto,
    #[allow(dead_code)]
    Static,
    #[allow(dead_code)]
    Extern,
    #[allow(dead_code)]
    Register,
    #[allow(dead_code)]
    Typedef,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CType {
    Void,
    Int(IntSize, Signedness),
    Float(FloatSize),
    Pointer(Box<CType>, TypeQualifiers),
    Array(Box<CType>, Option<usize>),
    Function(Box<CType>, Vec<CType>, bool),
    Struct(String),
    Union(String),
    #[allow(dead_code)]
    Enum(String),
    #[allow(dead_code)]
    TypedefName(String),
    Bool,
    #[allow(dead_code)]
    Qualified(Box<CType>, TypeQualifiers),
}

impl CType {

    pub fn int() -> Self {
        CType::Int(IntSize::Int, Signedness::Signed)
    }

    pub fn uint() -> Self {
        CType::Int(IntSize::Int, Signedness::Unsigned)
    }

    pub fn long() -> Self {
        CType::Int(IntSize::Long, Signedness::Signed)
    }

    pub fn ulong() -> Self {
        CType::Int(IntSize::Long, Signedness::Unsigned)
    }

    pub fn char_signed() -> Self {
        CType::Int(IntSize::Char, Signedness::Signed)
    }

    pub fn char_unsigned() -> Self {
        CType::Int(IntSize::Char, Signedness::Unsigned)
    }

    pub fn float() -> Self {
        CType::Float(FloatSize::Float)
    }

    pub fn double() -> Self {
        CType::Float(FloatSize::Double)
    }

    pub fn ptr(inner: CType) -> Self {
        CType::Pointer(Box::new(inner), TypeQualifiers::none())
    }

    #[allow(dead_code)]
    pub fn array(inner: CType, size: usize) -> Self {
        CType::Array(Box::new(inner), Some(size))
    }

    pub fn is_pointer(&self) -> bool {
        matches!(self, CType::Pointer(_, _))
    }

    #[allow(dead_code)]
    pub fn is_integer(&self) -> bool {
        matches!(self, CType::Int(_, _) | CType::Bool)
    }

    #[allow(dead_code)]
    pub fn is_float(&self) -> bool {
        matches!(self, CType::Float(_))
    }

    pub fn is_generic_long_ptr(&self) -> bool {
        matches!(self, CType::Pointer(inner, _) if **inner == CType::Int(IntSize::Long, Signedness::Signed))
    }

    #[allow(dead_code)]
    pub fn pointee(&self) -> Option<&CType> {
        match self {
            CType::Pointer(inner, _) => Some(inner),
            _ => None,
        }
    }

}

impl Default for CType {
    fn default() -> Self {
        CType::Int(IntSize::Int, Signedness::Signed)
    }
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    Neg,
    Plus,
    Not,
    BitNot,
    Deref,
    AddrOf,
    #[allow(dead_code)]
    PreInc,
    #[allow(dead_code)]
    PreDec,
    #[allow(dead_code)]
    PostInc,
    #[allow(dead_code)]
    PostDec,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    #[allow(dead_code)]
    And,
    #[allow(dead_code)]
    Or,
    Comma,
}

impl BinaryOp {
    pub fn precedence(&self) -> u8 {
        match self {
            BinaryOp::Comma => 1,
            BinaryOp::Or => 3,
            BinaryOp::And => 4,
            BinaryOp::BitOr => 5,
            BinaryOp::BitXor => 6,
            BinaryOp::BitAnd => 7,
            BinaryOp::Eq | BinaryOp::Ne => 8,
            BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => 9,
            BinaryOp::Shl | BinaryOp::Shr => 10,
            BinaryOp::Add | BinaryOp::Sub => 11,
            BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => 12,
        }
    }

    pub fn is_left_assoc(&self) -> bool {
        true
    }

    pub fn symbol(&self) -> &'static str {
        match self {
            BinaryOp::Add => "+",
            BinaryOp::Sub => "-",
            BinaryOp::Mul => "*",
            BinaryOp::Div => "/",
            BinaryOp::Mod => "%",
            BinaryOp::BitAnd => "&",
            BinaryOp::BitOr => "|",
            BinaryOp::BitXor => "^",
            BinaryOp::Shl => "<<",
            BinaryOp::Shr => ">>",
            BinaryOp::Eq => "==",
            BinaryOp::Ne => "!=",
            BinaryOp::Lt => "<",
            BinaryOp::Le => "<=",
            BinaryOp::Gt => ">",
            BinaryOp::Ge => ">=",
            BinaryOp::And => "&&",
            BinaryOp::Or => "||",
            BinaryOp::Comma => ",",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AssignOp {
    Assign,
    #[allow(dead_code)]
    AddAssign,
    #[allow(dead_code)]
    SubAssign,
    #[allow(dead_code)]
    MulAssign,
    #[allow(dead_code)]
    DivAssign,
    #[allow(dead_code)]
    ModAssign,
    #[allow(dead_code)]
    AndAssign,
    #[allow(dead_code)]
    OrAssign,
    #[allow(dead_code)]
    XorAssign,
    #[allow(dead_code)]
    ShlAssign,
    #[allow(dead_code)]
    ShrAssign,
}

impl AssignOp {
    pub fn symbol(&self) -> &'static str {
        match self {
            AssignOp::Assign => "=",
            AssignOp::AddAssign => "+=",
            AssignOp::SubAssign => "-=",
            AssignOp::MulAssign => "*=",
            AssignOp::DivAssign => "/=",
            AssignOp::ModAssign => "%=",
            AssignOp::AndAssign => "&=",
            AssignOp::OrAssign => "|=",
            AssignOp::XorAssign => "^=",
            AssignOp::ShlAssign => "<<=",
            AssignOp::ShrAssign => ">>=",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IntLiteral {
    pub value: i128,
    pub suffix: IntLiteralSuffix,
    pub base: IntLiteralBase,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum IntLiteralSuffix {
    #[default]
    None,
    #[allow(dead_code)]
    U,
    L,
    #[allow(dead_code)]
    UL,
    #[allow(dead_code)]
    LL,
    #[allow(dead_code)]
    ULL,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum IntLiteralBase {
    #[default]
    Decimal,
    #[allow(dead_code)]
    Hex,
    #[allow(dead_code)]
    Octal,
    #[allow(dead_code)]
    Binary,
}

#[derive(Debug, Clone)]
pub struct FloatLiteral {
    pub value: f64,
    pub suffix: FloatLiteralSuffix,
}

impl PartialEq for FloatLiteral {
    fn eq(&self, other: &Self) -> bool {
        self.value.to_bits() == other.value.to_bits() && self.suffix == other.suffix
    }
}

impl Eq for FloatLiteral {}

impl std::hash::Hash for FloatLiteral {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.to_bits().hash(state);
        self.suffix.hash(state);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum FloatLiteralSuffix {
    #[default]
    None,
    F,
    #[allow(dead_code)]
    L,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StringLiteral {
    pub value: String,
    pub is_wide: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CExpr {
    IntLit(IntLiteral),
    FloatLit(FloatLiteral),
    StringLit(StringLiteral),
    #[allow(dead_code)]
    CharLit(char),

    Var(String),

    Unary(UnaryOp, Box<CExpr>),
    Binary(BinaryOp, Box<CExpr>, Box<CExpr>),

    Assign(AssignOp, Box<CExpr>, Box<CExpr>),

    Ternary(Box<CExpr>, Box<CExpr>, Box<CExpr>),

    Call(Box<CExpr>, Vec<CExpr>),

    Cast(CType, Box<CExpr>),

    Member(Box<CExpr>, String),
    MemberPtr(Box<CExpr>, String),

    #[allow(dead_code)]
    Index(Box<CExpr>, Box<CExpr>),

    SizeofType(CType),
    #[allow(dead_code)]
    SizeofExpr(Box<CExpr>),

    AlignofType(CType),

    #[allow(dead_code)]
    CompoundLit(CType, Vec<Initializer>),

    #[allow(dead_code)]
    Generic(Box<CExpr>, Vec<(Option<CType>, CExpr)>),

    #[allow(dead_code)]
    Paren(Box<CExpr>),

    #[allow(dead_code)]
    StmtExpr(Vec<CStmt>, Box<CExpr>),
}

#[allow(dead_code)]
impl CExpr {

    pub fn int(value: i64) -> Self {
        CExpr::IntLit(IntLiteral {
            value: value as i128,
            suffix: IntLiteralSuffix::None,
            base: IntLiteralBase::Decimal,
        })
    }

    pub fn var(name: impl Into<String>) -> Self {
        CExpr::Var(name.into())
    }

    pub fn call(func: CExpr, args: Vec<CExpr>) -> Self {
        CExpr::Call(Box::new(func), args)
    }

    pub fn deref(expr: CExpr) -> Self {
        CExpr::Unary(UnaryOp::Deref, Box::new(expr))
    }

    pub fn addr_of(expr: CExpr) -> Self {
        CExpr::Unary(UnaryOp::AddrOf, Box::new(expr))
    }

    pub fn cast(ty: CType, expr: CExpr) -> Self {
        CExpr::Cast(ty, Box::new(expr))
    }

    pub fn assign(lhs: CExpr, rhs: CExpr) -> Self {
        CExpr::Assign(AssignOp::Assign, Box::new(lhs), Box::new(rhs))
    }

    pub fn binary(op: BinaryOp, lhs: CExpr, rhs: CExpr) -> Self {
        CExpr::Binary(op, Box::new(lhs), Box::new(rhs))
    }

    pub fn index(arr: CExpr, idx: CExpr) -> Self {
        CExpr::Index(Box::new(arr), Box::new(idx))
    }

    pub fn member(expr: CExpr, field: impl Into<String>) -> Self {
        CExpr::Member(Box::new(expr), field.into())
    }

    pub fn member_ptr(expr: CExpr, field: impl Into<String>) -> Self {
        CExpr::MemberPtr(Box::new(expr), field.into())
    }

    pub fn has_side_effects(&self) -> bool {
        match self {
            CExpr::IntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::Var(_) => false,
            CExpr::Unary(op, inner) => matches!(
                op,
                UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec
            ) || inner.has_side_effects(),
            CExpr::Binary(_, l, r) => l.has_side_effects() || r.has_side_effects(),
            CExpr::Assign(_, _, _) => true,
            CExpr::Call(_, _) => true,
            CExpr::Ternary(c, t, e) => {
                c.has_side_effects() || t.has_side_effects() || e.has_side_effects()
            }
            CExpr::Cast(_, inner) => inner.has_side_effects(),
            CExpr::Member(inner, _) | CExpr::MemberPtr(inner, _) => inner.has_side_effects(),
            CExpr::Index(arr, idx) => arr.has_side_effects() || idx.has_side_effects(),
            CExpr::SizeofType(_) | CExpr::AlignofType(_) => false,
            CExpr::SizeofExpr(e) => e.has_side_effects(),
            CExpr::CompoundLit(_, _) => false,
            CExpr::Generic(e, _) => e.has_side_effects(),
            CExpr::Paren(inner) => inner.has_side_effects(),
            CExpr::StmtExpr(_, _) => true,
        }
    }

}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Initializer {
    #[allow(dead_code)]
    Expr(CExpr),
    #[allow(dead_code)]
    List(Vec<InitItem>),
    #[allow(dead_code)]
    String(StringLiteral),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InitItem {
    pub designator: Option<Designator>,
    pub init: Initializer,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Designator {
    #[allow(dead_code)]
    Field(String),
    #[allow(dead_code)]
    Index(CExpr),
    #[allow(dead_code)]
    Range(CExpr, CExpr),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Label {
    Named(String),
    Case(CExpr),
    Default,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CStmt {
    Empty,

    Expr(CExpr),

    Block(Vec<CBlockItem>),

    If(CExpr, Box<CStmt>, Option<Box<CStmt>>),
    Switch(CExpr, Box<CStmt>),
    While(CExpr, Box<CStmt>),
    DoWhile(Box<CStmt>, CExpr),
    For(Option<ForInit>, Option<CExpr>, Option<CExpr>, Box<CStmt>),

    Goto(String),
    Continue,
    Break,
    Return(Option<CExpr>),

    Labeled(Label, Box<CStmt>),

    #[allow(dead_code)]
    Decl(Vec<VarDecl>),

    Sequence(Vec<CStmt>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ForInit {
    #[allow(dead_code)]
    Expr(CExpr),
    #[allow(dead_code)]
    Decl(Vec<VarDecl>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CBlockItem {
    Stmt(CStmt),
    #[allow(dead_code)]
    Decl(Vec<VarDecl>),
}



#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarDecl {
    pub name: String,
    pub ty: CType,
    pub storage_class: StorageClass,
    pub qualifiers: TypeQualifiers,
    pub init: Option<Initializer>,
    pub loc: SourceLoc,
}

#[allow(dead_code)]
impl VarDecl {
    pub fn new(name: impl Into<String>, ty: CType) -> Self {
        Self {
            name: name.into(),
            ty,
            storage_class: StorageClass::Auto,
            qualifiers: TypeQualifiers::none(),
            init: None,
            loc: SourceLoc::unknown(),
        }
    }

    pub fn with_init(mut self, init: Initializer) -> Self {
        self.init = Some(init);
        self
    }

    pub fn with_storage(mut self, sc: StorageClass) -> Self {
        self.storage_class = sc;
        self
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FuncParam {
    pub name: Option<String>,
    pub ty: CType,
    pub loc: SourceLoc,
}

impl FuncParam {
    pub fn new(name: Option<String>, ty: CType) -> Self {
        Self {
            name,
            ty,
            loc: SourceLoc::unknown(),
        }
    }

    pub fn named(name: impl Into<String>, ty: CType) -> Self {
        Self::new(Some(name.into()), ty)
    }

}

#[derive(Debug, Clone, PartialEq)]
pub struct FuncDef {
    pub name: String,
    pub return_type: CType,
    pub params: Vec<FuncParam>,
    pub is_variadic: bool,
    pub storage_class: StorageClass,
    pub body: CStmt,
    pub local_vars: Vec<VarDecl>,
    pub loc: SourceLoc,
}


#[derive(Debug, Clone, PartialEq)]
pub struct FuncDecl {
    pub name: String,
    pub return_type: CType,
    pub params: Vec<FuncParam>,
    pub is_variadic: bool,
    pub loc: SourceLoc,
}

impl FuncDecl {
    pub fn new(name: impl Into<String>, return_type: CType, params: Vec<FuncParam>) -> Self {
        Self {
            name: name.into(),
            return_type,
            params,
            is_variadic: false,
            loc: SourceLoc::unknown(),
        }
    }
}


#[derive(Debug, Clone, PartialEq)]
pub struct StructField {
    pub name: Option<String>,
    pub ty: CType,
    pub bit_width: Option<u32>,
}

impl StructField {
    pub fn new(name: impl Into<String>, ty: CType) -> Self {
        Self {
            name: Some(name.into()),
            ty,
            bit_width: None,
        }
    }

}

#[derive(Debug, Clone, PartialEq)]
pub struct StructDef {
    pub name: Option<String>,
    pub is_union: bool,
    pub fields: Vec<StructField>,
    pub loc: SourceLoc,
}

impl StructDef {
    pub fn new_struct(name: impl Into<String>, fields: Vec<StructField>) -> Self {
        Self {
            name: Some(name.into()),
            is_union: false,
            fields,
            loc: SourceLoc::unknown(),
        }
    }

}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumConst {
    pub name: String,
    pub value: Option<CExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumDef {
    pub name: Option<String>,
    pub constants: Vec<EnumConst>,
    pub loc: SourceLoc,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedefDecl {
    pub name: String,
    pub ty: CType,
    pub loc: SourceLoc,
}


#[derive(Debug, Clone, PartialEq)]
pub enum TopLevelDecl {
    FuncDef(FuncDef),
    FuncDecl(FuncDecl),
    VarDecl(VarDecl),
    StructDef(StructDef),
    #[allow(dead_code)]
    EnumDef(EnumDef),
    #[allow(dead_code)]
    Typedef(TypedefDecl),
}


#[derive(Debug, Clone, PartialEq, Default)]
pub struct TranslationUnit {
    pub decls: Vec<TopLevelDecl>,
    pub symbols: HashMap<String, usize>,
    pub type_defs: HashMap<String, CType>,
}

impl TranslationUnit {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_function(&mut self, func: FuncDef) {
        let name = func.name.clone();
        let idx = self.decls.len();
        self.decls.push(TopLevelDecl::FuncDef(func));
        self.symbols.insert(name, idx);
    }

    pub fn add_func_decl(&mut self, decl: FuncDecl) {
        let name = decl.name.clone();
        let idx = self.decls.len();
        self.decls.push(TopLevelDecl::FuncDecl(decl));
        self.symbols.insert(name, idx);
    }

    pub fn add_global_var(&mut self, var: VarDecl) {
        let name = var.name.clone();
        if self.symbols.contains_key(&name) {
            return;
        }
        let idx = self.decls.len();
        self.decls.push(TopLevelDecl::VarDecl(var));
        self.symbols.insert(name, idx);
    }

    /// Rebuild `symbols` from actual `decls` positions.
    /// Must be called after any operation that reorders or prepends to `decls`.
    pub fn rebuild_symbols(&mut self) {
        self.symbols.clear();
        for (i, decl) in self.decls.iter().enumerate() {
            let name = match decl {
                TopLevelDecl::FuncDef(f) => Some(f.name.clone()),
                TopLevelDecl::FuncDecl(f) => Some(f.name.clone()),
                TopLevelDecl::VarDecl(v) => Some(v.name.clone()),
                _ => None,
            };
            if let Some(name) = name {
                self.symbols.entry(name).or_insert(i);
            }
        }
    }

}


pub trait ExprTransform {
    fn transform_expr(&mut self, expr: CExpr) -> CExpr {
        self.walk_expr(expr)
    }

    fn walk_expr(&mut self, expr: CExpr) -> CExpr {
        match expr {
            CExpr::IntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::Var(_) => expr,
            CExpr::Unary(op, inner) => CExpr::Unary(op, Box::new(self.transform_expr(*inner))),
            CExpr::Binary(op, l, r) => CExpr::Binary(
                op,
                Box::new(self.transform_expr(*l)),
                Box::new(self.transform_expr(*r)),
            ),
            CExpr::Assign(op, l, r) => CExpr::Assign(
                op,
                Box::new(self.transform_expr(*l)),
                Box::new(self.transform_expr(*r)),
            ),
            CExpr::Ternary(c, t, e) => CExpr::Ternary(
                Box::new(self.transform_expr(*c)),
                Box::new(self.transform_expr(*t)),
                Box::new(self.transform_expr(*e)),
            ),
            CExpr::Call(f, args) => CExpr::Call(
                Box::new(self.transform_expr(*f)),
                args.into_iter().map(|a| self.transform_expr(a)).collect(),
            ),
            CExpr::Cast(ty, inner) => CExpr::Cast(ty, Box::new(self.transform_expr(*inner))),
            CExpr::Member(inner, field) => {
                CExpr::Member(Box::new(self.transform_expr(*inner)), field)
            }
            CExpr::MemberPtr(inner, field) => {
                CExpr::MemberPtr(Box::new(self.transform_expr(*inner)), field)
            }
            CExpr::Index(arr, idx) => CExpr::Index(
                Box::new(self.transform_expr(*arr)),
                Box::new(self.transform_expr(*idx)),
            ),
            CExpr::SizeofExpr(inner) => CExpr::SizeofExpr(Box::new(self.transform_expr(*inner))),
            CExpr::SizeofType(ty) => CExpr::SizeofType(ty),
            CExpr::AlignofType(ty) => CExpr::AlignofType(ty),
            CExpr::CompoundLit(ty, inits) => CExpr::CompoundLit(
                ty,
                inits
                    .into_iter()
                    .map(|i| self.transform_initializer(i))
                    .collect(),
            ),
            CExpr::Generic(ctrl, assocs) => CExpr::Generic(
                Box::new(self.transform_expr(*ctrl)),
                assocs
                    .into_iter()
                    .map(|(ty, e)| (ty, self.transform_expr(e)))
                    .collect(),
            ),
            CExpr::Paren(inner) => CExpr::Paren(Box::new(self.transform_expr(*inner))),
            CExpr::StmtExpr(stmts, expr) => CExpr::StmtExpr(
                stmts
                    .into_iter()
                    .map(|s| self.transform_stmt_in_expr(s))
                    .collect(),
                Box::new(self.transform_expr(*expr)),
            ),
        }
    }

    fn transform_initializer(&mut self, init: Initializer) -> Initializer {
        match init {
            Initializer::Expr(e) => Initializer::Expr(self.transform_expr(e)),
            Initializer::List(items) => Initializer::List(
                items
                    .into_iter()
                    .map(|item| InitItem {
                        designator: item.designator,
                        init: self.transform_initializer(item.init),
                    })
                    .collect(),
            ),
            Initializer::String(lit) => Initializer::String(lit),
        }
    }

    fn transform_stmt_in_expr(&mut self, stmt: CStmt) -> CStmt {
        stmt
    }
}

pub trait StmtTransform: ExprTransform {
    fn transform_stmt(&mut self, stmt: CStmt) -> CStmt {
        self.walk_stmt(stmt)
    }

    fn walk_stmt(&mut self, stmt: CStmt) -> CStmt {
        match stmt {
            CStmt::Empty => CStmt::Empty,
            CStmt::Expr(e) => CStmt::Expr(self.transform_expr(e)),
            CStmt::Block(items) => CStmt::Block(
                items
                    .into_iter()
                    .map(|item| match item {
                        CBlockItem::Stmt(s) => {
                            CBlockItem::Stmt(StmtTransform::transform_stmt(self, s))
                        }
                        CBlockItem::Decl(decls) => CBlockItem::Decl(
                            decls
                                .into_iter()
                                .map(|mut d| {
                                    d.init = d.init.map(|i| self.transform_initializer(i));
                                    d
                                })
                                .collect(),
                        ),
                    })
                    .collect(),
            ),
            CStmt::If(cond, then_s, else_s) => CStmt::If(
                self.transform_expr(cond),
                Box::new(StmtTransform::transform_stmt(self, *then_s)),
                else_s.map(|e| Box::new(StmtTransform::transform_stmt(self, *e))),
            ),
            CStmt::Switch(expr, body) => CStmt::Switch(
                self.transform_expr(expr),
                Box::new(StmtTransform::transform_stmt(self, *body)),
            ),
            CStmt::While(cond, body) => CStmt::While(
                self.transform_expr(cond),
                Box::new(StmtTransform::transform_stmt(self, *body)),
            ),
            CStmt::DoWhile(body, cond) => CStmt::DoWhile(
                Box::new(StmtTransform::transform_stmt(self, *body)),
                self.transform_expr(cond),
            ),
            CStmt::For(init, cond, update, body) => CStmt::For(
                init.map(|i| match i {
                    ForInit::Expr(e) => ForInit::Expr(self.transform_expr(e)),
                    ForInit::Decl(decls) => ForInit::Decl(
                        decls
                            .into_iter()
                            .map(|mut d| {
                                d.init = d.init.map(|i| self.transform_initializer(i));
                                d
                            })
                            .collect(),
                    ),
                }),
                cond.map(|c| self.transform_expr(c)),
                update.map(|u| self.transform_expr(u)),
                Box::new(StmtTransform::transform_stmt(self, *body)),
            ),
            CStmt::Return(e) => CStmt::Return(e.map(|e| self.transform_expr(e))),
            CStmt::Goto(l) => CStmt::Goto(l),
            CStmt::Continue => CStmt::Continue,
            CStmt::Break => CStmt::Break,
            CStmt::Labeled(label, body) => {
                let label = match label {
                    Label::Case(e) => Label::Case(self.transform_expr(e)),
                    l => l,
                };
                CStmt::Labeled(label, Box::new(StmtTransform::transform_stmt(self, *body)))
            }
            CStmt::Decl(decls) => CStmt::Decl(
                decls
                    .into_iter()
                    .map(|mut d| {
                        d.init = d.init.map(|i| self.transform_initializer(i));
                        d
                    })
                    .collect(),
            ),
            CStmt::Sequence(stmts) => CStmt::Sequence(
                stmts
                    .into_iter()
                    .map(|s| StmtTransform::transform_stmt(self, s))
                    .collect(),
            ),
        }
    }
}
