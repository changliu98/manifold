

use crate::decompile::passes::c_pass::types::*;
use std::fmt::Write;

#[derive(Debug, Clone)]
pub struct PrintConfig {
    pub indent_size: usize,
    #[allow(dead_code)]
    pub max_line_width: usize,
    #[allow(dead_code)]
    pub emit_comments: bool,
    #[allow(dead_code)]
    pub compact: bool,
}

impl Default for PrintConfig {
    fn default() -> Self {
        Self {
            indent_size: 4,
            max_line_width: 100,
            emit_comments: true,
            compact: false,
        }
    }
}

pub struct Printer {
    config: PrintConfig,
    output: String,
    indent_level: usize,
    at_line_start: bool,
}

impl Printer {
    pub fn new(config: PrintConfig) -> Self {
        Self {
            config,
            output: String::new(),
            indent_level: 0,
            at_line_start: true,
        }
    }

    pub fn with_default_config() -> Self {
        Self::new(PrintConfig::default())
    }

    pub fn into_string(self) -> String {
        self.output
    }

    fn write_indent(&mut self) {
        if self.at_line_start {
            for _ in 0..(self.indent_level * self.config.indent_size) {
                self.output.push(' ');
            }
            self.at_line_start = false;
        }
    }

    fn write(&mut self, s: &str) {
        self.write_indent();
        self.output.push_str(s);
    }

    fn writeln(&mut self, s: &str) {
        self.write_indent();
        self.output.push_str(s);
        self.newline();
    }

    fn newline(&mut self) {
        self.output.push('\n');
        self.at_line_start = true;
    }

    fn indent<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        self.indent_level += 1;
        let result = f(self);
        self.indent_level -= 1;
        result
    }


    pub fn print_type(&mut self, ty: &CType) {
        self.write(&type_to_string(ty));
    }

    pub fn print_type_with_name(&mut self, ty: &CType, name: &str) {
        self.write(&type_to_named_decl(ty, name));
    }


    pub fn print_expr(&mut self, expr: &CExpr) {
        self.print_expr_prec(expr, 0);
    }

    fn print_expr_prec(&mut self, expr: &CExpr, parent_prec: u8) {
        let prec = expr_precedence(expr);
        let needs_parens = prec < parent_prec;

        if needs_parens {
            self.write("(");
        }

        match expr {
            CExpr::IntLit(lit) => self.print_int_literal(lit),
            CExpr::FloatLit(lit) => self.print_float_literal(lit),
            CExpr::StringLit(lit) => self.print_string_literal(lit),
            CExpr::CharLit(c) => self.print_char_literal(*c),
            CExpr::Var(name) => self.write(name),

            CExpr::Unary(op, inner) => match op {
                UnaryOp::PostInc | UnaryOp::PostDec => {
                    self.print_expr_prec(inner, prec);
                    self.write(unary_op_str(op));
                }
                _ => {
                    self.write(unary_op_str(op));
                    self.print_expr_prec(inner, prec);
                }
            },

            CExpr::Binary(op, lhs, rhs) => {
                let (l_prec, r_prec) = if op.is_left_assoc() {
                    (prec, prec + 1)
                } else {
                    (prec + 1, prec)
                };
                self.print_expr_prec(lhs, l_prec);
                self.write(" ");
                self.write(op.symbol());
                self.write(" ");
                self.print_expr_prec(rhs, r_prec);
            }

            CExpr::Assign(op, lhs, rhs) => {
                self.print_expr_prec(lhs, 3);
                self.write(" ");
                self.write(op.symbol());
                self.write(" ");
                self.print_expr_prec(rhs, 2);
            }

            CExpr::Ternary(cond, then_e, else_e) => {
                self.print_expr_prec(cond, 4);
                self.write(" ? ");
                self.print_expr_prec(then_e, 2);
                self.write(" : ");
                self.print_expr_prec(else_e, 2);
            }

            CExpr::Call(func, args) => {
                // Strip redundant function pointer casts for named functions, but keep casts for register variables (var_*) whose declared type may not be a function pointer.
                let callee = match func.as_ref() {
                    CExpr::Cast(CType::Pointer(inner, _), expr)
                        if matches!(inner.as_ref(), CType::Function(..)) =>
                    {
                        let is_register_var = matches!(expr.as_ref(), CExpr::Var(name) if name.starts_with("var_"));
                        if is_register_var { func.as_ref() } else { expr.as_ref() }
                    }
                    _ => func.as_ref(),
                };
                self.print_expr_prec(callee, 15);
                self.write("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_expr_prec(arg, 2);
                }
                self.write(")");
            }

            CExpr::Cast(ty, inner) => {
                self.write("(");
                self.print_type(ty);
                self.write(")");
                self.print_expr_prec(inner, 14);
            }

            CExpr::Member(inner, field) => {
                self.print_expr_prec(inner, 15);
                self.write(".");
                self.write(field);
            }

            CExpr::MemberPtr(inner, field) => {
                self.print_expr_prec(inner, 15);
                self.write("->");
                self.write(field);
            }

            CExpr::Index(arr, idx) => {
                self.print_expr_prec(arr, 15);
                self.write("[");
                self.print_expr(idx);
                self.write("]");
            }

            CExpr::SizeofType(ty) => {
                self.write("sizeof(");
                self.print_type(ty);
                self.write(")");
            }

            CExpr::SizeofExpr(inner) => {
                self.write("sizeof(");
                self.print_expr(inner);
                self.write(")");
            }

            CExpr::AlignofType(ty) => {
                self.write("_Alignof(");
                self.print_type(ty);
                self.write(")");
            }

            CExpr::CompoundLit(ty, inits) => {
                self.write("(");
                self.print_type(ty);
                self.write("){");
                self.print_initializer_list(inits);
                self.write("}");
            }

            CExpr::Generic(ctrl, assocs) => {
                self.write("_Generic(");
                self.print_expr(ctrl);
                for (ty_opt, expr) in assocs {
                    self.write(", ");
                    if let Some(ty) = ty_opt {
                        self.print_type(ty);
                    } else {
                        self.write("default");
                    }
                    self.write(": ");
                    self.print_expr(expr);
                }
                self.write(")");
            }

            CExpr::Paren(inner) => {
                self.write("(");
                self.print_expr(inner);
                self.write(")");
            }

            CExpr::StmtExpr(stmts, expr) => {
                self.write("({");
                self.newline();
                self.indent(|p| {
                    for stmt in stmts {
                        p.print_stmt(stmt);
                    }
                    p.print_expr(expr);
                    p.write(";");
                    p.newline();
                });
                self.write("})");
            }
        }

        if needs_parens {
            self.write(")");
        }
    }

    fn print_int_literal(&mut self, lit: &IntLiteral) {
        match lit.base {
            IntLiteralBase::Hex => write!(self.output, "0x{:x}", lit.value).unwrap(),
            IntLiteralBase::Octal if lit.value != 0 => {
                write!(self.output, "0{:o}", lit.value).unwrap()
            }
            IntLiteralBase::Binary => write!(self.output, "0b{:b}", lit.value).unwrap(),
            _ => write!(self.output, "{}", lit.value).unwrap(),
        }
        self.at_line_start = false;

        match lit.suffix {
            IntLiteralSuffix::None => {}
            IntLiteralSuffix::U => self.output.push('U'),
            IntLiteralSuffix::L => {
                if lit.value > i32::MAX as i128 || lit.value < i32::MIN as i128 {
                    self.output.push('L');
                }
            }
            IntLiteralSuffix::UL => self.output.push_str("UL"),
            IntLiteralSuffix::LL => self.output.push_str("LL"),
            IntLiteralSuffix::ULL => self.output.push_str("ULL"),
        }
    }

    fn print_float_literal(&mut self, lit: &FloatLiteral) {
        if lit.value.fract() == 0.0 {
            write!(self.output, "{:.1}", lit.value).unwrap();
        } else {
            write!(self.output, "{}", lit.value).unwrap();
        }
        self.at_line_start = false;

        match lit.suffix {
            FloatLiteralSuffix::None => {}
            FloatLiteralSuffix::F => self.output.push('f'),
            FloatLiteralSuffix::L => self.output.push('L'),
        }
    }

    fn print_string_literal(&mut self, lit: &StringLiteral) {
        if lit.is_wide {
            self.write("L");
        }
        self.write("\"");
        for c in lit.value.chars() {
            self.write(&escape_char(c));
        }
        self.write("\"");
    }

    fn print_char_literal(&mut self, c: char) {
        self.write("'");
        self.write(&escape_char(c));
        self.write("'");
    }

    fn print_initializer_list(&mut self, inits: &[Initializer]) {
        for (i, init) in inits.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.print_initializer(init);
        }
    }

    fn print_initializer(&mut self, init: &Initializer) {
        match init {
            Initializer::Expr(e) => self.print_expr(e),
            Initializer::List(items) => {
                self.write("{");
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    if let Some(ref des) = item.designator {
                        self.print_designator(des);
                        self.write(" = ");
                    }
                    self.print_initializer(&item.init);
                }
                self.write("}");
            }
            Initializer::String(lit) => self.print_string_literal(lit),
        }
    }

    fn print_designator(&mut self, des: &Designator) {
        match des {
            Designator::Field(name) => {
                self.write(".");
                self.write(name);
            }
            Designator::Index(idx) => {
                self.write("[");
                self.print_expr(idx);
                self.write("]");
            }
            Designator::Range(start, end) => {
                self.write("[");
                self.print_expr(start);
                self.write(" ... ");
                self.print_expr(end);
                self.write("]");
            }
        }
    }


    pub fn print_stmt(&mut self, stmt: &CStmt) {
        match stmt {
            CStmt::Empty => {}
            CStmt::Expr(e) => {
                self.write_indent();
                self.print_expr(e);
                self.writeln(";");
            }

            CStmt::Block(items) => {
                self.writeln("{");
                self.indent(|p| {
                    for item in items {
                        p.print_block_item(item);
                    }
                });
                self.writeln("}");
            }

            CStmt::If(cond, then_s, else_s) => {
                self.write_indent();
                self.write("if (");
                self.print_expr(cond);
                self.write(") ");
                self.print_stmt_body(then_s);

                if let Some(else_stmt) = else_s {
                    if matches!(**else_stmt, CStmt::If(_, _, _)) {
                        self.write_indent();
                        self.write("else ");
                        self.print_stmt(else_stmt);
                    } else {
                        self.write_indent();
                        self.write("else ");
                        self.print_stmt_body(else_stmt);
                    }
                }
            }

            CStmt::Switch(expr, body) => {
                self.write_indent();
                self.write("switch (");
                self.print_expr(expr);
                self.write(") ");
                self.print_stmt_body(body);
            }

            CStmt::While(cond, body) => {
                self.write_indent();
                self.write("while (");
                self.print_expr(cond);
                self.write(") ");
                self.print_stmt_body(body);
            }

            CStmt::DoWhile(body, cond) => {
                self.write_indent();
                self.write("do ");
                self.print_stmt_body(body);
                self.write_indent();
                self.write("while (");
                self.print_expr(cond);
                self.writeln(");");
            }

            CStmt::For(init, cond, update, body) => {
                self.write_indent();
                self.write("for (");

                if let Some(init) = init {
                    match init {
                        ForInit::Expr(e) => self.print_expr(e),
                        ForInit::Decl(decls) => {
                            for (i, decl) in decls.iter().enumerate() {
                                if i > 0 {
                                    self.write(", ");
                                }
                                if i == 0 {
                                    self.print_type_with_name(&decl.ty, &decl.name);
                                } else {
                                    self.write(&decl.name);
                                }
                                if let Some(ref init) = decl.init {
                                    self.write(" = ");
                                    self.print_initializer(init);
                                }
                            }
                        }
                    }
                }
                self.write("; ");

                if let Some(cond) = cond {
                    self.print_expr(cond);
                }
                self.write("; ");

                if let Some(update) = update {
                    self.print_expr(update);
                }
                self.write(") ");
                self.print_stmt_body(body);
            }

            CStmt::Goto(label) => {
                self.write_indent();
                self.write("goto ");
                self.write(label);
                self.writeln(";");
            }

            CStmt::Continue => self.writeln("continue;"),
            CStmt::Break => self.writeln("break;"),

            CStmt::Return(None) => self.writeln("return;"),
            CStmt::Return(Some(e)) => {
                self.write_indent();
                self.write("return ");
                self.print_expr(e);
                self.writeln(";");
            }

            CStmt::Labeled(label, body) => {
                let saved_indent = self.indent_level;
                self.indent_level = 0;

                match label {
                    Label::Named(name) => {
                        self.write(name);
                        self.writeln(":");
                    }
                    Label::Case(expr) => {
                        self.write("case ");
                        self.print_expr(expr);
                        self.writeln(":");
                    }
                    Label::Default => {
                        self.writeln("default:");
                    }
                }

                self.indent_level = saved_indent;
                self.print_stmt(body);
            }

            CStmt::Decl(decls) => {
                for decl in decls {
                    self.print_var_decl(decl);
                }
            }

            CStmt::Sequence(stmts) => {
                for stmt in stmts {
                    self.print_stmt(stmt);
                }
            }
        }
    }

    fn print_stmt_body(&mut self, stmt: &CStmt) {
        match stmt {
            CStmt::Block(_) => {
                self.print_stmt(stmt);
            }
            _ => {
                self.writeln("{");
                self.indent(|p| p.print_stmt(stmt));
                self.writeln("}");
            }
        }
    }

    fn print_block_item(&mut self, item: &CBlockItem) {
        match item {
            CBlockItem::Stmt(s) => self.print_stmt(s),
            CBlockItem::Decl(decls) => {
                for decl in decls {
                    self.print_var_decl(decl);
                }
            }
        }
    }


    pub fn print_var_decl(&mut self, decl: &VarDecl) {
        self.write_indent();

        match decl.storage_class {
            StorageClass::Static => self.write("static "),
            StorageClass::Extern => self.write("extern "),
            StorageClass::Register => self.write("register "),
            _ => {}
        }

        if decl.qualifiers.is_const {
            self.write("const ");
        }
        if decl.qualifiers.is_volatile {
            self.write("volatile ");
        }

        self.print_type_with_name(&decl.ty, &decl.name);

        if let Some(ref init) = decl.init {
            self.write(" = ");
            self.print_initializer(init);
        }

        self.writeln(";");
    }

    pub fn print_func_decl(&mut self, decl: &FuncDecl) {
        self.write_indent();
        self.print_type(&decl.return_type);
        self.write(" ");
        self.write(&decl.name);
        self.print_params(&decl.params, decl.is_variadic);
        self.writeln(";");
    }

    pub fn print_func_def(&mut self, func: &FuncDef) {
        match func.storage_class {
            StorageClass::Static => self.write("static "),
            StorageClass::Extern => self.write("extern "),
            _ => {}
        }

        self.print_type(&func.return_type);
        self.write(" ");
        self.write(&func.name);
        self.print_params(&func.params, func.is_variadic);
        self.newline();

        let body = if func.return_type == CType::Void {
            match &func.body {
                CStmt::Block(items) => {
                    let mut items = items.clone();
                    if let Some(last) = items.last() {
                        let should_strip = match last {
                            CBlockItem::Stmt(CStmt::Return(None)) => true,
                            CBlockItem::Stmt(CStmt::Labeled(_, inner)) => {
                                matches!(**inner, CStmt::Return(None))
                            }
                            _ => false,
                        };
                        if should_strip {
                            items.pop();
                        }
                    }
                    CStmt::Block(items)
                }
                CStmt::Sequence(stmts) => {
                    let mut stmts = stmts.clone();
                    if let Some(last) = stmts.last() {
                        if matches!(last, CStmt::Return(None)) {
                            stmts.pop();
                        }
                    }
                    CStmt::Sequence(stmts)
                }
                CStmt::Return(None) => CStmt::Empty,
                other => other.clone(),
            }
        } else {
            func.body.clone()
        };

        self.writeln("{");
        self.indent(|p| {
            for var in &func.local_vars {
                p.print_var_decl(var);
            }
            if !func.local_vars.is_empty() {
                p.newline();
            }

            match &body {
                CStmt::Block(items) => {
                    for item in items {
                        p.print_block_item(item);
                    }
                }
                other => p.print_stmt(other),
            }
        });
        self.writeln("}");
    }

    fn print_params(&mut self, params: &[FuncParam], is_variadic: bool) {
        self.write("(");
        if params.is_empty() && !is_variadic {
            self.write("void");
        } else {
            for (i, param) in params.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                if let Some(ref name) = param.name {
                    self.print_type_with_name(&param.ty, name);
                } else {
                    self.print_type(&param.ty);
                }
            }
            if is_variadic {
                if !params.is_empty() {
                    self.write(", ");
                }
                self.write("...");
            }
        }
        self.write(")");
    }

    pub fn print_struct_def(&mut self, def: &StructDef) {
        if def.is_union {
            self.write("union ");
        } else {
            self.write("struct ");
        }

        if let Some(ref name) = def.name {
            self.write(name);
            self.write(" ");
        }

        self.writeln("{");
        self.indent(|p| {
            for field in &def.fields {
                p.write_indent();
                if let Some(ref name) = field.name {
                    p.print_type_with_name(&field.ty, name);
                } else {
                    p.print_type(&field.ty);
                }
                if let Some(width) = field.bit_width {
                    write!(p.output, " : {}", width).unwrap();
                }
                p.writeln(";");
            }
        });
        self.writeln("};");
    }

    pub fn print_enum_def(&mut self, def: &EnumDef) {
        self.write("enum ");
        if let Some(ref name) = def.name {
            self.write(name);
            self.write(" ");
        }
        self.writeln("{");
        self.indent(|p| {
            for (i, constant) in def.constants.iter().enumerate() {
                p.write_indent();
                p.write(&constant.name);
                if let Some(ref val) = constant.value {
                    p.write(" = ");
                    p.print_expr(val);
                }
                if i < def.constants.len() - 1 {
                    p.write(",");
                }
                p.newline();
            }
        });
        self.writeln("};");
    }

    pub fn print_typedef(&mut self, typedef: &TypedefDecl) {
        self.write("typedef ");
        self.print_type_with_name(&typedef.ty, &typedef.name);
        self.writeln(";");
    }


    pub fn print_top_level(&mut self, decl: &TopLevelDecl) {
        match decl {
            TopLevelDecl::FuncDef(f) => self.print_func_def(f),
            TopLevelDecl::FuncDecl(d) => self.print_func_decl(d),
            TopLevelDecl::VarDecl(v) => self.print_var_decl(v),
            TopLevelDecl::StructDef(s) => self.print_struct_def(s),
            TopLevelDecl::EnumDef(e) => self.print_enum_def(e),
            TopLevelDecl::Typedef(t) => self.print_typedef(t),
        }
    }

    pub fn print_translation_unit(&mut self, tu: &TranslationUnit) {
        let includes = collect_needed_includes(tu);
        for inc in &includes {
            self.writeln(&format!("#include {}", inc));
        }
        if !includes.is_empty() {
            self.newline();
        }

        // Print in C declaration order: types, globals, forward decls, definitions.
        // This avoids sorting tu.decls (which would invalidate tu.symbols indices).
        let order = |d: &TopLevelDecl| -> u8 {
            match d {
                TopLevelDecl::StructDef(_) | TopLevelDecl::EnumDef(_) | TopLevelDecl::Typedef(_) => 0,
                TopLevelDecl::VarDecl(_) => 1,
                TopLevelDecl::FuncDecl(_) => 2,
                TopLevelDecl::FuncDef(_) => 3,
            }
        };
        let mut indices: Vec<usize> = (0..tu.decls.len()).collect();
        indices.sort_by_key(|&i| order(&tu.decls[i]));

        fn is_effectively_empty_body(stmt: &CStmt) -> bool {
            match stmt {
                CStmt::Empty => true,
                CStmt::Expr(e) => !e.has_side_effects(),
                CStmt::Block(items) => items.iter().all(|item| match item {
                    CBlockItem::Stmt(s) => is_effectively_empty_body(s),
                    CBlockItem::Decl(decls) => decls.is_empty(),
                }),
                CStmt::Sequence(stmts) => stmts.iter().all(is_effectively_empty_body),
                _ => false,
            }
        }

        let mut first = true;
        for i in indices {
            let decl = &tu.decls[i];
            if let TopLevelDecl::FuncDef(f) = decl {
                if is_effectively_empty_body(&f.body) && f.local_vars.is_empty() {
                    continue;
                }
            }
            if !first {
                self.newline();
            }
            first = false;
            self.print_top_level(decl);
        }
    }
}


fn type_to_string(ty: &CType) -> String {
    match ty {
        CType::Void => "void".to_string(),
        CType::Bool => "int".to_string(),
        CType::Int(size, sign) => {
            let sign_str = match sign {
                Signedness::Signed => "",
                Signedness::Unsigned => "unsigned ",
            };
            let size_str = match size {
                IntSize::Char => "char",
                IntSize::Short => "short",
                IntSize::Int => "int",
                IntSize::Long => "long",
                IntSize::LongLong => "long long",
            };
            format!("{}{}", sign_str, size_str)
        }
        CType::Float(size) => match size {
            FloatSize::Float => "float".to_string(),
            FloatSize::Double => "double".to_string(),
            FloatSize::LongDouble => "long double".to_string(),
        },
        CType::Pointer(inner, quals) => {
            let quals_str = qualifiers_to_string(quals);
            if matches!(inner.as_ref(), CType::Function(..)) {
                let (prefix, suffix) = type_to_decl_parts(inner);
                return format!("{} (*{}){}", prefix, quals_str.trim(), suffix);
            }
            format!("{} *{}", type_to_string(inner), quals_str)
        }
        CType::Array(inner, size) => {
            let size_str = size.map(|s| s.to_string()).unwrap_or_default();
            format!("{}[{}]", type_to_string(inner), size_str)
        }
        CType::Function(ret, params, variadic) => {
            let params_str = if params.is_empty() {
                "void".to_string()
            } else {
                let mut s: String = params
                    .iter()
                    .map(type_to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                if *variadic {
                    s.push_str(", ...");
                }
                s
            };
            format!("{} (*)({})", type_to_string(ret), params_str)
        }
        CType::Struct(name) => format!("struct {}", name),
        CType::Union(name) => format!("union {}", name),
        CType::Enum(name) => format!("enum {}", name),
        CType::TypedefName(name) => name.clone(),
        CType::Qualified(inner, quals) => {
            let quals_str = qualifiers_to_string(quals);
            format!("{}{}", quals_str, type_to_string(inner))
        }
    }
}

fn type_to_decl_parts(ty: &CType) -> (String, String) {
    match ty {
        CType::Array(inner, size) => {
            let (prefix, suffix) = type_to_decl_parts(inner);
            let size_str = size.map(|s| s.to_string()).unwrap_or_default();
            (prefix, format!("[{}]{}", size_str, suffix))
        }
        CType::Function(ret, params, variadic) => {
            let params_str = if params.is_empty() && !variadic {
                "void".to_string()
            } else {
                let mut s: String = params
                    .iter()
                    .map(type_to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                if *variadic {
                    if !params.is_empty() {
                        s.push_str(", ");
                    }
                    s.push_str("...");
                }
                s
            };
            (type_to_string(ret), format!("({})", params_str))
        }
        CType::Pointer(inner, quals) => {
            let (prefix, suffix) = type_to_decl_parts(inner);
            let quals_str = qualifiers_to_string(quals);
            if suffix.is_empty() {
                (format!("{} *{}", prefix, quals_str), String::new())
            } else {
                (format!("{} (*{})", prefix, quals_str), suffix)
            }
        }
        _ => (type_to_string(ty), String::new()),
    }
}

fn type_to_named_decl(ty: &CType, name: &str) -> String {
    match ty {
        CType::Pointer(inner, quals) => {
            let quals_str = qualifiers_to_string(quals);
            let declarator = if matches!(inner.as_ref(), CType::Array(..) | CType::Function(..)) {
                format!("(*{}{})", quals_str, name)
            } else {
                format!("*{}{}", quals_str, name)
            };
            type_to_named_decl(inner, &declarator)
        }
        CType::Array(inner, size) => {
            let size_str = size.map(|s| s.to_string()).unwrap_or_default();
            type_to_named_decl(inner, &format!("{}[{}]", name, size_str))
        }
        CType::Function(ret, params, variadic) => {
            let mut params_str = if params.is_empty() && !variadic {
                "void".to_string()
            } else {
                params
                    .iter()
                    .map(type_to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            if *variadic {
                if !params.is_empty() {
                    params_str.push_str(", ");
                }
                params_str.push_str("...");
            }
            type_to_named_decl(ret, &format!("{}({})", name, params_str))
        }
        CType::Qualified(inner, quals) => {
            let inner_decl = type_to_named_decl(inner, name);
            let quals_str = qualifiers_to_string(quals);
            if quals_str.is_empty() {
                inner_decl
            } else {
                format!("{}{}", quals_str, inner_decl)
            }
        }
        _ => {
            let base = type_to_string(ty);
            if name.is_empty() {
                base
            } else {
                format!("{} {}", base, name)
            }
        }
    }
}

fn qualifiers_to_string(quals: &TypeQualifiers) -> String {
    let mut parts = Vec::new();
    if quals.is_const {
        parts.push("const");
    }
    if quals.is_volatile {
        parts.push("volatile");
    }
    if quals.is_restrict {
        parts.push("restrict");
    }
    if parts.is_empty() {
        String::new()
    } else {
        parts.join(" ") + " "
    }
}

fn expr_precedence(expr: &CExpr) -> u8 {
    match expr {
        CExpr::IntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::Var(_) => 16,
        CExpr::Call(_, _) | CExpr::Member(_, _) | CExpr::MemberPtr(_, _) | CExpr::Index(_, _) => 15,
        CExpr::Unary(op, _) => match op {
            UnaryOp::PostInc | UnaryOp::PostDec => 15,
            _ => 14,
        },
        CExpr::Cast(_, _) => 14,
        CExpr::Binary(op, _, _) => op.precedence(),
        CExpr::Ternary(_, _, _) => 3,
        CExpr::Assign(_, _, _) => 2,
        CExpr::SizeofType(_) | CExpr::SizeofExpr(_) | CExpr::AlignofType(_) => 14,
        CExpr::CompoundLit(_, _) => 16,
        CExpr::Generic(_, _) => 16,
        CExpr::Paren(_) => 16,
        CExpr::StmtExpr(_, _) => 16,
    }
}

fn unary_op_str(op: &UnaryOp) -> &'static str {
    match op {
        UnaryOp::Neg => "-",
        UnaryOp::Plus => "+",
        UnaryOp::Not => "!",
        UnaryOp::BitNot => "~",
        UnaryOp::Deref => "*",
        UnaryOp::AddrOf => "&",
        UnaryOp::PreInc => "++",
        UnaryOp::PreDec => "--",
        UnaryOp::PostInc => "++",
        UnaryOp::PostDec => "--",
    }
}

fn escape_char(c: char) -> String {
    match c {
        '\n' => "\\n".to_string(),
        '\r' => "\\r".to_string(),
        '\t' => "\\t".to_string(),
        '\\' => "\\\\".to_string(),
        '"' => "\\\"".to_string(),
        '\'' => "\\'".to_string(),
        '\0' => "\\0".to_string(),
        c if c.is_ascii_graphic() || c == ' ' => c.to_string(),
        c => format!("\\x{:02x}", c as u32),
    }
}


pub fn print_translation_unit(tu: &TranslationUnit) -> String {
    let mut printer = Printer::with_default_config();
    printer.print_translation_unit(tu);
    printer.into_string()
}

pub fn print_stmt(stmt: &CStmt) -> String {
    let mut printer = Printer::with_default_config();
    printer.print_stmt(stmt);
    printer.into_string()
}

fn collect_called_names(tu: &TranslationUnit) -> std::collections::HashSet<String> {
    let mut names = std::collections::HashSet::new();
    for decl in &tu.decls {
        match decl {
            TopLevelDecl::FuncDef(f) => collect_called_names_stmt(&f.body, &mut names),
            TopLevelDecl::FuncDecl(f) => { names.insert(f.name.clone()); }
            _ => {}
        }
    }
    names
}

fn collect_called_names_stmt(stmt: &CStmt, names: &mut std::collections::HashSet<String>) {
    match stmt {
        CStmt::Expr(e) | CStmt::Return(Some(e)) => collect_called_names_expr(e, names),
        CStmt::If(cond, then_s, else_s) => {
            collect_called_names_expr(cond, names);
            collect_called_names_stmt(then_s, names);
            if let Some(e) = else_s { collect_called_names_stmt(e, names); }
        }
        CStmt::While(cond, body) => {
            collect_called_names_expr(cond, names);
            collect_called_names_stmt(body, names);
        }
        CStmt::DoWhile(body, cond) => {
            collect_called_names_stmt(body, names);
            collect_called_names_expr(cond, names);
        }
        CStmt::For(init, cond, update, body) => {
            if let Some(ForInit::Expr(e)) = init { collect_called_names_expr(e, names); }
            if let Some(c) = cond { collect_called_names_expr(c, names); }
            if let Some(u) = update { collect_called_names_expr(u, names); }
            collect_called_names_stmt(body, names);
        }
        CStmt::Switch(e, body) => {
            collect_called_names_expr(e, names);
            collect_called_names_stmt(body, names);
        }
        CStmt::Block(items) => {
            for item in items {
                match item {
                    CBlockItem::Stmt(s) => collect_called_names_stmt(s, names),
                    _ => {}
                }
            }
        }
        CStmt::Labeled(_, inner) => collect_called_names_stmt(inner, names),
        CStmt::Sequence(stmts) => {
            for s in stmts { collect_called_names_stmt(s, names); }
        }
        _ => {}
    }
}

fn collect_called_names_expr(expr: &CExpr, names: &mut std::collections::HashSet<String>) {
    match expr {
        CExpr::Call(func, args) => {
            if let CExpr::Var(name) = func.as_ref() {
                names.insert(name.clone());
            }
            collect_called_names_expr(func, names);
            for a in args { collect_called_names_expr(a, names); }
        }
        CExpr::Binary(_, l, r) | CExpr::Assign(_, l, r) => {
            collect_called_names_expr(l, names);
            collect_called_names_expr(r, names);
        }
        CExpr::Unary(_, inner) | CExpr::Cast(_, inner) | CExpr::Member(inner, _) | CExpr::MemberPtr(inner, _) => {
            collect_called_names_expr(inner, names);
        }
        CExpr::Ternary(c, t, e) => {
            collect_called_names_expr(c, names);
            collect_called_names_expr(t, names);
            collect_called_names_expr(e, names);
        }
        CExpr::Index(a, i) => {
            collect_called_names_expr(a, names);
            collect_called_names_expr(i, names);
        }
        _ => {}
    }
}

fn collect_needed_includes(tu: &TranslationUnit) -> Vec<&'static str> {
    let names = collect_called_names(tu);
    let mut includes = std::collections::BTreeSet::new();

    let mappings: &[(&[&str], &str)] = &[
        (&["printf", "fprintf", "sprintf", "snprintf", "puts", "putchar", "getchar",
           "fopen", "fclose", "fread", "fwrite", "fgets", "fputs", "fflush", "fseek",
           "ftell", "rewind", "sscanf", "fscanf", "perror", "stdin", "stdout", "stderr",
           "vprintf", "vfprintf", "vsprintf", "vsnprintf", "remove", "rename", "tmpfile",
           "setbuf", "setvbuf"], "<stdio.h>"),
        (&["malloc", "calloc", "realloc", "free", "exit", "abort", "atoi", "atol", "atof",
           "strtol", "strtoul", "strtod", "qsort", "bsearch", "abs", "labs", "getenv",
           "system", "rand", "srand", "EXIT_SUCCESS", "EXIT_FAILURE"], "<stdlib.h>"),
        (&["strlen", "strcmp", "strncmp", "strcpy", "strncpy", "strcat", "strncat",
           "memcpy", "memmove", "memset", "memcmp", "strstr", "strchr", "strrchr",
           "strtok", "strerror", "strdup", "strndup"], "<string.h>"),
        (&["isalpha", "isdigit", "isalnum", "isspace", "isupper", "islower", "toupper",
           "tolower", "isprint", "ispunct", "isxdigit", "iscntrl", "isgraph"], "<ctype.h>"),
        (&["assert", "__assert_fail"], "<assert.h>"),
        (&["va_start", "va_end", "va_arg", "va_copy"], "<stdarg.h>"),
        (&["errno"], "<errno.h>"),
        (&["open", "close", "read", "write", "lseek", "access", "unlink", "getpid",
           "getcwd", "chdir", "isatty", "dup", "dup2", "pipe", "fork", "execve"], "<unistd.h>"),
        (&["stat", "fstat", "lstat", "mkdir", "chmod"], "<sys/stat.h>"),
        (&["time", "clock", "difftime", "mktime", "localtime", "gmtime", "strftime",
           "ctime", "asctime"], "<time.h>"),
        (&["sin", "cos", "tan", "sqrt", "pow", "log", "log10", "exp", "fabs", "ceil",
           "floor", "round", "fmod", "atan2", "asin", "acos", "atan", "sinh", "cosh",
           "tanh", "__builtin_fabs"], "<math.h>"),
        (&["setjmp", "longjmp"], "<setjmp.h>"),
        (&["signal", "raise"], "<signal.h>"),
        (&["mmap", "munmap", "mprotect"], "<sys/mman.h>"),
        (&["socket", "bind", "listen", "accept", "connect", "send", "recv",
           "setsockopt", "getsockopt"], "<sys/socket.h>"),
        (&["htons", "htonl", "ntohs", "ntohl", "inet_addr", "inet_ntoa"], "<arpa/inet.h>"),
        (&["ioctl"], "<sys/ioctl.h>"),
        (&["fcntl"], "<fcntl.h>"),
        (&["select", "FD_SET", "FD_CLR", "FD_ISSET", "FD_ZERO"], "<sys/select.h>"),
        (&["pthread_create", "pthread_join", "pthread_mutex_lock", "pthread_mutex_unlock",
           "pthread_mutex_init", "pthread_mutex_destroy"], "<pthread.h>"),
    ];

    for (funcs, header) in mappings {
        for func in *funcs {
            if names.contains(*func) {
                includes.insert(*header);
                break;
            }
        }
    }

    includes.into_iter().collect()
}

