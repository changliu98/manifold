use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::decompile::passes::c_pass::helpers::{
    build_string_literal_map, collect_goto_label_targets, convert_param_type_from_param,
    extract_named_label, inline_string_literals, is_terminal_cstmt,
    param_name_for_reg, xtype_string_to_ctype,
};
use crate::decompile::passes::c_pass::types::{
    CExpr, CStmt, CType, FloatLiteral, FloatLiteralSuffix, IntLiteral, IntLiteralBase,
    IntLiteralSuffix, TopLevelDecl, TypeQualifiers,
};
use crate::x86::types::*;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// Known libc functions that take opaque struct pointer parameters; maps function_name -> Vec<(param_position, typedef_name)>.
fn known_opaque_struct_params() -> HashMap<&'static str, Vec<(usize, &'static str)>> {
    let mut m: HashMap<&str, Vec<(usize, &str)>> = HashMap::new();
    // FILE* at position 0
    for &func in &[
        "fclose", "fflush", "fgetc",
        "fseek", "fseeko", "ftell", "ftello", "rewind", "feof",
        "ferror", "clearerr", "fileno", "setbuf", "setvbuf",
        "fprintf", "fscanf", "vfprintf",
        "clearerr_unlocked",
        "feof_unlocked", "ferror_unlocked", "fileno_unlocked",
        "fgetc_unlocked", "getc_unlocked",
        "__freading", "__fpending", "__fwriting",
        "__freadable", "__fwritable", "__fsetlocking",
        "__overflow", "__uflow", "fclose_nothrow",
        "fflush_unlocked",
        "rpl_fclose", "rpl_fflush", "rpl_fseek", "rpl_fseeko",
        "rpl_ftell", "rpl_ftello", "rpl_fopen", "rpl_freopen",
    ] {
        m.entry(func).or_default().push((0, "FILE"));
    }
    // FILE* at position 1: int fputc(int, FILE*), int fputs(const char*, FILE*), etc.
    for &func in &["fputc", "fputs", "fputc_unlocked", "fputs_unlocked", "putc_unlocked"] {
        m.entry(func).or_default().push((1, "FILE"));
    }
    // FILE* at position 2: char* fgets(char*, int, FILE*)
    for &func in &["fgets", "fgets_unlocked"] {
        m.entry(func).or_default().push((2, "FILE"));
    }
    // fread/fwrite: FILE* at position 3
    for &func in &["fread", "fwrite", "fread_unlocked", "fwrite_unlocked"] {
        m.entry(func).or_default().push((3, "FILE"));
    }
    // DIR* at position 0
    for &func in &["closedir", "readdir", "readdir_r", "rewinddir", "seekdir", "telldir"] {
        m.entry(func).or_default().push((0, "DIR"));
    }
    m
}

/// Scan a CExpr to find struct names that appear in calls to known opaque-pointer functions.
fn collect_struct_names_from_expr(
    expr: &CExpr,
    opaque_params: &HashMap<&str, Vec<(usize, &str)>>,
    result: &mut HashMap<String, HashSet<String>>,
) {
    match expr {
        CExpr::Call(func_expr, args) => {
            // Get the function name from the call expression
            let func_name = match func_expr.as_ref() {
                CExpr::Var(name) => Some(name.as_str()),
                _ => None,
            };
            if let Some(name) = func_name {
                if let Some(param_info) = opaque_params.get(name) {
                    for &(pos, typedef_name) in param_info {
                        if pos < args.len() {
                            // Extract struct names from the argument expression
                            collect_struct_types_in_expr(&args[pos], typedef_name, result);
                        }
                    }
                }
            }
            // Recurse into subexpressions
            collect_struct_names_from_expr(func_expr, opaque_params, result);
            for arg in args {
                collect_struct_names_from_expr(arg, opaque_params, result);
            }
        }
        CExpr::Unary(_, inner) => collect_struct_names_from_expr(inner, opaque_params, result),
        CExpr::Binary(_, l, r) | CExpr::Assign(_, l, r) => {
            collect_struct_names_from_expr(l, opaque_params, result);
            collect_struct_names_from_expr(r, opaque_params, result);
        }
        CExpr::Ternary(c, t, e) => {
            collect_struct_names_from_expr(c, opaque_params, result);
            collect_struct_names_from_expr(t, opaque_params, result);
            collect_struct_names_from_expr(e, opaque_params, result);
        }
        CExpr::Cast(_, inner) => collect_struct_names_from_expr(inner, opaque_params, result),
        CExpr::Member(inner, _) | CExpr::MemberPtr(inner, _) => {
            collect_struct_names_from_expr(inner, opaque_params, result);
        }
        CExpr::Index(arr, idx) => {
            collect_struct_names_from_expr(arr, opaque_params, result);
            collect_struct_names_from_expr(idx, opaque_params, result);
        }
        CExpr::SizeofExpr(inner) | CExpr::Paren(inner) => {
            collect_struct_names_from_expr(inner, opaque_params, result);
        }
        _ => {}
    }
}

/// Extract struct type names from an expression that is passed to an opaque-pointer parameter.
fn collect_struct_types_in_expr(
    expr: &CExpr,
    typedef_name: &str,
    result: &mut HashMap<String, HashSet<String>>,
) {
    match expr {
        CExpr::Cast(CType::Pointer(inner, _), inner_expr) => {
            if let CType::Struct(name) = inner.as_ref() {
                result.entry(name.clone()).or_default().insert(typedef_name.to_string());
            }
            // Also recurse into the inner expression for nested casts
            collect_struct_types_in_expr(inner_expr, typedef_name, result);
        }
        CExpr::Var(_) => {
            // The variable itself might be typed as struct pointer; handled via var_types below
        }
        CExpr::Unary(_, inner) => collect_struct_types_in_expr(inner, typedef_name, result),
        CExpr::Paren(inner) => collect_struct_types_in_expr(inner, typedef_name, result),
        CExpr::Ternary(_, t, e) => {
            collect_struct_types_in_expr(t, typedef_name, result);
            collect_struct_types_in_expr(e, typedef_name, result);
        }
        _ => {}
    }
}

fn collect_struct_names_from_stmt(
    stmt: &CStmt,
    opaque_params: &HashMap<&str, Vec<(usize, &str)>>,
    result: &mut HashMap<String, HashSet<String>>,
) {
    match stmt {
        CStmt::Expr(e) => collect_struct_names_from_expr(e, opaque_params, result),
        CStmt::Block(items) => {
            for item in items {
                if let crate::decompile::passes::c_pass::types::CBlockItem::Stmt(s) = item {
                    collect_struct_names_from_stmt(s, opaque_params, result);
                }
            }
        }
        CStmt::If(c, t, e) => {
            collect_struct_names_from_expr(c, opaque_params, result);
            collect_struct_names_from_stmt(t, opaque_params, result);
            if let Some(e) = e { collect_struct_names_from_stmt(e, opaque_params, result); }
        }
        CStmt::Switch(e, body) => {
            collect_struct_names_from_expr(e, opaque_params, result);
            collect_struct_names_from_stmt(body, opaque_params, result);
        }
        CStmt::While(c, body) | CStmt::DoWhile(body, c) => {
            collect_struct_names_from_expr(c, opaque_params, result);
            collect_struct_names_from_stmt(body, opaque_params, result);
        }
        CStmt::For(_, cond, update, body) => {
            if let Some(c) = cond { collect_struct_names_from_expr(c, opaque_params, result); }
            if let Some(u) = update { collect_struct_names_from_expr(u, opaque_params, result); }
            collect_struct_names_from_stmt(body, opaque_params, result);
        }
        CStmt::Return(Some(e)) => collect_struct_names_from_expr(e, opaque_params, result),
        CStmt::Labeled(_, body) => collect_struct_names_from_stmt(body, opaque_params, result),
        CStmt::Sequence(stmts) => {
            for s in stmts { collect_struct_names_from_stmt(s, opaque_params, result); }
        }
        _ => {}
    }
}

/// Identify opaque libc struct types (FILE, DIR) from call args and function signatures.
fn identify_opaque_libc_structs_from_tu(
    tu: &crate::decompile::passes::c_pass::types::TranslationUnit,
) -> HashMap<String, String> {
    let opaque_params = known_opaque_struct_params();
    // Map from struct_name -> set of typedef_names it was identified as
    let mut struct_to_typedef: HashMap<String, HashSet<String>> = HashMap::new();

    // (1) Scan function bodies for calls to known opaque-pointer functions
    for decl in &tu.decls {
        if let TopLevelDecl::FuncDef(f) = decl {
            collect_struct_names_from_stmt(&f.body, &opaque_params, &mut struct_to_typedef);
        }
    }

    // (2) Check function signatures of known opaque-pointer functions for struct params. Only an EXTERNAL declaration (FuncDecl) is a genuine libc extern whose opaque-param typedef table (FILE*/DIR*) applies. A FuncDef is a LOCAL definition (external funcs are emitted as FuncDecl, never FuncDef - see `internal_functions` filtering), so its own recovered signature wins: a local function sharing a tabled libc name (e.g. a static helper named `fseek`) must NOT have its struct param force-tagged as FILE. The call-site scan in (1) still recovers typedefs from real calls to libc functions.
    for decl in &tu.decls {
        let (name, params) = match decl {
            TopLevelDecl::FuncDecl(f) => (f.name.as_str(), &f.params),
            _ => continue,
        };
        if let Some(param_info) = opaque_params.get(name) {
            for &(pos, typedef_name) in param_info {
                if pos < params.len() {
                    if let CType::Pointer(inner, _) = &params[pos].ty {
                        if let CType::Struct(sname) = inner.as_ref() {
                            struct_to_typedef
                                .entry(sname.clone())
                                .or_default()
                                .insert(typedef_name.to_string());
                        }
                    }
                }
            }
        }
    }

    // Only keep mappings where all votes agree on the same typedef name
    let mut result = HashMap::new();
    for (struct_name, typedef_names) in &struct_to_typedef {
        if typedef_names.len() == 1 {
            let typedef_name = typedef_names.iter().next().unwrap();
            result.insert(struct_name.clone(), typedef_name.clone());
        }
    }

    result
}

/// Rewrite a single CType, replacing opaque struct references with typedef names or void.
fn rewrite_ctype(ty: &CType, opaque_map: &HashMap<String, String>) -> CType {
    match ty {
        CType::Struct(name) => {
            if let Some(typedef_name) = opaque_map.get(name.as_str()) {
                if typedef_name == "void" {
                    CType::Void
                } else {
                    CType::TypedefName(typedef_name.clone())
                }
            } else {
                ty.clone()
            }
        }
        CType::Pointer(inner, quals) => {
            let new_inner = rewrite_ctype(inner, opaque_map);
            CType::Pointer(Box::new(new_inner), *quals)
        }
        CType::Array(inner, size) => {
            let new_inner = rewrite_ctype(inner, opaque_map);
            CType::Array(Box::new(new_inner), *size)
        }
        CType::Function(ret, params, variadic) => {
            let new_ret = rewrite_ctype(ret, opaque_map);
            let new_params: Vec<CType> = params.iter().map(|p| rewrite_ctype(p, opaque_map)).collect();
            CType::Function(Box::new(new_ret), new_params, *variadic)
        }
        CType::Qualified(inner, quals) => {
            let new_inner = rewrite_ctype(inner, opaque_map);
            CType::Qualified(Box::new(new_inner), *quals)
        }
        _ => ty.clone(),
    }
}

fn rewrite_ctype_in_expr(expr: &mut CExpr, opaque_map: &HashMap<String, String>) {
    match expr {
        CExpr::Cast(ty, inner) => {
            *ty = rewrite_ctype(ty, opaque_map);
            rewrite_ctype_in_expr(inner, opaque_map);
        }
        CExpr::SizeofType(ty) | CExpr::AlignofType(ty) => {
            *ty = rewrite_ctype(ty, opaque_map);
        }
        CExpr::Unary(_, inner) => rewrite_ctype_in_expr(inner, opaque_map),
        CExpr::Binary(_, l, r) | CExpr::Assign(_, l, r) => {
            rewrite_ctype_in_expr(l, opaque_map);
            rewrite_ctype_in_expr(r, opaque_map);
        }
        CExpr::Ternary(c, t, e) => {
            rewrite_ctype_in_expr(c, opaque_map);
            rewrite_ctype_in_expr(t, opaque_map);
            rewrite_ctype_in_expr(e, opaque_map);
        }
        CExpr::Call(f, args) => {
            rewrite_ctype_in_expr(f, opaque_map);
            for a in args { rewrite_ctype_in_expr(a, opaque_map); }
        }
        CExpr::Member(inner, _) | CExpr::MemberPtr(inner, _) => {
            rewrite_ctype_in_expr(inner, opaque_map);
        }
        CExpr::Index(arr, idx) => {
            rewrite_ctype_in_expr(arr, opaque_map);
            rewrite_ctype_in_expr(idx, opaque_map);
        }
        CExpr::SizeofExpr(inner) | CExpr::Paren(inner) => {
            rewrite_ctype_in_expr(inner, opaque_map);
        }
        CExpr::CompoundLit(ty, _) => {
            *ty = rewrite_ctype(ty, opaque_map);
        }
        _ => {}
    }
}

fn rewrite_ctype_in_stmt(stmt: &mut CStmt, opaque_map: &HashMap<String, String>) {
    match stmt {
        CStmt::Expr(e) => rewrite_ctype_in_expr(e, opaque_map),
        CStmt::Block(items) => {
            for item in items {
                match item {
                    crate::decompile::passes::c_pass::types::CBlockItem::Stmt(s) => {
                        rewrite_ctype_in_stmt(s, opaque_map);
                    }
                    crate::decompile::passes::c_pass::types::CBlockItem::Decl(decls) => {
                        for d in decls { d.ty = rewrite_ctype(&d.ty, opaque_map); }
                    }
                }
            }
        }
        CStmt::If(c, t, e) => {
            rewrite_ctype_in_expr(c, opaque_map);
            rewrite_ctype_in_stmt(t, opaque_map);
            if let Some(e) = e { rewrite_ctype_in_stmt(e, opaque_map); }
        }
        CStmt::Switch(e, body) => {
            rewrite_ctype_in_expr(e, opaque_map);
            rewrite_ctype_in_stmt(body, opaque_map);
        }
        CStmt::While(c, body) => {
            rewrite_ctype_in_expr(c, opaque_map);
            rewrite_ctype_in_stmt(body, opaque_map);
        }
        CStmt::DoWhile(body, c) => {
            rewrite_ctype_in_stmt(body, opaque_map);
            rewrite_ctype_in_expr(c, opaque_map);
        }
        CStmt::For(init, cond, update, body) => {
            if let Some(init) = init {
                match init {
                    crate::decompile::passes::c_pass::types::ForInit::Expr(e) => {
                        rewrite_ctype_in_expr(e, opaque_map);
                    }
                    crate::decompile::passes::c_pass::types::ForInit::Decl(decls) => {
                        for d in decls { d.ty = rewrite_ctype(&d.ty, opaque_map); }
                    }
                }
            }
            if let Some(c) = cond { rewrite_ctype_in_expr(c, opaque_map); }
            if let Some(u) = update { rewrite_ctype_in_expr(u, opaque_map); }
            rewrite_ctype_in_stmt(body, opaque_map);
        }
        CStmt::Return(Some(e)) => rewrite_ctype_in_expr(e, opaque_map),
        CStmt::Labeled(label, body) => {
            if let crate::decompile::passes::c_pass::types::Label::Case(e) = label {
                rewrite_ctype_in_expr(e, opaque_map);
            }
            rewrite_ctype_in_stmt(body, opaque_map);
        }
        CStmt::Decl(decls) => {
            for d in decls { d.ty = rewrite_ctype(&d.ty, opaque_map); }
        }
        CStmt::Sequence(stmts) => {
            for s in stmts { rewrite_ctype_in_stmt(s, opaque_map); }
        }
        _ => {}
    }
}

/// Rewrite CType::Struct references matching opaque libc types to CType::TypedefName in the TU.
fn rewrite_opaque_types_in_tu(
    tu: &mut crate::decompile::passes::c_pass::types::TranslationUnit,
    opaque_map: &HashMap<String, String>,
) {
    if opaque_map.is_empty() {
        return;
    }
    for decl in &mut tu.decls {
        match decl {
            TopLevelDecl::FuncDef(f) => {
                f.return_type = rewrite_ctype(&f.return_type, opaque_map);
                for p in &mut f.params { p.ty = rewrite_ctype(&p.ty, opaque_map); }
                for v in &mut f.local_vars { v.ty = rewrite_ctype(&v.ty, opaque_map); }
                rewrite_ctype_in_stmt(&mut f.body, opaque_map);
            }
            TopLevelDecl::FuncDecl(f) => {
                f.return_type = rewrite_ctype(&f.return_type, opaque_map);
                for p in &mut f.params { p.ty = rewrite_ctype(&p.ty, opaque_map); }
            }
            TopLevelDecl::VarDecl(v) => {
                v.ty = rewrite_ctype(&v.ty, opaque_map);
            }
            _ => {}
        }
    }
}

// SR-1 (FIXPLAN 4.5): bodies were converted when globals were still scalar-typed; against the new struct/array declarations, &g must decay to the element pointer and bare `g` must map to g[0] or g.<first_field> so that existing address-of and value uses keep compiling with the same semantics. Synthetic interior names are distinct Var strings handled in ClightEmitPass::run.
fn rewrite_recovered_global_expr(
    expr: &CExpr,
    arrays: &HashSet<String>,
    structs: &HashMap<String, String>,
) -> CExpr {
    use crate::decompile::passes::c_pass::types::UnaryOp;
    match expr {
        // *&g must be rewritten BEFORE the AddrOf arm: against recovered declarations the deref yields a struct/array, not the scalar lvalue the old declaration provided.
        CExpr::Unary(UnaryOp::Deref, outer_inner)
            if matches!(
                outer_inner.as_ref(),
                CExpr::Unary(UnaryOp::AddrOf, v)
                    if matches!(v.as_ref(), CExpr::Var(n)
                        if arrays.contains(n) || structs.contains_key(n))
            ) =>
        {
            let CExpr::Unary(UnaryOp::AddrOf, v) = outer_inner.as_ref() else {
                unreachable!("guard matched AddrOf");
            };
            let CExpr::Var(n) = v.as_ref() else {
                unreachable!("guard matched Var");
            };
            if arrays.contains(n) {
                CExpr::Index(Box::new(CExpr::Var(n.clone())), Box::new(CExpr::int(0)))
            } else {
                CExpr::Member(Box::new(CExpr::Var(n.clone())), structs[n].clone())
            }
        }
        // &g must be decided BEFORE the generic recursion rewrites the inner Var.
        CExpr::Unary(UnaryOp::AddrOf, inner) => match inner.as_ref() {
            CExpr::Var(n) if arrays.contains(n) => CExpr::Var(n.clone()),
            CExpr::Var(n) if structs.contains_key(n) => expr.clone(),
            _ => CExpr::Unary(
                UnaryOp::AddrOf,
                Box::new(rewrite_recovered_global_expr(inner, arrays, structs)),
            ),
        },
        CExpr::Var(n) if arrays.contains(n) => {
            CExpr::Index(Box::new(CExpr::Var(n.clone())), Box::new(CExpr::int(0)))
        }
        CExpr::Var(n) => match structs.get(n) {
            Some(first_field) => {
                CExpr::Member(Box::new(CExpr::Var(n.clone())), first_field.clone())
            }
            None => expr.clone(),
        },
        CExpr::Unary(op, inner) => CExpr::Unary(
            *op,
            Box::new(rewrite_recovered_global_expr(inner, arrays, structs)),
        ),
        CExpr::Binary(op, l, r) => CExpr::Binary(
            *op,
            Box::new(rewrite_recovered_global_expr(l, arrays, structs)),
            Box::new(rewrite_recovered_global_expr(r, arrays, structs)),
        ),
        CExpr::Assign(op, l, r) => CExpr::Assign(
            *op,
            Box::new(rewrite_recovered_global_expr(l, arrays, structs)),
            Box::new(rewrite_recovered_global_expr(r, arrays, structs)),
        ),
        CExpr::Ternary(c, t, e) => CExpr::Ternary(
            Box::new(rewrite_recovered_global_expr(c, arrays, structs)),
            Box::new(rewrite_recovered_global_expr(t, arrays, structs)),
            Box::new(rewrite_recovered_global_expr(e, arrays, structs)),
        ),
        CExpr::Call(f, args) => CExpr::Call(
            Box::new(rewrite_recovered_global_expr(f, arrays, structs)),
            args.iter()
                .map(|a| rewrite_recovered_global_expr(a, arrays, structs))
                .collect(),
        ),
        CExpr::Cast(ty, inner) => CExpr::Cast(
            ty.clone(),
            Box::new(rewrite_recovered_global_expr(inner, arrays, structs)),
        ),
        CExpr::Member(base, f) => CExpr::Member(
            Box::new(rewrite_recovered_global_expr(base, arrays, structs)),
            f.clone(),
        ),
        CExpr::MemberPtr(base, f) => CExpr::MemberPtr(
            Box::new(rewrite_recovered_global_expr(base, arrays, structs)),
            f.clone(),
        ),
        CExpr::Index(arr, idx) => CExpr::Index(
            Box::new(rewrite_recovered_global_expr(arr, arrays, structs)),
            Box::new(rewrite_recovered_global_expr(idx, arrays, structs)),
        ),
        CExpr::SizeofExpr(inner) => CExpr::SizeofExpr(Box::new(rewrite_recovered_global_expr(
            inner, arrays, structs,
        ))),
        CExpr::Paren(inner) => CExpr::Paren(Box::new(rewrite_recovered_global_expr(
            inner, arrays, structs,
        ))),
        _ => expr.clone(),
    }
}

fn rewrite_recovered_global_init(
    init: &mut crate::decompile::passes::c_pass::types::Initializer,
    arrays: &HashSet<String>,
    structs: &HashMap<String, String>,
) {
    use crate::decompile::passes::c_pass::types::Initializer;
    match init {
        Initializer::Expr(e) => *e = rewrite_recovered_global_expr(e, arrays, structs),
        Initializer::List(items) => {
            for item in items {
                rewrite_recovered_global_init(&mut item.init, arrays, structs);
            }
        }
        Initializer::String(_) => {}
    }
}

fn rewrite_recovered_global_stmt(
    stmt: &mut CStmt,
    arrays: &HashSet<String>,
    structs: &HashMap<String, String>,
) {
    match stmt {
        CStmt::Expr(e) => *e = rewrite_recovered_global_expr(e, arrays, structs),
        CStmt::Block(items) => {
            for item in items {
                match item {
                    crate::decompile::passes::c_pass::types::CBlockItem::Stmt(s) => {
                        rewrite_recovered_global_stmt(s, arrays, structs);
                    }
                    crate::decompile::passes::c_pass::types::CBlockItem::Decl(decls) => {
                        for d in decls {
                            if let Some(init) = &mut d.init {
                                rewrite_recovered_global_init(init, arrays, structs);
                            }
                        }
                    }
                }
            }
        }
        CStmt::If(c, t, e) => {
            *c = rewrite_recovered_global_expr(c, arrays, structs);
            rewrite_recovered_global_stmt(t, arrays, structs);
            if let Some(e) = e {
                rewrite_recovered_global_stmt(e, arrays, structs);
            }
        }
        CStmt::Switch(e, body) => {
            *e = rewrite_recovered_global_expr(e, arrays, structs);
            rewrite_recovered_global_stmt(body, arrays, structs);
        }
        CStmt::While(c, body) => {
            *c = rewrite_recovered_global_expr(c, arrays, structs);
            rewrite_recovered_global_stmt(body, arrays, structs);
        }
        CStmt::DoWhile(body, c) => {
            rewrite_recovered_global_stmt(body, arrays, structs);
            *c = rewrite_recovered_global_expr(c, arrays, structs);
        }
        CStmt::For(init, cond, update, body) => {
            if let Some(init) = init {
                match init {
                    crate::decompile::passes::c_pass::types::ForInit::Expr(e) => {
                        *e = rewrite_recovered_global_expr(e, arrays, structs);
                    }
                    crate::decompile::passes::c_pass::types::ForInit::Decl(decls) => {
                        for d in decls {
                            if let Some(i) = &mut d.init {
                                rewrite_recovered_global_init(i, arrays, structs);
                            }
                        }
                    }
                }
            }
            if let Some(c) = cond {
                *c = rewrite_recovered_global_expr(c, arrays, structs);
            }
            if let Some(u) = update {
                *u = rewrite_recovered_global_expr(u, arrays, structs);
            }
            rewrite_recovered_global_stmt(body, arrays, structs);
        }
        CStmt::Return(Some(e)) => *e = rewrite_recovered_global_expr(e, arrays, structs),
        CStmt::Labeled(label, body) => {
            if let crate::decompile::passes::c_pass::types::Label::Case(e) = label {
                *e = rewrite_recovered_global_expr(e, arrays, structs);
            }
            rewrite_recovered_global_stmt(body, arrays, structs);
        }
        CStmt::Decl(decls) => {
            for d in decls {
                if let Some(init) = &mut d.init {
                    rewrite_recovered_global_init(init, arrays, structs);
                }
            }
        }
        CStmt::Sequence(stmts) => {
            for s in stmts {
                rewrite_recovered_global_stmt(s, arrays, structs);
            }
        }
        _ => {}
    }
}

// IL-3/IL-4: classify each recovered struct by usage in the final TU (not by name or field-name prefix): !referenced -> void; referenced+!needs_layout -> opaque empty-body tag; needs_layout -> full definition. needs_layout requires a by-value object, member access, dereference/index, pointer arithmetic, or sizeof -- uses the same declared types the C compiler will see, so the typing walk can never produce a spurious "incomplete type". The libc name table is a naming fallback only; a struct whose fields are accessed keeps its full definition even if it also flows into fclose().

#[derive(Default)]
struct StructLayoutEvidence {
    /// Struct/union tags whose complete layout the TU requires.
    needs_layout: HashSet<String>,
    /// True when some layout-relevant base expression could not be typed; caller must treat every struct as needing its layout.
    incomplete: bool,
    /// First few untypeable sites (debug aid for extending the walker).
    incomplete_samples: Vec<String>,
}

impl StructLayoutEvidence {
    fn mark_incomplete(&mut self, site: &dyn std::fmt::Debug) {
        self.incomplete = true;
        if self.incomplete_samples.len() < 8 {
            let mut s = format!("{:?}", site);
            s.truncate(200);
            self.incomplete_samples.push(s);
        }
    }
}

/// Declared-type environment for the layout walk.
struct LayoutEnv<'a> {
    locals: HashMap<String, CType>,
    globals: &'a HashMap<String, CType>,
    callee_ret: &'a HashMap<String, CType>,
    /// tag name -> field name -> declared field type (from the recovered defs).
    fields: &'a HashMap<String, HashMap<String, CType>>,
}

impl LayoutEnv<'_> {
    fn var_type(&self, name: &str) -> Option<&CType> {
        self.locals.get(name).or_else(|| self.globals.get(name))
    }
}

fn strip_quals(ty: &CType) -> &CType {
    match ty {
        CType::Qualified(inner, _) => strip_quals(inner),
        _ => ty,
    }
}

/// Record that a complete object of type `ty` is required (recurses through arrays/qualifiers but NOT through pointers).
fn note_complete_object(ty: &CType, ev: &mut StructLayoutEvidence) {
    match ty {
        CType::Struct(name) | CType::Union(name) => {
            ev.needs_layout.insert(name.clone());
        }
        CType::Array(inner, _) | CType::Qualified(inner, _) => note_complete_object(inner, ev),
        _ => {}
    }
}

/// Pointer arithmetic / indexing / dereference through `ptr_ty` requires the pointee to be complete.
fn note_pointee_complete(ptr_ty: &CType, ev: &mut StructLayoutEvidence) {
    match strip_quals(ptr_ty) {
        CType::Pointer(inner, _) | CType::Array(inner, _) => note_complete_object(inner, ev),
        _ => {}
    }
}

/// Type an expression with declared types while recording layout evidence. Returns None when the type cannot be determined; consumers that need the base type (member access, pointer arithmetic, sizeof) set `ev.incomplete` on None so the caller can fall back conservatively.
fn layout_walk_expr(expr: &CExpr, env: &LayoutEnv, ev: &mut StructLayoutEvidence) -> Option<CType> {
    use crate::decompile::passes::c_pass::types::{
        BinaryOp, FloatLiteralSuffix, FloatSize, IntSize, Signedness, UnaryOp,
    };
    match expr {
        CExpr::IntLit(l) => {
            let wide = !matches!(l.suffix, crate::decompile::passes::c_pass::types::IntLiteralSuffix::None
                | crate::decompile::passes::c_pass::types::IntLiteralSuffix::U)
                || l.value < i32::MIN as i128
                || l.value > u32::MAX as i128;
            Some(CType::Int(if wide { IntSize::Long } else { IntSize::Int }, Signedness::Signed))
        }
        CExpr::FloatLit(l) => Some(CType::Float(if matches!(l.suffix, FloatLiteralSuffix::F) {
            FloatSize::Float
        } else {
            FloatSize::Double
        })),
        CExpr::StringLit(_) => Some(CType::ptr(CType::char_signed())),
        CExpr::CharLit(_) => Some(CType::int()),
        CExpr::Var(name) => env.var_type(name).cloned(),
        CExpr::Paren(inner) => layout_walk_expr(inner, env, ev),
        CExpr::Cast(ty, inner) => {
            layout_walk_expr(inner, env, ev);
            // A cast TO a by-value struct (rare) makes the layout observable.
            note_complete_object(strip_quals(ty), ev);
            Some(ty.clone())
        }
        CExpr::Unary(UnaryOp::AddrOf, inner) => {
            let it = layout_walk_expr(inner, env, ev);
            it.map(CType::ptr)
        }
        CExpr::Unary(UnaryOp::Deref, inner) => {
            let it = layout_walk_expr(inner, env, ev);
            match it.as_ref().map(strip_quals) {
                Some(CType::Pointer(p, _)) => {
                    note_complete_object(strip_quals(p), ev);
                    Some(p.as_ref().clone())
                }
                Some(CType::Array(elem, _)) => {
                    note_complete_object(strip_quals(elem), ev);
                    Some(elem.as_ref().clone())
                }
                Some(_) => {
                    // Deref of a definitely non-pointer: already a compile error in emitted C -- no layout implication.
                    None
                }
                None => {
                    // Untypeable base: could hide a struct pointer.
                    ev.mark_incomplete(expr);
                    None
                }
            }
        }
        CExpr::Unary(UnaryOp::Not, inner) => {
            layout_walk_expr(inner, env, ev);
            Some(CType::int())
        }
        CExpr::Unary(
            UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec,
            inner,
        ) => {
            // ++/-- on a pointer is pointer arithmetic.
            let it = layout_walk_expr(inner, env, ev);
            match it.as_ref().map(strip_quals) {
                Some(t @ CType::Pointer(_, _)) => note_pointee_complete(t, ev),
                Some(_) => {}
                None => ev.mark_incomplete(expr),
            }
            it
        }
        CExpr::Unary(_, inner) => {
            // Neg / Plus / BitNot: numeric, type-preserving enough for our use.
            layout_walk_expr(inner, env, ev)
        }
        CExpr::Binary(op, l, r) => {
            let lt = layout_walk_expr(l, env, ev);
            let rt = layout_walk_expr(r, env, ev);
            match op {
                BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt
                | BinaryOp::Ge | BinaryOp::And | BinaryOp::Or => Some(CType::int()),
                BinaryOp::Add | BinaryOp::Sub => {
                    let l_is_ptr = matches!(lt.as_ref().map(strip_quals), Some(CType::Pointer(_, _) | CType::Array(_, _)));
                    let r_is_ptr = matches!(rt.as_ref().map(strip_quals), Some(CType::Pointer(_, _) | CType::Array(_, _)));
                    if l_is_ptr {
                        note_pointee_complete(lt.as_ref().unwrap(), ev);
                    }
                    if r_is_ptr {
                        note_pointee_complete(rt.as_ref().unwrap(), ev);
                    }
                    match (l_is_ptr, r_is_ptr) {
                        (true, true) => Some(CType::long()), // ptr - ptr
                        // The non-pointer side being untypeable is harmless: it is the integer offset operand.
                        (true, false) => lt,
                        (false, true) => rt,
                        (false, false) => {
                            // Pointer arithmetic hidden behind an untypeable operand would need the pointee's size.
                            if lt.is_none() || rt.is_none() {
                                ev.mark_incomplete(expr);
                                None
                            } else {
                                lt
                            }
                        }
                    }
                }
                _ => {
                    // Mul/Div/Mod/bitwise/shifts: numeric only; pointers cannot legally appear, so unknown operands are harmless.
                    lt.or(rt)
                }
            }
        }
        CExpr::Assign(op, l, r) => {
            let lt = layout_walk_expr(l, env, ev);
            layout_walk_expr(r, env, ev);
            if !matches!(op, crate::decompile::passes::c_pass::types::AssignOp::Assign) {
                // Compound assignment on a pointer (p += n) is pointer arithmetic.
                match lt.as_ref().map(strip_quals) {
                    Some(t @ CType::Pointer(_, _)) => note_pointee_complete(t, ev),
                    Some(_) => {}
                    None => ev.mark_incomplete(expr),
                }
            }
            lt
        }
        CExpr::Ternary(c, t, e) => {
            layout_walk_expr(c, env, ev);
            let tt = layout_walk_expr(t, env, ev);
            let et = layout_walk_expr(e, env, ev);
            tt.or(et)
        }
        CExpr::Call(callee, args) => {
            for a in args {
                layout_walk_expr(a, env, ev);
            }
            match callee.as_ref() {
                CExpr::Var(name) => env.callee_ret.get(name).cloned(),
                other => {
                    let ct = layout_walk_expr(other, env, ev);
                    match ct.as_ref().map(strip_quals) {
                        Some(CType::Function(ret, _, _)) => Some(ret.as_ref().clone()),
                        Some(CType::Pointer(inner, _)) => match strip_quals(inner) {
                            CType::Function(ret, _, _) => Some(ret.as_ref().clone()),
                            _ => None,
                        },
                        _ => None,
                    }
                }
            }
        }
        CExpr::Member(base, field) => {
            let bt = layout_walk_expr(base, env, ev);
            match bt.as_ref().map(strip_quals) {
                Some(CType::Struct(name)) | Some(CType::Union(name)) => {
                    ev.needs_layout.insert(name.clone());
                    // A missing field is already a compile error in emitted C; the unknown result type propagates as None.
                    env.fields.get(name).and_then(|m| m.get(field)).cloned()
                }
                // Member access on a definitely non-struct type is already a compile error regardless of layout decisions -- no flag.
                Some(_) => None,
                None => {
                    ev.mark_incomplete(expr);
                    None
                }
            }
        }
        CExpr::MemberPtr(base, field) => {
            let bt = layout_walk_expr(base, env, ev);
            match bt.as_ref().map(strip_quals) {
                Some(CType::Pointer(inner, _)) | Some(CType::Array(inner, _)) => {
                    match strip_quals(inner) {
                        CType::Struct(name) | CType::Union(name) => {
                            ev.needs_layout.insert(name.clone());
                            env.fields.get(name).and_then(|m| m.get(field)).cloned()
                        }
                        // `->` through a non-struct pointer: compile error regardless of layout decisions -- no flag.
                        _ => None,
                    }
                }
                // `->` on a definitely non-pointer type: compile error anyway.
                Some(_) => None,
                None => {
                    ev.mark_incomplete(expr);
                    None
                }
            }
        }
        CExpr::Index(arr, idx) => {
            let at = layout_walk_expr(arr, env, ev);
            let it = layout_walk_expr(idx, env, ev);
            // C allows the commuted form i[arr]; pick whichever side is a pointer.
            let base = match at.as_ref().map(strip_quals) {
                Some(CType::Pointer(_, _) | CType::Array(_, _)) => at.clone(),
                _ => match it.as_ref().map(strip_quals) {
                    Some(CType::Pointer(_, _) | CType::Array(_, _)) => it.clone(),
                    _ => None,
                },
            };
            match base.as_ref().map(strip_quals) {
                Some(t @ (CType::Pointer(inner, _) | CType::Array(inner, _))) => {
                    note_pointee_complete(t, ev);
                    Some(inner.as_ref().clone())
                }
                _ => {
                    // Only an UNTYPEABLE operand can hide a struct pointer; two definitely-typed non-pointer operands are a compile error regardless.
                    if at.is_none() || it.is_none() {
                        ev.mark_incomplete(expr);
                    }
                    None
                }
            }
        }
        CExpr::SizeofType(ty) | CExpr::AlignofType(ty) => {
            note_complete_object(strip_quals(ty), ev);
            Some(CType::ulong())
        }
        CExpr::SizeofExpr(inner) => {
            match layout_walk_expr(inner, env, ev) {
                Some(t) => note_complete_object(strip_quals(&t), ev),
                None => ev.mark_incomplete(expr),
            }
            Some(CType::ulong())
        }
        CExpr::CompoundLit(ty, items) => {
            note_complete_object(strip_quals(ty), ev);
            for item in items {
                layout_walk_initializer(item, env, ev);
            }
            Some(ty.clone())
        }
        CExpr::StmtExpr(stmts, last) => {
            for s in stmts {
                layout_walk_stmt(s, env, ev);
            }
            layout_walk_expr(last, env, ev)
        }
        CExpr::Generic(ctrl, arms) => {
            layout_walk_expr(ctrl, env, ev);
            for (_, e) in arms {
                layout_walk_expr(e, env, ev);
            }
            None
        }
    }
}

fn layout_walk_initializer(
    init: &crate::decompile::passes::c_pass::types::Initializer,
    env: &LayoutEnv,
    ev: &mut StructLayoutEvidence,
) {
    use crate::decompile::passes::c_pass::types::Initializer;
    match init {
        Initializer::Expr(e) => {
            layout_walk_expr(e, env, ev);
        }
        Initializer::List(items) => {
            for item in items {
                layout_walk_initializer(&item.init, env, ev);
            }
        }
        Initializer::String(_) => {}
    }
}

fn layout_walk_stmt(stmt: &CStmt, env: &LayoutEnv, ev: &mut StructLayoutEvidence) {
    use crate::decompile::passes::c_pass::types::{CBlockItem, ForInit, Label};
    match stmt {
        CStmt::Expr(e) => {
            layout_walk_expr(e, env, ev);
        }
        CStmt::Block(items) => {
            for item in items {
                match item {
                    CBlockItem::Stmt(s) => layout_walk_stmt(s, env, ev),
                    CBlockItem::Decl(decls) => {
                        for d in decls {
                            note_complete_object(strip_quals(&d.ty), ev);
                            if let Some(init) = &d.init {
                                layout_walk_initializer(init, env, ev);
                            }
                        }
                    }
                }
            }
        }
        CStmt::If(c, t, e) => {
            layout_walk_expr(c, env, ev);
            layout_walk_stmt(t, env, ev);
            if let Some(e) = e {
                layout_walk_stmt(e, env, ev);
            }
        }
        CStmt::Switch(e, body) => {
            layout_walk_expr(e, env, ev);
            layout_walk_stmt(body, env, ev);
        }
        CStmt::While(c, body) => {
            layout_walk_expr(c, env, ev);
            layout_walk_stmt(body, env, ev);
        }
        CStmt::DoWhile(body, c) => {
            layout_walk_stmt(body, env, ev);
            layout_walk_expr(c, env, ev);
        }
        CStmt::For(init, cond, update, body) => {
            if let Some(init) = init {
                match init {
                    ForInit::Expr(e) => {
                        layout_walk_expr(e, env, ev);
                    }
                    ForInit::Decl(decls) => {
                        for d in decls {
                            note_complete_object(strip_quals(&d.ty), ev);
                            if let Some(i) = &d.init {
                                layout_walk_initializer(i, env, ev);
                            }
                        }
                    }
                }
            }
            if let Some(c) = cond {
                layout_walk_expr(c, env, ev);
            }
            if let Some(u) = update {
                layout_walk_expr(u, env, ev);
            }
            layout_walk_stmt(body, env, ev);
        }
        CStmt::Return(Some(e)) => {
            layout_walk_expr(e, env, ev);
        }
        CStmt::Labeled(label, body) => {
            if let Label::Case(e) = label {
                layout_walk_expr(e, env, ev);
            }
            layout_walk_stmt(body, env, ev);
        }
        CStmt::Decl(decls) => {
            for d in decls {
                note_complete_object(strip_quals(&d.ty), ev);
                if let Some(init) = &d.init {
                    layout_walk_initializer(init, env, ev);
                }
            }
        }
        CStmt::Sequence(stmts) => {
            for s in stmts {
                layout_walk_stmt(s, env, ev);
            }
        }
        _ => {}
    }
}

/// Walk the whole TU and collect layout evidence: which struct tags need their complete layout, and whether the typing analysis covered every layout-relevant site.
fn collect_struct_layout_evidence(
    tu: &crate::decompile::passes::c_pass::types::TranslationUnit,
    field_types: &HashMap<String, HashMap<String, CType>>,
) -> StructLayoutEvidence {
    let mut ev = StructLayoutEvidence::default();

    // Declared-type maps the compiler will see.
    let mut globals: HashMap<String, CType> = HashMap::new();
    let mut callee_ret: HashMap<String, CType> = HashMap::new();
    for decl in &tu.decls {
        match decl {
            TopLevelDecl::FuncDef(f) => {
                callee_ret.insert(f.name.clone(), f.return_type.clone());
            }
            TopLevelDecl::FuncDecl(d) => {
                callee_ret.entry(d.name.clone()).or_insert_with(|| d.return_type.clone());
            }
            TopLevelDecl::VarDecl(v) => {
                globals.insert(v.name.clone(), v.ty.clone());
            }
            _ => {}
        }
    }

    for decl in &tu.decls {
        match decl {
            TopLevelDecl::FuncDef(f) => {
                // By-value type positions.
                note_complete_object(strip_quals(&f.return_type), &mut ev);
                let mut locals: HashMap<String, CType> = HashMap::new();
                for p in &f.params {
                    note_complete_object(strip_quals(&p.ty), &mut ev);
                    if let Some(n) = &p.name {
                        locals.insert(n.clone(), p.ty.clone());
                    }
                }
                for v in &f.local_vars {
                    note_complete_object(strip_quals(&v.ty), &mut ev);
                    locals.insert(v.name.clone(), v.ty.clone());
                }
                let env = LayoutEnv {
                    locals,
                    globals: &globals,
                    callee_ret: &callee_ret,
                    fields: field_types,
                };
                for v in &f.local_vars {
                    if let Some(init) = &v.init {
                        layout_walk_initializer(init, &env, &mut ev);
                    }
                }
                layout_walk_stmt(&f.body, &env, &mut ev);
            }
            TopLevelDecl::FuncDecl(d) => {
                note_complete_object(strip_quals(&d.return_type), &mut ev);
                for p in &d.params {
                    note_complete_object(strip_quals(&p.ty), &mut ev);
                }
            }
            TopLevelDecl::VarDecl(v) => {
                note_complete_object(strip_quals(&v.ty), &mut ev);
                if let Some(init) = &v.init {
                    let env = LayoutEnv {
                        locals: HashMap::new(),
                        globals: &globals,
                        callee_ret: &callee_ret,
                        fields: field_types,
                    };
                    layout_walk_initializer(init, &env, &mut ev);
                }
            }
            _ => {}
        }
    }
    ev
}

/// Record the struct tags named by a field type of an EMITTED definition: by-value occurrences (including array elements, even behind a pointer-to-array) need their complete layout; pointer occurrences only keep the tag referenced. Returns true when a set changed (drives the emit-closure fixpoint).
fn note_emitted_field_type(
    ty: &CType,
    behind_ptr: bool,
    needs_layout: &mut HashSet<String>,
    referenced: &mut HashSet<String>,
) -> bool {
    match ty {
        CType::Struct(n) | CType::Union(n) => {
            let mut changed = referenced.insert(n.clone());
            if !behind_ptr {
                changed |= needs_layout.insert(n.clone());
            }
            changed
        }
        // An array's element type must be complete wherever the array type is spelled, even behind a pointer (`struct S (*p)[3]` requires S complete).
        CType::Array(inner, _) => note_emitted_field_type(inner, false, needs_layout, referenced),
        CType::Qualified(inner, _) => {
            note_emitted_field_type(inner, behind_ptr, needs_layout, referenced)
        }
        CType::Pointer(inner, _) => note_emitted_field_type(inner, true, needs_layout, referenced),
        CType::Function(ret, params, _) => {
            // A function type in a member declaration only references its parameter/return tags (no completeness needed to declare).
            let mut changed = note_emitted_field_type(ret, true, needs_layout, referenced);
            for p in params {
                changed |= note_emitted_field_type(p, true, needs_layout, referenced);
            }
            changed
        }
        _ => false,
    }
}

/// Collect struct names used by value (directly as CType::Struct, not behind a pointer).
fn collect_all_referenced_structs(
    tu: &crate::decompile::passes::c_pass::types::TranslationUnit,
) -> HashSet<String> {
    let mut referenced = HashSet::new();

    // Collect ALL struct names referenced in types (both by-value and via pointers)
    fn collect_struct_refs(ty: &CType, result: &mut HashSet<String>) {
        match ty {
            CType::Struct(name) => { result.insert(name.clone()); }
            CType::Pointer(inner, _) => collect_struct_refs(inner, result),
            CType::Array(inner, _) => collect_struct_refs(inner, result),
            CType::Function(ret, params, _) => {
                collect_struct_refs(ret, result);
                for p in params { collect_struct_refs(p, result); }
            }
            CType::Qualified(inner, _) => collect_struct_refs(inner, result),
            _ => {}
        }
    }

    for decl in &tu.decls {
        match decl {
            TopLevelDecl::FuncDef(f) => {
                collect_struct_refs(&f.return_type, &mut referenced);
                for p in &f.params { collect_struct_refs(&p.ty, &mut referenced); }
                for v in &f.local_vars { collect_struct_refs(&v.ty, &mut referenced); }
                // A struct may only appear inside a cast in the body (e.g. ((struct_1 *)p)->ofs_8 when p is typed as a generic pointer). Walk the body so such structs are not mistaken for unreferenced and suppressed to void; mirrors rewrite_ctype_in_stmt which would otherwise rewrite those casts.
                collect_referenced_structs_in_stmt(&f.body, &mut referenced);
            }
            TopLevelDecl::FuncDecl(f) => {
                collect_struct_refs(&f.return_type, &mut referenced);
                for p in &f.params { collect_struct_refs(&p.ty, &mut referenced); }
            }
            TopLevelDecl::VarDecl(v) => {
                collect_struct_refs(&v.ty, &mut referenced);
            }
            _ => {}
        }
    }

    referenced
}

/// Collect struct names from every CType appearing in an expression (casts, sizeof/alignof, compound literals). Mirrors rewrite_ctype_in_expr so the suppression collector sees exactly the locations the rewriter would touch.
fn collect_referenced_structs_in_expr(expr: &CExpr, result: &mut HashSet<String>) {
    fn collect_struct_refs(ty: &CType, result: &mut HashSet<String>) {
        match ty {
            CType::Struct(name) => { result.insert(name.clone()); }
            CType::Pointer(inner, _) => collect_struct_refs(inner, result),
            CType::Array(inner, _) => collect_struct_refs(inner, result),
            CType::Function(ret, params, _) => {
                collect_struct_refs(ret, result);
                for p in params { collect_struct_refs(p, result); }
            }
            CType::Qualified(inner, _) => collect_struct_refs(inner, result),
            _ => {}
        }
    }
    match expr {
        CExpr::Cast(ty, inner) => {
            collect_struct_refs(ty, result);
            collect_referenced_structs_in_expr(inner, result);
        }
        CExpr::SizeofType(ty) | CExpr::AlignofType(ty) => collect_struct_refs(ty, result),
        CExpr::CompoundLit(ty, _) => collect_struct_refs(ty, result),
        CExpr::Unary(_, inner) => collect_referenced_structs_in_expr(inner, result),
        CExpr::Binary(_, l, r) | CExpr::Assign(_, l, r) => {
            collect_referenced_structs_in_expr(l, result);
            collect_referenced_structs_in_expr(r, result);
        }
        CExpr::Ternary(c, t, e) => {
            collect_referenced_structs_in_expr(c, result);
            collect_referenced_structs_in_expr(t, result);
            collect_referenced_structs_in_expr(e, result);
        }
        CExpr::Call(f, args) => {
            collect_referenced_structs_in_expr(f, result);
            for a in args { collect_referenced_structs_in_expr(a, result); }
        }
        CExpr::Member(inner, _) | CExpr::MemberPtr(inner, _) => {
            collect_referenced_structs_in_expr(inner, result);
        }
        CExpr::Index(arr, idx) => {
            collect_referenced_structs_in_expr(arr, result);
            collect_referenced_structs_in_expr(idx, result);
        }
        CExpr::SizeofExpr(inner) | CExpr::Paren(inner) => {
            collect_referenced_structs_in_expr(inner, result);
        }
        _ => {}
    }
}

/// Collect struct names from every CType in a statement (expressions and inline declarations). Mirrors rewrite_ctype_in_stmt.
fn collect_referenced_structs_in_stmt(stmt: &CStmt, result: &mut HashSet<String>) {
    fn collect_struct_refs(ty: &CType, result: &mut HashSet<String>) {
        match ty {
            CType::Struct(name) => { result.insert(name.clone()); }
            CType::Pointer(inner, _) => collect_struct_refs(inner, result),
            CType::Array(inner, _) => collect_struct_refs(inner, result),
            CType::Function(ret, params, _) => {
                collect_struct_refs(ret, result);
                for p in params { collect_struct_refs(p, result); }
            }
            CType::Qualified(inner, _) => collect_struct_refs(inner, result),
            _ => {}
        }
    }
    match stmt {
        CStmt::Expr(e) => collect_referenced_structs_in_expr(e, result),
        CStmt::Block(items) => {
            for item in items {
                match item {
                    crate::decompile::passes::c_pass::types::CBlockItem::Stmt(s) => {
                        collect_referenced_structs_in_stmt(s, result);
                    }
                    crate::decompile::passes::c_pass::types::CBlockItem::Decl(decls) => {
                        for d in decls { collect_struct_refs(&d.ty, result); }
                    }
                }
            }
        }
        CStmt::If(c, t, e) => {
            collect_referenced_structs_in_expr(c, result);
            collect_referenced_structs_in_stmt(t, result);
            if let Some(e) = e { collect_referenced_structs_in_stmt(e, result); }
        }
        CStmt::Switch(e, body) => {
            collect_referenced_structs_in_expr(e, result);
            collect_referenced_structs_in_stmt(body, result);
        }
        CStmt::While(c, body) => {
            collect_referenced_structs_in_expr(c, result);
            collect_referenced_structs_in_stmt(body, result);
        }
        CStmt::DoWhile(body, c) => {
            collect_referenced_structs_in_stmt(body, result);
            collect_referenced_structs_in_expr(c, result);
        }
        CStmt::For(init, cond, update, body) => {
            if let Some(init) = init {
                match init {
                    crate::decompile::passes::c_pass::types::ForInit::Expr(e) => {
                        collect_referenced_structs_in_expr(e, result);
                    }
                    crate::decompile::passes::c_pass::types::ForInit::Decl(decls) => {
                        for d in decls { collect_struct_refs(&d.ty, result); }
                    }
                }
            }
            if let Some(c) = cond { collect_referenced_structs_in_expr(c, result); }
            if let Some(u) = update { collect_referenced_structs_in_expr(u, result); }
            collect_referenced_structs_in_stmt(body, result);
        }
        CStmt::Return(Some(e)) => collect_referenced_structs_in_expr(e, result),
        CStmt::Labeled(label, body) => {
            if let crate::decompile::passes::c_pass::types::Label::Case(e) = label {
                collect_referenced_structs_in_expr(e, result);
            }
            collect_referenced_structs_in_stmt(body, result);
        }
        CStmt::Decl(decls) => {
            for d in decls { collect_struct_refs(&d.ty, result); }
        }
        CStmt::Sequence(stmts) => {
            for s in stmts { collect_referenced_structs_in_stmt(s, result); }
        }
        _ => {}
    }
}

// TR-3 (FIXPLAN 5.2): select_clight_stmts drops ProgramSelectionState.struct_field_type_idx, so the emitter recomputes field-pointer selection from what survives the solve (SelectedFunction.statements / var_type_candidates+var_decl_idx/var_types) using the shared query.rs helpers that mirror solve.rs policy; running over the SELECTED statements makes the result exactly as precise as the printed program.
fn tr3_field_ptr_selection(
    db: &DecompileDB,
    funcs: &[crate::decompile::passes::clight_select::select::SelectedFunction],
    id_to_name: &HashMap<usize, String>,
) -> HashMap<(String, String), String> {
    use crate::decompile::passes::clight_select::query as csq;

    // name -> ident map mirroring select_clight_stmts' construction (sorted (id, name), first-wins, functions by address) so callee_ident_from_expr resolves identically here and inside the solve.
    let mut name_to_ident: HashMap<String, Ident> = HashMap::new();
    {
        let mut sorted_id_name: Vec<(&usize, &String)> = id_to_name.iter().collect();
        sorted_id_name.sort_by_key(|(id, name)| (**id, (*name).clone()));
        for (id, name) in sorted_id_name {
            let sanitized =
                crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(
                    name,
                );
            name_to_ident.entry(sanitized).or_insert(*id as Ident);
            name_to_ident.entry(name.clone()).or_insert(*id as Ident);
        }
        let mut sorted_funcs: Vec<_> = funcs.iter().collect();
        sorted_funcs.sort_by_key(|f| f.address);
        for func in sorted_funcs {
            name_to_ident
                .entry(func.name.clone())
                .or_insert(func.address as Ident);
        }
    }

    let param_xtypes = csq::build_param_xtypes(db);
    let rtl_to_mreg = csq::build_rtl_to_mreg_at_entry(db);
    let callee_sigs = csq::extract_callee_signatures(db, &param_xtypes, &rtl_to_mreg);

    let mut field_cands: HashMap<(String, String), Vec<String>> = HashMap::new();
    let mut evidence: HashSet<(String, String)> = HashSet::new();
    let mut conflicts: HashSet<(String, String)> = HashSet::new();

    // Address-sorted order for deterministic first-wins candidate merge, matching solve.rs's policy.
    let mut sorted_funcs: Vec<_> = funcs.iter().collect();
    sorted_funcs.sort_by_key(|f| f.address);

    // Phase 1: collect per-function selected register classes, field candidates and positive pointer evidence; register classes are retained for phase 2.
    let mut func_reg_classes: Vec<(HashSet<RTLReg>, HashSet<RTLReg>)> =
        Vec::with_capacity(sorted_funcs.len());
    for func in &sorted_funcs {
        // var_decl_idx indexes var_type_candidates (solver overrides appended as synthetic candidates by build_selected_function_from_program_state); single-candidate registers carry their type in var_types.
        let mut ptr_regs: HashSet<RTLReg> = HashSet::new();
        let mut float_regs: HashSet<RTLReg> = HashSet::new();
        for (reg, cands) in &func.var_type_candidates {
            let idx = func.var_decl_idx.get(reg).copied().unwrap_or(0);
            let sel = cands.get(idx).or_else(|| cands.first());
            if sel.map(|s| s.starts_with("ptr_")).unwrap_or(false) {
                ptr_regs.insert(*reg);
            }
            if sel.map(|s| s.starts_with("float_")).unwrap_or(false) {
                float_regs.insert(*reg);
            }
        }
        for (reg, ty) in &func.var_types {
            if !func.var_type_candidates.contains_key(reg) {
                if ty.starts_with("ptr_") {
                    ptr_regs.insert(*reg);
                } else if ty.starts_with("float_") {
                    float_regs.insert(*reg);
                }
            }
        }

        for (key, cands) in csq::collect_struct_field_type_candidates(func.statements.values()) {
            field_cands.entry(key).or_insert(cands);
        }
        for stmt in func.statements.values() {
            csq::scan_field_ptr_evidence(
                stmt,
                &ptr_regs,
                &callee_sigs,
                &name_to_ident,
                &mut evidence,
            );
        }
        func_reg_classes.push((ptr_regs, float_regs));
    }

    // Fields the pick rule would patch: phase 2's veto must treat loads of these as pointer-valued, since the patch is what makes them pointers in the printed C.
    let patchable: HashSet<(String, String)> = evidence
        .iter()
        .filter(|k| {
            field_cands
                .get(*k)
                .map_or(false, |cands| csq::pick_field_ptr_candidate(cands).is_some())
        })
        .cloned()
        .collect();

    // Phase 2: conflict scan. The veto must include registers that become float or pointer at C level only (float cast/load, load of a field this selection patches, pointer arithmetic over those), because from_relations' usage inference declares them double/void* even when the solver selected integral, causing `field + such_reg` to print as `void * + void *`.
    for (func, (ptr_regs, float_regs)) in sorted_funcs.iter().zip(func_reg_classes.iter_mut()) {
        csq::widen_float_regs_by_defs(func.statements.values(), float_regs);
        csq::widen_ptr_regs_by_defs(func.statements.values(), ptr_regs, &patchable);
        for stmt in func.statements.values() {
            csq::scan_field_ptr_conflicts(
                stmt,
                ptr_regs,
                float_regs,
                &callee_sigs,
                &name_to_ident,
                &mut conflicts,
            );
        }
    }

    // Contested fields (pointer evidence + float/int-arith usage, e.g. layout-merged structs) are not retyped: the patch would shift the type error, while `long` converts both ways. This veto is intentionally one-way conservative relative to solve.rs's pointer-preferring pick; if select.rs ever returns ProgramSelectionState, the veto belongs in infer_select_program.
    let mut selection: HashMap<(String, String), String> = HashMap::new();
    let mut sorted_evidence: Vec<&(String, String)> = evidence.iter().collect();
    sorted_evidence.sort();
    for key in sorted_evidence {
        if conflicts.contains(key) {
            if std::env::var("MANIFOLD_TR3_TRACE").is_ok() {
                eprintln!(
                    "[clight-emit] TR3: field {}.{} contested (float/int-arith conflict), kept scalar",
                    key.0, key.1
                );
            }
            continue;
        }
        if let Some(cands) = field_cands.get(key) {
            if let Some(i) = csq::pick_field_ptr_candidate(cands) {
                selection.insert(key.clone(), cands[i].clone());
            }
        }
    }
    selection
}

// TR-3 final veto over the final C AST: the Clight-level scan cannot see pointerness that exists only in the printed C (from_relations usage-inferred `void *`, inserted casts), and repair_pointer_arith ran against unpatched field types, so a bare field access where a pointer cannot compile must be kept scalar. Cast-wrapped uses like `(long)s->f * 8` compile unchanged and are not vetoed.

/// (struct, field) key of a BARE field access in the final C AST, resolving the base's struct identity from the inserted cast or declared variable type. Paren-transparent; deliberately NOT cast-transparent.
fn cexpr_bare_field_key(
    e: &CExpr,
    locals: &HashMap<String, CType>,
    globals: &HashMap<String, CType>,
) -> Option<(String, String)> {
    fn struct_of_ptr(t: &CType) -> Option<&str> {
        match t {
            CType::Pointer(inner, _) => match inner.as_ref() {
                CType::Struct(n) => Some(n),
                CType::Qualified(q, _) => match q.as_ref() {
                    CType::Struct(n) => Some(n),
                    _ => None,
                },
                _ => None,
            },
            CType::Qualified(inner, _) => struct_of_ptr(inner),
            _ => None,
        }
    }
    match e {
        CExpr::Paren(inner) => cexpr_bare_field_key(inner, locals, globals),
        CExpr::MemberPtr(base, f) => {
            let sname = match base.as_ref() {
                CExpr::Cast(t, _) => struct_of_ptr(t)?.to_string(),
                CExpr::Var(v) => struct_of_ptr(locals.get(v).or_else(|| globals.get(v))?)?
                    .to_string(),
                CExpr::Paren(inner) => match inner.as_ref() {
                    CExpr::Cast(t, _) => struct_of_ptr(t)?.to_string(),
                    _ => return None,
                },
                _ => return None,
            };
            Some((sname, f.clone()))
        }
        CExpr::Member(base, f) => {
            let sname = match base.as_ref() {
                CExpr::Var(v) => match locals.get(v).or_else(|| globals.get(v))? {
                    CType::Struct(n) => n.clone(),
                    _ => return None,
                },
                _ => return None,
            };
            Some((sname, f.clone()))
        }
        _ => None,
    }
}

/// Pointer-likeness in final-C terms: declared pointer locals/globals, casts, address-of, string literals, pointer arithmetic, and accesses of other candidate fields (which become pointers with the patch).
fn cexpr_is_ptr_final(
    e: &CExpr,
    locals: &HashMap<String, CType>,
    globals: &HashMap<String, CType>,
    candidates: &HashSet<(String, String)>,
) -> bool {
    use crate::decompile::passes::c_pass::types::{BinaryOp, UnaryOp};
    if let Some(k) = cexpr_bare_field_key(e, locals, globals) {
        if candidates.contains(&k) {
            return true;
        }
    }
    match e {
        CExpr::Cast(t, _) => t.is_pointer(),
        CExpr::Var(v) => locals
            .get(v)
            .or_else(|| globals.get(v))
            .map_or(false, |t| t.is_pointer()),
        CExpr::Unary(UnaryOp::AddrOf, _) => true,
        CExpr::StringLit(_) => true,
        CExpr::Paren(inner) => cexpr_is_ptr_final(inner, locals, globals, candidates),
        CExpr::Binary(BinaryOp::Add | BinaryOp::Sub, l, r) => {
            cexpr_is_ptr_final(l, locals, globals, candidates)
                || cexpr_is_ptr_final(r, locals, globals, candidates)
        }
        _ => false,
    }
}

fn tu_conflict_walk_expr(
    e: &CExpr,
    locals: &HashMap<String, CType>,
    globals: &HashMap<String, CType>,
    candidates: &HashSet<(String, String)>,
    out: &mut HashSet<(String, String)>,
) {
    use crate::decompile::passes::c_pass::types::{BinaryOp, UnaryOp};
    let key_of = |x: &CExpr| -> Option<(String, String)> {
        cexpr_bare_field_key(x, locals, globals).filter(|k| candidates.contains(k))
    };
    match e {
        CExpr::Binary(op, l, r) => {
            let lk = key_of(l);
            let rk = key_of(r);
            if (lk.is_some() || rk.is_some()) && std::env::var("MANIFOLD_TR3_TRACE2").is_ok() {
                let other = if lk.is_some() { r } else { l };
                eprintln!(
                    "[TR3-TU-DIAG] key={:?} op={:?} other_ptr={} other={:?}",
                    lk.as_ref().or(rk.as_ref()),
                    op,
                    cexpr_is_ptr_final(other, locals, globals, candidates),
                    other
                );
            }
            match op {
                BinaryOp::Add => {
                    // field + field (pointers cannot be added), field + ptr.
                    if lk.is_some() && rk.is_some() {
                        out.extend(lk.clone());
                        out.extend(rk.clone());
                    }
                    if let Some(k) = &lk {
                        if cexpr_is_ptr_final(r, locals, globals, candidates) {
                            out.insert(k.clone());
                        }
                    }
                    if let Some(k) = &rk {
                        if cexpr_is_ptr_final(l, locals, globals, candidates) {
                            out.insert(k.clone());
                        }
                    }
                }
                BinaryOp::Sub => {
                    // int - field: a pointer may only be subtracted from a pointer.
                    if let Some(k) = &rk {
                        if !cexpr_is_ptr_final(l, locals, globals, candidates) {
                            out.insert(k.clone());
                        }
                    }
                }
                BinaryOp::Mul
                | BinaryOp::Div
                | BinaryOp::Mod
                | BinaryOp::BitAnd
                | BinaryOp::BitOr
                | BinaryOp::BitXor
                | BinaryOp::Shl
                | BinaryOp::Shr => {
                    // No multiplicative/bitwise/shift operator accepts a pointer.
                    out.extend(lk);
                    out.extend(rk);
                }
                _ => {}
            }
            tu_conflict_walk_expr(l, locals, globals, candidates, out);
            tu_conflict_walk_expr(r, locals, globals, candidates, out);
        }
        CExpr::Unary(op, inner) => {
            if matches!(op, UnaryOp::Neg | UnaryOp::BitNot | UnaryOp::Deref) {
                // -f / ~f are invalid on pointers; *f is invalid on the void * candidate type.
                out.extend(key_of(inner));
            }
            tu_conflict_walk_expr(inner, locals, globals, candidates, out);
        }
        CExpr::Index(arr, idx) => {
            // f[i] derefs the void * candidate; a[f] indexes by a pointer.
            out.extend(key_of(arr));
            out.extend(key_of(idx));
            tu_conflict_walk_expr(arr, locals, globals, candidates, out);
            tu_conflict_walk_expr(idx, locals, globals, candidates, out);
        }
        CExpr::Assign(_, l, r) => {
            tu_conflict_walk_expr(l, locals, globals, candidates, out);
            tu_conflict_walk_expr(r, locals, globals, candidates, out);
        }
        CExpr::Ternary(c, t, f) => {
            tu_conflict_walk_expr(c, locals, globals, candidates, out);
            tu_conflict_walk_expr(t, locals, globals, candidates, out);
            tu_conflict_walk_expr(f, locals, globals, candidates, out);
        }
        CExpr::Call(f, args) => {
            tu_conflict_walk_expr(f, locals, globals, candidates, out);
            for a in args {
                tu_conflict_walk_expr(a, locals, globals, candidates, out);
            }
        }
        CExpr::Cast(_, inner)
        | CExpr::Paren(inner)
        | CExpr::SizeofExpr(inner)
        | CExpr::Member(inner, _)
        | CExpr::MemberPtr(inner, _) => {
            tu_conflict_walk_expr(inner, locals, globals, candidates, out);
        }
        _ => {}
    }
}

fn tu_conflict_walk_stmt(
    s: &CStmt,
    locals: &HashMap<String, CType>,
    globals: &HashMap<String, CType>,
    candidates: &HashSet<(String, String)>,
    out: &mut HashSet<(String, String)>,
) {
    use crate::decompile::passes::c_pass::types::{CBlockItem, ForInit, Initializer, Label};
    let walk_init = |init: &Initializer, out: &mut HashSet<(String, String)>| {
        fn rec(
            init: &Initializer,
            locals: &HashMap<String, CType>,
            globals: &HashMap<String, CType>,
            candidates: &HashSet<(String, String)>,
            out: &mut HashSet<(String, String)>,
        ) {
            match init {
                Initializer::Expr(e) => tu_conflict_walk_expr(e, locals, globals, candidates, out),
                Initializer::List(items) => {
                    for it in items {
                        rec(&it.init, locals, globals, candidates, out);
                    }
                }
                Initializer::String(_) => {}
            }
        }
        rec(init, locals, globals, candidates, out)
    };
    match s {
        CStmt::Expr(e) => tu_conflict_walk_expr(e, locals, globals, candidates, out),
        CStmt::Return(Some(e)) => tu_conflict_walk_expr(e, locals, globals, candidates, out),
        CStmt::If(c, t, e) => {
            tu_conflict_walk_expr(c, locals, globals, candidates, out);
            tu_conflict_walk_stmt(t, locals, globals, candidates, out);
            if let Some(e) = e {
                tu_conflict_walk_stmt(e, locals, globals, candidates, out);
            }
        }
        CStmt::Switch(e, body) => {
            tu_conflict_walk_expr(e, locals, globals, candidates, out);
            tu_conflict_walk_stmt(body, locals, globals, candidates, out);
        }
        CStmt::While(c, body) => {
            tu_conflict_walk_expr(c, locals, globals, candidates, out);
            tu_conflict_walk_stmt(body, locals, globals, candidates, out);
        }
        CStmt::DoWhile(body, c) => {
            tu_conflict_walk_stmt(body, locals, globals, candidates, out);
            tu_conflict_walk_expr(c, locals, globals, candidates, out);
        }
        CStmt::For(init, cond, update, body) => {
            if let Some(init) = init {
                match init {
                    ForInit::Expr(e) => tu_conflict_walk_expr(e, locals, globals, candidates, out),
                    ForInit::Decl(decls) => {
                        for d in decls {
                            if let Some(i) = &d.init {
                                walk_init(i, out);
                            }
                        }
                    }
                }
            }
            if let Some(c) = cond {
                tu_conflict_walk_expr(c, locals, globals, candidates, out);
            }
            if let Some(u) = update {
                tu_conflict_walk_expr(u, locals, globals, candidates, out);
            }
            tu_conflict_walk_stmt(body, locals, globals, candidates, out);
        }
        CStmt::Labeled(label, body) => {
            if let Label::Case(e) = label {
                tu_conflict_walk_expr(e, locals, globals, candidates, out);
            }
            tu_conflict_walk_stmt(body, locals, globals, candidates, out);
        }
        CStmt::Decl(decls) => {
            for d in decls {
                if let Some(i) = &d.init {
                    walk_init(i, out);
                }
            }
        }
        CStmt::Block(items) => {
            for item in items {
                match item {
                    CBlockItem::Stmt(st) => {
                        tu_conflict_walk_stmt(st, locals, globals, candidates, out)
                    }
                    CBlockItem::Decl(decls) => {
                        for d in decls {
                            if let Some(i) = &d.init {
                                walk_init(i, out);
                            }
                        }
                    }
                }
            }
        }
        CStmt::Sequence(stmts) => {
            for st in stmts {
                tu_conflict_walk_stmt(st, locals, globals, candidates, out);
            }
        }
        _ => {}
    }
}

/// Candidate keys whose bare uses in the final TU cannot compile as pointers.
fn tu_field_ptr_conflicts(
    tu: &crate::decompile::passes::c_pass::types::TranslationUnit,
    candidates: &HashSet<(String, String)>,
) -> HashSet<(String, String)> {
    if std::env::var("MANIFOLD_TR3_TRACE2").is_ok() {
        let _ = std::fs::write(
            "/tmp/w2d_veto_tu.c",
            crate::decompile::passes::c_pass::print::print_translation_unit(tu),
        );
    }
    let mut out: HashSet<(String, String)> = HashSet::new();
    let globals: HashMap<String, CType> = tu
        .decls
        .iter()
        .filter_map(|d| match d {
            TopLevelDecl::VarDecl(v) => Some((v.name.clone(), v.ty.clone())),
            _ => None,
        })
        .collect();
    for decl in &tu.decls {
        if let TopLevelDecl::FuncDef(f) = decl {
            let mut locals: HashMap<String, CType> = HashMap::new();
            for p in &f.params {
                if let Some(n) = &p.name {
                    locals.insert(n.clone(), p.ty.clone());
                }
            }
            for v in &f.local_vars {
                locals.insert(v.name.clone(), v.ty.clone());
            }
            tu_conflict_walk_stmt(&f.body, &locals, &globals, candidates, &mut out);
        }
    }
    if std::env::var("MANIFOLD_TR3_TRACE").is_ok() {
        // Diagnostic: 0 hits means key extraction misses the real AST shape.
        let mut hits = 0usize;
        fn count_expr(
            e: &CExpr,
            locals: &HashMap<String, CType>,
            globals: &HashMap<String, CType>,
            candidates: &HashSet<(String, String)>,
            hits: &mut usize,
        ) {
            if cexpr_bare_field_key(e, locals, globals)
                .map_or(false, |k| candidates.contains(&k))
            {
                *hits += 1;
            }
            match e {
                CExpr::Binary(_, l, r) | CExpr::Assign(_, l, r) => {
                    count_expr(l, locals, globals, candidates, hits);
                    count_expr(r, locals, globals, candidates, hits);
                }
                CExpr::Unary(_, i)
                | CExpr::Cast(_, i)
                | CExpr::Paren(i)
                | CExpr::Member(i, _)
                | CExpr::MemberPtr(i, _)
                | CExpr::SizeofExpr(i) => count_expr(i, locals, globals, candidates, hits),
                CExpr::Index(a, b) => {
                    count_expr(a, locals, globals, candidates, hits);
                    count_expr(b, locals, globals, candidates, hits);
                }
                CExpr::Call(f, args) => {
                    count_expr(f, locals, globals, candidates, hits);
                    for a in args {
                        count_expr(a, locals, globals, candidates, hits);
                    }
                }
                CExpr::Ternary(c, t, f) => {
                    count_expr(c, locals, globals, candidates, hits);
                    count_expr(t, locals, globals, candidates, hits);
                    count_expr(f, locals, globals, candidates, hits);
                }
                _ => {}
            }
        }
        fn count_stmt(
            s: &CStmt,
            locals: &HashMap<String, CType>,
            globals: &HashMap<String, CType>,
            candidates: &HashSet<(String, String)>,
            hits: &mut usize,
        ) {
            use crate::decompile::passes::c_pass::types::CBlockItem;
            match s {
                CStmt::Expr(e) | CStmt::Return(Some(e)) => {
                    count_expr(e, locals, globals, candidates, hits)
                }
                CStmt::If(c, t, e) => {
                    count_expr(c, locals, globals, candidates, hits);
                    count_stmt(t, locals, globals, candidates, hits);
                    if let Some(e) = e {
                        count_stmt(e, locals, globals, candidates, hits);
                    }
                }
                CStmt::Switch(e, b) | CStmt::While(e, b) | CStmt::DoWhile(b, e) => {
                    count_expr(e, locals, globals, candidates, hits);
                    count_stmt(b, locals, globals, candidates, hits);
                }
                CStmt::Labeled(_, b) => count_stmt(b, locals, globals, candidates, hits),
                CStmt::Block(items) => {
                    for it in items {
                        if let CBlockItem::Stmt(st) = it {
                            count_stmt(st, locals, globals, candidates, hits);
                        }
                    }
                }
                CStmt::Sequence(ss) => {
                    for st in ss {
                        count_stmt(st, locals, globals, candidates, hits);
                    }
                }
                _ => {}
            }
        }
        for decl in &tu.decls {
            if let TopLevelDecl::FuncDef(f) = decl {
                let mut locals: HashMap<String, CType> = HashMap::new();
                for p in &f.params {
                    if let Some(n) = &p.name {
                        locals.insert(n.clone(), p.ty.clone());
                    }
                }
                for v in &f.local_vars {
                    locals.insert(v.name.clone(), v.ty.clone());
                }
                count_stmt(&f.body, &locals, &globals, candidates, &mut hits);
            }
        }
        eprintln!(
            "[clight-emit] TR3 TU-veto diag: {} bare candidate-field uses keyed, {} conflicts",
            hits,
            out.len()
        );
    }
    out
}

// Shared read set for the select/emit split; the full set keeps both halves ordered after their producers, with clight_selected_functions the typed-tree handoff.
const CLIGHT_EMIT_INPUTS: &[&str] = &[
    "clight_selected_functions",
    "emit_clight_stmt",
    "emit_function",
    "emit_function_param",
    "emit_function_return_type",
    "emit_next",
    "emit_var_type_candidate",
    "emit_loop_body",
    "emit_switch_chain",
    "emit_struct_fields",
    "primary_exit_node",
    "loop_exit_branch",
    "trim_step",
    "known_extern_signature",
    "ident_to_symbol",
    "is_external_function",
    "clight_succ",
    "string_data",
    "instr_in_function",
    "emit_address_as_offset",
    "symbol_size",
    "interior_element_size",
    "is_global_array",
    "global_var_ref",
    "global_load_chunk",
    "emit_canonical_struct_id",
    "global_struct_catalog",
    "func_stacksz",
    "symbols",
    "reg_to_struct_id",
    "call_target_func",
    "call_arg_mapping",
];

const CLIGHT_EMIT_EXTRA_READS: &[&str] = &[
    "direct_call",
    "dwarf_func_param_name",
    "emit_break_stmt",
    "emit_function_param_count",
    "emit_function_param_is_pointer",
    "emit_function_param_type",
    "emit_function_return",
    "emit_function_return_type_xtype",
    "emit_function_void",
    "emit_global_is_char_ptr",
    "emit_global_is_ptr",
    "emit_global_struct_fields",
    "emit_goto_target",
    "emit_ifbody_false",
    "emit_ifbody_true",
    "emit_join_point",
    "emit_loop_exit",
    "emit_scond_no_join",
    "emit_sseq",
    "emit_struct_def",
    "emit_struct_field",
    "emit_var_is_struct",
    "func_param_struct_type",
    "known_global_type",
    "plt_entry",
    "reg_rtl",
    "resolved_extern_signature",
    "rtl_reg_used_in_func",
    "struct_id_to_canonical",
    "unknown_extern",
];

// Front half of codegen: CEGAR selection + tree assembly, kept separate so goto-reduction can rewrite the typed trees before emission with types frozen.
pub struct ClightSelectPass;

impl IRPass for ClightSelectPass {
    fn name(&self) -> &'static str {
        "clight_select"
    }

    fn run(&self, db: &mut DecompileDB) {
        let t = std::time::Instant::now();
        match crate::decompile::passes::clight_select::select::select_clight_stmts(db) {
            Ok(funcs) => {
                eprintln!(
                    "[clight-select] select_clight_stmts: {:?} ({} funcs)",
                    t.elapsed(),
                    funcs.len()
                );
                db.clight_selected_functions = funcs;
            }
            Err(e) => {
                log::warn!("ClightSelectPass: failed to select statements: {}", e);
                db.clight_selected_functions = Vec::new();
            }
        }
    }

    fn inputs(&self) -> &'static [&'static str] {
        CLIGHT_EMIT_INPUTS
    }

    fn outputs(&self) -> &'static [&'static str] {
        &["clight_selected_functions"]
    }

    fn extra_reads(&self) -> &'static [&'static str] {
        CLIGHT_EMIT_EXTRA_READS
    }
}

pub struct ClightEmitPass;

impl IRPass for ClightEmitPass {
    fn name(&self) -> &'static str {
        "ClightEmit"
    }

    fn run(&self, db: &mut DecompileDB) {
        let binary_path = db
            .binary_path
            .clone()
            .expect("binary_path must be set before ClightEmitPass");

        // Take the typed per-function trees produced by ClightSelectPass.
        let selected_functions = std::mem::take(&mut db.clight_selected_functions);
        eprintln!("[clight-emit] selected functions: {}", selected_functions.len());

        let mut id_to_name: HashMap<usize, String> = HashMap::new();
        // ident_to_symbol iteration order is non-deterministic; when several symbols share an id, prefer the shortest name with a lex tiebreak so the choice is stable.
        for (id, name) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
            let name_str = name.to_string();
            id_to_name
                .entry(*id)
                .and_modify(|existing| {
                    let take = name_str.len() < existing.len()
                        || (name_str.len() == existing.len() && name_str.as_str() < existing.as_str());
                    if take {
                        *existing = name_str.clone();
                    }
                })
                .or_insert_with(|| name_str);
        }
        // For symbol aliases at one address, deterministically keep the lex-smallest name.
        let mut sym_tuples: Vec<(Address, Symbol)> = db
            .rel_iter::<(Address, Symbol, Symbol)>("symbols")
            .map(|(a, n, _)| (*a, *n))
            .collect();
        sym_tuples.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
        for (addr, name) in sym_tuples {
            let id = addr as usize;
            // Keep the lex-smallest name across aliases rather than relying on last-write.
            id_to_name
                .entry(id)
                .and_modify(|existing| {
                    let candidate = name.to_string();
                    if candidate.as_str() < existing.as_str() {
                        *existing = candidate;
                    }
                })
                .or_insert_with(|| name.to_string());
        }
        for func in &selected_functions {
            id_to_name
                .entry(func.address as usize)
                .or_insert_with(|| func.name.clone());
        }

        let globals = match crate::decompile::passes::clight_select::query::extract_globals(db, &binary_path) {
            Ok(g) => g,
            Err(e) => {
                log::warn!("ClightEmitPass: failed to extract globals: {}", e);
                return;
            }
        };
        for g in &globals {
            id_to_name.entry(g.id).or_insert_with(|| g.name.clone());
        }

        // Resolve auto-gen L_XXXX labels from linker-fragmented funcs (multiple func_stacksz entries); rename only those fragments to their containing function. Disassembler-created internal jump targets stay so internal gotos don't collide.
        {
            let is_generated_label = |n: &str| -> bool {
                n.strip_prefix("L_")
                    .map_or(false, |h| !h.is_empty() && h.chars().all(|c| c.is_ascii_hexdigit()))
            };

            let mut raw: Vec<(u64, u64, String)> = db
                .rel_iter::<(Address, Address, Symbol, u64)>("func_stacksz")
                .map(|(s, e, n, _)| (*s, *e, n.to_string()))
                .collect();
            raw.sort_by_key(|(s, _, _)| *s);

            // Map of absorbed-fragment address -> absorbing function name; only these are renamed below.
            let mut absorbed_fragment: HashMap<u64, String> = HashMap::new();
            let mut func_ranges: Vec<(u64, u64, String)> = Vec::new();
            for (start, end, name) in raw {
                if is_generated_label(&name) {
                    if let Some(last) = func_ranges.last_mut() {
                        if start == last.1 {
                            last.1 = end;
                            absorbed_fragment.insert(start, last.2.clone());
                            continue;
                        }
                    }
                }
                func_ranges.push((start, end, name));
            }

            for (_id, name) in id_to_name.iter_mut() {
                if !is_generated_label(name) {
                    continue;
                }
                let addr = match u64::from_str_radix(&name[2..], 16) {
                    Ok(a) => a,
                    Err(_) => continue,
                };
                if let Some(func_name) = absorbed_fragment.get(&addr) {
                    *name = func_name.clone();
                }
            }
        }

        {
            // Both relations are multi-valued per ident; keep the smallest value explicitly to avoid non-deterministic last-wins from Ascent iteration order.
            let mut interior_elem_sizes: HashMap<usize, usize> = HashMap::new();
            for (ident, elem_size) in db.rel_iter::<(Ident, usize)>("interior_element_size") {
                interior_elem_sizes
                    .entry(*ident)
                    .and_modify(|e| *e = (*e).min(*elem_size))
                    .or_insert(*elem_size);
            }
            let mut array_elem_sizes: HashMap<usize, usize> = HashMap::new();
            for (ident, elem_size, _count) in db.rel_iter::<(Ident, usize, usize)>("is_global_array") {
                array_elem_sizes
                    .entry(*ident)
                    .and_modify(|e| *e = (*e).min(*elem_size))
                    .or_insert(*elem_size);
            }
            // symbol_size may carry several addresses per name (e.g. local statics sharing a name); resolve by min address for determinism.
            let mut symbol_addr_by_name: HashMap<&str, usize> = HashMap::new();
            for (addr, _, name) in db.rel_iter::<(Address, usize, Symbol)>("symbol_size") {
                symbol_addr_by_name
                    .entry(*name)
                    .and_modify(|e| *e = (*e).min(*addr as usize))
                    .or_insert(*addr as usize);
            }

            // SR-1 (FIXPLAN 4.5): interior idents of a recovered-struct global must not render as `(g + N)` (struct + int is invalid); name them `g.ofs_N` when the layout has a field at that offset, otherwise fall back to `(g + N)` byte-offset form.
            let struct_decl_field_offsets: HashMap<usize, std::collections::BTreeSet<i64>> = {
                let declared_global_ids: HashSet<usize> = globals
                    .iter()
                    .filter(|g| !g.is_string && g.scalar_value.is_none())
                    .map(|g| g.id)
                    .collect();
                let known_typed_names: HashSet<String> = db
                    .rel_iter::<(Symbol, XType)>("known_global_type")
                    .map(|(name, _)| {
                        crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(name)
                    })
                    .collect();
                let catalog_ids: HashSet<usize> = db
                    .rel_iter::<(u64, usize, usize, usize)>("global_struct_catalog")
                    .map(|(_, id, _, _)| *id)
                    .collect();
                // Min-sid per ident mirrors from_relations' winner; merge field offsets of every row carrying that sid.
                let mut chosen_sid: HashMap<usize, usize> = HashMap::new();
                for (ident, sid, _fields) in db
                    .rel_iter::<(Ident, usize, Arc<Vec<(i64, Ident, MemoryChunk)>>)>("emit_global_struct_fields")
                {
                    if !catalog_ids.contains(sid) || !declared_global_ids.contains(ident) {
                        continue;
                    }
                    chosen_sid
                        .entry(*ident)
                        .and_modify(|e| {
                            if *sid < *e {
                                *e = *sid;
                            }
                        })
                        .or_insert(*sid);
                }
                let mut offsets: HashMap<usize, std::collections::BTreeSet<i64>> = HashMap::new();
                for (ident, sid, fields) in db
                    .rel_iter::<(Ident, usize, Arc<Vec<(i64, Ident, MemoryChunk)>>)>("emit_global_struct_fields")
                {
                    if chosen_sid.get(ident) != Some(sid) {
                        continue;
                    }
                    let by_name = id_to_name.get(ident);
                    let known_typed = by_name
                        .map(|n| {
                            known_typed_names.contains(
                                &crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(n),
                            )
                        })
                        .unwrap_or(false);
                    if known_typed {
                        continue;
                    }
                    let entry = offsets.entry(*ident).or_default();
                    for (ofs, _, _) in fields.iter() {
                        entry.insert(*ofs);
                    }
                }
                offsets
            };

            for (interior_ident, base_name, offset) in db.rel_iter::<(Ident, Symbol, i64)>("emit_address_as_offset") {
                let maybe_base_ident = symbol_addr_by_name.get(*base_name).copied();

                let rewritten_name = if let Some(base_ident) = maybe_base_ident {
                    let elem_size_opt = interior_elem_sizes
                        .get(&base_ident)
                        .or_else(|| array_elem_sizes.get(&base_ident));
                    if let Some(&elem_size) = elem_size_opt {
                        if elem_size > 0 && *offset >= 0 && (*offset as usize) % elem_size == 0 {
                            let index = (*offset as usize) / elem_size;
                            format!("{}[{}]", base_name, index)
                        } else {
                            format!("({} + {})", base_name, offset)
                        }
                    } else if let Some(field_offsets) = struct_decl_field_offsets.get(&base_ident) {
                        // NOTE: these synthetic names are sanitized into plain identifiers downstream (sanitize_c_symbol_name), so they never parse as expressions; the member form yields a readable name ("g_ofs_4") instead of the opaque "(g + 4)".
                        if *offset == 0 {
                            base_name.to_string()
                        } else if field_offsets.contains(offset) {
                            // Matches the recovered definition's field naming (make_field_ident(offset) -> "ofs_N").
                            format!("{}.ofs_{}", base_name, offset)
                        } else {
                            format!("({} + {})", base_name, offset)
                        }
                    } else if *offset == 0 {
                        base_name.to_string()
                    } else {
                        format!("({} + {})", base_name, offset)
                    }
                } else {
                    format!("({} + {})", base_name, offset)
                };
                id_to_name.insert(*interior_ident, rewritten_name);
            }
        }

        let edges: Vec<(Node, Node)> = db
            .rel_iter::<(Node, Node)>("clight_succ")
            .map(|(src, dst)| (*src, *dst))
            .collect();
        let t = std::time::Instant::now();
        let raw_translation_unit = crate::decompile::passes::c_pass::convert::build_cast_from_relations(
            db,
            &selected_functions,
            &globals,
            &id_to_name,
            &edges,
        );
        eprintln!("[clight-emit] build_cast_from_relations (raw TU): {:?}", t.elapsed());

        let mut string_map = build_string_literal_map(db);
        for g in &globals {
            if g.is_string && !g.content.is_empty() {
                let s = String::from_utf8_lossy(&g.content)
                    .trim_end_matches('\0')
                    .to_string();
                string_map.entry(g.name.clone()).or_insert(s);
            }
        }

        // Build inline constant map from resolved .rodata scalar values
        let rodata_const_map: HashMap<String, CExpr> = globals
            .iter()
            .filter_map(|g| {
                use crate::decompile::passes::clight_select::query::ScalarConstant;
                let expr = match g.scalar_value.as_ref()? {
                    ScalarConstant::Float32(v) => CExpr::FloatLit(FloatLiteral {
                        value: *v as f64,
                        suffix: FloatLiteralSuffix::F,
                    }),
                    ScalarConstant::Float64(v) => CExpr::FloatLit(FloatLiteral {
                        value: *v,
                        suffix: FloatLiteralSuffix::None,
                    }),
                    ScalarConstant::Int32(v) => CExpr::IntLit(IntLiteral {
                        value: *v as i128,
                        suffix: IntLiteralSuffix::None,
                        base: IntLiteralBase::Decimal,
                    }),
                    ScalarConstant::Int64(v) => CExpr::IntLit(IntLiteral {
                        value: *v as i128,
                        suffix: IntLiteralSuffix::L,
                        base: IntLiteralBase::Decimal,
                    }),
                };
                Some((g.name.clone(), expr))
            })
            .collect();
        let struct_layouts = crate::decompile::passes::clight_select::query::extract_struct_layout_map(db);

        let external_funcs: HashSet<u64> =
            db.rel_iter::<(Address,)>("is_external_function").map(|(a,)| *a).collect();

        let internal_functions: Vec<_> = selected_functions
            .iter()
            .filter(|func| {
                !external_funcs.contains(&func.address)
                    && !func.name.starts_with('.')
                    && !db.should_skip_function(func.name.as_str())
            })
            .cloned()
            .collect();

        {
            let internal_addrs: HashSet<u64> =
                internal_functions.iter().map(|f| f.address).collect();
            // instr_in_function is multi-valued (shared PLT nodes); use HashMap<_, HashSet>.
            let mut node_to_funcs: HashMap<u64, HashSet<u64>> = HashMap::new();
            for (n, f) in db.rel_iter::<(Node, Address)>("instr_in_function") {
                node_to_funcs.entry(*n).or_default().insert(*f);
            }
            let called_addrs: HashSet<u64> = db
                .rel_iter::<(Address, Address)>("direct_call")
                .filter(|(caller, _)| {
                    node_to_funcs
                        .get(caller)
                        .map_or(false, |funcs| funcs.iter().any(|f| internal_addrs.contains(f)))
                })
                .map(|(_, callee)| *callee)
                .collect();
            for func in &selected_functions {
                if db.should_skip_function(func.name.as_str())
                    && called_addrs.contains(&func.address)
                {
                    let has_sig = db
                        .rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("known_extern_signature")
                        .any(|(n, ..)| *n == func.name.as_str());
                    if !has_sig {
                        db.rel_push("unknown_extern", (crate::util::leak::<String, str>(func.name.clone()),));
                    }
                }
            }
        }

        let mut ctx = crate::decompile::passes::c_pass::convert::from_relations::ConversionContext::new(
            id_to_name.clone(),
        );

        let mut var_types_for_emission: HashMap<String, CType> = HashMap::new();
        let mut all_statements: Vec<(Node, CStmt)> = Vec::new();
        let mut all_edges: Vec<(Node, Node)> = Vec::new();
        let mut node_to_func_addr: HashMap<Node, u64> = HashMap::new();

        for func in &internal_functions {
            let mut statements = Vec::new();
            let mut func_edges = Vec::new();

            for (reg, pty) in func.param_regs.iter().zip(func.param_types.iter()) {
                let name = param_name_for_reg(*reg);
                let ty = match pty {
                    crate::x86::types::ParamType::StructPointer(_)
                    | crate::x86::types::ParamType::Typed(_) => {
                        convert_param_type_from_param(pty)
                    }
                    _ => {
                        if let Some(type_str) = func.var_types.get(reg) {
                            xtype_string_to_ctype(type_str)
                        } else {
                            convert_param_type_from_param(pty)
                        }
                    }
                };
                var_types_for_emission.entry(name).or_insert(ty);
            }

            for (var_name, type_str) in &func.var_types {
                let ty = xtype_string_to_ctype(type_str);
                let name = format!("var_{}", var_name);
                var_types_for_emission.entry(name).or_insert(ty);
            }

            for (reg, struct_id) in &func.reg_struct_ids {
                let name = format!("var_{}", reg);
                let struct_type_name = format!("struct_{:x}", struct_id);
                let ptr_type = CType::Pointer(
                    Box::new(CType::Struct(struct_type_name)),
                    TypeQualifiers::none(),
                );
                var_types_for_emission.insert(name, ptr_type);
            }

            {
                let mut sorted_stmt_nodes: Vec<Node> = func.statements.keys().copied().collect();
                sorted_stmt_nodes.sort();
                for node in sorted_stmt_nodes {
                    let clight_stmt = &func.statements[&node];
                    let cstmt = crate::decompile::passes::c_pass::convert::from_relations::convert_stmt(
                        clight_stmt,
                        &mut ctx,
                    );
                    let cstmt = crate::decompile::passes::c_pass::helpers::map_stmt_exprs(&cstmt, &|e| {
                        inline_string_literals(e, &string_map)
                    });
                    let cstmt = crate::decompile::passes::c_pass::helpers::map_stmt_exprs_total(&cstmt, &|e| {
                        crate::decompile::passes::c_pass::helpers::inline_rodata_constants_preserving_addrof(e, &rodata_const_map)
                    });
                    let cstmt = crate::decompile::passes::c_pass::convert::from_relations::narrow_varargs_in_stmt(&cstmt);
                    statements.push((node, cstmt));
                }
            }

            // func.successors is a HashMap; iterating directly leaks non-deterministic ordering into func_edges -> all_edges -> remapped_edges. order_nodes_dfs sorts adjacency lists, but it relies on the *set* of (src, dst) pairs being the same, which it is, so the impact is mainly on diagnostic stability. Sort by source for a stable iteration order anyway.
            let mut succ_nodes: Vec<Node> = func.successors.keys().copied().collect();
            succ_nodes.sort();
            for node in succ_nodes {
                if let Some(succs) = func.successors.get(&node) {
                    for succ in succs {
                        func_edges.push((node, *succ));
                    }
                }
            }
            {
                let label_to_node: HashMap<String, Node> = statements
                    .iter()
                    .filter_map(|(n, s)| extract_named_label(s).map(|name| (name, *n)))
                    .collect();
                let node_set: HashSet<Node> =
                    statements.iter().map(|(n, _)| *n).collect();
                let mut extra_edges = Vec::new();
                for (node, stmt) in &statements {
                    let mut targets = Vec::new();
                    collect_goto_label_targets(stmt, &mut targets);
                    for label in &targets {
                        if let Some(&target) = label_to_node.get(label.as_str()) {
                            if node_set.contains(&target) {
                                extra_edges.push((*node, target));
                            }
                        }
                    }
                }
                func_edges.extend(extra_edges);
            }

            {
                let mut sorted_nodes: Vec<Node> =
                    statements.iter().map(|(n, _)| *n).collect();
                sorted_nodes.sort();
                let has_outgoing: HashSet<Node> =
                    func_edges.iter().map(|(f, _)| *f).collect();
                let stmt_map: HashMap<Node, &CStmt> =
                    statements.iter().map(|(n, s)| (*n, s)).collect();
                let mut extra_edges = Vec::new();
                for window in sorted_nodes.windows(2) {
                    let curr = window[0];
                    let next_node = window[1];
                    if has_outgoing.contains(&curr) {
                        continue;
                    }
                    if let Some(stmt) = stmt_map.get(&curr) {
                        if !is_terminal_cstmt(stmt) {
                            extra_edges.push((curr, next_node));
                        }
                    }
                }
                func_edges.extend(extra_edges);
            }

            for (node, _) in &statements {
                node_to_func_addr.insert(*node, func.address);
            }

            // (Resolved TODO: a late "CsharpminorStmt structuring pass" here is superseded - late control-flow structuring over the final statement stream is done by the post-select ForLoopPass wired in the elevator (always on; the PhoenixStructurePass alternative was adjudicated out and removed 2026-06-10, see UNRESOLVED O-13); upstream structural recovery belongs in structuring_pass / clight_select, not at emission.)
            all_statements.extend(statements);
            all_edges.extend(func_edges);
        }

        db.cast_selected_functions = internal_functions;
        db.cast_globals = globals;
        db.cast_id_to_name = id_to_name;
        db.cast_struct_layouts = struct_layouts;
        db.cast_var_types_for_emission = var_types_for_emission.clone();
        db.cast_raw_translation_unit = Some(raw_translation_unit);

        let t = std::time::Instant::now();
        let mut struct_defs = crate::decompile::passes::clight_select::query::extract_struct_definitions(db);
        eprintln!("[clight-emit] extract_struct_definitions: {:?} ({} structs)", t.elapsed(), struct_defs.len());

        let stmt_map: HashMap<Node, CStmt> = all_statements.into_iter().collect();

        log::info!(
            "Building translation unit from {} statements",
            stmt_map.len()
        );

        let t = std::time::Instant::now();
        let mut tu = crate::decompile::passes::c_pass::convert::build_translation_unit_from_stmt_map_with_types(
            db,
            &db.cast_selected_functions,
            &db.cast_globals,
            &db.cast_id_to_name,
            &stmt_map,
            &all_edges,
            &db.cast_var_types_for_emission,
            &node_to_func_addr,
        );
        eprintln!("[clight-emit] build_translation_unit (optimized TU): {:?}", t.elapsed());

        // SR-1 (FIXPLAN 4.5): rewrite function bodies to be consistent with the recovered-global declarations (struct/array VarDecls produced only by from_relations, not convert_xtype). Must run before opaqueness/layout analyses.
        {
            let mut array_globals: HashSet<String> = HashSet::new();
            let mut struct_globals: HashMap<String, String> = HashMap::new();
            let first_field_of: HashMap<&String, &String> = struct_defs
                .iter()
                .filter_map(|ex| {
                    let name = ex.definition.name.as_ref()?;
                    let first = ex.definition.fields.first()?.name.as_ref()?;
                    Some((name, first))
                })
                .collect();
            for decl in &tu.decls {
                if let TopLevelDecl::VarDecl(v) = decl {
                    match &v.ty {
                        CType::Array(..) => {
                            array_globals.insert(v.name.clone());
                        }
                        CType::Struct(sname) => {
                            if let Some(f) = first_field_of.get(sname) {
                                struct_globals.insert(v.name.clone(), (*f).clone());
                            }
                        }
                        _ => {}
                    }
                }
            }
            if !array_globals.is_empty() || !struct_globals.is_empty() {
                eprintln!(
                    "[clight-emit] SR-1 recovered-global decls: {} struct, {} array",
                    struct_globals.len(),
                    array_globals.len()
                );
                for decl in &mut tu.decls {
                    if let TopLevelDecl::FuncDef(f) = decl {
                        rewrite_recovered_global_stmt(&mut f.body, &array_globals, &struct_globals);
                        for v in &mut f.local_vars {
                            if let Some(init) = &mut v.init {
                                rewrite_recovered_global_init(init, &array_globals, &struct_globals);
                            }
                        }
                    }
                }
            }
        }

        // TR-3 (FIXPLAN 5.2): apply field-pointer selection to extracted definitions BEFORE field_types/layout evidence reads them. Runs AFTER the optimized TU and SR-1 rewrite so the final C is available for the last veto -- the Clight-level scan cannot see pointerness that exists only in from_relations' usage-inferred decls, and repair_pointer_arith already ran against unpatched types.
        {
            let t = std::time::Instant::now();
            let mut tr3_selection = tr3_field_ptr_selection(
                db,
                &db.cast_selected_functions,
                &db.cast_id_to_name,
            );
            if !tr3_selection.is_empty() {
                let cand_keys: HashSet<(String, String)> =
                    tr3_selection.keys().cloned().collect();
                let tu_conflicts = tu_field_ptr_conflicts(&tu, &cand_keys);
                if !tu_conflicts.is_empty() && std::env::var("MANIFOLD_TR3_TRACE").is_ok() {
                    let mut sorted: Vec<_> = tu_conflicts.iter().collect();
                    sorted.sort();
                    for k in sorted {
                        eprintln!(
                            "[clight-emit] TR3: field {}.{} contested (C-level ptr-arith), kept scalar",
                            k.0, k.1
                        );
                    }
                }
                tr3_selection.retain(|k, _| !tu_conflicts.contains(k));
            }
            let patched = crate::decompile::passes::clight_select::query::apply_struct_field_type_selection(
                &mut struct_defs,
                &tr3_selection,
            );
            if patched > 0 {
                eprintln!(
                    "[clight-emit] TR3 field-type selection: {} field(s) -> pointer ({:?})",
                    patched,
                    t.elapsed()
                );
            }
        }

        // Identify opaque libc structs (FILE, DIR) via C AST scan and RTL-level analysis.
        let t = std::time::Instant::now();
        let mut opaque_map = identify_opaque_libc_structs_from_tu(&tu);
        eprintln!("[clight-emit] identify_opaque_libc_structs: {:?} ({} found)", t.elapsed(), opaque_map.len());

        // Supplement with RTL-level analysis: struct IDs flowing through opaque-pointer call args.
        {
            let opaque_params_flat = known_opaque_struct_params();
            let reg_to_sid: HashMap<RTLReg, usize> = db
                .rel_iter::<(Address, RTLReg, usize)>("reg_to_struct_id")
                .map(|&(_, reg, sid)| (reg, sid))
                .collect();
            let func_names: HashMap<Address, String> = db
                .rel_iter::<(Address, Symbol, Node)>("emit_function")
                .map(|(addr, name, _)| (*addr, name.to_string()))
                .collect();
            let call_targets: HashMap<Node, String> = db
                .rel_iter::<(Node, Address)>("call_target_func")
                .filter_map(|(node, addr)| func_names.get(addr).map(|name| (*node, name.clone())))
                .collect();
            for &(call_node, pos, reg) in db.rel_iter::<(Node, usize, RTLReg)>("call_arg_mapping") {
                if let Some(&sid) = reg_to_sid.get(&reg) {
                    if let Some(callee_name) = call_targets.get(&call_node) {
                        if let Some(param_info) = opaque_params_flat.get(callee_name.as_str()) {
                            for &(expected_pos, typedef_name) in param_info {
                                if pos == expected_pos {
                                    let struct_name = format!("struct_{:x}", sid);
                                    opaque_map.entry(struct_name).or_insert_with(|| typedef_name.to_string());
                                }
                            }
                        }
                    }
                }
            }
        }

        // IL-3/IL-4 evidence: which tags the final TU names at all, and which require a complete layout. The name table above is now only a naming fallback.
        let t = std::time::Instant::now();
        let mut structs_referenced_in_code = collect_all_referenced_structs(&tu);
        let field_types: HashMap<String, HashMap<String, CType>> = struct_defs
            .iter()
            .filter_map(|ex| {
                let name = ex.definition.name.clone()?;
                let fields: HashMap<String, CType> = ex
                    .definition
                    .fields
                    .iter()
                    .filter_map(|f| f.name.clone().map(|n| (n, f.ty.clone())))
                    .collect();
                Some((name, fields))
            })
            .collect();
        let layout_ev = collect_struct_layout_evidence(&tu, &field_types);
        let analysis_complete = !layout_ev.incomplete;
        let mut needs_layout = layout_ev.needs_layout;
        // Requiring a layout implies referencing the tag.
        structs_referenced_in_code.extend(needs_layout.iter().cloned());
        if !analysis_complete {
            // Some layout-relevant base could not be typed: conservatively treat every struct as needing its layout.
            eprintln!(
                "[clight-emit] struct layout evidence incomplete; sample untypeable sites: {:?}",
                layout_ev.incomplete_samples
            );
        }

        // Closure: a full definition's by-value embedded fields need their layout too (incomplete embedded field is a compile error), and pointer fields keep their tag referenced. The emit predicate mirrors the final loop; insertions are monotone so this is a deterministic fixpoint.
        loop {
            let mut changed = false;
            for extracted in &struct_defs {
                let Some(name) = extracted.definition.name.as_ref() else { continue };
                let tabled_opaque = opaque_map.contains_key(name)
                    && (!analysis_complete || !needs_layout.contains(name));
                let emits_full = structs_referenced_in_code.contains(name)
                    && !tabled_opaque
                    && (!analysis_complete || needs_layout.contains(name));
                if !emits_full {
                    continue;
                }
                for field in &extracted.definition.fields {
                    changed |= note_emitted_field_type(
                        &field.ty,
                        false,
                        &mut needs_layout,
                        &mut structs_referenced_in_code,
                    );
                }
            }
            if !changed {
                break;
            }
        }

        // Suppression map: name-table opaque -> typedef name, unreferenced -> void.
        let mut suppressed_structs: HashMap<String, String> = HashMap::new();
        // RTL-supplement tabled tags with no extracted definition keep their typedef rewrite, gated on layout evidence.
        {
            let extracted_names: HashSet<&String> = struct_defs
                .iter()
                .filter_map(|e| e.definition.name.as_ref())
                .collect();
            for (name, typedef_name) in &opaque_map {
                if !extracted_names.contains(name)
                    && (!analysis_complete || !needs_layout.contains(name))
                {
                    suppressed_structs.insert(name.clone(), typedef_name.clone());
                }
            }
        }

        let (mut n_full, mut n_opaque, mut n_tabled, mut n_voided) = (0usize, 0usize, 0usize, 0usize);
        for extracted in &struct_defs {
            if let Some(name) = &extracted.definition.name {
                if let Some(typedef_name) = opaque_map.get(name) {
                    if !analysis_complete || !needs_layout.contains(name) {
                        // Known libc opaque type: rewrite to the documented typedef (FILE/DIR), definition skipped.
                        suppressed_structs.insert(name.clone(), typedef_name.clone());
                        n_tabled += 1;
                        continue;
                    }
                    // Tabled, but fields are accessed: keep the full definition (rewriting to FILE would break member accesses); fall through.
                }
                if !structs_referenced_in_code.contains(name) {
                    // IL-4: zero usage evidence -- never named, no field accessed.
                    suppressed_structs.insert(name.clone(), "void".to_string());
                    n_voided += 1;
                    continue;
                }
                if analysis_complete && !needs_layout.contains(name) {
                    // IL-3: referenced only behind pointers, never dereferenced -- emit empty-body tag so pointer uses compile while the bogus layout is suppressed.
                    let mut opaque_def = extracted.definition.clone();
                    opaque_def.fields.clear();
                    tu.decls.push(TopLevelDecl::StructDef(opaque_def));
                    n_opaque += 1;
                    continue;
                }
                n_full += 1;
            }
            tu.decls.push(TopLevelDecl::StructDef(extracted.definition.clone()));
        }
        eprintln!(
            "[clight-emit] struct usage evidence: {} full, {} opaque, {} tabled({}), {} voided, analysis_complete={} ({:?})",
            n_full, n_opaque, n_tabled, opaque_map.len(), n_voided, analysis_complete, t.elapsed()
        );

        // Rewrite suppressed structs: opaque -> TypedefName, unreferenced -> Void.
        if !suppressed_structs.is_empty() {
            rewrite_opaque_types_in_tu(&mut tu, &suppressed_structs);
            for ty in db.cast_var_types_for_emission.values_mut() {
                *ty = rewrite_ctype(ty, &suppressed_structs);
            }
        }

        db.cast_optimized_translation_unit = Some(tu);
    }

    fn inputs(&self) -> &'static [&'static str] {
        CLIGHT_EMIT_INPUTS
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "cast_selected_functions",
            "cast_globals",
            "cast_id_to_name",
            "cast_struct_layouts",
            "cast_var_types_for_emission",
            "cast_raw_translation_unit",
            "cast_optimized_translation_unit",
        ]
    }

    fn extra_reads(&self) -> &'static [&'static str] {
        CLIGHT_EMIT_EXTRA_READS
    }
}

