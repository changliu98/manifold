use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::c_pass::helpers::{
    build_string_literal_map, candtype_to_ctype, collect_goto_label_targets,
    convert_param_type_from_param, inline_string_literals, is_terminal_cstmt, param_name_for_reg,
    rodata_fp_constant_labels,
};
use crate::decompile::passes::c_pass::types::{CExpr, CStmt, CType, TopLevelDecl, TypeQualifiers};
use crate::decompile::passes::pass::IRPass;
use crate::decompile::passes::rtl_pass::StackAddrOrigin;
use crate::util::exec_order_key;
use crate::x86::op::{Addressing, Operation};
use crate::x86::types::*;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

fn clight_addrof_ident(expr: &ClightExpr) -> Option<Ident> {
    match expr {
        ClightExpr::Ecast(inner, _) => clight_addrof_ident(inner),
        ClightExpr::Eaddrof(inner, _) => match inner.as_ref() {
            ClightExpr::Evar(ident, _) | ClightExpr::Etempvar(ident, _) => Some(*ident),
            _ => None,
        },
        _ => None,
    }
}

fn storage_alias_root(mut ident: Ident, aliases: &HashMap<Ident, Ident>) -> Ident {
    let mut seen = HashSet::new();
    while seen.insert(ident) {
        let Some(next) = aliases.get(&ident).copied() else {
            break;
        };
        if next == ident {
            break;
        }
        ident = next;
    }
    ident
}

fn is_self_address_materialization(
    stmt: &ClightStmt,
    storage_aliases: &HashMap<Ident, Ident>,
) -> bool {
    let ClightStmt::Sset(destination, value) = stmt else {
        return false;
    };
    let Some(owner) = clight_addrof_ident(value) else {
        return false;
    };
    storage_alias_root(*destination, storage_aliases) == storage_alias_root(owner, storage_aliases)
}

fn uses_storage_alias(stmt: &ClightStmt, storage_aliases: &HashMap<Ident, Ident>) -> bool {
    let ClightStmt::Sset(destination, value) = stmt else {
        return false;
    };
    storage_aliases.contains_key(destination)
        || clight_addrof_ident(value).is_some_and(|owner| storage_aliases.contains_key(&owner))
}

/// Append the source-language va_start operation after the recovered SysV
/// va_list field stores.  The local stays a byte buffer so the remaining
/// machine-derived accesses retain their exact offsets; casting its address to
/// __builtin_va_list lets GCC populate the unnamed GP/FP arguments that cannot
/// be named as ordinary C parameters.
fn source_va_start(va_list_local: Ident, last_named: RTLReg) -> CStmt {
    let va_list_ptr = CType::Pointer(
        Box::new(CType::TypedefName("__builtin_va_list".to_string())),
        TypeQualifiers::none(),
    );
    let va_list = CExpr::deref(CExpr::cast(
        va_list_ptr,
        CExpr::var(format!("var_{va_list_local}")),
    ));
    CStmt::Expr(CExpr::call(
        CExpr::var("__builtin_va_start"),
        vec![va_list, CExpr::var(param_name_for_reg(last_named))],
    ))
}

fn append_source_va_start(stmt: CStmt, va_list_local: Ident, last_named: RTLReg) -> CStmt {
    let start = source_va_start(va_list_local, last_named);
    match stmt {
        CStmt::Sequence(mut statements) => {
            statements.push(start);
            CStmt::Sequence(statements)
        }
        other => CStmt::Sequence(vec![other, start]),
    }
}

/// Count selected primitive writes with this exact source-event origin.
/// Compound headers do not confer their origin on unlabeled child statements.
fn count_selected_store_origins(stmt: &ClightStmt, origin: Option<Node>, target: Node) -> usize {
    match stmt {
        ClightStmt::Sassign(..) => usize::from(origin == Some(target)),
        ClightStmt::Slabel(label, inner) => count_selected_store_origins(inner, Some(*label as Node), target),
        ClightStmt::Ssequence(stmts) if stmts.len() == 1 => count_selected_store_origins(&stmts[0], origin, target),
        ClightStmt::Ssequence(stmts) => stmts.iter().map(|s| count_selected_store_origins(s, None, target)).sum(),
        ClightStmt::Sifthenelse(_, a, b) | ClightStmt::Sloop(a, b) =>
            count_selected_store_origins(a, None, target) + count_selected_store_origins(b, None, target),
        ClightStmt::Sswitch(_, cases) => cases.iter().map(|(_, s)| count_selected_store_origins(s, None, target)).sum(),
        _ => 0,
    }
}

fn unwrapped_assigned_var(expr: &CExpr) -> Option<&str> {
    match expr {
        CExpr::Var(name) => Some(name),
        CExpr::Cast(_, inner) | CExpr::Paren(inner) => unwrapped_assigned_var(inner),
        _ => None,
    }
}

fn count_assignments_to(stmt: &CStmt, destination: &str) -> usize {
    match stmt {
        CStmt::Expr(CExpr::Assign(_, lhs, _)) => {
            usize::from(unwrapped_assigned_var(lhs) == Some(destination))
        }
        CStmt::Block(items) => items
            .iter()
            .map(|item| match item {
                crate::decompile::passes::c_pass::types::CBlockItem::Stmt(stmt) => {
                    count_assignments_to(stmt, destination)
                }
                crate::decompile::passes::c_pass::types::CBlockItem::Decl(_) => 0,
            })
            .sum(),
        CStmt::If(_, then_stmt, else_stmt) => {
            count_assignments_to(then_stmt, destination)
                + else_stmt
                    .as_deref()
                    .map_or(0, |stmt| count_assignments_to(stmt, destination))
        }
        CStmt::Switch(_, body)
        | CStmt::While(_, body)
        | CStmt::DoWhile(body, _)
        | CStmt::For(_, _, _, body)
        | CStmt::Labeled(_, body) | CStmt::Effect(_, body)  => count_assignments_to(body, destination),
        CStmt::Sequence(statements) => statements
            .iter()
            .map(|stmt| count_assignments_to(stmt, destination))
            .sum(),
        _ => 0,
    }
}

fn insert_va_start_after_assignment(
    stmt: &mut CStmt,
    destination: &str,
    va_list_local: Ident,
    last_named: RTLReg,
) -> usize {
    if matches!(
        stmt,
        CStmt::Expr(CExpr::Assign(_, lhs, _))
            if unwrapped_assigned_var(lhs) == Some(destination)
    ) {
        let original = std::mem::replace(stmt, CStmt::Empty);
        *stmt = append_source_va_start(original, va_list_local, last_named);
        return 1;
    }
    match stmt {
        CStmt::Block(items) => items
            .iter_mut()
            .map(|item| match item {
                crate::decompile::passes::c_pass::types::CBlockItem::Stmt(stmt) => {
                    insert_va_start_after_assignment(stmt, destination, va_list_local, last_named)
                }
                crate::decompile::passes::c_pass::types::CBlockItem::Decl(_) => 0,
            })
            .sum(),
        CStmt::If(_, then_stmt, else_stmt) => {
            insert_va_start_after_assignment(then_stmt, destination, va_list_local, last_named)
                + else_stmt.as_deref_mut().map_or(0, |stmt| {
                    insert_va_start_after_assignment(stmt, destination, va_list_local, last_named)
                })
        }
        CStmt::Switch(_, body)
        | CStmt::While(_, body)
        | CStmt::DoWhile(body, _)
        | CStmt::For(_, _, _, body)
        | CStmt::Labeled(_, body) | CStmt::Effect(_, body)  => {
            insert_va_start_after_assignment(body, destination, va_list_local, last_named)
        }
        CStmt::Sequence(statements) => statements
            .iter_mut()
            .map(|stmt| {
                insert_va_start_after_assignment(stmt, destination, va_list_local, last_named)
            })
            .sum(),
        _ => 0,
    }
}

/// Known libc functions that take opaque struct pointer parameters; maps function_name -> Vec<(param_position, typedef_name)>.
fn known_opaque_struct_params() -> HashMap<&'static str, Vec<(usize, &'static str)>> {
    let mut m: HashMap<&str, Vec<(usize, &str)>> = HashMap::new();
    // FILE* at position 0
    for &func in &[
        "fclose",
        "fflush",
        "fgetc",
        "fseek",
        "fseeko",
        "ftell",
        "ftello",
        "rewind",
        "feof",
        "ferror",
        "clearerr",
        "fileno",
        "setbuf",
        "setvbuf",
        "fprintf",
        "fscanf",
        "vfprintf",
        "clearerr_unlocked",
        "feof_unlocked",
        "ferror_unlocked",
        "fileno_unlocked",
        "fgetc_unlocked",
        "getc_unlocked",
        "__freading",
        "__fpending",
        "__fwriting",
        "__freadable",
        "__fwritable",
        "__fsetlocking",
        "__overflow",
        "__uflow",
        "fclose_nothrow",
        "fflush_unlocked",
        "rpl_fclose",
        "rpl_fflush",
        "rpl_fseek",
        "rpl_fseeko",
        "rpl_ftell",
        "rpl_ftello",
        "rpl_fopen",
        "rpl_freopen",
    ] {
        m.entry(func).or_default().push((0, "FILE"));
    }
    // FILE* at position 1: int fputc(int, FILE*), int fputs(const char*, FILE*), etc.
    for &func in &[
        "fputc",
        "fputs",
        "fputc_unlocked",
        "fputs_unlocked",
        "putc_unlocked",
    ] {
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
    for &func in &[
        "closedir",
        "readdir",
        "readdir_r",
        "rewinddir",
        "seekdir",
        "telldir",
    ] {
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
                result
                    .entry(name.clone())
                    .or_default()
                    .insert(typedef_name.to_string());
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
            if let Some(e) = e {
                collect_struct_names_from_stmt(e, opaque_params, result);
            }
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
            if let Some(c) = cond {
                collect_struct_names_from_expr(c, opaque_params, result);
            }
            if let Some(u) = update {
                collect_struct_names_from_expr(u, opaque_params, result);
            }
            collect_struct_names_from_stmt(body, opaque_params, result);
        }
        CStmt::Return(Some(e)) => collect_struct_names_from_expr(e, opaque_params, result),
        CStmt::Labeled(_, body) | CStmt::Effect(_, body)  => collect_struct_names_from_stmt(body, opaque_params, result),
        CStmt::Sequence(stmts) => {
            for s in stmts {
                collect_struct_names_from_stmt(s, opaque_params, result);
            }
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

    // (2) Only an EXTERNAL declaration is a genuine libc extern whose opaque-param typedef table applies; a local definition sharing a tabled name keeps its own recovered signature.
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
        CType::Function(ret, params, variadic, unprototyped) => {
            let new_ret = rewrite_ctype(ret, opaque_map);
            let new_params: Vec<CType> = params
                .iter()
                .map(|p| rewrite_ctype(p, opaque_map))
                .collect();
            CType::Function(Box::new(new_ret), new_params, *variadic, *unprototyped)
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
            for a in args {
                rewrite_ctype_in_expr(a, opaque_map);
            }
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
                        for d in decls {
                            d.ty = rewrite_ctype(&d.ty, opaque_map);
                        }
                    }
                }
            }
        }
        CStmt::If(c, t, e) => {
            rewrite_ctype_in_expr(c, opaque_map);
            rewrite_ctype_in_stmt(t, opaque_map);
            if let Some(e) = e {
                rewrite_ctype_in_stmt(e, opaque_map);
            }
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
                        for d in decls {
                            d.ty = rewrite_ctype(&d.ty, opaque_map);
                        }
                    }
                }
            }
            if let Some(c) = cond {
                rewrite_ctype_in_expr(c, opaque_map);
            }
            if let Some(u) = update {
                rewrite_ctype_in_expr(u, opaque_map);
            }
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
            for d in decls {
                d.ty = rewrite_ctype(&d.ty, opaque_map);
            }
        }
        CStmt::Sequence(stmts) => {
            for s in stmts {
                rewrite_ctype_in_stmt(s, opaque_map);
            }
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
                for p in &mut f.params {
                    p.ty = rewrite_ctype(&p.ty, opaque_map);
                }
                for v in &mut f.local_vars {
                    v.ty = rewrite_ctype(&v.ty, opaque_map);
                }
                rewrite_ctype_in_stmt(&mut f.body, opaque_map);
            }
            TopLevelDecl::FuncDecl(f) => {
                f.return_type = rewrite_ctype(&f.return_type, opaque_map);
                for p in &mut f.params {
                    p.ty = rewrite_ctype(&p.ty, opaque_map);
                }
            }
            TopLevelDecl::VarDecl(v) => {
                v.ty = rewrite_ctype(&v.ty, opaque_map);
            }
            _ => {}
        }
    }
}

// SR-1: bodies were converted when globals were scalar-typed, so against the new struct/array declarations &g must decay to the element pointer and bare g must map to g[0] or its first field.
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
        // An explicit member already presents the recovered aggregate at the
        // right field coordinate. Rewriting its direct owner Var as the
        // aggregate's first-field scalar would compose `g.ofs_0.ofs_N`.
        // This is the shape produced when an interior synthetic global has
        // already been coalesced to its owner's exact field.
        CExpr::Member(base, f) if matches!(base.as_ref(), CExpr::Var(name) if structs.contains_key(name)) => {
            CExpr::Member(base.clone(), f.clone())
        }
        CExpr::Member(base, f) => CExpr::Member(
            Box::new(rewrite_recovered_global_expr(base, arrays, structs)),
            f.clone(),
        ),
        CExpr::MemberPtr(base, f) => CExpr::MemberPtr(
            Box::new(rewrite_recovered_global_expr(base, arrays, structs)),
            f.clone(),
        ),
        // An explicit interior alias already indexes the recovered owner.
        // Rewriting its direct owner Var as owner[0] would produce the invalid
        // two-dimensional form owner[0][N].
        CExpr::Index(base, idx) if matches!(base.as_ref(), CExpr::Var(name) if arrays.contains(name)) => {
            CExpr::Index(
                base.clone(),
                Box::new(rewrite_recovered_global_expr(idx, arrays, structs)),
            )
        }
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

fn expr_mentions_byte_array(expr: &CExpr, byte_arrays: &HashSet<String>) -> bool {
    match expr {
        CExpr::Var(name) => byte_arrays.contains(name),
        CExpr::Unary(_, inner)
        | CExpr::Cast(_, inner)
        | CExpr::Paren(inner)
        | CExpr::SizeofExpr(inner) => expr_mentions_byte_array(inner, byte_arrays),
        CExpr::Index(base, _) => expr_mentions_byte_array(base, byte_arrays),
        _ => false,
    }
}

fn expr_is_proven_integer(expr: &CExpr) -> bool {
    match expr {
        CExpr::IntLit(_)
        | CExpr::CharLit(_)
        | CExpr::SizeofType(_)
        | CExpr::SizeofExpr(_)
        | CExpr::AlignofType(_) => true,
        CExpr::Cast(CType::Int(..) | CType::Bool | CType::Enum(_), _) => true,
        CExpr::Paren(inner) => expr_is_proven_integer(inner),
        CExpr::Unary(
            crate::decompile::passes::c_pass::types::UnaryOp::Neg
            | crate::decompile::passes::c_pass::types::UnaryOp::Plus
            | crate::decompile::passes::c_pass::types::UnaryOp::BitNot,
            inner,
        ) => expr_is_proven_integer(inner),
        _ => false,
    }
}

fn repair_byte_array_pointer_arithmetic(expr: &CExpr, byte_arrays: &HashSet<String>) -> CExpr {
    let CExpr::Binary(op, lhs, rhs) = expr else {
        return expr.clone();
    };
    let lhs_is_byte = expr_mentions_byte_array(lhs, byte_arrays);
    let rhs_is_byte = expr_mentions_byte_array(rhs, byte_arrays);
    let char_pointer = CType::ptr(CType::char_unsigned());
    match (op, lhs_is_byte, rhs_is_byte) {
        (crate::decompile::passes::c_pass::types::BinaryOp::Add, true, false)
            if expr_is_proven_integer(rhs) =>
        {
            CExpr::Binary(
                *op,
                Box::new(CExpr::Cast(char_pointer, lhs.clone())),
                rhs.clone(),
            )
        }
        (crate::decompile::passes::c_pass::types::BinaryOp::Sub, true, false)
            if expr_is_proven_integer(rhs) =>
        {
            CExpr::Binary(
                *op,
                Box::new(CExpr::Cast(char_pointer, lhs.clone())),
                rhs.clone(),
            )
        }
        (crate::decompile::passes::c_pass::types::BinaryOp::Add, false, true)
            if expr_is_proven_integer(lhs) =>
        {
            CExpr::Binary(
                *op,
                lhs.clone(),
                Box::new(CExpr::Cast(char_pointer, rhs.clone())),
            )
        }
        _ => expr.clone(),
    }
}

fn repair_byte_array_bitwise_scalar_reads(expr: &CExpr, byte_arrays: &HashSet<String>) -> CExpr {
    let CExpr::Binary(op, lhs, rhs) = expr else {
        return expr.clone();
    };
    if !matches!(
        op,
        crate::decompile::passes::c_pass::types::BinaryOp::BitAnd
            | crate::decompile::passes::c_pass::types::BinaryOp::BitOr
            | crate::decompile::passes::c_pass::types::BinaryOp::BitXor
    ) {
        return expr.clone();
    }
    let scalar = |operand: &CExpr| match operand {
        CExpr::Var(name) if byte_arrays.contains(name) => {
            CExpr::Index(Box::new(CExpr::Var(name.clone())), Box::new(CExpr::int(0)))
        }
        _ => operand.clone(),
    };
    CExpr::Binary(*op, Box::new(scalar(lhs)), Box::new(scalar(rhs)))
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

// IL-3/IL-4: classify each recovered struct by usage in the final TU -- unreferenced becomes void, referenced without layout an opaque tag, and needs_layout a full definition.

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
    /// The target's C data model, so a literal too wide for `int` gets a
    /// spelling that actually holds it.
    model: crate::abi::DataModel,
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
            let wide = !matches!(
                l.suffix,
                crate::decompile::passes::c_pass::types::IntLiteralSuffix::None
                    | crate::decompile::passes::c_pass::types::IntLiteralSuffix::U
            ) || l.value < i32::MIN as i128
                || l.value > u32::MAX as i128;
            Some(if wide {
                CType::int64(env.model, Signedness::Signed)
            } else {
                CType::Int(IntSize::Int, Signedness::Signed)
            })
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
                BinaryOp::Eq
                | BinaryOp::Ne
                | BinaryOp::Lt
                | BinaryOp::Le
                | BinaryOp::Gt
                | BinaryOp::Ge
                | BinaryOp::And
                | BinaryOp::Or => Some(CType::int()),
                BinaryOp::Add | BinaryOp::Sub => {
                    let l_is_ptr = matches!(
                        lt.as_ref().map(strip_quals),
                        Some(CType::Pointer(_, _) | CType::Array(_, _))
                    );
                    let r_is_ptr = matches!(
                        rt.as_ref().map(strip_quals),
                        Some(CType::Pointer(_, _) | CType::Array(_, _))
                    );
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
            if !matches!(
                op,
                crate::decompile::passes::c_pass::types::AssignOp::Assign
            ) {
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
                        Some(CType::Function(ret, _, _, _)) => Some(ret.as_ref().clone()),
                        Some(CType::Pointer(inner, _)) => match strip_quals(inner) {
                            CType::Function(ret, _, _, _) => Some(ret.as_ref().clone()),
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
    model: crate::abi::DataModel,
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
                callee_ret
                    .entry(d.name.clone())
                    .or_insert_with(|| d.return_type.clone());
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
                    model,
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
                        model,
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
        CType::Function(ret, params, _, _) => {
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
            CType::Struct(name) => {
                result.insert(name.clone());
            }
            CType::Pointer(inner, _) => collect_struct_refs(inner, result),
            CType::Array(inner, _) => collect_struct_refs(inner, result),
            CType::Function(ret, params, _, _) => {
                collect_struct_refs(ret, result);
                for p in params {
                    collect_struct_refs(p, result);
                }
            }
            CType::Qualified(inner, _) => collect_struct_refs(inner, result),
            _ => {}
        }
    }

    for decl in &tu.decls {
        match decl {
            TopLevelDecl::FuncDef(f) => {
                collect_struct_refs(&f.return_type, &mut referenced);
                for p in &f.params {
                    collect_struct_refs(&p.ty, &mut referenced);
                }
                for v in &f.local_vars {
                    collect_struct_refs(&v.ty, &mut referenced);
                }
                // A struct may only appear inside a cast in the body (e.g. ((struct_1 *)p)->ofs_8 when p is typed as a generic pointer). Walk the body so such structs are not mistaken for unreferenced and suppressed to void; mirrors rewrite_ctype_in_stmt which would otherwise rewrite those casts.
                collect_referenced_structs_in_stmt(&f.body, &mut referenced);
            }
            TopLevelDecl::FuncDecl(f) => {
                collect_struct_refs(&f.return_type, &mut referenced);
                for p in &f.params {
                    collect_struct_refs(&p.ty, &mut referenced);
                }
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
            CType::Struct(name) => {
                result.insert(name.clone());
            }
            CType::Pointer(inner, _) => collect_struct_refs(inner, result),
            CType::Array(inner, _) => collect_struct_refs(inner, result),
            CType::Function(ret, params, _, _) => {
                collect_struct_refs(ret, result);
                for p in params {
                    collect_struct_refs(p, result);
                }
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
            for a in args {
                collect_referenced_structs_in_expr(a, result);
            }
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
            CType::Struct(name) => {
                result.insert(name.clone());
            }
            CType::Pointer(inner, _) => collect_struct_refs(inner, result),
            CType::Array(inner, _) => collect_struct_refs(inner, result),
            CType::Function(ret, params, _, _) => {
                collect_struct_refs(ret, result);
                for p in params {
                    collect_struct_refs(p, result);
                }
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
                        for d in decls {
                            collect_struct_refs(&d.ty, result);
                        }
                    }
                }
            }
        }
        CStmt::If(c, t, e) => {
            collect_referenced_structs_in_expr(c, result);
            collect_referenced_structs_in_stmt(t, result);
            if let Some(e) = e {
                collect_referenced_structs_in_stmt(e, result);
            }
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
                        for d in decls {
                            collect_struct_refs(&d.ty, result);
                        }
                    }
                }
            }
            if let Some(c) = cond {
                collect_referenced_structs_in_expr(c, result);
            }
            if let Some(u) = update {
                collect_referenced_structs_in_expr(u, result);
            }
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
            for d in decls {
                collect_struct_refs(&d.ty, result);
            }
        }
        CStmt::Sequence(stmts) => {
            for s in stmts {
                collect_referenced_structs_in_stmt(s, result);
            }
        }
        _ => {}
    }
}

// Shared read set for the select/emit split; the full set keeps both halves ordered after their producers, with clight_selected_functions the typed-tree handoff.
const CLIGHT_EMIT_INPUTS: &[&str] = &[
    "clight_selected_functions",
    "committed_interfaces",
    "interface_vars",
    "emit_clight_stmt",
    "emit_clight_stmt_world",
    "emit_next_world",
    "structure_world",
    "emit_function",
    "func_entry_node",
    "emit_function_param",
    "emit_function_return_type",
    "emit_next",
    "clight_function_owners",
    "clight_targeted_nop_owner",
    "emit_var_type_candidate",
    "emit_loop_body",
    "emit_switch_chain",
    "emit_struct_fields",
    "primary_exit_node",
    "trim_step",
    "known_extern_signature",
    "ident_to_symbol",
    "is_external_function",
    "clight_succ",
    "string_data",
    "instr_in_function",
    "emit_address_as_offset",
    "symbol_size",
    "is_global_array",
    "global_storage_extent",
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
    "loop_exit_to_return",
    "emit_function_param_count",
    "emit_function_param_is_pointer",
    "emit_function_param_type",
    "emit_function_return",
    "emit_function_return_type_xtype",
    "emit_function_return_type_xtype_candidate",
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
    "emit_clight_sseq",
    "emit_clight_sseq_edge",
    "emit_struct_def",
    "emit_struct_field",
    "emit_var_is_struct",
    "func_param_struct_type",
    "func_param_position_type",
    "global_symbol",
    // Read by the propagator selection engine during the explicit maximal-
    // certification ablation, but declared unconditionally: an undeclared read
    // is silently empty in a parallel sub-DB.
    "mach_inst",
    // Pipeline-proven pointer classes consumed as hard declaration constraints
    // by the selector. This imperative query read must be present in parallel
    // sub-DBs just like the flow/class evidence below.
    "must_be_ptr",
    // Machine register-class evidence per value web, read by the adequacy audit
    // (always) and the register-class theory (propagator engine only).
    "web_class_gpr",
    "web_class_fp",
    // Load/store memory chunks, the flow theory's per-node width/class anchors.
    "rtl_inst",
    // Preferred no-model fallback for the deliberately advanced subword
    // signedness siblings published after RTL finalization.
    "rtl_superset_authoritative_chunk",
    "is_varargs_fn",
    "known_varargs_function",
    "known_global_type",
    "plt_entry",
    "code_pointer_in_data",
    "pointer_in_data",
    "reg_rtl",
    "resolved_extern_signature",
    "rtl_reg_used_in_func",
    "struct_id_to_canonical",
    "unknown_extern",
    "escaped_stack_region_field",
    "escaped_stack_region_caller_field",
    "escaped_stack_region_extent",
    // Both were read by the escaped-buffer layout derivation without being
    // declared, which leaves them empty in a parallel sub-db: the buffers then
    // lose their canonical base locals and every member rewrite with them.
    "slot_escaped_canonical",
    "slot_escaped_region_canonical",
    "stack_buffer_alias",
    "stack_buffer_end_alias",
    "stack_buffer_address_root",
    "semantic_frame_storage",
    "semantic_storage_obligation",
    "semantic_storage_projection",
    "semantic_storage_selected_target",
    "frame_read_storage_access_owner",
    "stack_var",
    "stack_base_move",
    "variadic_register_save_area_init",
    // Exact initialized bytes back designated initializers when a synthetic
    // interior global is coalesced into a recovered aggregate owner.
    "retained_initialized_data_range",
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
        crate::decompile::passes::clight_select::syntax::Stack::production().audit_selection(db);
    }

    fn inputs(&self) -> &'static [&'static str] {
        CLIGHT_EMIT_INPUTS
    }

    fn outputs(&self) -> &'static [&'static str] {
        static OUTPUTS: std::sync::LazyLock<Vec<&'static str>> = std::sync::LazyLock::new(|| {
            let mut outputs = vec![
                "clight_selected_functions",
                "committed_interfaces",
                "interface_vars",
            ];
            outputs.extend(
                crate::decompile::passes::clight_select::syntax::Stack::production().writes(),
            );
            outputs.sort_unstable();
            outputs.dedup();
            outputs
        });
        &OUTPUTS
    }

    fn extra_reads(&self) -> &'static [&'static str] {
        static READS: std::sync::LazyLock<Vec<&'static str>> = std::sync::LazyLock::new(|| {
            let mut reads = CLIGHT_EMIT_EXTRA_READS.to_vec();
            reads.extend(
                crate::decompile::passes::clight_select::syntax::Stack::production().reads(),
            );
            reads.sort_unstable();
            reads.dedup();
            reads
        });
        &READS
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
        eprintln!(
            "[clight-emit] selected functions: {}",
            selected_functions.len()
        );

        let mut id_to_name: HashMap<usize, String> = HashMap::new();
        // ident_to_symbol iteration order is non-deterministic; when several symbols share an id, prefer the shortest name with a lex tiebreak so the choice is stable.
        for (id, name) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
            let name_str = name.to_string();
            id_to_name
                .entry(*id)
                .and_modify(|existing| {
                    let take = name_str.len() < existing.len()
                        || (name_str.len() == existing.len()
                            && name_str.as_str() < existing.as_str());
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

        let globals =
            match crate::decompile::passes::clight_select::query::extract_globals(db, &binary_path)
            {
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
                n.strip_prefix("L_").map_or(false, |h| {
                    !h.is_empty() && h.chars().all(|c| c.is_ascii_hexdigit())
                })
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

        let mut global_lvalue_alias_candidates: HashMap<usize, HashSet<CExpr>> = HashMap::new();
        {
            // Use the same physical-storage/logical-layout reconciliation as
            // the declaration builder. A byte fallback here must correspond
            // to the byte array actually emitted there.
            let array_layouts = crate::decompile::passes::c_pass::convert::from_relations::recovered_global_array_declarations(db);
            // A repeated local-static spelling does not identify one storage
            // owner. Preserve every candidate and reject ambiguous aliases
            // instead of deterministically choosing the wrong address.
            let mut symbol_addrs_by_name: HashMap<&str, std::collections::BTreeSet<usize>> =
                HashMap::new();
            for (addr, _, name) in db.rel_iter::<(Address, usize, Symbol)>("symbol_size") {
                symbol_addrs_by_name
                    .entry(*name)
                    .or_default()
                    .insert(*addr as usize);
            }
            for (addr, name, _) in db.rel_iter::<(Address, Symbol, Symbol)>("symbols") {
                symbol_addrs_by_name
                    .entry(*name)
                    .or_default()
                    .insert(*addr as usize);
            }

            let struct_catalog_ids: HashSet<usize> = db
                .rel_iter::<(u64, usize, usize, usize)>("global_struct_catalog")
                .map(|(_, id, _, _)| *id)
                .collect();
            let mut known_typed_names: HashSet<String> = db
                .rel_iter::<(Symbol, XType)>("known_global_type")
                .map(|(name, _)| {
                    crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(name)
                })
                .collect();
            // The translation-unit builder gives solver-committed interface
            // types the same authority as known_global_type. Mirror both
            // sources here: a recovered aggregate candidate must not create
            // `owner.ofs_0` aliases when the declaration is committed to a
            // scalar/pointer type instead.
            known_typed_names.extend(
                db.committed_interfaces
                    .globals
                    .keys()
                    .filter_map(|ident| id_to_name.get(ident))
                    .map(|name| {
                        crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(name)
                    }),
            );
            let struct_owner_ids: HashSet<usize> = db
                .rel_iter::<(Ident, usize, Arc<Vec<(i64, Ident, MemoryChunk)>>)>(
                    "emit_global_struct_fields",
                )
                .filter_map(|(ident, sid, _)| struct_catalog_ids.contains(sid).then_some(*ident))
                .collect();

            // These are the names the translation-unit builder can actually
            // define. Read-only scalar folding is overridden for recovered
            // aggregate owners, because their interior aliases need storage.
            let declared_global_ids: HashSet<usize> = globals
                .iter()
                .filter(|global| {
                    !global.is_string
                        && (global.scalar_value.is_none()
                            || global.scalar_writable
                            || array_layouts.contains_key(&global.id)
                            || struct_owner_ids.contains(&global.id))
                })
                .map(|global| global.id)
                .collect();
            let globals_by_id: HashMap<
                usize,
                &crate::decompile::passes::clight_select::query::GlobalData,
            > = globals.iter().map(|global| (global.id, global)).collect();

            // SR-1 (FIXPLAN 4.5): interior idents of a recovered-struct global must not render as `(g + N)` (struct + int is invalid); name them `g.ofs_N` when the layout has a field at that offset, otherwise fall back to `(g + N)` byte-offset form.
            let struct_decl_field_offsets: HashMap<usize, std::collections::BTreeSet<i64>> = {
                // Min-sid per ident mirrors from_relations' winner; merge field offsets of every row carrying that sid.
                let mut chosen_sid: HashMap<usize, usize> = HashMap::new();
                for (ident, sid, _fields) in db
                    .rel_iter::<(Ident, usize, Arc<Vec<(i64, Ident, MemoryChunk)>>)>(
                        "emit_global_struct_fields",
                    )
                {
                    if !struct_catalog_ids.contains(sid) || !declared_global_ids.contains(ident) {
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
                    .rel_iter::<(Ident, usize, Arc<Vec<(i64, Ident, MemoryChunk)>>)>(
                        "emit_global_struct_fields",
                    )
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

            // A scalar machine access at an aggregate's base is still an
            // access to its first bytes, not a value of the whole C aggregate.
            // Seed an explicit base lvalue just like the interior aliases
            // below, so convert_expr can retain the Clight access type as
            // `*(T *)&owner.first` / `*(T *)&owner[0]`.  The later aggregate
            // rewrite otherwise turns a bare scalar Evar into `owner.first`
            // and silently inherits an unrelated winning field type (for
            // example, an overlapping 8-byte load can make a 4-byte float
            // access print as assignment from void *).
            for (base_ident, field_offsets) in &struct_decl_field_offsets {
                if !field_offsets.contains(&0) || !declared_global_ids.contains(base_ident) {
                    continue;
                }
                let Some(raw_owner_name) = id_to_name.get(base_ident) else {
                    continue;
                };
                if symbol_addrs_by_name
                    .get(raw_owner_name.as_str())
                    .is_some_and(|addresses| {
                        addresses.len() != 1 || !addresses.contains(base_ident)
                    })
                {
                    continue;
                }
                let owner_name = crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(raw_owner_name);
                if known_typed_names.contains(&owner_name)
                    || globals_by_id
                        .get(base_ident)
                        .is_some_and(|global| !global.pointer_init.is_empty())
                {
                    continue;
                }
                global_lvalue_alias_candidates
                    .entry(*base_ident)
                    .or_default()
                    .insert(CExpr::Member(
                        Box::new(CExpr::Var(owner_name)),
                        "ofs_0".to_string(),
                    ));
            }
            for base_ident in array_layouts.keys() {
                // The declaration builder gives a recovered struct precedence
                // when the same exact storage extent also admits an array
                // layout. Mirror that choice instead of inserting both base
                // coordinates and rejecting the owner as ambiguous below.
                if struct_decl_field_offsets.contains_key(base_ident)
                    || !declared_global_ids.contains(base_ident)
                {
                    continue;
                }
                let Some(raw_owner_name) = id_to_name.get(base_ident) else {
                    continue;
                };
                if symbol_addrs_by_name
                    .get(raw_owner_name.as_str())
                    .is_some_and(|addresses| {
                        addresses.len() != 1 || !addresses.contains(base_ident)
                    })
                {
                    continue;
                }
                let owner_name = crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(raw_owner_name);
                if known_typed_names.contains(&owner_name)
                    || globals_by_id
                        .get(base_ident)
                        .is_some_and(|global| !global.pointer_init.is_empty())
                {
                    continue;
                }
                global_lvalue_alias_candidates
                    .entry(*base_ident)
                    .or_default()
                    .insert(CExpr::Index(
                        Box::new(CExpr::Var(owner_name)),
                        Box::new(CExpr::int(0)),
                    ));
            }

            for (interior_ident, base_name, offset) in
                db.rel_iter::<(Ident, Symbol, i64)>("emit_address_as_offset")
            {
                let maybe_base_ident = symbol_addrs_by_name
                    .get(*base_name)
                    .filter(|addresses| addresses.len() == 1)
                    .and_then(|addresses| addresses.first().copied());
                let alias = if let Some(base_ident) = maybe_base_ident {
                    let owner_name = id_to_name
                        .get(&base_ident)
                        .map(|name| {
                            crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(name)
                        });
                    // The TU builder gives recovered structs precedence over
                    // arrays. Mirror that object-shape choice here.
                    if let (Some(field_offsets), Some(owner_name)) = (
                        struct_decl_field_offsets.get(&base_ident),
                        owner_name.as_ref(),
                    ) {
                        if globals_by_id
                            .get(&base_ident)
                            .is_some_and(|global| !global.pointer_init.is_empty())
                        {
                            continue;
                        }
                        if *offset > 0 && field_offsets.contains(offset) {
                            Some(CExpr::Member(
                                Box::new(CExpr::Var(owner_name.clone())),
                                format!("ofs_{}", offset),
                            ))
                        } else {
                            None
                        }
                    } else if let (Some(&(elem_size, _)), Some(owner_name)) =
                        (array_layouts.get(&base_ident), owner_name.as_ref())
                    {
                        if !declared_global_ids.contains(&base_ident)
                            || known_typed_names.contains(owner_name)
                            || globals_by_id
                                .get(&base_ident)
                                .is_some_and(|global| global.pointer_init.len() == 1)
                            || globals_by_id
                                .get(interior_ident)
                                .is_some_and(|global| !global.pointer_init.is_empty())
                        {
                            continue;
                        }
                        if elem_size > 0 && *offset >= 0 && (*offset as usize) % elem_size == 0 {
                            let index = (*offset as usize) / elem_size;
                            Some(CExpr::Index(
                                Box::new(CExpr::Var(owner_name.clone())),
                                Box::new(CExpr::int(index as i64)),
                            ))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                };
                // An interior coordinate must remain an expression. Encoding
                // `owner[index]` in id_to_name loses the brackets when the C
                // identifier sanitizer runs and silently allocates unrelated
                // storage. Offset zero already has the owner's ordinary name.
                if *offset > 0 {
                    if let Some(alias) = alias {
                        global_lvalue_alias_candidates
                            .entry(*interior_ident)
                            .or_default()
                            .insert(alias);
                    }
                }
            }
        }
        let global_lvalue_aliases: HashMap<usize, CExpr> = global_lvalue_alias_candidates
            .into_iter()
            .filter_map(|(ident, candidates)| {
                (candidates.len() == 1).then(|| (ident, candidates.into_iter().next().unwrap()))
            })
            .collect();

        // Resolve post-selection field types before either TU build. The
        // explicit function-scope ablation also runs the retired local/global
        // interface votes here for byte-compatible comparison.
        {
            let callee_sigs = db.committed_interfaces.callee_signatures();
            // Sort (id, name) before the first-wins insert so the surviving id for a duplicated name is deterministic, not dependent on HashMap iteration order. Mirrors the sibling builder in decl_solve::field_ptr_selection.
            let mut name_to_ident: HashMap<String, Ident> = HashMap::new();
            let mut sorted_id_name: Vec<(&usize, &String)> = id_to_name.iter().collect();
            sorted_id_name.sort_by_key(|(id, name)| (**id, (*name).clone()));
            for (id, name) in sorted_id_name {
                name_to_ident.entry(name.clone()).or_insert(*id as Ident);
            }
            // Data globals = OBJECT-kind symbols; a call through one of these names is the call-through-non-function family.
            let global_names: HashSet<String> = db
                .rel_iter::<(
                    Address,
                    usize,
                    Symbol,
                    Symbol,
                    Symbol,
                    usize,
                    Symbol,
                    usize,
                    Symbol,
                )>("symbol_table")
                .filter(|(_, _, sym_type, ..)| **sym_type == *"OBJECT")
                .map(|(.., name)| name.to_string())
                .collect();
            // The EMITTED function set (same filter as `internal_functions` below): the field-pointer authority decides only from functions that are actually printed, matching the retired TR-3 scan which ran over cast_selected_functions (= internal_functions).
            let external_funcs: HashSet<Address> = db
                .rel_iter::<(Address,)>("is_external_function")
                .map(|(a,)| *a)
                .collect();
            let internal_addrs: HashSet<Address> = selected_functions
                .iter()
                .filter(|f| {
                    !external_funcs.contains(&f.address)
                        && !f.name.starts_with('.')
                        && !db.should_skip_function(f.name.as_str())
                })
                .map(|f| f.address)
                .collect();
            let out = crate::decompile::passes::clight_select::decl_solve::run(
                &selected_functions,
                &internal_addrs,
                &callee_sigs,
                &name_to_ident,
                &global_names,
                &id_to_name,
                db.ablate_scope_function,
            );
            let force_long_reg_total: usize = out.force_long_regs.values().map(|s| s.len()).sum();
            let force_ptr_reg_total: usize = out.force_ptr_regs.values().map(|s| s.len()).sum();
            eprintln!(
                "[clight-emit] field-solve: {} force-long fields, {} field-ptr selections; legacy interface votes: {} fnptr globals, {} force-long regs / {} force-ptr regs in {} funcs",
                out.field_force_long.len(),
                out.field_ptr_selection.len(),
                out.fnptr_globals.len(),
                force_long_reg_total,
                force_ptr_reg_total,
                out.force_long_regs.len(),
            );
            db.decl_solve_field_force_long = out.field_force_long;
            db.decl_solve_field_ptr_selection = out.field_ptr_selection;
            db.decl_solve_fnptr_globals = if db.ablate_scope_function {
                out.fnptr_globals
            } else {
                db.committed_interfaces
                    .global_decl_types
                    .iter()
                    .filter_map(|(ident, ty)| {
                        id_to_name.get(ident).map(|name| {
                            (
                                crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(name),
                                ty.clone(),
                            )
                        })
                    })
                    .collect()
            };
            db.decl_solve_force_long_regs = out.force_long_regs;
            db.decl_solve_force_ptr_regs = out.force_ptr_regs;
        }

        // The raw (.light.c) TU is only read under --trace, and building it unconditionally cost 183s on ls/dir/vdir; build it only when tracing.
        let raw_translation_unit = if db.trace_enabled {
            let edges: Vec<(Node, Node)> = db
                .rel_iter::<(Node, Node)>("clight_succ")
                .map(|(src, dst)| (*src, *dst))
                .collect();
            let t = std::time::Instant::now();
            let tu = crate::decompile::passes::c_pass::convert::build_cast_from_relations(
                db,
                &selected_functions,
                &globals,
                &id_to_name,
                &global_lvalue_aliases,
                &edges,
                db.data_model(),
            );
            eprintln!(
                "[clight-emit] build_cast_from_relations (raw TU): {:?}",
                t.elapsed()
            );
            tu
        } else {
            crate::decompile::passes::c_pass::TranslationUnit::default()
        };

        let mut string_map = build_string_literal_map(db);
        let rodata_fp_labels = rodata_fp_constant_labels(db);
        for g in &globals {
            if g.is_string && !g.content.is_empty() && !rodata_fp_labels.contains(&g.name) {
                let s = String::from_utf8_lossy(&g.content)
                    .trim_end_matches('\0')
                    .to_string();
                string_map.entry(g.name.clone()).or_insert(s);
            }
        }

        // Inline constants only from read-only (.rodata) scalars: writable .data scalars keep their storage, so folding a read would be unsound.
        let rodata_const_map: HashMap<String, CExpr> = globals
            .iter()
            .filter(|g| !g.scalar_writable)
            .filter_map(|g| Some((g.name.clone(), g.scalar_value.as_ref()?.to_cexpr())))
            .collect();
        let struct_layouts =
            crate::decompile::passes::clight_select::query::extract_struct_layout_map(db);

        let external_funcs: HashSet<u64> = db
            .rel_iter::<(Address,)>("is_external_function")
            .map(|(a,)| *a)
            .collect();

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
                    node_to_funcs.get(caller).map_or(false, |funcs| {
                        funcs.iter().any(|f| internal_addrs.contains(f))
                    })
                })
                .map(|(_, callee)| *callee)
                .collect();
            for func in &selected_functions {
                if db.should_skip_function(func.name.as_str())
                    && called_addrs.contains(&func.address)
                {
                    let has_sig = db
                        .rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>(
                            "known_extern_signature",
                        )
                        .any(|(n, ..)| *n == func.name.as_str());
                    if !has_sig {
                        db.rel_push(
                            "unknown_extern",
                            (crate::util::leak::<String, str>(func.name.clone()),),
                        );
                    }
                }
            }
        }

        let data_model = db.data_model();
        let mut pure_stack_address_nodes: HashSet<Node> = db
            .rel_iter::<(Node, RTLInst)>("rtl_inst")
            .filter_map(|(node, inst)| match inst {
                RTLInst::Iop(
                    Operation::Olea(Addressing::Ainstack(_))
                    | Operation::Oleal(Addressing::Ainstack(_)),
                    args,
                    _,
                ) if args.is_empty() => Some(*node),
                _ => None,
            })
            .collect();
        let mut stack_address_origins: HashMap<Node, HashSet<StackAddrOrigin>> = HashMap::new();
        for (node, _, origin) in
            db.rel_iter::<(Node, RTLReg, StackAddrOrigin)>("canonical_stack_addr_def_origin")
        {
            stack_address_origins
                .entry(*node)
                .or_default()
                .insert(*origin);
        }
        pure_stack_address_nodes.extend(stack_address_origins.into_iter().filter_map(
            |(node, origins)| {
                (!origins.is_empty()
                    && origins
                        .iter()
                        .all(|origin| matches!(origin, StackAddrOrigin::Slot(..))))
                .then_some(node)
            },
        ));
        let mut storage_alias_candidates: HashMap<(Address, Ident), HashSet<Ident>> =
            HashMap::new();
        for (func, member, base, _) in
            db.rel_iter::<(Address, RTLReg, RTLReg, usize)>("stack_buffer_alias")
        {
            storage_alias_candidates
                .entry((*func, *member as Ident))
                .or_default()
                .insert(*base as Ident);
        }
        let mut storage_aliases: HashMap<Address, HashMap<Ident, Ident>> = HashMap::new();
        for ((func, member), candidates) in storage_alias_candidates {
            if candidates.len() == 1 {
                storage_aliases
                    .entry(func)
                    .or_default()
                    .insert(member, *candidates.iter().next().unwrap());
            }
        }
        let exact_stack_buffer_store_sites = crate::decompile::passes::c_pass::convert::from_relations::derive_exact_stack_buffer_store_sites(db);
        // Resolve each proven SysV register-save-area store to the physical
        // byte-buffer local that owns the containing va_list.  Ambiguous or
        // scalar-only storage fails closed: source va_start is inserted only
        // when both the ABI site and one storage owner are exact.
        let variadic_store_destinations: HashMap<Node, RTLReg> = db
            .rel_iter::<(Node, RTLInst)>("rtl_inst")
            .filter_map(|(node, inst)| match inst {
                RTLInst::Iop(Operation::Omove, args, destination) if args.len() == 1 => {
                    Some((*node, *destination))
                }
                _ => None,
            })
            .collect();
        let mut variadic_va_start_specs: HashMap<Address, HashSet<(Node, RTLReg, Ident)>> =
            HashMap::new();
        for (func, _save_slot, store_node) in
            db.rel_iter::<(Address, i64, Node)>("variadic_register_save_area_init")
        {
            let Some((base, relative)) = exact_stack_buffer_store_sites.get(&(*func, *store_node))
            else {
                continue;
            };
            if *relative == 16 {
                if let (Ok(base), Some(destination)) = (
                    Ident::try_from(*base),
                    variadic_store_destinations.get(store_node),
                ) {
                    variadic_va_start_specs
                        .entry(*func)
                        .or_default()
                        .insert((*store_node, *destination, base));
                }
            }
        }
        let empty_storage_aliases = HashMap::new();
        let selected_exact_pointer_stores: HashSet<_> = db
            .rel_iter::<(Address, Node, crate::decompile::passes::semantic_counterexample::ledger::ObjectId, i64, usize)>("semantic_storage_selected_target")
            .filter(|r| r.4 == 8)
            .map(|r| (r.0, r.1))
            .collect();
        let mut ctx =
            crate::decompile::passes::c_pass::convert::from_relations::ConversionContext::new(
                id_to_name.clone(),
                data_model,
            );
        ctx.global_lvalue_aliases = global_lvalue_aliases.clone();
        let mut var_types_for_emission: HashMap<String, CType> = HashMap::new();
        let mut all_statements: Vec<((Address, Node), CStmt)> = Vec::new();
        let mut all_edges: HashMap<Address, Vec<(Node, Node)>> = HashMap::new();

        for func in &internal_functions {
            let mut statements = Vec::new();
            let mut func_edges = Vec::new();
            ctx.source_post_effects.clear();
            ctx.applied_source_effects.clear();
            if let (Some(specs), Some(&last_named)) = (
                variadic_va_start_specs.get(&func.address), func.param_regs.last(),
            ) {
                for &(node, _, va_list_local) in specs {
                    if selected_exact_pointer_stores.contains(&(func.address, node))
                        && func.statements.iter().map(|(&origin, stmt)|
                            count_selected_store_origins(stmt, Some(origin), node)).sum::<usize>() == 1
                    {
                        ctx.source_post_effects.insert(node, source_va_start(va_list_local, last_named));
                    }
                }
            }

            for (reg, pty) in func.param_regs.iter().zip(func.param_types.iter()) {
                let name = param_name_for_reg(*reg);
                let ty = match pty {
                    crate::x86::types::ParamType::StructPointer(_)
                    | crate::x86::types::ParamType::Typed(_) => {
                        convert_param_type_from_param(pty, data_model)
                    }
                    _ => {
                        if let Some(type_str) = func.var_types.get(reg) {
                            candtype_to_ctype(*type_str, data_model)
                        } else {
                            convert_param_type_from_param(pty, data_model)
                        }
                    }
                };
                var_types_for_emission.entry(name).or_insert(ty);
            }

            for (var_name, type_str) in &func.var_types {
                let ty = candtype_to_ctype(*type_str, data_model);
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
                sorted_stmt_nodes.sort_by_key(|node| exec_order_key(*node));
                for node in sorted_stmt_nodes {
                    let clight_stmt = &func.statements[&node];
                    let function_storage_aliases = storage_aliases
                        .get(&func.address)
                        .unwrap_or(&empty_storage_aliases);
                    let self_address =
                        is_self_address_materialization(clight_stmt, function_storage_aliases);
                    let pure_address = pure_stack_address_nodes.contains(&node);
                    let mapped_address = uses_storage_alias(clight_stmt, function_storage_aliases);
                    if self_address && (pure_address || mapped_address) {
                        continue;
                    }
                    let cstmt =
                        crate::decompile::passes::c_pass::convert::from_relations::convert_stmt_at(
                            clight_stmt,
                            &mut ctx,
                            node,
                        );
                    // A finalized exact scalar load is stronger than the
                    // high-recall string_data byte-shape hint.  Fold proven
                    // scalars first so an integer such as 37 (bytes
                    // `25 00 00 00`) cannot subsequently become "%".  The
                    // scalar rewriter deliberately preserves direct address-of
                    // operands, so genuine and mixed-use strings still reach
                    // the string pass below.
                    let cstmt = crate::decompile::passes::c_pass::helpers::map_stmt_exprs_total(
                        &cstmt,
                        &|e| {
                            crate::decompile::passes::c_pass::helpers::inline_rodata_constants_preserving_addrof(e, &rodata_const_map)
                        },
                    );
                    let cstmt =
                        crate::decompile::passes::c_pass::helpers::map_stmt_exprs(&cstmt, &|e| {
                            inline_string_literals(e, &string_map)
                        });
                    let cstmt = crate::decompile::passes::c_pass::convert::from_relations::narrow_varargs_in_stmt(&cstmt);
                    statements.push((node, cstmt));
                }
            }

            if let (Some(specs), Some(&last_named)) = (
                variadic_va_start_specs.get(&func.address),
                func.param_regs.last(),
            ) {
                let mut specs: Vec<(Node, RTLReg, Ident)> = specs.iter().copied().collect();
                specs.sort_unstable();
                for (node, destination, va_list_local) in specs {
                    if ctx.applied_source_effects.contains(&node) { continue; }
                    let destination = param_name_for_reg(destination);
                    let matches: usize = statements
                        .iter()
                        .map(|(_, stmt)| count_assignments_to(stmt, &destination))
                        .sum();
                    if matches != 1 {
                        continue;
                    }
                    let inserted: usize = statements
                        .iter_mut()
                        .map(|(_, stmt)| {
                            insert_va_start_after_assignment(
                                stmt,
                                &destination,
                                va_list_local,
                                last_named,
                            )
                        })
                        .sum();
                    debug_assert_eq!(inserted, 1);
                }
            }
            if !ctx.applied_source_effects.is_empty() {
                eprintln!("[source-abi] function={:#x} origin-bound-va-start={}", func.address, ctx.applied_source_effects.len());
            }

            // func.successors is a HashMap, so iterating it leaks non-deterministic ordering into the edge sets; the pair set is the same, but sort by source for stable diagnostics anyway.
            let mut succ_nodes: Vec<Node> = func.successors.keys().copied().collect();
            succ_nodes.sort_by_key(|node| exec_order_key(*node));
            for node in succ_nodes {
                if let Some(succs) = func.successors.get(&node) {
                    for succ in succs {
                        func_edges.push((node, *succ));
                    }
                }
            }
            {
                // Map every label a node defines, so a goto edge is built even when the target label sits inside a fused Sequence; first-writer-wins is deterministic.
                let mut label_to_node: HashMap<String, Node> = HashMap::new();
                for (n, s) in &statements {
                    let mut labels = Vec::new();
                    crate::decompile::passes::c_pass::helpers::collect_defined_labels(
                        s,
                        &mut labels,
                    );
                    for label in labels {
                        label_to_node.entry(label).or_insert(*n);
                    }
                }
                let node_set: HashSet<Node> = statements.iter().map(|(n, _)| *n).collect();
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
                let mut sorted_nodes: Vec<Node> = statements.iter().map(|(n, _)| *n).collect();
                sorted_nodes.sort_by_key(|node| exec_order_key(*node));
                let has_outgoing: HashSet<Node> = func_edges.iter().map(|(f, _)| *f).collect();
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

            // (Resolved TODO: late control-flow structuring is done by the post-select ForLoopPass; upstream structural recovery belongs in structuring_pass / clight_select, not at emission.)
            all_statements.extend(statements.into_iter().map(|(node,stmt)| ((func.address,node),stmt)));
            all_edges.insert(func.address,func_edges);
        }

        db.cast_selected_functions = internal_functions;
        db.cast_globals = globals;
        db.cast_id_to_name = id_to_name;
        db.cast_struct_layouts = struct_layouts;
        db.cast_var_types_for_emission = var_types_for_emission.clone();
        db.cast_raw_translation_unit = Some(raw_translation_unit);

        let t = std::time::Instant::now();
        let mut struct_defs =
            crate::decompile::passes::clight_select::query::extract_struct_definitions(db);
        eprintln!(
            "[clight-emit] extract_struct_definitions: {:?} ({} structs)",
            t.elapsed(),
            struct_defs.len()
        );

        let stmt_map: HashMap<(Address, Node), CStmt> = all_statements.into_iter().collect();

        log::info!(
            "Building translation unit from {} statements",
            stmt_map.len()
        );

        let t = std::time::Instant::now();
        let (mut tu, variable_origins) = crate::decompile::passes::c_pass::convert::from_relations::build_translation_unit_with_variable_origins(
            db,
            &db.cast_selected_functions,
            &db.cast_globals,
            &db.cast_id_to_name,
            &global_lvalue_aliases,
            &stmt_map,
            &all_edges,
            &db.cast_var_types_for_emission,
        );
        eprintln!(
            "[clight-emit] build_translation_unit (optimized TU): {:?}",
            t.elapsed()
        );
        db.rel_set("emit_c_variable_origin", variable_origins.into_iter().collect::<ascent::boxcar::Vec<_>>());
        db.cast_post_emit_audit_trail =
            Some(crate::decompile::analysis::coverage_pass::PostEmitAuditTrail::new(&tu));

        // SR-1 (FIXPLAN 4.5): rewrite function bodies to be consistent with the recovered-global declarations (struct/array VarDecls produced only by from_relations, not convert_xtype). Must run before opaqueness/layout analyses.
        {
            let mut array_globals: HashSet<String> = HashSet::new();
            let mut byte_array_globals: HashSet<String> = HashSet::new();
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
                        CType::Array(element, ..) => {
                            array_globals.insert(v.name.clone());
                            if matches!(
                                element.as_ref(),
                                CType::Int(
                                    crate::decompile::passes::c_pass::types::IntSize::Char,
                                    _
                                )
                            ) {
                                byte_array_globals.insert(v.name.clone());
                            }
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
                        let local_byte_arrays: HashSet<String> = f
                            .local_vars
                            .iter()
                            .filter_map(|local| match &local.ty {
                                CType::Array(element, _)
                                    if matches!(
                                        element.as_ref(),
                                        CType::Int(
                                            crate::decompile::passes::c_pass::types::IntSize::Char,
                                            _
                                        )
                                    ) =>
                                {
                                    Some(local.name.clone())
                                }
                                _ => None,
                            })
                            .collect();
                        rewrite_recovered_global_stmt(&mut f.body, &array_globals, &struct_globals);
                        f.body = crate::decompile::passes::c_pass::helpers::map_stmt_exprs(
                            &f.body,
                            &|expr| {
                                let expr =
                                    repair_byte_array_pointer_arithmetic(expr, &byte_array_globals);
                                Some(repair_byte_array_bitwise_scalar_reads(
                                    &expr,
                                    &local_byte_arrays,
                                ))
                            },
                        );
                        for v in &mut f.local_vars {
                            if let Some(init) = &mut v.init {
                                rewrite_recovered_global_init(
                                    init,
                                    &array_globals,
                                    &struct_globals,
                                );
                            }
                        }
                    }
                }
            }
        }

        // Materialize Stage B's committed function-pointer data globals at the
        // TU level (or the legacy vote under the explicit ablation). Runtime
        // stores through `*(long *)&name` remain legal aliasing, while
        // `name(args)` becomes a function-pointer call.
        if !db.decl_solve_fnptr_globals.is_empty() {
            let mut patched = 0usize;
            for decl in &mut tu.decls {
                if let TopLevelDecl::VarDecl(v) = decl {
                    if let Some(fnty) = db.decl_solve_fnptr_globals.get(&v.name) {
                        v.ty = fnty.clone();
                        v.init = None;
                        patched += 1;
                    }
                }
            }
            eprintln!(
                "[clight-emit] interface commitment: {} global decls retyped to fn pointers",
                patched
            );
        }

        // CTYPING_PLAN 5.3: apply decl_solve's field-pointer selection before field_types reads it, combined with the force-long retypes; the former C-AST final veto is RETIRED as it removed nothing.
        {
            let t = std::time::Instant::now();
            let mut tr3_selection: HashMap<(String, String), String> =
                db.decl_solve_field_ptr_selection.clone();
            for key in &db.decl_solve_field_force_long {
                tr3_selection.insert(key.clone(), "long".to_string());
            }
            let patched =
                crate::decompile::passes::clight_select::query::apply_struct_field_type_selection(
                    &mut struct_defs,
                    &tr3_selection,
                );
            if patched > 0 {
                eprintln!(
                    "[clight-emit] decl-solve field-type selection: {} field(s) retyped ({:?})",
                    patched,
                    t.elapsed()
                );
            }
        }

        // Identify opaque libc structs (FILE, DIR) via C AST scan and RTL-level analysis.
        let t = std::time::Instant::now();
        let mut opaque_map = identify_opaque_libc_structs_from_tu(&tu);
        for id in crate::x86::types::LIBC_RECORDS {
            if let Some((typedef, _)) = crate::x86::types::libc_record(id) {
                opaque_map.insert(format!("struct_{id:x}"), typedef.to_string());
            }
        }
        eprintln!(
            "[clight-emit] identify_opaque_libc_structs: {:?} ({} found)",
            t.elapsed(),
            opaque_map.len()
        );

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
                                    opaque_map
                                        .entry(struct_name)
                                        .or_insert_with(|| typedef_name.to_string());
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
        let layout_ev = collect_struct_layout_evidence(&tu, &field_types, db.data_model());
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
                let Some(name) = extracted.definition.name.as_ref() else {
                    continue;
                };
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

        let (mut n_full, mut n_opaque, mut n_tabled, mut n_voided) =
            (0usize, 0usize, 0usize, 0usize);
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
            tu.decls
                .push(TopLevelDecl::StructDef(extracted.definition.clone()));
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

        if let Some(audit) = db.cast_post_emit_audit_trail.as_mut() {
            if let Err(reason) = audit.record(
                crate::decompile::analysis::coverage_pass::PostEmitCheckpoint::ClightEmitFinalize,
                &tu,
            ) {
                log::warn!("coverage: cannot record ClightEmit checkpoint: {reason}");
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
            "cast_post_emit_audit_trail",
            "cast_optimized_translation_unit",
            "emit_c_variable_origin",
        ]
    }

    fn extra_reads(&self) -> &'static [&'static str] {
        CLIGHT_EMIT_EXTRA_READS
    }
}

#[cfg(test)]
mod tests {
    use super::{
        append_source_va_start, count_assignments_to, insert_va_start_after_assignment,
        is_self_address_materialization, repair_byte_array_bitwise_scalar_reads,
        repair_byte_array_pointer_arithmetic, rewrite_recovered_global_expr, uses_storage_alias,
        ClightEmitPass, ClightSelectPass,
    };
    use crate::decompile::passes::c_pass::types::{
        AssignOp, CExpr, CStmt, CType, FloatSize, UnaryOp,
    };
    use crate::decompile::passes::clight_pass::ClightPass;
    use crate::decompile::passes::pass::IRPass;
    use crate::x86::types::{ClightExpr, ClightStmt, ClightType};
    use std::collections::{HashMap, HashSet};

    #[test]
    fn selected_abi_event_survives_explicit_memory_view_lowering() {
        use crate::decompile::passes::c_pass::convert::from_relations::{convert_stmt_at, ConversionContext};
        use crate::x86::types::{ClightAttr, ClightSignedness};
        let word = ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default());
        let store = ClightStmt::Sassign(
            ClightExpr::Ederef(Box::new(ClightExpr::Etempvar(7,
                ClightType::Tpointer(std::sync::Arc::new(word.clone()), ClightAttr::default()))), word.clone()),
            ClightExpr::EconstLong(123, word),
        );
        let nested = ClightStmt::Ssequence(vec![
            ClightStmt::Slabel(42, Box::new(store.clone())),
            ClightStmt::Scall(None, ClightExpr::Etempvar(99, ClightType::Tvoid), vec![]),
        ]);
        assert_eq!(super::count_selected_store_origins(&nested, Some(10), 42), 1);
        assert_eq!(super::count_selected_store_origins(&nested, Some(42), 10), 0);
        let mut ctx = ConversionContext::new(HashMap::new(), crate::abi::DataModel::Lp64);
        ctx.source_post_effects.insert(42, super::source_va_start(20, 1));
        let converted = convert_stmt_at(&nested, &mut ctx, 10);
        let printed = crate::decompile::passes::c_pass::print::print_stmt(&converted);
        assert_eq!(printed.matches("__builtin_va_start").count(), 1, "{printed}");
        assert!(printed.find("__builtin_memcpy").unwrap() < printed.find("__builtin_va_start").unwrap());
        assert!(printed.find("__builtin_va_start").unwrap() < printed.find("var_99(").unwrap());
        assert_eq!(ctx.applied_source_effects, HashSet::from([42]));

        // A compound header does not license moving the initialization after
        // an entire loop, or attaching it to a different unlabelled store.
        let compound = ClightStmt::Sloop(Box::new(store), Box::new(ClightStmt::Sskip));
        assert_eq!(super::count_selected_store_origins(&compound, Some(42), 42), 0);
        ctx.applied_source_effects.clear();
        let converted = convert_stmt_at(&compound, &mut ctx, 42);
        assert!(!crate::decompile::passes::c_pass::print::print_stmt(&converted).contains("__builtin_va_start"));
        assert!(ctx.applied_source_effects.is_empty());
    }

    #[test]
    fn proven_variadic_save_store_appends_source_va_start() {
        let original = CStmt::Expr(CExpr::assign(CExpr::var("slot"), CExpr::var("save_area")));
        let va_list_local = 0x1234;
        let last_named = 0x5678;

        let rewritten = append_source_va_start(original.clone(), va_list_local, last_named);

        assert!(matches!(
            rewritten,
            CStmt::Sequence(parts)
                if parts.len() == 2
                    && parts[0] == original
                    && matches!(
                        &parts[1],
                        CStmt::Expr(CExpr::Call(callee, args))
                            if matches!(callee.as_ref(), CExpr::Var(name) if name == "__builtin_va_start")
                                && matches!(
                                    args.as_slice(),
                                    [
                                        CExpr::Unary(
                                            UnaryOp::Deref,
                                            target,
                                        ),
                                        CExpr::Var(last),
                                    ] if matches!(
                                        target.as_ref(),
                                        CExpr::Cast(
                                            CType::Pointer(inner, _),
                                            local,
                                        ) if matches!(inner.as_ref(), CType::TypedefName(name) if name == "__builtin_va_list")
                                            && matches!(local.as_ref(), CExpr::Var(name) if name == "var_4660")
                                    ) && last == &crate::decompile::passes::c_pass::helpers::param_name_for_reg(last_named)
                                )
                    )
        ));
    }

    #[test]
    fn folded_sequence_inserts_va_start_after_the_unique_save_assignment() {
        let destination = "var_99";
        let mut body = CStmt::Sequence(vec![
            CStmt::Expr(CExpr::assign(CExpr::var("other"), CExpr::int(1))),
            CStmt::Labeled(
                crate::decompile::passes::c_pass::types::Label::Named("save".to_string()),
                Box::new(CStmt::Sequence(vec![
                    CStmt::Expr(CExpr::assign(
                        CExpr::var(destination),
                        CExpr::var("register_save_area"),
                    )),
                    CStmt::Expr(CExpr::call(CExpr::var("consume"), vec![])),
                ])),
            ),
        ]);

        assert_eq!(count_assignments_to(&body, destination), 1);
        assert_eq!(
            insert_va_start_after_assignment(&mut body, destination, 0x1234, 0x5678),
            1
        );
        let printed = crate::decompile::passes::c_pass::print::print_stmt(&body);
        let save = printed.find("var_99 = register_save_area;").unwrap();
        let start = printed.find("__builtin_va_start").unwrap();
        let consume = printed.find("consume()").unwrap();
        assert!(save < start && start < consume, "{printed}");
    }

    #[test]
    fn recovered_byte_array_keeps_byte_stride_in_pointer_addition() {
        let byte_array = "bytes".to_string();
        let expr = CExpr::Binary(
            crate::decompile::passes::c_pass::types::BinaryOp::Add,
            Box::new(CExpr::int(2)),
            Box::new(CExpr::Cast(
                CType::ptr(CType::int()),
                Box::new(CExpr::Index(
                    Box::new(CExpr::Var(byte_array.clone())),
                    Box::new(CExpr::int(0)),
                )),
            )),
        );

        let wrapped = CExpr::Assign(
            AssignOp::Assign,
            Box::new(CExpr::Var("cursor".to_string())),
            Box::new(expr),
        );
        let repaired = crate::decompile::passes::c_pass::helpers::map_expr(&wrapped, &|expr| {
            Some(repair_byte_array_pointer_arithmetic(
                expr,
                &HashSet::from([byte_array.clone()]),
            ))
        });
        assert!(matches!(
            repaired,
            CExpr::Assign(
                _,
                _,
                rhs
            ) if matches!(
                rhs.as_ref(),
                CExpr::Binary(
                    crate::decompile::passes::c_pass::types::BinaryOp::Add,
                    _,
                    byte_rhs,
                ) if matches!(
                    byte_rhs.as_ref(),
                    CExpr::Cast(CType::Pointer(inner, _), _)
                        if matches!(inner.as_ref(), CType::Int(crate::decompile::passes::c_pass::types::IntSize::Char, _))
                )
            )
        ));

        let already_byte_scaled = CExpr::Binary(
            crate::decompile::passes::c_pass::types::BinaryOp::Add,
            Box::new(CExpr::Cast(
                CType::ptr(CType::char_signed()),
                Box::new(CExpr::Var("cursor".to_string())),
            )),
            Box::new(CExpr::Cast(
                CType::long(),
                Box::new(CExpr::Index(
                    Box::new(CExpr::Var(byte_array.clone())),
                    Box::new(CExpr::int(0)),
                )),
            )),
        );
        assert_eq!(
            repair_byte_array_pointer_arithmetic(
                &already_byte_scaled,
                &HashSet::from([byte_array]),
            ),
            already_byte_scaled,
            "an existing pointer-plus-integer expression must not become pointer-plus-pointer",
        );
    }

    #[test]
    fn byte_buffer_in_bitwise_value_context_reads_its_first_byte() {
        let buffer = "overflow_flag".to_string();
        let expr = CExpr::Binary(
            crate::decompile::passes::c_pass::types::BinaryOp::BitOr,
            Box::new(CExpr::int(1)),
            Box::new(CExpr::Var(buffer.clone())),
        );

        let repaired =
            repair_byte_array_bitwise_scalar_reads(&expr, &HashSet::from([buffer.clone()]));
        assert!(matches!(
            repaired,
            CExpr::Binary(_, _, rhs)
                if matches!(
                    rhs.as_ref(),
                    CExpr::Index(base, index)
                        if base.as_ref() == &CExpr::Var(buffer)
                            && index.as_ref() == &CExpr::int(0)
                )
        ));
    }

    #[test]
    fn casted_self_address_materialization_is_recognized() {
        let ident = 0x7100;
        let self_address = ClightStmt::Sset(
            ident,
            ClightExpr::Ecast(
                Box::new(ClightExpr::Eaddrof(
                    Box::new(ClightExpr::Evar(ident, ClightType::Tvoid)),
                    ClightType::Tvoid,
                )),
                ClightType::Tvoid,
            ),
        );
        let other_address = ClightStmt::Sset(
            ident,
            ClightExpr::Eaddrof(
                Box::new(ClightExpr::Evar(ident + 1, ClightType::Tvoid)),
                ClightType::Tvoid,
            ),
        );

        assert!(is_self_address_materialization(
            &self_address,
            &HashMap::new()
        ));
        assert!(!is_self_address_materialization(
            &other_address,
            &HashMap::new()
        ));

        let alias = ident + 2;
        let aliased_address = ClightStmt::Sset(
            alias,
            ClightExpr::Eaddrof(
                Box::new(ClightExpr::Evar(ident, ClightType::Tvoid)),
                ClightType::Tvoid,
            ),
        );
        assert!(is_self_address_materialization(
            &aliased_address,
            &HashMap::from([(alias, ident)]),
        ));
        assert!(uses_storage_alias(
            &aliased_address,
            &HashMap::from([(alias, ident)]),
        ));
    }

    #[test]
    fn explicit_recovered_global_member_is_not_prefixed_by_first_field() {
        let owner = "L_e090".to_string();
        let expr = CExpr::Member(Box::new(CExpr::Var(owner.clone())), "ofs_8".to_string());
        let structs = HashMap::from([(owner.clone(), "ofs_0".to_string())]);

        let rewritten = rewrite_recovered_global_expr(&expr, &HashSet::new(), &structs);

        assert_eq!(rewritten, expr);
        assert_eq!(
            rewrite_recovered_global_expr(&CExpr::Var(owner.clone()), &HashSet::new(), &structs,),
            CExpr::Member(Box::new(CExpr::Var(owner.clone())), "ofs_0".to_string(),),
            "a genuinely bare aggregate use must still select its scalar first field",
        );
        assert_ne!(
            rewritten,
            CExpr::Member(
                Box::new(CExpr::Member(
                    Box::new(CExpr::Var(owner)),
                    "ofs_0".to_string(),
                )),
                "ofs_8".to_string(),
            ),
            "an interior field already rewritten to its owner was composed twice",
        );
    }

    #[test]
    fn explicit_recovered_global_index_is_not_prefixed_by_first_element() {
        let owner = "global_bytes".to_string();
        let expr = CExpr::Index(Box::new(CExpr::Var(owner.clone())), Box::new(CExpr::int(7)));
        let arrays = HashSet::from([owner.clone()]);

        assert_eq!(
            rewrite_recovered_global_expr(&expr, &arrays, &HashMap::new()),
            expr,
        );
        assert_eq!(
            rewrite_recovered_global_expr(&CExpr::Var(owner.clone()), &arrays, &HashMap::new(),),
            CExpr::Index(Box::new(CExpr::Var(owner)), Box::new(CExpr::int(0))),
            "a genuinely bare aggregate use must still select its first element",
        );
    }

    #[test]
    fn typed_aggregate_base_alias_survives_recovered_global_rewrite() {
        let owner = "L_26640".to_string();
        let alias = CExpr::Member(Box::new(CExpr::Var(owner.clone())), "ofs_0".to_string());
        let expr = CExpr::Unary(
            UnaryOp::Deref,
            Box::new(CExpr::Cast(
                CType::ptr(CType::Float(FloatSize::Float)),
                Box::new(CExpr::Unary(UnaryOp::AddrOf, Box::new(alias))),
            )),
        );
        let structs = HashMap::from([(owner, "ofs_0".to_string())]);

        assert_eq!(
            rewrite_recovered_global_expr(&expr, &HashSet::new(), &structs),
            expr,
            "the aggregate rewrite must preserve the access-specific cast around an exact base coordinate",
        );
    }

    #[test]
    fn clight_sseq_relations_are_scheduler_isolated() {
        let clight = ClightPass;
        assert!(clight.outputs().contains(&"emit_clight_sseq"));
        assert!(clight.outputs().contains(&"emit_clight_sseq_edge"));
        assert!(!clight.outputs().contains(&"emit_sseq"));

        let select = ClightSelectPass;
        assert!(select.extra_reads().contains(&"emit_clight_sseq"));
        assert!(select.extra_reads().contains(&"emit_clight_sseq_edge"));
        assert!(!select.extra_reads().contains(&"emit_sseq"));

        let emit = ClightEmitPass;
        assert!(emit.extra_reads().contains(&"emit_clight_sseq"));
        assert!(emit.extra_reads().contains(&"emit_clight_sseq_edge"));
        assert!(!emit.extra_reads().contains(&"emit_sseq"));
    }

    #[test]
    fn semantic_function_ownership_is_a_scheduled_clight_handoff() {
        let clight = ClightPass;
        assert!(clight.outputs().contains(&"clight_function_owners"));
        assert!(clight.outputs().contains(&"clight_targeted_nop_owner"));

        let select = ClightSelectPass;
        assert!(select.inputs().contains(&"clight_function_owners"));
        assert!(select.inputs().contains(&"clight_targeted_nop_owner"));
    }

    #[test]
    fn source_va_start_reads_the_proven_register_save_store() {
        let emit = ClightEmitPass;
        assert!(emit
            .extra_reads()
            .contains(&"variadic_register_save_area_init"));
        assert!(emit.extra_reads().contains(&"semantic_storage_selected_target"));
    }

    #[test]
    fn relocated_global_recovery_declares_array_layout_scheduler_read() {
        let select = ClightSelectPass;
        assert!(select.inputs().contains(&"is_global_array"));

        let emit = ClightEmitPass;
        assert!(emit.inputs().contains(&"is_global_array"));
    }

    #[test]
    fn shared_frame_coordinates_are_available_in_parallel_emit_and_select() {
        for pass in [&ClightSelectPass as &dyn IRPass, &ClightEmitPass as &dyn IRPass] {
            for input in crate::decompile::analysis::frame_coordinates::INPUTS {
                assert!(pass.inputs().contains(input) || pass.extra_reads().contains(input), "{} omitted {input}", pass.name());
            }
        }
    }
}
