use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::decompile::passes::c_pass::helpers::{
    build_string_literal_map, collect_goto_label_targets, convert_param_type_from_param,
    extract_named_label, inline_rodata_constants, inline_string_literals, is_terminal_cstmt,
    param_name_for_reg, xtype_string_to_ctype,
};
use crate::decompile::passes::c_pass::types::{
    CExpr, CStmt, CType, FloatLiteral, FloatLiteralSuffix, IntLiteral, IntLiteralBase,
    IntLiteralSuffix, TopLevelDecl, TypeQualifiers,
};
use crate::x86::types::*;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// Known libc functions that take opaque struct pointer parameters.
/// Maps function_name -> Vec<(param_position, typedef_name)>.
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

    // (2) Check function signatures of known opaque-pointer functions for struct params.
    for decl in &tu.decls {
        let (name, params) = match decl {
            TopLevelDecl::FuncDef(f) => (f.name.as_str(), &f.params),
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

/// Check if all fields have auto-generated names (ofs_N, _pad_N, i_N, s_N, uc_N, field_N).
fn all_fields_autogenerated(def: &crate::decompile::passes::c_pass::types::StructDef) -> bool {
    if def.fields.is_empty() {
        return true;
    }
    def.fields.iter().all(|f| {
        match &f.name {
            Some(name) => {
                name.starts_with("ofs_")
                    || name.starts_with("_pad_")
                    || name.starts_with("i_")
                    || name.starts_with("s_")
                    || name.starts_with("uc_")
                    || name.starts_with("field_")
            }
            None => true,
        }
    })
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

        let selected_functions = match crate::decompile::passes::clight_select::select::select_clight_stmts(db) {
            Ok(funcs) => funcs,
            Err(e) => {
                log::warn!("ClightEmitPass: failed to select statements: {}", e);
                return;
            }
        };

        let mut id_to_name: HashMap<usize, String> = HashMap::new();
        for (id, name) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
            let name_str = name.to_string();
            id_to_name
                .entry(*id)
                .and_modify(|existing| {
                    if name.len() < existing.len() {
                        *existing = name_str.clone();
                    }
                })
                .or_insert_with(|| name_str);
        }
        // ELF symbols override ident_to_symbol.
        for (addr, name, _) in db.rel_iter::<(Address, Symbol, Symbol)>("symbols") {
            let id = *addr as usize;
            id_to_name.insert(id, name.to_string());
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

        // Resolve auto-generated L_XXXX labels by merging fragmented func_stacksz ranges back into their containing function.
        {
            let is_generated_label = |n: &str| -> bool {
                n.strip_prefix("L_")
                    .map_or(false, |h| !h.is_empty() && h.chars().all(|c| c.is_ascii_hexdigit()))
            };

            // Collect jump table target addresses to prevent label-to-function-name resolution
            let jump_table_target_addrs: HashSet<u64> = db
                .rel_iter::<(Node, usize, Node)>("jump_table_target")
                .map(|(_, _, target)| *target)
                .collect();

            let mut raw: Vec<(u64, u64, String)> = db
                .rel_iter::<(Address, Address, Symbol, u64)>("func_stacksz")
                .map(|(s, e, n, _)| (*s, *e, n.to_string()))
                .collect();
            raw.sort_by_key(|(s, _, _)| *s);

            // Merge: absorb consecutive L_XXXX entries into the preceding real function
            let mut func_ranges: Vec<(u64, u64, String)> = Vec::new();
            for (start, end, name) in raw {
                if is_generated_label(&name) {
                    // Extend the previous real function's end to cover this fragment
                    if let Some(last) = func_ranges.last_mut() {
                        if start == last.1 {
                            last.1 = end;
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
                // Don't rename labels that are jump table targets (internal labels needed by switch/case gotos)
                if jump_table_target_addrs.contains(&addr) {
                    continue;
                }
                let idx = match func_ranges.binary_search_by_key(&addr, |(s, _, _)| *s) {
                    Ok(i) => i,
                    Err(i) => i,
                };
                if idx > 0 {
                    let (start, end, func_name) = &func_ranges[idx - 1];
                    if addr >= *start && addr < *end {
                        *name = func_name.clone();
                    }
                }
            }
        }

        {
            let interior_elem_sizes: HashMap<usize, usize> = db
                .rel_iter::<(Ident, usize)>("interior_element_size")
                .map(|(ident, elem_size)| (*ident, *elem_size))
                .collect();
            let array_elem_sizes: HashMap<usize, usize> = db
                .rel_iter::<(Ident, usize, usize)>("is_global_array")
                .map(|(ident, elem_size, _count)| (*ident, *elem_size))
                .collect();
            for (interior_ident, base_name, offset) in db.rel_iter::<(Ident, Symbol, i64)>("emit_address_as_offset") {
                let maybe_base_ident = db
                    .rel_iter::<(Address, usize, Symbol)>("symbol_size")
                    .find(|(_, _, name)| *name == *base_name)
                    .map(|(addr, _, _)| *addr as usize);

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
        let raw_translation_unit = crate::decompile::passes::c_pass::convert::build_cast_from_relations(
            db,
            &selected_functions,
            &globals,
            &id_to_name,
            &edges,
        );

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
            let node_to_func: HashMap<u64, u64> = db
                .rel_iter::<(Node, Address)>("instr_in_function")
                .map(|(n, f)| (*n, *f))
                .collect();
            let called_addrs: HashSet<u64> = db
                .rel_iter::<(Address, Address)>("direct_call")
                .filter(|(caller, _)| {
                    node_to_func
                        .get(caller)
                        .map_or(false, |f| internal_addrs.contains(f))
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
                    let cstmt = crate::decompile::passes::c_pass::helpers::map_stmt_exprs(&cstmt, &|e| {
                        inline_rodata_constants(e, &rodata_const_map)
                    });
                    let cstmt = crate::decompile::passes::c_pass::convert::from_relations::narrow_varargs_in_stmt(&cstmt);
                    statements.push((node, cstmt));
                }
            }

            for (node, succs) in &func.successors {
                for succ in succs {
                    func_edges.push((*node, *succ));
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

            // TODO: wire up CsharpminorStmt structuring pass in the pipeline.
            all_statements.extend(statements);
            all_edges.extend(func_edges);
        }

        db.cast_selected_functions = internal_functions;
        db.cast_globals = globals;
        db.cast_id_to_name = id_to_name;
        db.cast_struct_layouts = struct_layouts;
        db.cast_var_types_for_emission = var_types_for_emission.clone();
        db.cast_raw_translation_unit = Some(raw_translation_unit);

        let struct_defs = crate::decompile::passes::clight_select::query::extract_struct_definitions(db);
        let stmt_map: HashMap<Node, CStmt> = all_statements.into_iter().collect();

        log::info!(
            "Building translation unit from {} statements",
            stmt_map.len()
        );

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

        // Identify opaque libc structs (FILE, DIR) via C AST scan and RTL-level analysis.
        let mut opaque_map = identify_opaque_libc_structs_from_tu(&tu);

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

        let opaque_struct_names: HashSet<String> = opaque_map.keys().cloned().collect();

        // Collect struct names referenced in emitted function bodies (field accesses, casts, etc.)
        let structs_referenced_in_code = collect_all_referenced_structs(&tu);

        // Build suppression map: opaque types -> typedef name, unreferenced auto-generated -> void.
        let mut suppressed_structs: HashMap<String, String> = opaque_map.clone();

        // Append struct defs, skipping opaque libc types and unreferenced auto-generated structs.
        for extracted in &struct_defs {
            if let Some(name) = &extracted.definition.name {
                if opaque_struct_names.contains(name) {
                    continue;
                }
                // Only suppress if: auto-generated fields AND not referenced in any emitted function.
                if !structs_referenced_in_code.contains(name) && all_fields_autogenerated(&extracted.definition) {
                    suppressed_structs.insert(name.clone(), "void".to_string());
                    continue;
                }
            }
            tu.decls.push(TopLevelDecl::StructDef(extracted.definition.clone()));
        }

        // Rewrite suppressed structs: opaque -> TypedefName, auto-generated -> Void.
        if !suppressed_structs.is_empty() {
            rewrite_opaque_types_in_tu(&mut tu, &suppressed_structs);
            for ty in db.cast_var_types_for_emission.values_mut() {
                *ty = rewrite_ctype(ty, &suppressed_structs);
            }
        }

        db.cast_optimized_translation_unit = Some(tu);
    }

    fn inputs(&self) -> &'static [&'static str] {
        &[
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
        ]
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
}

