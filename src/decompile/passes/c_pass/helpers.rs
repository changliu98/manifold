use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::c_pass::types::{
    CBlockItem, CExpr, CStmt, CType, ForInit, InitItem, Initializer,
    Label, VarDecl,
};
use crate::x86::types::*;
use std::collections::HashMap;
use std::collections::HashSet;


pub fn map_expr(e: &CExpr, f: &impl Fn(&CExpr) -> Option<CExpr>) -> CExpr {
    let transformed = match e {
        CExpr::Unary(op, inner) => CExpr::Unary(*op, Box::new(map_expr(inner, f))),
        CExpr::Binary(op, lhs, rhs) => {
            CExpr::Binary(*op, Box::new(map_expr(lhs, f)), Box::new(map_expr(rhs, f)))
        }
        CExpr::Assign(op, lhs, rhs) => {
            CExpr::Assign(*op, Box::new(map_expr(lhs, f)), Box::new(map_expr(rhs, f)))
        }
        CExpr::Ternary(c, t, e) => CExpr::Ternary(
            Box::new(map_expr(c, f)),
            Box::new(map_expr(t, f)),
            Box::new(map_expr(e, f)),
        ),
        CExpr::Call(func, args) => CExpr::Call(
            Box::new(map_expr(func, f)),
            args.iter().map(|a| map_expr(a, f)).collect(),
        ),
        CExpr::Index(arr, idx) => {
            CExpr::Index(Box::new(map_expr(arr, f)), Box::new(map_expr(idx, f)))
        }
        CExpr::Member(expr, field) => CExpr::Member(Box::new(map_expr(expr, f)), field.clone()),
        CExpr::MemberPtr(expr, field) => {
            CExpr::MemberPtr(Box::new(map_expr(expr, f)), field.clone())
        }
        CExpr::Cast(ty, expr) => CExpr::Cast(ty.clone(), Box::new(map_expr(expr, f))),
        CExpr::SizeofExpr(expr) => CExpr::SizeofExpr(Box::new(map_expr(expr, f))),
        CExpr::Paren(expr) => CExpr::Paren(Box::new(map_expr(expr, f))),
        _ => e.clone(),
    };

    f(&transformed).unwrap_or(transformed)
}

fn map_initializer(init: &Initializer, f: &impl Fn(&CExpr) -> Option<CExpr>) -> Initializer {
    match init {
        Initializer::Expr(e) => Initializer::Expr(map_expr(e, f)),
        Initializer::List(items) => Initializer::List(
            items
                .iter()
                .map(|item| InitItem {
                    designator: item.designator.clone(),
                    init: map_initializer(&item.init, f),
                })
                .collect(),
        ),
        Initializer::String(lit) => Initializer::String(lit.clone()),
    }
}

pub fn map_stmt_exprs(s: &CStmt, f: &impl Fn(&CExpr) -> Option<CExpr>) -> CStmt {
    match s {
        CStmt::Expr(e) => CStmt::Expr(map_expr(e, f)),
        CStmt::If(cond, then_s, else_s) => CStmt::If(
            map_expr(cond, f),
            Box::new(map_stmt_exprs(then_s, f)),
            else_s.as_ref().map(|s| Box::new(map_stmt_exprs(s, f))),
        ),
        CStmt::Switch(expr, body) => {
            CStmt::Switch(map_expr(expr, f), Box::new(map_stmt_exprs(body, f)))
        }
        CStmt::While(cond, body) => {
            CStmt::While(map_expr(cond, f), Box::new(map_stmt_exprs(body, f)))
        }
        CStmt::DoWhile(body, cond) => {
            CStmt::DoWhile(Box::new(map_stmt_exprs(body, f)), map_expr(cond, f))
        }
        CStmt::For(init, cond, update, body) => {
            let new_init = match init {
                Some(ForInit::Expr(e)) => {
                    Some(ForInit::Expr(map_expr(e, f)))
                }
                _ => init.clone(),
            };
            let new_cond = cond.as_ref().map(|e| map_expr(e, f));
            let new_update = update.as_ref().map(|e| map_expr(e, f));
            CStmt::For(
                new_init,
                new_cond,
                new_update,
                Box::new(map_stmt_exprs(body, f)),
            )
        }
        CStmt::Return(Some(e)) => CStmt::Return(Some(map_expr(e, f))),
        CStmt::Block(items) => CStmt::Block(
            items
                .iter()
                .map(|item| match item {
                    CBlockItem::Stmt(stmt) => CBlockItem::Stmt(map_stmt_exprs(stmt, f)),
                    CBlockItem::Decl(decls) => CBlockItem::Decl(
                        decls
                            .iter()
                            .map(|d| VarDecl {
                                init: d.init.as_ref().map(|init| map_initializer(init, f)),
                                ..d.clone()
                            })
                            .collect(),
                    ),
                })
                .collect(),
        ),
        CStmt::Sequence(stmts) => CStmt::Sequence(
            stmts.iter().map(|s| map_stmt_exprs(s, f)).collect(),
        ),
        CStmt::Labeled(label, inner) => CStmt::Labeled(
            label.clone(),
            Box::new(map_stmt_exprs(inner, f)),
        ),
        _ => s.clone(),
    }
}


pub fn collect_goto_targets(stmt: &CStmt) -> Vec<String> {
    let mut targets = Vec::new();
    collect_goto_targets_inner(stmt, &mut targets);
    targets
}

fn collect_goto_targets_inner(stmt: &CStmt, targets: &mut Vec<String>) {
    match stmt {
        CStmt::Goto(lbl) => targets.push(lbl.clone()),
        CStmt::Expr(e) => collect_gotos_from_expr(e, targets),
        CStmt::Return(Some(e)) => collect_gotos_from_expr(e, targets),
        CStmt::Block(items) => {
            for item in items {
                match item {
                    CBlockItem::Stmt(s) => collect_goto_targets_inner(s, targets),
                    CBlockItem::Decl(decls) => {
                        for d in decls {
                            if let Some(init) = &d.init {
                                collect_gotos_from_initializer(init, targets);
                            }
                        }
                    }
                }
            }
        }
        CStmt::If(cond, then_br, else_br) => {
            collect_gotos_from_expr(cond, targets);
            collect_goto_targets_inner(then_br, targets);
            if let Some(e) = else_br {
                collect_goto_targets_inner(e, targets);
            }
        }
        CStmt::While(cond, body) => {
            collect_gotos_from_expr(cond, targets);
            collect_goto_targets_inner(body, targets);
        }
        CStmt::DoWhile(body, cond) => {
            collect_gotos_from_expr(cond, targets);
            collect_goto_targets_inner(body, targets);
        }
        CStmt::For(init, cond, update, body) => {
            if let Some(init_part) = init {
                match init_part {
                    ForInit::Expr(e) => collect_gotos_from_expr(e, targets),
                    ForInit::Decl(decls) => {
                        for d in decls {
                            if let Some(init) = &d.init {
                                collect_gotos_from_initializer(init, targets);
                            }
                        }
                    }
                }
            }
            if let Some(c) = cond {
                collect_gotos_from_expr(c, targets);
            }
            if let Some(u) = update {
                collect_gotos_from_expr(u, targets);
            }
            collect_goto_targets_inner(body, targets);
        }
        CStmt::Switch(expr, body) => {
            collect_gotos_from_expr(expr, targets);
            collect_goto_targets_inner(body, targets);
        }
        CStmt::Labeled(Label::Case(e), inner) => {
            collect_gotos_from_expr(e, targets);
            collect_goto_targets_inner(inner, targets);
        }
        CStmt::Labeled(_, inner) => collect_goto_targets_inner(inner, targets),
        CStmt::Sequence(stmts) => {
            for s in stmts {
                collect_goto_targets_inner(s, targets);
            }
        }
        _ => {}
    }
}

fn collect_gotos_from_expr(expr: &CExpr, targets: &mut Vec<String>) {
    match expr {
        CExpr::StmtExpr(stmts, final_expr) => {
            for s in stmts {
                collect_goto_targets_inner(s, targets);
            }
            collect_gotos_from_expr(final_expr, targets);
        }
        CExpr::Unary(_, inner) | CExpr::Cast(_, inner) | CExpr::SizeofExpr(inner) | CExpr::Paren(inner) => {
            collect_gotos_from_expr(inner, targets);
        }
        CExpr::AlignofType(_) => {}
        CExpr::Binary(_, l, r) | CExpr::Assign(_, l, r) | CExpr::Index(l, r) => {
            collect_gotos_from_expr(l, targets);
            collect_gotos_from_expr(r, targets);
        }
        CExpr::Ternary(c, t, e) => {
            collect_gotos_from_expr(c, targets);
            collect_gotos_from_expr(t, targets);
            collect_gotos_from_expr(e, targets);
        }
        CExpr::Call(func, args) => {
            collect_gotos_from_expr(func, targets);
            for arg in args {
                collect_gotos_from_expr(arg, targets);
            }
        }
        CExpr::Member(inner, _) | CExpr::MemberPtr(inner, _) => {
            collect_gotos_from_expr(inner, targets);
        }
        CExpr::CompoundLit(_, inits) => {
            for init in inits {
                collect_gotos_from_initializer(init, targets);
            }
        }
        CExpr::Generic(expr, associations) => {
            collect_gotos_from_expr(expr, targets);
            for (_, assoc_expr) in associations {
                collect_gotos_from_expr(assoc_expr, targets);
            }
        }
        _ => {}
    }
}

fn collect_gotos_from_initializer(init: &Initializer, targets: &mut Vec<String>) {
    match init {
        Initializer::Expr(e) => collect_gotos_from_expr(e, targets),
        Initializer::List(items) => {
            for item in items {
                collect_gotos_from_initializer(&item.init, targets);
            }
        }
        _ => {}
    }
}


pub fn strip_dead_labels(stmt: &CStmt, dead_labels: &HashSet<String>) -> CStmt {
    match stmt {
        CStmt::Labeled(Label::Named(lbl), inner) if dead_labels.contains(lbl) => {
            strip_dead_labels(inner, dead_labels)
        }
        CStmt::Labeled(label, inner) => CStmt::Labeled(
            label.clone(),
            Box::new(strip_dead_labels(inner, dead_labels)),
        ),
        CStmt::Block(items) => CStmt::Block(
            items
                .iter()
                .map(|item| match item {
                    CBlockItem::Stmt(s) => CBlockItem::Stmt(strip_dead_labels(s, dead_labels)),
                    other => other.clone(),
                })
                .collect(),
        ),
        CStmt::If(cond, then_br, else_br) => CStmt::If(
            cond.clone(),
            Box::new(strip_dead_labels(then_br, dead_labels)),
            else_br
                .as_ref()
                .map(|e| Box::new(strip_dead_labels(e, dead_labels))),
        ),
        CStmt::While(cond, body) => {
            CStmt::While(cond.clone(), Box::new(strip_dead_labels(body, dead_labels)))
        }
        CStmt::DoWhile(body, cond) => {
            CStmt::DoWhile(Box::new(strip_dead_labels(body, dead_labels)), cond.clone())
        }
        CStmt::For(init, cond, update, body) => CStmt::For(
            init.clone(),
            cond.clone(),
            update.clone(),
            Box::new(strip_dead_labels(body, dead_labels)),
        ),
        CStmt::Switch(expr, body) => {
            CStmt::Switch(expr.clone(), Box::new(strip_dead_labels(body, dead_labels)))
        }
        CStmt::Sequence(stmts) => CStmt::Sequence(
            stmts
                .iter()
                .map(|s| strip_dead_labels(s, dead_labels))
                .collect(),
        ),
        other => other.clone(),
    }
}


pub fn collect_all_labels(stmt: &CStmt) -> Vec<String> {
    let mut out = Vec::new();
    collect_all_labels_rec(stmt, &mut out);
    out
}

fn collect_all_labels_rec(stmt: &CStmt, out: &mut Vec<String>) {
    if let CStmt::Labeled(Label::Named(lbl), inner) = stmt {
        out.push(lbl.clone());
        collect_all_labels_rec(inner, out);
        return;
    }

    match stmt {
        CStmt::Block(items) => {
            for item in items {
                if let CBlockItem::Stmt(s) = item {
                    collect_all_labels_rec(s, out);
                }
            }
        }
        CStmt::If(_, t, e) => {
            collect_all_labels_rec(t, out);
            if let Some(e) = e {
                collect_all_labels_rec(e, out);
            }
        }
        CStmt::While(_, b) | CStmt::DoWhile(b, _) => collect_all_labels_rec(b, out),
        CStmt::For(_, _, _, b) => collect_all_labels_rec(b, out),
        CStmt::Switch(_, b) => collect_all_labels_rec(b, out),
        CStmt::Sequence(stmts) => {
            for s in stmts {
                collect_all_labels_rec(s, out);
            }
        }
        _ => {}
    }
}


pub fn flatten_blocks_and_cleanup(stmt: &CStmt) -> CStmt {
    match stmt {
        CStmt::Block(items) => {
            let cleaned_items: Vec<CBlockItem> = items
                .iter()
                .filter_map(|item| match item {
                    CBlockItem::Stmt(s) => {
                        let cleaned = flatten_blocks_and_cleanup(s);
                        if matches!(cleaned, CStmt::Empty) {
                            None
                        } else {
                            Some(CBlockItem::Stmt(cleaned))
                        }
                    }
                    CBlockItem::Decl(decls) => {
                        Some(CBlockItem::Decl(decls.clone()))
                    }
                })
                .collect();

            let flattened_items: Vec<CBlockItem> = cleaned_items
                .into_iter()
                .flat_map(|item| match item {
                    CBlockItem::Stmt(CStmt::Block(inner_items)) => {
                        let has_decls =
                            inner_items.iter().any(|i| matches!(i, CBlockItem::Decl(_)));
                        if has_decls {
                            vec![CBlockItem::Stmt(CStmt::Block(inner_items))]
                        } else {
                            inner_items
                        }
                    }
                    other => vec![other],
                })
                .collect();

            match flattened_items.len() {
                0 => CStmt::Empty,
                1 => {
                    match &flattened_items[0] {
                        CBlockItem::Stmt(s) => s.clone(),
                        CBlockItem::Decl(_) => CStmt::Block(flattened_items),
                    }
                }
                _ => CStmt::Block(flattened_items),
            }
        }

        CStmt::If(cond, then_stmt, else_stmt) => {
            let cleaned_then = flatten_blocks_and_cleanup(then_stmt);
            let cleaned_else = else_stmt
                .as_ref()
                .map(|e| Box::new(flatten_blocks_and_cleanup(e)));

            if matches!(cleaned_then, CStmt::Empty)
                && cleaned_else
                    .as_ref()
                    .map_or(true, |e| matches!(**e, CStmt::Empty))
            {
                return CStmt::Empty;
            }

            CStmt::If(cond.clone(), Box::new(cleaned_then), cleaned_else)
        }

        CStmt::While(cond, body) => {
            let cleaned_body = flatten_blocks_and_cleanup(body);
            CStmt::While(cond.clone(), Box::new(cleaned_body))
        }

        CStmt::DoWhile(body, cond) => {
            let cleaned_body = flatten_blocks_and_cleanup(body);
            CStmt::DoWhile(Box::new(cleaned_body), cond.clone())
        }

        CStmt::For(init, cond, update, body) => {
            let cleaned_body = flatten_blocks_and_cleanup(body);
            CStmt::For(
                init.clone(),
                cond.clone(),
                update.clone(),
                Box::new(cleaned_body),
            )
        }

        CStmt::Switch(expr, body) => {
            let cleaned_body = flatten_blocks_and_cleanup(body);
            CStmt::Switch(expr.clone(), Box::new(cleaned_body))
        }

        CStmt::Labeled(label, inner) => {
            let cleaned_inner = flatten_blocks_and_cleanup(inner);
            CStmt::Labeled(label.clone(), Box::new(cleaned_inner))
        }

        other => other.clone(),
    }
}

pub fn param_name_for_reg(reg: crate::x86::types::RTLReg) -> String {
    let ident = crate::x86::types::ident_from_reg(reg);
    format!("var_{}", ident)
}

pub fn convert_param_type_from_param(
    param: &crate::x86::types::ParamType,
) -> CType {
    match param {
        crate::x86::types::ParamType::StructPointer(struct_id) => {
            let struct_name = format!("struct_{:x}", struct_id);
            CType::ptr(CType::Struct(struct_name))
        }
        crate::x86::types::ParamType::Pointer => {
            CType::ptr(CType::Void)
        }
        crate::x86::types::ParamType::Typed(xtype) => match xtype {
            crate::x86::types::XType::Xvoid => CType::Void,
            crate::x86::types::XType::Xint8signed => CType::char_signed(),
            crate::x86::types::XType::Xint8unsigned => CType::char_unsigned(),
            crate::x86::types::XType::Xint16signed => {
                CType::Int(crate::decompile::passes::c_pass::types::IntSize::Short, crate::decompile::passes::c_pass::types::Signedness::Signed)
            }
            crate::x86::types::XType::Xint16unsigned => {
                CType::Int(crate::decompile::passes::c_pass::types::IntSize::Short, crate::decompile::passes::c_pass::types::Signedness::Unsigned)
            }
            crate::x86::types::XType::Xint | crate::x86::types::XType::Xany32 => CType::int(),
            crate::x86::types::XType::Xintunsigned => CType::uint(),
            crate::x86::types::XType::Xlong | crate::x86::types::XType::Xany64 => CType::long(),
            crate::x86::types::XType::Xlongunsigned => CType::ulong(),
            crate::x86::types::XType::Xptr => CType::ptr(CType::Void),
            crate::x86::types::XType::Xcharptr => CType::ptr(CType::char_signed()),
            crate::x86::types::XType::Xintptr => CType::ptr(CType::int()),
            crate::x86::types::XType::Xfloatptr => CType::ptr(CType::double()),
            crate::x86::types::XType::Xsingleptr => CType::ptr(CType::float()),
            crate::x86::types::XType::Xfuncptr => CType::ptr(CType::Function(Box::new(CType::Void), Vec::new(), false)),
            crate::x86::types::XType::Xfloat => CType::double(),
            crate::x86::types::XType::Xsingle => CType::float(),
            crate::x86::types::XType::Xbool => CType::Bool,
            crate::x86::types::XType::XstructPtr(struct_id) => {
                let struct_name = format!("struct_{:x}", struct_id);
                CType::ptr(CType::Struct(struct_name))
            }
        },
        crate::x86::types::ParamType::Integer | crate::x86::types::ParamType::Unknown => {
            CType::int()
        }
    }
}

pub fn xtype_string_to_ctype(type_str: &str) -> CType {
    use crate::decompile::passes::c_pass::types::{IntSize, FloatSize, Signedness};

    if type_str.starts_with("ptr_struct_") {
        let struct_name = format!("struct_{}", &type_str["ptr_struct_".len()..]);
        return CType::Pointer(
            Box::new(CType::Struct(struct_name)),
            crate::decompile::passes::c_pass::types::TypeQualifiers::none(),
        );
    }

    match type_str {
        "int_IBool" => CType::Bool,
        "int_I8" => CType::Int(IntSize::Char, Signedness::Signed),
        "int_I8_unsigned" => CType::Int(IntSize::Char, Signedness::Unsigned),
        "int_I16" => CType::Int(IntSize::Short, Signedness::Signed),
        "int_I16_unsigned" => CType::Int(IntSize::Short, Signedness::Unsigned),
        "int_I32" => CType::Int(IntSize::Int, Signedness::Signed),
        "int_I32_unsigned" => CType::Int(IntSize::Int, Signedness::Unsigned),
        "int_I64" => CType::Int(IntSize::Long, Signedness::Signed),
        "int_I64_unsigned" => CType::Int(IntSize::Long, Signedness::Unsigned),
        "float_F32" => CType::Float(FloatSize::Float),
        "float_F64" => CType::Float(FloatSize::Double),
        "ptr_I64" => CType::Pointer(Box::new(CType::long()), crate::decompile::passes::c_pass::types::TypeQualifiers::none()),
        "ptr_char" => CType::Pointer(Box::new(CType::char_signed()), crate::decompile::passes::c_pass::types::TypeQualifiers::none()),
        "ptr_int" => CType::Pointer(Box::new(CType::int()), crate::decompile::passes::c_pass::types::TypeQualifiers::none()),
        "ptr_double" => CType::Pointer(Box::new(CType::double()), crate::decompile::passes::c_pass::types::TypeQualifiers::none()),
        "ptr_float" => CType::Pointer(Box::new(CType::float()), crate::decompile::passes::c_pass::types::TypeQualifiers::none()),
        "ptr_func" => CType::Pointer(Box::new(CType::Function(Box::new(CType::Void), Vec::new(), false)), crate::decompile::passes::c_pass::types::TypeQualifiers::none()),
        "void" => CType::Void,
        _ => CType::Int(IntSize::Long, Signedness::Signed),
    }
}

pub fn build_string_literal_map(db: &DecompileDB) -> HashMap<String, String> {
    let mut map = HashMap::new();
    for (label, content, _size) in db.rel_iter::<(String, String, usize)>("string_data") {
        map.insert(label.clone(), content.clone());
        map.insert(format!(".{}", label), content.clone());
    }

    let mut string_ranges: Vec<(u64, &str)> = Vec::new();
    for (label, content, _size) in db.rel_iter::<(String, String, usize)>("string_data") {
        if let Some(hex) = label.strip_prefix("L_").or_else(|| label.strip_prefix(".L_")) {
            if let Ok(addr) = u64::from_str_radix(hex, 16) {
                string_ranges.push((addr, content.as_str()));
            }
        }
    }
    string_ranges.sort_by_key(|(addr, _)| *addr);

    if !string_ranges.is_empty() {
        let mut label_addrs: Vec<(&str, u64)> = Vec::new();
        for (ident, symbol) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
            label_addrs.push((*symbol, *ident as u64));
        }
        for (addr, name, _) in db.rel_iter::<(crate::x86::types::Address, crate::x86::types::Symbol, crate::x86::types::Symbol)>("symbols") {
            label_addrs.push((*name, *addr));
        }
        for (label, addr) in &label_addrs {
            if !label.starts_with("L_") && !label.starts_with(".L_") && !label.starts_with("data_") {
                continue;
            }
            if map.contains_key(*label) {
                continue;
            }
            let idx = string_ranges.partition_point(|(start, _)| *start <= *addr);
            if idx > 0 {
                let (start, content) = &string_ranges[idx - 1];
                let offset = (*addr - start) as usize;
                if offset > 0 && offset < content.len() && content.is_char_boundary(offset) {
                    let substring = &content[offset..];
                    map.insert(label.to_string(), substring.to_string());
                    map.insert(format!(".{}", label), substring.to_string());
                }
            }
        }
    }

    map
}

pub fn inline_string_literals(expr: &CExpr, string_map: &HashMap<String, String>) -> Option<CExpr> {
    use crate::decompile::passes::c_pass::types::UnaryOp;

    if let CExpr::Unary(UnaryOp::AddrOf, inner) = expr {
        if let CExpr::Var(name) = inner.as_ref() {
            if let Some(str_content) = string_map.get(name) {
                return Some(CExpr::StringLit(crate::decompile::passes::c_pass::types::StringLiteral {
                    value: str_content.clone(),
                    is_wide: false,
                }));
            }
        }
        if let CExpr::StringLit(_) = inner.as_ref() {
            return Some(inner.as_ref().clone());
        }
    }

    if let CExpr::Cast(ty, inner) = expr {
        if let CExpr::Var(name) = inner.as_ref() {
            if let Some(str_content) = string_map.get(name) {
                if matches!(ty, CType::Pointer(_, _)) || is_char_pointer_type(ty) {
                    return Some(CExpr::StringLit(crate::decompile::passes::c_pass::types::StringLiteral {
                        value: str_content.clone(),
                        is_wide: false,
                    }));
                }
            }
        }
        if let CExpr::Var(name) = inner.as_ref() {
            if let Some(str_content) = string_map.get(name) {
                if matches!(ty, CType::Int(crate::decompile::passes::c_pass::types::IntSize::Long, _)) {
                    return Some(CExpr::StringLit(crate::decompile::passes::c_pass::types::StringLiteral {
                        value: str_content.clone(),
                        is_wide: false,
                    }));
                }
            }
        }
        if let CExpr::Unary(UnaryOp::AddrOf, addr_inner) = inner.as_ref() {
            if let CExpr::Var(name) = addr_inner.as_ref() {
                if let Some(str_content) = string_map.get(name) {
                    return Some(CExpr::StringLit(crate::decompile::passes::c_pass::types::StringLiteral {
                        value: str_content.clone(),
                        is_wide: false,
                    }));
                }
            }
            if let CExpr::StringLit(lit) = addr_inner.as_ref() {
                return Some(CExpr::StringLit(lit.clone()));
            }
        }
        if let CExpr::StringLit(lit) = inner.as_ref() {
            return Some(CExpr::StringLit(lit.clone()));
        }
    }

    if let CExpr::Var(name) = expr {
        if let Some(str_content) = string_map.get(name) {
            if name.starts_with(".L_") || name.starts_with("L_") {
                return Some(CExpr::StringLit(crate::decompile::passes::c_pass::types::StringLiteral {
                    value: str_content.clone(),
                    is_wide: false,
                }));
            }
        }
    }

    None
}

pub fn inline_rodata_constants(expr: &CExpr, const_map: &HashMap<String, CExpr>) -> Option<CExpr> {
    if let CExpr::Var(name) = expr {
        if let Some(replacement) = const_map.get(name) {
            return Some(replacement.clone());
        }
    }
    None
}

pub fn is_char_pointer_type(ty: &CType) -> bool {
    use crate::decompile::passes::c_pass::types::IntSize;
    matches!(ty,
        CType::Pointer(inner, _) if matches!(inner.as_ref(),
            CType::Int(IntSize::Char, _) | CType::Void
        )
    )
}

pub fn extract_named_label(stmt: &CStmt) -> Option<String> {
    match stmt {
        CStmt::Labeled(Label::Named(name), _) => Some(name.clone()),
        _ => None,
    }
}

pub fn collect_goto_label_targets(stmt: &CStmt, targets: &mut Vec<String>) {
    match stmt {
        CStmt::Goto(label) => targets.push(label.clone()),
        CStmt::Labeled(_, inner) => collect_goto_label_targets(inner, targets),
        CStmt::Sequence(stmts) => {
            for s in stmts {
                collect_goto_label_targets(s, targets);
            }
        }
        CStmt::Block(items) => {
            for item in items {
                if let CBlockItem::Stmt(s) = item {
                    collect_goto_label_targets(s, targets);
                }
            }
        }
        CStmt::If(_, then_s, else_s) => {
            collect_goto_label_targets(then_s, targets);
            if let Some(e) = else_s {
                collect_goto_label_targets(e, targets);
            }
        }
        CStmt::Switch(_, body) => collect_goto_label_targets(body, targets),
        _ => {}
    }
}

pub fn is_terminal_cstmt(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Return(_) => true,
        CStmt::Goto(_) => true,
        CStmt::Break => true,
        CStmt::Continue => true,
        CStmt::Labeled(_, inner) => is_terminal_cstmt(inner),
        CStmt::If(_, _, _) => true,
        CStmt::Switch(_, _) => true,
        CStmt::While(_, _) | CStmt::DoWhile(_, _) | CStmt::For(_, _, _, _) => true,
        _ => false,
    }
}
