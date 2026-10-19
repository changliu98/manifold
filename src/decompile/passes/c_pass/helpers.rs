use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::c_pass::types::{
    CBlockItem, CExpr, CStmt, CType, Designator, ForInit, InitItem, Initializer, Label, VarDecl,
};
use crate::decompile::passes::clight_select::candtype::CandType;
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
        CExpr::CompoundLit(ty, initializers) => CExpr::CompoundLit(
            ty.clone(),
            initializers
                .iter()
                .map(|init| map_initializer(init, f))
                .collect(),
        ),
        CExpr::Generic(selector, arms) => CExpr::Generic(
            Box::new(map_expr(selector, f)),
            arms.iter()
                .map(|(ty, arm)| (ty.clone(), map_expr(arm, f)))
                .collect(),
        ),
        CExpr::StmtExpr(stmts, tail) => CExpr::StmtExpr(
            stmts.iter().map(|stmt| map_stmt_exprs(stmt, f)).collect(),
            Box::new(map_expr(tail, f)),
        ),
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
                    designator: item
                        .designator
                        .as_ref()
                        .map(|designator| map_designator(designator, f)),
                    init: map_initializer(&item.init, f),
                })
                .collect(),
        ),
        Initializer::String(lit) => Initializer::String(lit.clone()),
    }
}

fn map_designator(designator: &Designator, f: &impl Fn(&CExpr) -> Option<CExpr>) -> Designator {
    match designator {
        Designator::Field(field) => Designator::Field(field.clone()),
        Designator::Index(expr) => Designator::Index(map_expr(expr, f)),
        Designator::Range(first, last) => Designator::Range(map_expr(first, f), map_expr(last, f)),
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
                Some(ForInit::Expr(e)) => Some(ForInit::Expr(map_expr(e, f))),
                Some(ForInit::Decl(decls)) => Some(ForInit::Decl(
                    decls
                        .iter()
                        .map(|decl| VarDecl {
                            init: decl.init.as_ref().map(|init| map_initializer(init, f)),
                            ..decl.clone()
                        })
                        .collect(),
                )),
                None => None,
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
        CStmt::Sequence(stmts) => {
            CStmt::Sequence(stmts.iter().map(|s| map_stmt_exprs(s, f)).collect())
        }
        CStmt::Labeled(label, inner) => CStmt::Labeled(
            match label {
                Label::Case(expr) => Label::Case(map_expr(expr, f)),
                _ => label.clone(),
            },
            Box::new(map_stmt_exprs(inner, f)),
        ),
        CStmt::Effect(site, inner) =>
            CStmt::Effect(*site, Box::new(map_stmt_exprs(inner, f))),
        CStmt::Decl(decls) => CStmt::Decl(
            decls
                .iter()
                .map(|decl| VarDecl {
                    init: decl.init.as_ref().map(|init| map_initializer(init, f)),
                    ..decl.clone()
                })
                .collect(),
        ),
        _ => s.clone(),
    }
}

// Stmt-level version of `inline_rodata_constants_preserving_addrof`. Identical structure to `map_stmt_exprs` but applies the AddrOf-aware top-down rewrite to every contained CExpr in one pass.
pub fn map_stmt_exprs_total(s: &CStmt, f: &impl Fn(&CExpr) -> CExpr) -> CStmt {
    match s {
        CStmt::Expr(e) => CStmt::Expr(f(e)),
        CStmt::If(cond, then_s, else_s) => CStmt::If(
            f(cond),
            Box::new(map_stmt_exprs_total(then_s, f)),
            else_s
                .as_ref()
                .map(|s| Box::new(map_stmt_exprs_total(s, f))),
        ),
        CStmt::Switch(expr, body) => {
            CStmt::Switch(f(expr), Box::new(map_stmt_exprs_total(body, f)))
        }
        CStmt::While(cond, body) => CStmt::While(f(cond), Box::new(map_stmt_exprs_total(body, f))),
        CStmt::DoWhile(body, cond) => {
            CStmt::DoWhile(Box::new(map_stmt_exprs_total(body, f)), f(cond))
        }
        CStmt::For(init, cond, update, body) => {
            let new_init = match init {
                Some(ForInit::Expr(e)) => Some(ForInit::Expr(f(e))),
                Some(ForInit::Decl(decls)) => Some(ForInit::Decl(
                    decls
                        .iter()
                        .map(|decl| VarDecl {
                            init: decl
                                .init
                                .as_ref()
                                .map(|init| map_initializer_total(init, f)),
                            ..decl.clone()
                        })
                        .collect(),
                )),
                None => None,
            };
            let new_cond = cond.as_ref().map(|e| f(e));
            let new_update = update.as_ref().map(|e| f(e));
            CStmt::For(
                new_init,
                new_cond,
                new_update,
                Box::new(map_stmt_exprs_total(body, f)),
            )
        }
        CStmt::Return(Some(e)) => CStmt::Return(Some(f(e))),
        CStmt::Block(items) => CStmt::Block(
            items
                .iter()
                .map(|item| match item {
                    CBlockItem::Stmt(stmt) => CBlockItem::Stmt(map_stmt_exprs_total(stmt, f)),
                    CBlockItem::Decl(decls) => CBlockItem::Decl(
                        decls
                            .iter()
                            .map(|d| VarDecl {
                                init: d.init.as_ref().map(|init| map_initializer_total(init, f)),
                                ..d.clone()
                            })
                            .collect(),
                    ),
                })
                .collect(),
        ),
        CStmt::Sequence(stmts) => {
            CStmt::Sequence(stmts.iter().map(|s| map_stmt_exprs_total(s, f)).collect())
        }
        CStmt::Labeled(label, inner) => CStmt::Labeled(
            match label {
                Label::Case(expr) => Label::Case(f(expr)),
                _ => label.clone(),
            },
            Box::new(map_stmt_exprs_total(inner, f)),
        ),
        CStmt::Effect(site, inner) =>
            CStmt::Effect(*site, Box::new(map_stmt_exprs_total(inner, f))),
        CStmt::Decl(decls) => CStmt::Decl(
            decls
                .iter()
                .map(|decl| VarDecl {
                    init: decl
                        .init
                        .as_ref()
                        .map(|init| map_initializer_total(init, f)),
                    ..decl.clone()
                })
                .collect(),
        ),
        _ => s.clone(),
    }
}

fn map_initializer_total(init: &Initializer, f: &impl Fn(&CExpr) -> CExpr) -> Initializer {
    match init {
        Initializer::Expr(e) => Initializer::Expr(f(e)),
        Initializer::List(items) => Initializer::List(
            items
                .iter()
                .map(|item| InitItem {
                    designator: item
                        .designator
                        .as_ref()
                        .map(|designator| map_designator_total(designator, f)),
                    init: map_initializer_total(&item.init, f),
                })
                .collect(),
        ),
        Initializer::String(lit) => Initializer::String(lit.clone()),
    }
}

fn map_designator_total(designator: &Designator, f: &impl Fn(&CExpr) -> CExpr) -> Designator {
    match designator {
        Designator::Field(field) => Designator::Field(field.clone()),
        Designator::Index(expr) => Designator::Index(f(expr)),
        Designator::Range(first, last) => Designator::Range(f(first), f(last)),
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
        CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)  => collect_goto_targets_inner(inner, targets),
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
        CExpr::Unary(_, inner)
        | CExpr::Cast(_, inner)
        | CExpr::SizeofExpr(inner)
        | CExpr::Paren(inner) => {
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
        CStmt::Effect(label, inner) => CStmt::Effect(
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
                    CBlockItem::Decl(decls) => Some(CBlockItem::Decl(decls.clone())),
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
                1 => match &flattened_items[0] {
                    CBlockItem::Stmt(s) => s.clone(),
                    CBlockItem::Decl(_) => CStmt::Block(flattened_items),
                },
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
        CStmt::Effect(label, inner) => {
            let cleaned_inner = flatten_blocks_and_cleanup(inner);
            CStmt::Effect(label.clone(), Box::new(cleaned_inner))
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
    model: crate::abi::DataModel,
) -> CType {
    match param {
        crate::x86::types::ParamType::StructPointer(struct_id) => {
            let struct_name = format!("struct_{:x}", struct_id);
            CType::ptr(CType::Struct(struct_name))
        }
        crate::x86::types::ParamType::Pointer => CType::ptr(CType::Void),
        crate::x86::types::ParamType::Typed(xtype) => match xtype {
            crate::x86::types::XType::Xvoid => CType::Void,
            crate::x86::types::XType::Xint8signed => CType::char_signed(),
            crate::x86::types::XType::Xint8unsigned => CType::char_unsigned(),
            crate::x86::types::XType::Xint16signed => CType::Int(
                crate::decompile::passes::c_pass::types::IntSize::Short,
                crate::decompile::passes::c_pass::types::Signedness::Signed,
            ),
            crate::x86::types::XType::Xint16unsigned => CType::Int(
                crate::decompile::passes::c_pass::types::IntSize::Short,
                crate::decompile::passes::c_pass::types::Signedness::Unsigned,
            ),
            crate::x86::types::XType::Xint | crate::x86::types::XType::Xany32 => CType::int(),
            crate::x86::types::XType::Xintunsigned => CType::uint(),
            // Xlong is the C type `long`; Xany64 is merely a 64-bit value and
            // needs the model's spelling for one.  Merging them declared every
            // 64-bit value `long`, which is 32 bits wide off LP64.
            crate::x86::types::XType::Xlong => CType::long(),
            crate::x86::types::XType::Xany64 => CType::int64(
                model,
                crate::decompile::passes::c_pass::types::Signedness::Signed,
            ),
            crate::x86::types::XType::Xlongunsigned => CType::ulong(),
            crate::x86::types::XType::Xptr => CType::ptr(CType::Void),
            crate::x86::types::XType::Xcharptr => CType::ptr(CType::char_signed()),
            crate::x86::types::XType::Xcharptrptr => CType::ptr(CType::ptr(CType::char_signed())),
            crate::x86::types::XType::Xintptr => CType::ptr(CType::int()),
            crate::x86::types::XType::Xfloatptr => CType::ptr(CType::double()),
            crate::x86::types::XType::Xsingleptr => CType::ptr(CType::float()),
            crate::x86::types::XType::Xfuncptr => CType::ptr(CType::Function(
                Box::new(CType::Void),
                Vec::new(),
                false,
                false,
            )),
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

/// Candidate type -> CType for declaration emission. Total, with no fallback arm: the string match
/// this replaced had none for `ptr_ptr_char`, so a `char **` register was declared `long`.
pub fn candtype_to_ctype(candidate: CandType, model: crate::abi::DataModel) -> CType {
    use crate::decompile::passes::c_pass::types::{FloatSize, IntSize, Signedness, TypeQualifiers};
    use crate::decompile::passes::clight_select::candtype::Sign;

    let ptr = |inner: CType| CType::Pointer(Box::new(inner), TypeQualifiers::none());
    let signedness = |sign: Sign| match sign {
        Sign::Signed => Signedness::Signed,
        Sign::Unsigned => Signedness::Unsigned,
    };
    match candidate {
        CandType::Void => CType::Void,
        CandType::Bool => CType::Bool,
        CandType::I8(sign) => CType::Int(IntSize::Char, signedness(sign)),
        CandType::I16(sign) => CType::Int(IntSize::Short, signedness(sign)),
        CandType::I32(sign) => CType::Int(IntSize::Int, signedness(sign)),
        CandType::I64(sign) => CType::int64(model, signedness(sign)),
        CandType::F32 => CType::Float(FloatSize::Float),
        CandType::F64 => CType::Float(FloatSize::Double),
        CandType::PtrLong => ptr(CType::long()),
        CandType::PtrVoid => ptr(CType::Void),
        CandType::PtrChar => ptr(CType::char_signed()),
        CandType::PtrCharPtr => ptr(ptr(CType::char_signed())),
        CandType::PtrInt => ptr(CType::int()),
        CandType::PtrDouble => ptr(CType::double()),
        CandType::PtrFloat => ptr(CType::float()),
        CandType::PtrFunc => ptr(CType::Function(
            Box::new(CType::Void),
            Vec::new(),
            false,
            false,
        )),
        CandType::PtrStruct(sid) => ptr(CType::Struct(format!("struct_{:x}", sid))),
    }
}

/// Labels whose exact storage address is read by a scalar floating-point
/// instruction.  The instruction supplies stronger evidence than the generic
/// NUL-terminated byte scan: any finite bit pattern beginning with a nonzero
/// byte and then zero can otherwise be mistaken for a short string.
pub fn rodata_fp_constant_labels(db: &DecompileDB) -> HashSet<String> {
    let fp_addrs: HashSet<u64> = db
        .rel_iter::<(u64, usize, u64)>("rodata_fp_const")
        .map(|(addr, _, _)| *addr)
        .collect();
    let mut labels = HashSet::new();

    let mut insert_variants = |label: &str| {
        labels.insert(label.to_string());
        if let Some(unprefixed) = label.strip_prefix('.') {
            labels.insert(unprefixed.to_string());
        } else {
            labels.insert(format!(".{label}"));
        }
    };

    for addr in &fp_addrs {
        insert_variants(&format!("L_{addr:x}"));
    }
    for (ident, symbol) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
        if fp_addrs.contains(&(*ident as u64)) {
            insert_variants(symbol);
        }
    }
    for (addr, name, _) in db.rel_iter::<(
        crate::x86::types::Address,
        crate::x86::types::Symbol,
        crate::x86::types::Symbol,
    )>("symbols")
    {
        if fp_addrs.contains(addr) {
            insert_variants(name);
        }
    }
    labels
}

pub fn build_string_literal_map(db: &DecompileDB) -> HashMap<String, String> {
    let fp_labels = rodata_fp_constant_labels(db);
    let mut map = HashMap::new();
    for (label, content, _size) in db.rel_iter::<(String, String, usize)>("string_data") {
        if fp_labels.contains(label) {
            continue;
        }
        map.insert(label.clone(), content.clone());
        map.insert(format!(".{}", label), content.clone());
    }

    let mut string_ranges: Vec<(u64, &str)> = Vec::new();
    for (label, content, _size) in db.rel_iter::<(String, String, usize)>("string_data") {
        if fp_labels.contains(label) {
            continue;
        }
        if let Some(hex) = label
            .strip_prefix("L_")
            .or_else(|| label.strip_prefix(".L_"))
        {
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
        for (addr, name, _) in db.rel_iter::<(
            crate::x86::types::Address,
            crate::x86::types::Symbol,
            crate::x86::types::Symbol,
        )>("symbols")
        {
            label_addrs.push((*name, *addr));
        }
        for (label, addr) in &label_addrs {
            if fp_labels.contains(*label) {
                continue;
            }
            if !label.starts_with("L_") && !label.starts_with(".L_") && !label.starts_with("SUB_") {
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
                // Skip empty entries: &L_x for a 0x00-leading float constant is not a real "", which reaches char* via a pointer cast.
                if !str_content.is_empty() {
                    return Some(CExpr::StringLit(
                        crate::decompile::passes::c_pass::types::StringLiteral {
                            value: str_content.clone(),
                            is_wide: false,
                        },
                    ));
                }
            }
        }
        if let CExpr::StringLit(_) = inner.as_ref() {
            return Some(inner.as_ref().clone());
        }
    }

    if let CExpr::Cast(ty, inner) = expr {
        if let CExpr::Var(name) = inner.as_ref() {
            if let Some(str_content) = string_map.get(name) {
                // For an empty entry require a genuine char* target; a (void*)/(float*) cast of a 0x00-leading float constant is not a real "".
                let char_ctx = is_char_pointer_type(ty);
                if (char_ctx) || (!str_content.is_empty() && matches!(ty, CType::Pointer(_, _))) {
                    return Some(CExpr::StringLit(
                        crate::decompile::passes::c_pass::types::StringLiteral {
                            value: str_content.clone(),
                            is_wide: false,
                        },
                    ));
                }
            }
        }
        if let CExpr::Var(name) = inner.as_ref() {
            if let Some(str_content) = string_map.get(name) {
                // In a non-char context like (long)L_x an empty entry is a 0x00-leading scalar coinciding with a string terminator, not a real "".
                if !str_content.is_empty()
                    && matches!(
                        ty,
                        CType::Int(crate::decompile::passes::c_pass::types::IntSize::Long, _)
                    )
                {
                    return Some(CExpr::StringLit(
                        crate::decompile::passes::c_pass::types::StringLiteral {
                            value: str_content.clone(),
                            is_wide: false,
                        },
                    ));
                }
            }
        }
        if let CExpr::Unary(UnaryOp::AddrOf, addr_inner) = inner.as_ref() {
            if let CExpr::Var(name) = addr_inner.as_ref() {
                if let Some(str_content) = string_map.get(name) {
                    return Some(CExpr::StringLit(
                        crate::decompile::passes::c_pass::types::StringLiteral {
                            value: str_content.clone(),
                            is_wide: false,
                        },
                    ));
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
            // Skip empty entries: a bare L_x with no char* context is a zero-length anchor coinciding with a scalar constant, not a real "".
            if (name.starts_with(".L_") || name.starts_with("L_")) && !str_content.is_empty() {
                return Some(CExpr::StringLit(
                    crate::decompile::passes::c_pass::types::StringLiteral {
                        value: str_content.clone(),
                        is_wide: false,
                    },
                ));
            }
        }
    }

    None
}

// Top-down walk that inlines `Var(name)` to a rodata scalar from `const_map`, but skips any Var sitting directly inside an `&` (address-of). Taking the address of an inlined scalar literal (`&1530735616`) is meaningless C: the AddrOf wanted the symbol's storage location, not its value.
pub fn inline_rodata_constants_preserving_addrof(
    expr: &CExpr,
    const_map: &HashMap<String, CExpr>,
) -> CExpr {
    use crate::decompile::passes::c_pass::types::UnaryOp;
    match expr {
        CExpr::Unary(UnaryOp::AddrOf, inner) => {
            // Do NOT inline a Var that's the direct operand of `&`; keep the symbol. Recurse otherwise to handle `&(struct.field)` and similar nested cases.
            let new_inner: CExpr = match inner.as_ref() {
                CExpr::Var(name) if const_map.contains_key(name) => (**inner).clone(),
                _ => inline_rodata_constants_preserving_addrof(inner, const_map),
            };
            CExpr::Unary(UnaryOp::AddrOf, Box::new(new_inner))
        }
        CExpr::Var(name) => {
            if let Some(replacement) = const_map.get(name) {
                replacement.clone()
            } else {
                expr.clone()
            }
        }
        CExpr::Unary(op, inner) => CExpr::Unary(
            *op,
            Box::new(inline_rodata_constants_preserving_addrof(inner, const_map)),
        ),
        CExpr::Binary(op, lhs, rhs) => CExpr::Binary(
            *op,
            Box::new(inline_rodata_constants_preserving_addrof(lhs, const_map)),
            Box::new(inline_rodata_constants_preserving_addrof(rhs, const_map)),
        ),
        CExpr::Assign(op, lhs, rhs) => CExpr::Assign(
            *op,
            Box::new(inline_rodata_constants_preserving_addrof(lhs, const_map)),
            Box::new(inline_rodata_constants_preserving_addrof(rhs, const_map)),
        ),
        CExpr::Ternary(c, t, e) => CExpr::Ternary(
            Box::new(inline_rodata_constants_preserving_addrof(c, const_map)),
            Box::new(inline_rodata_constants_preserving_addrof(t, const_map)),
            Box::new(inline_rodata_constants_preserving_addrof(e, const_map)),
        ),
        CExpr::Call(func, args) => CExpr::Call(
            Box::new(inline_rodata_constants_preserving_addrof(func, const_map)),
            args.iter()
                .map(|a| inline_rodata_constants_preserving_addrof(a, const_map))
                .collect(),
        ),
        CExpr::Index(arr, idx) => CExpr::Index(
            Box::new(inline_rodata_constants_preserving_addrof(arr, const_map)),
            Box::new(inline_rodata_constants_preserving_addrof(idx, const_map)),
        ),
        CExpr::Member(e, field) => CExpr::Member(
            Box::new(inline_rodata_constants_preserving_addrof(e, const_map)),
            field.clone(),
        ),
        CExpr::MemberPtr(e, field) => CExpr::MemberPtr(
            Box::new(inline_rodata_constants_preserving_addrof(e, const_map)),
            field.clone(),
        ),
        CExpr::Cast(ty, e) => CExpr::Cast(
            ty.clone(),
            Box::new(inline_rodata_constants_preserving_addrof(e, const_map)),
        ),
        CExpr::SizeofExpr(e) => CExpr::SizeofExpr(Box::new(
            inline_rodata_constants_preserving_addrof(e, const_map),
        )),
        CExpr::Paren(e) => CExpr::Paren(Box::new(inline_rodata_constants_preserving_addrof(
            e, const_map,
        ))),
        _ => expr.clone(),
    }
}

pub fn is_char_pointer_type(ty: &CType) -> bool {
    use crate::decompile::passes::c_pass::types::IntSize;
    matches!(ty,
        CType::Pointer(inner, _) if matches!(inner.as_ref(),
            CType::Int(IntSize::Char, _) | CType::Void
        )
    )
}

// Collect EVERY named label in a statement tree: extract_named_label sees only a top-level Labeled, so a label past a leading Sskip would build no goto edge and leave the node disconnected.
pub fn collect_defined_labels(stmt: &CStmt, out: &mut Vec<String>) {
    match stmt {
        CStmt::Labeled(Label::Named(name), inner) => {
            out.push(name.clone());
            collect_defined_labels(inner, out);
        }
        CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)  => collect_defined_labels(inner, out),
        CStmt::Sequence(stmts) => {
            for s in stmts {
                collect_defined_labels(s, out);
            }
        }
        CStmt::Block(items) => {
            for item in items {
                if let CBlockItem::Stmt(s) = item {
                    collect_defined_labels(s, out);
                }
            }
        }
        CStmt::If(_, then_s, else_s) => {
            collect_defined_labels(then_s, out);
            if let Some(e) = else_s {
                collect_defined_labels(e, out);
            }
        }
        CStmt::While(_, body) | CStmt::DoWhile(body, _) | CStmt::For(_, _, _, body) => {
            collect_defined_labels(body, out);
        }
        CStmt::Switch(_, body) => collect_defined_labels(body, out),
        _ => {}
    }
}

pub fn collect_goto_label_targets(stmt: &CStmt, targets: &mut Vec<String>) {
    match stmt {
        CStmt::Goto(label) => targets.push(label.clone()),
        CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)  => collect_goto_label_targets(inner, targets),
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
        CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)  => is_terminal_cstmt(inner),
        // Conversion wraps tail calls as `{ call; return; }`.  Treat the
        // wrapper by its last executable statement; otherwise the optimized
        // CFG invents fallthrough from a shared PLT tail-call node into the
        // next statement-bearing function entry.
        CStmt::Block(items) => items
            .iter()
            .rev()
            .find_map(|item| match item {
                CBlockItem::Stmt(s) if !matches!(s, CStmt::Empty) => Some(is_terminal_cstmt(s)),
                _ => None,
            })
            .unwrap_or(false),
        CStmt::Sequence(stmts) => stmts
            .iter()
            .rev()
            .find_map(|s| (!matches!(s, CStmt::Empty)).then(|| is_terminal_cstmt(s)))
            .unwrap_or(false),
        CStmt::If(_, _, _) => true,
        CStmt::Switch(_, _) => true,
        CStmt::While(_, _) | CStmt::DoWhile(_, _) | CStmt::For(_, _, _, _) => true,
        _ => false,
    }
}

#[cfg(test)]
mod terminal_tests {
    use super::*;
    use crate::decompile::passes::c_pass::types::UnaryOp;

    #[test]
    fn scalar_fp_constant_wins_over_incidental_string_decode() {
        let mut db = DecompileDB::default();
        db.rel_push(
            "string_data",
            ("L_175f0".to_string(), "\u{1}".to_string(), 2usize),
        );
        db.rel_push(
            "string_data",
            ("L_17620".to_string(), "real string".to_string(), 12usize),
        );
        db.rel_push(
            "rodata_fp_const",
            (0x175f0u64, 8usize, 0x3ca0_0000_0000_0001u64),
        );

        let strings = build_string_literal_map(&db);
        assert!(!strings.contains_key("L_175f0"));
        assert!(!strings.contains_key(".L_175f0"));
        assert_eq!(
            strings.get("L_17620").map(String::as_str),
            Some("real string")
        );
    }

    #[test]
    fn exact_scalar_rewrite_prevents_later_raw_string_override() {
        let label = "L_40200c";
        let string_map = HashMap::from([(label.to_string(), "%".to_string())]);
        let scalar_map = HashMap::from([(label.to_string(), CExpr::int(37))]);

        let rewritten = inline_rodata_constants_preserving_addrof(&CExpr::var(label), &scalar_map);
        assert_eq!(rewritten, CExpr::int(37));
        assert_eq!(inline_string_literals(&rewritten, &string_map), None);
    }

    #[test]
    fn scalar_precedence_preserves_mixed_use_address_for_string_rewrite() {
        let label = "L_40200c";
        let string_map = HashMap::from([(label.to_string(), "%".to_string())]);
        let scalar_map = HashMap::from([(label.to_string(), CExpr::int(37))]);
        let address = CExpr::Unary(UnaryOp::AddrOf, Box::new(CExpr::var(label)));

        let rewritten = inline_rodata_constants_preserving_addrof(&address, &scalar_map);
        assert_eq!(rewritten, address);
        assert!(matches!(
            inline_string_literals(&rewritten, &string_map),
            Some(CExpr::StringLit(literal)) if literal.value == "%"
        ));
    }

    #[test]
    fn scalar_first_order_keeps_genuine_string_without_scalar_evidence() {
        let label = "L_40200c";
        let string_map = HashMap::from([(label.to_string(), "%".to_string())]);
        let rewritten =
            inline_rodata_constants_preserving_addrof(&CExpr::var(label), &HashMap::new());

        assert_eq!(rewritten, CExpr::var(label));
        assert!(matches!(
            inline_string_literals(&rewritten, &string_map),
            Some(CExpr::StringLit(literal)) if literal.value == "%"
        ));
    }

    #[test]
    fn labeled_tailcall_block_is_terminal() {
        let stmt = CStmt::Labeled(
            Label::Named("tail".into()),
            Box::new(CStmt::Block(vec![
                CBlockItem::Stmt(CStmt::Expr(CExpr::call(CExpr::var("callee"), Vec::new()))),
                CBlockItem::Stmt(CStmt::Return(None)),
            ])),
        );

        assert!(is_terminal_cstmt(&stmt));
    }

    #[test]
    fn expression_mapper_reaches_compound_initializers_designators_and_stmt_exprs() {
        let expression = CExpr::CompoundLit(
            CType::long(),
            vec![Initializer::List(vec![InitItem {
                designator: Some(Designator::Index(CExpr::var("old"))),
                init: Initializer::Expr(CExpr::StmtExpr(
                    vec![
                        CStmt::Expr(CExpr::call(CExpr::var("consume"), vec![CExpr::var("old")])),
                        CStmt::Decl(vec![VarDecl::new("nested", CType::long())
                            .with_init(Initializer::Expr(CExpr::var("old")))]),
                    ],
                    Box::new(CExpr::var("old")),
                )),
            }])],
        );
        let rewritten = map_expr(&expression, &|candidate| match candidate {
            CExpr::Var(name) if name == "old" => Some(CExpr::var("new")),
            _ => None,
        });

        let CExpr::CompoundLit(_, initializers) = rewritten else {
            panic!("compound literal shape changed")
        };
        let [Initializer::List(items)] = initializers.as_slice() else {
            panic!("initializer list disappeared")
        };
        assert!(matches!(
            items[0].designator,
            Some(Designator::Index(CExpr::Var(ref name))) if name == "new"
        ));
        let Initializer::Expr(CExpr::StmtExpr(stmts, tail)) = &items[0].init else {
            panic!("statement expression disappeared")
        };
        assert!(matches!(tail.as_ref(), CExpr::Var(name) if name == "new"));
        assert!(matches!(
            &stmts[0],
            CStmt::Expr(CExpr::Call(_, args))
                if matches!(&args[0], CExpr::Var(name) if name == "new")
        ));
        assert!(matches!(
            &stmts[1],
            CStmt::Decl(decls)
                if matches!(&decls[0].init,
                    Some(Initializer::Expr(CExpr::Var(name))) if name == "new")
        ));
    }
}
