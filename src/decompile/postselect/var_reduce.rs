// Post-emission variable reduction on the final C AST.
use std::collections::{HashMap, HashSet};
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::c_pass::helpers::map_expr;
use crate::decompile::passes::c_pass::types::*;
use crate::decompile::passes::pass::IRPass;

// complete read-only walkers

fn visit_expr(e: &CExpr, f: &mut dyn FnMut(&CExpr)) {
    f(e);
    match e {
        CExpr::Unary(_, a) | CExpr::Cast(_, a) | CExpr::Member(a, _) | CExpr::MemberPtr(a, _)
        | CExpr::Paren(a) | CExpr::SizeofExpr(a) => visit_expr(a, f),
        CExpr::Binary(_, a, b) | CExpr::Assign(_, a, b) | CExpr::Index(a, b) => {
            visit_expr(a, f);
            visit_expr(b, f);
        }
        CExpr::Ternary(a, b, c) => {
            visit_expr(a, f);
            visit_expr(b, f);
            visit_expr(c, f);
        }
        CExpr::Call(g, args) => {
            visit_expr(g, f);
            args.iter().for_each(|a| visit_expr(a, f));
        }
        _ => {}
    }
}

// Every top-level expr directly in statement `s` (NOT recursing into child statements).
fn stmt_top_exprs(s: &CStmt, f: &mut dyn FnMut(&CExpr)) {
    match s {
        CStmt::Expr(e) | CStmt::Return(Some(e)) => f(e),
        CStmt::If(c, _, _) | CStmt::Switch(c, _) | CStmt::While(c, _) | CStmt::DoWhile(_, c) => f(c),
        CStmt::For(init, cond, update, _) => {
            if let Some(ForInit::Expr(e)) = init {
                f(e);
            }
            if let Some(ForInit::Decl(ds)) = init {
                ds.iter().for_each(|d| decl_init_exprs(d, f));
            }
            if let Some(c) = cond {
                f(c);
            }
            if let Some(u) = update {
                f(u);
            }
        }
        CStmt::Decl(ds) => ds.iter().for_each(|d| decl_init_exprs(d, f)),
        _ => {}
    }
}

fn decl_init_exprs(d: &VarDecl, f: &mut dyn FnMut(&CExpr)) {
    fn go(init: &Initializer, f: &mut dyn FnMut(&CExpr)) {
        match init {
            Initializer::Expr(e) => f(e),
            Initializer::List(items) => items.iter().for_each(|it| go(&it.init, f)),
            Initializer::String(_) => {}
        }
    }
    if let Some(i) = &d.init {
        go(i, f);
    }
}

// Visit every statement (incl nested).
fn visit_stmts(s: &CStmt, f: &mut dyn FnMut(&CStmt)) {
    f(s);
    for c in stmt_children(s) {
        visit_stmts(c, f);
    }
}

fn stmt_children(s: &CStmt) -> Vec<&CStmt> {
    match s {
        CStmt::Block(items) => items
            .iter()
            .filter_map(|it| if let CBlockItem::Stmt(st) = it { Some(st) } else { None })
            .collect(),
        CStmt::Sequence(v) => v.iter().collect(),
        CStmt::If(_, t, e) => {
            let mut c = vec![t.as_ref()];
            if let Some(e) = e {
                c.push(e.as_ref());
            }
            c
        }
        CStmt::Switch(_, b) | CStmt::While(_, b) | CStmt::Labeled(_, b) | CStmt::DoWhile(b, _) => {
            vec![b.as_ref()]
        }
        CStmt::For(_, _, _, b) => vec![b.as_ref()],
        _ => vec![],
    }
}

// queries

fn count_var_in_expr(e: &CExpr, name: &str) -> u32 {
    let mut n = 0;
    visit_expr(e, &mut |x| {
        if let CExpr::Var(v) = x {
            if v == name {
                n += 1;
            }
        }
    });
    n
}

// occurrences of `name` in the always-evaluated part of statement s (mirrors subst_use_in_stmt)
fn count_var_cond_part(s: &CStmt, name: &str) -> u32 {
    match s {
        CStmt::Expr(e) | CStmt::Return(Some(e)) => count_var_in_expr(e, name),
        CStmt::If(c, _, _) | CStmt::Switch(c, _) | CStmt::While(c, _) | CStmt::DoWhile(_, c) => {
            count_var_in_expr(c, name)
        }
        CStmt::For(_, Some(c), _, _) => count_var_in_expr(c, name),
        _ => 0,
    }
}

// total occurrences of `name` anywhere in statement s (incl nested bodies)
fn count_var_total(s: &CStmt, name: &str) -> u32 {
    let mut n = 0;
    visit_stmts(s, &mut |st| stmt_top_exprs(st, &mut |e| n += count_var_in_expr(e, name)));
    n
}

fn expr_has_call(e: &CExpr) -> bool {
    let mut f = false;
    visit_expr(e, &mut |x| {
        if matches!(x, CExpr::Call(..)) {
            f = true;
        }
    });
    f
}

fn expr_has_load(e: &CExpr) -> bool {
    let mut f = false;
    visit_expr(e, &mut |x| {
        if matches!(x, CExpr::Unary(UnaryOp::Deref, _) | CExpr::MemberPtr(_, _) | CExpr::Index(_, _)) {
            f = true;
        }
    });
    f
}

fn expr_impure(e: &CExpr) -> bool {
    expr_has_call(e) || expr_has_load(e)
}

fn is_store(e: &CExpr) -> bool {
    matches!(e, CExpr::Assign(_, lhs, _) if !matches!(lhs.as_ref(), CExpr::Var(_)))
}

// A statement (incl nested) carries an observable side effect: a call, or a store through a pointer.
fn stmt_has_side_effect(s: &CStmt) -> bool {
    let mut f = false;
    visit_stmts(s, &mut |st| {
        stmt_top_exprs(st, &mut |e| {
            visit_expr(e, &mut |x| {
                if matches!(x, CExpr::Call(..)) || is_store(x) {
                    f = true;
                }
            })
        })
    });
    f
}

// statement is a plain `v = rhs;`
fn simple_def<'a>(s: &'a CStmt) -> Option<(&'a str, &'a CExpr)> {
    if let CStmt::Expr(CExpr::Assign(AssignOp::Assign, lhs, rhs)) = s {
        if let CExpr::Var(v) = lhs.as_ref() {
            return Some((v.as_str(), rhs.as_ref()));
        }
    }
    None
}

fn free_vars(e: &CExpr) -> Vec<String> {
    let mut v = Vec::new();
    visit_expr(e, &mut |x| {
        if let CExpr::Var(n) = x {
            v.push(n.clone());
        }
    });
    v
}

// statement assigns (defs or stores into) any of `vars`
fn stmt_assigns_any(s: &CStmt, vars: &[String]) -> bool {
    let mut f = false;
    visit_stmts(s, &mut |st| {
        stmt_top_exprs(st, &mut |e| {
            visit_expr(e, &mut |x| {
                if let CExpr::Assign(_, lhs, _) = x {
                    if let CExpr::Var(n) = lhs.as_ref() {
                        if vars.iter().any(|v| v == n) {
                            f = true;
                        }
                    }
                }
            })
        })
    });
    f
}

// substitution

fn subst_once(e: &CExpr, name: &str, rhs: &CExpr) -> CExpr {
    map_expr(e, &|x| match x {
        CExpr::Var(n) if n == name => Some(rhs.clone()),
        _ => None,
    })
}

// Substitute the read of `name` in the always-evaluated part of `s`; returns the new statement.
fn subst_use_in_stmt(s: &CStmt, name: &str, rhs: &CExpr) -> CStmt {
    match s {
        CStmt::Expr(e) => CStmt::Expr(subst_once(e, name, rhs)),
        CStmt::Return(Some(e)) => CStmt::Return(Some(subst_once(e, name, rhs))),
        CStmt::If(c, t, el) => CStmt::If(subst_once(c, name, rhs), t.clone(), el.clone()),
        CStmt::Switch(c, b) => CStmt::Switch(subst_once(c, name, rhs), b.clone()),
        CStmt::While(c, b) => CStmt::While(subst_once(c, name, rhs), b.clone()),
        CStmt::DoWhile(b, c) => CStmt::DoWhile(b.clone(), subst_once(c, name, rhs)),
        CStmt::For(i, Some(c), u, b) => {
            CStmt::For(i.clone(), Some(subst_once(c, name, rhs)), u.clone(), b.clone())
        }
        other => other.clone(),
    }
}

// the fold

fn fold_list(stmts: &mut Vec<CStmt>, cand: &HashSet<String>, folded: &mut Vec<String>) {
    // recurse into nested lists first
    for s in stmts.iter_mut() {
        fold_children(s, cand, folded);
    }

    let mut i = 0usize;
    'outer: while i < stmts.len() {
        let (v, rhs) = match simple_def(&stmts[i]) {
            Some((v, rhs)) if cand.contains(v) => (v.to_string(), rhs.clone()),
            _ => {
                i += 1;
                continue;
            }
        };
        let rhs_impure = expr_impure(&rhs);
        let rhs_vars = free_vars(&rhs);

        for j in (i + 1)..stmts.len() {
            let total = count_var_total(&stmts[j], &v);
            if total == 0 {
                // between statement: must be inert and not clobber rhs's inputs
                if stmt_has_side_effect(&stmts[j]) || stmt_assigns_any(&stmts[j], &rhs_vars) {
                    break; // unsafe to move past; give up on this candidate
                }
                continue;
            }
            // stmts[j] holds the (single) read
            let cond = count_var_cond_part(&stmts[j], &v);
            let safe = total == 1
                && cond == 1
                && !(rhs_impure && stmt_has_side_effect(&stmts[j]));
            if safe {
                let new_use = subst_use_in_stmt(&stmts[j], &v, &rhs);
                stmts[j] = new_use;
                stmts.remove(i);
                folded.push(v);
                continue 'outer; // statement at i is now the next one
            }
            break; // read found but not safely foldable
        }
        i += 1;
    }
}

fn fold_children(s: &mut CStmt, cand: &HashSet<String>, folded: &mut Vec<String>) {
    match s {
        CStmt::Block(items) => {
            if items.iter().all(|it| matches!(it, CBlockItem::Stmt(_))) {
                let mut v: Vec<CStmt> = items
                    .iter()
                    .map(|it| match it {
                        CBlockItem::Stmt(s) => s.clone(),
                        _ => unreachable!(),
                    })
                    .collect();
                fold_list(&mut v, cand, folded);
                *items = v.into_iter().map(CBlockItem::Stmt).collect();
            } else {
                // mixed decls/stmts: no sibling fold here, just recurse
                for it in items.iter_mut() {
                    if let CBlockItem::Stmt(st) = it {
                        fold_children(st, cand, folded);
                    }
                }
            }
        }
        CStmt::Sequence(v) => fold_list(v, cand, folded),
        CStmt::If(_, t, e) => {
            fold_children(t, cand, folded);
            if let Some(e) = e {
                fold_children(e, cand, folded);
            }
        }
        CStmt::Switch(_, b) | CStmt::While(_, b) | CStmt::Labeled(_, b) | CStmt::DoWhile(b, _) => {
            fold_children(b, cand, folded)
        }
        CStmt::For(_, _, _, b) => fold_children(b, cand, folded),
        _ => {}
    }
}

fn reduce_function(func: &mut FuncDef) -> usize {
    // counts: total Var reads, and simple-def-statement counts
    let mut var_total: HashMap<String, u32> = HashMap::new();
    let mut defs: HashMap<String, u32> = HashMap::new();
    visit_stmts(&func.body, &mut |s| {
        if let Some((v, rhs)) = simple_def(s) {
            *defs.entry(v.to_string()).or_default() += 1;
            visit_expr(rhs, &mut |x| {
                if let CExpr::Var(n) = x {
                    *var_total.entry(n.clone()).or_default() += 1;
                }
            });
        } else {
            stmt_top_exprs(s, &mut |e| {
                visit_expr(e, &mut |x| {
                    if let CExpr::Var(n) = x {
                        *var_total.entry(n.clone()).or_default() += 1;
                    }
                })
            });
        }
    });

    // candidate: declared local with NO initializer, exactly one simple def, exactly one read.
    let no_init: HashSet<&str> = func
        .local_vars
        .iter()
        .filter(|d| d.init.is_none())
        .map(|d| d.name.as_str())
        .collect();
    let cand: HashSet<String> = no_init
        .iter()
        .filter(|n| defs.get(**n).copied().unwrap_or(0) == 1
            && var_total.get(**n).copied().unwrap_or(0) == 1)
        .map(|n| n.to_string())
        .collect();
    if cand.is_empty() {
        return 0;
    }

    let mut folded: Vec<String> = Vec::new();
    fold_children(&mut func.body, &cand, &mut folded);

    if !folded.is_empty() {
        let gone: HashSet<&String> = folded.iter().collect();
        // a folded local no longer appears anywhere -> drop its declaration
        let mut appears: HashSet<String> = HashSet::new();
        visit_stmts(&func.body, &mut |s| {
            stmt_top_exprs(s, &mut |e| {
                visit_expr(e, &mut |x| {
                    if let CExpr::Var(n) = x {
                        appears.insert(n.clone());
                    }
                })
            })
        });
        func.local_vars
            .retain(|d| !(gone.contains(&d.name) && !appears.contains(&d.name)));
    }
    folded.len()
}

pub struct VarReducePass;

impl IRPass for VarReducePass {
    fn name(&self) -> &'static str {
        "var_reduce"
    }

    fn run(&self, db: &mut DecompileDB) {
        if std::env::var("MANIFOLD_NO_VARREDUCE").is_ok() {
            return;
        }
        let tu = match db.cast_optimized_translation_unit.as_mut() {
            Some(tu) => tu,
            None => return,
        };
        let mut total = 0usize;
        for decl in tu.decls.iter_mut() {
            if let TopLevelDecl::FuncDef(f) = decl {
                // fixpoint so chained temps (t1=*p; t2=t1->f; x=t2) collapse fully
                loop {
                    let n = reduce_function(f);
                    total += n;
                    if n == 0 {
                        break;
                    }
                }
            }
        }
        log::info!("var_reduce: folded {} single-use temporaries", total);
    }

    fn inputs(&self) -> &'static [&'static str] {
        // Depend on the emitted TU so this runs strictly after (and solo, on the main DB) ClightEmitPass.
        &["cast_optimized_translation_unit"]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &["cast_optimized_translation_unit"]
    }
}
