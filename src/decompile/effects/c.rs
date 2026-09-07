//! Conservative C-side effect projection. Postselection proposals must retain
//! scoped value occurrences, enclosing control, and potentially interfering
//! calls/stores. This checks preservation, not whole-function equivalence.
use crate::decompile::passes::c_pass::types::*;
use std::collections::HashSet;

#[derive(Default)]
struct Inspect {
    names: HashSet<String>,
    impure: bool,
    locals: HashSet<String>,
}
impl ExprTransform for Inspect {
    fn transform_expr(&mut self, expr: CExpr) -> CExpr {
        match &expr {
            CExpr::Var(name) => {
                self.names.insert(name.clone());
            }
            CExpr::Call(..) => self.impure = true,
            CExpr::Unary(
                UnaryOp::Deref
                | UnaryOp::PreInc
                | UnaryOp::PostInc
                | UnaryOp::PreDec
                | UnaryOp::PostDec,
                _,
            )
            | CExpr::Index(..)
            | CExpr::MemberPtr(..) => self.impure = true,
            CExpr::Assign(_, lhs, _) => {
                if !matches!(lhs.as_ref(),CExpr::Var(n) if self.locals.contains(n)) {
                    self.impure = true;
                }
            }
            _ => {}
        }
        self.walk_expr(expr)
    }
    fn transform_stmt_in_expr(&mut self, stmt: CStmt) -> CStmt {
        self.transform_stmt(stmt)
    }
}
impl StmtTransform for Inspect {}

fn inspect(expr: &CExpr, locals: &HashSet<String>) -> Inspect {
    let mut visitor = Inspect {
        locals: locals.clone(),
        ..Default::default()
    };
    visitor.transform_expr(expr.clone());
    visitor
}
fn sequence(items: Vec<CStmt>) -> CStmt {
    let mut out = Vec::new();
    for item in items {
        match item {
            CStmt::Empty => {}
            CStmt::Sequence(s) => out.extend(s),
            other => out.push(other),
        }
    }
    if out.len() == 1 {
        out.pop().unwrap()
    } else if out.is_empty() {
        CStmt::Empty
    } else {
        CStmt::Sequence(out)
    }
}

fn project(stmt: &CStmt, protected: &HashSet<String>, locals: &HashSet<String>) -> CStmt {
    match stmt {
        CStmt::Expr(e) => {
            let used = inspect(e, locals);
            if used.impure || !used.names.is_disjoint(protected) {
                stmt.clone()
            } else {
                CStmt::Empty
            }
        }
        CStmt::Return(value) => CStmt::Return(
            value
                .as_ref()
                .filter(|e| !inspect(e, locals).names.is_disjoint(protected))
                .cloned(),
        ),
        CStmt::Goto(_) | CStmt::Continue | CStmt::Break => stmt.clone(),
        CStmt::Block(items) => sequence(
            items
                .iter()
                .map(|item| match item {
                    CBlockItem::Stmt(s) => project(s, protected, locals),
                    CBlockItem::Decl(d) => declarations(d, protected, locals),
                })
                .collect(),
        ),
        CStmt::Sequence(items) => sequence(
            items
                .iter()
                .map(|s| project(s, protected, locals))
                .collect(),
        ),
        CStmt::Decl(d) => declarations(d, protected, locals),
        CStmt::If(cond, a, b) => {
            let a = project(a, protected, locals);
            let b = b.as_ref().map(|s| project(s, protected, locals));
            if a == CStmt::Empty
                && b.as_ref().is_none_or(|s| *s == CStmt::Empty)
                && !inspect(cond, locals).impure
            {
                CStmt::Empty
            } else {
                CStmt::If(cond.clone(), Box::new(a), b.map(Box::new))
            }
        }
        CStmt::While(cond, body) => {
            CStmt::While(cond.clone(), Box::new(project(body, protected, locals)))
        }
        CStmt::DoWhile(body, cond) => {
            CStmt::DoWhile(Box::new(project(body, protected, locals)), cond.clone())
        }
        CStmt::For(init, cond, step, body) => CStmt::For(
            init.clone(),
            cond.clone(),
            step.clone(),
            Box::new(project(body, protected, locals)),
        ),
        CStmt::Switch(cond, body) => {
            CStmt::Switch(cond.clone(), Box::new(project(body, protected, locals)))
        }
        CStmt::Labeled(label, body) => {
            CStmt::Labeled(label.clone(), Box::new(project(body, protected, locals)))
        }
        CStmt::Effect(site, body) => CStmt::Effect(*site, body.clone()),
        CStmt::Empty => CStmt::Empty,
    }
}
fn declarations(decls: &[VarDecl], protected: &HashSet<String>, locals: &HashSet<String>) -> CStmt {
    sequence(
        decls
            .iter()
            .filter_map(|d| {
                if let Some(Initializer::Expr(expr)) = &d.init {
                    Some(project(
                        &CStmt::Expr(CExpr::Assign(
                            AssignOp::Assign,
                            Box::new(CExpr::Var(d.name.clone())),
                            Box::new(expr.clone()),
                        )),
                        protected,
                        locals,
                    ))
                } else {
                    None
                }
            })
            .collect(),
    )
}

pub(crate) fn protected_names(function: &FuncDef) -> HashSet<String> {
    if !has_effect(&function.body) {
        return HashSet::new();
    }
    let fences = occurrences(&function.body);
    if fences.is_empty() {
        return HashSet::new();
    }
    let mut inputs = Inspect::default();
    for (_, body) in fences {
        inputs.transform_stmt(body);
    }
    let protected = inputs.names;
    let locals = function.local_vars.iter().map(|v| v.name.clone()).collect();
    let projection = project(&function.body, &protected, &locals);
    let mut visitor = Inspect::default();
    visitor.transform_stmt(projection);
    visitor.names.extend(protected);
    visitor.names
}

pub(crate) fn preserves(function: &FuncDef, proposal: &CStmt) -> bool {
    if !has_effect(&function.body) {
        return true;
    }
    let protected = protected_names(function);
    let locals = function.local_vars.iter().map(|v| v.name.clone()).collect();
    project(&function.body, &protected, &locals) == project(proposal, &protected, &locals)
}

pub(crate) fn occurrences(stmt: &CStmt) -> Vec<(super::EffectSite, CStmt)> {
    if !has_effect(stmt) {
        return Vec::new();
    }
    #[derive(Default)]
    struct Collect(Vec<(super::EffectSite, CStmt)>);
    impl ExprTransform for Collect {
        fn transform_expr(&mut self, e: CExpr) -> CExpr {
            // A marker under sizeof is not an executed occurrence. Generic
            // selection needs type-driven arm selection; do not certify it.
            if matches!(e, CExpr::SizeofExpr(_) | CExpr::Generic(..)) {
                e
            } else {
                self.walk_expr(e)
            }
        }
        fn transform_stmt_in_expr(&mut self, s: CStmt) -> CStmt {
            self.transform_stmt(s)
        }
    }
    impl StmtTransform for Collect {
        fn transform_stmt(&mut self, s: CStmt) -> CStmt {
            if let CStmt::Effect(site, body) = &s {
                self.0.push((*site, (**body).clone()));
            }
            self.walk_stmt(s)
        }
    }
    let mut collect = Collect::default();
    collect.transform_stmt(stmt.clone());
    collect.0
}

pub(crate) fn has_effect(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Effect(..) => true,
        CStmt::Expr(e) => expr_has_effect(e),
        CStmt::Return(e) => e.as_ref().is_some_and(expr_has_effect),
        CStmt::Decl(d) => d
            .iter()
            .any(|d| d.init.as_ref().is_some_and(init_has_effect)),
        CStmt::Block(items) => items.iter().any(|i| match i {
            CBlockItem::Stmt(s) => has_effect(s),
            CBlockItem::Decl(d) => d
                .iter()
                .any(|d| d.init.as_ref().is_some_and(init_has_effect)),
        }),
        CStmt::Sequence(items) => items.iter().any(has_effect),
        CStmt::If(c, a, b) => {
            expr_has_effect(c) || has_effect(a) || b.as_ref().is_some_and(|s| has_effect(s))
        }
        CStmt::Switch(c, b) | CStmt::While(c, b) | CStmt::DoWhile(b, c) => {
            expr_has_effect(c) || has_effect(b)
        }
        CStmt::For(i, c, s, b) => {
            i.as_ref().is_some_and(|i| match i {
                ForInit::Expr(e) => expr_has_effect(e),
                ForInit::Decl(d) => d
                    .iter()
                    .any(|d| d.init.as_ref().is_some_and(init_has_effect)),
            }) || c.as_ref().is_some_and(expr_has_effect)
                || s.as_ref().is_some_and(expr_has_effect)
                || has_effect(b)
        }
        CStmt::Labeled(l, b) => matches!(l,Label::Case(e) if expr_has_effect(e)) || has_effect(b),
        CStmt::Empty | CStmt::Goto(_) | CStmt::Break | CStmt::Continue => false,
    }
}

fn init_has_effect(init: &Initializer) -> bool {
    match init {
        Initializer::Expr(e) => expr_has_effect(e),
        Initializer::List(items) => items.iter().any(|i| init_has_effect(&i.init)),
        Initializer::String(_) => false,
    }
}
fn expr_has_effect(expr: &CExpr) -> bool {
    match expr {
        CExpr::StmtExpr(stmts, result) => stmts.iter().any(has_effect) || expr_has_effect(result),
        CExpr::Unary(_, e)
        | CExpr::Cast(_, e)
        | CExpr::Member(e, _)
        | CExpr::MemberPtr(e, _)
        | CExpr::Paren(e)
        | CExpr::SizeofExpr(e) => expr_has_effect(e),
        CExpr::Binary(_, a, b) | CExpr::Assign(_, a, b) | CExpr::Index(a, b) => {
            expr_has_effect(a) || expr_has_effect(b)
        }
        CExpr::Ternary(c, a, b) => expr_has_effect(c) || expr_has_effect(a) || expr_has_effect(b),
        CExpr::Call(f, args) => expr_has_effect(f) || args.iter().any(expr_has_effect),
        CExpr::CompoundLit(_, items) => items.iter().any(init_has_effect),
        CExpr::Generic(e, arms) => {
            expr_has_effect(e) || arms.iter().any(|(_, e)| expr_has_effect(e))
        }
        CExpr::IntLit(_)
        | CExpr::FloatLit(_)
        | CExpr::StringLit(_)
        | CExpr::CharLit(_)
        | CExpr::Var(_)
        | CExpr::SizeofType(_)
        | CExpr::AlignofType(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn occurrence_walk_includes_statement_expressions_but_not_sizeof() {
        let site = crate::decompile::effects::EffectSite {
            function: 1,
            node: 2,
            epoch: 3,
            alternative: 4,
        };
        let expr = CExpr::StmtExpr(
            vec![CStmt::Effect(site, Box::new(CStmt::Expr(CExpr::int(1))))],
            Box::new(CExpr::int(2)),
        );
        assert_eq!(occurrences(&CStmt::Return(Some(expr.clone()))).len(), 1);
        assert!(occurrences(&CStmt::Return(Some(CExpr::SizeofExpr(Box::new(expr))))).is_empty());
    }
    #[test]
    fn projections_detect_drop_duplicate_guard_and_call_reordering() {
        let store = CStmt::Expr(CExpr::Assign(
            AssignOp::Assign,
            Box::new(CExpr::Var("captured".into())),
            Box::new(CExpr::Var("input".into())),
        ));
        let call = CStmt::Expr(CExpr::Call(Box::new(CExpr::Var("callee".into())), vec![]));
        let protected = HashSet::from(["captured".to_string()]);
        let locals = HashSet::from(["captured".to_string(), "input".to_string()]);
        let baseline = CStmt::Sequence(vec![call.clone(), store.clone()]);
        for changed in [
            call.clone(),
            CStmt::Sequence(vec![call.clone(), store.clone(), store.clone()]),
            CStmt::Sequence(vec![store.clone(), call.clone()]),
            CStmt::Sequence(vec![
                call,
                CStmt::If(CExpr::Var("guard".into()), Box::new(store), None),
            ]),
        ] {
            assert_ne!(
                project(&baseline, &protected, &locals),
                project(&changed, &protected, &locals)
            );
        }
    }
}
