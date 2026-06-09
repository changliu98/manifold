// Post-emission variable reduction on the final C AST. Two cooperating transformations, run per function as fold -> coalesce -> fold: * single-use temporary folding (`reduce_function`): inline `t = e; use(t)`. * live-range coalescing (`run_coalesce`): merge non-interfering locals into one (identical-type, then relaxed cross-type with cast insertion) and delete identity copies. Interference comes from a backward-liveness lattice over a CFG that models goto/label/break/continue (see CLAUDE.md); every axis is conservative, and an unmodelable CFG bails (no merge).
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
        let rhs_vars = vars(&rhs);

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

// --------------------------- expr helpers ---------------------------

/// Collect every variable *read* in an expression (plain `Var` occurrences).
fn collect_vars(e: &CExpr, out: &mut Vec<String>) {
    match e {
        CExpr::Var(n) => out.push(n.clone()),
        CExpr::Unary(_, a) | CExpr::Cast(_, a) | CExpr::Member(a, _) | CExpr::MemberPtr(a, _)
        | CExpr::Paren(a) | CExpr::SizeofExpr(a) => collect_vars(a, out),
        CExpr::Binary(_, a, b) | CExpr::Assign(_, a, b) | CExpr::Index(a, b) => {
            collect_vars(a, out);
            collect_vars(b, out);
        }
        CExpr::Ternary(a, b, c) => {
            collect_vars(a, out);
            collect_vars(b, out);
            collect_vars(c, out);
        }
        CExpr::Call(g, args) => {
            collect_vars(g, out);
            args.iter().for_each(|a| collect_vars(a, out));
        }
        _ => {}
    }
}

fn vars(e: &CExpr) -> Vec<String> {
    let mut v = Vec::new();
    collect_vars(e, &mut v);
    v
}

/// def / uses for a *statement-level* expression. A kill is recorded ONLY for `Var = rhs` (unconditional, whole-variable, plain assignment). Every other shape (compound assign, inc/dec, store through a pointer, conditional assign nested in `?:`/`&&`/`||`) records no kill and treats all operands as uses - over-approximating liveness, which is always safe (it can only block a merge, never enable an unsound one).
fn leaf_def_uses(e: &CExpr) -> (Option<String>, Vec<String>) {
    if let CExpr::Assign(AssignOp::Assign, lhs, rhs) = e {
        if let CExpr::Var(x) = &**lhs {
            return (Some(x.clone()), vars(rhs));
        }
    }
    (None, vars(e))
}

/// `Var(a) = Var(b)` -> Some(b): an exact copy whose def/src do not interfere.
fn copy_src(e: &CExpr) -> Option<String> {
    if let CExpr::Assign(AssignOp::Assign, lhs, rhs) = e {
        if let (CExpr::Var(_), CExpr::Var(b)) = (&**lhs, &**rhs) {
            return Some(b.clone());
        }
    }
    None
}

fn for_init_vars(init: &Option<ForInit>) -> Vec<String> {
    match init {
        Some(ForInit::Expr(e)) => vars(e),
        Some(ForInit::Decl(ds)) => ds.iter().flat_map(decl_init_vars).collect(),
        None => Vec::new(),
    }
}

fn decl_init_vars(d: &VarDecl) -> Vec<String> {
    match &d.init {
        Some(Initializer::Expr(e)) => vars(e),
        _ => Vec::new(),
    }
}

/// Normalize so every block item is a `Stmt` (Decl items -> `Stmt(Decl)`), used only for the analysis clone so the CFG builder can treat blocks uniformly.
fn normalize(s: &CStmt) -> CStmt {
    match s {
        CStmt::Block(items) => CStmt::Block(
            items
                .iter()
                .map(|it| match it {
                    CBlockItem::Stmt(st) => CBlockItem::Stmt(normalize(st)),
                    CBlockItem::Decl(ds) => CBlockItem::Stmt(CStmt::Decl(ds.clone())),
                })
                .collect(),
        ),
        CStmt::If(c, t, e) => CStmt::If(
            c.clone(),
            Box::new(normalize(t)),
            e.as_ref().map(|x| Box::new(normalize(x))),
        ),
        CStmt::Switch(c, b) => CStmt::Switch(c.clone(), Box::new(normalize(b))),
        CStmt::While(c, b) => CStmt::While(c.clone(), Box::new(normalize(b))),
        CStmt::DoWhile(b, c) => CStmt::DoWhile(Box::new(normalize(b)), c.clone()),
        CStmt::For(i, c, u, b) => {
            CStmt::For(i.clone(), c.clone(), u.clone(), Box::new(normalize(b)))
        }
        CStmt::Labeled(l, b) => CStmt::Labeled(l.clone(), Box::new(normalize(b))),
        CStmt::Sequence(ss) => CStmt::Sequence(ss.iter().map(normalize).collect()),
        _ => s.clone(),
    }
}

// --------------------------- CFG ---------------------------

struct FlowNode {
    def: Option<String>,
    uses: Vec<String>,
    copy_src: Option<String>,
    succ: Vec<usize>,
}

struct Cfg {
    nodes: Vec<FlowNode>,
    labels: HashMap<String, usize>,
    gotos: Vec<(usize, String)>,
    ok: bool,
}

const EXIT: usize = 0;

impl Cfg {
    fn new() -> Self {
        // node 0 = EXIT sink (no successors).
        Cfg {
            nodes: vec![FlowNode { def: None, uses: vec![], copy_src: None, succ: vec![] }],
            labels: HashMap::new(),
            gotos: Vec::new(),
            ok: true,
        }
    }

    fn add(&mut self, def: Option<String>, uses: Vec<String>) -> usize {
        self.nodes.push(FlowNode { def, uses, copy_src: None, succ: vec![] });
        self.nodes.len() - 1
    }

    /// Lower a statement; return its entry node id. `next` is the node reached when the statement completes normally; `brk`/`cont` are the targets of an enclosing loop/switch.
    fn lower(
        &mut self,
        s: &CStmt,
        next: usize,
        brk: Option<usize>,
        cont: Option<usize>,
    ) -> usize {
        match s {
            CStmt::Empty | CStmt::Decl(_) => {
                let uses = if let CStmt::Decl(ds) = s {
                    ds.iter().flat_map(decl_init_vars).collect()
                } else {
                    vec![]
                };
                let id = self.add(None, uses);
                self.nodes[id].succ = vec![next];
                id
            }
            CStmt::Expr(e) => {
                let (def, uses) = leaf_def_uses(e);
                let cs = copy_src(e);
                let id = self.add(def, uses);
                self.nodes[id].copy_src = cs;
                self.nodes[id].succ = vec![next];
                id
            }
            CStmt::Return(e) => {
                let uses = e.as_ref().map(|x| vars(x)).unwrap_or_default();
                let id = self.add(None, uses);
                self.nodes[id].succ = vec![EXIT];
                id
            }
            CStmt::Goto(l) => {
                let id = self.add(None, vec![]);
                self.gotos.push((id, l.clone()));
                id
            }
            CStmt::Break => {
                let id = self.add(None, vec![]);
                match brk {
                    Some(t) => self.nodes[id].succ = vec![t],
                    None => self.ok = false,
                }
                id
            }
            CStmt::Continue => {
                let id = self.add(None, vec![]);
                match cont {
                    Some(t) => self.nodes[id].succ = vec![t],
                    None => self.ok = false,
                }
                id
            }
            CStmt::Labeled(label, inner) => {
                let id = self.add(None, vec![]);
                if let Label::Named(l) = label {
                    self.labels.insert(l.clone(), id);
                }
                let ie = self.lower(inner, next, brk, cont);
                self.nodes[id].succ = vec![ie];
                id
            }
            CStmt::If(c, t, e) => {
                let id = self.add(None, vars(c));
                let te = self.lower(t, next, brk, cont);
                let ee = match e {
                    Some(es) => self.lower(es, next, brk, cont),
                    None => next,
                };
                self.nodes[id].succ = vec![te, ee];
                id
            }
            CStmt::While(c, b) => {
                let id = self.add(None, vars(c));
                let be = self.lower(b, id, Some(next), Some(id));
                self.nodes[id].succ = vec![be, next];
                id
            }
            CStmt::DoWhile(b, c) => {
                let cid = self.add(None, vars(c));
                let be = self.lower(b, cid, Some(next), Some(cid));
                self.nodes[cid].succ = vec![be, next];
                be
            }
            CStmt::For(init, cond, upd, b) => {
                let init_id = self.add(None, for_init_vars(init));
                let cond_id = self.add(None, cond.as_ref().map(|c| vars(c)).unwrap_or_default());
                let upd_id = self.add(None, upd.as_ref().map(|u| vars(u)).unwrap_or_default());
                let be = self.lower(b, upd_id, Some(next), Some(upd_id));
                self.nodes[init_id].succ = vec![cond_id];
                self.nodes[cond_id].succ = vec![be, next];
                self.nodes[upd_id].succ = vec![cond_id];
                init_id
            }
            CStmt::Switch(c, body) => {
                let id = self.add(None, vars(c));
                // Switch body: a list of statements, some labeled `case`/`default`. Internal fall-through is sequential; `break` exits to `next`.
                let items: Vec<&CStmt> = match &**body {
                    CStmt::Block(b) => b
                        .iter()
                        .map(|it| match it {
                            CBlockItem::Stmt(st) => st,
                            CBlockItem::Decl(_) => unreachable!("normalized"),
                        })
                        .collect(),
                    CStmt::Sequence(ss) => ss.iter().collect(),
                    single => vec![single],
                };
                let entries = self.lower_list(&items, next, Some(next), cont);
                let mut succ = Vec::new();
                let mut has_default = false;
                for (it, ent) in items.iter().zip(entries.iter()) {
                    if let CStmt::Labeled(lab, _) = it {
                        match lab {
                            Label::Case(_) => succ.push(*ent),
                            Label::Default => {
                                succ.push(*ent);
                                has_default = true;
                            }
                            Label::Named(_) => {}
                        }
                    }
                }
                if !has_default {
                    succ.push(next);
                }
                self.nodes[id].succ = succ;
                id
            }
            CStmt::Block(items) => {
                let v: Vec<&CStmt> = items
                    .iter()
                    .map(|it| match it {
                        CBlockItem::Stmt(st) => st,
                        CBlockItem::Decl(_) => unreachable!("normalized"),
                    })
                    .collect();
                let entries = self.lower_list(&v, next, brk, cont);
                *entries.first().unwrap_or(&next)
            }
            CStmt::Sequence(ss) => {
                let v: Vec<&CStmt> = ss.iter().collect();
                let entries = self.lower_list(&v, next, brk, cont);
                *entries.first().unwrap_or(&next)
            }
        }
    }

    /// Lower a statement list with sequential fall-through; return the entry node id of each statement (so a switch can wire to its case labels).
    fn lower_list(
        &mut self,
        items: &[&CStmt],
        next: usize,
        brk: Option<usize>,
        cont: Option<usize>,
    ) -> Vec<usize> {
        let n = items.len();
        let mut entries = vec![next; n];
        let mut cur_next = next;
        for i in (0..n).rev() {
            let e = self.lower(items[i], cur_next, brk, cont);
            entries[i] = e;
            cur_next = e;
        }
        entries
    }

    /// Resolve goto edges; an unresolved target makes the CFG unsafe.
    fn resolve_gotos(&mut self) {
        let fixups = std::mem::take(&mut self.gotos);
        for (id, label) in fixups {
            match self.labels.get(&label) {
                Some(&t) => self.nodes[id].succ = vec![t],
                None => self.ok = false,
            }
        }
    }
}

// --------------------------- liveness + interference ---------------------------

/// Build the candidate-only interference relation. Returns `None` if the CFG could not be modeled exactly (caller must not coalesce).
fn interference(
    cfg: &Cfg,
    cand: &HashMap<String, u32>,
) -> Option<HashSet<(u32, u32)>> {
    if !cfg.ok {
        return None;
    }
    let n = cfg.nodes.len();
    // Work bound: skip liveness on pathologically large functions rather than risk a slow fixpoint. Bailing only forgoes coalescing; it is never unsafe.
    if n.saturating_mul(cand.len()) > 8_000_000 {
        return None;
    }
    // Pre-filter each node's def/uses/copy_src to candidate ids.
    let id_of = |name: &str| cand.get(name).copied();
    let mut node_def: Vec<Option<u32>> = vec![None; n];
    let mut node_uses: Vec<Vec<u32>> = vec![Vec::new(); n];
    let mut node_copy: Vec<Option<u32>> = vec![None; n];
    for (i, nd) in cfg.nodes.iter().enumerate() {
        node_def[i] = nd.def.as_ref().and_then(|s| id_of(s));
        node_uses[i] = nd.uses.iter().filter_map(|u| id_of(u)).collect();
        node_copy[i] = nd.copy_src.as_ref().and_then(|s| id_of(s));
    }

    // Backward may-liveness lattice (join = union). Iterate to fixpoint.
    let mut live_in: Vec<HashSet<u32>> = vec![HashSet::new(); n];
    let mut changed = true;
    let mut guard = 0usize;
    let cap = n.saturating_mul(cand.len()).saturating_add(n).saturating_add(16);
    while changed {
        changed = false;
        guard += 1;
        if guard > cap + 4 {
            return None; // non-convergence safety net; never coalesce on doubt
        }
        for i in (0..n).rev() {
            // live_out = union live_in[succ]
            let mut out: HashSet<u32> = HashSet::new();
            for &s in &cfg.nodes[i].succ {
                for &v in &live_in[s] {
                    out.insert(v);
                }
            }
            // live_in = uses union (live_out \ def)
            let mut new_in = out.clone();
            if let Some(d) = node_def[i] {
                new_in.remove(&d);
            }
            for &u in &node_uses[i] {
                new_in.insert(u);
            }
            if new_in != live_in[i] {
                live_in[i] = new_in;
                changed = true;
            }
        }
    }

    // Interference: at every def, the defined var conflicts with everything live-out there (except itself and, at a copy `d = src`, the source).
    let mut interfere: HashSet<(u32, u32)> = HashSet::new();
    for i in 0..n {
        let Some(d) = node_def[i] else { continue };
        let copy = node_copy[i];
        let mut out: HashSet<u32> = HashSet::new();
        for &s in &cfg.nodes[i].succ {
            for &v in &live_in[s] {
                out.insert(v);
            }
        }
        for &v in &out {
            if v == d {
                continue;
            }
            if copy == Some(v) {
                continue; // copy-related: d and src may share storage here
            }
            interfere.insert(if d < v { (d, v) } else { (v, d) });
        }
    }
    Some(interfere)
}

// --------------------------- coalescing ---------------------------

fn is_scalar(ty: &CType) -> bool {
    matches!(
        ty,
        CType::Int(..) | CType::Float(..) | CType::Pointer(..) | CType::Bool | CType::Enum(_)
    )
}

struct Uf {
    parent: Vec<u32>,
    members: Vec<Vec<u32>>, // valid only at roots
}

impl Uf {
    fn new(k: usize) -> Self {
        Uf {
            parent: (0..k as u32).collect(),
            members: (0..k as u32).map(|i| vec![i]).collect(),
        }
    }
    fn find(&mut self, x: u32) -> u32 {
        let mut r = x;
        while self.parent[r as usize] != r {
            r = self.parent[r as usize];
        }
        let mut c = x;
        while self.parent[c as usize] != r {
            let nx = self.parent[c as usize];
            self.parent[c as usize] = r;
            c = nx;
        }
        r
    }
    /// Union iff no member of one class interferes with any member of the other (keeps every class pairwise non-interfering - the soundness invariant). Same-type is guaranteed by the caller.
    fn try_union(&mut self, a: u32, b: u32, interfere: &HashSet<(u32, u32)>) -> bool {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return true;
        }
        for &x in &self.members[ra as usize] {
            for &y in &self.members[rb as usize] {
                let pair = if x < y { (x, y) } else { (y, x) };
                if interfere.contains(&pair) {
                    return false;
                }
            }
        }
        let moved = std::mem::take(&mut self.members[rb as usize]);
        self.parent[rb as usize] = ra;
        self.members[ra as usize].extend(moved);
        true
    }
}

// Above this candidate count, skip the O(k^2) greedy general merge and keep only copy-related coalescing, to bound cost on pathologically large funcs.
const GREEDY_CAP: usize = 600;

// --------------------------- merge plan + relaxed (cross-type) ---------------------------

#[derive(PartialEq, Clone, Copy)]
enum Grp {
    IntPtr,
    Float,
}

fn group_of(ty: &CType) -> Grp {
    match ty {
        CType::Float(_) => Grp::Float,
        _ => Grp::IntPtr,
    }
}

/// Storage (slot) type for a relaxed, multi-type class. `long` holds every integer/pointer <= 8 bytes losslessly on LP64; `double` holds float/double. Reading a member back as its original type therefore round-trips exactly, which is what preserves pointer-arithmetic scaling and integer truncation.
fn storage_ty(g: Grp) -> CType {
    match g {
        Grp::IntPtr => CType::long(),
        Grp::Float => CType::double(),
    }
}

struct Plan {
    /// member name -> representative name (the rep itself is absent).
    rename: HashMap<String, String>,
    /// member name -> (original type, slot type) for members whose declared type differs from the class slot type - their reads/writes get casts.
    relaxed: HashMap<String, (CType, CType)>,
    /// representative name -> slot type to re-declare it as (mixed classes).
    rep_ty: HashMap<String, CType>,
}

impl Plan {
    fn empty() -> Self {
        Plan { rename: HashMap::new(), relaxed: HashMap::new(), rep_ty: HashMap::new() }
    }
    fn is_empty(&self) -> bool {
        self.rename.is_empty()
    }
    fn repof<'a>(&'a self, v: &'a str) -> &'a str {
        self.rename.get(v).map(|s| s.as_str()).unwrap_or(v)
    }
}

/// Coalesce non-interfering locals (identical-type, then - when `relax` - cross-type with cast insertion) and delete identity copies. Returns the number of locals eliminated.
fn run_coalesce(func: &mut FuncDef) -> usize {
    // Candidates: scalar locals with no initializer whose address is never taken. (Params/globals are not in local_vars; inited locals are skipped so no initialization is ever dropped; address-taken locals are excluded because aliasing breaks the liveness model.)
    let mut addr_taken: HashSet<String> = HashSet::new();
    collect_addr_taken_stmt(&func.body, &mut addr_taken);

    let mut names: Vec<String> = func
        .local_vars
        .iter()
        .filter(|d| d.init.is_none() && is_scalar(&d.ty) && !addr_taken.contains(&d.name))
        .map(|d| d.name.clone())
        .collect();
    names.sort();
    names.dedup();

    let relax = std::env::var("MANIFOLD_NO_RELAX_COALESCE").is_err();

    let plan: Plan = if names.len() < 2 {
        Plan::empty()
    } else {
        let cand: HashMap<String, u32> = names
            .iter()
            .enumerate()
            .map(|(i, n)| (n.clone(), i as u32))
            .collect();
        let ty_of: Vec<CType> = {
            let m: HashMap<&str, &CType> =
                func.local_vars.iter().map(|d| (d.name.as_str(), &d.ty)).collect();
            names.iter().map(|n| (*m.get(n.as_str()).unwrap()).clone()).collect()
        };

        // Build CFG over a normalized clone, then liveness -> interference.
        let norm = normalize(&func.body);
        let mut cfg = Cfg::new();
        cfg.lower(&norm, EXIT, None, None);
        cfg.resolve_gotos();
        match interference(&cfg, &cand) {
            None => Plan::empty(), // unmodelable CFG: never coalesce
            Some(interfere) => {
                // Vars whose every write is a top-level plain `v = rhs` are "simply-defined" - only these may be RELAXED-merged, so the read/write cast rewrite is total and valid.
                let mut complex: HashSet<String> = HashSet::new();
                mark_complex_stmt(&func.body, &mut complex);
                build_plan(&names, &cand, &ty_of, &cfg, &interfere, &complex, relax)
            }
        }
    };

    // Apply the plan: rename, insert casts for relaxed members, and drop same-class copies (`v = w` where both now share a slot - incl. `x = x;`).
    func.body = apply_plan_stmt(&func.body, &plan);
    if !plan.is_empty() {
        func.local_vars.retain(|d| !plan.rename.contains_key(&d.name));
        for d in func.local_vars.iter_mut() {
            if let Some(s) = plan.rep_ty.get(&d.name) {
                d.ty = s.clone();
            }
        }
    }
    plan.rename.len()
}

/// Two-tier union-find coalescing -> merge plan.
fn build_plan(
    names: &[String],
    cand: &HashMap<String, u32>,
    ty_of: &[CType],
    cfg: &Cfg,
    interfere: &HashSet<(u32, u32)>,
    complex: &HashSet<String>,
    relax: bool,
) -> Plan {
    // Copy pairs (def, src) get merged first so copies collapse to identity.
    let mut copies: Vec<(u32, u32)> = Vec::new();
    for nd in &cfg.nodes {
        if let (Some(d), Some(s)) = (&nd.def, &nd.copy_src) {
            if let (Some(&di), Some(&si)) = (cand.get(d), cand.get(s)) {
                if di != si {
                    copies.push((di, si));
                }
            }
        }
    }
    copies.sort();
    copies.dedup();

    let k = names.len();
    let mut uf = Uf::new(k);
    let same_ty = |a: u32, b: u32| ty_of[a as usize] == ty_of[b as usize];

    // Tier 1: identical-type merges (no casts) - copies first, then greedy.
    for &(d, s) in &copies {
        if same_ty(d, s) {
            uf.try_union(d, s, interfere);
        }
    }
    if k <= GREEDY_CAP {
        for a in 0..k as u32 {
            for b in (a + 1)..k as u32 {
                if same_ty(a, b) && uf.find(a) != uf.find(b) {
                    uf.try_union(a, b, interfere);
                }
            }
        }
    }

    // Tier 2: relaxed cross-type merges (same storage group), only between classes whose every member is simply-defined (so cast insertion is sound).
    if relax && k <= GREEDY_CAP {
        let elig: Vec<bool> = names.iter().map(|n| !complex.contains(n)).collect();
        let grp: Vec<Grp> = ty_of.iter().map(group_of).collect();
        for a in 0..k as u32 {
            for b in (a + 1)..k as u32 {
                if grp[a as usize] != grp[b as usize] {
                    continue;
                }
                let (ra, rb) = (uf.find(a), uf.find(b));
                if ra == rb {
                    continue;
                }
                let ea = uf.members[ra as usize].iter().all(|&m| elig[m as usize]);
                let eb = uf.members[rb as usize].iter().all(|&m| elig[m as usize]);
                if ea && eb {
                    uf.try_union(a, b, interfere);
                }
            }
        }
    }

    // Materialize classes -> plan.
    let mut classes: HashMap<u32, Vec<u32>> = HashMap::new();
    for i in 0..k as u32 {
        classes.entry(uf.find(i)).or_default().push(i);
    }
    let mut plan = Plan::empty();
    for members in classes.values() {
        if members.len() < 2 {
            continue;
        }
        let rep_i = *members
            .iter()
            .min_by(|&&x, &&y| names[x as usize].cmp(&names[y as usize]))
            .unwrap();
        let rep = names[rep_i as usize].clone();
        let first_ty = &ty_of[members[0] as usize];
        let all_same = members.iter().all(|&i| &ty_of[i as usize] == first_ty);
        let slot = if all_same {
            first_ty.clone()
        } else {
            storage_ty(group_of(first_ty))
        };
        for &i in members {
            let nm = &names[i as usize];
            if *nm != rep {
                plan.rename.insert(nm.clone(), rep.clone());
            }
            if ty_of[i as usize] != slot {
                plan.relaxed.insert(nm.clone(), (ty_of[i as usize].clone(), slot.clone()));
            }
        }
        if !all_same {
            plan.rep_ty.insert(rep, slot);
        }
    }
    plan
}

// --------------------------- rewrite (rename + cast insertion) ---------------------------

fn scalar_width(ty: &CType) -> Option<u32> {
    match ty {
        CType::Bool => Some(1),
        CType::Int(sz, _) => Some(match sz {
            IntSize::Char => 1,
            IntSize::Short => 2,
            IntSize::Int => 4,
            IntSize::Long | IntSize::LongLong => 8,
        }),
        CType::Enum(_) => Some(4),
        CType::Pointer(..) => Some(8),
        CType::Float(sz) => Some(match sz {
            FloatSize::Float => 4,
            FloatSize::Double => 8,
            FloatSize::LongDouble => 16,
        }),
        _ => None,
    }
}

/// Build `(outer)inner`, collapsing a redundant adjacent cast when it is provably value-preserving: identical types, pointer-over-pointer (casts compose), or integer-over-wider-integer (the outer truncation subsumes the inner). Anything else is kept verbatim.
fn mk_cast(outer: CType, inner: CExpr) -> CExpr {
    if let CExpr::Cast(mid, e) = &inner {
        let both_ptr = outer.is_pointer() && mid.is_pointer();
        let int_narrow = {
            let is_plain_int = |t: &CType| {
                !t.is_pointer() && !matches!(t, CType::Float(_)) && scalar_width(t).is_some()
            };
            match (scalar_width(&outer), scalar_width(mid)) {
                (Some(wo), Some(wm)) => is_plain_int(&outer) && is_plain_int(mid) && wo <= wm,
                _ => false,
            }
        };
        if outer == *mid || both_ptr || int_narrow {
            return CExpr::Cast(outer, e.clone());
        }
    }
    CExpr::Cast(outer, Box::new(inner))
}

/// Rewrite an expression under the plan: rename merged vars, and for relaxed members emit `(orig_ty)rep` on reads and `rep = (slot_ty)rhs` on plain writes. An assign LHS variable is renamed but never wrapped in a cast (it must stay an lvalue).
fn rewrite_expr(e: &CExpr, plan: &Plan) -> CExpr {
    match e {
        CExpr::Var(v) => {
            let nm = plan.rename.get(v).cloned().unwrap_or_else(|| v.clone());
            match plan.relaxed.get(v) {
                Some((tv, _)) => mk_cast(tv.clone(), CExpr::Var(nm)),
                None => CExpr::Var(nm),
            }
        }
        CExpr::Assign(AssignOp::Assign, lhs, rhs) => {
            if let CExpr::Var(v) = &**lhs {
                let new_rhs = rewrite_expr(rhs, plan);
                let nm = plan.rename.get(v).cloned().unwrap_or_else(|| v.clone());
                let stored = match plan.relaxed.get(v) {
                    Some((_, slot)) => mk_cast(slot.clone(), new_rhs),
                    None => new_rhs,
                };
                return CExpr::Assign(
                    AssignOp::Assign,
                    Box::new(CExpr::Var(nm)),
                    Box::new(stored),
                );
            }
            CExpr::Assign(
                AssignOp::Assign,
                Box::new(rewrite_expr(lhs, plan)),
                Box::new(rewrite_expr(rhs, plan)),
            )
        }
        CExpr::Assign(op, lhs, rhs) => {
            // Compound assign. A var LHS here is complex-written => never relaxed => same-type rename only (no cast).
            if let CExpr::Var(v) = &**lhs {
                let nm = plan.rename.get(v).cloned().unwrap_or_else(|| v.clone());
                return CExpr::Assign(*op, Box::new(CExpr::Var(nm)), Box::new(rewrite_expr(rhs, plan)));
            }
            CExpr::Assign(*op, Box::new(rewrite_expr(lhs, plan)), Box::new(rewrite_expr(rhs, plan)))
        }
        CExpr::Unary(op, a) => CExpr::Unary(*op, Box::new(rewrite_expr(a, plan))),
        CExpr::Binary(op, a, b) => {
            CExpr::Binary(*op, Box::new(rewrite_expr(a, plan)), Box::new(rewrite_expr(b, plan)))
        }
        CExpr::Ternary(a, b, c) => CExpr::Ternary(
            Box::new(rewrite_expr(a, plan)),
            Box::new(rewrite_expr(b, plan)),
            Box::new(rewrite_expr(c, plan)),
        ),
        CExpr::Call(g, args) => CExpr::Call(
            Box::new(rewrite_expr(g, plan)),
            args.iter().map(|x| rewrite_expr(x, plan)).collect(),
        ),
        CExpr::Cast(ty, a) => mk_cast(ty.clone(), rewrite_expr(a, plan)),
        CExpr::Member(a, f) => CExpr::Member(Box::new(rewrite_expr(a, plan)), f.clone()),
        CExpr::MemberPtr(a, f) => CExpr::MemberPtr(Box::new(rewrite_expr(a, plan)), f.clone()),
        CExpr::Index(a, b) => {
            CExpr::Index(Box::new(rewrite_expr(a, plan)), Box::new(rewrite_expr(b, plan)))
        }
        CExpr::Paren(a) => CExpr::Paren(Box::new(rewrite_expr(a, plan))),
        CExpr::SizeofExpr(a) => CExpr::SizeofExpr(Box::new(rewrite_expr(a, plan))),
        _ => e.clone(),
    }
}

fn rewrite_init(init: &Initializer, plan: &Plan) -> Initializer {
    match init {
        Initializer::Expr(e) => Initializer::Expr(rewrite_expr(e, plan)),
        Initializer::List(items) => Initializer::List(
            items
                .iter()
                .map(|it| InitItem {
                    designator: it.designator.clone(),
                    init: rewrite_init(&it.init, plan),
                })
                .collect(),
        ),
        Initializer::String(s) => Initializer::String(s.clone()),
    }
}

fn rewrite_decls(ds: &[VarDecl], plan: &Plan) -> Vec<VarDecl> {
    ds.iter()
        .map(|d| VarDecl { init: d.init.as_ref().map(|i| rewrite_init(i, plan)), ..d.clone() })
        .collect()
}

fn rewrite_for_init(fi: &ForInit, plan: &Plan) -> ForInit {
    match fi {
        ForInit::Expr(e) => ForInit::Expr(rewrite_expr(e, plan)),
        ForInit::Decl(ds) => ForInit::Decl(rewrite_decls(ds, plan)),
    }
}

/// Apply the plan to a statement: rewrite every expression, drop same-class copies (`v = w` with `repof(v)==repof(w)`, including `x = x;`) to `Empty`, and prune the resulting empties from statement lists (labels preserved).
fn apply_plan_stmt(s: &CStmt, plan: &Plan) -> CStmt {
    match s {
        CStmt::Expr(e) => {
            if let CExpr::Assign(AssignOp::Assign, l, r) = e {
                if let (CExpr::Var(v), CExpr::Var(w)) = (&**l, &**r) {
                    if plan.repof(v) == plan.repof(w) {
                        return CStmt::Empty;
                    }
                }
            }
            CStmt::Expr(rewrite_expr(e, plan))
        }
        CStmt::Return(Some(e)) => CStmt::Return(Some(rewrite_expr(e, plan))),
        CStmt::If(c, t, el) => CStmt::If(
            rewrite_expr(c, plan),
            Box::new(apply_plan_stmt(t, plan)),
            el.as_ref().map(|x| Box::new(apply_plan_stmt(x, plan))),
        ),
        CStmt::Switch(c, b) => {
            CStmt::Switch(rewrite_expr(c, plan), Box::new(apply_plan_stmt(b, plan)))
        }
        CStmt::While(c, b) => {
            CStmt::While(rewrite_expr(c, plan), Box::new(apply_plan_stmt(b, plan)))
        }
        CStmt::DoWhile(b, c) => {
            CStmt::DoWhile(Box::new(apply_plan_stmt(b, plan)), rewrite_expr(c, plan))
        }
        CStmt::For(i, c, u, b) => CStmt::For(
            i.as_ref().map(|fi| rewrite_for_init(fi, plan)),
            c.as_ref().map(|e| rewrite_expr(e, plan)),
            u.as_ref().map(|e| rewrite_expr(e, plan)),
            Box::new(apply_plan_stmt(b, plan)),
        ),
        CStmt::Block(items) => CStmt::Block(
            items
                .iter()
                .filter_map(|it| match it {
                    CBlockItem::Stmt(st) => {
                        let ns = apply_plan_stmt(st, plan);
                        if matches!(ns, CStmt::Empty) {
                            None
                        } else {
                            Some(CBlockItem::Stmt(ns))
                        }
                    }
                    CBlockItem::Decl(ds) => Some(CBlockItem::Decl(rewrite_decls(ds, plan))),
                })
                .collect(),
        ),
        CStmt::Sequence(ss) => CStmt::Sequence(
            ss.iter()
                .map(|x| apply_plan_stmt(x, plan))
                .filter(|x| !matches!(x, CStmt::Empty))
                .collect(),
        ),
        CStmt::Labeled(l, b) => CStmt::Labeled(l.clone(), Box::new(apply_plan_stmt(b, plan))),
        CStmt::Decl(ds) => CStmt::Decl(rewrite_decls(ds, plan)),
        _ => s.clone(),
    }
}

// --------------------------- "simply-defined" detection ---------------------------

/// Mark every variable that is ever written in a non-simple way (compound assign, ++/--, or an assignment that is not a top-level `Var = rhs` statement). Such variables are ineligible for relaxed (cast) merging.
fn mark_complex_stmt(s: &CStmt, out: &mut HashSet<String>) {
    match s {
        CStmt::Expr(CExpr::Assign(AssignOp::Assign, l, r)) if matches!(&**l, CExpr::Var(_)) => {
            // Top-level plain assign: the LHS var is a simple write; only its rhs can contribute complex writes.
            mark_complex_expr(r, out);
        }
        CStmt::Expr(e) | CStmt::Return(Some(e)) => mark_complex_expr(e, out),
        CStmt::If(c, t, el) => {
            mark_complex_expr(c, out);
            mark_complex_stmt(t, out);
            if let Some(e) = el {
                mark_complex_stmt(e, out);
            }
        }
        CStmt::Switch(c, b) | CStmt::While(c, b) => {
            mark_complex_expr(c, out);
            mark_complex_stmt(b, out);
        }
        CStmt::DoWhile(b, c) => {
            mark_complex_stmt(b, out);
            mark_complex_expr(c, out);
        }
        CStmt::For(i, c, u, b) => {
            match i {
                Some(ForInit::Expr(e)) => mark_complex_expr(e, out),
                Some(ForInit::Decl(ds)) => ds.iter().for_each(|d| {
                    if let Some(Initializer::Expr(e)) = &d.init {
                        mark_complex_expr(e, out)
                    }
                }),
                None => {}
            }
            if let Some(e) = c {
                mark_complex_expr(e, out);
            }
            if let Some(e) = u {
                mark_complex_expr(e, out);
            }
            mark_complex_stmt(b, out);
        }
        CStmt::Block(items) => items.iter().for_each(|it| match it {
            CBlockItem::Stmt(st) => mark_complex_stmt(st, out),
            CBlockItem::Decl(ds) => ds.iter().for_each(|d| {
                if let Some(Initializer::Expr(e)) = &d.init {
                    mark_complex_expr(e, out)
                }
            }),
        }),
        CStmt::Sequence(ss) => ss.iter().for_each(|x| mark_complex_stmt(x, out)),
        CStmt::Labeled(_, b) => mark_complex_stmt(b, out),
        CStmt::Decl(ds) => ds.iter().for_each(|d| {
            if let Some(Initializer::Expr(e)) = &d.init {
                mark_complex_expr(e, out)
            }
        }),
        _ => {}
    }
}

/// In a non-top-level (or non-plain-assign) context, any var that is assigned or ++/--'d is a complex write.
fn mark_complex_expr(e: &CExpr, out: &mut HashSet<String>) {
    match e {
        CExpr::Assign(_, lhs, rhs) => {
            if let CExpr::Var(v) = &**lhs {
                out.insert(v.clone());
            } else {
                mark_complex_expr(lhs, out);
            }
            mark_complex_expr(rhs, out);
        }
        CExpr::Unary(op, a) => {
            if matches!(
                op,
                UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec
            ) {
                if let CExpr::Var(v) = &**a {
                    out.insert(v.clone());
                }
            }
            mark_complex_expr(a, out);
        }
        CExpr::Binary(_, a, b) | CExpr::Index(a, b) => {
            mark_complex_expr(a, out);
            mark_complex_expr(b, out);
        }
        CExpr::Ternary(a, b, c) => {
            mark_complex_expr(a, out);
            mark_complex_expr(b, out);
            mark_complex_expr(c, out);
        }
        CExpr::Call(g, args) => {
            mark_complex_expr(g, out);
            args.iter().for_each(|a| mark_complex_expr(a, out));
        }
        CExpr::Cast(_, a) | CExpr::Member(a, _) | CExpr::MemberPtr(a, _) | CExpr::Paren(a)
        | CExpr::SizeofExpr(a) => mark_complex_expr(a, out),
        _ => {}
    }
}

// Locals whose address is taken (`&v`) anywhere - excluded from coalescing because aliasing breaks the scalar liveness model. Reuses the shared statement/expression visitors.
fn collect_addr_taken_stmt(s: &CStmt, out: &mut HashSet<String>) {
    visit_stmts(s, &mut |st| {
        stmt_top_exprs(st, &mut |e| {
            visit_expr(e, &mut |x| {
                if let CExpr::Unary(UnaryOp::AddrOf, inner) = x {
                    if let CExpr::Var(n) = inner.as_ref() {
                        out.insert(n.clone());
                    }
                }
            })
        })
    });
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
        let coalesce_on = std::env::var("MANIFOLD_NO_COALESCE").is_err();
        let mut total = 0usize;
        let mut merged = 0usize;
        for decl in tu.decls.iter_mut() {
            if let TopLevelDecl::FuncDef(f) = decl {
                // 1) Fold single-use temporaries first, so coalescing operates on real variables (and its casts don't block any folds). fixpoint so chained temps (t1=*p; t2=t1->f; x=t2) collapse.
                loop {
                    let n = reduce_function(f);
                    total += n;
                    if n == 0 {
                        break;
                    }
                }
                // 2) Merge non-interfering locals (live-range coalescing) + drop identity copies.
                if coalesce_on {
                    merged += run_coalesce(f);
                }
                // 3) Mop up any temporaries coalescing newly made single-use.
                loop {
                    let n = reduce_function(f);
                    total += n;
                    if n == 0 {
                        break;
                    }
                }
            }
        }
        log::info!(
            "var_reduce: coalesced {} locals, folded {} single-use temporaries",
            merged,
            total
        );
    }

    fn inputs(&self) -> &'static [&'static str] {
        // Depend on the emitted TU so this runs strictly after (and solo, on the main DB) ClightEmitPass.
        &["cast_optimized_translation_unit"]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &["cast_optimized_translation_unit"]
    }
}
