// Post-emission variable reduction on the final C AST: split-init -> coalesce -> re-fuse per function, with interference from a bitset backward-liveness lattice over an exact CFG.
use crate::decompile::elevator::config::CONFIG;
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::c_pass::types::*;
use crate::decompile::passes::pass::IRPass;
use crate::x86::types::{Address, RTLReg};
use std::collections::{HashMap, HashSet};

// complete read-only walkers

fn visit_expr(e: &CExpr, f: &mut dyn FnMut(&CExpr)) {
    f(e);
    match e {
        CExpr::Unary(_, a)
        | CExpr::Cast(_, a)
        | CExpr::Member(a, _)
        | CExpr::MemberPtr(a, _)
        | CExpr::Paren(a)
        | CExpr::SizeofExpr(a) => visit_expr(a, f),
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
        CExpr::CompoundLit(_, inits) => inits
            .iter()
            .for_each(|init| visit_initializer_exprs(init, f)),
        CExpr::Generic(selector, arms) => {
            visit_expr(selector, f);
            arms.iter().for_each(|(_, arm)| visit_expr(arm, f));
        }
        CExpr::StmtExpr(stmts, tail) => {
            stmts.iter().for_each(|stmt| visit_stmt_exprs(stmt, f));
            visit_expr(tail, f);
        }
        _ => {}
    }
}

fn visit_initializer_exprs(init: &Initializer, f: &mut dyn FnMut(&CExpr)) {
    match init {
        Initializer::Expr(expr) => visit_expr(expr, f),
        Initializer::List(items) => items.iter().for_each(|item| {
            if let Some(designator) = &item.designator {
                visit_designator_exprs(designator, f);
            }
            visit_initializer_exprs(&item.init, f);
        }),
        Initializer::String(_) => {}
    }
}

fn visit_designator_exprs(designator: &Designator, f: &mut dyn FnMut(&CExpr)) {
    match designator {
        Designator::Field(_) => {}
        Designator::Index(expr) => visit_expr(expr, f),
        Designator::Range(first, last) => {
            visit_expr(first, f);
            visit_expr(last, f);
        }
    }
}

fn visit_stmt_exprs(stmt: &CStmt, f: &mut dyn FnMut(&CExpr)) {
    stmt_top_exprs(stmt, &mut |expr| visit_expr(expr, f));
    if let CStmt::Block(items) = stmt {
        for item in items {
            if let CBlockItem::Decl(decls) = item {
                for decl in decls {
                    if let Some(init) = &decl.init {
                        visit_initializer_exprs(init, f);
                    }
                }
            }
        }
    }
    stmt_children(stmt)
        .into_iter()
        .for_each(|child| visit_stmt_exprs(child, f));
}

// Every top-level expr directly in statement `s` (NOT recursing into child statements).
fn stmt_top_exprs(s: &CStmt, f: &mut dyn FnMut(&CExpr)) {
    match s {
        CStmt::Expr(e) | CStmt::Return(Some(e)) => f(e),
        CStmt::If(c, _, _) | CStmt::Switch(c, _) | CStmt::While(c, _) | CStmt::DoWhile(_, c) => {
            f(c)
        }
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
            .filter_map(|it| {
                if let CBlockItem::Stmt(st) = it {
                    Some(st)
                } else {
                    None
                }
            })
            .collect(),
        CStmt::Sequence(v) => v.iter().collect(),
        CStmt::If(_, t, e) => {
            let mut c = vec![t.as_ref()];
            if let Some(e) = e {
                c.push(e.as_ref());
            }
            c
        }
        CStmt::Switch(_, b)
        | CStmt::While(_, b)
        | CStmt::Labeled(_, b) | CStmt::Effect(_, b)
        | CStmt::DoWhile(b, _) => {
            vec![b.as_ref()]
        }
        CStmt::For(_, _, _, b) => vec![b.as_ref()],
        _ => vec![],
    }
}

/// A scalar object lvalue/designator may be wrapped in any number of
/// parentheses without changing what it denotes.
fn paren_var(e: &CExpr) -> Option<&str> {
    match e {
        CExpr::Var(name) => Some(name.as_str()),
        CExpr::Paren(inner) => paren_var(inner),
        _ => None,
    }
}

// statement is a plain `v = rhs;`
fn simple_def<'a>(s: &'a CStmt) -> Option<(&'a str, &'a CExpr)> {
    if let CStmt::Expr(CExpr::Assign(AssignOp::Assign, lhs, rhs)) = s {
        if let Some(v) = paren_var(lhs) {
            return Some((v, rhs.as_ref()));
        }
    }
    None
}

// Expr helpers

/// Collect every variable *read* in an expression (plain `Var` occurrences).
fn collect_vars(e: &CExpr, out: &mut Vec<String>) {
    match e {
        CExpr::Var(n) => out.push(n.clone()),
        CExpr::Unary(_, a)
        | CExpr::Cast(_, a)
        | CExpr::Member(a, _)
        | CExpr::MemberPtr(a, _)
        | CExpr::Paren(a)
        | CExpr::SizeofExpr(a) => collect_vars(a, out),
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
        CExpr::CompoundLit(_, inits) => inits
            .iter()
            .for_each(|init| collect_initializer_vars(init, out)),
        CExpr::Generic(selector, arms) => {
            collect_vars(selector, out);
            arms.iter().for_each(|(_, arm)| collect_vars(arm, out));
        }
        CExpr::StmtExpr(stmts, tail) => {
            stmts.iter().for_each(|stmt| collect_stmt_vars(stmt, out));
            collect_vars(tail, out);
        }
        _ => {}
    }
}

fn collect_initializer_vars(init: &Initializer, out: &mut Vec<String>) {
    match init {
        Initializer::Expr(expr) => collect_vars(expr, out),
        Initializer::List(items) => items.iter().for_each(|item| {
            if let Some(designator) = &item.designator {
                collect_designator_vars(designator, out);
            }
            collect_initializer_vars(&item.init, out);
        }),
        Initializer::String(_) => {}
    }
}

fn collect_designator_vars(designator: &Designator, out: &mut Vec<String>) {
    match designator {
        Designator::Field(_) => {}
        Designator::Index(expr) => collect_vars(expr, out),
        Designator::Range(first, last) => {
            collect_vars(first, out);
            collect_vars(last, out);
        }
    }
}

fn collect_stmt_vars(stmt: &CStmt, out: &mut Vec<String>) {
    stmt_top_exprs(stmt, &mut |expr| collect_vars(expr, out));
    if let CStmt::Block(items) = stmt {
        for item in items {
            if let CBlockItem::Decl(decls) = item {
                for decl in decls {
                    if let Some(init) = &decl.init {
                        collect_initializer_vars(init, out);
                    }
                }
            }
        }
    }
    stmt_children(stmt)
        .into_iter()
        .for_each(|child| collect_stmt_vars(child, out));
}

fn vars(e: &CExpr) -> Vec<String> {
    let mut v = Vec::new();
    collect_vars(e, &mut v);
    v
}

/// Compound assigns and inc/dec are USE-then-DEF (VR-4); non-var LHS and nested assigns are conservatively uses-only, which over-approximates liveness and can only block merges.
fn leaf_def_uses(e: &CExpr) -> (Option<String>, Vec<String>) {
    if let CExpr::Assign(op, lhs, rhs) = e {
        if let Some(x) = paren_var(lhs) {
            if *op == AssignOp::Assign {
                return (Some(x.to_string()), vars(rhs));
            }
            // compound assign: the var's old value is one of the uses
            let mut uses = vec![x.to_string()];
            collect_vars(rhs, &mut uses);
            return (Some(x.to_string()), uses);
        }
    }
    if let CExpr::Unary(op, a) = e {
        if matches!(
            op,
            UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec
        ) {
            if let Some(x) = paren_var(a) {
                return (Some(x.to_string()), vec![x.to_string()]);
            }
        }
    }
    (None, vars(e))
}

/// `Var(a) = Var(b)` -> Some(b): an exact copy whose def/src do not interfere.
fn copy_src(e: &CExpr) -> Option<String> {
    if let CExpr::Assign(AssignOp::Assign, lhs, rhs) = e {
        if paren_var(lhs).is_some() {
            if let Some(b) = paren_var(rhs) {
                return Some(b.to_string());
            }
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
    let mut result = Vec::new();
    if let Some(init) = &d.init {
        collect_initializer_vars(init, &mut result);
    }
    result
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
        CStmt::Effect(l, b) => CStmt::Effect(l.clone(), Box::new(normalize(b))),
        CStmt::Sequence(ss) => CStmt::Sequence(ss.iter().map(normalize).collect()),
        _ => s.clone(),
    }
}

// CFG

struct FlowNode {
    def: Option<String>,
    uses: Vec<String>,
    copy_src: Option<String>,
    succ: Vec<usize>,
    /// Unknown-target jump (unresolved goto / orphan break/continue): modeled as all-candidates-live barrier so any possible target is covered without bailing the whole function.
    barrier: bool,
}

struct Cfg {
    nodes: Vec<FlowNode>,
    labels: HashMap<String, usize>,
    gotos: Vec<(usize, String)>,
}

const EXIT: usize = 0;

impl Cfg {
    fn new() -> Self {
        // node 0 = EXIT sink (no successors).
        Cfg {
            nodes: vec![FlowNode {
                def: None,
                uses: vec![],
                copy_src: None,
                succ: vec![],
                barrier: false,
            }],
            labels: HashMap::new(),
            gotos: Vec::new(),
        }
    }

    fn add(&mut self, def: Option<String>, uses: Vec<String>) -> usize {
        self.nodes.push(FlowNode {
            def,
            uses,
            copy_src: None,
            succ: vec![],
            barrier: false,
        });
        self.nodes.len() - 1
    }

    /// Lower a statement; return its entry node id. `next` is the node reached when the statement completes normally; `brk`/`cont` are the targets of an enclosing loop/switch.
    fn lower(&mut self, s: &CStmt, next: usize, brk: Option<usize>, cont: Option<usize>) -> usize {
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
                    None => self.nodes[id].barrier = true, // no enclosing loop/switch: unknown target
                }
                id
            }
            CStmt::Continue => {
                let id = self.add(None, vec![]);
                match cont {
                    Some(t) => self.nodes[id].succ = vec![t],
                    None => self.nodes[id].barrier = true, // no enclosing loop: unknown target
                }
                id
            }
            CStmt::Effect(_, inner) => self.lower(inner, next, brk, cont),
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

    /// Resolve goto edges; absent labels become barriers instead of poisoning the whole function.
    fn resolve_gotos(&mut self) {
        let fixups = std::mem::take(&mut self.gotos);
        for (id, label) in fixups {
            match self.labels.get(&label) {
                Some(&t) => self.nodes[id].succ = vec![t],
                None => self.nodes[id].barrier = true,
            }
        }
    }
}

// Liveness + interference

#[inline]
fn bit_set(row: &mut [u64], i: u32) {
    row[(i / 64) as usize] |= 1u64 << (i % 64);
}

#[inline]
fn bit_clear(row: &mut [u64], i: u32) {
    row[(i / 64) as usize] &= !(1u64 << (i % 64));
}

/// Symmetric k x k interference bit-matrix over candidate ids (row i = vars interfering with i).
struct BitMatrix {
    w: usize, // words per row
    rows: Vec<u64>,
}

impl BitMatrix {
    fn new(k: usize) -> Self {
        let w = (k + 63) / 64;
        BitMatrix {
            w,
            rows: vec![0u64; k * w],
        }
    }
    fn row(&self, i: u32) -> &[u64] {
        let o = i as usize * self.w;
        &self.rows[o..o + self.w]
    }
    fn set(&mut self, a: u32, b: u32) {
        let o = a as usize * self.w;
        bit_set(&mut self.rows[o..o + self.w], b);
    }
    fn or_into_row(&mut self, a: u32, bits: &[u64]) {
        let o = a as usize * self.w;
        for j in 0..self.w {
            self.rows[o + j] |= bits[j];
        }
    }
    #[cfg(test)]
    fn get(&self, a: u32, b: u32) -> bool {
        self.rows[a as usize * self.w + (b / 64) as usize] >> (b % 64) & 1 == 1
    }
}

/// Build the candidate-only interference relation from a backward may-liveness fixpoint. Returns `Err` only on resource bail (work bound / non-convergence); unknown-target jumps use the barrier model instead of bailing.
fn interference(cfg: &Cfg, cand: &HashMap<String, u32>) -> Result<BitMatrix, &'static str> {
    let n = cfg.nodes.len();
    let k = cand.len();
    // Work bound: skip liveness on pathologically large functions rather than risk a slow fixpoint. Bailing only forgoes coalescing; it is never unsafe.
    if n.saturating_mul(k) > CONFIG.coalesce.work_bound {
        return Err("work-bound");
    }
    let w = (k + 63) / 64;
    // Pre-filter each node's def/uses/copy_src to candidate ids.
    let id_of = |name: &str| cand.get(name).copied();
    let mut node_def: Vec<Option<u32>> = vec![None; n];
    let mut node_copy: Vec<Option<u32>> = vec![None; n];
    let mut use_bits: Vec<u64> = vec![0u64; n * w];
    let all_row: Vec<u64> = {
        let mut r = vec![0u64; w];
        for i in 0..k {
            bit_set(&mut r, i as u32);
        }
        r
    };
    for (i, nd) in cfg.nodes.iter().enumerate() {
        let row = &mut use_bits[i * w..(i + 1) * w];
        if nd.barrier {
            row.copy_from_slice(&all_row); // unknown jump target: everything may be needed
        } else {
            for u in &nd.uses {
                if let Some(id) = id_of(u) {
                    bit_set(row, id);
                }
            }
        }
        node_def[i] = nd.def.as_ref().and_then(|s| id_of(s));
        node_copy[i] = nd.copy_src.as_ref().and_then(|s| id_of(s));
    }

    // Backward may-liveness lattice (join = union). Iterate to fixpoint.
    let mut live_in: Vec<u64> = vec![0u64; n * w];
    let mut scratch: Vec<u64> = vec![0u64; w];
    let mut changed = true;
    let mut guard = 0usize;
    let cap = n.saturating_mul(k).saturating_add(n).saturating_add(16);
    while changed {
        changed = false;
        guard += 1;
        if guard > cap + 4 {
            return Err("fixpoint"); // non-convergence safety net; never coalesce on doubt
        }
        for i in (0..n).rev() {
            // live_out = union live_in[succ]
            scratch.fill(0);
            for &s in &cfg.nodes[i].succ {
                let sr = &live_in[s * w..(s + 1) * w];
                for j in 0..w {
                    scratch[j] |= sr[j];
                }
            }
            // live_in = uses union (live_out \ def)
            if let Some(d) = node_def[i] {
                bit_clear(&mut scratch, d);
            }
            let ur = &use_bits[i * w..(i + 1) * w];
            for j in 0..w {
                scratch[j] |= ur[j];
            }
            let cur = &mut live_in[i * w..(i + 1) * w];
            if scratch[..] != cur[..] {
                cur.copy_from_slice(&scratch);
                changed = true;
            }
        }
    }

    // Interference: at every def, the defined var conflicts with everything live-out there (except itself and, at a copy `d = src`, the source).
    let mut m = BitMatrix::new(k);
    for i in 0..n {
        let Some(d) = node_def[i] else { continue };
        scratch.fill(0);
        for &s in &cfg.nodes[i].succ {
            let sr = &live_in[s * w..(s + 1) * w];
            for j in 0..w {
                scratch[j] |= sr[j];
            }
        }
        bit_clear(&mut scratch, d);
        if let Some(c) = node_copy[i] {
            bit_clear(&mut scratch, c); // copy-related: d and src may share storage here
        }
        m.or_into_row(d, &scratch);
        // symmetric closure: (v, d) for every v live-out at d's def
        for j in 0..w {
            let mut word = scratch[j];
            while word != 0 {
                let v = (j as u32) * 64 + word.trailing_zeros();
                m.set(v, d);
                word &= word - 1;
            }
        }
    }
    Ok(m)
}

// Coalescing

fn is_scalar(ty: &CType) -> bool {
    matches!(
        ty,
        CType::Int(..) | CType::Float(..) | CType::Pointer(..) | CType::Bool | CType::Enum(_)
    )
}

/// Coalescing may change an object's declaration and storage. Restrict it to ordinary automatic scalar locals: storage duration and every object-level qualifier are semantically significant and must remain untouched.
fn is_plain_auto_scalar(d: &VarDecl) -> bool {
    d.storage_class == StorageClass::Auto
        && d.storage_views.is_empty()
        && !d.qualifiers.is_const
        && !d.qualifiers.is_volatile
        && !d.qualifiers.is_restrict
        && is_scalar(&d.ty)
}

struct Uf {
    parent: Vec<u32>,
    members: Vec<Vec<u32>>, // valid only at roots
    membs: Vec<Vec<u64>>,   // roots: bitset of members
    neigh: Vec<Vec<u64>>,   // roots: union of the members' interference rows
}

impl Uf {
    fn new(k: usize, interfere: &BitMatrix) -> Self {
        let w = (k + 63) / 64;
        Uf {
            parent: (0..k as u32).collect(),
            members: (0..k as u32).map(|i| vec![i]).collect(),
            membs: (0..k as u32)
                .map(|i| {
                    let mut r = vec![0u64; w];
                    bit_set(&mut r, i);
                    r
                })
                .collect(),
            neigh: (0..k as u32).map(|i| interfere.row(i).to_vec()).collect(),
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
    /// Union iff no member of one class interferes with any member of the other. Same-type/eligibility is guaranteed by the caller.
    fn try_union(&mut self, a: u32, b: u32) -> bool {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return true;
        }
        let (ru, rv) = (ra as usize, rb as usize);
        if self.neigh[ru]
            .iter()
            .zip(&self.membs[rv])
            .any(|(x, y)| x & y != 0)
        {
            return false;
        }
        let moved = std::mem::take(&mut self.members[rv]);
        self.parent[rv] = ra;
        self.members[ru].extend(moved);
        let mv = std::mem::take(&mut self.membs[rv]);
        for (dst, src) in self.membs[ru].iter_mut().zip(&mv) {
            *dst |= src;
        }
        let nv = std::mem::take(&mut self.neigh[rv]);
        for (dst, src) in self.neigh[ru].iter_mut().zip(&nv) {
            *dst |= src;
        }
        true
    }
}

// Above CONFIG.coalesce.greedy_cap, skip O(k^2) greedy pair enumeration and keep only copy-related coalescing; functions this large also tend to hit the CONFIG.coalesce.work_bound liveness bail first.

// Same-CType merge plan.

struct Plan {
    /// member name -> representative name (the rep itself is absent).
    rename: HashMap<String, String>,
}

impl Plan {
    fn empty() -> Self {
        Plan {
            rename: HashMap::new(),
        }
    }
    fn is_empty(&self) -> bool {
        self.rename.is_empty()
    }
    fn repof<'a>(&'a self, v: &'a str) -> &'a str {
        self.rename.get(v).map(|s| s.as_str()).unwrap_or(v)
    }
}

/// Coalesce non-interfering, identical-CType locals and delete copies that become identities. Cross-type storage reuse is deliberately excluded: preserving every assignment conversion's value, timing, and floating-point environment effects is outside this pass's proof model. Return the applied plan so representation provenance follows the same transformation as the AST.
fn coalesce_locals(func: &mut FuncDef) -> Plan {
    let effect_protected = crate::decompile::effects::c::protected_names(func);
    // Candidates are plain, uninitialized automatic scalar locals whose address is never taken and whose writes are all represented exactly by the scalar CFG. Static/register/extern locals, qualified objects, inited locals, aliased locals, and vars with nested/compound/inc-dec writes are excluded because changing their storage or missing a def is unsound.
    let mut addr_taken: HashSet<String> = HashSet::new();
    collect_addr_taken_stmt(&func.body, &mut addr_taken);
    let mut complex: HashSet<String> = HashSet::new();
    mark_complex_stmt(&func.body, &mut complex);

    let mut names: Vec<String> = func
        .local_vars
        .iter()
        .filter(|d| {
            d.init.is_none()
                && is_plain_auto_scalar(d)
                && !effect_protected.contains(&d.name)
                && !addr_taken.contains(&d.name)
                && !complex.contains(&d.name)
        })
        .map(|d| d.name.clone())
        .collect();
    names.sort();
    names.dedup();

    let plan: Plan = if names.len() < 2 {
        Plan::empty()
    } else {
        let cand: HashMap<String, u32> = names
            .iter()
            .enumerate()
            .map(|(i, n)| (n.clone(), i as u32))
            .collect();
        let ty_of: Vec<CType> = {
            let m: HashMap<&str, &CType> = func
                .local_vars
                .iter()
                .map(|d| (d.name.as_str(), &d.ty))
                .collect();
            names
                .iter()
                .map(|n| (*m.get(n.as_str()).unwrap()).clone())
                .collect()
        };

        // Build CFG over a normalized clone, then liveness -> interference.
        let norm = normalize(&func.body);
        let mut cfg = Cfg::new();
        cfg.lower(&norm, EXIT, None, None);
        cfg.resolve_gotos();
        let (plan, bail) = match interference(&cfg, &cand) {
            Err(reason) => (Plan::empty(), reason), // resource bail: never coalesce on doubt
            Ok(interfere) => (build_plan(&names, &cand, &ty_of, &cfg, &interfere), "-"),
        };
        if std::env::var("MANIFOLD_VR_STATS").is_ok() {
            let barriers = cfg.nodes.iter().filter(|nd| nd.barrier).count();
            eprintln!(
                "vr-stats fn={} k={} nodes={} barriers={} bail={} merged={}",
                func.name,
                names.len(),
                cfg.nodes.len(),
                barriers,
                bail,
                plan.rename.len()
            );
        }
        plan
    };

    // With no merge, preserve the AST byte-for-byte. Besides being cheaper, this prevents an empty plan from rewriting existing cast syntax or deleting a pre-existing self-assignment (which can be volatile).
    if plan.is_empty() {
        return plan;
    }

    // Apply the same-type plan and drop an original distinct-variable copy (`v = w`) when both now share a slot.
    func.body = apply_plan_stmt(&func.body, &plan);
    let committed: HashSet<_> = func.local_vars.iter().filter(|d| d.type_committed)
        .map(|d| plan.repof(&d.name).to_owned()).collect();
    for declaration in &mut func.local_vars {
        declaration.type_committed |= committed.contains(&declaration.name);
    }
    func.local_vars
        .retain(|d| !plan.rename.contains_key(&d.name));
    plan
}

#[cfg(test)]
fn run_coalesce(func: &mut FuncDef) -> usize {
    coalesce_locals(func).rename.len()
}

/// Project existing value origins through the exact, already-applied merge
/// plans. Keep the native function/register identities: two disjoint values
/// sharing a C binding does not imply that their machine storage aliases.
/// This changes no type or frame-coordinate evidence and invents no origins
/// for declarations eliminated without a proven binding replacement.
fn project_variable_origins(db: &mut DecompileDB, plans: &HashMap<String, Plan>) {
    if plans.is_empty() {
        return;
    }
    let mut origins: Vec<_> = db
        .rel_iter::<(Address, RTLReg, String, String)>("emit_c_variable_origin")
        .map(|(function, reg, owner, name)| {
            let representative = plans
                .get(owner)
                .map_or(name.as_str(), |plan| plan.repof(name));
            (*function, *reg, owner.clone(), representative.to_owned())
        })
        .collect();
    origins.sort_unstable();
    origins.dedup();
    db.rel_set(
        "emit_c_variable_origin",
        origins.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
}

/// Same-CType union-find coalescing -> merge plan.
fn build_plan(
    names: &[String],
    cand: &HashMap<String, u32>,
    ty_of: &[CType],
    cfg: &Cfg,
    interfere: &BitMatrix,
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
    let cap = CONFIG.coalesce.greedy_cap;
    let mut uf = Uf::new(k, interfere);
    let same_ty = |a: u32, b: u32| ty_of[a as usize] == ty_of[b as usize];

    // Identical-type merges: copies first, then greedy per type bucket.
    for &(d, s) in &copies {
        if same_ty(d, s) {
            uf.try_union(d, s);
        }
    }
    if k <= cap {
        let mut keys: Vec<&CType> = Vec::new();
        let mut buckets: Vec<Vec<u32>> = Vec::new();
        for i in 0..k {
            match keys.iter().position(|t| **t == ty_of[i]) {
                Some(p) => buckets[p].push(i as u32),
                None => {
                    keys.push(&ty_of[i]);
                    buckets.push(vec![i as u32]);
                }
            }
        }
        for bucket in &buckets {
            for ai in 0..bucket.len() {
                for bi in (ai + 1)..bucket.len() {
                    let (a, b) = (bucket[ai], bucket[bi]);
                    if uf.find(a) != uf.find(b) {
                        uf.try_union(a, b);
                    }
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
        debug_assert!(members
            .iter()
            .all(|&i| ty_of[i as usize] == ty_of[rep_i as usize]));
        for &i in members {
            let nm = &names[i as usize];
            if *nm != rep {
                plan.rename.insert(nm.clone(), rep.clone());
            }
        }
    }
    plan
}

// Rewrite names only. Existing expression and cast structure is preserved.
fn rewrite_expr(e: &CExpr, plan: &Plan) -> CExpr {
    match e {
        CExpr::Var(v) => CExpr::Var(plan.rename.get(v).cloned().unwrap_or_else(|| v.clone())),
        CExpr::Assign(op, lhs, rhs) => CExpr::Assign(
            *op,
            Box::new(rewrite_expr(lhs, plan)),
            Box::new(rewrite_expr(rhs, plan)),
        ),
        CExpr::Unary(op, a) => CExpr::Unary(*op, Box::new(rewrite_expr(a, plan))),
        CExpr::Binary(op, a, b) => CExpr::Binary(
            *op,
            Box::new(rewrite_expr(a, plan)),
            Box::new(rewrite_expr(b, plan)),
        ),
        CExpr::Ternary(a, b, c) => CExpr::Ternary(
            Box::new(rewrite_expr(a, plan)),
            Box::new(rewrite_expr(b, plan)),
            Box::new(rewrite_expr(c, plan)),
        ),
        CExpr::Call(g, args) => CExpr::Call(
            Box::new(rewrite_expr(g, plan)),
            args.iter().map(|x| rewrite_expr(x, plan)).collect(),
        ),
        CExpr::Cast(ty, a) => CExpr::Cast(ty.clone(), Box::new(rewrite_expr(a, plan))),
        CExpr::Member(a, f) => CExpr::Member(Box::new(rewrite_expr(a, plan)), f.clone()),
        CExpr::MemberPtr(a, f) => CExpr::MemberPtr(Box::new(rewrite_expr(a, plan)), f.clone()),
        CExpr::Index(a, b) => CExpr::Index(
            Box::new(rewrite_expr(a, plan)),
            Box::new(rewrite_expr(b, plan)),
        ),
        CExpr::Paren(a) => CExpr::Paren(Box::new(rewrite_expr(a, plan))),
        CExpr::SizeofExpr(a) => CExpr::SizeofExpr(Box::new(rewrite_expr(a, plan))),
        CExpr::CompoundLit(ty, inits) => CExpr::CompoundLit(
            ty.clone(),
            inits.iter().map(|init| rewrite_init(init, plan)).collect(),
        ),
        CExpr::Generic(selector, arms) => CExpr::Generic(
            Box::new(rewrite_expr(selector, plan)),
            arms.iter()
                .map(|(ty, arm)| (ty.clone(), rewrite_expr(arm, plan)))
                .collect(),
        ),
        CExpr::StmtExpr(stmts, tail) => CExpr::StmtExpr(
            stmts
                .iter()
                .map(|stmt| apply_plan_stmt(stmt, plan))
                .collect(),
            Box::new(rewrite_expr(tail, plan)),
        ),
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
                    designator: it
                        .designator
                        .as_ref()
                        .map(|designator| rewrite_designator(designator, plan)),
                    init: rewrite_init(&it.init, plan),
                })
                .collect(),
        ),
        Initializer::String(s) => Initializer::String(s.clone()),
    }
}

fn rewrite_designator(designator: &Designator, plan: &Plan) -> Designator {
    match designator {
        Designator::Field(field) => Designator::Field(field.clone()),
        Designator::Index(expr) => Designator::Index(rewrite_expr(expr, plan)),
        Designator::Range(first, last) => {
            Designator::Range(rewrite_expr(first, plan), rewrite_expr(last, plan))
        }
    }
}

fn rewrite_decls(ds: &[VarDecl], plan: &Plan) -> Vec<VarDecl> {
    ds.iter()
        .map(|d| VarDecl {
            init: d.init.as_ref().map(|i| rewrite_init(i, plan)),
            ..d.clone()
        })
        .collect()
}

fn rewrite_for_init(fi: &ForInit, plan: &Plan) -> ForInit {
    match fi {
        ForInit::Expr(e) => ForInit::Expr(rewrite_expr(e, plan)),
        ForInit::Decl(ds) => ForInit::Decl(rewrite_decls(ds, plan)),
    }
}

/// Apply the plan to a statement: rewrite every expression, drop original distinct-variable copies (`v = w`, `v != w`) whose variables were merged, and prune the resulting empties from statement lists (labels preserved).
fn apply_plan_stmt(s: &CStmt, plan: &Plan) -> CStmt {
    match s {
        CStmt::Expr(e) => {
            if let CExpr::Assign(AssignOp::Assign, l, r) = e {
                if let (Some(v), Some(w)) = (paren_var(l), paren_var(r)) {
                    if v != w && plan.repof(v) == plan.repof(w) {
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
        CStmt::Effect(l, b) => CStmt::Effect(l.clone(), Box::new(apply_plan_stmt(b, plan))),
        CStmt::Decl(ds) => CStmt::Decl(rewrite_decls(ds, plan)),
        _ => s.clone(),
    }
}

// "simply-defined" detection

/// Mark every variable that is ever written in a non-simple way (compound assign, ++/--, or an assignment that is not a top-level `Var = rhs` statement). Such variables are excluded from all coalescing.
fn mark_complex_stmt(s: &CStmt, out: &mut HashSet<String>) {
    match s {
        CStmt::Expr(CExpr::Assign(AssignOp::Assign, l, r)) if paren_var(l).is_some() => {
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
                    if let Some(init) = &d.init {
                        mark_complex_initializer(init, out)
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
                if let Some(init) = &d.init {
                    mark_complex_initializer(init, out)
                }
            }),
        }),
        CStmt::Sequence(ss) => ss.iter().for_each(|x| mark_complex_stmt(x, out)),
        CStmt::Labeled(_, b) | CStmt::Effect(_, b) => mark_complex_stmt(b, out),
        CStmt::Decl(ds) => ds.iter().for_each(|d| {
            if let Some(init) = &d.init {
                mark_complex_initializer(init, out)
            }
        }),
        _ => {}
    }
}

/// In a non-top-level (or non-plain-assign) context, any var that is assigned or ++/--'d is a complex write.
fn mark_complex_expr(e: &CExpr, out: &mut HashSet<String>) {
    match e {
        CExpr::Assign(_, lhs, rhs) => {
            if let Some(v) = paren_var(lhs) {
                out.insert(v.to_string());
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
                if let Some(v) = paren_var(a) {
                    out.insert(v.to_string());
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
        CExpr::CompoundLit(_, inits) => inits
            .iter()
            .for_each(|init| mark_complex_initializer(init, out)),
        CExpr::Generic(selector, arms) => {
            mark_complex_expr(selector, out);
            arms.iter().for_each(|(_, arm)| mark_complex_expr(arm, out));
        }
        CExpr::StmtExpr(stmts, tail) => {
            stmts
                .iter()
                .for_each(|stmt| mark_stmt_expr_writes_complex(stmt, out));
            mark_complex_expr(tail, out);
        }
        CExpr::Cast(_, a)
        | CExpr::Member(a, _)
        | CExpr::MemberPtr(a, _)
        | CExpr::Paren(a)
        | CExpr::SizeofExpr(a) => mark_complex_expr(a, out),
        _ => {}
    }
}

fn mark_complex_initializer(init: &Initializer, out: &mut HashSet<String>) {
    match init {
        Initializer::Expr(expr) => mark_complex_expr(expr, out),
        Initializer::List(items) => items.iter().for_each(|item| {
            if let Some(designator) = &item.designator {
                mark_complex_designator(designator, out);
            }
            mark_complex_initializer(&item.init, out);
        }),
        Initializer::String(_) => {}
    }
}

fn mark_complex_designator(designator: &Designator, out: &mut HashSet<String>) {
    match designator {
        Designator::Field(_) => {}
        Designator::Index(expr) => mark_complex_expr(expr, out),
        Designator::Range(first, last) => {
            mark_complex_expr(first, out);
            mark_complex_expr(last, out);
        }
    }
}

// A statement expression is embedded in one CFG expression node, so writes in
// its internal statements have no separate FlowNode definitions.  Excluding
// those locals from coalescing is conservative and preserves evaluation order.
fn mark_stmt_expr_writes_complex(stmt: &CStmt, out: &mut HashSet<String>) {
    stmt_top_exprs(stmt, &mut |expr| mark_complex_expr(expr, out));
    if let CStmt::Block(items) = stmt {
        for item in items {
            if let CBlockItem::Decl(decls) = item {
                for decl in decls {
                    if let Some(init) = &decl.init {
                        mark_complex_initializer(init, out);
                    }
                }
            }
        }
    }
    stmt_children(stmt)
        .into_iter()
        .for_each(|child| mark_stmt_expr_writes_complex(child, out));
}

// Locals whose address is taken (`&v`) anywhere - excluded from coalescing because aliasing breaks the scalar liveness model. Reuses the shared statement/expression visitors.
fn collect_addr_taken_stmt(s: &CStmt, out: &mut HashSet<String>) {
    visit_stmt_exprs(s, &mut |expr| {
        if let CExpr::Unary(UnaryOp::AddrOf, inner) = expr {
            if let Some(name) = paren_var(inner) {
                out.insert(name.to_string());
            }
        }
    });
}

// Initializer splitting (VR-3a)

/// True when the initializer expression is const-pure: no variable reads, no calls/loads/stores/inc-dec; safe to move below other declarations.
fn const_pure_expr(e: &CExpr) -> bool {
    let mut ok = true;
    visit_expr(e, &mut |x| match x {
        CExpr::Var(_)
        | CExpr::Call(..)
        | CExpr::Assign(..)
        | CExpr::Unary(UnaryOp::Deref, _)
        | CExpr::Unary(UnaryOp::PreInc, _)
        | CExpr::Unary(UnaryOp::PreDec, _)
        | CExpr::Unary(UnaryOp::PostInc, _)
        | CExpr::Unary(UnaryOp::PostDec, _)
        | CExpr::MemberPtr(..)
        | CExpr::Index(..)
        | CExpr::StmtExpr(..) => ok = false,
        _ => {}
    });
    ok
}

/// Turn `T x = const` into a declaration plus a leading assignment so `x` becomes a coalescing candidate. Only plain automatic scalar objects with a const-pure initializer and no escaped address are eligible.
fn split_scalar_inits(func: &mut FuncDef) -> Vec<String> {
    let mut addr_taken: HashSet<String> = HashSet::new();
    collect_addr_taken_stmt(&func.body, &mut addr_taken);

    let splittable = |d: &VarDecl| {
        is_plain_auto_scalar(d)
            && !addr_taken.contains(&d.name)
            && matches!(&d.init, Some(Initializer::Expr(e)) if const_pure_expr(e))
    };
    // A remaining (unsplit) initializer that reads a candidate would observe it before its moved assignment runs, so that candidate must not be split.
    let mut read_by_remaining: HashSet<String> = HashSet::new();
    for d in func.local_vars.iter().filter(|d| !splittable(d)) {
        decl_init_exprs(d, &mut |e| {
            for v in vars(e) {
                read_by_remaining.insert(v);
            }
        });
    }

    // A var excluded only by read_by_remaining has a const-pure init (reads nothing), so it cannot extend read_by_remaining; one pass suffices.
    let mut split: Vec<String> = Vec::new();
    let mut assigns: Vec<CStmt> = Vec::new();
    for d in func.local_vars.iter_mut() {
        if !splittable(d) || read_by_remaining.contains(&d.name) {
            continue;
        }
        let Some(Initializer::Expr(e)) = d.init.clone() else {
            continue;
        };
        assigns.push(CStmt::Expr(CExpr::Assign(
            AssignOp::Assign,
            Box::new(CExpr::Var(d.name.clone())),
            Box::new(e),
        )));
        split.push(d.name.clone());
        d.init = None;
    }
    if split.is_empty() {
        return split;
    }
    let old = std::mem::replace(&mut func.body, CStmt::Empty);
    func.body = match old {
        CStmt::Block(items) => {
            let mut v: Vec<CBlockItem> = assigns.into_iter().map(CBlockItem::Stmt).collect();
            v.extend(items);
            CStmt::Block(v)
        }
        CStmt::Sequence(ss) => {
            let mut v = assigns;
            v.extend(ss);
            CStmt::Sequence(v)
        }
        other => {
            let mut v: Vec<CBlockItem> = assigns.into_iter().map(CBlockItem::Stmt).collect();
            v.push(CBlockItem::Stmt(other));
            CStmt::Block(v)
        }
    };
    split
}

/// Demote a pointer-typed local used as an integer counter (self +/-const plus
/// an == 0 test) to long, so GCC's non-null assumption cannot delete the loop
/// exit.  A variable used uncast anywhere in a dereference address is excluded:
/// `*(p + k)` requires `p` to remain pointer-typed just as much as `*p` does.
fn demote_pointer_counters(func: &mut FuncDef) -> usize {
    let effect_protected = crate::decompile::effects::c::protected_names(func);
    use std::collections::HashSet;

    let has_ptr_local = func.local_vars.iter().any(|d| d.ty.is_pointer());
    if !has_ptr_local {
        return 0;
    }

    fn peel(e: &CExpr) -> &CExpr {
        match e {
            CExpr::Cast(_, inner) | CExpr::Paren(inner) => peel(inner),
            _ => e,
        }
    }
    fn peeled_var(e: &CExpr) -> Option<&str> {
        match peel(e) {
            CExpr::Var(n) => Some(n.as_str()),
            _ => None,
        }
    }
    // Collect variables used in an address expression without an intervening
    // explicit cast. A cast is a valid boundary: `*((char *)counter + k)`
    // remains well-typed if `counter` is later demoted to long.
    fn collect_uncast_address_vars(e: &CExpr, out: &mut HashSet<String>) {
        match e {
            CExpr::Var(n) => {
                out.insert(n.clone());
            }
            CExpr::Cast(_, _) => {}
            CExpr::Unary(_, a) | CExpr::Member(a, _) | CExpr::MemberPtr(a, _) | CExpr::Paren(a) => {
                collect_uncast_address_vars(a, out)
            }
            CExpr::Binary(_, a, b) | CExpr::Index(a, b) => {
                collect_uncast_address_vars(a, out);
                collect_uncast_address_vars(b, out);
            }
            CExpr::Ternary(a, b, c) => {
                collect_uncast_address_vars(a, out);
                collect_uncast_address_vars(b, out);
                collect_uncast_address_vars(c, out);
            }
            CExpr::CompoundLit(_, inits) => inits
                .iter()
                .for_each(|init| collect_uncast_initializer_vars(init, out)),
            CExpr::Generic(selector, arms) => {
                collect_uncast_address_vars(selector, out);
                arms.iter()
                    .for_each(|(_, arm)| collect_uncast_address_vars(arm, out));
            }
            CExpr::StmtExpr(stmts, tail) => {
                for stmt in stmts {
                    collect_uncast_stmt_address_vars(stmt, out);
                }
                collect_uncast_address_vars(tail, out);
            }
            _ => {}
        }
    }

    fn collect_uncast_initializer_vars(init: &Initializer, out: &mut HashSet<String>) {
        match init {
            Initializer::Expr(expr) => collect_uncast_address_vars(expr, out),
            Initializer::List(items) => items.iter().for_each(|item| {
                if let Some(designator) = &item.designator {
                    match designator {
                        Designator::Field(_) => {}
                        Designator::Index(expr) => collect_uncast_address_vars(expr, out),
                        Designator::Range(first, last) => {
                            collect_uncast_address_vars(first, out);
                            collect_uncast_address_vars(last, out);
                        }
                    }
                }
                collect_uncast_initializer_vars(&item.init, out);
            }),
            Initializer::String(_) => {}
        }
    }

    fn collect_uncast_stmt_address_vars(stmt: &CStmt, out: &mut HashSet<String>) {
        stmt_top_exprs(stmt, &mut |expr| collect_uncast_address_vars(expr, out));
        if let CStmt::Block(items) = stmt {
            for item in items {
                if let CBlockItem::Decl(decls) = item {
                    for decl in decls {
                        if let Some(init) = &decl.init {
                            collect_uncast_initializer_vars(init, out);
                        }
                    }
                }
            }
        }
        for child in stmt_children(stmt) {
            collect_uncast_stmt_address_vars(child, out);
        }
    }

    let is_int_const = |e: &CExpr| matches!(peel(e), CExpr::IntLit(_));
    let is_zero = |e: &CExpr| matches!(peel(e), CExpr::IntLit(l) if l.value == 0);

    let mut self_add: HashSet<String> = HashSet::new(); // has `v = ...(v +/- const)...`
    let mut null_cmp: HashSet<String> = HashSet::new(); // has `v ==/!= 0`
    let mut bare_deref: HashSet<String> = HashSet::new(); // dereferenced without a cast

    visit_stmts(&func.body, &mut |s| {
        stmt_top_exprs(s, &mut |top| {
            visit_expr(top, &mut |e| match e {
                CExpr::Assign(AssignOp::Assign, lhs, rhs) => {
                    if let Some(v) = peeled_var(lhs) {
                        let mut found = false;
                        visit_expr(rhs, &mut |sub| {
                            if let CExpr::Binary(BinaryOp::Add | BinaryOp::Sub, a, b) = sub {
                                if (peeled_var(a) == Some(v) && is_int_const(b))
                                    || (peeled_var(b) == Some(v) && is_int_const(a))
                                {
                                    found = true;
                                }
                            }
                        });
                        if found {
                            self_add.insert(v.to_string());
                        }
                    }
                }
                CExpr::Binary(BinaryOp::Eq | BinaryOp::Ne, a, b) => {
                    if let Some(v) = peeled_var(a) {
                        if is_zero(b) {
                            null_cmp.insert(v.to_string());
                        }
                    }
                    if let Some(v) = peeled_var(b) {
                        if is_zero(a) {
                            null_cmp.insert(v.to_string());
                        }
                    }
                }
                CExpr::Unary(UnaryOp::Deref, base)
                | CExpr::Member(base, _)
                | CExpr::MemberPtr(base, _) => collect_uncast_address_vars(base, &mut bare_deref),
                // Only the indexed object's base must stay pointer-typed; the
                // subscript is an integer operand and may still be demoted.
                CExpr::Index(base, _) => collect_uncast_address_vars(base, &mut bare_deref),
                _ => {}
            });
        });
    });

    let mut demoted = 0usize;
    for d in func.local_vars.iter_mut() {
        if d.ty.is_pointer()
            && d.storage_views.is_empty()
            && !d.type_committed
            && !effect_protected.contains(&d.name)
            && self_add.contains(&d.name)
            && null_cmp.contains(&d.name)
            && !bare_deref.contains(&d.name)
        {
            d.ty = CType::long();
            demoted += 1;
        }
    }
    demoted
}

/// Re-absorb surviving split assignments back into their declarations (cosmetic inverse of `split_scalar_inits`); only a leading prefix is absorbed in declaration order, so execution order is preserved exactly.
fn refuse_scalar_inits(func: &mut FuncDef, split: &[String]) {
    if split.is_empty() {
        return;
    }
    let split_set: HashSet<&str> = split.iter().map(String::as_str).collect();
    let mut fused: HashSet<String> = HashSet::new();
    loop {
        let head_def: Option<(String, CExpr)> = {
            let head: Option<&CStmt> = match &func.body {
                CStmt::Block(items) => items.first().and_then(|it| match it {
                    CBlockItem::Stmt(s) => Some(s),
                    CBlockItem::Decl(_) => None,
                }),
                CStmt::Sequence(ss) => ss.first(),
                _ => None,
            };
            head.and_then(simple_def).and_then(|(v, rhs)| {
                if split_set.contains(v) && !fused.contains(v) && const_pure_expr(rhs) {
                    Some((v.to_string(), rhs.clone()))
                } else {
                    None
                }
            })
        };
        let Some((v, rhs)) = head_def else { break };
        let Some(d) = func
            .local_vars
            .iter_mut()
            .find(|d| d.name == v && d.init.is_none())
        else {
            break;
        };
        d.init = Some(Initializer::Expr(rhs));
        fused.insert(v);
        match &mut func.body {
            CStmt::Block(items) => {
                items.remove(0);
            }
            CStmt::Sequence(ss) => {
                ss.remove(0);
            }
            _ => unreachable!("head_def only matches Block/Sequence"),
        }
    }
}

pub struct VarReducePass;

impl IRPass for VarReducePass {
    fn name(&self) -> &'static str {
        "var_reduce"
    }

    fn run(&self, db: &mut DecompileDB) {
        let tu = match db.cast_optimized_translation_unit.as_mut() {
            Some(tu) => tu,
            None => return,
        };
        let mut merged = 0usize;
        let mut split_total = 0usize;
        let mut plans = HashMap::new();
        for decl in tu.decls.iter_mut() {
            if let TopLevelDecl::FuncDef(f) = decl {
                // 0) Split eligible initializers into coalescing candidates; surviving assignments are re-fused at the end.
                let split = split_scalar_inits(f);
                split_total += split.len();
                // 1) Merge non-interfering locals using CFG/liveness proof. Cross-statement single-use folding is deliberately absent: moving an rhs into a later expression needs evaluation-count, path, sequencing, and clobber proofs that this AST pass cannot establish mechanically.
                let plan = coalesce_locals(f);
                merged += plan.rename.len();
                if !plan.is_empty() {
                    // Key on the actual emitted owner, including any header-
                    // collision rename, never on a guessed function spelling.
                    plans.insert(f.name.clone(), plan);
                }
                // 2) Re-fuse surviving split initializers (identity inverse of 0).
                refuse_scalar_inits(f, &split);
                // 3) Retype pointer locals used as integer countdown counters to `long` (UB-safe at -O2).
                demote_pointer_counters(f);
            }
        }
        if let Some(audit) = db.cast_post_emit_audit_trail.as_mut() {
            if let Err(reason) = audit.record(
                crate::decompile::analysis::coverage_pass::PostEmitCheckpoint::VarReduce,
                tu,
            ) {
                log::warn!("coverage: cannot record var_reduce checkpoint: {reason}");
            }
        }
        // Publish the AST and its binding projection together at this pass
        // boundary; downstream readers must not see names that we removed.
        project_variable_origins(db, &plans);
        log::info!(
            "var_reduce: coalesced {} locals, split {} initializers",
            merged,
            split_total
        );
    }

    fn inputs(&self) -> &'static [&'static str] {
        // Depend on the emitted TU so this runs strictly after (and solo, on the main DB) ClightEmitPass.
        &[
            "cast_optimized_translation_unit",
            "cast_post_emit_audit_trail",
            "emit_c_variable_origin",
        ]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "cast_optimized_translation_unit",
            "cast_post_emit_audit_trail",
            "emit_c_variable_origin",
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lv(n: &str) -> VarDecl {
        VarDecl::new(n, CType::long())
    }

    #[test]
    fn coalescing_preserves_type_commitments_on_the_actual_representative() {
        let mut committed = lv("b");
        committed.type_committed = true;
        let mut f = fd(vec![lv("a"), committed], vec![
            assign("a", CExpr::int(1)), callstmt("consume", CExpr::var("a")),
            assign("b", CExpr::int(2)), callstmt("consume", CExpr::var("b")),
        ]);
        assert_eq!(run_coalesce(&mut f), 1);
        assert_eq!(f.local_vars.len(), 1);
        assert!(f.local_vars[0].type_committed);
        assert_eq!(f.local_vars[0].ty, CType::long());
    }

    #[test]
    fn storage_declarations_are_excluded_without_losing_other_coalescing() {
        let mut storage = lv("storage");
        storage.storage_views.push(
            crate::decompile::passes::semantic_counterexample::ledger::ObjectView {
                object: crate::decompile::passes::semantic_counterexample::ledger::ObjectId {
                    function: 1,
                    base: 0,
                },
                offset: 0,
                extent: 8,
            },
        );
        assert!(!is_plain_auto_scalar(&storage));
        let mut function = fd(
            vec![storage, lv("a"), lv("b")],
            vec![
                assign("a", CExpr::int(1)),
                callstmt("consume", CExpr::var("a")),
                assign("b", CExpr::int(2)),
                callstmt("consume", CExpr::var("b")),
                assign("storage", CExpr::int(3)),
                CStmt::Return(Some(CExpr::var("storage"))),
            ],
        );
        assert_eq!(run_coalesce(&mut function), 1);
        assert!(function
            .local_vars
            .iter()
            .any(|v| v.name == "storage" && !v.storage_views.is_empty()));
    }

    fn assign(v: &str, e: CExpr) -> CStmt {
        CStmt::Expr(CExpr::Assign(
            AssignOp::Assign,
            Box::new(CExpr::var(v)),
            Box::new(e),
        ))
    }

    fn callstmt(f: &str, arg: CExpr) -> CStmt {
        CStmt::Expr(CExpr::call(CExpr::var(f), vec![arg]))
    }

    fn add(a: CExpr, b: CExpr) -> CExpr {
        CExpr::Binary(BinaryOp::Add, Box::new(a), Box::new(b))
    }

    fn exact_memcpy_store(dst: &str, value: CExpr) -> CStmt {
        let access_ty = CType::long();
        let source = CExpr::CompoundLit(
            access_ty.clone(),
            vec![Initializer::Expr(CExpr::Cast(
                access_ty.clone(),
                Box::new(value),
            ))],
        );
        CStmt::Expr(CExpr::call(
            CExpr::var("__builtin_memcpy"),
            vec![
                CExpr::Cast(CType::ptr(CType::Void), Box::new(CExpr::var(dst))),
                CExpr::Unary(UnaryOp::AddrOf, Box::new(source)),
                CExpr::SizeofType(access_ty),
            ],
        ))
    }

    fn fd(locals: Vec<VarDecl>, body: Vec<CStmt>) -> FuncDef {
        FuncDef {
            name: "t".into(),
            return_type: CType::long(),
            params: vec![],
            is_variadic: false,
            storage_class: StorageClass::Auto,
            body: CStmt::Block(body.into_iter().map(CBlockItem::Stmt).collect()),
            local_vars: locals,
            loc: SourceLoc::unknown(),
        }
    }

    fn provenance_db(functions: Vec<FuncDef>) -> DecompileDB {
        let mut db = DecompileDB::default();
        db.target_abi = Some(crate::abi::AbiConfig::sysv_x86_64());
        let mut tu = TranslationUnit::new();
        for function in functions {
            tu.add_function(function);
        }
        db.cast_optimized_translation_unit = Some(tu);
        db
    }

    fn origin(db: &mut DecompileDB, function: Address, reg: RTLReg, owner: &str, name: &str) {
        db.rel_push(
            "emit_c_variable_origin",
            (function, reg, owner.to_owned(), name.to_owned()),
        );
    }

    fn origins(db: &DecompileDB) -> std::collections::BTreeSet<(Address, RTLReg, String, String)> {
        db.rel_iter::<(Address, RTLReg, String, String)>("emit_c_variable_origin")
            .cloned()
            .collect()
    }

    fn native_slot(
        db: &mut DecompileDB,
        node: Address,
        reg: RTLReg,
        offset: i64,
        symbol: &'static str,
    ) {
        db.rel_push("stack_var", (100_u64, node, offset, reg));
        db.rel_push("settled_bp_frame_base", (100_u64, node, -8_i64));
        db.rel_push(
            "instruction",
            (
                node, 4_usize, "", "MOV", symbol, "dst", "", "", 0_usize, 0_usize,
            ),
        );
        db.rel_push(
            "op_indirect",
            (symbol, "NONE", "RBP", "NONE", 1_i64, offset, 8_usize),
        );
    }

    fn disjoint_pair(a: &str, b: &str) -> FuncDef {
        fd(
            vec![lv(a), lv(b)],
            vec![
                assign(a, CExpr::int(1)),
                callstmt("consume", CExpr::var(a)),
                assign(b, CExpr::int(2)),
                CStmt::Return(Some(CExpr::var(b))),
            ],
        )
    }

    #[test]
    fn coalescing_preserves_native_identities_and_exported_stack_locations() {
        let mut db = provenance_db(vec![disjoint_pair("a", "b")]);
        origin(&mut db, 100, 101, "t", "a");
        origin(&mut db, 100, 102, "t", "b");
        native_slot(&mut db, 90, 101, -8, "slot_a");
        native_slot(&mut db, 7, 102, -16, "slot_b");
        let before = crate::debug::recovered_types::collect(&db).unwrap();
        assert_eq!(before["variables"].as_array().unwrap().len(), 2);

        VarReducePass.run(&mut db);

        assert_eq!(
            origins(&db),
            std::collections::BTreeSet::from([
                (100, 101, "t".into(), "a".into()),
                (100, 102, "t".into(), "a".into()),
            ])
        );
        let TopLevelDecl::FuncDef(f) =
            &db.cast_optimized_translation_unit.as_ref().unwrap().decls[0]
        else {
            panic!()
        };
        assert_eq!(
            f.local_vars.len(),
            1,
            "no dummy declarations to retain origins"
        );
        let after = crate::debug::recovered_types::collect(&db).unwrap();
        assert_eq!(after["variables"].as_array().unwrap().len(), 2);
        for old in before["variables"].as_array().unwrap() {
            let new = after["variables"]
                .as_array()
                .unwrap()
                .iter()
                .find(|new| new["rbp_offset"] == old["rbp_offset"])
                .unwrap();
            assert_eq!(new["name"], "a");
            for key in ["function_address", "type", "evidence_nodes"] {
                assert_eq!(new[key], old[key], "changed {key}");
            }
        }
    }

    #[test]
    fn provenance_does_not_change_the_coalesced_c_program() {
        let input = disjoint_pair("a", "b");
        let mut expected = input.clone();
        assert_eq!(run_all(&mut expected), 1);
        let mut db = provenance_db(vec![input]);
        origin(&mut db, 100, 101, "t", "a");
        origin(&mut db, 100, 102, "t", "b");
        VarReducePass.run(&mut db);
        assert_eq!(
            db.cast_optimized_translation_unit.as_ref().unwrap().decls[0],
            TopLevelDecl::FuncDef(expected)
        );
    }

    #[test]
    fn provenance_is_scoped_to_the_emitted_function_owner() {
        let mut merged = disjoint_pair("a", "b");
        merged.name = "allocator_local".into();
        let mut untouched = fd(
            vec![lv("a"), lv("b")],
            vec![
                assign("a", CExpr::int(1)),
                assign("b", CExpr::int(2)),
                CStmt::Return(Some(add(CExpr::var("a"), CExpr::var("b")))),
            ],
        );
        untouched.name = "other".into();
        let mut db = provenance_db(vec![merged, untouched]);
        origin(&mut db, 100, 101, "allocator_local", "b");
        origin(&mut db, 200, 101, "other", "b");
        VarReducePass.run(&mut db);
        assert_eq!(
            origins(&db),
            std::collections::BTreeSet::from([
                (100, 101, "allocator_local".into(), "a".into()),
                (200, 101, "other".into(), "b".into()),
            ])
        );
    }

    #[test]
    fn successive_merge_plans_compose_existing_origins() {
        let mut db = provenance_db(vec![disjoint_pair("b", "c")]);
        origin(&mut db, 100, 101, "t", "b");
        origin(&mut db, 100, 102, "t", "c");
        VarReducePass.run(&mut db);
        let TopLevelDecl::FuncDef(f) =
            &mut db.cast_optimized_translation_unit.as_mut().unwrap().decls[0]
        else {
            panic!()
        };
        *f = disjoint_pair("b", "a");
        VarReducePass.run(&mut db);
        let expected = std::collections::BTreeSet::from([
            (100, 101, "t".into(), "a".into()),
            (100, 102, "t".into(), "a".into()),
        ]);
        assert_eq!(origins(&db), expected);
        let tree = db.cast_optimized_translation_unit.clone();
        VarReducePass.run(&mut db);
        assert_eq!(origins(&db), expected);
        assert_eq!(db.cast_optimized_translation_unit, tree);
    }

    #[test]
    fn absent_bindings_do_not_receive_invented_merge_provenance() {
        let mut db = provenance_db(vec![disjoint_pair("a", "b")]);
        origin(&mut db, 100, 101, "t", "b");
        origin(&mut db, 100, 102, "t", "already_removed");
        native_slot(&mut db, 90, 101, -8, "slot_a");
        native_slot(&mut db, 7, 102, -16, "slot_b");
        VarReducePass.run(&mut db);
        assert!(origins(&db).contains(&(100, 102, "t".into(), "already_removed".into())));
        let exported = crate::debug::recovered_types::collect(&db).unwrap();
        assert_eq!(exported["variables"].as_array().unwrap().len(), 1);
        assert_eq!(exported["variables"][0]["rbp_offset"], -8);
    }

    #[test]
    fn multiple_value_origins_of_a_binding_all_follow_its_merge() {
        let mut db = provenance_db(vec![disjoint_pair("a", "b")]);
        for reg in [101, 102, 103] {
            origin(&mut db, 100, reg, "t", "b");
        }
        VarReducePass.run(&mut db);
        assert_eq!(
            origins(&db),
            [101, 102, 103]
                .into_iter()
                .map(|reg| (100, reg, "t".into(), "a".into()))
                .collect()
        );
    }

    #[test]
    fn cross_type_locals_keep_distinct_value_origins() {
        let mut function = disjoint_pair("a", "b");
        function.local_vars[1].ty = CType::int();
        let mut db = provenance_db(vec![function]);
        origin(&mut db, 100, 101, "t", "a");
        origin(&mut db, 100, 102, "t", "b");
        let before = origins(&db);
        VarReducePass.run(&mut db);
        assert_eq!(origins(&db), before);
    }

    #[test]
    fn origin_projection_is_a_declared_read_write_handoff() {
        assert!(VarReducePass.inputs().contains(&"emit_c_variable_origin"));
        assert!(VarReducePass.outputs().contains(&"emit_c_variable_origin"));
    }

    fn fl(value: f64) -> CExpr {
        CExpr::FloatLit(FloatLiteral {
            value,
            suffix: FloatLiteralSuffix::None,
        })
    }

    /// Mirror of VarReducePass::run for a single function.
    fn run_all(f: &mut FuncDef) -> usize {
        let split = split_scalar_inits(f);
        let merged = run_coalesce(f);
        refuse_scalar_inits(f, &split);
        merged
    }

    fn assert_pipeline_identity(mut f: FuncDef) {
        let original = f.clone();
        assert_eq!(run_all(&mut f), 0);
        assert_eq!(f, original);
    }

    #[test]
    fn single_use_assignment_conversion_is_preserved_by_retaining_the_temporary() {
        // Retaining the typed temporary preserves the assignment conversion
        // before a later int-to-pointer cast.
        assert_pipeline_identity(fd(
            vec![VarDecl::new("converted", CType::int())],
            vec![
                assign("converted", add(CExpr::var("source"), CExpr::int(1))),
                callstmt(
                    "consume",
                    CExpr::Cast(CType::ptr(CType::Void), Box::new(CExpr::var("converted"))),
                ),
            ],
        ));
    }

    #[test]
    fn single_use_narrowing_is_preserved_by_retaining_the_temporary() {
        assert_pipeline_identity(fd(
            vec![VarDecl::new("narrowed", CType::char_unsigned())],
            vec![
                assign("narrowed", CExpr::var("source")),
                CStmt::Return(Some(CExpr::var("narrowed"))),
            ],
        ));
    }

    #[test]
    fn aggregate_single_use_temporary_is_retained() {
        let aggregate = CType::Struct("record".into());
        assert_pipeline_identity(fd(
            vec![
                VarDecl::new("source", aggregate.clone()),
                VarDecl::new("copy", aggregate),
            ],
            vec![
                assign("copy", CExpr::var("source")),
                callstmt("consume", CExpr::var("copy")),
            ],
        ));
    }

    #[test]
    fn cross_type_locals_are_never_coalesced() {
        let cases = vec![
            fd(
                vec![
                    VarDecl::new("b", CType::Bool),
                    VarDecl::new("n", CType::long()),
                ],
                vec![
                    assign("b", fl(0.5)),
                    callstmt("use_b", CExpr::var("b")),
                    assign("n", CExpr::int(2)),
                    CStmt::Return(Some(CExpr::var("n"))),
                ],
            ),
            fd(
                vec![
                    VarDecl::new("f", CType::float()),
                    VarDecl::new("d", CType::double()),
                ],
                vec![
                    assign("f", fl(16_777_217.0)),
                    callstmt("use_f", CExpr::var("f")),
                    assign("d", fl(2.0)),
                    CStmt::Return(Some(CExpr::var("d"))),
                ],
            ),
            fd(
                vec![
                    VarDecl::new("byte", CType::char_unsigned()),
                    VarDecl::new("n", CType::long()),
                ],
                vec![
                    assign("byte", CExpr::Cast(CType::uint(), Box::new(fl(0.5)))),
                    callstmt("use_byte", CExpr::var("byte")),
                    assign("n", CExpr::int(2)),
                    CStmt::Return(Some(CExpr::var("n"))),
                ],
            ),
        ];

        for mut f in cases {
            let original = f.clone();
            assert_eq!(run_coalesce(&mut f), 0);
            assert_eq!(f, original);
        }
    }

    #[test]
    fn cross_type_copy_is_retained_with_its_assignment_conversion() {
        let mut f = fd(
            vec![
                VarDecl::new("rounded", CType::float()),
                VarDecl::new("source", CType::double()),
            ],
            vec![
                assign("source", fl(16_777_217.0)),
                assign("rounded", CExpr::var("source")),
                callstmt("use_rounded", CExpr::var("rounded")),
                CStmt::Return(Some(CExpr::int(0))),
            ],
        );
        let original = f.clone();

        assert_eq!(run_coalesce(&mut f), 0);
        assert_eq!(f, original);
    }

    #[test]
    fn volatile_store_and_load_are_retained_and_not_coalesced() {
        let mut volatile = VarDecl::new("v", CType::long());
        volatile.qualifiers.is_volatile = true;
        assert_pipeline_identity(fd(
            vec![volatile.clone()],
            vec![
                assign("v", CExpr::call(CExpr::var("produce"), vec![])),
                CStmt::Return(Some(CExpr::var("v"))),
            ],
        ));

        let mut coalesce = fd(
            vec![volatile, lv("plain")],
            vec![
                assign("v", CExpr::int(1)),
                callstmt("use_v1", CExpr::var("v")),
                callstmt("use_v2", CExpr::var("v")),
                assign("plain", CExpr::int(2)),
                callstmt("use_plain", CExpr::var("plain")),
                CStmt::Return(Some(CExpr::var("plain"))),
            ],
        );
        assert_eq!(run_coalesce(&mut coalesce), 0);
        assert_eq!(coalesce.local_vars.len(), 2);
    }

    #[test]
    fn static_local_is_not_coalesced_with_an_automatic_local() {
        let mut persistent = lv("persistent");
        persistent.storage_class = StorageClass::Static;
        let mut f = fd(
            vec![persistent, lv("per_call")],
            vec![
                assign("persistent", CExpr::int(1)),
                callstmt("use_persistent1", CExpr::var("persistent")),
                callstmt("use_persistent2", CExpr::var("persistent")),
                assign("per_call", CExpr::int(2)),
                callstmt("use_per_call", CExpr::var("per_call")),
                CStmt::Return(Some(CExpr::var("per_call"))),
            ],
        );
        let original = f.clone();

        assert_eq!(run_coalesce(&mut f), 0);
        assert_eq!(f, original);
    }

    #[test]
    fn restrict_qualified_local_is_not_coalesced() {
        let mut restricted = VarDecl::new("restricted", CType::ptr(CType::int()));
        restricted.qualifiers.is_restrict = true;
        let mut f = fd(
            vec![restricted, VarDecl::new("plain", CType::ptr(CType::int()))],
            vec![
                assign(
                    "restricted",
                    CExpr::Cast(CType::ptr(CType::int()), Box::new(CExpr::int(0))),
                ),
                callstmt("use_restricted1", CExpr::var("restricted")),
                callstmt("use_restricted2", CExpr::var("restricted")),
                assign(
                    "plain",
                    CExpr::Cast(CType::ptr(CType::int()), Box::new(CExpr::int(0))),
                ),
                callstmt("use_plain", CExpr::var("plain")),
                CStmt::Return(Some(CExpr::int(0))),
            ],
        );
        let original = f.clone();

        assert_eq!(run_coalesce(&mut f), 0);
        assert_eq!(f, original);
    }

    #[test]
    fn unrelated_merge_preserves_a_volatile_self_assignment() {
        let mut volatile = lv("volatile_value");
        volatile.qualifiers.is_volatile = true;
        let mut f = fd(
            vec![volatile, lv("a"), lv("b")],
            vec![
                assign("volatile_value", CExpr::var("volatile_value")),
                assign("a", CExpr::int(1)),
                callstmt("use_a1", CExpr::var("a")),
                callstmt("use_a2", CExpr::var("a")),
                assign("b", CExpr::int(2)),
                callstmt("use_b", CExpr::var("b")),
                CStmt::Return(Some(CExpr::var("b"))),
            ],
        );

        assert_eq!(run_coalesce(&mut f), 1);
        let CStmt::Block(items) = &f.body else {
            panic!("body must remain a block")
        };
        assert!(matches!(
            items.first(),
            Some(CBlockItem::Stmt(CStmt::Expr(CExpr::Assign(
                AssignOp::Assign,
                lhs,
                rhs
            )))) if matches!(lhs.as_ref(), CExpr::Var(v) if v == "volatile_value")
                && matches!(rhs.as_ref(), CExpr::Var(v) if v == "volatile_value")
        ));
    }

    #[test]
    fn no_merge_is_an_exact_ast_identity_including_nested_casts() {
        let mut f = fd(
            vec![lv("x")],
            vec![CStmt::Return(Some(CExpr::Cast(
                CType::char_unsigned(),
                Box::new(CExpr::Cast(CType::uint(), Box::new(CExpr::var("x")))),
            )))],
        );
        let original = f.clone();

        assert_eq!(run_coalesce(&mut f), 0);
        assert_eq!(f, original);
    }

    #[test]
    fn unrelated_merge_preserves_preexisting_cast_layers() {
        let cast = CExpr::Cast(
            CType::char_unsigned(),
            Box::new(CExpr::Cast(CType::uint(), Box::new(CExpr::var("external")))),
        );
        let mut f = fd(
            vec![lv("a"), lv("b")],
            vec![
                callstmt("observe", cast),
                assign("a", CExpr::int(1)),
                callstmt("use_a1", CExpr::var("a")),
                callstmt("use_a2", CExpr::var("a")),
                assign("b", CExpr::int(2)),
                callstmt("use_b", CExpr::var("b")),
                CStmt::Return(Some(CExpr::var("b"))),
            ],
        );

        assert_eq!(run_coalesce(&mut f), 1);
        let CStmt::Block(items) = &f.body else {
            panic!("body must remain a block")
        };
        assert!(matches!(
            items.first(),
            Some(CBlockItem::Stmt(CStmt::Expr(CExpr::Call(_, args))))
                if matches!(
                    args.first(),
                    Some(CExpr::Cast(outer, inner))
                        if *outer == CType::char_unsigned()
                            && matches!(
                                inner.as_ref(),
                                CExpr::Cast(mid, _) if *mid == CType::uint()
                            )
                )
        ));
    }

    #[test]
    fn nested_writes_are_excluded_from_coalescing() {
        let nested_writes = add(
            CExpr::Assign(
                AssignOp::Assign,
                Box::new(CExpr::var("y")),
                Box::new(CExpr::int(1)),
            ),
            CExpr::Assign(
                AssignOp::Assign,
                Box::new(CExpr::var("z")),
                Box::new(CExpr::int(2)),
            ),
        );
        let mut f = fd(
            vec![lv("y"), lv("z")],
            vec![
                assign("external", nested_writes),
                CStmt::Expr(CExpr::call(
                    CExpr::var("use_pair"),
                    vec![CExpr::var("y"), CExpr::var("z")],
                )),
                CStmt::Return(Some(CExpr::int(0))),
            ],
        );
        let original = f.clone();

        assert_eq!(run_coalesce(&mut f), 0);
        assert_eq!(f, original);
    }

    #[test]
    fn cross_type_coalescing_rejects_int128_and_long() {
        let mut f = fd(
            vec![
                VarDecl::new("wide", CType::Int(IntSize::Int128, Signedness::Signed)),
                lv("narrow"),
            ],
            vec![
                assign("wide", CExpr::int(1)),
                callstmt("use_wide1", CExpr::var("wide")),
                callstmt("use_wide2", CExpr::var("wide")),
                assign("narrow", CExpr::int(2)),
                callstmt("use_narrow", CExpr::var("narrow")),
                CStmt::Return(Some(CExpr::var("narrow"))),
            ],
        );

        assert_eq!(run_coalesce(&mut f), 0);
        assert_eq!(f.local_vars.len(), 2);
    }

    #[test]
    fn cross_type_coalescing_rejects_long_double_and_double() {
        let mut f = fd(
            vec![
                VarDecl::new("wide", CType::Float(FloatSize::LongDouble)),
                VarDecl::new("narrow", CType::double()),
            ],
            vec![
                assign("wide", fl(1.0)),
                callstmt("use_wide1", CExpr::var("wide")),
                callstmt("use_wide2", CExpr::var("wide")),
                assign("narrow", fl(2.0)),
                callstmt("use_narrow", CExpr::var("narrow")),
                CStmt::Return(Some(CExpr::var("narrow"))),
            ],
        );

        assert_eq!(run_coalesce(&mut f), 0);
        assert_eq!(f.local_vars.len(), 2);
    }

    #[test]
    fn single_use_temporary_does_not_move_a_call_past_return() {
        assert_pipeline_identity(fd(
            vec![lv("result")],
            vec![
                assign("result", CExpr::call(CExpr::var("produce"), vec![])),
                CStmt::Return(Some(CExpr::int(0))),
                CStmt::Return(Some(CExpr::var("result"))),
            ],
        ));
    }

    #[test]
    fn single_use_temporary_does_not_move_a_call_past_goto() {
        assert_pipeline_identity(fd(
            vec![lv("result")],
            vec![
                assign("result", CExpr::call(CExpr::var("produce"), vec![])),
                CStmt::Goto("done".into()),
                CStmt::Return(Some(CExpr::var("result"))),
                CStmt::Labeled(
                    Label::Named("done".into()),
                    Box::new(CStmt::Return(Some(CExpr::int(0)))),
                ),
            ],
        ));
    }

    #[test]
    fn single_use_snapshot_is_not_moved_past_increment() {
        assert_pipeline_identity(fd(
            vec![lv("snapshot")],
            vec![
                assign("snapshot", CExpr::var("x")),
                CStmt::Expr(CExpr::Unary(UnaryOp::PostInc, Box::new(CExpr::var("x")))),
                CStmt::Return(Some(CExpr::var("snapshot"))),
            ],
        ));
    }

    #[test]
    fn single_use_snapshot_is_not_moved_into_a_target_that_writes_its_input() {
        let target_write = CExpr::Assign(
            AssignOp::Assign,
            Box::new(CExpr::var("x")),
            Box::new(CExpr::int(2)),
        );
        assert_pipeline_identity(fd(
            vec![lv("snapshot")],
            vec![
                assign("snapshot", CExpr::var("x")),
                CStmt::Return(Some(add(CExpr::var("snapshot"), target_write))),
            ],
        ));

        assert_pipeline_identity(fd(
            vec![lv("snapshot")],
            vec![
                assign("snapshot", CExpr::var("x")),
                CStmt::Expr(CExpr::call(
                    CExpr::var("consume"),
                    vec![
                        CExpr::var("snapshot"),
                        CExpr::Unary(UnaryOp::PostInc, Box::new(CExpr::var("x"))),
                    ],
                )),
            ],
        ));
    }

    #[test]
    fn impure_single_use_rhs_is_not_moved_into_conditional_expression_positions() {
        let conditional_uses = vec![
            CExpr::Ternary(
                Box::new(CExpr::var("cond")),
                Box::new(CExpr::var("result")),
                Box::new(CExpr::int(0)),
            ),
            CExpr::Binary(
                BinaryOp::And,
                Box::new(CExpr::var("cond")),
                Box::new(CExpr::var("result")),
            ),
            CExpr::Binary(
                BinaryOp::Or,
                Box::new(CExpr::var("cond")),
                Box::new(CExpr::var("result")),
            ),
        ];
        for use_expr in conditional_uses {
            assert_pipeline_identity(fd(
                vec![lv("result")],
                vec![
                    assign("result", CExpr::call(CExpr::var("produce"), vec![])),
                    CStmt::Return(Some(use_expr)),
                ],
            ));
        }
    }

    #[test]
    fn single_use_temporary_is_not_substituted_into_a_repeated_loop_condition() {
        assert_pipeline_identity(fd(
            vec![lv("result")],
            vec![
                assign("result", CExpr::call(CExpr::var("produce"), vec![])),
                CStmt::While(CExpr::var("result"), Box::new(CStmt::Empty)),
                CStmt::Return(Some(CExpr::int(0))),
            ],
        ));

        assert_pipeline_identity(fd(
            vec![lv("snapshot")],
            vec![
                assign("snapshot", CExpr::var("x")),
                CStmt::While(
                    CExpr::var("snapshot"),
                    Box::new(CStmt::Expr(CExpr::Unary(
                        UnaryOp::PostDec,
                        Box::new(CExpr::var("x")),
                    ))),
                ),
                CStmt::Return(Some(CExpr::int(0))),
            ],
        ));
    }

    // ---- VR-4: compound assign / inc-dec are USE-then-DEF ----

    #[test]
    fn vr4_leaf_def_uses_shapes() {
        // x += 1  -> def x, uses contain x
        let (d, u) = leaf_def_uses(&CExpr::Assign(
            AssignOp::AddAssign,
            Box::new(CExpr::var("x")),
            Box::new(CExpr::int(1)),
        ));
        assert_eq!(d.as_deref(), Some("x"));
        assert!(u.iter().any(|v| v == "x"));
        // x++  -> def x, uses [x]
        let (d, u) = leaf_def_uses(&CExpr::Unary(UnaryOp::PostInc, Box::new(CExpr::var("x"))));
        assert_eq!(d.as_deref(), Some("x"));
        assert_eq!(u, vec!["x".to_string()]);
        // *p += 1  -> no var def, p used
        let (d, u) = leaf_def_uses(&CExpr::Assign(
            AssignOp::AddAssign,
            Box::new(CExpr::deref(CExpr::var("p"))),
            Box::new(CExpr::int(1)),
        ));
        assert_eq!(d, None);
        assert!(u.iter().any(|v| v == "p"));
    }

    #[test]
    fn paren_wrapped_lvalues_are_recognized_by_the_def_model() {
        let wrapped_x = CExpr::Paren(Box::new(CExpr::Paren(Box::new(CExpr::var("x")))));
        let (d, u) = leaf_def_uses(&CExpr::Assign(
            AssignOp::Assign,
            Box::new(wrapped_x.clone()),
            Box::new(CExpr::var("rhs")),
        ));
        assert_eq!(d.as_deref(), Some("x"));
        assert_eq!(u, vec!["rhs".to_string()]);

        let (d, u) = leaf_def_uses(&CExpr::Unary(UnaryOp::PreInc, Box::new(wrapped_x)));
        assert_eq!(d.as_deref(), Some("x"));
        assert_eq!(u, vec!["x".to_string()]);

        let copy = CExpr::Assign(
            AssignOp::Assign,
            Box::new(CExpr::Paren(Box::new(CExpr::var("x")))),
            Box::new(CExpr::Paren(Box::new(CExpr::var("source")))),
        );
        assert_eq!(copy_src(&copy).as_deref(), Some("source"));
    }

    #[test]
    fn paren_wrapped_address_take_excludes_the_local_from_coalescing() {
        let mut f = fd(
            vec![lv("addressed"), lv("plain")],
            vec![
                callstmt(
                    "escape",
                    CExpr::Unary(
                        UnaryOp::AddrOf,
                        Box::new(CExpr::Paren(Box::new(CExpr::var("addressed")))),
                    ),
                ),
                assign("addressed", CExpr::int(1)),
                callstmt("use_addressed", CExpr::var("addressed")),
                assign("plain", CExpr::int(2)),
                CStmt::Return(Some(CExpr::var("plain"))),
            ],
        );
        let original = f.clone();

        assert_eq!(run_coalesce(&mut f), 0);
        assert_eq!(f, original);
    }

    #[test]
    fn paren_wrapped_nested_writes_are_excluded_from_coalescing() {
        let nested = add(
            CExpr::Assign(
                AssignOp::Assign,
                Box::new(CExpr::Paren(Box::new(CExpr::var("y")))),
                Box::new(CExpr::int(1)),
            ),
            CExpr::Unary(
                UnaryOp::PostInc,
                Box::new(CExpr::Paren(Box::new(CExpr::var("z")))),
            ),
        );
        let mut f = fd(
            vec![lv("y"), lv("z")],
            vec![
                assign("external", nested),
                CStmt::Expr(CExpr::call(
                    CExpr::var("use_pair"),
                    vec![CExpr::var("y"), CExpr::var("z")],
                )),
                CStmt::Return(Some(CExpr::int(0))),
            ],
        );
        let original = f.clone();

        assert_eq!(run_coalesce(&mut f), 0);
        assert_eq!(f, original);
    }

    #[test]
    fn vr4_incdec_def_blocks_uninit_merge() {
        // a++; b++: each ++ is a USE-then-DEF so the other var is live-out at each def -> a/b interfere and must not merge.
        let mut f = fd(
            vec![lv("a"), lv("b")],
            vec![
                CStmt::Expr(CExpr::Unary(UnaryOp::PostInc, Box::new(CExpr::var("a")))),
                CStmt::Expr(CExpr::Unary(UnaryOp::PostInc, Box::new(CExpr::var("b")))),
                CStmt::Return(Some(add(CExpr::var("a"), CExpr::var("b")))),
            ],
        );
        let merged = run_all(&mut f);
        assert_eq!(merged, 0);
        assert_eq!(f.local_vars.len(), 2);
    }

    // ---- VR-3b: unknown-target jumps are barriers, not whole-function bails ----

    #[test]
    fn orphan_continue_is_barrier_not_bail() {
        // Orphan continue is a barrier; a and b defs are downstream so they still coalesce (old code bailed the whole function).
        let mut f = fd(
            vec![lv("a"), lv("b")],
            vec![
                CStmt::If(CExpr::int(1), Box::new(CStmt::Continue), None),
                assign("a", CExpr::int(1)),
                callstmt("f", CExpr::var("a")),
                callstmt("f", CExpr::var("a")),
                assign("b", CExpr::int(2)),
                callstmt("g", CExpr::var("b")),
                CStmt::Return(Some(CExpr::var("b"))),
            ],
        );
        let merged = run_all(&mut f);
        assert_eq!(merged, 1);
        assert_eq!(f.local_vars.len(), 1);
    }

    #[test]
    fn unresolved_goto_is_barrier_not_bail() {
        let mut f = fd(
            vec![lv("a"), lv("b")],
            vec![
                CStmt::If(
                    CExpr::int(1),
                    Box::new(CStmt::Goto("L_nowhere".into())),
                    None,
                ),
                assign("a", CExpr::int(1)),
                callstmt("f", CExpr::var("a")),
                callstmt("f", CExpr::var("a")),
                assign("b", CExpr::int(2)),
                callstmt("g", CExpr::var("b")),
                CStmt::Return(Some(CExpr::var("b"))),
            ],
        );
        let merged = run_all(&mut f);
        assert_eq!(merged, 1);
        assert_eq!(f.local_vars.len(), 1);
    }

    #[test]
    fn barrier_keeps_upstream_defs_apart() {
        // a's def is upstream of the barrier; barrier makes b live-out at a's def, so they interfere and must not merge.
        let mut f = fd(
            vec![lv("a"), lv("b")],
            vec![
                assign("a", CExpr::int(1)),
                callstmt("f", CExpr::var("a")),
                callstmt("f", CExpr::var("a")),
                CStmt::If(CExpr::int(1), Box::new(CStmt::Continue), None),
                assign("b", CExpr::int(2)),
                callstmt("g", CExpr::var("b")),
                CStmt::Return(Some(CExpr::var("b"))),
            ],
        );
        let merged = run_all(&mut f);
        assert_eq!(merged, 0);
        assert_eq!(f.local_vars.len(), 2);
    }

    // ---- goto-cycle (post-CF-4 flat loop): loop-carried vars must not merge ----

    #[test]
    fn goto_cycle_loop_carried_not_merged() {
        // b is live around the back edge at a's def -> (a,b) interfere; the b=a copy exemption applies only at the copy node and must not unlock the merge.
        let mut f = fd(
            vec![lv("a"), lv("b")],
            vec![
                CStmt::Labeled(
                    Label::Named("top".into()),
                    Box::new(assign("b", CExpr::var("a"))),
                ),
                assign("a", add(CExpr::var("a"), CExpr::int(1))),
                CStmt::If(
                    CExpr::Binary(
                        BinaryOp::Lt,
                        Box::new(CExpr::var("a")),
                        Box::new(CExpr::int(10)),
                    ),
                    Box::new(CStmt::Goto("top".into())),
                    None,
                ),
                CStmt::Return(Some(CExpr::var("b"))),
            ],
        );
        let merged = run_all(&mut f);
        assert_eq!(merged, 0);
        assert_eq!(f.local_vars.len(), 2);
    }

    #[test]
    fn interference_is_symmetric() {
        // a = 1; b = 2; return a + b;  -> exactly the pair (a,b), set both ways.
        let body = CStmt::Block(
            vec![
                assign("a", CExpr::int(1)),
                assign("b", CExpr::int(2)),
                CStmt::Return(Some(add(CExpr::var("a"), CExpr::var("b")))),
            ]
            .into_iter()
            .map(CBlockItem::Stmt)
            .collect(),
        );
        let mut cfg = Cfg::new();
        cfg.lower(&normalize(&body), EXIT, None, None);
        cfg.resolve_gotos();
        let mut cand = HashMap::new();
        cand.insert("a".to_string(), 0u32);
        cand.insert("b".to_string(), 1u32);
        let m = interference(&cfg, &cand).expect("no resource bail");
        assert!(m.get(0, 1));
        assert!(m.get(1, 0));
    }

    // ---- VR-3a: initializer splitting ----

    #[test]
    fn split_zero_init_coalesces_disjoint() {
        // a's initializer previously blocked coalescing; after splitting, a and b have disjoint ranges and merge; surviving rep re-fuses `= 0`.
        let mut f = fd(
            vec![lv("a").with_init(Initializer::Expr(CExpr::int(0))), lv("b")],
            vec![
                callstmt("f", CExpr::var("a")),
                callstmt("f", CExpr::var("a")),
                assign("b", CExpr::int(2)),
                callstmt("g", CExpr::var("b")),
                CStmt::Return(Some(CExpr::var("b"))),
            ],
        );
        let merged = run_all(&mut f);
        assert_eq!(merged, 1);
        assert_eq!(f.local_vars.len(), 1);
        assert_eq!(f.local_vars[0].name, "a");
        assert!(f.local_vars[0].init.is_some(), "surviving rep re-fuses = 0");
        // the split assignment was absorbed back into the declaration
        if let CStmt::Block(items) = &f.body {
            assert!(matches!(
                items.first(),
                Some(CBlockItem::Stmt(CStmt::Expr(CExpr::Call(..))))
            ));
        } else {
            panic!("body should still be a block");
        }
    }

    #[test]
    fn split_refuse_is_identity_when_nothing_merges() {
        // a and b interfere; nothing folds; split + refuse must be a no-op.
        let mut f = fd(
            vec![lv("a").with_init(Initializer::Expr(CExpr::int(0))), lv("b")],
            vec![
                assign("b", add(CExpr::var("a"), CExpr::int(1))),
                callstmt("g", CExpr::var("b")),
                CStmt::Return(Some(add(CExpr::var("a"), CExpr::var("b")))),
            ],
        );
        let orig = f.clone();
        let merged = run_all(&mut f);
        assert_eq!(merged, 0);
        assert_eq!(f, orig, "split followed by refuse must be the identity");
    }

    #[test]
    fn nonautomatic_and_qualified_inits_are_not_split() {
        let mut volatile = lv("v").with_init(Initializer::Expr(CExpr::int(0)));
        volatile.qualifiers.is_volatile = true;
        let mut restricted =
            VarDecl::new("r", CType::ptr(CType::int())).with_init(Initializer::Expr(CExpr::Cast(
                CType::ptr(CType::int()),
                Box::new(CExpr::int(0)),
            )));
        restricted.qualifiers.is_restrict = true;
        let mut f = fd(
            vec![
                lv("s")
                    .with_init(Initializer::Expr(CExpr::int(0)))
                    .with_storage(StorageClass::Static),
                VarDecl {
                    qualifiers: TypeQualifiers {
                        is_const: true,
                        ..TypeQualifiers::none()
                    },
                    ..lv("c").with_init(Initializer::Expr(CExpr::int(0)))
                },
                volatile,
                restricted,
            ],
            vec![CStmt::Return(Some(CExpr::int(0)))],
        );
        let split = split_scalar_inits(&mut f);
        assert!(split.is_empty());
        assert!(f.local_vars.iter().all(|d| d.init.is_some()));
    }

    #[test]
    fn pointer_counter_without_pointer_use_is_demoted() {
        let mut f = fd(
            vec![VarDecl::new("p", CType::ptr(CType::Void))],
            vec![
                assign("p", add(CExpr::var("p"), CExpr::int(1))),
                CStmt::If(
                    CExpr::Binary(
                        BinaryOp::Eq,
                        Box::new(CExpr::var("p")),
                        Box::new(CExpr::int(0)),
                    ),
                    Box::new(CStmt::Empty),
                    None,
                ),
            ],
        );

        assert_eq!(demote_pointer_counters(&mut f), 1);
        assert_eq!(f.local_vars[0].ty, CType::long());
    }

    #[test]
    fn pointer_counter_used_in_offset_deref_is_not_demoted() {
        let pointer_ty = CType::ptr(CType::Void);
        let mut f = fd(
            vec![VarDecl::new("p", pointer_ty.clone())],
            vec![
                assign("p", add(CExpr::var("p"), CExpr::int(1))),
                CStmt::Expr(CExpr::Assign(
                    AssignOp::Assign,
                    Box::new(CExpr::deref(add(CExpr::var("p"), CExpr::int(-1)))),
                    Box::new(CExpr::int(7)),
                )),
                CStmt::If(
                    CExpr::Binary(
                        BinaryOp::Eq,
                        Box::new(CExpr::var("p")),
                        Box::new(CExpr::int(0)),
                    ),
                    Box::new(CStmt::Empty),
                    None,
                ),
            ],
        );

        assert_eq!(demote_pointer_counters(&mut f), 0);
        assert_eq!(f.local_vars[0].ty, pointer_ty);
    }

    #[test]
    fn compound_literal_memcpy_value_remains_live_across_another_definition() {
        let mut f = fd(
            vec![lv("saved"), lv("scratch")],
            vec![
                assign("saved", CExpr::var("source")),
                assign("scratch", CExpr::call(CExpr::var("produce"), vec![])),
                exact_memcpy_store("destination", CExpr::var("saved")),
                CStmt::Return(Some(CExpr::var("scratch"))),
            ],
        );
        let original = f.clone();

        assert_eq!(run_coalesce(&mut f), 0);
        assert_eq!(f, original);
    }

    #[test]
    fn compound_literal_reads_are_renamed_after_safe_coalescing() {
        let mut f = fd(
            vec![lv("first"), lv("second")],
            vec![
                assign("first", CExpr::int(1)),
                exact_memcpy_store("destination", CExpr::var("first")),
                assign("second", CExpr::int(2)),
                exact_memcpy_store("destination", add(CExpr::var("second"), CExpr::int(3))),
                CStmt::Return(Some(CExpr::int(0))),
            ],
        );

        assert_eq!(run_coalesce(&mut f), 1);
        assert_eq!(f.local_vars.len(), 1);
        let survivor = f.local_vars[0].name.clone();
        let mut referenced = Vec::new();
        visit_stmt_exprs(&f.body, &mut |expr| collect_vars(expr, &mut referenced));
        assert!(referenced.iter().any(|name| name == &survivor));
        assert!(!referenced
            .iter()
            .any(|name| name != &survivor && matches!(name.as_str(), "first" | "second")));
    }

    #[test]
    fn statement_expression_block_initializer_keeps_its_source_live() {
        let nested = CStmt::Block(vec![CBlockItem::Decl(vec![
            lv("nested").with_init(Initializer::Expr(CExpr::var("saved")))
        ])]);
        let stmt_expr = CExpr::StmtExpr(vec![nested], Box::new(CExpr::int(0)));
        let mut f = fd(
            vec![lv("saved"), lv("scratch")],
            vec![
                assign("saved", CExpr::var("source")),
                assign("scratch", CExpr::call(CExpr::var("produce"), vec![])),
                callstmt("consume", stmt_expr),
                CStmt::Return(Some(CExpr::var("scratch"))),
            ],
        );
        let original = f.clone();

        assert_eq!(run_coalesce(&mut f), 0);
        assert_eq!(f, original);
    }

    #[test]
    fn nested_block_initializer_address_take_excludes_the_local() {
        let nested = CStmt::Block(vec![CBlockItem::Decl(vec![VarDecl::new(
            "pointer",
            CType::ptr(CType::long()),
        )
        .with_init(Initializer::Expr(CExpr::addr_of(CExpr::var("addressed"))))])]);
        let mut f = fd(
            vec![lv("addressed"), lv("other")],
            vec![
                assign("addressed", CExpr::int(1)),
                nested,
                assign("other", CExpr::int(2)),
                CStmt::Return(Some(CExpr::var("other"))),
            ],
        );
        let original = f.clone();

        assert_eq!(run_coalesce(&mut f), 0);
        assert_eq!(f, original);
    }
}
