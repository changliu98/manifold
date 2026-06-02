//! Standalone goto-reduction pass (default OFF, GOTO_REDUCE=1) running between ClightSelectPass and ClightEmitPass: threads goto chains and removes effect-free lone-Sgoto forwarding blocks on already-typed trees (clight_selected_functions), protecting entry/loop/switch heads and leaving goto cycles intact.
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::x86::types::{ClightStmt, Ident, Node};
use std::collections::{HashMap, HashSet};

pub struct GotoReducePass;

impl IRPass for GotoReducePass {
    fn name(&self) -> &'static str {
        "goto_reduce"
    }

    fn run(&self, db: &mut DecompileDB) {
        // Off by default: post-type-selection forwarding-block threading is largely redundant with select's inline/dedup, so enable with GOTO_REDUCE=1 to evaluate or build it out.
        if std::env::var("GOTO_REDUCE").ok().as_deref() != Some("1") {
            return;
        }

        let mut total_removed = 0usize;
        let n_funcs = db.clight_selected_functions.len();
        for func in db.clight_selected_functions.iter_mut() {
            total_removed += reduce_function(
                &mut func.statements,
                &mut func.successors,
                func.entry_node,
                &func.loop_headers,
                &func.switch_heads,
            );
        }
        eprintln!(
            "[goto_reduce] removed {} forwarding blocks across {} functions",
            total_removed, n_funcs
        );
    }

    fn inputs(&self) -> &'static [&'static str] {
        &["clight_selected_functions"]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &["clight_selected_functions"]
    }
}

// Return t if `stmt` is a lone unconditional `goto t` block (effect-free); otherwise None.
fn lone_goto_target(stmt: &ClightStmt) -> Option<Node> {
    match stmt {
        ClightStmt::Sgoto(t) => Some(*t as Node),
        ClightStmt::Slabel(_, inner) => match inner.as_ref() {
            ClightStmt::Sgoto(t) => Some(*t as Node),
            _ => None,
        },
        _ => None,
    }
}

fn stmt_has_goto_to(stmt: &ClightStmt, target: Node) -> bool {
    let mut targets = Vec::new();
    collect_goto_targets(stmt, &mut targets);
    targets.into_iter().any(|t| t == target)
}

fn collect_goto_targets(stmt: &ClightStmt, out: &mut Vec<Node>) {
    match stmt {
        ClightStmt::Sgoto(t) => out.push(*t as Node),
        ClightStmt::Sifthenelse(_, th, el) => {
            collect_goto_targets(th, out);
            collect_goto_targets(el, out);
        }
        ClightStmt::Sloop(b, i) => {
            collect_goto_targets(b, out);
            collect_goto_targets(i, out);
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss {
                collect_goto_targets(s, out);
            }
        }
        ClightStmt::Slabel(_, inner) => collect_goto_targets(inner, out),
        ClightStmt::Sswitch(_, cases) => {
            for (_, s) in cases {
                collect_goto_targets(s, out);
            }
        }
        _ => {}
    }
}

// Follow a forwarding chain to its terminal target; None if cyclic, so pure goto loops are left untouched.
fn resolve_final(start: Node, forward: &HashMap<Node, Node>) -> Option<Node> {
    let mut seen: HashSet<Node> = HashSet::new();
    seen.insert(start);
    let mut cur = start;
    loop {
        match forward.get(&cur) {
            None => return Some(cur),
            Some(&next) => {
                if !seen.insert(next) {
                    return None;
                }
                cur = next;
            }
        }
    }
}

// Retarget every `Sgoto(x)` to `Sgoto(map[x])` throughout a statement tree.
fn redirect_gotos(stmt: &ClightStmt, map: &HashMap<Node, Node>) -> ClightStmt {
    match stmt {
        ClightStmt::Sgoto(t) => match map.get(&(*t as Node)) {
            Some(&f) => ClightStmt::Sgoto(f as Ident),
            None => stmt.clone(),
        },
        ClightStmt::Sifthenelse(c, th, el) => ClightStmt::Sifthenelse(
            c.clone(),
            Box::new(redirect_gotos(th, map)),
            Box::new(redirect_gotos(el, map)),
        ),
        ClightStmt::Sloop(b, i) => ClightStmt::Sloop(
            Box::new(redirect_gotos(b, map)),
            Box::new(redirect_gotos(i, map)),
        ),
        ClightStmt::Ssequence(ss) => {
            ClightStmt::Ssequence(ss.iter().map(|s| redirect_gotos(s, map)).collect())
        }
        ClightStmt::Slabel(l, inner) => {
            ClightStmt::Slabel(*l, Box::new(redirect_gotos(inner, map)))
        }
        ClightStmt::Sswitch(e, cases) => ClightStmt::Sswitch(
            e.clone(),
            cases
                .iter()
                .map(|(lbl, s)| (lbl.clone(), redirect_gotos(s, map)))
                .collect(),
        ),
        _ => stmt.clone(),
    }
}

// Thread goto chains and remove dead forwarding blocks in one function; returns the count removed.
fn reduce_function(
    stmts: &mut HashMap<Node, ClightStmt>,
    succ: &mut HashMap<Node, Vec<Node>>,
    entry: Node,
    loop_heads: &HashSet<Node>,
    switch_heads: &HashSet<Node>,
) -> usize {
    let protected =
        |n: Node| n == entry || loop_heads.contains(&n) || switch_heads.contains(&n);

    let mut all_removed: HashSet<Node> = HashSet::new();

    // Fixpoint: removing a forwarding block can expose another; bounded as a backstop since resolve_final collapses chains in one pass.
    let mut iters = 0;
    loop {
        iters += 1;
        if iters > 64 {
            break;
        }

        // forwarding(node) = lone-goto block, not protected, not a self-goto.
        let mut forward: HashMap<Node, Node> = HashMap::new();
        for (&n, s) in stmts.iter() {
            if protected(n) {
                continue;
            }
            if let Some(t) = lone_goto_target(s) {
                if t != n {
                    forward.insert(n, t);
                }
            }
        }
        if forward.is_empty() {
            break;
        }

        // CFG predecessors from successors; in flat Clight a predecessor that does not still goto the block reaches it by fall-through (or inlining), so the block must be kept.
        let mut cfg_preds: HashMap<Node, Vec<Node>> = HashMap::new();
        for (&p, ds) in succ.iter() {
            for &d in ds {
                cfg_preds.entry(d).or_default().push(p);
            }
        }
        let mut pre_removable: HashSet<Node> = HashSet::new();
        for &n in forward.keys() {
            let preds_ok = cfg_preds.get(&n).map_or(true, |ps| {
                ps.iter()
                    .all(|p| stmts.get(p).map_or(false, |s| stmt_has_goto_to(s, n)))
            });
            if preds_ok {
                pre_removable.insert(n);
            }
        }

        // thread(node) = final target. Cyclic chains resolve to None and are left as-is.
        let mut redirect: HashMap<Node, Node> = HashMap::new();
        for &n in forward.keys() {
            if let Some(f) = resolve_final(n, &forward) {
                if f != n {
                    redirect.insert(n, f);
                }
            }
        }
        if redirect.is_empty() {
            break;
        }

        let mut changed = false;
        let nodes: Vec<Node> = stmts.keys().copied().collect();
        for node in nodes {
            if let Some(s) = stmts.get(&node) {
                let updated = redirect_gotos(s, &redirect);
                if &updated != s {
                    stmts.insert(node, updated);
                    changed = true;
                }
            }
        }

        // Recount incoming gotos post-thread; a removable block now has none.
        let mut goto_in: HashMap<Node, usize> = HashMap::new();
        for s in stmts.values() {
            let mut targets = Vec::new();
            collect_goto_targets(s, &mut targets);
            for t in targets {
                *goto_in.entry(t).or_insert(0) += 1;
            }
        }
        for n in pre_removable {
            if protected(n) || goto_in.get(&n).copied().unwrap_or(0) > 0 {
                continue;
            }
            let still_forwarding = stmts.get(&n).map_or(false, |s| lone_goto_target(s).is_some());
            if still_forwarding {
                stmts.remove(&n);
                all_removed.insert(n);
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    // Keep the CFG consistent: drop edges touching removed blocks (threaded gotos already carry control to the final targets).
    if !all_removed.is_empty() {
        succ.retain(|k, _| !all_removed.contains(k));
        for ds in succ.values_mut() {
            ds.retain(|d| !all_removed.contains(d));
        }
    }

    all_removed.len()
}
