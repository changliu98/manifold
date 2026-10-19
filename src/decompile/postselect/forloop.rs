// Loop recognition on the final C AST: wrap goto-cycles the upstream structurer dropped into while(1) with back-edges as continue, under a per-function do-no-harm guard on goto count.

use crate::decompile::elevator::config::CONFIG;
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::c_pass::types::*;
use crate::decompile::passes::pass::IRPass;
use std::collections::{HashMap, HashSet};

// Goto/label queries

fn has_goto_or_label(s: &CStmt) -> bool {
    match s {
        CStmt::Goto(_) => true,
        CStmt::Labeled(Label::Named(_), _) => true,
        CStmt::Labeled(_, inner) | CStmt::Effect(_, inner) => has_goto_or_label(inner),
        CStmt::Block(items) => items.iter().any(|it| match it {
            CBlockItem::Stmt(st) => has_goto_or_label(st),
            _ => false,
        }),
        CStmt::Sequence(v) => v.iter().any(has_goto_or_label),
        CStmt::If(_, t, e) => {
            has_goto_or_label(t) || e.as_ref().map_or(false, |x| has_goto_or_label(x))
        }
        CStmt::Switch(_, b) | CStmt::While(_, b) | CStmt::DoWhile(b, _) => has_goto_or_label(b),
        CStmt::For(_, _, _, b) => has_goto_or_label(b),
        _ => false,
    }
}

fn count_gotos(s: &CStmt) -> usize {
    match s {
        CStmt::Goto(_) => 1,
        CStmt::Labeled(_, inner) | CStmt::Effect(_, inner) => count_gotos(inner),
        CStmt::Block(items) => items
            .iter()
            .map(|it| match it {
                CBlockItem::Stmt(st) => count_gotos(st),
                _ => 0,
            })
            .sum(),
        CStmt::Sequence(v) => v.iter().map(count_gotos).sum(),
        CStmt::If(_, t, e) => count_gotos(t) + e.as_ref().map_or(0, |x| count_gotos(x)),
        CStmt::Switch(_, b) | CStmt::While(_, b) | CStmt::DoWhile(b, _) => count_gotos(b),
        CStmt::For(_, _, _, b) => count_gotos(b),
        _ => 0,
    }
}

fn count_loops(s: &CStmt) -> usize {
    let here = matches!(s, CStmt::While(..) | CStmt::For(..) | CStmt::DoWhile(..)) as usize;
    let nested = match s {
        CStmt::Labeled(_, inner) | CStmt::Effect(_, inner) => count_loops(inner),
        CStmt::Block(items) => items
            .iter()
            .map(|it| match it {
                CBlockItem::Stmt(st) => count_loops(st),
                _ => 0,
            })
            .sum(),
        CStmt::Sequence(v) => v.iter().map(count_loops).sum(),
        CStmt::If(_, t, e) => count_loops(t) + e.as_ref().map_or(0, |x| count_loops(x)),
        CStmt::Switch(_, b) | CStmt::While(_, b) | CStmt::DoWhile(b, _) => count_loops(b),
        CStmt::For(_, _, _, b) => count_loops(b),
        _ => 0,
    };
    here + nested
}

fn collect_labels(s: &CStmt, out: &mut HashSet<String>) {
    match s {
        CStmt::Labeled(Label::Named(n), inner) => {
            out.insert(n.clone());
            collect_labels(inner, out);
        }
        CStmt::Labeled(_, inner) | CStmt::Effect(_, inner) => collect_labels(inner, out),
        CStmt::Block(items) => items.iter().for_each(|it| {
            if let CBlockItem::Stmt(st) = it {
                collect_labels(st, out)
            }
        }),
        CStmt::Sequence(v) => v.iter().for_each(|x| collect_labels(x, out)),
        CStmt::If(_, t, e) => {
            collect_labels(t, out);
            if let Some(x) = e {
                collect_labels(x, out)
            }
        }
        CStmt::Switch(_, b)
        | CStmt::While(_, b)
        | CStmt::DoWhile(b, _)
        | CStmt::For(_, _, _, b) => collect_labels(b, out),
        _ => {}
    }
}

fn collect_goto_targets(s: &CStmt, out: &mut Vec<String>) {
    match s {
        CStmt::Goto(t) => out.push(t.clone()),
        CStmt::Labeled(_, inner) | CStmt::Effect(_, inner) => collect_goto_targets(inner, out),
        CStmt::Block(items) => items.iter().for_each(|it| {
            if let CBlockItem::Stmt(st) = it {
                collect_goto_targets(st, out)
            }
        }),
        CStmt::Sequence(v) => v.iter().for_each(|x| collect_goto_targets(x, out)),
        CStmt::If(_, t, e) => {
            collect_goto_targets(t, out);
            if let Some(x) = e {
                collect_goto_targets(x, out)
            }
        }
        CStmt::Switch(_, b)
        | CStmt::While(_, b)
        | CStmt::DoWhile(b, _)
        | CStmt::For(_, _, _, b) => collect_goto_targets(b, out),
        _ => {}
    }
}

// Safety net: every goto must still resolve to a defined label after rewriting.
fn all_gotos_resolve(s: &CStmt) -> bool {
    let mut labels = HashSet::new();
    collect_labels(s, &mut labels);
    let mut targets = Vec::new();
    collect_goto_targets(s, &mut targets);
    targets.iter().all(|t| labels.contains(t))
}

// Conservative: unknown/loop/switch => false.
fn stmt_diverges(s: &CStmt) -> bool {
    match s {
        CStmt::Goto(_) | CStmt::Break | CStmt::Continue | CStmt::Return(_) => true,
        CStmt::If(_, t, Some(e)) => stmt_diverges(t) && stmt_diverges(e),
        CStmt::Block(items) => items
            .iter()
            .rev()
            .find_map(|it| match it {
                CBlockItem::Stmt(st) => Some(st),
                _ => None,
            })
            .map_or(false, stmt_diverges),
        CStmt::Sequence(v) => v.last().map_or(false, stmt_diverges),
        CStmt::Labeled(_, b) | CStmt::Effect(_, b) => stmt_diverges(b),
        _ => false,
    }
}

// `continue` passes through `switch` but not nested loops; recurse into switches but stop at loops.
fn contains_backedge(s: &CStmt, h: &str) -> bool {
    match s {
        CStmt::Goto(t) => t.as_str() == h,
        CStmt::While(..) | CStmt::DoWhile(..) | CStmt::For(..) => false,
        CStmt::Switch(_, b) => contains_backedge(b, h),
        CStmt::If(_, t, e) => {
            contains_backedge(t, h) || e.as_ref().map_or(false, |x| contains_backedge(x, h))
        }
        CStmt::Block(items) => items.iter().any(|it| match it {
            CBlockItem::Stmt(st) => contains_backedge(st, h),
            _ => false,
        }),
        CStmt::Sequence(v) => v.iter().any(|x| contains_backedge(x, h)),
        CStmt::Labeled(_, b) | CStmt::Effect(_, b) => contains_backedge(b, h),
        _ => false,
    }
}

// Top-level break/continue belongs to an enclosing loop/switch; wrapping would silently re-target it.
fn captures_break_or_continue(s: &CStmt) -> bool {
    match s {
        CStmt::Break | CStmt::Continue => true,
        CStmt::While(..) | CStmt::DoWhile(..) | CStmt::For(..) | CStmt::Switch(..) => false,
        CStmt::If(_, t, e) => {
            captures_break_or_continue(t)
                || e.as_ref().map_or(false, |x| captures_break_or_continue(x))
        }
        CStmt::Block(items) => items.iter().any(|it| match it {
            CBlockItem::Stmt(st) => captures_break_or_continue(st),
            _ => false,
        }),
        CStmt::Sequence(v) => v.iter().any(captures_break_or_continue),
        CStmt::Labeled(_, b) | CStmt::Effect(_, b) => captures_break_or_continue(b),
        _ => false,
    }
}

fn header_label(s: &CStmt) -> Option<String> {
    match s {
        CStmt::Labeled(Label::Named(n), _) => Some(n.clone()),
        _ => None,
    }
}

// Peel one `Labeled(h, _)` layer off the loop header (keeps any stacked inner labels).
fn strip_header(s: CStmt, h: &str) -> CStmt {
    match s {
        CStmt::Labeled(Label::Named(n), inner) if n == h => *inner,
        other => other,
    }
}

// Recurses through switch/if (continue not captured), stops at nested loops.
fn convert_backedges(s: CStmt, h: &str) -> CStmt {
    match s {
        CStmt::Goto(t) if t == h => CStmt::Continue,
        CStmt::While(..) | CStmt::DoWhile(..) | CStmt::For(..) => s,
        CStmt::Switch(c, b) => CStmt::Switch(c, Box::new(convert_backedges(*b, h))),
        CStmt::If(c, t, e) => CStmt::If(
            c,
            Box::new(convert_backedges(*t, h)),
            e.map(|x| Box::new(convert_backedges(*x, h))),
        ),
        CStmt::Block(items) => CStmt::Block(
            items
                .into_iter()
                .map(|it| match it {
                    CBlockItem::Stmt(st) => CBlockItem::Stmt(convert_backedges(st, h)),
                    d => d,
                })
                .collect(),
        ),
        CStmt::Sequence(v) => {
            CStmt::Sequence(v.into_iter().map(|x| convert_backedges(x, h)).collect())
        }
        CStmt::Labeled(l, b) => CStmt::Labeled(l, Box::new(convert_backedges(*b, h))),
        CStmt::Effect(l, b) => CStmt::Effect(l, Box::new(convert_backedges(*b, h))),
        other => other,
    }
}

// Block <-> stmt view

fn items_to_stmts(items: Vec<CBlockItem>) -> Vec<CStmt> {
    items
        .into_iter()
        .map(|it| match it {
            CBlockItem::Stmt(s) => s,
            CBlockItem::Decl(d) => CStmt::Decl(d),
        })
        .collect()
}

fn stmts_to_items(stmts: Vec<CStmt>) -> Vec<CBlockItem> {
    stmts
        .into_iter()
        .map(|s| match s {
            CStmt::Decl(d) => CBlockItem::Decl(d),
            other => CBlockItem::Stmt(other),
        })
        .collect()
}

// Core recursion

fn recover(
    s: CStmt,
    refs: &HashMap<String, usize>,
    structural_loop_headers: &HashSet<String>,
) -> CStmt {
    match s {
        CStmt::Block(items) => {
            let stmts: Vec<CStmt> = items_to_stmts(items)
                .into_iter()
                .map(|x| recover(x, refs, structural_loop_headers))
                .collect();
            let stmts = if_convert_seq(stmts, refs, structural_loop_headers);
            CStmt::Block(stmts_to_items(recover_seq(
                stmts,
                refs,
                structural_loop_headers,
            )))
        }
        CStmt::Sequence(v) => {
            let v: Vec<CStmt> = v
                .into_iter()
                .map(|x| recover(x, refs, structural_loop_headers))
                .collect();
            let v = if_convert_seq(v, refs, structural_loop_headers);
            CStmt::Sequence(recover_seq(v, refs, structural_loop_headers))
        }
        CStmt::If(c, t, e) => CStmt::If(
            c,
            Box::new(recover(*t, refs, structural_loop_headers)),
            e.map(|x| Box::new(recover(*x, refs, structural_loop_headers))),
        ),
        CStmt::Switch(c, b) => {
            CStmt::Switch(c, Box::new(recover(*b, refs, structural_loop_headers)))
        }
        CStmt::While(c, b) => CStmt::While(c, Box::new(recover(*b, refs, structural_loop_headers))),
        CStmt::DoWhile(b, c) => {
            CStmt::DoWhile(Box::new(recover(*b, refs, structural_loop_headers)), c)
        }
        CStmt::For(i, c, u, b) => CStmt::For(
            i,
            c,
            u,
            Box::new(recover(*b, refs, structural_loop_headers)),
        ),
        CStmt::Labeled(l, b) => {
            let b = recover(*b, refs, structural_loop_headers);
            // Only `while`: do-while/for have a different continue target. Skips nested loops.
            let b = match (&l, b) {
                (Label::Named(h), CStmt::While(c, body)) => {
                    CStmt::While(c, Box::new(convert_backedges(*body, h)))
                }
                (_, b) => b,
            };
            CStmt::Labeled(l, Box::new(b))
        }
        other => other,
    }
}

// `if (C) goto L;` (no else, then is exactly a goto) -> (C, L).
fn as_if_goto(s: &CStmt) -> Option<(CExpr, String)> {
    if let CStmt::If(c, then, None) = s {
        if let Some(l) = as_single_goto(then) {
            return Some((c.clone(), l));
        }
    }
    None
}

fn as_single_goto(s: &CStmt) -> Option<String> {
    match s {
        CStmt::Goto(l) => Some(l.clone()),
        CStmt::Block(items) => {
            let mut it = items.iter().filter_map(|x| match x {
                CBlockItem::Stmt(st) => Some(st),
                _ => None,
            });
            match (it.next(), it.next()) {
                (Some(st), None) => as_single_goto(st),
                _ => None,
            }
        }
        CStmt::Sequence(v) if v.len() == 1 => as_single_goto(&v[0]),
        _ => None,
    }
}

// Semantics-preserving negation, preferring a flipped comparison for readability.
fn negate(c: &CExpr) -> CExpr {
    match c {
        CExpr::Unary(UnaryOp::Not, inner) => (**inner).clone(),
        CExpr::Binary(op, a, b) => {
            let flip = match op {
                BinaryOp::Eq => Some(BinaryOp::Ne),
                BinaryOp::Ne => Some(BinaryOp::Eq),
                BinaryOp::Lt => Some(BinaryOp::Ge),
                BinaryOp::Ge => Some(BinaryOp::Lt),
                BinaryOp::Gt => Some(BinaryOp::Le),
                BinaryOp::Le => Some(BinaryOp::Gt),
                _ => None,
            };
            match flip {
                Some(f) => CExpr::Binary(f, a.clone(), b.clone()),
                None => CExpr::Unary(UnaryOp::Not, Box::new(c.clone())),
            }
        }
        _ => CExpr::Unary(UnaryOp::Not, Box::new(c.clone())),
    }
}

// If-conversion: `if (C) goto L; S; L:` (single-ref L) -> `if (!C) { S }`. Sound regardless of S's internal labels since `if` captures neither break nor continue.
fn if_convert_seq(
    mut items: Vec<CStmt>,
    refs: &HashMap<String, usize>,
    structural_loop_headers: &HashSet<String>,
) -> Vec<CStmt> {
    let mut i = 0;
    while i < items.len() {
        if let Some((c, l)) = as_if_goto(&items[i]) {
            if refs.get(&l).copied().unwrap_or(0) == 1 {
                if let Some(j) = (i + 1..items.len())
                    .find(|&k| header_label(&items[k]).as_deref() == Some(l.as_str()))
                {
                    if j > i + 1 {
                        let s_region: Vec<CStmt> = items[i + 1..j].to_vec();
                        let if_stmt = CStmt::If(
                            negate(&c),
                            Box::new(recover(
                                CStmt::Block(stmts_to_items(s_region)),
                                refs,
                                structural_loop_headers,
                            )),
                            None,
                        );
                        let stripped = strip_header(items[j].clone(), &l);
                        items.splice(i..=j, vec![if_stmt, stripped]);
                    }
                }
            }
        }
        i += 1;
    }
    items
}

fn recover_seq(
    mut items: Vec<CStmt>,
    refs: &HashMap<String, usize>,
    structural_loop_headers: &HashSet<String>,
) -> Vec<CStmt> {
    let mut i = 0;
    while i < items.len() {
        let h = match header_label(&items[i]) {
            Some(h) => h,
            None => {
                i += 1;
                continue;
            }
        };

        // A label-layout cycle is not CFG evidence.  Only recover a loop when
        // the earlier Cshminor dominator/back-edge analysis proved this exact
        // node to be a valid natural-loop header.  In particular, a dispatch
        // label inside an already structured loop can receive gotos from case
        // lowering without being a second loop header.
        if !structural_loop_headers.contains(&h) {
            i += 1;
            continue;
        }

        let mut back_max: Option<usize> = None;
        for j in i..items.len() {
            if contains_backedge(&items[j], &h) {
                back_max = Some(j);
            }
        }
        let bm = match back_max {
            Some(bm) => bm,
            None => {
                i += 1;
                continue;
            }
        };

        let region = &items[i..=bm];
        // Skip regions with decls (re-running an initializer changes semantics) or top-level break/continue (belongs to an enclosing construct; wrapping would re-target it).
        if region
            .iter()
            .any(|s| matches!(s, CStmt::Decl(_)) || captures_break_or_continue(s))
        {
            i += 1;
            continue;
        }

        let region: Vec<CStmt> = items[i..=bm].to_vec();
        let loop_stmt = build_loop(region, &h, refs, structural_loop_headers);
        items.splice(i..=bm, std::iter::once(loop_stmt));
        i += 1; // step past the wrapped loop
    }
    items
}

// Wrap `region` (whose first statement is labeled `h`) into `Labeled(h, while(1){..})`.
fn build_loop(
    region: Vec<CStmt>,
    h: &str,
    refs: &HashMap<String, usize>,
    structural_loop_headers: &HashSet<String>,
) -> CStmt {
    let mut body = region;
    body[0] = strip_header(body[0].clone(), h);

    // Inner loops must be recognized first so the outer back-edge conversion below correctly skips them.
    let body = recover_seq(body, refs, structural_loop_headers);

    // Outer back-edges -> continue (skips the inner loops just formed).
    let mut body: Vec<CStmt> = body.into_iter().map(|s| convert_backedges(s, h)).collect();

    // Fall-off path exits the original loop; append explicit break so while(1) doesn't re-iterate.
    if body.last().map_or(true, |s| !stmt_diverges(s)) {
        body.push(CStmt::Break);
    }

    let while_stmt = CStmt::While(CExpr::int(1), Box::new(CStmt::Block(stmts_to_items(body))));
    // Keep H on the loop so external `goto H` (loop entries) still resolve.
    CStmt::Labeled(Label::Named(h.to_string()), Box::new(while_stmt))
}

// CF-7: loop-exit break conversion -- `goto L` inside a loop where L immediately follows becomes `break`; stops at intervening loops/switches (break binds innermost); asymmetric with continue which passes through switch.

fn stacked_labels(s: &CStmt) -> HashSet<String> {
    let mut out = HashSet::new();
    let mut cur = s;
    while let CStmt::Labeled(l, inner) = cur {
        if let Label::Named(n) = l {
            out.insert(n.clone());
        }
        cur = inner;
    }
    out
}

fn is_loop_stmt(s: &CStmt) -> bool {
    match s {
        CStmt::While(..) | CStmt::DoWhile(..) | CStmt::For(..) => true,
        CStmt::Labeled(_, b) | CStmt::Effect(_, b) => is_loop_stmt(b),
        _ => false,
    }
}

// Stops at nested loops AND switches (break would bind to the inner construct); if/block/label are transparent.
fn convert_exit_gotos(s: CStmt, exits: &HashSet<String>) -> CStmt {
    match s {
        CStmt::Goto(t) if exits.contains(&t) => CStmt::Break,
        CStmt::While(..) | CStmt::DoWhile(..) | CStmt::For(..) | CStmt::Switch(..) => s,
        CStmt::If(c, t, e) => CStmt::If(
            c,
            Box::new(convert_exit_gotos(*t, exits)),
            e.map(|x| Box::new(convert_exit_gotos(*x, exits))),
        ),
        CStmt::Block(items) => CStmt::Block(
            items
                .into_iter()
                .map(|it| match it {
                    CBlockItem::Stmt(st) => CBlockItem::Stmt(convert_exit_gotos(st, exits)),
                    d => d,
                })
                .collect(),
        ),
        CStmt::Sequence(v) => CStmt::Sequence(
            v.into_iter()
                .map(|x| convert_exit_gotos(x, exits))
                .collect(),
        ),
        CStmt::Labeled(l, b) => CStmt::Labeled(l, Box::new(convert_exit_gotos(*b, exits))),
        CStmt::Effect(l, b) => CStmt::Effect(l, Box::new(convert_exit_gotos(*b, exits))),
        other => other,
    }
}

fn convert_loop_exits(s: CStmt, exits: &HashSet<String>) -> CStmt {
    match s {
        CStmt::Labeled(l, b) => CStmt::Labeled(l, Box::new(convert_loop_exits(*b, exits))),
        CStmt::Effect(l, b) => CStmt::Effect(l, Box::new(convert_loop_exits(*b, exits))),
        CStmt::While(c, b) => CStmt::While(c, Box::new(convert_exit_gotos(*b, exits))),
        CStmt::DoWhile(b, c) => CStmt::DoWhile(Box::new(convert_exit_gotos(*b, exits)), c),
        CStmt::For(i, c, u, b) => CStmt::For(i, c, u, Box::new(convert_exit_gotos(*b, exits))),
        other => other,
    }
}

fn break_convert_seq(mut items: Vec<CStmt>) -> Vec<CStmt> {
    for i in 0..items.len() {
        if i + 1 >= items.len() || !is_loop_stmt(&items[i]) {
            continue;
        }
        let exits = stacked_labels(&items[i + 1]);
        if exits.is_empty() {
            continue;
        }
        let cur = std::mem::replace(&mut items[i], CStmt::Empty);
        items[i] = convert_loop_exits(cur, &exits);
    }
    items
}

fn break_convert(s: CStmt) -> CStmt {
    match s {
        CStmt::Block(items) => {
            let stmts: Vec<CStmt> = items_to_stmts(items)
                .into_iter()
                .map(break_convert)
                .collect();
            CStmt::Block(stmts_to_items(break_convert_seq(stmts)))
        }
        CStmt::Sequence(v) => CStmt::Sequence(break_convert_seq(
            v.into_iter().map(break_convert).collect(),
        )),
        CStmt::If(c, t, e) => CStmt::If(
            c,
            Box::new(break_convert(*t)),
            e.map(|x| Box::new(break_convert(*x))),
        ),
        CStmt::Switch(c, b) => CStmt::Switch(c, Box::new(break_convert(*b))),
        CStmt::While(c, b) => CStmt::While(c, Box::new(break_convert(*b))),
        CStmt::DoWhile(b, c) => CStmt::DoWhile(Box::new(break_convert(*b)), c),
        CStmt::For(i, c, u, b) => CStmt::For(i, c, u, Box::new(break_convert(*b))),
        CStmt::Labeled(l, b) => CStmt::Labeled(l, Box::new(break_convert(*b))),
        CStmt::Effect(l, b) => CStmt::Effect(l, Box::new(break_convert(*b))),
        other => other,
    }
}

// Single-ref goto inlining -- moves single-use labeled blocks to their goto site; return-tail duplication also performed; goto-ending body duplication was measured counterproductive (net-zero goto, crowds out beneficial dups).

fn wrap_block(v: Vec<CStmt>) -> CStmt {
    let mut v: Vec<CStmt> = v
        .into_iter()
        .filter(|s| !matches!(s, CStmt::Empty))
        .collect();
    match v.len() {
        0 => CStmt::Empty,
        1 => v.pop().unwrap(),
        _ => CStmt::Block(v.into_iter().map(CBlockItem::Stmt).collect()),
    }
}

// True if the statement recursively contains a loop or switch; such a region must never be tail-duplicated.
fn run_contains_loop_or_switch(s: &CStmt) -> bool {
    match s {
        CStmt::While(..) | CStmt::DoWhile(..) | CStmt::For(..) | CStmt::Switch(..) => true,
        CStmt::Labeled(_, inner) | CStmt::Effect(_, inner) => run_contains_loop_or_switch(inner),
        CStmt::Block(items) => items.iter().any(|it| match it {
            CBlockItem::Stmt(st) => run_contains_loop_or_switch(st),
            _ => false,
        }),
        CStmt::Sequence(v) => v.iter().any(run_contains_loop_or_switch),
        CStmt::If(_, t, e) => {
            run_contains_loop_or_switch(t)
                || e.as_ref().map_or(false, |x| run_contains_loop_or_switch(x))
        }
        _ => false,
    }
}

fn list_has_goto(run: &[CStmt], l: &str) -> bool {
    let mut t = Vec::new();
    for s in run {
        collect_goto_targets(s, &mut t);
    }
    t.iter().any(|x| x == l)
}

// Replace the (single-use) `goto l` with the moved block; returns how many replaced.
fn replace_all_gotos(s: &mut CStmt, l: &str, block: &[CStmt]) -> usize {
    let mut n = 0;
    match s {
        CStmt::Goto(name) if name == l => {
            *s = wrap_block(block.to_vec());
            n += 1;
        }
        CStmt::Block(items) => {
            for it in items.iter_mut() {
                if let CBlockItem::Stmt(st) = it {
                    n += replace_all_gotos(st, l, block);
                }
            }
        }
        CStmt::Sequence(v) => {
            for st in v.iter_mut() {
                n += replace_all_gotos(st, l, block);
            }
        }
        CStmt::If(_, t, e) => {
            n += replace_all_gotos(t, l, block);
            if let Some(x) = e {
                n += replace_all_gotos(x, l, block);
            }
        }
        CStmt::Switch(_, b) | CStmt::While(_, b) | CStmt::DoWhile(b, _) | CStmt::Labeled(_, b) | CStmt::Effect(_, b) => {
            n += replace_all_gotos(b, l, block)
        }
        CStmt::For(_, _, _, b) => n += replace_all_gotos(b, l, block),
        _ => {}
    }
    n
}

// CrossJumpRevert: reverses gcc tail-merging of identical return tails by duplicating bounded return-tails (CONFIG.forloop.max_dup_tail) back to each goto site -- fidelity-positive.

// Charge the whole statement tree, not only the number of entries in the
// surrounding run.  Single-use block moves can collapse a chain of labels into
// one deeply nested Block/If statement.  Treating that tree as one statement
// lets the later return-tail case clone an arbitrarily large subtree to every
// predecessor, and repeated moves can make the hidden subtree larger before
// the duplication check sees it.  A recursively bounded, goto-free tail cannot
// compound in that way: every duplicate consumes an existing goto without
// introducing another one, so at most the function's original goto count
// copies, each of bounded cost, can be made.
fn stmt_tree_fits_budget(stmt: &CStmt, remaining: &mut usize) -> bool {
    if *remaining == 0 {
        return false;
    }
    *remaining -= 1;

    match stmt {
        CStmt::Block(items) => items.iter().all(|item| match item {
            CBlockItem::Stmt(stmt) => stmt_tree_fits_budget(stmt, remaining),
            // Declarations make a tail ineligible below, but still charge the
            // container if this helper is reused independently.
            CBlockItem::Decl(_) => {
                if *remaining == 0 {
                    false
                } else {
                    *remaining -= 1;
                    true
                }
            }
        }),
        CStmt::Sequence(stmts) => stmts
            .iter()
            .all(|stmt| stmt_tree_fits_budget(stmt, remaining)),
        CStmt::If(_, then_stmt, else_stmt) => {
            stmt_tree_fits_budget(then_stmt, remaining)
                && else_stmt
                    .as_deref()
                    .is_none_or(|stmt| stmt_tree_fits_budget(stmt, remaining))
        }
        CStmt::Switch(_, body)
        | CStmt::While(_, body)
        | CStmt::Labeled(_, body) | CStmt::Effect(_, body)
        | CStmt::For(_, _, _, body) => stmt_tree_fits_budget(body, remaining),
        CStmt::DoWhile(body, _) => stmt_tree_fits_budget(body, remaining),
        CStmt::Empty
        | CStmt::Expr(_)
        | CStmt::Goto(_)
        | CStmt::Continue
        | CStmt::Break
        | CStmt::Return(_)
        | CStmt::Decl(_) => true,
    }
}

fn run_tree_fits_budget(run: &[CStmt], budget: usize) -> bool {
    let mut remaining = budget;
    run.iter()
        .all(|stmt| stmt_tree_fits_budget(stmt, &mut remaining))
}

fn ends_in_return(s: &CStmt) -> bool {
    match s {
        CStmt::Return(_) => true,
        CStmt::Block(items) => items.last().map_or(
            false,
            |it| matches!(it, CBlockItem::Stmt(st) if ends_in_return(st)),
        ),
        CStmt::Sequence(v) => v.last().map_or(false, ends_in_return),
        CStmt::If(_, t, Some(e)) => ends_in_return(t) && ends_in_return(e),
        _ => false,
    }
}

fn run_has_any_goto(run: &[CStmt]) -> bool {
    let mut t = Vec::new();
    for s in run {
        collect_goto_targets(s, &mut t);
    }
    !t.is_empty()
}

fn run_has_named_label(run: &[CStmt]) -> bool {
    let mut set = HashSet::new();
    for s in run {
        collect_labels(s, &mut set);
    }
    !set.is_empty()
}

fn run_has_decl(run: &[CStmt]) -> bool {
    fn has(s: &CStmt) -> bool {
        match s {
            CStmt::Decl(_) => true,
            CStmt::Block(items) => items.iter().any(|it| match it {
                CBlockItem::Decl(_) => true,
                CBlockItem::Stmt(st) => has(st),
            }),
            CStmt::Sequence(v) => v.iter().any(has),
            CStmt::If(_, t, e) => has(t) || e.as_ref().map_or(false, |x| has(x)),
            CStmt::Switch(_, b)
            | CStmt::While(_, b)
            | CStmt::DoWhile(b, _)
            | CStmt::Labeled(_, b) | CStmt::Effect(_, b) => has(b),
            CStmt::For(_, _, _, b) => has(b),
            _ => false,
        }
    }
    run.iter().any(has)
}

// (A) single-use MOVE: predecessor transfers, no self-goto; (B) bounded return-tail DUPLICATE: returns on every path, no internal goto/label/decl.
fn scan_for_inlinable<T>(
    items: &mut Vec<T>,
    counts: &HashMap<String, usize>,
    as_stmt: impl Fn(&T) -> Option<&CStmt>,
    to_run_stmt: impl Fn(&T) -> CStmt,
) -> Option<(String, Vec<CStmt>)> {
    for i in 0..items.len() {
        let Some(CStmt::Labeled(Label::Named(l), inner)) = as_stmt(&items[i]) else {
            continue;
        };
        let k = counts.get(l).copied().unwrap_or(0);
        if k == 0 {
            continue; // unreferenced
        }
        if matches!(**inner, CStmt::Labeled(..)) {
            continue; // stacked labels: skip
        }
        let prev_transfers = i > 0 && as_stmt(&items[i - 1]).map_or(false, stmt_diverges);
        let mut run = vec![(**inner).clone()];
        let mut j = i;
        if !stmt_diverges(&run[0]) {
            let mut m = i + 1;
            loop {
                if m >= items.len() {
                    break;
                }
                if matches!(as_stmt(&items[m]), Some(CStmt::Labeled(..))) {
                    break;
                }
                let st = to_run_stmt(&items[m]);
                let done = stmt_diverges(&st);
                run.push(st);
                j = m;
                if done {
                    break;
                }
                m += 1;
            }
        }
        if !run.last().map_or(false, stmt_diverges) {
            continue; // not self-contained (could fall through)
        }
        let can_move = k == 1 && prev_transfers && !list_has_goto(&run, l);
        // Duplicate only recursively small, loop/switch-free return tails.
        // `run.len()` is not a size bound: one entry can contain a deeply
        // nested tree assembled by earlier single-use moves.
        let is_return_tail = run_tree_fits_budget(&run, CONFIG.forloop.max_dup_tail)
            && run.last().map_or(false, ends_in_return)
            && !run.iter().any(run_contains_loop_or_switch)
            && !run_has_any_goto(&run)
            && !run_has_named_label(&run)
            && !run_has_decl(&run);
        if can_move {
            let label = l.clone();
            items.drain(i..=j); // moved to its single goto site
            return Some((label, run));
        }
        if is_return_tail {
            let label = l.clone();
            if prev_transfers {
                items.drain(i..=j); // remove only when nothing falls into it
            }
            return Some((label, run));
        }
    }
    None
}

fn extract_inlinable(
    s: &mut CStmt,
    counts: &HashMap<String, usize>,
) -> Option<(String, Vec<CStmt>)> {
    let child = match s {
        CStmt::Block(items) => items.iter_mut().find_map(|it| match it {
            CBlockItem::Stmt(st) => extract_inlinable(st, counts),
            _ => None,
        }),
        CStmt::Sequence(v) => v.iter_mut().find_map(|st| extract_inlinable(st, counts)),
        CStmt::If(_, t, e) => extract_inlinable(t, counts)
            .or_else(|| e.as_mut().and_then(|x| extract_inlinable(x, counts))),
        CStmt::Switch(_, b) | CStmt::While(_, b) | CStmt::DoWhile(b, _) | CStmt::Labeled(_, b) | CStmt::Effect(_, b) => {
            extract_inlinable(b, counts)
        }
        CStmt::For(_, _, _, b) => extract_inlinable(b, counts),
        _ => None,
    };
    if child.is_some() {
        return child;
    }
    match s {
        CStmt::Block(items) => scan_for_inlinable(
            items,
            counts,
            |it| match it {
                CBlockItem::Stmt(st) => Some(st),
                _ => None,
            },
            |it| match it {
                CBlockItem::Stmt(st) => st.clone(),
                CBlockItem::Decl(ds) => CStmt::Decl(ds.clone()),
            },
        ),
        CStmt::Sequence(v) => scan_for_inlinable(v, counts, |st| Some(st), |st| st.clone()),
        _ => None,
    }
}

// Iteratively move single-use labeled blocks to their goto site. Returns gotos removed.
fn inline_gotos(body: &mut CStmt) -> usize {
    let mut total = 0;
    let cap = count_gotos(body) + 4;
    for _ in 0..cap {
        let mut counts: HashMap<String, usize> = HashMap::new();
        let mut tgts = Vec::new();
        collect_goto_targets(body, &mut tgts);
        for t in tgts {
            *counts.entry(t).or_default() += 1;
        }
        match extract_inlinable(body, &counts) {
            Some((label, block)) => {
                total += replace_all_gotos(body, &label, &block);
            }
            None => break,
        }
    }
    total
}

// Pass

pub struct ForLoopPass;

impl IRPass for ForLoopPass {
    fn name(&self) -> &'static str {
        "forloop"
    }

    fn run(&self, db: &mut DecompileDB) {
        // Always on (gate removed 2026-06-10): corpus A/B showed goto_per_func -27%, var_exact +18%, recompile_mean_errors flat; only cost is cc_ratio +3% (each recovered loop adds one cyclomatic unit).
        // Recovery is nevertheless constrained by structural CFG evidence:
        // labels and sequence position alone cannot establish reachability.
        let structural_loop_headers: HashSet<String> = db
            .rel_iter::<(crate::x86::types::Address, crate::x86::types::Node)>("valid_loop")
            .map(|(_, node)| format!("L{}", node))
            .collect();
        let tu = match db.cast_optimized_translation_unit.as_mut() {
            Some(tu) => tu,
            None => return,
        };
        let mut improved = 0usize;
        let mut removed = 0usize;
        let (mut tot_g, mut kept_g) = (0usize, 0usize);
        for decl in tu.decls.iter_mut() {
            if let TopLevelDecl::FuncDef(f) = decl {
                if !has_goto_or_label(&f.body) {
                    continue;
                }
                let before = count_gotos(&f.body);
                let loops_before = count_loops(&f.body);
                tot_g += before;

                // 1) Inline single-ref labeled blocks at their goto site.
                let mut cand = f.body.clone();
                inline_gotos(&mut cand);

                // 2) Recover loops + if-bodies (counts recomputed after inlining).
                let mut tgts = Vec::new();
                collect_goto_targets(&cand, &mut tgts);
                let mut refs: HashMap<String, usize> = HashMap::new();
                for t in tgts {
                    *refs.entry(t).or_insert(0) += 1;
                }
                let cand = recover(cand, &refs, &structural_loop_headers);

                // 3) CF-7 runs last so while(1) loops formed in step 2 also get their exit gotos converted.
                let cand = break_convert(cand);
                let after = count_gotos(&cand);
                if after < before && count_loops(&cand) >= loops_before && all_gotos_resolve(&cand)
                    && crate::decompile::effects::c::preserves(f, &cand)
                {
                    f.body = cand;
                    improved += 1;
                    removed += before - after;
                }
                kept_g += count_gotos(&f.body);
            }
        }
        if let Some(audit) = db.cast_post_emit_audit_trail.as_mut() {
            if let Err(reason) = audit.record(
                crate::decompile::analysis::coverage_pass::PostEmitCheckpoint::ForLoop,
                tu,
            ) {
                log::warn!("coverage: cannot record forloop checkpoint: {reason}");
            }
        }
        log::info!(
            "forloop: improved {} funcs, removed {} of {} gotos ({} residual)",
            improved,
            removed,
            tot_g,
            kept_g
        );
    }

    fn inputs(&self) -> &'static [&'static str] {
        &[
            "cast_optimized_translation_unit",
            "cast_post_emit_audit_trail",
        ]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "cast_optimized_translation_unit",
            "cast_post_emit_audit_trail",
        ]
    }

    fn extra_reads(&self) -> &'static [&'static str] {
        &["valid_loop"]
    }
}

// Tests

#[cfg(test)]
mod tests {
    use super::*;

    fn lbl(n: &str, s: CStmt) -> CStmt {
        CStmt::Labeled(Label::Named(n.to_string()), Box::new(s))
    }
    fn block(v: Vec<CStmt>) -> CStmt {
        CStmt::Block(v.into_iter().map(CBlockItem::Stmt).collect())
    }
    fn goto(n: &str) -> CStmt {
        CStmt::Goto(n.to_string())
    }
    fn while1(body: Vec<CStmt>) -> CStmt {
        CStmt::While(CExpr::int(1), Box::new(block(body)))
    }

    fn refs_for(s: &CStmt) -> HashMap<String, usize> {
        let mut refs = HashMap::new();
        let mut targets = Vec::new();
        collect_goto_targets(s, &mut targets);
        for target in targets {
            *refs.entry(target).or_default() += 1;
        }
        refs
    }
    fn if_then(t: CStmt) -> CStmt {
        CStmt::If(CExpr::int(1), Box::new(t), None)
    }

    fn stmt_tree_nodes(stmt: &CStmt) -> usize {
        let children = match stmt {
            CStmt::Block(items) => items
                .iter()
                .map(|item| match item {
                    CBlockItem::Stmt(stmt) => stmt_tree_nodes(stmt),
                    CBlockItem::Decl(_) => 1,
                })
                .sum(),
            CStmt::Sequence(stmts) => stmts.iter().map(stmt_tree_nodes).sum(),
            CStmt::If(_, then_stmt, else_stmt) => {
                stmt_tree_nodes(then_stmt) + else_stmt.as_deref().map_or(0, stmt_tree_nodes)
            }
            CStmt::Switch(_, body)
            | CStmt::While(_, body)
            | CStmt::Labeled(_, body) | CStmt::Effect(_, body)
            | CStmt::For(_, _, _, body) => stmt_tree_nodes(body),
            CStmt::DoWhile(body, _) => stmt_tree_nodes(body),
            _ => 0,
        };
        1 + children
    }

    #[test]
    fn small_return_tail_is_still_inlined() {
        let tail = block(vec![CStmt::Expr(CExpr::int(7)), CStmt::Return(None)]);
        assert!(run_tree_fits_budget(
            std::slice::from_ref(&tail),
            CONFIG.forloop.max_dup_tail,
        ));
        let mut input = block(vec![if_then(goto("Lret")), lbl("Lret", tail)]);

        inline_gotos(&mut input);
        assert_eq!(count_gotos(&input), 0, "small safe tail was not inlined");
    }

    #[test]
    fn moved_goto_chain_cannot_hide_an_unbounded_duplicate_tail() {
        const FANOUT: usize = 12;
        const CHAIN: usize = 32;

        // Deferred fallthrough elision and exact ITE join edges expose this
        // production shape: several conditional predecessors target a chain
        // of single-use sections.  Moving each section is size-neutral, but it
        // folds the chain into one recursively deep Block.  The old
        // `run.len() <= 8` check called that one statement and copied the whole
        // chain FANOUT times.
        let mut items: Vec<CStmt> = (0..FANOUT).map(|_| if_then(goto("L0"))).collect();
        for index in 0..CHAIN {
            items.push(lbl(
                &format!("L{index}"),
                block(vec![
                    CStmt::Expr(CExpr::int(index as i64)),
                    goto(&format!("L{}", index + 1)),
                ]),
            ));
        }
        items.push(lbl(&format!("L{CHAIN}"), CStmt::Return(None)));
        let mut input = block(items);
        let before_nodes = stmt_tree_nodes(&input);

        inline_gotos(&mut input);

        let after_nodes = stmt_tree_nodes(&input);
        assert_eq!(
            count_gotos(&input),
            FANOUT,
            "oversized recursively assembled tail should remain shared"
        );
        assert!(
            after_nodes <= before_nodes,
            "tail inlining compounded statement-tree cost: {before_nodes} -> {after_nodes}"
        );
    }

    #[test]
    fn layout_cycle_requires_structural_loop_header() {
        // This is the shape produced by an option-dispatch switch inside an
        // already recovered outer loop: a case-lowering goto reaches the
        // dispatch label, but the CFG has no back edge to a second header.
        let input = block(vec![while1(vec![lbl(
            "L17515",
            CStmt::Switch(CExpr::var("option"), Box::new(block(vec![goto("L17515")]))),
        )])]);
        let refs = refs_for(&input);

        let without_cfg_proof = recover(input.clone(), &refs, &HashSet::new());
        assert_eq!(count_loops(&without_cfg_proof), 1);
        assert_eq!(count_gotos(&without_cfg_proof), 1);

        let proven_headers = HashSet::from(["L17515".to_string()]);
        let with_cfg_proof = recover(input, &refs, &proven_headers);
        assert_eq!(count_loops(&with_cfg_proof), 2);
        assert_eq!(count_gotos(&with_cfg_proof), 0);
    }

    fn count_breaks(s: &CStmt) -> usize {
        match s {
            CStmt::Break => 1,
            CStmt::Labeled(_, b) | CStmt::Effect(_, b) => count_breaks(b),
            CStmt::Block(items) => items
                .iter()
                .map(|it| match it {
                    CBlockItem::Stmt(st) => count_breaks(st),
                    _ => 0,
                })
                .sum(),
            CStmt::Sequence(v) => v.iter().map(count_breaks).sum(),
            CStmt::If(_, t, e) => count_breaks(t) + e.as_ref().map_or(0, |x| count_breaks(x)),
            CStmt::Switch(_, b) | CStmt::While(_, b) | CStmt::DoWhile(b, _) => count_breaks(b),
            CStmt::For(_, _, _, b) => count_breaks(b),
            _ => 0,
        }
    }

    #[test]
    fn exit_to_next_converts() {
        let s = block(vec![
            while1(vec![if_then(goto("L")), CStmt::Continue]),
            lbl("L", CStmt::Return(None)),
        ]);
        let out = break_convert(s);
        assert_eq!(count_gotos(&out), 0);
        assert_eq!(count_breaks(&out), 1);
    }

    // `break` inside a switch exits the switch, not the outer loop; goto must stay.
    #[test]
    fn inner_switch_blocks_conversion() {
        let s = block(vec![
            while1(vec![CStmt::Switch(
                CExpr::int(1),
                Box::new(block(vec![goto("L")])),
            )]),
            lbl("L", CStmt::Return(None)),
        ]);
        let out = break_convert(s);
        assert_eq!(count_gotos(&out), 1);
        assert_eq!(count_breaks(&out), 0);
    }

    // A goto inside an inner loop exits TWO loops; `break` exits one. Must stay.
    #[test]
    fn inner_loop_blocks_conversion() {
        let s = block(vec![
            while1(vec![while1(vec![goto("L")])]),
            lbl("L", CStmt::Return(None)),
        ]);
        let out = break_convert(s);
        assert_eq!(count_gotos(&out), 1);
        assert_eq!(count_breaks(&out), 0);
    }

    #[test]
    fn label_after_inner_loop_converts() {
        let s = block(vec![while1(vec![
            while1(vec![goto("L")]),
            lbl("L", CStmt::Continue),
        ])]);
        let out = break_convert(s);
        assert_eq!(count_gotos(&out), 0);
        assert_eq!(count_breaks(&out), 1);
    }

    #[test]
    fn same_level_goto_untouched() {
        let s = block(vec![
            goto("L"),
            while1(vec![CStmt::Continue]),
            lbl("L", CStmt::Return(None)),
        ]);
        let out = break_convert(s);
        assert_eq!(count_gotos(&out), 1);
    }

    #[test]
    fn skip_past_next_untouched() {
        let s = block(vec![
            while1(vec![goto("M")]),
            lbl("L", CStmt::Expr(CExpr::int(0))),
            lbl("M", CStmt::Return(None)),
        ]);
        let out = break_convert(s);
        assert_eq!(count_gotos(&out), 1);
    }

    #[test]
    fn stacked_labels_convert() {
        let s = block(vec![
            while1(vec![goto("L2")]),
            lbl("L1", lbl("L2", CStmt::Return(None))),
        ]);
        let out = break_convert(s);
        assert_eq!(count_gotos(&out), 0);
        assert_eq!(count_breaks(&out), 1);
    }

    // Label wrapper on a recovered loop must not hide it from the adjacency scan.
    #[test]
    fn labeled_loop_and_dowhile_convert() {
        let s = block(vec![
            lbl("H", while1(vec![if_then(goto("L"))])),
            lbl(
                "L",
                CStmt::DoWhile(Box::new(block(vec![goto("M")])), CExpr::int(0)),
            ),
            lbl("M", CStmt::Return(None)),
        ]);
        let out = break_convert(s);
        assert_eq!(count_gotos(&out), 0);
        assert_eq!(count_breaks(&out), 2);
    }
}
