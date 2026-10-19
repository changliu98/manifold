// Does control leave this statement on every path?
fn rl_diverts(s: &CStmt) -> bool {
    match s {
        CStmt::Return(_) | CStmt::Goto(_) | CStmt::Break | CStmt::Continue => true,
        CStmt::If(_, t, Some(e)) => rl_diverts(t) && rl_diverts(e),
        CStmt::Labeled(_, b) | CStmt::Effect(_, b) => rl_diverts(b),
        CStmt::Block(items) => items.iter().any(|i| match i {
            CBlockItem::Stmt(st) => rl_diverts(st),
            _ => false,
        }),
        CStmt::Sequence(v) => v.iter().any(rl_diverts),
        _ => false,
    }
}

fn rl_contains_continue(s: &CStmt) -> bool {
    match s {
        CStmt::Continue => true,
        CStmt::If(_, t, e) => {
            rl_contains_continue(t) || e.as_ref().is_some_and(|x| rl_contains_continue(x))
        }
        CStmt::Labeled(_, b) | CStmt::Effect(_, b) => rl_contains_continue(b),
        CStmt::Block(items) => items.iter().any(|i| match i {
            CBlockItem::Stmt(st) => rl_contains_continue(st),
            _ => false,
        }),
        CStmt::Sequence(v) => v.iter().any(rl_contains_continue),
        _ => false,
    }
}

fn rl_top_level(s: &CStmt) -> Vec<&CStmt> {
    match s {
        CStmt::Block(items) => items
            .iter()
            .filter_map(|i| match i {
                CBlockItem::Stmt(st) => Some(st),
                _ => None,
            })
            .collect(),
        CStmt::Sequence(v) => v.iter().collect(),
        other => vec![other],
    }
}

// A `continue` bound to the wrong body frontier leaves the statements after it
// unreachable: nothing is labeled, so no goto can re-enter them, and the loop
// re-tests the same unchanged condition forever.
fn rl_body_has_dead_tail_after_continue(body: &CStmt) -> bool {
    let seq = rl_top_level(body);
    for (i, st) in seq.iter().enumerate() {
        if !rl_diverts(st) {
            continue;
        }
        if !rl_contains_continue(st) {
            break;
        }
        for next in &seq[i + 1..] {
            match next {
                CStmt::Labeled(..) => break,
                CStmt::Empty => {}
                _ => return true,
            }
        }
        break;
    }
    false
}

fn rl_count_spin_loops(s: &CStmt) -> usize {
    let mut n = 0;
    let mut children: Vec<&CStmt> = Vec::new();
    match s {
        CStmt::While(_, b) | CStmt::DoWhile(b, _) | CStmt::For(_, _, _, b) => {
            if rl_body_has_dead_tail_after_continue(b) {
                n += 1;
            }
            children.push(b);
        }
        CStmt::If(_, t, e) => {
            children.push(t);
            if let Some(x) = e {
                children.push(x);
            }
        }
        CStmt::Switch(_, b) | CStmt::Labeled(_, b) | CStmt::Effect(_, b) => children.push(b),
        CStmt::Block(items) => {
            for i in items {
                if let CBlockItem::Stmt(st) = i {
                    children.push(st);
                }
            }
        }
        CStmt::Sequence(v) => children.extend(v.iter()),
        _ => {}
    }
    for c in children {
        n += rl_count_spin_loops(c);
    }
    n
}

fn rl_spin_loops(out: &TestOutput, func: &str) -> usize {
    rl_count_spin_loops(&func_def(out, func).body)
}

#[test]
fn all_functions_present() {
    for name in ["fmt_prefix_count", "skip_escape_pairs", "run_length"] {
        assert!(OUTPUT.text.contains(name), "missing '{name}'");
    }
}

#[test]
fn fmt_prefix_count_loop_is_not_a_spin() {
    assert_eq!(
        rl_spin_loops(&OUTPUT, "fmt_prefix_count"),
        0,
        "continue bound past the loop header, body tail unreachable:\n{}",
        body(&OUTPUT, "fmt_prefix_count")
    );
}

#[test]
fn skip_escape_pairs_loop_is_not_a_spin() {
    assert_eq!(
        rl_spin_loops(&OUTPUT, "skip_escape_pairs"),
        0,
        "continue bound past the loop header, body tail unreachable:\n{}",
        body(&OUTPUT, "skip_escape_pairs")
    );
}

#[test]
fn run_length_loop_is_not_a_spin() {
    assert_eq!(
        rl_spin_loops(&OUTPUT, "run_length"),
        0,
        "continue bound past the loop header, body tail unreachable:\n{}",
        body(&OUTPUT, "run_length")
    );
}

#[test]
fn fmt_prefix_count_keeps_both_character_tests() {
    let b = body(&OUTPUT, "fmt_prefix_count");
    assert!(b.contains("37"), "'%' test lost:\n{b}");
    assert!(b.contains("115"), "'s' test lost:\n{b}");
}

#[test]
fn run_length_has_a_loop() {
    assert!(has_any_loop(&OUTPUT, "run_length"), "expected a loop");
}
