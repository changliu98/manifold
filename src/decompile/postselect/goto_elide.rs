// Fall-through goto elision on the final C AST: drop `goto L` only where L is
// literally the next statement's label in the layout that will be printed.
//
// Adjacency is a property of the printed layout, so the elision is only sound
// once no later transform can still move statements.  It therefore runs as the
// last AST transform in the pipeline, after everything that rewrites the
// statement list: forloop's single-ref block moves, if-conversion, loop
// wrapping and break conversion, and var_reduce's declaration fusion.  Eliding
// before them would make each one responsible for an invariant it cannot see,
// and would erase the target a later pass would need to reinstate the transfer;
// control would instead fall into whichever section ends up next.

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::c_pass::helpers::flatten_blocks_and_cleanup;
use crate::decompile::passes::c_pass::types::*;
use crate::decompile::passes::pass::IRPass;

pub fn simplify_fallthrough_gotos_in_final_stmt(stmt: &CStmt) -> CStmt {
    simplify_fallthrough_gotos_counted(stmt).0
}

fn simplify_fallthrough_gotos_counted(stmt: &CStmt) -> (CStmt, usize) {
    let laid_out = flatten_blocks_and_cleanup(stmt);
    let mut count = 0;
    let simplified = simplify_stmt_fallthrough(&laid_out, None, &mut count);
    (flatten_blocks_and_cleanup(&simplified), count)
}

fn simplify_fallthrough_gotos_in_block_with_next(
    items: Vec<CBlockItem>,
    outer_next_label: Option<&str>,
    count: &mut usize,
) -> Vec<CBlockItem> {
    if items.is_empty() {
        return items;
    }

    let mut result = Vec::with_capacity(items.len());
    let mut i = 0;

    while i < items.len() {
        let current = &items[i];

        let next_label = if i + 1 < items.len() {
            get_first_label_from_item(&items[i + 1])
        } else {
            outer_next_label.map(|s| s.to_string())
        };

        match current {
            CBlockItem::Stmt(stmt) => {
                let simplified = simplify_stmt_fallthrough(stmt, next_label.as_deref(), count);
                result.push(CBlockItem::Stmt(simplified));
            }
            other => result.push(other.clone()),
        }
        i += 1;
    }

    result
}

fn simplify_stmt_fallthrough(stmt: &CStmt, next_label: Option<&str>, count: &mut usize) -> CStmt {
    match stmt {
        CStmt::Goto(target) => {
            if let Some(next_lbl) = next_label {
                if normalize_label(target) == normalize_label(next_lbl) {
                    *count += 1;
                    return CStmt::Empty;
                }
            }
            stmt.clone()
        }

        CStmt::If(cond, then_s, Some(else_s)) => {
            // A direct arm goto to the next label simplifies to Empty during
            // recursion.  Classify the cleaned result, not the now-vanished
            // goto: testing is_goto_to_label here made both collapse arms
            // unreachable and left `if (c) {} else { ... }` in final output.
            let simplified_then =
                flatten_blocks_and_cleanup(&simplify_stmt_fallthrough(then_s, next_label, count));
            let simplified_else =
                flatten_blocks_and_cleanup(&simplify_stmt_fallthrough(else_s, next_label, count));

            if next_label.is_some() {
                let else_is_fallthrough = matches!(&simplified_else, CStmt::Empty);
                let then_is_fallthrough = matches!(&simplified_then, CStmt::Empty);

                if else_is_fallthrough && then_is_fallthrough {
                    // Both control transfers are redundant, but evaluating
                    // the condition is not necessarily redundant: it may
                    // contain a call, assignment, or volatile access.  An
                    // expression statement preserves exactly that evaluation
                    // while allowing control to fall through once.
                    return CStmt::Expr(cond.clone());
                }

                if else_is_fallthrough {
                    return CStmt::If(cond.clone(), Box::new(simplified_then), None);
                }

                if then_is_fallthrough {
                    let negated_cond = negate_condition(cond);
                    return CStmt::If(negated_cond, Box::new(simplified_else), None);
                }
            }

            CStmt::If(
                cond.clone(),
                Box::new(simplified_then),
                Some(Box::new(simplified_else)),
            )
        }

        CStmt::If(cond, then_s, None) => {
            let simplified_then = simplify_stmt_fallthrough(then_s, next_label, count);
            CStmt::If(cond.clone(), Box::new(simplified_then), None)
        }

        CStmt::Labeled(label, inner) => {
            let simplified_inner = simplify_stmt_fallthrough(inner, next_label, count);
            CStmt::Labeled(label.clone(), Box::new(simplified_inner))
        }
        CStmt::Effect(label, inner) => {
            let simplified_inner = simplify_stmt_fallthrough(inner, next_label, count);
            CStmt::Effect(label.clone(), Box::new(simplified_inner))
        }

        CStmt::Block(items) => {
            let simplified =
                simplify_fallthrough_gotos_in_block_with_next(items.clone(), next_label, count);
            CStmt::Block(simplified)
        }

        CStmt::Sequence(stmts) => {
            if stmts.is_empty() {
                return CStmt::Empty;
            }
            let mut result = Vec::with_capacity(stmts.len());
            for (j, s) in stmts.iter().enumerate() {
                let next = if j + 1 < stmts.len() {
                    get_first_label_from_stmt(&stmts[j + 1])
                } else {
                    next_label.map(|s| s.to_string())
                };
                result.push(simplify_stmt_fallthrough(s, next.as_deref(), count));
            }
            CStmt::Sequence(result)
        }

        // Recurse into loop/switch bodies with next_label = None, since a goto at a loop body's end falls to the back-edge and a fall-through past a case label is meaningful.
        CStmt::While(cond, body) => CStmt::While(
            cond.clone(),
            Box::new(simplify_stmt_fallthrough(body, None, count)),
        ),

        CStmt::DoWhile(body, cond) => CStmt::DoWhile(
            Box::new(simplify_stmt_fallthrough(body, None, count)),
            cond.clone(),
        ),

        CStmt::For(init, cond, update, body) => CStmt::For(
            init.clone(),
            cond.clone(),
            update.clone(),
            Box::new(simplify_stmt_fallthrough(body, None, count)),
        ),

        CStmt::Switch(disc, body) => CStmt::Switch(
            disc.clone(),
            Box::new(simplify_stmt_fallthrough(body, None, count)),
        ),

        other => other.clone(),
    }
}

fn normalize_label(label: &str) -> String {
    let s = label.strip_prefix('.').unwrap_or(label);
    let s = s.strip_prefix('L').unwrap_or(s);
    let s = s.strip_prefix('_').unwrap_or(s);
    if s.chars().all(|c| c.is_ascii_hexdigit()) {
        s.to_lowercase()
    } else {
        label.to_lowercase()
    }
}

fn get_first_label_from_item(item: &CBlockItem) -> Option<String> {
    match item {
        CBlockItem::Stmt(stmt) => get_first_label_from_stmt(stmt),
        _ => None,
    }
}

fn get_first_label_from_stmt(stmt: &CStmt) -> Option<String> {
    match stmt {
        CStmt::Labeled(Label::Named(name), _) => Some(name.clone()),
        CStmt::Block(items) if !items.is_empty() => get_first_label_from_item(&items[0]),
        CStmt::Sequence(stmts) if !stmts.is_empty() => get_first_label_from_stmt(&stmts[0]),
        _ => None,
    }
}

fn negate_condition(cond: &CExpr) -> CExpr {
    match cond {
        CExpr::Unary(UnaryOp::Not, inner) => (**inner).clone(),
        CExpr::Binary(BinaryOp::Eq, lhs, rhs) => {
            CExpr::Binary(BinaryOp::Ne, lhs.clone(), rhs.clone())
        }
        CExpr::Binary(BinaryOp::Ne, lhs, rhs) => {
            CExpr::Binary(BinaryOp::Eq, lhs.clone(), rhs.clone())
        }
        // Relational complements are not equivalent for floating operands:
        // when either side is NaN, !(a < b) is true while a >= b is false.
        // This final untyped C AST no longer carries enough evidence to prove
        // an expression integral, so retain logical negation for every
        // relational comparison. Eq/Ne remain exact complements even for NaN.
        other => CExpr::Unary(UnaryOp::Not, Box::new(other.clone())),
    }
}

// Pass

pub struct GotoElidePass;

impl IRPass for GotoElidePass {
    fn name(&self) -> &'static str {
        "goto_elide"
    }

    fn run(&self, db: &mut DecompileDB) {
        let tu = match db.cast_optimized_translation_unit.as_mut() {
            Some(tu) => tu,
            None => return,
        };
        let mut elided = 0usize;
        for decl in tu.decls.iter_mut() {
            if let TopLevelDecl::FuncDef(f) = decl {
                let (body, count) = simplify_fallthrough_gotos_counted(&f.body);
                if crate::decompile::effects::c::preserves(f, &body) {
                    f.body = body;
                    elided += count;
                }
            }
        }
        log::info!("goto_elide: dropped {} fall-through gotos", elided);
    }

    fn inputs(&self) -> &'static [&'static str] {
        &["cast_optimized_translation_unit"]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &["cast_optimized_translation_unit"]
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

    fn contains_goto(stmt: &CStmt, target: &str) -> bool {
        match stmt {
            CStmt::Goto(actual) => actual == target,
            CStmt::Block(items) => items.iter().any(|item| match item {
                CBlockItem::Stmt(stmt) => contains_goto(stmt, target),
                _ => false,
            }),
            CStmt::Sequence(stmts) => stmts.iter().any(|stmt| contains_goto(stmt, target)),
            CStmt::If(_, then_stmt, else_stmt) => {
                contains_goto(then_stmt, target)
                    || else_stmt
                        .as_deref()
                        .is_some_and(|stmt| contains_goto(stmt, target))
            }
            CStmt::Labeled(_, inner) | CStmt::Effect(_, inner)
            | CStmt::While(_, inner)
            | CStmt::DoWhile(inner, _)
            | CStmt::For(_, _, _, inner)
            | CStmt::Switch(_, inner) => contains_goto(inner, target),
            _ => false,
        }
    }

    #[test]
    fn final_layout_keeps_goto_when_another_section_is_interposed() {
        let target = "L_return";
        let body = block(vec![
            lbl("L_source", CStmt::Goto(target.to_string())),
            lbl("L_other", CStmt::Expr(CExpr::int(1))),
            lbl(target, CStmt::Return(Some(CExpr::int(0)))),
        ]);

        let simplified = simplify_fallthrough_gotos_in_final_stmt(&body);
        assert!(
            contains_goto(&simplified, target),
            "final-layout simplification erased a non-fallthrough goto: {simplified:#?}"
        );
    }

    #[test]
    fn final_layout_removes_goto_to_immediately_following_label() {
        let target = "L_return";
        let body = block(vec![
            lbl("L_source", CStmt::Goto(target.to_string())),
            lbl(target, CStmt::Return(Some(CExpr::int(0)))),
        ]);

        let simplified = simplify_fallthrough_gotos_in_final_stmt(&body);
        assert!(
            !format!("{simplified:?}").contains("Goto"),
            "an actual final-layout fallthrough was not simplified: {simplified:#?}"
        );
    }

    // A branch with two goto arms whose else-target is the next section at emit
    // time and a different section after a later pass moves it.  Deciding on the
    // emit layout drops `goto L_48f9`, and control then falls into whatever the
    // move put next -- here an error path.  Deciding on the printed layout keeps
    // the goto, because L_48f9 is no longer adjacent.
    #[test]
    fn else_arm_goto_survives_a_later_reorder_of_its_target() {
        let laid_out_at_emit = block(vec![
            lbl(
                "L_59a9",
                CStmt::If(
                    CExpr::var("cond"),
                    Box::new(CStmt::Goto("L_5361".to_string())),
                    Some(Box::new(CStmt::Goto("L_48f9".to_string()))),
                ),
            ),
            lbl("L_48f9", CStmt::Expr(CExpr::var("ok_path"))),
            lbl("L_4adb", CStmt::Expr(CExpr::var("error_path"))),
            lbl("L_5361", CStmt::Return(Some(CExpr::int(0)))),
        ]);

        // A later pass moves the L_48f9 section past the error path; L_4adb is
        // now what lexically follows the if.
        let reordered = block(vec![
            lbl(
                "L_59a9",
                CStmt::If(
                    CExpr::var("cond"),
                    Box::new(CStmt::Goto("L_5361".to_string())),
                    Some(Box::new(CStmt::Goto("L_48f9".to_string()))),
                ),
            ),
            lbl("L_4adb", CStmt::Expr(CExpr::var("error_path"))),
            lbl("L_48f9", CStmt::Expr(CExpr::var("ok_path"))),
            lbl("L_5361", CStmt::Return(Some(CExpr::int(0)))),
        ]);

        // Eliding on the pre-reorder layout drops the else arm.
        let elided_early = simplify_fallthrough_gotos_in_final_stmt(&laid_out_at_emit);
        assert!(
            !contains_goto(&elided_early, "L_48f9"),
            "the pre-reorder layout is the one where the else goto looks redundant"
        );

        // Eliding on the layout that is actually printed keeps it.
        let elided_final = simplify_fallthrough_gotos_in_final_stmt(&reordered);
        assert!(
            contains_goto(&elided_final, "L_48f9"),
            "the else arm's goto must survive when its target is not the next section: {elided_final:#?}"
        );
        assert_eq!(
            first_label_after_stmt_named(&elided_final, "L_59a9").as_deref(),
            Some("L_4adb"),
            "test fixture must place the error path immediately after the branch"
        );
    }

    // clight_select used to fold an ITE arm's goto to the compound's join when
    // the arm's remaining lexical suffix was transparent.  That test was made
    // on a layout the emitter never promised; the same suffix-transparency
    // property now belongs here, decided on the layout that gets printed.
    #[test]
    fn an_arm_goto_to_the_join_is_dropped_only_when_the_join_is_next() {
        let transparent = block(vec![
            lbl(
                "L_branch",
                CStmt::If(
                    CExpr::var("cond"),
                    Box::new(CStmt::Goto("L_join".to_string())),
                    Some(Box::new(CStmt::Expr(CExpr::var("arm_effect")))),
                ),
            ),
            lbl("L_join", CStmt::Return(Some(CExpr::int(0)))),
        ]);
        let elided = simplify_fallthrough_gotos_in_final_stmt(&transparent);
        assert!(
            !contains_goto(&elided, "L_join"),
            "an arm goto whose join is the next section was kept: {elided:#?}"
        );
        let CStmt::Block(elided_items) = &elided else {
            panic!("expected final block layout: {elided:#?}");
        };
        let CBlockItem::Stmt(CStmt::Labeled(_, branch) | CStmt::Effect(_, branch)) = &elided_items[0] else {
            panic!("expected labeled branch: {elided:#?}");
        };
        let CStmt::If(CExpr::Unary(UnaryOp::Not, inner_cond), retained_arm, collapsed_else) =
            branch.as_ref()
        else {
            panic!("empty then-arm was not collapsed: {elided:#?}");
        };
        assert_eq!(inner_cond.as_ref(), &CExpr::var("cond"));
        assert_eq!(
            retained_arm.as_ref(),
            &CStmt::Expr(CExpr::var("arm_effect"))
        );
        assert!(collapsed_else.is_none());

        let bypasses_effect = block(vec![
            lbl(
                "L_branch",
                CStmt::If(
                    CExpr::var("cond"),
                    Box::new(CStmt::Goto("L_join".to_string())),
                    Some(Box::new(CStmt::Expr(CExpr::var("arm_effect")))),
                ),
            ),
            lbl("L_suffix", CStmt::Expr(CExpr::var("suffix_effect"))),
            lbl("L_join", CStmt::Return(Some(CExpr::int(0)))),
        ]);
        let retained = simplify_fallthrough_gotos_in_final_stmt(&bypasses_effect);
        assert!(
            contains_goto(&retained, "L_join"),
            "a goto that bypasses a semantic suffix was erased: {retained:#?}"
        );
    }

    #[test]
    fn relational_arm_collapse_uses_nan_safe_logical_negation() {
        let target = "L_join";
        let condition = CExpr::Binary(
            BinaryOp::Lt,
            Box::new(CExpr::var("lhs")),
            Box::new(CExpr::var("rhs")),
        );
        let body = block(vec![
            lbl(
                "L_branch",
                CStmt::If(
                    condition.clone(),
                    Box::new(CStmt::Goto(target.to_string())),
                    Some(Box::new(CStmt::Expr(CExpr::var("unordered_path")))),
                ),
            ),
            lbl(target, CStmt::Return(Some(CExpr::int(0)))),
        ]);

        let simplified = simplify_fallthrough_gotos_in_final_stmt(&body);
        let CStmt::Block(items) = &simplified else {
            panic!("expected final block layout: {simplified:#?}");
        };
        let CBlockItem::Stmt(CStmt::Labeled(_, branch) | CStmt::Effect(_, branch)) = &items[0] else {
            panic!("expected labeled branch: {simplified:#?}");
        };
        let CStmt::If(actual_condition, retained_arm, None) = branch.as_ref() else {
            panic!("then fallthrough did not collapse: {simplified:#?}");
        };

        assert_eq!(
            actual_condition,
            &CExpr::Unary(UnaryOp::Not, Box::new(condition)),
            "a relational complement would change unordered/NaN behavior"
        );
        assert_eq!(
            retained_arm.as_ref(),
            &CStmt::Expr(CExpr::var("unordered_path"))
        );
    }

    #[test]
    fn else_fallthrough_collapses_without_inverting_condition() {
        let target = "L_join";
        let condition = CExpr::var("cond");
        let body = block(vec![
            lbl(
                "L_branch",
                CStmt::If(
                    condition.clone(),
                    Box::new(CStmt::Expr(CExpr::var("effect"))),
                    Some(Box::new(CStmt::Goto(target.to_string()))),
                ),
            ),
            lbl(target, CStmt::Return(Some(CExpr::int(0)))),
        ]);

        let simplified = simplify_fallthrough_gotos_in_final_stmt(&body);
        let CStmt::Block(items) = &simplified else {
            panic!("expected final block layout: {simplified:#?}");
        };
        let CBlockItem::Stmt(CStmt::Labeled(_, branch) | CStmt::Effect(_, branch)) = &items[0] else {
            panic!("expected labeled branch: {simplified:#?}");
        };
        let CStmt::If(actual_condition, retained_arm, None) = branch.as_ref() else {
            panic!("else fallthrough did not collapse: {simplified:#?}");
        };
        assert_eq!(actual_condition, &condition);
        assert_eq!(retained_arm.as_ref(), &CStmt::Expr(CExpr::var("effect")));
    }

    #[test]
    fn two_fallthrough_arms_keep_condition_evaluation() {
        let target = "L_join";
        let condition = CExpr::call(CExpr::var("observe"), vec![]);
        let body = block(vec![
            lbl(
                "L_branch",
                CStmt::If(
                    condition.clone(),
                    Box::new(CStmt::Goto(target.to_string())),
                    Some(Box::new(CStmt::Goto(target.to_string()))),
                ),
            ),
            lbl(target, CStmt::Return(Some(CExpr::int(0)))),
        ]);

        let simplified = simplify_fallthrough_gotos_in_final_stmt(&body);
        let CStmt::Block(items) = &simplified else {
            panic!("expected final block layout: {simplified:#?}");
        };
        let CBlockItem::Stmt(CStmt::Labeled(_, branch) | CStmt::Effect(_, branch)) = &items[0] else {
            panic!("expected labeled branch: {simplified:#?}");
        };
        assert_eq!(
            branch.as_ref(),
            &CStmt::Expr(condition),
            "dropping both redundant gotos must not drop condition side effects"
        );
    }

    fn first_label_after_stmt_named(body: &CStmt, name: &str) -> Option<String> {
        let CStmt::Block(items) = body else {
            return None;
        };
        let idx = items
            .iter()
            .position(|it| get_first_label_from_item(it).as_deref() == Some(name))?;
        get_first_label_from_item(items.get(idx + 1)?)
    }
}
