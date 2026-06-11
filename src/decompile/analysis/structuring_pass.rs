
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::clight_pass::invert_condition;
use crate::decompile::passes::pass::IRPass;
use crate::util::exec_order_key;
use crate::x86::op::{Comparison, Condition};
use crate::x86::types::{Address, BuiltinArg, Constant, CsharpminorExpr, CsharpminorStmt, Node, RTLReg, Symbol};
use ascent::ascent_par;
use ascent::Dual;
use ascent::lattice::set::Set;
use log::debug;
use rayon::prelude::*;
use std::collections::{HashMap, HashSet};

fn dom_set_with_self(strict: &Set<Node>, n: Node) -> Set<Node> {
    let mut s = strict.0.clone();
    s.insert(n);
    Set(s)
}

pub struct StructuringPass;

impl IRPass for StructuringPass {
    fn name(&self) -> &'static str {
        "Structuring"
    }

    fn run(&self, db: &mut DecompileDB) {
        // Build working set from csharp_stmt_candidate
        let original: HashMap<Node, CsharpminorStmt> = db
            .rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt_candidate")
            .map(|(n, s)| (*n, s.clone()))
            .collect();
        let mut working = original.clone();

        // Apply optimizations in-memory (csharp_stmt_candidate is preserved)
        propagate_copies(&mut working, db);
        inline_constants(&mut working, db);
        eliminate_dead_returns(&mut working, db);
        inline_single_use_temps(&mut working, db);
        lift_setcc_arith_to_ite(&mut working, db);

        // Push only the deltas to csharp_stmt_override (O(N) lookup via HashMap)
        for (node, new_stmt) in &working {
            let is_changed = original.get(node).map_or(true, |orig| orig != new_stmt);
            if is_changed {
                db.rel_push("csharp_stmt_override", (*node, new_stmt.clone()));
            }
        }

        // instr_in_function is multi-valued: shared nodes (e.g. PLT trampolines) belong to every reaching function.
        let node_to_funcs: HashMap<Node, Vec<Address>> = {
            let mut groups: HashMap<Node, Vec<Address>> = HashMap::new();
            for (n, f) in db.rel_iter::<(Node, Address)>("instr_in_function") {
                groups.entry(*n).or_default().push(*f);
            }
            for v in groups.values_mut() {
                v.sort();
                v.dedup();
            }
            groups
        };

        // Next relation for target resolution and sequential ordering
        let next_map: HashMap<Node, Node> = db
            .rel_iter::<(Node, Node)>("next")
            .map(|&(a, b)| (a, b))
            .collect();

        // CF-6: include cminor_succ preds so taint-mirror can catch edges clight sees but the function-local stmt view misses (cross-function preds, preds with no csharp stmt); values sorted for determinism.
        let cminor_preds: HashMap<Node, Vec<Node>> = {
            let mut m: HashMap<Node, Vec<Node>> = HashMap::new();
            for &(src, dst) in db.rel_iter::<(Node, Node)>("cminor_succ") {
                m.entry(dst).or_default().push(src);
            }
            for v in m.values_mut() {
                v.sort_unstable();
                v.dedup();
            }
            m
        };

        // Authoritative function entry from emit_function; may point to a non-stmt node that structure() resolves through next_map.
        let func_entry: HashMap<Address, Node> = db
            .rel_iter::<(Address, Symbol, Node)>("emit_function")
            .map(|(addr, _, entry)| (*addr, *entry))
            .collect();

        let all_stmts: Vec<(Node, CsharpminorStmt)> = working
            .into_iter()
            .collect();

        let mut func_stmts: HashMap<Address, Vec<(Node, CsharpminorStmt)>> = HashMap::new();
        let mut unowned_stmts: Vec<(Node, CsharpminorStmt)> = Vec::new();

        for (node, stmt) in &all_stmts {
            if let Some(funcs) = node_to_funcs.get(node) {
                for &func_addr in funcs {
                    func_stmts
                        .entry(func_addr)
                        .or_default()
                        .push((*node, stmt.clone()));
                }
            } else {
                unowned_stmts.push((*node, stmt.clone()));
            }
        }

        for stmts in func_stmts.values_mut() {
            stmts.sort_by_key(|(n, _)| *n);
        }

        // Process functions in parallel
        let per_func_results: Vec<_> = func_stmts.par_iter()
            .map(|(func_addr, stmts)| {
                if stmts.len() <= 1 {
                    return (*func_addr, StructuringResult {
                        stmts: stmts.clone(),
                        goto_is_break: vec![],
                        switch_chain_members: vec![],
                        valid_switches: vec![],
                        ifbody_true: vec![],
                        ifbody_false: vec![],
                        join_points: vec![],
                        scond_no_join: vec![],
                    });
                }

                let declared_entry = func_entry.get(func_addr).copied();
                let structured = structure(stmts, &next_map, declared_entry, &cminor_preds);
                (*func_addr, structured)
            })
            .collect();

        // Merge results
        let mut result_stmts: Vec<(Node, CsharpminorStmt)> = Vec::new();
        let mut all_goto_is_break: Vec<(Node, Node)> = Vec::new();
        let mut all_switch_members: Vec<(Address, Node, Node, u64, i64, Node)> = Vec::new();
        let mut all_valid_switches: Vec<(Address, Node, u64)> = Vec::new();
        let mut all_ifbody_true: Vec<(Address, Node, Node)> = Vec::new();
        let mut all_ifbody_false: Vec<(Address, Node, Node)> = Vec::new();
        let mut all_join_points: Vec<(Address, Node, Node)> = Vec::new();
        let mut all_scond_no_join: Vec<(Address, Node)> = Vec::new();
        for (func_addr, structured) in per_func_results {
            result_stmts.extend(structured.stmts);
            all_goto_is_break.extend(structured.goto_is_break);
            for (head, member, reg, val, target) in &structured.switch_chain_members {
                all_switch_members.push((func_addr, *head, *member, *reg, *val, *target));
            }
            for (head, reg) in &structured.valid_switches {
                all_valid_switches.push((func_addr, *head, *reg));
            }
            for (branch, member) in &structured.ifbody_true {
                all_ifbody_true.push((func_addr, *branch, *member));
            }
            for (branch, member) in &structured.ifbody_false {
                all_ifbody_false.push((func_addr, *branch, *member));
            }
            for (branch, join) in &structured.join_points {
                all_join_points.push((func_addr, *branch, *join));
            }
            for branch in &structured.scond_no_join {
                all_scond_no_join.push((func_addr, *branch));
            }
        }

        result_stmts.extend(unowned_stmts);

        // Preserve pre-existing csharp_stmt tuples in case the single-producer invariant breaks.
        let existing: Vec<(Node, CsharpminorStmt)> = db
            .rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt")
            .map(|(n, s)| (*n, s.clone()))
            .collect();

        // Shared nodes are structured once per owning function, so the same (node, stmt) can appear multiple times.
        let mut seen: HashSet<(Node, CsharpminorStmt)> = HashSet::new();
        let new_rel = ascent::boxcar::Vec::<(Node, CsharpminorStmt)>::new();
        for tuple in existing.into_iter().chain(result_stmts) {
            if seen.insert(tuple.clone()) {
                new_rel.push(tuple);
            }
        }
        db.rel_set("csharp_stmt", new_rel);

        let break_rel = ascent::boxcar::Vec::<(Node, Node)>::new();
        for tuple in all_goto_is_break {
            break_rel.push(tuple);
        }
        db.rel_set("goto_is_break", break_rel);

        let switch_member_rel = ascent::boxcar::Vec::<(Address, Node, Node, u64, i64, Node)>::new();
        for tuple in all_switch_members {
            switch_member_rel.push(tuple);
        }
        db.rel_set("switch_chain_member", switch_member_rel);

        let valid_switch_rel = ascent::boxcar::Vec::<(Address, Node, u64)>::new();
        for tuple in &all_valid_switches {
            valid_switch_rel.push(*tuple);
        }
        db.rel_set("valid_switch_chain", valid_switch_rel);

        let emit_switch_rel = ascent::boxcar::Vec::<(Address, Node, u64)>::new();
        for tuple in &all_valid_switches {
            emit_switch_rel.push(*tuple);
        }
        db.rel_set("emit_switch_chain", emit_switch_rel);

        // Export if-body structural metadata for clight_select compound assembly
        let ifbody_true_rel = ascent::boxcar::Vec::<(Address, Node, Node)>::new();
        for tuple in all_ifbody_true {
            ifbody_true_rel.push(tuple);
        }
        db.rel_set("emit_ifbody_true", ifbody_true_rel);

        let ifbody_false_rel = ascent::boxcar::Vec::<(Address, Node, Node)>::new();
        for tuple in all_ifbody_false {
            ifbody_false_rel.push(tuple);
        }
        db.rel_set("emit_ifbody_false", ifbody_false_rel);

        let join_point_rel = ascent::boxcar::Vec::<(Address, Node, Node)>::new();
        for tuple in all_join_points {
            join_point_rel.push(tuple);
        }
        db.rel_set("emit_join_point", join_point_rel);

        let scond_no_join_rel = ascent::boxcar::Vec::<(Address, Node)>::new();
        for tuple in all_scond_no_join {
            scond_no_join_rel.push(tuple);
        }
        db.rel_set("emit_scond_no_join", scond_no_join_rel);
    }

    fn inputs(&self) -> &'static [&'static str] {
        &["csharp_stmt_candidate", "instr_in_function", "single_def_const", "dead_def", "code_in_block", "next", "emit_inline_temp", "emit_var_type_candidate", "emit_function", "emit_function_param_candidate"]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &["csharp_stmt", "csharp_stmt_override", "goto_is_break", "switch_chain_member", "valid_switch_chain", "emit_switch_chain",
          "emit_ifbody_true", "emit_ifbody_false", "emit_join_point", "emit_scond_no_join", "emit_var_type_candidate"]
    }
}

fn is_terminal_stmt(stmt: &CsharpminorStmt) -> bool {
    match stmt {
        CsharpminorStmt::Sjump(_)
        | CsharpminorStmt::Sreturn(_)
        | CsharpminorStmt::Stailcall(_, _, _)
        | CsharpminorStmt::Scond(_, _, _, _)
        | CsharpminorStmt::Sjumptable(_, _) => true,
        CsharpminorStmt::Scall(_, _, either::Either::Right(either::Either::Right(name)), _) => {
            matches!(
                *name,
                "abort"
                    | "exit"
                    | "_exit"
                    | "_Exit"
                    | "__assert_fail"
                    | "__assert_perror_fail"
                    | "__stack_chk_fail"
                    | "__fortify_fail"
                    | "pthread_exit"
                    | "longjmp"
                    | "_longjmp"
                    | "siglongjmp"
                    | "__cxa_throw"
                    | "__cxa_rethrow"
                    | "quick_exit"
                    | "thrd_exit"
            )
        }
        CsharpminorStmt::Sifthenelse(_, _, then_s, else_s) => {
            is_terminal_stmt(then_s) && is_terminal_stmt(else_s)
        }
        _ => false,
    }
}

// CFG analysis, reachability, if-then-else body, loop, and switch detection
ascent_par! {
    pub struct StructuringProgram;

    relation stmt(Node, CsharpminorStmt);
    relation seq_next(Node, Node);

    relation cfg_edge(Node, Node);
    cfg_edge(*node, *target) <--
        stmt(node, ?CsharpminorStmt::Sjump(target));

    cfg_edge(*node, *t) <--
        stmt(node, ?CsharpminorStmt::Scond(_, _, t, _));
    cfg_edge(*node, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(_, _, _, f));

    relation jumptable_target(Node, Node);
    cfg_edge(*node, *target) <-- jumptable_target(node, target);

    relation is_terminal(Node);
    is_terminal(*node) <-- stmt(node, s), if is_terminal_stmt(s);

    cfg_edge(*node, *next) <--
        stmt(node, _),
        seq_next(node, next),
        !is_terminal(node);

    // Scond where neither target dominates the branch (not a back edge) is an if-then-else candidate
    relation scond_node(Node, Node, Node);
    scond_node(*node, *t, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(_, _, t, f)),
        !dominates(node, t),
        !dominates(node, f);

    // Demand-driven reachability: transitive closure from scond targets only (not all V nodes), reducing O(V^2) to O(T*V) where T = unique scond targets.
    relation scond_target(Node);
    scond_target(*t) <-- scond_node(_, t, _);
    scond_target(*f) <-- scond_node(_, _, f);

    relation target_reaches(Node, Node);
    target_reaches(*src, *next) <-- scond_target(src), cfg_edge(src, next);
    target_reaches(*src, *next) <-- target_reaches(src, cur), cfg_edge(cur, next);

    relation target_reaches_or_eq(Node, Node);
    target_reaches_or_eq(*a, *b) <-- target_reaches(a, b);
    target_reaches_or_eq(*t, *t) <-- scond_node(_, t, _), is_terminal(t);
    target_reaches_or_eq(*f, *f) <-- scond_node(_, _, f), is_terminal(f);

    relation join_candidate(Node, Node);
    join_candidate(*branch, *node) <--
        scond_node(branch, t, f),
        target_reaches_or_eq(t, node),
        target_reaches_or_eq(f, node),
        dominates(node, branch),
        postdominates(branch, node);

    lattice join_point(Node, ascent::Dual<Node>);
    join_point(*branch, ascent::Dual(*node)) <--
        join_candidate(branch, node);

    // (target, branch): each condition branch's two CFG targets, tagged with the branch.
    relation scond_branch_target(Node, Node);
    scond_branch_target(*t, *branch) <-- scond_node(branch, t, _);
    scond_branch_target(*f, *branch) <-- scond_node(branch, _, f);

    // A node directly targeted by >=2 distinct condition branches.
    relation multi_branch_target(Node);
    multi_branch_target(*node) <--
        scond_branch_target(node, b1),
        scond_branch_target(node, b2),
        if b1 != b2;

    // A shared landing pad of a MULTI-WAY guard chain that merges back into common code: it is targeted by >=2 distinct branches AND it flows on to a join point that is ITSELF targeted by >=2 distinct branches (so the post-pad merge is a genuine multi-way reconvergence, e.g. `if (A||B|| !D) { error; } ok:` where both the error block and the ok/return block are jumped to by several guards). Inlining such a pad into one branch's if-body steals it from the others (collapsing the chain, dropping their conditions) or duplicates it onto the wrong path; it must stay a standalone labeled block reached by `goto`. A clean `&&`/`||` short-circuit whose shared exit merges via a plain fallthrough/jump (join not itself a branch target) is NOT flagged, so the existing inliner keeps folding it goto-free; neither is a terminal-exit guard chain (no join to reach).
    relation shared_target(Node);
    shared_target(*node) <--
        multi_branch_target(node),
        join_point(_, ?ascent::Dual(j)),
        multi_branch_target(j),
        target_reaches_or_eq(node, j);

    // If-body membership: nodes reachable from branch targets, stopping at join point
    relation ifbody_true(Node, Node);
    relation ifbody_false(Node, Node);
    ifbody_true(*branch, *t) <--
        scond_node(branch, t, _),
        join_point(branch, ?ascent::Dual(join)),
        if t != join,
        !shared_target(t),
        !loop_header(t);

    ifbody_true(*branch, *next) <--
        ifbody_true(branch, cur),
        cfg_edge(cur, next),
        join_point(branch, ?ascent::Dual(join)),
        if next != join,
        !shared_target(next),
        dominates(next, branch),
        !loop_header(next),
        !loop_body_node(next);

    ifbody_false(*branch, *f) <--
        scond_node(branch, _, f),
        join_point(branch, ?ascent::Dual(join)),
        if f != join,
        !shared_target(f),
        !loop_header(f);

    ifbody_false(*branch, *next) <--
        ifbody_false(branch, cur),
        cfg_edge(cur, next),
        join_point(branch, ?ascent::Dual(join)),
        if next != join,
        !shared_target(next),
        dominates(next, branch),
        !loop_header(next),
        !loop_body_node(next);

    // No-join case: one branch exits, the other continues
    relation scond_no_join(Node);
    scond_no_join(*branch) <--
        scond_node(branch, _, _),
        !join_candidate(branch, _);

    ifbody_true(*branch, *t) <--
        scond_no_join(branch),
        scond_node(branch, t, _),
        !shared_target(t),
        !loop_header(t);
    ifbody_true(*branch, *next) <--
        scond_no_join(branch),
        ifbody_true(branch, cur),
        cfg_edge(cur, next),
        !shared_target(next),
        dominates(next, branch),
        !loop_header(next),
        !loop_body_node(next);

    ifbody_false(*branch, *f) <--
        scond_no_join(branch),
        scond_node(branch, _, f),
        !shared_target(f),
        !loop_header(f);
    ifbody_false(*branch, *next) <--
        scond_no_join(branch),
        ifbody_false(branch, cur),
        cfg_edge(cur, next),
        !shared_target(next),
        dominates(next, branch),
        !loop_header(next),
        !loop_body_node(next);

    // Entry node for the function (lowest address statement node)
    relation entry_node(Node);

    // Lattice-based dominator computation (Cooper-Harvey-Kennedy flavor), same shape as cshminor_pass. Storage is O(V*d) (d = dom-tree depth) vs the O(V^2) path_avoiding workspace this replaces; on vim it drops the pass peak by tens of GB.
    #[local] lattice strict_dom_set(Node, Dual<Set<Node>>);
    lattice dom_set(Node, Dual<Set<Node>>);

    dom_set(*entry, Dual(Set::singleton(*entry))) <--
        entry_node(entry);

    strict_dom_set(*n, Dual(p_doms.0.clone())) <--
        cfg_edge(p, n),
        dom_set(p, p_doms),
        !entry_node(n);

    dom_set(*n, Dual(dom_set_with_self(&strict.0, *n))) <--
        strict_dom_set(n, strict),
        !entry_node(n);

    // Strict dominance: d dominates n and d != n.
    relation dominates(Node, Node);
    dominates(*n, *d) <--
        dom_set(n, doms_dual),
        for d in doms_dual.0.iter(),
        if *d != *n;

    // Post-dominators: dominance on the reversed CFG, seeded from exit nodes (no outgoing cfg edge: returns, tailcalls, noreturn calls). An if-join must post-dominate the branch; this rejects "joins" that lie on one branch's exclusive (e.g. shared-error) path instead of at the true reconvergence point.
    relation exit_node(Node);
    exit_node(*n) <-- stmt(n, _), !cfg_edge(n, _);

    #[local] lattice strict_pdom_set(Node, Dual<Set<Node>>);
    lattice pdom_set(Node, Dual<Set<Node>>);

    pdom_set(*ex, Dual(Set::singleton(*ex))) <--
        exit_node(ex);

    strict_pdom_set(*n, Dual(s_doms.0.clone())) <--
        cfg_edge(n, s),
        pdom_set(s, s_doms),
        !exit_node(n);

    pdom_set(*n, Dual(dom_set_with_self(&strict.0, *n))) <--
        strict_pdom_set(n, strict),
        !exit_node(n);

    // Strict post-dominance: d post-dominates n and d != n.
    relation postdominates(Node, Node);
    postdominates(*n, *d) <--
        pdom_set(n, doms_dual),
        for d in doms_dual.0.iter(),
        if *d != *n;

    // Predecessor relation for reverse walks
    relation pred(Node, Node);
    pred(*to, *from) <-- cfg_edge(from, to);

    // Back edge: CFG edge where the target dominates the source (proper loop detection)
    relation back_edge(Node, Node);
    back_edge(*node, *target) <--
        cfg_edge(node, target),
        dominates(node, target),
        if *target != *node;
    // Self-loops are always back edges
    back_edge(*node, *node) <--
        cfg_edge(node, target),
        if *target == *node;

    // Natural loop body via reverse walk from latch
    relation loop_header(Node);
    loop_header(*header) <-- back_edge(_, header);

    relation loop_body(Node, Node);
    loop_body(*header, *header) <-- back_edge(_, header);
    loop_body(*header, *src) <-- back_edge(src, header);
    loop_body(*header, *p) <--
        loop_body(header, node),
        pred(node, p),
        dominates(p, header),
        if *p != *header;

    // Flat projection: node belongs to some loop body (used to guard if-body expansion)
    relation loop_body_node(Node);
    loop_body_node(*node) <-- loop_body(_, node);

    // Loop exit condition: Scond where one target stays in the loop and one exits
    relation loop_exit_cond(Node, Node, Node, Node);
    loop_exit_cond(*header, *cond_node, *f, *t) <--
        loop_body(header, cond_node),
        stmt(cond_node, ?CsharpminorStmt::Scond(_, _, t, f)),
        loop_body(header, t),
        !loop_body(header, f);

    loop_exit_cond(*header, *cond_node, *t, *f) <--
        loop_body(header, cond_node),
        stmt(cond_node, ?CsharpminorStmt::Scond(_, _, t, f)),
        loop_body(header, f),
        !loop_body(header, t);

    // Sjump inside loop targeting outside becomes break
    relation loop_break_jump(Node, Node, Node);

    loop_break_jump(*header, *node, *target) <--
        loop_body(header, node),
        stmt(node, ?CsharpminorStmt::Sjump(target)),
        !loop_body(header, target);

    // Exit cond closest to header (likely while condition)
    lattice primary_exit_cond(Node, ascent::Dual<Node>);
    primary_exit_cond(*header, ascent::Dual(*cond_node)) <--
        loop_exit_cond(header, cond_node, _, _);

    relation goto_is_break(Node, Node);
    goto_is_break(*node, *target) <-- loop_break_jump(_, node, target);

    relation cond_is_break(Node, Node);
    cond_is_break(*cond_node, *exit_target) <-- loop_exit_cond(_, cond_node, exit_target, _);

    relation break_stmt(Node, CsharpminorStmt);

    break_stmt(*node, CsharpminorStmt::Sbreak) <-- goto_is_break(node, _);
    break_stmt(*cond_node, CsharpminorStmt::Sifthenelse(
        cond.clone(), args.clone(),
        Box::new(CsharpminorStmt::Sbreak),
        Box::new(CsharpminorStmt::Snop),
    )) <--
        cond_is_break(cond_node, exit_target),
        stmt(cond_node, ?CsharpminorStmt::Scond(cond, args, t, _f)),
        if t == exit_target;

    break_stmt(*cond_node, CsharpminorStmt::Sifthenelse(
        invert_condition(cond), args.clone(),
        Box::new(CsharpminorStmt::Sbreak),
        Box::new(CsharpminorStmt::Snop),
    )) <--
        cond_is_break(cond_node, exit_target),
        stmt(cond_node, ?CsharpminorStmt::Scond(cond, args, _t, f)),
        if f == exit_target;

    relation trim_node(Node);

    // Sjump to sequential next is a nop
    trim_node(*node) <--
        stmt(node, ?CsharpminorStmt::Sjump(target)),
        seq_next(node, target);

    trim_node(*node) <--
        ifbody_true(branch, node),
        stmt(node, ?CsharpminorStmt::Sjump(target)),
        join_point(branch, ?ascent::Dual(join)),
        if *target == *join;

    trim_node(*node) <--
        ifbody_false(branch, node),
        stmt(node, ?CsharpminorStmt::Sjump(target)),
        join_point(branch, ?ascent::Dual(join)),
        if *target == *join;

    trim_node(*node) <--
        ifbody_true(branch, node),
        stmt(node, ?CsharpminorStmt::Sjump(target)),
        ifbody_true(branch, target);

    trim_node(*node) <--
        ifbody_false(branch, node),
        stmt(node, ?CsharpminorStmt::Sjump(target)),
        ifbody_false(branch, target);

    trim_node(*node) <--
        back_edge(node, _),
        stmt(node, ?CsharpminorStmt::Sjump(_));

    trim_node(*node) <-- goto_is_break(node, _);
    trim_node(*node) <-- cond_is_break(node, _);

    // Switch chain detection: if-else-if chains comparing same register for equality. Excludes nodes already classified as loop-exit conditions (cond_is_break), which are semantically `if (x == EOF) break;` rather than switch cases. Without this guard the chain extends across the break test (e.g., chaining `if (c == -1) break;` together with the real `case 'a'/'s'/'z'` body), causing the case bodies to be trimmed as switch interior and emit_loop_body to lose them.
    relation compares_eq(Node, u64, i64, Node, Node);

    // Ceq: true branch is the matching case, false branch continues
    compares_eq(*node, *reg, *val, *t, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompimm(cmp, val) = cond,
        if *cmp == Comparison::Ceq,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0],
        !cond_is_break(node, _);

    compares_eq(*node, *reg, *val, *t, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompuimm(cmp, val) = cond,
        if *cmp == Comparison::Ceq,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0],
        !cond_is_break(node, _);

    compares_eq(*node, *reg, *val, *t, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccomplimm(cmp, val) = cond,
        if *cmp == Comparison::Ceq,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0],
        !cond_is_break(node, _);

    compares_eq(*node, *reg, *val, *t, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompluimm(cmp, val) = cond,
        if *cmp == Comparison::Ceq,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0],
        !cond_is_break(node, _);

    // Cne: inverted; false branch matches (reg == val), true continues
    compares_eq(*node, *reg, *val, *f, *t) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompimm(cmp, val) = cond,
        if *cmp == Comparison::Cne,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0],
        !cond_is_break(node, _);

    compares_eq(*node, *reg, *val, *f, *t) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompuimm(cmp, val) = cond,
        if *cmp == Comparison::Cne,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0],
        !cond_is_break(node, _);

    compares_eq(*node, *reg, *val, *f, *t) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccomplimm(cmp, val) = cond,
        if *cmp == Comparison::Cne,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0],
        !cond_is_break(node, _);

    compares_eq(*node, *reg, *val, *f, *t) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompluimm(cmp, val) = cond,
        if *cmp == Comparison::Cne,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0],
        !cond_is_break(node, _);

    relation switch_chain(Node, Node, u64, i64, Node);
    switch_chain(*node, *node, *reg, *val, *t) <--
        compares_eq(node, reg, val, t, _);

    // Direct chain only: false branch of prev is a compares_eq on the same register. Bridge rules across non-Ceq Sconds were removed because their Scond outlived the dead-coded chain and jumped to dropped members.
    switch_chain(*head, *f, *reg, *next_val, *next_t) <--
        switch_chain(head, prev, reg, _, _),
        compares_eq(prev, _, _, _, f),
        compares_eq(f, reg, next_val, next_t, _);

    relation switch_count(Node, usize);
    switch_count(*head, count) <--
        switch_chain(head, _, _, _, _),
        agg count = ascent::aggregators::count() in switch_chain(head, _, _, _, _);

    relation valid_switch(Node, u64);
    valid_switch(*head, *reg) <--
        switch_count(head, count),
        if *count >= 3,
        switch_chain(head, _, reg, _, _);

    relation is_interior_member(Node);
    is_interior_member(*member) <--
        switch_chain(head, member, _, _, _),
        if head != member;

    relation primary_switch(Node, u64);
    primary_switch(*head, *reg) <--
        valid_switch(head, reg),
        !is_interior_member(head);

    relation switch_default(Node, Node);
    switch_default(*head, *f) <--
        primary_switch(head, _),
        switch_chain(head, member, _, _, _),
        compares_eq(member, _, _, _, f),
        !switch_chain(head, f, _, _, _);

    trim_node(*member) <--
        primary_switch(head, _),
        switch_chain(head, member, _, _, _),
        if head != member;

}

pub struct StructuringResult {
    pub stmts: Vec<(Node, CsharpminorStmt)>,
    pub goto_is_break: Vec<(Node, Node)>,
    pub switch_chain_members: Vec<(Node, Node, u64, i64, Node)>,
    pub valid_switches: Vec<(Node, u64)>,
    pub ifbody_true: Vec<(Node, Node)>,
    pub ifbody_false: Vec<(Node, Node)>,
    pub join_points: Vec<(Node, Node)>,
    pub scond_no_join: Vec<Node>,
}

// Run CFG analysis, if-then-else construction, loop recovery, and break/continue conversion
pub fn structure(
    stmts: &[(Node, CsharpminorStmt)],
    next_map: &HashMap<Node, Node>,
    declared_entry: Option<Node>,
    cminor_preds: &HashMap<Node, Vec<Node>>,
) -> StructuringResult {
    if stmts.is_empty() {
        return StructuringResult {
            stmts: vec![],
            goto_is_break: vec![],
            switch_chain_members: vec![],
            valid_switches: vec![],
            ifbody_true: vec![],
            ifbody_false: vec![],
            join_points: vec![],
            scond_no_join: vec![],
        };
    }

    let mut current_stmts: Vec<(Node, CsharpminorStmt)> = stmts.to_vec();
    current_stmts.sort_by_key(|(n, _)| *n);

    // Resolve synthetic/missing Scond targets by walking `next` chain.
    let stmt_nodes: HashSet<Node> = current_stmts.iter().map(|(n, _)| *n).collect();

    let resolve_target = |target: Node| -> Node {
        if stmt_nodes.contains(&target) {
            return target;
        }
        let real_addr = target & !(1u64 << 62);
        if stmt_nodes.contains(&real_addr) {
            return real_addr;
        }
        // Resolves into synthetic chains too: a branch may land on a fused store (e.g. `global = CONST`) whose real head has no statement after const folding.
        walk_next_to_stmt(real_addr, next_map, &stmt_nodes).unwrap_or(target)
    };

    for (_, stmt) in &mut current_stmts {
        match stmt {
            CsharpminorStmt::Scond(_, _, ifso, ifnot) => {
                *ifso = resolve_target(*ifso);
                *ifnot = resolve_target(*ifnot);
            }
            CsharpminorStmt::Sjump(target) => {
                *target = resolve_target(*target);
            }
            _ => {}
        }
    }

    let mut prog = StructuringProgram::default();

    for (node, s) in &current_stmts {
        prog.stmt.push((*node, s.clone()));
    }

    let seq_edges = compute_sequential_edges(&current_stmts, next_map);
    for &(a, b) in &seq_edges {
        prog.seq_next.push((a, b));
    }

    for (node, stmt) in &current_stmts {
        if let CsharpminorStmt::Sjumptable(_, targets) = stmt {
            for t in targets.as_ref() {
                prog.jumptable_target.push((*node, *t));
            }
        }
    }

    // Authoritative entry from emit_function, resolved to a stmt node through `next` chain; falls back to lowest-address stmt if emit_function entry is missing or unreachable.
    let entry_node = declared_entry
        .and_then(|e| {
            if stmt_nodes.contains(&e) {
                Some(e)
            } else {
                walk_next_to_stmt(e, next_map, &stmt_nodes)
            }
        })
        .unwrap_or_else(|| {
            debug!("structuring: falling back to lowest-address entry");
            current_stmts[0].0
        });
    prog.entry_node.push((entry_node,));

    prog.run();

    let stmt_map: HashMap<Node, CsharpminorStmt> =
        current_stmts.iter().cloned().collect();

    let join_points: HashMap<Node, Node> = prog
        .join_point
        .iter()
        .map(|entry| {
            let guard = entry.read().unwrap();
            (guard.0, (guard.1).0)
        })
        .collect();

    let scond_nodes: HashMap<Node, (Node, Node)> = prog
        .scond_node
        .iter()
        .map(|(branch, t, f)| (*branch, (*t, *f)))
        .collect();

    let no_join_nodes: HashSet<Node> = prog
        .scond_no_join
        .iter()
        .map(|(n,)| *n)
        .collect();

    let mut true_bodies: HashMap<Node, Vec<Node>> = HashMap::new();
    for (branch, member) in &prog.ifbody_true {
        true_bodies.entry(*branch).or_default().push(*member);
    }
    for nodes in true_bodies.values_mut() {
        nodes.sort();
    }


    let mut false_bodies: HashMap<Node, Vec<Node>> = HashMap::new();
    for (branch, member) in &prog.ifbody_false {
        false_bodies.entry(*branch).or_default().push(*member);
    }
    for nodes in false_bodies.values_mut() {
        nodes.sort();
    }

    let mut loop_bodies: HashMap<Node, Vec<Node>> = HashMap::new();
    for (header, member) in &prog.loop_body {
        loop_bodies.entry(*header).or_default().push(*member);
    }
    for nodes in loop_bodies.values_mut() {
        nodes.sort();
        nodes.dedup();
    }

    let back_edges: Vec<(Node, Node)> = prog
        .back_edge
        .iter()
        .map(|(src, header)| (*src, *header))
        .collect();

    let trimmed: HashSet<Node> = prog
        .trim_node
        .iter()
        .map(|(n,)| *n)
        .collect();

    let break_stmts: HashMap<Node, CsharpminorStmt> = prog
        .break_stmt
        .iter()
        .map(|(n, s)| (*n, s.clone()))
        .collect();

    let goto_is_break: Vec<(Node, Node)> = prog
        .goto_is_break
        .iter()
        .map(|(n, t)| (*n, *t))
        .collect();

    let loop_exit_cond_nodes: HashSet<Node> = prog
        .cond_is_break
        .iter()
        .map(|(n, _)| *n)
        .collect();

    let primary_exits: HashMap<Node, Node> = prog
        .primary_exit_cond
        .iter()
        .map(|entry| {
            let guard = entry.read().unwrap();
            (guard.0, (guard.1).0)
        })
        .collect();

    let mut switch_chain_members: Vec<(Node, Node, u64, i64, Node)> = prog
        .switch_chain
        .iter()
        .filter(|(head, _, _, _, _)| {
            prog.primary_switch.iter().any(|(h, _)| h == head)
        })
        .map(|(head, member, reg, val, target)| (*head, *member, *reg, *val, *target))
        .collect();

    let mut valid_switches: Vec<(Node, u64)> = prog
        .primary_switch
        .iter()
        .map(|(head, reg)| (*head, *reg))
        .collect();

    // Fallback: imperative comparison tree analysis for complex switch patterns. Runs alongside Ascent-recovered switches, deduplicating by head AND by any node that already participates in an Ascent-recovered chain. Without the second guard the tree walker rediscovers each Ascent chain starting from every interior Ceq node (e.g., for `case 0/1/2/3` it would emit four switches rooted at 0,1,2,3), producing the back-to-back duplicate `switch` blocks observed in coreutils mains.
    let ascent_chain_nodes: HashSet<Node> = switch_chain_members
        .iter()
        .map(|(_, member, _, _, _)| *member)
        .collect();

    // CF-1: canonicalize identical dispatch roots. The walker treats every re-entry point into a shared compare cascade as a fresh switch root and each root expands the FULL dispatch (one binary dispatch observed as 25 byte-identical C switches in __strftime_internal). Two roots with the same discriminant, the same walked MEMBER NODES, and the same (value -> target) mapping are the same physical dispatch entered at different points - shared members imply the shared tail, hence the same no-match/default continuation - so every duplicate root's statement collapses to `goto canonical_head` and contributes no switch of its own.
    let mut canon_by_shape: HashMap<(u64, Vec<Node>, Vec<(i64, Node)>), Node> = HashMap::new();
    let mut dup_redirects: Vec<(Node, Node)> = Vec::new();
    {
        let mut by_head: HashMap<Node, (u64, Vec<Node>, Vec<(i64, Node)>)> = HashMap::new();
        for (head, member, reg, val, target) in &switch_chain_members {
            let e = by_head.entry(*head).or_insert((*reg, Vec::new(), Vec::new()));
            e.1.push(*member);
            e.2.push((*val, *target));
        }
        // Sorted member set + sorted (value -> target) map form the shape key; heads visit in ascending order so the lowest head is deterministically canonical.
        let mut heads: Vec<Node> = by_head.keys().copied().collect();
        heads.sort_unstable();
        let mut dup_heads: HashSet<Node> = HashSet::new();
        for h in heads {
            let (reg, mut members, mut pairs) = by_head.remove(&h).expect("head collected above");
            members.sort_unstable();
            members.dedup();
            pairs.sort_unstable();
            pairs.dedup();
            match canon_by_shape.entry((reg, members, pairs)) {
                std::collections::hash_map::Entry::Occupied(e) => {
                    dup_redirects.push((h, *e.get()));
                    dup_heads.insert(h);
                }
                std::collections::hash_map::Entry::Vacant(v) => {
                    v.insert(h);
                }
            }
        }
        switch_chain_members.retain(|(head, _, _, _, _)| !dup_heads.contains(head));
        valid_switches.retain(|(head, _)| !dup_heads.contains(head));
    }

    // Walker fallback roots flow through the same shape canonicalization: a root whose head already belongs to an Ascent chain is skipped outright, and a root whose shape duplicates an already-kept switch (Ascent or earlier walker root) collapses to a redirect instead of a fresh switch. Roots process LARGEST-first so a full-cascade walk canonicalizes before the mid-entry walks that see only its tail.
    let mut tree_results = detect_comparison_tree_switches(&current_stmts, next_map, &loop_exit_cond_nodes);
    tree_results.sort_by(|a, b| b.2.len().cmp(&a.2.len()).then(a.0.cmp(&b.0)));
    // CF-6 diagnostics: per-function dump of walker inputs/results and canonicalization decisions. Buffered into one eprint per function so parallel structure() calls do not interleave lines.
    let cf6_trace = std::env::var("MANIFOLD_CF6_TRACE").is_ok();
    if cf6_trace {
        let mut buf = String::new();
        buf.push_str(&format!("[CF6] === function entry {:#x} ===\n", entry_node));
        for (n, s) in &current_stmts {
            match s {
                CsharpminorStmt::Scond(cond, args, t, f) => {
                    buf.push_str(&format!("[CF6] stmt {:#x}: Scond {:?} args={:?} t={:#x} f={:#x} break={}\n",
                        n, cond, args, t, f, loop_exit_cond_nodes.contains(n)));
                }
                CsharpminorStmt::Sset(d, e) => {
                    buf.push_str(&format!("[CF6] stmt {:#x}: Sset r{} = {:?}\n", n, d, e));
                }
                CsharpminorStmt::Sjump(t) => {
                    buf.push_str(&format!("[CF6] stmt {:#x}: Sjump {:#x}\n", n, t));
                }
                _ => {}
            }
        }
        let mut ac: Vec<(Node, Node, u64, i64, Node)> = switch_chain_members.clone();
        ac.sort_unstable();
        for (h, m, r, v, t) in ac {
            buf.push_str(&format!("[CF6] ascent row: head={:#x} member={:#x} reg=r{} val={} target={:#x}\n", h, m, r, v, t));
        }
        for (head, reg, cases) in &tree_results {
            buf.push_str(&format!("[CF6] walker root {:#x} reg=r{} cases={:?}\n", head, reg,
                cases.iter().map(|(v, t, m)| format!("{}=>{:#x}@{:#x}", v, t, m)).collect::<Vec<_>>()));
        }
        eprint!("{}", buf);
    }
    // Per-reg union of member nodes already claimed by kept switches (Ascent rows seed it; walker keeps extend it). A later root whose member NODES are all already claimed is the same physical dispatch entered mid-cascade; when its (value -> target) pairs do NOT match the kept switch (the values live in a different space because the entry sits after an in-place discriminant rebase), redirecting is UNSOUND (the kept head would re-test the rebased value in root space), so the root is skipped outright: its raw statements remain and the kept switch already owns the shared members.
    let mut kept_members_by_reg: HashMap<u64, HashSet<Node>> = HashMap::new();
    for (_, member, reg, _, _) in &switch_chain_members {
        kept_members_by_reg.entry(*reg).or_default().insert(*member);
    }
    for (head, reg, ref cases) in &tree_results {
        if ascent_chain_nodes.contains(head) { continue; }
        if cases.len() >= 3 {
            let mut members: Vec<Node> = cases.iter().map(|(_, _, m)| *m).collect();
            members.sort_unstable();
            members.dedup();
            let mut pairs: Vec<(i64, Node)> = cases.iter().map(|(v, t, _)| (*v, *t)).collect();
            pairs.sort_unstable();
            pairs.dedup();
            // Subset merge on shared physical nodes: a mid-cascade entry redirects to its containing switch's head. Use min() over all containing switches (not find_map) -- two containing switches caused a random redirect target (FUN_14f00 flicker); lowest head is canonical, matching the ascending-heads policy above. Disjoint-member sibling cascades (compiler-duplicated, e.g. gcc tail-duplication) keep separate switches.
            let subset_canon = canon_by_shape
                .iter()
                .filter_map(|((kreg, kmembers, kpairs), khead)| {
                    if *kreg == *reg
                        && members.iter().all(|m| kmembers.binary_search(m).is_ok())
                        && pairs.iter().all(|p| kpairs.binary_search(p).is_ok())
                    {
                        Some(*khead)
                    } else {
                        None
                    }
                })
                .min();
            if let Some(canon) = subset_canon {
                if canon != *head {
                    dup_redirects.push((*head, canon));
                }
                continue;
            }
            // Cross-space mid-entry: every member node already claimed by kept same-reg switches, but the value pairs differ (entry after an in-place rebase). Skip without redirect.
            if let Some(kept) = kept_members_by_reg.get(reg) {
                if !members.is_empty() && members.iter().all(|m| kept.contains(m)) {
                    if cf6_trace {
                        eprintln!("[CF6] root {:#x} skipped: member nodes already claimed by kept same-reg switches", head);
                    }
                    continue;
                }
            }
            canon_by_shape.insert((*reg, members, pairs), *head);
            let kept = kept_members_by_reg.entry(*reg).or_default();
            for &(val, target, member_node) in cases {
                switch_chain_members.push((*head, member_node, *reg, val, target));
                kept.insert(member_node);
            }
            valid_switches.push((*head, *reg));
        }
    }

    // CF-6: clight suppresses clean chain members, killing the last compare's no-match exit edge; rewrite each untainted leaf (one chain-exiting branch) to `Sjump(exit)` and reattribute its case rows to the head, so the surviving goto IS the default routing. Tainted leaves keep their raw compare. Applies to both Ascent-recovered chains and walker trees.
    let mut leaf_rewrites: Vec<(Node, Node)> = Vec::new();
    {
        // Local CFG pred map mirrors the edge set clight's chain_member_tainted sees via cminor_succ.
        let seq_map: HashMap<Node, Node> = seq_edges.iter().copied().collect();
        let mut pred_map: HashMap<Node, Vec<Node>> = HashMap::new();
        for (n, s) in &current_stmts {
            let mut outs: Vec<Node> = Vec::new();
            match s {
                CsharpminorStmt::Scond(_, _, t, f) => {
                    outs.push(*t);
                    outs.push(*f);
                }
                CsharpminorStmt::Sjump(t) => outs.push(*t),
                CsharpminorStmt::Sjumptable(_, ts) => outs.extend(ts.iter().copied()),
                _ => {}
            }
            if !is_terminal_stmt(s) {
                if let Some(&nx) = seq_map.get(n) {
                    outs.push(nx);
                }
            }
            for o in outs {
                pred_map.entry(o).or_default().push(*n);
            }
        }

        // Only sole-owner non-head members are rewrite-eligible: a node claimed by another switch would have its goto suppressed or collide with that switch's Sswitch materialization.
        let mut member_heads: HashMap<Node, Vec<Node>> = HashMap::new();
        for (h, m, _, _, _) in &switch_chain_members {
            if *m != *h {
                member_heads.entry(*m).or_default().push(*h);
            }
        }
        for v in member_heads.values_mut() {
            v.sort_unstable();
            v.dedup();
        }
        let head_set: HashSet<Node> = valid_switches.iter().map(|(h, _)| *h).collect();

        // Heads in ascending order for deterministic processing.
        let mut heads: Vec<Node> = valid_switches.iter().map(|(h, _)| *h).collect();
        heads.sort_unstable();
        heads.dedup();
        let mut demoted_heads: HashSet<Node> = HashSet::new();
        for head in heads {
            let rows: Vec<(Node, Node)> = switch_chain_members
                .iter()
                .filter(|(h, _, _, _, _)| *h == head)
                .map(|(_, m, _, _, t)| (*m, *t))
                .collect();
            let mut chain: HashSet<Node> = rows.iter().map(|(m, _)| *m).collect();
            chain.insert(head);
            let case_targets: HashSet<Node> = rows.iter().map(|(_, t)| *t).collect();
            // Taint fixpoint mirroring clight's chain_member_tainted: union of local and cminor_succ preds is a superset, so the mirror can only over-taint (safe: skips rewrites), never under-taint.
            let mut tainted: HashSet<Node> = HashSet::new();
            loop {
                let mut changed = false;
                for &(m, _) in &rows {
                    if m == head || tainted.contains(&m) {
                        continue;
                    }
                    let local = pred_map.get(&m).map(|v| v.as_slice()).unwrap_or(&[]);
                    let global = cminor_preds.get(&m).map(|v| v.as_slice()).unwrap_or(&[]);
                    if local
                        .iter()
                        .chain(global.iter())
                        .any(|p| !chain.contains(p) || tainted.contains(p))
                    {
                        tainted.insert(m);
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            let mut members: Vec<Node> = rows.iter().map(|(m, _)| *m).filter(|m| *m != head).collect();
            members.sort_unstable();
            members.dedup();
            // Leaf = exactly one chain-exiting branch. Rewrite is sound: untainted leaves are only reached through suppressed in-chain compares, so `goto exit` IS the no-match branch.
            let mut head_leaves: Vec<(Node, Node)> = Vec::new();
            let mut exits: std::collections::BTreeSet<Node> = std::collections::BTreeSet::new();
            for &m in &members {
                if let Some(CsharpminorStmt::Scond(_, _, t, f)) = stmt_map.get(&m) {
                    let t_exit = !chain.contains(t) && !case_targets.contains(t);
                    let f_exit = !chain.contains(f) && !case_targets.contains(f);
                    match (t_exit, f_exit) {
                        (true, false) => {
                            exits.insert(*t);
                            head_leaves.push((m, *t));
                        }
                        (false, true) => {
                            exits.insert(*f);
                            head_leaves.push((m, *f));
                        }
                        // Both in-chain: suppressible. Both exiting: not one goto -- leave raw compare.
                        _ => {}
                    }
                }
            }
            // A splitter head (neither branch hits a case target, e.g. gcc's top-level `jg`) with multiple no-match exits is unsound as a defaultless Sswitch: rowless values would misroute silently. Demote such heads; a non-splitter head's multiple leaf exits are fine because routing guards between funnels survive as non-members or taint their successors.
            let head_splitter = match stmt_map.get(&head) {
                Some(CsharpminorStmt::Scond(_, _, t, f)) => {
                    // A head branch exiting the chain without hitting a case target is a no-match destination.
                    if !chain.contains(t) && !case_targets.contains(t) {
                        exits.insert(*t);
                    }
                    if !chain.contains(f) && !case_targets.contains(f) {
                        exits.insert(*f);
                    }
                    !case_targets.contains(t) && !case_targets.contains(f)
                }
                // Non-compare head: treat conservatively as splitter to demote multi-exit chains.
                _ => true,
            };
            if head_splitter && exits.len() > 1 {
                demoted_heads.insert(head);
                if cf6_trace {
                    eprintln!(
                        "[CF6] head {:#x} demoted: splitter head with {} distinct no-match exits {:?}",
                        head,
                        exits.len(),
                        exits.iter().map(|e| format!("{:#x}", e)).collect::<Vec<_>>()
                    );
                }
                continue;
            }
            for (m, exit) in head_leaves {
                if tainted.contains(&m) {
                    continue;
                }
                if head_set.contains(&m) {
                    continue;
                }
                if member_heads.get(&m).map_or(false, |hs| hs.as_slice() != [head]) {
                    continue;
                }
                leaf_rewrites.push((m, exit));
            }
        }
        if !demoted_heads.is_empty() {
            valid_switches.retain(|(h, _)| !demoted_heads.contains(h));
            switch_chain_members.retain(|(h, _, _, _, _)| !demoted_heads.contains(h));
        }
        if cf6_trace {
            for (m, ex) in &leaf_rewrites {
                eprintln!("[CF6] leaf member {:#x} rewritten to goto {:#x} (no-match routing)", m, ex);
            }
        }
        // Reattribute rewritten leaves' case rows to their head so chain_member_node no longer suppresses the node (its statement is now the default goto).
        let leaf_set: HashSet<Node> = leaf_rewrites.iter().map(|(m, _)| *m).collect();
        for row in switch_chain_members.iter_mut() {
            if leaf_set.contains(&row.1) {
                row.1 = row.0;
            }
        }
    }

    // Includes rewritten leaf nodes so they are excluded from if-then-else metadata: their scond_node/join facts describe a compare that no longer exists.
    let switch_member_nodes: HashSet<Node> = switch_chain_members
        .iter()
        .map(|(_, member, _, _, _)| *member)
        .chain(leaf_rewrites.iter().map(|(m, _)| *m))
        .collect();

    // Determine valid if-then-else branches for metadata export, excluding loop exit conditions and switch members.
    let skip_branches: HashSet<Node> = loop_exit_cond_nodes.iter()
        .chain(switch_member_nodes.iter())
        .copied()
        .collect();

    let valid_ite_branches: HashSet<Node> = join_points.keys()
        .chain(no_join_nodes.iter())
        .filter(|branch| !skip_branches.contains(branch))
        .copied()
        .collect();

    // Flat output: keep all statements, only trim redundant Sjumps and switch interior nodes
    let mut result_stmts: Vec<(Node, CsharpminorStmt)> = current_stmts.clone();

    result_stmts.retain(|(node, stmt)| {
        !(trimmed.contains(node) && matches!(stmt, CsharpminorStmt::Sjump(_)))
    });

    // Apply CF-1 duplicate-root redirects: the duplicate's compare statement is replaced by a jump to the canonical dispatch head. Sound because shape identity (same discriminant, same member nodes, same value->target map) means the canonical head performs the identical dispatch including the shared no-match continuation.
    for (dup, canon) in &dup_redirects {
        for entry in result_stmts.iter_mut() {
            if entry.0 == *dup {
                entry.1 = CsharpminorStmt::Sjump(*canon);
            }
        }
    }

    // Apply CF-6 leaf rewrites after dup_redirects: a node claimed by both gets the direct default goto (shorter than re-dispatching through the canonical head; both are correct).
    for (leaf, exit) in &leaf_rewrites {
        for entry in result_stmts.iter_mut() {
            if entry.0 == *leaf {
                entry.1 = CsharpminorStmt::Sjump(*exit);
            }
        }
    }

    result_stmts.sort_by_key(|(n, _)| *n);

    // Export if-body membership metadata (filtered to valid branches only)
    let mut out_ifbody_true: Vec<(Node, Node)> = Vec::new();
    let mut out_ifbody_false: Vec<(Node, Node)> = Vec::new();
    for (&branch, members) in &true_bodies {
        if valid_ite_branches.contains(&branch) {
            for &member in members {
                out_ifbody_true.push((branch, member));
            }
        }
    }
    for (&branch, members) in &false_bodies {
        if valid_ite_branches.contains(&branch) {
            for &member in members {
                out_ifbody_false.push((branch, member));
            }
        }
    }

    let out_join_points: Vec<(Node, Node)> = join_points.iter()
        .filter(|(branch, _)| valid_ite_branches.contains(branch))
        .map(|(&branch, &join)| (branch, join))
        .collect();

    let out_scond_no_join: Vec<Node> = no_join_nodes.iter()
        .filter(|branch| valid_ite_branches.contains(branch))
        .copied()
        .collect();

    debug!("=== Structuring complete ===");

    StructuringResult {
        stmts: result_stmts,
        goto_is_break,
        switch_chain_members,
        valid_switches,
        ifbody_true: out_ifbody_true,
        ifbody_false: out_ifbody_false,
        join_points: out_join_points,
        scond_no_join: out_scond_no_join,
    }
}

/// Walk GCC comparison trees (mixed eq/ne/range checks) to extract switch case values.
fn switch_disc_offset(op: &crate::x86::types::CminorBinop, cst: &Constant) -> Option<i64> {
    use crate::x86::types::CminorBinop;
    let raw = match (op, cst) {
        (CminorBinop::Oaddl, Constant::Olongconst(v))
        | (CminorBinop::Oadd, Constant::Ointconst(v))
        | (CminorBinop::Oaddl, Constant::Ointconst(v))
        | (CminorBinop::Oadd, Constant::Olongconst(v)) => *v,
        (CminorBinop::Osubl, Constant::Olongconst(v))
        | (CminorBinop::Osub, Constant::Ointconst(v))
        | (CminorBinop::Osubl, Constant::Ointconst(v))
        | (CminorBinop::Osub, Constant::Olongconst(v)) => v.wrapping_neg(),
        _ => return None,
    };
    if raw < i32::MIN as i64 || raw > i32::MAX as i64 {
        return None;
    }
    Some(raw)
}

// Path-interval helpers for the comparison-tree walker (inclusive bounds in root-discriminant space; None = unbounded).
fn clamp_lo(lo: Option<i64>, v: i64) -> Option<i64> {
    Some(lo.map_or(v, |l| l.max(v)))
}
fn clamp_hi(hi: Option<i64>, v: i64) -> Option<i64> {
    Some(hi.map_or(v, |h| h.min(v)))
}
// A finite, small, non-negative interval that may be enumerated as switch cases. Width and sign policy mirror the established unsigned range arms (< 32 values, lower bound >= 0).
fn enumerable_range(lo: Option<i64>, hi: Option<i64>) -> Option<(i64, i64)> {
    let (l, h) = (lo?, hi?);
    if l >= 0 && h >= l && h.checked_sub(l).map_or(false, |w| w < 32) {
        Some((l, h))
    } else {
        None
    }
}

/// True when a range-guard branch target is INTERIOR dispatch (further tests/rebases of the same discriminant, a jump table, or a loop-exit compare) rather than a case body. Enumerating an interval as cases is only sound when the branch lands on a body: an interior target means the values subdivide further and the deeper Ceq/Cne/jumptable nodes own them. Follows pure jump/nop/rebase preludes a bounded number of hops; unresolved chains conservatively count as interior (no enumeration).
fn range_target_is_interior(
    start: Node,
    disc_reg: RTLReg,
    stmt_map: &HashMap<Node, &CsharpminorStmt>,
    seq_next_map: &HashMap<Node, Node>,
    resolve_reg: &dyn Fn(RTLReg) -> (RTLReg, i64),
    cond_break_nodes: &HashSet<Node>,
) -> bool {
    let mut cur = start;
    for _ in 0..8 {
        if cond_break_nodes.contains(&cur) {
            return true;
        }
        match stmt_map.get(&cur) {
            Some(CsharpminorStmt::Scond(cond, args, _, _)) if args.len() == 1 => {
                let reg_opt = match &args[0] {
                    CsharpminorExpr::Evar(r) => Some(*r),
                    CsharpminorExpr::Ebinop(_, lhs, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
                        (CsharpminorExpr::Evar(r), CsharpminorExpr::Econst(_)) => Some(*r),
                        _ => None,
                    },
                    _ => None,
                };
                return match reg_opt {
                    Some(r) => {
                        let is_cmp = matches!(
                            cond,
                            Condition::Ccompimm(_, _)
                                | Condition::Ccompuimm(_, _)
                                | Condition::Ccomplimm(_, _)
                                | Condition::Ccompluimm(_, _)
                                | Condition::Cmaskzero(_)
                                | Condition::Cmasknotzero(_)
                        );
                        is_cmp && resolve_reg(r).0 == disc_reg
                    }
                    None => false,
                };
            }
            Some(CsharpminorStmt::Scond(_, _, _, _)) => return false,
            Some(CsharpminorStmt::Sjumptable(_, _)) => return true,
            Some(CsharpminorStmt::Sjump(t)) => {
                if *t == cur {
                    return false;
                }
                cur = *t;
            }
            Some(CsharpminorStmt::Snop) => match seq_next_map.get(&cur) {
                Some(&n) => cur = n,
                None => return false,
            },
            Some(CsharpminorStmt::Sset(_, expr)) => {
                // Discriminant-rebasing prelude (dst = disc +/- const, in-place or derived copy) precedes deeper dispatch; any other statement begins a case body.
                let rebase = match expr {
                    CsharpminorExpr::Ebinop(op, lhs, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
                        (CsharpminorExpr::Evar(src), CsharpminorExpr::Econst(cst)) => {
                            switch_disc_offset(op, cst).is_some() && resolve_reg(*src).0 == disc_reg
                        }
                        _ => false,
                    },
                    _ => false,
                };
                if !rebase {
                    return false;
                }
                match seq_next_map.get(&cur) {
                    Some(&n) => cur = n,
                    None => return false,
                }
            }
            _ => return false,
        }
    }
    true
}

/// Walk GCC comparison trees (mixed eq/ne/range checks) to extract switch case values.
fn detect_comparison_tree_switches(
    stmts: &[(Node, CsharpminorStmt)],
    next_map: &HashMap<Node, Node>,
    cond_break_nodes: &HashSet<Node>,
) -> Vec<(Node, u64, Vec<(i64, Node, Node)>)> {
    let stmt_map: HashMap<Node, &CsharpminorStmt> = stmts.iter().map(|(n, s)| (*n, s)).collect();

    let stmt_node_set: HashSet<Node> = stmts.iter().map(|(n, _)| *n).collect();
    let seq_next_map: HashMap<Node, Node> = stmts
        .iter()
        .filter_map(|&(node, _)| {
            walk_next_to_stmt(node, next_map, &stmt_node_set).map(|nxt| (node, nxt))
        })
        .collect();

    // Track register derivations: dst = src +/- offset. Skip self-derivations (dst == src) which arise from in-place updates like `eax = eax + N`; treating them as offset chains corrupts accumulation when other Sconds reference the same reg before the update.
    let mut reg_derivation: HashMap<RTLReg, (RTLReg, i64)> = HashMap::new();
    for (_, s) in stmts {
        if let CsharpminorStmt::Sset(dst, expr) = s {
            match expr {
                CsharpminorExpr::Ebinop(op, lhs, rhs) => {
                    if let (CsharpminorExpr::Evar(src), CsharpminorExpr::Econst(cst)) = (lhs.as_ref(), rhs.as_ref()) {
                        if *src == *dst {
                            continue;
                        }
                        if let Some(off) = switch_disc_offset(op, cst) {
                            reg_derivation.insert(*dst, (*src, off));
                        }
                    }
                }
                _ => {}
            }
        }
    }

    // Resolve register to root discriminant + cumulative offset
    let resolve_reg = |reg: RTLReg| -> (RTLReg, i64) {
        let mut current = reg;
        let mut total_offset: i64 = 0;
        let mut visited = HashSet::new();
        while let Some(&(src, off)) = reg_derivation.get(&current) {
            if !visited.insert(current) { break; }
            total_offset += off;
            current = src;
        }
        (current, total_offset)
    };

    // Walk comparison tree, collecting (case_value, target, member_node) per branch. `local_disc_offset` tracks in-place updates to disc_reg seen so far along this DFS path (e.g., `eax = eax + (-2); cmp $1, eax` means the cmp tests `disc_orig + (-2)` against 1). `path_lo`/`path_hi` carry the inclusive interval (in ROOT discriminant space) that the discriminant is known to lie in on this DFS path, accumulated from signed range guards; a guard branch whose interval becomes finite and small is a case cluster (gcc's signed binary-search `jg`/`jle` partition shape).
    fn walk_tree(
        node: Node,
        disc_reg: RTLReg,
        local_disc_offset: i64,
        path_lo: Option<i64>,
        path_hi: Option<i64>,
        stmt_map: &HashMap<Node, &CsharpminorStmt>,
        seq_next_map: &HashMap<Node, Node>,
        reg_derivation: &HashMap<RTLReg, (RTLReg, i64)>,
        resolve_reg: &dyn Fn(RTLReg) -> (RTLReg, i64),
        cond_break_nodes: &HashSet<Node>,
        cases: &mut Vec<(i64, Node, Node)>,
        visited: &mut HashSet<Node>,
    ) {
        if !visited.insert(node) { return; }

        // Loop-exit compares are not dispatch members (same exclusion the Ascent chain rules apply via !cond_is_break, and the same reason roots skip them): crossing one walks out of the dispatch region, e.g. around a loop back edge into the next iteration's tests.
        if cond_break_nodes.contains(&node) { return; }

        // Track in-place self-updates of the discriminant for subsequent compares on this path: `Sset(disc_reg, disc_reg + N)` updates local_disc_offset by N.
        if let Some(s) = stmt_map.get(&node) {
            if stmt_def_reg(s) == Some(disc_reg) {
                if let CsharpminorStmt::Sset(_, expr) = s {
                    if let CsharpminorExpr::Ebinop(op, lhs, rhs) = expr {
                        if let (CsharpminorExpr::Evar(src), CsharpminorExpr::Econst(cst)) =
                            (lhs.as_ref(), rhs.as_ref())
                        {
                            if *src == disc_reg {
                                if let Some(off) = switch_disc_offset(op, cst) {
                                    if let Some(&next) = seq_next_map.get(&node) {
                                        // The path interval is in root space (compare offsets renormalize), so it passes through unchanged.
                                        walk_tree(next, disc_reg, local_disc_offset + off, path_lo, path_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
                                    }
                                    return;
                                }
                            }
                        }
                    }
                }
                // Any other redefinition of the discriminant (call/builtin result, or an Sset whose RHS is not the modeled in-place +/-const) KILLS the dispatch value: compares beyond this point test an unrelated value, and continuing with the stale offset fabricates case rows (observed: walking through a loop header's `c = f()` call carried a -3 rebase onto the loop-exit compares, minting phantom `case 5`).
                return;
            }
        }

        // Match Scond with arg either Evar(reg) or Ebinop(Oaddl/Oadd, Evar(reg), Econst(offset)); the inline-temp pattern GCC/clang emits for `(disc - K) <op> imm`.
        let cmp = match stmt_map.get(&node) {
            Some(CsharpminorStmt::Scond(cond, args, ifso, ifnot)) if args.len() == 1 => {
                let (reg_opt, inline_off) = match &args[0] {
                    CsharpminorExpr::Evar(reg) => (Some(*reg), 0i64),
                    CsharpminorExpr::Ebinop(op, lhs, rhs) => {
                        if let (CsharpminorExpr::Evar(reg), CsharpminorExpr::Econst(cst))
                            = (lhs.as_ref(), rhs.as_ref())
                        {
                            match switch_disc_offset(op, cst) {
                                Some(o) => (Some(*reg), o),
                                None => (None, 0),
                            }
                        } else {
                            (None, 0)
                        }
                    }
                    _ => (None, 0),
                };
                reg_opt.map(|reg| (reg, inline_off, *cond, *ifso, *ifnot))
            }
            _ => None,
        };

        let (reg, inline_off, cond, ifso, ifnot) = match cmp {
            Some(c) => c,
            None => {
                // Only pure control (jump/nop/discriminant-rebase) may be walked through: any state change kills row attribution because the head's dispatch jumps over it, binding deeper rows to skipped-state targets (observed: gcc -O1 cmove cascades between compares caused `case 3` to execute case 29's body). Discriminant-rebase Ssets (clang's lea form) are exempted as dispatch plumbing, not body state.
                match stmt_map.get(&node) {
                    Some(CsharpminorStmt::Sjump(t)) => {
                        if *t != node {
                            walk_tree(*t, disc_reg, local_disc_offset, path_lo, path_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
                        }
                    }
                    Some(CsharpminorStmt::Snop) => {
                        if let Some(&next) = seq_next_map.get(&node) {
                            walk_tree(next, disc_reg, local_disc_offset, path_lo, path_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
                        }
                    }
                    Some(CsharpminorStmt::Sset(_, expr)) => {
                        let rebase_copy = match expr {
                            CsharpminorExpr::Ebinop(op, lhs, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
                                (CsharpminorExpr::Evar(src), CsharpminorExpr::Econst(cst)) => {
                                    switch_disc_offset(op, cst).is_some()
                                        && resolve_reg(*src).0 == disc_reg
                                }
                                _ => false,
                            },
                            _ => false,
                        };
                        if rebase_copy {
                            if let Some(&next) = seq_next_map.get(&node) {
                                walk_tree(next, disc_reg, local_disc_offset, path_lo, path_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
                            }
                        }
                    }
                    _ => {}
                }
                return;
            }
        };

        let (root_reg, derive_off) = resolve_reg(reg);
        // Apply the local offset only if the comparison's register IS the discriminant (an in-place update to disc_reg shifts the effective compared value).
        let path_off = if root_reg == disc_reg { local_disc_offset } else { 0 };
        let offset = derive_off + inline_off + path_off;
        let is_disc = root_reg == disc_reg;

        match cond {
            // Ceq: true branch = case body, false continues
            Condition::Ccompimm(Comparison::Ceq, val)
            | Condition::Ccompuimm(Comparison::Ceq, val)
            | Condition::Ccomplimm(Comparison::Ceq, val)
            | Condition::Ccompluimm(Comparison::Ceq, val) if is_disc => {
                let case_val = val - offset;
                cases.push((case_val, ifso, node));
                walk_tree(ifnot, disc_reg, local_disc_offset, path_lo, path_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
            }

            // Cne: false branch = case body (inverted), true continues
            Condition::Ccompimm(Comparison::Cne, val)
            | Condition::Ccompuimm(Comparison::Cne, val)
            | Condition::Ccomplimm(Comparison::Cne, val)
            | Condition::Ccompluimm(Comparison::Cne, val) if is_disc => {
                let case_val = val - offset;
                cases.push((case_val, ifnot, node));
                walk_tree(ifso, disc_reg, local_disc_offset, path_lo, path_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
            }

            // Cmaskzero(M) on disc means `(disc & M) == 0`. When the AND was the prior instruction that bounded disc to [0..M] (mask is 2^n - 1), this is exactly `disc == 0`, i.e., case 0 of `switch (disc) { ... }`. Treat it like Ceq(0). clang -O1 fuses `and $M, %disc; je case0` into a single Cmaskzero(M).
            Condition::Cmaskzero(mask) if is_disc && mask > 0 && (mask & (mask + 1)) == 0 => {
                let case_val = -offset;
                cases.push((case_val, ifso, node));
                walk_tree(ifnot, disc_reg, local_disc_offset, path_lo, path_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
            }

            // Cmasknotzero(M) on disc means `(disc & M) != 0`. With M = 2^n - 1, this is the negation of case 0. Treat like Cne(0).
            Condition::Cmasknotzero(mask) if is_disc && mask > 0 && (mask & (mask + 1)) == 0 => {
                let case_val = -offset;
                cases.push((case_val, ifnot, node));
                walk_tree(ifso, disc_reg, local_disc_offset, path_lo, path_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
            }

            // Unsigned `disc < bound` with `disc + offset` (offset <= 0) enumerates range [-offset, bound-offset-1] for the true branch; bounded to keep Sswitch table small. The true branch additionally implies the signed interval [-offset, bound-offset-1] (an unsigned upper bound on a small non-negative range), which narrows the path interval for nested signed guards.
            Condition::Ccompuimm(Comparison::Clt, bound)
            | Condition::Ccompluimm(Comparison::Clt, bound) if is_disc => {
                let disc_lower = -offset;
                let disc_upper = bound - offset - 1;
                if disc_lower >= 0 && disc_upper >= disc_lower && (disc_upper - disc_lower) < 32 {
                    for v in disc_lower..=disc_upper {
                        cases.push((v, ifso, node));
                    }
                }
                let (t_lo, t_hi) = if disc_lower >= 0 && disc_upper >= disc_lower {
                    (clamp_lo(path_lo, disc_lower), clamp_hi(path_hi, disc_upper))
                } else { (path_lo, path_hi) };
                walk_tree(ifso, disc_reg, local_disc_offset, t_lo, t_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
                walk_tree(ifnot, disc_reg, local_disc_offset, path_lo, path_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
            }

            // Unsigned `disc <= bound`: similar but inclusive upper bound.
            Condition::Ccompuimm(Comparison::Cle, bound)
            | Condition::Ccompluimm(Comparison::Cle, bound) if is_disc => {
                let disc_lower = -offset;
                let disc_upper = bound - offset;
                if disc_lower >= 0 && disc_upper >= disc_lower && (disc_upper - disc_lower) < 32 {
                    for v in disc_lower..=disc_upper {
                        cases.push((v, ifso, node));
                    }
                }
                let (t_lo, t_hi) = if disc_lower >= 0 && disc_upper >= disc_lower {
                    (clamp_lo(path_lo, disc_lower), clamp_hi(path_hi, disc_upper))
                } else { (path_lo, path_hi) };
                walk_tree(ifso, disc_reg, local_disc_offset, t_lo, t_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
                walk_tree(ifnot, disc_reg, local_disc_offset, path_lo, path_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
            }

            // Unsigned (disc + neg_off) > bound with neg_off < 0: false branch represents disc in [-off, -off + bound]. Used by gcc -O1 to test a contiguous case cluster like `case 2: case 3:` via `sub $2,%eax; cmp $1,%eax; ja default`.
            Condition::Ccompuimm(Comparison::Cgt, bound)
            | Condition::Ccompluimm(Comparison::Cgt, bound) if is_disc && offset < 0 => {
                let disc_lower = -offset;
                let disc_upper = bound - offset;
                if disc_lower >= 0 && disc_upper >= disc_lower && (disc_upper - disc_lower) < 32 {
                    for v in disc_lower..=disc_upper {
                        cases.push((v, ifnot, node));
                    }
                }
                let (f_lo, f_hi) = if disc_lower >= 0 && disc_upper >= disc_lower {
                    (clamp_lo(path_lo, disc_lower), clamp_hi(path_hi, disc_upper))
                } else { (path_lo, path_hi) };
                walk_tree(ifso, disc_reg, local_disc_offset, path_lo, path_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
                walk_tree(ifnot, disc_reg, local_disc_offset, f_lo, f_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
            }

            // Unsigned (disc + neg_off) >= bound: false branch represents disc in [-off, -off + bound - 1].
            Condition::Ccompuimm(Comparison::Cge, bound)
            | Condition::Ccompluimm(Comparison::Cge, bound) if is_disc && offset < 0 => {
                let disc_lower = -offset;
                let disc_upper = bound - offset - 1;
                if disc_lower >= 0 && disc_upper >= disc_lower && (disc_upper - disc_lower) < 32 {
                    for v in disc_lower..=disc_upper {
                        cases.push((v, ifnot, node));
                    }
                }
                let (f_lo, f_hi) = if disc_lower >= 0 && disc_upper >= disc_lower {
                    (clamp_lo(path_lo, disc_lower), clamp_hi(path_hi, disc_upper))
                } else { (path_lo, path_hi) };
                walk_tree(ifso, disc_reg, local_disc_offset, path_lo, path_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
                walk_tree(ifnot, disc_reg, local_disc_offset, f_lo, f_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
            }

            // SIGNED range guards on the discriminant (gcc/clang binary-search partition tests: `jg`/`jle`/`jl`/`jge`). Each branch narrows the path interval; a branch whose interval becomes finite and small is a contiguous case CLUSTER (e.g. `cmp $4; jg ...` then `cmp $2; jg BODY` isolates {3,4}). When that branch lands on a BODY (not further dispatch on the same discriminant), enumerate its values as cases of this guard, making the guard a chain member: the range-dispatch joins the recovered switch instead of surviving as a raw if re-testing the discriminant. Dedup-order soundness: any `!= v` path constraints not representable in the interval correspond to Ceq/Cne cases pushed EARLIER on this DFS path, and the post-walk first-occurrence dedup discards the interval's stale binding of v.
            Condition::Ccompimm(scmp, val)
            | Condition::Ccomplimm(scmp, val)
                if is_disc && matches!(scmp, Comparison::Cgt | Comparison::Cge | Comparison::Clt | Comparison::Cle) => {
                // Bound in root-disc space; the compare tests (disc_root + offset) OP val, i.e. disc_root OP (val - offset). On overflow (b = None) the branch intervals stay UNNARROWED and must not enumerate: with a degenerate already-finite path interval, enumerating both branches would bind the same values to two targets.
                let b = val.checked_sub(offset);
                let (t_lo, t_hi, f_lo, f_hi) = match (scmp, b) {
                    (Comparison::Cgt, Some(b)) => (
                        b.checked_add(1).map_or(path_lo, |x| clamp_lo(path_lo, x)), path_hi,
                        path_lo, clamp_hi(path_hi, b),
                    ),
                    (Comparison::Cge, Some(b)) => (
                        clamp_lo(path_lo, b), path_hi,
                        path_lo, b.checked_sub(1).map_or(path_hi, |x| clamp_hi(path_hi, x)),
                    ),
                    (Comparison::Clt, Some(b)) => (
                        path_lo, b.checked_sub(1).map_or(path_hi, |x| clamp_hi(path_hi, x)),
                        clamp_lo(path_lo, b), path_hi,
                    ),
                    (Comparison::Cle, Some(b)) => (
                        path_lo, clamp_hi(path_hi, b),
                        b.checked_add(1).map_or(path_lo, |x| clamp_lo(path_lo, x)), path_hi,
                    ),
                    _ => (path_lo, path_hi, path_lo, path_hi),
                };
                if b.is_some() {
                    if let Some((l, h)) = enumerable_range(t_lo, t_hi) {
                        if !range_target_is_interior(ifso, disc_reg, stmt_map, seq_next_map, resolve_reg, cond_break_nodes) {
                            for v in l..=h {
                                cases.push((v, ifso, node));
                            }
                        }
                    }
                    if let Some((l, h)) = enumerable_range(f_lo, f_hi) {
                        if !range_target_is_interior(ifnot, disc_reg, stmt_map, seq_next_map, resolve_reg, cond_break_nodes) {
                            for v in l..=h {
                                cases.push((v, ifnot, node));
                            }
                        }
                    }
                }
                walk_tree(ifso, disc_reg, local_disc_offset, t_lo, t_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
                walk_tree(ifnot, disc_reg, local_disc_offset, f_lo, f_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
            }

            // Other range guards on the discriminant (unsigned Cgt/Cge with offset >= 0): partition the disc space without binding case values; cases come only from Ceq/Cne leaves below.
            Condition::Ccompuimm(Comparison::Cgt, _)
            | Condition::Ccompluimm(Comparison::Cgt, _)
            | Condition::Ccompuimm(Comparison::Cge, _)
            | Condition::Ccompluimm(Comparison::Cge, _) if is_disc => {
                walk_tree(ifso, disc_reg, local_disc_offset, path_lo, path_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
                walk_tree(ifnot, disc_reg, local_disc_offset, path_lo, path_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
            }

            // Non-discriminant or mask test: explore both branches
            _ => {
                walk_tree(ifso, disc_reg, local_disc_offset, path_lo, path_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
                walk_tree(ifnot, disc_reg, local_disc_offset, path_lo, path_hi, stmt_map, seq_next_map, reg_derivation, resolve_reg, cond_break_nodes, cases, visited);
            }
        }
    }

    // Find switch roots (Ceq/Cne/range-guard on a register, possibly via offset binop) and walk to enumerate cases; out-of-range branches reach a Ceq/Cne leaf or fall through to default.
    let mut results: Vec<(Node, u64, Vec<(i64, Node, Node)>)> = Vec::new();
    let mut used_heads: HashSet<Node> = HashSet::new();

    for (node, s) in stmts {
        // Loop-exit Sconds (e.g., `if (c == -1) break;`) syntactically match the discriminant pattern but semantically aren't switch cases. Treating them as roots replays the chain that the Ascent rules already recovered farther down, producing the back-to-back duplicate switches observed in coreutils mains.
        if cond_break_nodes.contains(node) { continue; }
        if let CsharpminorStmt::Scond(cond, args, _, _) = s {
            if args.len() != 1 { continue; }
            // Extract reg (possibly through Oaddl/Osubl with constant inline offset)
            let reg_opt: Option<RTLReg> = match &args[0] {
                CsharpminorExpr::Evar(reg) => Some(*reg),
                CsharpminorExpr::Ebinop(_, lhs, rhs) => {
                    if let (CsharpminorExpr::Evar(reg), CsharpminorExpr::Econst(_))
                        = (lhs.as_ref(), rhs.as_ref())
                    {
                        Some(*reg)
                    } else { None }
                }
                _ => None,
            };
            if let Some(reg) = reg_opt {
                let is_disc_compare = matches!(cond,
                    Condition::Ccompimm(_, _)
                    | Condition::Ccompuimm(_, _)
                    | Condition::Ccomplimm(_, _)
                    | Condition::Ccompluimm(_, _)
                    | Condition::Cmaskzero(_)
                    | Condition::Cmasknotzero(_)
                );
                if !is_disc_compare { continue; }

                let (root_reg, _) = resolve_reg(reg);
                if used_heads.contains(node) { continue; }

                let mut cases: Vec<(i64, Node, Node)> = Vec::new();
                let mut visited = HashSet::new();
                walk_tree(
                    *node, root_reg, 0i64,
                    None, None,
                    &stmt_map, &seq_next_map, &reg_derivation,
                    &resolve_reg, cond_break_nodes,
                    &mut cases, &mut visited,
                );

                // Deduplicate cases by value (keep first occurrence)
                let mut seen_vals: HashSet<i64> = HashSet::new();
                cases.retain(|(val, _, _)| seen_vals.insert(*val));

                if cases.len() >= 3 {
                    used_heads.insert(*node);
                    results.push((*node, root_reg as u64, cases));
                }
            }
        }
    }

    results
}

// Walk the execution-order chain from `start` until a stmt_nodes member is reached. Splices synthetic chain members (A|1<<62, A|1<<63) in at their real-address position; without this they become unreachable islands and statements they carry (e.g. a fused `global = CONST`) are torn out of their branch and re-emitted at the function bottom.
fn walk_next_to_stmt(
    start: Node,
    next_map: &HashMap<Node, Node>,
    stmt_nodes: &HashSet<Node>,
) -> Option<Node> {
    const S1: u64 = crate::util::SYNTH_NODE_BIT; // executes 1st after its real address
    const S2: u64 = 1u64 << 63; // executes 2nd (two-step chains, e.g. arith_store_*)
    let base = start & !(S1 | S2);
    // Remaining members of start's own synthetic chain execute before next(base).
    if start & (S1 | S2) == 0 && stmt_nodes.contains(&(base | S1)) {
        return Some(base | S1);
    }
    if start & S2 == 0 && stmt_nodes.contains(&(base | S2)) {
        return Some(base | S2);
    }
    let mut cur = base;
    let mut visited: HashSet<Node> = HashSet::new();
    while visited.insert(cur) {
        let nxt = *next_map.get(&cur)?;
        if stmt_nodes.contains(&nxt) {
            return Some(nxt);
        }
        // A statement-less successor may still head a synthetic chain (e.g. its Sset folded away, leaving the fused store at nxt | 1<<62).
        if stmt_nodes.contains(&(nxt | S1)) {
            return Some(nxt | S1);
        }
        if stmt_nodes.contains(&(nxt | S2)) {
            return Some(nxt | S2);
        }
        cur = nxt;
    }
    None
}

fn compute_sequential_edges(
    stmts: &[(Node, CsharpminorStmt)],
    next_map: &HashMap<Node, Node>,
) -> Vec<(Node, Node)> {
    let stmt_nodes: HashSet<Node> = stmts.iter().map(|(n, _)| *n).collect();
    stmts
        .iter()
        .filter_map(|(n, _)| {
            walk_next_to_stmt(*n, next_map, &stmt_nodes).map(|nxt| (*n, nxt))
        })
        .collect()
}

fn lift_setcc_arith_to_ite(working: &mut HashMap<Node, CsharpminorStmt>, db: &DecompileDB) {
    use crate::x86::types::CminorBinop;
    use std::collections::HashMap as Map;
    let next_map: Map<Node, Node> = db
        .rel_iter::<(Node, Node)>("next")
        .map(|&(a, b)| (a, b))
        .collect();

    fn walk_to_working(start: Node, next_map: &Map<Node, Node>, working: &HashMap<Node, CsharpminorStmt>) -> Option<Node> {
        let mut cur = start;
        let mut seen = HashSet::new();
        while seen.insert(cur) {
            match next_map.get(&cur) {
                Some(&n) => {
                    if working.contains_key(&n) {
                        return Some(n);
                    }
                    cur = n;
                }
                None => return None,
            }
        }
        None
    }

    fn cminor_cmp_to_condition(op: &CminorBinop, rhs_const: i64) -> Option<Condition> {
        match op {
            CminorBinop::Ocmp(c) => Some(Condition::Ccompimm(*c, rhs_const)),
            CminorBinop::Ocmpu(c) => Some(Condition::Ccompuimm(*c, rhs_const)),
            CminorBinop::Ocmpl(c) => Some(Condition::Ccomplimm(*c, rhs_const)),
            CminorBinop::Ocmplu(c) => Some(Condition::Ccompluimm(*c, rhs_const)),
            _ => None,
        }
    }

    let snapshot: Vec<(Node, CsharpminorStmt)> = working.iter().map(|(n, s)| (*n, s.clone())).collect();
    let mut rewrites: Vec<(Node, CsharpminorStmt, Node)> = Vec::new();

    for (n1, s1) in &snapshot {
        let (reg1, cmp_op, arg_reg, rhs_const) = match s1 {
            CsharpminorStmt::Sset(r, CsharpminorExpr::Ebinop(op, lhs, rhs))
                if matches!(op,
                    CminorBinop::Ocmp(_) | CminorBinop::Ocmpu(_)
                    | CminorBinop::Ocmpl(_) | CminorBinop::Ocmplu(_)) =>
            {
                match (lhs.as_ref(), rhs.as_ref()) {
                    (CsharpminorExpr::Evar(arg), CsharpminorExpr::Econst(Constant::Ointconst(c))) => {
                        (*r, op.clone(), *arg, *c as i64)
                    }
                    (CsharpminorExpr::Evar(arg), CsharpminorExpr::Econst(Constant::Olongconst(c))) => {
                        (*r, op.clone(), *arg, *c)
                    }
                    _ => continue,
                }
            }
            _ => continue,
        };

        let cond = match cminor_cmp_to_condition(&cmp_op, rhs_const) {
            Some(c) => c,
            None => continue,
        };

        let n2 = match walk_to_working(*n1, &next_map, working) {
            Some(n) => n,
            None => continue,
        };
        let s2 = match working.get(&n2) {
            Some(s) => s.clone(),
            None => continue,
        };

        let (add_const, is_long) = match &s2 {
            CsharpminorStmt::Sset(r, CsharpminorExpr::Ebinop(op, lhs, rhs)) if *r == reg1 => {
                let is_long = matches!(op, CminorBinop::Oaddl);
                if !is_long && !matches!(op, CminorBinop::Oadd) {
                    continue;
                }
                match (lhs.as_ref(), rhs.as_ref()) {
                    (CsharpminorExpr::Evar(v), CsharpminorExpr::Econst(Constant::Ointconst(c))) if *v == reg1 => {
                        (*c as i64, is_long)
                    }
                    (CsharpminorExpr::Evar(v), CsharpminorExpr::Econst(Constant::Olongconst(c))) if *v == reg1 => {
                        (*c, is_long)
                    }
                    _ => continue,
                }
            }
            _ => continue,
        };

        let true_const = if is_long { Constant::Olongconst(add_const + 1) } else { Constant::Ointconst(add_const + 1) };
        let false_const = if is_long { Constant::Olongconst(add_const) } else { Constant::Ointconst(add_const) };

        let cond_args = vec![CsharpminorExpr::Evar(arg_reg)];
        let then_stmt = Box::new(CsharpminorStmt::Sset(reg1, CsharpminorExpr::Econst(true_const)));
        let else_stmt = Box::new(CsharpminorStmt::Sset(reg1, CsharpminorExpr::Econst(false_const)));

        let ite = CsharpminorStmt::Sifthenelse(cond, cond_args, then_stmt, else_stmt);
        rewrites.push((*n1, ite, n2));
    }

    for (n1, ite, n2) in rewrites {
        working.insert(n1, ite);
        working.insert(n2, CsharpminorStmt::Snop);
    }
}

fn inline_constants(working: &mut HashMap<Node, CsharpminorStmt>, db: &DecompileDB) {
    let mut def_count: HashMap<RTLReg, usize> = HashMap::new();
    for (_, stmt) in working.iter() {
        match stmt {
            CsharpminorStmt::Sset(reg, _) => {
                *def_count.entry(*reg).or_insert(0) += 1;
            }
            CsharpminorStmt::Scall(Some(reg), _, _, _) => {
                *def_count.entry(*reg).or_insert(0) += 1;
            }
            CsharpminorStmt::Sbuiltin(Some(reg), _, _, _) => {
                *def_count.entry(*reg).or_insert(0) += 1;
            }
            _ => {}
        }
    }

    let param_regs: HashSet<RTLReg> = db
        .rel_iter::<(Address, RTLReg)>("emit_function_param_candidate")
        .map(|&(_, r)| r)
        .collect();
    for &reg in &param_regs {
        *def_count.entry(reg).or_insert(0) += 1;
    }

    let mut const_map: HashMap<RTLReg, Constant> = HashMap::new();
    let mut multi_def: HashSet<RTLReg> = HashSet::new();
    // Sort so first-seen-wins-unless-conflict is order-invariant.
    let mut sdc_tuples: Vec<(RTLReg, Constant)> = db
        .rel_iter::<(RTLReg, Constant)>("single_def_const")
        .cloned()
        .collect();
    sdc_tuples.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| format!("{:?}", a.1).cmp(&format!("{:?}", b.1))));
    for (reg, cst) in sdc_tuples {
        if multi_def.contains(&reg) {
            continue;
        }
        if def_count.get(&reg).copied().unwrap_or(0) > 1 {
            multi_def.insert(reg);
            continue;
        }
        if let Some(existing) = const_map.get(&reg) {
            if *existing != cst {
                const_map.remove(&reg);
                multi_def.insert(reg);
            }
        } else {
            const_map.insert(reg, cst);
        }
    }
    if const_map.is_empty() {
        return;
    }

    let const_set_nodes: HashSet<Node> = working.iter().filter_map(|(node, stmt)| {
        if let CsharpminorStmt::Sset(reg, CsharpminorExpr::Econst(cst)) = stmt {
            if const_map.get(reg) == Some(cst) { Some(*node) } else { None }
        } else {
            None
        }
    }).collect();

    let nodes: Vec<Node> = working.keys().copied().collect();
    for node in nodes {
        let stmt = working.get(&node).unwrap().clone();
        if const_set_nodes.contains(&node) {
            if let CsharpminorStmt::Sset(reg, CsharpminorExpr::Econst(cst)) = &stmt {
                if const_map.get(reg) == Some(cst) {
                    working.insert(node, CsharpminorStmt::Snop);
                    continue;
                }
            }
        }
        let new_stmt = subst_consts_in_stmt(&stmt, &const_map);
        if new_stmt != stmt {
            working.insert(node, new_stmt);
        }
    }
}

fn subst_consts_in_expr(
    expr: &CsharpminorExpr,
    consts: &HashMap<RTLReg, Constant>,
) -> CsharpminorExpr {
    match expr {
        CsharpminorExpr::Evar(reg) => {
            if let Some(cst) = consts.get(reg) {
                CsharpminorExpr::Econst(cst.clone())
            } else {
                expr.clone()
            }
        }
        CsharpminorExpr::Eunop(op, inner) => {
            CsharpminorExpr::Eunop(op.clone(), Box::new(subst_consts_in_expr(inner, consts)))
        }
        CsharpminorExpr::Ebinop(op, lhs, rhs) => {
            CsharpminorExpr::Ebinop(
                op.clone(),
                Box::new(subst_consts_in_expr(lhs, consts)),
                Box::new(subst_consts_in_expr(rhs, consts)),
            )
        }
        CsharpminorExpr::Eload(chunk, addr) => {
            CsharpminorExpr::Eload(*chunk, Box::new(subst_consts_in_expr(addr, consts)))
        }
        CsharpminorExpr::Econdition(cond, t, f) => {
            CsharpminorExpr::Econdition(
                Box::new(subst_consts_in_expr(cond, consts)),
                Box::new(subst_consts_in_expr(t, consts)),
                Box::new(subst_consts_in_expr(f, consts)),
            )
        }
        _ => expr.clone(),
    }
}

fn subst_consts_in_stmt(
    stmt: &CsharpminorStmt,
    consts: &HashMap<RTLReg, Constant>,
) -> CsharpminorStmt {
    match stmt {
        CsharpminorStmt::Sset(reg, expr) => {
            CsharpminorStmt::Sset(*reg, subst_consts_in_expr(expr, consts))
        }
        CsharpminorStmt::Sstore(chunk, addr, val) => {
            CsharpminorStmt::Sstore(
                *chunk,
                subst_consts_in_expr(addr, consts),
                subst_consts_in_expr(val, consts),
            )
        }
        CsharpminorStmt::Scall(dst, sig, callee, args) => {
            let new_callee = match callee {
                either::Either::Left(expr) => {
                    either::Either::Left(subst_consts_in_expr(expr, consts))
                }
                r => r.clone(),
            };
            let new_args: Vec<_> = args.iter()
                .map(|a| subst_consts_in_expr(a, consts))
                .collect();
            CsharpminorStmt::Scall(*dst, sig.clone(), new_callee, new_args)
        }
        CsharpminorStmt::Stailcall(sig, callee, args) => {
            let new_callee = match callee {
                either::Either::Left(expr) => {
                    either::Either::Left(subst_consts_in_expr(expr, consts))
                }
                r => r.clone(),
            };
            let new_args: Vec<_> = args.iter()
                .map(|a| subst_consts_in_expr(a, consts))
                .collect();
            CsharpminorStmt::Stailcall(sig.clone(), new_callee, new_args)
        }
        CsharpminorStmt::Scond(cond, args, ifso, ifnot) => {
            let new_args: Vec<_> = args.iter()
                .map(|a| subst_consts_in_expr(a, consts))
                .collect();
            CsharpminorStmt::Scond(cond.clone(), new_args, *ifso, *ifnot)
        }
        CsharpminorStmt::Sjumptable(expr, targets) => {
            CsharpminorStmt::Sjumptable(
                subst_consts_in_expr(expr, consts),
                targets.clone(),
            )
        }
        CsharpminorStmt::Sreturn(expr) => {
            CsharpminorStmt::Sreturn(subst_consts_in_expr(expr, consts))
        }
        CsharpminorStmt::Sseq(stmts) => {
            let new_stmts: Vec<_> = stmts.iter()
                .map(|s| subst_consts_in_stmt(s, consts))
                .collect();
            CsharpminorStmt::Sseq(new_stmts)
        }
        CsharpminorStmt::Sbuiltin(dst, name, args, res) => {
            let new_args: Vec<_> = args.iter()
                .map(|a| subst_consts_in_builtin_arg(a, consts))
                .collect();
            let new_res = subst_consts_in_builtin_arg(res, consts);
            CsharpminorStmt::Sbuiltin(*dst, name.clone(), new_args, new_res)
        }
        _ => stmt.clone(),
    }
}

fn subst_consts_in_builtin_arg(
    arg: &BuiltinArg<CsharpminorExpr>,
    consts: &HashMap<RTLReg, Constant>,
) -> BuiltinArg<CsharpminorExpr> {
    match arg {
        BuiltinArg::BA(expr) => {
            BuiltinArg::BA(subst_consts_in_expr(expr, consts))
        }
        BuiltinArg::BASplitLong(hi, lo) => {
            BuiltinArg::BASplitLong(
                Box::new(subst_consts_in_builtin_arg(hi, consts)),
                Box::new(subst_consts_in_builtin_arg(lo, consts)),
            )
        }
        BuiltinArg::BAAddPtr(base, ofs) => {
            BuiltinArg::BAAddPtr(
                Box::new(subst_consts_in_builtin_arg(base, consts)),
                Box::new(subst_consts_in_builtin_arg(ofs, consts)),
            )
        }
        _ => arg.clone(),
    }
}

// Block-local copy propagation; analysis in CopyPropagationProgram, fixpoint fold in Rust.
fn propagate_copies(working: &mut HashMap<Node, CsharpminorStmt>, db: &mut DecompileDB) {
    use crate::x86::types::XType;

    let code_in_block: HashMap<Node, Node> = db
        .rel_iter::<(Node, Node)>("code_in_block")
        .map(|&(addr, blk)| (addr, blk))
        .collect();

    let mut prog = CopyPropagationProgram::default();
    for (node, stmt) in working.iter() {
        prog.stmt.push((*node, stmt.clone()));
    }
    for &node in working.keys() {
        // Synthetic nodes (high bit 62 set) carry no code_in_block entry from disassembly; map them onto the block of their base address so copy_killed_between can see redefinitions emitted at synth addresses (e.g. arith_load/store synth ops that redefine the dst).
        let lookup = if let Some(&blk) = code_in_block.get(&node) {
            Some(blk)
        } else {
            let base = node & !(1u64 << 62);
            code_in_block.get(&base).copied()
        };
        if let Some(blk) = lookup {
            prog.in_block.push((node, blk));
        }
    }
    // VR-2: cminor_succ covers synthetic bit-62 nodes via rtl_succ bridge rules, making their kills visible to the cross-block available-copies lattice.
    for &(a, b) in db.rel_iter::<(Node, Node)>("cminor_succ") {
        prog.edge.push((a, b));
    }
    for &(_, entry) in db.rel_iter::<(Address, Node)>("func_entry_node") {
        prog.entry.push((entry,));
    }

    prog.run();

    // Gather per-node applicable substitutions: Vec<(dst, src)>.
    let mut substs_by_node: HashMap<Node, Vec<(RTLReg, RTLReg)>> = HashMap::new();
    for (u, dst, src) in &prog.applicable_subst {
        substs_by_node.entry(*u).or_default().push((*dst, *src));
    }

    // Fold to fixpoint per node; sort pairs first for determinism.
    let mut replacements: HashMap<Node, CsharpminorStmt> = HashMap::new();
    for (node, pairs) in &mut substs_by_node {
        pairs.sort();
        pairs.dedup();
        let original = match working.get(node) {
            Some(s) => s.clone(),
            None => continue,
        };
        let mut current = original.clone();
        loop {
            let mut changed = false;
            for &(dst, src) in pairs.iter() {
                let next = subst_var_in_stmt(&current, dst, src);
                if next != current {
                    current = next;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        if current != original {
            replacements.insert(*node, current);
        }
    }

    let dead_copies: HashSet<Node> = prog.dead_copy_v2.iter().map(|(n,)| *n).collect();

    if replacements.is_empty() && dead_copies.is_empty() {
        return;
    }

    // For each dead copy, transfer dst's types to src via Ascent's copy_intro.
    let existing_types: Vec<(RTLReg, XType)> = db
        .rel_iter::<(RTLReg, XType)>("emit_var_type_candidate")
        .cloned()
        .collect();
    let intros_by_node: HashMap<Node, (RTLReg, RTLReg)> = prog
        .copy_intro
        .iter()
        .map(|(n, dst, src)| (*n, (*dst, *src)))
        .collect();
    for &copy_node in &dead_copies {
        if let Some(&(dst, src)) = intros_by_node.get(&copy_node) {
            for (reg, xty) in &existing_types {
                if *reg == dst {
                    db.rel_push("emit_var_type_candidate", (src, xty.clone()));
                }
            }
        }
    }

    for node in &dead_copies {
        working.insert(*node, CsharpminorStmt::Snop);
    }
    for (node, replacement) in &replacements {
        working.insert(*node, replacement.clone());
    }
}

// Helpers used by propagate_copies and its Ascent rules.

fn stmt_uses_set(stmt: &CsharpminorStmt) -> HashSet<RTLReg> {
    let mut vars = HashSet::new();
    match stmt {
        CsharpminorStmt::Sset(_, expr) => collect_expr_vars(expr, &mut vars),
        CsharpminorStmt::Sstore(_, addr, val) => {
            collect_expr_vars(addr, &mut vars);
            collect_expr_vars(val, &mut vars);
        }
        CsharpminorStmt::Scall(_, _, callee, args) => {
            if let either::Either::Left(e) = callee { collect_expr_vars(e, &mut vars); }
            for a in args { collect_expr_vars(a, &mut vars); }
        }
        CsharpminorStmt::Stailcall(_, callee, args) => {
            if let either::Either::Left(e) = callee { collect_expr_vars(e, &mut vars); }
            for a in args { collect_expr_vars(a, &mut vars); }
        }
        CsharpminorStmt::Sbuiltin(_, _, args, res) => {
            for a in args { collect_builtin_arg_vars(a, &mut vars); }
            collect_builtin_arg_vars(res, &mut vars);
        }
        CsharpminorStmt::Scond(_, args, _, _) => {
            for a in args { collect_expr_vars(a, &mut vars); }
        }
        CsharpminorStmt::Sjumptable(expr, _) => collect_expr_vars(expr, &mut vars),
        CsharpminorStmt::Sreturn(expr) => collect_expr_vars(expr, &mut vars),
        _ => {}
    }
    vars
}

fn stmt_def_reg(stmt: &CsharpminorStmt) -> Option<RTLReg> {
    match stmt {
        CsharpminorStmt::Sset(reg, _) => Some(*reg),
        CsharpminorStmt::Scall(Some(reg), _, _, _) => Some(*reg),
        CsharpminorStmt::Sbuiltin(Some(reg), _, _, _) => Some(*reg),
        _ => None,
    }
}

fn subst_var_in_expr(
    expr: &CsharpminorExpr, old: RTLReg, new: RTLReg,
) -> CsharpminorExpr {
    match expr {
        CsharpminorExpr::Evar(r) if *r == old => CsharpminorExpr::Evar(new),
        CsharpminorExpr::Eunop(op, inner) =>
            CsharpminorExpr::Eunop(op.clone(), Box::new(subst_var_in_expr(inner, old, new))),
        CsharpminorExpr::Ebinop(op, l, r) =>
            CsharpminorExpr::Ebinop(
                op.clone(),
                Box::new(subst_var_in_expr(l, old, new)),
                Box::new(subst_var_in_expr(r, old, new)),
            ),
        CsharpminorExpr::Eload(chunk, addr) =>
            CsharpminorExpr::Eload(*chunk, Box::new(subst_var_in_expr(addr, old, new))),
        CsharpminorExpr::Econdition(c, t, f) =>
            CsharpminorExpr::Econdition(
                Box::new(subst_var_in_expr(c, old, new)),
                Box::new(subst_var_in_expr(t, old, new)),
                Box::new(subst_var_in_expr(f, old, new)),
            ),
        _ => expr.clone(),
    }
}

fn subst_var_in_ba(
    ba: &BuiltinArg<CsharpminorExpr>, old: RTLReg, new: RTLReg,
) -> BuiltinArg<CsharpminorExpr> {
    match ba {
        BuiltinArg::BA(e) => BuiltinArg::BA(subst_var_in_expr(e, old, new)),
        BuiltinArg::BASplitLong(a, b) =>
            BuiltinArg::BASplitLong(
                Box::new(subst_var_in_ba(a, old, new)),
                Box::new(subst_var_in_ba(b, old, new)),
            ),
        BuiltinArg::BAAddPtr(a, b) =>
            BuiltinArg::BAAddPtr(
                Box::new(subst_var_in_ba(a, old, new)),
                Box::new(subst_var_in_ba(b, old, new)),
            ),
        _ => ba.clone(),
    }
}

fn subst_var_in_stmt(
    stmt: &CsharpminorStmt, old: RTLReg, new: RTLReg,
) -> CsharpminorStmt {
    match stmt {
        CsharpminorStmt::Sset(dst, expr) =>
            CsharpminorStmt::Sset(*dst, subst_var_in_expr(expr, old, new)),
        CsharpminorStmt::Sstore(chunk, addr, val) =>
            CsharpminorStmt::Sstore(
                *chunk,
                subst_var_in_expr(addr, old, new),
                subst_var_in_expr(val, old, new),
            ),
        CsharpminorStmt::Scall(dst, sig, callee, args) => {
            let new_callee = match callee {
                either::Either::Left(e) =>
                    either::Either::Left(subst_var_in_expr(e, old, new)),
                other => other.clone(),
            };
            let new_args: Vec<_> = args.iter()
                .map(|a| subst_var_in_expr(a, old, new)).collect();
            CsharpminorStmt::Scall(dst.clone(), sig.clone(), new_callee, new_args)
        }
        CsharpminorStmt::Stailcall(sig, callee, args) => {
            let new_callee = match callee {
                either::Either::Left(e) =>
                    either::Either::Left(subst_var_in_expr(e, old, new)),
                other => other.clone(),
            };
            let new_args: Vec<_> = args.iter()
                .map(|a| subst_var_in_expr(a, old, new)).collect();
            CsharpminorStmt::Stailcall(sig.clone(), new_callee, new_args)
        }
        CsharpminorStmt::Sbuiltin(dst, name, args, res) => {
            let new_args: Vec<_> = args.iter()
                .map(|a| subst_var_in_ba(a, old, new)).collect();
            let new_res = subst_var_in_ba(res, old, new);
            CsharpminorStmt::Sbuiltin(dst.clone(), name.clone(), new_args, new_res)
        }
        CsharpminorStmt::Scond(cond, args, ifso, ifnot) => {
            let new_args: Vec<_> = args.iter()
                .map(|a| subst_var_in_expr(a, old, new)).collect();
            CsharpminorStmt::Scond(cond.clone(), new_args, *ifso, *ifnot)
        }
        CsharpminorStmt::Sjumptable(expr, targets) =>
            CsharpminorStmt::Sjumptable(subst_var_in_expr(expr, old, new), targets.clone()),
        CsharpminorStmt::Sreturn(expr) =>
            CsharpminorStmt::Sreturn(subst_var_in_expr(expr, old, new)),
        _ => stmt.clone(),
    }
}

// VR-2 helpers: available-copies dataflow over the statement-level CFG.

// Transfer one statement through the avail-copies lattice: kill entries whose dst or src is redefined, then gen the statement's own copy.
fn copy_transfer(
    avail: &Set<(Node, RTLReg, RTLReg)>,
    node: Node,
    stmt: &CsharpminorStmt,
) -> Set<(Node, RTLReg, RTLReg)> {
    let def = stmt_def_reg(stmt);
    let mut out: std::collections::BTreeSet<(Node, RTLReg, RTLReg)> = avail
        .0
        .iter()
        .filter(|(_, dst, src)| def.map_or(true, |d| d != *dst && d != *src))
        .copied()
        .collect();
    if let CsharpminorStmt::Sset(dst, CsharpminorExpr::Evar(src)) = stmt {
        if dst != src {
            out.insert((node, *dst, *src));
        }
    }
    Set(out)
}

// Entries of the avail set that copy into `dst`, as (intro, src) pairs.
fn avail_copies_of(avail: &Set<(Node, RTLReg, RTLReg)>, dst: RTLReg) -> Vec<(Node, RTLReg)> {
    avail
        .0
        .iter()
        .filter(|(_, d, _)| *d == dst)
        .map(|(i, _, s)| (*i, *s))
        .collect()
}

// CopyPropagationProgram: Ascent copy propagation. Outputs applicable_subst, dead_copy_v2, copy_intro.
ascent_par! {
    pub struct CopyPropagationProgram;

    relation stmt(Node, CsharpminorStmt);
    relation in_block(Node, Node);
    // VR-2 inputs: statement-level CFG edges (cminor_succ) and function entry nodes.
    relation edge(Node, Node);
    relation entry(Node);

    // Both in same block AND a strictly precedes b. Synthetic nodes (bit 62 set) execute immediately after their base address, so naive numeric comparison reorders them past all real-address nodes. exec_order_key folds the address into a 2x+1 form so a synth at base X sits between real X and the next real address.
    relation before_in_block(Node, Node);
    before_in_block(*a, *b) <--
        in_block(a, blk),
        in_block(b, blk),
        if exec_order_key(*a) < exec_order_key(*b);

    // Registers defined at a node.
    relation stmt_defines(Node, RTLReg);
    stmt_defines(*n, reg) <--
        stmt(n, s),
        if let Some(reg) = stmt_def_reg(s);

    // Registers used (read) at a node. Computed once per stmt.
    relation stmt_uses(Node, RTLReg);
    stmt_uses(*n, reg) <--
        stmt(n, s),
        let used = stmt_uses_set(s),
        for reg in used;

    // Copy introductions: Sset(dst, Evar(src)) with dst != src.
    relation copy_intro(Node, RTLReg, RTLReg);
    copy_intro(*n, *dst, *src) <--
        stmt(n, ?CsharpminorStmt::Sset(dst, CsharpminorExpr::Evar(src))),
        if dst != src;

    // A kill of the copy between intro and use: some k strictly between intro and u (same block) defines either dst or src.
    relation copy_killed_between(Node, RTLReg, RTLReg, Node);
    copy_killed_between(*intro, *dst, *src, *u) <--
        copy_intro(intro, dst, src),
        before_in_block(intro, k),
        before_in_block(k, u),
        stmt_defines(k, d),
        if d == dst || d == src;

    // The copy introduced at `intro` is live at use-node `u`.
    relation copy_active_at(Node, RTLReg, RTLReg, Node);
    copy_active_at(*u, *dst, *src, *intro) <--
        copy_intro(intro, dst, src),
        before_in_block(intro, u),
        !copy_killed_between(intro, dst, src, u);

    // VR-2: avail_in is a Dual<Set> intersection lattice -- keeps only path-invariant copies. Loop safety falls out of the meet: at a loop header the entry path (no intro yet) intersects back-edge state, so loop-interior copies never appear available at first-iteration reads, and in-loop redefinitions of dst or src drop the entry on the back edge.
    lattice avail_in(Node, Dual<Set<(Node, RTLReg, RTLReg)>>);

    // Function entries start with no available copies.
    avail_in(*e, Dual(Set::default())) <-- entry(e);

    // Propagate along CFG edges through the pred's transfer (kill defs, then gen intro).
    avail_in(*n, Dual(copy_transfer(&pin.0, *p, s))) <--
        edge(p, n),
        avail_in(p, pin),
        stmt(p, s);

    // Pred without a statement in this program's view has unknown effects: kill everything.
    avail_in(*n, Dual(Set::default())) <--
        edge(p, n),
        avail_in(p, _),
        !stmt(p, _);

    // Cross-block coverage feeds the same active/covered/dead pipeline; tuples materialize only at use sites.
    copy_active_at(*u, *dst, src, intro) <--
        stmt_uses(u, dst),
        avail_in(u, av),
        for (intro, src) in avail_copies_of(&av.0, *dst);

    // The copy at `intro` has a use of `dst` it does NOT cover (dst read where the copy is inactive: another block, or before `intro` via a back-edge, the loop-carried read); such uses cannot be rewritten to `src`, so killing/substituting the copy would strip dst's def and collapse the loop-carried value to its pre-loop definition (a frozen counter/accumulator).
    relation copy_use_uncovered(Node);
    copy_use_uncovered(*intro) <--
        copy_intro(intro, dst, src),
        stmt_uses(u, dst),
        !copy_active_at(u, dst, src, intro);

    // Non-transitive on purpose; Rust fold runs the chain while preserving the original-uses anchor.
    relation applicable_subst(Node, RTLReg, RTLReg);
    applicable_subst(*u, *dst, *src) <--
        copy_active_at(u, dst, src, intro),
        stmt_uses(u, dst),
        !copy_use_uncovered(intro);

    // A copy is dead if at least one substitution fires for it AND every use of dst is covered.
    relation dead_copy_v2(Node);
    dead_copy_v2(*intro) <--
        copy_intro(intro, dst, src),
        copy_active_at(u, dst, src, intro),
        stmt_uses(u, dst),
        !copy_use_uncovered(intro);
}

fn eliminate_dead_returns(working: &mut HashMap<Node, CsharpminorStmt>, db: &DecompileDB) {
    let dead_regs: HashSet<RTLReg> = db
        .rel_iter::<(RTLReg,)>("dead_def")
        .map(|&(reg,)| reg)
        .collect();
    if dead_regs.is_empty() {
        return;
    }

    // Cross-check dead_def claims against actual uses in working to avoid dropping live returns.
    let mut used_regs: HashSet<RTLReg> = HashSet::new();
    for stmt in working.values() {
        match stmt {
            CsharpminorStmt::Sset(_, expr) => {
                collect_expr_vars(expr, &mut used_regs);
            }
            CsharpminorStmt::Sstore(_, addr, value) => {
                collect_expr_vars(addr, &mut used_regs);
                collect_expr_vars(value, &mut used_regs);
            }
            CsharpminorStmt::Sreturn(expr) => {
                collect_expr_vars(expr, &mut used_regs);
            }
            CsharpminorStmt::Scall(_, _, callee, args) => {
                if let either::Either::Left(expr) = callee {
                    collect_expr_vars(expr, &mut used_regs);
                }
                for a in args.iter() { collect_expr_vars(a, &mut used_regs); }
            }
            CsharpminorStmt::Stailcall(_, callee, args) => {
                if let either::Either::Left(expr) = callee {
                    collect_expr_vars(expr, &mut used_regs);
                }
                for a in args.iter() { collect_expr_vars(a, &mut used_regs); }
            }
            CsharpminorStmt::Sbuiltin(_, _, args, res) => {
                for a in args.iter() { collect_builtin_arg_vars(a, &mut used_regs); }
                collect_builtin_arg_vars(res, &mut used_regs);
            }
            CsharpminorStmt::Scond(_, args, _, _) => {
                for a in args.iter() { collect_expr_vars(a, &mut used_regs); }
            }
            CsharpminorStmt::Sjumptable(expr, _) => {
                collect_expr_vars(expr, &mut used_regs);
            }
            _ => {}
        }
    }

    // Sort nodes so deterministic even if downstream reads working in insertion order.
    let mut nodes: Vec<Node> = working.keys().copied().collect();
    nodes.sort();
    for node in nodes {
        let stmt = working.get(&node).unwrap().clone();
        if let CsharpminorStmt::Scall(Some(dst), sig, callee, args) = &stmt {
            if dead_regs.contains(dst) && !used_regs.contains(dst) {
                working.insert(node, CsharpminorStmt::Scall(None, sig.clone(), callee.clone(), args.clone()));
            }
        }
    }
}

/// Collect free variable registers referenced inside a BuiltinArg<CsharpminorExpr>.
fn collect_builtin_arg_vars(ba: &BuiltinArg<CsharpminorExpr>, out: &mut HashSet<RTLReg>) {
    match ba {
        BuiltinArg::BA(e) => collect_expr_vars(e, out),
        BuiltinArg::BASplitLong(a, b) | BuiltinArg::BAAddPtr(a, b) => {
            collect_builtin_arg_vars(a, out);
            collect_builtin_arg_vars(b, out);
        }
        _ => {}
    }
}

/// Collect all free variable registers referenced in an expression.
fn collect_expr_vars(expr: &CsharpminorExpr, out: &mut HashSet<RTLReg>) {
    match expr {
        CsharpminorExpr::Evar(r) => { out.insert(*r); }
        CsharpminorExpr::Eunop(_, inner) => collect_expr_vars(inner, out),
        CsharpminorExpr::Ebinop(_, l, r) => { collect_expr_vars(l, out); collect_expr_vars(r, out); }
        CsharpminorExpr::Eload(_, addr) => collect_expr_vars(addr, out),
        CsharpminorExpr::Econdition(c, t, f) => {
            collect_expr_vars(c, out); collect_expr_vars(t, out); collect_expr_vars(f, out);
        }
        _ => {}
    }
}

/// Count occurrences of `Evar(reg)` in an expression.
fn count_var_in_expr(expr: &CsharpminorExpr, reg: RTLReg) -> usize {
    match expr {
        CsharpminorExpr::Evar(r) => if *r == reg { 1 } else { 0 },
        CsharpminorExpr::Eunop(_, inner) => count_var_in_expr(inner, reg),
        CsharpminorExpr::Ebinop(_, l, r) => count_var_in_expr(l, reg) + count_var_in_expr(r, reg),
        CsharpminorExpr::Eload(_, addr) => count_var_in_expr(addr, reg),
        CsharpminorExpr::Econdition(c, t, f) =>
            count_var_in_expr(c, reg) + count_var_in_expr(t, reg) + count_var_in_expr(f, reg),
        _ => 0,
    }
}

fn count_var_in_builtin_arg(ba: &BuiltinArg<CsharpminorExpr>, reg: RTLReg) -> usize {
    match ba {
        BuiltinArg::BA(e) => count_var_in_expr(e, reg),
        BuiltinArg::BASplitLong(a, b) | BuiltinArg::BAAddPtr(a, b) =>
            count_var_in_builtin_arg(a, reg) + count_var_in_builtin_arg(b, reg),
        _ => 0,
    }
}

/// Count occurrences of `Evar(reg)` in a statement.
fn count_var_in_stmt(stmt: &CsharpminorStmt, reg: RTLReg) -> usize {
    match stmt {
        CsharpminorStmt::Sset(_, expr) => count_var_in_expr(expr, reg),
        CsharpminorStmt::Sstore(_, addr, val) =>
            count_var_in_expr(addr, reg) + count_var_in_expr(val, reg),
        CsharpminorStmt::Scall(_, _, callee, args) => {
            let c = if let either::Either::Left(e) = callee { count_var_in_expr(e, reg) } else { 0 };
            c + args.iter().map(|a| count_var_in_expr(a, reg)).sum::<usize>()
        }
        CsharpminorStmt::Stailcall(_, callee, args) => {
            let c = if let either::Either::Left(e) = callee { count_var_in_expr(e, reg) } else { 0 };
            c + args.iter().map(|a| count_var_in_expr(a, reg)).sum::<usize>()
        }
        CsharpminorStmt::Sbuiltin(_, _, args, res) => {
            args.iter().map(|a| count_var_in_builtin_arg(a, reg)).sum::<usize>()
                + count_var_in_builtin_arg(res, reg)
        }
        CsharpminorStmt::Scond(_, args, _, _) =>
            args.iter().map(|a| count_var_in_expr(a, reg)).sum::<usize>(),
        CsharpminorStmt::Sjumptable(expr, _) => count_var_in_expr(expr, reg),
        CsharpminorStmt::Sreturn(expr) => count_var_in_expr(expr, reg),
        CsharpminorStmt::Sseq(stmts) =>
            stmts.iter().map(|s| count_var_in_stmt(s, reg)).sum::<usize>(),
        _ => 0,
    }
}

/// Substitute `replacement` for every `Evar(reg)` in an expression.
fn subst_expr_for_var_in_expr(
    expr: &CsharpminorExpr, reg: RTLReg, replacement: &CsharpminorExpr,
) -> CsharpminorExpr {
    match expr {
        CsharpminorExpr::Evar(r) if *r == reg => replacement.clone(),
        CsharpminorExpr::Eunop(op, inner) =>
            CsharpminorExpr::Eunop(op.clone(), Box::new(subst_expr_for_var_in_expr(inner, reg, replacement))),
        CsharpminorExpr::Ebinop(op, l, r) =>
            CsharpminorExpr::Ebinop(
                op.clone(),
                Box::new(subst_expr_for_var_in_expr(l, reg, replacement)),
                Box::new(subst_expr_for_var_in_expr(r, reg, replacement)),
            ),
        CsharpminorExpr::Eload(chunk, addr) =>
            CsharpminorExpr::Eload(*chunk, Box::new(subst_expr_for_var_in_expr(addr, reg, replacement))),
        CsharpminorExpr::Econdition(c, t, f) =>
            CsharpminorExpr::Econdition(
                Box::new(subst_expr_for_var_in_expr(c, reg, replacement)),
                Box::new(subst_expr_for_var_in_expr(t, reg, replacement)),
                Box::new(subst_expr_for_var_in_expr(f, reg, replacement)),
            ),
        _ => expr.clone(),
    }
}

fn subst_expr_for_var_in_ba(
    ba: &BuiltinArg<CsharpminorExpr>, reg: RTLReg, replacement: &CsharpminorExpr,
) -> BuiltinArg<CsharpminorExpr> {
    match ba {
        BuiltinArg::BA(e) => BuiltinArg::BA(subst_expr_for_var_in_expr(e, reg, replacement)),
        BuiltinArg::BASplitLong(a, b) =>
            BuiltinArg::BASplitLong(
                Box::new(subst_expr_for_var_in_ba(a, reg, replacement)),
                Box::new(subst_expr_for_var_in_ba(b, reg, replacement)),
            ),
        BuiltinArg::BAAddPtr(a, b) =>
            BuiltinArg::BAAddPtr(
                Box::new(subst_expr_for_var_in_ba(a, reg, replacement)),
                Box::new(subst_expr_for_var_in_ba(b, reg, replacement)),
            ),
        _ => ba.clone(),
    }
}

/// Substitute `replacement` for every `Evar(reg)` in a statement.
fn subst_expr_for_var_in_stmt(
    stmt: &CsharpminorStmt, reg: RTLReg, replacement: &CsharpminorExpr,
) -> CsharpminorStmt {
    match stmt {
        CsharpminorStmt::Sset(dst, expr) =>
            CsharpminorStmt::Sset(*dst, subst_expr_for_var_in_expr(expr, reg, replacement)),
        CsharpminorStmt::Sstore(chunk, addr, val) =>
            CsharpminorStmt::Sstore(
                *chunk,
                subst_expr_for_var_in_expr(addr, reg, replacement),
                subst_expr_for_var_in_expr(val, reg, replacement),
            ),
        CsharpminorStmt::Scall(dst, sig, callee, args) => {
            let new_callee = match callee {
                either::Either::Left(e) =>
                    either::Either::Left(subst_expr_for_var_in_expr(e, reg, replacement)),
                other => other.clone(),
            };
            let new_args: Vec<_> = args.iter()
                .map(|a| subst_expr_for_var_in_expr(a, reg, replacement)).collect();
            CsharpminorStmt::Scall(*dst, sig.clone(), new_callee, new_args)
        }
        CsharpminorStmt::Stailcall(sig, callee, args) => {
            let new_callee = match callee {
                either::Either::Left(e) =>
                    either::Either::Left(subst_expr_for_var_in_expr(e, reg, replacement)),
                other => other.clone(),
            };
            let new_args: Vec<_> = args.iter()
                .map(|a| subst_expr_for_var_in_expr(a, reg, replacement)).collect();
            CsharpminorStmt::Stailcall(sig.clone(), new_callee, new_args)
        }
        CsharpminorStmt::Sbuiltin(dst, name, args, res) => {
            let new_args: Vec<_> = args.iter()
                .map(|a| subst_expr_for_var_in_ba(a, reg, replacement)).collect();
            let new_res = subst_expr_for_var_in_ba(res, reg, replacement);
            CsharpminorStmt::Sbuiltin(*dst, name.clone(), new_args, new_res)
        }
        CsharpminorStmt::Scond(cond, args, ifso, ifnot) => {
            let new_args: Vec<_> = args.iter()
                .map(|a| subst_expr_for_var_in_expr(a, reg, replacement)).collect();
            CsharpminorStmt::Scond(cond.clone(), new_args, *ifso, *ifnot)
        }
        CsharpminorStmt::Sjumptable(expr, targets) =>
            CsharpminorStmt::Sjumptable(subst_expr_for_var_in_expr(expr, reg, replacement), targets.clone()),
        CsharpminorStmt::Sreturn(expr) =>
            CsharpminorStmt::Sreturn(subst_expr_for_var_in_expr(expr, reg, replacement)),
        CsharpminorStmt::Sseq(stmts) => {
            let new_stmts: Vec<_> = stmts.iter()
                .map(|s| subst_expr_for_var_in_stmt(s, reg, replacement)).collect();
            CsharpminorStmt::Sseq(new_stmts)
        }
        _ => stmt.clone(),
    }
}

/// Returns true if an expression is pure (no memory loads).
fn expr_is_pure(expr: &CsharpminorExpr) -> bool {
    match expr {
        CsharpminorExpr::Evar(_) | CsharpminorExpr::Econst(_) | CsharpminorExpr::Eaddrof(_) => true,
        CsharpminorExpr::Eunop(_, inner) => expr_is_pure(inner),
        CsharpminorExpr::Ebinop(_, l, r) => expr_is_pure(l) && expr_is_pure(r),
        CsharpminorExpr::Eload(_, _) => false,
        CsharpminorExpr::Econdition(c, t, f) =>
            expr_is_pure(c) && expr_is_pure(t) && expr_is_pure(f),
    }
}

/// Inline single-def/single-use Iop temps; skips Iload, backward refs, and intervening redefs.
fn inline_single_use_temps(working: &mut HashMap<Node, CsharpminorStmt>, db: &DecompileDB) {
    let inline_regs: HashSet<RTLReg> = db
        .rel_iter::<RTLReg>("emit_inline_temp")
        .copied()
        .collect();
    if inline_regs.is_empty() {
        return;
    }

    // Build def map: reg -> (node, expr) for Sset definitions of inline-eligible regs
    let mut def_map: HashMap<RTLReg, (Node, CsharpminorExpr)> = HashMap::new();
    let mut multi_def: HashSet<RTLReg> = HashSet::new();
    for (&node, stmt) in working.iter() {
        if let CsharpminorStmt::Sset(reg, expr) = stmt {
            if inline_regs.contains(reg) {
                if def_map.contains_key(reg) {
                    multi_def.insert(*reg);
                } else {
                    def_map.insert(*reg, (node, expr.clone()));
                }
            }
        }
    }
    for reg in &multi_def {
        def_map.remove(reg);
    }

    // Filter: skip non-pure expressions (belt-and-suspenders for Iload safety)
    def_map.retain(|_, (_, expr)| expr_is_pure(expr));

    if def_map.is_empty() {
        return;
    }

    // Build per-node register defs (Sset, Scall, Sbuiltin) for intervening-def check.
    let mut node_defs: HashMap<Node, HashSet<RTLReg>> = HashMap::new();
    for (&node, stmt) in working.iter() {
        match stmt {
            CsharpminorStmt::Sset(reg, _) => {
                node_defs.entry(node).or_default().insert(*reg);
            }
            CsharpminorStmt::Scall(Some(reg), _, _, _) => {
                node_defs.entry(node).or_default().insert(*reg);
            }
            CsharpminorStmt::Sbuiltin(Some(reg), _, _, _) => {
                node_defs.entry(node).or_default().insert(*reg);
            }
            _ => {}
        }
    }

    // Sorted node list for checking intervening definitions by address order
    let mut sorted_nodes: Vec<Node> = working.keys().copied().collect();
    sorted_nodes.sort();

    // Build use map: for each eligible reg, find use sites and occurrence count
    let mut use_sites: HashMap<RTLReg, Vec<(Node, usize)>> = HashMap::new();
    for (&node, stmt) in working.iter() {
        for (&reg, (def_node, _)) in &def_map {
            if node == *def_node { continue; }
            let count = count_var_in_stmt(stmt, reg);
            if count > 0 {
                use_sites.entry(reg).or_default().push((node, count));
            }
        }
    }

    // Process in sorted node order (by def_node address) for determinism.
    let mut candidates: Vec<(RTLReg, Node, CsharpminorExpr)> = def_map.into_iter()
        .map(|(reg, (node, expr))| (reg, node, expr))
        .collect();
    candidates.sort_by_key(|(_, node, _)| *node);

    // Track modified nodes to avoid stale substitutions in chained temps
    let mut modified_nodes: HashSet<Node> = HashSet::new();

    let mut inlined = 0usize;
    for (reg, def_node, expr) in &candidates {
        if modified_nodes.contains(def_node) { continue; }

        let sites = match use_sites.get(reg) {
            Some(s) => s,
            None => continue,
        };
        if sites.len() != 1 { continue; }
        let (use_node, occurrence_count) = sites[0];
        if occurrence_count != 1 { continue; }

        if modified_nodes.contains(&use_node) { continue; }

        // Skip backward references (def >= use); address-order scan is unreliable in loops.
        if *def_node >= use_node { continue; }

        // Check no operand is redefined between def and use (conservative, sound for acyclic forward refs).
        let mut expr_operands = HashSet::new();
        collect_expr_vars(&expr, &mut expr_operands);

        let mut operand_redefined = false;
        for &node in &sorted_nodes {
            if node <= *def_node { continue; }
            if node >= use_node { break; }
            if let Some(defs_at_node) = node_defs.get(&node) {
                if !defs_at_node.is_disjoint(&expr_operands) {
                    operand_redefined = true;
                    break;
                }
            }
        }
        if operand_redefined { continue; }

        let use_stmt = match working.get(&use_node) {
            Some(s) => s.clone(),
            None => continue,
        };

        let new_stmt = subst_expr_for_var_in_stmt(&use_stmt, *reg, &expr);
        working.insert(use_node, new_stmt);
        working.insert(*def_node, CsharpminorStmt::Snop);
        modified_nodes.insert(use_node);
        modified_nodes.insert(*def_node);
        inlined += 1;
    }

    if inlined > 0 {
        debug!("inline_single_use_temps: inlined {} temporaries", inlined);
    }
}
