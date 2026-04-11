
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::clight_pass::invert_condition;
use crate::decompile::passes::pass::IRPass;
use crate::x86::op::{Comparison, Condition};
use crate::x86::types::{Address, BuiltinArg, Constant, CsharpminorExpr, CsharpminorStmt, Node, RTLReg};
use ascent::ascent_par;
use log::debug;
use rayon::prelude::*;
use std::collections::{HashMap, HashSet};

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

                let structured = structure(stmts, &next_map);
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

        // Shared nodes are structured once per owning function, so the same (node, stmt) can appear multiple times.
        let mut seen: HashSet<(Node, CsharpminorStmt)> = HashSet::new();
        let new_rel = ascent::boxcar::Vec::<(Node, CsharpminorStmt)>::new();
        for tuple in result_stmts {
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
        &["csharp_stmt_candidate", "instr_in_function", "single_def_const", "dead_def", "code_in_block", "next", "emit_inline_temp", "emit_var_type_candidate"]
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

    // Transitive reachability via trrel
    #[ds(ascent_byods_rels::trrel)]
    relation reaches(Node, Node);

    reaches(*a, *b) <-- cfg_edge(a, b);

    // Scond where neither target dominates the branch (not a back edge) is an if-then-else candidate
    relation scond_node(Node, Node, Node);
    scond_node(*node, *t, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(_, _, t, f)),
        !dominates(node, t),
        !dominates(node, f);

    // Join point: minimum node reachable from both targets that is dominated by the branch
    relation join_candidate(Node, Node);
    join_candidate(*branch, *node) <--
        scond_node(branch, t, f),
        reaches(t, node),
        reaches(f, node),
        dominates(node, branch);

    lattice join_point(Node, ascent::Dual<Node>);
    join_point(*branch, ascent::Dual(*node)) <--
        join_candidate(branch, node);

    // If-body membership: nodes reachable from branch targets, stopping at join point
    relation ifbody_true(Node, Node);
    relation ifbody_false(Node, Node);
    ifbody_true(*branch, *t) <--
        scond_node(branch, t, _),
        join_point(branch, ?ascent::Dual(join)),
        if t != join,
        !loop_header(t);

    ifbody_true(*branch, *next) <--
        ifbody_true(branch, cur),
        cfg_edge(cur, next),
        join_point(branch, ?ascent::Dual(join)),
        if next != join,
        dominates(next, branch),
        !loop_header(next),
        !loop_body_node(next);

    ifbody_false(*branch, *f) <--
        scond_node(branch, _, f),
        join_point(branch, ?ascent::Dual(join)),
        if f != join,
        !loop_header(f);

    ifbody_false(*branch, *next) <--
        ifbody_false(branch, cur),
        cfg_edge(cur, next),
        join_point(branch, ?ascent::Dual(join)),
        if next != join,
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
        !loop_header(t);
    ifbody_true(*branch, *next) <--
        scond_no_join(branch),
        ifbody_true(branch, cur),
        cfg_edge(cur, next),
        dominates(next, branch),
        !loop_header(next),
        !loop_body_node(next);

    ifbody_false(*branch, *f) <--
        scond_no_join(branch),
        scond_node(branch, _, f),
        !loop_header(f);
    ifbody_false(*branch, *next) <--
        scond_no_join(branch),
        ifbody_false(branch, cur),
        cfg_edge(cur, next),
        dominates(next, branch),
        !loop_header(next),
        !loop_body_node(next);

    // Entry node for the function (lowest address statement node)
    relation entry_node(Node);

    // Reachability from entry (used for dominance computation)
    relation reachable_from_entry(Node);
    reachable_from_entry(*entry) <-- entry_node(entry);
    reachable_from_entry(*b) <-- reachable_from_entry(a), cfg_edge(a, b);

    // Path avoiding: path_avoiding(n, d) means n is reachable from entry without going through d
    relation path_avoiding(Node, Node);
    path_avoiding(*entry, *d) <--
        entry_node(entry),
        reachable_from_entry(d),
        if *entry != *d;
    path_avoiding(*n, *d) <--
        path_avoiding(prev, d),
        cfg_edge(prev, n),
        if *n != *d;

    // Dominance: d dominates n iff cannot reach n from entry without going through d
    // (d strictly dominates n when d != n)
    relation dominates(Node, Node);
    dominates(*n, *d) <--
        reachable_from_entry(n),
        reachable_from_entry(d),
        !path_avoiding(n, d),
        if *n != *d;

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

    // Switch chain detection: if-else-if chains comparing same register for equality
    relation compares_eq(Node, u64, i64, Node, Node);

    // Ceq: true branch is the matching case, false branch continues
    compares_eq(*node, *reg, *val, *t, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompimm(cmp, val) = cond,
        if *cmp == Comparison::Ceq,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0];

    compares_eq(*node, *reg, *val, *t, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompuimm(cmp, val) = cond,
        if *cmp == Comparison::Ceq,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0];

    compares_eq(*node, *reg, *val, *t, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccomplimm(cmp, val) = cond,
        if *cmp == Comparison::Ceq,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0];

    compares_eq(*node, *reg, *val, *t, *f) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompluimm(cmp, val) = cond,
        if *cmp == Comparison::Ceq,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0];

    // Cne: inverted; false branch matches (reg == val), true continues
    compares_eq(*node, *reg, *val, *f, *t) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompimm(cmp, val) = cond,
        if *cmp == Comparison::Cne,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0];

    compares_eq(*node, *reg, *val, *f, *t) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompuimm(cmp, val) = cond,
        if *cmp == Comparison::Cne,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0];

    compares_eq(*node, *reg, *val, *f, *t) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccomplimm(cmp, val) = cond,
        if *cmp == Comparison::Cne,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0];

    compares_eq(*node, *reg, *val, *f, *t) <--
        stmt(node, ?CsharpminorStmt::Scond(cond, args, t, f)),
        if let Condition::Ccompluimm(cmp, val) = cond,
        if *cmp == Comparison::Cne,
        if args.len() == 1,
        if let CsharpminorExpr::Evar(reg) = &args[0];

    relation switch_chain(Node, Node, u64, i64, Node);
    switch_chain(*node, *node, *reg, *val, *t) <--
        compares_eq(node, reg, val, t, _);

    // Direct chain: false branch of prev is a compares_eq on the same register
    switch_chain(*head, *f, *reg, *next_val, *next_t) <--
        switch_chain(head, prev, reg, _, _),
        compares_eq(prev, _, _, _, f),
        compares_eq(f, reg, next_val, next_t, _);

    // Bridge chain: prev's false leads to non-eq Scond then compares_eq (GCC range-check interleaving)
    switch_chain(*head, *f_f, *reg, *next_val, *next_t) <--
        switch_chain(head, prev, reg, _, _),
        compares_eq(prev, _, _, _, f),
        stmt(f, ?CsharpminorStmt::Scond(_, _, _, f_f)),
        compares_eq(f_f, reg, next_val, next_t, _);

    switch_chain(*head, *f_t, *reg, *next_val, *next_t) <--
        switch_chain(head, prev, reg, _, _),
        compares_eq(prev, _, _, _, f),
        stmt(f, ?CsharpminorStmt::Scond(_, _, f_t, _)),
        compares_eq(f_t, reg, next_val, next_t, _);

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

    // Suppress intermediate Scond nodes bridged over during chain detection
    trim_node(*f) <--
        primary_switch(head, reg),
        switch_chain(head, prev, reg, _, _),
        compares_eq(prev, _, _, _, f),
        stmt(f, ?CsharpminorStmt::Scond(_, _, _, f_f)),
        switch_chain(head, f_f, _, _, _);

    trim_node(*f) <--
        primary_switch(head, reg),
        switch_chain(head, prev, reg, _, _),
        compares_eq(prev, _, _, _, f),
        stmt(f, ?CsharpminorStmt::Scond(_, _, f_t, _)),
        switch_chain(head, f_t, _, _, _);
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
pub fn structure(stmts: &[(Node, CsharpminorStmt)], next_map: &HashMap<Node, Node>) -> StructuringResult {
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
        // Walk `next` chain to first statement node
        let mut cur = real_addr;
        let mut visited = HashSet::new();
        while visited.insert(cur) {
            if let Some(&nxt) = next_map.get(&cur) {
                if stmt_nodes.contains(&nxt) {
                    return nxt;
                }
                cur = nxt;
            } else {
                break;
            }
        }
        target
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

    let seq_edges = compute_sequential_edges(&current_stmts);
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

    // Populate entry node: the first (lowest address) statement node is the function entry
    let entry_node = current_stmts[0].0;
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

    // Fallback: imperative comparison tree analysis for complex switch patterns
    if valid_switches.is_empty() {
        let tree_results = detect_comparison_tree_switches(&current_stmts, next_map);
        for (head, reg, ref cases) in &tree_results {
            if cases.len() >= 3 {
                for &(val, target, member_node) in cases {
                    switch_chain_members.push((*head, member_node, *reg, val, target));
                }
                valid_switches.push((*head, *reg));
            }
        }
    }

    let switch_member_nodes: HashSet<Node> = switch_chain_members
        .iter()
        .map(|(_, member, _, _, _)| *member)
        .collect();

    // Determine valid if-then-else branches for metadata export.
    // Exclude loop exit conditions and switch members.
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
fn detect_comparison_tree_switches(
    stmts: &[(Node, CsharpminorStmt)],
    next_map: &HashMap<Node, Node>,
) -> Vec<(Node, u64, Vec<(i64, Node, Node)>)> {
    use crate::x86::types::CminorBinop;

    let stmt_map: HashMap<Node, &CsharpminorStmt> = stmts.iter().map(|(n, s)| (*n, s)).collect();

    // Sequential successor map via `next` chain walk
    let stmt_node_set: HashSet<Node> = stmts.iter().map(|(n, _)| *n).collect();
    let mut seq_next_map: HashMap<Node, Node> = HashMap::new();
    for &(node, _) in stmts {
        let mut cur = node;
        let mut visited = HashSet::new();
        while visited.insert(cur) {
            if let Some(&nxt) = next_map.get(&cur) {
                if stmt_node_set.contains(&nxt) {
                    seq_next_map.insert(node, nxt);
                    break;
                }
                cur = nxt;
            } else {
                break;
            }
        }
    }

    // Track register derivations: dst = src +/- offset
    let mut reg_derivation: HashMap<RTLReg, (RTLReg, i64)> = HashMap::new();
    for (_, s) in stmts {
        if let CsharpminorStmt::Sset(dst, expr) = s {
            match expr {
                CsharpminorExpr::Ebinop(op, lhs, rhs) => {
                    if let (CsharpminorExpr::Evar(src), CsharpminorExpr::Econst(cst)) = (lhs.as_ref(), rhs.as_ref()) {
                        let offset = match (op, cst) {
                            (CminorBinop::Oaddl, Constant::Olongconst(v)) => Some(*v),
                            (CminorBinop::Oadd, Constant::Ointconst(v)) => Some(*v),
                            (CminorBinop::Osubl, Constant::Olongconst(v)) => Some(-*v),
                            (CminorBinop::Osub, Constant::Ointconst(v)) => Some(-*v),
                            (CminorBinop::Oaddl, Constant::Ointconst(v)) => Some(*v),
                            (CminorBinop::Oadd, Constant::Olongconst(v)) => Some(*v),
                            _ => None,
                        };
                        if let Some(off) = offset {
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

    // Walk comparison tree, collecting (case_value, target, member_node) per branch.
    fn walk_tree(
        node: Node,
        disc_reg: RTLReg,
        stmt_map: &HashMap<Node, &CsharpminorStmt>,
        seq_next_map: &HashMap<Node, Node>,
        reg_derivation: &HashMap<RTLReg, (RTLReg, i64)>,
        resolve_reg: &dyn Fn(RTLReg) -> (RTLReg, i64),
        cases: &mut Vec<(i64, Node, Node)>,
        visited: &mut HashSet<Node>,
    ) {
        if !visited.insert(node) { return; }

        let cmp = match stmt_map.get(&node) {
            Some(CsharpminorStmt::Scond(cond, args, ifso, ifnot)) if args.len() == 1 => {
                if let CsharpminorExpr::Evar(reg) = &args[0] {
                    Some((*reg, *cond, *ifso, *ifnot))
                } else { None }
            }
            _ => None,
        };

        let (reg, cond, ifso, ifnot) = match cmp {
            Some(c) => c,
            None => {
                // Follow sequential successor
                if let Some(&next) = seq_next_map.get(&node) {
                    walk_tree(next, disc_reg, stmt_map, seq_next_map, reg_derivation, resolve_reg, cases, visited);
                }
                return;
            }
        };

        let (root_reg, offset) = resolve_reg(reg);
        let is_disc = root_reg == disc_reg;

        match cond {
            // Ceq: true branch = case body, false continues
            Condition::Ccompimm(Comparison::Ceq, val)
            | Condition::Ccompuimm(Comparison::Ceq, val)
            | Condition::Ccomplimm(Comparison::Ceq, val)
            | Condition::Ccompluimm(Comparison::Ceq, val) if is_disc => {
                let case_val = val - offset;
                cases.push((case_val, ifso, node));
                walk_tree(ifnot, disc_reg, stmt_map, seq_next_map, reg_derivation, resolve_reg, cases, visited);
            }

            // Cne: false branch = case body (inverted), true continues
            Condition::Ccompimm(Comparison::Cne, val)
            | Condition::Ccompuimm(Comparison::Cne, val)
            | Condition::Ccomplimm(Comparison::Cne, val)
            | Condition::Ccompluimm(Comparison::Cne, val) if is_disc => {
                let case_val = val - offset;
                cases.push((case_val, ifnot, node));
                walk_tree(ifso, disc_reg, stmt_map, seq_next_map, reg_derivation, resolve_reg, cases, visited);
            }

            // Cgt range check: disc > (bound - offset); enumerate false-branch cases
            Condition::Ccompimm(Comparison::Cgt, bound)
            | Condition::Ccompuimm(Comparison::Cgt, bound)
            | Condition::Ccomplimm(Comparison::Cgt, bound)
            | Condition::Ccompluimm(Comparison::Cgt, bound) if is_disc => {
                let disc_upper = bound - offset;
                let disc_lower = if offset < 0 { -offset } else { 0 };
                if disc_upper >= disc_lower && (disc_upper - disc_lower) < 8 {
                    for v in disc_lower..=disc_upper {
                        cases.push((v, ifnot, node));
                    }
                }
                walk_tree(ifso, disc_reg, stmt_map, seq_next_map, reg_derivation, resolve_reg, cases, visited);
            }

            Condition::Ccompimm(Comparison::Cle, bound)
            | Condition::Ccompuimm(Comparison::Cle, bound)
            | Condition::Ccomplimm(Comparison::Cle, bound)
            | Condition::Ccompluimm(Comparison::Cle, bound) if is_disc => {
                let disc_upper = bound - offset;
                let disc_lower = if offset < 0 { -offset } else { 0 };
                if disc_upper >= disc_lower && (disc_upper - disc_lower) < 8 {
                    for v in disc_lower..=disc_upper {
                        cases.push((v, ifso, node));
                    }
                }
                walk_tree(ifnot, disc_reg, stmt_map, seq_next_map, reg_derivation, resolve_reg, cases, visited);
            }

            // Non-discriminant or mask test: explore both branches
            _ => {
                walk_tree(ifso, disc_reg, stmt_map, seq_next_map, reg_derivation, resolve_reg, cases, visited);
                walk_tree(ifnot, disc_reg, stmt_map, seq_next_map, reg_derivation, resolve_reg, cases, visited);
            }
        }
    }

    // Find switch roots: Scond with Ceq comparison
    let mut results: Vec<(Node, u64, Vec<(i64, Node, Node)>)> = Vec::new();
    let mut used_heads: HashSet<Node> = HashSet::new();

    for (node, s) in stmts {
        if let CsharpminorStmt::Scond(cond, args, _, _) = s {
            if args.len() != 1 { continue; }
            if let CsharpminorExpr::Evar(reg) = &args[0] {
                let is_eq = matches!(cond,
                    Condition::Ccompimm(Comparison::Ceq, _)
                    | Condition::Ccompuimm(Comparison::Ceq, _)
                    | Condition::Ccomplimm(Comparison::Ceq, _)
                    | Condition::Ccompluimm(Comparison::Ceq, _)
                );
                if !is_eq { continue; }

                let (root_reg, _) = resolve_reg(*reg);
                if used_heads.contains(node) { continue; }

                let mut cases: Vec<(i64, Node, Node)> = Vec::new();
                let mut visited = HashSet::new();
                walk_tree(
                    *node, root_reg,
                    &stmt_map, &seq_next_map, &reg_derivation,
                    &resolve_reg,
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

fn compute_sequential_edges(stmts: &[(Node, CsharpminorStmt)]) -> Vec<(Node, Node)> {
    let mut sorted_nodes: Vec<Node> = stmts.iter().map(|(n, _)| *n).collect();
    sorted_nodes.sort();
    sorted_nodes.windows(2).map(|w| (w[0], w[1])).collect()
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

    let mut const_map: HashMap<RTLReg, Constant> = HashMap::new();
    let mut multi_def: HashSet<RTLReg> = HashSet::new();
    for &(reg, ref cst) in db.rel_iter::<(RTLReg, Constant)>("single_def_const") {
        if multi_def.contains(&reg) {
            continue;
        }
        if def_count.get(&reg).copied().unwrap_or(0) > 1 {
            multi_def.insert(reg);
            continue;
        }
        if let Some(existing) = const_map.get(&reg) {
            if *existing != *cst {
                const_map.remove(&reg);
                multi_def.insert(reg);
            }
        } else {
            const_map.insert(reg, cst.clone());
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

fn propagate_copies(working: &mut HashMap<Node, CsharpminorStmt>, db: &mut DecompileDB) {
    let stmts: Vec<(Node, CsharpminorStmt)> = working.iter()
        .map(|(n, s)| (*n, s.clone()))
        .collect();

    let code_in_block: HashMap<Node, Node> = db
        .rel_iter::<(Node, Node)>("code_in_block")
        .map(|&(addr, blk)| (addr, blk))
        .collect();

    let mut blocks: HashMap<Node, Vec<(Node, CsharpminorStmt)>> = HashMap::new();
    for (node, stmt) in &stmts {
        if let Some(&blk) = code_in_block.get(node) {
            blocks.entry(blk).or_default().push((*node, stmt.clone()));
        }
    }
    for block_stmts in blocks.values_mut() {
        block_stmts.sort_by_key(|(node, _)| *node);
    }

    fn collect_expr_vars(expr: &CsharpminorExpr, vars: &mut HashSet<RTLReg>) {
        match expr {
            CsharpminorExpr::Evar(reg) => { vars.insert(*reg); }
            CsharpminorExpr::Eunop(_, inner) => collect_expr_vars(inner, vars),
            CsharpminorExpr::Ebinop(_, l, r) => {
                collect_expr_vars(l, vars);
                collect_expr_vars(r, vars);
            }
            CsharpminorExpr::Eload(_, addr) => collect_expr_vars(addr, vars),
            CsharpminorExpr::Econdition(c, t, f) => {
                collect_expr_vars(c, vars);
                collect_expr_vars(t, vars);
                collect_expr_vars(f, vars);
            }
            _ => {}
        }
    }

    fn stmt_uses(stmt: &CsharpminorStmt) -> HashSet<RTLReg> {
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
                fn ba_vars(ba: &BuiltinArg<CsharpminorExpr>, vars: &mut HashSet<RTLReg>) {
                    match ba {
                        BuiltinArg::BA(e) => collect_expr_vars(e, vars),
                        BuiltinArg::BASplitLong(a, b) |
                        BuiltinArg::BAAddPtr(a, b) => { ba_vars(a, vars); ba_vars(b, vars); }
                        _ => {}
                    }
                }
                for a in args { ba_vars(a, &mut vars); }
                ba_vars(res, &mut vars);
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

    fn stmt_def(stmt: &CsharpminorStmt) -> Option<RTLReg> {
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

    let mut replacements: HashMap<Node, CsharpminorStmt> = HashMap::new();
    let mut dead_copies: HashSet<Node> = HashSet::new();

    for (_blk, block_stmts) in &blocks {
        let mut active_copies: Vec<(RTLReg, RTLReg, Node)> = Vec::new();
        let mut copy_use_count: HashMap<Node, usize> = HashMap::new();
        let mut copy_replaced_count: HashMap<Node, usize> = HashMap::new();

        for (node, stmt) in block_stmts {
            let node = *node;

            let uses = stmt_uses(stmt);
            let mut current_stmt = stmt.clone();
            for (dst, src, copy_node) in &active_copies {
                if uses.contains(dst) {
                    current_stmt = subst_var_in_stmt(&current_stmt, *dst, *src);
                    *copy_replaced_count.entry(*copy_node).or_insert(0) += 1;
                }
            }
            if current_stmt != *stmt {
                replacements.insert(node, current_stmt.clone());
            }

            if let Some(def_reg) = stmt_def(&current_stmt) {
                active_copies.retain(|(dst, src, _)| {
                    def_reg != *src && def_reg != *dst
                });
            }

            if let CsharpminorStmt::Sset(dst, CsharpminorExpr::Evar(src)) = stmt {
                if dst != src {
                    active_copies.push((*dst, *src, node));
                    let mut use_count = 0usize;
                    for (future_node, future_stmt) in block_stmts {
                        if *future_node <= node { continue; }
                        let future_uses = stmt_uses(future_stmt);
                        if future_uses.contains(dst) {
                            use_count += 1;
                        }
                        if let Some(def_reg) = stmt_def(future_stmt) {
                            if def_reg == *src || def_reg == *dst { break; }
                        }
                    }
                    copy_use_count.insert(node, use_count);
                }
            }
        }

        for (copy_node, total) in &copy_use_count {
            let replaced = copy_replaced_count.get(copy_node).copied().unwrap_or(0);
            if replaced >= *total && *total > 0 {
                dead_copies.insert(*copy_node);
            }
        }
    }

    if replacements.is_empty() && dead_copies.is_empty() {
        return;
    }

    // Propagate types: for each dead copy Sset(dst, Evar(src)), transfer dst's
    // types to src in emit_var_type_candidate so downstream conversion uses the
    // correct type for the substituted variable.
    let existing_types: Vec<(RTLReg, crate::x86::types::XType)> = db
        .rel_iter::<(RTLReg, crate::x86::types::XType)>("emit_var_type_candidate")
        .cloned()
        .collect();
    for &copy_node in &dead_copies {
        if let Some(CsharpminorStmt::Sset(dst, CsharpminorExpr::Evar(src))) = working.get(&copy_node) {
            for (reg, xty) in &existing_types {
                if *reg == *dst {
                    db.rel_push("emit_var_type_candidate", (*src, xty.clone()));
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

fn eliminate_dead_returns(working: &mut HashMap<Node, CsharpminorStmt>, db: &DecompileDB) {
    let dead_regs: HashSet<RTLReg> = db
        .rel_iter::<(RTLReg,)>("dead_def")
        .map(|&(reg,)| reg)
        .collect();
    if dead_regs.is_empty() {
        return;
    }

    let nodes: Vec<Node> = working.keys().copied().collect();
    for node in nodes {
        let stmt = working.get(&node).unwrap().clone();
        if let CsharpminorStmt::Scall(Some(dst), sig, callee, args) = &stmt {
            if dead_regs.contains(dst) {
                working.insert(node, CsharpminorStmt::Scall(None, sig.clone(), callee.clone(), args.clone()));
            }
        }
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
