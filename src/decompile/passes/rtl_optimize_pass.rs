// RTLOptimizePass: imperative finalization of RTL candidates (disambiguation, copy-prop, DSE, nop collapse, inline-temp discovery), split out so the RTL pass proper stays pure Ascent.

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::x86::op::{Comparison, Condition, Operation};
use crate::x86::types::*;
use either::Either;
use log::info;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::sync::Arc;
use rayon::prelude::*;

#[cfg(debug_assertions)]
use ascent::ascent_par;

// Declarative RTL optimizer; _v2 outputs are diffed against the imperative results (debug-only: excluded entirely in release builds where nothing reads them).
#[cfg(debug_assertions)]
ascent_par! {
    #![measure_rule_times]

    pub struct RTLOptimizerProgram;

    // Seeded inputs.
    relation rtl_opt_inst(Node, RTLInst);
    relation rtl_opt_succ(Node, Node);
    relation rtl_opt_func(Node, Address);
    relation rtl_opt_param(Address, RTLReg);
    relation rtl_opt_entry(Address, Node);
    // Mem-indirect call target-load address regs (call node -> address reg), seeded from FunctionCFG::mem_call_addr_uses so the v2 mirror matches the imperative def/use model.
    relation rtl_opt_mem_call_use(Node, RTLReg);

    // def/use extracted from instructions.
    relation rtl_def(Address, Node, RTLReg);
    relation rtl_use(Address, Node, RTLReg);

    // Definitions
    rtl_def(func, node, *dst) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Iop(_, _, dst));

    rtl_def(func, node, *dst) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Iload(_, _, _, dst));

    rtl_def(func, node, *dst) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Icall(_, _, _, Some(dst), _));

    rtl_def(func, node, *r) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Ibuiltin(_, _, BuiltinArg::BA(r)));

    // Uses
    rtl_use(func, node, *u) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Iop(_, args, _)),
        for u in args.iter();

    rtl_use(func, node, *u) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Iload(_, _, args, _)),
        for u in args.iter();

    rtl_use(func, node, *u) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Istore(_, _, args, _)),
        for u in args.iter();

    rtl_use(func, node, *src) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Istore(_, _, _, src));

    rtl_use(func, node, *u) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Icall(_, _, args, _, _)),
        for u in args.iter();

    rtl_use(func, node, *r) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Icall(_, Either::Left(r), _, _, _));

    // A mem-indirect call also uses the regs forming its target-load address.
    rtl_use(func, node, *r) <--
        rtl_opt_func(node, func),
        rtl_opt_mem_call_use(node, r);

    rtl_use(func, node, *u) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Itailcall(_, _, args)),
        for u in args.iter();

    rtl_use(func, node, *r) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Itailcall(_, Either::Left(r), _));

    rtl_use(func, node, *u) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Icond(_, args, _, _)),
        for u in args.iter();

    rtl_use(func, node, *r) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Ijumptable(r, _));

    rtl_use(func, node, *r) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Ireturn(r));

    // Ibuiltin uses: flatten BuiltinArg recursively.
    rtl_use(func, node, reg) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Ibuiltin(_, args, _)),
        for arg in args.iter(),
        let regs = flatten_ba_uses(arg),
        for reg in regs.iter().copied();

    // Live-out via backward dataflow.
    relation live_out(Node, RTLReg);

    // r live at exit of n if r is used at some successor before being defined there
    live_out(n, r) <--
        rtl_opt_succ(n, succ),
        rtl_use(_, succ, r);

    live_out(n, r) <--
        rtl_opt_succ(n, succ),
        live_out(succ, r),
        !rtl_def(_, succ, r);

    // rtl_reach(a, b): b is reachable from a (trrel).
    #[local]
    #[ds(ascent_byods_rels::trrel)]
    relation rtl_reach(Node, Node);

    rtl_reach(src, dst) <-- rtl_opt_succ(src, dst);

    // Single-definition counting.
    #[local] relation reg_def_count(Address, RTLReg, usize);

    reg_def_count(func, r, count) <--
        rtl_def(func, _, r),
        agg count = ascent::aggregators::count() in rtl_def(func, _, r);

    // Self-zero-rewrite: xor r,r or sub r,r where args == dst.
    relation self_zero_v2(Node);
    self_zero_v2(*node) <--
        rtl_opt_inst(node, ?RTLInst::Iop(op, args, dst)),
        if matches!(op, Operation::Oxor | Operation::Osub | Operation::Oxorl | Operation::Osubl),
        if args.len() == 2,
        if args[0] == args[1],
        if args[0] == *dst;

    // Copy candidates: Omove with 1 arg and distinct src/dst.
    #[local] relation copy_candidate(Address, Node, RTLReg, RTLReg); // (func, copy_node, src, dst)
    copy_candidate(func, node, args[0], *dst) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Iop(Operation::Omove, args, dst)),
        if args.len() == 1,
        if args[0] != *dst;

    // dst must be defined exactly once, in this copy_node
    #[local] relation dst_single_def_at(Address, Node, RTLReg);
    dst_single_def_at(func, node, *dst) <--
        copy_candidate(func, node, _, dst),
        reg_def_count(func, dst, 1),
        rtl_def(func, node, dst);

    // There is a use of dst NOT reachable from the copy_node (unsafe)
    #[local] relation dst_use_unreachable(Address, Node, RTLReg); // (func, copy_node, dst)
    dst_use_unreachable(func, copy_node, *dst) <--
        copy_candidate(func, copy_node, _, dst),
        rtl_use(func, use_node, dst),
        if use_node != copy_node,
        !rtl_reach(copy_node, use_node);

    // Unsafe: a use equal to the copy_node itself (dst uses itself at its own def).
    #[local] relation dst_self_use(Address, Node, RTLReg);
    dst_self_use(func, node, *dst) <--
        copy_candidate(func, node, _, dst),
        rtl_use(func, node, dst);

    // src redefined between copy_node and a use of dst: a mid between (copy_node, use_node] defines src.
    #[local] relation src_redef_on_path(Address, Node, RTLReg); // (func, copy_node, src)
    src_redef_on_path(func, copy_node, *src) <--
        copy_candidate(func, copy_node, src, dst),
        rtl_use(func, use_node, dst),
        rtl_reach(copy_node, mid),
        rtl_reach(mid, use_node),
        if mid != copy_node,
        rtl_def(func, mid, src);

    // Case where mid == use_node (use_node itself is a redef of src).
    src_redef_on_path(func, copy_node, *src) <--
        copy_candidate(func, copy_node, src, dst),
        rtl_use(func, use_node, dst),
        rtl_reach(copy_node, use_node),
        if use_node != copy_node,
        rtl_def(func, use_node, src);

    // At least one use of dst exists
    #[local] relation dst_has_use(Address, Node, RTLReg);
    dst_has_use(func, node, *dst) <--
        copy_candidate(func, node, _, dst),
        rtl_use(func, _, dst);

    // Final substitution: dst -> src
    relation copy_subst_v2(RTLReg, RTLReg);
    // Copy-eliminated node (replace with Inop)
    relation copy_eliminated_v2(Node);

    copy_subst_v2(*dst, *src), copy_eliminated_v2(*copy_node) <--
        copy_candidate(func, copy_node, src, dst),
        !rtl_opt_param(func, dst),
        dst_single_def_at(func, copy_node, dst),
        dst_has_use(func, copy_node, dst),
        !dst_self_use(func, copy_node, dst),
        !dst_use_unreachable(func, copy_node, dst),
        !src_redef_on_path(func, copy_node, src);

    // Resolved substitutions: follow dst -> src chains until fixpoint.
    relation copy_subst_resolved_v2(RTLReg, RTLReg);
    copy_subst_resolved_v2(dst, src) <-- copy_subst_v2(dst, src), !copy_subst_v2(src, _);
    copy_subst_resolved_v2(dst, resolved) <--
        copy_subst_v2(dst, src),
        copy_subst_resolved_v2(src, resolved);

    // Dead store: def not in live_out, is Iop or Iload, not param.
    relation dead_store_v2(Node);
    dead_store_v2(*node) <--
        rtl_def(func, node, reg),
        !rtl_opt_param(func, reg),
        !live_out(node, reg),
        rtl_opt_inst(node, inst),
        if matches!(inst, RTLInst::Iop(_,_,_) | RTLInst::Iload(_,_,_,_));

    // Dead call dst: Icall with dst not live-out; drop the dst, keep the call.
    relation dead_call_dst_v2(Node);
    dead_call_dst_v2(*node) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Icall(_, _, _, Some(dst), _)),
        !rtl_opt_param(func, dst),
        !live_out(node, dst);

    // Inline-temp candidates: single-def single-use Iop whose args are live at the use site.
    #[local] relation reg_distinct_uses(Address, RTLReg, usize);
    // Count distinct use-nodes per reg; rtl_use is (func, node, reg) so set semantics apply.
    reg_distinct_uses(func, r, count) <--
        rtl_use(func, _, r),
        agg count = ascent::aggregators::count() in rtl_use(func, _, r);

    #[local] relation inline_temp_def(Address, RTLReg, Node);
    inline_temp_def(func, *reg, *def_node) <--
        reg_def_count(func, reg, 1),
        rtl_def(func, def_node, reg),
        !rtl_opt_param(func, reg),
        rtl_opt_inst(def_node, ?RTLInst::Iop(_, _, _));

    #[local] relation inline_temp_use(Address, RTLReg, Node);
    inline_temp_use(func, *reg, *use_node) <--
        reg_distinct_uses(func, reg, 1),
        rtl_use(func, use_node, reg);

    // def_args must be in live_in(use_node); live_in(u) = use(u) | (live_out(u) \ def(u)).
    #[local] relation live_in(Node, RTLReg);
    live_in(n, r) <-- rtl_use(_, n, r);
    live_in(n, r) <--
        live_out(n, r),
        !rtl_def(_, n, r);

    #[local] relation def_arg_not_live_at_use(Address, RTLReg);
    def_arg_not_live_at_use(func, *reg) <--
        inline_temp_def(func, reg, def_node),
        inline_temp_use(func, reg, use_node),
        rtl_opt_inst(def_node, ?RTLInst::Iop(_, args, _)),
        for a in args.iter(),
        !live_in(use_node, a);

    #[local] relation inline_temp_reach_ok(Address, RTLReg);
    inline_temp_reach_ok(func, *reg) <--
        inline_temp_def(func, reg, def_node),
        inline_temp_use(func, reg, use_node),
        rtl_reach(def_node, use_node);

    relation inline_temp_v2(RTLReg);
    inline_temp_v2(*reg) <--
        inline_temp_def(func, reg, _),
        inline_temp_use(func, reg, _),
        !def_arg_not_live_at_use(func, reg),
        inline_temp_reach_ok(func, reg);
}

// Flatten BuiltinArg uses recursively (helper for Ascent rule).
pub(crate) fn flatten_ba_uses(arg: &BuiltinArg<RTLReg>) -> Vec<RTLReg> {
    let mut out = Vec::new();
    collect_ba_uses(arg, &mut out);
    out
}

// Build and run RTLOptimizerProgram over a PassContext; returns the program for inspection.
#[cfg(debug_assertions)]
fn run_rtl_optimizer_program(ctx: &PassContext) -> RTLOptimizerProgram {
    let mut prog = RTLOptimizerProgram::default();

    for (&func_addr, func) in &ctx.functions {
        for (&node, inst) in &func.inst {
            prog.rtl_opt_inst.push((node, inst.clone()));
            prog.rtl_opt_func.push((node, func_addr));
        }
        for (&src, dsts) in &func.succs {
            if func.inst.contains_key(&src) {
                for &dst in dsts {
                    prog.rtl_opt_succ.push((src, dst));
                }
            }
        }
        for &reg in &func.params {
            prog.rtl_opt_param.push((func_addr, reg));
        }
        for (&node, regs) in &func.mem_call_addr_uses {
            for &r in regs {
                prog.rtl_opt_mem_call_use.push((node, r));
            }
        }
        prog.rtl_opt_entry.push((func_addr, func.entry));
    }

    prog.run();
    prog
}


#[derive(Debug, Default, Clone, Copy)]
struct RtlOptStats {
    copies: usize,
    dead: usize,
    nops: usize,
    inline_temps: usize,
    zero_rewrites: usize,
}

impl RtlOptStats {
    fn accumulate(&mut self, other: Self) {
        self.copies += other.copies;
        self.dead += other.dead;
        self.nops += other.nops;
        self.inline_temps += other.inline_temps;
        self.zero_rewrites += other.zero_rewrites;
    }

    fn has_changes(self) -> bool {
        self.copies > 0
            || self.dead > 0
            || self.nops > 0
            || self.inline_temps > 0
            || self.zero_rewrites > 0
    }
}

#[cfg(debug_assertions)]
struct AscentV2Snapshot {
    self_zero: HashSet<Node>,
    dead_store: HashSet<Node>,
    dead_call: HashSet<Node>,
    copy_subst: HashMap<RTLReg, RTLReg>,
    inline_temp: HashSet<RTLReg>,
    dead_or_copy_eliminated: HashSet<Node>,
}

fn optimize_rtl_candidates(db: &mut DecompileDB) -> Option<RtlOptStats> {
    let mut ctx = PassContext::load(db);
    if ctx.functions.is_empty() {
        return None;
    }

    let var_types = std::mem::take(&mut ctx.var_types);

    let func_regs: HashMap<Address, HashSet<RTLReg>> = ctx.functions.iter()
        .map(|(&addr, func)| {
            let mut regs = HashSet::new();
            for inst in func.inst.values() {
                collect_inst_regs(inst, &mut regs);
            }
            regs.extend(func.params.iter());
            (addr, regs)
        })
        .collect();

    let per_func_var_types: HashMap<Address, HashMap<RTLReg, XType>> = func_regs.iter()
        .map(|(&addr, regs)| {
            let ft: HashMap<RTLReg, XType> = regs.iter()
                .filter_map(|&reg| var_types.get(&reg).map(|&ty| (reg, ty)))
                .collect();
            (addr, ft)
        })
        .collect();
    let per_func_var_types = std::sync::Mutex::new(per_func_var_types);

    // Return-value register per function (RTLPass binding); after static-eq branch folding prunes the dead tail, a function whose recorded return reg no longer has a surviving def has lost its only return value and is genuinely void (e.g. deregister_tm_clones).
    let func_return_reg: HashMap<Address, RTLReg> = db
        .rel_iter::<(Address, RTLReg)>("emit_function_return")
        .map(|&(addr, reg)| (addr, reg))
        .collect();

    // RTLOptimizerProgram is the Ascent v2 of the imperative optimizer. Its outputs are only consumed by the debug-only RTL_V2_DIFF block below, so in release builds we skip it entirely (dominates the RTL pass -- ~57s on a 700KB binary).
    #[cfg(debug_assertions)]
    let ascent_v2: Option<AscentV2Snapshot> = if std::env::var("RTL_V2_DIFF").is_ok() {
        let ascent_opt = run_rtl_optimizer_program(&ctx);
        let self_zero: HashSet<Node> = ascent_opt.self_zero_v2.iter().map(|&(n,)| n).collect();
        let dead_store: HashSet<Node> = ascent_opt.dead_store_v2.iter().map(|&(n,)| n).collect();
        let copy_eliminated: HashSet<Node> = ascent_opt.copy_eliminated_v2.iter().map(|&(n,)| n).collect();
        let dead_call: HashSet<Node> = ascent_opt.dead_call_dst_v2.iter().map(|&(n,)| n).collect();
        let copy_subst: HashMap<RTLReg, RTLReg> = ascent_opt.copy_subst_resolved_v2
            .iter().map(|&(d, s)| (d, s)).collect();
        let inline_temp: HashSet<RTLReg> = ascent_opt.inline_temp_v2.iter().map(|&(r,)| r).collect();
        let dead_or_copy_eliminated: HashSet<Node> = dead_store.union(&copy_eliminated).copied().collect();
        Some(AscentV2Snapshot { self_zero, dead_store, dead_call, copy_subst, inline_temp, dead_or_copy_eliminated })
    } else {
        None
    };

    let results: Vec<_> = ctx.functions.par_iter_mut()
        .map(|(&func_addr, func)| {
            let mut func_var_types = per_func_var_types.lock().unwrap()
                .remove(&func_addr).unwrap_or_default();

            // Track iteration-1 imperative outputs for diffing against Ascent.
            let imp_self_zero: HashSet<Node> = func.inst.iter()
                .filter_map(|(&n, inst)| match inst {
                    RTLInst::Iop(op, args, dst)
                        if args.len() == 2
                            && args[0] == args[1]
                            && args[0] == *dst
                            && matches!(op, Operation::Oxor | Operation::Osub | Operation::Oxorl | Operation::Osubl) =>
                    {
                        Some(n)
                    }
                    _ => None,
                })
                .collect();

            let folded_static_branch = fold_static_eq_branches(func);

            let zero_rewrites = self_zero_rewrite(func);

            let mut copies = 0usize;
            let mut dead = 0usize;
            let mut iter1_copy_subst: HashMap<RTLReg, RTLReg> = HashMap::new();
            let mut iter1_dead_store_nodes: HashSet<Node> = HashSet::new();
            let mut iter1_dead_call_nodes: HashSet<Node> = HashSet::new();
            let mut first_iter = true;
            loop {
                let du = DefUseInfo::build(func);
                let liveness = LivenessInfo::build(func, &du);

                // Capture snapshot for iteration-1 comparison
                let dead_before: HashMap<Node, RTLInst> = if first_iter {
                    func.inst.iter().map(|(&n, i)| (n, i.clone())).collect()
                } else {
                    HashMap::new()
                };

                let (c, copy_subst) = copy_propagation(func, &du, &liveness);
                if first_iter {
                    iter1_copy_subst = copy_subst.clone();
                }
                for (&dst, &src) in &copy_subst {
                    if let Some(&ty) = func_var_types.get(&dst) {
                        func_var_types.entry(src).or_insert(ty);
                    }
                }
                let d = dead_store_elimination(func, &du, &liveness);

                if first_iter {
                    for (&n, before) in &dead_before {
                        let after = func.inst.get(&n);
                        match (before, after) {
                            (RTLInst::Iop(_,_,_) | RTLInst::Iload(_,_,_,_),
                                Some(RTLInst::Inop)) => {
                                // Non-nop def now nop: could be copy-prop or dead-store; both map to Inop.
                                iter1_dead_store_nodes.insert(n);
                            }
                            (RTLInst::Icall(_, _, _, Some(_), _),
                                Some(RTLInst::Icall(_, _, _, None, _))) => {
                                iter1_dead_call_nodes.insert(n);
                            }
                            _ => {}
                        }
                    }
                }

                if c == 0 && d == 0 {
                    break;
                }
                first_iter = false;
                copies += c;
                dead += d;
            }

            let nops = nop_collapse(func);

            let du = DefUseInfo::build(func);
            let liveness = LivenessInfo::build(func, &du);
            let inlines = find_inline_temps(func, &du, &liveness);

            // The function became void if static-eq folding pruned the defining node of its recorded return value, leaving the return reg with no surviving def (and not a parameter); scoped to folded functions so normal returns are untouched.
            let became_void = folded_static_branch
                && func_return_reg.get(&func_addr).is_some_and(|ret_reg| {
                    !func.params.contains(ret_reg)
                        && du.defs.get(ret_reg).map_or(true, |d| d.is_empty())
                });

            (
                RtlOptStats {
                    copies,
                    dead,
                    nops,
                    inline_temps: inlines.len(),
                    zero_rewrites,
                },
                inlines,
                func_var_types,
                // iteration-1 imperative snapshots for v2 diffing
                func_addr,
                imp_self_zero,
                iter1_copy_subst,
                iter1_dead_store_nodes,
                iter1_dead_call_nodes,
                became_void,
            )
        })
        .collect();

    let mut stats = RtlOptStats::default();
    let mut merged_var_types = var_types;

    let mut imp_self_zero_all: HashSet<Node> = HashSet::new();
    let mut imp_copy_subst_all: HashMap<RTLReg, RTLReg> = HashMap::new();
    let mut imp_dead_store_all: HashSet<Node> = HashSet::new();
    let mut imp_dead_call_all: HashSet<Node> = HashSet::new();
    let mut newly_void: HashSet<Address> = HashSet::new();

    for (func_stats, inlines, func_vt, fa, isz, icp, idst, idcl, became_void) in results {
        stats.accumulate(func_stats);
        ctx.inline_temps.extend(inlines);
        merged_var_types.extend(func_vt);
        imp_self_zero_all.extend(isz);
        for (d, s) in icp { imp_copy_subst_all.insert(d, s); }
        imp_dead_store_all.extend(idst);
        imp_dead_call_all.extend(idcl);
        if became_void { newly_void.insert(fa); }
    }

    // Diff logging: compare Ascent v2 vs imperative iteration-1 outputs (uses eprintln so diffs surface during test runs, where no env_logger is configured).
    #[cfg(debug_assertions)]
    if let Some(v2) = &ascent_v2 {
        let self_zero_missing: Vec<_> = imp_self_zero_all.difference(&v2.self_zero).copied().collect();
        let self_zero_extra: Vec<_> = v2.self_zero.difference(&imp_self_zero_all).copied().collect();
        if !self_zero_missing.is_empty() || !self_zero_extra.is_empty() {
            eprintln!(
                "rtl_v2 diff self_zero: imperative={} ascent={} missing_from_ascent={} extra_in_ascent={}",
                imp_self_zero_all.len(), v2.self_zero.len(),
                self_zero_missing.len(), self_zero_extra.len()
            );
        }
        // imp_dead_store_all = union of copy-eliminated and dead-store nodes (both Inop in iter 1); compare against the same Ascent union.
        let ds_missing: Vec<_> = imp_dead_store_all.difference(&v2.dead_or_copy_eliminated).copied().collect();
        let ds_extra: Vec<_> = v2.dead_or_copy_eliminated.difference(&imp_dead_store_all).copied().collect();
        if !ds_missing.is_empty() || !ds_extra.is_empty() {
            eprintln!(
                "rtl_v2 diff dead_or_copy_elim (iter1): imperative={} ascent_union={} missing_from_ascent={} extra_in_ascent={}",
                imp_dead_store_all.len(), v2.dead_or_copy_eliminated.len(),
                ds_missing.len(), ds_extra.len()
            );
        }
        let dc_missing: Vec<_> = imp_dead_call_all.difference(&v2.dead_call).copied().collect();
        let dc_extra: Vec<_> = v2.dead_call.difference(&imp_dead_call_all).copied().collect();
        if !dc_missing.is_empty() || !dc_extra.is_empty() {
            eprintln!(
                "rtl_v2 diff dead_call_dst (iter1): imperative={} ascent={} missing={} extra={}",
                imp_dead_call_all.len(), v2.dead_call.len(),
                dc_missing.len(), dc_extra.len()
            );
        }
        // ascent copy_subst is path-conservative; expected subset of imperative.
        let cp_missing: Vec<_> = imp_copy_subst_all.iter()
            .filter(|&(d, _)| !v2.copy_subst.contains_key(d))
            .map(|(&d, &s)| (d, s))
            .collect();
        let cp_mismatch: Vec<_> = v2.copy_subst.iter()
            .filter_map(|(&d, &s_asc)| {
                imp_copy_subst_all.get(&d).and_then(|&s_imp| {
                    if s_asc != s_imp { Some((d, s_imp, s_asc)) } else { None }
                })
            })
            .collect();
        let cp_extra: Vec<_> = v2.copy_subst.iter()
            .filter(|&(d, _)| !imp_copy_subst_all.contains_key(d))
            .map(|(&d, &s)| (d, s))
            .collect();
        if !cp_missing.is_empty() || !cp_extra.is_empty() || !cp_mismatch.is_empty() {
            eprintln!(
                "rtl_v2 diff copy_subst (iter1): imperative={} ascent={} ascent_missing={} ascent_extra={} value_mismatch={}",
                imp_copy_subst_all.len(), v2.copy_subst.len(),
                cp_missing.len(), cp_extra.len(), cp_mismatch.len()
            );
        }
        let it_missing: Vec<_> = ctx.inline_temps.difference(&v2.inline_temp).copied().collect();
        let it_extra: Vec<_> = v2.inline_temp.difference(&ctx.inline_temps).copied().collect();
        if !it_missing.is_empty() || !it_extra.is_empty() {
            eprintln!(
                "rtl_v2 diff inline_temp: imperative={} ascent={} missing={} extra={}",
                ctx.inline_temps.len(), v2.inline_temp.len(),
                it_missing.len(), it_extra.len()
            );
        }
    }

    ctx.var_types = merged_var_types;
    ctx.write_back(db);

    if !newly_void.is_empty() {
        mark_functions_void(db, &newly_void);
    }
    Some(stats)
}

// Retype functions that lost their only return value (to static-eq branch folding) as void: emit_function_void_candidate wins the return-type ladder in signature reconciliation (Case 1) so the function renders `void`, and the stale has-return / return-type signals are dropped so they cannot reintroduce a bogus return type.
fn mark_functions_void(db: &mut DecompileDB, void_funcs: &HashSet<Address>) {
    let mut void_cand: Vec<(Address,)> = db
        .rel_iter::<(Address,)>("emit_function_void_candidate")
        .cloned()
        .collect();
    for &f in void_funcs {
        if !void_cand.iter().any(|&(a,)| a == f) {
            void_cand.push((f,));
        }
    }
    db.rel_set("emit_function_void_candidate", void_cand.into_iter().collect::<ascent::boxcar::Vec<_>>());

    let has_ret: Vec<(Address,)> = db
        .rel_iter::<(Address,)>("emit_function_has_return_candidate")
        .filter(|&&(a,)| !void_funcs.contains(&a))
        .cloned()
        .collect();
    db.rel_set("emit_function_has_return_candidate", has_ret.into_iter().collect::<ascent::boxcar::Vec<_>>());

    let ret: Vec<(Address, RTLReg)> = db
        .rel_iter::<(Address, RTLReg)>("emit_function_return")
        .filter(|&&(a, _)| !void_funcs.contains(&a))
        .cloned()
        .collect();
    db.rel_set("emit_function_return", ret.into_iter().collect::<ascent::boxcar::Vec<_>>());

    let ret_ct: Vec<(Address, ClightType)> = db
        .rel_iter::<(Address, ClightType)>("emit_function_return_type_candidate")
        .filter(|&&(a, _)| !void_funcs.contains(&a))
        .cloned()
        .collect();
    db.rel_set("emit_function_return_type_candidate", ret_ct.into_iter().collect::<ascent::boxcar::Vec<_>>());

    let ret_xt: Vec<(Address, XType)> = db
        .rel_iter::<(Address, XType)>("emit_function_return_type_xtype_candidate")
        .filter(|&&(a, _)| !void_funcs.contains(&a))
        .cloned()
        .collect();
    db.rel_set("emit_function_return_type_xtype_candidate", ret_xt.into_iter().collect::<ascent::boxcar::Vec<_>>());
}

pub(crate) fn trim_direct_call_args_to_callee_arity(db: &mut DecompileDB) {
    let callee_arity: HashMap<Address, usize> = db
        .rel_iter::<(Address, Signature)>("emit_function_signature_candidate")
        .fold(HashMap::new(), |mut acc, (addr, sig)| {
            acc.entry(*addr)
                .and_modify(|curr| *curr = (*curr).max(sig.sig_args.len()))
                .or_insert(sig.sig_args.len());
            acc
        });

    let call_targets: HashMap<Node, Address> = db
        .rel_iter::<(Node, Address)>("call_target_func")
        .map(|(call_node, target)| (*call_node, *target))
        .collect();

    let filtered_mapping: Vec<(Node, usize, RTLReg)> = db
        .rel_iter::<(Node, usize, RTLReg)>("call_arg_mapping")
        .filter_map(|&(node, pos, reg)| {
            if let Some(&target) = call_targets.get(&node) {
                if let Some(&arity) = callee_arity.get(&target) {
                    if pos >= arity {
                        return None;
                    }
                }
            }
            Some((node, pos, reg))
        })
        .collect();

    db.rel_set(
        "call_arg_mapping",
        filtered_mapping
            .iter()
            .copied()
            .collect::<ascent::boxcar::Vec<_>>(),
    );
    db.rel_set(
        "call_arg",
        filtered_mapping
            .iter()
            .copied()
            .collect::<ascent::boxcar::Vec<_>>(),
    );

    let mut normalized_mapping: HashMap<(Node, usize), RTLReg> = HashMap::new();
    for (node, pos, reg) in filtered_mapping {
        if let Some(&target) = call_targets.get(&node) {
            if let Some(&arity) = callee_arity.get(&target) {
                debug_assert!(pos < arity);
            }
        }
        normalized_mapping
            .entry((node, pos))
            .and_modify(|curr| *curr = (*curr).max(reg))
            .or_insert(reg);
    }

    let mut args_by_call: HashMap<Node, Vec<(usize, RTLReg)>> = HashMap::new();
    for (&(node, pos), &reg) in &normalized_mapping {
        args_by_call.entry(node).or_default().push((pos, reg));
    }
    let rebuild_args = |node: Node| -> Option<Arc<Vec<RTLReg>>> {
        let mut pairs = args_by_call.get(&node)?.clone();
        pairs.sort_by_key(|(pos, _)| *pos);
        // Scatter by position into a dense vector padded with DEFAULT_VAR so a dropped leading arg leaves a sentinel hole rather than left-shifting later args into its slot (Args is purely positional); contiguous positions 0..N overwrite every slot.
        let len = pairs.last().map(|(pos, _)| *pos + 1).unwrap_or(0);
        let mut args: Vec<RTLReg> = vec![crate::util::DEFAULT_VAR as RTLReg; len];
        for (pos, reg) in pairs {
            args[pos] = reg;
        }
        Some(Arc::new(args))
    };

    let mut call_nodes: HashSet<Node> = db
        .rel_iter::<(Node, Arc<Vec<RTLReg>>)>("call_args_collected_candidate")
        .map(|(node, _)| *node)
        .collect();
    call_nodes.extend(args_by_call.keys().copied());

    let mut existing_call_args: HashMap<Node, Arc<Vec<RTLReg>>> = HashMap::new();
    for &(node, ref args) in db.rel_iter::<(Node, Arc<Vec<RTLReg>>)>("call_args_collected_candidate") {
        let should_replace = existing_call_args
            .get(&node)
            .map(|curr| curr.len() < args.len())
            .unwrap_or(true);
        if should_replace {
            existing_call_args.insert(node, args.clone());
        }
    }

    let new_call_args: ascent::boxcar::Vec<(Node, Arc<Vec<RTLReg>>)> = call_nodes
        .into_iter()
        .map(|node| {
            let args = rebuild_args(node)
                .or_else(|| existing_call_args.get(&node).cloned())
                .unwrap_or_else(|| Arc::new(vec![]));
            (node, args)
        })
        .collect();
    db.rel_set("call_args_collected_candidate", new_call_args);

    let mut rebuilt_args: HashMap<Node, Arc<Vec<RTLReg>>> = db
        .rel_iter::<(Node, Arc<Vec<RTLReg>>)>("call_args_collected_candidate")
        .map(|(node, args)| (*node, args.clone()))
        .collect();

    // Merge float args after integer args for each call node
    for &(call_node, ref float_args) in db.rel_iter::<(Node, Arc<Vec<RTLReg>>)>("call_float_args_collected") {
        if !float_args.is_empty() {
            let int_args = rebuilt_args.entry(call_node).or_insert_with(|| Arc::new(vec![]));
            let mut combined = (**int_args).clone();
            combined.extend_from_slice(float_args);
            *int_args = Arc::new(combined);
        }
    }

    let new_rtl_inst: ascent::boxcar::Vec<(Node, RTLInst)> = db
        .rel_iter::<(Node, RTLInst)>("rtl_inst_candidate")
        .map(|(node, inst)| {
            let replacement_args = rebuilt_args.get(node);
            let patched = match inst {
                RTLInst::Icall(sig, callee, args, dst, next) => {
                    RTLInst::Icall(
                        sig.clone(),
                        callee.clone(),
                        replacement_args.cloned().unwrap_or_else(|| args.clone()),
                        *dst,
                        *next,
                    )
                }
                RTLInst::Itailcall(sig, callee, args) => {
                    RTLInst::Itailcall(
                        sig.clone(),
                        callee.clone(),
                        replacement_args.cloned().unwrap_or_else(|| args.clone()),
                    )
                }
                _ => inst.clone(),
            };
            (*node, patched)
        })
        .collect();
    db.rel_set("rtl_inst_candidate", new_rtl_inst);
}

pub struct RTLOptimizePass;

impl IRPass for RTLOptimizePass {
    fn name(&self) -> &'static str { "rtl_optimize" }

    fn run(&self, db: &mut DecompileDB) {
        trim_direct_call_args_to_callee_arity(db);
        if let Some(stats) = optimize_rtl_candidates(db) {
            if stats.has_changes() {
                info!(
                    "rtl: {} copies propagated, {} dead stores, {} nops collapsed, {} inline temps, {} zero rewrites",
                    stats.copies,
                    stats.dead,
                    stats.nops,
                    stats.inline_temps,
                    stats.zero_rewrites,
                );
            }
        }
    }

    fn inputs(&self) -> &'static [&'static str] {
        &[
            "rtl_inst_candidate",
            "rtl_succ_candidate",
            "instr_in_function",
            "emit_function",
            "emit_function_param_candidate",
            "emit_var_type_candidate",
            "emit_function_signature_candidate",
            "emit_function_return",
            "call_target_func",
            "call_arg_mapping",
            "call_args_collected_candidate",
            "call_float_args_collected",
        ]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "rtl_inst",
            "rtl_succ",
            "rtl_next",
            "single_def_const",
            "emit_inline_temp",
            "call_arg_mapping",
            "call_arg",
            "call_args_collected_candidate",
            // Static-eq branch folding can retype a function void; these signal that to the signature reconciliation pass.
            "emit_function_void_candidate",
            "emit_function_has_return_candidate",
            "emit_function_return",
            "emit_function_return_type_candidate",
            "emit_function_return_type_xtype_candidate",
        ]
    }

    fn extra_reads(&self) -> &'static [&'static str] {
        // Read imperatively in PassContext::load to add a mem-indirect call's target-load address regs as uses of the call node (keeps the vtable Iload alive through DSE).
        &["call_through_memory_load"]
    }
}

pub(crate) struct FunctionCFG {
    #[allow(dead_code)]
    pub(crate) func_addr: Address,
    pub(crate) entry: Node,
    pub(crate) nodes: BTreeSet<Node>,
    pub(crate) inst: BTreeMap<Node, RTLInst>,
    pub(crate) succs: HashMap<Node, Vec<Node>>,
    pub(crate) preds: HashMap<Node, Vec<Node>>,
    pub(crate) params: HashSet<RTLReg>,
    // For a mem-indirect call (`call [base+idx*s+ofs]`), the address regs feeding the vtable/function-pointer load; rtl_pass threads these into call_through_memory_load (consumed only by cshminor for Eload rendering), so the optimizer's def/use model never saw them and DSE killed the producing Iload, collapsing the call target to an uninitialized var. Recorded here so they count as uses of the call node.
    pub(crate) mem_call_addr_uses: HashMap<Node, Vec<RTLReg>>,
}


struct PassContext {
    functions: BTreeMap<Address, FunctionCFG>,
    var_types: HashMap<RTLReg, XType>,
    inline_temps: HashSet<RTLReg>,
}

impl PassContext {
    fn load(db: &DecompileDB) -> Self {
        let rtl_insts: Vec<(Node, RTLInst)> = db
            .rel_iter::<(Node, RTLInst)>("rtl_inst_candidate")
            .cloned()
            .collect();
        let rtl_succs: Vec<(Node, Node)> = db
            .rel_iter::<(Node, Node)>("rtl_succ_candidate")
            .cloned()
            .collect();
        let instr_in_func: Vec<(Node, Address)> = db
            .rel_iter::<(Node, Address)>("instr_in_function")
            .cloned()
            .collect();
        let emit_funcs: Vec<(Address, Symbol, Node)> = db
            .rel_iter::<(Address, Symbol, Node)>("emit_function")
            .cloned()
            .collect();
        let emit_params: Vec<(Address, RTLReg)> = db
            .rel_iter::<(Address, RTLReg)>("emit_function_param_candidate")
            .cloned()
            .collect();
        // Address regs feeding a mem-indirect call's target load, per call node (node -> [base, idx?]); see FunctionCFG::mem_call_addr_uses. Declared in extra_reads().
        let mut mem_call_addr_uses: HashMap<Node, Vec<RTLReg>> = HashMap::new();
        for (node, _temp, _chunk, _addr, args) in
            db.rel_iter::<(Node, RTLReg, MemoryChunk, crate::x86::op::Addressing, Arc<Vec<RTLReg>>)>("call_through_memory_load")
        {
            let entry = mem_call_addr_uses.entry(*node).or_default();
            for &r in args.iter() {
                if !entry.contains(&r) {
                    entry.push(r);
                }
            }
        }
        let var_types: HashMap<RTLReg, XType> = {
            let mut groups: HashMap<RTLReg, Vec<XType>> = HashMap::new();
            for (reg, xty) in db.rel_iter::<(RTLReg, XType)>("emit_var_type_candidate") {
                groups.entry(*reg).or_default().push(*xty);
            }
            groups.into_iter().map(|(reg, mut tys)| {
                tys.sort_by_key(|ty| (crate::decompile::passes::clight_pass::xtype_refine_priority(ty), *ty));
                let chosen = *tys.last().unwrap();
                (reg, chosen)
            }).collect()
        };

        let node_to_func: HashMap<Node, Address> = {
            let mut groups: HashMap<Node, Address> = HashMap::new();
            for &(n, f) in &instr_in_func {
                groups.entry(n)
                    .and_modify(|curr| *curr = (*curr).min(f))
                    .or_insert(f);
            }
            groups
        };

        let func_entries: HashMap<Address, Node> = emit_funcs.iter()
            .map(|&(addr, _, entry)| (addr, entry))
            .collect();

        let mut func_params: HashMap<Address, HashSet<RTLReg>> = HashMap::new();
        for &(addr, reg) in &emit_params {
            func_params.entry(addr).or_default().insert(reg);
        }

        let mut func_node_candidates: HashMap<Address, HashMap<Node, Vec<RTLInst>>> = HashMap::new();
        for (node, inst) in &rtl_insts {
            if let Some(&func) = node_to_func.get(node) {
                func_node_candidates.entry(func).or_default()
                    .entry(*node).or_default().push(inst.clone());
            }
        }

        let mut reg_usage_count: HashMap<RTLReg, usize> = HashMap::new();
        for (_, inst) in &rtl_insts {
            let mut regs = HashSet::new();
            collect_inst_regs(inst, &mut regs);
            for reg in regs {
                *reg_usage_count.entry(reg).or_insert(0) += 1;
            }
        }

        let mut func_insts: HashMap<Address, BTreeMap<Node, RTLInst>> = HashMap::new();
        for (func, node_candidates) in func_node_candidates {
            let insts = func_insts.entry(func).or_default();
            for (node, candidates) in node_candidates {
                if candidates.len() == 1 {
                    insts.insert(node, candidates.into_iter().next().unwrap());
                } else {
                    let mut candidates = candidates;
                    candidates.sort_by_cached_key(|inst| format!("{:?}", inst));
    // Bias selection toward Icond when both Icond and Iop coexist (fused flag-setter+jcc: cmp/test/sub/and+jcc; Iop is side-effect-only, Icond carries the CFG edge); without this Iop wins tie-break and the branch is dropped. reg_usage_count is a secondary tie-breaker for fused-flag and call-arg disambiguation cases beyond cmov shadow (now resolved upstream by lop_overwrite_use_id).
                    let best = candidates.into_iter().max_by_key(|inst| {
                        let mut regs = HashSet::new();
                        collect_inst_regs(inst, &mut regs);
                        let score: usize = regs.iter()
                            .map(|r| reg_usage_count.get(r).copied().unwrap_or(0))
                            .sum();
                        let arg_bonus = match inst {
                            RTLInst::Iop(_, args, _) if !args.is_empty() => 1,
                            RTLInst::Iload(_, _, args, _) if !args.is_empty() => 1,
                            RTLInst::Icond(_, args, _, _) if !args.is_empty() => 1,
                            _ => 0,
                        };
                        let cond_bonus = if matches!(inst, RTLInst::Icond(..)) { 100 } else { 0 };
                        score + arg_bonus + cond_bonus
                    }).unwrap();
                    insts.insert(node, best);
                }
            }
        }

        let mut func_succs: HashMap<Address, HashMap<Node, Vec<Node>>> = HashMap::new();
        for &(src, dst) in &rtl_succs {
            if let Some(&func) = node_to_func.get(&src) {
                func_succs.entry(func).or_default()
                    .entry(src).or_default().push(dst);
            }
        }

        let mut functions = BTreeMap::new();
        for (&func_addr, insts) in &func_insts {
            let entry = match func_entries.get(&func_addr) {
                Some(&e) => e,
                None => continue,
            };
            let nodes: BTreeSet<Node> = insts.keys().copied().collect();

            let raw_succs = func_succs.remove(&func_addr).unwrap_or_default();
            let mut succs: HashMap<Node, Vec<Node>> = HashMap::new();
            for (src, dsts) in raw_succs {
                if nodes.contains(&src) {
                    succs.insert(src, dsts);
                }
            }

            let nodes_vec: Vec<Node> = nodes.iter().copied().collect();
            for (i, &node) in nodes_vec.iter().enumerate() {
                if succs.contains_key(&node) {
                    continue;
                }
                let inst = match insts.get(&node) {
                    Some(inst) => inst,
                    None => continue,
                };
                let needs_fallthrough = matches!(inst,
                    RTLInst::Inop | RTLInst::Iop(..) | RTLInst::Iload(..)
                    | RTLInst::Istore(..) | RTLInst::Icall(..) | RTLInst::Ibuiltin(..)
                );
                if needs_fallthrough {
                    if let Some(&next_node) = nodes_vec.get(i + 1) {
                        succs.entry(node).or_default().push(next_node);
                    }
                }
                match inst {
                    RTLInst::Ibranch(Either::Right(target)) => {
                        if !succs.contains_key(&node) {
                            if let Some(&dst) = nodes.range(*target..).next() {
                                succs.entry(node).or_default().push(dst);
                            }
                        }
                    }
                    _ => {}
                }
            }

            let mut preds: HashMap<Node, Vec<Node>> = HashMap::new();
            for (&src, dsts) in &succs {
                for &dst in dsts {
                    if nodes.contains(&dst) {
                        preds.entry(dst).or_default().push(src);
                    }
                }
            }

            let func_mem_call_uses: HashMap<Node, Vec<RTLReg>> = nodes.iter()
                .filter_map(|n| mem_call_addr_uses.get(n).map(|regs| (*n, regs.clone())))
                .collect();

            functions.insert(func_addr, FunctionCFG {
                func_addr,
                entry,
                nodes,
                inst: insts.clone(),
                succs,
                preds,
                params: func_params.remove(&func_addr).unwrap_or_default(),
                mem_call_addr_uses: func_mem_call_uses,
            });
        }

        PassContext { functions, var_types, inline_temps: HashSet::new() }
    }

    fn write_back(self, db: &mut DecompileDB) {
        let new_insts = ascent::boxcar::Vec::<(Node, RTLInst)>::new();
        let new_succs = ascent::boxcar::Vec::<(Node, Node)>::new();
        let mut live_regs: HashSet<RTLReg> = HashSet::new();

        // Sort succs: func.succs is HashMap, so unsorted pushes make rtl_next/rtl_succ nondeterministic.
        for (_func_addr, func) in &self.functions {
            for (&node, inst) in &func.inst {
                new_insts.push((node, inst.clone()));
                collect_inst_regs(inst, &mut live_regs);
            }
            let mut src_nodes: Vec<Node> = func.succs.keys().copied().collect();
            src_nodes.sort();
            for src in src_nodes {
                if !func.inst.contains_key(&src) { continue; }
                if let Some(dsts) = func.succs.get(&src) {
                    let mut sorted_dsts: Vec<Node> = dsts.clone();
                    sorted_dsts.sort();
                    for dst in sorted_dsts {
                        new_succs.push((src, dst));
                    }
                }
            }
        }

        let new_sdc = ascent::boxcar::Vec::<(RTLReg, Constant)>::new();
        for (_func_addr, func) in &self.functions {
            for (_, inst) in &func.inst {
                if let RTLInst::Iop(op, args, dst) = inst {
                    if args.is_empty() {
                        if let Some(cst) = crate::decompile::passes::cminor_pass::constant_from_operation(op) {
                            new_sdc.push((*dst, cst));
                        }
                    }
                }
            }
        }
        db.rel_set("single_def_const", new_sdc);

        db.rel_set("rtl_next", new_succs.clone());
        db.rel_set("rtl_inst", new_insts);
        db.rel_set("rtl_succ", new_succs);

        let inline_vec = ascent::boxcar::Vec::<RTLReg>::new();
        // Sort to keep emit_inline_temp deterministic across runs (inline_temps is a HashSet).
        let mut inline_sorted: Vec<RTLReg> = self.inline_temps.iter().copied().collect();
        inline_sorted.sort();
        for reg in inline_sorted {
            if live_regs.contains(&reg) {
                inline_vec.push(reg);
            }
        }
        db.rel_set("emit_inline_temp", inline_vec);
    }
}

pub(crate) fn collect_inst_regs(inst: &RTLInst, regs: &mut HashSet<RTLReg>) {
    match inst {
        RTLInst::Inop => {}
        RTLInst::Iop(_, args, dst) => {
            for &a in args.iter() { regs.insert(a); }
            regs.insert(*dst);
        }
        RTLInst::Iload(_, _, args, dst) => {
            for &a in args.iter() { regs.insert(a); }
            regs.insert(*dst);
        }
        RTLInst::Istore(_, _, args, src) => {
            for &a in args.iter() { regs.insert(a); }
            regs.insert(*src);
        }
        RTLInst::Icall(_, callee, args, dst, _) => {
            if let Either::Left(r) = callee { regs.insert(*r); }
            for &a in args.iter() { regs.insert(a); }
            if let Some(d) = dst { regs.insert(*d); }
        }
        RTLInst::Itailcall(_, callee, args) => {
            if let Either::Left(r) = callee { regs.insert(*r); }
            for &a in args.iter() { regs.insert(a); }
        }
        RTLInst::Ibuiltin(_, args, res) => {
            collect_builtin_arg_regs(args, regs);
            collect_single_builtin_arg_regs(res, regs);
        }
        RTLInst::Icond(_, args, _, _) => {
            for &a in args.iter() { regs.insert(a); }
        }
        RTLInst::Ijumptable(reg, _) => { regs.insert(*reg); }
        RTLInst::Ibranch(_) => {}
        RTLInst::Ireturn(reg) => { regs.insert(*reg); }
    }
}

fn collect_builtin_arg_regs(args: &[BuiltinArg<RTLReg>], regs: &mut HashSet<RTLReg>) {
    for arg in args {
        collect_single_builtin_arg_regs(arg, regs);
    }
}

fn collect_single_builtin_arg_regs(arg: &BuiltinArg<RTLReg>, regs: &mut HashSet<RTLReg>) {
    match arg {
        BuiltinArg::BA(r) => { regs.insert(*r); }
        BuiltinArg::BASplitLong(a, b) | BuiltinArg::BAAddPtr(a, b) => {
            collect_single_builtin_arg_regs(a, regs);
            collect_single_builtin_arg_regs(b, regs);
        }
        _ => {}
    }
}


pub(crate) struct DefUseInfo {
    node_def: HashMap<Node, RTLReg>,
    node_uses: HashMap<Node, Vec<RTLReg>>,
    defs: HashMap<RTLReg, Vec<Node>>,
    uses: HashMap<RTLReg, Vec<Node>>,
}

impl DefUseInfo {
    pub(crate) fn build(func: &FunctionCFG) -> Self {
        let mut node_def: HashMap<Node, RTLReg> = HashMap::new();
        let mut node_uses: HashMap<Node, Vec<RTLReg>> = HashMap::new();
        let mut defs: HashMap<RTLReg, Vec<Node>> = HashMap::new();
        let mut uses: HashMap<RTLReg, Vec<Node>> = HashMap::new();

        for (&node, inst) in &func.inst {
            let (def, mut used) = inst_def_use(inst);
            // A mem-indirect call uses the regs that form its target-load address (the Icall callee is only a synthetic temp); without these, DSE eliminates the producing vtable Iload and the call target collapses to an uninitialized var.
            if let Some(extra) = func.mem_call_addr_uses.get(&node) {
                for &r in extra {
                    if !used.contains(&r) {
                        used.push(r);
                    }
                }
            }
            if let Some(d) = def {
                node_def.insert(node, d);
                defs.entry(d).or_default().push(node);
            }
            node_uses.insert(node, used.clone());
            for u in used {
                uses.entry(u).or_default().push(node);
            }
        }

        DefUseInfo { node_def, node_uses, defs, uses }
    }
}

pub(crate) fn inst_def_use(inst: &RTLInst) -> (Option<RTLReg>, Vec<RTLReg>) {
    match inst {
        RTLInst::Inop => (None, vec![]),
        RTLInst::Iop(_, args, dst) => (Some(*dst), args.iter().copied().collect()),
        RTLInst::Iload(_, _, args, dst) => (Some(*dst), args.iter().copied().collect()),
        RTLInst::Istore(_, _, args, src) => {
            let mut used: Vec<RTLReg> = args.iter().copied().collect();
            used.push(*src);
            (None, used)
        }
        RTLInst::Icall(_, callee, args, dst, _) => {
            let mut used: Vec<RTLReg> = args.iter().copied().collect();
            if let Either::Left(r) = callee { used.push(*r); }
            (dst.as_ref().copied(), used)
        }
        RTLInst::Itailcall(_, callee, args) => {
            let mut used: Vec<RTLReg> = args.iter().copied().collect();
            if let Either::Left(r) = callee { used.push(*r); }
            (None, used)
        }
        RTLInst::Ibuiltin(_, args, res) => {
            let mut used = Vec::new();
            for a in args { collect_ba_uses(a, &mut used); }
            let def = match res {
                BuiltinArg::BA(r) => Some(*r),
                _ => None,
            };
            (def, used)
        }
        RTLInst::Icond(_, args, _, _) => (None, args.iter().copied().collect()),
        RTLInst::Ijumptable(reg, _) => (None, vec![*reg]),
        RTLInst::Ibranch(_) => (None, vec![]),
        RTLInst::Ireturn(reg) => (None, vec![*reg]),
    }
}

fn collect_ba_uses(arg: &BuiltinArg<RTLReg>, out: &mut Vec<RTLReg>) {
    match arg {
        BuiltinArg::BA(r) => out.push(*r),
        BuiltinArg::BASplitLong(a, b) | BuiltinArg::BAAddPtr(a, b) => {
            collect_ba_uses(a, out);
            collect_ba_uses(b, out);
        }
        _ => {}
    }
}


pub(crate) struct LivenessInfo {
    pub(crate) live_in: HashMap<Node, HashSet<RTLReg>>,
    pub(crate) live_out: HashMap<Node, HashSet<RTLReg>>,
}

impl LivenessInfo {
    pub(crate) fn build(func: &FunctionCFG, du: &DefUseInfo) -> Self {
        let mut live_in: HashMap<Node, HashSet<RTLReg>> = HashMap::new();
        let mut live_out: HashMap<Node, HashSet<RTLReg>> = HashMap::new();

        for &node in &func.nodes {
            live_in.insert(node, HashSet::new());
            live_out.insert(node, HashSet::new());
        }

        let mut worklist: VecDeque<Node> = func.nodes.iter().copied().collect();
        let mut in_worklist: HashSet<Node> = func.nodes.iter().copied().collect();

        while let Some(node) = worklist.pop_front() {
            in_worklist.remove(&node);

            let mut new_out = HashSet::new();
            if let Some(succs) = func.succs.get(&node) {
                for &s in succs {
                    if let Some(s_in) = live_in.get(&s) {
                        new_out.extend(s_in);
                    }
                }
            }

            let mut new_in = new_out.clone();
            if let Some(&def) = du.node_def.get(&node) {
                new_in.remove(&def);
            }
            if let Some(used) = du.node_uses.get(&node) {
                for &u in used {
                    new_in.insert(u);
                }
            }

            let old_in = match live_in.get(&node) {
                Some(li) => li,
                None => continue,
            };
            if &new_in != old_in {
                live_in.insert(node, new_in);
                live_out.insert(node, new_out);
                if let Some(preds) = func.preds.get(&node) {
                    for &p in preds {
                        if func.nodes.contains(&p) && in_worklist.insert(p) {
                            worklist.push_back(p);
                        }
                    }
                }
            } else if live_out.get(&node).map_or(true, |o| o != &new_out) {
                live_out.insert(node, new_out);
            }
        }

        LivenessInfo { live_in, live_out }
    }
}


fn reachable_from(func: &FunctionCFG, node: Node) -> HashSet<Node> {
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    if let Some(succs) = func.succs.get(&node) {
        for &s in succs {
            if visited.insert(s) {
                queue.push_back(s);
            }
        }
    }
    while let Some(n) = queue.pop_front() {
        if let Some(succs) = func.succs.get(&n) {
            for &s in succs {
                if visited.insert(s) {
                    queue.push_back(s);
                }
            }
        }
    }
    visited
}

fn src_not_redefined_on_paths_to_uses(
    func: &FunctionCFG,
    du: &DefUseInfo,
    copy_node: Node,
    src: RTLReg,
    dst_uses: &[Node],
) -> bool {
    let src_def_nodes = match du.defs.get(&src) {
        Some(defs) => defs,
        None => return true,
    };

    let redefs: Vec<Node> = src_def_nodes.iter()
        .filter(|&&n| n != copy_node)
        .copied()
        .collect();
    if redefs.is_empty() {
        return true;
    }

    let forward = reachable_from(func, copy_node);

    let reachable_redefs: Vec<Node> = redefs.iter()
        .filter(|n| forward.contains(n))
        .copied()
        .collect();
    if reachable_redefs.is_empty() {
        return true;
    }

    let mut backward = HashSet::new();
    let mut queue = VecDeque::new();
    for &u in dst_uses {
        if backward.insert(u) {
            queue.push_back(u);
        }
    }
    while let Some(node) = queue.pop_front() {
        if let Some(preds) = func.preds.get(&node) {
            for &p in preds {
                if backward.insert(p) {
                    queue.push_back(p);
                }
            }
        }
    }

    !reachable_redefs.iter().any(|n| backward.contains(n))
}

// True for an integer equality/inequality comparison, where `cmp x, x` is statically known (equal -> Ceq true / Cne false) regardless of value; ordered comparisons (Clt/Cle/Cgt/Cge) and float comparisons are excluded so only provably-determined branches fold.
fn const_eq_branch_taken(cond: &Condition) -> Option<bool> {
    match cond {
        Condition::Ccomp(c) | Condition::Ccompu(c)
        | Condition::Ccompl(c) | Condition::Ccomplu(c) => match c {
            Comparison::Ceq => Some(true),
            Comparison::Cne => Some(false),
            _ => None,
        },
        _ => None,
    }
}

// Constant-fold a two-register conditional branch whose operands provably hold the SAME value, then drop the now-unreachable nodes: CRT stubs (deregister_tm_clones) compare two LEAs of the same global with `je`, so the statically-taken branch leaves the fall-through tail (and its undefined-return-value load) dead. Operands are equal only when the same register or both the identical 0-arg constant (`single_def_const`, e.g. same Oaddrsymbol), never firing for genuine runtime compares. Returns true if a branch was folded.
fn fold_static_eq_branches(func: &mut FunctionCFG) -> bool {
    let mut const_of: HashMap<RTLReg, Constant> = HashMap::new();
    for inst in func.inst.values() {
        if let RTLInst::Iop(op, args, dst) = inst {
            if args.is_empty() {
                if let Some(cst) = crate::decompile::passes::cminor_pass::constant_from_operation(op) {
                    const_of.insert(*dst, cst);
                }
            }
        }
    }

    let mut folds: Vec<(Node, Node, Node)> = Vec::new();
    for (&node, inst) in &func.inst {
        if let RTLInst::Icond(cond, args, Either::Right(ifso), Either::Right(ifnot)) = inst {
            if args.len() != 2 {
                continue;
            }
            let same_value = args[0] == args[1]
                || matches!((const_of.get(&args[0]), const_of.get(&args[1])),
                    (Some(a), Some(b)) if a == b);
            if !same_value {
                continue;
            }
            match const_eq_branch_taken(cond) {
                Some(true) => folds.push((node, *ifso, *ifnot)),
                Some(false) => folds.push((node, *ifnot, *ifso)),
                None => {}
            }
        }
    }
    if folds.is_empty() {
        return false;
    }

    for &(node, taken, _dead) in &folds {
        func.inst.insert(node, RTLInst::Ibranch(Either::Right(taken)));
        func.succs.insert(node, vec![taken]);
    }

    // Recompute reachability from entry and drop now-unreachable nodes so the dead tail and its bogus return-value load cannot surface downstream.
    let mut reachable: HashSet<Node> = HashSet::new();
    let mut stack = vec![func.entry];
    reachable.insert(func.entry);
    while let Some(n) = stack.pop() {
        if let Some(succs) = func.succs.get(&n) {
            for &s in succs {
                if func.inst.contains_key(&s) && reachable.insert(s) {
                    stack.push(s);
                }
            }
        }
    }

    func.nodes.retain(|n| reachable.contains(n));
    func.inst.retain(|n, _| reachable.contains(n));
    func.succs.retain(|n, _| reachable.contains(n));
    for dsts in func.succs.values_mut() {
        dsts.retain(|d| reachable.contains(d));
    }
    let mut new_preds: HashMap<Node, Vec<Node>> = HashMap::new();
    for (&src, dsts) in &func.succs {
        for &dst in dsts {
            new_preds.entry(dst).or_default().push(src);
        }
    }
    func.preds = new_preds;
    true
}

pub(crate) fn self_zero_rewrite(func: &mut FunctionCFG) -> usize {
    let mut count = 0;
    for (_node, inst) in func.inst.iter_mut() {
        let rewrite = match inst {
            RTLInst::Iop(op, args, dst) if args.len() == 2 && args[0] == args[1] => {
                match op {
                    Operation::Oxor | Operation::Osub => {
                        Some(RTLInst::Iop(Operation::Ointconst(0), Arc::new(vec![]), *dst))
                    }
                    Operation::Oxorl | Operation::Osubl => {
                        Some(RTLInst::Iop(Operation::Olongconst(0), Arc::new(vec![]), *dst))
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        if let Some(new_inst) = rewrite {
            *inst = new_inst;
            count += 1;
        }
    }
    count
}

pub(crate) fn copy_propagation(
    func: &mut FunctionCFG,
    du: &DefUseInfo,
    _liveness: &LivenessInfo,
) -> (usize, HashMap<RTLReg, RTLReg>) {
    let mut candidates: Vec<(Node, RTLReg, RTLReg)> = Vec::new();

    for (&node, inst) in &func.inst {
        if let RTLInst::Iop(Operation::Omove, args, dst) = inst {
            if args.len() == 1 && args[0] != *dst {
                let src = args[0];
                candidates.push((node, src, *dst));
            }
        }
    }

    let mut subst: HashMap<RTLReg, RTLReg> = HashMap::new();
    let mut dead_nodes: HashSet<Node> = HashSet::new();

    for (copy_node, src, dst) in &candidates {
        let src = *src;
        let dst = *dst;

        if func.params.contains(&dst) {
            continue;
        }

        let dst_defs = du.defs.get(&dst).map_or(0, |d| d.len());
        if dst_defs != 1 {
            continue;
        }

        let dst_uses = match du.uses.get(&dst) {
            Some(u) => u,
            None => {
                continue;
            }
        };

        let mut safe = true;
        for &use_node in dst_uses {
            if use_node == *copy_node {
                safe = false;
                break;
            }
        }
        if !safe { continue; }

        let reachable = reachable_from(func, *copy_node);
        for &use_node in dst_uses {
            if !reachable.contains(&use_node) {
                safe = false;
                break;
            }
        }
        if !safe { continue; }

        safe = src_not_redefined_on_paths_to_uses(func, du, *copy_node, src, dst_uses);

        if safe {
            subst.insert(dst, src);
            dead_nodes.insert(*copy_node);
        }
    }

    if subst.is_empty() {
        return (0, HashMap::new());
    }

    let mut resolved: HashMap<RTLReg, RTLReg> = HashMap::new();
    for (&dst, &src) in &subst {
        let mut target = src;
        let mut visited = HashSet::new();
        visited.insert(dst);
        while let Some(&next) = subst.get(&target) {
            if !visited.insert(next) {
                break;
            }
            target = next;
        }
        resolved.insert(dst, target);
    }

    let count = resolved.len();

    for (&node, inst) in func.inst.iter_mut() {
        if dead_nodes.contains(&node) {
            continue;
        }
        *inst = subst_in_inst(inst, &resolved);
    }

    for &node in &dead_nodes {
        if let Some(inst) = func.inst.get_mut(&node) {
            *inst = RTLInst::Inop;
        }
    }

    (count, resolved)
}

pub(crate) fn subst_in_inst(inst: &RTLInst, map: &HashMap<RTLReg, RTLReg>) -> RTLInst {
    match inst {
        RTLInst::Inop => RTLInst::Inop,
        RTLInst::Iop(op, args, dst) => {
            let new_args = subst_args(args, map);
            RTLInst::Iop(op.clone(), new_args, *dst)
        }
        RTLInst::Iload(chunk, addr, args, dst) => {
            let new_args = subst_args(args, map);
            RTLInst::Iload(*chunk, addr.clone(), new_args, *dst)
        }
        RTLInst::Istore(chunk, addr, args, src) => {
            let new_args = subst_args(args, map);
            let new_src = map.get(src).copied().unwrap_or(*src);
            RTLInst::Istore(*chunk, addr.clone(), new_args, new_src)
        }
        RTLInst::Icall(sig, callee, args, dst, next) => {
            let new_callee = match callee {
                Either::Left(r) => Either::Left(map.get(r).copied().unwrap_or(*r)),
                other => other.clone(),
            };
            let new_args = subst_args(args, map);
            RTLInst::Icall(sig.clone(), new_callee, new_args, *dst, *next)
        }
        RTLInst::Itailcall(sig, callee, args) => {
            let new_callee = match callee {
                Either::Left(r) => Either::Left(map.get(r).copied().unwrap_or(*r)),
                other => other.clone(),
            };
            let new_args = subst_args(args, map);
            RTLInst::Itailcall(sig.clone(), new_callee, new_args)
        }
        RTLInst::Ibuiltin(name, args, res) => {
            let new_args: Vec<_> = args.iter().map(|a| subst_ba(a, map)).collect();
            RTLInst::Ibuiltin(name.clone(), new_args, res.clone())
        }
        RTLInst::Icond(cond, args, ifso, ifnot) => {
            let new_args = subst_args(args, map);
            RTLInst::Icond(cond.clone(), new_args, ifso.clone(), ifnot.clone())
        }
        RTLInst::Ijumptable(reg, targets) => {
            let new_reg = map.get(reg).copied().unwrap_or(*reg);
            RTLInst::Ijumptable(new_reg, targets.clone())
        }
        RTLInst::Ibranch(target) => RTLInst::Ibranch(target.clone()),
        RTLInst::Ireturn(reg) => {
            let new_reg = map.get(reg).copied().unwrap_or(*reg);
            RTLInst::Ireturn(new_reg)
        }
    }
}

pub(crate) fn subst_args(args: &Args, map: &HashMap<RTLReg, RTLReg>) -> Args {
    Arc::new(args.iter().map(|r| map.get(r).copied().unwrap_or(*r)).collect())
}

pub(crate) fn subst_ba(ba: &BuiltinArg<RTLReg>, map: &HashMap<RTLReg, RTLReg>) -> BuiltinArg<RTLReg> {
    match ba {
        BuiltinArg::BA(r) => BuiltinArg::BA(map.get(r).copied().unwrap_or(*r)),
        BuiltinArg::BASplitLong(a, b) => BuiltinArg::BASplitLong(
            Box::new(subst_ba(a, map)),
            Box::new(subst_ba(b, map)),
        ),
        BuiltinArg::BAAddPtr(a, b) => BuiltinArg::BAAddPtr(
            Box::new(subst_ba(a, map)),
            Box::new(subst_ba(b, map)),
        ),
        other => other.clone(),
    }
}


pub(crate) fn dead_store_elimination(
    func: &mut FunctionCFG,
    du: &DefUseInfo,
    liveness: &LivenessInfo,
) -> usize {
    let mut count = 0;

    let dead_nodes: Vec<Node> = func.inst.iter()
        .filter_map(|(&node, inst)| {
            let def_reg = du.node_def.get(&node)?;

            if func.params.contains(def_reg) {
                return None;
            }

            let live_out = liveness.live_out.get(&node)?;
            if live_out.contains(def_reg) {
                return None;
            }

            match inst {
                RTLInst::Iop(_, _, _) => Some(node),
                RTLInst::Iload(_, _, _, _) => Some(node),
                _ => None,
            }
        })
        .collect();

    for node in &dead_nodes {
        if let Some(inst) = func.inst.get_mut(node) {
            *inst = RTLInst::Inop;
            count += 1;
        }
    }

    let dead_call_nodes: Vec<Node> = func.inst.iter()
        .filter_map(|(&node, inst)| {
            if let RTLInst::Icall(_, _, _, Some(dst), _) = inst {
                if func.params.contains(dst) {
                    return None;
                }
                let live_out = liveness.live_out.get(&node)?;
                if !live_out.contains(dst) {
                    return Some(node);
                }
            }
            None
        })
        .collect();

    for node in dead_call_nodes {
        if let Some(RTLInst::Icall(sig, callee, args, _, next)) = func.inst.get(&node).cloned() {
            func.inst.insert(node, RTLInst::Icall(sig, callee, args, None, next));
            count += 1;
        }
    }

    count
}


pub(crate) fn nop_collapse(func: &mut FunctionCFG) -> usize {
    let nop_nodes: Vec<Node> = func.inst.iter()
        .filter(|(&node, inst)| {
            matches!(inst, RTLInst::Inop) && node != func.entry
        })
        .map(|(&node, _)| node)
        .collect();

    if nop_nodes.is_empty() {
        return 0;
    }

    let nop_set: HashSet<Node> = nop_nodes.iter().copied().collect();

    let mut nop_target: HashMap<Node, Node> = HashMap::new();
    for &nop in &nop_nodes {
        let mut target = nop;
        let mut visited = HashSet::new();
        visited.insert(nop);
        loop {
            let succs = func.succs.get(&target);
            match succs.and_then(|s| if s.len() == 1 { Some(s[0]) } else { None }) {
                Some(next) if nop_set.contains(&next) && visited.insert(next) => {
                    target = next;
                }
                Some(next) if nop_set.contains(&next) => {
                    break;
                }
                Some(next) => {
                    nop_target.insert(nop, next);
                    break;
                }
                None => {
                    break;
                }
            }
        }
    }

    if nop_target.is_empty() {
        return 0;
    }

    let mut count = 0;

    for (&_pred, succs) in func.succs.iter_mut() {
        for succ in succs.iter_mut() {
            if let Some(&target) = nop_target.get(succ) {
                *succ = target;
            }
        }
    }

    for inst in func.inst.values_mut() {
        retarget_inst(inst, &nop_target);
    }

    for (&nop, _) in &nop_target {
        func.inst.remove(&nop);
        func.succs.remove(&nop);
        func.nodes.remove(&nop);
        count += 1;
    }

    loop {
        if !matches!(func.inst.get(&func.entry), Some(RTLInst::Inop)) {
            break;
        }
        let succs = func.succs.get(&func.entry);
        match succs.and_then(|s| if s.len() == 1 { Some(s[0]) } else { None }) {
            Some(target) if target != func.entry => {
                let old_entry = func.entry;
                func.entry = target;
                func.inst.remove(&old_entry);
                func.succs.remove(&old_entry);
                func.nodes.remove(&old_entry);
                count += 1;
            }
            _ => break,
        }
    }

    let mut preds: HashMap<Node, Vec<Node>> = HashMap::new();
    for (&src, dsts) in &func.succs {
        if func.inst.contains_key(&src) {
            for &dst in dsts {
                preds.entry(dst).or_default().push(src);
            }
        }
    }
    func.preds = preds;

    count
}

fn retarget_inst(inst: &mut RTLInst, nop_target: &HashMap<Node, Node>) {
    match inst {
        RTLInst::Icond(_, _, ifso, ifnot) => {
            retarget_either(ifso, nop_target);
            retarget_either(ifnot, nop_target);
        }
        RTLInst::Ibranch(target) => {
            retarget_either(target, nop_target);
        }
        RTLInst::Icall(_, _, _, _, next) => {
            if let Some(&target) = nop_target.get(next) {
                *next = target;
            }
        }
        RTLInst::Ijumptable(_, targets) => {
            let new_targets: Vec<Node> = targets.iter()
                .map(|n| nop_target.get(n).copied().unwrap_or(*n))
                .collect();
            if new_targets != **targets {
                *targets = Arc::new(new_targets);
            }
        }
        _ => {}
    }
}

pub(crate) fn retarget_either(target: &mut Either<Symbol, Node>, nop_target: &HashMap<Node, Node>) {
    if let Either::Right(node) = target {
        if let Some(&new_node) = nop_target.get(node) {
            *node = new_node;
        }
    }
}


pub(crate) fn find_inline_temps(
    func: &FunctionCFG,
    du: &DefUseInfo,
    liveness: &LivenessInfo,
) -> HashSet<RTLReg> {
    let mut result = HashSet::new();

    for (&reg, def_nodes) in &du.defs {
        if def_nodes.len() != 1 { continue; }
        let def_node = def_nodes[0];

        let use_node = match du.uses.get(&reg) {
            Some(u) => {
                let mut distinct: Vec<Node> = u.clone();
                distinct.sort_unstable();
                distinct.dedup();
                if distinct.len() != 1 { continue; }
                distinct[0]
            }
            _ => continue,
        };

        if func.params.contains(&reg) { continue; }

        let inst = match func.inst.get(&def_node) {
            Some(i) => i,
            None => continue,
        };
        // Only inline Iop temps; Iload is unsafe without aliasing/intervening store checks.
        let def_args: Vec<RTLReg> = match inst {
            RTLInst::Iop(_, args, _) => args.iter().copied().collect(),
            _ => continue,
        };

        let use_live_in = match liveness.live_in.get(&use_node) {
            Some(li) => li,
            None => continue,
        };
        if !def_args.iter().all(|a| use_live_in.contains(a)) {
            continue;
        }

        let reachable = reachable_from(func, def_node);
        if !reachable.contains(&use_node) {
            continue;
        }

        result.insert(reg);
    }

    result
}
