// RTLOptimizePass: imperative finalization of RTL candidates (disambiguation, copy-prop, DSE, nop collapse, inline-temp discovery), split out so the RTL pass proper stays pure Ascent.

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::util::{SYNTH_NODE_BIT, SYNTH_NODE_BIT2};
use crate::x86::op::{Comparison, Condition, Operation};
use crate::x86::types::*;
use ascent::{ascent, lattice::set::Set, Dual};
use either::Either;
use log::info;
use rayon::prelude::*;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::sync::Arc;

fn unique_external_cfg_entry(
    region_nodes: &HashSet<Node>,
    cfg_edges: &[(Node, Node)],
) -> Option<Node> {
    let entries: HashSet<Node> = cfg_edges
        .iter()
        .filter_map(|&(src, dst)| {
            (region_nodes.contains(&dst) && !region_nodes.contains(&src)).then_some(dst)
        })
        .collect();
    (entries.len() == 1).then(|| *entries.iter().next().unwrap())
}

// Resolve a raw instruction address to the first semantic RTL node reached by
// the explicit instruction-next chain, without crossing a function boundary.
// The cache is point-keyed: each skipped address is visited at most once per
// function, and no node-id ordering is used as a proxy for control flow.
fn resolve_next_semantic_node(
    func: Address,
    start: Node,
    semantic_nodes: &BTreeSet<Node>,
    raw_next: &HashMap<Node, Vec<Node>>,
    node_owners: &HashMap<Node, BTreeSet<Address>>,
    cache: &mut HashMap<Node, Option<Node>>,
) -> Option<Node> {
    if semantic_nodes.contains(&start) {
        return Some(start);
    }
    if let Some(cached) = cache.get(&start) {
        return *cached;
    }

    let owned_by_func = |node: Node| {
        node_owners
            .get(&node)
            .is_some_and(|owners| owners.contains(&func))
    };

    let mut path = Vec::new();
    let mut visited = HashSet::new();
    let mut current = start;
    let resolved = loop {
        if semantic_nodes.contains(&current) {
            break Some(current);
        }
        if let Some(cached) = cache.get(&current) {
            break *cached;
        }
        if !owned_by_func(current) || !visited.insert(current) {
            break None;
        }
        path.push(current);

        let Some(nexts) = raw_next.get(&current) else {
            break None;
        };
        if nexts.len() != 1 {
            break None;
        }
        let next = nexts[0];
        if !owned_by_func(next) {
            break None;
        }
        current = next;
    };

    for node in path {
        cache.insert(node, resolved);
    }
    resolved
}

#[cfg(debug_assertions)]
use ascent::ascent_par;

/// A fact that remains valid at a CFG point only when every path from the
/// function entry to that point has passed its introduction without a
/// relevant redefinition.  Keeping these facts inside one point-keyed lattice
/// avoids materializing node-to-node reachability.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum RtlAvailableFact {
    Copy {
        intro: Node,
        src: RTLReg,
        dst: RTLReg,
    },
    InlineExpr {
        intro: Node,
        dst: RTLReg,
        args: Vec<RTLReg>,
    },
}

/// Forward must-availability transfer. Definitions kill facts that depend on
/// the defined register, then unions the current node's precomputed queried
/// introductions for successors. The enclosing `Dual<Set<_>>` intersects
/// predecessor states, so a fact is absent after any bypass or redefining
/// branch and at a first-iteration loop read that precedes its definition.
fn rtl_availability_transfer(
    available: &Set<RtlAvailableFact>,
    inst: &RTLInst,
    introductions: &Set<RtlAvailableFact>,
) -> Set<RtlAvailableFact> {
    let defined = inst_def_use(inst).0;
    let mut out: BTreeSet<RtlAvailableFact> = available
        .iter()
        .filter(|fact| match fact {
            RtlAvailableFact::Copy { src, dst, .. } => {
                defined.map_or(true, |reg| reg != *src && reg != *dst)
            }
            RtlAvailableFact::InlineExpr { dst, args, .. } => {
                defined.map_or(true, |reg| reg != *dst && !args.contains(&reg))
            }
        })
        .cloned()
        .collect();
    out.extend(introductions.iter().cloned());
    Set(out)
}

fn rtl_copy_available(
    available: &Set<RtlAvailableFact>,
    intro: Node,
    src: RTLReg,
    dst: RTLReg,
) -> bool {
    available.contains(&RtlAvailableFact::Copy { intro, src, dst })
}

fn rtl_inline_expr_available(available: &Set<RtlAvailableFact>, intro: Node, dst: RTLReg) -> bool {
    available.iter().any(|fact| {
        matches!(
            fact,
            RtlAvailableFact::InlineExpr {
                intro: fact_intro,
                dst: fact_dst,
                ..
            } if *fact_intro == intro && *fact_dst == dst
        )
    })
}

fn rtl_copy_clobbered_at_use(inst: &RTLInst, src: RTLReg, dst: RTLReg) -> bool {
    inst_def_use(inst)
        .0
        .map_or(false, |defined| defined == src || defined == dst)
}

fn rtl_inline_expr_clobbered_at_use(def_inst: &RTLInst, use_inst: &RTLInst, dst: RTLReg) -> bool {
    let Some(defined) = inst_def_use(use_inst).0 else {
        return false;
    };
    match def_inst {
        RTLInst::Iop(_, args, _) => defined == dst || args.contains(&defined),
        _ => true,
    }
}

/// Small production dataflow used by both imperative RTL optimizer consumers.
/// Reachability is represented only by the point-keyed lattice; the output
/// relations materialize queried def/use failures, never all node pairs.
ascent! {
    struct RtlAvailabilityProgram;

    relation rtl_avail_inst(Node, RTLInst);
    // Exactly one row per instruction node. The set is empty when this
    // invocation has no queried fact introduced at that node.
    relation rtl_intro_facts(Node, Set<RtlAvailableFact>);
    relation rtl_avail_succ(Node, Node);
    relation rtl_avail_entry(Node);
    relation copy_query(Node, RTLReg, RTLReg, Node); // (intro, src, dst, use)
    relation inline_query(Node, RTLReg, Node); // (intro, dst, use)

    #[local] lattice rtl_available_in(Node, Dual<Set<RtlAvailableFact>>);
    #[local] relation rtl_available_node(Node);

    rtl_available_in(*entry, Dual(Set::default())) <-- rtl_avail_entry(entry);

    rtl_available_in(*dst, Dual(rtl_availability_transfer(&available.0, inst, introductions))) <--
        rtl_avail_succ(src, dst),
        rtl_available_in(src, available),
        rtl_avail_inst(src, inst),
        rtl_intro_facts(src, introductions);

    // Unknown nodes conservatively kill the full availability state.
    rtl_available_in(*dst, Dual(Set::default())) <--
        rtl_avail_succ(src, dst),
        rtl_available_in(src, _),
        !rtl_avail_inst(src, _);

    rtl_available_node(*node) <-- rtl_available_in(node, _);

    relation copy_unavailable(Node, Node); // (intro, use)
    copy_unavailable(*intro, *use_node) <--
        copy_query(intro, src, dst, use_node),
        rtl_available_in(use_node, available),
        if !rtl_copy_available(&available.0, *intro, *src, *dst);
    copy_unavailable(*intro, *use_node) <--
        copy_query(intro, _, _, use_node),
        !rtl_available_node(use_node);
    copy_unavailable(*intro, *use_node) <--
        copy_query(intro, _, _, use_node),
        if intro == use_node;
    copy_unavailable(*intro, *use_node) <--
        copy_query(intro, src, dst, use_node),
        rtl_avail_inst(use_node, inst),
        if rtl_copy_clobbered_at_use(inst, *src, *dst);

    relation inline_unavailable(Node, Node); // (intro, use)
    inline_unavailable(*intro, *use_node) <--
        inline_query(intro, dst, use_node),
        rtl_available_in(use_node, available),
        if !rtl_inline_expr_available(&available.0, *intro, *dst);
    inline_unavailable(*intro, *use_node) <--
        inline_query(intro, _, use_node),
        !rtl_available_node(use_node);
    inline_unavailable(*intro, *use_node) <--
        inline_query(intro, _, use_node),
        if intro == use_node;
    inline_unavailable(*intro, *use_node) <--
        inline_query(intro, dst, use_node),
        rtl_avail_inst(intro, def_inst),
        rtl_avail_inst(use_node, use_inst),
        if rtl_inline_expr_clobbered_at_use(def_inst, use_inst, *dst);
}

#[derive(Default)]
struct RtlAvailabilityInfo {
    copy_unavailable: BTreeSet<(Node, Node)>,
    inline_unavailable: BTreeSet<(Node, Node)>,
}

#[derive(Clone, Copy)]
enum RtlAvailabilityMode {
    Copies,
    InlineExprs,
    Both,
}

impl RtlAvailabilityMode {
    fn copies(self) -> bool {
        matches!(self, Self::Copies | Self::Both)
    }

    fn inline_exprs(self) -> bool {
        matches!(self, Self::InlineExprs | Self::Both)
    }
}

impl RtlAvailabilityInfo {
    fn copy_is_available(&self, intro: Node, use_node: Node) -> bool {
        !self.copy_unavailable.contains(&(intro, use_node))
    }

    fn inline_is_available(&self, intro: Node, use_node: Node) -> bool {
        !self.inline_unavailable.contains(&(intro, use_node))
    }
}

fn analyze_rtl_availability(
    func: &FunctionCFG,
    du: &DefUseInfo,
    mode: RtlAvailabilityMode,
) -> RtlAvailabilityInfo {
    let mut program = RtlAvailabilityProgram::default();
    for (&node, inst) in &func.inst {
        program.rtl_avail_inst.push((node, inst.clone()));
        let mut introductions = BTreeSet::new();
        if let RTLInst::Iop(op, args, dst) = inst {
            if mode.copies() && *op == Operation::Omove && args.len() == 1 && args[0] != *dst {
                if let Some(uses) = du.uses.get(dst) {
                    introductions.insert(RtlAvailableFact::Copy {
                        intro: node,
                        src: args[0],
                        dst: *dst,
                    });
                    for &use_node in uses {
                        program.copy_query.push((node, args[0], *dst, use_node));
                    }
                }
            }
            if mode.inline_exprs() {
                if let Some(uses) = du.uses.get(dst) {
                    introductions.insert(RtlAvailableFact::InlineExpr {
                        intro: node,
                        dst: *dst,
                        args: args.iter().copied().collect(),
                    });
                    for &use_node in uses {
                        program.inline_query.push((node, *dst, use_node));
                    }
                }
            }
        }
        program.rtl_intro_facts.push((node, Set(introductions)));
    }
    for (&src, dsts) in &func.succs {
        for &dst in dsts {
            program.rtl_avail_succ.push((src, dst));
        }
    }
    program.rtl_avail_entry.push((func.entry,));
    program.run();
    RtlAvailabilityInfo {
        copy_unavailable: program.copy_unavailable.iter().copied().collect(),
        inline_unavailable: program.inline_unavailable.iter().copied().collect(),
    }
}

// Declarative RTL optimizer; _v2 outputs are diffed against the imperative results (debug-only: excluded entirely in release builds where nothing reads them).
#[cfg(debug_assertions)]
ascent_par! {
    #![measure_rule_times]

    pub struct RTLOptimizerProgram;

    // Seeded inputs.
    relation rtl_opt_inst(Node, RTLInst);
    relation rtl_opt_succ(Node, Node);
    relation rtl_opt_func(Node, Address);
    relation rtl_opt_shared(Node);
    relation rtl_opt_param(Address, RTLReg);
    // Mem-indirect call target-load address regs (call node -> address reg), seeded from FunctionCFG::mem_call_addr_uses so the v2 mirror matches the imperative def/use model.
    relation rtl_opt_mem_call_use(Node, RTLReg);
    // Exact queried def/use failures from the production point-keyed lattice.
    relation rtl_opt_copy_unavailable(Node, Node);
    relation rtl_opt_inline_unavailable(Node, Node);

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

    // Single-definition counting.
    #[local] relation reg_def_count(Address, RTLReg, usize);

    reg_def_count(func, r, count) <--
        rtl_def(func, _, r),
        agg count = ascent::aggregators::count() in rtl_def(func, _, r);

    // Self-zero-rewrite: xor r,r or sub r,r where args == dst.
    relation self_zero_v2(Node);
    self_zero_v2(*node) <--
        rtl_opt_inst(node, ?RTLInst::Iop(op, args, dst)),
        !rtl_opt_shared(node),
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

    // Every dst use must have the exact copy fact available.  This rejects an
    // unreachable use, an entry-to-use path bypassing the copy, and any path
    // that redefines src/dst before the use.
    #[local] relation copy_use_uncovered(Address, Node, RTLReg); // (func, copy_node, dst)
    copy_use_uncovered(func, *copy_node, *dst) <--
        copy_candidate(func, copy_node, _, dst),
        rtl_use(func, use_node, dst),
        rtl_opt_copy_unavailable(copy_node, use_node);

    // Unsafe: a use equal to the copy_node itself (dst uses itself at its own def).
    #[local] relation dst_self_use(Address, Node, RTLReg);
    dst_self_use(func, node, *dst) <--
        copy_candidate(func, node, _, dst),
        rtl_use(func, node, dst);

    // At least one use of dst exists
    #[local] relation dst_has_use(Address, Node, RTLReg);
    dst_has_use(func, node, *dst) <--
        copy_candidate(func, node, _, dst),
        rtl_use(func, _, dst);

    // A private copy cannot be propagated into a physical shared node: the
    // other owner contexts may have different reaching definitions.
    #[local] relation copy_use_shared(Address, Node, RTLReg);
    copy_use_shared(func, *copy_node, *dst) <--
        copy_candidate(func, copy_node, _, dst),
        rtl_use(func, use_node, dst),
        rtl_opt_shared(use_node);

    // Final substitution: dst -> src
    relation copy_subst_v2(RTLReg, RTLReg);
    // Copy-eliminated node (replace with Inop)
    relation copy_eliminated_v2(Node);

    copy_subst_v2(*dst, *src), copy_eliminated_v2(*copy_node) <--
        copy_candidate(func, copy_node, src, dst),
        !rtl_opt_shared(copy_node),
        !rtl_opt_param(func, dst),
        !rtl_opt_mem_call_use(_, dst),
        dst_single_def_at(func, copy_node, dst),
        dst_has_use(func, copy_node, dst),
        !dst_self_use(func, copy_node, dst),
        !copy_use_shared(func, copy_node, dst),
        !copy_use_uncovered(func, copy_node, dst);

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
        !rtl_opt_shared(node),
        !rtl_opt_param(func, reg),
        !live_out(node, reg),
        rtl_opt_inst(node, inst),
        if matches!(inst, RTLInst::Iop(_,_,_) | RTLInst::Iload(_,_,_,_));

    // Dead call dst: Icall with dst not live-out; drop the dst, keep the call.
    relation dead_call_dst_v2(Node);
    dead_call_dst_v2(*node) <--
        rtl_opt_func(node, func),
        rtl_opt_inst(node, ?RTLInst::Icall(_, _, _, Some(dst), _)),
        !rtl_opt_shared(node),
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
        !rtl_opt_shared(def_node),
        !rtl_opt_param(func, reg),
        rtl_opt_inst(def_node, ?RTLInst::Iop(_, _, _));

    #[local] relation inline_temp_use(Address, RTLReg, Node);
    inline_temp_use(func, *reg, *use_node) <--
        reg_distinct_uses(func, reg, 1),
        rtl_use(func, use_node, reg),
        !rtl_opt_shared(use_node);

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

    #[local] relation inline_temp_unavailable(Address, RTLReg);
    inline_temp_unavailable(func, *reg) <--
        inline_temp_def(func, reg, def_node),
        inline_temp_use(func, reg, use_node),
        rtl_opt_inline_unavailable(def_node, use_node);

    relation inline_temp_v2(RTLReg);
    inline_temp_v2(*reg) <--
        inline_temp_def(func, reg, _),
        inline_temp_use(func, reg, _),
        !def_arg_not_live_at_use(func, reg),
        !inline_temp_unavailable(func, reg);
}

// Build and run RTLOptimizerProgram over a PassContext; returns the program for inspection.
#[cfg(debug_assertions)]
fn run_rtl_optimizer_program(ctx: &PassContext) -> RTLOptimizerProgram {
    let mut prog = RTLOptimizerProgram::default();

    for (&func_addr, func) in &ctx.functions {
        let du = DefUseInfo::build(func);
        let availability = analyze_rtl_availability(func, &du, RtlAvailabilityMode::Both);
        for (&node, inst) in &func.inst {
            prog.rtl_opt_inst.push((node, inst.clone()));
            prog.rtl_opt_func.push((node, func_addr));
        }
        for &node in &func.shared_nodes {
            prog.rtl_opt_shared.push((node,));
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
        for &(intro, use_node) in &availability.copy_unavailable {
            prog.rtl_opt_copy_unavailable.push((intro, use_node));
        }
        for &(intro, use_node) in &availability.inline_unavailable {
            prog.rtl_opt_inline_unavailable.push((intro, use_node));
        }
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
    copy_eliminated: HashSet<Node>,
    dead_call: HashSet<Node>,
    copy_subst: HashMap<RTLReg, RTLReg>,
    inline_temp: HashSet<RTLReg>,
}

fn optimize_rtl_candidates(db: &mut DecompileDB) -> Option<RtlOptStats> {
    // These are production facts, not debug mirrors. Always replace both
    // relations, including when there is no function to optimize, so a reused
    // DB cannot retain kills from an earlier run.
    db.rel_set("dead_store", ascent::boxcar::Vec::<(Node,)>::new());
    db.rel_set("copy_eliminated", ascent::boxcar::Vec::<(Node,)>::new());

    let mut ctx = PassContext::load(db);
    if ctx.functions.is_empty() {
        return None;
    }

    let var_types = std::mem::take(&mut ctx.var_types);

    let func_regs: HashMap<Address, HashSet<RTLReg>> = ctx
        .functions
        .iter()
        .map(|(&addr, func)| {
            let mut regs = HashSet::new();
            for inst in func.inst.values() {
                collect_inst_regs(inst, &mut regs);
            }
            regs.extend(func.params.iter());
            (addr, regs)
        })
        .collect();

    let per_func_var_types: HashMap<Address, HashMap<RTLReg, XType>> = func_regs
        .iter()
        .map(|(&addr, regs)| {
            let ft: HashMap<RTLReg, XType> = regs
                .iter()
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

    // RTLOptimizerProgram is the Ascent v2 of the imperative optimizer. Its outputs are only consumed by the debug-only RTL_V2_DIFF block below, so in release builds we skip it entirely (dominates the RTL pass at ~57s on a 700KB binary).
    #[cfg(debug_assertions)]
    let ascent_v2: Option<AscentV2Snapshot> = if std::env::var("RTL_V2_DIFF").is_ok() {
        let ascent_opt = run_rtl_optimizer_program(&ctx);
        let self_zero: HashSet<Node> = ascent_opt.self_zero_v2.iter().map(|&(n,)| n).collect();
        let dead_store: HashSet<Node> = ascent_opt.dead_store_v2.iter().map(|&(n,)| n).collect();
        let copy_eliminated: HashSet<Node> = ascent_opt
            .copy_eliminated_v2
            .iter()
            .map(|&(n,)| n)
            .collect();
        let dead_call: HashSet<Node> = ascent_opt.dead_call_dst_v2.iter().map(|&(n,)| n).collect();
        let copy_subst: HashMap<RTLReg, RTLReg> = ascent_opt
            .copy_subst_resolved_v2
            .iter()
            .map(|&(d, s)| (d, s))
            .collect();
        let inline_temp: HashSet<RTLReg> =
            ascent_opt.inline_temp_v2.iter().map(|&(r,)| r).collect();
        Some(AscentV2Snapshot {
            self_zero,
            dead_store,
            copy_eliminated,
            dead_call,
            copy_subst,
            inline_temp,
        })
    } else {
        None
    };

    let results: Vec<_> = ctx
        .functions
        .par_iter_mut()
        .map(|(&func_addr, func)| {
            let mut func_var_types = per_func_var_types
                .lock()
                .unwrap()
                .remove(&func_addr)
                .unwrap_or_default();

            // Track iteration-1 imperative outputs for diffing against Ascent.
            let imp_self_zero: HashSet<Node> = func
                .inst
                .iter()
                .filter_map(|(&n, inst)| match inst {
                    RTLInst::Iop(op, args, dst)
                        if args.len() == 2
                            && args[0] == args[1]
                            && args[0] == *dst
                            && matches!(
                                op,
                                Operation::Oxor
                                    | Operation::Osub
                                    | Operation::Oxorl
                                    | Operation::Osubl
                            ) =>
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
            let mut iter1_copy_eliminated_nodes: HashSet<Node> = HashSet::new();
            let mut iter1_dead_store_nodes: HashSet<Node> = HashSet::new();
            let mut iter1_dead_call_nodes: HashSet<Node> = HashSet::new();
            let mut copy_eliminated_nodes: HashSet<Node> = HashSet::new();
            let mut dead_store_nodes: HashSet<Node> = HashSet::new();
            let mut first_iter = true;
            loop {
                let du = DefUseInfo::build(func);
                let liveness = LivenessInfo::build(func, &du);

                let (c, copy_subst, copy_kills) = copy_propagation(func, &du, &liveness);
                if first_iter {
                    iter1_copy_subst = copy_subst.clone();
                    iter1_copy_eliminated_nodes = copy_kills.clone();
                }
                copy_eliminated_nodes.extend(copy_kills);
                for (&dst, &src) in &copy_subst {
                    if let Some(&ty) = func_var_types.get(&dst) {
                        func_var_types.entry(src).or_insert(ty);
                    }
                }
                let (d, dead_store_kills, dead_call_kills) =
                    dead_store_elimination(func, &du, &liveness);

                if first_iter {
                    iter1_dead_store_nodes = dead_store_kills.clone();
                    iter1_dead_call_nodes = dead_call_kills;
                }
                dead_store_nodes.extend(dead_store_kills);

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
                iter1_copy_eliminated_nodes,
                iter1_dead_store_nodes,
                iter1_dead_call_nodes,
                copy_eliminated_nodes,
                dead_store_nodes,
                became_void,
            )
        })
        .collect();

    let mut stats = RtlOptStats::default();
    let mut merged_var_types = var_types;

    let mut imp_self_zero_all: HashSet<Node> = HashSet::new();
    let mut imp_copy_subst_all: HashMap<RTLReg, RTLReg> = HashMap::new();
    let mut imp_copy_eliminated_all: HashSet<Node> = HashSet::new();
    let mut imp_dead_store_all: HashSet<Node> = HashSet::new();
    let mut imp_dead_call_all: HashSet<Node> = HashSet::new();
    let mut copy_eliminated_all: HashSet<Node> = HashSet::new();
    let mut dead_store_all: HashSet<Node> = HashSet::new();
    let mut newly_void: HashSet<Address> = HashSet::new();

    for (
        func_stats,
        inlines,
        func_vt,
        fa,
        isz,
        icp,
        icpe,
        idst,
        idcl,
        copy_kills,
        dead_store_kills,
        became_void,
    ) in results
    {
        stats.accumulate(func_stats);
        ctx.inline_temps.extend(inlines);
        merged_var_types.extend(func_vt);
        imp_self_zero_all.extend(isz);
        for (d, s) in icp {
            imp_copy_subst_all.insert(d, s);
        }
        imp_copy_eliminated_all.extend(icpe);
        imp_dead_store_all.extend(idst);
        imp_dead_call_all.extend(idcl);
        copy_eliminated_all.extend(copy_kills);
        dead_store_all.extend(dead_store_kills);
        if became_void {
            newly_void.insert(fa);
        }
    }

    // Diff logging: compare Ascent v2 vs imperative iteration-1 outputs (uses eprintln so diffs surface during test runs, where no env_logger is configured).
    #[cfg(debug_assertions)]
    if let Some(v2) = &ascent_v2 {
        let self_zero_missing: Vec<_> = imp_self_zero_all
            .difference(&v2.self_zero)
            .copied()
            .collect();
        let self_zero_extra: Vec<_> = v2
            .self_zero
            .difference(&imp_self_zero_all)
            .copied()
            .collect();
        if !self_zero_missing.is_empty() || !self_zero_extra.is_empty() {
            eprintln!(
                "rtl_v2 diff self_zero: imperative={} ascent={} missing_from_ascent={} extra_in_ascent={}",
                imp_self_zero_all.len(), v2.self_zero.len(),
                self_zero_missing.len(), self_zero_extra.len()
            );
        }
        let ds_missing: Vec<_> = imp_dead_store_all
            .difference(&v2.dead_store)
            .copied()
            .collect();
        let ds_extra: Vec<_> = v2
            .dead_store
            .difference(&imp_dead_store_all)
            .copied()
            .collect();
        if !ds_missing.is_empty() || !ds_extra.is_empty() {
            eprintln!(
                "rtl_v2 diff dead_store (iter1): imperative={} ascent={} missing_from_ascent={} extra_in_ascent={}",
                imp_dead_store_all.len(), v2.dead_store.len(),
                ds_missing.len(), ds_extra.len()
            );
        }
        let ce_missing: Vec<_> = imp_copy_eliminated_all
            .difference(&v2.copy_eliminated)
            .copied()
            .collect();
        let ce_extra: Vec<_> = v2
            .copy_eliminated
            .difference(&imp_copy_eliminated_all)
            .copied()
            .collect();
        if !ce_missing.is_empty() || !ce_extra.is_empty() {
            eprintln!(
                "rtl_v2 diff copy_eliminated (iter1): imperative={} ascent={} missing_from_ascent={} extra_in_ascent={}",
                imp_copy_eliminated_all.len(), v2.copy_eliminated.len(),
                ce_missing.len(), ce_extra.len()
            );
        }
        let dc_missing: Vec<_> = imp_dead_call_all
            .difference(&v2.dead_call)
            .copied()
            .collect();
        let dc_extra: Vec<_> = v2
            .dead_call
            .difference(&imp_dead_call_all)
            .copied()
            .collect();
        if !dc_missing.is_empty() || !dc_extra.is_empty() {
            eprintln!(
                "rtl_v2 diff dead_call_dst (iter1): imperative={} ascent={} missing={} extra={}",
                imp_dead_call_all.len(),
                v2.dead_call.len(),
                dc_missing.len(),
                dc_extra.len()
            );
        }
        // ascent copy_subst is path-conservative; expected subset of imperative.
        let cp_missing: Vec<_> = imp_copy_subst_all
            .iter()
            .filter(|&(d, _)| !v2.copy_subst.contains_key(d))
            .map(|(&d, &s)| (d, s))
            .collect();
        let cp_mismatch: Vec<_> = v2
            .copy_subst
            .iter()
            .filter_map(|(&d, &s_asc)| {
                imp_copy_subst_all.get(&d).and_then(|&s_imp| {
                    if s_asc != s_imp {
                        Some((d, s_imp, s_asc))
                    } else {
                        None
                    }
                })
            })
            .collect();
        let cp_extra: Vec<_> = v2
            .copy_subst
            .iter()
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
        let it_missing: Vec<_> = ctx
            .inline_temps
            .difference(&v2.inline_temp)
            .copied()
            .collect();
        let it_extra: Vec<_> = v2
            .inline_temp
            .difference(&ctx.inline_temps)
            .copied()
            .collect();
        if !it_missing.is_empty() || !it_extra.is_empty() {
            eprintln!(
                "rtl_v2 diff inline_temp: imperative={} ascent={} missing={} extra={}",
                ctx.inline_temps.len(),
                v2.inline_temp.len(),
                it_missing.len(),
                it_extra.len()
            );
        }
    }

    ctx.var_types = merged_var_types;
    ctx.write_back(db);

    let mut dead_store_nodes: Vec<Node> = dead_store_all.into_iter().collect();
    dead_store_nodes.sort_unstable();
    db.rel_set(
        "dead_store",
        dead_store_nodes
            .into_iter()
            .map(|node| (node,))
            .collect::<ascent::boxcar::Vec<_>>(),
    );

    let mut copy_eliminated_nodes: Vec<Node> = copy_eliminated_all.into_iter().collect();
    copy_eliminated_nodes.sort_unstable();
    db.rel_set(
        "copy_eliminated",
        copy_eliminated_nodes
            .into_iter()
            .map(|node| (node,))
            .collect::<ascent::boxcar::Vec<_>>(),
    );

    if !newly_void.is_empty() {
        mark_functions_void(db, &newly_void);
    }
    Some(stats)
}

// Retype functions that lost their only return value to void: emit_function_void_candidate wins the ladder, and stale has-return signals are dropped so they cannot reintroduce a bogus return type.
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
    db.rel_set(
        "emit_function_void_candidate",
        void_cand.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );

    let has_ret: Vec<(Address,)> = db
        .rel_iter::<(Address,)>("emit_function_has_return_candidate")
        .filter(|&&(a,)| !void_funcs.contains(&a))
        .cloned()
        .collect();
    db.rel_set(
        "emit_function_has_return_candidate",
        has_ret.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );

    let ret: Vec<(Address, RTLReg)> = db
        .rel_iter::<(Address, RTLReg)>("emit_function_return")
        .filter(|&&(a, _)| !void_funcs.contains(&a))
        .cloned()
        .collect();
    db.rel_set(
        "emit_function_return",
        ret.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );

    let ret_ct: Vec<(Address, ClightType)> = db
        .rel_iter::<(Address, ClightType)>("emit_function_return_type_candidate")
        .filter(|&&(a, _)| !void_funcs.contains(&a))
        .cloned()
        .collect();
    db.rel_set(
        "emit_function_return_type_candidate",
        ret_ct.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );

    let ret_xt: Vec<(Address, XType)> = db
        .rel_iter::<(Address, XType)>("emit_function_return_type_xtype_candidate")
        .filter(|&&(a, _)| !void_funcs.contains(&a))
        .cloned()
        .collect();
    db.rel_set(
        "emit_function_return_type_xtype_candidate",
        ret_xt.into_iter().collect::<ascent::boxcar::Vec<_>>(),
    );
}

pub(crate) fn trim_direct_call_args_to_callee_arity(db: &mut DecompileDB) {
    let mut callee_arity: HashMap<Address, usize> = db
        .rel_iter::<(Address, Signature)>("emit_function_signature_candidate")
        .fold(HashMap::new(), |mut acc, (addr, sig)| {
            acc.entry(*addr)
                .and_modify(|curr| *curr = (*curr).max(sig.sig_args.len()))
                .or_insert(sig.sig_args.len());
            acc
        });

    // RTL's first signature candidate holds register params only; include the upstream stack-param count now, or this pass deletes recovered stack arguments before reconciliation widens the callee.
    let shared_arg_slots = db.abi().uses_shared_arg_slots();
    let first_stack_arg_position = db.abi().first_stack_arg_position();
    for &(addr, stack_count) in db.rel_iter::<(Address, usize)>("emit_function_stack_param_count") {
        let arity = callee_arity.entry(addr).or_insert(0);
        if shared_arg_slots && stack_count > 0 {
            // Win64's home space fixes the first stack parameter at ordinal 4, so preserve unobserved register-slot gaps instead of treating stack params as a dense suffix.
            *arity = (*arity).max(first_stack_arg_position) + stack_count;
        } else {
            *arity += stack_count;
        }
    }

    let call_targets: HashMap<Node, Address> = db
        .rel_iter::<(Node, Address)>("call_target_func")
        .map(|(call_node, target)| (*call_node, *target))
        .collect();

    // Variadic callees receive more args than their fixed signature, so detect them structurally via the SysV variadic XMM register-save-area prologue rather than trimming their tail args.
    let varargs_callees: HashSet<Address> = db
        .rel_iter::<(Address,)>("func_has_variadic_xmm_prologue")
        .map(|&(addr,)| addr)
        .collect();

    let filtered_mapping: Vec<(Node, usize, RTLReg)> = db
        .rel_iter::<(Node, usize, RTLReg)>("call_arg_mapping")
        .filter_map(|&(node, pos, reg)| {
            if let Some(&target) = call_targets.get(&node) {
                // Root E: keep the whole argument tail for a detected-variadic callee; arg_setup_candidate already restricts each position to a def that structurally reaches the call.
                let keep_varargs_tail = varargs_callees.contains(&target);
                if !keep_varargs_tail {
                    if let Some(&arity) = callee_arity.get(&target) {
                        if pos >= arity {
                            return None;
                        }
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
            let keep_varargs_tail = varargs_callees.contains(&target);
            if !keep_varargs_tail {
                if let Some(&arity) = callee_arity.get(&target) {
                    debug_assert!(pos < arity);
                }
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
        // Scatter by position (sentinel DEFAULT_VAR for holes so dropped leading args don't left-shift later ones); len = max_pos+1 is safe because pos <= 5 (6-entry ARG_REGS, rtl_pass.rs).
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
    for &(node, ref args) in
        db.rel_iter::<(Node, Arc<Vec<RTLReg>>)>("call_args_collected_candidate")
    {
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
    for &(call_node, ref float_args) in
        db.rel_iter::<(Node, Arc<Vec<RTLReg>>)>("call_float_args_collected")
    {
        if !float_args.is_empty() {
            let int_args = rebuilt_args
                .entry(call_node)
                .or_insert_with(|| Arc::new(vec![]));
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
                RTLInst::Icall(sig, callee, args, dst, next) => RTLInst::Icall(
                    sig.clone(),
                    callee.clone(),
                    replacement_args.cloned().unwrap_or_else(|| args.clone()),
                    *dst,
                    *next,
                ),
                RTLInst::Itailcall(sig, callee, args) => RTLInst::Itailcall(
                    sig.clone(),
                    callee.clone(),
                    replacement_args.cloned().unwrap_or_else(|| args.clone()),
                ),
                _ => inst.clone(),
            };
            (*node, patched)
        })
        .collect();
    db.rel_set("rtl_inst_candidate", new_rtl_inst);
}

pub struct RTLOptimizePass;

impl IRPass for RTLOptimizePass {
    fn name(&self) -> &'static str {
        "rtl_optimize"
    }

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
            "next",
            "instr_in_function",
            "emit_function",
            "emit_function_param_candidate",
            "emit_var_type_candidate",
            "emit_function_signature_candidate",
            "emit_function_stack_param_count",
            "emit_function_return",
            "call_target_func",
            "call_arg_mapping",
            "call_args_collected_candidate",
            "call_float_args_collected",
            "func_has_variadic_xmm_prologue",
        ]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "rtl_inst",
            "rtl_succ",
            "rtl_next",
            "single_def_const",
            "emit_inline_temp",
            // Exact production optimizer kills, retained after nop collapse so
            // downstream audits can distinguish deliberate removal from loss.
            "dead_store",
            "copy_eliminated",
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
        // Read imperatively in PassContext::load: call_through_memory_load (keeps a vtable Iload alive), jump_table_* (protects an in-loop dispatch entry), escaped-slot/stack_var relations (protect every SSA alias observed through escaped pointers from DSE), and stack_def_used (the slot's real reaching-definition count, which bounds constant folding).
        &[
            "call_through_memory_load",
            "jump_table_impl",
            "jump_table_cmp",
            "jump_table_target",
            "slot_escaped_canonical",
            "slot_escaped_region_canonical",
            "stack_var",
            "stack_def_used",
        ]
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
    // The address regs feeding a mem-indirect call's function-pointer load; rtl_pass threads them only into call_through_memory_load, so record them here or DSE kills the producing Iload.
    pub(crate) mem_call_addr_uses: HashMap<Node, Vec<RTLReg>>,
    // Jump-table dispatch entries of IN-LOOP tables: collapsing one threads the guard past the switch, so only these are protected from nop_collapse.
    pub(crate) dispatch_entry_nodes: HashSet<Node>,
    // Canonical SSA regs of address-escaped stack slots: the callee may write through the escaped pointer, a use reg liveness cannot see, so their stores are excluded from DSE.
    pub(crate) escaped_slot_regs: HashSet<RTLReg>,
    // Frame-slot SSA regs whose slot has more than one definition reaching a
    // single read.  Their RTL def count is not the slot's definition count, so
    // they must not be treated as compile-time constants.
    pub(crate) multi_def_slot_regs: HashSet<RTLReg>,
    // Physical tail-merged blocks can be reached from several function
    // entries.  They participate in every owner's dataflow, but an
    // owner-local optimization must not rewrite the shared instruction: a
    // different owner can have different reaching definitions or
    // reachability.  Such nodes are therefore analysis-visible and
    // transformation-frozen.
    pub(crate) shared_nodes: HashSet<Node>,
}

struct PassContext {
    functions: BTreeMap<Address, FunctionCFG>,
    var_types: HashMap<RTLReg, XType>,
    inline_temps: HashSet<RTLReg>,
    // Deterministic pre-optimization selections.  These are a conservative
    // fallback if two owner contexts ever disagree despite shared-node
    // freezing, and make write-back independent of parallel completion order.
    original_insts: BTreeMap<Node, RTLInst>,
    original_succs: BTreeSet<(Node, Node)>,
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
        let mut raw_next: HashMap<Node, Vec<Node>> = HashMap::new();
        for &(src, dst) in db.rel_iter::<(Node, Node)>("next") {
            raw_next.entry(src).or_default().push(dst);
        }
        for dsts in raw_next.values_mut() {
            dsts.sort_unstable();
            dsts.dedup();
        }
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
        // Per jump table: dispatch entry, bounds-check guard, and case targets;
        // loop membership is tested as "a case body reaches the guard", since
        // the dispatch JMP's edges are not yet in the CFG.  Address order says
        // nothing about which implementation node is reachable first, so use
        // the unique CFG entry from outside the complete dispatch region.
        let mut impl_nodes_by_table: HashMap<Node, HashSet<Node>> = HashMap::new();
        for &(impl_addr, jmp_addr) in db.rel_iter::<(Node, Node)>("jump_table_impl") {
            impl_nodes_by_table
                .entry(jmp_addr)
                .or_default()
                .insert(impl_addr);
        }
        let mut dispatch_entry_by_table: HashMap<Node, Node> = HashMap::new();
        for (jmp_addr, mut region) in impl_nodes_by_table {
            region.insert(jmp_addr);
            if let Some(entry) = unique_external_cfg_entry(&region, &rtl_succs) {
                dispatch_entry_by_table.insert(jmp_addr, entry);
            }
        }
        let mut table_guard: HashMap<Node, Node> = HashMap::new();
        for &(jmp_addr, cmp_addr) in db.rel_iter::<(Node, Node)>("jump_table_cmp") {
            table_guard.entry(jmp_addr).or_insert(cmp_addr);
        }
        let mut table_cases: HashMap<Node, Vec<Node>> = HashMap::new();
        for &(jmp_addr, _idx, target) in db.rel_iter::<(Node, usize, Node)>("jump_table_target") {
            table_cases.entry(jmp_addr).or_default().push(target);
        }
        // (dispatch_entry, guard, case_targets) per table that has both an entry and a guard.
        let dispatch_loop_probes: Vec<(Node, Node, Vec<Node>)> = dispatch_entry_by_table
            .iter()
            .filter_map(|(&jmp, &entry)| {
                let guard = *table_guard.get(&jmp)?;
                let cases = table_cases.get(&jmp).cloned().unwrap_or_default();
                Some((entry, guard, cases))
            })
            .collect();

        // Address regs feeding a mem-indirect call's target load, per call node (node -> [base, idx?]); see FunctionCFG::mem_call_addr_uses. Declared in extra_reads().
        let mut mem_call_addr_uses: HashMap<Node, Vec<RTLReg>> = HashMap::new();
        for (node, _temp, _chunk, _addr, args) in db.rel_iter::<(
            Node,
            RTLReg,
            MemoryChunk,
            crate::x86::op::Addressing,
            Arc<Vec<RTLReg>>,
        )>("call_through_memory_load")
        {
            let entry = mem_call_addr_uses.entry(*node).or_default();
            for &r in args.iter() {
                if !entry.contains(&r) {
                    entry.push(r);
                }
            }
        }

        // Per function, every SSA name for an address-escaped stack slot whose
        // stores must not be dead-store-eliminated. The escaped-slot facts
        // carry one canonical name per offset, but stack_var is point-local and
        // the same offset can therefore have other SSA names on different CFG
        // arms. An external alias observes the memory cell, not just its
        // canonical name, so protect all names structurally joined by
        // (function, offset). These relations are declared in extra_reads().
        let mut escaped_slot_regs: HashMap<Address, HashSet<RTLReg>> = HashMap::new();
        let mut escaped_slot_offsets: HashMap<Address, HashSet<i64>> = HashMap::new();
        for &(func, ofs, reg) in db.rel_iter::<(Address, i64, RTLReg)>("slot_escaped_canonical") {
            escaped_slot_regs.entry(func).or_default().insert(reg);
            escaped_slot_offsets.entry(func).or_default().insert(ofs);
        }
        for &(func, ofs, reg) in
            db.rel_iter::<(Address, i64, RTLReg)>("slot_escaped_region_canonical")
        {
            escaped_slot_regs.entry(func).or_default().insert(reg);
            escaped_slot_offsets.entry(func).or_default().insert(ofs);
        }
        for &(func, _node, ofs, reg) in db.rel_iter::<(Address, Node, i64, RTLReg)>("stack_var") {
            if escaped_slot_offsets
                .get(&func)
                .is_some_and(|offsets| offsets.contains(&ofs))
            {
                escaped_slot_regs.entry(func).or_default().insert(reg);
            }
        }

        // Per function, the frame-slot SSA names whose slot is written by more
        // than one instruction reaching the same read.  StackAnalysis pairs
        // every definition of a slot with the reads it reaches, and that is the
        // slot's real definition count.  The RTL def count is not: a store
        // whose frame anchor was never recovered produces no def of this name
        // at all, leaving a genuinely re-assigned slot looking single-def and
        // letting its one visible initializer be substituted into every read.
        // Only reaching-definition structure decides this; nothing here
        // compares addresses to guess which write came first.
        let mut slot_read_defs: HashMap<(Address, i64), HashSet<Address>> = HashMap::new();
        for &(def_addr, _, _, use_addr, _, use_ofs) in
            db.rel_iter::<(Address, Symbol, i64, Address, Symbol, i64)>("stack_def_used")
        {
            slot_read_defs
                .entry((use_addr, use_ofs))
                .or_default()
                .insert(def_addr);
        }
        let mut multi_def_slot_regs: HashMap<Address, HashSet<RTLReg>> = HashMap::new();
        for &(func, node, ofs, reg) in db.rel_iter::<(Address, Node, i64, RTLReg)>("stack_var") {
            if slot_read_defs
                .get(&(node, ofs))
                .is_some_and(|defs| defs.len() > 1)
            {
                multi_def_slot_regs.entry(func).or_default().insert(reg);
            }
        }
        // Per reg, keep the max-(refine_priority, type) candidate via fold-during-insert (avoids intermediate Vec; key embeds type so equal-key ties are identical values, making the winner iteration-order-independent).
        let var_types: HashMap<RTLReg, XType> = {
            let key = |ty: &XType| {
                (
                    crate::decompile::passes::clight_pass::xtype_refine_priority(ty),
                    *ty,
                )
            };
            let mut chosen: HashMap<RTLReg, XType> = HashMap::new();
            for (reg, xty) in db.rel_iter::<(RTLReg, XType)>("emit_var_type_candidate") {
                chosen
                    .entry(*reg)
                    .and_modify(|cur| {
                        if key(xty) > key(cur) {
                            *cur = *xty;
                        }
                    })
                    .or_insert(*xty);
            }
            chosen
        };

        let func_entries: HashMap<Address, Node> = emit_funcs
            .iter()
            .map(|&(addr, _, entry)| (addr, entry))
            .collect();

        // A physical block can be a compiler tail merge owned by several
        // function entries.  Choosing one owner (formerly the minimum address)
        // amputates the tail from every other function's optimizer CFG, so
        // liveness can delete definitions that the shared tail uses.  Retain
        // every emitted owner.  This is structural ownership, never an address
        // or node-order reachability guess.
        let mut all_node_owners: HashMap<Node, BTreeSet<Address>> = HashMap::new();
        for &(node, func) in &instr_in_func {
            all_node_owners.entry(node).or_default().insert(func);
        }
        let mut node_to_funcs: HashMap<Node, BTreeSet<Address>> = HashMap::new();
        for &(node, func) in &instr_in_func {
            if func_entries.contains_key(&func) {
                node_to_funcs.entry(node).or_default().insert(func);
            }
        }
        let globally_shared_nodes: HashSet<Node> = node_to_funcs
            .iter()
            .filter_map(|(&node, owners)| (owners.len() > 1).then_some(node))
            .collect();

        let mut func_params: HashMap<Address, HashSet<RTLReg>> = HashMap::new();
        for &(addr, reg) in &emit_params {
            func_params.entry(addr).or_default().insert(reg);
        }

        let mut node_candidates: HashMap<Node, Vec<RTLInst>> = HashMap::new();
        for (node, inst) in &rtl_insts {
            if node_to_funcs.contains_key(node) {
                node_candidates.entry(*node).or_default().push(inst.clone());
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

        // Select a physical instruction once, before projecting it into owner
        // CFGs.  Thus every owner starts with byte-for-byte identical shared
        // nodes and HashMap iteration can never choose their meaning.
        let mut original_insts: BTreeMap<Node, RTLInst> = BTreeMap::new();
        for (node, candidates) in node_candidates {
            // INVARIANT: node_candidates entries are created only via push, so
            // each Vec has at least one element.
            let best = if candidates.len() == 1 {
                candidates
                    .into_iter()
                    .next()
                    .expect("len()==1 guard: single candidate present")
            } else {
                let mut candidates = candidates;
                candidates.sort_by_cached_key(|inst| format!("{:?}", inst));
                // Icond wins categorically when Icond and Iop collide on one
                // node, since Iop is side-effect-only while Icond carries the
                // CFG edge; score only breaks ties among same-kind candidates.
                candidates
                    .into_iter()
                    .max_by_key(|inst| {
                        let mut regs = HashSet::new();
                        collect_inst_regs(inst, &mut regs);
                        let score: usize = regs
                            .iter()
                            .map(|r| reg_usage_count.get(r).copied().unwrap_or(0))
                            .sum();
                        let arg_bonus = match inst {
                            RTLInst::Iop(_, args, _) if !args.is_empty() => 1,
                            RTLInst::Iload(_, _, args, _) if !args.is_empty() => 1,
                            RTLInst::Icond(_, args, _, _) if !args.is_empty() => 1,
                            _ => 0,
                        };
                        let is_cond = matches!(inst, RTLInst::Icond(..));
                        (is_cond, score + arg_bonus)
                    })
                    .expect(
                        "non-empty by construction: node_candidates entries are created by push",
                    )
            };
            original_insts.insert(node, best);
        }

        let mut func_insts: HashMap<Address, BTreeMap<Node, RTLInst>> = HashMap::new();
        for (&node, inst) in &original_insts {
            if let Some(owners) = node_to_funcs.get(&node) {
                for &func in owners {
                    func_insts
                        .entry(func)
                        .or_default()
                        .insert(node, inst.clone());
                }
            }
        }

        let mut func_succs: HashMap<Address, HashMap<Node, Vec<Node>>> = HashMap::new();
        for &(src, dst) in &rtl_succs {
            if let Some(owners) = node_to_funcs.get(&src) {
                for &func in owners {
                    func_succs
                        .entry(func)
                        .or_default()
                        .entry(src)
                        .or_default()
                        .push(dst);
                }
            }
        }
        // Recovered jump-table targets are the explicit CFG successors of the
        // indirect dispatch.  They are not represented by `next` (which ends
        // at the JMP) and some frontends retain the dispatch as an unresolved
        // symbolic Ibranch rather than an Ijumptable.  Feed the recovered case
        // edges into the same per-function CFG before liveness/DSE, otherwise
        // every value defined before the switch and used only by a case looks
        // dead.  Raw case labels are normalized through `next` below, exactly
        // like ordinary branch targets.
        for (&dispatch, targets) in &table_cases {
            if let Some(owners) = node_to_funcs.get(&dispatch) {
                for &func in owners {
                    func_succs
                        .entry(func)
                        .or_default()
                        .entry(dispatch)
                        .or_default()
                        .extend(targets.iter().copied());
                }
            }
        }

        let mut functions = BTreeMap::new();
        for (&func_addr, insts) in &func_insts {
            let entry = match func_entries.get(&func_addr) {
                Some(&e) => e,
                None => continue,
            };
            let nodes: BTreeSet<Node> = insts.keys().copied().collect();

            let mut raw_succs = func_succs.remove(&func_addr).unwrap_or_default();
            let mut next_semantic_cache: HashMap<Node, Option<Node>> = HashMap::new();

            // Linear canonicalizes through raw instructions that have no LTL
            // form. RTL can later materialize one of those instructions (a
            // memory CMP, for example, becomes an Iload followed by an Icond).
            // The inherited ltl_succ then jumps around the new operation and
            // makes it an unreachable island in the optimizer CFG.
            //
            // At this point candidate selection is complete, so repair the
            // fallthrough against the actual semantic-node set. This applies
            // to every straight-line instruction unless RTL has explicitly
            // routed it into a synthetic expansion. Synthetic nodes have
            // dedicated tag bits (a namespace classification, not an ordering
            // proxy), so that exception is exact. The successor itself is
            // found solely by walking the structural raw-next chain within
            // this function.
            for (&src, inst) in insts {
                if !matches!(
                    inst,
                    RTLInst::Inop
                        | RTLInst::Iop(..)
                        | RTLInst::Iload(..)
                        | RTLInst::Istore(..)
                        | RTLInst::Ibuiltin(..)
                ) {
                    continue;
                }
                let Some(raw_dsts) = raw_next.get(&src) else {
                    continue;
                };
                if raw_dsts.len() != 1 {
                    continue;
                }
                let Some(structural_dst) = resolve_next_semantic_node(
                    func_addr,
                    raw_dsts[0],
                    &nodes,
                    &raw_next,
                    &all_node_owners,
                    &mut next_semantic_cache,
                ) else {
                    continue;
                };
                let enters_synthetic_expansion = raw_succs.get(&src).is_some_and(|dsts| {
                    dsts.iter()
                        .any(|dst| dst & (SYNTH_NODE_BIT | SYNTH_NODE_BIT2) != 0)
                });
                if !enters_synthetic_expansion {
                    raw_succs.insert(src, vec![structural_dst]);
                }
            }

            let mut succs: HashMap<Node, Vec<Node>> = HashMap::new();
            for (src, dsts) in raw_succs {
                if nodes.contains(&src) {
                    let mut semantic_dsts: Vec<Node> = dsts
                        .into_iter()
                        .filter_map(|dst| {
                            resolve_next_semantic_node(
                                func_addr,
                                dst,
                                &nodes,
                                &raw_next,
                                &all_node_owners,
                                &mut next_semantic_cache,
                            )
                        })
                        .collect();
                    semantic_dsts.sort_unstable();
                    semantic_dsts.dedup();
                    if !semantic_dsts.is_empty() {
                        succs.insert(src, semantic_dsts);
                    }
                }
            }

            for &node in &nodes {
                if succs.contains_key(&node) {
                    continue;
                }
                let inst = match insts.get(&node) {
                    Some(inst) => inst,
                    None => continue,
                };
                let raw_target = match inst {
                    RTLInst::Inop
                    | RTLInst::Iop(..)
                    | RTLInst::Iload(..)
                    | RTLInst::Istore(..)
                    | RTLInst::Ibuiltin(..) => raw_next
                        .get(&node)
                        .and_then(|nexts| (nexts.len() == 1).then_some(nexts[0])),
                    RTLInst::Icall(_, _, _, _, next) => Some(*next),
                    RTLInst::Ibranch(Either::Right(target)) => Some(*target),
                    _ => None,
                };
                if let Some(dst) = raw_target.and_then(|target| {
                    resolve_next_semantic_node(
                        func_addr,
                        target,
                        &nodes,
                        &raw_next,
                        &all_node_owners,
                        &mut next_semantic_cache,
                    )
                }) {
                    succs.entry(node).or_default().push(dst);
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

            let func_mem_call_uses: HashMap<Node, Vec<RTLReg>> = nodes
                .iter()
                .filter_map(|n| mem_call_addr_uses.get(n).map(|regs| (*n, regs.clone())))
                .collect();
            let function_shared_nodes: HashSet<Node> = nodes
                .iter()
                .filter(|node| globally_shared_nodes.contains(node))
                .copied()
                .collect();

            let mut func = FunctionCFG {
                func_addr,
                entry,
                nodes,
                inst: insts.clone(),
                succs,
                preds,
                params: func_params.remove(&func_addr).unwrap_or_default(),
                mem_call_addr_uses: func_mem_call_uses,
                dispatch_entry_nodes: HashSet::new(),
                escaped_slot_regs: escaped_slot_regs.remove(&func_addr).unwrap_or_default(),
                multi_def_slot_regs: multi_def_slot_regs.remove(&func_addr).unwrap_or_default(),
                shared_nodes: function_shared_nodes,
            };
            // A dispatch entry is protected only when some case body flows back to the bounds-check guard, i.e. the switch is inside a loop; structural CFG reachability, no address comparison.
            let mut dispatch_entry_nodes: HashSet<Node> = HashSet::new();
            for (entry, guard, cases) in &dispatch_loop_probes {
                if !func.nodes.contains(entry) || dispatch_entry_nodes.contains(entry) {
                    continue;
                }
                let in_loop = cases
                    .iter()
                    .any(|c| func.nodes.contains(c) && reachable_from(&func, *c).contains(guard));
                if in_loop {
                    dispatch_entry_nodes.insert(*entry);
                }
            }
            func.dispatch_entry_nodes = dispatch_entry_nodes;

            functions.insert(func_addr, func);
        }

        let original_succs: BTreeSet<(Node, Node)> = functions
            .values()
            .flat_map(|func| {
                func.succs.iter().flat_map(|(&src, dsts)| {
                    dsts.iter()
                        .copied()
                        .map(move |dst| (src, dst))
                        .collect::<Vec<_>>()
                })
            })
            .collect();

        PassContext {
            functions,
            var_types,
            inline_temps: HashSet::new(),
            original_insts,
            original_succs,
        }
    }

    fn write_back(self, db: &mut DecompileDB) {
        let PassContext {
            functions,
            var_types: _,
            inline_temps,
            original_insts,
            original_succs,
        } = self;

        let mut escaped_regs = HashSet::new();
        let mut multi_def_slot_regs = HashSet::new();
        let mut parameter_regs = HashSet::new();
        for func in functions.values() {
            escaped_regs.extend(func.escaped_slot_regs.iter().copied());
            multi_def_slot_regs.extend(func.multi_def_slot_regs.iter().copied());
            parameter_regs.extend(func.params.iter().copied());
        }

        // Reconcile the owner-local views into one physical RTL program.  A
        // shared node is frozen, so equal results are expected.  Should a
        // future transform violate that contract, fall back to the original
        // instruction instead of publishing two meanings for one node.
        let mut final_insts: BTreeMap<Node, RTLInst> = BTreeMap::new();
        let mut conflicting_nodes: BTreeSet<Node> = BTreeSet::new();
        for func in functions.values() {
            for (&node, inst) in &func.inst {
                if conflicting_nodes.contains(&node) {
                    continue;
                }
                if let Some(existing) = final_insts.get(&node) {
                    if existing != inst {
                        conflicting_nodes.insert(node);
                        if let Some(original) = original_insts.get(&node) {
                            final_insts.insert(node, original.clone());
                        }
                    }
                } else {
                    final_insts.insert(node, inst.clone());
                }
            }
        }

        let mut final_succs: BTreeSet<(Node, Node)> = BTreeSet::new();
        for func in functions.values() {
            for (&src, dsts) in &func.succs {
                if func.inst.contains_key(&src) {
                    final_succs.extend(dsts.iter().map(|&dst| (src, dst)));
                }
            }
        }
        // A baseline instruction restored after a disagreement needs its
        // baseline CFG edges as well; owner-specific folded/retargeted edges
        // cannot describe it soundly.
        for &node in &conflicting_nodes {
            final_succs.retain(|(src, _)| *src != node);
            final_succs.extend(
                original_succs
                    .iter()
                    .filter(|(src, _)| *src == node)
                    .copied(),
            );
        }
        final_succs.retain(|(src, _)| final_insts.contains_key(src));

        let mut live_regs: HashSet<RTLReg> = HashSet::new();
        let mut global_def_count: HashMap<RTLReg, usize> = HashMap::new();
        let mut global_use_nodes: HashMap<RTLReg, HashSet<Node>> = HashMap::new();
        for (&node, inst) in &final_insts {
            collect_inst_regs(inst, &mut live_regs);
            let (defined, used) = inst_def_use(inst);
            if let Some(reg) = defined {
                *global_def_count.entry(reg).or_default() += 1;
            }
            for reg in used {
                global_use_nodes.entry(reg).or_default().insert(node);
            }
        }

        // The relation's contract is program-global single-def: consumers
        // substitute the constant at every use.  Counting inside one owner CFG
        // is unsound for a register web fed by several private predecessors of
        // a shared tail.
        let new_sdc = ascent::boxcar::Vec::<(RTLReg, Constant)>::new();
        for inst in final_insts.values() {
            if let RTLInst::Iop(op, args, dst) = inst {
                if args.is_empty()
                    && global_def_count.get(dst) == Some(&1)
                    && !escaped_regs.contains(dst)
                    && !multi_def_slot_regs.contains(dst)
                {
                    if let Some(cst) =
                        crate::decompile::passes::cminor_pass::constant_from_operation(op)
                    {
                        new_sdc.push((*dst, cst));
                    }
                }
            }
        }
        db.rel_set("single_def_const", new_sdc);

        let new_insts: ascent::boxcar::Vec<(Node, RTLInst)> = final_insts.into_iter().collect();
        let new_succs: ascent::boxcar::Vec<(Node, Node)> = final_succs.into_iter().collect();
        db.rel_set("rtl_next", new_succs.clone());
        db.rel_set("rtl_inst", new_insts);
        db.rel_set("rtl_succ", new_succs);

        let inline_vec = ascent::boxcar::Vec::<RTLReg>::new();
        // Sort and recheck the single-def/single-use contract globally: a
        // private owner view cannot certify a web shared by another entry.
        let mut inline_sorted: Vec<RTLReg> = inline_temps.iter().copied().collect();
        inline_sorted.sort();
        for reg in inline_sorted {
            if live_regs.contains(&reg)
                && global_def_count.get(&reg) == Some(&1)
                && global_use_nodes
                    .get(&reg)
                    .is_some_and(|uses| uses.len() == 1)
                && !parameter_regs.contains(&reg)
            {
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
            for &a in args.iter() {
                regs.insert(a);
            }
            regs.insert(*dst);
        }
        RTLInst::Iload(_, _, args, dst) => {
            for &a in args.iter() {
                regs.insert(a);
            }
            regs.insert(*dst);
        }
        RTLInst::Istore(_, _, args, src) => {
            for &a in args.iter() {
                regs.insert(a);
            }
            regs.insert(*src);
        }
        RTLInst::Icall(_, callee, args, dst, _) => {
            if let Either::Left(r) = callee {
                regs.insert(*r);
            }
            for &a in args.iter() {
                regs.insert(a);
            }
            if let Some(d) = dst {
                regs.insert(*d);
            }
        }
        RTLInst::Itailcall(_, callee, args) => {
            if let Either::Left(r) = callee {
                regs.insert(*r);
            }
            for &a in args.iter() {
                regs.insert(a);
            }
        }
        RTLInst::Ibuiltin(_, args, res) => {
            collect_builtin_arg_regs(args, regs);
            collect_single_builtin_arg_regs(res, regs);
        }
        RTLInst::Icond(_, args, _, _) => {
            for &a in args.iter() {
                regs.insert(a);
            }
        }
        RTLInst::Ijumptable(reg, _) => {
            regs.insert(*reg);
        }
        RTLInst::Ibranch(_) => {}
        RTLInst::Ireturn(reg) => {
            regs.insert(*reg);
        }
    }
}

fn collect_builtin_arg_regs(args: &[BuiltinArg<RTLReg>], regs: &mut HashSet<RTLReg>) {
    for arg in args {
        collect_single_builtin_arg_regs(arg, regs);
    }
}

fn collect_single_builtin_arg_regs(arg: &BuiltinArg<RTLReg>, regs: &mut HashSet<RTLReg>) {
    match arg {
        BuiltinArg::BA(r) => {
            regs.insert(*r);
        }
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

        DefUseInfo {
            node_def,
            node_uses,
            defs,
            uses,
        }
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
            if let Either::Left(r) = callee {
                used.push(*r);
            }
            (dst.as_ref().copied(), used)
        }
        RTLInst::Itailcall(_, callee, args) => {
            let mut used: Vec<RTLReg> = args.iter().copied().collect();
            if let Either::Left(r) = callee {
                used.push(*r);
            }
            (None, used)
        }
        RTLInst::Ibuiltin(_, args, res) => {
            let mut used = Vec::new();
            for a in args {
                collect_ba_uses(a, &mut used);
            }
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

// True for an integer equality/inequality comparison, where `cmp x, x` is statically known (equal -> Ceq true / Cne false) regardless of value; ordered comparisons (Clt/Cle/Cgt/Cge) and float comparisons are excluded so only provably-determined branches fold.
fn const_eq_branch_taken(cond: &Condition) -> Option<bool> {
    match cond {
        Condition::Ccomp(c)
        | Condition::Ccompu(c)
        | Condition::Ccompl(c)
        | Condition::Ccomplu(c) => match c {
            Comparison::Ceq => Some(true),
            Comparison::Cne => Some(false),
            _ => None,
        },
        _ => None,
    }
}

// Constant-fold a two-register conditional branch whose operands provably hold the SAME value, then drop the unreachable nodes; equal only for the same register or an identical 0-arg constant.
fn fold_static_eq_branches(func: &mut FunctionCFG) -> bool {
    // single_def_const, enforced: a register counts as constant ONLY when that constant op is its sole def, or a multi-def register could fold a runtime branch through a non-reaching def.
    let du = DefUseInfo::build(func);
    let mut const_of: HashMap<RTLReg, Constant> = HashMap::new();
    for inst in func.inst.values() {
        if let RTLInst::Iop(op, args, dst) = inst {
            if args.is_empty() {
                if let Some(cst) =
                    crate::decompile::passes::cminor_pass::constant_from_operation(op)
                {
                    // A frame slot whose reads have several reaching
                    // definitions is not constant, whether or not every one of
                    // those definitions became an RTL def of this name.
                    if func.multi_def_slot_regs.contains(dst) {
                        continue;
                    }
                    if du.defs.get(dst).is_some_and(|d| d.len() == 1) {
                        const_of.insert(*dst, cst);
                    }
                }
            }
        }
    }

    let mut folds: Vec<(Node, Node, Node)> = Vec::new();
    for (&node, inst) in &func.inst {
        if func.shared_nodes.contains(&node) {
            continue;
        }
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
        func.inst
            .insert(node, RTLInst::Ibranch(Either::Right(taken)));
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
    for (node, inst) in func.inst.iter_mut() {
        if func.shared_nodes.contains(node) {
            continue;
        }
        let rewrite = match inst {
            RTLInst::Iop(op, args, dst) if args.len() == 2 && args[0] == args[1] => match op {
                Operation::Oxor | Operation::Osub => Some(RTLInst::Iop(
                    Operation::Ointconst(0),
                    Arc::new(vec![]),
                    *dst,
                )),
                Operation::Oxorl | Operation::Osubl => Some(RTLInst::Iop(
                    Operation::Olongconst(0),
                    Arc::new(vec![]),
                    *dst,
                )),
                _ => None,
            },
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
) -> (usize, HashMap<RTLReg, RTLReg>, HashSet<Node>) {
    let mut candidates: Vec<(Node, RTLReg, RTLReg)> = Vec::new();

    for (&node, inst) in &func.inst {
        if func.shared_nodes.contains(&node) {
            continue;
        }
        if let RTLInst::Iop(Operation::Omove, args, dst) = inst {
            if args.len() == 1 && args[0] != *dst {
                let src = args[0];
                candidates.push((node, src, *dst));
            }
        }
    }
    if candidates.is_empty() {
        return (0, HashMap::new(), HashSet::new());
    }
    let availability = analyze_rtl_availability(func, du, RtlAvailabilityMode::Copies);

    let mut subst: HashMap<RTLReg, RTLReg> = HashMap::new();
    let mut dead_nodes: HashSet<Node> = HashSet::new();
    // These uses live in call_through_memory_load rather than inside the
    // Icall.  Instruction-local substitution cannot rewrite that side
    // relation, so eliminating their producer would leave downstream Cminor
    // reconstruction reading the old, uninitialized register.
    let mem_call_addr_regs: HashSet<RTLReg> = func
        .mem_call_addr_uses
        .values()
        .flatten()
        .copied()
        .collect();

    // Pass 1: classify each Omove candidate as propagatable or not, recording the dst of every unsafe copy (notably one whose source is clobbered before a use).
    let mut unsafe_dsts: HashSet<RTLReg> = HashSet::new();
    let mut safe_list: Vec<(Node, RTLReg, RTLReg)> = Vec::new();
    for (copy_node, src, dst) in &candidates {
        let src = *src;
        let dst = *dst;
        let mut safe = !func.params.contains(&dst)
            && !mem_call_addr_regs.contains(&dst)
            && du.defs.get(&dst).map_or(0, |d| d.len()) == 1;
        if safe {
            match du.uses.get(&dst) {
                None => safe = false,
                Some(dst_uses) => {
                    safe = dst_uses.iter().all(|&use_node| {
                        !func.shared_nodes.contains(&use_node)
                            && availability.copy_is_available(*copy_node, use_node)
                    });
                }
            }
        }
        if safe {
            safe_list.push((*copy_node, src, dst));
        } else {
            unsafe_dsts.insert(dst);
        }
    }

    // Pass 2: a copy whose SOURCE is an unsafe copy's dst must not propagate either, or a later dead-store pass drops the producer and the use reads uninitialized memory.
    for (copy_node, src, dst) in &safe_list {
        if unsafe_dsts.contains(src) {
            continue;
        }
        subst.insert(*dst, *src);
        dead_nodes.insert(*copy_node);
    }

    if subst.is_empty() {
        return (0, HashMap::new(), HashSet::new());
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

    (count, resolved, dead_nodes)
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
    Arc::new(
        args.iter()
            .map(|r| map.get(r).copied().unwrap_or(*r))
            .collect(),
    )
}

pub(crate) fn subst_ba(
    ba: &BuiltinArg<RTLReg>,
    map: &HashMap<RTLReg, RTLReg>,
) -> BuiltinArg<RTLReg> {
    match ba {
        BuiltinArg::BA(r) => BuiltinArg::BA(map.get(r).copied().unwrap_or(*r)),
        BuiltinArg::BASplitLong(a, b) => {
            BuiltinArg::BASplitLong(Box::new(subst_ba(a, map)), Box::new(subst_ba(b, map)))
        }
        BuiltinArg::BAAddPtr(a, b) => {
            BuiltinArg::BAAddPtr(Box::new(subst_ba(a, map)), Box::new(subst_ba(b, map)))
        }
        other => other.clone(),
    }
}

pub(crate) fn dead_store_elimination(
    func: &mut FunctionCFG,
    du: &DefUseInfo,
    liveness: &LivenessInfo,
) -> (usize, HashSet<Node>, HashSet<Node>) {
    let mut count = 0;
    let dead_nodes: Vec<Node> = func
        .inst
        .iter()
        .filter_map(|(&node, inst)| {
            if func.shared_nodes.contains(&node) {
                return None;
            }
            let def_reg = du.node_def.get(&node)?;

            if func.params.contains(def_reg) {
                return None;
            }

            // A store to an address-escaped stack slot is never dead: the callee reads it through the escaped pointer, protecting every by-reference out-param's initialization.
            if func.escaped_slot_regs.contains(def_reg) {
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

    let dead_call_nodes: Vec<Node> = func
        .inst
        .iter()
        .filter_map(|(&node, inst)| {
            if func.shared_nodes.contains(&node) {
                return None;
            }
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

    for node in &dead_call_nodes {
        if let Some(RTLInst::Icall(sig, callee, args, _, next)) = func.inst.get(node).cloned() {
            func.inst
                .insert(*node, RTLInst::Icall(sig, callee, args, None, next));
            count += 1;
        }
    }

    (
        count,
        dead_nodes.into_iter().collect(),
        dead_call_nodes.into_iter().collect(),
    )
}

pub(crate) fn nop_collapse(func: &mut FunctionCFG) -> usize {
    // An in-loop dispatch entry is DSE-nopped but not removable: keep it self-canonical, or threading the guard past the switch leaves a dead switch.
    let dispatch_entry = &func.dispatch_entry_nodes;
    let nop_nodes: Vec<Node> = func
        .inst
        .iter()
        .filter(|(&node, inst)| {
            matches!(inst, RTLInst::Inop)
                && node != func.entry
                && !dispatch_entry.contains(&node)
                && !func.shared_nodes.contains(&node)
                && func.preds.get(&node).map_or(true, |preds| {
                    preds.iter().all(|pred| !func.shared_nodes.contains(pred))
                })
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
            let new_targets: Vec<Node> = targets
                .iter()
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
    let mut candidates = Vec::new();

    for (&reg, def_nodes) in &du.defs {
        if def_nodes.len() != 1 {
            continue;
        }
        let def_node = def_nodes[0];
        if func.shared_nodes.contains(&def_node) {
            continue;
        }

        let use_node = match du.uses.get(&reg) {
            Some(u) => {
                let mut distinct: Vec<Node> = u.clone();
                distinct.sort_unstable();
                distinct.dedup();
                if distinct.len() != 1 {
                    continue;
                }
                if func.shared_nodes.contains(&distinct[0]) {
                    continue;
                }
                distinct[0]
            }
            _ => continue,
        };

        if func.params.contains(&reg) {
            continue;
        }

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

        candidates.push((reg, def_node, use_node));
    }

    if candidates.is_empty() {
        return HashSet::new();
    }
    let availability = analyze_rtl_availability(func, du, RtlAvailabilityMode::InlineExprs);
    candidates
        .into_iter()
        .filter_map(|(reg, def_node, use_node)| {
            // The point-keyed lattice proves the expression definition reaches
            // the use on every entry-to-use path with all operands unchanged.
            availability
                .inline_is_available(def_node, use_node)
                .then_some(reg)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{
        copy_propagation, find_inline_temps, fold_static_eq_branches, optimize_rtl_candidates,
        reachable_from, unique_external_cfg_entry, DefUseInfo, FunctionCFG, LivenessInfo,
        PassContext, RTLOptimizePass,
    };
    use crate::decompile::elevator::DecompileDB;
    use crate::decompile::passes::pass::IRPass;
    use crate::x86::op::{Addressing, Comparison, Condition, Operation};
    use crate::x86::types::{Constant, MemoryChunk, RTLInst};
    use either::Either;
    use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
    use std::sync::Arc;

    fn synthetic_ids<const N: usize>() -> [u64; N] {
        std::array::from_fn(|index| index as u64 + 1)
    }

    fn synthetic_function(
        entry: u64,
        instructions: Vec<(u64, RTLInst)>,
        edges: &[(u64, u64)],
        params: &[u64],
    ) -> FunctionCFG {
        let inst: BTreeMap<_, _> = instructions.into_iter().collect();
        let mut succs: HashMap<u64, Vec<u64>> = HashMap::new();
        let mut preds: HashMap<u64, Vec<u64>> = HashMap::new();
        for &(src, dst) in edges {
            succs.entry(src).or_default().push(dst);
            preds.entry(dst).or_default().push(src);
        }
        FunctionCFG {
            func_addr: 0x1000,
            entry,
            nodes: inst.keys().copied().collect(),
            inst,
            succs,
            preds,
            params: params.iter().copied().collect(),
            mem_call_addr_uses: HashMap::new(),
            dispatch_entry_nodes: HashSet::new(),
            escaped_slot_regs: HashSet::new(),
            multi_def_slot_regs: HashSet::new(),
            shared_nodes: HashSet::new(),
        }
    }

    fn run_copy_propagation(mut func: FunctionCFG) -> (usize, HashMap<u64, u64>, HashSet<u64>) {
        let du = DefUseInfo::build(&func);
        let liveness = LivenessInfo::build(&func, &du);
        copy_propagation(&mut func, &du, &liveness)
    }

    #[test]
    fn availability_rejects_production_copy_with_unreachable_use() {
        let [copy, reachable_exit, unreachable_use] = [0x10, 0x20, 0x90];
        let [src, dst] = [1, 2];
        let func = synthetic_function(
            copy,
            vec![
                (
                    copy,
                    RTLInst::Iop(Operation::Omove, Arc::new(vec![src]), dst),
                ),
                (reachable_exit, RTLInst::Ireturn(src)),
                (unreachable_use, RTLInst::Ireturn(dst)),
            ],
            &[(copy, reachable_exit)],
            &[src],
        );

        let (count, subst, eliminated) = run_copy_propagation(func);
        assert_eq!(count, 0);
        assert!(subst.is_empty());
        assert!(!eliminated.contains(&copy));
    }

    #[test]
    fn availability_rejects_production_copy_redefined_on_one_branch() {
        let [copy, redef, clean, join] = [0x10, 0x20, 0x30, 0x40];
        let [src, dst] = [1, 2];
        let func = synthetic_function(
            copy,
            vec![
                (
                    copy,
                    RTLInst::Iop(Operation::Omove, Arc::new(vec![src]), dst),
                ),
                (
                    redef,
                    RTLInst::Iop(Operation::Ointconst(7), Arc::new(vec![]), src),
                ),
                (clean, RTLInst::Inop),
                (join, RTLInst::Ireturn(dst)),
            ],
            &[(copy, redef), (copy, clean), (redef, join), (clean, join)],
            &[src],
        );

        let (count, subst, eliminated) = run_copy_propagation(func);
        assert_eq!(count, 0);
        assert!(subst.is_empty());
        assert!(!eliminated.contains(&copy));
    }

    #[test]
    fn availability_rejects_production_copy_before_first_loop_definition() {
        let [entry, use_node, copy] = [0x10, 0x20, 0x30];
        let [src, dst, used] = [1, 2, 3];
        let func = synthetic_function(
            entry,
            vec![
                (entry, RTLInst::Inop),
                (
                    use_node,
                    RTLInst::Iop(Operation::Oaddimm(1), Arc::new(vec![dst]), used),
                ),
                (
                    copy,
                    RTLInst::Iop(Operation::Omove, Arc::new(vec![src]), dst),
                ),
            ],
            &[(entry, use_node), (use_node, copy), (copy, use_node)],
            &[src],
        );

        let (count, subst, eliminated) = run_copy_propagation(func);
        assert_eq!(count, 0);
        assert!(subst.is_empty());
        assert!(!eliminated.contains(&copy));
    }

    #[test]
    fn availability_retains_production_copy_on_straight_line() {
        let [copy, use_node, exit] = [0x10, 0x20, 0x30];
        let [src, dst, result] = [1, 2, 3];
        let func = synthetic_function(
            copy,
            vec![
                (
                    copy,
                    RTLInst::Iop(Operation::Omove, Arc::new(vec![src]), dst),
                ),
                (
                    use_node,
                    RTLInst::Iop(Operation::Oaddimm(1), Arc::new(vec![dst]), result),
                ),
                (exit, RTLInst::Ireturn(result)),
            ],
            &[(copy, use_node), (use_node, exit)],
            &[src],
        );

        let (count, subst, eliminated) = run_copy_propagation(func);
        assert_eq!(count, 1);
        assert_eq!(subst.get(&dst), Some(&src));
        assert!(eliminated.contains(&copy));
    }

    #[test]
    fn availability_carries_production_inline_expression_def_to_use() {
        let [def, use_node, exit] = [0x10, 0x20, 0x30];
        let [source, temp, result] = [1, 2, 3];
        let func = synthetic_function(
            def,
            vec![
                (
                    def,
                    RTLInst::Iop(Operation::Oaddimm(1), Arc::new(vec![source]), temp),
                ),
                (
                    use_node,
                    RTLInst::Iop(Operation::Oadd, Arc::new(vec![temp, source]), result),
                ),
                (exit, RTLInst::Ireturn(result)),
            ],
            &[(def, use_node), (use_node, exit)],
            &[source],
        );

        let du = DefUseInfo::build(&func);
        let liveness = LivenessInfo::build(&func, &du);
        assert!(find_inline_temps(&func, &du, &liveness).contains(&temp));
    }

    #[test]
    fn availability_rejects_production_inline_expression_on_bypass() {
        let [entry, def, bypass, use_node, exit] = [0x10, 0x20, 0x30, 0x40, 0x50];
        let [source, temp, result] = [1, 2, 3];
        let func = synthetic_function(
            entry,
            vec![
                (entry, RTLInst::Inop),
                (
                    def,
                    RTLInst::Iop(Operation::Oaddimm(1), Arc::new(vec![source]), temp),
                ),
                (bypass, RTLInst::Inop),
                (
                    use_node,
                    RTLInst::Iop(Operation::Oadd, Arc::new(vec![temp, source]), result),
                ),
                (exit, RTLInst::Ireturn(result)),
            ],
            &[
                (entry, def),
                (entry, bypass),
                (def, use_node),
                (bypass, use_node),
                (use_node, exit),
            ],
            &[source],
        );

        let du = DefUseInfo::build(&func);
        let liveness = LivenessInfo::build(&func, &du);
        assert!(!find_inline_temps(&func, &du, &liveness).contains(&temp));
    }

    #[test]
    fn availability_rejects_production_inline_before_first_loop_definition() {
        let [entry, use_node, def] = [0x10, 0x20, 0x30];
        let [source, temp, result] = [1, 2, 3];
        let func = synthetic_function(
            entry,
            vec![
                (entry, RTLInst::Inop),
                (
                    use_node,
                    RTLInst::Iop(Operation::Oadd, Arc::new(vec![temp, source]), result),
                ),
                (
                    def,
                    RTLInst::Iop(Operation::Oaddimm(1), Arc::new(vec![source]), temp),
                ),
            ],
            &[(entry, use_node), (use_node, def), (def, use_node)],
            &[source],
        );

        let du = DefUseInfo::build(&func);
        let liveness = LivenessInfo::build(&func, &du);
        assert!(!find_inline_temps(&func, &du, &liveness).contains(&temp));
    }

    #[test]
    fn dispatch_entry_uses_cfg_incoming_edges_not_node_order() {
        let region = HashSet::from([0x100, 0x200, 0x300]);
        let edges = vec![(0x50, 0x200), (0x200, 0x100), (0x100, 0x300)];

        assert_eq!(unique_external_cfg_entry(&region, &edges), Some(0x200));
        assert_eq!(
            unique_external_cfg_entry(&region, &[(0x50, 0x200), (0x60, 0x100)]),
            None
        );
    }

    #[test]
    fn recovered_jump_table_edges_keep_pre_dispatch_values_live() {
        let func = 0x9000;
        let entry = 0x900;
        let dispatch = 0x700;
        // Deliberately reverse every numeric order: only the explicit table
        // edge and raw `next` chain may connect the dispatch to its case.
        let raw_case = 0x300;
        let case = 0x100;
        let ret = 0x80;
        let incoming = 1;
        let saved = 2;
        let result = 3;
        let mut db = DecompileDB::default();

        for (node, inst) in [
            (
                entry,
                RTLInst::Iop(Operation::Omove, Arc::new(vec![incoming]), saved),
            ),
            (
                dispatch,
                RTLInst::Ibranch(Either::Left("recovered_dispatch")),
            ),
            (
                case,
                RTLInst::Iop(Operation::Oaddimm(1), Arc::new(vec![saved]), result),
            ),
            (ret, RTLInst::Ireturn(result)),
        ] {
            db.rel_push("rtl_inst_candidate", (node, inst));
        }
        for node in [entry, dispatch, raw_case, case, ret] {
            db.rel_push("instr_in_function", (node, func));
        }
        db.rel_push("emit_function", (func, "jump_table_liveness", entry));
        db.rel_push("emit_function_param_candidate", (func, incoming));
        db.rel_push("rtl_succ_candidate", (entry, dispatch));
        db.rel_push("jump_table_target", (dispatch, 0usize, raw_case));
        db.rel_push("next", (raw_case, case));
        db.rel_push("rtl_succ_candidate", (case, ret));

        let context = PassContext::load(&db);
        assert_eq!(
            context.functions[&func]
                .succs
                .get(&dispatch)
                .map(Vec::as_slice),
            Some([case].as_slice())
        );

        optimize_rtl_candidates(&mut db).expect("function must be optimized");

        assert!(db
            .rel_iter::<(u64, RTLInst)>("rtl_inst")
            .any(|(node, inst)| {
                *node == case
                    && matches!(
                        inst,
                        RTLInst::Iop(Operation::Oaddimm(1), args, dst)
                            if args.as_slice() == [incoming] && *dst == result
                    )
            }));
        assert!(db
            .rel_iter::<(u64, u64)>("rtl_next")
            .any(|edge| *edge == (dispatch, case)));
        assert!(!db
            .rel_iter::<(u64,)>("dead_store")
            .any(|&(node,)| node == entry));
    }

    #[test]
    fn pass_context_resolves_dropped_branch_targets_through_structural_next() {
        let func: u64 = 0x1000;
        let branch: u64 = 0x800;
        let raw_target: u64 = 0x900;
        // Deliberately reverse the numeric order of the structural chain.
        let skipped: u64 = 0x100;
        let semantic_target: u64 = 0x200;
        let synthetic = branch | (1u64 << 62);
        let mut db = DecompileDB::default();

        db.rel_push(
            "rtl_inst_candidate",
            (branch, RTLInst::Ibranch(Either::Right(raw_target))),
        );
        db.rel_push("rtl_inst_candidate", (semantic_target, RTLInst::Ireturn(1)));
        db.rel_push(
            "rtl_inst_candidate",
            (
                synthetic,
                RTLInst::Iop(Operation::Olongconst(0), Arc::new(vec![]), 2),
            ),
        );
        db.rel_push("rtl_succ_candidate", (synthetic, semantic_target));
        db.rel_push("next", (raw_target, skipped));
        db.rel_push("next", (skipped, semantic_target));
        for node in [branch, raw_target, skipped, semantic_target, synthetic] {
            db.rel_push("instr_in_function", (node, func));
        }
        db.rel_push("emit_function", (func, "structural_next", branch));

        let context = PassContext::load(&db);
        let function = context.functions.get(&func).expect("function loaded");
        assert_eq!(
            function.succs.get(&branch).map(Vec::as_slice),
            Some([semantic_target].as_slice())
        );
        assert_ne!(
            function.succs.get(&branch).map(Vec::as_slice),
            Some([synthetic].as_slice()),
            "numeric successor guessing routed the branch into a synthetic node"
        );
    }

    #[test]
    fn pass_context_interposes_rtl_only_semantic_fallthrough() {
        let func = 0x9000;
        // Deliberately reverse numeric order. Only `next` and the candidate
        // edges describe execution.
        let [entry, source, materialized, jcc, taken, fallthrough] =
            [0x900, 0x800, 0x200, 0x700, 0x100, 0x80];
        let [base, address, delimiter, loaded] = [1, 2, 3, 4];
        let mut db = DecompileDB::default();

        for (node, inst) in [
            (
                entry,
                RTLInst::Iload(
                    MemoryChunk::MInt8Unsigned,
                    Addressing::Aindexed(0),
                    Arc::new(vec![base]),
                    delimiter,
                ),
            ),
            (
                source,
                RTLInst::Iop(Operation::Oaddlimm(-1), Arc::new(vec![base]), address),
            ),
            (
                materialized,
                RTLInst::Iload(
                    MemoryChunk::MInt8Unsigned,
                    Addressing::Aindexed(0),
                    Arc::new(vec![address]),
                    loaded,
                ),
            ),
            (
                jcc,
                RTLInst::Icond(
                    Condition::Ccomp(Comparison::Cne),
                    Arc::new(vec![loaded, delimiter]),
                    Either::Right(taken),
                    Either::Right(fallthrough),
                ),
            ),
            (taken, RTLInst::Ireturn(base)),
            (fallthrough, RTLInst::Ireturn(base)),
        ] {
            db.rel_push("rtl_inst_candidate", (node, inst));
            db.rel_push("instr_in_function", (node, func));
        }
        db.rel_push("emit_function", (func, "interposed_fallthrough", entry));
        db.rel_push("emit_function_param_candidate", (func, base));
        for edge in [
            (entry, source),
            // These are Linear's stale skip-over edges. RTL has since
            // materialized `materialized -> jcc` between them and the source.
            (source, taken),
            (source, fallthrough),
            (materialized, jcc),
            (jcc, taken),
            (jcc, fallthrough),
        ] {
            db.rel_push("rtl_succ_candidate", edge);
        }
        for edge in [
            (entry, source),
            (source, materialized),
            (materialized, jcc),
            (jcc, fallthrough),
        ] {
            db.rel_push("next", edge);
        }

        let context = PassContext::load(&db);
        let function = &context.functions[&func];
        assert_eq!(
            function.succs.get(&source).map(Vec::as_slice),
            Some([materialized].as_slice())
        );
        assert!(reachable_from(function, entry).contains(&jcc));

        let du = DefUseInfo::build(function);
        let liveness = LivenessInfo::build(function, &du);
        assert!(liveness.live_out[&entry].contains(&delimiter));
    }

    #[test]
    fn pass_context_does_not_cross_a_function_boundary_to_find_a_successor() {
        let func: u64 = 0x1000;
        let other_func: u64 = 0x2000;
        let branch: u64 = 0x3052;
        let raw_target: u64 = 0x305c;
        let outside: u64 = 0x3060;
        let synthetic = branch | (1u64 << 62);
        let mut db = DecompileDB::default();

        db.rel_push(
            "rtl_inst_candidate",
            (branch, RTLInst::Ibranch(Either::Right(raw_target))),
        );
        db.rel_push(
            "rtl_inst_candidate",
            (
                synthetic,
                RTLInst::Iop(Operation::Olongconst(0), Arc::new(vec![]), 2),
            ),
        );
        db.rel_push("next", (raw_target, outside));
        for node in [branch, raw_target, synthetic] {
            db.rel_push("instr_in_function", (node, func));
        }
        db.rel_push("instr_in_function", (outside, other_func));
        db.rel_push("emit_function", (func, "boundary", branch));

        let context = PassContext::load(&db);
        let function = context.functions.get(&func).expect("function loaded");
        assert!(
            !function.succs.contains_key(&branch),
            "a terminal branch acquired a successor from numeric node order"
        );
    }

    #[test]
    fn copy_used_by_memory_indirect_call_side_relation_is_retained() {
        let copy = 0x10;
        let call = 0x20;
        let ret = 0x30;
        let param = 1;
        let copied = 2;
        let callee_temp = 3;

        let mut func = FunctionCFG {
            func_addr: 0x1000,
            entry: copy,
            nodes: BTreeSet::from([copy, call, ret]),
            inst: BTreeMap::from([
                (
                    copy,
                    RTLInst::Iop(Operation::Omove, Arc::new(vec![param]), copied),
                ),
                (
                    call,
                    RTLInst::Icall(None, Either::Left(callee_temp), Arc::new(vec![]), None, ret),
                ),
                (ret, RTLInst::Ireturn(param)),
            ]),
            succs: HashMap::from([(copy, vec![call]), (call, vec![ret])]),
            preds: HashMap::from([(call, vec![copy]), (ret, vec![call])]),
            params: HashSet::from([param]),
            mem_call_addr_uses: HashMap::from([(call, vec![copied])]),
            dispatch_entry_nodes: HashSet::new(),
            escaped_slot_regs: HashSet::new(),
            multi_def_slot_regs: HashSet::new(),
            shared_nodes: HashSet::new(),
        };

        let du = DefUseInfo::build(&func);
        let liveness = LivenessInfo::build(&func, &du);
        let (count, subst, eliminated) = copy_propagation(&mut func, &du, &liveness);

        assert_eq!(count, 0);
        assert!(subst.is_empty());
        assert!(eliminated.is_empty());
        assert!(matches!(
            func.inst.get(&copy),
            Some(RTLInst::Iop(Operation::Omove, args, dst))
                if args.as_slice() == [param] && *dst == copied
        ));
    }

    #[test]
    fn optimizer_kill_relations_include_every_fixpoint_iteration() {
        let func: u64 = 0x1000;
        let [producer, copy, dead_use, ret]: [u64; 4] = [0x10, 0x20, 0x30, 0x40];
        let [param, produced, copied, unused]: [u64; 4] = [0x100, 0x101, 0x102, 0x103];
        let mut db = DecompileDB::default();

        for (node, inst) in [
            (
                producer,
                RTLInst::Iop(Operation::Oaddimm(1), Arc::new(vec![param]), produced),
            ),
            (
                copy,
                RTLInst::Iop(Operation::Omove, Arc::new(vec![produced]), copied),
            ),
            (
                dead_use,
                RTLInst::Iop(Operation::Oaddimm(1), Arc::new(vec![copied]), unused),
            ),
            (ret, RTLInst::Ireturn(param)),
        ] {
            db.rel_push("rtl_inst_candidate", (node, inst));
            db.rel_push("instr_in_function", (node, func));
        }
        for edge in [(producer, copy), (copy, dead_use), (dead_use, ret)] {
            db.rel_push("rtl_succ_candidate", edge);
        }
        db.rel_push("emit_function", (func, "synthetic", producer));
        db.rel_push("emit_function_param_candidate", (func, param));

        optimize_rtl_candidates(&mut db).expect("synthetic function must be optimized");

        let dead_stores: Vec<_> = db
            .rel_iter::<(u64,)>("dead_store")
            .map(|&(node,)| node)
            .collect();
        let copies: Vec<_> = db
            .rel_iter::<(u64,)>("copy_eliminated")
            .map(|&(node,)| node)
            .collect();
        assert_eq!(dead_stores, vec![producer, dead_use]);
        assert_eq!(copies, vec![copy]);
        assert!(matches!(
            db.rel_iter::<(u64, RTLInst)>("rtl_inst").next(),
            Some((node, RTLInst::Ireturn(reg))) if *node == ret && *reg == param
        ));

        assert!(RTLOptimizePass.outputs().contains(&"dead_store"));
        assert!(RTLOptimizePass.outputs().contains(&"copy_eliminated"));
    }

    #[test]
    fn shared_tail_liveness_preserves_each_owners_private_definition() {
        let [func_a, func_b] = [0x9000, 0x1000];
        // Deliberately put the shared tail below both entries: ownership and
        // liveness must come from explicit CFG structure, never node order.
        let [entry_a, entry_b, shared_use, shared_ret] = [0x900, 0x700, 0x50, 0x40];
        let [incoming, result] = [0x101, 0x102];
        let mut db = DecompileDB::default();

        for (node, inst) in [
            (
                entry_a,
                RTLInst::Iop(Operation::Ointconst(1), Arc::new(vec![]), incoming),
            ),
            (
                entry_b,
                RTLInst::Iop(Operation::Ointconst(2), Arc::new(vec![]), incoming),
            ),
            (
                shared_use,
                RTLInst::Iop(Operation::Oaddimm(1), Arc::new(vec![incoming]), result),
            ),
            (shared_ret, RTLInst::Ireturn(result)),
        ] {
            db.rel_push("rtl_inst_candidate", (node, inst));
        }
        for (node, func) in [
            (entry_a, func_a),
            (entry_b, func_b),
            (shared_use, func_a),
            (shared_use, func_b),
            (shared_ret, func_a),
            (shared_ret, func_b),
        ] {
            db.rel_push("instr_in_function", (node, func));
        }
        for edge in [
            (entry_a, shared_use),
            (entry_b, shared_use),
            (shared_use, shared_ret),
        ] {
            db.rel_push("rtl_succ_candidate", edge);
        }
        db.rel_push("emit_function", (func_a, "owner_a", entry_a));
        db.rel_push("emit_function", (func_b, "owner_b", entry_b));

        let ctx = PassContext::load(&db);
        for func in [func_a, func_b] {
            assert!(ctx.functions[&func].inst.contains_key(&shared_use));
            assert!(ctx.functions[&func].shared_nodes.contains(&shared_use));
        }

        optimize_rtl_candidates(&mut db).expect("both owner CFGs must be optimized");

        let final_insts: BTreeMap<_, _> =
            db.rel_iter::<(u64, RTLInst)>("rtl_inst").cloned().collect();
        assert!(matches!(
            final_insts.get(&entry_a),
            Some(RTLInst::Iop(Operation::Ointconst(1), args, dst))
                if args.is_empty() && *dst == incoming
        ));
        assert!(matches!(
            final_insts.get(&entry_b),
            Some(RTLInst::Iop(Operation::Ointconst(2), args, dst))
                if args.is_empty() && *dst == incoming
        ));
        assert_eq!(
            final_insts
                .keys()
                .filter(|&&node| node == shared_use)
                .count(),
            1,
            "one physical shared node was emitted more than once"
        );
        assert!(
            !db.rel_iter::<(u64,)>("dead_store")
                .any(|&(node,)| node == entry_a || node == entry_b),
            "an owner-private definition used by the shared tail was killed"
        );
        assert!(
            !db.rel_iter::<(u64, Constant)>("single_def_const")
                .any(|&(reg, _)| reg == incoming),
            "a two-predecessor shared register web was exported as single-def"
        );
    }

    #[test]
    fn callee_observed_neighbor_aliases_are_loaded_as_escaped_dse_roots() {
        let mut db = DecompileDB::default();
        let [func, entry, canonical, point_local_alias] = synthetic_ids();

        db.rel_push(
            "rtl_inst_candidate",
            (
                entry,
                RTLInst::Iop(
                    Operation::Olongconst(7),
                    Arc::new(vec![]),
                    point_local_alias,
                ),
            ),
        );
        db.rel_push("instr_in_function", (entry, func));
        db.rel_push("emit_function", (func, "synthetic", entry));
        db.rel_push("slot_escaped_region_canonical", (func, 40_i64, canonical));
        db.rel_push("stack_var", (func, entry, 40_i64, point_local_alias));

        let ctx = PassContext::load(&db);
        let roots = &ctx.functions[&func].escaped_slot_regs;
        assert!(roots.contains(&canonical));
        assert!(roots.contains(&point_local_alias));
    }

    // A slot written on two paths keeps only the definitions whose frame
    // anchor was recovered, so the RTL def count can read as one.  The slot's
    // reaching definitions are what decide constness.
    #[test]
    fn a_slot_read_with_two_reaching_defs_is_not_single_def() {
        let mut db = DecompileDB::default();
        let [func, entry, other_def, read, slot_reg] = synthetic_ids();
        let slot: i64 = 83;

        db.rel_push(
            "rtl_inst_candidate",
            (
                entry,
                RTLInst::Iop(Operation::Ointconst(0), Arc::new(vec![]), slot_reg),
            ),
        );
        db.rel_push("rtl_inst_candidate", (read, RTLInst::Ireturn(slot_reg)));
        db.rel_push("instr_in_function", (entry, func));
        db.rel_push("instr_in_function", (read, func));
        db.rel_push("emit_function", (func, "synthetic", entry));
        db.rel_push("rtl_succ_candidate", (entry, read));
        db.rel_push("stack_var", (func, entry, slot, slot_reg));
        db.rel_push("stack_var", (func, read, slot, slot_reg));
        db.rel_push("stack_def_used", (entry, "", slot, read, "", slot));
        db.rel_push("stack_def_used", (other_def, "", slot, read, "", slot));

        let ctx = PassContext::load(&db);
        assert!(
            ctx.functions[&func].multi_def_slot_regs.contains(&slot_reg),
            "a slot read by two reaching definitions was left foldable"
        );

        // One reaching definition leaves the slot foldable.
        let mut single = DecompileDB::default();
        single.rel_push(
            "rtl_inst_candidate",
            (
                entry,
                RTLInst::Iop(Operation::Ointconst(0), Arc::new(vec![]), slot_reg),
            ),
        );
        single.rel_push("rtl_inst_candidate", (read, RTLInst::Ireturn(slot_reg)));
        single.rel_push("instr_in_function", (entry, func));
        single.rel_push("instr_in_function", (read, func));
        single.rel_push("emit_function", (func, "synthetic", entry));
        single.rel_push("rtl_succ_candidate", (entry, read));
        single.rel_push("stack_var", (func, entry, slot, slot_reg));
        single.rel_push("stack_var", (func, read, slot, slot_reg));
        single.rel_push("stack_def_used", (entry, "", slot, read, "", slot));

        let single_ctx = PassContext::load(&single);
        assert!(
            single_ctx.functions[&func].multi_def_slot_regs.is_empty(),
            "a slot with one reaching definition must stay foldable"
        );
    }

    #[test]
    fn a_multi_def_slot_reg_does_not_fold_a_runtime_branch() {
        let [def_a, def_b, branch, taken, untaken, slot_reg, other_reg] = synthetic_ids();
        let build = || FunctionCFG {
            func_addr: 0x1000,
            entry: def_a,
            nodes: BTreeSet::from([def_a, def_b, branch, taken, untaken]),
            inst: BTreeMap::from([
                (
                    def_a,
                    RTLInst::Iop(Operation::Ointconst(0), Arc::new(vec![]), slot_reg),
                ),
                (
                    def_b,
                    RTLInst::Iop(Operation::Ointconst(0), Arc::new(vec![]), other_reg),
                ),
                (
                    branch,
                    RTLInst::Icond(
                        Condition::Ccomp(Comparison::Ceq),
                        Arc::new(vec![slot_reg, other_reg]),
                        Either::Right(taken),
                        Either::Right(untaken),
                    ),
                ),
                (taken, RTLInst::Ireturn(slot_reg)),
                (untaken, RTLInst::Ireturn(other_reg)),
            ]),
            succs: HashMap::from([
                (def_a, vec![def_b]),
                (def_b, vec![branch]),
                (branch, vec![taken, untaken]),
            ]),
            preds: HashMap::from([
                (def_b, vec![def_a]),
                (branch, vec![def_b]),
                (taken, vec![branch]),
                (untaken, vec![branch]),
            ]),
            params: HashSet::new(),
            mem_call_addr_uses: HashMap::new(),
            dispatch_entry_nodes: HashSet::new(),
            escaped_slot_regs: HashSet::new(),
            multi_def_slot_regs: HashSet::new(),
            shared_nodes: HashSet::new(),
        };

        let mut foldable = build();
        assert!(
            fold_static_eq_branches(&mut foldable),
            "two genuinely single-def constants still fold"
        );

        let mut guarded = build();
        guarded.multi_def_slot_regs.insert(slot_reg);
        assert!(
            !fold_static_eq_branches(&mut guarded),
            "a slot with several reaching definitions folded a runtime branch"
        );
        assert!(
            matches!(guarded.inst.get(&branch), Some(RTLInst::Icond(..))),
            "the branch was rewritten despite the slot not being constant"
        );
    }
}
