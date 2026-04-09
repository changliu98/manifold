

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::decompile::passes::rtl_pass::RTLPassProgram;
use crate::run_pass;
use crate::x86::op::Operation;
use crate::x86::types::*;

use either::Either;
use log::info;
use rayon::prelude::*;


pub struct RtlOptPass;

impl IRPass for RtlOptPass {
    fn name(&self) -> &'static str { "rtl_opt" }

    fn run(&self, db: &mut DecompileDB) {
        // Union-find based register coalescing (produces xtl_canonical)
        crate::decompile::analysis::rtl_variable::compute_variable_assignment(db);

        // Re-evaluate RTL rules with xtl_canonical from variable assignment
        run_pass!(db, RTLPassProgram);
        crate::decompile::passes::rtl_pass::trim_direct_call_args_to_callee_arity(db);

        // Convert LTL builtins to RTL (after 2nd Ascent evaluation, preserving original order)
        crate::decompile::passes::rtl_pass::convert_and_push_builtins(db);

        let mut ctx = PassContext::load(db);
        if ctx.functions.is_empty() {
            return;
        }

        let var_types = std::mem::take(&mut ctx.var_types);
        let split_counter = AtomicU64::new(0);

        // Partition var_types by function: each function gets types for its own registers
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

        // Process all functions in parallel
        let results: Vec<_> = ctx.functions.par_iter_mut()
            .map(|(&func_addr, func)| {
                let mut func_var_types = per_func_var_types.lock().unwrap()
                    .remove(&func_addr).unwrap_or_default();

                let zero_rewrites = self_zero_rewrite(func);

                let mut copies = 0usize;
                let mut dead = 0usize;
                loop {
                    let du = DefUseInfo::build(func);
                    let liveness = LivenessInfo::build(func, &du);

                    let (c, copy_subst) = copy_propagation(func, &du, &liveness);
                    // Transfer types from eliminated copy destinations to their
                    // sources. The RTL pass assigns types to call-arg-setup
                    // copies (the Omove destinations); after copy propagation
                    // replaces those with the original registers, the originals
                    // need the type info for coalescing to work.
                    for (&dst, &src) in &copy_subst {
                        if let Some(&ty) = func_var_types.get(&dst) {
                            func_var_types.entry(src).or_insert(ty);
                        }
                    }
                    let d = dead_store_elimination(func, &du, &liveness);

                    if c == 0 && d == 0 {
                        break;
                    }
                    copies += c;
                    dead += d;
                }

                // Single rebuild after copy-prop/DSE loop for remaining passes
                let mut du = DefUseInfo::build(func);
                let mut liveness = LivenessInfo::build(func, &du);

                // Propagate types through surviving Omoves: if the copy
                // source has a type but the destination doesn't, transfer it.
                for (_, inst) in func.inst.iter() {
                    if let RTLInst::Iop(Operation::Omove, args, dst) = inst {
                        if args.len() == 1 && !func_var_types.contains_key(dst) {
                            if let Some(&ty) = func_var_types.get(&args[0]) {
                                func_var_types.insert(*dst, ty);
                            }
                        }
                    }
                }

                // Record single-def registers before coalescing. Merge
                // targets that were single-def gain extra defs only from
                // absorbed same-type registers — splitting those apart is
                // counterproductive.
                let single_def_before: HashSet<RTLReg> = du.defs.iter()
                    .filter(|(_, defs)| defs.len() == 1)
                    .map(|(&reg, _)| reg)
                    .collect();

                let (coalesced, merge_targets) = live_range_coalescing(func, &du, &liveness, &mut func_var_types);

                // Rebuild only if coalescing changed the function
                if coalesced > 0 {
                    du = DefUseInfo::build(func);
                    liveness = LivenessInfo::build(func, &du);
                }

                // Merge targets that were single-def before coalescing: their
                // multiple defs now come entirely from coalescing, not from
                // original register reuse. Don't split these.
                let no_split: HashSet<RTLReg> = merge_targets.iter()
                    .filter(|r| single_def_before.contains(r))
                    .copied()
                    .collect();

                let mut local_counter = split_counter.fetch_add(1000, Ordering::Relaxed);
                let splits = variable_splitting(func, &du, &liveness, &mut func_var_types, &mut local_counter, &no_split);

                let nops = nop_collapse(func);

                // Rebuild only if splitting or nop collapse changed something
                if splits > 0 || nops > 0 {
                    du = DefUseInfo::build(func);
                    liveness = LivenessInfo::build(func, &du);
                }

                let inlines = find_inline_temps(func, &du, &liveness);

                (copies, dead, nops, coalesced, zero_rewrites, splits, inlines, func_var_types)
            })
            .collect();

        // Merge results
        let mut total_copies = 0usize;
        let mut total_dead = 0usize;
        let mut total_nops = 0usize;
        let mut total_coalesced = 0usize;
        let mut total_inline = 0usize;
        let mut total_zero_rewrites = 0usize;
        let mut total_splits = 0usize;
        let mut merged_var_types = var_types;

        for (copies, dead, nops, coalesced, zero_rewrites, splits, inlines, func_vt) in results {
            total_copies += copies;
            total_dead += dead;
            total_nops += nops;
            total_coalesced += coalesced;
            total_zero_rewrites += zero_rewrites;
            total_splits += splits;
            total_inline += inlines.len();
            ctx.inline_temps.extend(inlines);
            // Merge per-function var_types back (function writes take precedence)
            merged_var_types.extend(func_vt);
        }

        ctx.var_types = merged_var_types;

        let has_changes = total_copies > 0 || total_dead > 0 || total_nops > 0
            || total_coalesced > 0 || total_inline > 0 || total_zero_rewrites > 0
            || total_splits > 0;
        if has_changes {
            info!(
                "rtl_opt: {} copies propagated, {} dead stores eliminated, {} nops collapsed, {} vars coalesced, {} inline temps, {} self-zero rewrites, {} vars split",
                total_copies, total_dead, total_nops, total_coalesced, total_inline, total_zero_rewrites, total_splits
            );
        }
        ctx.write_back(db);
    }

    fn inputs(&self) -> &'static [&'static str] {
        // Must include ALL of RTLPassProgram's inputs since we re-run it via run_pass!(db, RTLPassProgram) to re-evaluate with xtl_canonical.
        static INPUTS: std::sync::LazyLock<Vec<&'static str>> = std::sync::LazyLock::new(|| {
            let rtl_inputs = RTLPassProgram::inputs_only();
            let own = &[
                "rtl_inst_candidate",
                "rtl_succ_candidate",
                "instr_in_function",
                "emit_function",
                "emit_function_param_candidate",
                "emit_var_type_candidate",
            ];
            let mut combined: Vec<&'static str> = rtl_inputs.iter().copied().collect();
            for &s in own {
                if !combined.contains(&s) {
                    combined.push(s);
                }
            }
            combined
        });
        &INPUTS
    }

    fn outputs(&self) -> &'static [&'static str] {
        static OUTPUTS: std::sync::LazyLock<Vec<&'static str>> = std::sync::LazyLock::new(|| {
            let rtl_outputs = RTLPassProgram::rule_outputs();
            let own = &[
                "rtl_inst",
                "rtl_succ",
                "instr_in_function",
                "emit_inline_temp",
            ];
            let mut combined: Vec<&'static str> = rtl_outputs.iter().copied().collect();
            for &s in own {
                if !combined.contains(&s) {
                    combined.push(s);
                }
            }
            combined
        });
        &OUTPUTS
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
        let var_types: HashMap<RTLReg, XType> = db
            .rel_iter::<(RTLReg, XType)>("emit_var_type_candidate")
            .cloned()
            .collect();

        let node_to_func: HashMap<Node, Address> = instr_in_func.iter()
            .map(|&(n, f)| (n, f))
            .collect();

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
                        score + arg_bonus
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

            functions.insert(func_addr, FunctionCFG {
                func_addr,
                entry,
                nodes,
                inst: insts.clone(),
                succs,
                preds,
                params: func_params.remove(&func_addr).unwrap_or_default(),
            });
        }

        PassContext { functions, var_types, inline_temps: HashSet::new() }
    }

    fn write_back(self, db: &mut DecompileDB) {
        let new_insts = ascent::boxcar::Vec::<(Node, RTLInst)>::new();
        let new_succs = ascent::boxcar::Vec::<(Node, Node)>::new();
        let mut live_regs: HashSet<RTLReg> = HashSet::new();

        for (_func_addr, func) in &self.functions {
            for (&node, inst) in &func.inst {
                new_insts.push((node, inst.clone()));
                collect_inst_regs(inst, &mut live_regs);
            }
            for (&src, dsts) in &func.succs {
                if func.inst.contains_key(&src) {
                    for &dst in dsts {
                        new_succs.push((src, dst));
                    }
                }
            }
        }

        // Recompute single_def_const: variable IDs may be stale after coalescing/copy propagation.
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

        db.rel_set("rtl_inst", new_insts);
        db.rel_set("rtl_succ", new_succs);

        let inline_vec = ascent::boxcar::Vec::<RTLReg>::new();
        for &reg in &self.inline_temps {
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
            let (def, used) = inst_def_use(inst);
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

/// Check that src is not redefined on any path from copy_node to any use of dst; only blocks propagation when a src redef is actually between the copy and a dst use.
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

    // Redefs of src other than at copy_node
    let redefs: Vec<Node> = src_def_nodes.iter()
        .filter(|&&n| n != copy_node)
        .copied()
        .collect();
    if redefs.is_empty() {
        return true;
    }

    // Forward: nodes reachable from copy
    let forward = reachable_from(func, copy_node);

    // Quick filter: only redefs that are forward-reachable matter
    let reachable_redefs: Vec<Node> = redefs.iter()
        .filter(|n| forward.contains(n))
        .copied()
        .collect();
    if reachable_redefs.is_empty() {
        return true;
    }

    // Backward: nodes that can reach any dst_use
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

    // Unsafe if any redef is on a path from copy to a use
    !reachable_redefs.iter().any(|n| backward.contains(n))
}

/// Rewrite self-zeroing idioms (`xor reg, reg`, `sub reg, reg`) to explicit zero constants so downstream type inference can assign the correct type independently of the register's other uses.
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
        // SAFETY: Only inline Iop temps; Iload is unsafe without aliasing/intervening store checks.
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


pub(crate) fn live_range_coalescing(
    func: &mut FunctionCFG,
    du: &DefUseInfo,
    liveness: &LivenessInfo,
    var_types: &mut HashMap<RTLReg, XType>,
) -> (usize, HashSet<RTLReg>) {
    if func.nodes.len() > 20000 {
        return (0, HashSet::new());
    }

    let mut interferes: HashMap<RTLReg, HashSet<RTLReg>> = HashMap::new();

    for (&node, _) in &func.inst {
        if let Some(&def_reg) = du.node_def.get(&node) {
            if let Some(live_out) = liveness.live_out.get(&node) {
                for &live_reg in live_out {
                    if live_reg != def_reg {
                        interferes.entry(def_reg).or_default().insert(live_reg);
                        interferes.entry(live_reg).or_default().insert(def_reg);
                    }
                }
            }
        }
    }

    let all_regs: BTreeSet<RTLReg> = du.defs.keys()
        .chain(du.uses.keys())
        .copied()
        .collect();

    let mut by_type: BTreeMap<XType, Vec<RTLReg>> = BTreeMap::new();
    for &reg in &all_regs {
        if func.params.contains(&reg) { continue; }
        if let Some(&ty) = var_types.get(&reg) {
            by_type.entry(ty).or_default().push(reg);
        }
    }

    let mut rename: HashMap<RTLReg, RTLReg> = HashMap::new();

    for (_ty, regs) in &by_type {
        let mut reps: Vec<(RTLReg, HashSet<RTLReg>)> = Vec::new();

        for &reg in regs {
            if rename.contains_key(&reg) { continue; }

            let my_intf = interferes.get(&reg).cloned().unwrap_or_default();

            let mut merged = false;
            for (rep, rep_intf) in &mut reps {
                if !rep_intf.contains(&reg) && !my_intf.contains(rep) {
                    rename.insert(reg, *rep);
                    rep_intf.extend(my_intf.iter());
                    merged = true;
                    break;
                }
            }

            if !merged {
                reps.push((reg, my_intf));
            }
        }
    }

    if rename.is_empty() {
        return (0, HashSet::new());
    }

    let mut resolved: HashMap<RTLReg, RTLReg> = HashMap::new();
    for &src in rename.keys() {
        let mut target = src;
        let mut visited = HashSet::new();
        visited.insert(src);
        while let Some(&next) = rename.get(&target) {
            if !visited.insert(next) { break; }
            target = next;
        }
        resolved.insert(src, target);
    }

    let count = resolved.len();

    // Collect merge targets: registers that absorbed other registers.
    let merge_targets: HashSet<RTLReg> = resolved.values().copied().collect();

    for (_, inst) in func.inst.iter_mut() {
        *inst = rename_in_inst(inst, &resolved);
    }

    for (&old, &new) in &resolved {
        if let Some(ty) = var_types.remove(&old) {
            var_types.entry(new).or_insert(ty);
        }
    }

    (count, merge_targets)
}

pub(crate) fn rename_in_inst(inst: &RTLInst, map: &HashMap<RTLReg, RTLReg>) -> RTLInst {
    rename_in_inst_dual(inst, map, map)
}

/// Rename variables in an RTL instruction with separate def/use maps; prevents incorrect renaming during variable splitting.
fn rename_in_inst_dual(
    inst: &RTLInst,
    def_map: &HashMap<RTLReg, RTLReg>,
    use_map: &HashMap<RTLReg, RTLReg>,
) -> RTLInst {
    match inst {
        RTLInst::Inop => RTLInst::Inop,
        RTLInst::Iop(op, args, dst) => {
            let new_args = subst_args(args, use_map);
            let new_dst = def_map.get(dst).copied().unwrap_or(*dst);
            RTLInst::Iop(op.clone(), new_args, new_dst)
        }
        RTLInst::Iload(chunk, addr, args, dst) => {
            let new_args = subst_args(args, use_map);
            let new_dst = def_map.get(dst).copied().unwrap_or(*dst);
            RTLInst::Iload(*chunk, addr.clone(), new_args, new_dst)
        }
        RTLInst::Istore(chunk, addr, args, src) => {
            let new_args = subst_args(args, use_map);
            let new_src = use_map.get(src).copied().unwrap_or(*src);
            RTLInst::Istore(*chunk, addr.clone(), new_args, new_src)
        }
        RTLInst::Icall(sig, callee, args, dst, next) => {
            let new_callee = match callee {
                Either::Left(r) => Either::Left(use_map.get(r).copied().unwrap_or(*r)),
                other => other.clone(),
            };
            let new_args = subst_args(args, use_map);
            let new_dst = dst.map(|d| def_map.get(&d).copied().unwrap_or(d));
            RTLInst::Icall(sig.clone(), new_callee, new_args, new_dst, *next)
        }
        RTLInst::Itailcall(sig, callee, args) => {
            let new_callee = match callee {
                Either::Left(r) => Either::Left(use_map.get(r).copied().unwrap_or(*r)),
                other => other.clone(),
            };
            let new_args = subst_args(args, use_map);
            RTLInst::Itailcall(sig.clone(), new_callee, new_args)
        }
        RTLInst::Ibuiltin(name, args, res) => {
            let new_args: Vec<_> = args.iter().map(|a| subst_ba(a, use_map)).collect();
            let new_res = subst_ba(res, def_map);
            RTLInst::Ibuiltin(name.clone(), new_args, new_res)
        }
        RTLInst::Icond(cond, args, ifso, ifnot) => {
            let new_args = subst_args(args, use_map);
            RTLInst::Icond(cond.clone(), new_args, ifso.clone(), ifnot.clone())
        }
        RTLInst::Ijumptable(reg, targets) => {
            let new_reg = use_map.get(reg).copied().unwrap_or(*reg);
            RTLInst::Ijumptable(new_reg, targets.clone())
        }
        RTLInst::Ibranch(target) => RTLInst::Ibranch(target.clone()),
        RTLInst::Ireturn(reg) => {
            let new_reg = use_map.get(reg).copied().unwrap_or(*reg);
            RTLInst::Ireturn(new_reg)
        }
    }
}

/// Split variables with multiple disconnected live ranges into separate variables so each reuse of a physical register (e.g., struct pointer then integer) can get its own C type.
pub(crate) fn variable_splitting(
    func: &mut FunctionCFG,
    du: &DefUseInfo,
    _liveness: &LivenessInfo,
    var_types: &mut HashMap<RTLReg, XType>,
    split_counter: &mut u64,
    coalesced_regs: &HashSet<RTLReg>,
) -> usize {
    if func.nodes.len() > 20000 {
        return 0;
    }

    let mut total_splits = 0;
    let mut def_rename: HashMap<Node, HashMap<RTLReg, RTLReg>> = HashMap::new();
    let mut use_rename: HashMap<Node, HashMap<RTLReg, RTLReg>> = HashMap::new();

    for (reg, def_nodes) in &du.defs {
        if def_nodes.len() <= 1 { continue; }
        if func.params.contains(reg) { continue; }
        // Skip registers whose multiple defs came entirely from
        // coalescing. Coalescing only merges same-type non-interfering
        // registers, so the absorbed defs all share the same RTL-pass
        // type. Splitting them apart would create redundant variables.
        //
        // Safe because: coalescing is type-gated (same XType bucket) and
        // interference-checked. The type_pass downstream resolves any
        // minor type_candidate conflicts (e.g., Xptr vs Xcharptr) by
        // priority — the merged result is a valid supertype.
        if coalesced_regs.contains(reg) { continue; }

        let use_nodes = match du.uses.get(reg) {
            Some(u) if !u.is_empty() => u,
            _ => continue,
        };

        let def_set: HashSet<Node> = def_nodes.iter().copied().collect();

        // For each use, find which defs reach it (backward walk stopping at defs)
        let mut use_reaching: HashMap<Node, Vec<Node>> = HashMap::new();
        for &use_node in use_nodes {
            let reaching = find_reaching_defs(func, use_node, &def_set);
            if !reaching.is_empty() {
                use_reaching.insert(use_node, reaching);
            }
        }

        // Build webs via union-find over def nodes
        let mut uf_parent: HashMap<Node, Node> = HashMap::new();
        let mut uf_rank: HashMap<Node, usize> = HashMap::new();
        for &d in def_nodes {
            uf_parent.insert(d, d);
            uf_rank.insert(d, 0);
        }

        for reaching in use_reaching.values() {
            if reaching.len() > 1 {
                let first = reaching[0];
                for &d in &reaching[1..] {
                    uf_union(&mut uf_parent, &mut uf_rank, first, d);
                }
            }
        }

        // Collect webs
        let mut web_members: HashMap<Node, Vec<Node>> = HashMap::new();
        for &d in def_nodes {
            let root = uf_find(&mut uf_parent, d);
            web_members.entry(root).or_default().push(d);
        }

        if web_members.len() <= 1 { continue; }

        // Sort webs: largest first (keep the largest, split the rest)
        let mut webs: Vec<Vec<Node>> = web_members.into_values().collect();
        webs.sort_by_key(|members| std::cmp::Reverse(members.len()));

        for members in webs.iter().skip(1) {
            *split_counter += 1;
            let new_reg = (1u64 << 63) | (1u64 << 62) | (*split_counter << 6);

            let web_defs: HashSet<Node> = members.iter().copied().collect();

            // Rename defs in this web
            for &def_node in &web_defs {
                def_rename.entry(def_node).or_default().insert(*reg, new_reg);
            }

            // Rename uses reached exclusively by defs in this web
            for (&use_node, reaching) in &use_reaching {
                if !reaching.is_empty() && reaching.iter().all(|d| web_defs.contains(d)) {
                    use_rename.entry(use_node).or_default().insert(*reg, new_reg);
                }
            }

            // Copy type info to new variable
            if let Some(xtype) = var_types.get(reg) {
                var_types.insert(new_reg, *xtype);
            }

            total_splits += 1;
        }
    }

    if def_rename.is_empty() && use_rename.is_empty() {
        return 0;
    }

    // Apply per-node renames with separate def/use maps to avoid incorrectly renaming a def when only the use should be renamed (or vice versa)
    let all_nodes: HashSet<Node> = def_rename.keys().chain(use_rename.keys()).copied().collect();
    let empty_map: HashMap<RTLReg, RTLReg> = HashMap::new();
    for node in all_nodes {
        if let Some(inst) = func.inst.get_mut(&node) {
            let d = def_rename.get(&node).unwrap_or(&empty_map);
            let u = use_rename.get(&node).unwrap_or(&empty_map);
            *inst = rename_in_inst_dual(inst, d, u);
        }
    }

    total_splits
}

/// Walk backward from `use_node` to find which defs of the variable reach it.
fn find_reaching_defs(
    func: &FunctionCFG,
    use_node: Node,
    def_set: &HashSet<Node>,
) -> Vec<Node> {
    let mut reaching = Vec::new();
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();

    visited.insert(use_node);

    // The use reads the PREVIOUS value, so look at predecessors.
    if let Some(preds) = func.preds.get(&use_node) {
        for &p in preds {
            if visited.insert(p) {
                queue.push_back(p);
            }
        }
    }

    while let Some(node) = queue.pop_front() {
        if def_set.contains(&node) {
            reaching.push(node);
            continue; // Don't look past this def
        }
        if let Some(preds) = func.preds.get(&node) {
            for &p in preds {
                if visited.insert(p) {
                    queue.push_back(p);
                }
            }
        }
    }

    reaching.sort();
    reaching.dedup();
    reaching
}

fn uf_find(parent: &mut HashMap<Node, Node>, x: Node) -> Node {
    let p = *parent.get(&x).unwrap_or(&x);
    if p == x { return x; }
    let root = uf_find(parent, p);
    parent.insert(x, root);
    root
}

fn uf_union(parent: &mut HashMap<Node, Node>, rank: &mut HashMap<Node, usize>, a: Node, b: Node) {
    let ra = uf_find(parent, a);
    let rb = uf_find(parent, b);
    if ra == rb { return; }
    let rank_a = *rank.get(&ra).unwrap_or(&0);
    let rank_b = *rank.get(&rb).unwrap_or(&0);
    if rank_a < rank_b {
        parent.insert(ra, rb);
    } else if rank_a > rank_b {
        parent.insert(rb, ra);
    } else {
        parent.insert(rb, ra);
        rank.insert(ra, rank_a + 1);
    }
}
