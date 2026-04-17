use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::decompile::passes::rtl_pass::fresh_xtl_reg;
use crate::run_pass;
use crate::x86::mach::Mreg;
use crate::x86::op::Addressing;
use crate::x86::types::*;
use ascent::ascent_par;

const CALL_SITE_CONFIRM_THRESHOLD: f64 = 0.5;

// Mode aggregator: value with highest count, ties broken by larger value.
pub(crate) fn majority_usize<'a>(inp: impl Iterator<Item = (&'a usize,)>) -> impl Iterator<Item = usize> {
    let mut counts: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
    let mut total = 0usize;
    for (&v,) in inp {
        *counts.entry(v).or_insert(0) += 1;
        total += 1;
    }
    let best = counts.into_iter().max_by(|a, b| a.1.cmp(&b.1).then(a.0.cmp(&b.0)));
    best.map(|(v, _)| v).into_iter()
}

// Frequency of the mode returned by majority_usize.
pub(crate) fn mode_freq_usize<'a>(inp: impl Iterator<Item = (&'a usize,)>) -> impl Iterator<Item = usize> {
    let mut counts: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
    for (&v,) in inp { *counts.entry(v).or_insert(0) += 1; }
    counts.into_iter().max_by(|a, b| a.1.cmp(&b.1).then(a.0.cmp(&b.0))).map(|(_, c)| c).into_iter()
}

pub(crate) fn max_plus_one_usize<'a>(inp: impl Iterator<Item = (&'a usize,)>) -> impl Iterator<Item = usize> {
    inp.map(|(&v,)| v).max().map(|m| m + 1).into_iter()
}

pub(crate) fn count_items_sig<'a, T: 'a>(inp: impl Iterator<Item = (&'a T,)>) -> impl Iterator<Item = usize> {
    std::iter::once(inp.count())
}

pub(crate) fn max_usize<'a>(inp: impl Iterator<Item = (&'a usize,)>) -> impl Iterator<Item = usize> {
    inp.map(|(&v,)| v).max().into_iter()
}

// Declarative helpers consumed by reconcile_signatures below.
ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct SignatureReconciliationProgram;

    // Input relations (swapped in from the DB).
    relation emit_function(Address, Symbol, Node);
    relation func_has_param_evidence(Address, usize);
    relation call_target_func(Node, Address);
    relation call_arg(Node, usize, RTLReg);
    relation call_has_arg_evidence(Node, usize);
    relation call_args_collected_candidate(Node, Args);
    relation call_float_args_collected(Node, Args);
    relation emit_function_param_count_candidate(Address, usize);
    relation emit_function_float_param_count(Address, usize);
    relation emit_function_stack_param_count(Address, usize);
    relation known_varargs_function(Symbol, usize);
    relation emit_function_has_return_candidate(Address);
    relation emit_function_void_candidate(Address);
    relation emit_function_return_type_xtype_candidate(Address, XType);
    relation call_returns_value(Address, Mreg);

    // Calls that have precise per-position arg_mapping.
    #[local] relation call_precise(Node);
    call_precise(n) <-- call_arg(n, _, _);

    // Per-call integer-position evidence; precise mapping wins.
    #[local] relation call_int_pos(Node, usize);
    call_int_pos(n, p) <-- call_arg(n, p, _);
    // Fall back to call_has_arg_evidence only when no precise mapping exists for this call.
    call_int_pos(n, p) <--
        call_has_arg_evidence(n, p),
        !call_precise(n);

    // A call site is informative if it has any arg evidence for its target.
    #[local] relation call_has_any_arg(Node);
    call_has_any_arg(n) <-- call_int_pos(n, _);

    // Per-(func, pos) call-site support counts.
    #[local] relation call_pos_evidence(Address, Node, usize);
    call_pos_evidence(target, n, p) <--
        call_target_func(n, target),
        call_int_pos(n, p);

    #[local] relation informative_call(Address, Node);
    informative_call(target, n) <--
        call_target_func(n, target),
        call_has_any_arg(n);

    // Number of informative call sites per function
    relation informative_call_count(Address, usize);
    informative_call_count(f, c) <--
        informative_call(f, _),
        agg c = count_items_sig(n) in informative_call(f, n);

    // Number of informative call sites that have evidence for a given position
    #[local] relation call_pos_support(Address, usize, usize);
    call_pos_support(f, p, c) <--
        call_pos_evidence(f, _, p),
        agg c = count_items_sig(n) in call_pos_evidence(f, n, p);

    // Definition-side integer-position evidence.
    #[local] relation def_int_pos(Address, usize);
    def_int_pos(f, p) <-- func_has_param_evidence(f, p);

    // Position confirmed if definition reads it, or informative-call coverage >= threshold. Positions 0..6.
    #[local] relation int_pos_confirmed(Address, usize);

    // (a) definition confirms
    int_pos_confirmed(f, p) <--
        def_int_pos(f, p),
        if *p < 6;

    // (b) call-site ratio confirms (only when there is at least one informative call)
    int_pos_confirmed(f, p) <--
        call_pos_support(f, p, c),
        informative_call_count(f, total),
        if *p < 6,
        if *total > 0,
        if (*c as f64) / (*total as f64) >= CALL_SITE_CONFIRM_THRESHOLD;

    // Reconciled int count: max confirmed position + 1. Emits only when some confirmation exists.
    relation reconciled_int_count(Address, usize);
    reconciled_int_count(f, n) <--
        int_pos_confirmed(f, _),
        agg n = max_plus_one_usize(p) in int_pos_confirmed(f, p);

    // Max of def_int_pos for fallback when all call sites failed backward reach.
    relation def_int_count_max(Address, usize);
    def_int_count_max(f, n) <--
        def_int_pos(f, _),
        agg n = max_plus_one_usize(p) in def_int_pos(f, p);

    // Per-call-site arg counts: max int-args + float count (when non-empty).
    #[local] relation call_int_arg_count_raw(Node, usize);
    call_int_arg_count_raw(n, len) <--
        call_args_collected_candidate(n, args),
        let len = args.len();
    #[local] relation call_int_arg_count(Node, usize);
    call_int_arg_count(n, m) <--
        call_int_arg_count_raw(n, _),
        agg m = max_usize(l) in call_int_arg_count_raw(n, l);

    #[local] relation call_float_arg_count(Node, usize);
    call_float_arg_count(n, fc) <--
        call_float_args_collected(n, args),
        let fc = args.len(),
        if fc > 0;

    #[local] relation call_total_arg_count(Node, usize);
    call_total_arg_count(n, ic) <--
        call_int_arg_count(n, ic),
        !call_float_arg_count(n, _);
    call_total_arg_count(n, ic + fc) <--
        call_int_arg_count(n, ic),
        call_float_arg_count(n, fc);
    // Calls with no int args entry but float args present still count floats.
    call_total_arg_count(n, fc) <--
        call_float_arg_count(n, fc),
        !call_int_arg_count(n, _);

    // Sample (target, arg_count) per call; 0 counted for calls with no arg evidence.
    #[local] relation call_site_count_sample(Address, Node, usize);
    call_site_count_sample(target, n, c) <--
        call_target_func(n, target),
        call_total_arg_count(n, c);
    call_site_count_sample(target, n, 0) <--
        call_target_func(n, target),
        !call_total_arg_count(n, _);

    // Total call sites per function (every call_target_func entry).
    relation total_call_sites(Address, usize);
    total_call_sites(f, c) <--
        call_site_count_sample(f, _, _),
        agg c = count_items_sig(n) in call_site_count_sample(f, n, _);

    // Majority mode: arg-count with highest frequency, ties broken by larger value.
    relation call_site_mode(Address, usize);
    call_site_mode(f, m) <--
        call_site_count_sample(f, _, _),
        agg m = majority_usize(c) in call_site_count_sample(f, _, c);

    relation call_site_mode_freq(Address, usize);
    call_site_mode_freq(f, freq) <--
        call_site_count_sample(f, _, _),
        agg freq = mode_freq_usize(c) in call_site_count_sample(f, _, c);

    // has_call_sites: any call_target_func entry for f.
    relation has_call_sites(Address);
    has_call_sites(f) <-- call_target_func(_, f);

    // True when some call site targeting f has its return value consumed.
    relation any_call_uses_return(Address);
    any_call_uses_return(f) <--
        call_target_func(n, f),
        call_returns_value(n, _);

    // Varargs: emit_function whose name is listed in known_varargs_function.
    relation is_varargs_fn(Address);
    is_varargs_fn(addr) <--
        emit_function(addr, name, _),
        known_varargs_function(name, _);

    // main() detection by name only.
    relation is_main_fn(Address);
    is_main_fn(addr) <--
        emit_function(addr, name, _),
        if *name == "main";

    // C++ mangled-name detection: _ZN prefix implies "this" is a pointer.
    relation is_cpp_method_fn(Address);
    is_cpp_method_fn(addr) <--
        emit_function(addr, name, _),
        if name.starts_with("_ZN");

    // Return-type ladder. Case 7 (no info -> Xvoid) is implicit: no row emitted, caller reads Xvoid default.
    relation reconciled_return_type(Address, XType);

    // Case 1: definition says void -- always wins
    reconciled_return_type(f, XType::Xvoid) <--
        emit_function_void_candidate(f);

    // Case 2: def has_return + explicit xtype
    reconciled_return_type(f, ty) <--
        emit_function_has_return_candidate(f),
        emit_function_return_type_xtype_candidate(f, ty),
        !emit_function_void_candidate(f);

    // Case 3: def has_return but no xtype
    reconciled_return_type(f, XType::Xany64) <--
        emit_function_has_return_candidate(f),
        !emit_function_return_type_xtype_candidate(f, _),
        !emit_function_void_candidate(f);

    // Case 4: def xtype present without has_return (unusual but preserves behavior)
    reconciled_return_type(f, ty) <--
        emit_function_return_type_xtype_candidate(f, ty),
        !emit_function_has_return_candidate(f),
        !emit_function_void_candidate(f);

    // Case 5: call sites but none consume return -> Xvoid
    reconciled_return_type(f, XType::Xvoid) <--
        has_call_sites(f),
        !any_call_uses_return(f),
        !emit_function_void_candidate(f),
        !emit_function_has_return_candidate(f),
        !emit_function_return_type_xtype_candidate(f, _);

    // Case 6: call sites and at least one consumes return -> Xany64
    reconciled_return_type(f, XType::Xany64) <--
        has_call_sites(f),
        any_call_uses_return(f),
        !emit_function_void_candidate(f),
        !emit_function_has_return_candidate(f),
        !emit_function_return_type_xtype_candidate(f, _);
}

fn arg_regs() -> &'static [Mreg] {
    &crate::x86::abi::abi_config().int_arg_regs
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignatureConfidence {
    KnownExtern,
    HighConfidence,
    CallSiteMajority,
    DefinitionOnly,
    Inferred,
}

#[derive(Debug, Clone)]
pub struct FunctionPrototype {
    pub address: Address,
    #[allow(dead_code)]
    pub name: Symbol,
    pub param_count: usize,
    pub param_types: Vec<XType>,
    pub return_type: XType,
    pub confidence: SignatureConfidence,
    /// True for known varargs callees; param_count is the fixed prefix only.
    pub is_varargs: bool,
}

pub struct SignatureReconciliationPass;

impl IRPass for SignatureReconciliationPass {
    fn name(&self) -> &'static str { "signature-reconciliation" }

    fn run(&self, db: &mut DecompileDB) {
        reconcile_signatures(db);
    }

    fn inputs(&self) -> &'static [&'static str] {
        &[
            "emit_function", "emit_function_param_candidate", "emit_function_param_count_candidate",
            "emit_function_param_type_candidate", "emit_function_has_return_candidate", "emit_function_void_candidate",
            "emit_function_return_type_xtype_candidate", "emit_function_signature_candidate",
            "call_target_func", "call_args_collected_candidate", "call_float_args_collected", "call_returns_value",
            "known_extern_signature", "call_site", "reg_rtl", "reg_def_used",
            "func_param_position_type", "reg_xtl",
            "emit_var_type_candidate", "call_arg",
            "func_has_param_evidence", "call_has_arg_evidence",
            "emit_function_float_param_count", "emit_function_stack_param_count",
            "rtl_inst",
        ]
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "emit_function_param", "emit_function_param_count",
            "emit_function_param_type", "emit_function_has_return",
            "emit_function_void", "emit_function_return_type_xtype",
            "emit_function_return_type",
            "emit_function_signature", "call_args_collected",
            "emit_var_is_struct", "emit_function_param_is_pointer",
            "func_param_struct_type",
        ]
    }
}

// ABI parameter order: integer regs first (DI..R9), then float regs (X0..X7)
fn param_mreg_sort_key(mreg: Mreg) -> usize {
    match mreg {
        Mreg::DI => 0,
        Mreg::SI => 1,
        Mreg::DX => 2,
        Mreg::CX => 3,
        Mreg::R8 => 4,
        Mreg::R9 => 5,
        Mreg::X0 => 6,
        Mreg::X1 => 7,
        Mreg::X2 => 8,
        Mreg::X3 => 9,
        Mreg::X4 => 10,
        Mreg::X5 => 11,
        Mreg::X6 => 12,
        Mreg::X7 => 13,
        _ => 100,
    }
}

// Per-position int arg confirmation is in Ascent (int_pos_confirmed / reconciled_int_count).

fn reconcile_signatures(db: &mut DecompileDB) {

    let functions: HashMap<Address, Symbol> = db.rel_iter::<(Address, Symbol, Node)>("emit_function")
        .map(|&(addr, name, _)| (addr, name))
        .collect();

    if functions.is_empty() {
        return;
    }

    run_pass!(db, SignatureReconciliationProgram);

    // Consume Ascent helper relations into per-function lookup maps.
    let reconciled_int_count_map: HashMap<Address, usize> = db
        .rel_iter::<(Address, usize)>("reconciled_int_count")
        .map(|&(a, c)| (a, c))
        .collect();
    let def_int_count_max_map: HashMap<Address, usize> = db
        .rel_iter::<(Address, usize)>("def_int_count_max")
        .map(|&(a, c)| (a, c))
        .collect();
    let call_site_mode_map: HashMap<Address, usize> = db
        .rel_iter::<(Address, usize)>("call_site_mode")
        .map(|&(a, c)| (a, c))
        .collect();
    let call_site_mode_freq_map: HashMap<Address, usize> = db
        .rel_iter::<(Address, usize)>("call_site_mode_freq")
        .map(|&(a, c)| (a, c))
        .collect();
    let total_call_sites_map: HashMap<Address, usize> = db
        .rel_iter::<(Address, usize)>("total_call_sites")
        .map(|&(a, c)| (a, c))
        .collect();
    let has_call_sites_set: HashSet<Address> = db
        .rel_iter::<(Address,)>("has_call_sites")
        .map(|&(a,)| a)
        .collect();
    let any_call_uses_return_set: HashSet<Address> = db
        .rel_iter::<(Address,)>("any_call_uses_return")
        .map(|&(a,)| a)
        .collect();
    let is_varargs_fn_set: HashSet<Address> = db
        .rel_iter::<(Address,)>("is_varargs_fn")
        .map(|&(a,)| a)
        .collect();
    let is_main_fn_set: HashSet<Address> = db
        .rel_iter::<(Address,)>("is_main_fn")
        .map(|&(a,)| a)
        .collect();
    let is_cpp_method_fn_set: HashSet<Address> = db
        .rel_iter::<(Address,)>("is_cpp_method_fn")
        .map(|&(a,)| a)
        .collect();
    let reconciled_return_type_map: HashMap<Address, XType> = db
        .rel_iter::<(Address, XType)>("reconciled_return_type")
        .map(|&(a, ref t)| (a, t.clone()))
        .collect();

    let extern_sigs: HashMap<Symbol, (usize, XType, Arc<Vec<XType>>)> = db.rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("known_extern_signature")
        .map(|&(name, count, ref ret, ref params)| (name, (count, ret.clone(), params.clone())))
        .collect();

    let mut def_param_counts: HashMap<Address, usize> = HashMap::new();
    for &(addr, count) in db.rel_iter::<(Address, usize)>("emit_function_param_count_candidate") {
        let entry = def_param_counts.entry(addr).or_insert(0);
        *entry = (*entry).max(count);
    }

    let mut def_param_types: HashMap<Address, HashMap<RTLReg, XType>> = HashMap::new();
    for &(addr, reg, ref xtype) in db.rel_iter::<(Address, RTLReg, XType)>("emit_function_param_type_candidate") {
        def_param_types.entry(addr).or_default().insert(reg, xtype.clone());
    }

    let mut rtl_to_mreg: HashMap<(Address, RTLReg), Mreg> = HashMap::new();
    for &(node, ref mreg, rtl_reg) in db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl") {
        rtl_to_mreg.insert((node, rtl_reg), *mreg);
    }

    let mut def_params: HashMap<Address, Vec<RTLReg>> = HashMap::new();
    for &(addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param_candidate") {
        def_params.entry(addr).or_default().push(reg);
    }
    for (addr, params) in def_params.iter_mut() {
        params.sort_by_key(|reg| {
            if let Some(mreg) = rtl_to_mreg.get(&(*addr, *reg)) {
                param_mreg_sort_key(*mreg)
            } else {
                usize::MAX
            }
        });
        params.dedup();
    }

    let def_has_return: std::collections::HashSet<Address> = db.rel_iter::<(Address,)>("emit_function_has_return_candidate")
        .map(|&(addr,)| addr)
        .collect();
    let def_void: std::collections::HashSet<Address> = db.rel_iter::<(Address,)>("emit_function_void_candidate")
        .map(|&(addr,)| addr)
        .collect();
    let def_return_types: HashMap<Address, XType> = db.rel_iter::<(Address, XType)>("emit_function_return_type_xtype_candidate")
        .map(|&(addr, ref xtype)| (addr, xtype.clone()))
        .collect();

    // call_targets is consumed by patch_db and the call-site arg-type lookup below.
    let call_targets: HashMap<Node, Address> = db.rel_iter::<(Node, Address)>("call_target_func")
        .map(|&(call_node, target)| (call_node, target))
        .collect();

    let emit_var_types: HashMap<RTLReg, Vec<XType>> = {
        let mut map: HashMap<RTLReg, Vec<XType>> = HashMap::new();
        for &(reg, ref xtype) in db.rel_iter::<(RTLReg, XType)>("emit_var_type_candidate") {
            let types = map.entry(reg).or_default();
            if !types.contains(xtype) {
                types.push(xtype.clone());
            }
        }
        // Sort candidates so tie-breakers are stable regardless of parallel Ascent tuple order.
        for types in map.values_mut() {
            types.sort();
        }
        map
    };

    let call_arg_data: Vec<(Node, usize, RTLReg)> = db
        .rel_iter::<(Node, usize, RTLReg)>("call_arg")
        .cloned()
        .collect();

    let mut call_site_arg_types: HashMap<Address, HashMap<usize, Vec<XType>>> = HashMap::new();
    for &(call_node, pos, arg_rtl) in &call_arg_data {
        if let Some(&target_addr) = call_targets.get(&call_node) {
            if let Some(xtypes) = emit_var_types.get(&arg_rtl) {
                for xtype in xtypes {
                    call_site_arg_types
                        .entry(target_addr)
                        .or_default()
                        .entry(pos)
                        .or_default()
                        .push(xtype.clone());
                }
            }
        }
    }
    // Sort caller-type vectors so later tie-breaking is independent of source tuple order.
    for pos_map in call_site_arg_types.values_mut() {
        for v in pos_map.values_mut() {
            v.sort();
        }
    }

    // Position-level int-arg evidence lives in the Ascent program above.

    let float_param_counts: HashMap<Address, usize> = db
        .rel_iter::<(Address, usize)>("emit_function_float_param_count")
        .map(|&(addr, count)| (addr, count))
        .collect();

    let stack_param_counts: HashMap<Address, usize> = db
        .rel_iter::<(Address, usize)>("emit_function_stack_param_count")
        .map(|&(addr, count)| (addr, count))
        .collect();

    let known_internal_sigs: HashMap<&str, (usize, XType, Vec<XType>)> = [
        ("main", (2, XType::Xint, vec![XType::Xint, XType::Xcharptrptr])),
    ].into_iter().collect();

    // Detect param registers used as load/store base addresses in RTL, catching pointers missed by Datalog type inference, and struct-like multi-offset access patterns.
    let (param_is_ptr, param_struct_offsets): (HashSet<RTLReg>, HashMap<RTLReg, HashSet<i64>>) = {
        let mut ptr_set = HashSet::new();
        let mut offsets_map: HashMap<RTLReg, HashSet<i64>> = HashMap::new();
        let mut param_regs: HashSet<RTLReg> = HashSet::new();
        for &(_addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param_candidate") {
            param_regs.insert(reg);
        }
        for &(_node, ref inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
            let (addr_mode, args) = match inst {
                RTLInst::Iload(_, addr, args, _) => (addr, args),
                RTLInst::Istore(_, addr, args, _) => (addr, args),
                _ => continue,
            };
            let offset = match addr_mode {
                Addressing::Aindexed(ofs) => *ofs,
                Addressing::Aindexed2(ofs) => *ofs,
                Addressing::Aindexed2scaled(_, ofs) => *ofs,
                _ => continue,
            };
            if let Some(&base_rtl) = args.first() {
                if param_regs.contains(&base_rtl) {
                    ptr_set.insert(base_rtl);
                    offsets_map.entry(base_rtl).or_default().insert(offset);
                }
            }
        }
        (ptr_set, offsets_map)
    };

    let mut prototypes: Vec<FunctionPrototype> = Vec::new();

    for (&func_addr, &func_name) in &functions {
        // Varargs detection: declarative via SignatureReconciliationProgram.
        let is_va = is_varargs_fn_set.contains(&func_addr);
        if is_va {
            if let Some((param_count, ret_type, param_types)) = extern_sigs.get(func_name) {
                // Variadic internal function: force known param count to avoid materializing register dumps.
                prototypes.push(FunctionPrototype {
                    address: func_addr,
                    name: func_name,
                    param_count: *param_count,
                    param_types: (**param_types).clone(),
                    return_type: *ret_type,
                    confidence: SignatureConfidence::KnownExtern,
                    is_varargs: true,
                });
                continue;
            }
            // Varargs known but no extern sig: fall through, remember is_va so call sites keep extra args.
        }

        // Hardcode int main(int argc, char **argv) when is_main_fn fires.
        if is_main_fn_set.contains(&func_addr) {
            if let Some((param_count, ret_type, param_types)) = known_internal_sigs.get(func_name) {
                prototypes.push(FunctionPrototype {
                    address: func_addr,
                    name: func_name,
                    param_count: *param_count,
                    param_types: param_types.clone(),
                    return_type: *ret_type,
                    confidence: SignatureConfidence::HighConfidence,
                    is_varargs: is_va,
                });
                continue;
            }
        }

        let def_count = def_param_counts.get(&func_addr).copied().unwrap_or(0);

        // has_call_sites, total_sites, mode, mode_freq are Ascent-derived.
        let has_call_sites = has_call_sites_set.contains(&func_addr);
        let total_sites = total_call_sites_map.get(&func_addr).copied().unwrap_or(0);
        let call_site_mode = call_site_mode_map.get(&func_addr).copied().unwrap_or(0);
        let mode_freq = call_site_mode_freq_map.get(&func_addr).copied().unwrap_or(0);
        let consensus_ratio = if total_sites > 0 {
            mode_freq as f64 / total_sites as f64
        } else {
            0.0
        };

        // reconciled_int_count: declarative; absent row means 0 (matches old base case).
        let reconciled_int = reconciled_int_count_map.get(&func_addr).copied().unwrap_or(0);
        let float_count = float_param_counts.get(&func_addr).copied().unwrap_or(0);
        let stack_count = stack_param_counts.get(&func_addr).copied().unwrap_or(0);
        let position_based_count = reconciled_int + float_count + stack_count;

        // Use position-level result, but allow call-site override with strong consensus
        let reconciled_count = if !has_call_sites {
            position_based_count
        } else if call_site_mode > position_based_count
            && consensus_ratio >= 0.6 && total_sites >= 2
        {
            // Call sites strongly agree on more params -- trust them
            call_site_mode
        } else {
            position_based_count
        };

        // Never reduce to 0 if there was any evidence
        let reconciled_count = if reconciled_count == 0 && def_count > 0 && !has_call_sites {
            def_count
        } else {
            reconciled_count
        };


        let confidence = if !has_call_sites {
            SignatureConfidence::DefinitionOnly
        } else if reconciled_count == def_count && def_count == call_site_mode {
            SignatureConfidence::HighConfidence
        } else if reconciled_count != def_count && has_call_sites {
            SignatureConfidence::CallSiteMajority
        } else {
            SignatureConfidence::Inferred
        };

        let existing_types = def_param_types.get(&func_addr);
        let existing_params = def_params.get(&func_addr);
        let mut param_types = Vec::with_capacity(reconciled_count);
        for i in 0..reconciled_count {
            let mut resolved_type: Option<XType> = None;

            // Priority 1: Definition type from emit_function_param_type
            if let Some(params) = existing_params {
                if let Some(&reg) = params.get(i) {
                    if let Some(types) = existing_types {
                        if let Some(xtype) = types.get(&reg) {
                            resolved_type = Some(xtype.clone());
                        }
                    }
                }
            }

            // Priority 1.5: Definition-side emit_var_type (struct/ptr refinements), upgrading to pointer or struct pointer based on RTL load/store base usage.
            if resolved_type.is_none() || matches!(
                resolved_type,
                Some(
                    XType::Xint
                        | XType::Xintunsigned
                        | XType::Xlong
                        | XType::Xlongunsigned
                        | XType::Xany32
                        | XType::Xany64
                        | XType::Xptr
                )
            ) {
                if let Some(params) = existing_params {
                    if let Some(&reg) = params.get(i) {
                        if let Some(xtypes) = emit_var_types.get(&reg) {
                            // Pick the most specific type from candidates (prefer struct ptr > ptr > specific int > generic int)
                            let best = xtypes.iter().max_by_key(|t| match t {
                                XType::XstructPtr(_) => 5,
                                XType::Xcharptr | XType::Xcharptrptr | XType::Xintptr | XType::Xfloatptr | XType::Xsingleptr | XType::Xfuncptr => 4,
                                XType::Xptr => 3,
                                XType::Xint8signed | XType::Xint8unsigned | XType::Xint16signed | XType::Xint16unsigned => 2,
                                XType::Xfloat | XType::Xsingle => 2,
                                _ => 1,
                            });
                            if let Some(best_type) = best {
                                resolved_type = Some(best_type.clone());
                            }
                        } else if param_is_ptr.contains(&reg) {
                            // Check if it's a struct pointer (multiple offsets)
                            if let Some(offsets) = param_struct_offsets.get(&reg) {
                                if offsets.len() > 1 {
                                    // Look up struct ID from struct_recovery
                                    let struct_id = db.rel_iter::<(Address, RTLReg, usize)>("emit_var_is_struct_candidate")
                                        .find(|&&(_, r, _)| r == reg)
                                        .map(|&(_, _, sid)| sid);
                                    if let Some(sid) = struct_id {
                                        resolved_type = Some(XType::XstructPtr(sid));
                                    } else {
                                        resolved_type = Some(XType::Xintptr);
                                    }
                                } else {
                                    resolved_type = Some(XType::Xintptr);
                                }
                            } else {
                                resolved_type = Some(XType::Xptr);
                            }
                        }
                    }
                }
            }

            // Priority 2: Call-site majority vote, upgrading generic int placeholders only.
            if resolved_type.is_none() || matches!(
                resolved_type,
                Some(
                    XType::Xint
                        | XType::Xintunsigned
                        | XType::Xlong
                        | XType::Xlongunsigned
                        | XType::Xany32
                        | XType::Xany64
                )
            ) {
                if let Some(pos_types) = call_site_arg_types.get(&func_addr) {
                    if let Some(caller_types) = pos_types.get(&i) {
                        if !caller_types.is_empty() {
                            let mut type_counts: HashMap<&XType, usize> = HashMap::new();
                            for t in caller_types {
                                *type_counts.entry(t).or_insert(0) += 1;
                            }
                            let should_override = match resolved_type.as_ref() {
                                None => true,
                                Some(current) => matches!(
                                    current,
                                    XType::Xint
                                        | XType::Xintunsigned
                                        | XType::Xlong
                                        | XType::Xlongunsigned
                                        | XType::Xany32
                                        | XType::Xany64
                                ),
                            };
                            if let Some((&best_type, &best_count)) = type_counts.iter()
                                .max_by_key(|(ty, count)| (**count, **ty))
                            {
                                if best_count * 2 > caller_types.len() {
                                    if should_override {
                                        resolved_type = Some(best_type.clone());
                                    }
                                }
                            }
                            if should_override && matches!(
                                resolved_type,
                                None
                                    | Some(
                                        XType::Xint
                                            | XType::Xintunsigned
                                            | XType::Xlong
                                            | XType::Xlongunsigned
                                            | XType::Xany32
                                            | XType::Xany64
                                    )
                            ) {
                                if let Some(best_ptr) = caller_types.iter().max_by_key(|t| (match t {
                                    XType::XstructPtr(_) => 6,
                                    XType::Xcharptr => 5,
                                    XType::Xcharptrptr
                                    | XType::Xintptr
                                    | XType::Xfloatptr
                                    | XType::Xsingleptr
                                    | XType::Xfuncptr => 4,
                                    XType::Xptr => 3,
                                    _ => 0,
                                }, **t)) {
                                    if matches!(
                                        best_ptr,
                                        XType::XstructPtr(_)
                                            | XType::Xcharptr
                                            | XType::Xcharptrptr
                                            | XType::Xintptr
                                            | XType::Xfloatptr
                                            | XType::Xsingleptr
                                            | XType::Xfuncptr
                                            | XType::Xptr
                                    ) {
                                        resolved_type = Some(best_ptr.clone());
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // Default to Xany64 (register-width floor), not Xint (which would lie about ptrs/longs).
            param_types.push(resolved_type.unwrap_or(XType::Xany64));
        }

        // C++ method: _ZN-mangled names upgrade param 0 (this) to Xptr.
        if is_cpp_method_fn_set.contains(&func_addr) && !param_types.is_empty() {
            let needs_upgrade = matches!(
                param_types[0],
                XType::Xint | XType::Xintunsigned | XType::Xlong | XType::Xlongunsigned |
                XType::Xany32 | XType::Xany64 | XType::Xvoid
            );
            if needs_upgrade {
                param_types[0] = XType::Xptr;
            }
        }

        let def_ret_type = def_return_types.get(&func_addr);

        // reconciled_return_type: Ascent-derived. Absent row defaults to Xvoid.
        let return_type = reconciled_return_type_map
            .get(&func_addr)
            .cloned()
            .unwrap_or(XType::Xvoid);

        let count_changed = reconciled_count != def_count;
        let current_param_types: Vec<XType> = (0..reconciled_count)
            .map(|i| {
                existing_params
                    .and_then(|params| params.get(i))
                    .and_then(|reg| existing_types.and_then(|types| types.get(reg)))
                    .cloned()
                    .unwrap_or(XType::Xany64)
            })
            .collect();
        let param_types_changed = current_param_types != param_types;
        let ret_type_changed = match def_ret_type {
            Some(dt) => *dt != return_type,
            None => return_type != XType::Xvoid,
        };
        let void_override = return_type == XType::Xvoid
            && (def_has_return.contains(&func_addr) || def_return_types.contains_key(&func_addr));

        if count_changed || param_types_changed || ret_type_changed || void_override {
            prototypes.push(FunctionPrototype {
                address: func_addr,
                name: func_name,
                param_count: reconciled_count,
                param_types,
                return_type,
                confidence,
                is_varargs: is_va,
            });
        }
    }

    if prototypes.is_empty() {
        return;
    }

    log::info!("SignatureReconciliation: patching {} function prototypes", prototypes.len());

    patch_db(db, &prototypes);
}

fn patch_db(
    db: &mut DecompileDB,
    prototypes: &[FunctionPrototype],
) {
    let proto_map: HashMap<Address, &FunctionPrototype> = prototypes.iter()
        .map(|p| (p.address, p))
        .collect();

    let call_targets: HashMap<Node, Address> = db.rel_iter::<(Node, Address)>("call_target_func")
        .map(|&(call_node, target)| (call_node, target))
        .collect();

    let rtl_to_mreg: HashMap<(Address, RTLReg), Mreg> = db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl")
        .map(|&(node, ref mreg, rtl_reg)| ((node, rtl_reg), *mreg))
        .collect();

    {
        let mut existing_params: HashMap<Address, Vec<RTLReg>> = HashMap::new();
        for &(addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param_candidate") {
            let params = existing_params.entry(addr).or_default();
            if !params.contains(&reg) {
                params.push(reg);
            }
        }
        for (addr, params) in existing_params.iter_mut() {
            params.sort_by_key(|reg| {
                rtl_to_mreg.get(&(*addr, *reg))
                    .map(|m| param_mreg_sort_key(*m))
                    .unwrap_or(usize::MAX)
            });
        }

        let mut new_params: Vec<(Address, RTLReg)> = Vec::new();

        for &(addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param_candidate") {
            if !proto_map.contains_key(&addr) {
                new_params.push((addr, reg));
            }
        }

        for proto in prototypes {
            let existing = existing_params.get(&proto.address).cloned().unwrap_or_default();
            let current_count = existing.len();

            for (i, &reg) in existing.iter().enumerate() {
                if i < proto.param_count {
                    new_params.push((proto.address, reg));
                }
            }

            if proto.param_count > current_count {
                for i in current_count..proto.param_count {
                    let synthetic_reg = if i < arg_regs().len() {
                        fresh_xtl_reg(proto.address, arg_regs()[i])
                    } else {
                        crate::decompile::passes::rtl_pass::fresh_stack_param_reg(
                            proto.address,
                            i - arg_regs().len(),
                        )
                    };
                    new_params.push((proto.address, synthetic_reg));

                    let xtype = proto.param_types.get(i).cloned().unwrap_or(XType::Xany64);
                    db.rel_push("emit_function_param_type_candidate", (proto.address, synthetic_reg, xtype));
                }
            }
        }

        db.rel_set("emit_function_param", new_params.into_iter().collect::<ascent::boxcar::Vec<_>>());
    }

    {
        let mut existing_params: HashMap<Address, Vec<RTLReg>> = HashMap::new();
        for &(addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param_candidate") {
            let params = existing_params.entry(addr).or_default();
            if !params.contains(&reg) {
                params.push(reg);
            }
        }
        for (addr, params) in existing_params.iter_mut() {
            params.sort_by_key(|reg| {
                rtl_to_mreg.get(&(*addr, *reg))
                    .map(|m| param_mreg_sort_key(*m))
                    .unwrap_or(usize::MAX)
            });
        }

        let mut new_param_types: Vec<(Address, RTLReg, XType)> = db
            .rel_iter::<(Address, RTLReg, XType)>("emit_function_param_type_candidate")
            .filter(|&&(addr, _, _)| !proto_map.contains_key(&addr))
            .cloned()
            .collect();

        for proto in prototypes {
            if let Some(params) = existing_params.get(&proto.address) {
                for (i, &reg) in params.iter().enumerate().take(proto.param_count) {
                    let xtype = proto.param_types.get(i).cloned().unwrap_or(XType::Xany64);
                    new_param_types.push((proto.address, reg, xtype));
                }
            }
        }

        db.rel_set("emit_function_param_type", new_param_types.into_iter().collect::<ascent::boxcar::Vec<_>>());
    }

    {
        let known_param_regs: HashSet<(Address, RTLReg)> = {
            let mut set = HashSet::new();
            let existing_params: HashMap<Address, Vec<RTLReg>> = {
                let mut m: HashMap<Address, Vec<RTLReg>> = HashMap::new();
                for &(addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param_candidate") {
                    m.entry(addr).or_default().push(reg);
                }
                for (addr, params) in m.iter_mut() {
                    params.sort_by_key(|reg| {
                        rtl_to_mreg.get(&(*addr, *reg))
                            .map(|mreg| param_mreg_sort_key(*mreg))
                            .unwrap_or(usize::MAX)
                    });
                    params.dedup();
                }
                m
            };
            for proto in prototypes {
                if proto.confidence == SignatureConfidence::KnownExtern {
                    if let Some(params) = existing_params.get(&proto.address) {
                        for &reg in params.iter().take(proto.param_count) {
                            set.insert((proto.address, reg));
                        }
                    }
                }
            }
            set
        };
        if !known_param_regs.is_empty() {
            let known_addrs: HashSet<Address> = known_param_regs.iter().map(|(a, _)| *a).collect();

            let new_struct: Vec<(Address, RTLReg, usize)> = db
                .rel_iter::<(Address, RTLReg, usize)>("emit_var_is_struct_candidate")
                .filter(|&&(addr, reg, _)| !known_param_regs.contains(&(addr, reg)))
                .cloned()
                .collect();
            db.rel_set("emit_var_is_struct", new_struct.into_iter().collect::<ascent::boxcar::Vec<_>>());

            let new_ptr: Vec<(Address, RTLReg)> = db
                .rel_iter::<(Address, RTLReg)>("emit_function_param_is_pointer_candidate")
                .filter(|&&(addr, reg)| !known_param_regs.contains(&(addr, reg)))
                .cloned()
                .collect();
            db.rel_set("emit_function_param_is_pointer", new_ptr.into_iter().collect::<ascent::boxcar::Vec<_>>());

            let new_param_struct: Vec<(Address, usize, usize)> = db
                .rel_iter::<(Address, usize, usize)>("func_param_struct_type_candidate")
                .filter(|&&(addr, _, _)| !known_addrs.contains(&addr))
                .cloned()
                .collect();
            db.rel_set("func_param_struct_type", new_param_struct.into_iter().collect::<ascent::boxcar::Vec<_>>());
        }
    }

    {
        let mut count_map: HashMap<Address, usize> = HashMap::new();
        for &(addr, count) in db.rel_iter::<(Address, usize)>("emit_function_param_count_candidate") {
            if !proto_map.contains_key(&addr) {
                let entry = count_map.entry(addr).or_insert(0);
                *entry = (*entry).max(count);
            }
        }
        for proto in prototypes {
            count_map.insert(proto.address, proto.param_count);
        }
        let new_counts: Vec<(Address, usize)> = count_map.into_iter().collect();
        db.rel_set("emit_function_param_count", new_counts.into_iter().collect::<ascent::boxcar::Vec<_>>());
    }

    {
        let mut new_sigs: Vec<(Address, Signature)> = db.rel_iter::<(Address, Signature)>("emit_function_signature_candidate")
            .filter(|&&(addr, _)| !proto_map.contains_key(&addr))
            .cloned()
            .collect();
        for proto in prototypes {
            let sig = Signature {
                sig_args: Arc::new(proto.param_types.clone()),
                sig_res: proto.return_type.clone(),
                sig_cc: CallConv::default(),
            };
            new_sigs.push((proto.address, sig));
        }
        db.rel_set("emit_function_signature", new_sigs.into_iter().collect::<ascent::boxcar::Vec<_>>());
    }

    {
        let mut new_ret: Vec<(Address, XType)> = db.rel_iter::<(Address, XType)>("emit_function_return_type_xtype_candidate")
            .filter(|&&(addr, _)| !proto_map.contains_key(&addr))
            .cloned()
            .collect();
        for proto in prototypes {
            if proto.return_type != XType::Xvoid {
                new_ret.push((proto.address, proto.return_type.clone()));
            }
        }
        db.rel_set("emit_function_return_type_xtype", new_ret.into_iter().collect::<ascent::boxcar::Vec<_>>());
    }

    {
        use crate::decompile::passes::csh_pass::clight_type_from_xtype;
        let mut new_ret_ct: Vec<(Address, crate::x86::types::ClightType)> = db.rel_iter::<(Address, ClightType)>("emit_function_return_type_candidate")
            .filter(|&&(addr, _)| !proto_map.contains_key(&addr))
            .cloned()
            .collect();
        for proto in prototypes {
            if proto.return_type != XType::Xvoid {
                new_ret_ct.push((proto.address, clight_type_from_xtype(&proto.return_type)));
            }
        }
        db.rel_set("emit_function_return_type", new_ret_ct.into_iter().collect::<ascent::boxcar::Vec<_>>());
    }

    {
        let mut new_has_ret: Vec<(Address,)> = db.rel_iter::<(Address,)>("emit_function_has_return_candidate")
            .filter(|&&(addr,)| !proto_map.contains_key(&addr))
            .cloned()
            .collect();
        let mut new_void: Vec<(Address,)> = db.rel_iter::<(Address,)>("emit_function_void_candidate")
            .filter(|&&(addr,)| !proto_map.contains_key(&addr))
            .cloned()
            .collect();
        for proto in prototypes {
            if proto.return_type != XType::Xvoid {
                new_has_ret.push((proto.address,));
            } else {
                new_void.push((proto.address,));
            }
        }
        db.rel_set("emit_function_has_return", new_has_ret.into_iter().collect::<ascent::boxcar::Vec<_>>());
        db.rel_set("emit_function_void", new_void.into_iter().collect::<ascent::boxcar::Vec<_>>());
    }

    {
        let reg_rtl_map: HashMap<(Node, Mreg), RTLReg> = db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl")
            .map(|&(addr, ref mreg, rtl)| ((addr, *mreg), rtl))
            .collect();

        let mut reg_def_at_use: HashMap<(Mreg, Address), Address> = HashMap::new();
        for &(def_addr, ref mreg, use_addr) in db.rel_iter::<(Address, Mreg, Address)>("reg_def_used") {
            reg_def_at_use.insert((*mreg, use_addr), def_addr);
        }

        let mut new_call_args: Vec<(Node, Arc<Vec<RTLReg>>)> = Vec::new();
        let mut patched_calls: std::collections::HashSet<Node> = std::collections::HashSet::new();

        for &(call_node, ref args) in db.rel_iter::<(Node, Args)>("call_args_collected_candidate") {
            let target = match call_targets.get(&call_node) {
                Some(&t) => t,
                None => {
                    new_call_args.push((call_node, args.clone()));
                    continue;
                }
            };

            let proto = match proto_map.get(&target) {
                Some(p) => p,
                None => {
                    new_call_args.push((call_node, args.clone()));
                    continue;
                }
            };

            if args.len() == proto.param_count {
                new_call_args.push((call_node, args.clone()));
                continue;
            }

            if args.len() > proto.param_count {
                // Truncate unconditionally: Signature/FuncDef/FuncDecl model only fixed-arity sigs.
                let trimmed: Vec<RTLReg> = args.iter().take(proto.param_count).cloned().collect();
                new_call_args.push((call_node, Arc::new(trimmed)));
                patched_calls.insert(call_node);
                continue;
            }

            let mut widened = args.as_ref().clone();
            for i in args.len()..proto.param_count {
                if i >= arg_regs().len() {
                    break;
                }
                let mreg = arg_regs()[i];

                if let Some(&rtl) = reg_rtl_map.get(&(call_node, mreg)) {
                    widened.push(rtl);
                    continue;
                }

                if let Some(&def_addr) = reg_def_at_use.get(&(mreg, call_node)) {
                    if let Some(&rtl) = reg_rtl_map.get(&(def_addr, mreg)) {
                        widened.push(rtl);
                        continue;
                    }
                }

                let synthetic = fresh_xtl_reg(call_node, mreg);
                widened.push(synthetic);
            }
            new_call_args.push((call_node, Arc::new(widened)));
            patched_calls.insert(call_node);
        }

        if !patched_calls.is_empty() {
            log::info!("SignatureReconciliation: widened args at {} call sites", patched_calls.len());
            db.rel_set("call_args_collected", new_call_args.into_iter().collect::<ascent::boxcar::Vec<_>>());
        }
    }
}
