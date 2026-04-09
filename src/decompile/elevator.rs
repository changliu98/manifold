// Main decompilation pipeline: type-erased relation storage, CSV loading, and staged pass execution.

use std::sync::Arc;
use std::any::Any;
use std::collections::HashMap as StdHashMap;

// Monomorphized clone function for type-erased relation entries.
type CloneFn = fn(&dyn Any) -> Box<dyn Any + Send + Sync>;

// Returns (tuple_count, approx_heap_bytes) for a type-erased relation.
type SizeFn = fn(&dyn Any) -> (usize, usize);

fn clone_fn<T: Clone + Any + Send + Sync>(any: &dyn Any) -> Box<dyn Any + Send + Sync> {
    let val = any.downcast_ref::<T>().expect("clone_fn type mismatch");
    Box::new(val.clone())
}

fn vec_size_fn<T: 'static>(any: &dyn Any) -> (usize, usize) {
    any.downcast_ref::<ascent::boxcar::Vec<T>>()
        .map(|v| (v.len(), v.len() * std::mem::size_of::<T>()))
        .unwrap_or((0, 0))
}

pub trait RelationMeasure: 'static + Send + Sync {
    fn measure(&self) -> (usize, usize);
}

impl<E: 'static + Send + Sync> RelationMeasure for ascent::boxcar::Vec<E> {
    fn measure(&self) -> (usize, usize) {
        (self.len(), self.len() * std::mem::size_of::<E>())
    }
}

fn measure_fn<T: 'static + RelationMeasure>(any: &dyn Any) -> (usize, usize) {
    any.downcast_ref::<T>()
        .map(|v| v.measure())
        .unwrap_or((0, 0))
}

// Read current process RSS in MB from /proc/self/status (Linux only).
pub fn get_rss_mb() -> f64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("VmRSS:"))
                .and_then(|l| l.split_whitespace().nth(1))
                .and_then(|v| v.parse::<f64>().ok())
        })
        .map(|kb| kb / 1024.0)
        .unwrap_or(0.0)
}

// Type-erased relation entry with optional clone/size functions for non-Clone types (e.g., lattice fields with RwLock).
pub struct RelationEntry {
    data: Box<dyn Any + Send + Sync>,
    cloner: Option<CloneFn>,
    sizer: Option<SizeFn>,
}

impl RelationEntry {
    fn new_clonable<T: 'static + Clone + Send + Sync>(value: T) -> Self {
        Self { data: Box::new(value), cloner: Some(clone_fn::<T>), sizer: None }
    }

    fn new_vec<T: 'static + Clone + Send + Sync>(value: ascent::boxcar::Vec<T>) -> Self {
        Self {
            data: Box::new(value),
            cloner: Some(clone_fn::<ascent::boxcar::Vec<T>>),
            sizer: Some(vec_size_fn::<T>),
        }
    }

    fn new_opaque<T: 'static + Send + Sync>(value: T) -> Self {
        Self { data: Box::new(value), cloner: None, sizer: None }
    }

    fn try_clone(&self) -> Option<Self> {
        let cloner = self.cloner?;
        let cloned_data = cloner(self.data.as_ref());
        Some(Self { data: cloned_data, cloner: self.cloner, sizer: self.sizer })
    }

    pub fn size_info(&self) -> Option<(usize, usize)> {
        self.sizer.map(|f| f(self.data.as_ref()))
    }
}
use crate::decompile::passes::c_pass::types::{CType, TranslationUnit};
use crate::decompile::passes::clight_select::select::SelectedFunction;
use crate::decompile::passes::clight_select::query::GlobalData;

use crate::util::leak;
use crate::x86::mach::Mreg;
use crate::x86::types::*;
use either::Either;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

// Strip GCC/Clang optimizer clone suffixes (_constprop_N, _isra_N, etc.) from symbol names.
fn strip_clone_suffix(name: &str) -> Option<&str> {
    // Order matters: check longer suffixes first to avoid partial matches.
    for pattern in &["_constprop_", "_isra_", "_part_", "_lto_priv_"] {
        if let Some(pos) = name.find(pattern) {
            return Some(&name[..pos]);
        }
    }
    // _cold has no trailing number
    if let Some(pos) = name.rfind("_cold") {
        if pos + 5 == name.len() {
            return Some(&name[..pos]);
        }
    }
    None
}

// External function definition parsed from extern.json.
#[derive(Debug, Clone, Deserialize, Serialize)]
struct ExternFunction {
    name: String,
    #[serde(default)]
    builtin: bool,
    #[serde(default)]
    sig_args: Vec<String>,
    #[serde(default)]
    sig_res: Option<String>,
    #[serde(default)]
    ptr_params: Vec<usize>,
}

#[derive(Debug, Deserialize)]
struct ExternFunctions {
    functions: Vec<ExternFunction>,
}

fn xtype_from_string(s: &str) -> Option<XType> {
    match s {
        "Xint" => Some(XType::Xint),
        "Xlong" => Some(XType::Xlong),
        "Xfloat" => Some(XType::Xfloat),
        "Xsingle" => Some(XType::Xsingle),
        "Xptr" => Some(XType::Xptr),
        "Xcharptr" => Some(XType::Xcharptr),
        "Xcharptrptr" => Some(XType::Xcharptrptr),
        "Xintptr" => Some(XType::Xintptr),
        "Xfloatptr" => Some(XType::Xfloatptr),
        "Xsingleptr" => Some(XType::Xsingleptr),
        "Xfuncptr" => Some(XType::Xfuncptr),
        "Xvoid" => Some(XType::Xvoid),
        "Xbool" => Some(XType::Xbool),
        "Xint8signed" => Some(XType::Xint8signed),
        "Xint8unsigned" => Some(XType::Xint8unsigned),
        "Xint16signed" => Some(XType::Xint16signed),
        "Xint16unsigned" => Some(XType::Xint16unsigned),
        "Xany32" => Some(XType::Xany32),
        "Xany64" => Some(XType::Xany64),
        _ => None,
    }
}

// Central storage for all Datalog relations and pipeline state; hand-written (not macro-generated) for fast compilation.
pub struct DecompileDB {
    pub relations: StdHashMap<&'static str, RelationEntry>,

    pub cast_selected_functions: Vec<SelectedFunction>,
    pub cast_globals: Vec<GlobalData>,
    pub cast_id_to_name: HashMap<usize, String>,
    pub cast_struct_layouts: HashMap<usize, Vec<(i64, String, MemoryChunk)>>,
    pub cast_var_types_for_emission: HashMap<String, CType>,
    pub cast_raw_translation_unit: Option<TranslationUnit>,
    pub cast_optimized_translation_unit: Option<TranslationUnit>,
    pub binary_path: Option<std::path::PathBuf>,
    pub trace_enabled: bool,
    pub skip_function_names: HashSet<&'static str>,
    pub skip_function_prefixes: Vec<&'static str>,
    pub measure_rule_times: bool,
    pub rule_time_reports: Vec<(String, String)>,
}

impl Default for DecompileDB {
    fn default() -> Self {
        Self {
            relations: StdHashMap::new(),

            cast_selected_functions: Default::default(),
            cast_globals: Default::default(),
            cast_id_to_name: Default::default(),
            cast_struct_layouts: Default::default(),
            cast_var_types_for_emission: Default::default(),
            cast_raw_translation_unit: None,
            cast_optimized_translation_unit: None,
            binary_path: None,
            trace_enabled: false,
            skip_function_names: HashSet::new(),
            skip_function_prefixes: Vec::new(),
            measure_rule_times: false,
            rule_time_reports: Vec::new(),
        }
    }
}

// Low-level relation store used by pass macros and codegen.
impl DecompileDB {
    pub fn put_relation<T: 'static + Clone + Send + Sync>(&mut self, name: &'static str, value: T) {
        self.relations.insert(name, RelationEntry::new_clonable(value));
    }

    // Swap a relation in-place between the DB and a pass-local field (avoids heap alloc/dealloc).
    pub fn swap_relation_with<T: 'static + Send + Sync + Default>(
        &mut self, name: &'static str, field: &mut T
    ) {
        if let Some(entry) = self.relations.get_mut(name) {
            if let Some(db_val) = entry.data.downcast_mut::<T>() {
                std::mem::swap(field, db_val);
                return;
            }
        }
        let mut default_val = T::default();
        std::mem::swap(field, &mut default_val);
        self.relations.insert(name, RelationEntry::new_opaque(default_val));
    }


    // Swap variant for Clone+RelationMeasure types, preserving clone and size functions.
    pub fn swap_relation_with_clonable<T: 'static + Clone + Send + Sync + Default + RelationMeasure>(
        &mut self, name: &'static str, field: &mut T
    ) {
        if let Some(entry) = self.relations.get_mut(name) {
            if let Some(db_val) = entry.data.downcast_mut::<T>() {
                std::mem::swap(field, db_val);
                if entry.sizer.is_none() {
                    entry.sizer = Some(measure_fn::<T>);
                }
                return;
            }
        }
        let mut default_val = T::default();
        std::mem::swap(field, &mut default_val);
        self.relations.insert(name, RelationEntry {
            data: Box::new(default_val),
            cloner: Some(clone_fn::<T>),
            sizer: Some(measure_fn::<T>),
        });
    }

    // Push a single tuple into a relation (creates if missing).
    pub fn rel_push<T: 'static + Clone + Send + Sync>(&mut self, name: &'static str, tuple: T) {
        self.relations
            .entry(name)
            .or_insert_with(|| RelationEntry::new_vec(ascent::boxcar::Vec::<T>::default()))
            .data
            .downcast_mut::<ascent::boxcar::Vec<T>>()
            .expect("relation type mismatch")
            .push(tuple);
    }

    pub fn rel_set<T: 'static + Clone + Send + Sync>(&mut self, name: &'static str, value: T) {
        self.put_relation(name, value);
    }

    // Iterate over a relation's tuples (empty iterator if missing).
    pub fn rel_iter<T: 'static + Send + Sync>(&self, name: &'static str) -> impl Iterator<Item = &T> + '_ {
        self.relations
            .get(name)
            .and_then(|entry| entry.data.downcast_ref::<ascent::boxcar::Vec<T>>())
            .into_iter()
            .flat_map(|v| v.iter())
    }

    // Clone a subset of relations for parallel pass execution; returns None if any lacks a clone function.
    fn try_clone_relations(&self, names: &[&'static str]) -> Option<StdHashMap<&'static str, RelationEntry>> {
        let mut result = StdHashMap::new();
        for &name in names {
            if let Some(entry) = self.relations.get(name) {
                result.insert(name, entry.try_clone()?);
            }
        }
        Some(result)
    }
}

impl DecompileDB {



    // Derive mach_func ranges and func_span from instr_in_function and func_entry.
    pub(crate) fn compute_mach_func_from_function_inference(&mut self) {
        let code_end: u64 = self.rel_iter::<(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize)>("unrefinedinstruction")
            .map(|(addr, size, ..)| *addr + *size as u64)
            .max()
            .unwrap_or(0);

        let mut uniq: std::collections::BTreeSet<u64> = std::collections::BTreeSet::new();
        for (_, func_addr) in self.rel_iter::<(Node, Address)>("instr_in_function") {
            if *func_addr > 0 {
                uniq.insert(*func_addr);
            }
        }

        let starts: Vec<u64> = uniq.into_iter().collect();
        let mut ranges: Vec<(u64, u64)> = Vec::new();
        for window in starts.windows(2) {
            let start = window[0];
            let end = window[1];
            if start < end {
                ranges.push((start, end));
            }
        }
        if let Some(&last) = starts.last() {
            if code_end > last {
                ranges.push((last, code_end));
            }
        }

        self.rel_set("mach_func", ranges.into_iter().collect::<ascent::boxcar::Vec<_>>());

        let mut entries: Vec<(u64, &str)> = self
            .rel_iter::<(Symbol, Address)>("func_entry")
            .map(|(name, addr)| (*addr, *name))
            .collect();
        entries.sort_unstable_by_key(|(addr, _)| *addr);

        let mut spans: Vec<(&str, u64, u64)> = Vec::new();
        for window in entries.windows(2) {
            let (start_addr, name) = (window[0].0, window[0].1);
            let end_addr = window[1].0;
            if start_addr < end_addr {
                spans.push((name, start_addr, end_addr));
            }
        }
        if let Some(&(last_addr, last_name)) = entries.last() {
            if code_end > last_addr {
                spans.push((last_name, last_addr, code_end));
            }
        }

        self.rel_set("func_span", spans.into_iter().collect::<ascent::boxcar::Vec<_>>());
    }

    pub fn load_preset_functions(&mut self) {
        self.load_json_signatures();
        self.load_skip_functions();
    }

    // Load CRT/library function names and prefixes to skip from skip_functions.json.
    fn load_skip_functions(&mut self) {
        let json_str = include_str!("../data/json/skip_functions.json");
        let parsed: serde_json::Value = match serde_json::from_str(json_str) {
            Ok(v) => v,
            Err(e) => {
                log::warn!("Failed to parse skip_functions.json: {}", e);
                return;
            }
        };
        for (category, names) in parsed.as_object().into_iter().flatten() {
            if category == "_comment" {
                continue;
            }
            if category == "skip_prefixes" {
                if let Some(arr) = names.as_array() {
                    for prefix in arr {
                        if let Some(s) = prefix.as_str() {
                            self.skip_function_prefixes.push(leak(s.to_string()));
                        }
                    }
                }
                continue;
            }
            if let Some(arr) = names.as_array() {
                for name in arr {
                    if let Some(s) = name.as_str() {
                        self.skip_function_names.insert(leak(s.to_string()));
                    }
                }
            }
        }
        log::info!("Loaded {} skip function names, {} prefixes",
            self.skip_function_names.len(), self.skip_function_prefixes.len());
    }

    // Check if a function should be skipped (exact, prefix, or base-name after stripping clone suffixes).
    pub fn should_skip_function(&self, name: &str) -> bool {
        if self.skip_function_names.contains(name)
            || self.skip_function_prefixes.iter().any(|p| name.starts_with(p))
        {
            return true;
        }
        // Strip sanitized optimizer clone suffixes and check the base name.
        if let Some(base) = strip_clone_suffix(name) {
            return self.skip_function_names.contains(base)
                || self.skip_function_prefixes.iter().any(|p| base.starts_with(p));
        }
        false
    }

    // Load external function type signatures from extern.json into known_extern_signature and related relations.
    fn load_json_signatures(&mut self) {
        let json_content = include_str!("../data/json/extern.json");

        let extern_funcs: ExternFunctions = match serde_json::from_str(json_content) {
            Ok(funcs) => funcs,
            Err(e) => {
                log::warn!("Failed to parse extern.json: {}. Continuing without extern signatures.", e);
                return;
            }
        };

        for func in extern_funcs.functions {
            let name_sym: Symbol = Box::leak(func.name.clone().into_boxed_str());

            let args_opt: Option<Vec<XType>> =
                func.sig_args.iter().map(|s| xtype_from_string(s)).collect();

            let res_opt = func.sig_res.as_ref().and_then(|s| xtype_from_string(s));

            if let (Some(args), Some(res)) = (args_opt, res_opt) {
                let args_arc = Arc::new(args);
                if func.builtin {
                    self.rel_push("builtin_func_type", (name_sym, args_arc.clone(), res));
                }

                self.rel_push("known_extern_signature", (
                    name_sym,
                    args_arc.len(),
                    res,
                    args_arc,
                ));
            }

            // Derive ptr_params from sig_args: any param with a pointer type
            for (idx, arg_str) in func.sig_args.iter().enumerate() {
                if matches!(arg_str.as_str(),
                    "Xptr" | "Xcharptr" | "Xcharptrptr" | "Xintptr" | "Xfloatptr" | "Xsingleptr" | "Xfuncptr"
                ) {
                    self.rel_push("known_func_param_is_ptr", (name_sym, idx));
                }
            }

            if let Some(ret) = &func.sig_res {
                match ret.as_str() {
                    "Xptr" | "Xcharptr" | "Xintptr" | "Xfloatptr" | "Xsingleptr" | "Xfuncptr" => { self.rel_push("known_func_returns_ptr", (name_sym,)); }
                    "Xlong" => { self.rel_push("known_func_returns_long", (name_sym,)); }
                    "Xint" => { self.rel_push("known_func_returns_int", (name_sym,)); }
                    "Xfloat" => { self.rel_push("known_func_returns_float", (name_sym,)); }
                    "Xsingle" => { self.rel_push("known_func_returns_single", (name_sym,)); }
                    _ => {}
                }
            }
        }
        
        log::info!("Loaded {} external function signatures from extern.json",
                 self.rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("known_extern_signature").count());
    }

    // Print the top N relations by heap size (only works for relations with sizer set).
    pub fn print_top_relations(&self, top_n: usize) {
        let mut sizes: Vec<(&str, usize, usize)> = self.relations.iter()
            .filter_map(|(&name, entry)| {
                entry.size_info().map(|(count, bytes)| (name, count, bytes))
            })
            .collect();
        sizes.sort_by(|a, b| b.2.cmp(&a.2));
        for (name, count, bytes) in sizes.iter().take(top_n) {
            let mb = *bytes as f64 / 1024.0 / 1024.0;
            log::debug!("{:40} {:>10} tuples  {:>10.1} MB", name, count, mb);
        }
    }

    // Execute the full decompilation pipeline: schedule passes, run them (with optional parallelism), handle tracing.
    pub fn run_pipeline(&mut self, binary_path: &std::path::Path, trace_enabled: bool, measure_rule_times: bool) {
        log::info!("Starting decompilation pipeline...");

        let measure_mem = std::env::var("MEASURE_MEM").is_ok();

        self.binary_path = Some(binary_path.to_path_buf());
        self.trace_enabled = trace_enabled;
        self.measure_rule_times = measure_rule_times;

        self.load_preset_functions();

        use crate::decompile::passes::pass::{IRPass, PassScheduler};
        use crate::decompile::passes::*;
        use crate::decompile::analysis::*;

        let passes: Vec<Box<dyn IRPass>> = vec![
            Box::new(abi_pass::AbiPass),
            Box::new(canary_vla_pass::CanaryVlaPass),
            Box::new(asm_pass::AsmPass),
            Box::new(stack_pass::StackAnalysisPass),
            Box::new(mach_pass::MachPass),
            Box::new(linear_pass::LinearPass),
            Box::new(rtl_pass::RTLPass),
            Box::new(type_pass::TypePass),
            Box::new(global_array_pass::GlobalArrayPass),
            Box::new(ptr_to_pass::PtrToPass),
            Box::new(struct_recovery_pass::StructRecoveryPass),
            Box::new(signature_pass::SignatureReconciliationPass),
            Box::new(cminor_pass::CminorPass),
            Box::new(csh_pass::CshPass),
            Box::new(cshminor_pass::CshminorPass),
            Box::new(structuring_pass::StructuringPass),
            Box::new(clight_pass::ClightPass),
            Box::new(clight_pass::ClightFieldPass),
            Box::new(clight_emit_pass::ClightEmitPass),
        ];

        let schedule = PassScheduler::build_schedule(&passes);
        schedule.print();

        for stage in &schedule.stages {
            if stage.passes.len() == 1 {
                let idx = stage.passes[0];
                let pass = &passes[idx];
                let start = std::time::Instant::now();
                let rss_before = if measure_mem { get_rss_mb() } else { 0.0 };
                eprintln!("[PASS] Starting {}", pass.name());
                pass.run(self);
                let elapsed = start.elapsed();
                eprintln!("[PASS] {} completed in {:?}", pass.name(), elapsed);
                if measure_mem {
                    let rss_after = get_rss_mb();
                    let delta = rss_after - rss_before;
                    log::debug!("{} => RSS: {:.0} MB (+{:.0} MB), {:.2?}", pass.name(), rss_after, delta, elapsed);
                    self.print_top_relations(5);
                } else {
                    log::info!("Pass {} completed in {:?}", pass.name(), elapsed);
                }
            } else {
                let pass_names: Vec<&str> = stage.passes.iter()
                    .map(|&idx| passes[idx].name())
                    .collect();

                let pass_ios: Vec<(&[&'static str], &[&'static str])> = stage.passes.iter()
                    .map(|&idx| (passes[idx].inputs(), passes[idx].outputs()))
                    .collect();

                let sub_dbs: Option<Vec<DecompileDB>> = pass_ios.iter()
                    .map(|(inputs, outputs)| {
                        // Clone both inputs and outputs since output relations may have pre-existing data that pass rules read.
                        let mut all_needed: Vec<&'static str> = inputs.to_vec();
                        all_needed.extend_from_slice(outputs);
                        all_needed.sort();
                        all_needed.dedup();
                        let cloned = self.try_clone_relations(&all_needed)?;
                        let mut sub_db = DecompileDB::default();
                        sub_db.measure_rule_times = self.measure_rule_times;
                        sub_db.binary_path = self.binary_path.clone();
                        sub_db.trace_enabled = self.trace_enabled;
                        sub_db.relations = cloned;
                        Some(sub_db)
                    })
                    .collect();

                if let Some(mut sub_dbs) = sub_dbs {
                    log::info!("Running parallel stage: [{}]", pass_names.join(", "));
                    eprintln!("[STAGE] Starting parallel stage: [{}]", pass_names.join(", "));
                    let stage_start = std::time::Instant::now();

                    rayon::scope(|s| {
                        for (i, sub_db) in sub_dbs.iter_mut().enumerate() {
                            let idx = stage.passes[i];
                            let pass = &passes[idx];
                            s.spawn(move |_| {
                                eprintln!("[PASS] Starting {} (parallel)", pass.name());
                                let start = std::time::Instant::now();
                                pass.run(sub_db);
                                let elapsed = start.elapsed();
                                eprintln!("[PASS] {} completed in {:?} (parallel)", pass.name(), elapsed);
                            });
                        }
                    });

                    for (i, mut sub_db) in sub_dbs.into_iter().enumerate() {
                        let (_inputs, outputs) = &pass_ios[i];
                        for &out_name in *outputs {
                            if let Some(val) = sub_db.relations.remove(out_name) {
                                self.relations.insert(out_name, val);
                            }
                        }
                        self.rule_time_reports.extend(sub_db.rule_time_reports);
                    }

                    if measure_mem {
                        let rss_after = get_rss_mb();
                        log::debug!("parallel stage => RSS: {:.0} MB, {:.2?}", rss_after, stage_start.elapsed());
                        self.print_top_relations(5);
                    } else {
                        log::info!("Parallel stage completed in {:?}", stage_start.elapsed());
                    }
                } else {
                    log::info!("Running sequential stage (non-clonable inputs): [{}]", pass_names.join(", "));
                    for &idx in &stage.passes {
                        let pass = &passes[idx];
                        let start = std::time::Instant::now();
                        let rss_before = if measure_mem { get_rss_mb() } else { 0.0 };
                        eprintln!("[PASS] Starting {}", pass.name());
                        pass.run(self);
                        let elapsed = start.elapsed();
                        eprintln!("[PASS] {} completed in {:?}", pass.name(), elapsed);
                        if measure_mem {
                            let rss_after = get_rss_mb();
                            let delta = rss_after - rss_before;
                            log::debug!("{} => RSS: {:.0} MB (+{:.0} MB), {:.2?}", pass.name(), rss_after, delta, elapsed);
                        } else {
                            log::info!("Pass {} completed in {:?}", pass.name(), elapsed);
                        }
                    }
                }
            }
        }

        log::info!("Decompilation pipeline completed.");

        if let Ok(trace_val) = std::env::var("TRACE_NODE") {
            if let Ok(node_addr) = if trace_val.starts_with("0x") || trace_val.starts_with("0X") {
                u64::from_str_radix(&trace_val[2..], 16)
            } else {
                trace_val.parse::<u64>()
            } {
                self.debug_trace_node(node_addr);
            } else {
                eprintln!("[Trace] Invalid TRACE_NODE value: {}", trace_val);
            }
        }

        if let Ok(trace_val) = std::env::var("TRACE_FUNC") {
            if let Ok(func_addr) = if trace_val.starts_with("0x") || trace_val.starts_with("0X") {
                u64::from_str_radix(&trace_val[2..], 16)
            } else {
                trace_val.parse::<u64>()
            } {
                self.debug_trace_func(func_addr);
            }
        }
    }

    // Trace a single node through all pipeline stages (activated via TRACE_NODE env var).
    fn debug_trace_node(&self, node: u64) {
        eprintln!("\n========== TRACE NODE {} (0x{:x}) ==========", node, node);

        let ltl: Vec<_> = self.rel_iter::<(Node, LTLInst)>("ltl_inst").filter(|(n, _)| *n == node).collect();
        if ltl.is_empty() {
            eprintln!("[TRACE] ltl_inst({}) = MISSING", node);
        } else {
            for (_, inst) in &ltl {
                eprintln!("[TRACE] ltl_inst({}) = {:?}", node, inst);
            }
        }

        let iif: Vec<_> = self.rel_iter::<(Node, Address)>("instr_in_function").filter(|(n, _)| *n == node).collect();
        if iif.is_empty() {
            eprintln!("[TRACE] instr_in_function({}) = MISSING", node);
        } else {
            for (_, func) in &iif {
                eprintln!("[TRACE] instr_in_function({}) = func 0x{:x}", node, func);
            }
        }

        let arg_candidates: Vec<_> = self.rel_iter::<(Node, Mreg, Node)>("arg_setup_candidate")
            .filter(|(_, _, call)| *call == node).collect();
        if arg_candidates.is_empty() {
            eprintln!("[TRACE] arg_setup_candidate(_, _, {}) = NONE", node);
        } else {
            for (def, mreg, _) in &arg_candidates {
                eprintln!("[TRACE] arg_setup_candidate(def={}, mreg={:?}, call={})", def, mreg, node);
            }
        }

        let clobbers: Vec<_> = self.rel_iter::<(Node, Mreg, Node)>("call_clobbers_arg_reg")
            .filter(|(_, _, call)| *call == node).collect();
        for (def, mreg, _) in &clobbers {
            eprintln!("[TRACE] call_clobbers_arg_reg(def={}, mreg={:?}, call={})", def, mreg, node);
        }

        let arg_setups: Vec<_> = self.rel_iter::<(Node, Mreg, Node)>("call_arg_setup_detected")
            .filter(|(_, _, call)| *call == node).collect();
        if arg_setups.is_empty() {
            eprintln!("[TRACE] call_arg_setup_detected(_, _, {}) = NONE", node);
        } else {
            for (def, mreg, _) in &arg_setups {
                eprintln!("[TRACE] call_arg_setup_detected(def={}, mreg={:?}, call={})", def, mreg, node);
            }
        }

        let arg_mappings: Vec<_> = self.rel_iter::<(Node, usize, RTLReg)>("call_arg_mapping")
            .filter(|(n, _, _)| *n == node).collect();
        if arg_mappings.is_empty() {
            eprintln!("[TRACE] call_arg_mapping({}, _, _) = NONE", node);
        } else {
            for (_, pos, rtl_reg) in &arg_mappings {
                eprintln!("[TRACE] call_arg_mapping({}, pos={}, rtl_reg={})", node, pos, rtl_reg);
            }
        }

        let args_collected: Vec<_> = self.rel_iter::<(Node, Args)>("call_args_collected")
            .filter(|(n, _)| *n == node).collect();
        if args_collected.is_empty() {
            eprintln!("[TRACE] call_args_collected({}) = MISSING", node);
        } else {
            for (_, args) in &args_collected {
                eprintln!("[TRACE] call_args_collected({}) = {:?}", node, args);
            }
        }

        let ret_regs: Vec<_> = self.rel_iter::<(Node, RTLReg)>("call_return_reg")
            .filter(|(n, _)| *n == node).collect();
        if ret_regs.is_empty() {
            eprintln!("[TRACE] call_return_reg({}) = NONE", node);
        } else {
            for (_, reg) in &ret_regs {
                eprintln!("[TRACE] call_return_reg({}) = {}", node, reg);
            }
        }

        let rtl: Vec<_> = self.rel_iter::<(Node, RTLInst)>("rtl_inst").filter(|(n, _)| *n == node).collect();
        if rtl.is_empty() {
            eprintln!("[TRACE] rtl_inst({}) = MISSING", node);
        } else {
            for (_, inst) in &rtl {
                eprintln!("[TRACE] rtl_inst({}) = {:?}", node, inst);
            }
        }

        let cminor: Vec<_> = self.rel_iter::<(Node, CminorStmt)>("cminor_stmt").filter(|(n, _)| *n == node).collect();
        if cminor.is_empty() {
            eprintln!("[TRACE] cminor_stmt({}) = MISSING", node);
        } else {
            for (_, stmt) in &cminor {
                eprintln!("[TRACE] cminor_stmt({}) = {:?}", node, stmt);
            }
        }

        let csharp: Vec<_> = self.rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt").filter(|(n, _)| *n == node).collect();
        if csharp.is_empty() {
            eprintln!("[TRACE] csharp_stmt({}) = MISSING", node);
        } else {
            for (_, stmt) in &csharp {
                eprintln!("[TRACE] csharp_stmt({}) = {:?}", node, stmt);
            }
        }

        let clight: Vec<_> = self.rel_iter::<(Node, ClightStmt)>("clight_stmt").filter(|(n, _)| *n == node).collect();
        if clight.is_empty() {
            eprintln!("[TRACE] clight_stmt({}) = MISSING", node);
        } else {
            for (_, stmt) in &clight {
                eprintln!("[TRACE] clight_stmt({}) = {:?}", node, stmt);
            }
        }

        let raw: Vec<_> = self.rel_iter::<(Node, ClightStmt)>("clight_stmt_raw").filter(|(n, _)| *n == node).collect();
        if raw.is_empty() {
            eprintln!("[TRACE] clight_stmt_raw({}) = MISSING", node);
        } else {
            for (_, stmt) in &raw {
                eprintln!("[TRACE] clight_stmt_raw({}) = {:?}", node, stmt);
            }
        }

        let owned_loop: Vec<_> = self.rel_iter::<(Address, Node, Node)>("node_owned_by_loop")
            .filter(|(_, n, _)| *n == node).collect();
        for (addr, _, head) in &owned_loop {
            eprintln!("[TRACE] node_owned_by_loop(func=0x{:x}, node={}, header={})", addr, node, head);
        }

        let owned_ite: Vec<_> = self.rel_iter::<(Address, Node, Node)>("node_owned_by_ifthenelse")
            .filter(|(_, n, _)| *n == node).collect();
        for (addr, _, branch) in &owned_ite {
            eprintln!("[TRACE] node_owned_by_ifthenelse(func=0x{:x}, node={}, branch={})", addr, node, branch);
        }

        let for_func: Vec<_> = self.rel_iter::<(Address, Node, ClightStmt)>("clight_stmt_for_func_raw")
            .filter(|(_, n, _)| *n == node).collect();
        if for_func.is_empty() {
            eprintln!("[TRACE] clight_stmt_for_func_raw(_, {}, _) = MISSING", node);
        } else {
            for (addr, _, stmt) in &for_func {
                eprintln!("[TRACE] clight_stmt_for_func_raw(func=0x{:x}, {}, {:?})", addr, node, stmt);
            }
        }

        let dead: Vec<_> = self.rel_iter::<(Address, Node, ClightStmt)>("clight_stmt_dead")
            .filter(|(_, n, _)| *n == node).collect();
        for (addr, _, stmt) in &dead {
            eprintln!("[TRACE] clight_stmt_dead(func=0x{:x}, {}, {:?})", addr, node, stmt);
        }

        let emitted: Vec<_> = self.rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt")
            .filter(|(_, n, _)| *n == node).collect();
        if emitted.is_empty() {
            eprintln!("[TRACE] emit_clight_stmt(_, {}, _) = MISSING", node);
        } else {
            for (addr, _, stmt) in &emitted {
                eprintln!("[TRACE] emit_clight_stmt(func=0x{:x}, {}, {:?})", addr, node, stmt);
            }
        }

        if let Some((_, inst)) = ltl.first() {
            if let LTLInst::Lcall(callee) = inst {
                match callee {
                    Either::Right(Either::Left(target_addr)) => {
                        let sig: Vec<_> = self.rel_iter::<(Address, Signature)>("emit_function_signature")
                            .filter(|(a, _)| a == target_addr).collect();
                        if sig.is_empty() {
                            eprintln!("[TRACE] emit_function_signature(0x{:x}) = MISSING", target_addr);
                        } else {
                            for (_, s) in &sig {
                                eprintln!("[TRACE] emit_function_signature(0x{:x}) = {:?}", target_addr, s);
                            }
                        }
                        let ident: Vec<_> = self.rel_iter::<(Address, Ident)>("addr_to_func_ident")
                            .filter(|(a, _)| a == target_addr).collect();
                        if ident.is_empty() {
                            eprintln!("[TRACE] addr_to_func_ident(0x{:x}) = MISSING", target_addr);
                        } else {
                            for (_, id) in &ident {
                                eprintln!("[TRACE] addr_to_func_ident(0x{:x}) = {}", target_addr, id);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        let reg_rtls: Vec<_> = self.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl")
            .filter(|(n, _, _)| *n == node).collect();
        if !reg_rtls.is_empty() {
            for (_, mreg, rtl) in &reg_rtls {
                eprintln!("[TRACE] reg_rtl({}, {:?}) = {}", node, mreg, rtl);
            }
        }

        let ltl_edges: Vec<_> = self.rel_iter::<(Node, Node)>("ltl_succ")
            .filter(|(n, _)| *n == node).collect();
        for (_, dst) in &ltl_edges {
            eprintln!("[TRACE] ltl_succ({}) = {}", node, dst);
        }

        let cminor_edges: Vec<_> = self.rel_iter::<(Node, Node)>("cminor_succ")
            .filter(|(n, _)| *n == node).collect();
        for (_, dst) in &cminor_edges {
            eprintln!("[TRACE] cminor_succ({}) = {}", node, dst);
        }

        let clight_edges: Vec<_> = self.rel_iter::<(Node, Node)>("clight_succ")
            .filter(|(n, _)| *n == node).collect();
        for (_, dst) in &clight_edges {
            eprintln!("[TRACE] clight_succ({}) = {}", node, dst);
        }

        let loop_heads: Vec<_> = self.rel_iter::<(Address, Node)>("loop_head")
            .filter(|(_, n)| *n == node).collect();
        if loop_heads.is_empty() {
            eprintln!("[TRACE] loop_head(_, {}) = NOT a loop head", node);
        } else {
            for (func, _) in &loop_heads {
                eprintln!("[TRACE] loop_head(func=0x{:x}, {}) = YES", func, node);
            }
        }

        let valid_loops: Vec<_> = self.rel_iter::<(Address, Node)>("valid_loop")
            .filter(|(_, n)| *n == node).collect();
        if valid_loops.is_empty() {
            eprintln!("[TRACE] valid_loop(_, {}) = NOT valid", node);
        } else {
            for (func, _) in &valid_loops {
                eprintln!("[TRACE] valid_loop(func=0x{:x}, {}) = YES", func, node);
            }
        }

        let back_edges: Vec<_> = self.rel_iter::<(Address, Node, Node)>("loop_back_edge")
            .filter(|(_, _, h)| *h == node).collect();
        for (func, latch, _) in &back_edges {
            eprintln!("[TRACE] loop_back_edge(func=0x{:x}, latch={}, header={})", func, latch, node);
        }

        let back_edges_from: Vec<_> = self.rel_iter::<(Address, Node, Node)>("loop_back_edge")
            .filter(|(_, l, _)| *l == node).collect();
        for (func, _, header) in &back_edges_from {
            eprintln!("[TRACE] loop_back_edge(func=0x{:x}, latch={}, header={})", func, node, header);
        }

        let idom_entries: Vec<_> = self.rel_iter::<(Address, Node, Node)>("idom")
            .filter(|(_, n, _)| *n == node).collect();
        for (func, _, d) in &idom_entries {
            eprintln!("[TRACE] idom(func=0x{:x}, {}) = {}", func, node, d);
        }

        let preds: Vec<_> = self.rel_iter::<(Node, Node)>("cminor_succ")
            .filter(|(_, t)| *t == node).collect();
        for (src, _) in &preds {
            eprintln!("[TRACE] cminor_succ({}, {}) [predecessor]", src, node);
        }

        eprintln!("========== END TRACE NODE {} ==========\n", node);
    }

    // Trace all call nodes within a function (activated via TRACE_FUNC env var).
    fn debug_trace_func(&self, func_addr: u64) {
        eprintln!("\n========== TRACE FUNC 0x{:x} ==========", func_addr);

        let func_name: Vec<_> = self.rel_iter::<(Address, Symbol, Node)>("emit_function")
            .filter(|(a, _, _)| *a == func_addr).collect();
        if func_name.is_empty() {
            eprintln!("[TRACE] emit_function(0x{:x}) = NOT FOUND", func_addr);
            return;
        }
        for (_, name, entry) in &func_name {
            eprintln!("[TRACE] emit_function(0x{:x}, name={}, entry={})", func_addr, name, entry);
        }

        let mut nodes: Vec<u64> = self.rel_iter::<(Node, Address)>("instr_in_function")
            .filter(|(_, f)| *f == func_addr)
            .map(|(n, _)| *n)
            .collect();
        nodes.sort();
        eprintln!("[TRACE] Function 0x{:x} has {} nodes: {:?}",
            func_addr, nodes.len(),
            nodes.iter().map(|n| format!("0x{:x}", n)).collect::<Vec<_>>());

        let call_nodes: Vec<u64> = nodes.iter().copied().filter(|n| {
            self.rel_iter::<(Node, LTLInst)>("ltl_inst").any(|(addr, inst)| *addr == *n && matches!(inst, LTLInst::Lcall(_)))
        }).collect();

        if call_nodes.is_empty() {
            eprintln!("[TRACE] No call nodes found in function 0x{:x}", func_addr);
        } else {
            eprintln!("[TRACE] Call nodes: {:?}",
                call_nodes.iter().map(|n| format!("0x{:x}", n)).collect::<Vec<_>>());
            for &call_node in &call_nodes {
                self.debug_trace_node(call_node);
            }
        }

        let ite_bodies: Vec<_> = self.rel_iter::<(Address, Node, Node, bool)>("emit_ifthenelse_body")
            .filter(|(f, _, _, _)| *f == func_addr).collect();
        if !ite_bodies.is_empty() {
            eprintln!("[TRACE] emit_ifthenelse_body entries:");
            let mut sorted_ite: Vec<_> = ite_bodies.iter().collect();
            sorted_ite.sort_by_key(|(_, branch, node, _)| (*branch, *node));
            for (_, branch, node, is_if) in &sorted_ite {
                eprintln!("[TRACE]   branch={} (0x{:x}), node={} (0x{:x}), is_if={}",
                    branch, branch, node, node, is_if);
            }
        }

        let merge_pts: Vec<_> = self.rel_iter::<(Address, Node, Node)>("ifthenelse_merge_point")
            .filter(|(f, _, _)| *f == func_addr).collect();
        for (_, branch, merge) in &merge_pts {
            eprintln!("[TRACE] ifthenelse_merge_point(branch={}, merge={})", branch, merge);
        }

        let emitted: Vec<_> = self.rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt")
            .filter(|(a, _, _)| *a == func_addr).collect();
        eprintln!("[TRACE] emit_clight_stmt count for func 0x{:x}: {}", func_addr, emitted.len());
        let mut sorted_emitted: Vec<_> = emitted.iter().collect();
        sorted_emitted.sort_by_key(|(_, n, _)| *n);
        for (_, n, stmt) in &sorted_emitted {
            eprintln!("[TRACE]   node {} (0x{:x}): {:?}", n, n, stmt);
        }

        eprintln!("========== END TRACE FUNC 0x{:x} ==========\n", func_addr);
    }

}
