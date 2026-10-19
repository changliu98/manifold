// Main decompilation pipeline: type-erased relation storage, CSV loading, and staged pass execution.

use std::any::Any;
use std::collections::HashMap as StdHashMap;
use std::sync::Arc;

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
        Self {
            data: Box::new(value),
            cloner: Some(clone_fn::<T>),
            sizer: None,
        }
    }

    fn new_vec<T: 'static + Clone + Send + Sync>(value: ascent::boxcar::Vec<T>) -> Self {
        Self {
            data: Box::new(value),
            cloner: Some(clone_fn::<ascent::boxcar::Vec<T>>),
            sizer: Some(vec_size_fn::<T>),
        }
    }

    fn new_opaque<T: 'static + Send + Sync>(value: T) -> Self {
        Self {
            data: Box::new(value),
            cloner: None,
            sizer: None,
        }
    }

    fn try_clone(&self) -> Option<Self> {
        let cloner = self.cloner?;
        let cloned_data = cloner(self.data.as_ref());
        Some(Self {
            data: cloned_data,
            cloner: self.cloner,
            sizer: self.sizer,
        })
    }

    pub fn size_info(&self) -> Option<(usize, usize)> {
        self.sizer.map(|f| f(self.data.as_ref()))
    }
}
use crate::decompile::analysis::coverage_pass::PostEmitAuditTrail;

/// Transaction boundary for an IR epoch. Missing relations are part of the
/// snapshot too: restoring must erase facts first produced by the old epoch.
pub(crate) struct RelationCheckpoint {
    names: Vec<&'static str>,
    saved: StdHashMap<&'static str, RelationEntry>,
}
use crate::decompile::passes::c_pass::types::{CType, TranslationUnit};
use crate::decompile::passes::clight_select::query::{
    CommittedInterfaces, GlobalData, InterfaceVars,
};
use crate::decompile::passes::clight_select::select::SelectedFunction;

/// Pipeline policy fixed at the 2026-06 corpus optimum; behavior env gates were removed after A/B decisions closed -- the pass list and CONFIG ARE the configuration; diagnostic env vars (TRACE_NODE etc.) remain but never change output.
pub mod config {
    /// Every tuned magnitude the pipeline reads, grouped by consuming subsystem. Heuristic numbers are declared here as named fields and read back through CONFIG rather than written as literals at their use sites, so the whole tuning surface is enumerable in one place and no two call sites can drift apart. Symbol knowledge (libc signature tables, noreturn sets, header declarations) is NOT configuration and does not belong here: those names are linker-visible and stable. Neither do architectural facts derived from the ABI, such as stack alignment or page size, which are exact rather than tuned.
    pub struct PipelineConfig {
        pub interface: InterfaceConfig,
        pub coalesce: CoalesceConfig,
        pub solve: SolveConfig,
        pub select: SelectConfig,
        pub forloop: ForloopConfig,
        pub ptr_to: PtrToConfig,
        pub struct_recovery: StructRecoveryConfig,
        pub signature: SignatureConfig,
        pub global_array: GlobalArrayConfig,
        pub jump_table: JumpTableConfig,
        pub vla: VlaConfig,
        pub main_detect: MainDetectConfig,
    }

    /// clight_select: program-scope interface commitment.
    pub struct InterfaceConfig {
        /// Maximum number of class-distinct alternatives carried by one program-level interface variable. Rank zero is always retained.
        pub alt_cap: usize,
        /// Master rounds of the program selection solve (`syntax::program`). Each round evaluates every function whose interface choice is new; at the cap the best fully evaluated choice is kept.
        pub max_rounds: usize,
        /// The most Z3 work (rlimit units) those rounds spend, as a multiple of the work of the open solves that bound each function. Each solve is predicted to cost its function's open solve: a round runs only if its exact solves fit, and its partial solves are taken cheapest first while they fit. Work, unlike time, is deterministic. The default of `DecompileDB::max_round_work`, which `--max-round-work` sets.
        pub max_round_work: u64,
        /// Most combinations of open-global alternatives one statement is typed under; the globals of a statement beyond it stay committed program-wide.
        pub max_global_cases: usize,
        /// Fixed, program-independent Stage-B strata. These never depend on the number of registers or selection variables in a particular function.
        pub legality_weight: u64,
        pub structural_weight: u64,
        pub agreement_weight: u64,
        pub prior_weight: u64,
    }

    /// var_reduce: variable coalescing work bounds.
    pub struct CoalesceConfig {
        /// Above this count, skip O(k^2) pair enumeration and use copy-only coalescing (bitset engine).
        pub greedy_cap: usize,
        /// Liveness work bound (nodes x candidates); bail on coalescing when exceeded -- never unsafe, only forgone.
        pub work_bound: usize,
    }

    /// clight_select: z3 resource budgets.
    pub struct SolveConfig {
        /// Deterministic work allowance (Z3 rlimit units) of every selection Optimize check: Stage A/C per function, each refinement round included, and Stage B per program. A backstop against runaway checks, not a tuning knob: with the stratified objective the largest SURE per-function solve uses 433M units over all of its checks.
        pub rlimit: u32,
        /// Work (Z3 rlimit units) a function's refinement transaction may spend over all of its rounds before it starts no further round; the round under way still finishes within `rlimit`. Tuned: every SURE campaign before checks were bounded ran refinement under this gate, and stretching it to `rlimit` multiplied O2 selection time ninefold.
        pub refinement_rlimit: u32,
        /// Wall-clock backstop of the propagator ablation engine only. The default Optimize engine has none, so its output does not depend on machine load.
        pub timeout_ms: u32,
    }

    /// clight_select: statement-tree assembly bounds.
    pub struct SelectConfig {
        /// ITE compound-assembly node cap (CF-9 backstop; post-CF-1 the dispatch duplication that motivated it is gone -- 0 binds over 30+ runs).
        pub ite_max_nodes: usize,
        /// Assembled-tree depth ceiling for splicing a goto target inline; the gate charges the target's full depth so backward-ordered chains cannot compound past it. Keeping the goto is always safe, so this only forgoes structure.
        pub max_goto_inline_depth: usize,
    }

    /// forloop: return-tail duplication bound.
    pub struct ForloopConfig {
        /// Max stmts in a return-tail eligible for EagerReturns/CrossJumpRevert duplication (return-ending blocks, no internal goto/label/decl).
        pub max_dup_tail: usize,
    }

    /// ptr_to: pointer provenance window.
    pub struct PtrToConfig {
        /// |offset| bound above which an Olea/Oaddimm addend is read as an absolute address or a wide constant rather than a field/element displacement, so it does not extend a pointer provenance chain into an integer register. EMPIRICAL, not derived: a real aggregate can exceed 64KiB, and a small absolute address can fall under it. Structurally the right test is whether the addend lands in a mapped image range; this window stands in for that until ptr_to can see the section map.
        pub embed_max_offset: i64,
    }

    /// struct_recovery: stack-window and stride bounds.
    pub struct StructRecoveryConfig {
        /// Largest frame offset admitted into a stack-struct window. EMPIRICAL: a real stack aggregate can be larger, and an unrelated local can fall under it.
        pub max_stack_struct_size: i64,
        /// SR-4 diagnostic only: distance below the cap at which a window is reported as near-cap. Never changes recovery.
        pub near_cap_probe_margin: i64,
        /// Minimum number of same-chunk offsets before a uniform stride is read as an array rather than coincidence.
        pub min_uniform_stride_fields: usize,
    }

    /// signature: call-site reconciliation.
    pub struct SignatureConfig {
        /// Fraction of informative call sites that must agree before an argument position is confirmed.
        pub call_site_confirm_ratio: f64,
    }

    /// global_array: rodata string scanning.
    pub struct GlobalArrayConfig {
        /// Bytes scanned for a NUL before giving up on reading rodata as a string; bounds the scan, never validates it.
        pub max_string_bytes: usize,
    }

    /// cfg: indirect-jump table recovery. EMPIRICAL throughout; membership validation of each entry is the real correctness test, so these are safety bounds rather than decisions.
    pub struct JumpTableConfig {
        /// A CMP/SUB/AND immediate at or above this is not read as a switch bound.
        pub max_bounds_immediate: i64,
        /// Entry count assumed when no static bound is recovered and no data symbol bounds the table.
        pub default_entry_count: usize,
        /// Hard ceiling on entries read from any one table.
        pub max_entry_count: usize,
    }

    /// canary_vla: instruction windows for the alignment and stack-probe idioms. EMPIRICAL: these count instructions along the structural next chain, which stands in for a dataflow slice of the allocation until the pass can consume one.
    pub struct VlaConfig {
        /// Instructions scanned backward from an alloca for the alignment arithmetic (DIV/IDIV/IMUL).
        pub align_scan_back: usize,
        /// Instructions scanned backward from a DIV/IDIV for its operand setup.
        pub div_operand_scan_back: usize,
        /// Instructions scanned further backward for the rounding arithmetic feeding the divide.
        pub align_arith_scan_back: usize,
        /// Instructions scanned backward from an alloca when collecting the stack-probe neighborhood.
        pub probe_scan_back: usize,
        /// Instructions scanned forward from an alloca when collecting the stack-probe neighborhood.
        pub probe_scan_forward: usize,
        /// Instructions scanned backward from a probe SUB for its CMP guard.
        pub probe_block_scan_back: usize,
        /// Instructions scanned forward from a probe SUB for its OR/JMP tail.
        pub probe_block_scan_forward: usize,
        /// Instructions scanned forward from the captured alloca result for its post-adjustment arithmetic.
        pub result_adjust_scan_forward: usize,
    }

    /// function inference: recovering main from the CRT entry.
    pub struct MainDetectConfig {
        /// Instructions scanned forward from the ELF entry for the argument setup that hands main to __libc_start_main.
        pub entry_scan_insns: usize,
    }

    /// THE single assignment of every tuned value. Change a heuristic here, never at a use site.
    pub const CONFIG: PipelineConfig = PipelineConfig {
        interface: InterfaceConfig {
            alt_cap: 4,
            max_rounds: 8,
            max_round_work: 6,
            max_global_cases: 64,
            legality_weight: 1_000_000_000_000,
            structural_weight: 1_000_000,
            agreement_weight: 10_000,
            prior_weight: 1,
        },
        coalesce: CoalesceConfig {
            greedy_cap: 4096,
            work_bound: 8_000_000,
        },
        solve: SolveConfig {
            rlimit: 500_000_000,
            refinement_rlimit: 20_000_000,
            timeout_ms: 120_000,
        },
        select: SelectConfig {
            ite_max_nodes: 1_000_000,
            max_goto_inline_depth: 256,
        },
        forloop: ForloopConfig { max_dup_tail: 8 },
        ptr_to: PtrToConfig {
            embed_max_offset: 65536,
        },
        struct_recovery: StructRecoveryConfig {
            max_stack_struct_size: 1024,
            near_cap_probe_margin: 128,
            min_uniform_stride_fields: 3,
        },
        signature: SignatureConfig {
            call_site_confirm_ratio: 0.5,
        },
        global_array: GlobalArrayConfig {
            max_string_bytes: 4096,
        },
        jump_table: JumpTableConfig {
            max_bounds_immediate: 1000,
            default_entry_count: 256,
            max_entry_count: 512,
        },
        vla: VlaConfig {
            align_scan_back: 30,
            div_operand_scan_back: 3,
            align_arith_scan_back: 6,
            probe_scan_back: 20,
            probe_scan_forward: 10,
            probe_block_scan_back: 5,
            probe_block_scan_forward: 3,
            result_adjust_scan_forward: 6,
        },
        main_detect: MainDetectConfig {
            entry_scan_insns: 32,
        },
    };
}

use crate::mreg::Mreg;
use crate::util::leak;
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
        "Xintunsigned" => Some(XType::Xintunsigned),
        "Xlongunsigned" => Some(XType::Xlongunsigned),
        "Xany32" => Some(XType::Xany32),
        "Xany64" => Some(XType::Xany64),
        _ => None,
    }
}

#[cfg(test)]
mod xtype_parser_tests {
    use super::*;

    #[test]
    fn external_signature_parser_accepts_all_unsigned_scalar_widths() {
        assert_eq!(xtype_from_string("Xintunsigned"), Some(XType::Xintunsigned));
        assert_eq!(
            xtype_from_string("Xlongunsigned"),
            Some(XType::Xlongunsigned)
        );
    }
}

// Central storage for all Datalog relations and pipeline state; hand-written (not macro-generated) for fast compilation.
/// Experimental controls; production is the all-false fixed policy.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SemanticAblations {
    pub disable_storage_search: bool,
    pub disable_existing_views: bool,
    pub global_call_observer: bool,
    /// Selection without the TypeRecovery module: no evidence graph, bindings,
    /// declaration alternatives or projections; declarations keep the legacy profile.
    pub disable_type_recovery: bool,
    /// Selection without validator-backed admission: no value/effect obligations
    /// and no declaration-transfer refinement. Their fact collection still runs.
    pub disable_semantic_admission: bool,
}

pub struct DecompileDB {
    pub relations: StdHashMap<&'static str, RelationEntry>,

    // Target ABI lives here rather than in process-global state, as the in-process ELF/PE harness and parallel sub-DBs require.
    pub target_abi: Option<crate::abi::AbiConfig>,

    // Typed per-function trees produced by ClightSelectPass and consumed by ClightEmitPass.
    pub clight_selected_functions: Vec<SelectedFunction>,
    pub(crate) effect_epoch: u32,
    pub committed_interfaces: CommittedInterfaces,
    pub interface_vars: InterfaceVars,
    pub interface_instance_dump: String,

    pub cast_selected_functions: Vec<SelectedFunction>,
    pub cast_globals: Vec<GlobalData>,
    pub cast_id_to_name: HashMap<usize, String>,
    pub cast_struct_layouts: HashMap<usize, Vec<(i64, String, MemoryChunk)>>,
    pub cast_var_types_for_emission: HashMap<String, CType>,
    pub cast_raw_translation_unit: Option<TranslationUnit>,
    /// Compact, stage-separated exact-statement persistence audit.  It keeps
    /// one baseline key set with per-stage multiplicities instead of retaining
    /// a TranslationUnit or full witness map at every post-emit checkpoint.
    pub(crate) cast_post_emit_audit_trail: Option<PostEmitAuditTrail>,
    pub cast_optimized_translation_unit: Option<TranslationUnit>,

    // Post-selection field decisions. Function/global interface declarations
    // are owned by Stage B; the remaining interface-shaped maps below are
    // populated only by the explicit function-scope ablation path.
    pub decl_solve_field_force_long: HashSet<(String, String)>,
    pub decl_solve_field_ptr_selection: HashMap<(String, String), String>,
    pub decl_solve_fnptr_globals: HashMap<String, CType>,
    // Legacy ablation-only register overrides, retained so
    // --ablate-scope=function reproduces the pre-interprocedural pipeline.
    pub decl_solve_force_long_regs: HashMap<Address, HashSet<RTLReg>>,
    // Legacy ablation-only pointer companion to force_long_regs.
    pub decl_solve_force_ptr_regs: HashMap<Address, HashSet<RTLReg>>,
    // Address-taken stack regions the struct-construction synthesis recovered as a sized buffer: declared `unsigned char[size]` by from_relations so its raw byte-offset store candidates are in-bounds. Keyed by function address, var id.
    pub stack_struct_buffers: HashMap<Address, HashMap<RTLReg, i64>>,
    // Runtime-indexed stack arrays: array local id -> (element MemoryChunk, element count), so arr + i strides by element size.
    pub stack_array_buffers:
        HashMap<Address, HashMap<RTLReg, (crate::x86::types::MemoryChunk, usize)>>,
    pub binary_path: Option<std::path::PathBuf>,
    pub trace_enabled: bool,
    /// Explicit paper ablation: keep the byte-identical per-function selector
    /// path and skip program-scope commitment/re-solving.
    pub ablate_scope_function: bool,
    /// Experimental paper ablation: feed final committed-global flow
    /// disagreements back into Stage B as soft prices and re-open only those
    /// commitments.
    pub ablate_flow_anchor_reopen: bool,
    /// Experimental paper ablation: retain the propagator after a flow-induced
    /// UNSAT by exempting only the audited contradiction sites.
    pub ablate_flow_max_certification: bool,
    pub semantic_ablations: SemanticAblations,
    /// The program selection solve's round work budget, as a multiple of its
    /// open solves' work (`--max-round-work`, default
    /// `CONFIG.interface.max_round_work`).
    pub max_round_work: u64,
    /// Diagnostic CLI output; never changes decompilation behavior.
    pub dump_interface_vars: bool,
    pub dump_interface_instance: bool,
    pub skip_function_names: HashSet<&'static str>,
    pub skip_function_prefixes: Vec<&'static str>,
    // Library-provided DATA globals (gnulib statics): emitted extern so they bind to the library definition instead of colliding at link.
    pub skip_global_names: HashSet<&'static str>,
    pub measure_rule_times: bool,
    pub rule_time_reports: Vec<(String, String)>,
}

impl Default for DecompileDB {
    fn default() -> Self {
        Self {
            relations: StdHashMap::new(),
            target_abi: None,

            clight_selected_functions: Default::default(),
            effect_epoch: 0,
            committed_interfaces: Default::default(),
            interface_vars: Default::default(),
            interface_instance_dump: Default::default(),
            cast_selected_functions: Default::default(),
            cast_globals: Default::default(),
            cast_id_to_name: Default::default(),
            cast_struct_layouts: Default::default(),
            cast_var_types_for_emission: Default::default(),
            cast_raw_translation_unit: None,
            cast_post_emit_audit_trail: None,
            cast_optimized_translation_unit: None,
            decl_solve_field_force_long: Default::default(),
            decl_solve_field_ptr_selection: Default::default(),
            decl_solve_fnptr_globals: Default::default(),
            decl_solve_force_long_regs: Default::default(),
            decl_solve_force_ptr_regs: Default::default(),
            stack_struct_buffers: Default::default(),
            stack_array_buffers: Default::default(),
            binary_path: None,
            trace_enabled: false,
            ablate_scope_function: false,
            ablate_flow_anchor_reopen: false,
            ablate_flow_max_certification: false,
            semantic_ablations: SemanticAblations::default(),
            max_round_work: config::CONFIG.interface.max_round_work,
            dump_interface_vars: false,
            dump_interface_instance: false,
            skip_function_names: HashSet::new(),
            skip_function_prefixes: Vec::new(),
            skip_global_names: HashSet::new(),
            measure_rule_times: false,
            rule_time_reports: Vec::new(),
        }
    }
}

// Low-level relation store used by pass macros and codegen.
impl DecompileDB {
    pub fn unresolved_effect_count(&self) -> usize {
        self.rel_iter::<(u64,crate::decompile::effects::Receipt)>("effect_receipt")
            .filter(|(_,r)| r.artifact.stage==crate::decompile::effects::Stage::Emission
                && r.outcome!=crate::decompile::effects::Outcome::Carried).count()
    }
    pub fn abi(&self) -> &crate::abi::AbiConfig {
        self.target_abi
            .as_ref()
            .expect("target ABI not initialized; call load_from_binary first")
    }

    /// The target's C data model.  Unlike `abi()` this does not insist an image
    /// has been loaded: the in-process fixtures that build C types without
    /// decompiling anything are all written against LP64, so that is the answer
    /// when no target has been established.
    pub fn data_model(&self) -> crate::abi::DataModel {
        self.target_abi
            .as_ref()
            .map_or(crate::abi::DataModel::Lp64, |abi| abi.data_model())
    }

    pub fn put_relation<T: 'static + Clone + Send + Sync>(&mut self, name: &'static str, value: T) {
        self.relations
            .insert(name, RelationEntry::new_clonable(value));
    }

    // Swap a relation in-place between the DB and a pass-local field (avoids heap alloc/dealloc).
    pub fn swap_relation_with<T: 'static + Send + Sync + Default>(
        &mut self,
        name: &'static str,
        field: &mut T,
    ) {
        if let Some(entry) = self.relations.get_mut(name) {
            if let Some(db_val) = entry.data.downcast_mut::<T>() {
                std::mem::swap(field, db_val);
                return;
            }
        }
        let mut default_val = T::default();
        std::mem::swap(field, &mut default_val);
        self.relations
            .insert(name, RelationEntry::new_opaque(default_val));
    }

    // Swap variant for Clone+RelationMeasure types, preserving clone and size functions.
    pub fn swap_relation_with_clonable<
        T: 'static + Clone + Send + Sync + Default + RelationMeasure,
    >(
        &mut self,
        name: &'static str,
        field: &mut T,
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
        self.relations.insert(
            name,
            RelationEntry {
                data: Box::new(default_val),
                cloner: Some(clone_fn::<T>),
                sizer: Some(measure_fn::<T>),
            },
        );
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
    pub fn rel_iter<T: 'static + Send + Sync>(
        &self,
        name: &'static str,
    ) -> impl Iterator<Item = &T> + '_ {
        self.relations
            .get(name)
            .and_then(|entry| entry.data.downcast_ref::<ascent::boxcar::Vec<T>>())
            .into_iter()
            .flat_map(|v| v.iter())
    }

    // Parallel Ascent stores lattice rows behind RwLock so a join can update
    // the value in place.  Keep that representation point-keyed in the DB and
    // expose read guards instead of materializing a pairwise relation merely
    // for imperative consumers.
    pub fn rel_lattice_iter<T: 'static + Send + Sync>(
        &self,
        name: &'static str,
    ) -> impl Iterator<Item = std::sync::RwLockReadGuard<'_, T>> + '_ {
        self.relations
            .get(name)
            .and_then(|entry| {
                entry
                    .data
                    .downcast_ref::<ascent::boxcar::Vec<std::sync::RwLock<T>>>()
            })
            .into_iter()
            .flat_map(|v| v.iter())
            .map(|row| row.read().expect("Ascent lattice row lock poisoned"))
    }

    // Clone a subset of relations for parallel pass execution; returns None if any lacks a clone function.
    fn try_clone_relations(
        &self,
        names: &[&'static str],
    ) -> Option<StdHashMap<&'static str, RelationEntry>> {
        let mut result = StdHashMap::new();
        for &name in names {
            if let Some(entry) = self.relations.get(name) {
                result.insert(name, entry.try_clone()?);
            }
        }
        Some(result)
    }

    pub(crate) fn checkpoint_relations(
        &self,
        names: &[&'static str],
    ) -> Option<RelationCheckpoint> {
        Some(RelationCheckpoint {
            names: names.to_vec(),
            saved: self.try_clone_relations(names)?,
        })
    }

    /// Exchange only the checkpoint's declared relations. The returned epoch
    /// can be restored on validation failure without cloning its large outputs.
    pub(crate) fn exchange_checkpoint(
        &mut self,
        checkpoint: RelationCheckpoint,
    ) -> RelationCheckpoint {
        let previous = checkpoint.names.iter().filter_map(|name| {
            self.relations.remove(name).map(|entry| (*name, entry))
        }).collect();
        self.relations.extend(checkpoint.saved);
        RelationCheckpoint { names: checkpoint.names, saved: previous }
    }

    /// Non-relational outputs are transactional too. Input configuration,
    /// immutable analyses and diagnostic timing do not belong to this swap.
    fn exchange_inference_outputs(&mut self, mut other: Box<Self>) -> Box<Self> {
        macro_rules! exchange { ($($field:ident),* $(,)?) => { $(std::mem::swap(&mut self.$field, &mut other.$field);)* }; }
        exchange!(effect_epoch, clight_selected_functions, committed_interfaces, interface_vars,
            interface_instance_dump, cast_selected_functions, cast_globals,
            cast_id_to_name, cast_struct_layouts, cast_var_types_for_emission,
            cast_raw_translation_unit, cast_post_emit_audit_trail, cast_optimized_translation_unit,
            decl_solve_field_force_long, decl_solve_field_ptr_selection, decl_solve_fnptr_globals,
            decl_solve_force_long_regs, decl_solve_force_ptr_regs, stack_struct_buffers, stack_array_buffers);
        other
    }
}

impl DecompileDB {
    // Derive mach_func ranges and func_span from instr_in_function and func_entry.
    pub(crate) fn compute_mach_func_from_function_inference(&mut self) {
        let code_end: u64 = self
            .rel_iter::<(
                Address,
                usize,
                &'static str,
                &'static str,
                Symbol,
                Symbol,
                Symbol,
                Symbol,
                usize,
                usize,
            )>("unrefinedinstruction")
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

        self.rel_set(
            "mach_func",
            ranges.into_iter().collect::<ascent::boxcar::Vec<_>>(),
        );

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

        self.rel_set(
            "func_span",
            spans.into_iter().collect::<ascent::boxcar::Vec<_>>(),
        );
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
            // Library-provided DATA globals -> skip_global_names (emitted extern), not functions.
            if category == "gnulib_globals" {
                if let Some(arr) = names.as_array() {
                    for name in arr {
                        if let Some(s) = name.as_str() {
                            self.skip_global_names.insert(leak(s.to_string()));
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
        log::info!(
            "Loaded {} skip function names, {} prefixes",
            self.skip_function_names.len(),
            self.skip_function_prefixes.len()
        );
    }

    // Check if a function should be skipped (exact, prefix, or base-name after stripping clone suffixes).
    pub fn should_skip_function(&self, name: &str) -> bool {
        if self.skip_function_names.contains(name)
            || self
                .skip_function_prefixes
                .iter()
                .any(|p| name.starts_with(p))
        {
            return true;
        }
        // Strip sanitized optimizer clone suffixes and check the base name.
        if let Some(base) = strip_clone_suffix(name) {
            return self.skip_function_names.contains(base)
                || self
                    .skip_function_prefixes
                    .iter()
                    .any(|p| base.starts_with(p));
        }
        false
    }

    // A library-provided DATA global (gnulib static): emit extern so it binds to the library definition, not a colliding tentative one.
    pub fn is_lib_global(&self, name: &str) -> bool {
        let base = name.split('@').next().unwrap_or(name);
        self.skip_global_names.contains(base)
    }

    // Load external function type signatures from extern.json into known_extern_signature and related relations.
    fn load_json_signatures(&mut self) {
        let json_content = include_str!("../data/json/extern.json");

        let extern_funcs: ExternFunctions = match serde_json::from_str(json_content) {
            Ok(funcs) => funcs,
            Err(e) => {
                log::warn!(
                    "Failed to parse extern.json: {}. Continuing without extern signatures.",
                    e
                );
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
                self.rel_push(
                    "known_extern_signature",
                    (name_sym, args_arc.len(), res, args_arc),
                );
            }

            // Derive ptr_params from sig_args: any param with a pointer type
            for (idx, arg_str) in func.sig_args.iter().enumerate() {
                if matches!(
                    arg_str.as_str(),
                    "Xptr"
                        | "Xcharptr"
                        | "Xcharptrptr"
                        | "Xintptr"
                        | "Xfloatptr"
                        | "Xsingleptr"
                        | "Xfuncptr"
                ) {
                    self.rel_push("known_func_param_is_ptr", (name_sym, idx));
                }
            }

            if let Some(ret) = &func.sig_res {
                match ret.as_str() {
                    "Xptr" | "Xcharptr" | "Xintptr" | "Xfloatptr" | "Xsingleptr" | "Xfuncptr" => {
                        self.rel_push("known_func_returns_ptr", (name_sym,));
                    }
                    "Xlong" => {
                        self.rel_push("known_func_returns_long", (name_sym,));
                    }
                    _ => {}
                }
            }
        }

        log::info!(
            "Loaded {} external function signatures from extern.json",
            self.rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("known_extern_signature")
                .count()
        );
    }

    // Print the top N relations by heap size (only works for relations with sizer set).
    pub fn print_top_relations(&self, top_n: usize) {
        let mut sizes: Vec<(&str, usize, usize)> = self
            .relations
            .iter()
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
    pub fn run_pipeline(
        &mut self,
        binary_path: &std::path::Path,
        trace_enabled: bool,
        measure_rule_times: bool,
    ) {
        log::info!("Starting decompilation pipeline...");

        let measure_mem = std::env::var("MEASURE_MEM").is_ok();

        self.binary_path = Some(binary_path.to_path_buf());
        self.trace_enabled = trace_enabled;
        self.measure_rule_times = measure_rule_times;

        self.load_preset_functions();

        use crate::decompile::passes::pass::PassScheduler;

        let passes = pipeline_passes();

        let schedule = PassScheduler::build_schedule(&passes);
        schedule.print();

        let rtl_stage = schedule.stages.iter().position(|stage|
            stage.passes.iter().any(|&idx| passes[idx].name() == "rtl"));
        let mut initial_epoch = None;
        let mut initial_buffers = None;
        let mut rollback: Option<(RelationCheckpoint, Box<DecompileDB>, usize)> = None;
        let mut epoch = 0_usize;
        let mut stage_index = 0_usize;
        self.effect_epoch = 0;
        while stage_index < schedule.stages.len() {
            let stage = &schedule.stages[stage_index];
            if Some(stage_index) == rtl_stage && epoch == 0 && !self.semantic_ablations.disable_storage_search {
                // Immutable opaque lattices need not be cloned: the scheduler
                // proves that replayed passes only read them. Checkpoint the
                // union of replay outputs, including read/write overlaps.
                let mut outputs: Vec<_> = schedule.stages[stage_index..].iter()
                    .flat_map(|s| s.passes.iter().flat_map(|&i| passes[i].outputs().iter().copied())).collect();
                outputs.sort_unstable(); outputs.dedup();
                initial_epoch = self.checkpoint_relations(&outputs);
                initial_buffers = Some((self.stack_struct_buffers.clone(), self.stack_array_buffers.clone()));
                if initial_epoch.is_none() {
                    let opaque: Vec<_> = outputs.iter().filter(|name| self.relations.get(**name).is_some_and(|r| r.cloner.is_none())).collect();
                    eprintln!("[selection-feedback] mutable inputs lack checkpoint support: {opaque:?}");
                }
            }
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
                    log::debug!(
                        "{} => RSS: {:.0} MB (+{:.0} MB), {:.2?}",
                        pass.name(),
                        rss_after,
                        delta,
                        elapsed
                    );
                    self.print_top_relations(5);
                } else {
                    log::info!("Pass {} completed in {:?}", pass.name(), elapsed);
                }
            } else {
                let pass_names: Vec<&str> =
                    stage.passes.iter().map(|&idx| passes[idx].name()).collect();

                let pass_ios: Vec<(&[&'static str], &[&'static str], &[&'static str])> = stage
                    .passes
                    .iter()
                    .map(|&idx| {
                        (
                            passes[idx].inputs(),
                            passes[idx].outputs(),
                            passes[idx].extra_reads(),
                        )
                    })
                    .collect();

                let sub_dbs: Option<Vec<DecompileDB>> = pass_ios
                    .iter()
                    .map(|(inputs, outputs, extras)| {
                        // Clone inputs, outputs, and imperative reads. Outputs may have pre-existing data that pass rules read; extras are imperative `rel_iter` reads outside the Ascent program.
                        let mut all_needed: Vec<&'static str> = inputs.to_vec();
                        all_needed.extend_from_slice(outputs);
                        all_needed.extend_from_slice(extras);
                        all_needed.sort();
                        all_needed.dedup();
                        let cloned = self.try_clone_relations(&all_needed)?;
                        let mut sub_db = DecompileDB::default();
                        sub_db.target_abi = self.target_abi.clone();
                        sub_db.measure_rule_times = self.measure_rule_times;
                        sub_db.binary_path = self.binary_path.clone();
                        sub_db.trace_enabled = self.trace_enabled;
                        sub_db.ablate_scope_function = self.ablate_scope_function;
                        sub_db.ablate_flow_anchor_reopen = self.ablate_flow_anchor_reopen;
                        sub_db.ablate_flow_max_certification = self.ablate_flow_max_certification;
                        sub_db.semantic_ablations = self.semantic_ablations;
                        sub_db.max_round_work = self.max_round_work;
                        sub_db.effect_epoch = self.effect_epoch;
                        sub_db.dump_interface_vars = self.dump_interface_vars;
                        sub_db.dump_interface_instance = self.dump_interface_instance;
                        sub_db.relations = cloned;
                        Some(sub_db)
                    })
                    .collect();

                if let Some(mut sub_dbs) = sub_dbs {
                    log::info!("Running parallel stage: [{}]", pass_names.join(", "));
                    eprintln!(
                        "[STAGE] Starting parallel stage: [{}]",
                        pass_names.join(", ")
                    );
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
                                eprintln!(
                                    "[PASS] {} completed in {:?} (parallel)",
                                    pass.name(),
                                    elapsed
                                );
                            });
                        }
                    });

                    for (i, mut sub_db) in sub_dbs.into_iter().enumerate() {
                        let (_inputs, outputs, _extras) = &pass_ios[i];
                        for &out_name in *outputs {
                            if let Some(val) = sub_db.relations.remove(out_name) {
                                self.relations.insert(out_name, val);
                            }
                        }
                        self.rule_time_reports.extend(sub_db.rule_time_reports);
                    }

                    if measure_mem {
                        let rss_after = get_rss_mb();
                        log::debug!(
                            "parallel stage => RSS: {:.0} MB, {:.2?}",
                            rss_after,
                            stage_start.elapsed()
                        );
                        self.print_top_relations(5);
                    } else {
                        log::info!("Parallel stage completed in {:?}", stage_start.elapsed());
                    }
                } else {
                    log::info!(
                        "Running sequential stage (non-clonable inputs): [{}]",
                        pass_names.join(", ")
                    );
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
                            log::debug!(
                                "{} => RSS: {:.0} MB (+{:.0} MB), {:.2?}",
                                pass.name(),
                                rss_after,
                                delta,
                                elapsed
                            );
                        } else {
                            log::info!("Pass {} completed in {:?}", pass.name(), elapsed);
                        }
                    }
                }
            }
            if Some(stage_index) == rtl_stage && rollback.is_some()
                && !crate::decompile::passes::semantic_counterexample::record_materialization(self)
            {
                let (previous, typed, next) = rollback.take().unwrap();
                self.exchange_checkpoint(previous);
                self.exchange_inference_outputs(typed);
                eprintln!("[selection-feedback] epoch={epoch} rolled back: incomplete RTL materialization");
                stage_index = next;
                continue;
            }
            if stage.passes.iter().any(|&idx| passes[idx].name() == "clight_select") {
                if rollback.take().is_some() {
                    eprintln!("[selection-feedback] epoch={epoch} reached final selection on regenerated facts");
                }
                let requests: Vec<_> = self.rel_iter::<(Address, Node, i64, i64)>("selection_storage_request").copied().collect();
                if !requests.is_empty() {
                    let next = if epoch < 4 {
                        initial_epoch.as_ref().and_then(|snapshot| {
                            let saved: Option<StdHashMap<_, _>> = snapshot.saved.iter()
                                .map(|(name, value)| Some((*name, value.try_clone()?))).collect();
                            Some(RelationCheckpoint { names: snapshot.names.clone(), saved: saved? })
                        })
                    } else { None };
                    if let (Some(next), Some(restart)) = (next, rtl_stage) {
                        // Keep only explicit hypotheses and proof history from
                        // the rejected epoch. Every other downstream relation
                        // and typed selection is recomputed from original input.
                        let history = ["semantic_storage_obligation", "semantic_storage_counterexample", "semantic_storage_refinement", "semantic_storage_search"];
                        let history = self.try_clone_relations(&history);
                        let mut objects: Vec<_> = self.rel_iter::<(Address, Node, i64, i64)>("semantic_frame_object").copied().chain(requests).collect();
                        objects.sort_unstable(); objects.dedup();
                        let mut fields: Vec<_> = self.rel_iter::<(Address, i64, i64, MemoryChunk)>("semantic_frame_object_field").copied()
                            .chain(self.rel_iter::<(Address, i64, i64, MemoryChunk)>("selection_storage_field_request").copied()).collect();
                        fields.sort_unstable(); fields.dedup();
                        eprintln!("[selection-feedback] epoch={} requested-objects={}", epoch + 1, objects.len());
                        let previous = self.exchange_checkpoint(next);
                        let typed = self.exchange_inference_outputs(Box::new(Self::default()));
                        if let Some((buffers, arrays)) = &initial_buffers {
                            self.stack_struct_buffers = buffers.clone();
                            self.stack_array_buffers = arrays.clone();
                        }
                        if let Some(history) = history { self.relations.extend(history); }
                        self.rel_set("semantic_frame_object", objects.into_iter().collect::<ascent::boxcar::Vec<_>>());
                        self.rel_set("semantic_frame_object_field", fields.into_iter().collect::<ascent::boxcar::Vec<_>>());
                        rollback = Some((previous, typed, stage_index + 1));
                        epoch += 1;
                        self.effect_epoch = epoch as u32;
                        stage_index = restart;
                        continue;
                    }
                    eprintln!("[selection-feedback] requests={} unresolved: epoch budget or input checkpoint unavailable", requests.len());
                }
            }
            stage_index += 1;
        }

        // The final storage discharge sees the actual post-selection C tree,
        // not a proposed type or an earlier epoch's declaration names.
        crate::decompile::passes::semantic_counterexample::ledger::check_emission(self);
        crate::decompile::effects::finalize(self);
        log::info!("Decompilation pipeline completed.");

        // Comma-separated so one run can follow a whole slot web or branch
        // junction; tracing them one at a time costs a full pipeline per node.
        if let Ok(trace_val) = std::env::var("TRACE_NODE") {
            for item in trace_val
                .split(',')
                .map(str::trim)
                .filter(|s| !s.is_empty())
            {
                if let Ok(node_addr) = if item.starts_with("0x") || item.starts_with("0X") {
                    u64::from_str_radix(&item[2..], 16)
                } else {
                    item.parse::<u64>()
                } {
                    self.debug_trace_node(node_addr);
                } else {
                    eprintln!("[Trace] Invalid TRACE_NODE value: {}", item);
                }
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

        // Diagnostic only, never changes output: dump the semantic Clight CFG
        // (emit_next edges, ownership lattice, per-function statement keys) so
        // ownership gaps can be analyzed offline instead of one TRACE_NODE run
        // per node.
        if let Ok(path) = std::env::var("MANIFOLD_DUMP_CFG") {
            self.debug_dump_clight_cfg(&path);
        }
    }

    // Write the post-pipeline Clight CFG relations as TSV for offline analysis
    // (activated via MANIFOLD_DUMP_CFG env var).
    fn debug_dump_clight_cfg(&self, path: &str) {
        use std::io::Write as _;
        let mut out = match std::fs::File::create(path) {
            Ok(f) => std::io::BufWriter::new(f),
            Err(e) => {
                eprintln!("[dump-cfg] cannot create {}: {}", path, e);
                return;
            }
        };
        for (a, b) in self.rel_iter::<(Node, Node)>("emit_next") {
            let _ = writeln!(out, "next\t{:#x}\t{:#x}", a, b);
        }
        for (func, _, entry) in self.rel_iter::<(Address, Symbol, Node)>("emit_function") {
            let _ = writeln!(out, "entry\t{:#x}\t{:#x}", func, entry);
        }
        for (func, entry) in self.rel_iter::<(Address, Node)>("func_entry_node") {
            let _ = writeln!(out, "resolved_entry\t{:#x}\t{:#x}", func, entry);
        }
        for fact in self.rel_lattice_iter::<(Node, ascent::lattice::set::Set<Address>)>(
            "clight_function_owners",
        ) {
            let (node, owners) = &*fact;
            for owner in owners.0.iter() {
                let _ = writeln!(out, "own\t{:#x}\t{:#x}", node, owner);
            }
        }
        for (addr, node) in self.rel_iter::<(Address, Node)>("clight_targeted_nop_owner") {
            let _ = writeln!(out, "nopown\t{:#x}\t{:#x}", node, addr);
        }
        for (addr, node, stmt) in self.rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt") {
            let kind = match crate::decompile::analysis::coverage_pass::stmt_kind_label(stmt) {
                Some(k) => k,
                None => continue,
            };
            let _ = writeln!(out, "stmt\t{:#x}\t{:#x}\t{}", addr, node, kind);
        }
        for (addr, target) in self.rel_iter::<(Address, Node)>("emit_goto_target") {
            let _ = writeln!(out, "goto_target\t{:#x}\t{:#x}", addr, target);
        }
        for (a, b) in self.rel_iter::<(Node, Node)>("cminor_succ") {
            let _ = writeln!(out, "cminor\t{:#x}\t{:#x}", a, b);
        }
        eprintln!("[dump-cfg] wrote {}", path);
    }

    // Trace a single node through all pipeline stages (activated via TRACE_NODE env var).
    fn debug_trace_node(&self, node: u64) {
        eprintln!("\n========== TRACE NODE {} (0x{:x}) ==========", node, node);

        for (_, size, bytes, mnem, src, dst, op3, op4, _, _) in self
            .rel_iter::<(
                Address,
                usize,
                &'static str,
                &'static str,
                Symbol,
                Symbol,
                Symbol,
                Symbol,
                usize,
                usize,
            )>("instruction")
            .filter(|(addr, _, _, _, _, _, _, _, _, _)| *addr == node)
        {
            eprintln!(
                "[TRACE] instruction({}) = size {} bytes {:?} {} {:?}, {:?}, {:?}, {:?}",
                node, size, bytes, mnem, src, dst, op3, op4
            );
            for operand in [*src, *dst, *op3, *op4] {
                for (_, reg) in self
                    .rel_iter::<(Symbol, &'static str)>("op_register")
                    .filter(|(symbol, _)| *symbol == operand)
                {
                    eprintln!("[TRACE] op_register({:?}) = {}", operand, reg);
                }
                for (_, seg, base, index, scale, disp, width) in self
                    .rel_iter::<(
                        Symbol,
                        &'static str,
                        &'static str,
                        &'static str,
                        i64,
                        i64,
                        usize,
                    )>("op_indirect")
                    .filter(|(symbol, _, _, _, _, _, _)| *symbol == operand)
                {
                    eprintln!(
                        "[TRACE] op_indirect({:?}) = seg {} base {} index {} scale {} disp {} width {}",
                        operand, seg, base, index, scale, disp, width
                    );
                }
            }
        }
        for (_, reg) in self
            .rel_iter::<(Address, Mreg)>("reg_def")
            .filter(|(addr, _)| *addr == node)
        {
            eprintln!("[TRACE] reg_def({}) = {:?}", node, reg);
        }
        for (_, reg) in self
            .rel_iter::<(Address, Mreg)>("reg_use")
            .filter(|(addr, _)| *addr == node)
        {
            eprintln!("[TRACE] reg_use({}) = {:?}", node, reg);
        }
        for (_, xmm, base, index, scale, disp) in self
            .rel_iter::<(Address, Mreg, &'static str, &'static str, i64, i64)>("sse_wide_mem_store")
            .filter(|(addr, _, _, _, _, _)| *addr == node)
        {
            eprintln!(
                "[TRACE] sse_wide_mem_store({}) = {:?}, {}+{}*{}+{}",
                node, xmm, base, index, scale, disp
            );
        }
        for (_, kind, src, ofs, site) in self
            .rel_iter::<(Address, i64, Mreg, i64, Address)>("xmm_hi_mem_store")
            .filter(|(addr, _, _, _, _)| *addr == node)
        {
            eprintln!(
                "[TRACE] xmm_hi_mem_store({}) = kind {} src {:?} ofs {} site {:#x}",
                node, kind, src, ofs, site
            );
        }
        let ltl: Vec<_> = self
            .rel_iter::<(Node, LTLInst)>("ltl_inst")
            .filter(|(n, _)| *n == node)
            .collect();
        if ltl.is_empty() {
            eprintln!("[TRACE] ltl_inst({}) = MISSING", node);
        } else {
            for (_, inst) in &ltl {
                eprintln!("[TRACE] ltl_inst({}) = {:?}", node, inst);
            }
        }

        let iif: Vec<_> = self
            .rel_iter::<(Node, Address)>("instr_in_function")
            .filter(|(n, _)| *n == node)
            .collect();
        if iif.is_empty() {
            eprintln!("[TRACE] instr_in_function({}) = MISSING", node);
        } else {
            for (_, func) in &iif {
                eprintln!("[TRACE] instr_in_function({}) = func 0x{:x}", node, func);
            }
        }

        let live_params: Vec<_> = self
            .rel_iter::<(Address, Address, Mreg)>("arg_reg_param_live_at")
            .filter(|(_, addr, _)| *addr == node)
            .collect();
        if live_params.is_empty() {
            eprintln!("[TRACE] arg_reg_param_live_at(_, {}, _) = NONE", node);
        } else {
            for (func, _, mreg) in &live_params {
                eprintln!(
                    "[TRACE] arg_reg_param_live_at(func=0x{:x}, addr={}, mreg={:?})",
                    func, node, mreg
                );
            }
        }

        let call_targets: Vec<_> = self
            .rel_iter::<(Node, Address)>("call_target_func")
            .filter(|(call, _)| *call == node)
            .collect();
        if call_targets.is_empty() {
            eprintln!("[TRACE] call_target_func({}, _) = NONE", node);
        } else {
            for (_, callee) in &call_targets {
                eprintln!("[TRACE] call_target_func({}, callee=0x{:x})", node, callee);
                let validated: Vec<_> = self
                    .rel_iter::<(Address, Mreg)>("func_param_validated")
                    .filter(|(func, _)| *func == *callee)
                    .collect();
                if validated.is_empty() {
                    eprintln!("[TRACE] func_param_validated(0x{:x}, _) = NONE", callee);
                } else {
                    for (_, mreg) in &validated {
                        eprintln!(
                            "[TRACE] func_param_validated(0x{:x}, mreg={:?})",
                            callee, mreg
                        );
                    }
                }
            }
        }

        let arg_candidates: Vec<_> = self
            .rel_iter::<(Node, Mreg, Node)>("arg_setup_candidate")
            .filter(|(_, _, call)| *call == node)
            .collect();
        if arg_candidates.is_empty() {
            eprintln!("[TRACE] arg_setup_candidate(_, _, {}) = NONE", node);
        } else {
            for (def, mreg, _) in &arg_candidates {
                eprintln!(
                    "[TRACE] arg_setup_candidate(def={}, mreg={:?}, call={})",
                    def, mreg, node
                );
            }
        }

        let arg_joins: Vec<_> = self
            .rel_iter::<(Node, Mreg, RTLReg)>("call_arg_join")
            .filter(|(call, _, _)| *call == node)
            .collect();
        for (_, mreg, use_id) in &arg_joins {
            eprintln!(
                "[TRACE] call_arg_join(call={}, mreg={:?}, use_id={})",
                node, mreg, use_id
            );
        }

        let arg_setups: Vec<_> = self
            .rel_iter::<(Node, Mreg, Node)>("call_arg_setup_detected")
            .filter(|(_, _, call)| *call == node)
            .collect();
        if arg_setups.is_empty() {
            eprintln!("[TRACE] call_arg_setup_detected(_, _, {}) = NONE", node);
        } else {
            for (def, mreg, _) in &arg_setups {
                eprintln!(
                    "[TRACE] call_arg_setup_detected(def={}, mreg={:?}, call={})",
                    def, mreg, node
                );
            }
        }

        let arg_mappings: Vec<_> = self
            .rel_iter::<(Node, usize, RTLReg)>("call_arg_mapping")
            .filter(|(n, _, _)| *n == node)
            .collect();
        if arg_mappings.is_empty() {
            eprintln!("[TRACE] call_arg_mapping({}, _, _) = NONE", node);
        } else {
            for (_, pos, rtl_reg) in &arg_mappings {
                eprintln!(
                    "[TRACE] call_arg_mapping({}, pos={}, rtl_reg={})",
                    node, pos, rtl_reg
                );
            }
        }

        let args_collected: Vec<_> = self
            .rel_iter::<(Node, Args)>("call_args_collected")
            .filter(|(n, _)| *n == node)
            .collect();
        if args_collected.is_empty() {
            eprintln!("[TRACE] call_args_collected({}) = MISSING", node);
        } else {
            for (_, args) in &args_collected {
                eprintln!("[TRACE] call_args_collected({}) = {:?}", node, args);
            }
        }

        let ret_regs: Vec<_> = self
            .rel_iter::<(Node, RTLReg)>("call_return_reg")
            .filter(|(n, _)| *n == node)
            .collect();
        if ret_regs.is_empty() {
            eprintln!("[TRACE] call_return_reg({}) = NONE", node);
        } else {
            for (_, reg) in &ret_regs {
                eprintln!("[TRACE] call_return_reg({}) = {}", node, reg);
            }
        }

        // Frame-slot dataflow.  A slot access lowers only when the machine
        // store survived as mach_imm_stack_init / Lsetstack AND stack_var
        // names the slot at this exact address; when either is absent the
        // access silently produces no RTL def, which is otherwise invisible.
        for (_, ofs, imm, ty) in self
            .rel_iter::<(Address, i64, i64, Typ)>("mach_imm_stack_init")
            .filter(|(a, _, _, _)| *a == node)
        {
            eprintln!(
                "[TRACE] mach_imm_stack_init({}) = ofs {} imm {} {:?}",
                node, ofs, imm, ty
            );
        }
        for (func, _, ofs, reg) in self
            .rel_iter::<(Address, Address, i64, RTLReg)>("stack_xtl")
            .filter(|(_, a, _, _)| *a == node)
        {
            eprintln!(
                "[TRACE] stack_xtl(func=0x{:x}, {}, ofs {}) = {}",
                func, node, ofs, reg
            );
        }
        for (func, _, ofs, reg) in self
            .rel_iter::<(Address, Address, i64, RTLReg)>("stack_var")
            .filter(|(_, a, _, _)| *a == node)
        {
            eprintln!(
                "[TRACE] stack_var(func=0x{:x}, {}, ofs {}) = {}",
                func, node, ofs, reg
            );
        }
        for (def_addr, _, def_ofs, use_addr, _, use_ofs) in self
            .rel_iter::<(Address, Symbol, i64, Address, Symbol, i64)>("stack_def_used")
            .filter(|(d, _, _, u, _, _)| *d == node || *u == node)
        {
            eprintln!(
                "[TRACE] stack_def_used(def 0x{:x} ofs {} -> use 0x{:x} ofs {})",
                def_addr, def_ofs, use_addr, use_ofs
            );
        }

        // The candidate relations are what rtl_pass derived, before the RTL
        // optimizer's copy propagation, DSE and nop collapse ran.  Printing both
        // is what separates "the rule never fired" from "the optimizer removed
        // it", which are otherwise indistinguishable from rtl_inst alone.
        let rtl_cand: Vec<_> = self
            .rel_iter::<(Node, RTLInst)>("rtl_inst_candidate")
            .filter(|(n, _)| *n == node)
            .collect();
        if rtl_cand.is_empty() {
            eprintln!("[TRACE] rtl_inst_candidate({}) = MISSING", node);
        } else {
            for (_, inst) in &rtl_cand {
                eprintln!("[TRACE] rtl_inst_candidate({}) = {:?}", node, inst);
            }
        }
        for (_, succ) in self
            .rel_iter::<(Node, Node)>("rtl_succ_candidate")
            .filter(|(n, _)| *n == node)
        {
            eprintln!("[TRACE] rtl_succ_candidate({}) = {}", node, succ);
        }

        let rtl: Vec<_> = self
            .rel_iter::<(Node, RTLInst)>("rtl_inst")
            .filter(|(n, _)| *n == node)
            .collect();
        if rtl.is_empty() {
            eprintln!("[TRACE] rtl_inst({}) = MISSING", node);
        } else {
            for (_, inst) in &rtl {
                eprintln!("[TRACE] rtl_inst({}) = {:?}", node, inst);
            }
        }
        if self
            .rel_iter::<(Node,)>("copy_eliminated")
            .any(|(n,)| *n == node)
        {
            eprintln!("[TRACE] copy_eliminated({})", node);
        }
        if self
            .rel_iter::<(Node,)>("dead_store")
            .any(|(n,)| *n == node)
        {
            eprintln!("[TRACE] dead_store({})", node);
        }
        for (_, succ) in self
            .rel_iter::<(Node, Node)>("rtl_next")
            .filter(|(src, _)| *src == node)
        {
            eprintln!("[TRACE] rtl_next({}) = {}", node, succ);
        }
        for (pred, _) in self
            .rel_iter::<(Node, Node)>("rtl_next")
            .filter(|(_, dst)| *dst == node)
        {
            eprintln!("[TRACE] rtl_next({}) -> {}", pred, node);
        }

        // Whether this node's operands were declared compile-time constants.
        // A frame-slot pseudo listed here has every use rewritten to the
        // literal, so a slot write that never became a def of that pseudo
        // shows up as a wrong constant rather than as a missing statement.
        let mut node_regs: Vec<RTLReg> = Vec::new();
        for (_, inst) in &rtl {
            match inst {
                RTLInst::Iop(_, args, dst)
                | RTLInst::Iload(_, _, args, dst)
                | RTLInst::Istore(_, _, args, dst) => {
                    node_regs.extend(args.iter().copied());
                    node_regs.push(*dst);
                }
                RTLInst::Icond(_, args, _, _) | RTLInst::Itailcall(_, _, args) => {
                    node_regs.extend(args.iter().copied())
                }
                RTLInst::Icall(_, _, args, dst, _) => {
                    node_regs.extend(args.iter().copied());
                    node_regs.extend(dst.iter().copied());
                }
                RTLInst::Ijumptable(reg, _) | RTLInst::Ireturn(reg) => node_regs.push(*reg),
                _ => {}
            }
        }
        node_regs.sort_unstable();
        node_regs.dedup();
        for (reg, cst) in self
            .rel_iter::<(RTLReg, Constant)>("single_def_const")
            .filter(|(r, _)| node_regs.contains(r))
        {
            eprintln!("[TRACE] single_def_const({}) = {:?}", reg, cst);
            if let Constant::Oaddrsymbol(ident, offset) = cst {
                for (_, symbol) in self
                    .rel_iter::<(Ident, Symbol)>("ident_to_symbol")
                    .filter(|(id, _)| *id == *ident)
                {
                    eprintln!(
                        "[TRACE] address_constant_symbol({}) = {} + {}",
                        reg, symbol, offset
                    );
                    for (label, content, size) in self
                        .rel_iter::<(String, String, usize)>("string_data")
                        .filter(|(label, _, _)| label == symbol)
                    {
                        eprintln!(
                            "[TRACE] string_data({}) = {:?} ({} bytes)",
                            label, content, size
                        );
                    }
                }
                let addr = *ident as Address;
                let pointer_width = self.abi().pointer_size as Address;
                for relation in ["pointer_in_data", "code_pointer_in_data"] {
                    for (slot, target) in
                        self.rel_iter::<(Address, Address)>(relation)
                            .filter(|(slot, _)| {
                                *slot <= addr && addr < slot.saturating_add(pointer_width)
                            })
                    {
                        eprintln!(
                            "[TRACE] {} slot {:#x} -> {:#x} masks address {:#x}",
                            relation, slot, target, addr
                        );
                    }
                }
            }
        }

        let cminor: Vec<_> = self
            .rel_iter::<(Node, CminorStmt)>("cminor_stmt")
            .filter(|(n, _)| *n == node)
            .collect();
        if cminor.is_empty() {
            eprintln!("[TRACE] cminor_stmt({}) = MISSING", node);
        } else {
            for (_, stmt) in &cminor {
                eprintln!("[TRACE] cminor_stmt({}) = {:?}", node, stmt);
            }
        }

        let csharp: Vec<_> = self
            .rel_iter::<(Node, CsharpminorStmt)>("csharp_stmt")
            .filter(|(n, _)| *n == node)
            .collect();
        if csharp.is_empty() {
            eprintln!("[TRACE] csharp_stmt({}) = MISSING", node);
        } else {
            for (_, stmt) in &csharp {
                eprintln!("[TRACE] csharp_stmt({}) = {:?}", node, stmt);
            }
        }

        let clight: Vec<_> = self
            .rel_iter::<(Node, ClightStmt)>("clight_stmt")
            .filter(|(n, _)| *n == node)
            .collect();
        if clight.is_empty() {
            eprintln!("[TRACE] clight_stmt({}) = MISSING", node);
        } else {
            for (_, stmt) in &clight {
                eprintln!("[TRACE] clight_stmt({}) = {:?}", node, stmt);
            }
        }

        let raw: Vec<_> = self
            .rel_iter::<(Node, ClightStmt)>("clight_stmt_raw")
            .filter(|(n, _)| *n == node)
            .collect();
        if raw.is_empty() {
            eprintln!("[TRACE] clight_stmt_raw({}) = MISSING", node);
        } else {
            for (_, stmt) in &raw {
                eprintln!("[TRACE] clight_stmt_raw({}) = {:?}", node, stmt);
            }
        }

        let owned_loop: Vec<_> = self
            .rel_iter::<(Address, Node, Node)>("node_owned_by_loop")
            .filter(|(_, n, _)| *n == node)
            .collect();
        for (addr, _, head) in &owned_loop {
            eprintln!(
                "[TRACE] node_owned_by_loop(func=0x{:x}, node={}, header={})",
                addr, node, head
            );
        }

        let owned_ite: Vec<_> = self
            .rel_iter::<(Address, Node, Node)>("node_owned_by_ifthenelse")
            .filter(|(_, n, _)| *n == node)
            .collect();
        for (addr, _, branch) in &owned_ite {
            eprintln!(
                "[TRACE] node_owned_by_ifthenelse(func=0x{:x}, node={}, branch={})",
                addr, node, branch
            );
        }

        let for_func: Vec<_> = self
            .rel_iter::<(Address, Node, ClightStmt)>("clight_stmt_for_func_raw")
            .filter(|(_, n, _)| *n == node)
            .collect();
        if for_func.is_empty() {
            eprintln!("[TRACE] clight_stmt_for_func_raw(_, {}, _) = MISSING", node);
        } else {
            for (addr, _, stmt) in &for_func {
                eprintln!(
                    "[TRACE] clight_stmt_for_func_raw(func=0x{:x}, {}, {:?})",
                    addr, node, stmt
                );
            }
        }

        let dead: Vec<_> = self
            .rel_iter::<(Address, Node, ClightStmt)>("clight_stmt_dead")
            .filter(|(_, n, _)| *n == node)
            .collect();
        for (addr, _, stmt) in &dead {
            eprintln!(
                "[TRACE] clight_stmt_dead(func=0x{:x}, {}, {:?})",
                addr, node, stmt
            );
        }

        let emitted: Vec<_> = self
            .rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt")
            .filter(|(_, n, _)| *n == node)
            .collect();
        if emitted.is_empty() {
            eprintln!("[TRACE] emit_clight_stmt(_, {}, _) = MISSING", node);
        } else {
            for (addr, _, stmt) in &emitted {
                eprintln!(
                    "[TRACE] emit_clight_stmt(func=0x{:x}, {}, {:?})",
                    addr, node, stmt
                );
            }
        }

        for func in &self.cast_selected_functions {
            if func.statements.contains_key(&node) {
                eprintln!(
                    "[TRACE] selected_function(func=0x{:x}) successors({}) = {:?}",
                    func.address,
                    node,
                    func.successors.get(&node)
                );
                let mut selected_preds: Vec<_> = func
                    .successors
                    .iter()
                    .filter_map(|(src, dsts)| dsts.contains(&node).then_some(*src))
                    .collect();
                selected_preds.sort_unstable();
                eprintln!(
                    "[TRACE] selected_function(func=0x{:x}) predecessors({}) = {:?}",
                    func.address, node, selected_preds
                );
            }
        }

        if let Some((_, inst)) = ltl.first() {
            if let LTLInst::Lcall(callee) = inst {
                match callee {
                    Either::Right(Either::Left(target_addr)) => {
                        let sig: Vec<_> = self
                            .rel_iter::<(Address, Signature)>("emit_function_signature")
                            .filter(|(a, _)| a == target_addr)
                            .collect();
                        if sig.is_empty() {
                            eprintln!(
                                "[TRACE] emit_function_signature(0x{:x}) = MISSING",
                                target_addr
                            );
                        } else {
                            for (_, s) in &sig {
                                eprintln!(
                                    "[TRACE] emit_function_signature(0x{:x}) = {:?}",
                                    target_addr, s
                                );
                            }
                        }
                        let ident: Vec<_> = self
                            .rel_iter::<(Address, Ident)>("addr_to_func_ident")
                            .filter(|(a, _)| a == target_addr)
                            .collect();
                        if ident.is_empty() {
                            eprintln!("[TRACE] addr_to_func_ident(0x{:x}) = MISSING", target_addr);
                        } else {
                            for (_, id) in &ident {
                                eprintln!(
                                    "[TRACE] addr_to_func_ident(0x{:x}) = {}",
                                    target_addr, id
                                );
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        let reg_rtls: Vec<_> = self
            .rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl")
            .filter(|(n, _, _)| *n == node)
            .collect();
        if !reg_rtls.is_empty() {
            for (_, mreg, rtl) in &reg_rtls {
                eprintln!("[TRACE] reg_rtl({}, {:?}) = {}", node, mreg, rtl);
            }
        }

        let ltl_edges: Vec<_> = self
            .rel_iter::<(Node, Node)>("ltl_succ")
            .filter(|(n, _)| *n == node)
            .collect();
        for (_, dst) in &ltl_edges {
            eprintln!("[TRACE] ltl_succ({}) = {}", node, dst);
        }

        let cminor_edges: Vec<_> = self
            .rel_iter::<(Node, Node)>("cminor_succ")
            .filter(|(n, _)| *n == node)
            .collect();
        for (_, dst) in &cminor_edges {
            eprintln!("[TRACE] cminor_succ({}) = {}", node, dst);
        }

        let clight_edges: Vec<_> = self
            .rel_iter::<(Node, Node)>("clight_succ")
            .filter(|(n, _)| *n == node)
            .collect();
        for (_, dst) in &clight_edges {
            eprintln!("[TRACE] clight_succ({}) = {}", node, dst);
        }
        let clight_preds: Vec<_> = self
            .rel_iter::<(Node, Node)>("clight_succ")
            .filter(|(_, dst)| *dst == node)
            .collect();
        for (src, _) in &clight_preds {
            eprintln!("[TRACE] clight_succ({}, {}) [predecessor]", src, node);
        }

        let loop_heads: Vec<_> = self
            .rel_iter::<(Address, Node)>("loop_head")
            .filter(|(_, n)| *n == node)
            .collect();
        if loop_heads.is_empty() {
            eprintln!("[TRACE] loop_head(_, {}) = NOT a loop head", node);
        } else {
            for (func, _) in &loop_heads {
                eprintln!("[TRACE] loop_head(func=0x{:x}, {}) = YES", func, node);
            }
        }

        let valid_loops: Vec<_> = self
            .rel_iter::<(Address, Node)>("valid_loop")
            .filter(|(_, n)| *n == node)
            .collect();
        if valid_loops.is_empty() {
            eprintln!("[TRACE] valid_loop(_, {}) = NOT valid", node);
        } else {
            for (func, _) in &valid_loops {
                eprintln!("[TRACE] valid_loop(func=0x{:x}, {}) = YES", func, node);
            }
        }

        let back_edges: Vec<_> = self
            .rel_iter::<(Address, Node, Node)>("loop_back_edge")
            .filter(|(_, _, h)| *h == node)
            .collect();
        for (func, latch, _) in &back_edges {
            eprintln!(
                "[TRACE] loop_back_edge(func=0x{:x}, latch={}, header={})",
                func, latch, node
            );
        }

        let back_edges_from: Vec<_> = self
            .rel_iter::<(Address, Node, Node)>("loop_back_edge")
            .filter(|(_, l, _)| *l == node)
            .collect();
        for (func, _, header) in &back_edges_from {
            eprintln!(
                "[TRACE] loop_back_edge(func=0x{:x}, latch={}, header={})",
                func, node, header
            );
        }

        let idom_entries: Vec<_> = self
            .rel_iter::<(Address, Node, Node)>("idom")
            .filter(|(_, n, _)| *n == node)
            .collect();
        for (func, _, d) in &idom_entries {
            eprintln!("[TRACE] idom(func=0x{:x}, {}) = {}", func, node, d);
        }

        let preds: Vec<_> = self
            .rel_iter::<(Node, Node)>("cminor_succ")
            .filter(|(_, t)| *t == node)
            .collect();
        for (src, _) in &preds {
            eprintln!("[TRACE] cminor_succ({}, {}) [predecessor]", src, node);
        }

        eprintln!("========== END TRACE NODE {} ==========\n", node);
    }

    // Trace all call nodes within a function (activated via TRACE_FUNC env var).
    fn debug_trace_func(&self, func_addr: u64) {
        eprintln!("\n========== TRACE FUNC 0x{:x} ==========", func_addr);

        let func_name: Vec<_> = self
            .rel_iter::<(Address, Symbol, Node)>("emit_function")
            .filter(|(a, _, _)| *a == func_addr)
            .collect();
        if func_name.is_empty() {
            eprintln!("[TRACE] emit_function(0x{:x}) = NOT FOUND", func_addr);
            return;
        }
        for (_, name, entry) in &func_name {
            eprintln!(
                "[TRACE] emit_function(0x{:x}, name={}, entry={})",
                func_addr, name, entry
            );
        }

        let mut nodes: Vec<u64> = self
            .rel_iter::<(Node, Address)>("instr_in_function")
            .filter(|(_, f)| *f == func_addr)
            .map(|(n, _)| *n)
            .collect();
        nodes.sort();
        eprintln!(
            "[TRACE] Function 0x{:x} has {} nodes: {:?}",
            func_addr,
            nodes.len(),
            nodes
                .iter()
                .map(|n| format!("0x{:x}", n))
                .collect::<Vec<_>>()
        );

        let call_nodes: Vec<u64> = nodes
            .iter()
            .copied()
            .filter(|n| {
                self.rel_iter::<(Node, LTLInst)>("ltl_inst")
                    .any(|(addr, inst)| *addr == *n && matches!(inst, LTLInst::Lcall(_)))
            })
            .collect();

        if call_nodes.is_empty() {
            eprintln!("[TRACE] No call nodes found in function 0x{:x}", func_addr);
        } else {
            eprintln!(
                "[TRACE] Call nodes: {:?}",
                call_nodes
                    .iter()
                    .map(|n| format!("0x{:x}", n))
                    .collect::<Vec<_>>()
            );
            for &call_node in &call_nodes {
                self.debug_trace_node(call_node);
            }
        }

        let ite_bodies: Vec<_> = self
            .rel_iter::<(Address, Node, Node, bool)>("emit_ifthenelse_body")
            .filter(|(f, _, _, _)| *f == func_addr)
            .collect();
        if !ite_bodies.is_empty() {
            eprintln!("[TRACE] emit_ifthenelse_body entries:");
            let mut sorted_ite: Vec<_> = ite_bodies.iter().collect();
            sorted_ite.sort_by_key(|(_, branch, node, _)| (*branch, *node));
            for (_, branch, node, is_if) in &sorted_ite {
                eprintln!(
                    "[TRACE]   branch={} (0x{:x}), node={} (0x{:x}), is_if={}",
                    branch, branch, node, node, is_if
                );
            }
        }

        let merge_pts: Vec<_> = self
            .rel_iter::<(Address, Node, Node)>("ifthenelse_merge_point")
            .filter(|(f, _, _)| *f == func_addr)
            .collect();
        for (_, branch, merge) in &merge_pts {
            eprintln!(
                "[TRACE] ifthenelse_merge_point(branch={}, merge={})",
                branch, merge
            );
        }

        let emitted: Vec<_> = self
            .rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt")
            .filter(|(a, _, _)| *a == func_addr)
            .collect();
        eprintln!(
            "[TRACE] emit_clight_stmt count for func 0x{:x}: {}",
            func_addr,
            emitted.len()
        );
        let mut sorted_emitted: Vec<_> = emitted.iter().collect();
        sorted_emitted.sort_by_key(|(_, n, _)| *n);
        for (_, n, stmt) in &sorted_emitted {
            eprintln!("[TRACE]   node {} (0x{:x}): {:?}", n, n, stmt);
        }

        eprintln!("========== END TRACE FUNC 0x{:x} ==========\n", func_addr);
    }
}

// The pipeline's pass list.  Registration order only breaks ties: the
// scheduler derives the real order from each pass's declared I/O, and adds an
// edge from an earlier pass to a later one that shares a relation.
pub fn pipeline_passes() -> Vec<Box<dyn crate::decompile::passes::pass::IRPass>> {
    use crate::decompile::analysis::*;
    use crate::decompile::passes::pass::IRPass;
    use crate::decompile::passes::*;
    use crate::decompile::postselect::*;

    let passes: Vec<Box<dyn IRPass>> = vec![
        Box::new(abi_pass::AbiPass),
        Box::new(canary_vla_pass::CanaryVlaPass),
        Box::new(asm_pass::AsmPass),
        Box::new(aarch64_asm_pass::Aarch64AsmPass),
        Box::new(arm32_asm_pass::Arm32AsmPass),
        Box::new(abi_pass::NoreturnSitePass),
        Box::new(stack_pass::StackAnalysisPass),
        Box::new(mach_pass::MachPass),
        Box::new(linear_pass::LinearPass),
        Box::new(rtl_dominator_pass::RTLDominatorPass),
        Box::new(frame_coordinate_pass::FrameCoordinatePass),
        Box::new(frame_write_pass::FrameWritePass),
        Box::new(machine_storage_pass::MachineStoragePass),
        Box::new(rtl_pass::RTLPass),
        Box::new(stack_ptr_canonical_pass::StackPtrCanonicalPass),
        Box::new(rtl_optimize_pass::RTLOptimizePass),
        Box::new(relocation_points_to_pass::RelocationPointsToPass),
        Box::new(type_pass::TypePass),
        Box::new(global_array_pass::GlobalArrayPass),
        Box::new(relocation_points_to_pass::RelocationArrayPass),
        Box::new(ptr_to_pass::PtrToPass),
        Box::new(struct_recovery_pass::StructRecoveryPass),
        Box::new(signature_pass::SignatureReconciliationPass),
        // Recover only dependency- and control-compatible local RTL
        // interpretations after signatures make the authoritative RTL final.
        Box::new(rtl_optimize_pass::RTLSupersetPass),
        Box::new(cminor_pass::CminorPass),
        Box::new(csh_pass::CshPass),
        Box::new(cshminor_pass::CshminorPass),
        Box::new(structuring_pass::StructuringPass::default()),
        Box::new(closed_form_switch_pass::ClosedFormSwitchPass),
        Box::new(clight_pass::ClightPass),
        Box::new(clight_pass::ClightFieldPass),
        Box::new(clight_emit_pass::ClightSelectPass),
        Box::new(clight_emit_pass::ClightEmitPass),
        // PhoenixStructurePass removed 2026-06-10: wave-2 adjudication kept it OFF (-3..-10% gotos at 28:1 line churn, UNRESOLVED O-13); recoverable at c291258.
        Box::new(forloop::ForLoopPass),
        Box::new(var_reduce::VarReducePass),
        // Last: fall-through goto elision reads the layout that gets printed, so it must follow every pass that can still move a statement.
        Box::new(goto_elide::GotoElidePass),
        // Diagnostic tail: accounts for every decoded instruction against the printed tree.
        Box::new(coverage_pass::CoverageAuditPass),
    ];
    passes
}

#[cfg(test)]
mod epoch_checkpoint_tests {
    use super::*;

    #[test]
    fn replay_keeps_opaque_immutable_inputs_and_restores_typed_outputs() {
        let mut db = DecompileDB::default();
        db.relations.insert("immutable_analysis", RelationEntry::new_opaque(std::sync::RwLock::new(42_u64)));
        db.rel_push("shared", (1_u64,));
        let original = db.checkpoint_relations(&["shared", "derived"]).unwrap();
        db.rel_push("shared", (2_u64,));
        db.rel_push("derived", (3_u64,));
        db.stack_struct_buffers.insert(1, HashMap::from([(10, 16)]));
        db.cast_id_to_name.insert(10, "original".into());
        db.effect_epoch = 7;
        let old = db.exchange_checkpoint(original);
        let typed = db.exchange_inference_outputs(Box::new(DecompileDB::default()));
        assert_eq!(db.effect_epoch,0);
        db.effect_epoch = 8;
        assert!(db.stack_struct_buffers.is_empty() && db.cast_id_to_name.is_empty());
        assert_eq!(*db.relations["immutable_analysis"].data.downcast_ref::<std::sync::RwLock<u64>>().unwrap().read().unwrap(), 42);
        db.stack_struct_buffers.insert(1, HashMap::from([(10, 99)]));
        db.rel_push("derived", (99_u64,));
        db.exchange_checkpoint(old);
        db.exchange_inference_outputs(typed);
        assert_eq!(db.effect_epoch,7);
        assert_eq!(db.stack_struct_buffers[&1][&10], 16);
        assert_eq!(db.cast_id_to_name[&10], "original");
        assert_eq!(db.rel_iter::<(u64,)>("derived").copied().collect::<Vec<_>>(), vec![(3,)]);
    }

    #[test]
    fn fresh_epoch_restores_shared_inputs_and_removes_old_derived_facts() {
        let mut db = DecompileDB::default();
        db.rel_push("shared_input_output", (1_u64,));
        db.rel_push("unrelated_input", (42_u64,));
        let original = db.checkpoint_relations(&["shared_input_output", "derived_output"]).unwrap();
        db.rel_push("shared_input_output", (2_u64,));
        db.rel_push("derived_output", (3_u64,));
        let first_epoch = db.exchange_checkpoint(original);
        assert_eq!(db.rel_iter::<(u64,)>("shared_input_output").copied().collect::<Vec<_>>(), vec![(1,)]);
        assert_eq!(db.rel_iter::<(u64,)>("derived_output").count(), 0);
        db.rel_push("derived_output", (99_u64,));
        db.exchange_checkpoint(first_epoch);
        assert_eq!(db.rel_iter::<(u64,)>("shared_input_output").copied().collect::<Vec<_>>(), vec![(1,), (2,)]);
        assert_eq!(db.rel_iter::<(u64,)>("derived_output").copied().collect::<Vec<_>>(), vec![(3,)]);
        assert_eq!(db.rel_iter::<(u64,)>("unrelated_input").copied().collect::<Vec<_>>(), vec![(42,)]);
    }
}
