use crate::decompile::elevator::config::CONFIG;
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::clight_pass::is_nonempty_stmt;
use crate::decompile::passes::clight_select::candtype::{CandType, Sign};
use crate::decompile::passes::csh_pass::ident_from_node;
use crate::mreg::Mreg;
use crate::x86::types::*;
use ascent::lattice::set::Set;
use object::{Object, ObjectSection, ObjectSymbol, SymbolKind};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fs;
use std::path::Path;

/// Selection priority over XType, best first.
///
/// This is NOT derivable from `CandType::priority`, and the two are deliberately not unified: the
/// candidate spelling is lossy, so `Xany32` and `Xint` share `int_I32` and `Xany64` and `Xlong`
/// share `int_I64`. The width-only placeholders must lose to their concrete siblings, a distinction
/// only this function can express. Everywhere the spelling IS injective the two must agree, which
/// `xtype_priority_agrees_with_candidate_priority` in the tests below pins.
fn xtype_priority(xtype: &XType) -> u8 {
    match xtype {
        XType::Xvoid => 0,
        XType::Xbool => 1,
        XType::Xany32 => 2,
        XType::Xint => 4,
        XType::Xany64 => 5,
        XType::Xintunsigned => 5,
        XType::Xlong => 6,
        XType::Xlongunsigned => 7,
        XType::Xint8signed | XType::Xint8unsigned => 8,
        XType::Xint16signed | XType::Xint16unsigned => 9,
        XType::Xfloat => 10,
        XType::Xsingle => 11,
        XType::Xptr => 12,
        XType::Xintptr | XType::Xfloatptr | XType::Xsingleptr => 12,
        XType::Xcharptr | XType::Xcharptrptr => 13,
        XType::Xfuncptr => 14,
        XType::XstructPtr(_) => 15,
        _ => 0,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CalleeSignature {
    pub param_count: usize,
    pub return_type: XType,
    #[allow(dead_code)]
    pub param_types: Vec<XType>,
    // True when this callee is variadic; param_count is then the fixed-arg count. Drives the ArityTooMany leniency in ctyping (extra args allowed only for variadics).
    pub is_varargs: bool,
}

/// The class algebra shared by the per-function selector and the
/// program-level interface solve.  It deliberately mirrors
/// `solve::xtype_to_ty`: widths and signedness remain concrete `XType`
/// payloads, while commitment happens over the smaller semantic class.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InterfaceClass {
    Void,
    Int,
    Float,
    PtrInt,
    PtrFloat,
    PtrFunc,
    PtrStruct(usize),
}

impl InterfaceClass {
    pub fn from_xtype(xtype: &XType) -> Self {
        match xtype {
            XType::Xvoid => Self::Void,
            XType::Xfloat | XType::Xsingle => Self::Float,
            XType::Xfloatptr | XType::Xsingleptr => Self::PtrFloat,
            XType::Xfuncptr => Self::PtrFunc,
            XType::XstructPtr(sid) => Self::PtrStruct(*sid),
            XType::Xptr | XType::Xcharptr | XType::Xcharptrptr | XType::Xintptr => Self::PtrInt,
            _ => Self::Int,
        }
    }

    pub fn from_clight(ty: &ClightType) -> Self {
        match ty {
            ClightType::Tvoid => Self::Void,
            ClightType::Tfloat(..) => Self::Float,
            ClightType::Tfunction(..) => Self::PtrFunc,
            ClightType::Tpointer(inner, _) | ClightType::Tarray(inner, _, _) => {
                match inner.as_ref() {
                    ClightType::Tfloat(..) => Self::PtrFloat,
                    ClightType::Tfunction(..) => Self::PtrFunc,
                    ClightType::Tstruct(sid, _) => Self::PtrStruct(*sid),
                    _ => Self::PtrInt,
                }
            }
            _ => Self::Int,
        }
    }

    /// The coarse interface class of a declaration candidate. Total over `CandType`, so a new
    /// candidate variant cannot silently land in the `Int` catch-all.
    pub fn from_candidate(candidate: CandType) -> Self {
        match candidate {
            CandType::Void => Self::Void,
            CandType::PtrStruct(sid) => Self::PtrStruct(sid),
            CandType::PtrDouble | CandType::PtrFloat => Self::PtrFloat,
            CandType::PtrFunc => Self::PtrFunc,
            CandType::PtrLong
            | CandType::PtrVoid
            | CandType::PtrChar
            | CandType::PtrCharPtr
            | CandType::PtrInt => Self::PtrInt,
            CandType::F32 | CandType::F64 => Self::Float,
            CandType::Bool
            | CandType::I8(_)
            | CandType::I16(_)
            | CandType::I32(_)
            | CandType::I64(_) => Self::Int,
        }
    }

    pub fn label(self) -> String {
        match self {
            Self::Void => "void".into(),
            Self::Int => "int".into(),
            Self::Float => "float".into(),
            Self::PtrInt => "ptr(int)".into(),
            Self::PtrFloat => "ptr(float)".into(),
            Self::PtrFunc => "ptr(func)".into(),
            Self::PtrStruct(sid) => format!("ptr(struct:{sid:x})"),
        }
    }

    pub fn is_pointer(self) -> bool {
        matches!(
            self,
            Self::PtrInt | Self::PtrFloat | Self::PtrFunc | Self::PtrStruct(_)
        )
    }

    pub fn representative_xtype(self) -> XType {
        match self {
            Self::Void => XType::Xvoid,
            Self::Int => XType::Xlong,
            Self::Float => XType::Xfloat,
            Self::PtrInt => XType::Xptr,
            Self::PtrFloat => XType::Xfloatptr,
            Self::PtrFunc => XType::Xfuncptr,
            Self::PtrStruct(sid) => XType::XstructPtr(sid),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum InterfaceAuthority {
    CallSite,
    Reconciled,
    DefinitionVoid,
    Extern,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommittedFunctionInterface {
    pub signature: CalleeSignature,
    pub authority: InterfaceAuthority,
}

/// The only downstream authority for function and data-global interfaces.
/// `by_name` covers skip-listed/called-only declarations which have no emitted
/// definition, while `functions` is the stable program-wide identifier view
/// consumed by selection.
#[derive(Debug, Clone, Default)]
pub struct CommittedInterfaces {
    pub functions: BTreeMap<Ident, CommittedFunctionInterface>,
    pub by_name: BTreeMap<String, CommittedFunctionInterface>,
    pub globals: BTreeMap<Ident, XType>,
    /// Concrete declaration for function-pointer data slots.  The class-level
    /// assignment remains in `globals`; this retains call arity/return detail
    /// that Xfuncptr intentionally does not encode.
    pub global_decl_types: BTreeMap<Ident, crate::decompile::passes::c_pass::types::CType>,
    pub hard_globals: BTreeSet<Ident>,
    pub extern_internal_aliases: Vec<(Ident, String)>,
}

impl CommittedInterfaces {
    pub fn callee_signatures(&self) -> HashMap<Ident, CalleeSignature> {
        self.functions
            .iter()
            .map(|(&ident, iface)| (ident, iface.signature.clone()))
            .collect()
    }

    pub fn function(&self, ident: Ident) -> Option<&CalleeSignature> {
        self.functions.get(&ident).map(|iface| &iface.signature)
    }

    pub fn named_function(&self, name: &str) -> Option<&CalleeSignature> {
        self.by_name.get(name).map(|iface| &iface.signature)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InterfaceVarId {
    Param { function: Ident, position: usize },
    Return { function: Ident },
    Global { symbol: Ident },
}

impl InterfaceVarId {
    pub fn label(&self) -> String {
        match self {
            Self::Param { function, position } => format!("fn:{function:x}:param:{position}"),
            Self::Return { function } => format!("fn:{function:x}:return"),
            Self::Global { symbol } => format!("global:{symbol:x}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterfaceAlternative {
    pub class: InterfaceClass,
    pub xtype: XType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterfaceVar {
    pub id: InterfaceVarId,
    /// Rank zero is the pre-interprocedural reconciled/known choice.
    pub domain: Vec<InterfaceAlternative>,
    /// Extern signatures and header-DB globals are ABI ground truth.
    pub hard_rank0: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InterfaceDiagnostics {
    pub register_instances: usize,
    pub aliased_registers: usize,
    pub conflicting_aliased_registers: usize,
    pub extern_internal_aliases: usize,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InterfaceVars {
    pub vars: Vec<InterfaceVar>,
    pub diagnostics: InterfaceDiagnostics,
}

impl InterfaceVars {
    pub fn render_tsv(&self, committed: &CommittedInterfaces) -> String {
        let mut out = String::from("id\thard\trank0\tcommitted\tdomain\n");
        for var in &self.vars {
            let domain = var
                .domain
                .iter()
                .enumerate()
                .map(|(rank, alt)| format!("{rank}:{}:{:?}", alt.class.label(), alt.xtype))
                .collect::<Vec<_>>()
                .join(",");
            out.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\n",
                var.id.label(),
                var.hard_rank0,
                var.domain[0].class.label(),
                match var.id {
                    InterfaceVarId::Param { function, position } => committed
                        .function(function)
                        .and_then(|signature| signature.param_types.get(position))
                        .map(InterfaceClass::from_xtype)
                        .unwrap_or(var.domain[0].class)
                        .label(),
                    InterfaceVarId::Return { function } => committed
                        .function(function)
                        .map(|signature| InterfaceClass::from_xtype(&signature.return_type))
                        .unwrap_or(var.domain[0].class)
                        .label(),
                    InterfaceVarId::Global { symbol } => committed
                        .globals
                        .get(&symbol)
                        .map(InterfaceClass::from_xtype)
                        .unwrap_or(var.domain[0].class)
                        .label(),
                },
                domain
            ));
        }
        out.push_str(&format!(
            "# register_instances={} aliased_registers={} conflicting_aliased_registers={} extern_internal_aliases={}\n",
            self.diagnostics.register_instances,
            self.diagnostics.aliased_registers,
            self.diagnostics.conflicting_aliased_registers,
            self.diagnostics.extern_internal_aliases,
        ));
        out
    }
}

/// Authoritative global object types indexed by the Clight global ident. Loads
/// initially carry only a machine-chunk annotation (for example
/// `MAny64 -> long`); this map joins both ABI declarations and the object-type
/// facts used by the emitter. `EvarSymbol` is excluded: this pipeline uses it
/// for function designators, not object loads.
#[derive(Debug, Clone, Default)]
pub struct KnownGlobalTypes {
    pub by_ident: HashMap<Ident, ClightType>,
    pub hard_idents: BTreeSet<Ident>,
}

#[derive(Debug, Clone)]
pub struct FunctionData {
    pub address: Address,
    pub name: String,
    /// Target pointer width (CompCert's Archi.ptr64), carried from the ABI so the per-function solve and wt audit can type-check against the right width.
    pub ptr64: bool,
    pub entry_node: Node,
    pub return_type: ClightType,
    #[allow(dead_code)]
    pub return_reg: Option<RTLReg>,
    pub param_regs: Vec<RTLReg>,
    pub param_types: Vec<ParamType>,
    pub stack_size: u64,

    pub node_statements: HashMap<Node, Vec<ClightStmt>>,

    pub successors: HashMap<Node, Vec<Node>>,

    pub used_regs: HashSet<RTLReg>,

    /// Registers carrying pipeline-proven pointer values (ABI pointer
    /// parameters/results, address formation, indirect callees, main argv).
    /// Candidate generation remains permissive; the solver consumes this as a
    /// hard class fact so integer reuse cannot truncate the pointer on LP64.
    pub must_pointer_regs: HashSet<RTLReg>,

    pub struct_fields: HashMap<i64, Vec<(i64, Ident, MemoryChunk)>>,

    pub sseq_groups: HashMap<Node, Vec<Node>>,

    pub var_types: HashMap<RTLReg, CandType>,

    /// All type candidates per register for variable declarations; clang_refine swaps declaration types on type mismatch errors.
    pub var_type_candidates: HashMap<RTLReg, Vec<CandType>>,

    /// Current declaration type index per register (used by clang_refine).
    pub var_decl_idx: HashMap<RTLReg, usize>,

    pub loop_headers: HashSet<Node>,
    pub switch_heads: HashSet<Node>,

    pub reg_struct_ids: HashMap<RTLReg, usize>,

    /// Per-struct, per-field type candidates for struct body emission, keyed by (struct_name, field_name); clang_refine advances indices to try different field types.
    pub struct_field_type_candidates: HashMap<(String, String), Vec<String>>,
    pub struct_field_type_idx: HashMap<(String, String), usize>,

    pub reg_to_mreg: HashMap<RTLReg, Mreg>,

    /// Comparison signedness of every ordering Mcond this function owns, keyed
    /// by real address (node ids masked of their synthetic bits). Behavioral
    /// evidence for the propagator engine; empty otherwise.
    pub cond_branch_class:
        HashMap<Address, crate::decompile::passes::clight_select::branch_theory::CmpClass>,

    /// Machine register-class evidence for the whole program, shared by every
    /// per-function solve. `Arc` keeps the two sets allocated once rather than
    /// cloned per recovered function.
    pub class_evidence:
        std::sync::Arc<crate::decompile::passes::clight_select::adequacy::ClassEvidence>,

    /// Machine anchors the flow theory checks this function's selection
    /// against, and the straight-line blocks it folds.
    pub flow_anchors: crate::decompile::passes::clight_select::flow::FlowAnchors,
    pub flow_blocks: Vec<crate::decompile::passes::clight_select::flow::Block>,

    // Known callee signatures indexed by function ident (address)
    pub callee_signatures: HashMap<Ident, CalleeSignature>,

    /// Program-level authoritative global types shared by every per-function
    /// solve.  `Arc` avoids cloning the maps once per recovered function.
    pub known_global_types: std::sync::Arc<KnownGlobalTypes>,
}

#[derive(Debug, Clone)]
pub enum ScalarConstant {
    Int32(i32),
    Int64(i64),
    Float32(f32),
    Float64(f64),
}

impl ScalarConstant {
    /// Render this resolved scalar as a C literal, shared by the writable-.data declaration path and the read-only inline-at-use path so both emit the identical literal.
    pub fn to_cexpr(&self) -> crate::decompile::passes::c_pass::types::CExpr {
        use crate::decompile::passes::c_pass::types::{
            CExpr, FloatLiteral, FloatLiteralSuffix, IntLiteral, IntLiteralBase, IntLiteralSuffix,
        };
        match self {
            ScalarConstant::Float32(v) => CExpr::FloatLit(FloatLiteral {
                value: *v as f64,
                suffix: FloatLiteralSuffix::F,
            }),
            ScalarConstant::Float64(v) => CExpr::FloatLit(FloatLiteral {
                value: *v,
                suffix: FloatLiteralSuffix::None,
            }),
            ScalarConstant::Int32(v) => CExpr::IntLit(IntLiteral {
                value: *v as i128,
                suffix: IntLiteralSuffix::None,
                base: IntLiteralBase::Decimal,
            }),
            ScalarConstant::Int64(v) => CExpr::IntLit(IntLiteral {
                value: *v as i128,
                suffix: IntLiteralSuffix::L,
                base: IntLiteralBase::Decimal,
            }),
        }
    }
}

#[derive(Debug, Clone)]
pub struct GlobalData {
    pub id: usize,
    pub name: String,
    pub is_string: bool,
    pub content: Vec<u8>,
    pub is_pointer: bool,
    pub scalar_value: Option<ScalarConstant>,
    /// True when scalar_value came from a writable (SHF_WRITE) section: it must be emitted as a real initialized declaration and never constant-folded, since the program can store to it.
    pub scalar_writable: bool,
    /// Recovered initializer for a relocated pointer-valued global from
    /// pointer_in_data plus section bytes. A single authoritative relocation
    /// stays scalar; an is_global_array extent may expand it into pointer-sized
    /// slots when the complete extent is aligned and present in the image.
    pub pointer_init: Vec<crate::decompile::passes::c_pass::types::CExpr>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RelocatedPointerWord {
    Target(u64),
    Raw(u64),
}

/// Exact byte coordinate of an address that the disassembly first named as a
/// standalone interior global.  The declaration owner, rather than the
/// synthetic interior name, is the only C object that may own those bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RelocationTargetCoordinate {
    owner: u64,
    offset: i64,
}

fn relocation_declaration_target(
    target: u64,
    target_coordinates: &HashMap<u64, RelocationTargetCoordinate>,
) -> u64 {
    target_coordinates
        .get(&target)
        .map_or(target, |coordinate| coordinate.owner)
}

fn relocation_target_coordinate_expr(
    owner_name: &str,
    coordinate: RelocationTargetCoordinate,
) -> crate::decompile::passes::c_pass::types::CExpr {
    use crate::decompile::passes::c_pass::types::{BinaryOp, CExpr, CType, UnaryOp};
    let owner = CExpr::Var(
        crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(
            owner_name,
        ),
    );
    CExpr::Binary(
        BinaryOp::Add,
        Box::new(CExpr::Cast(
            CType::ptr(CType::char_unsigned()),
            Box::new(CExpr::Unary(UnaryOp::AddrOf, Box::new(owner))),
        )),
        Box::new(CExpr::int(coordinate.offset)),
    )
}

/// Whether a relocation target has a valid C spelling at the point where the
/// current global is declared. Globals are emitted in extraction order, so a
/// name is usable only after its declaration has entered `named_globals_in_scope`;
/// the current object's own name is also in scope within its initializer.
fn relocation_target_is_representable(
    target: u64,
    current_global: u64,
    target_is_string: bool,
    named_targets: &HashMap<u64, String>,
    named_globals_in_scope: &HashSet<u64>,
) -> bool {
    target_is_string
        || (named_targets.contains_key(&target)
            && (target == current_global || named_globals_in_scope.contains(&target)))
}

/// Recover the pointer-sized words used to initialize a relocated global.
///
/// A relocation at `base` is authoritative and is therefore the scalar
/// fallback for every failed aggregate check. A validated aggregate may instead
/// carry its first relocation in an interior word; in that case there is no
/// scalar fallback, and the whole initialized image is accepted atomically or
/// not at all. Aggregate recovery is deliberately driven by an existing
/// `is_global_array` layout rather than by the address of an unrelated later
/// relocation. Candidate extents are tried largest-first and accepted only when
/// pointer-width aligned, fully backed by initialized bytes, contain at least
/// one relocation, and are completely representable. Targets must have a
/// relocatable C spelling; an absolute numeric address is never a safe
/// initializer after recompilation.
fn recover_relocated_pointer_words(
    base: u64,
    pointer_size: usize,
    layouts: &[(usize, usize)],
    readable_bytes: Option<u64>,
    reloc_targets: &BTreeMap<u64, u64>,
    mut target_is_representable: impl FnMut(u64) -> bool,
    mut read_word: impl FnMut(u64, usize) -> Option<u64>,
) -> Vec<RelocatedPointerWord> {
    let scalar = match reloc_targets.get(&base).copied() {
        Some(base_target) if target_is_representable(base_target) => {
            vec![RelocatedPointerWord::Target(base_target)]
        }
        // A relocation whose target has no valid C spelling cannot be
        // reconstructed as either a scalar or part of an aggregate.
        Some(_) => return Vec::new(),
        None => Vec::new(),
    };

    if !matches!(pointer_size, 4 | 8) {
        return scalar;
    }
    let Some(readable_bytes) = readable_bytes else {
        return scalar;
    };

    let mut candidate_extents: Vec<usize> = layouts
        .iter()
        .copied()
        .filter_map(|(elem_size, count)| {
            if elem_size == 0 || count == 0 || elem_size % pointer_size != 0 {
                return None;
            }
            let extent = elem_size.checked_mul(count)?;
            if extent < pointer_size || extent % pointer_size != 0 {
                return None;
            }
            let extent_u64 = u64::try_from(extent).ok()?;
            if extent_u64 > readable_bytes || base.checked_add(extent_u64).is_none() {
                return None;
            }
            Some(extent)
        })
        .collect();
    candidate_extents.sort_unstable_by(|left, right| right.cmp(left));
    candidate_extents.dedup();

    for extent in candidate_extents {
        let mut words = Vec::new();
        let mut complete = true;
        let mut saw_relocation = false;
        for offset in (0..extent).step_by(pointer_size) {
            let Some(offset) = u64::try_from(offset).ok() else {
                complete = false;
                break;
            };
            let Some(slot) = base.checked_add(offset) else {
                complete = false;
                break;
            };
            if let Some(&target) = reloc_targets.get(&slot) {
                if !target_is_representable(target) {
                    complete = false;
                    break;
                }
                saw_relocation = true;
                words.push(RelocatedPointerWord::Target(target));
            } else if let Some(raw) = read_word(slot, pointer_size) {
                words.push(RelocatedPointerWord::Raw(raw));
            } else {
                complete = false;
                break;
            }
        }

        if complete && saw_relocation && !words.is_empty() {
            return words;
        }
    }

    scalar
}

fn consecutive_pointer_run(
    base: u64,
    pointer_size: usize,
    code_pointer_slots: &BTreeSet<u64>,
    object_starts: &HashSet<u64>,
) -> usize {
    if !matches!(pointer_size, 4 | 8) || !code_pointer_slots.contains(&base) {
        return 0;
    }
    let mut count = 1usize;
    loop {
        let Some(offset) = count.checked_mul(pointer_size) else {
            break;
        };
        let Some(slot) = base.checked_add(offset as u64) else {
            break;
        };
        if object_starts.contains(&slot) || !code_pointer_slots.contains(&slot) {
            break;
        }
        count += 1;
    }
    count
}

/// Order global definitions so every acyclic pointer-initializer dependency is
/// declared before the object whose initializer names it.  This is C scope
/// ordering only: the numeric address is used solely as a deterministic
/// tie-break among unrelated declarations, never as a reachability fact.
///
/// A relocation in a validated array extent is a dependency of the array's
/// base definition, not a standalone global at the relocation slot.  Cyclic
/// components cannot be made valid by reordering alone and retain stable
/// address order; initializer recovery will conservatively reject any still-
/// forward edge in such a component.
fn order_globals_for_pointer_initializers(
    global_ids: &[usize],
    array_layouts: &HashMap<usize, Vec<(usize, usize)>>,
    pointer_targets: &BTreeMap<u64, u64>,
    target_coordinates: &HashMap<u64, RelocationTargetCoordinate>,
) -> Vec<usize> {
    let ids: BTreeSet<usize> = global_ids.iter().copied().collect();
    let mut outgoing: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    let mut indegree: BTreeMap<usize, usize> = ids.iter().copied().map(|id| (id, 0)).collect();

    for &source in &ids {
        let base = source as u64;
        let max_extent = array_layouts
            .get(&source)
            .into_iter()
            .flatten()
            .filter_map(|&(elem_size, count)| elem_size.checked_mul(count))
            .filter(|&extent| extent > 0)
            .max()
            .unwrap_or(1);
        let Some(end) = base.checked_add(max_extent as u64) else {
            continue;
        };

        for (&slot, &raw_target) in pointer_targets.range(base..end) {
            if slot != base && !array_layouts.contains_key(&source) {
                continue;
            }
            let target = relocation_declaration_target(raw_target, target_coordinates);
            let Ok(target) = usize::try_from(target) else {
                continue;
            };
            if target == source || !ids.contains(&target) {
                continue;
            }
            if outgoing.entry(target).or_default().insert(source) {
                *indegree
                    .get_mut(&source)
                    .expect("every dependency source is a global id") += 1;
            }
        }
    }

    let mut ready: BTreeSet<usize> = indegree
        .iter()
        .filter_map(|(&id, &degree)| (degree == 0).then_some(id))
        .collect();
    let mut ordered = Vec::with_capacity(ids.len());
    while let Some(id) = ready.pop_first() {
        ordered.push(id);
        if let Some(dependents) = outgoing.get(&id) {
            for &dependent in dependents {
                let degree = indegree
                    .get_mut(&dependent)
                    .expect("every dependent is a global id");
                *degree -= 1;
                if *degree == 0 {
                    ready.insert(dependent);
                }
            }
        }
    }

    // Stable, lossless fallback for cycles.  Recovery's scope check remains
    // the authority that suppresses a declaration-order-invalid initializer.
    let emitted: BTreeSet<usize> = ordered.iter().copied().collect();
    for &id in ids.difference(&emitted) {
        ordered.push(id);
    }
    ordered
}

impl FunctionData {
    pub fn new(
        address: Address,
        name: String,
        param_regs: Vec<RTLReg>,
        param_types: Vec<ParamType>,
        return_reg: Option<RTLReg>,
        stack_size: u64,
        entry_node: Node,
        ptr64: bool,
    ) -> Self {
        FunctionData {
            address,
            name,
            ptr64,
            entry_node,
            return_type: ClightType::Tvoid,
            return_reg,
            param_regs,
            param_types,
            stack_size,
            node_statements: HashMap::new(),
            successors: HashMap::new(),
            used_regs: HashSet::new(),
            must_pointer_regs: HashSet::new(),
            struct_fields: HashMap::new(),
            sseq_groups: HashMap::new(),
            var_types: HashMap::new(),
            var_type_candidates: HashMap::new(),
            var_decl_idx: HashMap::new(),
            struct_field_type_candidates: HashMap::new(),
            struct_field_type_idx: HashMap::new(),
            loop_headers: HashSet::new(),
            switch_heads: HashSet::new(),
            reg_struct_ids: HashMap::new(),
            reg_to_mreg: HashMap::new(),
            cond_branch_class: HashMap::new(),
            callee_signatures: HashMap::new(),
            known_global_types: std::sync::Arc::new(KnownGlobalTypes::default()),
            class_evidence: std::sync::Arc::new(Default::default()),
            flow_anchors: Default::default(),
            flow_blocks: Vec::new(),
        }
    }
}

/// Collect the machine anchors the flow theory checks against, and partition
/// each function into straight-line blocks.
///
/// Every source here is a fact the pipeline already maintains: the memory chunk
/// an RTL load or store commits (an instruction-encoding fact), the known
/// external signatures (an ABI fact), and the committed global types. Nothing
/// derived from a candidate's own type guess is used as an anchor, and
/// per-node register-file class is deliberately NOT used -- at web level it is
/// already consumed upstream, and per node it is unsound for bit-copies.
fn build_flow_anchors(db: &DecompileDB, func_map: &mut HashMap<Address, FunctionData>) {
    use crate::decompile::passes::clight_select::flow;

    // Chunk anchors: an Iload commits its destination, an Istore its source.
    let mut chunk_at: BTreeMap<Node, (RTLReg, flow::AVal)> = BTreeMap::new();
    for (node, inst) in db.rel_iter::<(Node, RTLInst)>("rtl_inst") {
        let (chunk, reg) = match inst {
            RTLInst::Iload(chunk, _, _, dst) => (*chunk, *dst),
            RTLInst::Istore(chunk, _, _, src) => (*chunk, *src),
            _ => continue,
        };
        let anchor = flow::anchor_of_chunk(chunk);
        if anchor.is_top() {
            continue;
        }
        // A node carrying two different chunk commitments is not a fact we can
        // rely on, so drop both rather than pick one.
        match chunk_at.entry(*node) {
            std::collections::btree_map::Entry::Occupied(mut e) => {
                if *e.get() != (reg, anchor) {
                    e.insert((reg, flow::AVal::top()));
                }
            }
            std::collections::btree_map::Entry::Vacant(e) => {
                e.insert((reg, anchor));
            }
        }
    }
    chunk_at.retain(|_, (_, a)| !a.is_top());

    // Extern signatures, deterministically resolved exactly as the committed
    // interface build resolves them: sort the arities and take the first.
    let mut sigs_by_name: BTreeMap<String, Vec<(usize, XType, Vec<XType>)>> = BTreeMap::new();
    for (name, count, ret, params) in
        db.rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("known_extern_signature")
    {
        let name =
            crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(name);
        sigs_by_name
            .entry(name)
            .or_default()
            .push((*count, *ret, params.as_ref().clone()));
    }
    let extern_sig: BTreeMap<String, (XType, Vec<XType>)> = sigs_by_name
        .into_iter()
        .map(|(name, mut cands)| {
            cands.sort();
            let (_, ret, params) = cands.remove(0);
            (name, (ret, params))
        })
        .collect();

    for func in func_map.values_mut() {
        let ptr64 = func.ptr64;
        let mut anchors = flow::FlowAnchors::default();

        let mut nodes: Vec<Node> = func.node_statements.keys().copied().collect();
        nodes.sort_unstable();
        for node in &nodes {
            if let Some(&(reg, aval)) = chunk_at.get(node) {
                anchors.chunk.insert(*node, (reg, aval));
            }
            let cands = &func.node_statements[node];
            if let Some(name) = flow::agreed_callee(cands) {
                if let Some((ret, params)) = extern_sig.get(&name) {
                    let arg_anchors: Vec<flow::AVal> = params
                        .iter()
                        .map(|p| flow::anchor_of_xtype(p, ptr64))
                        .collect();
                    anchors
                        .call
                        .insert(*node, (arg_anchors, flow::anchor_of_xtype(ret, ptr64)));
                }
            }
        }
        for (ident, ty) in &func.known_global_types.by_ident {
            let a = flow::claim_of_type(ty, ptr64);
            if !a.is_top() {
                anchors.global.insert(*ident, a);
            }
        }

        let successors: BTreeMap<Node, Vec<Node>> = func
            .successors
            .iter()
            .map(|(k, v)| {
                let mut v = v.clone();
                v.sort_unstable();
                v.dedup();
                (*k, v)
            })
            .collect();
        func.flow_blocks = flow::basic_blocks(&nodes, &successors);
        func.flow_anchors = anchors;
    }
}

fn prefer_known_global_type(slot: &mut XType, candidate: XType) {
    if (xtype_priority(&candidate), candidate) > (xtype_priority(slot), *slot) {
        *slot = candidate;
    }
}

/// Pick a concrete carrier for a Clight type without changing its interface
/// class.  This is used only when the authoritative source is the header DB,
/// which stores canonical Clight types rather than XTypes.
pub(crate) fn representative_xtype_for_clight(ty: &ClightType) -> XType {
    match ty {
        ClightType::Tvoid => XType::Xvoid,
        ClightType::Tint(ClightIntSize::IBool, ..) => XType::Xbool,
        ClightType::Tint(ClightIntSize::I8, ClightSignedness::Signed, _) => XType::Xint8signed,
        ClightType::Tint(ClightIntSize::I8, ClightSignedness::Unsigned, _) => XType::Xint8unsigned,
        ClightType::Tint(ClightIntSize::I16, ClightSignedness::Signed, _) => XType::Xint16signed,
        ClightType::Tint(ClightIntSize::I16, ClightSignedness::Unsigned, _) => {
            XType::Xint16unsigned
        }
        ClightType::Tint(_, ClightSignedness::Unsigned, _) => XType::Xintunsigned,
        ClightType::Tint(..) => XType::Xint,
        ClightType::Tlong(ClightSignedness::Unsigned, _) => XType::Xlongunsigned,
        ClightType::Tlong(..) | ClightType::Tint128(..) => XType::Xlong,
        ClightType::Tfloat(ClightFloatSize::F32, _) => XType::Xsingle,
        ClightType::Tfloat(ClightFloatSize::F64, _) => XType::Xfloat,
        ClightType::Tfunction(..) => XType::Xfuncptr,
        ClightType::Tpointer(inner, _) | ClightType::Tarray(inner, _, _) => match inner.as_ref() {
            ClightType::Tfloat(ClightFloatSize::F32, _) => XType::Xsingleptr,
            ClightType::Tfloat(..) => XType::Xfloatptr,
            ClightType::Tfunction(..) => XType::Xfuncptr,
            ClightType::Tstruct(sid, _) => XType::XstructPtr(*sid),
            ClightType::Tint(ClightIntSize::I8, ..) => XType::Xcharptr,
            ClightType::Tint(..) => XType::Xintptr,
            _ => XType::Xptr,
        },
        ClightType::Tstruct(sid, _) => XType::XstructPtr(*sid),
        ClightType::Tunion(..) => XType::Xlong,
    }
}

/// Reproduce the emitter's global-object declaration authority for the exact
/// selector audit. `global_symbol` is the provenance guard: `symbols` and
/// `ident_to_symbol` also contain functions, so using either can type a function
/// designator as an object when the ABI tables happen to contain the same
/// spelling (for example `__ctype_b_loc`). ABI types override inferred object
/// types; among inferred facts, char* is more specific than void*. The
/// header-variable table is the emitter's final authority and therefore has
/// highest precedence here as well.
fn extract_known_global_types(db: &DecompileDB) -> KnownGlobalTypes {
    let mut xtype_by_name: BTreeMap<String, XType> = BTreeMap::new();
    for (name, xtype) in db.rel_iter::<(Symbol, XType)>("known_global_type") {
        xtype_by_name
            .entry((*name).to_string())
            .and_modify(|current| prefer_known_global_type(current, *xtype))
            .or_insert(*xtype);
    }

    let mut object_names: BTreeMap<Ident, BTreeSet<String>> = BTreeMap::new();
    for (addr, name) in db.rel_iter::<(Address, Symbol)>("global_symbol") {
        object_names
            .entry(*addr as Ident)
            .or_default()
            .insert((*name).to_string());
    }

    let mut xtype_by_ident: BTreeMap<Ident, XType> = BTreeMap::new();
    for (ident,) in db.rel_iter::<(Ident,)>("emit_global_is_ptr") {
        if object_names.contains_key(ident) {
            xtype_by_ident.insert(*ident, XType::Xptr);
        }
    }
    for (ident,) in db.rel_iter::<(Ident,)>("emit_global_is_char_ptr") {
        if object_names.contains_key(ident) {
            xtype_by_ident.insert(*ident, XType::Xcharptr);
        }
    }

    for (&ident, names) in &object_names {
        let mut abi_type = None;
        for name in names {
            // Dynamic-symbol spellings may retain a version suffix; the ABI
            // table uses the unversioned C spelling.
            let canonical_name = name.split('@').next().unwrap_or(name.as_str());
            let Some(&xtype) = xtype_by_name
                .get(name)
                .or_else(|| xtype_by_name.get(canonical_name))
            else {
                continue;
            };
            match &mut abi_type {
                Some(current) => prefer_known_global_type(current, xtype),
                None => abi_type = Some(xtype),
            }
        }
        if let Some(xtype) = abi_type {
            xtype_by_ident.insert(ident, xtype);
        }
    }

    let by_ident = xtype_by_ident
        .into_iter()
        .map(|(ident, xtype)| {
            (
                ident,
                crate::decompile::passes::clight_select::wt_audit::xtype_to_clight(&xtype),
            )
        })
        .collect::<HashMap<_, _>>();

    let mut by_ident = by_ident;
    let mut hard_idents = BTreeSet::new();
    let header_vars = &crate::decompile::passes::c_pass::header_db::header_db().variables;
    for (&ident, names) in &object_names {
        for name in names {
            let canonical_name = name.split('@').next().unwrap_or(name.as_str());
            let emitted_name =
                crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(
                    canonical_name,
                );
            let Some(spelling) = header_vars.get(emitted_name.as_str()) else {
                continue;
            };
            if let Some(ty) =
                crate::decompile::passes::c_pass::header_db::canonical_variable_clight_type(
                    spelling,
                )
            {
                by_ident.insert(ident, ty);
                hard_idents.insert(ident);
                break;
            }
        }
    }

    KnownGlobalTypes {
        by_ident,
        hard_idents,
    }
}

/// Per-(function, reg) XType deduped from emit_function_param_type: int beats long-width placeholders, else highest priority wins; shared so extract_functions and extract_callee_signatures agree.
pub(crate) fn build_param_xtypes(db: &DecompileDB) -> HashMap<(Address, RTLReg), XType> {
    let mut param_xtypes: HashMap<(Address, RTLReg), XType> = HashMap::new();
    for (addr, reg, xtype) in db.rel_iter::<(Address, RTLReg, XType)>("emit_function_param_type") {
        param_xtypes
            .entry((*addr, *reg))
            .and_modify(|existing| {
                let dominated_by_int = matches!(
                    (*existing, *xtype),
                    (
                        XType::Xlong | XType::Xlongunsigned,
                        XType::Xint | XType::Xintunsigned
                    )
                );
                if dominated_by_int {
                    *existing = *xtype;
                } else if !matches!(
                    (*existing, *xtype),
                    (
                        XType::Xint | XType::Xintunsigned,
                        XType::Xlong | XType::Xlongunsigned
                    )
                ) {
                    if xtype_priority(xtype) > xtype_priority(existing) {
                        *existing = *xtype;
                    }
                }
            })
            .or_insert(*xtype);
    }
    param_xtypes
}

/// Select the single semantic return type from the reconciled candidate set.
/// Relations are sets, so their iteration order cannot decide a declaration
/// or the signature seen by callers.
pub(crate) fn best_reconciled_return_xtype(db: &DecompileDB, addr: Address) -> Option<XType> {
    db.rel_iter::<(Address, XType)>("emit_function_return_type_xtype")
        .filter(|(a, _)| *a == addr)
        .map(|(_, t)| *t)
        .max_by_key(|t| {
            (
                crate::decompile::passes::clight_pass::xtype_refine_priority(t),
                *t,
            )
        })
}

/// Maps (function, RTLReg) to entry-node Mreg for CC-slot ordering; keeps the smallest mreg explicitly so a broken single-value invariant in reg_rtl doesn't silently let Ascent set order pick the winner.
pub(crate) fn build_rtl_to_mreg_at_entry(db: &DecompileDB) -> HashMap<(Address, RTLReg), Mreg> {
    let mut rtl_to_mreg_at_entry: HashMap<(Address, RTLReg), Mreg> = HashMap::new();
    let mut entry_to_addrs: HashMap<Node, Vec<Address>> = HashMap::new();
    for (a, _, n) in db.rel_iter::<(Address, Symbol, Node)>("emit_function") {
        entry_to_addrs.entry(*n).or_default().push(*a);
    }
    for (node, mreg, rtl_reg) in db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl") {
        if let Some(addrs) = entry_to_addrs.get(node) {
            for &addr in addrs {
                rtl_to_mreg_at_entry
                    .entry((addr, *rtl_reg))
                    .and_modify(|e| {
                        if *mreg < *e {
                            *e = *mreg;
                        }
                    })
                    .or_insert(*mreg);
            }
        }
    }
    rtl_to_mreg_at_entry
}

#[derive(Clone, Copy)]
enum CallTypeEvidence {
    Bottom,
    Type(XType),
    Poison,
}

impl CallTypeEvidence {
    fn join(self, other: Self) -> Self {
        use CallTypeEvidence::*;
        match (self, other) {
            (Poison, _) | (_, Poison) => Poison,
            (Bottom, value) | (value, Bottom) => value,
            (Type(left), Type(right)) => {
                let lc = InterfaceClass::from_xtype(&left);
                let rc = InterfaceClass::from_xtype(&right);
                if lc == rc {
                    Type(
                        if (xtype_priority(&left), left) >= (xtype_priority(&right), right) {
                            left
                        } else {
                            right
                        },
                    )
                } else {
                    match (lc, rc) {
                        (InterfaceClass::Int, InterfaceClass::Float)
                        | (InterfaceClass::Float, InterfaceClass::Int) => Type(XType::Xfloat),
                        (InterfaceClass::Int | InterfaceClass::Float, pointer)
                        | (pointer, InterfaceClass::Int | InterfaceClass::Float)
                            if matches!(
                                pointer,
                                InterfaceClass::PtrInt
                                    | InterfaceClass::PtrFloat
                                    | InterfaceClass::PtrStruct(_)
                            ) =>
                        {
                            Type(XType::Xlong)
                        }
                        (InterfaceClass::PtrFunc, _) | (_, InterfaceClass::PtrFunc) => Poison,
                        (left, right)
                            if matches!(
                                left,
                                InterfaceClass::PtrInt
                                    | InterfaceClass::PtrFloat
                                    | InterfaceClass::PtrStruct(_)
                            ) && matches!(
                                right,
                                InterfaceClass::PtrInt
                                    | InterfaceClass::PtrFloat
                                    | InterfaceClass::PtrStruct(_)
                            ) =>
                        {
                            Type(XType::Xptr)
                        }
                        _ => Poison,
                    }
                }
            }
        }
    }
}

fn expr_annotation(expr: &ClightExpr) -> &ClightType {
    match expr {
        ClightExpr::EconstInt(_, ty)
        | ClightExpr::EconstFloat(_, ty)
        | ClightExpr::EconstSingle(_, ty)
        | ClightExpr::EconstLong(_, ty)
        | ClightExpr::Evar(_, ty)
        | ClightExpr::EvarSymbol(_, ty)
        | ClightExpr::Etempvar(_, ty)
        | ClightExpr::Ederef(_, ty)
        | ClightExpr::Eaddrof(_, ty)
        | ClightExpr::Eunop(_, _, ty)
        | ClightExpr::Ebinop(_, _, _, ty)
        | ClightExpr::Ecast(_, ty)
        | ClightExpr::Efield(_, _, ty)
        | ClightExpr::Esizeof(_, ty)
        | ClightExpr::Ealignof(_, ty)
        | ClightExpr::Econdition(_, _, _, ty) => ty,
    }
}

fn call_evidence_of_expr(expr: &ClightExpr) -> CallTypeEvidence {
    match expr {
        ClightExpr::EconstInt(0, _) | ClightExpr::EconstLong(0, _) => CallTypeEvidence::Bottom,
        _ => CallTypeEvidence::Type(representative_xtype_for_clight(expr_annotation(expr))),
    }
}

fn direct_callee_name(expr: &ClightExpr, ident_names: &BTreeMap<Ident, String>) -> Option<String> {
    match expr {
        ClightExpr::EvarSymbol(name, _) => Some(
            crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(name),
        ),
        ClightExpr::Evar(ident, _) => ident_names.get(ident).cloned(),
        ClightExpr::Eaddrof(inner, _) | ClightExpr::Ecast(inner, _) => {
            direct_callee_name(inner, ident_names)
        }
        _ => None,
    }
}

fn collect_call_evidence_expr(
    expr: &ClightExpr,
    ident_names: &BTreeMap<Ident, String>,
    out: &mut BTreeMap<String, Vec<Vec<CallTypeEvidence>>>,
) {
    match expr {
        ClightExpr::Ederef(inner, _)
        | ClightExpr::Eaddrof(inner, _)
        | ClightExpr::Eunop(_, inner, _)
        | ClightExpr::Ecast(inner, _)
        | ClightExpr::Efield(inner, _, _) => collect_call_evidence_expr(inner, ident_names, out),
        ClightExpr::Ebinop(_, left, right, _) => {
            collect_call_evidence_expr(left, ident_names, out);
            collect_call_evidence_expr(right, ident_names, out);
        }
        ClightExpr::Econdition(condition, yes, no, _) => {
            collect_call_evidence_expr(condition, ident_names, out);
            collect_call_evidence_expr(yes, ident_names, out);
            collect_call_evidence_expr(no, ident_names, out);
        }
        _ => {}
    }
}

fn collect_call_evidence_stmt(
    stmt: &ClightStmt,
    ident_names: &BTreeMap<Ident, String>,
    out: &mut BTreeMap<String, Vec<Vec<CallTypeEvidence>>>,
) {
    match stmt {
        ClightStmt::Sassign(left, right) => {
            collect_call_evidence_expr(left, ident_names, out);
            collect_call_evidence_expr(right, ident_names, out);
        }
        ClightStmt::Sset(_, expr) | ClightStmt::Sreturn(Some(expr)) => {
            collect_call_evidence_expr(expr, ident_names, out)
        }
        ClightStmt::Scall(_, callee, args) => {
            if let Some(name) = direct_callee_name(callee, ident_names) {
                out.entry(name)
                    .or_default()
                    .push(args.iter().map(call_evidence_of_expr).collect());
            }
            collect_call_evidence_expr(callee, ident_names, out);
            for arg in args {
                collect_call_evidence_expr(arg, ident_names, out);
            }
        }
        ClightStmt::Sbuiltin(_, _, _, args) => {
            for arg in args {
                collect_call_evidence_expr(arg, ident_names, out);
            }
        }
        ClightStmt::Ssequence(stmts) => {
            for stmt in stmts {
                collect_call_evidence_stmt(stmt, ident_names, out);
            }
        }
        ClightStmt::Sifthenelse(condition, yes, no) => {
            collect_call_evidence_expr(condition, ident_names, out);
            collect_call_evidence_stmt(yes, ident_names, out);
            collect_call_evidence_stmt(no, ident_names, out);
        }
        ClightStmt::Sloop(body, increment) => {
            collect_call_evidence_stmt(body, ident_names, out);
            collect_call_evidence_stmt(increment, ident_names, out);
        }
        ClightStmt::Sswitch(expr, cases) => {
            collect_call_evidence_expr(expr, ident_names, out);
            for (_, stmt) in cases {
                collect_call_evidence_stmt(stmt, ident_names, out);
            }
        }
        ClightStmt::Slabel(_, stmt) => collect_call_evidence_stmt(stmt, ident_names, out),
        _ => {}
    }
}

/// Construct the single program-level interface authority.  All evidence is
/// resolved here, once, in the order extern ABI > definition-side void >
/// reconciled internal signature.  Called-only fallback signatures are added
/// below after the relation-backed authorities have been collected.
pub(crate) fn extract_committed_interfaces(
    db: &DecompileDB,
    param_xtypes: &HashMap<(Address, RTLReg), XType>,
    rtl_to_mreg_at_entry: &HashMap<(Address, RTLReg), Mreg>,
) -> CommittedInterfaces {
    let mut callee_sigs: HashMap<Ident, CalleeSignature> = HashMap::new();
    let mut extern_idents = BTreeSet::new();

    // Pre-build symbol-to-idents map for O(1) lookup
    let mut symbol_to_idents: HashMap<Symbol, Vec<Ident>> = HashMap::new();
    for (id, sym) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
        symbol_to_idents.entry(*sym).or_default().push(*id);
    }

    // Varargs lookups built once. Internal functions: is_varargs_fn (mirrors signature_pass.rs) keyed by address. Extern callees: resolved_extern_signature carries no varargs bit, so join known_varargs_function by symbol name.
    let is_varargs_set: HashSet<Address> = db
        .rel_iter::<(Address,)>("is_varargs_fn")
        .map(|&(a,)| a)
        .collect();
    let known_varargs_syms: HashSet<Symbol> = db
        .rel_iter::<(Symbol, usize)>("known_varargs_function")
        .map(|&(name, _)| name)
        .collect();

    // resolved_extern_signature is multi-valued per symbol (one row per call-site signature); group and pick the lexicographically smallest tuple so the chosen signature is identical across runs regardless of Ascent set order.
    {
        let mut by_symbol: BTreeMap<Symbol, Vec<(usize, XType, Arc<Vec<XType>>)>> = BTreeMap::new();
        for (name, param_count, ret_type, param_types) in
            db.rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("resolved_extern_signature")
        {
            by_symbol.entry(*name).or_default().push((
                *param_count,
                *ret_type,
                param_types.clone(),
            ));
        }
        for (name, mut sigs) in by_symbol {
            sigs.sort();
            let (param_count, ret_type, param_types) = sigs.into_iter().next().unwrap();
            let is_varargs = known_varargs_syms.contains(&name);
            if let Some(idents) = symbol_to_idents.get(&name) {
                for &id in idents {
                    extern_idents.insert(id);
                    callee_sigs.insert(
                        id,
                        CalleeSignature {
                            param_count,
                            return_type: ret_type,
                            param_types: (*param_types).clone(),
                            is_varargs,
                        },
                    );
                }
            }
        }
    }

    // emit_function_param_count may be multi-valued; keep the smallest count per address and iterate in sorted address order for a deterministic result.
    let mut param_count_by_addr: BTreeMap<Address, usize> = BTreeMap::new();
    for &(addr, count) in db.rel_iter::<(Address, usize)>("emit_function_param_count") {
        param_count_by_addr
            .entry(addr)
            .and_modify(|c| *c = (*c).min(count))
            .or_insert(count);
    }
    for (addr, count) in param_count_by_addr {
        let ident = addr as Ident;
        if callee_sigs.contains_key(&ident) {
            continue;
        }
        // emit_function_param_type iteration order is non-deterministic and the relation is multi-valued per (addr, reg); take the deduped per-reg type from param_xtypes and order by calling-convention slot so param_types is positional and identical across runs.
        let mut typed: Vec<(RTLReg, XType)> = param_xtypes
            .iter()
            .filter(|((a, _), _)| *a == addr)
            .map(|((_, reg), xt)| (*reg, *xt))
            .collect();
        typed.sort_by(|x, y| {
            let kx = rtl_to_mreg_at_entry
                .get(&(addr, x.0))
                .map(|m| {
                    crate::decompile::analysis::signature_pass::param_mreg_sort_key(*m, db.abi())
                })
                .unwrap_or(usize::MAX);
            let ky = rtl_to_mreg_at_entry
                .get(&(addr, y.0))
                .map(|m| {
                    crate::decompile::analysis::signature_pass::param_mreg_sort_key(*m, db.abi())
                })
                .unwrap_or(usize::MAX);
            kx.cmp(&ky).then(x.0.cmp(&y.0))
        });
        let param_types: Vec<XType> = typed.into_iter().map(|(_, t)| t).collect();

        let definition_is_void = db
            .rel_iter::<(Address,)>("emit_function_void")
            .any(|&(candidate,)| candidate == addr);
        let ret_type = if definition_is_void {
            XType::Xvoid
        } else {
            best_reconciled_return_xtype(db, addr).unwrap_or(XType::Xvoid)
        };

        callee_sigs.insert(
            ident,
            CalleeSignature {
                param_count: count,
                return_type: ret_type,
                param_types,
                is_varargs: is_varargs_set.contains(&addr),
            },
        );
    }

    let definition_void: BTreeSet<Address> = db
        .rel_iter::<(Address,)>("emit_function_void")
        .map(|&(addr,)| addr)
        .collect();
    let internal_addrs: BTreeSet<Address> = db
        .rel_iter::<(Address, Symbol, Node)>("emit_function")
        .map(|&(addr, _, _)| addr)
        .collect();
    let external_addrs: BTreeSet<Address> = db
        .rel_iter::<(Address,)>("is_external_function")
        .map(|&(addr,)| addr)
        .collect();

    let mut committed = CommittedInterfaces::default();
    let mut sorted_sigs: Vec<_> = callee_sigs.into_iter().collect();
    sorted_sigs.sort_by_key(|(ident, _)| *ident);
    for (ident, signature) in sorted_sigs {
        let authority = if extern_idents.contains(&ident) {
            InterfaceAuthority::Extern
        } else if definition_void.contains(&(ident as Address)) {
            InterfaceAuthority::DefinitionVoid
        } else {
            InterfaceAuthority::Reconciled
        };
        committed.functions.insert(
            ident,
            CommittedFunctionInterface {
                signature,
                authority,
            },
        );
    }

    // Record the extern-precedence seam rather than silently assuming that an
    // ident carrying an extern spelling cannot also denote an emitted body.
    let mut symbol_rows: Vec<(Ident, String)> = db
        .rel_iter::<(Ident, Symbol)>("ident_to_symbol")
        .map(|(ident, name)| (*ident, (*name).to_string()))
        .collect();
    symbol_rows.sort();
    symbol_rows.dedup();
    for (ident, name) in &symbol_rows {
        if extern_idents.contains(ident)
            && internal_addrs.contains(&(*ident as Address))
            && !external_addrs.contains(&(*ident as Address))
        {
            committed
                .extern_internal_aliases
                .push((*ident, name.clone()));
        }
    }

    // Every spelling points to the same committed record.  Sanitized names
    // are the keys the C emitter uses; raw names remain useful for Clight's
    // EvarSymbol nodes and duplicate-name recovery.
    for (ident, raw_name) in &symbol_rows {
        let Some(iface) = committed.functions.get(ident).cloned() else {
            continue;
        };
        for name in [
            raw_name.clone(),
            crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(
                &raw_name,
            ),
        ] {
            match committed.by_name.entry(name) {
                std::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert(iface.clone());
                }
                std::collections::btree_map::Entry::Occupied(mut entry) => {
                    if iface.authority > entry.get().authority {
                        entry.insert(iface.clone());
                    }
                }
            }
        }
    }
    let mut emitted_names: Vec<(Address, String)> = db
        .rel_iter::<(Address, Symbol, Node)>("emit_function")
        .map(|(addr, name, _)| (*addr, (*name).to_string()))
        .collect();
    emitted_names.sort();
    emitted_names.dedup();
    for (addr, raw_name) in emitted_names {
        let Some(iface) = committed.functions.get(&(addr as Ident)).cloned() else {
            continue;
        };
        for name in [
            raw_name.clone(),
            crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(
                &raw_name,
            ),
        ] {
            committed
                .by_name
                .entry(name)
                .or_insert_with(|| iface.clone());
        }
    }

    // Curated extern declarations which were not observed at a resolved call
    // site still need a committed by-name prototype.  Do not attach them to an
    // internal ident here: only `resolved_extern_signature` has that mapping,
    // which preserves the audited extern-precedence boundary above.
    let known_varargs: BTreeSet<String> = db
        .rel_iter::<(Symbol, usize)>("known_varargs_function")
        .map(|(name, _)| {
            crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(name)
        })
        .collect();
    let mut known_by_name: BTreeMap<String, Vec<(usize, XType, Vec<XType>)>> = BTreeMap::new();
    for (name, count, ret, params) in
        db.rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("known_extern_signature")
    {
        let name =
            crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(name);
        known_by_name
            .entry(name)
            .or_default()
            .push((*count, *ret, params.as_ref().clone()));
    }
    for (name, mut candidates) in known_by_name {
        candidates.sort();
        let (param_count, return_type, param_types) = candidates.remove(0);
        let iface = CommittedFunctionInterface {
            signature: CalleeSignature {
                param_count,
                return_type,
                param_types,
                is_varargs: known_varargs.contains(&name),
            },
            authority: InterfaceAuthority::Extern,
        };
        match committed.by_name.entry(name) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(iface);
            }
            std::collections::btree_map::Entry::Occupied(mut entry) => {
                if iface.authority > entry.get().authority {
                    entry.insert(iface);
                }
            }
        }
    }

    // Definition-independent fallback for called-only functions.  The old
    // emitter performed this join after C conversion, creating a second
    // prototype authority.  Here the same conservative lattice is evaluated
    // over Clight annotations and committed exactly once.
    let mut ident_names = BTreeMap::new();
    for (ident, raw_name) in &symbol_rows {
        let sanitized =
            crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(
                raw_name,
            );
        ident_names
            .entry(*ident)
            .and_modify(|current: &mut String| {
                if sanitized < *current {
                    *current = sanitized.clone();
                }
            })
            .or_insert(sanitized);
    }
    let mut call_sites: BTreeMap<String, Vec<Vec<CallTypeEvidence>>> = BTreeMap::new();
    let mut statements: Vec<(Address, Node, ClightStmt)> = db
        .rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt")
        .map(|(address, node, stmt)| (*address, *node, stmt.clone()))
        .collect();
    statements.sort_by_cached_key(|(address, node, stmt)| (*address, *node, format!("{stmt:?}")));
    for (_, _, stmt) in &statements {
        collect_call_evidence_stmt(stmt, &ident_names, &mut call_sites);
    }

    let mut recovered_return_by_name = BTreeMap::new();
    let mut recovered_return_by_addr: BTreeMap<Address, XType> = BTreeMap::new();
    for (address, xtype) in db.rel_iter::<(Address, XType)>("emit_function_return_type_xtype") {
        recovered_return_by_addr
            .entry(*address)
            .and_modify(|current| {
                if (xtype_priority(xtype), *xtype) > (xtype_priority(current), *current) {
                    *current = *xtype;
                }
            })
            .or_insert(*xtype);
    }
    for (address, name, _) in db.rel_iter::<(Address, Symbol, Node)>("emit_function") {
        if let Some(xtype) = recovered_return_by_addr.get(address) {
            recovered_return_by_name.insert(
                crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(
                    name,
                ),
                *xtype,
            );
        }
    }
    for (name, sites) in call_sites {
        if committed.by_name.contains_key(&name) || sites.is_empty() {
            continue;
        }
        let arity = sites[0].len();
        if sites.iter().any(|site| site.len() != arity) {
            continue;
        }
        let mut joined = vec![CallTypeEvidence::Bottom; arity];
        for site in sites {
            for (slot, evidence) in joined.iter_mut().zip(site) {
                *slot = slot.join(evidence);
            }
        }
        let mut param_types = Vec::with_capacity(arity);
        let mut valid = true;
        for evidence in joined {
            match evidence {
                CallTypeEvidence::Bottom => param_types.push(XType::Xlong),
                CallTypeEvidence::Type(xtype) => param_types.push(xtype),
                CallTypeEvidence::Poison => {
                    valid = false;
                    break;
                }
            }
        }
        if !valid {
            continue;
        }
        let iface = CommittedFunctionInterface {
            signature: CalleeSignature {
                param_count: arity,
                return_type: recovered_return_by_name
                    .get(&name)
                    .copied()
                    .unwrap_or(XType::Xint),
                param_types,
                is_varargs: known_varargs.contains(&name),
            },
            authority: InterfaceAuthority::CallSite,
        };
        committed.by_name.insert(name.clone(), iface.clone());
        for (ident, mapped_name) in &ident_names {
            if mapped_name == &name {
                committed
                    .functions
                    .entry(*ident)
                    .or_insert_with(|| iface.clone());
            }
        }
    }

    let known_globals = extract_known_global_types(db);
    for (&ident, ty) in &known_globals.by_ident {
        committed
            .globals
            .insert(ident, representative_xtype_for_clight(ty));
    }
    committed.hard_globals = known_globals.hard_idents;

    committed
}

fn ranked_interface_domain(rank0: XType, mut candidates: Vec<XType>) -> Vec<InterfaceAlternative> {
    candidates.sort_by(|a, b| {
        xtype_priority(b)
            .cmp(&xtype_priority(a))
            .then_with(|| a.cmp(b))
    });
    candidates.insert(0, rank0);
    let mut seen = BTreeSet::new();
    let mut domain = Vec::new();
    for xtype in candidates {
        let class = InterfaceClass::from_xtype(&xtype);
        if seen.insert(class) {
            domain.push(InterfaceAlternative { class, xtype });
            if domain.len() == CONFIG.interface.alt_cap {
                break;
            }
        }
    }
    domain
}

fn param_type_xtype(param: &ParamType) -> XType {
    match param {
        ParamType::Pointer => XType::Xptr,
        ParamType::StructPointer(sid) => XType::XstructPtr(*sid),
        ParamType::Typed(xtype) => *xtype,
        ParamType::Integer | ParamType::Unknown => XType::Xint,
    }
}

/// Extract stable, class-deduplicated interface domains without changing any
/// selection.  The reconciliation result is always rank zero; raw union facts
/// contribute alternatives only.
fn extract_interface_vars(
    db: &DecompileDB,
    functions: &[FunctionData],
    committed: &CommittedInterfaces,
    known_globals: &KnownGlobalTypes,
) -> InterfaceVars {
    let mut raw_params: BTreeMap<(Address, usize), Vec<XType>> = BTreeMap::new();
    for (address, position, xtype) in
        db.rel_iter::<(Address, usize, XType)>("func_param_position_type")
    {
        raw_params
            .entry((*address, *position))
            .or_default()
            .push(*xtype);
    }
    let mut raw_returns: BTreeMap<Address, Vec<XType>> = BTreeMap::new();
    for (address, xtype) in
        db.rel_iter::<(Address, XType)>("emit_function_return_type_xtype_candidate")
    {
        raw_returns.entry(*address).or_default().push(*xtype);
    }

    let mut vars = Vec::new();
    for func in functions {
        let Some(sig) = committed.function(func.address as Ident) else {
            continue;
        };
        let fixed_count = sig
            .param_count
            .min(func.param_regs.len())
            .min(sig.param_types.len());
        for position in 0..fixed_count {
            let rank0 = sig
                .param_types
                .get(position)
                .copied()
                .or_else(|| func.param_types.get(position).map(param_type_xtype));
            let Some(rank0) = rank0 else { continue };
            let mut candidates = raw_params
                .get(&(func.address, position))
                .cloned()
                .unwrap_or_default();
            // The per-function selector can refine a parameter to a recovered
            // struct class through reg_struct_ids even when the positional
            // signature relation still carries only `Xintptr`.  Carry those
            // generated classes into the interface domain so Stage B can
            // represent (and retain) Stage A's preference instead of making a
            // rank-0 no-op spuriously dirty.
            if let Some(&reg) = func.param_regs.get(position) {
                if let Some(reg_candidates) = func.var_type_candidates.get(&reg) {
                    candidates.extend(reg_candidates.iter().map(|candidate| {
                        InterfaceClass::from_candidate(*candidate).representative_xtype()
                    }));
                } else if let Some(candidate) = func.var_types.get(&reg) {
                    candidates
                        .push(InterfaceClass::from_candidate(*candidate).representative_xtype());
                }
            }
            let domain = ranked_interface_domain(rank0, candidates);
            vars.push(InterfaceVar {
                id: InterfaceVarId::Param {
                    function: func.address as Ident,
                    position,
                },
                domain,
                hard_rank0: committed
                    .functions
                    .get(&(func.address as Ident))
                    .is_some_and(|iface| iface.authority == InterfaceAuthority::Extern),
            });
        }
        vars.push(InterfaceVar {
            id: InterfaceVarId::Return {
                function: func.address as Ident,
            },
            domain: ranked_interface_domain(
                sig.return_type,
                raw_returns.get(&func.address).cloned().unwrap_or_default(),
            ),
            hard_rank0: committed
                .functions
                .get(&(func.address as Ident))
                .is_some_and(|iface| iface.authority == InterfaceAuthority::Extern),
        });
    }

    let ptr_globals: BTreeSet<Ident> = db
        .rel_iter::<(Ident,)>("emit_global_is_ptr")
        .map(|&(ident,)| ident)
        .collect();
    let char_ptr_globals: BTreeSet<Ident> = db
        .rel_iter::<(Ident,)>("emit_global_is_char_ptr")
        .map(|&(ident,)| ident)
        .collect();
    let mut ident_names = BTreeMap::new();
    for (ident, name) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
        let sanitized =
            crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(name);
        ident_names
            .entry(*ident)
            .and_modify(|current: &mut String| {
                if sanitized < *current {
                    *current = sanitized.clone();
                }
            })
            .or_insert(sanitized);
    }
    let mut call_sites = BTreeMap::new();
    for (_, _, stmt) in db.rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt") {
        collect_call_evidence_stmt(stmt, &ident_names, &mut call_sites);
    }
    let called_names: BTreeSet<String> = call_sites.into_keys().collect();
    let mut called_globals = BTreeSet::new();
    for (ident, name) in db.rel_iter::<(Address, Symbol)>("global_symbol") {
        let sanitized =
            crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(name);
        if called_names.contains(&sanitized) {
            called_globals.insert(*ident as Ident);
        }
    }
    for (&ident, name) in &ident_names {
        if called_names.contains(name)
            && (ptr_globals.contains(&ident)
                || char_ptr_globals.contains(&ident)
                || committed.globals.contains_key(&ident))
        {
            called_globals.insert(ident);
        }
    }
    let global_ids: BTreeSet<Ident> = committed
        .globals
        .keys()
        .copied()
        .chain(ptr_globals.iter().copied())
        .chain(char_ptr_globals.iter().copied())
        .chain(called_globals.iter().copied())
        .collect();
    for ident in global_ids {
        let rank0 = committed.globals.get(&ident).copied().unwrap_or_else(|| {
            if called_globals.contains(&ident) {
                XType::Xfuncptr
            } else if char_ptr_globals.contains(&ident) {
                XType::Xcharptr
            } else {
                XType::Xptr
            }
        });
        let mut evidence = Vec::new();
        if ptr_globals.contains(&ident) {
            evidence.push(XType::Xptr);
        }
        if char_ptr_globals.contains(&ident) {
            evidence.push(XType::Xcharptr);
        }
        if called_globals.contains(&ident) {
            evidence.push(XType::Xfuncptr);
        }
        vars.push(InterfaceVar {
            id: InterfaceVarId::Global { symbol: ident },
            domain: ranked_interface_domain(rank0, evidence),
            hard_rank0: known_globals.hard_idents.contains(&ident),
        });
    }
    vars.sort_by(|a, b| a.id.cmp(&b.id));

    // T0.1 seam audit: compare the per-function class sets for every numeric
    // RTLReg reused by more than one function.  No address/order heuristic is
    // involved; this is diagnostic value-instance accounting only.
    let mut reg_instances: BTreeMap<RTLReg, Vec<(Address, BTreeSet<InterfaceClass>)>> =
        BTreeMap::new();
    let mut instance_count = 0usize;
    for func in functions {
        let regs: BTreeSet<RTLReg> = func
            .used_regs
            .iter()
            .copied()
            .chain(func.param_regs.iter().copied())
            .collect();
        instance_count += regs.len();
        for reg in regs {
            let mut classes = BTreeSet::new();
            if let Some(candidates) = func.var_type_candidates.get(&reg) {
                classes.extend(
                    candidates
                        .iter()
                        .map(|candidate| InterfaceClass::from_candidate(*candidate)),
                );
            }
            if let Some(position) = func
                .param_regs
                .iter()
                .position(|candidate| *candidate == reg)
            {
                if let Some(param) = func.param_types.get(position) {
                    classes.insert(InterfaceClass::from_xtype(&param_type_xtype(param)));
                }
            }
            if classes.is_empty() {
                if let Some(candidate) = func.var_types.get(&reg) {
                    classes.insert(InterfaceClass::from_candidate(*candidate));
                }
            }
            reg_instances
                .entry(reg)
                .or_default()
                .push((func.address, classes));
        }
    }
    let aliased_registers = reg_instances
        .values()
        .filter(|instances| instances.len() > 1)
        .count();
    let conflicting_aliased_registers = reg_instances
        .values()
        .filter(|instances| {
            instances.len() > 1
                && instances
                    .iter()
                    .skip(1)
                    .any(|(_, classes)| classes != &instances[0].1)
        })
        .count();

    InterfaceVars {
        vars,
        diagnostics: InterfaceDiagnostics {
            register_instances: instance_count,
            aliased_registers,
            conflicting_aliased_registers,
            extern_internal_aliases: committed.extern_internal_aliases.len(),
        },
    }
}

/// Reconstruct Clight straight-line groups from their structural successor
/// edges.  Relation iteration order and numeric node order are deliberately
/// irrelevant: a group is accepted only when the supplied edges form one
/// unambiguous chain rooted at `head` and cover every member exactly once.
/// Any member claimed by multiple heads invalidates every involved group.
fn reconstruct_sseq_groups(
    memberships: &[(Node, Node)],
    edges: &[(Node, Node, Node)],
) -> HashMap<Node, Vec<Node>> {
    let mut members_by_head: HashMap<Node, HashSet<Node>> = HashMap::new();
    let mut heads_by_member: HashMap<Node, HashSet<Node>> = HashMap::new();
    for &(head, member) in memberships {
        members_by_head.entry(head).or_default().insert(member);
        heads_by_member.entry(member).or_default().insert(head);
    }

    let mut invalid_heads = HashSet::new();
    for heads in heads_by_member.values() {
        if heads.len() > 1 {
            invalid_heads.extend(heads.iter().copied());
        }
    }

    let mut edges_by_head: HashMap<Node, HashSet<(Node, Node)>> = HashMap::new();
    for &(head, from, to) in edges {
        edges_by_head.entry(head).or_default().insert((from, to));
    }

    let mut result = HashMap::new();
    for (head, members) in members_by_head {
        if invalid_heads.contains(&head) || !members.contains(&head) {
            continue;
        }

        let mut successor: HashMap<Node, Node> = HashMap::new();
        let mut indegree: HashMap<Node, usize> = HashMap::new();
        let mut valid = true;
        if let Some(group_edges) = edges_by_head.get(&head) {
            for &(from, to) in group_edges {
                if !members.contains(&from) || !members.contains(&to) {
                    valid = false;
                    break;
                }
                if let Some(previous) = successor.insert(from, to) {
                    if previous != to {
                        valid = false;
                        break;
                    }
                }
                *indegree.entry(to).or_insert(0) += 1;
            }
        }
        if !valid || indegree.get(&head).copied().unwrap_or(0) != 0 {
            continue;
        }
        if members
            .iter()
            .any(|member| *member != head && indegree.get(member).copied().unwrap_or(0) != 1)
        {
            continue;
        }

        let mut ordered = Vec::with_capacity(members.len());
        let mut visited = HashSet::new();
        let mut current = head;
        loop {
            if !visited.insert(current) {
                valid = false;
                break;
            }
            ordered.push(current);
            let Some(&next) = successor.get(&current) else {
                break;
            };
            current = next;
        }
        if valid && visited.len() == members.len() {
            result.insert(head, ordered);
        }
    }
    result
}

/// Functions that structurally own every supplied node.  Ownership itself is
/// computed by ClightPass's point-keyed Set lattice; this helper only
/// intersects the already-computed lattice values when attaching a compound
/// straight-line group to its function(s).
fn common_function_owners(
    owner_sets: &HashMap<Node, Set<Address>>,
    nodes: &[Node],
) -> BTreeSet<Address> {
    let Some(first) = nodes.first() else {
        return BTreeSet::new();
    };
    let Some(first_owners) = owner_sets.get(first) else {
        return BTreeSet::new();
    };
    let mut common = first_owners.0.clone();
    for node in &nodes[1..] {
        let Some(owners) = owner_sets.get(node) else {
            return BTreeSet::new();
        };
        common.retain(|addr| owners.0.contains(addr));
        if common.is_empty() {
            break;
        }
    }
    common
}

// Every statement candidate for a goto target must carry the target label.
// Candidate sources are heterogeneous: ordinary Clight statements arrive
// pre-labeled, while recovered escaped-memory effects are appended directly
// to emit_clight_stmt. Treating "one candidate is labeled" as a node-wide
// property leaves the latter candidate unlabelled, so loop assembly can strip
// the only semantic case body selected for a recovered switch arm.
fn label_target_candidates(stmts: &mut [ClightStmt], label: Ident) {
    for stmt in stmts {
        if !matches!(stmt, ClightStmt::Slabel(existing, _) if *existing == label) {
            *stmt = ClightStmt::Slabel(label, Box::new(stmt.clone()));
        }
    }
}

#[cfg(test)]
mod goto_target_candidate_tests {
    use super::*;

    #[test]
    fn mixed_candidates_are_labeled_individually() {
        let label = 0x1200;
        let already_labeled = ClightStmt::Slabel(label, Box::new(ClightStmt::Scontinue));
        let mut candidates = vec![already_labeled.clone(), ClightStmt::Scontinue];

        label_target_candidates(&mut candidates, label);

        assert_eq!(candidates[0], already_labeled);
        assert!(matches!(
            &candidates[1],
            ClightStmt::Slabel(actual, inner)
                if *actual == label && **inner == ClightStmt::Scontinue
        ));
    }
}

pub fn extract_functions(
    db: &DecompileDB,
) -> Result<
    (
        Vec<FunctionData>,
        HashMap<usize, String>,
        CommittedInterfaces,
        InterfaceVars,
    ),
    String,
> {
    let mut functions = Vec::new();
    let mut func_map: HashMap<Address, FunctionData> = HashMap::new();
    let param_xtypes = build_param_xtypes(db);
    let known_global_types = std::sync::Arc::new(extract_known_global_types(db));

    let mut id_to_name: HashMap<usize, String> = HashMap::new();
    for (id, name) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
        let name_str = name.to_string();
        id_to_name
            .entry(*id)
            .and_modify(|existing| {
                if name.len() < existing.len() {
                    *existing = name_str.clone();
                }
            })
            .or_insert_with(|| name_str);
    }
    // ELF symbols are authoritative: override ident_to_symbol entries.
    for (addr, name, _) in db.rel_iter::<(Address, Symbol, Symbol)>("symbols") {
        let id = *addr as usize;
        id_to_name.insert(id, name.to_string());
    }

    // emit_function_param iteration order is non-deterministic, so sort each function's params by the Mreg's calling-convention slot with the RTLReg as tiebreak for stable p0/p1 assignments.
    let rtl_to_mreg_at_entry = build_rtl_to_mreg_at_entry(db);
    let mut func_params: HashMap<Address, Vec<RTLReg>> = HashMap::new();
    for (addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param") {
        let params = func_params.entry(*addr).or_default();
        if !params.contains(reg) {
            params.push(*reg);
        }
    }
    for (addr, params) in func_params.iter_mut() {
        params.sort_by(|a, b| {
            let ka = rtl_to_mreg_at_entry
                .get(&(*addr, *a))
                .map(|m| {
                    crate::decompile::analysis::signature_pass::param_mreg_sort_key(*m, db.abi())
                })
                .unwrap_or(usize::MAX);
            let kb = rtl_to_mreg_at_entry
                .get(&(*addr, *b))
                .map(|m| {
                    crate::decompile::analysis::signature_pass::param_mreg_sort_key(*m, db.abi())
                })
                .unwrap_or(usize::MAX);
            ka.cmp(&kb).then_with(|| a.cmp(b))
        });
    }

    let mut var_is_struct: HashMap<(Address, RTLReg), usize> = HashMap::new();
    for (addr, reg, sid) in db.rel_iter::<(Address, RTLReg, usize)>("emit_var_is_struct") {
        var_is_struct.insert((*addr, *reg), *sid);
    }

    let mut param_struct_by_pos: HashMap<(Address, usize), usize> = HashMap::new();
    for (func_addr, pos, canonical_id) in
        db.rel_iter::<(Address, usize, usize)>("func_param_struct_type")
    {
        param_struct_by_pos.insert((*func_addr, *pos), *canonical_id);
    }

    let mut struct_canonical: HashMap<usize, usize> = HashMap::new();
    for (orig, canon) in db.rel_iter::<(usize, usize)>("struct_id_to_canonical") {
        struct_canonical.insert(*orig, *canon);
    }

    let mut param_is_pointer: HashSet<(Address, RTLReg)> = HashSet::new();
    for (addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_param_is_pointer") {
        param_is_pointer.insert((*addr, *reg));
    }

    let mut func_return: HashMap<Address, RTLReg> = HashMap::new();
    for (addr, reg) in db.rel_iter::<(Address, RTLReg)>("emit_function_return") {
        func_return.insert(*addr, *reg);
    }

    // Final statement ordering must start at Cshminor's active semantic entry,
    // not the raw machine entry retained in emit_function for ABI recovery.
    // In particular, RTL entry-nop collapse can retarget the entry directly to
    // a synthetic first expansion stage that raw instruction `next` bypasses.
    let semantic_entries: HashMap<Address, Node> = db
        .rel_iter::<(Address, Node)>("func_entry_node")
        .map(|&(func, entry)| (func, entry))
        .collect();

    for (addr, name, raw_entry_node) in db.rel_iter::<(Address, Symbol, Node)>("emit_function") {
        let ident = *addr as usize;
        let final_name = if name.starts_with("FUN_") {
            id_to_name
                .get(&ident)
                .cloned()
                .unwrap_or_else(|| name.to_string())
        } else {
            name.to_string()
        };

        let param_regs: Vec<RTLReg> = func_params.get(addr).cloned().unwrap_or_default();

        let param_types: Vec<ParamType> = param_regs
            .iter()
            .enumerate()
            .map(|(pos, reg)| {
                if let Some(xtype) = param_xtypes.get(&(*addr, *reg)) {
                    if !matches!(
                        xtype,
                        XType::Xptr
                            | XType::Xcharptr
                            | XType::Xcharptrptr
                            | XType::Xintptr
                            | XType::Xfloatptr
                            | XType::Xsingleptr
                            | XType::Xfuncptr
                            | XType::Xlong
                            | XType::Xlongunsigned
                            | XType::Xany64
                    ) {
                        return ParamType::Typed(*xtype);
                    }
                }
                if let Some(sid) = var_is_struct.get(&(*addr, *reg)) {
                    let canonical_id = struct_canonical.get(sid).copied().unwrap_or(*sid);
                    ParamType::StructPointer(canonical_id)
                } else if let Some(&canonical_id) = param_struct_by_pos.get(&(*addr, pos)) {
                    ParamType::StructPointer(canonical_id)
                } else if let Some(xtype) = param_xtypes.get(&(*addr, *reg)) {
                    ParamType::Typed(*xtype)
                } else if param_is_pointer.contains(&(*addr, *reg)) {
                    ParamType::Pointer
                } else {
                    ParamType::Integer
                }
            })
            .collect();

        let return_reg = func_return.get(addr).copied();

        let entry_node = semantic_entries
            .get(addr)
            .copied()
            .unwrap_or(*raw_entry_node);
        let mut func_data = FunctionData::new(
            *addr,
            final_name,
            param_regs,
            param_types,
            return_reg,
            0,
            entry_node,
            db.abi().pointer_size == 8,
        );
        func_data.known_global_types = known_global_types.clone();
        func_map.insert(*addr, func_data);
    }

    // This is the final Clight semantic-CFG ownership lattice, not the earlier
    // machine-block ownership relation.  External-call lifting intentionally
    // disconnects PLT resolver implementation nodes from recovered C bodies.
    let mut function_owners: HashMap<Node, Set<Address>> = HashMap::new();
    for fact in db.rel_lattice_iter::<(Node, Set<Address>)>("clight_function_owners") {
        let (node, owners) = &*fact;
        function_owners
            .entry(*node)
            .and_modify(|current| current.0.extend(owners.0.iter().copied()))
            .or_insert_with(|| owners.clone());
    }
    let mut targeted_nop_owners: HashMap<Node, BTreeSet<Address>> = HashMap::new();
    for (addr, node) in db.rel_iter::<(Address, Node)>("clight_targeted_nop_owner") {
        targeted_nop_owners.entry(*node).or_default().insert(*addr);
    }

    // Straight-line groups can legitimately lie in a shared tail.  Rebuild
    // them independently for every function in the intersection of their
    // nodes' structural owner sets.
    let mut sseq_memberships_by_func: HashMap<Address, Vec<(Node, Node)>> = HashMap::new();
    for (head, member) in db.rel_iter::<(Node, Node)>("emit_clight_sseq") {
        for func_addr in common_function_owners(&function_owners, &[*head, *member]) {
            if func_map.contains_key(&func_addr) {
                sseq_memberships_by_func
                    .entry(func_addr)
                    .or_default()
                    .push((*head, *member));
            }
        }
    }
    let mut sseq_edges_by_func: HashMap<Address, Vec<(Node, Node, Node)>> = HashMap::new();
    for (head, from, to) in db.rel_iter::<(Node, Node, Node)>("emit_clight_sseq_edge") {
        for func_addr in common_function_owners(&function_owners, &[*head, *from, *to]) {
            if func_map.contains_key(&func_addr) {
                sseq_edges_by_func
                    .entry(func_addr)
                    .or_default()
                    .push((*head, *from, *to));
            }
        }
    }
    for (func_addr, func) in func_map.iter_mut() {
        let memberships = sseq_memberships_by_func
            .get(func_addr)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let edges = sseq_edges_by_func
            .get(func_addr)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        for (head, members) in reconstruct_sseq_groups(memberships, edges) {
            func.sseq_groups.insert(head, members);
        }
    }

    let goto_targets: HashSet<(Address, Node)> = db
        .rel_iter::<(Address, Node)>("emit_goto_target")
        .map(|(addr, target)| (*addr, *target))
        .collect();

    for (addr, node, stmt) in db.rel_iter::<(Address, Node, ClightStmt)>("emit_clight_stmt") {
        let is_goto_target = goto_targets.contains(&(*addr, *node));
        if !is_nonempty_stmt(stmt) && !is_goto_target {
            continue;
        }
        let is_semantically_owned = function_owners
            .get(node)
            .is_some_and(|owners| owners.0.contains(addr));
        let is_owned_control_anchor = targeted_nop_owners
            .get(node)
            .is_some_and(|owners| owners.contains(addr));
        if !is_semantically_owned && !is_owned_control_anchor {
            continue;
        }
        if let Some(func) = func_map.get_mut(addr) {
            func.node_statements
                .entry(*node)
                .or_insert_with(Vec::new)
                .push(stmt.clone());
        }
    }
    // Vec index 0 is semantic (UNSAT-fallback candidate); sort to lex-smallest debug form so selection is identical across runs despite non-deterministic Ascent set order.
    for func in func_map.values_mut() {
        for stmts in func.node_statements.values_mut() {
            if stmts.len() > 1 {
                stmts.sort_by_cached_key(|s| format!("{:?}", s));
            }
        }
    }

    for (addr, target) in db.rel_iter::<(Address, Node)>("emit_goto_target") {
        let is_semantically_owned = function_owners
            .get(target)
            .is_some_and(|owners| owners.0.contains(addr));
        let is_owned_control_anchor = targeted_nop_owners
            .get(target)
            .is_some_and(|owners| owners.contains(addr));
        if !is_semantically_owned && !is_owned_control_anchor {
            continue;
        }
        if let Some(func) = func_map.get_mut(addr) {
            let label = ident_from_node(*target);
            if let Some(stmts) = func.node_statements.get_mut(target) {
                label_target_candidates(stmts, label);
            } else {
                func.node_statements
                    .entry(*target)
                    .or_insert_with(Vec::new)
                    .push(ClightStmt::Slabel(label, Box::new(ClightStmt::Sskip)));
            }
        }
    }

    for (from_node, to_node) in db.rel_iter::<(Node, Node)>("emit_next") {
        let mut owners = function_owners
            .get(from_node)
            .map(|set| set.0.clone())
            .unwrap_or_default();
        if let Some(anchor_owners) = targeted_nop_owners.get(from_node) {
            owners.extend(anchor_owners.iter().copied());
        }
        for func_addr in owners {
            if let Some(func) = func_map.get_mut(&func_addr) {
                func.successors
                    .entry(*from_node)
                    .or_insert_with(Vec::new)
                    .push(*to_node);
            }
        }
    }
    // Sort successor lists for determinism (emit_next iteration order from parallel Ascent evaluation is not guaranteed).
    for func in func_map.values_mut() {
        for succs in func.successors.values_mut() {
            succs.sort();
            succs.dedup();
        }
    }

    for (addr, reg) in db.rel_iter::<(Address, RTLReg)>("rtl_reg_used_in_func") {
        if let Some(func) = func_map.get_mut(addr) {
            func.used_regs.insert(*reg);
        }
    }

    // Also collect registers from Clight statements, since variable coalescing can produce IDs differing from rtl_reg_used_in_func, causing missed type candidates.
    for func in func_map.values_mut() {
        let mut clight_regs: Vec<RTLReg> = Vec::new();
        for stmts in func.node_statements.values() {
            for stmt in stmts {
                clight_regs.extend(collect_stmt_regs(stmt));
            }
        }
        for reg in clight_regs {
            func.used_regs.insert(reg);
        }
    }

    let must_pointer_regs: HashSet<RTLReg> = db
        .rel_iter::<(RTLReg,)>("must_be_ptr")
        .map(|(reg,)| *reg)
        .collect();
    for func in func_map.values_mut() {
        func.must_pointer_regs.extend(
            func.used_regs
                .iter()
                .chain(func.param_regs.iter())
                .filter(|reg| must_pointer_regs.contains(reg))
                .copied(),
        );
    }

    for (addr, head, _) in db.rel_iter::<(Address, Node, Node)>("emit_loop_body") {
        if let Some(func) = func_map.get_mut(addr) {
            func.loop_headers.insert(*head);
        }
    }

    for (addr, head, _) in db.rel_iter::<(Address, Node, RTLReg)>("emit_switch_chain") {
        if let Some(func) = func_map.get_mut(addr) {
            func.switch_heads.insert(*head);
        }
    }

    for (addr, struct_id, fields) in
        db.rel_iter::<(Address, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>)>("emit_struct_fields")
    {
        if let Some(func) = func_map.get_mut(addr) {
            func.struct_fields.insert(*struct_id, fields.to_vec());
        }
    }

    // Collect all type candidates per register and pick the priority-based best; group first, since emit_var_type_candidate iteration order varies across runs, with a deterministic XType tiebreak.
    let mut reg_xtypes: HashMap<RTLReg, Vec<XType>> = HashMap::new();
    for (reg, xtype) in db.rel_iter::<(RTLReg, XType)>("emit_var_type_candidate") {
        reg_xtypes.entry(*reg).or_default().push(xtype.clone());
    }
    let mut reg_all_type_strs: HashMap<RTLReg, Vec<CandType>> = HashMap::new();
    let mut reg_best_xtype_val: HashMap<RTLReg, XType> = HashMap::new();
    for (reg, mut tys) in reg_xtypes {
        tys.sort();
        tys.dedup();
        let mut strs: Vec<CandType> = tys.iter().map(CandType::from_xtype).collect();
        strs.sort();
        strs.dedup();
        reg_all_type_strs.insert(reg, strs);

        let best = tys
            .iter()
            .max_by(|a, b| {
                xtype_priority(a)
                    .cmp(&xtype_priority(b))
                    .then_with(|| a.cmp(b))
            })
            .cloned()
            .expect("non-empty after grouping");
        let best_cand = CandType::from_xtype(&best);
        for func in func_map.values_mut() {
            if func.used_regs.contains(&reg) || func.param_regs.contains(&reg) {
                func.var_types.insert(reg, best_cand);
            }
        }
        reg_best_xtype_val.insert(reg, best);
    }

    // Upgrade param types from emit_var_type_candidate, but only FROM 64-bit generic placeholders, preserving narrow scalars and specific pointer types so XstructPtr cannot clobber main's argc.
    for func in func_map.values_mut() {
        for (i, reg) in func.param_regs.clone().iter().enumerate() {
            if let Some(best_xtype) = reg_best_xtype_val.get(reg) {
                let current = func.param_types.get(i);
                let should_upgrade = match (current, best_xtype) {
                    // Upgrade from 64-bit register-width placeholders (long/any64/ptr) to struct pointer.
                    (
                        Some(ParamType::Typed(
                            XType::Xlong | XType::Xlongunsigned | XType::Xany64 | XType::Xptr,
                        )),
                        XType::XstructPtr(sid),
                    ) => Some(ParamType::StructPointer(*sid)),
                    (Some(ParamType::Pointer), XType::XstructPtr(sid)) => {
                        Some(ParamType::StructPointer(*sid))
                    }
                    (Some(ParamType::Integer), XType::XstructPtr(sid)) => {
                        Some(ParamType::StructPointer(*sid))
                    }
                    // Upgrade Xlong (64-bit generic) to pointer when load analysis says it's a ptr. Xint stays Xint: int->ptr upgrade would clobber explicit `int argc` etc.
                    (
                        Some(ParamType::Typed(XType::Xlong)),
                        XType::Xptr | XType::Xcharptr | XType::Xintptr,
                    ) => Some(ParamType::Pointer),
                    _ => None,
                };
                if let Some(new_type) = should_upgrade {
                    if i < func.param_types.len() {
                        func.param_types[i] = new_type;
                    }
                }
            }
        }
    }

    // Populate reg_struct_ids BEFORE building candidates so ptr_struct_X candidates exist for struct-pointer regs; otherwise the selector falls back to ptr_int/ptr_char/ptr_void and emits `*(int *)p1` instead of `p1->ofs_0`.
    for (addr, reg, id) in db.rel_iter::<(Address, RTLReg, usize)>("reg_to_struct_id") {
        if let Some(func) = func_map.get_mut(addr) {
            let canonical_id = struct_canonical.get(id).copied().unwrap_or(*id);
            func.reg_struct_ids.insert(*reg, canonical_id);
        }
    }

    // Store all type candidates per register (sorted by priority, best first) and pad with same-size-class alternatives so clang_refine can search across ptr/int within the same width.
    for func in func_map.values_mut() {
        let all_regs: Vec<RTLReg> = func
            .used_regs
            .iter()
            .copied()
            .chain(func.param_regs.iter().copied())
            .collect();
        for reg in all_regs {
            let mut candidates: Vec<CandType> =
                reg_all_type_strs.get(&reg).cloned().unwrap_or_default();
            let mut push_once = |candidates: &mut Vec<CandType>, candidate: CandType| {
                if !candidates.contains(&candidate) {
                    candidates.push(candidate);
                }
            };

            // Add struct pointer candidate if this register is a known struct base
            if let Some(&sid) = func.reg_struct_ids.get(&reg) {
                push_once(&mut candidates, CandType::PtrStruct(sid));
            }

            // Determine size class from existing candidates; float registers keep only float types.
            // Classified through the candidate domain: the string tests here also looked for
            // `int_U32` / `int_U64`, so an unsigned-only register counted as neither width class
            // and picked up a spurious `int_I64` alternative below.
            let has_64 = candidates
                .iter()
                .any(|c| matches!(c, CandType::I64(_)) || c.is_pointer());
            let has_32 = candidates.iter().any(|c| matches!(c, CandType::I32(_)));
            let has_float = candidates.iter().any(|c| c.is_float());
            let has_ptr = candidates.iter().any(|c| c.is_pointer());

            if !has_float {
                if has_64 || (!has_32 && !has_float) {
                    // Always ensure int_I64 is available for 64-bit registers
                    push_once(&mut candidates, CandType::I64(Sign::Signed));
                    // Add pointer declaration alternatives only when the register has pointer evidence from the pipeline.
                    if has_ptr {
                        for alt in [CandType::PtrInt, CandType::PtrChar, CandType::PtrVoid] {
                            push_once(&mut candidates, alt);
                        }
                    }
                }
                if has_32 && !has_64 {
                    push_once(&mut candidates, CandType::I32(Sign::Signed));
                }
            }

            if candidates.len() > 1 {
                // Best first. The secondary key stays the SPELLING, not the enum discriminant, so
                // the order within a priority tier is the one the string sort produced.
                candidates.sort_by(|a, b| {
                    b.priority()
                        .cmp(&a.priority())
                        .then_with(|| a.label().cmp(&b.label()))
                });
                func.var_type_candidates.insert(reg, candidates);
            }
        }
    }

    // Selection-layer float/pointer brake: drop statement variants casting an assigned value to a bare float when the register carries a concrete non-float pointer candidate, since (double)ptr is never valid C.
    for func in func_map.values_mut() {
        let concrete_ptr_regs: std::collections::HashSet<RTLReg> = func
            .var_type_candidates
            .iter()
            .filter(|(_, cs)| cs.iter().any(|c| c.is_pointer() && !c.is_float_pointee()))
            .map(|(r, _)| *r)
            .collect();
        if concrete_ptr_regs.is_empty() {
            continue;
        }
        for stmts in func.node_statements.values_mut() {
            if stmts.len() <= 1 {
                continue;
            }
            let is_bad = |s: &ClightStmt| -> bool {
                let inner = match s {
                    ClightStmt::Slabel(_, b) => b.as_ref(),
                    other => other,
                };
                if let ClightStmt::Sset(id, rhs) = inner {
                    return concrete_ptr_regs.contains(&(*id as RTLReg))
                        && expr_casts_to_bare_float(rhs);
                }
                false
            };
            if stmts.iter().any(|s| !is_bad(s)) {
                stmts.retain(|s| !is_bad(s));
            }
        }
    }

    for (node, mreg, rtl_reg) in db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl") {
        if let Some(owners) = function_owners.get(node) {
            for func_addr in &owners.0 {
                if let Some(func) = func_map.get_mut(func_addr) {
                    func.reg_to_mreg.insert(*rtl_reg, *mreg);
                }
            }
        }
    }

    // Machine anchors and straight-line blocks for the flow theory. Built once
    // from relations the pipeline already maintains: the load/store chunk at
    // each node, the known external signatures, and the committed global types.
    build_flow_anchors(db, &mut func_map);

    // Machine register-class evidence, shared by the adequacy audit and the
    // class theory. Collected once and handed to every function by Arc.
    let class_evidence = std::sync::Arc::new(
        crate::decompile::passes::clight_select::adequacy::collect_class_evidence(db),
    );
    for func in func_map.values_mut() {
        func.class_evidence = class_evidence.clone();
    }

    // Behavioral evidence for the propagator selection engine: the signed vs
    // unsigned comparison each lifted Mcond performs. `mach_inst` is the
    // lifter's own output, so this is architecture-neutral and lands at the
    // address the lifter chose to host the condition -- for a compare-plus-
    // branch pair that is the COMPARE, which is where the multi-candidate
    // statement lives. Read only for the maximal-certification ablation, which
    // selects the propagator; the fixed production policy uses Optimize and no
    // other consumer wants the scan.
    if db.ablate_flow_max_certification {
        use crate::decompile::passes::clight_select::branch_theory::{
            condition_cmp_class, node_address, CmpClass,
        };
        let mut cond_class: HashMap<Address, CmpClass> = HashMap::new();
        for (addr, inst) in db.rel_iter::<(Address, MachInst)>("mach_inst") {
            if let MachInst::Mcond(cond, _, _) = inst {
                if let Some(class) = condition_cmp_class(cond) {
                    cond_class.insert(*addr, class);
                }
            }
        }
        for func in func_map.values_mut() {
            for node in func.node_statements.keys() {
                let addr = node_address(*node);
                if let Some(class) = cond_class.get(&addr) {
                    func.cond_branch_class.insert(addr, *class);
                }
            }
        }
        eprintln!(
            "[clight-select] ordering Mcond sites: {} program-wide, {} owned by recovered functions",
            cond_class.len(),
            func_map
                .values()
                .map(|f| f.cond_branch_class.len())
                .sum::<usize>()
        );
    }

    // Build the single committed signature authority, then hand the same map
    // to every per-function solve.
    let committed_interfaces =
        extract_committed_interfaces(db, &param_xtypes, &rtl_to_mreg_at_entry);
    {
        let callee_sigs = committed_interfaces.callee_signatures();
        for func in func_map.values_mut() {
            func.callee_signatures = callee_sigs.clone();
            if let Some(sig) = committed_interfaces.function(func.address as Ident) {
                func.return_type =
                    crate::decompile::passes::csh_pass::clight_type_from_xtype(&sig.return_type);
            }
        }
    }

    // TR-3: only 64-bit non-pointer scalar fields get a pointer alternative; narrower fields can't hold a pointer on LP64, and already-pointer fields need no re-selection. Keys mirror solve.rs::field_key_of_lvalue so candidate and evidence keys always agree.
    for func in func_map.values_mut() {
        let cands = collect_struct_field_type_candidates(
            func.node_statements.values().flat_map(|v| v.iter()),
        );
        if !cands.is_empty() {
            func.struct_field_type_candidates = cands;
        }
    }

    {
        let mut name_to_best_addr: HashMap<String, Address> = HashMap::new();
        for (addr, func) in func_map.iter() {
            let entry = name_to_best_addr.entry(func.name.clone());
            match entry {
                std::collections::hash_map::Entry::Vacant(e) => {
                    e.insert(*addr);
                }
                std::collections::hash_map::Entry::Occupied(mut e) => {
                    let existing_addr = *e.get();
                    let existing_count = func_map[&existing_addr].node_statements.len();
                    let new_count = func.node_statements.len();
                    // Tie-break on address: without it, equal-count name twins keep whichever HashMap iteration order placed first per run.
                    if new_count > existing_count
                        || (new_count == existing_count && *addr < existing_addr)
                    {
                        e.insert(*addr);
                    }
                }
            }
        }
        let keep_addrs: HashSet<Address> = name_to_best_addr.into_values().collect();
        func_map.retain(|addr, _| keep_addrs.contains(addr));
    }

    let mut addresses: Vec<_> = func_map.keys().copied().collect();
    addresses.sort();

    for addr in addresses {
        if let Some(func) = func_map.remove(&addr) {
            functions.push(func);
        }
    }

    let interface_vars = extract_interface_vars(
        db,
        &functions,
        &committed_interfaces,
        known_global_types.as_ref(),
    );

    Ok((functions, id_to_name, committed_interfaces, interface_vars))
}

fn is_valid_ascii_content(bytes: &[u8]) -> bool {
    if bytes.is_empty() {
        return false;
    }
    for &b in bytes {
        if b == 0 {
            return true;
        }
        let is_printable =
            (b >= 0x20 && b <= 0x7E) || b == b'\n' || b == b'\r' || b == b'\t' || b == 0x1b;
        if !is_printable {
            return false;
        }
    }
    true
}

// A section is "allocated" (gets a runtime address) when SHF_ALLOC is set for ELF; non-allocated sections (.comment, .note.*, .debug_*) live at sh_addr=0 and are never valid pointer targets. For non-ELF formats, fall back to a nonzero load address.
fn section_is_allocated(section: &object::Section) -> bool {
    match section.flags() {
        object::SectionFlags::Elf { sh_flags } => sh_flags & u64::from(object::elf::SHF_ALLOC) != 0,
        _ => section.address() != 0,
    }
}

// A section is writable when SHF_WRITE is set for ELF, else by the object crate's kind; a writable scalar global must keep its storage, while a read-only one may be inlined.
fn section_is_writable(section: &object::Section) -> bool {
    match section.flags() {
        object::SectionFlags::Elf { sh_flags } => sh_flags & u64::from(object::elf::SHF_WRITE) != 0,
        _ => matches!(section.kind(), object::SectionKind::Data),
    }
}

fn is_string_literal(bytes: &[u8]) -> Option<usize> {
    let null_pos = bytes.iter().position(|&b| b == 0)?;

    let str_bytes = &bytes[0..null_pos];

    if str_bytes.is_empty() {
        return None;
    }

    for &b in str_bytes {
        let is_printable =
            (b >= 0x20 && b <= 0x7E) || b == b'\n' || b == b'\r' || b == b'\t' || b >= 0x80;
        if !is_printable {
            return None;
        }
    }

    if str_bytes.iter().any(|&b| b >= 0x80) {
        if std::str::from_utf8(str_bytes).is_err() {
            return None;
        }
    }

    Some(null_pos + 1)
}

fn try_read_float32(remaining: &[u8]) -> Option<ScalarConstant> {
    if remaining.len() < 4 {
        return None;
    }
    let bytes: [u8; 4] = remaining[..4].try_into().ok()?;
    let val = f32::from_le_bytes(bytes);
    if val.is_finite() {
        Some(ScalarConstant::Float32(val))
    } else {
        None
    }
}

fn try_read_float64(remaining: &[u8]) -> Option<ScalarConstant> {
    if remaining.len() < 8 {
        return None;
    }
    let bytes: [u8; 8] = remaining[..8].try_into().ok()?;
    let val = f64::from_le_bytes(bytes);
    if val.is_finite() {
        Some(ScalarConstant::Float64(val))
    } else {
        None
    }
}

/// Resolve a scalar global's initial value from its section bytes, with a writable flag deciding between an initialized declaration and constant-folding; .bss resolves to None.
fn resolve_rodata_scalar(
    addr: u64,
    global_chunks: &HashMap<usize, MemoryChunk>,
    id: usize,
    data_ranges: &[(u64, u64, Vec<u8>, bool)],
    symbol_size_map: &HashMap<u64, u64>,
) -> Option<(ScalarConstant, bool)> {
    // Prefer the recorded load chunk, falling back to the ELF symbol size when none was recorded, or a .data scalar with an empty chunk row resolves to None and is emitted as zero.
    let chunk = match global_chunks.get(&id) {
        Some(c) => *c,
        None => match symbol_size_map.get(&addr).copied() {
            Some(1) => MemoryChunk::MInt8Signed,
            Some(2) => MemoryChunk::MInt16Signed,
            Some(4) => MemoryChunk::MInt32,
            Some(8) => MemoryChunk::MInt64,
            _ => return None,
        },
    };

    // Find the initialized-data section containing this address.
    let (sect_start, _sect_end, sect_data, writable) = data_ranges
        .iter()
        .find(|(start, end, _, _)| addr >= *start && addr < *end)?;
    let writable = *writable;

    let offset = (addr - sect_start) as usize;
    let remaining = &sect_data[offset..];

    let value = match chunk {
        MemoryChunk::MFloat32 => try_read_float32(remaining),
        // MFloat64 is authoritative and never falls back to f32: non-finite doubles fail the is_finite gate and would inline a bogus 0.0f; a failed read yields None so the global stays a symbol reference.
        MemoryChunk::MFloat64 => try_read_float64(remaining),
        // 1-byte scalars (bool / char). MBool decodes to 0/1; signed/unsigned int8 widen with the matching sign into the Int32 carrier (e.g. line_delim='\n'=10, verbose=true=1). Without these arms a 1-byte .data global falls to None and is emitted as BSS zero.
        MemoryChunk::MBool if !remaining.is_empty() => {
            Some(ScalarConstant::Int32((remaining[0] != 0) as i32))
        }
        MemoryChunk::MInt8Signed if !remaining.is_empty() => {
            Some(ScalarConstant::Int32(remaining[0] as i8 as i32))
        }
        MemoryChunk::MInt8Unsigned if !remaining.is_empty() => {
            Some(ScalarConstant::Int32(remaining[0] as i32))
        }
        // 2-byte scalars (short). Sign-extend / zero-extend into the Int32 carrier.
        MemoryChunk::MInt16Signed if remaining.len() >= 2 => {
            let bytes: [u8; 2] = remaining[..2].try_into().ok()?;
            Some(ScalarConstant::Int32(i16::from_le_bytes(bytes) as i32))
        }
        MemoryChunk::MInt16Unsigned if remaining.len() >= 2 => {
            let bytes: [u8; 2] = remaining[..2].try_into().ok()?;
            Some(ScalarConstant::Int32(u16::from_le_bytes(bytes) as i32))
        }
        MemoryChunk::MInt32 if remaining.len() >= 4 => {
            let bytes: [u8; 4] = remaining[..4].try_into().ok()?;
            let val = i32::from_le_bytes(bytes);
            Some(ScalarConstant::Int32(val))
        }
        MemoryChunk::MInt64 if remaining.len() >= 8 => {
            let bytes: [u8; 8] = remaining[..8].try_into().ok()?;
            let val = i64::from_le_bytes(bytes);
            Some(ScalarConstant::Int64(val))
        }
        _ => None,
    };
    value.map(|v| (v, writable))
}

pub fn extract_globals(db: &DecompileDB, binary_path: &Path) -> Result<Vec<GlobalData>, String> {
    let mut globals = Vec::new();

    // Globals can have several symbols at one address, so collect candidates and pick the lex-smallest name per id; HashMap::insert would pick a different alias each run and flip the type.
    let mut ident_name_candidates: HashMap<usize, Vec<String>> = HashMap::new();
    for (id, name) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
        ident_name_candidates
            .entry(*id)
            .or_default()
            .push(name.to_string());
    }
    let mut symbol_name_candidates: HashMap<usize, Vec<String>> = HashMap::new();
    for (addr, name, _) in db.rel_iter::<(Address, Symbol, Symbol)>("symbols") {
        symbol_name_candidates
            .entry(*addr as usize)
            .or_default()
            .push(name.to_string());
    }
    let mut id_to_name: HashMap<usize, String> = HashMap::new();
    for (id, mut names) in ident_name_candidates {
        names.sort();
        id_to_name.insert(id, names.into_iter().next().unwrap());
    }
    // ELF symbols are authoritative: override ident_to_symbol entries.
    for (id, mut names) in symbol_name_candidates {
        names.sort();
        id_to_name.insert(id, names.into_iter().next().unwrap());
    }

    let mut global_var_ids: Vec<usize> = db
        .rel_iter::<(usize,)>("global_var_ref")
        .map(|(id,)| *id)
        .collect();
    global_var_ids.sort_unstable();
    global_var_ids.dedup();

    let global_ptr_ids: std::collections::HashSet<usize> = db
        .rel_iter::<(Ident,)>("emit_global_is_ptr")
        .map(|(id,)| *id)
        .collect();

    let bin_data = fs::read(binary_path).map_err(|e| format!("Failed to read binary: {}", e))?;
    let obj_file =
        object::File::parse(&*bin_data).map_err(|e| format!("Failed to parse binary: {}", e))?;

    let func_addrs: HashSet<usize> = {
        let mut addrs = HashSet::new();
        for (addr, _, _) in db.rel_iter::<(Address, Symbol, Node)>("emit_function") {
            addrs.insert(*addr as usize);
        }
        for (addr,) in db.rel_iter::<(Address,)>("is_external_function") {
            addrs.insert(*addr as usize);
        }
        // Pre-build symbol-to-idents map for O(1) lookup
        let mut symbol_to_idents: HashMap<Symbol, Vec<Ident>> = HashMap::new();
        for (id, sym) in db.rel_iter::<(Ident, Symbol)>("ident_to_symbol") {
            symbol_to_idents.entry(*sym).or_default().push(*id);
        }
        for (name, _, _, _) in
            db.rel_iter::<(Symbol, usize, XType, Arc<Vec<XType>>)>("resolved_extern_signature")
        {
            if let Some(idents) = symbol_to_idents.get(name) {
                for &id in idents {
                    addrs.insert(id);
                }
            }
        }
        for (name,) in db.rel_iter::<(Symbol,)>("unknown_extern") {
            if let Some(idents) = symbol_to_idents.get(name) {
                for &id in idents {
                    addrs.insert(id);
                }
            }
        }
        // Every Text-kind ELF symbol address is code, never data: without this an address-taken skip-listed function is materialized as a bogus long in .bss and atexit jumps into data.
        for sym in obj_file.symbols() {
            if sym.kind() == SymbolKind::Text {
                addrs.insert(sym.address() as usize);
            }
        }
        addrs
    };

    // Build map of global load chunk types for rodata constant resolution. A literal in .rodata can be loaded with multiple chunks (e.g. as Float32 and Float64), so the relation carries several rows per id. Pick the smallest chunk by Ord so the resolved scalar value is stable across runs.
    let global_chunks: HashMap<usize, MemoryChunk> = {
        let mut groups: HashMap<usize, Vec<MemoryChunk>> = HashMap::new();
        for (id, chunk) in db.rel_iter::<(Ident, MemoryChunk)>("global_load_chunk") {
            groups.entry(*id).or_default().push(*chunk);
        }
        groups
            .into_iter()
            .map(|(id, mut chunks)| {
                chunks.sort();
                (id, chunks[0])
            })
            .collect()
    };

    // Width fallback for global_load_chunk: use the ELF symbol size when no chunk was recorded, keeping the smallest nonzero size per address; only power-of-two scalar data objects are admitted.
    let symbol_size_map: HashMap<u64, u64> = {
        let mut groups: HashMap<u64, Vec<u64>> = HashMap::new();
        for sym in obj_file.symbols() {
            if sym.kind() != SymbolKind::Data {
                continue;
            }
            let size = sym.size();
            if matches!(size, 1 | 2 | 4 | 8) {
                groups.entry(sym.address()).or_default().push(size);
            }
        }
        groups
            .into_iter()
            .map(|(addr, mut sizes)| {
                sizes.sort();
                (addr, sizes[0])
            })
            .collect()
    };

    // Initialized-data section ranges scanned for scalar globals, each tagged with writability, so non-zero .data scalars recover their file bytes; .bss is NOBITS and correctly stays zero.
    let data_ranges: Vec<(u64, u64, Vec<u8>, bool)> = obj_file
        .sections()
        .filter(|s| {
            matches!(
                s.kind(),
                object::SectionKind::ReadOnlyData
                    | object::SectionKind::ReadOnlyString
                    | object::SectionKind::Data
            )
        })
        .filter_map(|s| {
            let writable = section_is_writable(&s);
            // The end comes from the BYTES PRESENT, not from the section size: a PE .data section holding only zeros has VirtualSize > SizeOfRawData, and every reader below indexes `data` at an offset derived from this range, so a size-derived end reads out of bounds. An address past the file bytes has no initializer and correctly falls through to zero.
            s.data().ok().filter(|d| !d.is_empty()).map(|d| {
                (
                    s.address(),
                    s.address() + d.len() as u64,
                    d.to_vec(),
                    writable,
                )
            })
        })
        .collect();

    let string_data_map: HashMap<String, String> = db
        .rel_iter::<(String, String, usize)>("string_data")
        .map(|(label, content, _)| (label.clone(), content.clone()))
        .collect();
    let mut string_addr_map: Vec<(u64, String)> = Vec::new();
    for (label, content, _) in db.rel_iter::<(String, String, usize)>("string_data") {
        if let Some(hex) = label
            .strip_prefix("L_")
            .or_else(|| label.strip_prefix(".L_"))
        {
            if let Ok(addr) = u64::from_str_radix(hex, 16) {
                string_addr_map.push((addr, content.clone()));
            }
        }
    }
    string_addr_map.sort_by_key(|(addr, _)| *addr);

    // ELF relocation ground truth (slot_addr -> pointer target): both data and
    // code targets force is_pointer, suppress string detection on relocated
    // bytes, and drive initializer synthesis. Omitting code_pointer_in_data is
    // what turned a function table beginning with the addend 0xa8d0 into the
    // two-byte string "\xd0\xa8".
    let code_pointer_slots: BTreeSet<u64> = db
        .rel_iter::<(Address, Address)>("code_pointer_in_data")
        .map(|(slot, _)| *slot)
        .collect();
    let reloc_targets: BTreeMap<u64, u64> = db
        .rel_iter::<(Address, Address)>("pointer_in_data")
        .chain(db.rel_iter::<(Address, Address)>("code_pointer_in_data"))
        .map(|(slot, target)| (*slot, *target))
        .collect();
    let reloc_slots: Vec<u64> = reloc_targets.keys().copied().collect();

    // Keep every candidate because is_global_array is a set-valued relation.
    // Per global, recovery below tries the largest complete checked extent
    // first, then safely degrades through smaller layouts to the scalar base.
    let mut global_array_layouts: HashMap<usize, Vec<(usize, usize)>> = {
        let mut layouts: HashMap<usize, Vec<(usize, usize)>> = HashMap::new();
        for (ident, elem_size, count) in db.rel_iter::<(Ident, usize, usize)>("is_global_array") {
            layouts
                .entry(*ident)
                .or_default()
                .push((*elem_size, *count));
        }
        for candidates in layouts.values_mut() {
            candidates.sort_unstable();
            candidates.dedup();
        }
        layouts
    };

    // A run of adjacent pointer-width relocations to code is itself exact
    // object-layout evidence for a function-pointer table. This closes the
    // memory-indirect-call case where no ordinary global load publishes an
    // is_global_array row. Stop at a separately modeled global so two adjacent
    // scalar callback objects are never fused. A lone code pointer remains a
    // scalar.
    let object_starts: HashSet<u64> = global_var_ids.iter().map(|id| *id as u64).collect();
    for &id in &global_var_ids {
        let count = consecutive_pointer_run(
            id as u64,
            db.abi().pointer_size,
            &code_pointer_slots,
            &object_starts,
        );
        if count >= 2 {
            global_array_layouts
                .entry(id)
                .or_default()
                .push((db.abi().pointer_size, count));
        }
    }
    for layouts in global_array_layouts.values_mut() {
        layouts.sort_unstable();
        layouts.dedup();
    }

    // A Clight global ident may name an interior coordinate even when no
    // instruction directly mentions the object's base.  The base still owns
    // the storage and must receive the C declaration/initializer; otherwise a
    // later `base[index]` rewrite names an undeclared, zero-filled surrogate.
    // Admit an owner only when the producer supplied an exact array/struct
    // layout and the symbol name resolves to one unique owner id.
    let referenced_global_ids: HashSet<usize> = global_var_ids.iter().copied().collect();
    let mut recovered_owner_ids: HashSet<usize> = global_array_layouts.keys().copied().collect();
    recovered_owner_ids.extend(
        db.rel_iter::<(Ident, usize)>("global_storage_extent")
            .map(|(ident, _)| *ident),
    );
    let struct_catalog_ids: HashSet<usize> = db
        .rel_iter::<(u64, usize, usize, usize)>("global_struct_catalog")
        .map(|(_, id, _, _)| *id)
        .collect();
    recovered_owner_ids.extend(
        db.rel_iter::<(Ident, usize, Arc<Vec<(i64, Ident, MemoryChunk)>>)>(
            "emit_global_struct_fields",
        )
        .filter_map(|(ident, sid, _)| struct_catalog_ids.contains(sid).then_some(*ident)),
    );
    let mut owner_ids_by_symbol: HashMap<Symbol, BTreeSet<usize>> = HashMap::new();
    for (addr, _, name) in db.rel_iter::<(Address, usize, Symbol)>("symbol_size") {
        let ident = *addr as usize;
        if recovered_owner_ids.contains(&ident) {
            owner_ids_by_symbol.entry(*name).or_default().insert(ident);
        }
    }
    for (addr, name, _) in db.rel_iter::<(Address, Symbol, Symbol)>("symbols") {
        let ident = *addr as usize;
        if recovered_owner_ids.contains(&ident) {
            owner_ids_by_symbol.entry(*name).or_default().insert(ident);
        }
    }
    let mut target_coordinate_candidates: HashMap<u64, BTreeSet<(u64, i64)>> = HashMap::new();
    for (interior, owner_name, offset) in
        db.rel_iter::<(Ident, Symbol, i64)>("emit_address_as_offset")
    {
        if *offset <= 0 || !referenced_global_ids.contains(interior) {
            continue;
        }
        let Some(candidates) = owner_ids_by_symbol.get(owner_name) else {
            continue;
        };
        if candidates.len() == 1 {
            let owner = *candidates.first().unwrap();
            global_var_ids.push(owner);
            target_coordinate_candidates
                .entry(*interior as u64)
                .or_default()
                .insert((owner as u64, *offset));
        }
    }
    // A duplicated local-static spelling can map one interior coordinate to
    // several owners.  Such an address has no unambiguous C spelling and must
    // retain the conservative unrepresentable behavior below.
    let target_coordinates: HashMap<u64, RelocationTargetCoordinate> = target_coordinate_candidates
        .into_iter()
        .filter_map(|(target, coordinates)| {
            (coordinates.len() == 1).then(|| {
                let (owner, offset) = *coordinates.first().unwrap();
                (target, RelocationTargetCoordinate { owner, offset })
            })
        })
        .collect();
    global_var_ids.sort_unstable();
    global_var_ids.dedup();

    // A pointer initializer may name a higher-address anonymous global.  Walk
    // definitions in dependency order so that target has C declaration scope
    // when recovery validates and emits `&target`.
    global_var_ids = order_globals_for_pointer_initializers(
        &global_var_ids,
        &global_array_layouts,
        &reloc_targets,
        &target_coordinates,
    );

    // Address -> relocatable C name, for naming a pointer target that is
    // another global or a recovered function. Strings go through
    // string_addr_map. Function prototypes precede global definitions, so
    // function targets are in scope from the start.
    let addr_to_data_symbol: HashMap<u64, String> = {
        let mut m: HashMap<u64, String> = HashMap::new();
        for sym in obj_file.symbols() {
            if sym.kind() != SymbolKind::Data {
                continue;
            }
            let nm = sym.name().unwrap_or("");
            if nm.is_empty() {
                continue;
            }
            m.entry(sym.address())
                .and_modify(|e: &mut String| {
                    if nm < e.as_str() {
                        *e = nm.to_string();
                    }
                })
                .or_insert_with(|| nm.to_string());
        }
        // Some stripped data objects have a recovered relation name but no ELF
        // data symbol. They are still relocatable C targets because this same
        // extraction emits a declaration for every non-function global_var_ref.
        for &id in &global_var_ids {
            if func_addrs.contains(&id) {
                continue;
            }
            let name = id_to_name
                .get(&id)
                .cloned()
                .unwrap_or_else(|| format!("global_{}", id));
            m.entry(id as u64)
                .and_modify(|e: &mut String| {
                    if name.as_str() < e.as_str() {
                        *e = name.clone();
                    }
                })
                .or_insert(name);
        }
        for &id in &func_addrs {
            let name = id_to_name
                .get(&id)
                .cloned()
                .unwrap_or_else(|| format!("FUN_{id:x}"));
            m.entry(id as u64)
                .and_modify(|existing| {
                    if name.as_str() < existing.as_str() {
                        *existing = name.clone();
                    }
                })
                .or_insert(name);
        }
        m
    };

    // Read one target-width little-endian word stored at a data address
    // (pre-relocation file bytes).
    let read_pointer_word = |addr: u64, width: usize| -> Option<u64> {
        let width_u64 = u64::try_from(width).ok()?;
        let read_end = addr.checked_add(width_u64)?;
        let (start, _end, data, _w) = data_ranges
            .iter()
            .find(|(start, end, _, _)| addr >= *start && read_end <= *end)?;
        let off = (addr - start) as usize;
        match width {
            4 => Some(u32::from_le_bytes(data[off..off + 4].try_into().ok()?) as u64),
            8 => Some(u64::from_le_bytes(data[off..off + 8].try_into().ok()?)),
            _ => None,
        }
    };

    // Read the NUL-terminated C string at a data address from the section bytes; a bounded scan returning None on a non-printable byte, handling interior pointers into a larger literal.
    let read_cstr = |target: u64| -> Option<String> {
        let (start, end, data, _w) = data_ranges
            .iter()
            .find(|(start, end, _, _)| target >= *start && target < *end)?;
        let mut off = (target - start) as usize;
        let limit = ((*end - *start) as usize).min(off + 4096);
        let mut bytes = Vec::new();
        while off < limit {
            let b = data[off];
            if b == 0 {
                if bytes.is_empty() {
                    return None;
                }
                return Some(String::from_utf8_lossy(&bytes).into_owned());
            }
            let printable =
                (b >= 0x20 && b <= 0x7e) || b == b'\n' || b == b'\r' || b == b'\t' || b >= 0x80;
            if !printable {
                return None;
            }
            bytes.push(b);
            off += 1;
        }
        None
    };

    // Render only relocation-safe C targets: a literal string or the address of
    // a named data object that this translation unit can declare. Absolute
    // numeric addresses would become stale when the generated C is linked.
    let target_expr = |target: u64| -> Option<crate::decompile::passes::c_pass::types::CExpr> {
        use crate::decompile::passes::c_pass::types::{CExpr, StringLiteral, UnaryOp};
        if let Some(s) = read_cstr(target) {
            return Some(CExpr::StringLit(StringLiteral {
                value: s,
                is_wide: false,
            }));
        }
        if let Some(coordinate) = target_coordinates.get(&target) {
            let owner_name = addr_to_data_symbol.get(&coordinate.owner)?;
            // Machine offsets are byte coordinates.  Cast &owner to unsigned
            // char * before adding the offset so a later recovered array or
            // struct declaration cannot silently rescale it.
            return Some(relocation_target_coordinate_expr(owner_name, *coordinate));
        }
        if let Some(sym) = addr_to_data_symbol.get(&target) {
            return Some(CExpr::Unary(
                UnaryOp::AddrOf,
                Box::new(CExpr::Var(
                    crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(sym),
                )),
            ));
        }
        None
    };

    // Addresses with a recorded zero-length string_data anchor: positive evidence that a 0x00 byte is a real terminator, so an anonymous 0x00-leading float constant is not classified as "".
    let empty_string_addrs: std::collections::HashSet<u64> = string_addr_map
        .iter()
        .filter(|(_, content)| content.is_empty())
        .map(|(addr, _)| *addr)
        .collect();

    // Names that an earlier GlobalData entry will actually declare. This is a
    // C declaration-scope fact, not an address-based semantic inference.
    let mut named_globals_in_scope: HashSet<u64> = func_addrs.iter().map(|id| *id as u64).collect();

    for id in &global_var_ids {
        if func_addrs.contains(id) {
            continue;
        }
        let name = id_to_name
            .get(id)
            .cloned()
            .unwrap_or_else(|| format!("global_{}", id));

        let addr = *id as u64;
        let is_recovered_aggregate = recovered_owner_ids.contains(id);
        let mut is_string = false;
        let mut content = Vec::new();

        // Preserve an authoritative base relocation as a scalar initializer.
        // A validated is_global_array layout may also recover relocations in
        // interior words, but only when its complete initialized image is safe.
        let readable_bytes = data_ranges
            .iter()
            .find(|(start, end, _, _)| addr >= *start && addr < *end)
            .map(|(_, end, _, _)| *end - addr);
        let pointer_words = recover_relocated_pointer_words(
            addr,
            db.abi().pointer_size,
            global_array_layouts
                .get(id)
                .map(Vec::as_slice)
                .unwrap_or(&[]),
            readable_bytes,
            &reloc_targets,
            |target| {
                let declaration_target = relocation_declaration_target(target, &target_coordinates);
                relocation_target_is_representable(
                    declaration_target,
                    addr,
                    read_cstr(target).is_some(),
                    &addr_to_data_symbol,
                    &named_globals_in_scope,
                )
            },
            read_pointer_word,
        );
        let pointer_init: Vec<crate::decompile::passes::c_pass::types::CExpr> = pointer_words
            .into_iter()
            .map(|word| match word {
                RelocatedPointerWord::Target(target) => target_expr(target)
                    .expect("recovery admitted only relocation-safe pointer targets"),
                RelocatedPointerWord::Raw(raw) => {
                    use crate::decompile::passes::c_pass::types::{
                        CExpr, IntLiteral, IntLiteralBase, IntLiteralSuffix,
                    };
                    let value = match db.abi().pointer_size {
                        4 => raw as u32 as i32 as i128,
                        _ => raw as i64 as i128,
                    };
                    CExpr::IntLit(IntLiteral {
                        value,
                        suffix: IntLiteralSuffix::L,
                        base: IntLiteralBase::Decimal,
                    })
                }
            })
            .collect();

        // is_pointer from relocation ground truth or the access-derived signal.
        let is_pointer = !pointer_init.is_empty() || global_ptr_ids.contains(id);

        // Pointer globals are never string literals; skip all string detection for them.
        if !is_pointer && !is_recovered_aggregate {
            if let Some(str_content) = string_data_map.get(&name) {
                if is_valid_ascii_content(str_content.as_bytes()) {
                    is_string = true;
                    content = str_content.as_bytes().to_vec();
                    content.push(0);
                }
            }

            if !is_string {
                let idx = string_addr_map.partition_point(|(start, _)| *start <= addr);
                if idx > 0 {
                    let (start, str_content) = &string_addr_map[idx - 1];
                    let offset = (addr - start) as usize;
                    if offset == 0 {
                        let candidate = str_content.as_bytes();
                        if is_valid_ascii_content(candidate) {
                            is_string = true;
                            content = candidate.to_vec();
                            content.push(0);
                        }
                    } else if offset < str_content.len() {
                        let candidate = str_content[offset..].as_bytes();
                        if is_valid_ascii_content(candidate) {
                            is_string = true;
                            content = candidate.to_vec();
                            content.push(0);
                        }
                    }
                }
            }
        }

        // Try to resolve scalar constants from initialized-data sections before string detection, since float constants (e.g. 3.0f) start with 0x00 and would be misidentified as empty strings. The resolved value also reports whether it came from a writable (.data) or read-only (.rodata) section.
        let (scalar_value, scalar_writable) = if !is_string
            && !is_pointer
            && !is_recovered_aggregate
        {
            match resolve_rodata_scalar(addr, &global_chunks, *id, &data_ranges, &symbol_size_map) {
                Some((v, w)) => (Some(v), w),
                None => (None, false),
            }
        } else {
            (None, false)
        };

        // Pointer globals must never be classified as string literals: their file bytes are zero pre-relocation, so a leading 0x00 does not mean an empty string.
        if !is_string && scalar_value.is_none() && !is_pointer && !is_recovered_aggregate {
            for section in obj_file.sections() {
                // A global_var_ref id is a runtime address, which only SHF_ALLOC sections have; non-allocated metadata sections sit at sh_addr=0 and would render a constant as their bytes, so skip them.
                if !section_is_allocated(&section) {
                    continue;
                }
                let sect_addr = section.address();
                let sect_size = section.size();

                if addr >= sect_addr && addr < sect_addr + sect_size {
                    if let Ok(data) = section.data() {
                        let offset = (addr - sect_addr) as usize;
                        if offset < data.len() {
                            // Scan to NUL bounded by the section end, not a fixed window, or a >128-byte string is missed entirely; cheap on non-strings since is_string_literal bails at the first non-printable byte.
                            let remaining = &data[offset..];
                            // Relocation hardening: a pointer relocation inside a candidate string's byte span means those printable bytes are a relocated address, so refuse string classification.
                            let str_len = is_string_literal(remaining);
                            let reloc_in_span = match str_len {
                                Some(len) => {
                                    let lo = reloc_slots.partition_point(|&s| s < addr);
                                    reloc_slots
                                        .get(lo)
                                        .map_or(false, |&s| s < addr + len as u64)
                                }
                                None => false,
                            };
                            if let (Some(len), false) = (str_len, reloc_in_span) {
                                is_string = true;
                                content = remaining[0..len].to_vec();
                            } else if remaining[0] == 0
                                && !section_is_writable(&section)
                                && empty_string_addrs.contains(&addr)
                            {
                                // Empty string literal: a read-only 0x00-leading address that is also a recorded terminator anchor, the gate that keeps an anonymous 0x00-leading float constant from becoming "".
                                is_string = true;
                                content = vec![0u8];
                            }
                        }
                    }
                    break;
                }
            }
        }

        // Mirrors the emitter's early skip for inline strings and read-only
        // folded scalars. Other entries introduce a file-scope declaration;
        // stdio globals are already declared by the emitted headers.
        let introduces_named_declaration =
            !is_string && !(scalar_value.is_some() && !scalar_writable);

        globals.push(GlobalData {
            id: *id,
            name,
            is_string,
            content,
            is_pointer,
            scalar_value,
            scalar_writable,
            pointer_init,
        });
        if introduces_named_declaration {
            named_globals_in_scope.insert(addr);
        }
    }

    Ok(globals)
}

use crate::decompile::passes::c_pass::types::{
    CType, FloatSize, IntSize, Signedness, StructDef, StructField, TypeQualifiers,
};
use crate::x86::op::Condition;
use crate::x86::types::FieldType;
use std::sync::Arc;

#[derive(Debug, Clone)]
pub struct PrimaryExitData {
    #[allow(dead_code)]
    pub exit_node: Node,
    /// Where the loop's primary exit branch lands (the node OUTSIDE the body the break reaches), distinct from exit_node, the in-body condition node.
    pub exit_target: Option<Node>,
}

#[derive(Debug, Clone, Default)]
pub struct LoopInfo {
    pub body_nodes: Vec<Node>,
    pub primary_exit: Option<PrimaryExitData>,
    /// Exact outside-loop target for each non-primary conditional exit.  The
    /// guard itself must come from the statement chosen by clight_select: a
    /// separately materialized candidate can precede copy propagation or
    /// otherwise disagree with the solver's selected statement.
    pub exit_targets: HashMap<Node, Node>,
    /// Non-primary exits whose target flows to a function return (exit_node -> (value_node, ret_node)); select tail-duplicates value_node + ret_node's return into the exit branch instead of a valueless break (A5 dead-return-overwrite fix).
    pub exit_returns: HashMap<Node, (Node, Node)>,
}

// RB-5: pick deterministically among rows by ascending priority: fabricated-operand count, Tvoid-subexpr count, structural node count, then full structural order as a total tiebreak.

use std::cmp::Ordering;

/// Mreg discriminant fresh_xtl_reg packs when the backing Mreg is `Unknown` / "RTEMP"; taken from rtl_pass so the two decodings cannot drift.
use crate::decompile::passes::rtl_pass::MREG_UNKNOWN_DISCRIMINANT;

/// True for RTL register ids that do not carry a machine-register-backed value (DEFAULT_VAR sentinel or Unknown/RTEMP-backed temporaries).
fn is_fabricated_operand(reg: RTLReg) -> bool {
    if reg == crate::util::DEFAULT_VAR as RTLReg {
        return true;
    }
    // fresh_xtl_reg encoding: bit 63 | optional namespace bits | (node << MREG_DISCRIMINANT_BITS) | mreg id.
    (reg >> 63) == 1
        && ((reg & crate::decompile::passes::rtl_pass::MREG_DISCRIMINANT_MASK)
            == MREG_UNKNOWN_DISCRIMINANT
            // A register-indirect call with no reaching definition still has
            // a semantic PRE-call input pseudo.  Its low bits retain the
            // architectural register so distinct inputs do not collide, while
            // this namespace marks the unbound value as fabricated.  Once an
            // actual source aliases it, canonicalization replaces this id.
            || (reg & crate::decompile::passes::rtl_pass::FRESH_NS_CALL_INPUT) != 0)
}

#[cfg(test)]
mod fabricated_call_input_tests {
    use super::is_fabricated_operand;
    use crate::decompile::passes::rtl_pass::{fresh_call_input_reg, fresh_xtl_reg};
    use crate::mreg::Mreg;

    #[test]
    fn unresolved_call_input_namespace_is_fabricated() {
        let node = 0x1234;
        assert!(is_fabricated_operand(fresh_call_input_reg(node, Mreg::AX)));
        assert!(!is_fabricated_operand(fresh_xtl_reg(node, Mreg::AX)));
    }
}

/// (fabricated-operand count, structural node count) over a Csharpminor expr tree.
fn csharp_expr_stats(e: &CsharpminorExpr) -> (u32, u32) {
    match e {
        CsharpminorExpr::Evar(reg) => (is_fabricated_operand(*reg) as u32, 1),
        CsharpminorExpr::Eaddrof(_) | CsharpminorExpr::Econst(_) => (0, 1),
        CsharpminorExpr::Eunop(_, x) => {
            let (f, s) = csharp_expr_stats(x);
            (f, s + 1)
        }
        CsharpminorExpr::Ebinop(_, l, r) => {
            let (fl, sl) = csharp_expr_stats(l);
            let (fr, sr) = csharp_expr_stats(r);
            (fl + fr, sl + sr + 1)
        }
        CsharpminorExpr::Eload(_, x) => {
            let (f, s) = csharp_expr_stats(x);
            (f, s + 1)
        }
        CsharpminorExpr::Econdition(c, t, f_) => {
            let (fc, sc) = csharp_expr_stats(c);
            let (ft, st) = csharp_expr_stats(t);
            let (ff, sf) = csharp_expr_stats(f_);
            (fc + ft + ff, sc + st + sf + 1)
        }
    }
}

fn csharp_args_stats(args: &[CsharpminorExpr]) -> (u32, u32) {
    args.iter()
        .map(csharp_expr_stats)
        .fold((0, 0), |(fa, sa), (f, s)| (fa + f, sa + s))
}

/// (fabricated, void-typed, size) accumulated over a Clight expr tree.
fn clight_expr_stats(e: &ClightExpr, acc: &mut (u32, u32, u32)) {
    let node_ty = match e {
        ClightExpr::EconstInt(_, ty)
        | ClightExpr::EconstFloat(_, ty)
        | ClightExpr::EconstSingle(_, ty)
        | ClightExpr::EconstLong(_, ty)
        | ClightExpr::Evar(_, ty)
        | ClightExpr::EvarSymbol(_, ty)
        | ClightExpr::Etempvar(_, ty)
        | ClightExpr::Ederef(_, ty)
        | ClightExpr::Eaddrof(_, ty)
        | ClightExpr::Eunop(_, _, ty)
        | ClightExpr::Ebinop(_, _, _, ty)
        | ClightExpr::Ecast(_, ty)
        | ClightExpr::Efield(_, _, ty)
        | ClightExpr::Esizeof(_, ty)
        | ClightExpr::Ealignof(_, ty)
        | ClightExpr::Econdition(_, _, _, ty) => ty,
    };
    if matches!(node_ty, ClightType::Tvoid) {
        acc.1 += 1;
    }
    acc.2 += 1;
    match e {
        ClightExpr::Etempvar(id, _) => {
            if is_fabricated_operand(*id as RTLReg) {
                acc.0 += 1;
            }
        }
        ClightExpr::Ederef(x, _)
        | ClightExpr::Eaddrof(x, _)
        | ClightExpr::Eunop(_, x, _)
        | ClightExpr::Ecast(x, _)
        | ClightExpr::Efield(x, _, _) => clight_expr_stats(x, acc),
        ClightExpr::Ebinop(_, l, r, _) => {
            clight_expr_stats(l, acc);
            clight_expr_stats(r, acc);
        }
        ClightExpr::Econdition(c, t, f, _) => {
            clight_expr_stats(c, acc);
            clight_expr_stats(t, acc);
            clight_expr_stats(f, acc);
        }
        _ => {}
    }
}

/// (fabricated, void-typed, size) accumulated over a Clight stmt tree.
fn clight_stmt_stats(stmt: &ClightStmt, acc: &mut (u32, u32, u32)) {
    acc.2 += 1;
    match stmt {
        ClightStmt::Sskip | ClightStmt::Sbreak | ClightStmt::Scontinue | ClightStmt::Sgoto(_) => {}
        ClightStmt::Sassign(l, r) => {
            clight_expr_stats(l, acc);
            clight_expr_stats(r, acc);
        }
        ClightStmt::Sset(_, e) => clight_expr_stats(e, acc),
        ClightStmt::Scall(_, f, args) => {
            clight_expr_stats(f, acc);
            for a in args {
                clight_expr_stats(a, acc);
            }
        }
        ClightStmt::Sbuiltin(_, _, _, args) => {
            for a in args {
                clight_expr_stats(a, acc);
            }
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss {
                clight_stmt_stats(s, acc);
            }
        }
        ClightStmt::Sifthenelse(c, t, f) => {
            clight_expr_stats(c, acc);
            clight_stmt_stats(t, acc);
            clight_stmt_stats(f, acc);
        }
        ClightStmt::Sloop(b, s) => {
            clight_stmt_stats(b, acc);
            clight_stmt_stats(s, acc);
        }
        ClightStmt::Sreturn(e) => {
            if let Some(e) = e {
                clight_expr_stats(e, acc);
            }
        }
        ClightStmt::Sswitch(e, cases) => {
            clight_expr_stats(e, acc);
            for (_, s) in cases {
                clight_stmt_stats(s, acc);
            }
        }
        ClightStmt::Slabel(_, s) => clight_stmt_stats(s, acc),
    }
}

/// Length-first lexicographic order over slices with an element comparator.
fn cmp_slice<T>(a: &[T], b: &[T], f: impl Fn(&T, &T) -> Ordering) -> Ordering {
    a.len().cmp(&b.len()).then_with(|| {
        for (x, y) in a.iter().zip(b.iter()) {
            let o = f(x, y);
            if o != Ordering::Equal {
                return o;
            }
        }
        Ordering::Equal
    })
}

fn cmp_option<T>(a: &Option<T>, b: &Option<T>, f: impl Fn(&T, &T) -> Ordering) -> Ordering {
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (Some(x), Some(y)) => f(x, y),
    }
}

fn cmp_constant(a: &Constant, b: &Constant) -> Ordering {
    use Constant as C;
    let rank = |c: &C| -> u8 {
        match c {
            C::Ointconst(_) => 0,
            C::Ofloatconst(_) => 1,
            C::Osingleconst(_) => 2,
            C::Olongconst(_) => 3,
            C::Oaddrsymbol(_, _) => 4,
            C::Oaddrstack(_) => 5,
        }
    };
    rank(a).cmp(&rank(b)).then_with(|| match (a, b) {
        (C::Ointconst(x), C::Ointconst(y)) => x.cmp(y),
        (C::Ofloatconst(x), C::Ofloatconst(y)) => x.cmp(y), // F64: Ord via total_cmp
        (C::Osingleconst(x), C::Osingleconst(y)) => x.cmp(y), // F32: Ord via total_cmp
        (C::Olongconst(x), C::Olongconst(y)) => x.cmp(y),
        (C::Oaddrsymbol(ia, oa), C::Oaddrsymbol(ib, ob)) => ia.cmp(ib).then(oa.cmp(ob)),
        (C::Oaddrstack(x), C::Oaddrstack(y)) => x.cmp(y),
        _ => Ordering::Equal, // unreachable: equal ranks imply the same variant
    })
}

/// Total order key for CminorBinop: (variant rank, comparison payload).
fn cminor_binop_key(op: &CminorBinop) -> (u8, u8) {
    use CminorBinop as B;
    match op {
        B::Oadd => (0, 0),
        B::Osub => (1, 0),
        B::Omul => (2, 0),
        B::Odiv => (3, 0),
        B::Odivu => (4, 0),
        B::Omod => (5, 0),
        B::Omodu => (6, 0),
        B::Oand => (7, 0),
        B::Oor => (8, 0),
        B::Oxor => (9, 0),
        B::Oshl => (10, 0),
        B::Oshr => (11, 0),
        B::Oshru => (12, 0),
        B::Oaddf => (13, 0),
        B::Osubf => (14, 0),
        B::Omulf => (15, 0),
        B::Odivf => (16, 0),
        B::Oaddfs => (17, 0),
        B::Osubfs => (18, 0),
        B::Omulfs => (19, 0),
        B::Odivfs => (20, 0),
        B::Omaxf => (21, 0),
        B::Ominf => (22, 0),
        B::Oaddl => (23, 0),
        B::Osubl => (24, 0),
        B::Omull => (25, 0),
        B::Odivl => (26, 0),
        B::Odivlu => (27, 0),
        B::Omodl => (28, 0),
        B::Omodlu => (29, 0),
        B::Oandl => (30, 0),
        B::Oorl => (31, 0),
        B::Oxorl => (32, 0),
        B::Oshll => (33, 0),
        B::Oshrl => (34, 0),
        B::Oshrlu => (35, 0),
        B::Omulhs => (36, 0),
        B::Omulhu => (37, 0),
        B::Omullhs => (38, 0),
        B::Omullhu => (39, 0),
        B::Ocmp(c) => (40, *c as u8),
        B::Ocmpu(c) => (41, *c as u8),
        B::Ocmpf(c) => (42, *c as u8),
        B::Ocmpnotf(c) => (43, *c as u8),
        B::Ocmpfs(c) => (44, *c as u8),
        B::Ocmpnotfs(c) => (45, *c as u8),
        B::Ocmpl(c) => (46, *c as u8),
        B::Ocmplu(c) => (47, *c as u8),
    }
}

fn cmp_csharp_expr(a: &CsharpminorExpr, b: &CsharpminorExpr) -> Ordering {
    use CsharpminorExpr as E;
    let rank = |e: &E| -> u8 {
        match e {
            E::Evar(_) => 0,
            E::Eaddrof(_) => 1,
            E::Econst(_) => 2,
            E::Eunop(_, _) => 3,
            E::Ebinop(_, _, _) => 4,
            E::Eload(_, _) => 5,
            E::Econdition(_, _, _) => 6,
        }
    };
    rank(a).cmp(&rank(b)).then_with(|| match (a, b) {
        (E::Evar(x), E::Evar(y)) => x.cmp(y),
        (E::Eaddrof(x), E::Eaddrof(y)) => x.cmp(y),
        (E::Econst(x), E::Econst(y)) => cmp_constant(x, y),
        (E::Eunop(oa, xa), E::Eunop(ob, xb)) => {
            // CminorUnop is fieldless: the integer cast is its variant rank.
            (oa.clone() as u8)
                .cmp(&(ob.clone() as u8))
                .then_with(|| cmp_csharp_expr(xa, xb))
        }
        (E::Ebinop(oa, la, ra), E::Ebinop(ob, lb, rb)) => cminor_binop_key(oa)
            .cmp(&cminor_binop_key(ob))
            .then_with(|| cmp_csharp_expr(la, lb))
            .then_with(|| cmp_csharp_expr(ra, rb)),
        (E::Eload(ca, xa), E::Eload(cb, xb)) => ca.cmp(cb).then_with(|| cmp_csharp_expr(xa, xb)),
        (E::Econdition(ca, ta, fa), E::Econdition(cb, tb, fb)) => cmp_csharp_expr(ca, cb)
            .then_with(|| cmp_csharp_expr(ta, tb))
            .then_with(|| cmp_csharp_expr(fa, fb)),
        _ => Ordering::Equal, // unreachable: equal ranks imply the same variant
    })
}

fn cmp_clight_attr(a: &ClightAttr, b: &ClightAttr) -> Ordering {
    a.attr_volatile
        .cmp(&b.attr_volatile)
        .then_with(|| a.attr_alignas.cmp(&b.attr_alignas))
}

fn cmp_clight_type(a: &ClightType, b: &ClightType) -> Ordering {
    use ClightType as T;
    let rank = |t: &T| -> u8 {
        match t {
            T::Tvoid => 0,
            T::Tint(_, _, _) => 1,
            T::Tlong(_, _) => 2,
            T::Tfloat(_, _) => 3,
            T::Tpointer(_, _) => 4,
            T::Tarray(_, _, _) => 5,
            T::Tfunction(_, _, _) => 6,
            T::Tstruct(_, _) => 7,
            T::Tunion(_, _) => 8,
            T::Tint128(_, _) => 9,
        }
    };
    rank(a).cmp(&rank(b)).then_with(|| match (a, b) {
        (T::Tint(sa, ga, aa), T::Tint(sb, gb, ab)) => (*sa as u8)
            .cmp(&(*sb as u8))
            .then((*ga as u8).cmp(&(*gb as u8)))
            .then_with(|| cmp_clight_attr(aa, ab)),
        (T::Tlong(ga, aa), T::Tlong(gb, ab)) => (*ga as u8)
            .cmp(&(*gb as u8))
            .then_with(|| cmp_clight_attr(aa, ab)),
        (T::Tint128(ga, aa), T::Tint128(gb, ab)) => (*ga as u8)
            .cmp(&(*gb as u8))
            .then_with(|| cmp_clight_attr(aa, ab)),
        (T::Tfloat(fa, aa), T::Tfloat(fb, ab)) => (*fa as u8)
            .cmp(&(*fb as u8))
            .then_with(|| cmp_clight_attr(aa, ab)),
        (T::Tpointer(ta, aa), T::Tpointer(tb, ab)) => {
            cmp_clight_type(ta, tb).then_with(|| cmp_clight_attr(aa, ab))
        }
        (T::Tarray(ta, na, aa), T::Tarray(tb, nb, ab)) => cmp_clight_type(ta, tb)
            .then(na.cmp(nb))
            .then_with(|| cmp_clight_attr(aa, ab)),
        (T::Tfunction(pa, ra, ca), T::Tfunction(pb, rb, cb)) => {
            cmp_slice(pa, pb, cmp_clight_type)
                .then_with(|| cmp_clight_type(ra, rb))
                .then_with(|| ca.cmp(cb)) // CallConv: derived Ord
        }
        (T::Tstruct(ia, aa), T::Tstruct(ib, ab)) | (T::Tunion(ia, aa), T::Tunion(ib, ab)) => {
            ia.cmp(ib).then_with(|| cmp_clight_attr(aa, ab))
        }
        _ => Ordering::Equal, // unreachable: equal ranks imply the same variant
    })
}

fn cmp_clight_expr(a: &ClightExpr, b: &ClightExpr) -> Ordering {
    use ClightExpr as E;
    let rank = |e: &E| -> u8 {
        match e {
            E::EconstInt(_, _) => 0,
            E::EconstFloat(_, _) => 1,
            E::EconstSingle(_, _) => 2,
            E::EconstLong(_, _) => 3,
            E::Evar(_, _) => 4,
            E::EvarSymbol(_, _) => 5,
            E::Etempvar(_, _) => 6,
            E::Ederef(_, _) => 7,
            E::Eaddrof(_, _) => 8,
            E::Eunop(_, _, _) => 9,
            E::Ebinop(_, _, _, _) => 10,
            E::Ecast(_, _) => 11,
            E::Efield(_, _, _) => 12,
            E::Esizeof(_, _) => 13,
            E::Ealignof(_, _) => 14,
            E::Econdition(_, _, _, _) => 15,
        }
    };
    rank(a).cmp(&rank(b)).then_with(|| match (a, b) {
        (E::EconstInt(va, ta), E::EconstInt(vb, tb)) => {
            va.cmp(vb).then_with(|| cmp_clight_type(ta, tb))
        }
        (E::EconstFloat(va, ta), E::EconstFloat(vb, tb)) => {
            va.0.total_cmp(&vb.0).then_with(|| cmp_clight_type(ta, tb))
        }
        (E::EconstSingle(va, ta), E::EconstSingle(vb, tb)) => {
            va.0.total_cmp(&vb.0).then_with(|| cmp_clight_type(ta, tb))
        }
        (E::EconstLong(va, ta), E::EconstLong(vb, tb)) => {
            va.cmp(vb).then_with(|| cmp_clight_type(ta, tb))
        }
        (E::Evar(ia, ta), E::Evar(ib, tb)) | (E::Etempvar(ia, ta), E::Etempvar(ib, tb)) => {
            ia.cmp(ib).then_with(|| cmp_clight_type(ta, tb))
        }
        (E::EvarSymbol(sa, ta), E::EvarSymbol(sb, tb)) => {
            sa.cmp(sb).then_with(|| cmp_clight_type(ta, tb))
        }
        (E::Ederef(xa, ta), E::Ederef(xb, tb))
        | (E::Eaddrof(xa, ta), E::Eaddrof(xb, tb))
        | (E::Ecast(xa, ta), E::Ecast(xb, tb)) => {
            cmp_clight_expr(xa, xb).then_with(|| cmp_clight_type(ta, tb))
        }
        (E::Eunop(oa, xa, ta), E::Eunop(ob, xb, tb)) => (*oa as u8)
            .cmp(&(*ob as u8))
            .then_with(|| cmp_clight_expr(xa, xb))
            .then_with(|| cmp_clight_type(ta, tb)),
        (E::Ebinop(oa, la, ra, ta), E::Ebinop(ob, lb, rb, tb)) => (*oa as u8)
            .cmp(&(*ob as u8))
            .then_with(|| cmp_clight_expr(la, lb))
            .then_with(|| cmp_clight_expr(ra, rb))
            .then_with(|| cmp_clight_type(ta, tb)),
        (E::Efield(xa, ia, ta), E::Efield(xb, ib, tb)) => cmp_clight_expr(xa, xb)
            .then(ia.cmp(ib))
            .then_with(|| cmp_clight_type(ta, tb)),
        (E::Esizeof(ua, ta), E::Esizeof(ub, tb)) | (E::Ealignof(ua, ta), E::Ealignof(ub, tb)) => {
            cmp_clight_type(ua, ub).then_with(|| cmp_clight_type(ta, tb))
        }
        (E::Econdition(ca, xa, ya, ta), E::Econdition(cb, xb, yb, tb)) => cmp_clight_expr(ca, cb)
            .then_with(|| cmp_clight_expr(xa, xb))
            .then_with(|| cmp_clight_expr(ya, yb))
            .then_with(|| cmp_clight_type(ta, tb)),
        _ => Ordering::Equal, // unreachable: equal ranks imply the same variant
    })
}

fn cmp_external_function(a: &ExternalFunction, b: &ExternalFunction) -> Ordering {
    use crate::x86::types::ExternalFunction as F;
    let rank = |f: &F| -> u8 {
        match f {
            F::EFExternal(_, _) => 0,
            F::EFBuiltin(_, _) => 1,
            F::EFRuntime(_, _) => 2,
            F::EFVLoad(_) => 3,
            F::EFVStore(_) => 4,
            F::EFMalloc => 5,
            F::EFFree => 6,
            F::EFMemcpy(_, _) => 7,
            F::EFAnnot(_, _, _) => 8,
            F::EFAnnotVal(_, _, _) => 9,
            F::EFInlineAsm(_, _, _) => 10,
            F::EFDebug(_, _, _) => 11,
        }
    };
    rank(a).cmp(&rank(b)).then_with(|| match (a, b) {
        (F::EFExternal(na, sa), F::EFExternal(nb, sb))
        | (F::EFBuiltin(na, sa), F::EFBuiltin(nb, sb))
        | (F::EFRuntime(na, sa), F::EFRuntime(nb, sb)) => {
            na.cmp(nb).then_with(|| sa.cmp(sb)) // Signature: derived Ord
        }
        (F::EFVLoad(ca), F::EFVLoad(cb)) | (F::EFVStore(ca), F::EFVStore(cb)) => ca.cmp(cb),
        (F::EFMemcpy(xa, ya), F::EFMemcpy(xb, yb)) => xa.cmp(xb).then(ya.cmp(yb)),
        (F::EFAnnot(pa, na, ta), F::EFAnnot(pb, nb, tb)) => {
            pa.cmp(pb).then_with(|| na.cmp(nb)).then_with(|| ta.cmp(tb)) // Vec<Typ>: derived Ord
        }
        (F::EFAnnotVal(pa, na, ta), F::EFAnnotVal(pb, nb, tb)) => {
            pa.cmp(pb).then_with(|| na.cmp(nb)).then(ta.cmp(tb))
        }
        (F::EFInlineAsm(na, sa, ca), F::EFInlineAsm(nb, sb, cb)) => {
            na.cmp(nb).then_with(|| sa.cmp(sb)).then_with(|| ca.cmp(cb))
        }
        (F::EFDebug(pa, ia, ta), F::EFDebug(pb, ib, tb)) => {
            pa.cmp(pb).then(ia.cmp(ib)).then_with(|| ta.cmp(tb))
        }
        _ => Ordering::Equal, // unit variants / unreachable mixed pairs
    })
}

fn cmp_clight_stmt(a: &ClightStmt, b: &ClightStmt) -> Ordering {
    use ClightStmt as S;
    let rank = |s: &S| -> u8 {
        match s {
            S::Sskip => 0,
            S::Sassign(_, _) => 1,
            S::Sset(_, _) => 2,
            S::Scall(_, _, _) => 3,
            S::Sbuiltin(_, _, _, _) => 4,
            S::Ssequence(_) => 5,
            S::Sifthenelse(_, _, _) => 6,
            S::Sloop(_, _) => 7,
            S::Sbreak => 8,
            S::Scontinue => 9,
            S::Sreturn(_) => 10,
            S::Sswitch(_, _) => 11,
            S::Slabel(_, _) => 12,
            S::Sgoto(_) => 13,
        }
    };
    rank(a).cmp(&rank(b)).then_with(|| match (a, b) {
        (S::Sassign(la, ra), S::Sassign(lb, rb)) => {
            cmp_clight_expr(la, lb).then_with(|| cmp_clight_expr(ra, rb))
        }
        (S::Sset(ia, ea), S::Sset(ib, eb)) => ia.cmp(ib).then_with(|| cmp_clight_expr(ea, eb)),
        (S::Scall(ra, fa, aa), S::Scall(rb, fb, ab)) => ra
            .cmp(rb)
            .then_with(|| cmp_clight_expr(fa, fb))
            .then_with(|| cmp_slice(aa, ab, cmp_clight_expr)),
        (S::Sbuiltin(ra, ea, ta, aa), S::Sbuiltin(rb, eb, tb, ab)) => ra
            .cmp(rb)
            .then_with(|| cmp_external_function(ea, eb))
            .then_with(|| cmp_slice(ta, tb, cmp_clight_type))
            .then_with(|| cmp_slice(aa, ab, cmp_clight_expr)),
        (S::Ssequence(sa), S::Ssequence(sb)) => cmp_slice(sa, sb, cmp_clight_stmt),
        (S::Sifthenelse(ca, ta, fa), S::Sifthenelse(cb, tb, fb)) => cmp_clight_expr(ca, cb)
            .then_with(|| cmp_clight_stmt(ta, tb))
            .then_with(|| cmp_clight_stmt(fa, fb)),
        (S::Sloop(ba, sa), S::Sloop(bb, sb)) => {
            cmp_clight_stmt(ba, bb).then_with(|| cmp_clight_stmt(sa, sb))
        }
        (S::Sreturn(ea), S::Sreturn(eb)) => cmp_option(ea, eb, cmp_clight_expr),
        (S::Sswitch(ea, ca), S::Sswitch(eb, cb)) => cmp_clight_expr(ea, eb).then_with(|| {
            cmp_slice(ca, cb, |(la, sa), (lb, sb)| {
                la.cmp(lb).then_with(|| cmp_clight_stmt(sa, sb))
            })
        }),
        (S::Slabel(ia, sa), S::Slabel(ib, sb)) => ia.cmp(ib).then_with(|| cmp_clight_stmt(sa, sb)),
        (S::Sgoto(ia), S::Sgoto(ib)) => ia.cmp(ib),
        _ => Ordering::Equal, // unit variants / unreachable mixed pairs
    })
}

pub fn extract_loop_info(db: &DecompileDB) -> HashMap<Address, HashMap<Node, LoopInfo>> {
    let mut result: HashMap<Address, HashMap<Node, LoopInfo>> = HashMap::new();

    for (func_addr, loop_head, body_node) in db.rel_iter::<(Address, Node, Node)>("emit_loop_body")
    {
        if body_node != loop_head {
            result
                .entry(*func_addr)
                .or_default()
                .entry(*loop_head)
                .or_insert_with(LoopInfo::default)
                .body_nodes
                .push(*body_node);
        }
    }

    // Keep every structurally-derived target for a physical exit branch.  A
    // primary break is targetable only when that set is a singleton; choosing
    // one of conflicting targets would turn an analysis ambiguity into a CFG
    // rewrite.
    let mut exit_targets_by_branch: HashMap<(Address, Node, Node), HashSet<Node>> = HashMap::new();
    for (func_addr, loop_head, exit_node, _, _, exit_target, _) in db.rel_iter::<(
        Address,
        Node,
        Node,
        Condition,
        Arc<Vec<CsharpminorExpr>>,
        Node,
        Node,
    )>("emit_loop_exit")
    {
        result
            .entry(*func_addr)
            .or_default()
            .entry(*loop_head)
            .or_insert_with(LoopInfo::default);
        exit_targets_by_branch
            .entry((*func_addr, *loop_head, *exit_node))
            .or_default()
            .insert(*exit_target);
    }

    // A loop can be specialized around a primary exit only when the analysis
    // identifies one physical exit branch.  Choosing among several candidate
    // nodes by address would confuse layout with control-flow evidence.
    let mut primary_exit_nodes: HashMap<(Address, Node), HashSet<Node>> = HashMap::new();
    for (func_addr, loop_header, exit_node) in
        db.rel_iter::<(Address, Node, Node)>("primary_exit_node")
    {
        primary_exit_nodes
            .entry((*func_addr, *loop_header))
            .or_default()
            .insert(*exit_node);
    }
    let primary_exit_keys: HashSet<(Address, Node, Node)> = primary_exit_nodes
        .iter()
        .flat_map(|(&(func_addr, loop_header), exit_nodes)| {
            exit_nodes
                .iter()
                .map(move |&exit_node| (func_addr, loop_header, exit_node))
        })
        .collect();
    for ((func_addr, loop_header), mut exit_nodes) in primary_exit_nodes {
        if exit_nodes.len() != 1 {
            continue;
        }
        let exit_node = exit_nodes.drain().next().unwrap();
        let Some(exit_target) = exit_targets_by_branch
            .get(&(func_addr, loop_header, exit_node))
            .and_then(|targets| {
                (targets.len() == 1).then(|| targets.iter().next().copied().unwrap())
            })
        else {
            continue;
        };
        let primary_exit = PrimaryExitData {
            exit_node,
            exit_target: Some(exit_target),
        };
        result
            .entry(func_addr)
            .or_default()
            .entry(loop_header)
            .or_insert_with(LoopInfo::default)
            .primary_exit = Some(primary_exit);
    }

    // Non-primary exits retain only their unique structural target.  Their
    // condition is taken later from the selected Clight statement, never from
    // one of the candidate-level loop_exit_branch rows.
    for ((func_addr, loop_header, exit_node), targets) in &exit_targets_by_branch {
        if primary_exit_keys.contains(&(*func_addr, *loop_header, *exit_node)) || targets.len() != 1
        {
            continue;
        }
        let exit_target = *targets.iter().next().unwrap();
        result
            .entry(*func_addr)
            .or_default()
            .entry(*loop_header)
            .or_insert_with(LoopInfo::default)
            .exit_targets
            .insert(*exit_node, exit_target);
    }

    // Populate exit_returns from loop_exit_to_return (non-primary exits flowing
    // to a function return).  Tail duplication is safe only for a unique
    // structural (value, return) pair; ambiguous paths retain flat control
    // flow instead of selecting a pair by node id.
    let mut exit_return_candidates: HashMap<(Address, Node, Node), HashSet<(Node, Node)>> =
        HashMap::new();
    for (func_addr, loop_header, exit_node, value_node, ret_node) in
        db.rel_iter::<(Address, Node, Node, Node, Node)>("loop_exit_to_return")
    {
        exit_return_candidates
            .entry((*func_addr, *loop_header, *exit_node))
            .or_default()
            .insert((*value_node, *ret_node));
    }
    for ((func_addr, loop_header, exit_node), mut candidates) in exit_return_candidates {
        if candidates.len() != 1 {
            continue;
        }
        let candidate = candidates.drain().next().unwrap();
        result
            .entry(func_addr)
            .or_default()
            .entry(loop_header)
            .or_insert_with(LoopInfo::default)
            .exit_returns
            .insert(exit_node, candidate);
    }

    // exec_order_key (not raw id) is required: it keeps a synthetic node (addr | 1<<62) immediately after its base, preventing calls from being pushed past exits and eliminated as unreachable.
    for func_map in result.values_mut() {
        for info in func_map.values_mut() {
            info.body_nodes
                .sort_by_key(|&n| crate::util::exec_order_key(n));
        }
    }

    result
}

// If-then-else structural metadata from the structuring pass.
#[derive(Debug, Clone, Default)]
pub struct IteInfo {
    pub true_body_nodes: Vec<Node>,
    pub false_body_nodes: Vec<Node>,
    pub join_node: Option<Node>,
    pub no_join: bool,
}

pub fn extract_ite_info(db: &DecompileDB) -> HashMap<Address, HashMap<Node, IteInfo>> {
    let mut result: HashMap<Address, HashMap<Node, IteInfo>> = HashMap::new();

    for (func_addr, branch, member) in db.rel_iter::<(Address, Node, Node)>("emit_ifbody_true") {
        result
            .entry(*func_addr)
            .or_default()
            .entry(*branch)
            .or_insert_with(IteInfo::default)
            .true_body_nodes
            .push(*member);
    }

    for (func_addr, branch, member) in db.rel_iter::<(Address, Node, Node)>("emit_ifbody_false") {
        result
            .entry(*func_addr)
            .or_default()
            .entry(*branch)
            .or_insert_with(IteInfo::default)
            .false_body_nodes
            .push(*member);
    }

    // A structured branch has one immediate post-dominator.  Never choose
    // among conflicting facts by address: node magnitude says nothing about
    // CFG reachability.  Preserve only a structurally unique result; an
    // ambiguous branch is left unassembled below rather than guessed.
    let mut join_candidates: BTreeMap<(Address, Node), BTreeSet<Node>> = BTreeMap::new();
    for (func_addr, branch, join) in db.rel_iter::<(Address, Node, Node)>("emit_join_point") {
        join_candidates
            .entry((*func_addr, *branch))
            .or_default()
            .insert(*join);
    }
    for ((func_addr, branch), candidates) in join_candidates {
        let info = result
            .entry(func_addr)
            .or_default()
            .entry(branch)
            .or_insert_with(IteInfo::default);
        if candidates.len() == 1 {
            info.join_node = candidates.into_iter().next();
        } else {
            log::warn!(
                "structuring produced {} immediate joins for branch {branch:#x} in {func_addr:#x}; leaving it flat",
                candidates.len()
            );
        }
    }

    for (func_addr, branch) in db.rel_iter::<(Address, Node)>("emit_scond_no_join") {
        result
            .entry(*func_addr)
            .or_default()
            .entry(*branch)
            .or_insert_with(IteInfo::default)
            .no_join = true;
    }

    // exec_order_key places a synthetic node (addr | 1<<62) immediately after its base; a raw id sort would push all synthetic members after all real ones, tearing fused stores out of position.
    for func_map in result.values_mut() {
        for info in func_map.values_mut() {
            info.true_body_nodes
                .sort_by_key(|&n| crate::util::exec_order_key(n));
            info.false_body_nodes
                .sort_by_key(|&n| crate::util::exec_order_key(n));
        }
    }

    result
}

#[derive(Debug, Clone)]
pub struct ExtractedStruct {
    pub struct_id: usize,
    #[allow(dead_code)]
    pub layout_hash: u64,
    #[allow(dead_code)]
    pub is_canonical: bool,
    pub definition: StructDef,
}

fn fieldtype_to_ctype(field_type: &FieldType, model: crate::abi::DataModel) -> CType {
    match field_type {
        FieldType::Scalar(chunk) => chunk_to_ctype(*chunk, chunk_size(chunk), model),
        FieldType::Pointer(inner) => CType::Pointer(
            Box::new(fieldtype_to_ctype(inner, model)),
            TypeQualifiers::none(),
        ),
        FieldType::StructPointer(struct_id) => {
            let struct_name = format!("struct_{:x}", struct_id);
            CType::Pointer(Box::new(CType::Struct(struct_name)), TypeQualifiers::none())
        }
        FieldType::Array(elem, size) => {
            CType::Array(Box::new(fieldtype_to_ctype(elem, model)), Some(*size))
        }
        FieldType::EmbeddedStruct(struct_id) => CType::Struct(format!("struct_{:x}", struct_id)),
        FieldType::Union(variants) => {
            // SR-2: layout advance is the MAX variant size; pick the first max-size variant so printed width == advance (a smaller variant first would shift all later fields).
            let max_size = variants.iter().map(|v| v.size(8)).max().unwrap_or(4);
            variants
                .iter()
                .find(|v| v.size(8) == max_size)
                .map(|ft| fieldtype_to_ctype(ft, model))
                .unwrap_or(CType::Int(IntSize::Int, Signedness::Signed))
        }
        FieldType::OpaqueBlob(size) => CType::Array(
            Box::new(CType::Int(IntSize::Char, Signedness::Unsigned)),
            Some(*size),
        ),
        FieldType::Unknown => CType::Int(IntSize::Int, Signedness::Signed),
    }
}

fn chunk_size(chunk: &MemoryChunk) -> usize {
    match chunk {
        MemoryChunk::MBool | MemoryChunk::MInt8Signed | MemoryChunk::MInt8Unsigned => 1,
        MemoryChunk::MInt16Signed | MemoryChunk::MInt16Unsigned => 2,
        MemoryChunk::MInt32 | MemoryChunk::MFloat32 | MemoryChunk::MAny32 => 4,
        MemoryChunk::MInt64 | MemoryChunk::MFloat64 | MemoryChunk::MAny64 => 8,
        MemoryChunk::Unknown => 4,
    }
}

fn fieldtype_alignment(field_type: &FieldType, pointer_size: usize) -> usize {
    match field_type {
        FieldType::Scalar(chunk) => chunk_size(chunk),
        FieldType::Pointer(_) | FieldType::StructPointer(_) => pointer_size,
        // Embedded aggregates currently carry only an id here, not their
        // definition.  Their modeled width is one machine word, which is also
        // the strongest alignment we may safely assume at this boundary.
        FieldType::EmbeddedStruct(_) => pointer_size,
        FieldType::Array(elem, _) => fieldtype_alignment(elem, pointer_size),
        FieldType::Union(variants) => variants
            .iter()
            .map(|variant| fieldtype_alignment(variant, pointer_size))
            .max()
            .unwrap_or(1),
        FieldType::OpaqueBlob(_) => 1,
        FieldType::Unknown => 4,
    }
}

fn build_fields_with_padding(
    field_tuples: &[(usize, i64, FieldType, usize)],
    model: crate::abi::DataModel,
) -> Vec<StructField> {
    // Pointer fields are the target's pointer wide and align to it; assuming 8
    // lays a 32-bit image's structs out with the wrong stride.
    let ptr = model.pointer_size();
    let mut offset_map: BTreeMap<i64, &(usize, i64, FieldType, usize)> = BTreeMap::new();
    for entry in field_tuples {
        let (idx, offset, _, _) = entry;
        match offset_map.get(offset) {
            Some(existing) if existing.0 >= *idx => {}
            _ => {
                offset_map.insert(*offset, entry);
            }
        }
    }

    let mut fields = Vec::new();
    let mut current_end: i64 = 0;

    for (_offset, (_idx, offset, field_type, field_name)) in &offset_map {
        if *offset > current_end {
            let pad_size = (*offset - current_end) as usize;
            match pad_size {
                1 => fields.push(StructField::new(
                    format!("uc_{:x}", current_end),
                    CType::Int(IntSize::Char, Signedness::Unsigned),
                )),
                _ => fields.push(StructField::new(
                    format!("_pad_{:x}", current_end),
                    CType::Array(
                        Box::new(CType::Int(IntSize::Char, Signedness::Unsigned)),
                        Some(pad_size),
                    ),
                )),
            }
        }

        let name =
            crate::decompile::analysis::struct_recovery_pass::field_ident_to_name(*field_name);
        let ty = fieldtype_to_ctype(field_type, model);
        let alignment = fieldtype_alignment(field_type, ptr) as i64;
        let field = StructField::new(name, ty);
        fields.push(if offset.rem_euclid(alignment) == 0 {
            field
        } else {
            field.packed()
        });

        current_end = *offset + field_type.size(ptr) as i64;
    }

    fields
}

#[cfg(test)]
mod recovered_struct_layout_tests {
    use super::*;
    use crate::decompile::passes::c_pass::print::Printer;

    #[test]
    fn misaligned_wide_field_is_packed_without_packing_the_struct() {
        let tuples = vec![
            (0, 0, FieldType::Scalar(MemoryChunk::MInt32), 0),
            (1, 4, FieldType::Scalar(MemoryChunk::MInt32), 4),
            (2, 8, FieldType::Scalar(MemoryChunk::MInt32), 8),
            (3, 12, FieldType::Scalar(MemoryChunk::MInt32), 12),
            (4, 16, FieldType::Scalar(MemoryChunk::MInt32), 16),
            (5, 20, FieldType::Scalar(MemoryChunk::MInt64), 20),
            (6, 28, FieldType::Scalar(MemoryChunk::MInt8Unsigned), 28),
        ];
        let fields = build_fields_with_padding(&tuples, crate::abi::DataModel::Lp64);

        let wide = fields
            .iter()
            .find(|field| field.name.as_deref() == Some("ofs_20"))
            .expect("offset-20 field");
        assert!(wide.is_packed, "an 8-byte field at offset 20 needs packing");
        assert!(fields
            .iter()
            .filter(|field| field.name.as_deref() != Some("ofs_20"))
            .all(|field| !field.is_packed));

        let mut printer = Printer::with_default_config();
        printer.print_struct_def(&StructDef::new_struct("ring", fields));
        let rendered = printer.into_string();
        assert!(rendered.contains("long ofs_20 __attribute__((packed));"));
        assert!(!rendered.contains("struct ring __attribute__((packed))"));
    }

    #[test]
    fn synthetic_gap_is_a_byte_array() {
        let tuples = vec![
            (0, 0, FieldType::Scalar(MemoryChunk::MInt8Unsigned), 0),
            (1, 3, FieldType::Scalar(MemoryChunk::MInt8Unsigned), 3),
        ];
        let fields = build_fields_with_padding(&tuples, crate::abi::DataModel::Lp64);
        let gap = fields
            .iter()
            .find(|field| field.name.as_deref() == Some("_pad_1"))
            .expect("two-byte gap");
        assert_eq!(
            gap.ty,
            CType::Array(
                Box::new(CType::Int(IntSize::Char, Signedness::Unsigned)),
                Some(2)
            )
        );
    }
}

pub fn extract_struct_definitions(db: &DecompileDB) -> Vec<ExtractedStruct> {
    let data_model = db.data_model();
    let mut structs = Vec::new();
    let mut seen_struct_ids = HashSet::new();

    // Pre-collect efield-detected fields per struct ID (merging across functions); these come from ClightFieldPass and may contain fields not in struct_recovery. reg_to_struct_id may emit multiple sids per reg, so pick the smallest so the same reg resolves to the same canonical id every run.
    let reg_to_canonical_ids: HashMap<u64, usize> = {
        let mut groups: HashMap<u64, Vec<usize>> = HashMap::new();
        for &(_, reg, sid) in db.rel_iter::<(u64, u64, usize)>("reg_to_struct_id") {
            groups.entry(reg).or_default().push(sid);
        }
        groups
            .into_iter()
            .map(|(reg, mut sids)| {
                sids.sort();
                (reg, sids[0])
            })
            .collect()
    };

    // Collect (struct_id, field_offset, field_name, chunk) across all emit_struct_fields tuples, sorting before dedup-by-(struct_id, offset) so the winner is stable under non-deterministic iteration.
    let mut efield_collected: Vec<(usize, i64, Ident, MemoryChunk)> = Vec::new();
    for (_func_addr, base_offset, fields) in
        db.rel_iter::<(u64, i64, Arc<Vec<(i64, Ident, MemoryChunk)>>)>("emit_struct_fields")
    {
        let reg = *base_offset as u64;
        let struct_id = reg_to_canonical_ids
            .get(&reg)
            .copied()
            .unwrap_or_else(|| base_offset.unsigned_abs() as usize);
        for (field_offset, field_name, chunk) in fields.iter() {
            efield_collected.push((struct_id, *field_offset, *field_name, chunk.clone()));
        }
    }
    efield_collected.sort();
    let mut efield_extra_fields: HashMap<usize, BTreeMap<i64, (Ident, MemoryChunk)>> =
        HashMap::new();
    for (struct_id, field_offset, field_name, chunk) in efield_collected {
        efield_extra_fields
            .entry(struct_id)
            .or_default()
            .entry(field_offset)
            .or_insert((field_name, chunk));
    }

    for (layout_hash, canonical_id, _field_count, _total_size) in
        db.rel_iter::<(u64, usize, usize, usize)>("global_struct_catalog")
    {
        if seen_struct_ids.contains(canonical_id) {
            continue;
        }
        seen_struct_ids.insert(*canonical_id);

        let mut field_tuples: Vec<_> = db
            .rel_iter::<(usize, usize, i64, FieldType, Ident)>("emit_struct_field")
            .filter(|(sid, _, _, _, _)| *sid == *canonical_id)
            .map(|(_, idx, offset, field_type, field_name)| {
                (*idx, *offset, field_type.clone(), *field_name)
            })
            .collect();

        // Merge efield-detected fields that aren't in the canonical definition
        if let Some(efield_fields) = efield_extra_fields.get(canonical_id) {
            let existing_offsets: HashSet<i64> =
                field_tuples.iter().map(|(_, off, _, _)| *off).collect();
            let next_idx = field_tuples.len();
            for (idx, (offset, (field_name, chunk))) in efield_fields.iter().enumerate() {
                if !existing_offsets.contains(offset) {
                    field_tuples.push((
                        next_idx + idx,
                        *offset,
                        FieldType::Scalar(chunk.clone()),
                        *field_name,
                    ));
                }
            }
        }

        field_tuples.sort_by_key(|(_idx, offset, _, _)| *offset);

        let struct_name = format!("struct_{:x}", canonical_id);
        let struct_fields = build_fields_with_padding(&field_tuples, data_model);

        let definition = StructDef::new_struct(struct_name, struct_fields);

        structs.push(ExtractedStruct {
            struct_id: *canonical_id,
            layout_hash: *layout_hash,
            is_canonical: true,
            definition,
        });
    }

    if structs.is_empty() {
        for (struct_id, _field_count, _total_size) in
            db.rel_iter::<(usize, usize, usize)>("emit_struct_def")
        {
            if seen_struct_ids.contains(struct_id) {
                continue;
            }
            seen_struct_ids.insert(*struct_id);

            let mut field_tuples: Vec<_> = db
                .rel_iter::<(usize, usize, i64, FieldType, Ident)>("emit_struct_field")
                .filter(|(sid, _, _, _, _)| *sid == *struct_id)
                .map(|(_, idx, offset, field_type, field_name)| {
                    (*idx, *offset, field_type.clone(), *field_name)
                })
                .collect();

            field_tuples.sort_by_key(|(_idx, offset, _, _)| *offset);

            let struct_name = format!("struct_{:x}", struct_id);
            let struct_fields = build_fields_with_padding(&field_tuples, data_model);

            let layout_hash = compute_field_hash(&field_tuples);
            let definition = StructDef::new_struct(struct_name, struct_fields);

            structs.push(ExtractedStruct {
                struct_id: *struct_id,
                layout_hash,
                is_canonical: true,
                definition,
            });
        }
    }

    // Generate struct definitions from emit_struct_fields for efield-detected structs not matched to canonical struct_recovery IDs (register-based IDs from ClightFieldPass).
    for (struct_id, field_map) in &efield_extra_fields {
        if seen_struct_ids.contains(struct_id) {
            continue;
        }
        let struct_name = format!("struct_{:x}", struct_id);
        let field_tuples: Vec<(usize, i64, FieldType, usize)> = field_map
            .iter()
            .enumerate()
            .map(|(idx, (offset, (field_name, chunk)))| {
                (idx, *offset, FieldType::Scalar(chunk.clone()), *field_name)
            })
            .collect();

        let struct_fields = build_fields_with_padding(&field_tuples, data_model);
        let layout_hash = compute_field_hash(&field_tuples);
        let definition = StructDef::new_struct(struct_name, struct_fields);

        seen_struct_ids.insert(*struct_id);
        structs.push(ExtractedStruct {
            struct_id: *struct_id,
            layout_hash,
            is_canonical: false,
            definition,
        });
    }

    structs.sort_by_key(|s| s.struct_id);
    structs
}

fn compute_field_hash(fields: &[(usize, i64, FieldType, usize)]) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut hasher = DefaultHasher::new();
    for (idx, offset, ty, _name) in fields {
        idx.hash(&mut hasher);
        offset.hash(&mut hasher);
        ty.to_type_string().hash(&mut hasher);
    }
    hasher.finish()
}

pub fn extract_struct_layout_map(
    db: &DecompileDB,
) -> HashMap<usize, Vec<(i64, String, MemoryChunk)>> {
    let mut layouts = HashMap::new();

    let id_to_name: HashMap<usize, String> = db
        .rel_iter::<(Ident, Symbol)>("ident_to_symbol")
        .map(|(id, name)| (*id, name.to_string()))
        .collect();

    let canonical_ids: HashSet<usize> = db
        .rel_iter::<(u64, usize)>("emit_canonical_struct_id")
        .map(|(_hash, id)| *id)
        .collect();

    for (global_ident, struct_id, fields) in db
        .rel_iter::<(Ident, usize, Arc<Vec<(i64, Ident, MemoryChunk)>>)>(
            "emit_global_struct_fields",
        )
    {
        let _global_name = id_to_name
            .get(&(*global_ident as usize))
            .cloned()
            .unwrap_or_else(|| format!("global_{:x}", global_ident));

        let mapped_fields: Vec<(i64, String, MemoryChunk)> = fields
            .iter()
            .map(|(offset, field_ident, chunk)| {
                let field_name = id_to_name
                    .get(&(*field_ident as usize))
                    .cloned()
                    .unwrap_or_else(|| format!("field_{:x}", offset));
                (*offset, field_name, *chunk)
            })
            .collect();

        layouts.insert(*struct_id, mapped_fields);
    }

    layouts
}

/// A recovered memory chunk as a C type.  The 64-bit cases take the target's
/// spelling: declaring an 8-byte field `long` narrows it to 4 bytes off LP64 and
/// shifts every field after it.
fn chunk_to_ctype(chunk: MemoryChunk, size: usize, model: crate::abi::DataModel) -> CType {
    match chunk {
        // SR-2: MBool must map to unsigned char (1 byte), not CType::Bool which renders as "int" (4 bytes) and would shift every later field of the struct.
        MemoryChunk::MBool => CType::Int(IntSize::Char, Signedness::Unsigned),
        MemoryChunk::MInt8Signed => CType::Int(IntSize::Char, Signedness::Signed),
        MemoryChunk::MInt8Unsigned => CType::Int(IntSize::Char, Signedness::Unsigned),
        MemoryChunk::MInt16Signed => CType::Int(IntSize::Short, Signedness::Signed),
        MemoryChunk::MInt16Unsigned => CType::Int(IntSize::Short, Signedness::Unsigned),
        MemoryChunk::MInt32 | MemoryChunk::MAny32 => CType::Int(IntSize::Int, Signedness::Signed),
        MemoryChunk::MInt64 | MemoryChunk::MAny64 => CType::int64(model, Signedness::Signed),
        MemoryChunk::MFloat32 => {
            CType::Float(crate::decompile::passes::c_pass::types::FloatSize::Float)
        }
        MemoryChunk::MFloat64 => {
            CType::Float(crate::decompile::passes::c_pass::types::FloatSize::Double)
        }
        MemoryChunk::Unknown => match size {
            1 => CType::Int(IntSize::Char, Signedness::Unsigned),
            2 => CType::Int(IntSize::Short, Signedness::Signed),
            4 => CType::Int(IntSize::Int, Signedness::Signed),
            8 => CType::int64(model, Signedness::Signed),
            _ => CType::Int(IntSize::Int, Signedness::Signed),
        },
    }
}

// TR-3: struct-field pointer-type helpers shared between solver input and emission-side recomputation; the emission side must recompute, and scanning SELECTED statements is more precise.

/// (struct_name, field_name) key of a field-access lvalue. Mirror of solve.rs::field_key_of_lvalue.
pub(crate) fn clight_field_key_of_lvalue(e: &ClightExpr) -> Option<(String, String)> {
    if let ClightExpr::Efield(base, fid, _) = e {
        if let ClightExpr::Ederef(_, ClightType::Tstruct(sid, _)) = base.as_ref() {
            let struct_name = format!("struct_{:x}", sid);
            let field_name = crate::decompile::passes::csh_pass::field_ident_to_name(*fid);
            return Some((struct_name, field_name));
        }
    }
    None
}

/// (struct, field) key of a field-access value, possibly cast-wrapped. Mirror of solve.rs::field_key_of_expr.
pub(crate) fn clight_field_key_of_expr(e: &ClightExpr) -> Option<(String, String)> {
    match e {
        ClightExpr::Ecast(inner, _) => clight_field_key_of_expr(inner),
        _ => clight_field_key_of_lvalue(e),
    }
}

pub(crate) fn xtype_is_ptr_class(xt: &XType) -> bool {
    matches!(
        xt,
        XType::Xptr
            | XType::Xcharptr
            | XType::Xcharptrptr
            | XType::Xintptr
            | XType::Xfloatptr
            | XType::Xsingleptr
            | XType::Xfuncptr
            | XType::XstructPtr(_)
    )
}

/// True if a stored value carries a pointer (explicitly or implicitly via TR-3 ptr_regs, cast-wrapping, pointer arithmetic, or pointer-typed load/field). Mirror of solve.rs::clight_value_is_ptr.
pub(crate) fn clight_value_is_ptr(e: &ClightExpr, ptr_regs: &HashSet<RTLReg>) -> bool {
    match e {
        ClightExpr::Eaddrof(..) | ClightExpr::EvarSymbol(..) => true,
        ClightExpr::Etempvar(id, ct) => {
            matches!(ct, ClightType::Tpointer(..)) || ptr_regs.contains(&(*id as RTLReg))
        }
        ClightExpr::Evar(_, ct) => matches!(ct, ClightType::Tpointer(..)),
        ClightExpr::Ecast(inner, ct) => {
            matches!(ct, ClightType::Tpointer(..)) || clight_value_is_ptr(inner, ptr_regs)
        }
        // Pointer arithmetic: p+n propagates the pointer; p-q is a pointer only when rhs is not itself a pointer (pointer difference is an integer).
        ClightExpr::Ebinop(ClightBinaryOp::Oadd, l, r, _) => {
            clight_value_is_ptr(l, ptr_regs) || clight_value_is_ptr(r, ptr_regs)
        }
        ClightExpr::Ebinop(ClightBinaryOp::Osub, l, r, _) => {
            clight_value_is_ptr(l, ptr_regs) && !clight_value_is_ptr(r, ptr_regs)
        }
        ClightExpr::Ederef(_, ct) | ClightExpr::Efield(_, _, ct) => {
            matches!(ct, ClightType::Tpointer(..))
        }
        _ => false,
    }
}

/// Records (struct, field) keys with pointer evidence: a ptr-valued store in, out-flow to a ptr-selected register, or a ptr-typed callee param; an emission-side scan over SELECTED statements.
pub(crate) fn scan_field_ptr_evidence(
    stmt: &ClightStmt,
    ptr_regs: &HashSet<RTLReg>,
    callee_sigs: &HashMap<Ident, CalleeSignature>,
    name_to_ident: &HashMap<String, Ident>,
    out: &mut HashSet<(String, String)>,
) {
    match stmt {
        ClightStmt::Sassign(lhs, rhs) => {
            if clight_value_is_ptr(rhs, ptr_regs) {
                if let Some(key) = clight_field_key_of_lvalue(lhs) {
                    out.insert(key);
                }
            }
        }
        ClightStmt::Sset(id, e) => {
            // Out-flow: the field's value lands in a register selected as a pointer.
            if ptr_regs.contains(&(*id as RTLReg)) {
                if let Some(key) = clight_field_key_of_expr(e) {
                    out.insert(key);
                }
            }
        }
        ClightStmt::Scall(_, f, args) => {
            // Arg-flow: the field is passed where the callee expects a pointer.
            let callee = crate::decompile::passes::clight_select::select::callee_ident_from_expr(
                f,
                name_to_ident,
            );
            if let Some(sig) = callee.and_then(|id| callee_sigs.get(&id)) {
                for (i, a) in args.iter().enumerate() {
                    if let Some(pt) = sig.param_types.get(i) {
                        if xtype_is_ptr_class(pt) {
                            if let Some(key) = clight_field_key_of_expr(a) {
                                out.insert(key);
                            }
                        }
                    }
                }
            }
        }
        ClightStmt::Sifthenelse(_, a, b) | ClightStmt::Sloop(a, b) => {
            scan_field_ptr_evidence(a, ptr_regs, callee_sigs, name_to_ident, out);
            scan_field_ptr_evidence(b, ptr_regs, callee_sigs, name_to_ident, out);
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss {
                scan_field_ptr_evidence(s, ptr_regs, callee_sigs, name_to_ident, out);
            }
        }
        ClightStmt::Slabel(_, inner) => {
            scan_field_ptr_evidence(inner, ptr_regs, callee_sigs, name_to_ident, out)
        }
        ClightStmt::Sswitch(_, cases) => {
            for (_, s) in cases {
                scan_field_ptr_evidence(s, ptr_regs, callee_sigs, name_to_ident, out);
            }
        }
        _ => {}
    }
}

/// True when an expression is float-valued in the selected program.
fn clight_value_is_float(e: &ClightExpr, float_regs: &HashSet<RTLReg>) -> bool {
    match e {
        ClightExpr::EconstFloat(..) | ClightExpr::EconstSingle(..) => true,
        ClightExpr::Etempvar(id, ct) => {
            matches!(ct, ClightType::Tfloat(..)) || float_regs.contains(&(*id as RTLReg))
        }
        ClightExpr::Ecast(_, ct)
        | ClightExpr::Evar(_, ct)
        | ClightExpr::Ederef(_, ct)
        | ClightExpr::Efield(_, _, ct)
        | ClightExpr::Ebinop(_, _, _, ct)
        | ClightExpr::Eunop(_, _, ct)
        | ClightExpr::Econdition(_, _, _, ct) => matches!(ct, ClightType::Tfloat(..)),
        _ => false,
    }
}

/// Widens float_regs to a fixpoint for the TR-3 conflict veto: from_relations can refine a variable to double after solver selection, so a register may be float in the printed C without being float-SELECTED; the veto must account for this. Never use for positive pointer evidence.
pub(crate) fn widen_float_regs_by_defs<'a>(
    stmts: impl Iterator<Item = &'a ClightStmt> + Clone,
    float_regs: &mut HashSet<RTLReg>,
) {
    fn walk(s: &ClightStmt, float_regs: &mut HashSet<RTLReg>, grew: &mut bool) {
        match s {
            ClightStmt::Sset(id, e) => {
                let reg = *id as RTLReg;
                if !float_regs.contains(&reg) && clight_value_is_float(e, float_regs) {
                    float_regs.insert(reg);
                    *grew = true;
                }
            }
            ClightStmt::Ssequence(ss) => {
                for s in ss {
                    walk(s, float_regs, grew);
                }
            }
            ClightStmt::Sifthenelse(_, a, b) | ClightStmt::Sloop(a, b) => {
                walk(a, float_regs, grew);
                walk(b, float_regs, grew);
            }
            ClightStmt::Slabel(_, inner) => walk(inner, float_regs, grew),
            ClightStmt::Sswitch(_, cases) => {
                for (_, s) in cases {
                    walk(s, float_regs, grew);
                }
            }
            _ => {}
        }
    }
    loop {
        let mut grew = false;
        for s in stmts.clone() {
            walk(s, float_regs, &mut grew);
        }
        if !grew {
            break;
        }
    }
}

/// Widens ptr_regs to a fixpoint for the TR-3 veto only, counting retype-candidate fields as pointer-valued; never use for positive evidence, or a candidate field would justify itself.
pub(crate) fn widen_ptr_regs_by_defs<'a>(
    stmts: impl Iterator<Item = &'a ClightStmt> + Clone,
    ptr_regs: &mut HashSet<RTLReg>,
    evidenced: &HashSet<(String, String)>,
) {
    fn value_is_ptr_veto(
        e: &ClightExpr,
        regs: &HashSet<RTLReg>,
        evidenced: &HashSet<(String, String)>,
    ) -> bool {
        // A retype-candidate field load will become pointer-typed once patched.
        if let Some(k) = clight_field_key_of_expr(e) {
            if evidenced.contains(&k) {
                return true;
            }
        }
        // Remaining arms mirror clight_value_is_ptr with veto-aware recursion.
        match e {
            ClightExpr::Eaddrof(..) | ClightExpr::EvarSymbol(..) => true,
            ClightExpr::Etempvar(id, ct) => {
                matches!(ct, ClightType::Tpointer(..)) || regs.contains(&(*id as RTLReg))
            }
            ClightExpr::Evar(_, ct) => matches!(ct, ClightType::Tpointer(..)),
            ClightExpr::Ecast(inner, ct) => {
                matches!(ct, ClightType::Tpointer(..)) || value_is_ptr_veto(inner, regs, evidenced)
            }
            ClightExpr::Ebinop(ClightBinaryOp::Oadd, l, r, _) => {
                value_is_ptr_veto(l, regs, evidenced) || value_is_ptr_veto(r, regs, evidenced)
            }
            // Monotone transfer: over-veto p=a-b whenever a may be a pointer, since the non-monotone rhs term would make this fixpoint depend on HashMap order; over-vetoing keeps more fields long.
            ClightExpr::Ebinop(ClightBinaryOp::Osub, l, _, _) => {
                value_is_ptr_veto(l, regs, evidenced)
            }
            ClightExpr::Ederef(_, ct) | ClightExpr::Efield(_, _, ct) => {
                matches!(ct, ClightType::Tpointer(..))
            }
            _ => false,
        }
    }
    fn walk(
        s: &ClightStmt,
        ptr_regs: &mut HashSet<RTLReg>,
        evidenced: &HashSet<(String, String)>,
        grew: &mut bool,
    ) {
        match s {
            ClightStmt::Sset(id, e) => {
                let reg = *id as RTLReg;
                if !ptr_regs.contains(&reg) && value_is_ptr_veto(e, ptr_regs, evidenced) {
                    ptr_regs.insert(reg);
                    *grew = true;
                }
            }
            ClightStmt::Ssequence(ss) => {
                for s in ss {
                    walk(s, ptr_regs, evidenced, grew);
                }
            }
            ClightStmt::Sifthenelse(_, a, b) | ClightStmt::Sloop(a, b) => {
                walk(a, ptr_regs, evidenced, grew);
                walk(b, ptr_regs, evidenced, grew);
            }
            ClightStmt::Slabel(_, inner) => walk(inner, ptr_regs, evidenced, grew),
            ClightStmt::Sswitch(_, cases) => {
                for (_, s) in cases {
                    walk(s, ptr_regs, evidenced, grew);
                }
            }
            _ => {}
        }
    }
    loop {
        let mut grew = false;
        for s in stmts.clone() {
            walk(s, ptr_regs, evidenced, &mut grew);
        }
        if !grew {
            break;
        }
    }
}

/// Records (struct, field) keys whose usage contradicts a pointer retype (float context, or the field used as an integer offset); retyping a contested field moves the error rather than fixing it.
pub(crate) fn scan_field_ptr_conflicts(
    stmt: &ClightStmt,
    ptr_regs: &HashSet<RTLReg>,
    float_regs: &HashSet<RTLReg>,
    callee_sigs: &HashMap<Ident, CalleeSignature>,
    name_to_ident: &HashMap<String, Ident>,
    out: &mut HashSet<(String, String)>,
) {
    fn walk_expr(
        e: &ClightExpr,
        ptr_regs: &HashSet<RTLReg>,
        float_regs: &HashSet<RTLReg>,
        out: &mut HashSet<(String, String)>,
    ) {
        match e {
            ClightExpr::Ecast(inner, ct) => {
                if matches!(ct, ClightType::Tfloat(..)) {
                    if let Some(k) = clight_field_key_of_expr(inner) {
                        out.insert(k);
                    }
                }
                walk_expr(inner, ptr_regs, float_regs, out);
            }
            ClightExpr::Ebinop(op, l, r, _) => {
                let lk = clight_field_key_of_expr(l);
                let rk = clight_field_key_of_expr(r);
                // Field paired directly with a float operand: float context.
                if let Some(k) = &lk {
                    if clight_value_is_float(r, float_regs) {
                        out.insert(k.clone());
                    }
                }
                if let Some(k) = &rk {
                    if clight_value_is_float(l, float_regs) {
                        out.insert(k.clone());
                    }
                }
                if matches!(op, ClightBinaryOp::Oadd) {
                    // f1 + f2: pointers cannot be added -- both are integers.
                    if let (Some(k1), Some(k2)) = (&lk, &rk) {
                        out.insert(k1.clone());
                        out.insert(k2.clone());
                    }
                    // ptr + field: the field is the byte offset, an integer.
                    if let Some(k) = &lk {
                        if clight_value_is_ptr(r, ptr_regs) {
                            out.insert(k.clone());
                        }
                    }
                    if let Some(k) = &rk {
                        if clight_value_is_ptr(l, ptr_regs) {
                            out.insert(k.clone());
                        }
                    }
                }
                if matches!(op, ClightBinaryOp::Omul | ClightBinaryOp::Odiv) {
                    // field * scale and field / n reject pointers outright, so the field operand is a scaled count or index; only the multiplied operand is recorded, not an enclosing Oadd's pointer base.
                    if let Some(k) = &lk {
                        out.insert(k.clone());
                    }
                    if let Some(k) = &rk {
                        out.insert(k.clone());
                    }
                }
                walk_expr(l, ptr_regs, float_regs, out);
                walk_expr(r, ptr_regs, float_regs, out);
            }
            ClightExpr::Ederef(inner, _)
            | ClightExpr::Eaddrof(inner, _)
            | ClightExpr::Eunop(_, inner, _)
            | ClightExpr::Efield(inner, _, _) => walk_expr(inner, ptr_regs, float_regs, out),
            ClightExpr::Econdition(c, t, f, _) => {
                walk_expr(c, ptr_regs, float_regs, out);
                walk_expr(t, ptr_regs, float_regs, out);
                walk_expr(f, ptr_regs, float_regs, out);
            }
            _ => {}
        }
    }

    match stmt {
        ClightStmt::Sassign(lhs, rhs) => {
            if clight_value_is_float(rhs, float_regs) {
                if let Some(key) = clight_field_key_of_lvalue(lhs) {
                    out.insert(key);
                }
            }
            walk_expr(lhs, ptr_regs, float_regs, out);
            walk_expr(rhs, ptr_regs, float_regs, out);
        }
        ClightStmt::Sset(id, e) => {
            if float_regs.contains(&(*id as RTLReg)) {
                if let Some(key) = clight_field_key_of_expr(e) {
                    out.insert(key);
                }
            }
            walk_expr(e, ptr_regs, float_regs, out);
        }
        ClightStmt::Scall(_, f, args) => {
            let callee = crate::decompile::passes::clight_select::select::callee_ident_from_expr(
                f,
                name_to_ident,
            );
            let sig = callee.and_then(|id| callee_sigs.get(&id));
            for (i, a) in args.iter().enumerate() {
                if let Some(sig) = sig {
                    if let Some(pt) = sig.param_types.get(i) {
                        if matches!(pt, XType::Xfloat | XType::Xsingle) {
                            if let Some(key) = clight_field_key_of_expr(a) {
                                out.insert(key);
                            }
                        }
                    }
                }
                walk_expr(a, ptr_regs, float_regs, out);
            }
        }
        ClightStmt::Sifthenelse(c, a, b) => {
            walk_expr(c, ptr_regs, float_regs, out);
            scan_field_ptr_conflicts(a, ptr_regs, float_regs, callee_sigs, name_to_ident, out);
            scan_field_ptr_conflicts(b, ptr_regs, float_regs, callee_sigs, name_to_ident, out);
        }
        ClightStmt::Sloop(a, b) => {
            scan_field_ptr_conflicts(a, ptr_regs, float_regs, callee_sigs, name_to_ident, out);
            scan_field_ptr_conflicts(b, ptr_regs, float_regs, callee_sigs, name_to_ident, out);
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss {
                scan_field_ptr_conflicts(s, ptr_regs, float_regs, callee_sigs, name_to_ident, out);
            }
        }
        ClightStmt::Slabel(_, inner) => {
            scan_field_ptr_conflicts(inner, ptr_regs, float_regs, callee_sigs, name_to_ident, out)
        }
        ClightStmt::Sswitch(e, cases) => {
            walk_expr(e, ptr_regs, float_regs, out);
            for (_, s) in cases {
                scan_field_ptr_conflicts(s, ptr_regs, float_regs, callee_sigs, name_to_ident, out);
            }
        }
        ClightStmt::Sreturn(Some(e)) => walk_expr(e, ptr_regs, float_regs, out),
        _ => {}
    }
}

/// Default type string of a struct field, restricted to the retypeable class (64-bit non-pointer scalars); narrower fields can't hold a pointer on LP64 and already-pointer fields need no re-selection.
fn field_default_type_str(ty: &ClightType) -> Option<String> {
    match ty {
        ClightType::Tlong(ClightSignedness::Signed, _) => Some("long".to_string()),
        ClightType::Tlong(ClightSignedness::Unsigned, _) => Some("unsigned long".to_string()),
        ClightType::Tfloat(ClightFloatSize::F64, _) => Some("double".to_string()),
        _ => None,
    }
}

fn collect_field_defaults_expr(
    e: &ClightExpr,
    out: &mut BTreeMap<(String, String), BTreeSet<String>>,
) {
    if let ClightExpr::Efield(base, fid, fty) = e {
        if let ClightExpr::Ederef(_, ClightType::Tstruct(sid, _)) = base.as_ref() {
            if let Some(default) = field_default_type_str(fty) {
                let key = (
                    format!("struct_{:x}", sid),
                    crate::decompile::passes::csh_pass::field_ident_to_name(*fid),
                );
                out.entry(key).or_default().insert(default);
            }
        }
    }
    match e {
        ClightExpr::Ederef(inner, _)
        | ClightExpr::Eaddrof(inner, _)
        | ClightExpr::Ecast(inner, _)
        | ClightExpr::Eunop(_, inner, _)
        | ClightExpr::Efield(inner, _, _) => collect_field_defaults_expr(inner, out),
        ClightExpr::Ebinop(_, l, r, _) => {
            collect_field_defaults_expr(l, out);
            collect_field_defaults_expr(r, out);
        }
        ClightExpr::Econdition(c, t, f, _) => {
            collect_field_defaults_expr(c, out);
            collect_field_defaults_expr(t, out);
            collect_field_defaults_expr(f, out);
        }
        _ => {}
    }
}

fn collect_field_defaults_stmt(
    s: &ClightStmt,
    out: &mut BTreeMap<(String, String), BTreeSet<String>>,
) {
    match s {
        ClightStmt::Sassign(l, r) => {
            collect_field_defaults_expr(l, out);
            collect_field_defaults_expr(r, out);
        }
        ClightStmt::Sset(_, e) => collect_field_defaults_expr(e, out),
        ClightStmt::Scall(_, f, args) => {
            collect_field_defaults_expr(f, out);
            for a in args {
                collect_field_defaults_expr(a, out);
            }
        }
        ClightStmt::Sbuiltin(_, _, _, args) => {
            for a in args {
                collect_field_defaults_expr(a, out);
            }
        }
        ClightStmt::Ssequence(ss) => {
            for s in ss {
                collect_field_defaults_stmt(s, out);
            }
        }
        ClightStmt::Sifthenelse(c, a, b) => {
            collect_field_defaults_expr(c, out);
            collect_field_defaults_stmt(a, out);
            collect_field_defaults_stmt(b, out);
        }
        ClightStmt::Sloop(a, b) => {
            collect_field_defaults_stmt(a, out);
            collect_field_defaults_stmt(b, out);
        }
        ClightStmt::Sreturn(Some(e)) => collect_field_defaults_expr(e, out),
        ClightStmt::Sswitch(e, cases) => {
            collect_field_defaults_expr(e, out);
            for (_, st) in cases {
                collect_field_defaults_stmt(st, out);
            }
        }
        ClightStmt::Slabel(_, inner) => collect_field_defaults_stmt(inner, out),
        _ => {}
    }
}

/// True when the expression casts a value to a bare scalar float, looking THROUGH outer non-float casts, so the float/pointer brake catches both (double)v and (T*)(double)v.
fn expr_casts_to_bare_float(e: &ClightExpr) -> bool {
    match e {
        ClightExpr::Ecast(inner, ct) => {
            matches!(ct, ClightType::Tfloat(_, _)) || expr_casts_to_bare_float(inner)
        }
        _ => false,
    }
}

pub(crate) fn collect_struct_field_type_candidates<'a>(
    stmts: impl Iterator<Item = &'a ClightStmt>,
) -> HashMap<(String, String), Vec<String>> {
    let mut seen: BTreeMap<(String, String), BTreeSet<String>> = BTreeMap::new();
    for s in stmts {
        collect_field_defaults_stmt(s, &mut seen);
    }
    seen.into_iter()
        .map(|(key, defaults)| {
            let mut cands: Vec<String> = defaults.into_iter().collect();
            cands.push("void *".to_string());
            (key, cands)
        })
        .collect()
}

/// Pick rule for a pointer-evidenced field: prefer struct pointer, else first pointer candidate. Same rule applied inline by solve.rs::infer_select_program.
pub(crate) fn pick_field_ptr_candidate(cands: &[String]) -> Option<usize> {
    cands
        .iter()
        .position(|c| c.contains('*') && c.contains("struct"))
        .or_else(|| cands.iter().position(|c| c.contains('*')))
}

/// Parses a pointer candidate string ("void *" or "struct NAME *") back into a CType.
fn parse_field_type_candidate(s: &str) -> Option<CType> {
    if s == "void *" {
        return Some(CType::Pointer(
            Box::new(CType::Void),
            TypeQualifiers::none(),
        ));
    }
    if let Some(name) = s.strip_prefix("struct ").and_then(|r| r.strip_suffix(" *")) {
        return Some(CType::Pointer(
            Box::new(CType::Struct(name.to_string())),
            TypeQualifiers::none(),
        ));
    }
    None
}

/// Applies TR-3 field-type selection; only 8-byte scalar fields (long/ulong/double) may become pointers, preserving layout. Returns patch count. MANIFOLD_TR3_TRACE=1 logs each patch.
pub fn apply_struct_field_type_selection(
    structs: &mut [ExtractedStruct],
    selection: &HashMap<(String, String), String>,
) -> usize {
    if selection.is_empty() {
        return 0;
    }
    let trace = std::env::var("MANIFOLD_TR3_TRACE").is_ok();
    let mut patched = 0usize;
    for ex in structs.iter_mut() {
        let Some(sname) = ex.definition.name.clone() else {
            continue;
        };
        for field in ex.definition.fields.iter_mut() {
            let Some(fname) = field.name.clone() else {
                continue;
            };
            let Some(want) = selection.get(&(sname.clone(), fname)) else {
                continue;
            };
            // P5 decl solve: "long" forces an integer def onto a POINTER field whose every use is integer arithmetic (gcc proves the layout guess wrong) -- the inverse of the ptr patch below; 8-byte either way, layout preserved.
            if want == "long" {
                if matches!(field.ty, CType::Pointer(..)) {
                    if trace {
                        eprintln!(
                            "[clight-emit] decl-solve: field {}.{} forced {:?} -> long",
                            sname,
                            field.name.as_deref().unwrap_or("?"),
                            field.ty
                        );
                    }
                    field.ty = CType::long();
                    patched += 1;
                }
                continue;
            }
            let eligible = matches!(
                field.ty,
                CType::Int(IntSize::Long, _) | CType::Float(FloatSize::Double)
            );
            if !eligible {
                continue;
            }
            if let Some(new_ty) = parse_field_type_candidate(want) {
                if trace {
                    eprintln!(
                        "[clight-emit] TR3: field {}.{} retyped {:?} -> {}",
                        sname,
                        field.name.as_deref().unwrap_or("?"),
                        field.ty,
                        want
                    );
                }
                field.ty = new_ty;
                patched += 1;
            }
        }
    }
    patched
}

/// Collect all register IDs (from Etempvar) used in a statement.
pub fn collect_stmt_regs(stmt: &ClightStmt) -> Vec<RTLReg> {
    let mut regs = Vec::new();
    fn collect_expr_regs(expr: &ClightExpr, regs: &mut Vec<RTLReg>) {
        match expr {
            ClightExpr::Etempvar(id, _) => {
                let reg = *id as RTLReg;
                if !regs.contains(&reg) {
                    regs.push(reg);
                }
            }
            ClightExpr::Ederef(inner, _)
            | ClightExpr::Eaddrof(inner, _)
            | ClightExpr::Eunop(_, inner, _)
            | ClightExpr::Ecast(inner, _)
            | ClightExpr::Efield(inner, _, _) => collect_expr_regs(inner, regs),
            ClightExpr::Ebinop(_, lhs, rhs, _) => {
                collect_expr_regs(lhs, regs);
                collect_expr_regs(rhs, regs);
            }
            _ => {}
        }
    }
    fn collect_stmt_regs_inner(stmt: &ClightStmt, regs: &mut Vec<RTLReg>) {
        match stmt {
            ClightStmt::Sassign(lhs, rhs) => {
                collect_expr_regs(lhs, regs);
                collect_expr_regs(rhs, regs);
            }
            ClightStmt::Sset(id, expr) => {
                let r = *id as RTLReg;
                if !regs.contains(&r) {
                    regs.push(r);
                }
                collect_expr_regs(expr, regs);
            }
            ClightStmt::Scall(_, f, args) => {
                collect_expr_regs(f, regs);
                for a in args {
                    collect_expr_regs(a, regs);
                }
            }
            ClightStmt::Sreturn(Some(e)) => collect_expr_regs(e, regs),
            ClightStmt::Sifthenelse(c, t, e) => {
                collect_expr_regs(c, regs);
                collect_stmt_regs_inner(t, regs);
                collect_stmt_regs_inner(e, regs);
            }
            ClightStmt::Ssequence(ss) => {
                for s in ss {
                    collect_stmt_regs_inner(s, regs);
                }
            }
            ClightStmt::Sloop(a, b) => {
                collect_stmt_regs_inner(a, regs);
                collect_stmt_regs_inner(b, regs);
            }
            ClightStmt::Slabel(_, inner) => collect_stmt_regs_inner(inner, regs),
            ClightStmt::Sswitch(e, cases) => {
                collect_expr_regs(e, regs);
                for (_, s) in cases {
                    collect_stmt_regs_inner(s, regs);
                }
            }
            _ => {}
        }
    }
    collect_stmt_regs_inner(stmt, &mut regs);
    regs
}

#[cfg(test)]
mod sseq_tests {
    use super::*;

    #[test]
    fn reconstructs_nonmonotonic_ids_from_direct_edges() {
        let memberships = vec![(90, 70), (90, 90), (90, 10)];
        let edges = vec![(90, 10, 70), (90, 90, 10)];

        assert_eq!(
            reconstruct_sseq_groups(&memberships, &edges).get(&90),
            Some(&vec![90, 10, 70])
        );

        let mut reversed_memberships = memberships;
        reversed_memberships.reverse();
        let mut reversed_edges = edges;
        reversed_edges.reverse();
        assert_eq!(
            reconstruct_sseq_groups(&reversed_memberships, &reversed_edges).get(&90),
            Some(&vec![90, 10, 70]),
            "relation iteration order must not affect structural order"
        );
    }

    #[test]
    fn rejects_every_group_in_an_overlap() {
        let memberships = vec![(1, 1), (1, 2), (1, 3), (8, 8), (8, 2), (8, 9)];
        let edges = vec![(1, 1, 2), (1, 2, 3), (8, 8, 2), (8, 2, 9)];

        assert!(reconstruct_sseq_groups(&memberships, &edges).is_empty());
    }

    #[test]
    fn rejects_ambiguous_or_incomplete_edge_coverage() {
        let memberships = vec![(90, 90), (90, 10), (90, 70)];
        let branching = vec![(90, 90, 10), (90, 90, 70)];
        assert!(reconstruct_sseq_groups(&memberships, &branching).is_empty());

        let disconnected = vec![(90, 90, 10)];
        assert!(reconstruct_sseq_groups(&memberships, &disconnected).is_empty());
    }
}

#[cfg(test)]
mod relocated_pointer_tests {
    use super::*;

    #[test]
    fn pointer_initializer_targets_precede_sources_without_losing_globals() {
        let ids = vec![0x1000, 0x2000, 0x3000, 0x4000];
        let pointer_targets = BTreeMap::from([
            // Scalar source depends on a numerically later target.
            (0x1000, 0x3000),
            // The second word of a validated array belongs to its base.
            (0x2008, 0x4000),
        ]);
        let layouts = HashMap::from([(0x2000, vec![(8, 2)])]);

        let ordered = order_globals_for_pointer_initializers(
            &ids,
            &layouts,
            &pointer_targets,
            &HashMap::new(),
        );
        let position: HashMap<usize, usize> = ordered
            .iter()
            .enumerate()
            .map(|(index, &id)| (id, index))
            .collect();

        assert_eq!(ordered.len(), ids.len());
        assert_eq!(position.len(), ids.len());
        assert!(position[&0x3000] < position[&0x1000]);
        assert!(position[&0x4000] < position[&0x2000]);
    }

    #[test]
    fn cyclic_pointer_initializers_have_deterministic_lossless_order() {
        let ids = vec![0x3000, 0x1000, 0x2000];
        let pointer_targets = BTreeMap::from([(0x1000, 0x2000), (0x2000, 0x1000)]);

        let forward = order_globals_for_pointer_initializers(
            &ids,
            &HashMap::new(),
            &pointer_targets,
            &HashMap::new(),
        );
        let reversed = order_globals_for_pointer_initializers(
            &ids.iter().rev().copied().collect::<Vec<_>>(),
            &HashMap::new(),
            &pointer_targets,
            &HashMap::new(),
        );

        assert_eq!(forward, reversed);
        assert_eq!(forward, vec![0x3000, 0x1000, 0x2000]);
    }

    #[test]
    fn interior_pointer_dependency_is_owned_by_the_base_declaration() {
        let source = 0x1000_usize;
        let owner = 0x3000_usize;
        let interior = 0x3008_u64;
        let ids = vec![source, interior as usize, owner];
        let pointer_targets = BTreeMap::from([(source as u64, interior)]);
        let coordinates = HashMap::from([(
            interior,
            RelocationTargetCoordinate {
                owner: owner as u64,
                offset: 8,
            },
        )]);

        let ordered = order_globals_for_pointer_initializers(
            &ids,
            &HashMap::new(),
            &pointer_targets,
            &coordinates,
        );
        let position: HashMap<usize, usize> = ordered
            .iter()
            .enumerate()
            .map(|(index, &id)| (id, index))
            .collect();

        assert!(position[&owner] < position[&source]);
        assert_eq!(
            relocation_declaration_target(interior, &coordinates),
            owner as u64
        );

        use crate::decompile::passes::c_pass::types::{BinaryOp, CExpr, CType, UnaryOp};
        assert_eq!(
            relocation_target_coordinate_expr("global.words", coordinates[&interior]),
            CExpr::Binary(
                BinaryOp::Add,
                Box::new(CExpr::Cast(
                    CType::ptr(CType::char_unsigned()),
                    Box::new(CExpr::Unary(
                        UnaryOp::AddrOf,
                        Box::new(CExpr::Var("global_words".to_string())),
                    )),
                )),
                Box::new(CExpr::int(8)),
            ),
            "the interior offset must stay byte-scaled regardless of the owner's final type",
        );
    }

    #[test]
    fn unrelated_later_nonstring_relocation_cannot_erase_scalar_initializer() {
        let reloc_targets = BTreeMap::from([
            (0x1000, 0x2000),
            // This is the shape that the old first-later-relocation stride
            // heuristic incorrectly attached to the scalar at 0x1000.
            (0x1068, 0x3000),
        ]);

        let words = recover_relocated_pointer_words(
            0x1000,
            8,
            &[],
            Some(0x100),
            &reloc_targets,
            |target| target == 0x2000,
            |_, _| panic!("a scalar relocation must not scan later slots"),
        );

        assert_eq!(words, vec![RelocatedPointerWord::Target(0x2000)]);
    }

    #[test]
    fn validated_global_array_layout_recovers_complete_pointer_table() {
        let reloc_targets = BTreeMap::from([(0x1000, 0x2000), (0x1010, 0x2100)]);
        let raw_words = BTreeMap::from([(0x1008, 1), (0x1018, 0)]);

        let words = recover_relocated_pointer_words(
            0x1000,
            8,
            // Access-derived evidence may publish a shorter prefix alongside
            // the complete relocation-backed table layout.
            &[(16, 1), (16, 2)],
            Some(32),
            &reloc_targets,
            |target| matches!(target, 0x2000 | 0x2100),
            |slot, _| raw_words.get(&slot).copied(),
        );

        assert_eq!(
            words,
            vec![
                RelocatedPointerWord::Target(0x2000),
                RelocatedPointerWord::Raw(1),
                RelocatedPointerWord::Target(0x2100),
                RelocatedPointerWord::Raw(0),
            ]
        );

        let scalar = recover_relocated_pointer_words(
            0x1000,
            8,
            &[(16, 2)],
            Some(32),
            &reloc_targets,
            |target| target == 0x2000,
            |slot, _| raw_words.get(&slot).copied(),
        );
        assert_eq!(
            scalar,
            vec![RelocatedPointerWord::Target(0x2000)],
            "an unrepresentable aggregate target must not erase the safe scalar base"
        );
    }

    #[test]
    fn validated_global_array_layout_recovers_interior_relocation() {
        let reloc_targets = BTreeMap::from([(0x1008, 0x2000)]);
        let raw_words = BTreeMap::from([(0x1000, 11), (0x1010, 29)]);

        let words = recover_relocated_pointer_words(
            0x1000,
            8,
            &[(8, 3)],
            Some(24),
            &reloc_targets,
            |target| target == 0x2000,
            |slot, _| raw_words.get(&slot).copied(),
        );

        assert_eq!(
            words,
            vec![
                RelocatedPointerWord::Raw(11),
                RelocatedPointerWord::Target(0x2000),
                RelocatedPointerWord::Raw(29),
            ]
        );
    }

    #[test]
    fn raw_global_layout_without_relocation_is_not_reclassified() {
        let raw_words = BTreeMap::from([(0x1000, 11), (0x1008, 17), (0x1010, 29)]);

        let words = recover_relocated_pointer_words(
            0x1000,
            8,
            &[(8, 3)],
            Some(24),
            &BTreeMap::new(),
            |_| true,
            |slot, _| raw_words.get(&slot).copied(),
        );

        assert!(words.is_empty());
    }

    #[test]
    fn unrepresentable_interior_relocation_rejects_whole_layout() {
        let reloc_targets = BTreeMap::from([(0x1008, 0x2000)]);

        let words = recover_relocated_pointer_words(
            0x1000,
            8,
            &[(8, 3)],
            Some(24),
            &reloc_targets,
            |_| false,
            |_, _| Some(0),
        );

        assert!(words.is_empty());
    }

    #[test]
    fn named_but_later_target_falls_back_without_undeclared_reference() {
        let reloc_targets = BTreeMap::from([(0x1000, 0x2000), (0x1010, 0x2100)]);
        let named_targets = HashMap::from([(0x2100, "later_global".to_string())]);
        let named_globals_in_scope = HashSet::new();
        assert!(named_targets.contains_key(&0x2100));
        assert!(!relocation_target_is_representable(
            0x2100,
            0x1000,
            false,
            &named_targets,
            &named_globals_in_scope,
        ));

        let words = recover_relocated_pointer_words(
            0x1000,
            8,
            &[(16, 2)],
            Some(32),
            &reloc_targets,
            |target| {
                relocation_target_is_representable(
                    target,
                    0x1000,
                    target == 0x2000,
                    &named_targets,
                    &named_globals_in_scope,
                )
            },
            |_, _| Some(0),
        );

        assert_eq!(
            words,
            vec![RelocatedPointerWord::Target(0x2000)],
            "the later name must not enter an initializer before its declaration"
        );
    }

    #[test]
    fn recovered_function_target_is_representable_before_global_definitions() {
        let function = 0x2000;
        let named_targets = HashMap::from([(function, "FUN_2000".to_string())]);
        let names_in_scope = HashSet::from([function]);

        assert!(relocation_target_is_representable(
            function,
            0x1000,
            false,
            &named_targets,
            &names_in_scope,
        ));
    }

    #[test]
    fn code_pointer_run_stops_at_a_gap_or_separate_object() {
        let slots = BTreeSet::from([0x1000, 0x1008, 0x1010, 0x1020]);
        assert_eq!(
            consecutive_pointer_run(0x1000, 8, &slots, &HashSet::from([0x1000])),
            3
        );
        assert_eq!(
            consecutive_pointer_run(0x1000, 8, &slots, &HashSet::from([0x1000, 0x1010]),),
            2
        );
        assert_eq!(
            consecutive_pointer_run(0x1020, 8, &slots, &HashSet::new()),
            1
        );
    }
}

#[cfg(test)]
mod loop_info_tests {
    use super::*;
    use crate::x86::op::Comparison;

    const FUNC: Address = 0x1000;
    const HEADER: Node = 0x1010;

    fn condition() -> Condition {
        Condition::Ccompimm(Comparison::Ceq, 0)
    }

    fn add_exit(db: &mut DecompileDB, exit_node: Node, exit_target: Node) {
        let args = Arc::new(Vec::<CsharpminorExpr>::new());
        db.rel_push(
            "emit_loop_exit",
            (
                FUNC,
                HEADER,
                exit_node,
                condition(),
                args,
                exit_target,
                HEADER,
            ),
        );
    }

    #[test]
    fn ambiguous_primary_exit_nodes_decline_specialization_in_any_order() {
        for exits in [
            [(0x1020, 0x2000), (0x1030, 0x3000)],
            [(0x1030, 0x3000), (0x1020, 0x2000)],
        ] {
            let mut db = DecompileDB::default();
            for (exit_node, exit_target) in exits {
                add_exit(&mut db, exit_node, exit_target);
                db.rel_push("primary_exit_node", (FUNC, HEADER, exit_node));
            }

            let loops = extract_loop_info(&db);
            let info = loops.get(&FUNC).unwrap().get(&HEADER).unwrap();
            assert!(
                info.primary_exit.is_none(),
                "multiple physical exits must not be selected by node id"
            );
        }
    }

    #[test]
    fn ambiguous_primary_exit_targets_decline_specialization() {
        let exit_node = 0x1020;
        let mut db = DecompileDB::default();
        add_exit(&mut db, exit_node, 0x2000);
        add_exit(&mut db, exit_node, 0x3000);
        db.rel_push("primary_exit_node", (FUNC, HEADER, exit_node));

        let loops = extract_loop_info(&db);
        assert!(
            loops
                .get(&FUNC)
                .unwrap()
                .get(&HEADER)
                .unwrap()
                .primary_exit
                .is_none(),
            "conflicting outside targets must not be selected by node id"
        );
    }

    #[test]
    fn ambiguous_return_tails_decline_specialization_in_any_order() {
        let exit_node = 0x1020;
        let tail_orders: [[(Node, Node); 2]; 2] = [
            [(0x2000, 0x2010), (0x3000, 0x3010)],
            [(0x3000, 0x3010), (0x2000, 0x2010)],
        ];
        for tails in tail_orders {
            let mut db = DecompileDB::default();
            add_exit(&mut db, exit_node, 0x2000);
            for (value_node, return_node) in tails {
                db.rel_push(
                    "loop_exit_to_return",
                    (FUNC, HEADER, exit_node, value_node, return_node),
                );
            }

            let loops = extract_loop_info(&db);
            let info = loops.get(&FUNC).unwrap().get(&HEADER).unwrap();
            assert!(
                !info.exit_returns.contains_key(&exit_node),
                "ambiguous return tails must retain flat control flow"
            );
        }
    }

    #[test]
    fn unique_return_tail_remains_available() {
        let exit_node = 0x1020;
        let mut db = DecompileDB::default();
        add_exit(&mut db, exit_node, 0x2000);
        db.rel_push(
            "loop_exit_to_return",
            (FUNC, HEADER, exit_node, 0x2000 as Node, 0x2010 as Node),
        );

        let loops = extract_loop_info(&db);
        assert_eq!(
            loops
                .get(&FUNC)
                .unwrap()
                .get(&HEADER)
                .unwrap()
                .exit_returns
                .get(&exit_node),
            Some(&(0x2000, 0x2010))
        );
    }
}

#[cfg(test)]
mod tr3_tests {
    use super::*;

    fn tlong() -> ClightType {
        ClightType::Tlong(ClightSignedness::Signed, ClightAttr::default())
    }
    fn tstruct(sid: usize) -> ClightType {
        ClightType::Tstruct(sid, ClightAttr::default())
    }
    fn field_store(sid: usize, ofs: i64, fty: ClightType, rhs: ClightExpr) -> ClightStmt {
        ClightStmt::Sassign(
            ClightExpr::Efield(
                Box::new(ClightExpr::Ederef(
                    Box::new(ClightExpr::Etempvar(1, tlong())),
                    tstruct(sid),
                )),
                ofs as Ident,
                fty,
            ),
            rhs,
        )
    }

    #[test]
    fn pick_prefers_struct_ptr_then_any_ptr() {
        let cands = vec!["long".to_string(), "void *".to_string()];
        assert_eq!(pick_field_ptr_candidate(&cands), Some(1));
        let cands = vec![
            "long".to_string(),
            "void *".to_string(),
            "struct struct_7 *".to_string(),
        ];
        assert_eq!(pick_field_ptr_candidate(&cands), Some(2));
        let cands = vec!["long".to_string(), "double".to_string()];
        assert_eq!(pick_field_ptr_candidate(&cands), None);
    }

    #[test]
    fn parse_candidate_roundtrip() {
        assert_eq!(
            parse_field_type_candidate("void *"),
            Some(CType::Pointer(
                Box::new(CType::Void),
                TypeQualifiers::none()
            ))
        );
        assert_eq!(
            parse_field_type_candidate("struct struct_7 *"),
            Some(CType::Pointer(
                Box::new(CType::Struct("struct_7".to_string())),
                TypeQualifiers::none()
            ))
        );
        assert_eq!(parse_field_type_candidate("long"), None);
    }

    #[test]
    fn collect_only_64bit_scalar_fields() {
        // long field at offset 8 of struct 1: eligible.
        let s1 = field_store(1, 8, tlong(), ClightExpr::Etempvar(2, tlong()));
        // int field: not eligible (a pointer cannot fit).
        let s2 = field_store(
            1,
            0,
            ClightType::Tint(
                ClightIntSize::I32,
                ClightSignedness::Signed,
                ClightAttr::default(),
            ),
            ClightExpr::Etempvar(2, tlong()),
        );
        // already-pointer field: no re-selection needed.
        let s3 = field_store(
            2,
            0,
            ClightType::Tpointer(Arc::new(ClightType::Tvoid), ClightAttr::default()),
            ClightExpr::Etempvar(2, tlong()),
        );
        let stmts = vec![s1, s2, s3];
        let cands = collect_struct_field_type_candidates(stmts.iter());
        assert_eq!(cands.len(), 1);
        let c = cands
            .get(&("struct_1".to_string(), "ofs_8".to_string()))
            .unwrap();
        assert_eq!(c[0], "long");
        assert_eq!(c.last().unwrap(), "void *");
    }

    #[test]
    fn evidence_from_ptr_selected_reg_store_and_outflow() {
        let mut ptr_regs: HashSet<RTLReg> = HashSet::new();
        ptr_regs.insert(7);
        let sigs: HashMap<Ident, CalleeSignature> = HashMap::new();
        let names: HashMap<String, Ident> = HashMap::new();
        let mut out: HashSet<(String, String)> = HashSet::new();

        // In-flow: ptr-selected reg 7 stored into struct_1.ofs_8 (plain long types).
        let store = field_store(1, 8, tlong(), ClightExpr::Etempvar(7, tlong()));
        scan_field_ptr_evidence(&store, &ptr_regs, &sigs, &names, &mut out);
        assert!(out.contains(&("struct_1".to_string(), "ofs_8".to_string())));

        // Out-flow: field value lands in ptr-selected reg 7.
        let load = ClightStmt::Sset(
            7,
            ClightExpr::Efield(
                Box::new(ClightExpr::Ederef(
                    Box::new(ClightExpr::Etempvar(1, tlong())),
                    tstruct(3),
                )),
                8 as Ident,
                tlong(),
            ),
        );
        scan_field_ptr_evidence(&load, &ptr_regs, &sigs, &names, &mut out);
        assert!(out.contains(&("struct_3".to_string(), "ofs_8".to_string())));

        // Non-pointer store: no evidence.
        let mut out2: HashSet<(String, String)> = HashSet::new();
        let store_int = field_store(5, 0, tlong(), ClightExpr::Etempvar(9, tlong()));
        scan_field_ptr_evidence(&store_int, &ptr_regs, &sigs, &names, &mut out2);
        assert!(out2.is_empty());
    }

    #[test]
    fn apply_patches_only_8byte_scalars() {
        let selection: HashMap<(String, String), String> = [
            (
                ("struct_1".to_string(), "ofs_8".to_string()),
                "void *".to_string(),
            ),
            (
                ("struct_1".to_string(), "ofs_0".to_string()),
                "void *".to_string(),
            ),
        ]
        .into_iter()
        .collect();
        let def = StructDef::new_struct(
            "struct_1",
            vec![
                StructField::new("ofs_0", CType::Int(IntSize::Int, Signedness::Signed)),
                StructField::new("ofs_8", CType::Int(IntSize::Long, Signedness::Signed)),
            ],
        );
        let mut structs = vec![ExtractedStruct {
            struct_id: 1,
            layout_hash: 0,
            is_canonical: true,
            definition: def,
        }];
        let patched = apply_struct_field_type_selection(&mut structs, &selection);
        assert_eq!(patched, 1, "only the 8-byte field may be retyped");
        assert_eq!(
            structs[0].definition.fields[1].ty,
            CType::Pointer(Box::new(CType::Void), TypeQualifiers::none())
        );
        // 4-byte field untouched (layout preserved).
        assert_eq!(
            structs[0].definition.fields[0].ty,
            CType::Int(IntSize::Int, Signedness::Signed)
        );
    }
}

#[cfg(test)]
mod known_global_tests {
    use super::*;

    #[test]
    fn joins_authoritative_global_types_to_clight_idents() {
        let mut db = DecompileDB::default();
        db.rel_push("known_global_type", ("optarg", XType::Xcharptr));
        db.rel_push("known_global_type", ("stdout", XType::Xptr));
        db.rel_push("global_symbol", (0x28200u64, "optarg@GLIBC_2.2.5"));
        db.rel_push("global_symbol", (0x28300u64, "stdout@GLIBC_2.2.5"));
        // These broad aliases are deliberately not needed for the join.
        db.rel_push("ident_to_symbol", (0x28200usize, "optarg"));
        db.rel_push("symbols", (0x28300u64, "stdout", "stdout"));

        let known = extract_known_global_types(&db);
        assert!(matches!(
            known.by_ident.get(&0x28200),
            Some(ClightType::Tpointer(inner, _))
                if matches!(inner.as_ref(), ClightType::Tint(ClightIntSize::I8, ..))
        ));
        assert!(matches!(
            known.by_ident.get(&0x28300),
            Some(ClightType::Tpointer(inner, _))
                if matches!(inner.as_ref(), ClightType::Tvoid)
        ));
    }

    #[test]
    fn recovered_char_pointer_matches_the_emitted_object_declaration() {
        let mut db = DecompileDB::default();
        db.rel_push("global_symbol", (0x28438u64, "L_28438"));
        db.rel_push("emit_global_is_ptr", (0x28438usize,));
        db.rel_push("emit_global_is_char_ptr", (0x28438usize,));

        let known = extract_known_global_types(&db);
        assert!(matches!(
            known.by_ident.get(&0x28438),
            Some(ClightType::Tpointer(inner, _))
                if matches!(inner.as_ref(), ClightType::Tint(ClightIntSize::I8, ..))
        ));
    }

    #[test]
    fn header_variable_type_has_final_emitter_precedence() {
        let mut db = DecompileDB::default();
        db.rel_push("global_symbol", (0x28500u64, "environ@GLIBC_2.2.5"));
        // Deliberately conflicting lower-precedence facts: the emitter's
        // header table must still make this object char **.
        db.rel_push("known_global_type", ("environ", XType::Xint));
        db.rel_push("emit_global_is_ptr", (0x28500usize,));

        let known = extract_known_global_types(&db);
        assert!(matches!(
            known.by_ident.get(&0x28500),
            Some(ClightType::Tpointer(inner, _))
                if matches!(
                    inner.as_ref(),
                    ClightType::Tpointer(char_inner, _)
                        if matches!(
                            char_inner.as_ref(),
                            ClightType::Tint(ClightIntSize::I8, ..)
                        )
                )
        ));
    }

    #[test]
    fn function_symbol_is_not_typed_as_a_known_global_object() {
        let mut db = DecompileDB::default();
        db.rel_push("known_global_type", ("__ctype_b_loc", XType::Xptr));
        db.rel_push("ident_to_symbol", (0x401000usize, "__ctype_b_loc"));
        db.rel_push("symbols", (0x401000u64, "__ctype_b_loc", "__ctype_b_loc"));
        db.rel_push("emit_global_is_char_ptr", (0x401000usize,));

        let known = extract_known_global_types(&db);
        assert!(!known.by_ident.contains_key(&0x401000));
    }

    /// The two priority tables must agree wherever the candidate spelling is injective. `Xany32`
    /// and `Xany64` are width-only placeholders that share a spelling with their concrete sibling,
    /// so only `xtype_priority` can rank them lower; that is asserted separately rather than left
    /// as an unexplained gap.
    #[test]
    fn xtype_priority_agrees_with_candidate_priority() {
        use crate::decompile::passes::clight_select::candtype::CandType;
        use strum::IntoEnumIterator;

        let placeholders = [XType::Xany32, XType::Xany64];
        for xtype in XType::iter() {
            if placeholders.contains(&xtype) {
                continue;
            }
            assert_eq!(
                xtype_priority(&xtype),
                CandType::from_xtype(&xtype).priority(),
                "priority tables disagree for {:?}",
                xtype
            );
        }
        assert!(xtype_priority(&XType::Xany32) < xtype_priority(&XType::Xint));
        assert!(xtype_priority(&XType::Xany64) < xtype_priority(&XType::Xlong));
        // Both placeholders share their sibling's spelling, so the candidate domain cannot see the
        // difference; that is exactly why the two tables stay separate.
        assert_eq!(
            CandType::from_xtype(&XType::Xany32),
            CandType::from_xtype(&XType::Xint)
        );
        assert_eq!(
            CandType::from_xtype(&XType::Xany64),
            CandType::from_xtype(&XType::Xlong)
        );
    }
}
