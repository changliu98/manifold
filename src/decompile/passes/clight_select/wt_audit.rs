//! Read-only wt audit (P2): run the ctyping checker over each function's SELECTED statements and decl types and report diagnoses on stderr; behavior-neutral, gated by MANIFOLD_WT_AUDIT.

use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use crate::decompile::passes::clight_select::candtype::{CandType, Sign as CandSign};
use crate::decompile::passes::clight_select::ctyping::{self, Severity, WtEnv, WtError};
use crate::decompile::passes::clight_select::query::{FunctionData, KnownGlobalTypes};
use crate::decompile::passes::clight_select::select::{callee_ident_from_expr, SelectedFunction};
use crate::x86::types::{
    CallConv, ClightAttr, ClightExpr, ClightFloatSize, ClightIntSize, ClightSignedness, ClightType,
    Ident, MemoryChunk, Node, ParamType, XType,
};

use ClightFloatSize::{F32, F64};
use ClightIntSize::{IBool, I16, I32, I8};
use ClightSignedness::{Signed, Unsigned};

fn a() -> ClightAttr {
    ClightAttr::default()
}

fn tptr(t: ClightType) -> ClightType {
    ClightType::Tpointer(Arc::new(t), a())
}

/// `ptr_func` / Xfuncptr stand-ins print as unprototyped function pointers, so calls through them must skip arity/argument checks.
fn unproto_fn() -> ClightType {
    ClightType::Tfunction(
        Arc::new(Vec::new()),
        Arc::new(ClightType::Tvoid),
        CallConv {
            varargs: None,
            unproto: true,
            structured_ret: false,
        },
    )
}

/// Candidate type -> ClightType; the declaration type gcc will see. Total, with no fallback arm:
/// the string match this replaced had none for `ptr_ptr_char`, so a `char **` register was
/// type-checked as `long`.
pub(crate) fn candtype_to_clight(candidate: CandType) -> ClightType {
    use ClightType::*;
    let signedness = |sign: CandSign| match sign {
        CandSign::Signed => Signed,
        CandSign::Unsigned => Unsigned,
    };
    match candidate {
        CandType::Void => Tvoid,
        CandType::Bool => Tint(IBool, Signed, a()),
        CandType::I8(sign) => Tint(I8, signedness(sign), a()),
        CandType::I16(sign) => Tint(I16, signedness(sign), a()),
        CandType::I32(sign) => Tint(I32, signedness(sign), a()),
        CandType::I64(sign) => Tlong(signedness(sign), a()),
        CandType::F32 => Tfloat(F32, a()),
        CandType::F64 => Tfloat(F64, a()),
        CandType::PtrLong => tptr(Tlong(Signed, a())),
        CandType::PtrVoid => tptr(Tvoid),
        CandType::PtrChar => tptr(Tint(I8, Signed, a())),
        CandType::PtrCharPtr => tptr(tptr(Tint(I8, Signed, a()))),
        CandType::PtrInt => tptr(Tint(I32, Signed, a())),
        CandType::PtrDouble => tptr(Tfloat(F64, a())),
        CandType::PtrFloat => tptr(Tfloat(F32, a())),
        CandType::PtrFunc => tptr(unproto_fn()),
        CandType::PtrStruct(sid) => tptr(Tstruct(sid, a())),
    }
}

/// XType -> ClightType; mirrors the Typed(..) arm of convert_param_type_from_param.
pub(crate) fn xtype_to_clight(xt: &XType) -> ClightType {
    use ClightType::*;
    match xt {
        XType::Xvoid => Tvoid,
        XType::Xbool => Tint(IBool, Signed, a()),
        XType::Xint8signed => Tint(I8, Signed, a()),
        XType::Xint8unsigned => Tint(I8, Unsigned, a()),
        XType::Xint16signed => Tint(I16, Signed, a()),
        XType::Xint16unsigned => Tint(I16, Unsigned, a()),
        XType::Xint | XType::Xany32 => Tint(I32, Signed, a()),
        XType::Xintunsigned => Tint(I32, Unsigned, a()),
        XType::Xlong | XType::Xany64 => Tlong(Signed, a()),
        XType::Xlongunsigned => Tlong(Unsigned, a()),
        XType::Xfloat => Tfloat(F64, a()),
        XType::Xsingle => Tfloat(F32, a()),
        XType::Xptr => tptr(Tvoid),
        XType::Xcharptr => tptr(Tint(I8, Signed, a())),
        XType::Xcharptrptr => tptr(tptr(Tint(I8, Signed, a()))),
        XType::Xintptr => tptr(Tint(I32, Signed, a())),
        XType::Xfloatptr => tptr(Tfloat(F64, a())),
        XType::Xsingleptr => tptr(Tfloat(F32, a())),
        XType::Xfuncptr => tptr(unproto_fn()),
        XType::XstructPtr(sid) => tptr(Tstruct(*sid, a())),
    }
}

/// ParamType -> ClightType; mirrors convert_param_type_from_param.
pub(crate) fn param_type_to_clight(p: &ParamType) -> ClightType {
    use ClightType::*;
    match p {
        ParamType::StructPointer(sid) => tptr(Tstruct(*sid, a())),
        ParamType::Pointer => tptr(Tvoid),
        ParamType::Typed(xt) => xtype_to_clight(xt),
        ParamType::Integer | ParamType::Unknown => Tint(I32, Signed, a()),
    }
}

fn chunk_to_clight(c: &MemoryChunk) -> ClightType {
    use ClightType::*;
    match c {
        MemoryChunk::MBool => Tint(IBool, Signed, a()),
        MemoryChunk::MInt8Signed => Tint(I8, Signed, a()),
        MemoryChunk::MInt8Unsigned => Tint(I8, Unsigned, a()),
        MemoryChunk::MInt16Signed => Tint(I16, Signed, a()),
        MemoryChunk::MInt16Unsigned => Tint(I16, Unsigned, a()),
        MemoryChunk::MInt32 => Tint(I32, Signed, a()),
        MemoryChunk::MInt64 => Tlong(Signed, a()),
        MemoryChunk::MFloat32 => Tfloat(F32, a()),
        MemoryChunk::MFloat64 => Tfloat(F64, a()),
        MemoryChunk::MAny32 => Tint(I32, Signed, a()),
        MemoryChunk::MAny64 | MemoryChunk::Unknown => Tlong(Signed, a()),
    }
}

/// Composite-field env from FunctionData/SelectedFunction struct_fields (shared by the P2 audit and the P3 re-pick scorer).
pub(crate) fn fields_from_struct_fields(
    struct_fields: &HashMap<i64, Vec<(i64, Ident, MemoryChunk)>>,
) -> (
    HashMap<(Ident, Ident), ClightType>,
    std::collections::HashSet<Ident>,
) {
    let mut fields: HashMap<(Ident, Ident), ClightType> = HashMap::new();
    let mut known = std::collections::HashSet::new();
    for (sid, flist) in struct_fields {
        let sid = *sid as Ident;
        known.insert(sid);
        for (_, fid, chunk) in flist {
            fields.insert((sid, *fid), chunk_to_clight(chunk));
        }
    }
    (fields, known)
}

pub(crate) struct AuditEnv<'a> {
    temps: HashMap<Ident, ClightType>,
    fields: HashMap<(Ident, Ident), ClightType>,
    known_composites: std::collections::HashSet<Ident>,
    ret: ClightType,
    callee_sigs:
        &'a HashMap<Ident, crate::decompile::passes::clight_select::query::CalleeSignature>,
    name_to_ident: &'a HashMap<String, Ident>,
    known_global_types: &'a KnownGlobalTypes,
    ptr64: bool,
}

impl<'a> AuditEnv<'a> {
    /// Assemble from prepared parts (the P3 re-pick path: temps rendered from the z3 model rather than from selected candidate strings).
    pub(crate) fn from_parts(
        temps: HashMap<Ident, ClightType>,
        fields: HashMap<(Ident, Ident), ClightType>,
        known_composites: std::collections::HashSet<Ident>,
        ret: ClightType,
        callee_sigs: &'a HashMap<
            Ident,
            crate::decompile::passes::clight_select::query::CalleeSignature,
        >,
        name_to_ident: &'a HashMap<String, Ident>,
        known_global_types: &'a KnownGlobalTypes,
        ptr64: bool,
    ) -> Self {
        AuditEnv {
            temps,
            fields,
            known_composites,
            ret,
            callee_sigs,
            name_to_ident,
            known_global_types,
            ptr64,
        }
    }

    fn build(
        func: &'a FunctionData,
        sel: &SelectedFunction,
        name_to_ident: &'a HashMap<String, Ident>,
    ) -> Self {
        let mut temps: HashMap<Ident, ClightType> = HashMap::new();
        // Selected decl types: candidates[var_decl_idx (default 0)], var_types fallback -- exactly the from_relations seeding (from_relations.rs:834).
        for (reg, cands) in &sel.var_type_candidates {
            let idx = sel.var_decl_idx.get(reg).copied().unwrap_or(0);
            if let Some(&candidate) = cands.get(idx).or_else(|| sel.var_types.get(reg)) {
                temps.insert(*reg as Ident, candtype_to_clight(candidate));
            }
        }
        for (reg, &candidate) in &sel.var_types {
            temps
                .entry(*reg as Ident)
                .or_insert_with(|| candtype_to_clight(candidate));
        }
        // Params: the decl comes from the param type, except a bare `long` param decl yields to the selected local type (from_relations.rs:847).
        for (reg, pt) in sel.param_regs.iter().zip(sel.param_types.iter()) {
            let pty = param_type_to_clight(pt);
            match temps.get(&(*reg as Ident)) {
                Some(_) if matches!(pty, ClightType::Tlong(Signed, _)) => {}
                _ => {
                    temps.insert(*reg as Ident, pty);
                }
            }
        }

        let (fields, known) = fields_from_struct_fields(&sel.struct_fields);

        AuditEnv {
            temps,
            fields,
            known_composites: known,
            ret: sel.return_type.clone(),
            callee_sigs: &func.callee_signatures,
            name_to_ident,
            known_global_types: func.known_global_types.as_ref(),
            ptr64: func.ptr64,
        }
    }
}

impl WtEnv for AuditEnv<'_> {
    fn temp_type(&self, id: Ident) -> Option<ClightType> {
        self.temps.get(&id).cloned()
    }
    fn field_type(&self, sid: Ident, field: Ident) -> Option<ClightType> {
        self.fields.get(&(sid, field)).cloned()
    }
    fn composite_known(&self, sid: Ident) -> bool {
        self.known_composites.contains(&sid)
    }
    fn callee_type(&self, callee: &ClightExpr) -> Option<ClightType> {
        // Known signature -> a function type. varargs carries the fixed-arg count only for variadic callees (printf-shaped: extra args allowed); non-variadic callees get None so ArityTooMany fires on extra args. too-FEW stays meaningful either way.
        let id = callee_ident_from_expr(callee, self.name_to_ident)?;
        let sig = self.callee_sigs.get(&id)?;
        let params: Vec<ClightType> = sig.param_types.iter().map(xtype_to_clight).collect();
        Some(ClightType::Tfunction(
            Arc::new(params),
            Arc::new(xtype_to_clight(&sig.return_type)),
            CallConv {
                varargs: sig.is_varargs.then_some(sig.param_count as i64),
                unproto: false,
                structured_ret: false,
            },
        ))
    }
    fn global_ident_type(&self, id: Ident) -> Option<ClightType> {
        self.known_global_types.by_ident.get(&id).cloned()
    }
    fn return_type(&self) -> ClightType {
        self.ret.clone()
    }
    fn ptr64(&self) -> bool {
        self.ptr64
    }
}

/// Run the audit over the whole selection; prints one deterministic summary line always, per-function detail behind MANIFOLD_WT_AUDIT.
pub(crate) fn wt_audit(
    functions: &[FunctionData],
    selected: &[SelectedFunction],
    name_to_ident: &HashMap<String, Ident>,
) {
    let detail = std::env::var("MANIFOLD_WT_AUDIT").unwrap_or_default();
    let want_detail = |name: &str| -> bool {
        match detail.as_str() {
            "" => false,
            "1" | "true" => true,
            pat => name.contains(pat),
        }
    };

    let mut fam_counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut total_errors = 0usize;
    let mut total_warnings = 0usize;
    let mut funcs_with_errors = 0usize;

    for (func, sel) in functions.iter().zip(selected.iter()) {
        let env = AuditEnv::build(func, sel, name_to_ident);
        let mut nodes: Vec<Node> = sel.statements.keys().copied().collect();
        nodes.sort_unstable();

        let mut fn_errs: Vec<(Node, WtError)> = Vec::new();
        for node in nodes {
            let stmt = &sel.statements[&node];
            for e in ctyping::wt_check_stmt(stmt, &env) {
                fn_errs.push((node, e));
            }
        }

        let n_err = fn_errs
            .iter()
            .filter(|(_, e)| e.severity == Severity::Error)
            .count();
        let n_warn = fn_errs.len() - n_err;
        total_errors += n_err;
        total_warnings += n_warn;
        if n_err > 0 {
            funcs_with_errors += 1;
        }
        for (_, e) in &fn_errs {
            if e.severity == Severity::Error {
                *fam_counts.entry(e.kind.gcc_family()).or_default() += 1;
            }
        }

        if (n_err > 0 || n_warn > 0) && want_detail(&sel.name) {
            eprintln!(
                "[wt-audit] fn {} ({:#x}): {} errors, {} warnings",
                sel.name, sel.address, n_err, n_warn
            );
            for (node, e) in &fn_errs {
                let tag = match e.severity {
                    Severity::Error => "",
                    Severity::Warning => " (warn)",
                };
                eprintln!(
                    "[wt-audit]   node {:#x}: {}{}: {}",
                    node,
                    e.kind.gcc_family(),
                    tag,
                    e.detail
                );
            }
        }
    }

    // Count-desc, then name: stable and reads like the eval family table.
    let mut fams: Vec<(&'static str, usize)> = fam_counts.into_iter().collect();
    fams.sort_by_key(|(name, n)| (std::cmp::Reverse(*n), *name));
    let fam_str = fams
        .iter()
        .map(|(name, n)| format!("{}={}", name, n))
        .collect::<Vec<_>>()
        .join(" ");
    eprintln!(
        "[wt-audit] funcs={} with_errors={} errors={} warnings={} | {}",
        selected.len(),
        funcs_with_errors,
        total_errors,
        total_warnings,
        fam_str
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::x86::types::ClightStmt;

    #[test]
    fn symbolic_function_designator_ignores_same_named_object_type() {
        let object_ident = 0x5000usize;
        let object_types = KnownGlobalTypes {
            by_ident: [(object_ident, tptr(ClightType::Tvoid))]
                .into_iter()
                .collect(),
            ..KnownGlobalTypes::default()
        };
        // Deliberately map the symbolic spelling to the object ident. Object
        // typing is address-keyed and must still not override EvarSymbol.
        let name_to_ident = [("same_name".to_string(), object_ident)]
            .into_iter()
            .collect();
        let callee_sigs = HashMap::new();
        let env = AuditEnv::from_parts(
            HashMap::new(),
            HashMap::new(),
            std::collections::HashSet::new(),
            ClightType::Tvoid,
            &callee_sigs,
            &name_to_ident,
            &object_types,
            true,
        );
        let function_type = ClightType::Tfunction(
            Arc::new(Vec::new()),
            Arc::new(ClightType::Tvoid),
            CallConv {
                varargs: None,
                unproto: true,
                structured_ret: false,
            },
        );
        let call = ClightStmt::Scall(
            None,
            ClightExpr::EvarSymbol("same_name".to_string(), function_type),
            Vec::new(),
        );

        assert!(ctyping::wt_check_stmt(&call, &env).is_empty());
    }
}
