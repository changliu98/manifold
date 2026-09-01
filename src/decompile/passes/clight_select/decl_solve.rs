//! Post-selection struct-field decisions. Function-pointer globals and local
//! register declaration votes are retained only for the explicit
//! `--ablate-scope=function` compatibility path; Stage B owns them normally.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::decompile::passes::c_pass::types::{CType, TypeQualifiers};
use crate::decompile::passes::clight_select::candtype::{CandType, Sign};
use crate::decompile::passes::clight_select::query::CalleeSignature;
use crate::decompile::passes::clight_select::select::SelectedFunction;
use crate::x86::types::{
    Address, ClightBinaryOp, ClightExpr, ClightStmt, ClightType, Ident, RTLReg, XType,
};

#[derive(Default)]
pub struct DeclSolveOut {
    /// Fields whose use evidence is integer-DOMINATED (int uses, no bare deref uses): if the emitted def says pointer, retype to long (the `%`-on-void* family). Applied by apply_struct_field_type_selection.
    pub field_force_long: HashSet<(String, String)>,
    /// Per-(struct,field) pointer retype decision: positive pointer evidence minus the conflict veto; the field authority relocated here from the emit pass, valued with the chosen candidate string.
    pub field_ptr_selection: HashMap<(String, String), String>,
    /// Ablation-only legacy function-pointer global declarations.
    pub fnptr_globals: HashMap<String, CType>,
    /// Ablation-only legacy force-long declarations.
    pub force_long_regs: HashMap<Address, HashSet<RTLReg>>,
    /// Ablation-only legacy force-pointer declarations.
    pub force_ptr_regs: HashMap<Address, HashSet<RTLReg>>,
}

/// XType -> CType for fn-pointer signatures; mirrors helpers.rs convert_param_type_from_param's Typed arm at class level.
fn xtype_to_ctype(xt: &XType) -> CType {
    use crate::decompile::passes::c_pass::types::{FloatSize, IntSize, Signedness};
    match xt {
        XType::Xvoid => CType::Void,
        XType::Xfloat => CType::Float(FloatSize::Double),
        XType::Xsingle => CType::Float(FloatSize::Float),
        XType::Xbool => CType::Bool,
        XType::Xint8signed => CType::Int(IntSize::Char, Signedness::Signed),
        XType::Xint8unsigned => CType::Int(IntSize::Char, Signedness::Unsigned),
        XType::Xint16signed => CType::Int(IntSize::Short, Signedness::Signed),
        XType::Xint16unsigned => CType::Int(IntSize::Short, Signedness::Unsigned),
        XType::Xint | XType::Xany32 => CType::int(),
        XType::Xintunsigned => CType::uint(),
        XType::Xlongunsigned => CType::ulong(),
        XType::XstructPtr(sid) => CType::ptr(CType::Struct(format!("struct_{:x}", sid))),
        XType::Xcharptr => CType::ptr(CType::char_signed()),
        XType::Xcharptrptr => CType::ptr(CType::ptr(CType::char_signed())),
        XType::Xintptr => CType::ptr(CType::int()),
        XType::Xfloatptr => CType::ptr(CType::double()),
        XType::Xsingleptr => CType::ptr(CType::float()),
        XType::Xptr | XType::Xfuncptr => CType::ptr(CType::Void),
        _ => CType::long(),
    }
}

/// The annotation type of an expression (leaf accessor; mirrors ctyping::expr_annotation for the shapes a field base can take).
fn ann(e: &ClightExpr) -> Option<&ClightType> {
    use ClightExpr::*;
    match e {
        EconstInt(_, t)
        | EconstFloat(_, t)
        | EconstSingle(_, t)
        | EconstLong(_, t)
        | Evar(_, t)
        | EvarSymbol(_, t)
        | Etempvar(_, t)
        | Ederef(_, t)
        | Eaddrof(_, t)
        | Eunop(_, _, t)
        | Ebinop(_, _, _, t)
        | Ecast(_, t)
        | Efield(_, _, t)
        | Esizeof(_, t)
        | Ealignof(_, t)
        | Econdition(_, _, _, t) => Some(t),
    }
}

/// Struct sid when `e` is struct-pointer-typed (annotation or cast target).
fn struct_ptr_sid(e: &ClightExpr) -> Option<usize> {
    if let Some(ClightType::Tpointer(inner, _)) = ann(e) {
        if let ClightType::Tstruct(sid, _) = inner.as_ref() {
            return Some(*sid);
        }
    }
    None
}

/// The TR-3 field key of a field USE, either a materialized Efield or the raw deref form from_relations later prints as ->ofs_N; struct identity comes from the base's Tstruct annotation.
fn field_key(e: &ClightExpr) -> Option<(String, String)> {
    match e {
        ClightExpr::Efield(base, fid, _) => {
            let bt = match base.as_ref() {
                ClightExpr::Ederef(_, t) => t,
                ClightExpr::Etempvar(_, t)
                | ClightExpr::Evar(_, t)
                | ClightExpr::EvarSymbol(_, t) => t,
                _ => return None,
            };
            if let ClightType::Tstruct(sid, _) = bt {
                // DECL-1: the Efield id is a two's-complement-encoded usize, so a negative offset must be spelled by the one canonical decoder, keeping every field-key producer in one key space.
                return Some((
                    format!("struct_{:x}", sid),
                    crate::decompile::passes::csh_pass::field_ident_to_name(*fid),
                ));
            }
            None
        }
        ClightExpr::Ederef(inner, _) => match inner.as_ref() {
            ClightExpr::Ebinop(ClightBinaryOp::Oadd, l, r, _) => {
                let sid = struct_ptr_sid(l)?;
                let ofs = match r.as_ref() {
                    ClightExpr::EconstInt(n, _) => *n as i64,
                    ClightExpr::EconstLong(n, _) => *n,
                    _ => return None,
                };
                // DECL-1: negative struct-relative offsets are legal, so spell the field name with the canonical decoder and this raw-deref key space agrees with the materialized-Efield one for every sign.
                Some((
                    format!("struct_{:x}", sid),
                    crate::decompile::passes::csh_pass::field_ident_to_name(
                        ofs as crate::x86::types::Ident,
                    ),
                ))
            }
            base => {
                let sid = struct_ptr_sid(base)?;
                Some((format!("struct_{:x}", sid), "ofs_0".to_string()))
            }
        },
        _ => None,
    }
}

#[derive(Default, Clone)]
struct FieldVotes {
    int_ops: u32,
    bare_deref: u32,
}

struct Collector<'a> {
    fields: BTreeMap<(String, String), FieldVotes>,
    /// Called data-global name -> the set of argument counts observed at its call sites (the signature source: data globals have no recovered CalleeSignature).
    called_globals: BTreeMap<String, std::collections::BTreeSet<usize>>,
    /// Names of OBJECT-kind symbols (data globals) from the symbol table -- a call through one of these is the call-through-non-function family.
    global_names: &'a HashSet<String>,
    /// Clight global idents -> names (callees arrive as Evar(id) for ident-addressed globals, EvarSymbol for named externs).
    id_to_name: &'a HashMap<usize, String>,
    /// Current function's register candidate lists: a BARE field load into a register whose every candidate is integral is integer evidence for the FIELD, since cast-wrapped forms compile regardless.
    var_cands: &'a HashMap<crate::x86::types::RTLReg, Vec<CandType>>,
    /// Current function's registers used as a BARE operand of an integer-only operator: the use-based authority, right even when the solver mistyped the register as a pointer (the RC-3 family).
    reg_int_use: &'a HashSet<crate::x86::types::RTLReg>,
}

fn all_int_candidates(cands: &[CandType]) -> bool {
    !cands.is_empty() && cands.iter().all(|c| c.is_integer())
}

/// True when `op` rejects pointer operands outright: the bitwise/shift/mod set, plus `*`/`/` when the result is not float (a Tfloat `*`/`/` is genuine float arithmetic). A BARE register operand here is integer-used.
fn is_int_only_binop(op: &ClightBinaryOp, ty: &ClightType) -> bool {
    matches!(
        op,
        ClightBinaryOp::Omod
            | ClightBinaryOp::Oand
            | ClightBinaryOp::Oor
            | ClightBinaryOp::Oxor
            | ClightBinaryOp::Oshl
            | ClightBinaryOp::Oshr
    ) || (matches!(op, ClightBinaryOp::Omul | ClightBinaryOp::Odiv)
        && !matches!(ty, ClightType::Tfloat(..)))
}

/// The register at the root of an operand, peeling casts (the printer drops these, so a cast-wrapped `reg` is still `reg` in an integer position). Mirrors `bare_reg` used by force_register_decls.
fn bare_reg_of(e: &ClightExpr) -> Option<crate::x86::types::RTLReg> {
    match e {
        ClightExpr::Etempvar(id, _) => Some(*id as crate::x86::types::RTLReg),
        ClightExpr::Ecast(inner, _) => bare_reg_of(inner),
        _ => None,
    }
}

/// Registers used as a BARE operand of an integer-only operator anywhere in `stmts`. A field flowing into such a register is integer-used through it.
fn collect_int_op_regs<'a>(
    stmts: impl Iterator<Item = &'a ClightStmt>,
) -> HashSet<crate::x86::types::RTLReg> {
    fn expr(e: &ClightExpr, out: &mut HashSet<crate::x86::types::RTLReg>) {
        use ClightExpr::*;
        match e {
            Ebinop(op, l, r, t) => {
                if is_int_only_binop(op, t) {
                    for side in [l.as_ref(), r.as_ref()] {
                        if let Some(reg) = bare_reg_of(side) {
                            out.insert(reg);
                        }
                    }
                }
                expr(l, out);
                expr(r, out);
            }
            Eunop(crate::x86::types::ClightUnaryOp::Onotint, inner, _) => {
                if let Some(reg) = bare_reg_of(inner) {
                    out.insert(reg);
                }
                expr(inner, out);
            }
            Eaddrof(inner, _)
            | Eunop(_, inner, _)
            | Ecast(inner, _)
            | Ederef(inner, _)
            | Efield(inner, _, _) => expr(inner, out),
            Econdition(c, a, b, _) => {
                expr(c, out);
                expr(a, out);
                expr(b, out);
            }
            _ => {}
        }
    }
    fn stmt(s: &ClightStmt, out: &mut HashSet<crate::x86::types::RTLReg>) {
        use ClightStmt::*;
        match s {
            Sassign(l, r) => {
                expr(l, out);
                expr(r, out);
            }
            Sset(_, e) => expr(e, out),
            Scall(_, f, args) => {
                expr(f, out);
                for a in args {
                    expr(a, out);
                }
            }
            Sbuiltin(_, _, _, args) => {
                for a in args {
                    expr(a, out);
                }
            }
            Sreturn(Some(e)) => expr(e, out),
            Sifthenelse(c, a, b) => {
                expr(c, out);
                stmt(a, out);
                stmt(b, out);
            }
            Ssequence(ss) => {
                for s in ss {
                    stmt(s, out);
                }
            }
            Sloop(a, b) => {
                stmt(a, out);
                stmt(b, out);
            }
            Slabel(_, inner) => stmt(inner, out),
            Sswitch(e, cases) => {
                expr(e, out);
                for (_, s) in cases {
                    stmt(s, out);
                }
            }
            _ => {}
        }
    }
    let mut out = HashSet::new();
    for s in stmts {
        stmt(s, &mut out);
    }
    out
}

impl<'a> Collector<'a> {
    fn expr(&mut self, e: &ClightExpr) {
        use ClightExpr::*;
        match e {
            Ebinop(op, l, r, _) => {
                // Integer-only operators reject pointers outright, so a BARE field operand is decl-level integer evidence; * and / are undefined on pointers too, making field * 8 the same hard evidence.
                if matches!(
                    op,
                    ClightBinaryOp::Omod
                        | ClightBinaryOp::Oand
                        | ClightBinaryOp::Oor
                        | ClightBinaryOp::Oxor
                        | ClightBinaryOp::Oshl
                        | ClightBinaryOp::Oshr
                        | ClightBinaryOp::Omul
                        | ClightBinaryOp::Odiv
                ) {
                    for side in [l.as_ref(), r.as_ref()] {
                        if let Some(key) = field_key(side) {
                            self.fields.entry(key).or_default().int_ops += 1;
                        }
                    }
                }
                self.expr(l);
                self.expr(r);
            }
            Ederef(inner, _) => {
                // A bare field as a deref base is pointer evidence that blocks the force-long override (dual-use fields stay untouched).
                if let Some(key) = field_key(inner) {
                    self.fields.entry(key).or_default().bare_deref += 1;
                }
                self.expr(inner);
            }
            Efield(base, _, _) => self.expr(base),
            Eaddrof(inner, _) | Eunop(_, inner, _) | Ecast(inner, _) => self.expr(inner),
            Econdition(c, a, b, _) => {
                self.expr(c);
                self.expr(a);
                self.expr(b);
            }
            _ => {}
        }
    }

    fn stmt(&mut self, s: &ClightStmt) {
        use ClightStmt::*;
        match s {
            Sassign(l, r) => {
                self.expr(l);
                self.expr(r);
            }
            Sset(id, e) => {
                if let Some(key) = field_key(e) {
                    let reg = *id as crate::x86::types::RTLReg;
                    // Two routes to integer evidence for a loaded field: every candidate integral, or a USE fact that the register feeds an integer-only operator, which is the authority for the RC-3 family.
                    let int_only = self
                        .var_cands
                        .get(&reg)
                        .map(|c| all_int_candidates(c))
                        .unwrap_or(false)
                        || self.reg_int_use.contains(&reg);
                    if int_only {
                        self.fields.entry(key).or_default().int_ops += 1;
                    }
                }
                self.expr(e)
            }
            Scall(_, f, args) => {
                // A call through a global SYMBOL that is a data object (not a recovered function) is the call-through-non-function family: the decl must become a function pointer.
                let callee_name: Option<String> = match f {
                    ClightExpr::EvarSymbol(name, _) => Some(name.clone()),
                    ClightExpr::Evar(id, _) => self.id_to_name.get(id).cloned(),
                    _ => None,
                };
                if let Some(name) = callee_name {
                    if std::env::var("MANIFOLD_DECL_SOLVE_TRACE").is_ok() {
                        eprintln!(
                            "[decl-solve trace] call via {:?} (object-symbol: {})",
                            name,
                            self.global_names.contains(name.as_str())
                        );
                    }
                    if self.global_names.contains(name.as_str()) {
                        self.called_globals
                            .entry(name)
                            .or_default()
                            .insert(args.len());
                    }
                }
                self.expr(f);
                for a in args {
                    self.expr(a);
                }
            }
            Sbuiltin(_, _, _, args) => {
                for a in args {
                    self.expr(a);
                }
            }
            Sreturn(Some(e)) => self.expr(e),
            Sifthenelse(c, a, b) => {
                self.expr(c);
                self.stmt(a);
                self.stmt(b);
            }
            Ssequence(ss) => {
                for s in ss {
                    self.stmt(s);
                }
            }
            Sloop(a, b) => {
                self.stmt(a);
                self.stmt(b);
            }
            Slabel(_, inner) => self.stmt(inner),
            Sswitch(e, cases) => {
                self.expr(e);
                for (_, s) in cases {
                    self.stmt(s);
                }
            }
            _ => {}
        }
    }
}

/// Per-(struct,field) pointer retype decision, the field authority relocated from the emit pass; the same evidence -> widen -> conflicts shape run over the EMITTED function set.
fn field_ptr_selection(
    funcs: &[SelectedFunction],
    internal_addrs: &HashSet<Address>,
    callee_sigs: &HashMap<Ident, CalleeSignature>,
    id_to_name: &HashMap<usize, String>,
    int_veto: &HashSet<(String, String)>,
) -> HashMap<(String, String), String> {
    use crate::decompile::passes::clight_select::query as csq;

    // name -> ident exactly as the retired tr3_field_ptr_selection built it (sorted (id, name), first-wins, both sanitized and raw spellings) so callee_ident_from_expr resolves callee signatures identically.
    let mut name_to_ident: HashMap<String, Ident> = HashMap::new();
    let mut sorted_id_name: Vec<(&usize, &String)> = id_to_name.iter().collect();
    sorted_id_name.sort_by_key(|(id, name)| (**id, (*name).clone()));
    for (id, name) in sorted_id_name {
        let sanitized =
            crate::decompile::passes::c_pass::convert::from_relations::sanitize_c_symbol_name(name);
        name_to_ident.entry(sanitized).or_insert(*id as Ident);
        name_to_ident.entry(name.clone()).or_insert(*id as Ident);
    }

    let mut field_cands: HashMap<(String, String), Vec<String>> = HashMap::new();
    let mut evidence: HashSet<(String, String)> = HashSet::new();
    let mut conflicts: HashSet<(String, String)> = HashSet::new();

    // Emitted functions only, address-sorted for a deterministic first-wins candidate merge (candidates are identical per key, so order is moot for correctness; the discipline matches the retired scan).
    let mut sorted_funcs: Vec<&SelectedFunction> = funcs
        .iter()
        .filter(|f| internal_addrs.contains(&f.address))
        .collect();
    sorted_funcs.sort_by_key(|f| f.address);

    // Phase 1: per-function selected register classes (retained for phase 2), field candidates, and positive pointer evidence.
    let mut func_reg_classes: Vec<(HashSet<RTLReg>, HashSet<RTLReg>)> =
        Vec::with_capacity(sorted_funcs.len());
    for func in &sorted_funcs {
        let mut ptr_regs: HashSet<RTLReg> = HashSet::new();
        let mut float_regs: HashSet<RTLReg> = HashSet::new();
        for (reg, cands) in &func.var_type_candidates {
            let idx = func.var_decl_idx.get(reg).copied().unwrap_or(0);
            let sel = cands.get(idx).or_else(|| cands.first()).copied();
            if sel.is_some_and(|c| c.is_pointer()) {
                ptr_regs.insert(*reg);
            }
            if sel.is_some_and(|c| c.is_float()) {
                float_regs.insert(*reg);
            }
        }
        for (reg, ty) in &func.var_types {
            if !func.var_type_candidates.contains_key(reg) {
                if ty.is_pointer() {
                    ptr_regs.insert(*reg);
                } else if ty.is_float() {
                    float_regs.insert(*reg);
                }
            }
        }
        for (key, cands) in csq::collect_struct_field_type_candidates(func.statements.values()) {
            field_cands.entry(key).or_insert(cands);
        }
        for stmt in func.statements.values() {
            csq::scan_field_ptr_evidence(
                stmt,
                &ptr_regs,
                callee_sigs,
                &name_to_ident,
                &mut evidence,
            );
        }
        func_reg_classes.push((ptr_regs, float_regs));
    }

    // Fields the pick rule would patch: phase 2's veto must treat loads of these as pointer-valued, since the patch is what makes them pointers in the printed C.
    let patchable: HashSet<(String, String)> = evidence
        .iter()
        .filter(|k| {
            field_cands.get(*k).map_or(false, |cands| {
                csq::pick_field_ptr_candidate(cands).is_some()
            })
        })
        .cloned()
        .collect();

    // Phase 2: widen the register classes to a fixpoint, then collect the pointer-retype conflicts (float context, integer/offset arithmetic).
    for (func, (ptr_regs, float_regs)) in sorted_funcs.iter().zip(func_reg_classes.iter_mut()) {
        csq::widen_float_regs_by_defs(func.statements.values(), float_regs);
        csq::widen_ptr_regs_by_defs(func.statements.values(), ptr_regs, &patchable);
        for stmt in func.statements.values() {
            csq::scan_field_ptr_conflicts(
                stmt,
                ptr_regs,
                float_regs,
                callee_sigs,
                &name_to_ident,
                &mut conflicts,
            );
        }
    }

    // Integer-use evidence joins the conflict veto -- a field sitting in `%`/`&`/shift arithmetic must never receive a pointer patch.
    conflicts.extend(int_veto.iter().cloned());

    let mut selection: HashMap<(String, String), String> = HashMap::new();
    let mut sorted_evidence: Vec<&(String, String)> = evidence.iter().collect();
    sorted_evidence.sort();
    for key in sorted_evidence {
        if conflicts.contains(key) {
            continue;
        }
        if let Some(cands) = field_cands.get(key) {
            if let Some(i) = csq::pick_field_ptr_candidate(cands) {
                selection.insert(key.clone(), cands[i].clone());
            }
        }
    }
    selection
}

/// The register at the root of an operand, peeling casts: forcing its decl to long makes the peeled cast redundant, and the float/deref vetoes still catch genuinely float or pointer registers.
fn bare_reg(e: &ClightExpr) -> Option<RTLReg> {
    match e {
        ClightExpr::Etempvar(id, _) => Some(*id as RTLReg),
        ClightExpr::Ecast(inner, _) => bare_reg(inner),
        _ => None,
    }
}

#[derive(Default, Clone)]
struct RegVotes {
    int_only: u32,
    float_use: u32,
    ptr_use: u32,
}

/// Per-function register decl authority returning (forced_long, forced_ptr): an
/// int-only operator proves an integer, while a dereference/store-through or an
/// ABI-proven pointer argument proves a pointer.  Each verdict requires
/// unambiguous evidence.  In particular, the call vote is taken from the
/// reconciled callee signature, not from the cast annotation that ClightPass
/// materializes around every argument candidate.
fn force_register_decls(
    func: &SelectedFunction,
    callee_sigs: &HashMap<Ident, CalleeSignature>,
    name_to_ident: &HashMap<String, Ident>,
) -> (HashSet<RTLReg>, HashSet<RTLReg>) {
    // Eligible-long = selected float/pointer; eligible-ptr = selected int. An already-correct register needs no forcing, so each verdict only reconsiders the OTHER class (the two sets are disjoint).
    let class_of = |reg: &RTLReg| -> Option<CandType> {
        if let Some(cands) = func.var_type_candidates.get(reg) {
            let idx = func.var_decl_idx.get(reg).copied().unwrap_or(0);
            return cands.get(idx).or_else(|| cands.first()).copied();
        }
        func.var_types.get(reg).copied()
    };
    let mut all_regs: HashSet<RTLReg> = func.var_type_candidates.keys().copied().collect();
    all_regs.extend(func.var_types.keys().copied());
    let mut eligible_long: HashSet<RTLReg> = HashSet::new();
    let mut eligible_ptr: HashSet<RTLReg> = HashSet::new();
    for reg in &all_regs {
        match class_of(reg) {
            Some(c) if c.is_float() || c.is_pointer() => {
                eligible_long.insert(*reg);
            }
            Some(c) if c.is_integer() => {
                eligible_ptr.insert(*reg);
            }
            _ => {}
        }
    }
    if eligible_long.is_empty() && eligible_ptr.is_empty() {
        return (HashSet::new(), HashSet::new());
    }

    fn is_int_only_op(e: &ClightExpr) -> bool {
        // `*`/`/` are integer-only ONLY when the result is not float; a Tfloat `*`/`/` is genuine float arithmetic and must NOT be read as an int op (that would suppress legitimate float-source evidence).
        let int_mul_div = matches!(
            e,
            ClightExpr::Ebinop(ClightBinaryOp::Omul | ClightBinaryOp::Odiv, _, _, t)
                if !matches!(t, ClightType::Tfloat(..))
        );
        int_mul_div
            || matches!(
                e,
                ClightExpr::Ebinop(
                    ClightBinaryOp::Omod
                        | ClightBinaryOp::Oand
                        | ClightBinaryOp::Oor
                        | ClightBinaryOp::Oxor
                        | ClightBinaryOp::Oshl
                        | ClightBinaryOp::Oshr,
                    ..,
                ) | ClightExpr::Eunop(crate::x86::types::ClightUnaryOp::Onotint, ..)
            )
    }

    fn walk_expr(e: &ClightExpr, votes: &mut HashMap<RTLReg, RegVotes>) {
        use ClightExpr::*;
        match e {
            Ebinop(op, l, r, t) => {
                // * and / reject pointers, so a non-float multiply or divide is integer evidence too; a Tfloat one is genuine float arithmetic, so gate the int reading on a non-float result.
                let int_mul_div = matches!(op, ClightBinaryOp::Omul | ClightBinaryOp::Odiv)
                    && !matches!(t, ClightType::Tfloat(..));
                let int_only = int_mul_div
                    || matches!(
                        op,
                        ClightBinaryOp::Omod
                            | ClightBinaryOp::Oand
                            | ClightBinaryOp::Oor
                            | ClightBinaryOp::Oxor
                            | ClightBinaryOp::Oshl
                            | ClightBinaryOp::Oshr
                    );
                // Genuine float arithmetic -- NOT a bit op that merely inherited a Tfloat annotation from the mistyped operand.
                let float_arith = matches!(t, ClightType::Tfloat(..))
                    && matches!(
                        op,
                        ClightBinaryOp::Omul
                            | ClightBinaryOp::Odiv
                            | ClightBinaryOp::Oadd
                            | ClightBinaryOp::Osub
                    );
                for side in [l.as_ref(), r.as_ref()] {
                    if let Some(reg) = bare_reg(side) {
                        if int_only {
                            votes.entry(reg).or_default().int_only += 1;
                        }
                        if float_arith {
                            votes.entry(reg).or_default().float_use += 1;
                        }
                    }
                }
                walk_expr(l, votes);
                walk_expr(r, votes);
            }
            Eunop(crate::x86::types::ClightUnaryOp::Onotint, inner, _) => {
                if let Some(reg) = bare_reg(inner) {
                    votes.entry(reg).or_default().int_only += 1;
                }
                walk_expr(inner, votes);
            }
            Ederef(inner, _) => {
                // The dereferenced base is a genuine pointer.
                let base = match inner.as_ref() {
                    Ebinop(ClightBinaryOp::Oadd, l, _, _) => l.as_ref(),
                    other => other,
                };
                if let Some(reg) = bare_reg(base) {
                    votes.entry(reg).or_default().ptr_use += 1;
                }
                walk_expr(inner, votes);
            }
            Efield(base, _, _) => {
                let p = match base.as_ref() {
                    Ederef(inner, _) => inner.as_ref(),
                    other => other,
                };
                if let Some(reg) = bare_reg(p) {
                    votes.entry(reg).or_default().ptr_use += 1;
                }
                walk_expr(base, votes);
            }
            Ecast(inner, t) => {
                // A cast TO float proves the operand is floating, so it vetoes a wrong force-long without forcing float in the decl.
                if matches!(t, ClightType::Tfloat(..)) {
                    if let Some(reg) = bare_reg(inner) {
                        votes.entry(reg).or_default().float_use += 1;
                    }
                }
                walk_expr(inner, votes);
            }
            Eaddrof(inner, _) | Eunop(_, inner, _) => walk_expr(inner, votes),
            Econdition(c, a, b, _) => {
                walk_expr(c, votes);
                walk_expr(a, votes);
                walk_expr(b, votes);
            }
            _ => {}
        }
    }

    fn walk_stmt(
        s: &ClightStmt,
        votes: &mut HashMap<RTLReg, RegVotes>,
        callee_sigs: &HashMap<Ident, CalleeSignature>,
        name_to_ident: &HashMap<String, Ident>,
    ) {
        use ClightStmt::*;
        match s {
            Sassign(l, r) => {
                // `*R = ...` stores through a genuine pointer register.
                if let ClightExpr::Ederef(inner, _) = l {
                    if let Some(reg) = bare_reg(inner) {
                        votes.entry(reg).or_default().ptr_use += 1;
                    }
                }
                walk_expr(l, votes);
                walk_expr(r, votes);
            }
            Sset(id, e) => {
                // Assigned a genuine float SOURCE (literal or float arithmetic / float load), not a bit op that merely inherited Tfloat.
                let genuine_float = !is_int_only_op(e)
                    && (matches!(
                        e,
                        ClightExpr::EconstFloat(..) | ClightExpr::EconstSingle(..)
                    ) || matches!(ann(e), Some(ClightType::Tfloat(..))));
                if genuine_float {
                    votes.entry(*id as RTLReg).or_default().float_use += 1;
                }
                // NOTE: pointer-SOURCE evidence was tried here and REVERTED -- the emitter materializes annotation casts liberally, so counting them spuriously vetoed correct force-long verdicts (+11 gcc errors).
                walk_expr(e, votes);
            }
            Scall(_, f, args) => {
                // A reconciled pointer parameter is declaration-level evidence
                // for the value stored in the argument register.  Peel the
                // printer's cast wrapper with bare_reg: accepting an int ->
                // pointer C cast is not enough on ptr64, where an int local has
                // already truncated the machine value before the call.
                let sig = crate::decompile::passes::clight_select::select::callee_ident_from_expr(
                    f,
                    name_to_ident,
                )
                .and_then(|id| callee_sigs.get(&id));
                if let Some(sig) = sig {
                    for (i, arg) in args.iter().enumerate() {
                        if sig
                            .param_types
                            .get(i)
                            .map(crate::decompile::passes::clight_select::query::xtype_is_ptr_class)
                            .unwrap_or(false)
                        {
                            if let Some(reg) = bare_reg(arg) {
                                votes.entry(reg).or_default().ptr_use += 1;
                            }
                        }
                    }
                }
                walk_expr(f, votes);
                for a in args {
                    walk_expr(a, votes);
                }
            }
            Sbuiltin(_, _, _, args) => {
                for a in args {
                    walk_expr(a, votes);
                }
            }
            Sreturn(Some(e)) => walk_expr(e, votes),
            Sifthenelse(c, a, b) => {
                walk_expr(c, votes);
                walk_stmt(a, votes, callee_sigs, name_to_ident);
                walk_stmt(b, votes, callee_sigs, name_to_ident);
            }
            Ssequence(ss) => {
                for s in ss {
                    walk_stmt(s, votes, callee_sigs, name_to_ident);
                }
            }
            Sloop(a, b) => {
                walk_stmt(a, votes, callee_sigs, name_to_ident);
                walk_stmt(b, votes, callee_sigs, name_to_ident);
            }
            Slabel(_, inner) => walk_stmt(inner, votes, callee_sigs, name_to_ident),
            Sswitch(e, cases) => {
                walk_expr(e, votes);
                for (_, s) in cases {
                    walk_stmt(s, votes, callee_sigs, name_to_ident);
                }
            }
            _ => {}
        }
    }

    let mut votes: HashMap<RTLReg, RegVotes> = HashMap::new();
    // The emitted parameter declaration and the storage denoted by its RTLReg
    // are one C object.  A pointer-class recovered parameter therefore carries
    // the same declaration authority as a dereference or a pointer-parameter
    // call use; otherwise the body can truncate the incoming pointer through an
    // independently selected `int` temporary even though the function header
    // says `void *pN`.
    for (reg, pt) in func.param_regs.iter().zip(func.param_types.iter()) {
        let pointer_param = match pt {
            crate::x86::types::ParamType::Pointer
            | crate::x86::types::ParamType::StructPointer(_) => true,
            crate::x86::types::ParamType::Typed(xt) => {
                crate::decompile::passes::clight_select::query::xtype_is_ptr_class(xt)
            }
            crate::x86::types::ParamType::Integer | crate::x86::types::ParamType::Unknown => false,
        };
        if pointer_param {
            votes.entry(*reg).or_default().ptr_use += 1;
        }
    }
    let mut nodes: Vec<_> = func.statements.keys().copied().collect();
    nodes.sort_unstable();
    for n in nodes {
        walk_stmt(&func.statements[&n], &mut votes, callee_sigs, name_to_ident);
    }

    let forced_long: HashSet<RTLReg> = eligible_long
        .iter()
        .filter(|r| {
            votes.get(r).map_or(false, |v| {
                v.int_only > 0 && v.float_use == 0 && v.ptr_use == 0
            })
        })
        .copied()
        .collect();
    let forced_ptr: HashSet<RTLReg> = eligible_ptr
        .iter()
        .filter(|r| {
            votes.get(r).map_or(false, |v| {
                v.ptr_use > 0 && v.int_only == 0 && v.float_use == 0
            })
        })
        .copied()
        .collect();

    if std::env::var("MANIFOLD_FORCE_LONG_TRACE").is_ok() {
        let cands: Vec<_> = eligible_long
            .iter()
            .chain(eligible_ptr.iter())
            .filter_map(|r| {
                votes
                    .get(r)
                    .map(|v| (*r, v.int_only, v.float_use, v.ptr_use))
            })
            .filter(|(_, i, _, p)| *i > 0 || *p > 0)
            .collect();
        if !cands.is_empty() {
            eprintln!(
                "[force-reg] fn {:x}: elig(long={},ptr={}) forced(long={},ptr={}) cands(reg,int,float,ptr)={:?}",
                func.address,
                eligible_long.len(),
                eligible_ptr.len(),
                forced_long.len(),
                forced_ptr.len(),
                cands,
            );
        }
    }

    (forced_long, forced_ptr)
}

pub fn run(
    funcs: &[SelectedFunction],
    internal_addrs: &HashSet<Address>,
    callee_sigs: &HashMap<Ident, CalleeSignature>,
    name_to_ident: &HashMap<String, Ident>,
    global_names: &HashSet<String>,
    id_to_name: &HashMap<usize, String>,
    include_legacy_interface_votes: bool,
) -> DeclSolveOut {
    let empty: HashMap<crate::x86::types::RTLReg, Vec<CandType>> = HashMap::new();
    let empty_regs: HashSet<crate::x86::types::RTLReg> = HashSet::new();
    let mut fields: BTreeMap<(String, String), FieldVotes> = BTreeMap::new();
    let mut called: BTreeMap<String, std::collections::BTreeSet<usize>> = BTreeMap::new();
    // Address-sorted walk for deterministic counts (counts are order-free, but keep the discipline).
    let mut sorted: Vec<&SelectedFunction> = funcs.iter().collect();
    sorted.sort_by_key(|f| f.address);
    for f in &sorted {
        // Pre-pass: integer-only-op-used registers (def can follow use, so gather them first).
        let reg_int_use = collect_int_op_regs(f.statements.values());
        let mut c = Collector {
            fields: std::mem::take(&mut fields),
            called_globals: std::mem::take(&mut called),
            global_names,
            id_to_name,
            var_cands: &f.var_type_candidates,
            reg_int_use: &reg_int_use,
        };
        let _ = &empty;
        let mut nodes: Vec<_> = f.statements.keys().copied().collect();
        nodes.sort_unstable();
        for n in nodes {
            c.stmt(&f.statements[&n]);
        }
        fields = c.fields;
        called = c.called_globals;
    }
    let c = Collector {
        fields,
        called_globals: called,
        global_names,
        id_to_name,
        var_cands: &empty,
        reg_int_use: &empty_regs,
    };

    if std::env::var("MANIFOLD_DECL_SOLVE_TRACE").is_ok() {
        eprintln!(
            "[decl-solve trace] fields seen: {:?}",
            c.fields.keys().take(5).collect::<Vec<_>>()
        );
        eprintln!(
            "[decl-solve trace] called globals: {:?}; global_names sample: {:?}",
            c.called_globals.keys().take(5).collect::<Vec<_>>(),
            global_names.iter().take(5).collect::<Vec<_>>()
        );
    }
    let mut out = DeclSolveOut::default();
    let mut field_int_veto = HashSet::new();
    for (key, v) in &c.fields {
        if v.int_ops > 0 {
            field_int_veto.insert(key.clone());
            // The vote: integer uses with NO bare-deref pointer evidence means the decl must be integral; with both, the field is dual-use and `long` would shift errors rather than fix them -- leave it.
            if v.bare_deref == 0 {
                out.field_force_long.insert(key.clone());
            }
        }
    }

    // CTYPING_PLAN 5.3: the per-(struct,field) pointer retype decision, the field authority relocated from the emit-pass TR-3 scan. Runs over the emitted function set with the int-arith veto just computed joined into its conflicts (the emit pass joined it the same way).
    out.field_ptr_selection = field_ptr_selection(
        funcs,
        internal_addrs,
        callee_sigs,
        id_to_name,
        &field_int_veto,
    );
    for (name, arg_counts) in &c.called_globals {
        if !include_legacy_interface_votes {
            break;
        }
        // Signature priority: the recovered callee table when available, else synthesized from the CALL SITES; params are long, since int and pointer arguments both convert silently under -w.
        let sig = name_to_ident
            .get(name.as_str())
            .and_then(|id| callee_sigs.get(id));
        let fn_ty = match sig {
            Some(s) if !s.param_types.is_empty() => CType::Function(
                Box::new(xtype_to_ctype(&s.return_type)),
                s.param_types.iter().map(xtype_to_ctype).collect::<Vec<_>>(),
                false,
                false,
            ),
            _ => {
                // arg_counts is the sorted set of observed call-site arities.
                let min = arg_counts.iter().next().copied().unwrap_or(0);
                let max = arg_counts.iter().next_back().copied().unwrap_or(0);
                // DECL-2: pick the single C function type that accepts every observed arity.
                if max == min {
                    // One observed arity: a fixed prototype (min==0 prints `(void)`).
                    CType::Function(
                        Box::new(CType::long()),
                        vec![CType::long(); min],
                        false,
                        false,
                    )
                } else if min == 0 {
                    // Mixed 0-arg and N-arg call sites: emit K&R long (*name)(), never (...) which is a hard C error.
                    CType::func_unprototyped(CType::long())
                } else {
                    // Differing arities, all >=1: a variadic tail is well-formed (>=1 named param).
                    CType::Function(
                        Box::new(CType::long()),
                        vec![CType::long(); min],
                        true,
                        false,
                    )
                }
            }
        };
        out.fnptr_globals.insert(
            name.clone(),
            CType::Pointer(Box::new(fn_ty), TypeQualifiers::none()),
        );
    }

    // Register force-long (phase 5 register decl authority): per emitted function, registers whose usage proves they are integers despite a float/pointer selection.
    for f in &sorted {
        if !include_legacy_interface_votes {
            break;
        }
        if !internal_addrs.contains(&f.address) {
            continue;
        }
        let (forced_long, forced_ptr) = force_register_decls(f, callee_sigs, name_to_ident);
        if !forced_long.is_empty() {
            out.force_long_regs.insert(f.address, forced_long);
        }
        if !forced_ptr.is_empty() {
            out.force_ptr_regs.insert(f.address, forced_ptr);
        }
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::passes::clight_select::query::CalleeSignature;
    use crate::x86::types::{ClightAttr, ClightIntSize, ClightSignedness, ParamType};
    use std::sync::Arc;

    fn tint() -> ClightType {
        ClightType::Tint(
            ClightIntSize::I32,
            ClightSignedness::Signed,
            ClightAttr::default(),
        )
    }

    fn tvoid_ptr() -> ClightType {
        ClightType::Tpointer(Arc::new(ClightType::Tvoid), ClightAttr::default())
    }

    fn selected_with_stmt(reg: RTLReg, stmt: ClightStmt) -> SelectedFunction {
        SelectedFunction {
            address: 0x1000,
            name: "caller".to_string(),
            entry_node: 0x1000,
            return_type: ClightType::Tvoid,
            param_regs: vec![reg],
            param_types: vec![ParamType::Integer],
            stack_size: 0,
            structure_world:
                crate::decompile::analysis::structuring_pass::STRUCTURE_WORLD_STRUCTURED,
            statements: [(0x1010, stmt)].into_iter().collect(),
            selected_candidate_nodes: [0x1010].into_iter().collect(),
            selected_write_bytes: HashMap::new(),
            successors: HashMap::new(),
            used_regs: [reg].into_iter().collect(),
            struct_fields: HashMap::new(),
            sseq_groups: HashMap::new(),
            var_types: HashMap::new(),
            var_type_candidates: [(reg, vec![CandType::I32(Sign::Signed), CandType::PtrVoid])]
                .into_iter()
                .collect(),
            var_decl_idx: [(reg, 0)].into_iter().collect(),
            loop_headers: HashSet::new(),
            switch_heads: HashSet::new(),
            reg_struct_ids: HashMap::new(),
            loop_info: HashMap::new(),
        }
    }

    fn call_stmt(reg: RTLReg, callee: &str) -> ClightStmt {
        ClightStmt::Scall(
            None,
            ClightExpr::EvarSymbol(callee.to_string(), ClightType::Tvoid),
            vec![ClightExpr::Ecast(
                Box::new(ClightExpr::Etempvar(reg as Ident, tint())),
                tvoid_ptr(),
            )],
        )
    }

    fn ptr_sig_env(callee: &str) -> (HashMap<Ident, CalleeSignature>, HashMap<String, Ident>) {
        let ident = 0x77;
        (
            [(
                ident,
                CalleeSignature {
                    param_count: 1,
                    return_type: XType::Xint,
                    param_types: vec![XType::Xptr],
                    is_varargs: false,
                },
            )]
            .into_iter()
            .collect(),
            [(callee.to_string(), ident)].into_iter().collect(),
        )
    }

    #[test]
    fn signature_pointer_argument_retypes_cast_wrapped_int_storage() {
        let reg = 0x8000_0000_0000_0042;
        let func = selected_with_stmt(reg, call_stmt(reg, "consume_ptr"));
        let (sigs, names) = ptr_sig_env("consume_ptr");

        let (forced_long, forced_ptr) = force_register_decls(&func, &sigs, &names);
        assert!(forced_long.is_empty());
        assert_eq!(forced_ptr, [reg].into_iter().collect());
    }

    #[test]
    fn pointer_parameter_header_retypes_its_selected_int_storage() {
        let reg = 0x8000_0000_0000_0045;
        let mut func = selected_with_stmt(reg, ClightStmt::Sskip);
        func.param_types[0] = ParamType::Pointer;

        let (_, forced_ptr) = force_register_decls(&func, &HashMap::new(), &HashMap::new());
        assert_eq!(forced_ptr, [reg].into_iter().collect());
    }

    #[test]
    fn integer_operator_vetoes_pointer_argument_retype() {
        let reg: RTLReg = 0x8000_0000_0000_0043;
        let int_use = ClightStmt::Sset(
            reg as Ident + 1,
            ClightExpr::Ebinop(
                ClightBinaryOp::Oand,
                Box::new(ClightExpr::Etempvar(reg as Ident, tint())),
                Box::new(ClightExpr::EconstInt(1, tint())),
                tint(),
            ),
        );
        let mut func = selected_with_stmt(
            reg,
            ClightStmt::Ssequence(vec![call_stmt(reg, "consume_ptr"), int_use]),
        );
        func.used_regs.insert(reg + 1);
        let (sigs, names) = ptr_sig_env("consume_ptr");

        let (_, forced_ptr) = force_register_decls(&func, &sigs, &names);
        assert!(forced_ptr.is_empty());
    }

    #[test]
    fn integer_signature_does_not_invent_pointer_storage() {
        let reg = 0x8000_0000_0000_0044;
        let func = selected_with_stmt(reg, call_stmt(reg, "consume_int"));
        let ident = 0x78;
        let sigs = [(
            ident,
            CalleeSignature {
                param_count: 1,
                return_type: XType::Xint,
                param_types: vec![XType::Xint],
                is_varargs: false,
            },
        )]
        .into_iter()
        .collect();
        let names = [("consume_int".to_string(), ident)].into_iter().collect();

        let (_, forced_ptr) = force_register_decls(&func, &sigs, &names);
        assert!(forced_ptr.is_empty());
    }
}
