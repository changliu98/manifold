//! Program-scope interface commitment (Stage B).
//!
//! Stage A remains the existing byte-identical per-function solve.  This
//! module reads its fixed selections, re-scores only statements affected by
//! each interface alternative with the full Clight checker, and solves one
//! small deterministic finite-domain MaxSMT instance.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use z3::ast::{Ast, Bool, Int};
use z3::{Optimize, SatResult};

use crate::decompile::elevator::config;
use crate::decompile::passes::c_pass::types::{CType, TypeQualifiers};
use crate::decompile::passes::clight_select::candtype::{CandType, Sign};
use crate::decompile::passes::clight_select::ctyping::{self, Severity};
use crate::decompile::passes::clight_select::query::{
    CalleeSignature, CommittedInterfaces, FunctionData, InterfaceAuthority, InterfaceClass,
    InterfaceVar, InterfaceVarId, InterfaceVars, KnownGlobalTypes,
};
use crate::decompile::passes::clight_select::select::{
    callee_ident_from_expr, ProgramSelectionState,
};
use crate::decompile::passes::clight_select::wt_audit::{self, AuditEnv};
use crate::x86::types::{
    Address, ClightExpr, ClightSignedness, ClightStmt, ClightType, Ident, Node, ParamType, RTLReg,
    XType,
};

#[derive(Debug, Clone, Default)]
pub(crate) struct InterfaceSolveStats {
    pub variable_count: usize,
    pub declaration_variable_count: usize,
    pub edge_count: usize,
    pub solve_ms: u128,
    pub unsat_count: usize,
    pub fallback_count: usize,
    pub changed_from_rank0: usize,
    pub changed_declarations: usize,
}

pub(crate) struct InterfaceSolveOutcome {
    pub committed: CommittedInterfaces,
    pub stage_a_preferences: BTreeMap<InterfaceVarId, InterfaceClass>,
    pub assignments: BTreeMap<InterfaceVarId, InterfaceClass>,
    /// Exact domain rank chosen for every interface variable.  Class alone is
    /// not a commitment identity: multiple concrete XTypes may share it.
    pub choice_ranks: BTreeMap<InterfaceVarId, usize>,
    /// Stage-B local declaration decisions which differ from Stage A.  These
    /// are hard inputs to Stage C, so the selected statements can adapt; they
    /// are never patched into the emitted tree after solving.
    pub declaration_assignments: BTreeMap<(Address, RTLReg), InterfaceClass>,
    pub dirty_functions: BTreeSet<Address>,
    pub stats: InterfaceSolveStats,
    pub instance_dump: String,
}

/// A final Stage-C statement disagreed with the global type Stage B committed.
/// This is evidence about an upstream interface choice, not grounds to veto a
/// local statement candidate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct GlobalFlowDisagreement {
    pub function: Address,
    pub node: Node,
    pub symbol: Ident,
    pub claimed: crate::decompile::passes::clight_select::flow::AVal,
}

#[derive(Clone)]
struct CallEdge {
    caller: Address,
    node: Node,
    callee: Ident,
    args: Vec<InterfaceClass>,
    arg_regs: Vec<Option<RTLReg>>,
    result: Option<InterfaceClass>,
    result_reg: Option<RTLReg>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ExternPassThrough {
    caller: Address,
    callee: Ident,
    node: Node,
    caller_position: usize,
    callee_position: usize,
    expected: InterfaceClass,
}

#[derive(Default, Clone, Copy)]
struct DeclVotes {
    int_use: u32,
    float_use: u32,
    ptr_use: u32,
}

#[derive(Clone)]
struct DeclarationVar {
    function: Address,
    reg: RTLReg,
    domain: Vec<InterfaceClass>,
    votes: DeclVotes,
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

/// XType -> CType for an extern declaration.  `Xany64` is a 64-bit value and
/// takes the model's spelling for one; the catch-all below is the default
/// machine word, for which `long` is right under every supported model.
fn xtype_to_ctype(xtype: &XType, model: crate::abi::DataModel) -> CType {
    use crate::decompile::passes::c_pass::types::{FloatSize, IntSize, Signedness};
    match xtype {
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
        XType::XstructPtr(sid) => CType::ptr(CType::Struct(format!("struct_{sid:x}"))),
        XType::Xcharptr => CType::ptr(CType::char_signed()),
        XType::Xcharptrptr => CType::ptr(CType::ptr(CType::char_signed())),
        XType::Xintptr => CType::ptr(CType::int()),
        XType::Xfloatptr => CType::ptr(CType::double()),
        XType::Xsingleptr => CType::ptr(CType::float()),
        XType::Xptr | XType::Xfuncptr => CType::ptr(CType::Void),
        XType::Xany64 => CType::int64(model, Signedness::Signed),
        _ => CType::long(),
    }
}

fn called_global_decl_types(
    vars: &InterfaceVars,
    assignments: &BTreeMap<InterfaceVarId, InterfaceClass>,
    edges: &[CallEdge],
    initial: &CommittedInterfaces,
    model: crate::abi::DataModel,
) -> BTreeMap<Ident, CType> {
    let global_ids: BTreeSet<Ident> = vars
        .vars
        .iter()
        .filter_map(|var| match var.id {
            InterfaceVarId::Global { symbol } => Some(symbol),
            _ => None,
        })
        .filter(|symbol| {
            assignments.get(&InterfaceVarId::Global { symbol: *symbol })
                == Some(&InterfaceClass::PtrFunc)
        })
        .collect();
    let mut sites: BTreeMap<Ident, Vec<&CallEdge>> = BTreeMap::new();
    for edge in edges {
        if global_ids.contains(&edge.callee) {
            sites.entry(edge.callee).or_default().push(edge);
        }
    }
    let mut out = BTreeMap::new();
    for (ident, calls) in sites {
        let counts: BTreeSet<usize> = calls.iter().map(|edge| edge.args.len()).collect();
        let min = counts.iter().next().copied().unwrap_or(0);
        let max = counts.iter().next_back().copied().unwrap_or(0);
        let signature = initial.function(ident);
        let ret = signature
            .map(|sig| xtype_to_ctype(&sig.return_type, model))
            .unwrap_or_else(CType::long);
        let fn_ty = if let Some(signature) = signature.filter(|sig| !sig.param_types.is_empty()) {
            CType::Function(
                Box::new(ret),
                signature
                    .param_types
                    .iter()
                    .map(|xt| xtype_to_ctype(xt, model))
                    .collect(),
                signature.is_varargs,
                false,
            )
        } else if min == max {
            let params = calls[0]
                .args
                .iter()
                .map(|class| match class {
                    InterfaceClass::Float => CType::double(),
                    InterfaceClass::PtrInt
                    | InterfaceClass::PtrFloat
                    | InterfaceClass::PtrFunc
                    | InterfaceClass::PtrStruct(_) => CType::ptr(CType::Void),
                    _ => CType::long(),
                })
                .collect();
            CType::Function(Box::new(ret), params, false, false)
        } else if min == 0 {
            CType::func_unprototyped(ret)
        } else {
            CType::Function(Box::new(ret), vec![CType::long(); min], true, false)
        };
        out.insert(
            ident,
            CType::Pointer(Box::new(fn_ty), TypeQualifiers::none()),
        );
    }
    out
}

pub(crate) fn selected_reg_class(
    func: &FunctionData,
    state: &ProgramSelectionState,
    reg: RTLReg,
) -> Option<InterfaceClass> {
    if let Some(candidate) = state.var_type_override.get(&(func.address, reg)) {
        return Some(InterfaceClass::from_candidate(*candidate));
    }
    if let Some(candidates) = func.var_type_candidates.get(&reg) {
        let index = state
            .var_decl_idx
            .get(&(func.address, reg))
            .copied()
            .unwrap_or(0);
        if let Some(candidate) = candidates.get(index).or_else(|| candidates.first()) {
            return Some(InterfaceClass::from_candidate(*candidate));
        }
    }
    if let Some(candidate) = func.var_types.get(&reg) {
        return Some(InterfaceClass::from_candidate(*candidate));
    }
    func.param_regs
        .iter()
        .position(|candidate| *candidate == reg)
        .and_then(|position| func.param_types.get(position))
        .map(|param| match param {
            ParamType::Pointer => InterfaceClass::PtrInt,
            ParamType::StructPointer(sid) => InterfaceClass::PtrStruct(*sid),
            ParamType::Typed(xtype) => InterfaceClass::from_xtype(xtype),
            ParamType::Integer | ParamType::Unknown => InterfaceClass::Int,
        })
}

fn expr_class(
    func: &FunctionData,
    state: &ProgramSelectionState,
    expr: &ClightExpr,
) -> InterfaceClass {
    match expr {
        ClightExpr::Etempvar(ident, _) => selected_reg_class(func, state, *ident as RTLReg)
            .unwrap_or_else(|| InterfaceClass::from_clight(expr_annotation(expr))),
        _ => InterfaceClass::from_clight(expr_annotation(expr)),
    }
}

fn bare_reg(expr: &ClightExpr) -> Option<RTLReg> {
    match expr {
        ClightExpr::Etempvar(ident, _) => Some(*ident as RTLReg),
        ClightExpr::Ecast(inner, _) => bare_reg(inner),
        _ => None,
    }
}

fn selected_reg_candidate(
    func: &FunctionData,
    state: &ProgramSelectionState,
    reg: RTLReg,
) -> Option<CandType> {
    state
        .var_type_override
        .get(&(func.address, reg))
        .cloned()
        .or_else(|| {
            let candidates = func.var_type_candidates.get(&reg)?;
            let index = state
                .var_decl_idx
                .get(&(func.address, reg))
                .copied()
                .unwrap_or(0);
            candidates
                .get(index)
                .or_else(|| candidates.first())
                .cloned()
        })
        .or_else(|| func.var_types.get(&reg).cloned())
}

fn collect_edges_stmt(
    func: &FunctionData,
    state: &ProgramSelectionState,
    name_to_ident: &HashMap<String, Ident>,
    node: Node,
    stmt: &ClightStmt,
    out: &mut Vec<CallEdge>,
) {
    match stmt {
        ClightStmt::Scall(result, callee, args) => {
            if let Some(callee) = callee_ident_from_expr(callee, name_to_ident) {
                out.push(CallEdge {
                    caller: func.address,
                    node,
                    callee,
                    args: args
                        .iter()
                        .map(|arg| expr_class(func, state, arg))
                        .collect(),
                    arg_regs: args.iter().map(bare_reg).collect(),
                    result: result
                        .and_then(|ident| selected_reg_class(func, state, ident as RTLReg)),
                    result_reg: result.map(|ident| ident as RTLReg),
                });
            }
        }
        ClightStmt::Ssequence(stmts) => {
            for stmt in stmts {
                collect_edges_stmt(func, state, name_to_ident, node, stmt, out);
            }
        }
        ClightStmt::Sifthenelse(_, yes, no) => {
            collect_edges_stmt(func, state, name_to_ident, node, yes, out);
            collect_edges_stmt(func, state, name_to_ident, node, no, out);
        }
        ClightStmt::Sloop(body, increment) => {
            collect_edges_stmt(func, state, name_to_ident, node, body, out);
            collect_edges_stmt(func, state, name_to_ident, node, increment, out);
        }
        ClightStmt::Sswitch(_, cases) => {
            for (_, stmt) in cases {
                collect_edges_stmt(func, state, name_to_ident, node, stmt, out);
            }
        }
        (ClightStmt::Slabel(_, stmt) | ClightStmt::Seffect(_, stmt)) => {
            collect_edges_stmt(func, state, name_to_ident, node, stmt, out)
        }
        _ => {}
    }
}

fn selected_stmt<'a>(
    func: &'a FunctionData,
    state: &ProgramSelectionState,
    node: Node,
) -> Option<&'a ClightStmt> {
    let candidates = func.node_statements.get(&node)?;
    let selected = state
        .candidate_idx
        .get(&(func.address, node))
        .copied()
        .unwrap_or(Some(0))?;
    candidates.get(selected).or_else(|| candidates.first())
}

fn call_edges(
    functions: &[FunctionData],
    state: &ProgramSelectionState,
    name_to_ident: &HashMap<String, Ident>,
) -> Vec<CallEdge> {
    let mut out = Vec::new();
    for func in functions {
        let mut nodes: Vec<Node> = func.node_statements.keys().copied().collect();
        nodes.sort_unstable();
        for node in nodes {
            if let Some(stmt) = selected_stmt(func, state, node) {
                collect_edges_stmt(func, state, name_to_ident, node, stmt, &mut out);
            }
        }
    }
    out.sort_by(|left, right| {
        (
            left.caller,
            left.node,
            left.callee,
            &left.args,
            &left.arg_regs,
            left.result,
            left.result_reg,
        )
            .cmp(&(
                right.caller,
                right.node,
                right.callee,
                &right.args,
                &right.arg_regs,
                right.result,
                right.result_reg,
            ))
    });
    out
}

/// Exact external ABI evidence for an internal parameter passed directly to
/// a known extern.  The Clight edge may contain a cast inserted only because
/// Stage A selected the wrong declaration; `bare_reg` deliberately looks
/// through that cast and identifies the underlying parameter object.
fn extern_pass_throughs(
    functions: &[FunctionData],
    edges: &[CallEdge],
    initial: &CommittedInterfaces,
) -> Vec<ExternPassThrough> {
    let by_addr: BTreeMap<Address, &FunctionData> =
        functions.iter().map(|func| (func.address, func)).collect();
    let mut out = Vec::new();
    for edge in edges {
        let Some(callee) = initial
            .functions
            .get(&edge.callee)
            .filter(|iface| iface.authority == InterfaceAuthority::Extern)
        else {
            continue;
        };
        let Some(caller) = by_addr.get(&edge.caller) else {
            continue;
        };
        for (callee_position, arg_reg) in edge.arg_regs.iter().enumerate() {
            let Some(arg_reg) = arg_reg else { continue };
            let Some(caller_position) = caller
                .param_regs
                .iter()
                .position(|candidate| candidate == arg_reg)
            else {
                continue;
            };
            let Some(expected) = callee.signature.param_types.get(callee_position) else {
                continue;
            };
            out.push(ExternPassThrough {
                caller: edge.caller,
                callee: edge.callee,
                node: edge.node,
                caller_position,
                callee_position,
                expected: InterfaceClass::from_xtype(expected),
            });
        }
    }
    out.sort();
    out.dedup();
    out
}

fn expr_has_temp(expr: &ClightExpr, wanted: RTLReg) -> bool {
    match expr {
        ClightExpr::Etempvar(ident, _) => *ident as RTLReg == wanted,
        ClightExpr::Ederef(inner, _)
        | ClightExpr::Eaddrof(inner, _)
        | ClightExpr::Eunop(_, inner, _)
        | ClightExpr::Ecast(inner, _)
        | ClightExpr::Efield(inner, _, _) => expr_has_temp(inner, wanted),
        ClightExpr::Ebinop(_, left, right, _) => {
            expr_has_temp(left, wanted) || expr_has_temp(right, wanted)
        }
        ClightExpr::Econdition(condition, yes, no, _) => {
            expr_has_temp(condition, wanted)
                || expr_has_temp(yes, wanted)
                || expr_has_temp(no, wanted)
        }
        _ => false,
    }
}

fn expr_has_global(expr: &ClightExpr, wanted: Ident) -> bool {
    match expr {
        ClightExpr::Evar(ident, _) => *ident == wanted,
        ClightExpr::Ederef(inner, _)
        | ClightExpr::Eaddrof(inner, _)
        | ClightExpr::Eunop(_, inner, _)
        | ClightExpr::Ecast(inner, _)
        | ClightExpr::Efield(inner, _, _) => expr_has_global(inner, wanted),
        ClightExpr::Ebinop(_, left, right, _) => {
            expr_has_global(left, wanted) || expr_has_global(right, wanted)
        }
        ClightExpr::Econdition(condition, yes, no, _) => {
            expr_has_global(condition, wanted)
                || expr_has_global(yes, wanted)
                || expr_has_global(no, wanted)
        }
        _ => false,
    }
}

fn stmt_matches(
    stmt: &ClightStmt,
    temp: Option<RTLReg>,
    global: Option<Ident>,
    returns: bool,
) -> bool {
    let expr_match = |expr: &ClightExpr| {
        temp.is_some_and(|reg| expr_has_temp(expr, reg))
            || global.is_some_and(|ident| expr_has_global(expr, ident))
    };
    match stmt {
        ClightStmt::Sassign(left, right) => expr_match(left) || expr_match(right),
        ClightStmt::Sset(ident, expr) => {
            temp.is_some_and(|reg| *ident as RTLReg == reg) || expr_match(expr)
        }
        ClightStmt::Scall(result, callee, args) => {
            result.is_some_and(|ident| temp.is_some_and(|reg| ident as RTLReg == reg))
                || expr_match(callee)
                || args.iter().any(expr_match)
        }
        ClightStmt::Sbuiltin(result, _, _, args) => {
            result.is_some_and(|ident| temp.is_some_and(|reg| ident as RTLReg == reg))
                || args.iter().any(expr_match)
        }
        ClightStmt::Ssequence(stmts) => stmts
            .iter()
            .any(|stmt| stmt_matches(stmt, temp, global, returns)),
        ClightStmt::Sifthenelse(condition, yes, no) => {
            expr_match(condition)
                || stmt_matches(yes, temp, global, returns)
                || stmt_matches(no, temp, global, returns)
        }
        ClightStmt::Sloop(body, increment) => {
            stmt_matches(body, temp, global, returns)
                || stmt_matches(increment, temp, global, returns)
        }
        ClightStmt::Sreturn(expr) => returns || expr.as_ref().is_some_and(expr_match),
        ClightStmt::Sswitch(expr, cases) => {
            expr_match(expr)
                || cases
                    .iter()
                    .any(|(_, stmt)| stmt_matches(stmt, temp, global, returns))
        }
        (ClightStmt::Slabel(_, stmt) | ClightStmt::Seffect(_, stmt)) => stmt_matches(stmt, temp, global, returns),
        _ => false,
    }
}

pub(crate) fn functions_referencing_globals(
    functions: &[FunctionData],
    symbols: &BTreeSet<Ident>,
) -> BTreeSet<Address> {
    functions
        .iter()
        .filter(|func| {
            func.node_statements.values().any(|candidates| {
                candidates.iter().any(|stmt| {
                    symbols
                        .iter()
                        .any(|&symbol| stmt_matches(stmt, None, Some(symbol), false))
                })
            })
        })
        .map(|func| func.address)
        .collect()
}

fn vote_expr(expr: &ClightExpr, votes: &mut BTreeMap<RTLReg, DeclVotes>) {
    use crate::x86::types::{ClightBinaryOp as B, ClightExpr as E, ClightUnaryOp as U};
    match expr {
        E::Ebinop(op, left, right, ty) => {
            let integer_only =
                matches!(op, B::Omod | B::Oand | B::Oor | B::Oxor | B::Oshl | B::Oshr)
                    || (matches!(op, B::Omul | B::Odiv) && !matches!(ty, ClightType::Tfloat(..)));
            let float_arithmetic = matches!(ty, ClightType::Tfloat(..))
                && matches!(op, B::Oadd | B::Osub | B::Omul | B::Odiv);
            for side in [left.as_ref(), right.as_ref()] {
                if let Some(reg) = bare_reg(side) {
                    if integer_only {
                        votes.entry(reg).or_default().int_use += 1;
                    }
                    if float_arithmetic {
                        votes.entry(reg).or_default().float_use += 1;
                    }
                }
            }
            vote_expr(left, votes);
            vote_expr(right, votes);
        }
        E::Eunop(U::Onotint, inner, _) => {
            if let Some(reg) = bare_reg(inner) {
                votes.entry(reg).or_default().int_use += 1;
            }
            vote_expr(inner, votes);
        }
        E::Ederef(inner, _) => {
            let base = match inner.as_ref() {
                E::Ebinop(B::Oadd, left, _, _) => left.as_ref(),
                other => other,
            };
            if let Some(reg) = bare_reg(base) {
                votes.entry(reg).or_default().ptr_use += 1;
            }
            vote_expr(inner, votes);
        }
        E::Efield(base, _, _) => {
            let base = match base.as_ref() {
                E::Ederef(inner, _) => inner.as_ref(),
                other => other,
            };
            if let Some(reg) = bare_reg(base) {
                votes.entry(reg).or_default().ptr_use += 1;
            }
            vote_expr(base, votes);
        }
        E::Ecast(inner, ty) => {
            if matches!(ty, ClightType::Tfloat(..)) {
                if let Some(reg) = bare_reg(inner) {
                    votes.entry(reg).or_default().float_use += 1;
                }
            }
            vote_expr(inner, votes);
        }
        E::Eaddrof(inner, _) | E::Eunop(_, inner, _) => vote_expr(inner, votes),
        E::Econdition(condition, yes, no, _) => {
            vote_expr(condition, votes);
            vote_expr(yes, votes);
            vote_expr(no, votes);
        }
        _ => {}
    }
}

fn vote_stmt(
    stmt: &ClightStmt,
    votes: &mut BTreeMap<RTLReg, DeclVotes>,
    signatures: &HashMap<Ident, CalleeSignature>,
    name_to_ident: &HashMap<String, Ident>,
) {
    use crate::x86::types::{ClightBinaryOp as B, ClightExpr as E, ClightStmt as S};
    match stmt {
        S::Sassign(left, right) => {
            if let E::Ederef(inner, _) = left {
                if let Some(reg) = bare_reg(inner) {
                    votes.entry(reg).or_default().ptr_use += 1;
                }
            }
            vote_expr(left, votes);
            vote_expr(right, votes);
        }
        S::Sset(ident, expr) => {
            let integer_only = matches!(
                expr,
                E::Ebinop(B::Omod | B::Oand | B::Oor | B::Oxor | B::Oshl | B::Oshr, ..)
                    | E::Eunop(crate::x86::types::ClightUnaryOp::Onotint, ..)
            ) || matches!(
                expr,
                E::Ebinop(B::Omul | B::Odiv, _, _, ty)
                    if !matches!(ty, ClightType::Tfloat(..))
            );
            if !integer_only && matches!(expr_annotation(expr), ClightType::Tfloat(..)) {
                votes.entry(*ident as RTLReg).or_default().float_use += 1;
            }
            vote_expr(expr, votes);
        }
        S::Scall(_, callee, args) => {
            if let Some(signature) = callee_ident_from_expr(callee, name_to_ident)
                .and_then(|ident| signatures.get(&ident))
            {
                for (position, arg) in args.iter().enumerate() {
                    if signature
                        .param_types
                        .get(position)
                        .is_some_and(|xtype| InterfaceClass::from_xtype(xtype).is_pointer())
                    {
                        if let Some(reg) = bare_reg(arg) {
                            votes.entry(reg).or_default().ptr_use += 1;
                        }
                    }
                }
            }
            vote_expr(callee, votes);
            for arg in args {
                vote_expr(arg, votes);
            }
        }
        S::Sbuiltin(_, _, _, args) => {
            for arg in args {
                vote_expr(arg, votes);
            }
        }
        S::Sreturn(Some(expr)) => vote_expr(expr, votes),
        S::Ssequence(stmts) => {
            for stmt in stmts {
                vote_stmt(stmt, votes, signatures, name_to_ident);
            }
        }
        S::Sifthenelse(condition, yes, no) => {
            vote_expr(condition, votes);
            vote_stmt(yes, votes, signatures, name_to_ident);
            vote_stmt(no, votes, signatures, name_to_ident);
        }
        S::Sloop(body, increment) => {
            vote_stmt(body, votes, signatures, name_to_ident);
            vote_stmt(increment, votes, signatures, name_to_ident);
        }
        S::Sswitch(expr, cases) => {
            vote_expr(expr, votes);
            for (_, stmt) in cases {
                vote_stmt(stmt, votes, signatures, name_to_ident);
            }
        }
        S::Slabel(_, stmt) => vote_stmt(stmt, votes, signatures, name_to_ident),
        _ => {}
    }
}

/// Preserve decl_solve's old unambiguous register correction semantics inside
/// Stage B. Float evidence is a veto for integer/pointer corrections, never a
/// reason to turn an integer or pointer declaration into `double`.
fn declaration_vote_target(
    rank0: InterfaceClass,
    votes: DeclVotes,
) -> Option<(InterfaceClass, u32)> {
    if (rank0 == InterfaceClass::Float || rank0.is_pointer())
        && votes.int_use > 0
        && votes.float_use == 0
        && votes.ptr_use == 0
    {
        Some((InterfaceClass::Int, votes.int_use))
    } else if rank0 == InterfaceClass::Int
        && votes.ptr_use > 0
        && votes.int_use == 0
        && votes.float_use == 0
    {
        Some((InterfaceClass::PtrInt, votes.ptr_use))
    } else {
        None
    }
}

fn declaration_vars(
    functions: &[FunctionData],
    state: &ProgramSelectionState,
    committed: &CommittedInterfaces,
    name_to_ident: &HashMap<String, Ident>,
) -> (
    Vec<DeclarationVar>,
    BTreeMap<Address, BTreeMap<RTLReg, DeclVotes>>,
) {
    let signatures = committed.callee_signatures();
    let mut all_votes = BTreeMap::new();
    let mut declarations = Vec::new();
    for func in functions {
        let mut votes: BTreeMap<RTLReg, DeclVotes> = BTreeMap::new();
        // Preserve the absorbed declaration authority exactly: a recovered
        // pointer parameter is evidence about the one C object represented by
        // its RTL register.  It is not, however, a second call-graph variable.
        for (&reg, param) in func.param_regs.iter().zip(&func.param_types) {
            let is_pointer = match param {
                ParamType::Pointer | ParamType::StructPointer(_) => true,
                ParamType::Typed(xtype) => InterfaceClass::from_xtype(xtype).is_pointer(),
                ParamType::Integer | ParamType::Unknown => false,
            };
            if is_pointer {
                votes.entry(reg).or_default().ptr_use += 1;
            }
        }
        let mut nodes: Vec<Node> = func.node_statements.keys().copied().collect();
        nodes.sort_unstable();
        for node in nodes {
            if let Some(stmt) = selected_stmt(func, state, node) {
                vote_stmt(stmt, &mut votes, &signatures, name_to_ident);
            }
        }

        for reg in votes.keys().copied() {
            let reg_votes = votes.get(&reg).copied().unwrap_or_default();
            // Parameter declarations are the corresponding interface
            // variables; giving them a second solver variable would create
            // two owners for one C object.
            if func.param_regs.contains(&reg) {
                continue;
            }
            let Some(rank0_candidate) = selected_reg_candidate(func, state, reg) else {
                continue;
            };
            let rank0 = InterfaceClass::from_candidate(rank0_candidate);
            let Some((target, _)) = declaration_vote_target(rank0, reg_votes) else {
                continue;
            };
            // The absorbed authority intentionally may add the representative
            // target in Stage C.  Candidate cardinality is a generation
            // artifact, and the retired emitter override likewise did not
            // require that the opposite class had already been generated.
            let mut domain = vec![rank0];
            if target != rank0 {
                domain.push(target);
            }
            declarations.push(DeclarationVar {
                function: func.address,
                reg,
                domain,
                votes: reg_votes,
            });
        }
        all_votes.insert(func.address, votes);
    }
    declarations.sort_by_key(|decl| (decl.function, decl.reg));
    (declarations, all_votes)
}

fn assert_declaration_vote_clause(
    opt: &Optimize,
    variable: &Int,
    domain: &[InterfaceClass],
    rank0: InterfaceClass,
    votes: DeclVotes,
) {
    let Some((target, count)) = declaration_vote_target(rank0, votes) else {
        return;
    };
    let target_index = domain.iter().position(|class| {
        if target.is_pointer() {
            class.is_pointer()
        } else {
            *class == target
        }
    });
    if let Some(index) = target_index {
        opt.assert_soft(
            &variable._eq(Int::from_u64(index as u64)),
            config::CONFIG
                .interface
                .structural_weight
                .saturating_mul(count as u64),
            None,
        );
    }
}

fn selected_temp_types(
    func: &FunctionData,
    state: &ProgramSelectionState,
    override_param: Option<(RTLReg, XType)>,
) -> HashMap<Ident, ClightType> {
    let mut temps = HashMap::new();
    for (&reg, candidates) in &func.var_type_candidates {
        let chosen = state
            .var_type_override
            .get(&(func.address, reg))
            .cloned()
            .or_else(|| {
                let index = state
                    .var_decl_idx
                    .get(&(func.address, reg))
                    .copied()
                    .unwrap_or(0);
                candidates
                    .get(index)
                    .or_else(|| candidates.first())
                    .cloned()
            });
        if let Some(chosen) = chosen {
            temps.insert(reg as Ident, wt_audit::candtype_to_clight(chosen));
        }
    }
    for (&reg, candidate) in &func.var_types {
        temps
            .entry(reg as Ident)
            .or_insert_with(|| wt_audit::candtype_to_clight(*candidate));
    }
    for (&reg, param) in func.param_regs.iter().zip(&func.param_types) {
        let overridden_param_ty = override_param
            .as_ref()
            .filter(|(wanted, _)| *wanted == reg)
            .map(|(_, xtype)| wt_audit::xtype_to_clight(&xtype));
        let has_explicit_override = overridden_param_ty.is_some();
        let param_ty = overridden_param_ty.unwrap_or_else(|| wt_audit::param_type_to_clight(param));
        match temps.get(&(reg as Ident)) {
            // A rank-0 `long` parameter may retain a more refined selected
            // temp declaration.  An explicit marginal-cost alternative may
            // not: it must be checked as the declaration it proposes.
            Some(_)
                if !has_explicit_override
                    && matches!(param_ty, ClightType::Tlong(ClightSignedness::Signed, _)) => {}
            _ => {
                temps.insert(reg as Ident, param_ty);
            }
        }
    }
    temps
}

fn marginal_costs(
    var: &InterfaceVar,
    functions: &[FunctionData],
    state: &ProgramSelectionState,
    committed: &CommittedInterfaces,
    edges: &[CallEdge],
    name_to_ident: &HashMap<String, Ident>,
    by_addr: &BTreeMap<Address, usize>,
) -> Vec<(u64, u64)> {
    let mut affected: BTreeMap<usize, BTreeSet<Node>> = BTreeMap::new();
    let mut own_param = None;
    let mut own_return = None;
    let mut global = None;
    match var.id {
        InterfaceVarId::Param { function, position } => {
            if let Some(&index) = by_addr.get(&(function as Address)) {
                own_param = functions[index].param_regs.get(position).copied();
                let mut nodes: Vec<Node> =
                    functions[index].node_statements.keys().copied().collect();
                nodes.sort_unstable();
                if let Some(reg) = own_param {
                    for node in nodes {
                        if selected_stmt(&functions[index], state, node)
                            .is_some_and(|stmt| stmt_matches(stmt, Some(reg), None, false))
                        {
                            affected.entry(index).or_default().insert(node);
                        }
                    }
                }
            }
        }
        InterfaceVarId::Return { function } => {
            if let Some(&index) = by_addr.get(&(function as Address)) {
                own_return = Some(index);
                let mut nodes: Vec<Node> =
                    functions[index].node_statements.keys().copied().collect();
                nodes.sort_unstable();
                for node in nodes {
                    if selected_stmt(&functions[index], state, node)
                        .is_some_and(|stmt| stmt_matches(stmt, None, None, true))
                    {
                        affected.entry(index).or_default().insert(node);
                    }
                }
            }
        }
        InterfaceVarId::Global { symbol } => {
            global = Some(symbol);
            for (index, func) in functions.iter().enumerate() {
                let mut nodes: Vec<Node> = func.node_statements.keys().copied().collect();
                nodes.sort_unstable();
                for node in nodes {
                    if selected_stmt(func, state, node)
                        .is_some_and(|stmt| stmt_matches(stmt, None, Some(symbol), false))
                    {
                        affected.entry(index).or_default().insert(node);
                    }
                }
            }
        }
    }
    let target_function = match var.id {
        InterfaceVarId::Param { function, .. } | InterfaceVarId::Return { function } => {
            Some(function)
        }
        InterfaceVarId::Global { .. } => None,
    };
    if let Some(target) = target_function {
        for edge in edges.iter().filter(|edge| edge.callee == target) {
            if let Some(&index) = by_addr.get(&edge.caller) {
                affected.entry(index).or_default().insert(edge.node);
            }
        }
    }

    let base_signatures = committed.callee_signatures();
    let mut raw = Vec::with_capacity(var.domain.len());
    for alternative in &var.domain {
        let mut signatures = base_signatures.clone();
        match var.id {
            InterfaceVarId::Param { function, position } => {
                if let Some(signature) = signatures.get_mut(&function) {
                    if position < signature.param_types.len() {
                        signature.param_types[position] = alternative.xtype;
                    }
                }
            }
            InterfaceVarId::Return { function } => {
                if let Some(signature) = signatures.get_mut(&function) {
                    signature.return_type = alternative.xtype;
                }
            }
            InterfaceVarId::Global { .. } => {}
        }

        let mut errors = 0u64;
        let mut structural = 0u64;
        for (&index, nodes) in &affected {
            let func = &functions[index];
            let override_param = match var.id {
                InterfaceVarId::Param { function, .. } if function as Address == func.address => {
                    own_param.map(|reg| (reg, alternative.xtype))
                }
                _ => None,
            };
            let temps = selected_temp_types(func, state, override_param);
            let (fields, known) = wt_audit::fields_from_struct_fields(&func.struct_fields);
            let return_type = if own_return == Some(index) {
                wt_audit::xtype_to_clight(&alternative.xtype)
            } else {
                func.return_type.clone()
            };
            let mut known_globals: KnownGlobalTypes = func.known_global_types.as_ref().clone();
            if let Some(symbol) = global {
                known_globals
                    .by_ident
                    .insert(symbol, wt_audit::xtype_to_clight(&alternative.xtype));
            }
            let env = AuditEnv::from_parts(
                temps,
                fields,
                known,
                return_type,
                &signatures,
                name_to_ident,
                &known_globals,
                func.ptr64,
            );
            for &node in nodes {
                if let Some(stmt) = selected_stmt(func, state, node) {
                    let diagnostics = ctyping::wt_check_stmt(stmt, &env);
                    errors += ctyping::error_count(&diagnostics) as u64;
                    structural += diagnostics
                        .iter()
                        .filter(|diagnostic| diagnostic.severity == Severity::Warning)
                        .count() as u64;
                }
            }
        }
        raw.push((errors, structural));
    }
    let min_errors = raw.iter().map(|cost| cost.0).min().unwrap_or(0);
    let min_structural = raw
        .iter()
        .filter(|cost| cost.0 == min_errors)
        .map(|cost| cost.1)
        .min()
        .unwrap_or(0);
    raw.into_iter()
        .map(|(errors, structural)| {
            (
                errors.saturating_sub(min_errors),
                if errors == min_errors {
                    structural.saturating_sub(min_structural)
                } else {
                    structural
                },
            )
        })
        .collect()
}

fn stage_a_preferences(
    vars: &InterfaceVars,
    functions: &[FunctionData],
    state: &ProgramSelectionState,
) -> BTreeMap<InterfaceVarId, InterfaceClass> {
    let by_addr: BTreeMap<Address, &FunctionData> =
        functions.iter().map(|func| (func.address, func)).collect();
    vars.vars
        .iter()
        .map(|var| {
            let preference = match var.id {
                InterfaceVarId::Param { function, position } => by_addr
                    .get(&(function as Address))
                    .and_then(|func| func.param_regs.get(position).map(|reg| (*func, *reg)))
                    .and_then(|(func, reg)| selected_reg_class(func, state, reg))
                    .unwrap_or(var.domain[0].class),
                InterfaceVarId::Return { .. } | InterfaceVarId::Global { .. } => {
                    var.domain[0].class
                }
            };
            (var.id.clone(), preference)
        })
        .collect()
}

pub(crate) fn solve(
    functions: &[FunctionData],
    state: &ProgramSelectionState,
    vars: &InterfaceVars,
    initial: &CommittedInterfaces,
    name_to_ident: &HashMap<String, Ident>,
    model: crate::abi::DataModel,
) -> InterfaceSolveOutcome {
    solve_with_global_feedback(
        functions,
        state,
        vars,
        initial,
        name_to_ident,
        &[],
        None,
        model,
    )
}

/// Re-open only the Stage-B variables named by final flow disagreements.  The
/// disagreements become ordinary agreement-stratum soft clauses; unrelated
/// interface commitments are pinned to the previous Stage-B assignment so a
/// feedback pass cannot perturb them through solver tie-breaking.
pub(crate) fn solve_with_global_feedback(
    functions: &[FunctionData],
    state: &ProgramSelectionState,
    vars: &InterfaceVars,
    initial: &CommittedInterfaces,
    name_to_ident: &HashMap<String, Ident>,
    flow_feedback: &[GlobalFlowDisagreement],
    prior_choice_ranks: Option<&BTreeMap<InterfaceVarId, usize>>,
    model: crate::abi::DataModel,
) -> InterfaceSolveOutcome {
    let started = std::time::Instant::now();
    let feedback: BTreeSet<GlobalFlowDisagreement> = flow_feedback.iter().copied().collect();
    let mut feedback_by_symbol: BTreeMap<
        Ident,
        Vec<crate::decompile::passes::clight_select::flow::AVal>,
    > = BTreeMap::new();
    for item in &feedback {
        feedback_by_symbol
            .entry(item.symbol)
            .or_default()
            .push(item.claimed);
    }
    let reopened: BTreeSet<InterfaceVarId> = feedback_by_symbol
        .keys()
        .map(|&symbol| InterfaceVarId::Global { symbol })
        .collect();
    let ptr64 = functions.first().map(|func| func.ptr64).unwrap_or(true);
    let edges = call_edges(functions, state, name_to_ident);
    let extern_pass_throughs = extern_pass_throughs(functions, &edges, initial);
    let preferences = stage_a_preferences(vars, functions, state);
    let (declarations, declaration_votes) =
        declaration_vars(functions, state, initial, name_to_ident);
    let by_addr: BTreeMap<Address, usize> = functions
        .iter()
        .enumerate()
        .map(|(index, func)| (func.address, index))
        .collect();
    let costs: Vec<Vec<(u64, u64)>> = vars
        .vars
        .iter()
        .map(|var| {
            marginal_costs(
                var,
                functions,
                state,
                initial,
                &edges,
                name_to_ident,
                &by_addr,
            )
        })
        .collect();

    let mut var_index = BTreeMap::new();
    for (index, var) in vars.vars.iter().enumerate() {
        var_index.insert(var.id.clone(), index);
    }
    let interface_domains: Vec<Vec<InterfaceClass>> = vars
        .vars
        .iter()
        .map(|var| {
            var.domain
                .iter()
                .map(|alternative| alternative.class)
                .collect()
        })
        .collect();
    let (choices, declaration_choices, solve_result, no_model) =
        z3::with_z3_config(&z3::Config::new(), || {
            let opt = Optimize::new();
            let mut params = z3::Params::new();
            params.set_u32("random_seed", 0);
            params.set_u32("timeout", config::CONFIG.solve.timeout_ms);
            opt.set_params(&params);
            let zvars: Vec<Int> = vars
                .vars
                .iter()
                .map(|_| Int::fresh_const("interface"))
                .collect();
            let declaration_zvars: Vec<Int> = declarations
                .iter()
                .map(|_| Int::fresh_const("interface_decl"))
                .collect();
            for (index, var) in vars.vars.iter().enumerate() {
                let zvar = &zvars[index];
                opt.assert(&zvar.ge(Int::from_i64(0)));
                opt.assert(&zvar.lt(Int::from_u64(var.domain.len() as u64)));
                if var.hard_rank0 {
                    opt.assert(&zvar._eq(Int::from_i64(0)));
                }
                if let Some(&previous_rank) = prior_choice_ranks
                    .and_then(|assignments| assignments.get(&var.id))
                    .filter(|_| !reopened.contains(&var.id))
                {
                    if previous_rank < var.domain.len() {
                        opt.assert(&zvar._eq(Int::from_u64(previous_rank as u64)));
                    }
                }
                opt.assert_soft(
                    &zvar._eq(Int::from_i64(0)),
                    config::CONFIG.interface.prior_weight,
                    None,
                );
                for (alternative, (legality, structural)) in costs[index].iter().enumerate() {
                    if *legality > 0 {
                        opt.assert_soft(
                            &zvar._eq(Int::from_u64(alternative as u64)).not(),
                            config::CONFIG
                                .interface
                                .legality_weight
                                .saturating_mul(*legality),
                            None,
                        );
                    }
                    if *structural > 0 {
                        opt.assert_soft(
                            &zvar._eq(Int::from_u64(alternative as u64)).not(),
                            config::CONFIG
                                .interface
                                .structural_weight
                                .saturating_mul(*structural),
                            None,
                        );
                    }
                }
                if let InterfaceVarId::Global { symbol } = var.id {
                    if let Some(claims) = feedback_by_symbol.get(&symbol) {
                        for claim in claims {
                            let compatible: Vec<Bool> = var
                                .domain
                                .iter()
                                .enumerate()
                                .filter(|(_, alternative)| {
                                    crate::decompile::passes::clight_select::flow::anchor_of_xtype(
                                        &alternative.xtype,
                                        ptr64,
                                    )
                                    .compatible(*claim)
                                })
                                .map(|(rank, _)| zvar._eq(Int::from_u64(rank as u64)))
                                .collect();
                            if !compatible.is_empty() {
                                let refs: Vec<&Bool> = compatible.iter().collect();
                                opt.assert_soft(
                                    &Bool::or(&refs),
                                    config::CONFIG.interface.agreement_weight,
                                    None,
                                );
                            }
                        }
                    }
                }
            }
            for (index, declaration) in declarations.iter().enumerate() {
                let zvar = &declaration_zvars[index];
                opt.assert(&zvar.ge(Int::from_i64(0)));
                opt.assert(&zvar.lt(Int::from_u64(declaration.domain.len() as u64)));
                opt.assert_soft(
                    &zvar._eq(Int::from_i64(0)),
                    config::CONFIG.interface.prior_weight,
                    None,
                );
                assert_declaration_vote_clause(
                    &opt,
                    zvar,
                    &declaration.domain,
                    declaration.domain[0],
                    declaration.votes,
                );
            }

            // A known external ABI is stronger than the currently selected
            // caller expression, whose cast and pointer annotation may be a
            // consequence of the very interface error Stage B is solving.
            // Keep this soft: a source wrapper may intentionally cast its own
            // parameter before the call.  Structural weight makes exact ABI
            // evidence dominate ordinary call-site agreement and the rank-0
            // prior, while legality remains the higher stratum.
            for pass_through in &extern_pass_throughs {
                let id = InterfaceVarId::Param {
                    function: pass_through.caller as Ident,
                    position: pass_through.caller_position,
                };
                let Some(&index) = var_index.get(&id) else {
                    continue;
                };
                let Some(alternative) = vars.vars[index]
                    .domain
                    .iter()
                    .position(|candidate| candidate.class == pass_through.expected)
                else {
                    continue;
                };
                opt.assert_soft(
                    &zvars[index]._eq(Int::from_u64(alternative as u64)),
                    config::CONFIG.interface.structural_weight,
                    None,
                );
            }

            // A parameter register is the C parameter object itself, so its
            // selected-use evidence constrains pi directly rather than creating a
            // duplicate declaration variable.
            for func in functions {
                let Some(votes) = declaration_votes.get(&func.address) else {
                    continue;
                };
                for (position, &reg) in func.param_regs.iter().enumerate() {
                    let Some(&index) = var_index.get(&InterfaceVarId::Param {
                        function: func.address as Ident,
                        position,
                    }) else {
                        continue;
                    };
                    if let Some(&votes) = votes.get(&reg) {
                        assert_declaration_vote_clause(
                            &opt,
                            &zvars[index],
                            &interface_domains[index],
                            preferences[&vars.vars[index].id],
                            votes,
                        );
                    }
                }
            }
            for edge in &edges {
                let global_id = InterfaceVarId::Global {
                    symbol: edge.callee,
                };
                if let Some(&index) = var_index.get(&global_id) {
                    if let Some(alternative) = vars.vars[index]
                        .domain
                        .iter()
                        .position(|candidate| candidate.class == InterfaceClass::PtrFunc)
                    {
                        opt.assert_soft(
                            &zvars[index]._eq(Int::from_u64(alternative as u64)),
                            config::CONFIG.interface.agreement_weight,
                            None,
                        );
                    }
                }
                for (position, class) in edge.args.iter().copied().enumerate() {
                    let id = InterfaceVarId::Param {
                        function: edge.callee,
                        position,
                    };
                    let Some(&index) = var_index.get(&id) else {
                        continue;
                    };
                    if let Some(alternative) = vars.vars[index]
                        .domain
                        .iter()
                        .position(|candidate| candidate.class == class)
                    {
                        opt.assert_soft(
                            &zvars[index]._eq(Int::from_u64(alternative as u64)),
                            config::CONFIG.interface.agreement_weight,
                            None,
                        );
                    }
                }
                if let Some(class) = edge.result {
                    let id = InterfaceVarId::Return {
                        function: edge.callee,
                    };
                    if let Some(&index) = var_index.get(&id) {
                        if let Some(alternative) = vars.vars[index]
                            .domain
                            .iter()
                            .position(|candidate| candidate.class == class)
                        {
                            opt.assert_soft(
                                &zvars[index]._eq(Int::from_u64(alternative as u64)),
                                config::CONFIG.interface.agreement_weight,
                                None,
                            );
                        }
                    }
                }
            }

            let result = opt.check(&[]);
            if result != SatResult::Sat {
                return (
                    vec![0usize; vars.vars.len()],
                    vec![0usize; declarations.len()],
                    result,
                    false,
                );
            }
            let Some(model) = opt.get_model() else {
                return (
                    vec![0usize; vars.vars.len()],
                    vec![0usize; declarations.len()],
                    result,
                    true,
                );
            };
            let choices = zvars
                .iter()
                .zip(&vars.vars)
                .map(|(zvar, var)| {
                    model
                        .eval(zvar, true)
                        .and_then(|value| value.as_u64())
                        .map(|value| value as usize)
                        .filter(|value| *value < var.domain.len())
                        .unwrap_or(0)
                })
                .collect();
            let declaration_choices = declaration_zvars
                .iter()
                .zip(&declarations)
                .map(|(zvar, declaration)| {
                    model
                        .eval(zvar, true)
                        .and_then(|value| value.as_u64())
                        .map(|value| value as usize)
                        .filter(|value| *value < declaration.domain.len())
                        .unwrap_or(0)
                })
                .collect();
            (choices, declaration_choices, result, false)
        });
    let fell_back = solve_result != SatResult::Sat || no_model;
    if fell_back {
        eprintln!(
            "[interface-solve] WARN: program interface instance returned {:?}{}; retaining rank-0 assignments for the component without weakening hard evidence",
            solve_result,
            if no_model { " without a model" } else { "" },
        );
    }

    let mut committed = initial.clone();
    let mut assignments = BTreeMap::new();
    let mut choice_ranks = BTreeMap::new();
    let mut changed_from_rank0 = 0usize;
    for (var, choice) in vars.vars.iter().zip(&choices) {
        let alternative = &var.domain[*choice];
        assignments.insert(var.id.clone(), alternative.class);
        choice_ranks.insert(var.id.clone(), *choice);
        changed_from_rank0 += usize::from(*choice != 0);
        match var.id {
            InterfaceVarId::Param { function, position } => {
                if let Some(interface) = committed.functions.get_mut(&function) {
                    if position < interface.signature.param_types.len() {
                        interface.signature.param_types[position] = alternative.xtype;
                    }
                }
            }
            InterfaceVarId::Return { function } => {
                if let Some(interface) = committed.functions.get_mut(&function) {
                    interface.signature.return_type = alternative.xtype;
                }
            }
            InterfaceVarId::Global { symbol } => {
                committed.globals.insert(symbol, alternative.xtype);
            }
        }
    }
    for (name, interface) in committed.by_name.iter_mut() {
        if let Some(ident) = name_to_ident.get(name) {
            if let Some(committed_function) = committed.functions.get(ident) {
                interface.signature = committed_function.signature.clone();
            }
        }
    }
    committed.global_decl_types =
        called_global_decl_types(vars, &assignments, &edges, initial, model);

    let mut dirty_functions = BTreeSet::new();
    for (id, chosen) in &assignments {
        if preferences.get(id) == Some(chosen) {
            continue;
        }
        if let InterfaceVarId::Param { function, .. } | InterfaceVarId::Return { function } = id {
            dirty_functions.insert(*function as Address);
        }
    }
    let mut declaration_assignments = BTreeMap::new();
    for (declaration, &choice) in declarations.iter().zip(&declaration_choices) {
        if choice == 0 {
            continue;
        }
        declaration_assignments.insert(
            (declaration.function, declaration.reg),
            declaration.domain[choice],
        );
        dirty_functions.insert(declaration.function);
    }

    let mut dump = format!(
        "# weights legality={} structural={} agreement={} prior={}\nkind\tid\thard\trank0\tpreference\tchosen\tdomain\tcosts-or-votes\n",
        config::CONFIG.interface.legality_weight,
        config::CONFIG.interface.structural_weight,
        config::CONFIG.interface.agreement_weight,
        config::CONFIG.interface.prior_weight,
    );
    for (index, var) in vars.vars.iter().enumerate() {
        let cost_text = costs[index]
            .iter()
            .enumerate()
            .map(|(rank, (legality, structural))| format!("{rank}:{legality}/{structural}"))
            .collect::<Vec<_>>()
            .join(",");
        dump.push_str(&format!(
            "interface\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            var.id.label(),
            var.hard_rank0,
            var.domain[0].class.label(),
            preferences[&var.id].label(),
            assignments[&var.id].label(),
            var.domain
                .iter()
                .enumerate()
                .map(|(rank, alternative)| format!(
                    "{rank}:{}:{:?}",
                    alternative.class.label(),
                    alternative.xtype
                ))
                .collect::<Vec<_>>()
                .join(","),
            cost_text,
        ));
    }
    for (index, declaration) in declarations.iter().enumerate() {
        let choice = declaration_choices[index];
        dump.push_str(&format!(
            "declaration\tdecl:{:x}:{:x}\tfalse\t{}\t{}\t{}\t{}\tint:{},float:{},ptr:{}\n",
            declaration.function,
            declaration.reg,
            declaration.domain[0].label(),
            declaration.domain[0].label(),
            declaration.domain[choice].label(),
            declaration
                .domain
                .iter()
                .enumerate()
                .map(|(rank, class)| format!("{rank}:{}", class.label()))
                .collect::<Vec<_>>()
                .join(","),
            declaration.votes.int_use,
            declaration.votes.float_use,
            declaration.votes.ptr_use,
        ));
    }
    for item in &feedback {
        dump.push_str(&format!(
            "# flow-price function={:x} node={:x} global={:x} claimed={}\n",
            item.function,
            item.node,
            item.symbol,
            crate::decompile::passes::clight_select::flow::aval_label(item.claimed),
        ));
    }
    for pass_through in &extern_pass_throughs {
        dump.push_str(&format!(
            "# extern-pass-through caller={:x} node={:x} callee={:x} caller-param={} callee-param={} expected={}\n",
            pass_through.caller,
            pass_through.node,
            pass_through.callee,
            pass_through.caller_position,
            pass_through.callee_position,
            pass_through.expected.label(),
        ));
    }
    for edge in &edges {
        dump.push_str(&format!(
            "# edge caller={:x} node={:x} callee={:x} args={} arg_regs={} result={} result_reg={}\n",
            edge.caller,
            edge.node,
            edge.callee,
            edge.args
                .iter()
                .map(|class| class.label())
                .collect::<Vec<_>>()
                .join(","),
            edge.arg_regs
                .iter()
                .map(|reg| reg
                    .map(|reg| format!("{reg:x}"))
                    .unwrap_or_else(|| "-".into()))
                .collect::<Vec<_>>()
                .join(","),
            edge.result
                .map(|class| class.label())
                .unwrap_or_else(|| "void".into()),
            edge.result_reg
                .map(|reg| format!("{reg:x}"))
                .unwrap_or_else(|| "-".into()),
        ));
    }
    let changed_declarations = declaration_assignments.len();

    InterfaceSolveOutcome {
        committed,
        stage_a_preferences: preferences,
        assignments,
        choice_ranks,
        declaration_assignments,
        dirty_functions,
        stats: InterfaceSolveStats {
            variable_count: vars.vars.len(),
            declaration_variable_count: declarations.len(),
            edge_count: edges.len(),
            solve_ms: started.elapsed().as_millis(),
            unsat_count: usize::from(solve_result == SatResult::Unsat),
            fallback_count: usize::from(fell_back),
            changed_from_rank0,
            changed_declarations,
        },
        instance_dump: dump,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::passes::clight_select::query::{
        CommittedFunctionInterface, InterfaceAlternative, InterfaceAuthority,
    };
    use crate::x86::types::{CallConv, ClightAttr, ClightFloatSize, ClightIntSize};
    use std::sync::Arc;

    fn synthetic_ids<const N: usize>() -> [u64; N] {
        std::array::from_fn(|index| index as u64 + 1)
    }

    fn int_ty() -> ClightType {
        ClightType::Tint(
            ClightIntSize::I32,
            ClightSignedness::Signed,
            ClightAttr::default(),
        )
    }

    fn float_ty() -> ClightType {
        ClightType::Tfloat(ClightFloatSize::F64, ClightAttr::default())
    }

    fn fixture(hard_rank0: bool) -> (InterfaceSolveOutcome, Address, Address) {
        let [callee_addr, caller_addr] = synthetic_ids();
        let param = 7;
        let caller_arg = 11;
        let mut callee = FunctionData::new(
            callee_addr,
            "callee".into(),
            vec![param],
            vec![ParamType::Typed(XType::Xfloat)],
            None,
            0,
            1,
            true,
        );
        callee.used_regs.insert(param);
        callee
            .var_type_candidates
            .insert(param, vec![CandType::F64, CandType::I64(Sign::Signed)]);
        callee
            .node_statements
            .insert(1, vec![ClightStmt::Sreturn(None)]);

        let callee_ty = ClightType::Tfunction(
            Arc::new(vec![float_ty()]),
            Arc::new(ClightType::Tvoid),
            CallConv::default(),
        );
        let mut caller = FunctionData::new(
            caller_addr,
            "caller".into(),
            Vec::new(),
            Vec::new(),
            None,
            0,
            2,
            true,
        );
        caller.used_regs.insert(caller_arg);
        caller
            .var_type_candidates
            .insert(caller_arg, vec![CandType::I64(Sign::Signed), CandType::F64]);
        caller.node_statements.insert(
            2,
            vec![ClightStmt::Scall(
                None,
                ClightExpr::EvarSymbol("callee".into(), callee_ty),
                vec![ClightExpr::Etempvar(caller_arg as Ident, int_ty())],
            )],
        );

        let signature = CalleeSignature {
            param_count: 1,
            return_type: XType::Xvoid,
            param_types: vec![XType::Xfloat],
            is_varargs: false,
        };
        let mut committed = CommittedInterfaces::default();
        committed.functions.insert(
            callee_addr as Ident,
            CommittedFunctionInterface {
                signature: signature.clone(),
                authority: InterfaceAuthority::Reconciled,
            },
        );
        for func in [&mut callee, &mut caller] {
            func.callee_signatures
                .insert(callee_addr as Ident, signature.clone());
        }
        let vars = InterfaceVars {
            vars: vec![InterfaceVar {
                id: InterfaceVarId::Param {
                    function: callee_addr as Ident,
                    position: 0,
                },
                domain: vec![
                    InterfaceAlternative {
                        class: InterfaceClass::Float,
                        xtype: XType::Xfloat,
                    },
                    InterfaceAlternative {
                        class: InterfaceClass::Int,
                        xtype: XType::Xlong,
                    },
                ],
                hard_rank0,
            }],
            ..InterfaceVars::default()
        };
        let state = ProgramSelectionState {
            analysis_results: BTreeMap::new(),
            candidate_idx: [((callee_addr, 1), Some(0)), ((caller_addr, 2), Some(0))]
                .into_iter()
                .collect(),
            structure_world: HashMap::new(),
            var_decl_idx: [((callee_addr, param), 0), ((caller_addr, caller_arg), 0)]
                .into_iter()
                .collect(),
            var_type_override: HashMap::new(),
        };
        (
            solve(
                &[callee, caller],
                &state,
                &vars,
                &committed,
                &[("callee".into(), callee_addr as Ident)]
                    .into_iter()
                    .collect(),
                crate::abi::DataModel::Lp64,
            ),
            callee_addr,
            caller_addr,
        )
    }

    #[test]
    fn call_edge_agreement_can_move_a_soft_interface() {
        let (outcome, callee_addr, caller_addr) = fixture(false);
        assert_eq!(
            outcome.assignments[&InterfaceVarId::Param {
                function: callee_addr as Ident,
                position: 0,
            }],
            InterfaceClass::Int
        );
        assert!(outcome.dirty_functions.contains(&callee_addr));
        assert!(!outcome
            .declaration_assignments
            .contains_key(&(caller_addr, 11)));
    }

    #[test]
    fn known_extern_abi_outweighs_a_wrappers_pointer_prior() {
        let wrapper_addr = 0x100;
        let extern_addr = 0x200;
        let call = 0x110;
        let param = 0x700;
        let ptr_ty = ClightType::Tpointer(Arc::new(int_ty()), ClightAttr::default());
        let ulong_ty = ClightType::Tlong(ClightSignedness::Unsigned, ClightAttr::default());

        let mut wrapper = FunctionData::new(
            wrapper_addr,
            "wrapper".into(),
            vec![param],
            vec![ParamType::Typed(XType::Xptr)],
            None,
            0,
            call,
            true,
        );
        wrapper.used_regs.insert(param);
        wrapper
            .var_type_candidates
            .insert(param, vec![CandType::PtrInt, CandType::I64(Sign::Unsigned)]);
        wrapper.node_statements.insert(
            call,
            vec![ClightStmt::Scall(
                None,
                ClightExpr::EvarSymbol(
                    "external".into(),
                    ClightType::Tfunction(
                        Arc::new(vec![ulong_ty.clone()]),
                        Arc::new(ClightType::Tvoid),
                        CallConv::default(),
                    ),
                ),
                vec![ClightExpr::Ecast(
                    Box::new(ClightExpr::Etempvar(param as Ident, ptr_ty)),
                    ulong_ty,
                )],
            )],
        );

        let wrapper_signature = CalleeSignature {
            param_count: 1,
            return_type: XType::Xvoid,
            param_types: vec![XType::Xptr],
            is_varargs: false,
        };
        let external_signature = CalleeSignature {
            param_count: 1,
            return_type: XType::Xvoid,
            param_types: vec![XType::Xlongunsigned],
            is_varargs: false,
        };
        wrapper
            .callee_signatures
            .insert(extern_addr as Ident, external_signature.clone());

        let mut committed = CommittedInterfaces::default();
        committed.functions.insert(
            wrapper_addr as Ident,
            CommittedFunctionInterface {
                signature: wrapper_signature,
                authority: InterfaceAuthority::Reconciled,
            },
        );
        committed.functions.insert(
            extern_addr as Ident,
            CommittedFunctionInterface {
                signature: external_signature,
                authority: InterfaceAuthority::Extern,
            },
        );
        let vars = InterfaceVars {
            vars: vec![InterfaceVar {
                id: InterfaceVarId::Param {
                    function: wrapper_addr as Ident,
                    position: 0,
                },
                domain: vec![
                    InterfaceAlternative {
                        class: InterfaceClass::PtrInt,
                        xtype: XType::Xptr,
                    },
                    InterfaceAlternative {
                        class: InterfaceClass::Int,
                        xtype: XType::Xlongunsigned,
                    },
                ],
                hard_rank0: false,
            }],
            ..InterfaceVars::default()
        };
        let state = ProgramSelectionState {
            analysis_results: BTreeMap::new(),
            candidate_idx: [((wrapper_addr, call), Some(0))].into_iter().collect(),
            structure_world: HashMap::new(),
            var_decl_idx: [((wrapper_addr, param), 0)].into_iter().collect(),
            var_type_override: HashMap::new(),
        };

        let outcome = solve(
            &[wrapper],
            &state,
            &vars,
            &committed,
            &[("external".into(), extern_addr as Ident)]
                .into_iter()
                .collect(),
            crate::abi::DataModel::Lp64,
        );

        assert_eq!(
            outcome.assignments[&InterfaceVarId::Param {
                function: wrapper_addr as Ident,
                position: 0,
            }],
            InterfaceClass::Int
        );
        assert!(outcome.instance_dump.contains("# extern-pass-through"));
    }

    #[test]
    fn hard_interface_evidence_never_moves() {
        let (outcome, callee_addr, _) = fixture(true);
        assert_eq!(
            outcome.assignments[&InterfaceVarId::Param {
                function: callee_addr as Ident,
                position: 0,
            }],
            InterfaceClass::Float
        );
    }

    fn global_feedback_outcome(hard_rank0: bool) -> InterfaceSolveOutcome {
        let symbol = 0x9000usize;
        let id = InterfaceVarId::Global { symbol };
        let vars = InterfaceVars {
            vars: vec![InterfaceVar {
                id: id.clone(),
                domain: vec![
                    InterfaceAlternative {
                        class: InterfaceClass::Int,
                        xtype: XType::Xint,
                    },
                    InterfaceAlternative {
                        class: InterfaceClass::Float,
                        xtype: XType::Xfloat,
                    },
                ],
                hard_rank0,
            }],
            ..InterfaceVars::default()
        };
        let mut initial = CommittedInterfaces::default();
        initial.globals.insert(symbol, XType::Xint);
        let prior = [(id, 0usize)].into_iter().collect();
        solve_with_global_feedback(
            &[],
            &ProgramSelectionState {
                analysis_results: BTreeMap::new(),
                candidate_idx: HashMap::new(),
                structure_world: HashMap::new(),
                var_decl_idx: HashMap::new(),
                var_type_override: HashMap::new(),
            },
            &vars,
            &initial,
            &HashMap::new(),
            &[GlobalFlowDisagreement {
                function: 1,
                node: 2,
                symbol,
                claimed: crate::decompile::passes::clight_select::flow::anchor_of_xtype(
                    &XType::Xfloat,
                    true,
                ),
            }],
            Some(&prior),
            crate::abi::DataModel::Lp64,
        )
    }

    #[test]
    fn global_flow_disagreement_softly_reopens_stage_b() {
        let outcome = global_feedback_outcome(false);
        assert_eq!(
            outcome.assignments[&InterfaceVarId::Global { symbol: 0x9000 }],
            InterfaceClass::Float
        );
    }

    #[test]
    fn global_flow_price_never_overrides_hard_rank0() {
        let outcome = global_feedback_outcome(true);
        assert_eq!(
            outcome.assignments[&InterfaceVarId::Global { symbol: 0x9000 }],
            InterfaceClass::Int
        );
    }

    #[test]
    fn feedback_pins_unrelated_same_class_alternative_by_exact_rank() {
        let target = 0x9000usize;
        let unrelated = 0x9001usize;
        let target_id = InterfaceVarId::Global { symbol: target };
        let unrelated_id = InterfaceVarId::Global { symbol: unrelated };
        let vars = InterfaceVars {
            vars: vec![
                InterfaceVar {
                    id: target_id.clone(),
                    domain: vec![
                        InterfaceAlternative {
                            class: InterfaceClass::Int,
                            xtype: XType::Xint,
                        },
                        InterfaceAlternative {
                            class: InterfaceClass::Float,
                            xtype: XType::Xfloat,
                        },
                    ],
                    hard_rank0: false,
                },
                InterfaceVar {
                    id: unrelated_id.clone(),
                    domain: vec![
                        InterfaceAlternative {
                            class: InterfaceClass::Int,
                            xtype: XType::Xint,
                        },
                        InterfaceAlternative {
                            class: InterfaceClass::Int,
                            xtype: XType::Xlong,
                        },
                    ],
                    hard_rank0: false,
                },
            ],
            ..InterfaceVars::default()
        };
        let mut initial = CommittedInterfaces::default();
        initial.globals.insert(target, XType::Xint);
        initial.globals.insert(unrelated, XType::Xlong);
        let prior_ranks = [(target_id, 0usize), (unrelated_id.clone(), 1usize)]
            .into_iter()
            .collect();
        let outcome = solve_with_global_feedback(
            &[],
            &ProgramSelectionState {
                analysis_results: BTreeMap::new(),
                candidate_idx: HashMap::new(),
                structure_world: HashMap::new(),
                var_decl_idx: HashMap::new(),
                var_type_override: HashMap::new(),
            },
            &vars,
            &initial,
            &HashMap::new(),
            &[GlobalFlowDisagreement {
                function: 1,
                node: 2,
                symbol: target,
                claimed: crate::decompile::passes::clight_select::flow::anchor_of_xtype(
                    &XType::Xfloat,
                    true,
                ),
            }],
            Some(&prior_ranks),
            crate::abi::DataModel::Lp64,
        );
        assert_eq!(outcome.choice_ranks[&unrelated_id], 1);
        assert_eq!(outcome.committed.globals[&unrelated], XType::Xlong);
    }

    #[test]
    fn declaration_votes_are_committed_inside_stage_b() {
        let [address] = synthetic_ids();
        let reg = 9;
        let mut func = FunctionData::new(
            address,
            "decl_vote".into(),
            Vec::new(),
            Vec::new(),
            None,
            0,
            3,
            true,
        );
        func.used_regs.insert(reg);
        func.var_type_candidates
            .insert(reg, vec![CandType::I64(Sign::Signed)]);
        func.node_statements.insert(
            3,
            vec![ClightStmt::Sassign(
                ClightExpr::Ederef(
                    Box::new(ClightExpr::Etempvar(reg as Ident, int_ty())),
                    int_ty(),
                ),
                ClightExpr::EconstInt(1, int_ty()),
            )],
        );
        let state = ProgramSelectionState {
            analysis_results: BTreeMap::new(),
            candidate_idx: [((address, 3), Some(0))].into_iter().collect(),
            structure_world: HashMap::new(),
            var_decl_idx: [((address, reg), 0)].into_iter().collect(),
            var_type_override: HashMap::new(),
        };
        let outcome = solve(
            &[func],
            &state,
            &InterfaceVars::default(),
            &CommittedInterfaces::default(),
            &HashMap::new(),
            crate::abi::DataModel::Lp64,
        );
        assert_eq!(
            outcome.declaration_assignments[&(address, reg)],
            InterfaceClass::PtrInt
        );
        assert!(outcome.dirty_functions.contains(&address));
    }

    fn pointer_parameter_fixture() -> (FunctionData, ProgramSelectionState, RTLReg, Node) {
        let [address] = synthetic_ids();
        let reg = 9;
        let node = 3;
        let mut func = FunctionData::new(
            address,
            "pointer_parameter".into(),
            vec![reg],
            vec![ParamType::Typed(XType::Xlong)],
            None,
            0,
            node,
            true,
        );
        func.used_regs.insert(reg);
        func.var_type_candidates.insert(reg, vec![CandType::PtrInt]);
        let pointer_ty = ClightType::Tpointer(Arc::new(int_ty()), ClightAttr::default());
        func.node_statements.insert(
            node,
            vec![ClightStmt::Sassign(
                ClightExpr::Ederef(
                    Box::new(ClightExpr::Etempvar(reg as Ident, pointer_ty)),
                    int_ty(),
                ),
                ClightExpr::EconstInt(1, int_ty()),
            )],
        );
        let state = ProgramSelectionState {
            analysis_results: BTreeMap::new(),
            candidate_idx: [((address, node), Some(0))].into_iter().collect(),
            structure_world: HashMap::new(),
            var_decl_idx: [((address, reg), 0)].into_iter().collect(),
            var_type_override: HashMap::new(),
        };
        (func, state, reg, node)
    }

    #[test]
    fn explicit_param_override_replaces_refined_pointer_temp() {
        let (func, state, reg, _) = pointer_parameter_fixture();
        let selected = selected_temp_types(&func, &state, None);
        assert!(matches!(
            selected[&(reg as Ident)],
            ClightType::Tpointer(..)
        ));

        let overridden = selected_temp_types(&func, &state, Some((reg, XType::Xlong)));
        assert!(matches!(
            overridden[&(reg as Ident)],
            ClightType::Tlong(ClightSignedness::Signed, _)
        ));
    }

    #[test]
    fn pointer_dereference_prices_long_param_alternative() {
        let (func, state, reg, _) = pointer_parameter_fixture();
        let var = InterfaceVar {
            id: InterfaceVarId::Param {
                function: func.address as Ident,
                position: 0,
            },
            domain: vec![
                InterfaceAlternative {
                    class: InterfaceClass::PtrInt,
                    xtype: XType::Xintptr,
                },
                InterfaceAlternative {
                    class: InterfaceClass::Int,
                    xtype: XType::Xlong,
                },
            ],
            hard_rank0: false,
        };
        let signature = CalleeSignature {
            param_count: 1,
            return_type: XType::Xvoid,
            param_types: vec![XType::Xintptr],
            is_varargs: false,
        };
        let mut committed = CommittedInterfaces::default();
        committed.functions.insert(
            func.address as Ident,
            CommittedFunctionInterface {
                signature,
                authority: InterfaceAuthority::Reconciled,
            },
        );
        let by_addr = [(func.address, 0usize)].into_iter().collect();

        let costs = marginal_costs(
            &var,
            &[func],
            &state,
            &committed,
            &[],
            &HashMap::new(),
            &by_addr,
        );
        assert_eq!(costs[0].0, 0);
        assert!(costs[1].0 > costs[0].0, "costs={costs:?}, reg={reg}");
    }

    #[test]
    fn float_evidence_is_a_veto_not_a_declaration_target() {
        assert_eq!(
            declaration_vote_target(
                InterfaceClass::Int,
                DeclVotes {
                    float_use: 1,
                    ..DeclVotes::default()
                },
            ),
            None
        );
        assert_eq!(
            declaration_vote_target(
                InterfaceClass::PtrInt,
                DeclVotes {
                    int_use: 1,
                    float_use: 1,
                    ..DeclVotes::default()
                },
            ),
            None
        );
        assert_eq!(
            declaration_vote_target(
                InterfaceClass::Int,
                DeclVotes {
                    float_use: 1,
                    ptr_use: 1,
                    ..DeclVotes::default()
                },
            ),
            None
        );
    }
}
