//! The refutation half of selection: what the candidate sets CANNOT express.
//!
//! Selection can only ever pick among the candidates upstream produced. When
//! every candidate at a node contradicts a hard machine fact, no solver,
//! objective or theory can recover the right answer -- the defect is upstream,
//! in candidate generation, and reporting it as such is the point of this
//! module. It never changes a selection.
//!
//! The machine fact used here is register class. `web_class_gpr` /
//! `web_class_fp` record, per RTL value web, which register files the machine
//! actually keeps that value in; a web living only in general-purpose registers
//! holds an integer or a pointer and never a float, and a web living only in
//! XMM/VFP registers holds a float. Two buckets come out of that:
//!
//!   * upstream gaps: a node whose every candidate statement, or a register
//!     whose every type candidate, contradicts single-class evidence.
//!   * class conflicts: a web with BOTH classes of evidence. That is not one
//!     value with two opinions, it is two values the aliasing merged into one
//!     web, and no type is right for it. These are counted, never guessed at.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use crate::decompile::passes::clight_select::candtype::CandType;
use crate::decompile::passes::clight_select::query::FunctionData;
use crate::x86::types::{ClightExpr, ClightStmt, ClightType, Ident, Node, RTLReg};

/// Register-class evidence for every value web in the program, as collected
/// from the two Ascent relations.
#[derive(Debug, Clone, Default)]
pub struct ClassEvidence {
    pub gpr: HashSet<RTLReg>,
    pub fp: HashSet<RTLReg>,
}

impl ClassEvidence {
    pub fn is_gpr_only(&self, reg: RTLReg) -> bool {
        self.gpr.contains(&reg) && !self.fp.contains(&reg)
    }

    pub fn is_fp_only(&self, reg: RTLReg) -> bool {
        self.fp.contains(&reg) && !self.gpr.contains(&reg)
    }

    pub fn is_conflicted(&self, reg: RTLReg) -> bool {
        self.gpr.contains(&reg) && self.fp.contains(&reg)
    }

    pub fn is_empty(&self) -> bool {
        self.gpr.is_empty() && self.fp.is_empty()
    }
}

/// Machine-evidence contradiction carried by one candidate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Contradiction {
    /// A float type on a web the machine only keeps in general-purpose registers.
    FloatOnGpr,
    /// A non-float type on a web the machine only keeps in float registers.
    NonFloatOnFp,
}

fn is_float_type(ty: &ClightType) -> bool {
    matches!(ty, ClightType::Tfloat(..))
}

/// Every (register, type) an expression pins, i.e. every variable reference
/// whose spelling in this candidate carries a committed type.
fn expr_reg_types(e: &ClightExpr, out: &mut Vec<(Ident, ClightType)>) {
    match e {
        ClightExpr::Etempvar(id, ty) | ClightExpr::Evar(id, ty) => out.push((*id, ty.clone())),
        ClightExpr::Ederef(inner, _)
        | ClightExpr::Eaddrof(inner, _)
        | ClightExpr::Eunop(_, inner, _)
        | ClightExpr::Ecast(inner, _)
        | ClightExpr::Efield(inner, _, _) => expr_reg_types(inner, out),
        ClightExpr::Ebinop(_, l, r, _) => {
            expr_reg_types(l, out);
            expr_reg_types(r, out);
        }
        ClightExpr::Econdition(c, a, b, _) => {
            expr_reg_types(c, out);
            expr_reg_types(a, out);
            expr_reg_types(b, out);
        }
        _ => {}
    }
}

fn stmt_reg_types(s: &ClightStmt, out: &mut Vec<(Ident, ClightType)>) {
    match s {
        ClightStmt::Sset(_, rhs) => expr_reg_types(rhs, out),
        ClightStmt::Sassign(lhs, rhs) => {
            expr_reg_types(lhs, out);
            expr_reg_types(rhs, out);
        }
        ClightStmt::Sifthenelse(cond, a, b) => {
            expr_reg_types(cond, out);
            stmt_reg_types(a, out);
            stmt_reg_types(b, out);
        }
        ClightStmt::Ssequence(items) => items.iter().for_each(|i| stmt_reg_types(i, out)),
        ClightStmt::Slabel(_, inner) => stmt_reg_types(inner, out),
        ClightStmt::Sloop(a, b) => {
            stmt_reg_types(a, out);
            stmt_reg_types(b, out);
        }
        ClightStmt::Sreturn(Some(e)) => expr_reg_types(e, out),
        ClightStmt::Sswitch(e, cases) => {
            expr_reg_types(e, out);
            cases.iter().for_each(|(_, c)| stmt_reg_types(c, out));
        }
        ClightStmt::Scall(_, f, args) => {
            expr_reg_types(f, out);
            args.iter().for_each(|a| expr_reg_types(a, out));
        }
        ClightStmt::Sbuiltin(_, _, _, args) => args.iter().for_each(|a| expr_reg_types(a, out)),
        _ => {}
    }
}

/// The class contradictions one candidate statement carries, if any.
fn stmt_contradictions(
    stmt: &ClightStmt,
    evidence: &ClassEvidence,
) -> BTreeSet<(RTLReg, Contradiction)> {
    let mut pinned = Vec::new();
    stmt_reg_types(stmt, &mut pinned);
    let mut out = BTreeSet::new();
    for (ident, ty) in pinned {
        let reg = ident as RTLReg;
        if is_float_type(&ty) {
            if evidence.is_gpr_only(reg) {
                out.insert((reg, Contradiction::FloatOnGpr));
            }
        } else if evidence.is_fp_only(reg) {
            out.insert((reg, Contradiction::NonFloatOnFp));
        }
    }
    out
}

#[derive(Debug, Default, Clone)]
pub struct AdequacyReport {
    /// Functions examined.
    pub functions: usize,
    /// Nodes with at least one candidate statement.
    pub nodes: usize,
    /// Nodes where EVERY candidate statement contradicts single-class evidence.
    pub nodes_all_candidates_contradict: usize,
    /// Nodes where some but not all candidates contradict, i.e. selection can
    /// still reach a faithful answer and a theory veto is enough.
    pub nodes_partially_contradict: usize,
    /// Registers whose entire type-candidate set contradicts single-class evidence.
    pub regs_all_candidates_contradict: usize,
    /// Value webs carrying both GPR and FP evidence: instance-merge suspects.
    pub webs_class_conflict: usize,
    /// Of those, the ones actually used by a recovered function.
    pub webs_class_conflict_used: usize,
    /// Flow contradictions among FORCED statements only. Nothing on those
    /// chains is selectable, so no selection can avoid them: an upstream gap in
    /// the abstract-semantics sense rather than a selection error.
    pub flow_gap_contradictions: usize,
    /// Blocks carrying at least one such contradiction.
    pub flow_gap_blocks: usize,
    /// Detail lines, address-tagged, for the env-gated dump.
    pub detail: Vec<String>,
}

impl AdequacyReport {
    fn merge(&mut self, other: AdequacyReport) {
        self.functions += other.functions;
        self.nodes += other.nodes;
        self.nodes_all_candidates_contradict += other.nodes_all_candidates_contradict;
        self.nodes_partially_contradict += other.nodes_partially_contradict;
        self.regs_all_candidates_contradict += other.regs_all_candidates_contradict;
        self.webs_class_conflict_used += other.webs_class_conflict_used;
        self.flow_gap_contradictions += other.flow_gap_contradictions;
        self.flow_gap_blocks += other.flow_gap_blocks;
        self.detail.extend(other.detail);
    }
}

/// An RTL value web id encodes the node that defined it and that def's machine
/// register, so a bare id can be reported as an address a reader can look up.
fn reg_site(reg: RTLReg) -> String {
    let node = (reg & !(1u64 << 63)) >> crate::decompile::passes::rtl_pass::MREG_DISCRIMINANT_BITS;
    format!("{:#x}@{:#x}", reg, node)
}

fn audit_function(func: &FunctionData, evidence: &ClassEvidence) -> AdequacyReport {
    let mut rep = AdequacyReport {
        functions: 1,
        ..AdequacyReport::default()
    };

    let mut nodes: Vec<Node> = func.node_statements.keys().copied().collect();
    nodes.sort_unstable();
    for node in nodes {
        let cands = &func.node_statements[&node];
        if cands.is_empty() {
            continue;
        }
        rep.nodes += 1;
        let per_candidate: Vec<BTreeSet<(RTLReg, Contradiction)>> = cands
            .iter()
            .map(|s| stmt_contradictions(s, evidence))
            .collect();
        let bad = per_candidate.iter().filter(|c| !c.is_empty()).count();
        if bad == 0 {
            continue;
        }
        if bad == cands.len() {
            rep.nodes_all_candidates_contradict += 1;
            let mut all: BTreeSet<(RTLReg, Contradiction)> = BTreeSet::new();
            for c in &per_candidate {
                all.extend(c.iter().copied());
            }
            for (reg, kind) in all {
                rep.detail.push(format!(
                    "  UPSTREAM-GAP fn={} ({:#x}) node={:#x} cands={} reg={} {:?}",
                    func.name,
                    func.address,
                    node,
                    cands.len(),
                    reg_site(reg),
                    kind
                ));
            }
        } else {
            rep.nodes_partially_contradict += 1;
        }
    }

    let mut regs: Vec<RTLReg> = func.var_type_candidates.keys().copied().collect();
    regs.sort_unstable();
    for reg in regs {
        let cands = &func.var_type_candidates[&reg];
        if cands.is_empty() {
            continue;
        }
        if evidence.is_gpr_only(reg) && cands.iter().all(|c| c.is_float()) {
            rep.regs_all_candidates_contradict += 1;
            rep.detail.push(format!(
                "  UPSTREAM-GAP fn={} ({:#x}) reg={} all {} type candidates float on a GPR-only web",
                func.name,
                func.address,
                reg_site(reg),
                cands.len()
            ));
        } else if evidence.is_fp_only(reg) && !cands.iter().any(|c| c.is_float()) {
            rep.regs_all_candidates_contradict += 1;
            rep.detail.push(format!(
                "  UPSTREAM-GAP fn={} ({:#x}) reg={} no float among {} type candidates on an FP-only web",
                func.name,
                func.address,
                reg_site(reg),
                cands.len()
            ));
        }
        if evidence.is_conflicted(reg) {
            rep.webs_class_conflict_used += 1;
            rep.detail.push(format!(
                "  CLASS-CONFLICT fn={} ({:#x}) reg={} has both GPR and FP machine evidence (instance-merge suspect); {} type candidates",
                func.name,
                func.address,
                reg_site(reg),
                cands.len()
            ));
        }
    }

    audit_flow_gaps(func, &mut rep);
    rep
}

/// Flow half of the audit: fold each block using ONLY the forced statements,
/// so every contradiction found is one no selection could have avoided. A
/// multi-candidate node is skipped entirely rather than resolved to candidate
/// 0, because a contradiction that depends on a guess is a selection question,
/// not an adequacy one.
fn audit_flow_gaps(func: &FunctionData, rep: &mut AdequacyReport) {
    use crate::decompile::passes::clight_select::flow;

    if func.flow_blocks.is_empty() || func.flow_anchors.is_empty() {
        return;
    }
    let forced: BTreeMap<Node, ClightStmt> = func
        .node_statements
        .iter()
        .filter(|(_, c)| c.len() == 1)
        .map(|(n, c)| (*n, c[0].clone()))
        .collect();
    if forced.is_empty() {
        return;
    }
    // Every multi-candidate node is undecided here by construction, and must be
    // handed over so the fold forgets what it could have written.
    let undecided: BTreeMap<Node, Vec<ClightStmt>> = func
        .node_statements
        .iter()
        .filter(|(_, c)| c.len() > 1)
        .map(|(n, c)| (*n, c.clone()))
        .collect();
    let all_candidates: BTreeMap<Node, Vec<ClightStmt>> = func
        .node_statements
        .iter()
        .map(|(n, c)| (*n, c.clone()))
        .collect();
    let (_, contras) = flow::eval_function(
        &func.flow_blocks,
        &forced,
        &undecided,
        &all_candidates,
        &func.flow_anchors,
        &BTreeSet::new(),
        func.ptr64,
    );
    let mut blocks: BTreeSet<Node> = BTreeSet::new();
    for c in &contras {
        rep.flow_gap_contradictions += 1;
        blocks.insert(c.node);
        rep.detail.push(format!(
            "  FLOW-GAP fn={} ({:#x}) node={:#x} {} claims {} but {} is flowing (anchor {:?})",
            func.name,
            func.address,
            c.node,
            flow::loc_label(c.loc),
            flow::aval_label(c.claimed),
            flow::aval_label(c.flowing),
            c.kind
        ));
    }
    rep.flow_gap_blocks += blocks.len();
}

/// Audit the whole selection input and print one deterministic summary line;
/// the address-tagged detail is behind MANIFOLD_ADEQUACY (1/true for all, or a
/// substring to filter by function name). Diagnostic only: nothing here feeds
/// back into selection.
pub(crate) fn adequacy_audit(functions: &[FunctionData], evidence: &ClassEvidence) {
    if evidence.is_empty() {
        return;
    }

    let mut report = AdequacyReport::default();
    for func in functions {
        report.merge(audit_function(func, evidence));
    }
    report.webs_class_conflict = evidence.gpr.intersection(&evidence.fp).count();

    eprintln!(
        "[adequacy] funcs={} nodes={} upstream-gap-nodes={} partial-contradiction-nodes={} upstream-gap-regs={} class-conflict-webs={} ({} used by recovered functions) flow-gap-contradictions={} flow-gap-nodes={}",
        report.functions,
        report.nodes,
        report.nodes_all_candidates_contradict,
        report.nodes_partially_contradict,
        report.regs_all_candidates_contradict,
        report.webs_class_conflict,
        report.webs_class_conflict_used,
        report.flow_gap_contradictions,
        report.flow_gap_blocks
    );

    let detail = std::env::var("MANIFOLD_ADEQUACY").unwrap_or_default();
    if detail.is_empty() {
        return;
    }
    let mut lines = report.detail;
    lines.sort();
    lines.dedup();
    for line in lines {
        if detail == "1" || detail == "true" || line.contains(&detail) {
            eprintln!("{}", line);
        }
    }
}

/// Collect the two Ascent relations into the lookup the audit and the solver
/// theory share.
pub(crate) fn collect_class_evidence(
    db: &crate::decompile::elevator::DecompileDB,
) -> ClassEvidence {
    let mut evidence = ClassEvidence::default();
    for (reg,) in db.rel_iter::<(RTLReg,)>("web_class_gpr") {
        evidence.gpr.insert(*reg);
    }
    for (reg,) in db.rel_iter::<(RTLReg,)>("web_class_fp") {
        evidence.fp.insert(*reg);
    }
    evidence
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::x86::types::{ClightAttr, ClightIntSize, ClightSignedness};

    fn int_ty() -> ClightType {
        ClightType::Tint(
            ClightIntSize::I32,
            ClightSignedness::Signed,
            ClightAttr::default(),
        )
    }

    fn float_ty() -> ClightType {
        ClightType::Tfloat(
            crate::x86::types::ClightFloatSize::F64,
            ClightAttr::default(),
        )
    }

    fn evidence(gpr: &[RTLReg], fp: &[RTLReg]) -> ClassEvidence {
        ClassEvidence {
            gpr: gpr.iter().copied().collect(),
            fp: fp.iter().copied().collect(),
        }
    }

    #[test]
    fn float_spelling_on_a_gpr_only_web_is_a_contradiction() {
        let stmt = ClightStmt::Sset(7, ClightExpr::Etempvar(5, float_ty()));
        let ev = evidence(&[5], &[]);
        let found = stmt_contradictions(&stmt, &ev);
        assert_eq!(
            found.into_iter().collect::<Vec<_>>(),
            vec![(5u64, Contradiction::FloatOnGpr)]
        );
    }

    #[test]
    fn a_conflicted_web_is_never_a_contradiction() {
        let stmt = ClightStmt::Sset(7, ClightExpr::Etempvar(5, float_ty()));
        let ev = evidence(&[5], &[5]);
        assert!(stmt_contradictions(&stmt, &ev).is_empty());
    }

    #[test]
    fn an_int_spelling_on_a_gpr_web_is_clean() {
        let stmt = ClightStmt::Sset(7, ClightExpr::Etempvar(5, int_ty()));
        let ev = evidence(&[5], &[]);
        assert!(stmt_contradictions(&stmt, &ev).is_empty());
    }

    #[test]
    fn an_int_spelling_on_an_fp_only_web_is_a_contradiction() {
        let stmt = ClightStmt::Sset(7, ClightExpr::Etempvar(5, int_ty()));
        let ev = evidence(&[], &[5]);
        assert_eq!(
            stmt_contradictions(&stmt, &ev)
                .into_iter()
                .collect::<Vec<_>>(),
            vec![(5u64, Contradiction::NonFloatOnFp)]
        );
    }

    #[test]
    fn a_web_with_no_evidence_is_never_a_contradiction() {
        let stmt = ClightStmt::Sset(7, ClightExpr::Etempvar(5, float_ty()));
        assert!(stmt_contradictions(&stmt, &ClassEvidence::default()).is_empty());
    }
}
