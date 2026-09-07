//! Solver-side register-class theory: the second behavioral theory, and the
//! backstop for the upstream fix.
//!
//! `type_pass` already refuses to create a float type candidate on a value web
//! the machine only ever keeps in general-purpose registers, which is where the
//! defect belongs and where it is cheapest to kill. Candidates still reach
//! selection carrying a float spelling on such a web by other routes -- a type
//! propagated across a move from a different web, a signature slot, a candidate
//! built before the class evidence applied -- and this theory vetoes those at
//! selection time.
//!
//! Same safety rule as the branch theory: a candidate is only vetoed when some
//! sibling candidate at the same node is class-consistent, so the exactly-one
//! constraint always keeps a satisfying assignment and no veto can turn a
//! function UNSAT. When every candidate at a node contradicts the machine, that
//! is an ADEQUACY failure, not a selection failure; the theory stays silent and
//! `adequacy.rs` reports it.

use std::collections::HashMap;

use z3::ast::Bool;

use crate::decompile::passes::clight_select::adequacy::ClassEvidence;
use crate::x86::types::{ClightExpr, ClightStmt, ClightType, Ident, Node, RTLReg};

#[derive(Debug, Default, Clone, Copy)]
pub struct ClassStats {
    /// Value webs with single-class machine evidence used by this function.
    pub webs_single_class: usize,
    /// Value webs with both classes, left alone by design.
    pub webs_conflicted: usize,
    /// Multi-candidate nodes where at least one candidate contradicts the class.
    pub nodes_watched: usize,
    /// Multi-candidate nodes where EVERY candidate contradicts, so no veto is safe.
    pub nodes_all_contradict: usize,
    /// Candidate literals registered as vetoed.
    pub literals_vetoed: usize,
    /// Times the search fixed a vetoed literal to true.
    pub vetoes_fired: usize,
    /// Conflicts Z3 accepted from those vetoes.
    pub conflicts_injected: usize,
}

impl ClassStats {
    pub fn merge(&mut self, other: &ClassStats) {
        self.webs_single_class += other.webs_single_class;
        self.webs_conflicted += other.webs_conflicted;
        self.nodes_watched += other.nodes_watched;
        self.nodes_all_contradict += other.nodes_all_contradict;
        self.literals_vetoed += other.literals_vetoed;
        self.vetoes_fired += other.vetoes_fired;
        self.conflicts_injected += other.conflicts_injected;
    }
}

/// Tag identifying this theory's vetoes in the shared `VetoTheory`.
pub const TAG: &str = "class";

fn is_float_type(ty: &ClightType) -> bool {
    matches!(ty, ClightType::Tfloat(..))
}

fn expr_pins(e: &ClightExpr, out: &mut Vec<(Ident, bool)>) {
    match e {
        ClightExpr::Etempvar(id, ty) | ClightExpr::Evar(id, ty) => {
            out.push((*id, is_float_type(ty)))
        }
        ClightExpr::Ederef(inner, _)
        | ClightExpr::Eaddrof(inner, _)
        | ClightExpr::Eunop(_, inner, _)
        | ClightExpr::Ecast(inner, _)
        | ClightExpr::Efield(inner, _, _) => expr_pins(inner, out),
        ClightExpr::Ebinop(_, l, r, _) => {
            expr_pins(l, out);
            expr_pins(r, out);
        }
        ClightExpr::Econdition(c, a, b, _) => {
            expr_pins(c, out);
            expr_pins(a, out);
            expr_pins(b, out);
        }
        _ => {}
    }
}

fn stmt_pins(s: &ClightStmt, out: &mut Vec<(Ident, bool)>) {
    match s {
        ClightStmt::Sset(_, rhs) => expr_pins(rhs, out),
        ClightStmt::Sassign(lhs, rhs) => {
            expr_pins(lhs, out);
            expr_pins(rhs, out);
        }
        ClightStmt::Sifthenelse(cond, a, b) => {
            expr_pins(cond, out);
            stmt_pins(a, out);
            stmt_pins(b, out);
        }
        ClightStmt::Ssequence(items) => items.iter().for_each(|i| stmt_pins(i, out)),
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => stmt_pins(inner, out),
        ClightStmt::Sloop(a, b) => {
            stmt_pins(a, out);
            stmt_pins(b, out);
        }
        ClightStmt::Sreturn(Some(e)) => expr_pins(e, out),
        ClightStmt::Sswitch(e, cases) => {
            expr_pins(e, out);
            cases.iter().for_each(|(_, c)| stmt_pins(c, out));
        }
        ClightStmt::Scall(_, f, args) => {
            expr_pins(f, out);
            args.iter().for_each(|a| expr_pins(a, out));
        }
        ClightStmt::Sbuiltin(_, _, _, args) => args.iter().for_each(|a| expr_pins(a, out)),
        _ => {}
    }
}

/// True when this candidate spells some variable in a class the machine
/// contradicts. A web with both classes, or with none, contradicts nothing.
pub fn stmt_contradicts_class(stmt: &ClightStmt, evidence: &ClassEvidence) -> bool {
    let mut pins = Vec::new();
    stmt_pins(stmt, &mut pins);
    pins.iter().any(|&(ident, is_float)| {
        let reg = ident as RTLReg;
        if is_float {
            evidence.is_gpr_only(reg)
        } else {
            evidence.is_fp_only(reg)
        }
    })
}

/// Build the veto set for one function: at every multi-candidate node, veto the
/// candidates whose variable spellings contradict machine register class, but
/// only when a sibling candidate is consistent.
pub fn build_class_theory(
    nodes: &[Node],
    node_statements: &HashMap<Node, Vec<ClightStmt>>,
    selvar: &HashMap<Node, Vec<Bool>>,
    used_regs: &std::collections::HashSet<RTLReg>,
    evidence: &ClassEvidence,
) -> (Vec<Bool>, ClassStats) {
    let mut stats = ClassStats::default();
    for &reg in used_regs {
        if evidence.is_conflicted(reg) {
            stats.webs_conflicted += 1;
        } else if evidence.is_gpr_only(reg) || evidence.is_fp_only(reg) {
            stats.webs_single_class += 1;
        }
    }

    let mut vetoed: Vec<Bool> = Vec::new();
    for &node in nodes {
        let Some(vars) = selvar.get(&node) else {
            continue;
        };
        let Some(cands) = node_statements.get(&node) else {
            continue;
        };
        let bad: Vec<usize> = cands
            .iter()
            .enumerate()
            .filter(|(_, s)| stmt_contradicts_class(s, evidence))
            .map(|(i, _)| i)
            .collect();
        if bad.is_empty() {
            continue;
        }
        if bad.len() == cands.len() {
            // Every candidate is wrong: an upstream gap, not something selection
            // can fix. Vetoing here would only make the function UNSAT.
            stats.nodes_all_contradict += 1;
            continue;
        }
        stats.nodes_watched += 1;
        for index in bad {
            if let Some(literal) = vars.get(index) {
                vetoed.push(literal.clone());
                stats.literals_vetoed += 1;
            }
        }
    }
    (vetoed, stats)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::x86::types::{ClightAttr, ClightFloatSize, ClightIntSize, ClightSignedness};

    fn float_ty() -> ClightType {
        ClightType::Tfloat(ClightFloatSize::F64, ClightAttr::default())
    }

    fn int_ty() -> ClightType {
        ClightType::Tint(
            ClightIntSize::I32,
            ClightSignedness::Signed,
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
    fn a_float_spelling_on_a_gpr_web_contradicts() {
        let s = ClightStmt::Sset(9, ClightExpr::Etempvar(5, float_ty()));
        assert!(stmt_contradicts_class(&s, &evidence(&[5], &[])));
    }

    #[test]
    fn an_int_spelling_on_a_gpr_web_is_consistent() {
        let s = ClightStmt::Sset(9, ClightExpr::Etempvar(5, int_ty()));
        assert!(!stmt_contradicts_class(&s, &evidence(&[5], &[])));
    }

    #[test]
    fn a_conflicted_web_is_never_contradicted() {
        let s = ClightStmt::Sset(9, ClightExpr::Etempvar(5, float_ty()));
        assert!(!stmt_contradicts_class(&s, &evidence(&[5], &[5])));
    }

    // The safety property the whole design rests on: when every candidate at a
    // node contradicts, nothing is vetoed, so the exactly-one constraint keeps
    // a model and the function cannot be made UNSAT.
    #[test]
    fn a_node_whose_candidates_all_contradict_is_left_alone() {
        let ctx = z3::Context::thread_local();
        let _ = &ctx;
        let node: Node = 0x40;
        let cands = vec![
            ClightStmt::Sset(9, ClightExpr::Etempvar(5, float_ty())),
            ClightStmt::Sset(
                9,
                ClightExpr::Ecast(Box::new(ClightExpr::Etempvar(5, float_ty())), float_ty()),
            ),
        ];
        let vars = vec![Bool::new_const("a"), Bool::new_const("b")];
        let mut node_statements = HashMap::new();
        node_statements.insert(node, cands);
        let mut selvar = HashMap::new();
        selvar.insert(node, vars);
        let used: std::collections::HashSet<RTLReg> = [5u64].into_iter().collect();
        let (vetoed, stats) = build_class_theory(
            &[node],
            &node_statements,
            &selvar,
            &used,
            &evidence(&[5], &[]),
        );
        assert!(vetoed.is_empty());
        assert_eq!(stats.nodes_all_contradict, 1);
        assert_eq!(stats.nodes_watched, 0);
    }

    #[test]
    fn a_node_with_one_good_sibling_vetoes_only_the_bad_one() {
        let node: Node = 0x50;
        let cands = vec![
            ClightStmt::Sset(9, ClightExpr::Etempvar(5, float_ty())),
            ClightStmt::Sset(9, ClightExpr::Etempvar(5, int_ty())),
        ];
        let vars = vec![Bool::new_const("c"), Bool::new_const("d")];
        let mut node_statements = HashMap::new();
        node_statements.insert(node, cands);
        let mut selvar = HashMap::new();
        selvar.insert(node, vars);
        let used: std::collections::HashSet<RTLReg> = [5u64].into_iter().collect();
        let (vetoed, stats) = build_class_theory(
            &[node],
            &node_statements,
            &selvar,
            &used,
            &evidence(&[5], &[]),
        );
        assert_eq!(vetoed.len(), 1);
        assert_eq!(stats.literals_vetoed, 1);
        assert_eq!(stats.nodes_watched, 1);
        assert_eq!(stats.nodes_all_contradict, 0);
    }
}
