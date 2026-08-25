//! Pilot behavioral theory for "selection modulo behavior": the comparison a
//! flag-consuming instruction performs fixes the signedness of the comparison
//! the recovered C must perform, so a candidate statement whose comparison has
//! the other signedness does not implement the machine's semantics.
//!
//! The evidence is CompCert's own `Condition`, taken from the `mach_inst`
//! Mcond facts the lifter already derives, not from a raw mnemonic. Two things
//! follow. It is architecture-neutral -- an AArch64 or ARM32 lowering produces
//! the same Ccomp/Ccompu distinction, and no x86 spelling table is involved.
//! And it is keyed where the lifter emits the Mcond, which for a compare-plus-
//! branch pair is the COMPARE's address: that is the node the ambiguous
//! statement candidate actually occupies, whereas the branch usually carries a
//! single candidate and nothing to select.
//!
//! The theory only vetoes a candidate when some sibling candidate at the same
//! node DOES match the condition, so the exactly-one constraint at that node
//! always keeps a satisfying assignment and the veto can never make a function
//! UNSAT.

use z3::ast::Bool;

use crate::decompile::passes::clight_select::solve::clight_expr_type as expr_type;
use crate::util::semantic_node_address;
use crate::x86::op::{Comparison, Condition};
use crate::x86::types::{
    ClightBinaryOp, ClightExpr, ClightSignedness, ClightStmt, ClightType, Node,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpClass {
    Signed,
    Unsigned,
}

/// Signedness a lifted `Condition` tests, or `None` when it carries no
/// signedness at all.
///
/// Equality and inequality are excluded deliberately: `x == y` compiles to the
/// same machine comparison whether the operands are signed or unsigned, so a
/// Ceq/Cne condition is evidence of nothing and vetoing on it would reject
/// correct candidates. Only the four ordering comparisons discriminate. Float
/// conditions, mask tests and the opaque overflow variants carry no integer
/// signedness either.
pub fn condition_cmp_class(cond: &Condition) -> Option<CmpClass> {
    let (class, cmp) = match cond {
        Condition::Ccomp(c)
        | Condition::Ccompimm(c, _)
        | Condition::Ccompl(c)
        | Condition::Ccomplimm(c, _) => (CmpClass::Signed, c),
        Condition::Ccompu(c)
        | Condition::Ccompuimm(c, _)
        | Condition::Ccomplu(c)
        | Condition::Ccompluimm(c, _) => (CmpClass::Unsigned, c),
        _ => return None,
    };
    match cmp {
        Comparison::Clt | Comparison::Cle | Comparison::Cgt | Comparison::Cge => Some(class),
        Comparison::Ceq | Comparison::Cne | Comparison::Unknown => None,
    }
}

/// Node ids carry the two synthetic-node marker bits; instruction facts are
/// keyed by the real address.
pub fn node_address(node: Node) -> u64 {
    semantic_node_address(node)
}

fn type_class(ty: &ClightType) -> Option<CmpClass> {
    match ty {
        ClightType::Tint(_, ClightSignedness::Signed, _)
        | ClightType::Tlong(ClightSignedness::Signed, _)
        | ClightType::Tint128(ClightSignedness::Signed, _) => Some(CmpClass::Signed),
        ClightType::Tint(_, ClightSignedness::Unsigned, _)
        | ClightType::Tlong(ClightSignedness::Unsigned, _)
        | ClightType::Tint128(ClightSignedness::Unsigned, _)
        | ClightType::Tpointer(..)
        | ClightType::Tarray(..) => Some(CmpClass::Unsigned),
        _ => None,
    }
}

// C's usual arithmetic conversions make a comparison unsigned as soon as one
// side is; only a genuinely signed pair performs a signed compare. A side whose
// class is unknown (float, struct, void) leaves the comparison unclassified.
fn compare_class(lhs: &ClightExpr, rhs: &ClightExpr) -> Option<CmpClass> {
    let l = type_class(expr_type(lhs))?;
    let r = type_class(expr_type(rhs))?;
    if l == CmpClass::Unsigned || r == CmpClass::Unsigned {
        Some(CmpClass::Unsigned)
    } else {
        Some(CmpClass::Signed)
    }
}

fn expr_cmp_class(e: &ClightExpr) -> Option<CmpClass> {
    match e {
        ClightExpr::Ebinop(
            ClightBinaryOp::Olt | ClightBinaryOp::Ogt | ClightBinaryOp::Ole | ClightBinaryOp::Oge,
            lhs,
            rhs,
            _,
        ) => compare_class(lhs, rhs),
        ClightExpr::Ebinop(_, lhs, rhs, _) => expr_cmp_class(lhs).or_else(|| expr_cmp_class(rhs)),
        ClightExpr::Ederef(inner, _)
        | ClightExpr::Eaddrof(inner, _)
        | ClightExpr::Eunop(_, inner, _)
        | ClightExpr::Ecast(inner, _)
        | ClightExpr::Efield(inner, _, _) => expr_cmp_class(inner),
        ClightExpr::Econdition(c, a, b, _) => expr_cmp_class(c)
            .or_else(|| expr_cmp_class(a))
            .or_else(|| expr_cmp_class(b)),
        _ => None,
    }
}

/// Signedness of the first ordering comparison this candidate statement
/// performs, in pre-order. `None` means the candidate makes no ordered
/// comparison and so is never vetoed.
pub fn stmt_cmp_class(stmt: &ClightStmt) -> Option<CmpClass> {
    match stmt {
        ClightStmt::Sifthenelse(cond, a, b) => expr_cmp_class(cond)
            .or_else(|| stmt_cmp_class(a))
            .or_else(|| stmt_cmp_class(b)),
        ClightStmt::Slabel(_, inner) => stmt_cmp_class(inner),
        ClightStmt::Ssequence(items) => items.iter().find_map(stmt_cmp_class),
        ClightStmt::Sset(_, rhs) => expr_cmp_class(rhs),
        ClightStmt::Sassign(lhs, rhs) => expr_cmp_class(lhs).or_else(|| expr_cmp_class(rhs)),
        ClightStmt::Sreturn(Some(e)) => expr_cmp_class(e),
        ClightStmt::Sswitch(e, _) => expr_cmp_class(e),
        ClightStmt::Sloop(a, b) => stmt_cmp_class(a).or_else(|| stmt_cmp_class(b)),
        _ => None,
    }
}

#[derive(Debug, Default, Clone, Copy)]
pub struct BranchStats {
    /// Nodes with more than one candidate statement, i.e. the whole search space.
    pub multi_candidate_nodes: usize,
    /// Conditional-branch addresses this function owns.
    pub branch_addresses: usize,
    /// Multi-candidate nodes whose address is a signed/unsigned conditional branch.
    pub nodes_classified: usize,
    /// Of those, nodes where candidates disagree and one matches the mnemonic.
    pub nodes_watched: usize,
    /// Candidate literals registered as vetoed.
    pub literals_vetoed: usize,
    /// Times the search fixed a vetoed literal to true.
    pub vetoes_fired: usize,
    /// Conflicts Z3 accepted from those vetoes.
    pub conflicts_injected: usize,
}

impl BranchStats {
    pub fn merge(&mut self, other: &BranchStats) {
        self.multi_candidate_nodes += other.multi_candidate_nodes;
        self.branch_addresses += other.branch_addresses;
        self.nodes_classified += other.nodes_classified;
        self.nodes_watched += other.nodes_watched;
        self.literals_vetoed += other.literals_vetoed;
        self.vetoes_fired += other.vetoes_fired;
        self.conflicts_injected += other.conflicts_injected;
    }
}

/// Tag identifying this theory's vetoes in the shared `VetoTheory`.
pub const TAG: &str = "branch";

/// Build the veto set for one function: for every multi-candidate node whose
/// address carries an ordering Mcond, veto the candidates whose comparison
/// signedness contradicts that condition, but only when a sibling candidate
/// matches it.
pub fn build_branch_theory(
    nodes: &[Node],
    node_statements: &std::collections::HashMap<Node, Vec<ClightStmt>>,
    selvar: &std::collections::HashMap<Node, Vec<Bool>>,
    cond_class_at: &std::collections::HashMap<u64, CmpClass>,
) -> (Vec<Bool>, BranchStats) {
    let mut stats = BranchStats {
        multi_candidate_nodes: selvar.len(),
        branch_addresses: cond_class_at.len(),
        ..BranchStats::default()
    };
    let mut vetoed: Vec<Bool> = Vec::new();
    for &node in nodes {
        let Some(vars) = selvar.get(&node) else {
            continue;
        };
        let Some(&machine) = cond_class_at.get(&node_address(node)) else {
            continue;
        };
        let Some(cands) = node_statements.get(&node) else {
            continue;
        };
        stats.nodes_classified += 1;
        let classes: Vec<Option<CmpClass>> = cands.iter().map(stmt_cmp_class).collect();
        if !classes.iter().any(|c| *c == Some(machine)) {
            continue;
        }
        let mismatched: Vec<usize> = classes
            .iter()
            .enumerate()
            .filter(|(_, c)| c.is_some() && **c != Some(machine))
            .map(|(i, _)| i)
            .collect();
        if mismatched.is_empty() {
            continue;
        }
        stats.nodes_watched += 1;
        for index in mismatched {
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
    use crate::x86::types::{ClightAttr, ClightIntSize};

    fn attr() -> ClightAttr {
        ClightAttr::default()
    }

    fn int_ty(sign: ClightSignedness) -> ClightType {
        ClightType::Tint(ClightIntSize::I32, sign, attr())
    }

    fn cmp(op: ClightBinaryOp, sign: ClightSignedness) -> ClightExpr {
        ClightExpr::Ebinop(
            op,
            Box::new(ClightExpr::Etempvar(1, int_ty(sign))),
            Box::new(ClightExpr::EconstInt(0, int_ty(sign))),
            int_ty(ClightSignedness::Signed),
        )
    }

    #[test]
    fn conditions_split_signed_from_unsigned() {
        assert_eq!(
            condition_cmp_class(&Condition::Ccomp(Comparison::Clt)),
            Some(CmpClass::Signed)
        );
        assert_eq!(
            condition_cmp_class(&Condition::Ccompl(Comparison::Cge)),
            Some(CmpClass::Signed)
        );
        assert_eq!(
            condition_cmp_class(&Condition::Ccompimm(Comparison::Cle, 7)),
            Some(CmpClass::Signed)
        );
        assert_eq!(
            condition_cmp_class(&Condition::Ccompu(Comparison::Cgt)),
            Some(CmpClass::Unsigned)
        );
        assert_eq!(
            condition_cmp_class(&Condition::Ccomplu(Comparison::Cle)),
            Some(CmpClass::Unsigned)
        );
        assert_eq!(
            condition_cmp_class(&Condition::Ccompluimm(Comparison::Clt, 3)),
            Some(CmpClass::Unsigned)
        );
    }

    // An equality test compiles identically for signed and unsigned operands,
    // so it is evidence of nothing and must never veto.
    #[test]
    fn equality_conditions_carry_no_signedness() {
        assert_eq!(
            condition_cmp_class(&Condition::Ccomp(Comparison::Ceq)),
            None
        );
        assert_eq!(
            condition_cmp_class(&Condition::Ccomp(Comparison::Cne)),
            None
        );
        assert_eq!(
            condition_cmp_class(&Condition::Ccompu(Comparison::Ceq)),
            None
        );
        assert_eq!(
            condition_cmp_class(&Condition::Ccompuimm(Comparison::Cne, 0)),
            None
        );
    }

    // Float comparisons, mask tests and the opaque overflow variants are not
    // integer signedness evidence either.
    #[test]
    fn non_integer_conditions_are_unclassified() {
        assert_eq!(
            condition_cmp_class(&Condition::Ccompf(Comparison::Clt)),
            None
        );
        assert_eq!(
            condition_cmp_class(&Condition::Cnotcompfs(Comparison::Cge)),
            None
        );
        assert_eq!(condition_cmp_class(&Condition::Cmaskzero(4)), None);
        assert_eq!(condition_cmp_class(&Condition::Coverflow), None);
        assert_eq!(condition_cmp_class(&Condition::Cnotoverflow), None);
    }

    #[test]
    fn candidate_signedness_follows_operand_types() {
        let signed = ClightStmt::Sifthenelse(
            cmp(ClightBinaryOp::Olt, ClightSignedness::Signed),
            Box::new(ClightStmt::Sskip),
            Box::new(ClightStmt::Sskip),
        );
        let unsigned = ClightStmt::Sifthenelse(
            cmp(ClightBinaryOp::Olt, ClightSignedness::Unsigned),
            Box::new(ClightStmt::Sskip),
            Box::new(ClightStmt::Sskip),
        );
        assert_eq!(stmt_cmp_class(&signed), Some(CmpClass::Signed));
        assert_eq!(stmt_cmp_class(&unsigned), Some(CmpClass::Unsigned));
        assert_eq!(stmt_cmp_class(&ClightStmt::Sskip), None);
    }

    #[test]
    fn equality_comparisons_are_unclassified() {
        let eq = ClightStmt::Sifthenelse(
            cmp(ClightBinaryOp::Oeq, ClightSignedness::Signed),
            Box::new(ClightStmt::Sskip),
            Box::new(ClightStmt::Sskip),
        );
        assert_eq!(stmt_cmp_class(&eq), None);
    }

    #[test]
    fn a_pointer_operand_makes_the_compare_unsigned() {
        let ptr = ClightType::Tpointer(
            std::sync::Arc::new(int_ty(ClightSignedness::Signed)),
            attr(),
        );
        let e = ClightExpr::Ebinop(
            ClightBinaryOp::Olt,
            Box::new(ClightExpr::Etempvar(1, ptr.clone())),
            Box::new(ClightExpr::Etempvar(2, ptr)),
            int_ty(ClightSignedness::Signed),
        );
        assert_eq!(expr_cmp_class(&e), Some(CmpClass::Unsigned));
    }

    // The veto only arms when a sibling already matches the machine class, so
    // the exactly-one constraint at the node stays satisfiable.
    #[test]
    fn veto_needs_a_matching_sibling() {
        let cfg = z3::Config::new();
        z3::with_z3_config(&cfg, || {
            let node: Node = 0x1000;
            let signed = ClightStmt::Sifthenelse(
                cmp(ClightBinaryOp::Olt, ClightSignedness::Signed),
                Box::new(ClightStmt::Sskip),
                Box::new(ClightStmt::Sskip),
            );
            let unsigned = ClightStmt::Sifthenelse(
                cmp(ClightBinaryOp::Olt, ClightSignedness::Unsigned),
                Box::new(ClightStmt::Sskip),
                Box::new(ClightStmt::Sskip),
            );
            let mut node_statements = std::collections::HashMap::new();
            let mut selvar = std::collections::HashMap::new();
            let mut conds = std::collections::HashMap::new();
            selvar.insert(node, vec![Bool::fresh_const("s"), Bool::fresh_const("s")]);
            conds.insert(node, CmpClass::Signed);

            // Both candidates unsigned: nothing matches the signed Mcond, so
            // nothing is vetoed.
            node_statements.insert(node, vec![unsigned.clone(), unsigned.clone()]);
            let (vetoed, stats) = build_branch_theory(&[node], &node_statements, &selvar, &conds);
            assert!(vetoed.is_empty());
            assert_eq!(stats.nodes_classified, 1);
            assert_eq!(stats.nodes_watched, 0);

            // One signed sibling present: the unsigned candidate is vetoed.
            node_statements.insert(node, vec![unsigned, signed]);
            let (vetoed, stats) = build_branch_theory(&[node], &node_statements, &selvar, &conds);
            assert_eq!(vetoed.len(), 1);
            assert_eq!(stats.nodes_watched, 1);
        });
    }
}
