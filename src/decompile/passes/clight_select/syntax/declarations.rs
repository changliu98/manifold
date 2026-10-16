//! Finite concrete declaration choices shared by selection analyses.
//!
//! Managed declarations have a finite, structural domain. The C-class variable
//! is a projection of that domain, not a second authority for its spelling.
//! Legacy representatives remain explicit alternatives when proof is missing.

use crate::decompile::passes::clight_select::syntax::c_types::{anchor_index, render_type, term_to_ty, TypeDt};
use crate::decompile::passes::clight_select::syntax::constraints::{ModelView, SolveBackend};
use crate::decompile::passes::clight_select::syntax::{DeclarationContext, Stack};
use crate::decompile::passes::clight_select::type_graph::{
    TypeAdmission, TypeArena, TypeId, TypeTerm,
};
use crate::decompile::passes::clight_select::{candtype::CandType, query::FunctionData};
use crate::x86::types::{ClightExpr, ClightStmt, RTLReg};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use z3::ast::{Bool, Dynamic};

pub(crate) struct Choice {
    pub fallback: Bool,
    pub alternatives: Vec<(TypeId, Bool)>,
    pub legacy: BTreeSet<TypeId>,
    pub evidence: BTreeSet<TypeId>,
    pub proposed: BTreeSet<TypeId>,
}

#[derive(Default)]
pub(crate) struct Declarations(
    pub BTreeMap<RTLReg, Choice>,
    TypeArena,
    RefCell<Vec<CheckedProfile>>,
);

struct CheckedProfile {
    node: crate::x86::types::Node,
    candidate: usize,
    guard: Bool,
    declarations: BTreeMap<RTLReg, TypeTerm>,
}

/// The old renderer's representatives, made explicit before solving. These
/// are compatibility options, not positive evidence for source-level types.
fn legacy_terms(function: &FunctionData, reg: RTLReg) -> BTreeSet<TypeTerm> {
    use crate::decompile::passes::clight_select::candtype::Sign;
    let candidates = &function.var_type_candidates[&reg];
    let mut rendered = vec![CandType::I64(Sign::Signed), CandType::PtrLong];
    if candidates
        .iter()
        .any(|c| c.is_float() || c.is_float_pointee())
    {
        rendered.extend([CandType::F64, CandType::PtrDouble]);
    }
    rendered.extend(
        candidates
            .iter()
            .copied()
            .filter(|c| matches!(c, CandType::PtrStruct(_) | CandType::PtrFunc)),
    );
    rendered
        .into_iter()
        .map(|c| {
            let c = anchor_index(candidates, c, false)
                .map(|i| candidates[i])
                .unwrap_or(c);
            TypeTerm::from_candidate(c, function.data_model)
        })
        .collect()
}

/// All declaration dependencies, including definitions and conditional arms.
/// Unknown semantic operations still need this vocabulary to fall back safely.
pub(crate) fn dependencies(statement: &ClightStmt) -> BTreeSet<RTLReg> {
    fn expr(value: &ClightExpr, out: &mut BTreeSet<RTLReg>) {
        match value {
            ClightExpr::Etempvar(reg, _) => {
                out.insert(*reg as RTLReg);
            }
            ClightExpr::Ederef(a, _)
            | ClightExpr::Eaddrof(a, _)
            | ClightExpr::Ecast(a, _)
            | ClightExpr::Eunop(_, a, _)
            | ClightExpr::Efield(a, _, _) => expr(a, out),
            ClightExpr::Ebinop(_, a, b, _) => {
                expr(a, out);
                expr(b, out);
            }
            ClightExpr::Econdition(c, a, b, _) => {
                expr(c, out);
                expr(a, out);
                expr(b, out);
            }
            ClightExpr::EconstInt(..)
            | ClightExpr::EconstLong(..)
            | ClightExpr::EconstFloat(..)
            | ClightExpr::EconstSingle(..)
            | ClightExpr::Evar(..)
            | ClightExpr::EvarSymbol(..)
            | ClightExpr::Esizeof(..)
            | ClightExpr::Ealignof(..) => {}
        }
    }
    fn stmt(value: &ClightStmt, out: &mut BTreeSet<RTLReg>) {
        match value {
            ClightStmt::Sset(reg, rhs) => {
                out.insert(*reg as RTLReg);
                expr(rhs, out);
            }
            ClightStmt::Sassign(lhs, rhs) => {
                expr(lhs, out);
                expr(rhs, out);
            }
            ClightStmt::Scall(dst, callee, args) => {
                out.extend(dst.iter().map(|r| *r as RTLReg));
                expr(callee, out);
                for arg in args {
                    expr(arg, out);
                }
            }
            ClightStmt::Sbuiltin(dst, _, _, args) => {
                out.extend(dst.iter().map(|r| *r as RTLReg));
                for arg in args {
                    expr(arg, out);
                }
            }
            ClightStmt::Sifthenelse(c, a, b) => {
                expr(c, out);
                stmt(a, out);
                stmt(b, out);
            }
            ClightStmt::Sloop(a, b) => {
                stmt(a, out);
                stmt(b, out);
            }
            ClightStmt::Ssequence(statements) => {
                for s in statements {
                    stmt(s, out);
                }
            }
            ClightStmt::Sswitch(e, arms) => {
                expr(e, out);
                for (_, s) in arms {
                    stmt(s, out);
                }
            }
            ClightStmt::Slabel(_, s) | ClightStmt::Seffect(_, s) => stmt(s, out),
            ClightStmt::Sreturn(Some(e)) => expr(e, out),
            ClightStmt::Sskip
            | ClightStmt::Sbreak
            | ClightStmt::Scontinue
            | ClightStmt::Sreturn(None)
            | ClightStmt::Sgoto(_) => {}
        }
    }
    let mut result = BTreeSet::new();
    stmt(statement, &mut result);
    result
}

impl Declarations {
    pub fn build(
        stack: &Stack<'_>,
        cx: &DeclarationContext<'_>,
        registers: &[RTLReg],
        classes: &HashMap<RTLReg, Dynamic>,
        sink: &dyn SolveBackend,
    ) -> Self {
        let mut result = Self::default();
        for &reg in registers {
            let mut candidates: BTreeSet<_> = stack
                .components()
                .flat_map(|a| a.declaration_alternatives(cx, reg))
                .collect();
            if candidates.is_empty() {
                continue;
            }
            let legacy = legacy_terms(cx.function, reg);
            let evidence: BTreeSet<_> = stack
                .components()
                .flat_map(|a| a.evidenced_declarations(cx, reg))
                .filter(|ty| candidates.contains(ty))
                .collect();
            let proposed = candidates
                .iter()
                .cloned()
                .map(|ty| result.1.intern(ty))
                .collect();
            candidates.extend(legacy.iter().cloned());
            let evidence = evidence.into_iter().map(|ty| result.1.intern(ty)).collect();
            let legacy: BTreeSet<_> = legacy.into_iter().map(|ty| result.1.intern(ty)).collect();
            let alternatives: Vec<_> = candidates
                .into_iter()
                .map(|candidate| {
                    (
                        result.1.intern(candidate),
                        Bool::fresh_const("decl_concrete"),
                    )
                })
                .collect();
            let terms: Vec<_> = alternatives
                .iter()
                .map(|(_, selected)| (selected, 1))
                .collect();
            sink.assert_hard(&Bool::pb_eq(&terms, 1));
            for (candidate, selected) in &alternatives {
                sink.assert_hard(
                    &selected
                        .implies(classes[&reg]._eq(term_to_ty(cx.types, result.1.get(*candidate)))),
                );
            }
            let fallback = Bool::or(
                &alternatives
                    .iter()
                    .filter(|(id, _)| legacy.contains(id))
                    .map(|(_, selected)| selected.clone())
                    .collect::<Vec<_>>(),
            );
            result.0.insert(
                reg,
                Choice {
                    fallback,
                    alternatives,
                    legacy,
                    evidence,
                    proposed,
                },
            );
        }
        result
    }

    pub fn term(&self, id: TypeId) -> &TypeTerm {
        self.1.get(id)
    }

    pub fn options(&self, reg: RTLReg) -> impl Iterator<Item = (&TypeTerm, &Bool)> {
        self.0
            .get(&reg)
            .into_iter()
            .flat_map(|choice| &choice.alternatives)
            .map(|(id, b)| (self.term(*id), b))
    }

    pub fn selected(&self, model: &dyn ModelView, reg: RTLReg) -> Option<&TypeTerm> {
        self.0
            .get(&reg)?
            .alternatives
            .iter()
            .find_map(|(candidate, selected)| {
                (model.truth(selected) == Some(true)).then(|| self.term(*candidate))
            })
    }

    pub fn render(
        &self,
        types: &TypeDt,
        model: &dyn ModelView,
        class: &Dynamic,
        reg: RTLReg,
        function: &FunctionData,
        allow_void: bool,
    ) -> TypeTerm {
        self.selected(model, reg).cloned().unwrap_or_else(|| {
            assert!(
                !self.0.contains_key(&reg),
                "model lacks an exact declaration"
            );
            let rendered = render_type(types, model, class, reg, function, allow_void);
            let candidate = anchor_index(&function.var_type_candidates[&reg], rendered, allow_void)
                .map(|i| function.var_type_candidates[&reg][i])
                .unwrap_or(rendered);
            TypeTerm::from_candidate(candidate, function.data_model)
        })
    }

    /// Record EXACT declarations read by a positive check, not a syntactic
    /// overapproximation of native register names. Inlined producers can make
    /// a machine register irrelevant to the C proof.
    pub fn record_profile(
        &self,
        node: crate::x86::types::Node,
        candidate: usize,
        guard: Bool,
        registers: &BTreeSet<RTLReg>,
        profile: &HashMap<RTLReg, crate::decompile::passes::c_pass::types::CType>,
        data_model: crate::abi::DataModel,
    ) {
        let declarations = registers
            .iter()
            .filter_map(|reg| {
                profile
                    .get(reg)
                    .and_then(|ty| TypeTerm::from_c(ty, data_model))
                    .map(|ty| (*reg, ty))
            })
            .collect();
        self.2.borrow_mut().push(CheckedProfile {
            node,
            candidate,
            guard,
            declarations,
        });
    }

    pub fn commitments(
        &self,
        model: &dyn ModelView,
        statements: &HashMap<crate::x86::types::Node, Option<usize>>,
        results: &crate::decompile::passes::clight_select::syntax::Artifacts,
    ) -> BTreeMap<RTLReg, TypeTerm> {
        let validated = crate::decompile::passes::clight_select::solvers::profiles::VALIDATED.get(results);
        let admissions = self.admissions(model);
        // Preservation is not a whole-variable equivalence certificate. Freeze
        // evidence-selected changes and the exact bindings needed by accepted
        // checks or retained counterexamples, including a repaired legacy
        // carrier. An uncertified hypothesis still has ONE declaration owner:
        // emission must not silently replace the solver's explicit decision.
        let mut committed: BTreeMap<_, _> = admissions
            .iter()
            .filter(|(reg, status)| {
                **status != TypeAdmission::LegacyFallback
                    || validated.is_some_and(|regs| regs.contains(reg))
            })
            .filter_map(|(&reg, _)| self.selected(model, reg).map(|ty| (reg, ty.clone())))
            .collect();
        if let Some(bindings) = crate::decompile::passes::clight_select::solvers::profiles::PRESERVED.get(results) {
            committed.extend(bindings.iter().map(|(&reg, ty)| (reg, ty.clone())));
        }
        for &reg in crate::decompile::passes::clight_select::solvers::profiles::FALLBACK_PRESERVED
            .get(results)
            .into_iter()
            .flatten()
        {
            if let Some(ty) = self.selected(model, reg) {
                committed.insert(reg, ty.clone());
            }
        }
        let refined: BTreeSet<_> = self
            .0
            .iter()
            .filter_map(|(&reg, choice)| {
                choice
                    .alternatives
                    .iter()
                    .find(|(_, b)| model.truth(b) == Some(true))
                    .and_then(|(id, _)| {
                        (!choice.legacy.contains(id)
                            && self.term(*id).is_integer()
                            && validated.is_some_and(|regs| regs.contains(&reg)))
                        .then_some(reg)
                    })
            })
            .collect();
        for profile in self.2.borrow().iter() {
            // Use the final re-pick, not the optimizer's earlier statement
            // Boolean. The checked declaration guard is independent of it.
            if statements.get(&profile.node) != Some(&Some(profile.candidate))
                || !profile.declarations.keys().any(|r| refined.contains(r))
                || model.truth(&profile.guard) != Some(true)
            {
                continue;
            }
            for (&reg, ty) in &profile.declarations {
                if let Some(previous) = committed.insert(reg, ty.clone()) {
                    assert_eq!(previous, *ty, "checks disagree on a concrete declaration");
                }
            }
        }
        committed
    }

    pub fn admissions(&self, model: &dyn ModelView) -> BTreeMap<RTLReg, TypeAdmission> {
        self.0
            .iter()
            .filter_map(|(&reg, choice)| {
                choice
                    .alternatives
                    .iter()
                    .find(|(_, b)| model.truth(b) == Some(true))
                    .map(|(id, _)| {
                        let status = if choice.legacy.contains(id) {
                            TypeAdmission::LegacyFallback
                        } else if choice.evidence.contains(id) {
                            TypeAdmission::EvidenceSupported
                        } else if self.term(*id).is_integer() {
                            TypeAdmission::ValueAndDefinedness
                        } else {
                            TypeAdmission::ExplicitPointerViews
                        };
                        (reg, status)
                    })
            })
            .collect()
    }

    /// Guard a checked declaration profile, including the class fallback.
    pub fn guard(
        &self,
        reg: RTLReg,
        fallback_matches: bool,
        matches: impl Fn(&TypeTerm) -> bool,
    ) -> Bool {
        let Some(choice) = self.0.get(&reg) else {
            return Bool::from_bool(fallback_matches);
        };
        let terms: Vec<_> = choice
            .alternatives
            .iter()
            .filter_map(|(candidate, selected)| {
                matches(self.term(*candidate)).then_some(selected.clone())
            })
            .collect();
        Bool::or(&terms)
    }
}

#[cfg(test)]
mod tests {
    use crate::decompile::passes::clight_select::candtype::Sign;
    use crate::decompile::passes::clight_select::syntax::declarations::*;
    use crate::abi::DataModel;
    use crate::decompile::passes::c_pass::types::CType;

    #[test]
    fn commitments_use_the_final_candidate_and_exact_checked_inputs() {
        let mut choices = Declarations::default();
        let word = TypeTerm::from_candidate(CandType::I32(Sign::Unsigned), DataModel::Lp64);
        let id = choices.1.intern(word.clone());
        choices.0.insert(
            3,
            Choice {
                fallback: Bool::from_bool(false),
                alternatives: vec![(id, Bool::from_bool(true))],
                legacy: BTreeSet::new(),
                evidence: BTreeSet::new(),
                proposed: BTreeSet::from([id]),
            },
        );
        for (candidate, input) in [(0, 2), (1, 1)] {
            let profile = HashMap::from([(3, CType::uint()), (input, CType::ulong())]);
            choices.record_profile(
                10,
                candidate,
                Bool::from_bool(true),
                &BTreeSet::from([3, input]),
                &profile,
                DataModel::Lp64,
            );
        }
        let solver = z3::Solver::new();
        assert_eq!(solver.check(), z3::SatResult::Sat);
        let model = solver.get_model().unwrap();
        let mut results = crate::decompile::passes::clight_select::syntax::Artifacts::default();
        crate::decompile::passes::clight_select::solvers::profiles::VALIDATED.insert(&mut results, BTreeSet::from([3]));
        let declarations = choices.commitments(&model, &HashMap::from([(10, Some(1))]), &results);
        assert_eq!(declarations[&3], word);
        assert!(declarations.contains_key(&1));
        assert!(
            !declarations.contains_key(&2),
            "an unselected proof must not freeze a different input"
        );
    }
}
