//! Interface choices a function's problem can leave open.
//!
//! A function's typing touches interface variables: its own parameter and
//! return types, its callees' at each call, and the globals it reads. By
//! default each of them is the committed interface already on `FunctionData`,
//! the constant every typing rule reads. A variable listed in
//! `FunctionData::free_interfaces` is instead solved jointly with the
//! function: one selector per alternative of its domain, exactly one true,
//! and every rule that read the constant reads the chosen alternative. A pin
//! fixes the selector.
//!
//! A pinned choice gives the problem that committing that alternative would
//! give; an open one gives the best this function can do under any of its
//! alternatives. Declarations and evidence prepared before the solve still
//! come from the committed interface.

use std::collections::{BTreeMap, BTreeSet};
use z3::ast::{Bool, Dynamic};

use super::c_types::{clight_to_ty, xtype_to_ty, TypeDt};
use super::constraints::{ModelView, SolveBackend};
use super::ArtifactKey;
use crate::decompile::passes::clight_select::query::{
    representative_xtype_for_clight, FunctionData, InterfaceAlternative, InterfaceClass,
    InterfaceVarId,
};
use crate::decompile::passes::clight_select::wt_audit::xtype_to_clight;
use crate::decompile::passes::csh_pass::clight_type_from_xtype;
use crate::x86::types::{ClightExpr, ClightStmt, ClightType, Ident, XType};

/// The interface variables a solve leaves open, each with its domain and an
/// optional pin (an index into the domain).
#[derive(Debug, Clone, Default)]
pub(crate) struct FreeInterfaces(
    pub(crate) BTreeMap<InterfaceVarId, (Vec<InterfaceAlternative>, Option<usize>)>,
);

/// The chosen alternative (an index into its domain) of every open variable.
pub(crate) const CHOICES: ArtifactKey<BTreeMap<InterfaceVarId, usize>> =
    ArtifactKey::new("interface-choices");

/// The objective cost of a solve's model: the total weight of the soft clauses
/// it violates, and the number violated per weight.
pub(crate) const COST: ArtifactKey<(u64, BTreeMap<u64, usize>)> = ArtifactKey::new("objective-cost");

/// One open variable's alternatives, each with its selector.
pub(crate) type Alternatives = [(XType, Bool)];

/// The selectors of one solve's open interface variables.
#[derive(Default)]
pub(crate) struct InterfaceTerms(BTreeMap<InterfaceVarId, Vec<(XType, Bool)>>);

impl InterfaceTerms {
    pub(crate) fn build(free: &FreeInterfaces, backend: &dyn SolveBackend) -> Self {
        let mut terms = BTreeMap::new();
        for (id, (domain, pin)) in &free.0 {
            assert!(!domain.is_empty(), "interface {} has an empty domain", id.label());
            let selectors: Vec<(XType, Bool)> = domain
                .iter()
                .map(|alternative| (alternative.xtype, Bool::fresh_const("interface")))
                .collect();
            let one: Vec<(&Bool, i32)> = selectors.iter().map(|(_, s)| (s, 1)).collect();
            backend.assert_hard(&Bool::pb_eq(&one, 1));
            if let Some(index) = pin {
                backend.assert_hard(&selectors[*index].1);
            }
            terms.insert(id.clone(), selectors);
        }
        Self(terms)
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn param(&self, function: Ident, position: usize) -> Option<&Alternatives> {
        self.get(&InterfaceVarId::Param { function, position })
    }

    pub(crate) fn ret(&self, function: Ident) -> Option<&Alternatives> {
        self.get(&InterfaceVarId::Return { function })
    }

    pub(crate) fn global(&self, symbol: Ident) -> Option<&Alternatives> {
        self.get(&InterfaceVarId::Global { symbol })
    }

    fn get(&self, id: &InterfaceVarId) -> Option<&Alternatives> {
        self.0.get(id).map(Vec::as_slice)
    }

    pub(crate) fn choices(&self, model: &dyn ModelView) -> BTreeMap<InterfaceVarId, usize> {
        self.0
            .iter()
            .filter_map(|(id, alternatives)| {
                alternatives
                    .iter()
                    .position(|(_, selected)| model.truth(selected) == Some(true))
                    .map(|index| (id.clone(), index))
            })
            .collect()
    }
}

/// The type the chosen alternative denotes.
pub(crate) fn term(t: &TypeDt, alternatives: &Alternatives) -> Dynamic {
    term_of(alternatives, |_, xtype| xtype_to_ty(t, xtype))
}

/// The chosen alternative's term, each alternative's given by `of`.
fn term_of(alternatives: &Alternatives, of: impl Fn(usize, &XType) -> Dynamic) -> Dynamic {
    let last = alternatives.len() - 1;
    alternatives[..last]
        .iter()
        .enumerate()
        .rev()
        .fold(of(last, &alternatives[last].0), |chosen, (index, (xtype, selected))| {
            selected.ite(&of(index, xtype), &chosen)
        })
}

/// The alternative `FunctionData` already commits: the one of `committed`'s
/// class, or rank zero when there is none.
fn committed_index(alternatives: &Alternatives, committed: Option<&ClightType>) -> usize {
    committed
        .map(|ty| InterfaceClass::from_xtype(&representative_xtype_for_clight(ty)))
        .and_then(|class| {
            alternatives
                .iter()
                .position(|(xtype, _)| InterfaceClass::from_xtype(xtype) == class)
        })
        .unwrap_or(0)
}

/// The function's own return type. The committed alternative keeps
/// `FunctionData::return_type`; another is the declaration it would commit.
pub(crate) fn own_return_term(t: &TypeDt, func: &FunctionData, alternatives: &Alternatives) -> Dynamic {
    let committed = committed_index(alternatives, Some(&func.return_type));
    term_of(alternatives, |index, xtype| {
        if index == committed {
            clight_to_ty(t, &func.return_type)
        } else {
            clight_to_ty(t, &clight_type_from_xtype(xtype))
        }
    })
}

/// The declaration an open global's accesses take under alternative `index`.
/// None keeps `FunctionData`'s typing, its known type or, when it has none,
/// each access's own annotation: that is what the committed alternative means.
pub(crate) fn global_declaration(
    func: &FunctionData,
    symbol: Ident,
    alternatives: &Alternatives,
    index: usize,
) -> Option<ClightType> {
    let known = func.known_global_types.by_ident.get(&symbol);
    (index != committed_index(alternatives, known)).then(|| xtype_to_clight(&alternatives[index].0))
}

/// The globals `stmt` names, in any expression of it.
pub(crate) fn globals_named(stmt: &ClightStmt, out: &mut BTreeSet<Ident>) {
    match stmt {
        ClightStmt::Seffect(_, inner) | ClightStmt::Slabel(_, inner) => globals_named(inner, out),
        ClightStmt::Sassign(lhs, rhs) => {
            globals_in(lhs, out);
            globals_in(rhs, out);
        }
        ClightStmt::Sset(_, expr) | ClightStmt::Sreturn(Some(expr)) => globals_in(expr, out),
        ClightStmt::Scall(_, callee, args) => {
            globals_in(callee, out);
            args.iter().for_each(|arg| globals_in(arg, out));
        }
        ClightStmt::Sbuiltin(_, _, _, args) => args.iter().for_each(|arg| globals_in(arg, out)),
        ClightStmt::Ssequence(stmts) => stmts.iter().for_each(|s| globals_named(s, out)),
        ClightStmt::Sifthenelse(cond, then, otherwise) => {
            globals_in(cond, out);
            globals_named(then, out);
            globals_named(otherwise, out);
        }
        ClightStmt::Sloop(body, step) => {
            globals_named(body, out);
            globals_named(step, out);
        }
        ClightStmt::Sswitch(scrutinee, cases) => {
            globals_in(scrutinee, out);
            cases.iter().for_each(|(_, s)| globals_named(s, out));
        }
        ClightStmt::Sskip
        | ClightStmt::Sbreak
        | ClightStmt::Scontinue
        | ClightStmt::Sreturn(None)
        | ClightStmt::Sgoto(_) => {}
    }
}

fn globals_in(expr: &ClightExpr, out: &mut BTreeSet<Ident>) {
    match expr {
        ClightExpr::Evar(id, _) => {
            out.insert(*id);
        }
        ClightExpr::Ederef(inner, _)
        | ClightExpr::Eaddrof(inner, _)
        | ClightExpr::Eunop(_, inner, _)
        | ClightExpr::Ecast(inner, _)
        | ClightExpr::Efield(inner, _, _) => globals_in(inner, out),
        ClightExpr::Ebinop(_, lhs, rhs, _) => {
            globals_in(lhs, out);
            globals_in(rhs, out);
        }
        ClightExpr::Econdition(cond, then, otherwise, _) => {
            globals_in(cond, out);
            globals_in(then, out);
            globals_in(otherwise, out);
        }
        ClightExpr::EconstInt(..)
        | ClightExpr::EconstFloat(..)
        | ClightExpr::EconstSingle(..)
        | ClightExpr::EconstLong(..)
        | ClightExpr::EvarSymbol(..)
        | ClightExpr::Etempvar(..)
        | ClightExpr::Esizeof(..)
        | ClightExpr::Ealignof(..) => {}
    }
}

/// Whether the chosen alternative satisfies `property`.
pub(crate) fn chooses(alternatives: &Alternatives, property: impl Fn(&XType) -> bool) -> Bool {
    let matching: Vec<Bool> = alternatives
        .iter()
        .filter(|(xtype, _)| property(xtype))
        .map(|(_, selected)| selected.clone())
        .collect();
    Bool::or(&matching)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::passes::clight_select::candtype::{CandType, Sign};
    use crate::decompile::passes::clight_select::query::{CalleeSignature, KnownGlobalTypes};
    use crate::decompile::passes::clight_select::syntax::solve::solve_function_z3;
    use crate::x86::types::{ClightAttr, ClightFloatSize, ClightIntSize, ClightSignedness, ParamType};
    use std::collections::HashMap;
    use std::sync::Arc;

    const F: Ident = 0x100;
    const G: Ident = 0x200;
    const GLOBAL: Ident = 0x300;

    fn pointer() -> ClightType {
        ClightType::Tpointer(
            Arc::new(ClightType::Tint(ClightIntSize::I8, ClightSignedness::Signed, ClightAttr::default())),
            ClightAttr::default(),
        )
    }
    fn double() -> ClightType {
        ClightType::Tfloat(ClightFloatSize::F64, ClightAttr::default())
    }
    fn int() -> ClightType {
        ClightType::Tint(ClightIntSize::I32, ClightSignedness::Signed, ClightAttr::default())
    }

    /// A function at node 20 whose register 5 holds a pointer.
    fn function(statements: Vec<ClightStmt>) -> FunctionData {
        let mut f = FunctionData::new(F as u64, "f".into(), vec![], vec![], None, 0, 20, true);
        f.var_type_candidates.insert(5, vec![CandType::PtrChar]);
        f.must_pointer_regs.insert(5);
        f.node_statements.insert(20, statements);
        f
    }

    fn callee(f: &mut FunctionData, return_type: XType, param_types: Vec<XType>) {
        f.callee_signatures.insert(
            G,
            CalleeSignature { param_count: param_types.len(), return_type, param_types, is_varargs: false },
        );
    }

    fn open(f: &FunctionData, id: &InterfaceVarId, domain: &[XType], pin: Option<usize>) -> FunctionData {
        let mut f = f.clone();
        let domain = domain
            .iter()
            .map(|xtype| InterfaceAlternative { class: InterfaceClass::from_xtype(xtype), xtype: *xtype })
            .collect();
        f.free_interfaces.0.insert(id.clone(), (domain, pin));
        f
    }

    /// The open choices, the objective cost and the selected candidate at node 20.
    fn solve(f: &FunctionData) -> (BTreeMap<InterfaceVarId, usize>, u64, Option<usize>) {
        let (candidates, _, _, _, _, results) =
            solve_function_z3(f, &HashMap::new(), &[]).expect("a model");
        let choices = CHOICES.get(&results).cloned().unwrap_or_default();
        (choices, COST.get(&results).expect("a cost").0, candidates.get(&20).copied().flatten())
    }

    /// Pinned at the committed alternative the problem is the ordinary one;
    /// left open it picks `expected` at a lower cost, and pinning that
    /// alternative reaches the open optimum (the bound is attained).
    fn check_open_choice(f: &FunctionData, id: InterfaceVarId, domain: &[XType], expected: usize) {
        let (_, ordinary, _) = solve(f);
        let (_, committed, _) = solve(&open(f, &id, domain, Some(0)));
        let (choices, free, _) = solve(&open(f, &id, domain, None));
        let (_, attained, _) = solve(&open(f, &id, domain, Some(expected)));
        assert_eq!(committed, ordinary, "pinned at the committed alternative");
        assert_eq!(choices[&id], expected);
        assert!(free < committed, "open {free} vs committed {committed}");
        assert_eq!(attained, free);
    }

    #[test]
    fn an_open_callee_parameter_takes_the_class_of_its_argument() {
        // `g(p)` with a pointer p, where g's committed parameter is a double.
        let mut f = function(vec![ClightStmt::Scall(
            None,
            ClightExpr::Evar(G, int()),
            vec![ClightExpr::Etempvar(5, pointer())],
        )]);
        callee(&mut f, XType::Xvoid, vec![XType::Xfloat]);
        check_open_choice(&f, InterfaceVarId::Param { function: G, position: 0 }, &[XType::Xfloat, XType::Xptr], 1);
    }

    #[test]
    fn an_open_return_type_takes_the_class_the_function_returns() {
        let mut f = function(vec![ClightStmt::Sreturn(Some(ClightExpr::Etempvar(5, pointer())))]);
        f.return_type = double();
        check_open_choice(&f, InterfaceVarId::Return { function: F }, &[XType::Xfloat, XType::Xptr], 1);
    }

    #[test]
    fn an_open_global_takes_the_class_its_accesses_need() {
        // `p = global;` with a pointer p, where the global is committed a double.
        let mut f = function(vec![ClightStmt::Sset(5, ClightExpr::Evar(GLOBAL, double()))]);
        let mut known = KnownGlobalTypes::default();
        known.by_ident.insert(GLOBAL, double());
        f.known_global_types = Arc::new(known);
        check_open_choice(&f, InterfaceVarId::Global { symbol: GLOBAL }, &[XType::Xfloat, XType::Xptr], 1);
    }

    #[test]
    fn an_open_void_callee_return_decides_whether_its_result_may_be_kept() {
        // `r = g();` or `g();`, where g's committed return is int.
        let mut f = function(vec![
            ClightStmt::Scall(Some(6), ClightExpr::Evar(G, int()), vec![]),
            ClightStmt::Scall(None, ClightExpr::Evar(G, int()), vec![]),
        ]);
        f.var_type_candidates.insert(6, vec![CandType::I32(Sign::Signed)]);
        callee(&mut f, XType::Xint, vec![]);
        let id = InterfaceVarId::Return { function: G };
        let domain = [XType::Xint, XType::Xvoid];
        let (_, ordinary, _) = solve(&f);
        let (_, committed, _) = solve(&open(&f, &id, &domain, Some(0)));
        assert_eq!(committed, ordinary);
        // A void callee's result cannot be kept: the call is selected without it.
        let (_, _, selected) = solve(&open(&f, &id, &domain, Some(1)));
        assert_eq!(selected, Some(1));
    }

    #[test]
    fn an_open_own_parameter_is_declared_as_the_chosen_class() {
        // The parameter register is dereferenced, so only a pointer
        // alternative is feasible; its committed type is int.
        let mut f = FunctionData::new(F as u64, "f".into(), vec![3], vec![ParamType::Typed(XType::Xint)], None, 0, 20, true);
        f.var_type_candidates.insert(3, vec![CandType::I32(Sign::Signed), CandType::PtrChar]);
        f.var_type_candidates.insert(5, vec![CandType::I32(Sign::Signed)]);
        f.must_pointer_regs.insert(3);
        f.node_statements.insert(
            20,
            vec![ClightStmt::Sset(5, ClightExpr::Ederef(Box::new(ClightExpr::Etempvar(3, pointer())), int()))],
        );
        let id = InterfaceVarId::Param { function: F, position: 0 };
        let domain = [XType::Xint, XType::Xptr];
        let (choices, _, _) = solve(&open(&f, &id, &domain, None));
        assert_eq!(choices[&id], 1);
        assert!(solve_function_z3(&open(&f, &id, &domain, Some(0)), &HashMap::new(), &[]).is_err());
    }
}
