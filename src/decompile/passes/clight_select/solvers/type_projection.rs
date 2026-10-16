//! A deliberately small representation-substitution theorem for C pointers.
//!
//! Under the target's existing flat data-pointer ABI and the legacy program's
//! defined executions, a declaration may change its pointee when every read
//! immediately converts to a byte/void or full-width integer view and every
//! definition has that new type (or is null). Pointer-to-pointer alignment
//! assumptions do NOT follow from declaration spelling. Construction uses a
//! full-width integer bridge; typed dereferences and bare arithmetic/escape
//! are outside this substitution theorem.
//! This proves independence from a declaration spelling, not source-type
//! uniqueness, allocation lifetime, or whole-program binary equivalence.

use crate::decompile::passes::clight_select::type_graph::TypeTerm;
use crate::abi::DataModel;
use crate::decompile::passes::c_pass::{
    convert::from_relations::{convert_stmt, ConversionContext},
    helpers::param_name_for_reg,
    types::*,
};
use crate::x86::types::{ClightStmt, RTLReg};
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub(crate) struct Projection {
    pub node: crate::x86::types::Node,
    pub parent: ClightStmt,
    pub statement: ClightStmt,
    pub reg: RTLReg,
    pub ty: TypeTerm,
}
pub(crate) const PROJECTIONS: crate::decompile::passes::clight_select::syntax::ArtifactKey<Vec<Projection>> =
    crate::decompile::passes::clight_select::syntax::ArtifactKey::projected("declaration-projections", |projections, plan| {
        projections
            .iter()
            .map(|p| Projection {
                node: p.node,
                parent: plan.statement(p.node, &p.parent),
                statement: plan.statement(p.node, &p.statement),
                reg: plan.write(p.node, p.reg),
                ty: p.ty.clone(),
            })
            .collect()
    });

/// Instantiate the declaration grammar at its C conversion boundary. A new
/// pointee type needs an explicit assignment cast, not an emitter repair.
/// Construction preserves parent/world provenance; admission remains joint
/// with the exact declaration and the pointer transport theorem below.
pub(crate) fn extend_candidates(function: &mut crate::decompile::passes::clight_select::query::FunctionData) {
    use crate::x86::types::{ClightExpr, ClightType};
    fn instantiate(
        statement: &ClightStmt,
        reg: RTLReg,
        ty: &ClightType,
        word: &ClightType,
    ) -> Option<ClightStmt> {
        match statement {
            ClightStmt::Sset(dst, rhs) if *dst as RTLReg == reg => {
                // This grammar changes a pointee interpretation, not an
                // integer/float expression's semantic class.
                if !matches!(
                    rhs,
                    ClightExpr::Ecast(_, ClightType::Tpointer(..))
                        | ClightExpr::Etempvar(_, ClightType::Tpointer(..))
                        | ClightExpr::Eaddrof(_, ClightType::Tpointer(..))
                        | ClightExpr::Evar(_, ClightType::Tpointer(..))
                        | ClightExpr::EvarSymbol(_, ClightType::Tpointer(..))
                        | ClightExpr::Ederef(_, ClightType::Tpointer(..))
                        | ClightExpr::Efield(_, _, ClightType::Tpointer(..))
                        | ClightExpr::Ebinop(_, _, _, ClightType::Tpointer(..))
                        | ClightExpr::Econdition(_, _, _, ClightType::Tpointer(..))
                ) {
                    return None;
                }
                if matches!(rhs, ClightExpr::Ecast(_, existing) if existing == ty) {
                    return None;
                }
                // The word bridge does not depend on a pointee, so parents that
                // differ only in outer pointer casts denote one value and
                // project to one statement.
                let mut value = rhs;
                while let ClightExpr::Ecast(inner, ClightType::Tpointer(..)) = value {
                    value = inner.as_ref();
                }
                Some(ClightStmt::Sset(
                    *dst,
                    ClightExpr::Ecast(
                        Box::new(ClightExpr::Ecast(Box::new(value.clone()), word.clone())),
                        ty.clone(),
                    ),
                ))
            }
            ClightStmt::Slabel(label, body) => Some(ClightStmt::Slabel(
                *label,
                Box::new(instantiate(body, reg, ty, word)?),
            )),
            ClightStmt::Seffect(site, body) => Some(ClightStmt::Seffect(
                *site,
                Box::new(instantiate(body, reg, ty, word)?),
            )),
            _ => None,
        }
    }
    let mut projections = Vec::new();
    let mut additions = Vec::new();
    let word = TypeTerm::integer(
        (function.data_model.pointer_size() * 8) as u32,
        crate::decompile::passes::clight_select::candtype::Sign::Unsigned,
        function.data_model,
    )
    .unwrap()
    .to_clight(function.data_model);
    if let Some(graph) = crate::decompile::passes::clight_select::syntax::type_evidence::GRAPH.get(&function.analysis_facts) {
        for (&reg, terms) in &graph.hypotheses {
            for term in terms
                .iter()
                .filter(|t| t.is_pointer() && t.legacy_candidate(function.data_model).is_none())
            {
                for (&node, candidates) in &function.node_statements {
                    for (parent, statement) in candidates.iter().enumerate() {
                        let Some(projected) = instantiate(
                            statement,
                            reg,
                            &term.to_clight(function.data_model),
                            &word,
                        ) else {
                            continue;
                        };
                        if candidates.contains(&projected) {
                            continue;
                        }
                        projections.push(Projection {
                            node,
                            parent: statement.clone(),
                            statement: projected.clone(),
                            reg,
                            ty: term.clone(),
                        });
                        additions.push((node, parent, projected));
                    }
                }
            }
        }
    }
    crate::decompile::passes::clight_select::syntax::candidates::inherit(function, additions);
    PROJECTIONS.insert(&mut function.analysis_facts, projections);
}

pub(crate) fn pointer_transport(
    statement: &ClightStmt,
    reg: RTLReg,
    before: &TypeTerm,
    after: &TypeTerm,
    model: DataModel,
) -> bool {
    let (TypeTerm::Pointer(a), TypeTerm::Pointer(b)) = (before, after) else {
        return false;
    };
    if matches!(a.as_ref(), TypeTerm::Function { .. })
        || matches!(b.as_ref(), TypeTerm::Function { .. })
    {
        return false;
    }
    let name = param_name_for_reg(reg);
    let mut ctx = ConversionContext::new(HashMap::new(), model);
    let statement = convert_stmt(statement, &mut ctx);
    Transport {
        name: &name,
        target: &after.to_c(model),
        model,
    }
    .statement(&statement)
}

/// A declaration use is independent of the discarded high bits only when
/// the read itself is immediately converted to a fixed, no-wider integer
/// view. An outer cast around arithmetic does not establish this property.
/// Definitions need native transfer evidence and are deliberately excluded.
pub(super) fn integer_view_use(
    statement: &ClightStmt,
    reg: RTLReg,
    declarations: &HashMap<RTLReg, CType>,
    function: &crate::decompile::passes::clight_select::query::FunctionData,
    names: &HashMap<String, crate::x86::types::Ident>,
) -> bool {
    use crate::x86::types::ClightExpr;
    let Some(after) = declarations.get(&reg) else {
        return false;
    };
    let bytes = TypeTerm::from_c(after, function.data_model)
        .and_then(|t| t.object_bytes(function.data_model));
    let Some(bytes) = bytes else {
        return false;
    };
    let name = param_name_for_reg(reg);
    fn direct(e: &CExpr, name: &str) -> bool {
        match e {
            CExpr::Var(n) => n == name,
            CExpr::Paren(e) => direct(e, name),
            _ => false,
        }
    }
    fn read(e: &CExpr, name: &str, bytes: usize, model: DataModel) -> bool {
        match e {
            CExpr::Var(n) => n != name,
            CExpr::IntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_)
            | CExpr::AlignofType(_) => true,
            CExpr::Cast(ty, inner) => {
                let clips = matches!(ty, CType::Int(..))
                    && TypeTerm::from_c(ty, model)
                        .and_then(|t| t.object_bytes(model))
                        .is_some_and(|n| n <= bytes);
                (clips && direct(inner, name)) || read(inner, name, bytes, model)
            }
            CExpr::Unary(UnaryOp::AddrOf, _) | CExpr::SizeofExpr(_) => false,
            CExpr::Unary(_, e) | CExpr::Paren(e) | CExpr::Member(e, _) | CExpr::MemberPtr(e, _) => {
                read(e, name, bytes, model)
            }
            CExpr::Binary(_, a, b) | CExpr::Index(a, b) => {
                read(a, name, bytes, model) && read(b, name, bytes, model)
            }
            CExpr::Ternary(a, b, c) => [a, b, c].into_iter().all(|e| read(e, name, bytes, model)),
            _ => false,
        }
    }
    let mut context = ConversionContext::new(HashMap::new(), function.data_model);
    let mut observe = |expression: &ClightExpr, conversion: Option<CType>| {
        let expression = crate::decompile::passes::c_pass::convert::from_relations::convert_expr(
            expression,
            &mut context,
        );
        let expression = match conversion {
            Some(ty) => CExpr::cast(ty, expression),
            None => expression,
        };
        read(&expression, &name, bytes, function.data_model)
    };
    match crate::decompile::passes::clight_select::solvers::memory_theory::primitive(statement) {
        ClightStmt::Sifthenelse(condition, yes, no) => {
            observe(condition, None)
                && integer_view_use(yes, reg, declarations, function, names)
                && integer_view_use(no, reg, declarations, function, names)
        }
        ClightStmt::Ssequence(statements) => statements
            .iter()
            .all(|s| integer_view_use(s, reg, declarations, function, names)),
        ClightStmt::Sloop(body, increment) => {
            integer_view_use(body, reg, declarations, function, names)
                && integer_view_use(increment, reg, declarations, function, names)
        }
        ClightStmt::Sswitch(selector, arms) => {
            observe(selector, None)
                && arms
                    .iter()
                    .all(|(_, s)| integer_view_use(s, reg, declarations, function, names))
        }
        ClightStmt::Sreturn(Some(e)) => observe(
            e,
            Some(
                crate::decompile::passes::c_pass::convert::from_relations::convert_clight_type(
                    &function.return_type,
                    function.data_model,
                ),
            ),
        ),
        ClightStmt::Sset(dst, rhs) if *dst as RTLReg != reg => {
            observe(rhs, declarations.get(&(*dst as RTLReg)).cloned())
        }
        ClightStmt::Scall(dst, callee, arguments) if dst.is_none_or(|dst| dst as RTLReg != reg) => {
            if !observe(callee, None) {
                return false;
            }
            let signature = crate::decompile::passes::clight_select::select::callee_ident_from_expr(callee, names)
                .and_then(|id| function.callee_signatures.get(&id));
            arguments.iter().enumerate().all(|(i, argument)| {
                let formal = signature.and_then(|s| s.param_types.get(i)).map(|ty| {
                    crate::decompile::passes::clight_select::type_graph::TypeTerm::from_candidate(
                        crate::decompile::passes::clight_select::candtype::CandType::from_xtype(ty),
                        function.data_model,
                    )
                    .to_c(function.data_model)
                });
                observe(argument, formal)
            })
        }
        _ => !crate::decompile::passes::clight_select::syntax::declarations::dependencies(statement).contains(&reg),
    }
}

struct Transport<'a> {
    name: &'a str,
    target: &'a CType,
    model: DataModel,
}
impl Transport<'_> {
    fn direct(&self, e: &CExpr) -> bool {
        match e {
            CExpr::Var(name) => name == self.name,
            CExpr::Paren(e) => self.direct(e),
            _ => false,
        }
    }
    fn definition(&self, e: &CExpr) -> bool {
        match e {
            CExpr::IntLit(l) => l.value == 0,
            CExpr::Paren(e) => self.definition(e),
            CExpr::Cast(ty, e) if ty == self.target => self.expression(e),
            _ => false,
        }
    }
    fn expression(&self, e: &CExpr) -> bool {
        match e {
            CExpr::Var(name) => name != self.name,
            CExpr::IntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::StringLit(_)
            | CExpr::CharLit(_)
            | CExpr::SizeofType(_)
            | CExpr::AlignofType(_) => true,
            // Only a direct read is erased by a fixed cast. In (T)(p + k),
            // the stride still depends on p and must be checked recursively.
            CExpr::Cast(ty, inner) => {
                let neutral = match ty {
                    CType::Pointer(pointee, _) => matches!(
                        pointee.as_ref(),
                        CType::Void | CType::Bool | CType::Int(IntSize::Char, _)
                    ),
                    CType::Int(_, _) => {
                        TypeTerm::from_c(ty, self.model).and_then(|t| t.object_bytes(self.model))
                            == Some(self.model.pointer_size())
                    }
                    _ => false,
                };
                (neutral && self.direct(inner)) || self.expression(inner)
            }
            CExpr::SizeofExpr(e) if self.direct(e) => true, // all data pointers have the ABI size
            CExpr::Assign(AssignOp::Assign, lhs, rhs) if self.direct(lhs) => self.definition(rhs),
            CExpr::Unary(_, e)
            | CExpr::Paren(e)
            | CExpr::Member(e, _)
            | CExpr::MemberPtr(e, _)
            | CExpr::SizeofExpr(e) => self.expression(e),
            CExpr::Binary(_, a, b) | CExpr::Index(a, b) | CExpr::Assign(_, a, b) => {
                self.expression(a) && self.expression(b)
            }
            CExpr::Ternary(a, b, c) => {
                self.expression(a) && self.expression(b) && self.expression(c)
            }
            CExpr::Call(f, args) => self.expression(f) && args.iter().all(|e| self.expression(e)),
            CExpr::StmtExpr(statements, tail) => {
                statements.iter().all(|s| self.statement(s)) && self.expression(tail)
            }
            // New AST forms must opt into this theorem explicitly.
            CExpr::CompoundLit(..) | CExpr::Generic(..) => false,
        }
    }
    fn statement(&self, s: &CStmt) -> bool {
        match s {
            CStmt::Expr(e) | CStmt::Return(Some(e)) => self.expression(e),
            CStmt::Block(items) => items.iter().all(|i| match i {
                CBlockItem::Stmt(s) => self.statement(s),
                CBlockItem::Decl(_) => false,
            }),
            CStmt::If(c, a, b) => {
                self.expression(c)
                    && self.statement(a)
                    && b.as_ref().is_none_or(|s| self.statement(s))
            }
            CStmt::While(c, s) | CStmt::Switch(c, s) | CStmt::DoWhile(s, c) => {
                self.expression(c) && self.statement(s)
            }
            CStmt::For(init, cond, step, body) => {
                init.as_ref().is_none_or(|i| match i {
                    ForInit::Expr(e) => self.expression(e),
                    ForInit::Decl(_) => false,
                }) && cond.as_ref().is_none_or(|e| self.expression(e))
                    && step.as_ref().is_none_or(|e| self.expression(e))
                    && self.statement(body)
            }
            CStmt::Labeled(label, s) => {
                (!matches!(label, Label::Case(e) if !self.expression(e))) && self.statement(s)
            }
            CStmt::Effect(_, s) => self.statement(s),
            CStmt::Sequence(ss) => ss.iter().all(|s| self.statement(s)),
            CStmt::Empty
            | CStmt::Break
            | CStmt::Continue
            | CStmt::Return(None)
            | CStmt::Goto(_) => true,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::decompile::passes::clight_select::solvers::type_projection::*;
    #[test]
    fn fixed_views_are_safe_but_outer_casts_do_not_hide_pointer_stride() {
        let ty = CType::ptr(CType::char_signed());
        let check = Transport {
            name: "p",
            target: &ty,
            model: DataModel::Lp64,
        };
        assert!(check.expression(&CExpr::deref(CExpr::cast(ty.clone(), CExpr::var("p")))));
        assert!(!check.expression(&CExpr::deref(CExpr::var("p"))));
        assert!(!check.expression(&CExpr::cast(
            ty.clone(),
            CExpr::binary(BinaryOp::Add, CExpr::var("p"), CExpr::int(1))
        )));
        assert!(!check.expression(&CExpr::cast(ty.clone(), CExpr::addr_of(CExpr::var("p")))));
    }
    #[test]
    fn assignments_and_call_interfaces_cannot_introduce_implicit_views() {
        let ty = CType::ptr(CType::char_signed());
        let check = Transport {
            name: "p",
            target: &ty,
            model: DataModel::Lp64,
        };
        assert!(check.expression(&CExpr::assign(CExpr::var("p"), CExpr::int(0))));
        assert!(!check.expression(&CExpr::assign(CExpr::var("p"), CExpr::var("q"))));
        assert!(!check.expression(&CExpr::call(CExpr::var("f"), vec![CExpr::var("p")])));
        assert!(check.expression(&CExpr::call(
            CExpr::var("f"),
            vec![CExpr::cast(ty.clone(), CExpr::var("p"))]
        )));
    }

    #[test]
    fn declaration_alignment_is_not_address_alignment_evidence() {
        let ty = CType::ptr(CType::Int(IntSize::Short, Signedness::Unsigned));
        let check = Transport {
            name: "p",
            target: &ty,
            model: DataModel::Lp64,
        };
        assert!(!check.expression(&CExpr::cast(CType::ptr(CType::long()), CExpr::var("p"))));
        assert!(check.expression(&CExpr::cast(CType::ptr(CType::Void), CExpr::var("p"))));
        assert!(check.expression(&CExpr::cast(
            ty.clone(),
            CExpr::cast(CType::ulong(), CExpr::var("p"))
        )));
    }
}
