//! Selection-owned obligations over values, definedness, and memory effects.
//!
//! A check states its declaration dependencies and retains its counterexample.
//! Only refutations with a supported repair in the active structural world may
//! constrain selection. Unsupported/unknown checks are coverage gaps, not proofs.
//! Frame effects are single-access contracts: readable initial bytes and live
//! storage are assumptions, not an initialization or whole-function certificate.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::decompile::passes::c_pass::types::CType;
use crate::decompile::passes::semantic_counterexample as storage;
use crate::x86::types::{ClightStmt, RTLInst, RTLReg};

use super::{integer_semantics, memory_theory, query::FunctionData};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    Equivalent,
    Refuted,
    Unsupported,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Witness {
    Value {
        /// Concrete integer-carrier bits, keyed by the input relation's names.
        inputs: BTreeMap<RTLReg, u64>,
        memory: Option<u64>,
        machine: u64,
        source: u64,
        source_defined: bool,
    },
    Target,
    Storage(storage::Counterexample),
}

#[derive(Debug, Clone)]
pub struct Check {
    pub verdict: Verdict,
    pub registers: BTreeSet<RTLReg>,
    pub witness: Option<Witness>,
}

impl Check {
    pub(crate) fn plain(verdict: Verdict) -> Self {
        Self {
            verdict,
            registers: BTreeSet::new(),
            witness: None,
        }
    }
}

/// Open obligation interface: analysis modules can add checks without adding
/// a dispatch arm or reimplementing declaration/world-guarded refutation.
pub(crate) trait Obligation {
    fn family(&self) -> &'static str;
    fn check(
        &self,
        integers: &integer_semantics::Validator,
        stmt: &ClightStmt,
        declarations: &HashMap<RTLReg, CType>,
        function: &FunctionData,
    ) -> Check;
}

impl<T: Obligation + ?Sized> Obligation for &T {
    fn family(&self) -> &'static str {
        (**self).family()
    }
    fn check(
        &self,
        integers: &integer_semantics::Validator,
        stmt: &ClightStmt,
        declarations: &HashMap<RTLReg, CType>,
        function: &FunctionData,
    ) -> Check {
        (**self).check(integers, stmt, declarations, function)
    }
}

#[derive(Default)]
pub(crate) struct Obligations<'a>(
    pub BTreeMap<crate::x86::types::Node, Vec<Box<dyn Obligation + 'a>>>,
);

impl<'a> Obligations<'a> {
    pub(crate) fn push(&mut self, node: crate::x86::types::Node, obligation: impl Obligation + 'a) {
        self.0.entry(node).or_default().push(Box::new(obligation));
    }
}

pub(crate) struct Integer<'a>(pub &'a RTLInst);
pub(crate) struct IntegerAt<'a>(pub crate::x86::types::Node, pub &'a RTLInst);
pub(crate) struct WriteTarget<'a>(pub &'a memory_theory::WriteContract);
pub(crate) struct WriteValue<'a>(pub &'a RTLInst, pub &'a memory_theory::WriteContract);
pub(crate) struct ReadValue<'a>(pub &'a memory_theory::ReadContract);

impl Obligation for Integer<'_> {
    fn family(&self) -> &'static str {
        "integer"
    }
    fn check(
        &self,
        integers: &integer_semantics::Validator,
        stmt: &ClightStmt,
        declarations: &HashMap<RTLReg, CType>,
        function: &FunctionData,
    ) -> Check {
        integers.check(self.0, stmt, declarations, function.data_model)
    }
}
impl Obligation for IntegerAt<'_> {
    fn family(&self) -> &'static str {
        "integer"
    }
    fn check(
        &self,
        integers: &integer_semantics::Validator,
        stmt: &ClightStmt,
        declarations: &HashMap<RTLReg, CType>,
        function: &FunctionData,
    ) -> Check {
        integers.check_at(self.0, self.1, stmt, declarations, function)
    }
}
impl Obligation for WriteValue<'_> {
    fn family(&self) -> &'static str {
        "store-value"
    }
    fn check(
        &self,
        integers: &integer_semantics::Validator,
        stmt: &ClightStmt,
        declarations: &HashMap<RTLReg, CType>,
        function: &FunctionData,
    ) -> Check {
        integers.check_store(self.0, stmt, self.1, declarations, function)
    }
}
impl Obligation for ReadValue<'_> {
    fn family(&self) -> &'static str {
        "load-value"
    }
    fn check(
        &self,
        integers: &integer_semantics::Validator,
        stmt: &ClightStmt,
        declarations: &HashMap<RTLReg, CType>,
        function: &FunctionData,
    ) -> Check {
        integers.check_load(stmt, self.0, declarations, function)
    }
}
impl Obligation for WriteTarget<'_> {
    fn family(&self) -> &'static str {
        "store-target"
    }
    fn check(
        &self,
        _integers: &integer_semantics::Validator,
        stmt: &ClightStmt,
        _declarations: &HashMap<RTLReg, CType>,
        function: &FunctionData,
    ) -> Check {
        let verdict = match memory_theory::check(stmt, self.0, function) {
            memory_theory::Check::Matches => Verdict::Equivalent,
            memory_theory::Check::Mismatch => Verdict::Refuted,
            memory_theory::Check::Unknown => Verdict::Unsupported,
        };
        Check {
            witness: (verdict == Verdict::Refuted).then_some(Witness::Target),
            ..Check::plain(verdict)
        }
    }
}

pub(crate) struct Validator {
    integers: integer_semantics::Validator,
}
impl Validator {
    pub(crate) fn new() -> Self {
        Self {
            integers: integer_semantics::Validator::new(),
        }
    }
    pub(crate) fn check(
        &self,
        obligation: impl Obligation,
        stmt: &ClightStmt,
        declarations: &HashMap<RTLReg, CType>,
        function: &FunctionData,
    ) -> Check {
        obligation.check(&self.integers, stmt, declarations, function)
    }
}

pub(crate) fn check_layout(
    problem: &storage::Problem,
    representation: &storage::Representation,
) -> Check {
    match storage::validate_complete(problem, representation) {
        storage::Verdict::Validated => Check::plain(Verdict::Equivalent),
        storage::Verdict::Unknown => Check::plain(Verdict::Unknown),
        storage::Verdict::Refuted(witness) => Check {
            witness: Some(Witness::Storage(witness)),
            ..Check::plain(Verdict::Refuted)
        },
    }
}

#[cfg(test)]
#[path = "obligation_tests.rs"]
mod tests;
