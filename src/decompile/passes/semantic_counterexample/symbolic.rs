//! Machine-width symbolic values for representation obligations.
//!
//! The graph consumes the point-keyed reaching-source lattice. Unknown arms
//! and cycles become explicit arbitrary machine words; they are never silently
//! discarded to obtain a convenient bound. This is an overapproximation, so
//! UNSAT establishes a universal property while SAT is a representation-law
//! witness, not a claim that a whole-program execution reaches the call.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use ascent::lattice::set::Set;
use z3::ast::{Ast, Bool, BV};
use z3::{SatResult, Solver};

use crate::decompile::elevator::DecompileDB;
use crate::mreg::Mreg;
use crate::x86::op::{Addressing, Operation};
use crate::x86::types::{Address, LTLInst, Node};

const MAX_TERMS: usize = 128;
pub(super) const SOLVER_RLIMIT: u32 = 20_000;

#[derive(Clone, Debug)]
pub(crate) enum Expr {
    Frame,
    Relative(Arc<Expr>),
    Input(String),
    Apply(Operation, u32, Vec<Arc<Expr>>),
    Choice(String, Vec<Arc<Expr>>),
}

#[derive(Default)]
pub(super) struct SourceIndex {
    operations: BTreeMap<Node, Vec<(Operation, Arc<Vec<Mreg>>, Mreg)>>,
    sources: BTreeMap<(Address, Node, Mreg), Set<Option<Node>>>,
    writes: BTreeMap<(Node, Mreg), BTreeSet<u32>>,
    frame_dependencies: BTreeMap<(Address, Node, Mreg), Set<Node>>,
}

impl SourceIndex {
    pub(super) fn from_db(db: &DecompileDB) -> Self {
        let mut out = Self::default();
        for (node, inst) in db.rel_iter::<(Node, LTLInst)>("ltl_inst") {
            if let LTLInst::Lop(op, args, dst) = inst {
                let row = (op.clone(), args.clone(), *dst);
                let rows = out.operations.entry(*node).or_default();
                if !rows.contains(&row) {
                    rows.push(row);
                }
            }
        }
        for row in db
            .rel_lattice_iter::<(Address, Node, Mreg, Set<Option<Node>>)>("semantic_value_sources")
        {
            out.sources.insert((row.0, row.1, row.2), row.3.clone());
        }
        for &(node, reg, width) in db.rel_iter::<(Node, Mreg, u32)>("machine_register_write_view") {
            out.writes.entry((node, reg)).or_default().insert(width);
        }
        for row in
            db.rel_lattice_iter::<(Address, Node, Mreg, Set<Node>)>("semantic_frame_dependencies")
        {
            out.frame_dependencies
                .insert((row.0, row.1, row.2), row.3.clone());
        }
        out
    }

    pub(super) fn value(&self, function: Address, usage: Node, reg: Mreg) -> Arc<Expr> {
        Builder {
            index: self,
            function,
            cache: BTreeMap::new(),
            visiting: BTreeSet::new(),
            count: 0,
            frame: BTreeMap::new(),
        }
        .value(usage, reg)
    }

    pub(super) fn frame_origins(
        &self,
        function: Address,
        usage: Node,
        reg: Mreg,
    ) -> BTreeSet<Node> {
        let mut origins = BTreeSet::new();
        for source in self
            .sources
            .get(&(function, usage, reg))
            .into_iter()
            .flat_map(|s| &s.0)
        {
            if let Some(source) = source {
                if let Some(roots) = self.frame_dependencies.get(&(function, *source, reg)) {
                    origins.extend(roots.0.iter().copied());
                }
            }
        }
        origins
    }

    pub(super) fn pointer_group(
        &self,
        function: Address,
        call: Node,
        reg: Mreg,
        anchors: &[(Node, Mreg, Option<Mreg>, i64)],
    ) -> Arc<Expr> {
        let frame = anchors
            .iter()
            .map(|&(anchor, destination, index, scale)| {
                let index = index
                    .map(|reg| self.value(function, anchor, reg))
                    .unwrap_or_else(|| Arc::new(Expr::Apply(Operation::Olongconst(0), 64, vec![])));
                let root = Arc::new(Expr::Apply(
                    Operation::Oleal(Addressing::Aindexed2scaled(scale, 0)),
                    64,
                    vec![Arc::new(Expr::Frame), index],
                ));
                ((anchor, destination), root)
            })
            .collect();
        Builder {
            index: self,
            function,
            cache: BTreeMap::new(),
            visiting: BTreeSet::new(),
            count: 0,
            frame,
        }
        .value(call, reg)
    }
}

struct Builder<'a> {
    index: &'a SourceIndex,
    function: Address,
    cache: BTreeMap<(Node, Mreg), Arc<Expr>>,
    visiting: BTreeSet<(Node, Mreg)>,
    count: usize,
    frame: BTreeMap<(Node, Mreg), Arc<Expr>>,
}

impl Builder<'_> {
    fn unknown(&self, node: Node, reg: Mreg) -> Arc<Expr> {
        Arc::new(Expr::Input(format!(
            "word_{:x}_{node:x}_{reg:?}",
            self.function
        )))
    }

    fn value(&mut self, usage: Node, reg: Mreg) -> Arc<Expr> {
        let key = (usage, reg);
        if let Some(value) = self.cache.get(&key) {
            return value.clone();
        }
        if self.count >= MAX_TERMS || !self.visiting.insert(key) {
            return self.unknown(usage, reg);
        }
        self.count += 1;
        let sources = self
            .index
            .sources
            .get(&(self.function, usage, reg))
            .cloned()
            .unwrap_or_default();
        let mut alternatives = Vec::new();
        for source in &sources.0 {
            let Some(def) = source else {
                alternatives.push(self.unknown(usage, reg));
                continue;
            };
            if let Some(value) = self.frame.get(&(*def, reg)) {
                alternatives.push(value.clone());
                continue;
            }
            let operations = self.index.operations.get(def);
            let widths = self.index.writes.get(&(*def, reg));
            if let (Some(operations), Some(widths)) = (operations, widths) {
                if operations.len() == 1 && widths.len() == 1 {
                    let (op, args, dst) = &operations[0];
                    let width = *widths.first().unwrap();
                    if *dst == reg && supported(op, width) {
                        let operands = args.iter().map(|r| self.value(*def, *r)).collect();
                        alternatives.push(Arc::new(Expr::Apply(op.clone(), width, operands)));
                        continue;
                    }
                }
            }
            alternatives.push(self.unknown(*def, reg));
        }
        if alternatives.is_empty() {
            alternatives.push(self.unknown(usage, reg));
        }
        alternatives.dedup_by(|left, right| Arc::ptr_eq(left, right));
        let value = if alternatives.len() == 1 {
            alternatives.pop().unwrap()
        } else {
            Arc::new(Expr::Choice(
                format!("join_{:x}_{usage:x}_{reg:?}", self.function),
                alternatives,
            ))
        };
        self.visiting.remove(&key);
        self.cache.insert(key, value.clone());
        value
    }
}

fn operation_bits(op: &Operation) -> Option<u32> {
    use Operation::*;
    match op {
        Ointconst(_) | Oand | Oor | Oxor | Oadd | Osub | Omul | Oandimm(_) | Oorimm(_)
        | Oxorimm(_) | Oaddimm(_) | Omulimm(_) | Omoduimm(_) | Oshlimm(_) | Oshruimm(_)
        | Ocast8unsigned | Ocast16unsigned | Olea(_) => Some(32),
        Olongconst(_) | Oandl | Oorl | Oxorl | Oaddl | Osubl | Omull | Oandlimm(_) | Oorlimm(_)
        | Oxorlimm(_) | Oaddlimm(_) | Omullimm(_) | Omodluimm(_) | Oshllimm(_) | Oshrluimm(_)
        | Ocast32unsigned | Oleal(_) => Some(64),
        _ => None,
    }
}

fn supported(op: &Operation, width: u32) -> bool {
    (matches!(op, Operation::Omove) && matches!(width, 32 | 64))
        || operation_bits(op) == Some(width)
}

/// Operation semantics return a full architectural word. A 32-bit register
/// write zero-extends; a 32-bit MOV is therefore not the identity of a 64-bit
/// incoming source. Partial writes remain unsupported until their high-bit
/// preservation dependency is represented explicitly.
fn apply(op: &Operation, width: u32, args: &[BV], lemmas: &mut Vec<Bool>) -> Option<BV> {
    use Operation::*;
    let binary = |bits: u32, f: fn(&BV, BV) -> BV| {
        if args.len() != 2 {
            return None;
        }
        let value = f(&args[0].extract(bits - 1, 0), args[1].extract(bits - 1, 0));
        Some(if bits == 64 {
            value
        } else {
            value.zero_ext(64 - bits)
        })
    };
    let immediate = |bits: u32, n: i64, f: fn(&BV, BV) -> BV| {
        if args.len() != 1 {
            return None;
        }
        let value = f(&args[0].extract(bits - 1, 0), BV::from_i64(n, bits));
        Some(if bits == 64 {
            value
        } else {
            value.zero_ext(64 - bits)
        })
    };
    match op {
        Omove if args.len() == 1 && width == 64 => Some(args[0].clone()),
        Omove if args.len() == 1 && width == 32 => Some(args[0].extract(31, 0).zero_ext(32)),
        Ointconst(n) if args.is_empty() => Some(BV::from_i64(*n, 32).zero_ext(32)),
        Olongconst(n) if args.is_empty() => Some(BV::from_i64(*n, 64)),
        Oand => binary(32, BV::bvand),
        Oandl => binary(64, BV::bvand),
        Oor => binary(32, BV::bvor),
        Oorl => binary(64, BV::bvor),
        Oxor => binary(32, BV::bvxor),
        Oxorl => binary(64, BV::bvxor),
        Oadd => binary(32, BV::bvadd),
        Oaddl => binary(64, BV::bvadd),
        Osub => binary(32, BV::bvsub),
        Osubl => binary(64, BV::bvsub),
        Omul => binary(32, BV::bvmul),
        Omull => binary(64, BV::bvmul),
        Oandimm(n) => immediate(32, *n, BV::bvand),
        Oandlimm(n) => immediate(64, *n, BV::bvand),
        Oorimm(n) => immediate(32, *n, BV::bvor),
        Oorlimm(n) => immediate(64, *n, BV::bvor),
        Oxorimm(n) => immediate(32, *n, BV::bvxor),
        Oxorlimm(n) => immediate(64, *n, BV::bvxor),
        Oaddimm(n) => immediate(32, *n, BV::bvadd),
        Oaddlimm(n) => immediate(64, *n, BV::bvadd),
        Omulimm(n) => immediate(32, *n, BV::bvmul),
        Omullimm(n) => immediate(64, *n, BV::bvmul),
        Omoduimm(n) | Omodluimm(n) if *n > 0 && (width == 64 || (*n as u64) < (1_u64 << width)) => {
            let value = immediate(width, *n, BV::bvurem)?;
            // Trusted primitive transfer lemma, not an inferred precondition:
            // unsigned remainder by nonzero N is in [0,N). Giving the solver
            // this algebraic theorem avoids repeatedly bit-blasting division
            // merely to prove an allocation bound. The exact BV remains in
            // the term for all correspondence obligations.
            lemmas.push(value.bvult(BV::from_i64(*n, 64)));
            Some(value)
        }
        Oshlimm(n) if (0..32).contains(n) => immediate(32, *n, BV::bvshl),
        Oshllimm(n) if (0..64).contains(n) => immediate(64, *n, BV::bvshl),
        Oshruimm(n) if (0..32).contains(n) => immediate(32, *n, BV::bvlshr),
        Oshrluimm(n) if (0..64).contains(n) => immediate(64, *n, BV::bvlshr),
        Ocast8unsigned if args.len() == 1 => Some(args[0].extract(7, 0).zero_ext(56)),
        Ocast16unsigned if args.len() == 1 => Some(args[0].extract(15, 0).zero_ext(48)),
        Ocast32unsigned if args.len() == 1 => Some(args[0].extract(31, 0).zero_ext(32)),
        Olea(addressing) | Oleal(addressing) => {
            let (scale, offset) = match addressing {
                Addressing::Aindexed2(o) if args.len() == 2 => (1, *o),
                Addressing::Aindexed2scaled(s, o) if args.len() == 2 => (*s, *o),
                Addressing::Aindexed(o) if args.len() == 1 => (0, *o),
                _ => return None,
            };
            let mut value = args[0].extract(width - 1, 0);
            if args.len() == 2 {
                value = value.bvadd(
                    args[1]
                        .extract(width - 1, 0)
                        .bvmul(BV::from_i64(scale, width)),
                );
            }
            value = value.bvadd(BV::from_i64(offset, width));
            Some(if width == 64 {
                value
            } else {
                value.zero_ext(64 - width)
            })
        }
        _ => None,
    }
}

pub(super) fn encode(expr: &Arc<Expr>, solver: &Solver) -> BV {
    fn lower(
        expr: &Arc<Expr>,
        relative: bool,
        memo: &mut HashMap<(usize, bool), BV>,
        lemmas: &mut Vec<Bool>,
    ) -> BV {
        // Cache DAG nodes by identity, not recursively hashing a shared tree
        // (a chain of x+x would otherwise expand exponentially).
        let key = (Arc::as_ptr(expr) as usize, relative);
        if let Some(value) = memo.get(&key) {
            return value.clone();
        }
        let value = match expr.as_ref() {
            Expr::Frame => {
                if relative {
                    BV::from_u64(0, 64)
                } else {
                    BV::new_const("frame_origin", 64)
                }
            }
            Expr::Relative(inner) => lower(inner, true, memo, lemmas),
            Expr::Input(name) => BV::new_const(name.as_str(), 64),
            Expr::Apply(op, bits, args) => {
                let values: Vec<_> = args
                    .iter()
                    .map(|v| lower(v, relative, memo, lemmas))
                    .collect();
                apply(op, *bits, &values, lemmas).unwrap_or_else(|| {
                    BV::new_const(format!("unsupported_word_{}", memo.len()), 64)
                })
            }
            Expr::Choice(name, alternatives) => {
                let mut values = alternatives
                    .iter()
                    .map(|v| lower(v, relative, memo, lemmas));
                let mut value = values
                    .next()
                    .unwrap_or_else(|| BV::new_const(name.as_str(), 64));
                for (index, other) in values.enumerate() {
                    value = Bool::new_const(format!("{name}_{index}")).ite(&value, &other);
                }
                value
            }
        };
        memo.insert(key, value.clone());
        value
    }
    let mut lemmas = Vec::new();
    let value = lower(expr, false, &mut HashMap::new(), &mut lemmas);
    for lemma in lemmas {
        solver.assert(lemma);
    }
    value
}

/// Check a compositional pointer view without a list of pointer-arithmetic
/// idioms: P(F,x) must equal F + P(0,x) for every frame base and input word.
/// Every intermediate frame-dependent affine address must fit as well; a
/// later subtraction cannot justify first creating an out-of-object pointer.
pub(super) fn affine_view(expression: &Arc<Expr>, room: i64) -> Result<(Arc<Expr>, i64), Bound> {
    fn nodes(expr: &Arc<Expr>, seen: &mut HashMap<usize, bool>, out: &mut Vec<Arc<Expr>>) -> bool {
        let key = Arc::as_ptr(expr) as usize;
        if let Some(contains) = seen.get(&key) {
            return *contains;
        }
        let contains = match expr.as_ref() {
            Expr::Frame => true,
            Expr::Input(_) => false,
            Expr::Relative(_) => false,
            Expr::Apply(_, _, children) | Expr::Choice(_, children) => {
                let mut any = false;
                for child in children {
                    any |= nodes(child, seen, out);
                }
                any
            }
        };
        seen.insert(key, contains);
        if contains {
            out.push(expr.clone());
        }
        contains
    }
    let mut views = Vec::new();
    if !nodes(expression, &mut HashMap::new(), &mut views) {
        return Err(Bound::Unproven);
    }
    let mut maximum = 0;
    for view in views {
        let solver = solver();
        let pointer = encode(&view, &solver);
        let relative = Arc::new(Expr::Relative(view.clone()));
        let delta = encode(&relative, &solver);
        solver.assert(
            pointer
                .eq(BV::new_const("frame_origin", 64).bvadd(delta))
                .not(),
        );
        match solver.check() {
            SatResult::Unsat => {}
            SatResult::Unknown => return Err(Bound::Unknown),
            SatResult::Sat => return Err(Bound::Unproven),
        }
        match maximum_delta(&relative, 1, room) {
            Bound::Proven(bound) => maximum = maximum.max(bound),
            other => return Err(other),
        }
    }
    Ok((Arc::new(Expr::Relative(expression.clone())), maximum))
}

pub(super) fn solver() -> Solver {
    let solver = Solver::new();
    let mut params = z3::Params::new();
    params.set_u32("rlimit", SOLVER_RLIMIT);
    solver.set_params(&params);
    solver
}

#[derive(Clone, Debug)]
pub(crate) struct Index {
    pub expression: Arc<Expr>,
    pub scale: i64,
    /// Proven maximum displacement, not a sampled or guessed index bound.
    pub maximum_delta: i64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Bound {
    Proven(i64),
    Unproven,
    Unknown,
}

pub(super) fn maximum_delta(expression: &Arc<Expr>, scale: i64, room: i64) -> Bound {
    if scale <= 0 || room < 0 || room > super::MAX_OBJECT_BYTES {
        return Bound::Unproven;
    }
    let solver = solver();
    let value = encode(expression, &solver)
        .zero_ext(64)
        .bvmul(BV::from_i64(scale, 128));
    let fits = |limit| {
        solver.push();
        solver.assert(value.bvugt(BV::from_i64(limit, 128)));
        let result = solver.check();
        solver.pop(1);
        result
    };
    match fits(room) {
        SatResult::Sat => return Bound::Unproven,
        SatResult::Unknown => return Bound::Unknown,
        SatResult::Unsat => {}
    }
    let (mut low, mut high) = (0, room);
    while low < high {
        let mid = low + (high - low) / 2;
        match fits(mid) {
            SatResult::Unsat => high = mid,
            SatResult::Sat => low = mid + 1,
            SatResult::Unknown => return Bound::Unknown,
        }
    }
    Bound::Proven(low)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn input() -> Arc<Expr> {
        Arc::new(Expr::Input("input".into()))
    }
    fn op(op: Operation, bits: u32, args: Vec<Arc<Expr>>) -> Arc<Expr> {
        Arc::new(Expr::Apply(op, bits, args))
    }

    #[test]
    fn bounds_follow_machine_masks_shifts_scaling_and_remainder() {
        assert_eq!(
            maximum_delta(&op(Operation::Oandimm(7), 32, vec![input()]), 4, 64),
            Bound::Proven(28)
        );
        assert_eq!(
            maximum_delta(&op(Operation::Oshruimm(30), 32, vec![input()]), 1, 64),
            Bound::Proven(3)
        );
        assert_eq!(
            maximum_delta(&op(Operation::Omoduimm(3), 32, vec![input()]), 1, 64),
            Bound::Proven(2)
        );
    }

    #[test]
    fn unknown_arms_and_wrapping_address_arithmetic_cannot_prove_a_fit() {
        let choice = Arc::new(Expr::Choice(
            "branch".into(),
            vec![op(Operation::Ointconst(1), 32, vec![]), input()],
        ));
        assert_eq!(maximum_delta(&choice, 1, 64), Bound::Unproven);
        assert_eq!(
            maximum_delta(&op(Operation::Olongconst(-1), 64, vec![]), 2, 64),
            Bound::Unproven
        );
        assert!(!matches!(
            maximum_delta(&op(Operation::Omoduimm(0), 32, vec![input()]), 1, 64),
            Bound::Proven(_)
        ));
    }

    #[test]
    fn register_copy_width_is_part_of_the_state_relation() {
        let x = input();
        let difference = op(
            Operation::Osubl,
            64,
            vec![x.clone(), op(Operation::Omove, 32, vec![x])],
        );
        assert_eq!(maximum_delta(&difference, 1, 64), Bound::Unproven);
    }

    #[test]
    fn unsigned_remainder_transfer_lemma_matches_all_small_machine_values() {
        for bits in [8_u32, 16] {
            for divisor in [1_u64, 2, 3, 7, 255] {
                for value in 0..(1_u64 << bits) {
                    assert!(value % divisor < divisor);
                }
            }
        }
    }

    #[test]
    fn affine_views_compose_and_reject_unknown_or_truncated_pointer_arms() {
        let index = op(Operation::Oandimm(1), 32, vec![input()]);
        let base = op(
            Operation::Oleal(Addressing::Aindexed2scaled(2, 0)),
            64,
            vec![Arc::new(Expr::Frame), index],
        );
        let pointer = op(Operation::Oaddlimm(1), 64, vec![base.clone()]);
        let (delta, maximum) = affine_view(&pointer, 64).unwrap();
        assert_eq!(maximum, 3);
        assert_eq!(maximum_delta(&delta, 1, 64), Bound::Proven(3));
        let mixed = Arc::new(Expr::Choice(
            "unknown-arm".into(),
            vec![base.clone(), input()],
        ));
        assert!(affine_view(&mixed, 64).is_err());
        assert!(affine_view(&op(Operation::Omove, 32, vec![base]), 64).is_err());
    }
}
