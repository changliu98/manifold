//! Local translation validation of integer candidates against finalized RTL.
//!
//! The C side is the actual expression converter's output, interpreted with
//! integer promotions, assignment conversions and definedness. Incoming RTL
//! values are related to the chosen C declarations by their integer bits.
//! This checks one operation under that input relation, not whole-program
//! equivalence. Memory, calls, floating point and changed branch topology are
//! unsupported. No result is inferred from a type annotation alone.

use std::collections::{BTreeSet, HashMap};

use either::Either;
use z3::ast::{Ast, Bool, BV};
use z3::{SatResult, Solver};

use crate::abi::DataModel;
use crate::decompile::passes::c_pass::convert::from_relations::{convert_expr, ConversionContext};
use crate::decompile::passes::c_pass::types::{
    BinaryOp, CExpr, CType, IntLiteral, IntLiteralBase, IntLiteralSuffix, IntSize, Signedness,
    UnaryOp,
};
use crate::x86::op::{Comparison, Condition, Operation};
use crate::x86::types::{ClightExpr, ClightStmt, RTLInst, RTLReg};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    Equivalent,
    Refuted,
    Unsupported,
    Unknown,
}

pub struct Check {
    pub verdict: Verdict,
    /// All declarations the result depends on, including the destination.
    pub registers: BTreeSet<RTLReg>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct IntTy {
    bits: u32,
    signed: bool,
}

const INT: IntTy = IntTy {
    bits: 32,
    signed: true,
};

impl IntTy {
    fn from_c(ty: &CType, model: DataModel) -> Option<Self> {
        match ty {
            CType::Int(size, sign) => Some(Self {
                bits: match size {
                    IntSize::Char => 8,
                    IntSize::Short => 16,
                    IntSize::Int => 32,
                    IntSize::Long => model.long_size() as u32 * 8,
                    IntSize::LongLong => 64,
                    // Deliberately outside this pilot's supported domain.
                    IntSize::Int128 => return None,
                },
                signed: *sign == Signedness::Signed,
            }),
            CType::Bool => Some(Self {
                bits: 1,
                signed: false,
            }),
            CType::Qualified(inner, q) if !q.is_volatile => Self::from_c(inner, model),
            _ => None,
        }
    }

    fn promoted(self) -> Self {
        if self.bits < 32 {
            INT
        } else {
            self
        }
    }

    fn common(self, other: Self) -> Self {
        let a = self.promoted();
        let b = other.promoted();
        if a.bits == b.bits {
            Self {
                bits: a.bits,
                signed: a.signed && b.signed,
            }
        } else if a.bits > b.bits {
            a
        } else {
            b
        }
    }
}

#[derive(Clone)]
struct Value {
    bits: BV,
    ty: IntTy,
    defined: Bool,
}

impl Value {
    fn raw(bits: BV, signed: bool) -> Self {
        Self {
            ty: IntTy {
                bits: bits.get_size(),
                signed,
            },
            bits,
            defined: Bool::from_bool(true),
        }
    }

    fn cast(&self, ty: IntTy) -> Self {
        let bits = if ty.bits == 1 {
            self.truth().ite(&BV::from_u64(1, 1), &BV::from_u64(0, 1))
        } else if ty.bits < self.ty.bits {
            self.bits.extract(ty.bits - 1, 0)
        } else if ty.bits > self.ty.bits {
            if self.ty.signed {
                self.bits.sign_ext(ty.bits - self.ty.bits)
            } else {
                self.bits.zero_ext(ty.bits - self.ty.bits)
            }
        } else {
            self.bits.clone()
        };
        Self {
            bits,
            ty,
            defined: self.defined.clone(),
        }
    }

    fn truth(&self) -> Bool {
        self.bits.eq(BV::from_u64(0, self.ty.bits)).not()
    }

    fn boolean(value: Bool, defined: Bool) -> Self {
        Self {
            bits: value.ite(&BV::from_u64(1, 32), &BV::from_u64(0, 32)),
            ty: INT,
            defined,
        }
    }
}

struct Eval<'a> {
    declarations: &'a HashMap<RTLReg, CType>,
    model: DataModel,
    registers: BTreeSet<RTLReg>,
    fuel: usize,
}

impl Eval<'_> {
    fn reg(&mut self, reg: RTLReg) -> Option<Value> {
        let ty = IntTy::from_c(self.declarations.get(&reg)?, self.model)?;
        self.registers.insert(reg);
        Some(Value::raw(
            BV::new_const(format!("integer_input_{reg}"), ty.bits),
            ty.signed,
        ))
    }

    fn machine_reg(&mut self, reg: RTLReg, bits: u32) -> Option<Value> {
        Some(self.reg(reg)?.cast(IntTy {
            bits,
            signed: false,
        }))
    }

    fn literal(&self, lit: &IntLiteral) -> Option<Value> {
        // The printer emits a leading minus as C unary minus, so choose the
        // positive literal's type first. Decimal signed literals must fit;
        // exotic out-of-range literals are unsupported, not guessed.
        if lit.base != IntLiteralBase::Decimal {
            return None;
        }
        let unsigned = matches!(
            lit.suffix,
            IntLiteralSuffix::U | IntLiteralSuffix::UL | IntLiteralSuffix::ULL
        );
        let minimum = match lit.suffix {
            IntLiteralSuffix::None | IntLiteralSuffix::U => 32,
            IntLiteralSuffix::L | IntLiteralSuffix::UL => self.model.long_size() as u32 * 8,
            IntLiteralSuffix::LL | IntLiteralSuffix::ULL => 64,
        };
        let magnitude = lit.value.unsigned_abs();
        let bits = [32, 64].into_iter().find(|&bits| {
            bits >= minimum
                && magnitude
                    <= if unsigned {
                        (1u128 << bits) - 1
                    } else {
                        (1u128 << (bits - 1)) - 1
                    }
        })?;
        let value = BV::from_u64(magnitude as u64, bits);
        Some(Value::raw(
            if lit.value < 0 { value.bvneg() } else { value },
            !unsigned,
        ))
    }

    fn expr(&mut self, expr: &CExpr) -> Option<Value> {
        self.fuel = self.fuel.checked_sub(1)?;
        match expr {
            CExpr::Var(name) => self.reg(name.strip_prefix("var_")?.parse().ok()?),
            CExpr::IntLit(lit) => self.literal(lit),
            CExpr::Paren(inner) => self.expr(inner),
            CExpr::Cast(ty, inner) => Some(self.expr(inner)?.cast(IntTy::from_c(ty, self.model)?)),
            CExpr::Unary(op, inner) => {
                let value = self.expr(inner)?;
                let v = value.cast(value.ty.promoted());
                let mut defined = v.defined.clone();
                let bits = match op {
                    UnaryOp::Plus => v.bits,
                    UnaryOp::BitNot => v.bits.bvnot(),
                    UnaryOp::Not => return Some(Value::boolean(v.truth().not(), defined)),
                    UnaryOp::Neg => {
                        if v.ty.signed {
                            defined = Bool::and(&[defined, v.bits.bvneg_no_overflow()]);
                        }
                        v.bits.bvneg()
                    }
                    _ => return None,
                };
                Some(Value {
                    bits,
                    ty: v.ty,
                    defined,
                })
            }
            CExpr::Binary(op, left, right) => {
                let left = self.expr(left)?;
                let right = self.expr(right)?;
                c_binary(*op, left, right)
            }
            _ => None,
        }
    }
}

fn comparison(op: Comparison, a: &BV, b: &BV, signed: bool) -> Option<Bool> {
    Some(match op {
        Comparison::Ceq => a.eq(b),
        Comparison::Cne => a.eq(b).not(),
        Comparison::Clt => {
            if signed {
                a.bvslt(b)
            } else {
                a.bvult(b)
            }
        }
        Comparison::Cle => {
            if signed {
                a.bvsle(b)
            } else {
                a.bvule(b)
            }
        }
        Comparison::Cgt => {
            if signed {
                a.bvsgt(b)
            } else {
                a.bvugt(b)
            }
        }
        Comparison::Cge => {
            if signed {
                a.bvsge(b)
            } else {
                a.bvuge(b)
            }
        }
        Comparison::Unknown => return None,
    })
}

fn c_binary(op: BinaryOp, left: Value, right: Value) -> Option<Value> {
    use BinaryOp::*;
    let shift = matches!(op, Shl | Shr);
    let ty = if shift {
        left.ty.promoted()
    } else {
        left.ty.common(right.ty)
    };
    let a = left.cast(ty);
    let b = right.cast(if shift { right.ty.promoted() } else { ty });
    let mut defined = Bool::and(&[a.defined.clone(), b.defined.clone()]);
    if let Some(cmp) = match op {
        Eq => Some(Comparison::Ceq),
        Ne => Some(Comparison::Cne),
        Lt => Some(Comparison::Clt),
        Le => Some(Comparison::Cle),
        Gt => Some(Comparison::Cgt),
        Ge => Some(Comparison::Cge),
        _ => None,
    } {
        return Some(Value::boolean(
            comparison(cmp, &a.bits, &b.bits, ty.signed)?,
            defined,
        ));
    }
    let bits = match op {
        Add => {
            if ty.signed {
                defined = Bool::and(&[
                    defined,
                    a.bits.bvadd_no_overflow(&b.bits, true),
                    a.bits.bvadd_no_underflow(&b.bits),
                ]);
            }
            a.bits.bvadd(&b.bits)
        }
        Sub => {
            if ty.signed {
                defined = Bool::and(&[
                    defined,
                    a.bits.bvsub_no_overflow(&b.bits),
                    a.bits.bvsub_no_underflow(&b.bits, true),
                ]);
            }
            a.bits.bvsub(&b.bits)
        }
        Mul => {
            if ty.signed {
                defined = Bool::and(&[
                    defined,
                    a.bits.bvmul_no_overflow(&b.bits, true),
                    a.bits.bvmul_no_underflow(&b.bits),
                ]);
            }
            a.bits.bvmul(&b.bits)
        }
        Div | Mod => {
            defined = Bool::and(&[defined, b.truth()]);
            if ty.signed {
                defined = Bool::and(&[defined, a.bits.bvsdiv_no_overflow(&b.bits)]);
            }
            match (op, ty.signed) {
                (Div, true) => a.bits.bvsdiv(&b.bits),
                (Div, false) => a.bits.bvudiv(&b.bits),
                (_, true) => a.bits.bvsrem(&b.bits),
                (_, false) => a.bits.bvurem(&b.bits),
            }
        }
        BitAnd => a.bits.bvand(&b.bits),
        BitOr => a.bits.bvor(&b.bits),
        BitXor => a.bits.bvxor(&b.bits),
        Shl | Shr => {
            // Check the full promoted count before resizing it for Z3's
            // equal-width shift operands. Negative counts fail the unsigned bound.
            defined = Bool::and(&[
                defined,
                b.bits.bvult(BV::from_u64(ty.bits as u64, b.ty.bits)),
            ]);
            let count = b
                .cast(IntTy {
                    bits: ty.bits,
                    signed: false,
                })
                .bits;
            if op == Shl {
                if ty.signed {
                    let wide = a.bits.zero_ext(ty.bits).bvshl(count.zero_ext(ty.bits));
                    defined = Bool::and(&[
                        defined,
                        a.bits.bvsge(BV::from_u64(0, ty.bits)),
                        wide.bvule(BV::from_u64((1u64 << (ty.bits - 1)) - 1, ty.bits * 2)),
                    ]);
                }
                a.bits.bvshl(&count)
            } else if ty.signed {
                a.bits.bvashr(&count)
            } else {
                a.bits.bvlshr(&count)
            }
        }
        _ => return None,
    };
    Some(Value { bits, ty, defined })
}

fn machine_op(eval: &mut Eval<'_>, op: &Operation, args: &[RTLReg]) -> Option<Value> {
    use Operation::*;
    let (width, binary, immediate) = match op {
        Ointconst(n) => return Some(Value::raw(BV::from_i64(*n, 32), false)),
        Olongconst(n) => return Some(Value::raw(BV::from_i64(*n, 64), false)),
        Oadd => (32, BinaryOp::Add, None),
        Oaddimm(n) => (32, BinaryOp::Add, Some(*n)),
        Oaddl => (64, BinaryOp::Add, None),
        Oaddlimm(n) => (64, BinaryOp::Add, Some(*n)),
        Osub => (32, BinaryOp::Sub, None),
        Osubl => (64, BinaryOp::Sub, None),
        Omul => (32, BinaryOp::Mul, None),
        Omulimm(n) => (32, BinaryOp::Mul, Some(*n)),
        Omull => (64, BinaryOp::Mul, None),
        Omullimm(n) => (64, BinaryOp::Mul, Some(*n)),
        Oand => (32, BinaryOp::BitAnd, None),
        Oandimm(n) => (32, BinaryOp::BitAnd, Some(*n)),
        Oandl => (64, BinaryOp::BitAnd, None),
        Oandlimm(n) => (64, BinaryOp::BitAnd, Some(*n)),
        Oor => (32, BinaryOp::BitOr, None),
        Oorimm(n) => (32, BinaryOp::BitOr, Some(*n)),
        Oorl => (64, BinaryOp::BitOr, None),
        Oorlimm(n) => (64, BinaryOp::BitOr, Some(*n)),
        Oxor => (32, BinaryOp::BitXor, None),
        Oxorimm(n) => (32, BinaryOp::BitXor, Some(*n)),
        Oxorl => (64, BinaryOp::BitXor, None),
        Oxorlimm(n) => (64, BinaryOp::BitXor, Some(*n)),
        Ocast8signed | Ocast8unsigned | Ocast16signed | Ocast16unsigned | Ocast32signed
        | Ocast32unsigned => {
            if args.len() != 1 {
                return None;
            }
            let (bits, signed, out) = match op {
                Ocast8signed => (8, true, 32),
                Ocast8unsigned => (8, false, 32),
                Ocast16signed => (16, true, 32),
                Ocast16unsigned => (16, false, 32),
                Ocast32signed => (32, true, 64),
                _ => (32, false, 64),
            };
            return Some(eval.reg(args[0])?.cast(IntTy { bits, signed }).cast(IntTy {
                bits: out,
                signed: false,
            }));
        }
        Oneg | Onegl | Onot | Onotl => {
            if args.len() != 1 {
                return None;
            }
            let width = if matches!(op, Onegl | Onotl) { 64 } else { 32 };
            let a = eval.machine_reg(args[0], width)?.bits;
            return Some(Value::raw(
                if matches!(op, Oneg | Onegl) {
                    a.bvneg()
                } else {
                    a.bvnot()
                },
                false,
            ));
        }
        // Shift masking and fault behavior belong to the target ISA. Do not
        // invent those semantics from pointer size or the C operator spelling.
        _ => return None,
    };
    if args.len() != if immediate.is_some() { 1 } else { 2 } {
        return None;
    }
    let a = eval.machine_reg(args[0], width)?;
    let b = match immediate {
        Some(n) => Value::raw(BV::from_i64(n, width), false),
        None => eval.machine_reg(args[1], width)?,
    };
    // Unsigned C and RTL have identical modular add/sub/mul/bitwise semantics.
    c_binary(binary, a, b)
}

fn machine_condition(eval: &mut Eval<'_>, cond: &Condition, args: &[RTLReg]) -> Option<Bool> {
    use Condition::*;
    let (width, signed, cmp, immediate) = match cond {
        Ccomp(c) => (32, true, *c, None),
        Ccompu(c) => (32, false, *c, None),
        Ccompl(c) => (64, true, *c, None),
        Ccomplu(c) => (64, false, *c, None),
        Ccompimm(c, n) => (32, true, *c, Some(*n)),
        Ccompuimm(c, n) => (32, false, *c, Some(*n)),
        Ccomplimm(c, n) => (64, true, *c, Some(*n)),
        Ccompluimm(c, n) => (64, false, *c, Some(*n)),
        _ => return None,
    };
    if args.len() != if immediate.is_some() { 1 } else { 2 } {
        return None;
    }
    let a = eval.machine_reg(args[0], width)?.bits;
    let b = match immediate {
        Some(n) => BV::from_i64(n, width),
        None => eval.machine_reg(args[1], width)?.bits,
    };
    comparison(cmp, &a, &b, signed)
}

fn unlabel(stmt: &ClightStmt) -> &ClightStmt {
    match stmt {
        ClightStmt::Slabel(_, inner) => unlabel(inner),
        _ => stmt,
    }
}

fn integer_expression(expr: &ClightExpr, fuel: &mut usize, inputs: &mut BTreeSet<RTLReg>) -> bool {
    let Some(next) = fuel.checked_sub(1) else {
        return false;
    };
    *fuel = next;
    match expr {
        ClightExpr::Etempvar(id, _) => {
            inputs.insert(*id as RTLReg);
            true
        }
        ClightExpr::EconstInt(..) | ClightExpr::EconstLong(..) => true,
        ClightExpr::Ecast(e, _) | ClightExpr::Eunop(_, e, _) => integer_expression(e, fuel, inputs),
        ClightExpr::Ebinop(_, a, b, _) => {
            integer_expression(a, fuel, inputs) && integer_expression(b, fuel, inputs)
        }
        _ => false,
    }
}

fn same_inputs(expr: &ClightExpr, args: &[RTLReg]) -> bool {
    let mut inputs = BTreeSet::new();
    // Inlining or constant propagation can change the input vocabulary. That
    // requires reaching-definition/value equalities this local checker does
    // not have. Do not turn independent symbolic inputs into false refutations
    // or select an alternative with a different dependency footprint.
    integer_expression(expr, &mut 96, &mut inputs) && inputs == args.iter().copied().collect()
}

/// One reusable bounded solver per function. Unsupported and exhausted checks
/// never prohibit a candidate. The rlimit is deterministic; no timing-based
/// acceptance decision is used.
pub struct Validator {
    solver: Solver,
    checks: std::cell::Cell<usize>,
}

impl Validator {
    pub fn new() -> Self {
        let solver = Solver::new();
        let mut params = z3::Params::new();
        params.set_u32("rlimit", 20_000);
        solver.set_params(&params);
        Self {
            solver,
            checks: std::cell::Cell::new(0),
        }
    }

    pub fn check(
        &self,
        inst: &RTLInst,
        stmt: &ClightStmt,
        declarations: &HashMap<RTLReg, CType>,
        model: DataModel,
    ) -> Check {
        if self.checks.get() >= 256 {
            return Check {
                verdict: Verdict::Unknown,
                registers: BTreeSet::new(),
            };
        }
        self.checks.set(self.checks.get() + 1);
        let mut eval = Eval {
            declarations,
            model,
            registers: BTreeSet::new(),
            fuel: 96,
        };
        let mut ctx = ConversionContext::new(HashMap::new(), model);
        let obligation = (|| match (inst, unlabel(stmt)) {
            (RTLInst::Iop(op, args, dst), ClightStmt::Sset(id, rhs)) if *dst == *id as RTLReg => {
                if !same_inputs(rhs, args) {
                    return None;
                }
                let machine = machine_op(&mut eval, op, args)?;
                let destination = eval.reg(*dst)?.ty;
                // RTL specifies the result word, not the extra bits of a
                // wider C carrier. Proving a widened assignment requires
                // an architectural extension fact; equality of only the
                // low bits would incorrectly certify a widened add.
                if destination.bits > machine.ty.bits {
                    return None;
                }
                let c = eval
                    .expr(&convert_expr(rhs, &mut ctx))?
                    .cast(destination)
                    .cast(machine.ty);
                Some(Bool::and(&[c.defined, c.bits.eq(&machine.bits)]))
            }
            (
                RTLInst::Icond(cond, args, Either::Right(yes), Either::Right(no)),
                ClightStmt::Sifthenelse(expr, a, b),
            ) => {
                if yes == no {
                    return None;
                }
                if !same_inputs(expr, args) {
                    return None;
                }
                let (ClightStmt::Sgoto(a), ClightStmt::Sgoto(b)) = (unlabel(a), unlabel(b)) else {
                    return None;
                };
                let machine = machine_condition(&mut eval, cond, args)?;
                let expected = if *a as u64 == *yes && *b as u64 == *no {
                    machine
                } else if *a as u64 == *no && *b as u64 == *yes {
                    machine.not()
                } else {
                    return None;
                };
                let c = eval.expr(&convert_expr(expr, &mut ctx))?;
                Some(Bool::and(&[c.defined.clone(), c.truth().eq(expected)]))
            }
            _ => None,
        })();
        let verdict = match obligation {
            None => Verdict::Unsupported,
            Some(ok) => {
                let bad = ok.not().simplify();
                match bad.as_bool() {
                    Some(false) => Verdict::Equivalent,
                    Some(true) => Verdict::Refuted,
                    None => {
                        self.solver.push();
                        self.solver.assert(&bad);
                        let verdict = match self.solver.check() {
                            SatResult::Unsat => Verdict::Equivalent,
                            SatResult::Sat => Verdict::Refuted,
                            SatResult::Unknown => Verdict::Unknown,
                        };
                        self.solver.pop(1);
                        verdict
                    }
                }
            }
        };
        Check {
            verdict,
            registers: eval.registers,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::x86::types::{
        ClightAttr, ClightBinaryOp, ClightIntSize, ClightSignedness, ClightType,
    };
    use std::sync::Arc;

    fn long(signed: bool) -> ClightType {
        ClightType::Tlong(
            if signed {
                ClightSignedness::Signed
            } else {
                ClightSignedness::Unsigned
            },
            ClightAttr::default(),
        )
    }
    fn int(signed: bool) -> ClightType {
        ClightType::Tint(
            ClightIntSize::I32,
            if signed {
                ClightSignedness::Signed
            } else {
                ClightSignedness::Unsigned
            },
            ClightAttr::default(),
        )
    }
    fn bin(op: ClightBinaryOp, ty: ClightType) -> ClightExpr {
        ClightExpr::Ebinop(
            op,
            Box::new(ClightExpr::Etempvar(1, ty.clone())),
            Box::new(ClightExpr::Etempvar(2, ty.clone())),
            ty,
        )
    }
    fn decls() -> HashMap<RTLReg, CType> {
        [(1, CType::long()), (2, CType::long()), (3, CType::long())]
            .into_iter()
            .collect()
    }
    fn operation(op: Operation) -> RTLInst {
        RTLInst::Iop(op, Arc::new(vec![1, 2]), 3)
    }

    #[test]
    fn emitted_literals_keep_integer_width_signedness_and_minimum_values() {
        let v = Validator::new();
        let declarations = decls();
        let machine = RTLInst::Iop(Operation::Olongconst(u32::MAX as i64), Arc::new(vec![]), 3);
        let value = ClightStmt::Sset(3, ClightExpr::EconstInt(-1, int(false)));
        assert_eq!(
            v.check(&machine, &value, &declarations, DataModel::Lp64)
                .verdict,
            Verdict::Equivalent
        );
        let machine = RTLInst::Iop(Operation::Olongconst(i64::MIN), Arc::new(vec![]), 3);
        let value = ClightStmt::Sset(3, ClightExpr::EconstLong(i64::MIN, long(true)));
        assert_eq!(
            v.check(&machine, &value, &declarations, DataModel::Lp64)
                .verdict,
            Verdict::Equivalent
        );
        for (model, suffix) in [(DataModel::Lp64, "1L"), (DataModel::Llp64, "1LL")] {
            let mut ctx = ConversionContext::new(HashMap::new(), model);
            let expr = convert_expr(&ClightExpr::EconstLong(1, long(true)), &mut ctx);
            let mut printer =
                crate::decompile::passes::c_pass::print::Printer::with_default_config();
            printer.print_expr(&expr);
            assert_eq!(printer.into_string(), suffix);
        }
    }

    #[test]
    fn modular_arithmetic_is_distinct_from_signed_c_overflow() {
        let v = Validator::new();
        let machine = operation(Operation::Oaddl);
        assert_eq!(
            v.check(
                &machine,
                &ClightStmt::Sset(3, bin(ClightBinaryOp::Oadd, long(false))),
                &decls(),
                DataModel::Lp64
            )
            .verdict,
            Verdict::Equivalent
        );
        assert_eq!(
            v.check(
                &machine,
                &ClightStmt::Sset(3, bin(ClightBinaryOp::Oadd, long(true))),
                &decls(),
                DataModel::Lp64
            )
            .verdict,
            Verdict::Refuted
        );
    }

    #[test]
    fn same_types_do_not_prove_the_same_computation() {
        let v = Validator::new();
        assert_eq!(
            v.check(
                &operation(Operation::Oaddl),
                &ClightStmt::Sset(3, bin(ClightBinaryOp::Oxor, long(false))),
                &decls(),
                DataModel::Lp64
            )
            .verdict,
            Verdict::Refuted
        );
    }

    #[test]
    fn narrowing_is_checked_at_both_operation_and_assignment() {
        let v = Validator::new();
        let narrow = ClightStmt::Sset(3, bin(ClightBinaryOp::Oadd, int(false)));
        let mut word_declarations = decls();
        word_declarations.insert(3, CType::uint());
        assert_eq!(
            v.check(
                &operation(Operation::Oadd),
                &narrow,
                &word_declarations,
                DataModel::Lp64
            )
            .verdict,
            Verdict::Equivalent
        );
        assert_eq!(
            v.check(
                &operation(Operation::Oadd),
                &narrow,
                &decls(),
                DataModel::Lp64
            )
            .verdict,
            Verdict::Unsupported
        );
        assert_eq!(
            v.check(
                &operation(Operation::Oaddl),
                &narrow,
                &decls(),
                DataModel::Lp64
            )
            .verdict,
            Verdict::Refuted
        );
        let mut declarations = decls();
        declarations.insert(3, CType::int());
        let wide = ClightStmt::Sset(3, bin(ClightBinaryOp::Oadd, long(false)));
        assert_eq!(
            v.check(
                &operation(Operation::Oaddl),
                &wide,
                &declarations,
                DataModel::Lp64
            )
            .verdict,
            Verdict::Refuted
        );
    }

    #[test]
    fn mixed_width_branch_uses_actual_c_conversions_and_target_identity() {
        let v = Validator::new();
        let mut declarations = decls();
        declarations.insert(2, CType::Int(IntSize::Int, Signedness::Unsigned));
        let expr = ClightExpr::Ebinop(
            ClightBinaryOp::Olt,
            Box::new(ClightExpr::Etempvar(1, long(true))),
            Box::new(ClightExpr::Etempvar(2, int(false))),
            int(true),
        );
        let machine = RTLInst::Icond(
            Condition::Ccompl(Comparison::Clt),
            Arc::new(vec![1, 2]),
            Either::Right(11),
            Either::Right(12),
        );
        let stmt = ClightStmt::Sifthenelse(
            expr,
            Box::new(ClightStmt::Sgoto(11)),
            Box::new(ClightStmt::Sgoto(12)),
        );
        assert_eq!(
            v.check(&machine, &stmt, &declarations, DataModel::Lp64)
                .verdict,
            Verdict::Equivalent
        );
        let wrong = ClightStmt::Sifthenelse(
            bin(ClightBinaryOp::Olt, long(false)),
            Box::new(ClightStmt::Sgoto(11)),
            Box::new(ClightStmt::Sgoto(12)),
        );
        assert_eq!(
            v.check(&machine, &wrong, &declarations, DataModel::Lp64)
                .verdict,
            Verdict::Refuted
        );
        let inverted = ClightStmt::Sifthenelse(
            bin(ClightBinaryOp::Oge, long(true)),
            Box::new(ClightStmt::Sgoto(12)),
            Box::new(ClightStmt::Sgoto(11)),
        );
        assert_eq!(
            v.check(&machine, &inverted, &declarations, DataModel::Lp64)
                .verdict,
            Verdict::Equivalent
        );
    }

    #[test]
    fn checks_use_the_target_long_width() {
        let v = Validator::new();
        let declarations = [
            (1, CType::Int(IntSize::LongLong, Signedness::Signed)),
            (2, CType::Int(IntSize::LongLong, Signedness::Signed)),
            (3, CType::Int(IntSize::LongLong, Signedness::Signed)),
        ]
        .into_iter()
        .collect();
        let stmt = ClightStmt::Sset(3, bin(ClightBinaryOp::Oadd, long(false)));
        assert_eq!(
            v.check(
                &operation(Operation::Oaddl),
                &stmt,
                &declarations,
                DataModel::Llp64
            )
            .verdict,
            Verdict::Equivalent
        );
    }

    #[test]
    fn memory_and_unknown_declarations_are_not_claimed_as_validated() {
        let v = Validator::new();
        // Constant folding may have proved facts about the RTL inputs. Those
        // facts are outside this checker, so a changed input vocabulary is
        // unsupported rather than a counterexample over unrelated symbols.
        assert_eq!(
            v.check(
                &operation(Operation::Oaddl),
                &ClightStmt::Sset(3, ClightExpr::EconstLong(0, long(true))),
                &decls(),
                DataModel::Lp64
            )
            .verdict,
            Verdict::Unsupported
        );
        let stmt = ClightStmt::Sset(
            3,
            ClightExpr::Ederef(Box::new(ClightExpr::Etempvar(1, long(true))), long(true)),
        );
        assert_eq!(
            v.check(
                &operation(Operation::Oaddl),
                &stmt,
                &decls(),
                DataModel::Lp64
            )
            .verdict,
            Verdict::Unsupported
        );
        assert_eq!(
            v.check(
                &operation(Operation::Oaddl),
                &ClightStmt::Sset(3, bin(ClightBinaryOp::Oadd, long(false))),
                &HashMap::new(),
                DataModel::Lp64
            )
            .verdict,
            Verdict::Unsupported
        );
    }

    #[test]
    fn c_shift_definedness_checks_untruncated_count_and_signed_overflow() {
        let left = Value::raw(BV::from_u64(1, 32), true);
        for count in [31, 32, 1u64 << 32, u64::MAX] {
            let result = c_binary(
                BinaryOp::Shl,
                left.clone(),
                Value::raw(BV::from_u64(count, 64), false),
            )
            .unwrap();
            assert_eq!(result.defined.simplify().as_bool(), Some(false));
        }
    }
}
