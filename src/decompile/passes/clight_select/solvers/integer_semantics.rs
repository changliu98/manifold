//! Local translation validation of integer candidates against finalized RTL.
//!
//! The C side is the actual expression converter's output, interpreted with
//! integer promotions, assignment conversions and definedness. Incoming RTL
//! values are related to the chosen C declarations by their integer bits.
//! This checks one operation or an exact frame access under that input
//! relation, not whole-program equivalence. Calls, floating point, arbitrary
//! memory and changed branch topology are unsupported. A frame read assumes
//! live, readable storage; no reaching writer or initialization is invented.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use either::Either;
use z3::ast::{Ast, Bool, BV};
use z3::{SatResult, Solver};

use crate::abi::DataModel;
use crate::decompile::passes::c_pass::convert::from_relations::{
    convert_clight_type, convert_expr, ConversionContext,
};
use crate::decompile::passes::c_pass::types::{
    BinaryOp, CExpr, CType, IntLiteral, IntLiteralBase, IntLiteralSuffix, IntSize, Signedness,
    UnaryOp,
};
use crate::decompile::passes::clight_select::solvers::obligations::Witness;
pub use crate::decompile::passes::clight_select::solvers::obligations::{Check, Verdict};
use crate::decompile::passes::clight_select::{query::FunctionData, solvers::memory_theory};
use crate::x86::op::{Comparison, Condition, Operation};
use crate::x86::types::{ClightExpr, ClightStmt, MemoryChunk, RTLInst, RTLReg};

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
    fn carrier(ty: &CType, model: DataModel) -> Option<Self> {
        match ty {
            CType::Pointer(pointee, _) if !matches!(pointee.as_ref(), CType::Function(..)) => {
                Some(Self {
                    bits: (model.pointer_size() * 8) as u32,
                    signed: false,
                })
            }
            _ => Self::from_c(ty, model),
        }
    }
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
    /// The exact converted load expression and its shared machine/C bytes.
    /// Other dereferences, calls, or memory expressions remain unsupported.
    memory: Option<(CExpr, Value)>,
    word_inputs: BTreeSet<RTLReg>,
    // Ordered: dropping these Z3 terms frees AST ids, and Z3 recycles freed ids.
    // Hash order here would make later term ids, and the optimizer's choice
    // among equal-cost models, depend on the per-process hash seed.
    machine_overrides: BTreeMap<RTLReg, Value>,
}

impl Eval<'_> {
    /// Native logical registers are independently modeled at the maximum
    /// width supported by this checker. A C declaration is a projection of
    /// that state; it must not erase native high bits before the query exists.
    fn input_bits(reg: RTLReg) -> BV {
        BV::new_const(format!("integer_input_{reg}"), 64)
    }

    fn c_input(&mut self, reg: RTLReg, ty: IntTy) -> Value {
        self.registers.insert(reg);
        Value::raw(Self::input_bits(reg), false).cast(ty)
    }

    fn reg(&mut self, reg: RTLReg) -> Option<Value> {
        let ty = IntTy::from_c(self.declarations.get(&reg)?, self.model)?;
        Some(self.c_input(reg, ty))
    }

    fn carrier(&mut self, reg: RTLReg) -> Option<Value> {
        let ty = IntTy::carrier(self.declarations.get(&reg)?, self.model)?;
        Some(self.c_input(reg, ty))
    }

    fn machine_reg(&mut self, reg: RTLReg, bits: u32) -> Option<Value> {
        if self
            .machine_overrides
            .get(&reg)
            .is_some_and(|value| value.ty.bits < bits)
        {
            return None;
        }
        let value = self.machine_input(reg)?;
        // A producer's partial result must not invent untouched high bits.
        if value.ty.bits < bits {
            return None;
        }
        Some(value.cast(IntTy {
            bits,
            signed: false,
        }))
    }

    fn machine_input(&mut self, reg: RTLReg) -> Option<Value> {
        if let Some(value) = self.machine_overrides.get(&reg) {
            return Some(value.clone());
        }
        // Native state does not depend on whether a C declaration exists or
        // which scalar class the candidate assigns to it.
        self.registers.insert(reg);
        let value = Value::raw(Self::input_bits(reg), false);
        if self.word_inputs.contains(&reg) {
            Some(
                value
                    .cast(IntTy {
                        bits: 32,
                        signed: false,
                    })
                    .cast(IntTy {
                        bits: 64,
                        signed: false,
                    }),
            )
        } else {
            Some(value)
        }
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
        if let Some((load, value)) = &self.memory {
            if load == expr {
                return Some(value.clone());
            }
        }
        match expr {
            CExpr::Var(name) => self.reg(name.strip_prefix("var_")?.parse().ok()?),
            CExpr::IntLit(lit) => self.literal(lit),
            CExpr::Paren(inner) => self.expr(inner),
            CExpr::Cast(ty, inner) => {
                let target = IntTy::from_c(ty, self.model)?;
                // Only an explicit integer cast consumes the target ABI's
                // data-pointer bits. Bare pointer arithmetic remains outside
                // the integer evaluator; its stride is not integer addition.
                let value = if let CExpr::Var(name) = inner.as_ref() {
                    let reg = name.strip_prefix("var_")?.parse().ok()?;
                    if matches!(self.declarations.get(&reg), Some(CType::Pointer(..))) {
                        self.carrier(reg)?
                    } else {
                        self.expr(inner)?
                    }
                } else {
                    self.expr(inner)?
                };
                Some(value.cast(target))
            }
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
            CExpr::Ternary(condition, yes, no) => {
                let c = self.expr(condition)?;
                let a = self.expr(yes)?;
                let b = self.expr(no)?;
                let ty = a.ty.common(b.ty);
                let a = a.cast(ty);
                let b = b.cast(ty);
                Some(Value {
                    bits: c.truth().ite(&a.bits, &b.bits),
                    ty,
                    defined: Bool::and(&[c.defined.clone(), c.truth().ite(&a.defined, &b.defined)]),
                })
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
    if let Operation::Oflagselect(spec) = op {
        if args.len() != 3 || !spec.valid() {
            return None;
        }
        let old = eval.machine_reg(args[0], spec.result_bits)?;
        let taken = eval.machine_reg(args[1], spec.result_bits)?;
        let memory = eval.machine_reg(args[2], (spec.width * 8) as u32)?;
        let predicate = crate::decompile::effects::flags::machine_predicate(*spec, &memory.bits)?;
        let selected = predicate.ite(&taken.bits, &old.bits);
        return Some(Value::raw(
            if spec.result_bits == 32 {
                selected.zero_ext(32)
            } else {
                selected
            },
            false,
        ));
    }
    use Operation::*;
    let (width, binary, immediate) = match op {
        Olea(addressing) | Oleal(addressing) => {
            let width = if matches!(op, Olea(_)) { 32 } else { 64 };
            let (scale, offset) = match addressing {
                crate::x86::op::Addressing::Aindexed(offset) if args.len() == 1 => (0, *offset),
                crate::x86::op::Addressing::Aindexed2(offset) if args.len() == 2 => (1, *offset),
                crate::x86::op::Addressing::Aindexed2scaled(scale, offset) if args.len() == 2 => {
                    (*scale, *offset)
                }
                _ => return None, // Stack/global addresses need an object relation.
            };
            let mut value = eval.machine_reg(args[0], width)?.bits;
            if args.len() == 2 {
                value = value.bvadd(
                    eval.machine_reg(args[1], width)?
                        .bits
                        .bvmul(BV::from_i64(scale, width)),
                );
            }
            return Some(Value::raw(value.bvadd(BV::from_i64(offset, width)), false));
        }
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
            return Some(
                eval.machine_input(args[0])?
                    .cast(IntTy { bits, signed })
                    .cast(IntTy {
                        bits: out,
                        signed: false,
                    }),
            );
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
    machine_condition_at_width(eval, cond, args, None)
}

fn machine_condition_at_width(
    eval: &mut Eval<'_>,
    cond: &Condition,
    args: &[RTLReg],
    physical_width: Option<u32>,
) -> Option<Bool> {
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
    let width = physical_width.unwrap_or(width);
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
        (ClightStmt::Slabel(_, inner) | ClightStmt::Seffect(_, inner)) => unlabel(inner),
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
        ClightExpr::Econdition(c, a, b, _) => {
            integer_expression(c, fuel, inputs)
                && integer_expression(a, fuel, inputs)
                && integer_expression(b, fuel, inputs)
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

fn align_machine_inputs(
    eval: &mut Eval<'_>,
    expr: &ClightExpr,
    args: &[RTLReg],
    context: Option<(&FunctionData, crate::x86::types::Node)>,
) -> Option<()> {
    let mut actual = BTreeSet::new();
    if !integer_expression(expr, &mut eval.fuel.clone(), &mut actual) {
        return None;
    }
    if actual == args.iter().copied().collect() {
        return Some(());
    }
    let (function, node) = context?;
    let mut needed = BTreeSet::new();
    let mut bindings = BTreeMap::new();
    for &arg in args {
        if actual.contains(&arg) {
            needed.insert(arg);
            continue;
        }
        let producer = function.value_producers.get(&(node, arg))?;
        needed.extend(producer.arguments.iter().copied());
        // Each producer is interpreted from the common state at the final
        // use. Do not recursively borrow a proof at an intermediate point.
        let mut value = if producer.operation == Operation::Omove && producer.arguments.len() == 1 {
            producer_copy_value(eval, producer, function)?
        } else {
            machine_op(eval, &producer.operation, &producer.arguments)?
        };
        match producer.write_bits {
            Some(32) if function.ptr64 => {
                value = value
                    .cast(IntTy {
                        bits: 32,
                        signed: false,
                    })
                    .cast(IntTy {
                        bits: 64,
                        signed: false,
                    })
            }
            Some(bits) if bits < value.ty.bits => {
                value = value.cast(IntTy {
                    bits,
                    signed: false,
                })
            }
            _ => {}
        }
        bindings.insert(arg, value);
    }
    if needed != actual {
        return None;
    }
    eval.machine_overrides = bindings;
    Some(())
}

/// Compare in the producer's input vocabulary only when RTL has established
/// its value equation at THIS effect. We do not substitute at an arbitrary
/// later use or recursively expand operands without another availability proof.
fn store_source_value(
    eval: &mut Eval<'_>,
    source: RTLReg,
    bits: u32,
    rhs: &ClightExpr,
    usage: crate::x86::types::Node,
    function: &FunctionData,
) -> Option<Value> {
    if same_inputs(rhs, &[source]) {
        return eval.machine_reg(source, bits);
    }
    let producer = function.value_producers.get(&(usage, source))?;
    if !same_inputs(rhs, &producer.arguments) {
        return None;
    }
    let mut value = if producer.operation == Operation::Omove && producer.arguments.len() == 1 {
        producer_copy_value(eval, producer, function)?
    } else {
        machine_op(eval, &producer.operation, &producer.arguments)?
    };
    match producer.write_bits {
        // An x86-64 32-bit destination defines the full register by zero
        // extension. This comes from the decoded destination view, never the
        // C carrier or the sign of a literal. Partial 8/16-bit writes cannot
        // establish their untouched high bits.
        Some(32) if function.ptr64 => {
            value = value
                .cast(IntTy {
                    bits: 32,
                    signed: false,
                })
                .cast(IntTy {
                    bits: 64,
                    signed: false,
                });
        }
        Some(written) if bits > written => return None,
        _ => {}
    }
    (value.ty.bits >= bits).then_some(value)
}

/// One reusable bounded solver per function. Unsupported and exhausted checks
/// never prohibit a candidate. The rlimit is deterministic; no timing-based
/// acceptance decision is used.
pub struct Validator {
    solver: Solver,
    checks: std::cell::Cell<[usize; 9]>,
}

#[derive(Clone, Copy)]
enum Domain {
    Integer,
    FrameStore,
    FrameLoad,
    WordOperation,
    FlagEffect,
    LoadTransport,
    CopyTransport,
    SwitchInput,
    ResultRepresentation,
}

/// Decoder-owned result semantics. No storage target is inferred from the
/// proposed declaration, and proving this transfer does not prove aliasing.
#[derive(Clone, Debug)]
pub(crate) struct LoadValue {
    pub node: crate::x86::types::Node,
    pub chunk: MemoryChunk,
    pub destination: RTLReg,
    pub write_bits: Option<u32>,
    pub signed_word_load: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct CopyValue {
    pub node: crate::x86::types::Node,
    pub source: RTLReg,
    pub destination: RTLReg,
    pub bits: u32,
    pub storage: bool,
    /// Exact memory-input width/extension for a promoted stack load.
    pub memory_input: Option<(u32, bool)>,
}

struct Effect {
    machine: BV,
    source: BV,
    defined: Bool,
}

fn native_copy_value(eval: &mut Eval<'_>, copy: &CopyValue, ptr64: bool) -> Option<Value> {
    let (input_bits, signed) = copy.memory_input.unwrap_or((copy.bits, false));
    let observed = input_bits.min(copy.bits);
    let value = eval
        .machine_reg(copy.source, observed)?
        .cast(IntTy {
            bits: observed,
            signed,
        })
        .cast(IntTy {
            bits: copy.bits,
            signed: false,
        });
    Some(if !copy.storage && copy.bits == 32 && ptr64 {
        value.cast(IntTy {
            bits: 64,
            signed: false,
        })
    } else {
        value
    })
}

fn producer_copy_value(
    eval: &mut Eval<'_>,
    producer: &crate::decompile::passes::clight_select::solvers::producer_values::Producer,
    function: &FunctionData,
) -> Option<Value> {
    if let Some(copy) = crate::decompile::passes::clight_select::solvers::transfers::COPIES
        .get(&function.analysis_facts)
        .and_then(|copies| copies.get(&producer.definition))
    {
        // Omove may encode a byte load/store, not a register-width identity.
        // Its actual access/extension belongs to the decoder-owned transfer.
        native_copy_value(eval, copy, function.ptr64)
    } else {
        eval.machine_input(producer.arguments[0])
    }
}

impl Validator {
    pub fn new() -> Self {
        let solver = Solver::new();
        let mut params = z3::Params::new();
        params.set_u32("rlimit", 20_000);
        solver.set_params(&params);
        Self {
            solver,
            checks: std::cell::Cell::new([0; 9]),
        }
    }

    pub fn check(
        &self,
        inst: &RTLInst,
        stmt: &ClightStmt,
        declarations: &HashMap<RTLReg, CType>,
        model: DataModel,
    ) -> Check {
        self.check_instruction(inst, stmt, declarations, model, None)
    }

    pub(crate) fn check_at(
        &self,
        node: crate::x86::types::Node,
        inst: &RTLInst,
        stmt: &ClightStmt,
        declarations: &HashMap<RTLReg, CType>,
        function: &FunctionData,
    ) -> Check {
        self.check_instruction(
            inst,
            stmt,
            declarations,
            function.data_model,
            Some((function, node)),
        )
    }

    fn check_instruction(
        &self,
        inst: &RTLInst,
        stmt: &ClightStmt,
        declarations: &HashMap<RTLReg, CType>,
        model: DataModel,
        context: Option<(&FunctionData, crate::x86::types::Node)>,
    ) -> Check {
        let word_inputs = context
            .and_then(|(f, n)| f.word_inputs.get(&n))
            .cloned()
            .unwrap_or_default();
        let domain = if matches!(inst, RTLInst::Iop(Operation::Oflagselect(_), _, _)) {
            Domain::FlagEffect
        } else if word_inputs.is_empty() {
            Domain::Integer
        } else {
            Domain::WordOperation
        };
        let checked = self.check_effect(domain, declarations, model, |eval| {
            eval.word_inputs = word_inputs;
            let mut ctx = ConversionContext::new(HashMap::new(), model);
            match (inst, unlabel(stmt)) {
                (RTLInst::Iop(op, args, dst), ClightStmt::Sset(id, rhs))
                    if *dst == *id as RTLReg =>
                {
                    let mut direct_inputs = BTreeSet::new();
                    let direct_flag_view = matches!(op, Operation::Oflagselect(_))
                        && integer_expression(rhs, &mut eval.fuel.clone(), &mut direct_inputs)
                        && direct_inputs.iter().all(|reg| args.contains(reg));
                    // A flag predicate can be constant (e.g. TEST always
                    // clears OF). Extra machine inputs remain unconstrained,
                    // so their omission is proved, not assumed, by the query.
                    if !direct_flag_view {
                        align_machine_inputs(eval, rhs, args, context)?;
                    }
                    let machine = machine_op(eval, op, args)?;
                    let destination = eval.reg(*dst)?.ty;
                    // A widened carrier needs architectural extension evidence,
                    // not merely equality of the low machine-result bits.
                    if destination.bits > machine.ty.bits {
                        return None;
                    }
                    let mut c = eval.expr(&convert_expr(rhs, &mut ctx))?.cast(destination);
                    if matches!(op,Operation::Oflagselect(spec) if spec.result_bits==32)
                        && destination.bits == 32
                    {
                        c = c.cast(IntTy {
                            bits: 32,
                            signed: false,
                        });
                    }
                    let c = c.cast(machine.ty);
                    Some(Effect {
                        machine: machine.bits,
                        source: c.bits,
                        defined: c.defined,
                    })
                }
                (
                    RTLInst::Icond(cond, args, Either::Right(yes), Either::Right(no)),
                    ClightStmt::Sifthenelse(expr, a, b),
                ) => {
                    if yes == no {
                        return None;
                    }
                    align_machine_inputs(eval, expr, args, context)?;
                    let (ClightStmt::Sgoto(a), ClightStmt::Sgoto(b)) = (unlabel(a), unlabel(b))
                    else {
                        return None;
                    };
                    let width = context.and_then(|(f, node)| {
                        crate::decompile::passes::clight_select::solvers::observations::comparison_width(&f.analysis_facts, node)
                    });
                    let machine = machine_condition_at_width(eval, cond, args, width)?;
                    let same_target = |a, b| {
                        a == b
                            || context.is_some_and(|(f, _)| {
                                crate::decompile::passes::clight_select::solvers::observations::same_target(&f.analysis_facts, a, b)
                            })
                    };
                    let expected = if same_target(*a as u64, *yes) && same_target(*b as u64, *no) {
                        machine
                    } else if same_target(*a as u64, *no) && same_target(*b as u64, *yes) {
                        machine.not()
                    } else {
                        return None;
                    };
                    let c = eval.expr(&convert_expr(expr, &mut ctx))?;
                    let bit = |b: Bool| b.ite(&BV::from_u64(1, 1), &BV::from_u64(0, 1));
                    Some(Effect {
                        machine: bit(expected),
                        source: bit(c.truth()),
                        defined: c.defined,
                    })
                }
                _ => None,
            }
        });
        // The result-range test is a necessary condition of its own. An
        // equivalence query that was undecided or never ran (its family's
        // bound was spent) proves nothing either way, so it must not waive a
        // cast that cannot hold the native word.
        if matches!(checked.verdict, Verdict::Unsupported | Verdict::Unknown) {
            self.refute_result_cast(inst, stmt, declarations, model, context)
                .unwrap_or(checked)
        } else {
            checked
        }
    }

    /// Necessary result-range check, independent of interpreting pointer
    /// arithmetic or proving its lifetime. Only a refutation is published;
    /// fitting the cast range is never an equivalence/definedness certificate.
    fn refute_result_cast(
        &self,
        inst: &RTLInst,
        stmt: &ClightStmt,
        declarations: &HashMap<RTLReg, CType>,
        model: DataModel,
        context: Option<(&FunctionData, crate::x86::types::Node)>,
    ) -> Option<Check> {
        let (RTLInst::Iop(op, args, dst), ClightStmt::Sset(id, rhs)) = (inst, unlabel(stmt)) else {
            return None;
        };
        if *dst != *id as RTLReg {
            return None;
        }
        let mut converter = ConversionContext::new(HashMap::new(), model);
        let expression = convert_expr(rhs, &mut converter);
        let mut current = &expression;
        let mut casts = Vec::new();
        loop {
            match current {
                CExpr::Paren(inner) => current = inner,
                CExpr::Cast(ty, inner) => {
                    casts.push(IntTy::carrier(ty, model)?);
                    current = inner;
                }
                _ => break,
            }
        }
        if !casts.iter().any(|ty| ty.bits < 64) {
            return None;
        }
        let mut check =
            self.check_effect(Domain::ResultRepresentation, declarations, model, |eval| {
                eval.word_inputs = context
                    .and_then(|(f, n)| f.word_inputs.get(&n))
                    .cloned()
                    .unwrap_or_default();
                align_machine_inputs(eval, rhs, args, context)?;
                let machine = machine_op(eval, op, args)?;
                if !casts.iter().any(|ty| ty.bits < machine.ty.bits) {
                    return None;
                }
                let mut projection = machine.clone();
                for ty in casts.iter().rev() {
                    projection = projection.cast(*ty);
                }
                projection = projection.cast(machine.ty);
                Some(Effect {
                    machine: machine.bits,
                    source: projection.bits,
                    defined: Bool::from_bool(true),
                })
            });
        if check.verdict != Verdict::Refuted {
            return None;
        }
        let Some(Witness::Value {
            inputs,
            machine,
            source,
            ..
        }) = check.witness.take()
        else {
            return None;
        };
        check.witness = Some(Witness::Representation {
            inputs,
            machine,
            projection: source,
        });
        Some(check)
    }

    pub(crate) fn check_store(
        &self,
        inst: &RTLInst,
        stmt: &ClightStmt,
        contract: &memory_theory::WriteContract,
        declarations: &HashMap<RTLReg, CType>,
        function: &FunctionData,
    ) -> Check {
        self.check_effect(
            Domain::FrameStore,
            declarations,
            function.data_model,
            |eval| {
                if memory_theory::check(stmt, contract, function) != memory_theory::Check::Matches {
                    return None;
                }
                let ClightStmt::Sassign(lhs, rhs) = memory_theory::primitive(stmt) else {
                    return None;
                };
                let access = IntTy::from_c(
                    &convert_clight_type(
                        crate::decompile::passes::clight_select::syntax::solve::clight_expr_type(
                            lhs,
                        ),
                        function.data_model,
                    ),
                    function.data_model,
                )?;
                let bits = u32::try_from(contract.width.checked_mul(8)?).ok()?;
                if access.bits != bits || bits > 64 {
                    return None;
                }
                let machine = match inst {
                    RTLInst::Iop(op, args, dst) if contract.locals.contains(dst) => {
                        if matches!(op, Operation::Omove) && args.len() == 1 {
                            store_source_value(eval, args[0], bits, rhs, contract.node, function)?
                        } else {
                            if !same_inputs(rhs, args) {
                                return None;
                            }
                            machine_op(eval, op, args)?
                        }
                    }
                    RTLInst::Istore(
                        chunk,
                        crate::x86::op::Addressing::Ainstack(offset),
                        args,
                        source,
                    ) if args.is_empty()
                        && *offset == contract.object.base.checked_add(contract.offset)?
                        && crate::decompile::analysis::struct_recovery_pass::chunk_byte_size(
                            chunk,
                        ) == contract.width
                        && matches!(
                            chunk,
                            MemoryChunk::MInt8Signed
                                | MemoryChunk::MInt8Unsigned
                                | MemoryChunk::MInt16Signed
                                | MemoryChunk::MInt16Unsigned
                                | MemoryChunk::MInt32
                                | MemoryChunk::MInt64
                                | MemoryChunk::MAny32
                                | MemoryChunk::MAny64
                        ) =>
                    {
                        store_source_value(eval, *source, bits, rhs, contract.node, function)?
                    }
                    _ => return None,
                };
                if machine.ty.bits < bits {
                    return None;
                }
                let mut ctx = ConversionContext::new(HashMap::new(), function.data_model);
                // Both direct C assignment and the bytewise store codec convert
                // the value to the access type before writing these exact bytes.
                let source = eval.expr(&convert_expr(rhs, &mut ctx))?.cast(access);
                Some(Effect {
                    machine: machine.bits.extract(bits - 1, 0),
                    source: source.bits,
                    defined: source.defined,
                })
            },
        )
    }

    pub(crate) fn check_load(
        &self,
        stmt: &ClightStmt,
        contract: &memory_theory::ReadContract,
        declarations: &HashMap<RTLReg, CType>,
        function: &FunctionData,
    ) -> Check {
        let load = LoadValue {
            node: contract.node,
            chunk: contract.chunk,
            destination: contract.destination,
            write_bits: contract.write_bits,
            signed_word_load: contract.signed_word_load,
        };
        self.check_load_with(
            Domain::FrameLoad,
            stmt,
            &load,
            declarations,
            function,
            |rhs| memory_theory::read_operand(rhs, contract, function),
        )
    }

    /// Preserve the word fetched by a single load through the actual C
    /// expression and assignment conversion. This universally quantified
    /// transfer is necessary even for indexed/opaque addresses; it does not
    /// establish that the address itself is correct or initialized.
    pub(crate) fn check_load_transport(
        &self,
        stmt: &ClightStmt,
        load: &LoadValue,
        declarations: &HashMap<RTLReg, CType>,
        function: &FunctionData,
    ) -> Check {
        self.check_load_with(
            Domain::LoadTransport,
            stmt,
            load,
            declarations,
            function,
            memory_theory::single_read_operand,
        )
    }

    /// Omove has no intrinsic width. The observed width must come from a
    /// decoded register write or an exact native storage event, never CType.
    pub(crate) fn check_copy_transport(
        &self,
        stmt: &ClightStmt,
        copy: &CopyValue,
        declarations: &HashMap<RTLReg, CType>,
        function: &FunctionData,
    ) -> Check {
        self.check_effect(
            Domain::CopyTransport,
            declarations,
            function.data_model,
            |eval| {
                let ClightStmt::Sset(destination, rhs) = memory_theory::primitive(stmt) else {
                    return None;
                };
                if *destination as RTLReg != copy.destination {
                    return None;
                }
                eval.word_inputs = function
                    .word_inputs
                    .get(&copy.node)
                    .cloned()
                    .unwrap_or_default();
                align_machine_inputs(eval, rhs, &[copy.source], Some((function, copy.node)))?;
                let destination = eval.reg(copy.destination)?.ty;
                let result_bits = if !copy.storage
                    && copy.bits == 32
                    && function.ptr64
                    && destination.bits > 32
                {
                    64
                } else {
                    copy.bits
                };
                let machine_ty = IntTy {
                    bits: result_bits,
                    signed: false,
                };
                let machine = native_copy_value(eval, copy, function.ptr64)?.cast(machine_ty);
                let mut context = ConversionContext::new(HashMap::new(), function.data_model);
                let source = eval
                    .expr(&convert_expr(rhs, &mut context))?
                    .cast(destination)
                    .cast(machine_ty);
                Some(Effect {
                    machine: machine.bits,
                    source: source.bits,
                    defined: source.defined,
                })
            },
        )
    }

    /// Hold a recovered switch's case/target mapping fixed and validate its
    /// discriminant view. Every case predicate (and therefore the default)
    /// must agree at the native comparison width. This is not a proof of the
    /// comparison-tree recovery or of its target topology.
    pub(crate) fn check_switch_input(
        &self,
        node: crate::x86::types::Node,
        instruction: &RTLInst,
        statement: &ClightStmt,
        declarations: &HashMap<RTLReg, CType>,
        function: &FunctionData,
    ) -> Check {
        self.check_effect(
            Domain::SwitchInput,
            declarations,
            function.data_model,
            |eval| {
                let RTLInst::Icond(condition, arguments, _, _) = instruction else {
                    return None;
                };
                if arguments.len() != 1 {
                    return None;
                }
                let bits = match condition {
                    Condition::Ccompimm(..) | Condition::Ccompuimm(..) => 32,
                    Condition::Ccomplimm(..) | Condition::Ccompluimm(..) => 64,
                    _ => return None,
                };
                let ClightStmt::Sswitch(expression, cases) = memory_theory::primitive(statement)
                else {
                    return None;
                };
                eval.word_inputs = function.word_inputs.get(&node).cloned().unwrap_or_default();
                align_machine_inputs(eval, expression, arguments, Some((function, node)))?;
                let machine = eval.machine_reg(arguments[0], bits)?;
                let mut context = ConversionContext::new(HashMap::new(), function.data_model);
                let source = eval.expr(&convert_expr(expression, &mut context))?;
                let source = source.cast(source.ty.promoted());
                let agreement = Bool::and(
                    &cases
                        .iter()
                        .filter_map(|(value, _)| {
                            value.map(|value| {
                                machine
                                    .bits
                                    .eq(BV::from_i64(value, bits))
                                    .eq(source.bits.eq(BV::from_i64(value, source.ty.bits)))
                            })
                        })
                        .collect::<Vec<_>>(),
                );
                Some(Effect {
                    machine: BV::from_u64(1, 1),
                    source: agreement.ite(&BV::from_u64(1, 1), &BV::from_u64(0, 1)),
                    defined: source.defined,
                })
            },
        )
    }

    fn check_load_with<'a>(
        &self,
        domain: Domain,
        stmt: &'a ClightStmt,
        contract: &LoadValue,
        declarations: &HashMap<RTLReg, CType>,
        function: &FunctionData,
        read_operand: impl FnOnce(&'a ClightExpr) -> Option<&'a ClightExpr>,
    ) -> Check {
        self.check_effect(domain, declarations, function.data_model, |eval| {
            let ClightStmt::Sset(destination, rhs) = memory_theory::primitive(stmt) else {
                return None;
            };
            if *destination as RTLReg != contract.destination {
                return None;
            }
            let operand = read_operand(rhs)?;
            let access = IntTy::from_c(
                &convert_clight_type(
                    crate::decompile::passes::clight_select::syntax::solve::clight_expr_type(
                        operand,
                    ),
                    function.data_model,
                ),
                function.data_model,
            )?;
            let (bits, mut signed, mut result_bits) = match contract.chunk {
                MemoryChunk::MInt8Signed => (8, true, 32),
                MemoryChunk::MInt8Unsigned => (8, false, 32),
                MemoryChunk::MInt16Signed => (16, true, 32),
                MemoryChunk::MInt16Unsigned => (16, false, 32),
                MemoryChunk::MInt32 | MemoryChunk::MAny32 => (32, false, 32),
                MemoryChunk::MInt64 | MemoryChunk::MAny64 => (64, false, 64),
                _ => return None,
            };
            if access.bits != bits {
                return None;
            }
            let destination = eval.reg(contract.destination)?.ty;
            let mut zero_upper_word = false;
            if let Some(written) = contract.write_bits {
                if bits > written {
                    return None;
                }
                match written {
                    32 if function.ptr64 && destination.bits > 32 => {
                        result_bits = 64;
                        zero_upper_word = true;
                    }
                    64 if function.ptr64 => {
                        // A 32-bit memory chunk alone cannot distinguish
                        // MOVSXD from a 32-bit write that zeroes the high
                        // word. Require the independent decoder evidence.
                        if bits == 32 {
                            if !contract.signed_word_load {
                                return None;
                            }
                            signed = true;
                        }
                        result_bits = 64;
                    }
                    8 | 16 | 32 => result_bits = written,
                    _ => return None,
                }
            }
            if destination.bits > result_bits {
                return None;
            }
            let memory = BV::new_const(format!("frame_read_{}", contract.node), bits);
            let machine_ty = IntTy {
                bits: result_bits,
                signed: false,
            };
            let machine = if zero_upper_word {
                Value::raw(memory.clone(), signed)
                    .cast(IntTy {
                        bits: 32,
                        signed: false,
                    })
                    .cast(machine_ty)
            } else {
                Value::raw(memory.clone(), signed).cast(machine_ty)
            };
            let mut ctx = ConversionContext::new(HashMap::new(), function.data_model);
            // Substitute only this exact converted memory expression. The
            // shared cell has arbitrary bits, not a guessed reaching value.
            eval.memory = Some((
                convert_expr(operand, &mut ctx),
                Value::raw(memory, access.signed),
            ));
            let source = eval
                .expr(&convert_expr(rhs, &mut ctx))?
                .cast(destination)
                .cast(machine_ty);
            Some(Effect {
                machine: machine.bits,
                source: source.bits,
                defined: source.defined,
            })
        })
    }

    fn check_effect(
        &self,
        domain: Domain,
        declarations: &HashMap<RTLReg, CType>,
        model: DataModel,
        build: impl FnOnce(&mut Eval<'_>) -> Option<Effect>,
    ) -> Check {
        // Adding an obligation family must not remove an existing family's
        // semantic vetoes by consuming its quota. Keep one reusable verifier,
        // with the same deterministic per-family bound and explicit Unknown.
        // A result-representation query is one machine operation projected
        // through a cast chain, run only for a narrowing cast; it is not
        // bounded, so a large function's candidate count cannot turn a lossy
        // cast back into an admissible one.
        let mut checks = self.checks.get();
        if checks[domain as usize] >= 256 && !matches!(domain, Domain::ResultRepresentation) {
            return Check::plain(Verdict::Unknown);
        }
        checks[domain as usize] += 1;
        self.checks.set(checks);
        let mut eval = Eval {
            declarations,
            model,
            registers: BTreeSet::new(),
            fuel: if matches!(domain, Domain::FlagEffect) {
                2048
            } else {
                96
            },
            memory: None,
            word_inputs: BTreeSet::new(),
            machine_overrides: BTreeMap::new(),
        };
        let obligation = build(&mut eval);
        let mut witness = None;
        let verdict = match obligation {
            None => Verdict::Unsupported,
            Some(effect) => {
                let bad = Bool::and(&[effect.defined.clone(), effect.source.eq(&effect.machine)])
                    .not()
                    .simplify();
                if bad.as_bool() == Some(false) {
                    Verdict::Equivalent
                } else {
                    self.solver.push();
                    self.solver.assert(&bad);
                    let verdict = match self.solver.check() {
                        SatResult::Unsat => Verdict::Equivalent,
                        SatResult::Sat => {
                            if let Some(m) = self.solver.get_model() {
                                let inputs = eval
                                    .registers
                                    .iter()
                                    .filter_map(|reg| {
                                        let input = Eval::input_bits(*reg);
                                        Some((*reg, m.eval(&input, true)?.as_u64()?))
                                    })
                                    .collect();
                                if let (Some(machine), Some(source), Some(source_defined)) = (
                                    m.eval(&effect.machine, true).and_then(|v| v.as_u64()),
                                    m.eval(&effect.source, true).and_then(|v| v.as_u64()),
                                    m.eval(&effect.defined, true).and_then(|v| v.as_bool()),
                                ) {
                                    witness = Some(Witness::Value {
                                        inputs,
                                        memory: eval
                                            .memory
                                            .as_ref()
                                            .and_then(|(_, v)| m.eval(&v.bits, true)?.as_u64()),
                                        machine,
                                        source,
                                        source_defined,
                                    });
                                }
                            }
                            if witness.is_some() {
                                Verdict::Refuted
                            } else {
                                Verdict::Unknown
                            }
                        }
                        SatResult::Unknown => Verdict::Unknown,
                    };
                    self.solver.pop(1);
                    verdict
                }
            }
        };
        Check {
            verdict,
            registers: eval.registers,
            witness,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::decompile::passes::clight_select::solvers::integer_semantics::*;
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

    #[test]
    fn physical_byte_comparison_accepts_promotions_but_rejects_changed_predicates() {
        let mut function = FunctionData::new(
            1,
            "byte_comparison".into(),
            vec![],
            vec![],
            None,
            0,
            10,
            true,
        );
        crate::decompile::passes::clight_select::solvers::observations::set_comparison(
            &mut function.analysis_facts,
            10,
            8,
        );
        let native = RTLInst::Icond(
            Condition::Ccompimm(Comparison::Ceq, 0),
            Arc::new(vec![1]),
            Either::Right(20),
            Either::Right(30),
        );
        let comparison = |op| {
            ClightStmt::Sifthenelse(
                ClightExpr::Ebinop(
                    op,
                    Box::new(ClightExpr::Ecast(
                        Box::new(ClightExpr::Etempvar(1, int(true))),
                        int(true),
                    )),
                    Box::new(ClightExpr::EconstInt(0, int(true))),
                    int(true),
                ),
                Box::new(ClightStmt::Sgoto(20)),
                Box::new(ClightStmt::Sgoto(30)),
            )
        };
        let declarations = HashMap::from([(1, CType::char_signed())]);
        let validator = Validator::new();
        assert_eq!(
            validator
                .check_at(
                    10,
                    &native,
                    &comparison(ClightBinaryOp::Oeq),
                    &declarations,
                    &function
                )
                .verdict,
            Verdict::Equivalent
        );
        assert_eq!(
            validator
                .check_at(
                    10,
                    &native,
                    &comparison(ClightBinaryOp::One),
                    &declarations,
                    &function
                )
                .verdict,
            Verdict::Refuted
        );
        // Without the byte observation, the RTL32 comparison also observes
        // bits the C byte cannot retain. They are not erased from the model.
        assert_eq!(
            validator
                .check(
                    &native,
                    &comparison(ClightBinaryOp::Oeq),
                    &declarations,
                    function.data_model
                )
                .verdict,
            Verdict::Refuted
        );
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

    #[test]
    fn a_narrow_c_input_cannot_define_the_machine_upper_bits() {
        let validator = Validator::new();
        let mut declarations = decls();
        declarations.insert(1, CType::int());
        let instruction = RTLInst::Iop(Operation::Oaddlimm(0), Arc::new(vec![1]), 3);
        let signed_extension = ClightStmt::Sset(
            3,
            ClightExpr::Ecast(Box::new(ClightExpr::Etempvar(1, int(true))), long(true)),
        );
        assert_eq!(
            validator
                .check(
                    &instruction,
                    &signed_extension,
                    &declarations,
                    DataModel::Lp64
                )
                .verdict,
            Verdict::Refuted
        );

        let mut function = FunctionData::new(
            1,
            "width_relation".into(),
            vec![],
            vec![],
            None,
            0,
            10,
            true,
        );
        function.word_inputs.insert(10, BTreeSet::from([1]));
        assert_eq!(
            validator
                .check_at(
                    10,
                    &instruction,
                    &signed_extension,
                    &declarations,
                    &function
                )
                .verdict,
            Verdict::Refuted
        );
        let zero_extension = ClightStmt::Sset(
            3,
            ClightExpr::Ecast(
                Box::new(ClightExpr::Ecast(
                    Box::new(ClightExpr::Etempvar(1, int(true))),
                    int(false),
                )),
                long(false),
            ),
        );
        assert_eq!(
            validator
                .check_at(10, &instruction, &zero_extension, &declarations, &function)
                .verdict,
            Verdict::Equivalent
        );
    }

    #[test]
    fn decoded_copy_width_and_explicit_pointer_bridge_preserve_exact_bits() {
        let function =
            FunctionData::new(1, "copy_transfer".into(), vec![], vec![], None, 0, 10, true);
        let mut declarations = decls();
        declarations.insert(3, CType::uint());
        let statement = ClightStmt::Sset(3, ClightExpr::Etempvar(1, long(true)));
        let mut copy = CopyValue {
            node: 10,
            source: 1,
            destination: 3,
            bits: 32,
            storage: true,
            memory_input: None,
        };
        let checker = Validator::new();
        assert_eq!(
            checker
                .check_copy_transport(&statement, &copy, &declarations, &function)
                .verdict,
            Verdict::Equivalent
        );
        copy.bits = 64;
        assert_eq!(
            checker
                .check_copy_transport(&statement, &copy, &declarations, &function)
                .verdict,
            Verdict::Refuted
        );

        declarations.insert(1, CType::ptr(CType::Void));
        let pointer = ClightType::Tpointer(Arc::new(ClightType::Tvoid), ClightAttr::default());
        let statement = ClightStmt::Sset(
            3,
            ClightExpr::Ecast(
                Box::new(ClightExpr::Etempvar(1, pointer.clone())),
                int(false),
            ),
        );
        copy.bits = 32;
        assert_eq!(
            checker
                .check_copy_transport(&statement, &copy, &declarations, &function)
                .verdict,
            Verdict::Equivalent
        );
        copy.bits = 64;
        assert_eq!(
            checker
                .check_copy_transport(&statement, &copy, &declarations, &function)
                .verdict,
            Verdict::Refuted
        );
        let mut function = function;
        function.word_inputs.insert(10, BTreeSet::from([1]));
        declarations.insert(3, CType::ulong());
        let statement = ClightStmt::Sset(
            3,
            ClightExpr::Ecast(Box::new(ClightExpr::Etempvar(1, pointer)), long(false)),
        );
        assert_eq!(
            checker
                .check_copy_transport(&statement, &copy, &declarations, &function)
                .verdict,
            Verdict::Refuted,
            "the C cast must not borrow the machine's upper-word normalization"
        );
    }

    #[test]
    fn indexed_load_transport_exposes_a_real_lost_bit_witness() {
        let function = FunctionData::new(
            1,
            "indexed_transfer".into(),
            vec![],
            vec![],
            None,
            0,
            10,
            true,
        );
        let mut declarations = decls();
        declarations.insert(1, CType::ptr(CType::ulong()));
        declarations.insert(3, CType::uint());
        let pointer = ClightType::Tpointer(Arc::new(long(false)), ClightAttr::default());
        let address = ClightExpr::Ebinop(
            ClightBinaryOp::Oadd,
            Box::new(ClightExpr::Etempvar(1, pointer.clone())),
            Box::new(ClightExpr::Etempvar(2, long(false))),
            pointer,
        );
        let statement = ClightStmt::Sset(3, ClightExpr::Ederef(Box::new(address), long(false)));
        let load = LoadValue {
            node: 10,
            chunk: MemoryChunk::MAny64,
            destination: 3,
            write_bits: Some(64),
            signed_word_load: false,
        };
        let checker = Validator::new();
        let check = checker.check_load_transport(&statement, &load, &declarations, &function);
        assert_eq!(check.verdict, Verdict::Refuted);
        let Some(Witness::Value {
            machine,
            source,
            memory: Some(memory),
            source_defined,
            ..
        }) = check.witness
        else {
            panic!("expected a concrete loaded-word counterexample");
        };
        assert!(source_defined);
        assert_eq!(machine, memory);
        assert_ne!(machine, source);
        declarations.insert(3, CType::ulong());
        assert_eq!(
            checker
                .check_load_transport(&statement, &load, &declarations, &function)
                .verdict,
            Verdict::Equivalent
        );
    }

    #[test]
    fn switch_input_preserves_machine_case_predicates_without_flattening_control() {
        let mut function =
            FunctionData::new(1, "switch_view".into(), vec![], vec![], None, 0, 10, true);
        function.word_inputs.insert(10, BTreeSet::from([1]));
        let native = RTLInst::Icond(
            Condition::Ccompimm(Comparison::Ceq, -1),
            Arc::new(vec![1]),
            Either::Right(20),
            Either::Right(30),
        );
        let statement = ClightStmt::Sswitch(
            ClightExpr::Etempvar(1, int(true)),
            vec![
                (Some(-1), ClightStmt::Sgoto(20)),
                (Some(0), ClightStmt::Sgoto(40)),
                (None, ClightStmt::Sgoto(50)),
            ],
        );
        let mut declarations = decls();
        declarations.insert(1, CType::int());
        let checker = Validator::new();
        assert_eq!(
            checker
                .check_switch_input(10, &native, &statement, &declarations, &function)
                .verdict,
            Verdict::Equivalent
        );
        declarations.insert(1, CType::ulong());
        assert_eq!(
            checker
                .check_switch_input(10, &native, &statement, &declarations, &function)
                .verdict,
            Verdict::Refuted,
            "a machine 32-bit -1 case is not a zero-extended unsigned long -1 case"
        );
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
    fn a_narrow_self_updated_carrier_does_not_hide_wide_multiply_bits() {
        let declarations = HashMap::from([(1, CType::int())]);
        let native = RTLInst::Iop(Operation::Omullimm(65537), Arc::new(vec![1]), 1);
        let source = ClightStmt::Sset(
            1,
            ClightExpr::Ebinop(
                ClightBinaryOp::Omul,
                Box::new(ClightExpr::Ecast(
                    Box::new(ClightExpr::Etempvar(1, int(true))),
                    long(false),
                )),
                Box::new(ClightExpr::EconstLong(65537, long(false))),
                long(false),
            ),
        );
        let result = Validator::new().check(&native, &source, &declarations, DataModel::Lp64);
        assert_eq!(result.verdict, Verdict::Refuted);
        assert!(result.witness.is_some());
        let wide = HashMap::from([(1, CType::ulong())]);
        assert_eq!(
            Validator::new()
                .check(&native, &source, &wide, DataModel::Lp64)
                .verdict,
            Verdict::Equivalent
        );
    }

    #[test]
    fn pointer_result_casts_cannot_hide_a_native_address_high_word() {
        use crate::x86::op::Addressing;
        let pointer = ClightType::Tpointer(
            Arc::new(ClightType::Tint(
                ClightIntSize::I8,
                ClightSignedness::Unsigned,
                ClightAttr::default(),
            )),
            ClightAttr::default(),
        );
        let expression = ClightExpr::Ebinop(
            ClightBinaryOp::Oadd,
            Box::new(ClightExpr::Etempvar(1, pointer.clone())),
            Box::new(ClightExpr::Etempvar(2, long(false))),
            pointer,
        );
        let native = RTLInst::Iop(
            Operation::Oleal(Addressing::Aindexed2(0)),
            Arc::new(vec![1, 2]),
            3,
        );
        let declarations = HashMap::from([
            (1, CType::ptr(CType::char_unsigned())),
            (2, CType::ulong()),
            (3, CType::ulong()),
        ]);
        let bad = ClightStmt::Sset(
            3,
            ClightExpr::Ecast(Box::new(expression.clone()), int(false)),
        );
        let verdict = Validator::new().check(&native, &bad, &declarations, DataModel::Lp64);
        assert_eq!(verdict.verdict, Verdict::Refuted);
        assert!(matches!(
            verdict.witness,
            Some(Witness::Representation { .. })
        ));
        let wide = ClightStmt::Sset(3, ClightExpr::Ecast(Box::new(expression), long(false)));
        assert_eq!(
            Validator::new()
                .check(&native, &wide, &declarations, DataModel::Lp64)
                .verdict,
            Verdict::Unsupported,
            "representable bits do not prove pointer lifetime"
        );
    }

    #[test]
    fn a_spent_equivalence_bound_does_not_waive_the_result_representation() {
        use crate::x86::op::Addressing;
        let pointer = ClightType::Tpointer(Arc::new(ClightType::Tvoid), ClightAttr::default());
        let sum = ClightExpr::Ebinop(
            ClightBinaryOp::Oadd,
            Box::new(ClightExpr::Etempvar(1, pointer.clone())),
            Box::new(ClightExpr::Etempvar(2, long(true))),
            pointer,
        );
        let native = RTLInst::Iop(
            Operation::Oleal(Addressing::Aindexed2(0)),
            Arc::new(vec![1, 2]),
            3,
        );
        let declarations =
            HashMap::from([(1, CType::long()), (2, CType::long()), (3, CType::long())]);
        let truncated = ClightStmt::Sset(3, ClightExpr::Ecast(Box::new(sum), int(true)));
        let v = Validator::new();
        let spend = ClightStmt::Sset(3, bin(ClightBinaryOp::Oadd, int(false)));
        for _ in 0..256 {
            v.check(&operation(Operation::Oadd), &spend, &decls(), DataModel::Lp64);
        }
        assert_eq!(
            v.check(&operation(Operation::Oadd), &spend, &decls(), DataModel::Lp64)
                .verdict,
            Verdict::Unknown,
            "the integer family's bound is spent"
        );
        let verdict = v.check(&native, &truncated, &declarations, DataModel::Lp64);
        assert_eq!(verdict.verdict, Verdict::Refuted);
        assert!(matches!(
            verdict.witness,
            Some(Witness::Representation { .. })
        ));
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
        // The declaration alone does not prove the high machine word. This
        // fixture explicitly supplies the CFG-derived zero-extension view.
        let mut function =
            FunctionData::new(1, "mixed_branch".into(), vec![], vec![], None, 0, 10, true);
        function.word_inputs.insert(10, BTreeSet::from([2]));
        assert_eq!(
            v.check_at(10, &machine, &stmt, &declarations, &function)
                .verdict,
            Verdict::Equivalent
        );
        let wrong = ClightStmt::Sifthenelse(
            bin(ClightBinaryOp::Olt, long(false)),
            Box::new(ClightStmt::Sgoto(11)),
            Box::new(ClightStmt::Sgoto(12)),
        );
        assert_eq!(
            v.check_at(10, &machine, &wrong, &declarations, &function)
                .verdict,
            Verdict::Refuted
        );
        let inverted = ClightStmt::Sifthenelse(
            bin(ClightBinaryOp::Oge, long(true)),
            Box::new(ClightStmt::Sgoto(12)),
            Box::new(ClightStmt::Sgoto(11)),
        );
        assert_eq!(
            v.check_at(10, &machine, &inverted, &declarations, &function)
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
