//! Exact x86 CMP/TEST flag predicates. The machine checker uses bit-vector
//! subtraction; C construction below uses bounded pieces to avoid signed
//! overflow, including at 64 bits. This is ISA semantics, not an idiom list.

use super::EffectId;
use crate::x86::op::Comparison;
use crate::x86::types::{CminorBinop as B, CminorUnop as U, Constant, CsharpminorExpr as E};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Producer {
    Compare,
    Test,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Predicate {
    Overflow,
    NoOverflow,
    Below,
    AboveEqual,
    Equal,
    NotEqual,
    BelowEqual,
    Above,
    Sign,
    NonSign,
    Parity,
    NoParity,
    Less,
    GreaterEqual,
    LessEqual,
    Greater,
}

impl Predicate {
    pub(crate) fn cmov(mnemonic: &str) -> Option<Self> {
        Some(match mnemonic.strip_prefix("CMOV")? {
            "O" => Self::Overflow,
            "NO" => Self::NoOverflow,
            "B" | "C" | "NAE" => Self::Below,
            "AE" | "NB" | "NC" => Self::AboveEqual,
            "E" | "Z" => Self::Equal,
            "NE" | "NZ" => Self::NotEqual,
            "BE" | "NA" => Self::BelowEqual,
            "A" | "NBE" => Self::Above,
            "S" => Self::Sign,
            "NS" => Self::NonSign,
            "P" | "PE" => Self::Parity,
            "NP" | "PO" => Self::NoParity,
            "L" | "NGE" => Self::Less,
            "GE" | "NL" => Self::GreaterEqual,
            "LE" | "NG" => Self::LessEqual,
            "G" | "NLE" => Self::Greater,
            _ => return None,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FlagSelect {
    pub capture: u64,
    pub producer: Producer,
    pub predicate: Predicate,
    pub width: usize,
    pub immediate: i64,
    pub result_bits: u32,
}

impl FlagSelect {
    pub(crate) fn valid(&self) -> bool {
        matches!(self.width, 1 | 2 | 4 | 8) && matches!(self.result_bits, 32 | 64)
    }
    pub(crate) fn read_effect(&self) -> EffectId {
        EffectId {
            instruction: self.capture,
            slot: 0,
        }
    }
}

fn bin(op: B, a: E, b: E) -> E {
    E::Ebinop(op, Box::new(a), Box::new(b))
}
fn n(value: i64) -> E {
    E::Econst(Constant::Olongconst(value))
}
fn and(a: E, b: E) -> E {
    bin(B::Oandl, a, b)
}
fn xor(a: E, b: E) -> E {
    bin(B::Oxorl, a, b)
}
fn or(a: E, b: E) -> E {
    bin(B::Oorl, a, b)
}
fn eq(a: E, b: E) -> E {
    bin(B::Ocmplu(Comparison::Ceq), a, b)
}
fn ne(a: E, b: E) -> E {
    bin(B::Ocmplu(Comparison::Cne), a, b)
}
fn not(a: E) -> E {
    eq(a, n(0))
}

pub(crate) fn predicate_expr(spec: FlagSelect, loaded: E) -> Option<E> {
    if !spec.valid() {
        return None;
    }
    let bits = spec.width * 8;
    let mask = if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    };
    let sign = 1u64 << (bits - 1);
    let a = and(loaded, n(mask as i64));
    let b = n((spec.immediate as u64 & mask) as i64);
    let (sf, cf, of, zf, low_byte) = match spec.producer {
        Producer::Compare => {
            let sa = ne(and(a.clone(), n(sign as i64)), n(0));
            let sb = n(i64::from(spec.immediate as u64 & sign != 0));
            let borrow = bin(
                B::Ocmplu(Comparison::Clt),
                and(a.clone(), n((sign - 1) as i64)),
                and(b.clone(), n((sign - 1) as i64)),
            );
            let sf = xor(xor(sa.clone(), sb.clone()), borrow.clone());
            let cf = or(
                bin(B::Ocmplu(Comparison::Clt), sa.clone(), sb.clone()),
                and(eq(sa.clone(), sb.clone()), borrow),
            );
            let of = and(xor(sa.clone(), sb), xor(sa, sf.clone()));
            // Both operands are 0..255. The difference is -255..255, so
            // subtraction is defined even if a later C type choice is signed.
            let low = and(
                bin(B::Osubl, and(a.clone(), n(255)), and(b.clone(), n(255))),
                n(255),
            );
            (sf, cf, of, eq(a, b), low)
        }
        Producer::Test => {
            let value = and(a, b);
            (
                ne(and(value.clone(), n(sign as i64)), n(0)),
                n(0),
                n(0),
                eq(value.clone(), n(0)),
                and(value, n(255)),
            )
        }
    };
    let parity = || {
        let mut folded = low_byte;
        for shift in [4, 2, 1] {
            folded = xor(folded.clone(), bin(B::Oshrlu, folded, n(shift)));
        }
        eq(and(folded, n(1)), n(0))
    };
    use Predicate::*;
    Some(match spec.predicate {
        Overflow => of,
        NoOverflow => not(of),
        Below => cf,
        AboveEqual => not(cf),
        Equal => zf,
        NotEqual => not(zf),
        BelowEqual => or(cf, zf),
        Above => not(or(cf, zf)),
        Sign => sf,
        NonSign => not(sf),
        Parity => parity(),
        NoParity => not(parity()),
        Less => xor(sf, of),
        GreaterEqual => not(xor(sf, of)),
        LessEqual => or(xor(sf, of), zf),
        Greater => not(or(xor(sf, of), zf)),
    })
}

pub(crate) fn select_expr(spec: FlagSelect, old: E, taken: E, loaded: E) -> Option<E> {
    let value = E::Econdition(
        Box::new(predicate_expr(spec, loaded)?),
        Box::new(taken),
        Box::new(old),
    );
    Some(if spec.result_bits == 32 {
        E::Eunop(
            U::Olongofintu,
            Box::new(E::Eunop(U::Ointoflong, Box::new(value))),
        )
    } else {
        value
    })
}

/// Independent machine-side semantics: no C expression is consulted.
pub(crate) fn machine_predicate(spec: FlagSelect, a: &z3::ast::BV) -> Option<z3::ast::Bool> {
    use z3::ast::{Bool, BV};
    if !spec.valid() || a.get_size() != (spec.width * 8) as u32 {
        return None;
    }
    let bits = a.get_size();
    let b = BV::from_i64(spec.immediate, bits);
    let result = match spec.producer {
        Producer::Compare => a.bvsub(&b),
        Producer::Test => a.bvand(&b),
    };
    let bit = |v: &BV| v.extract(bits - 1, bits - 1).eq(BV::from_u64(1, 1));
    let sf = bit(&result);
    let zf = result.eq(BV::from_u64(0, bits));
    let cf = match spec.producer {
        Producer::Compare => a.bvult(&b),
        Producer::Test => Bool::from_bool(false),
    };
    let of = match spec.producer {
        Producer::Compare => Bool::and(&[bit(a).xor(bit(&b)), bit(a).xor(&sf)]),
        Producer::Test => Bool::from_bool(false),
    };
    let mut odd = result.extract(0, 0);
    for bit in 1..8 {
        odd = odd.bvxor(result.extract(bit, bit));
    }
    let pf = odd.eq(BV::from_u64(0, 1));
    use Predicate::*;
    Some(match spec.predicate {
        Overflow => of,
        NoOverflow => of.not(),
        Below => cf,
        AboveEqual => cf.not(),
        Equal => zf,
        NotEqual => zf.not(),
        BelowEqual => Bool::or(&[cf, zf]),
        Above => Bool::or(&[cf, zf]).not(),
        Sign => sf,
        NonSign => sf.not(),
        Parity => pf,
        NoParity => pf.not(),
        Less => sf.xor(&of),
        GreaterEqual => sf.xor(&of).not(),
        LessEqual => Bool::or(&[sf.xor(&of), zf]),
        Greater => Bool::or(&[sf.xor(&of), zf]).not(),
    })
}
