

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::{declare_io_from, run_pass};

use std::sync::Arc;
use std::convert::TryFrom;
use crate::x86::op::{Addressing, Comparison, Condition, Operation};
use crate::x86::types::*;
use ascent::ascent_par;
use either::Either;
use log::warn;


ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct CminorPassProgram;


    relation rtl_inst(Node, RTLInst);
    relation rtl_succ(Node, Node);
    relation instr_in_function(Node, Address);
    relation func_stacksz(Address, Address, Symbol, u64);
    relation call_return_reg(Node, RTLReg);

    relation cminor_stmt(Node, CminorStmt);
    relation cminor_fallthrough(Node, Node);


    cminor_stmt(node, CminorStmt::Snop) <--
        rtl_inst(node, ?RTLInst::Iop(Operation::Omove, args, dst)),
        if args.len() == 1 && args[0] == *dst;

    cminor_stmt(node, stmt) <--
        rtl_inst(node, ?RTLInst::Iop(op, args, dst)),
        if !(*op == Operation::Omove && args.len() == 1 && args[0] == *dst),
        let converted = {
            if args.is_empty() {
                if let Some(cst) = crate::decompile::passes::cminor_pass::constant_from_operation(&op) {
                    CminorExpr::Econst(cst)
                } else {
                    CminorExpr::Eop(op.clone(), args.clone())
                }
            } else if args.len() == 1 {
                if *op == Operation::Omove {
                    CminorExpr::Evar(args[0])
                } else if let Some(unop) = crate::decompile::passes::cminor_pass::unop_from_operation(&op) {
                    CminorExpr::Eunop(unop, args[0])
                } else {
                    CminorExpr::Eop(op.clone(), args.clone())
                }
            } else if args.len() == 2 {
                if let Some(binop) = crate::decompile::passes::cminor_pass::binop_from_operation(&op) {
                    CminorExpr::Ebinop(binop, args[0], args[1])
                } else {
                    CminorExpr::Eop(op.clone(), args.clone())
                }
            } else {
                CminorExpr::Eop(op.clone(), args.clone())
            }
        },
        let stmt = CminorStmt::Sassign(*dst, converted);


    cminor_stmt(node, stmt) <--
        rtl_inst(node, ?RTLInst::Iload(chunk, addr, args, dst)),
        let converted = CminorExpr::Eload(chunk.clone(), addr.clone(), args.clone()),
        let stmt = CminorStmt::Sassign(*dst, converted);

    cminor_stmt(node, stmt) <--
        rtl_inst(node, ?RTLInst::Istore(chunk, addr, args, src)),
        let stmt = CminorStmt::Sstore(chunk.clone(), addr.clone(), args.clone(), *src);

    cminor_stmt(node, stmt) <--
        rtl_inst(node, ?RTLInst::Ibuiltin(name, args, res)),
        let stmt = CminorStmt::Sbuiltin(None, name.clone(), args.clone(), res.clone());

    cminor_stmt(node, stmt) <--
        rtl_inst(node, ?RTLInst::Icond(cond, args, Either::Right(ifso), Either::Right(ifnot))),
        let stmt = CminorStmt::Sifthenelse(cond.clone(), args.clone(), *ifso, *ifnot);

    cminor_stmt(node, stmt) <--
        rtl_inst(node, ?RTLInst::Icond(cond, args, Either::Left(_sym), Either::Right(ifnot))),
        let stmt = CminorStmt::Sjump(*ifnot);

    cminor_stmt(node, stmt) <--
        rtl_inst(node, ?RTLInst::Icond(cond, args, Either::Right(ifso), Either::Left(_sym))),
        let stmt = CminorStmt::Sjump(*ifso);

    cminor_stmt(node, CminorStmt::Snop) <--
        rtl_inst(node, ?RTLInst::Icond(_, _, Either::Left(_), Either::Left(_)));

    cminor_stmt(node, stmt) <--
        rtl_inst(node, ?RTLInst::Ijumptable(arg, targets)),
        let stmt = CminorStmt::Sjumptable(*arg, targets.clone());

    cminor_stmt(node, stmt) <--
        rtl_inst(node, ?RTLInst::Ibranch(Either::Right(target))),
        let stmt = CminorStmt::Sjump(*target);

    cminor_stmt(node, CminorStmt::Sbuiltin(None, "__builtin_unreachable".to_string(), vec![], BuiltinArg::BAInt(0))) <--
        rtl_inst(node, ?RTLInst::Ibranch(Either::Left(_sym)));

    cminor_stmt(node, stmt) <--
        rtl_inst(node, ?RTLInst::Ireturn(opt)),
        let stmt = CminorStmt::Sreturn(*opt);

    cminor_stmt(node, CminorStmt::Snop) <--
        rtl_inst(node, RTLInst::Inop);


    cminor_stmt(node, stmt) <--
        rtl_inst(node, ?RTLInst::Icall(sig, callee, args, dst, _succ)),
        let stmt = CminorStmt::Scall(*dst, sig.clone(), callee.clone(), args.clone());


    cminor_stmt(node, stmt) <--
        rtl_inst(node, ?RTLInst::Itailcall(sig, callee, args)),
        let stmt = CminorStmt::Stailcall(sig.clone(), callee.clone(), args.clone());

    // Derive fallthrough from rtl_succ for synthetic nodes (bit 62 set) whose addresses break sort order
    cminor_fallthrough(node, next) <--
        rtl_succ(node, next),
        if (*node & (1u64 << 62) != 0) || (*next & (1u64 << 62) != 0),
        cminor_stmt(node, stmt),
        if matches!(stmt,
            CminorStmt::Sassign(_, _) | CminorStmt::Sstore(_, _, _, _) |
            CminorStmt::Sbuiltin(_, _, _, _) | CminorStmt::Scall(_, _, _, _) |
            CminorStmt::Snop),
        cminor_stmt(next, _),
        instr_in_function(node, func),
        instr_in_function(next, func);
}

pub struct CminorPass;

impl IRPass for CminorPass {
    fn name(&self) -> &'static str { "cminor" }

    fn run(&self, db: &mut DecompileDB) {
        run_pass!(db, CminorPassProgram);
    }

    declare_io_from!(CminorPassProgram);
}


const RECURSION_MAX_DEPTH: usize = 100;

pub(crate) fn immediate_from_operation(op: &Operation) -> Option<i64> {
    match op {
        Operation::Ointconst(n) => Some(*n),
        Operation::Olongconst(n) => Some(*n),
        Operation::Oaddimm(n) => Some(*n),
        Operation::Omulimm(n) => Some(*n),
        Operation::Oandimm(n) => Some(*n),
        Operation::Oorimm(n) => Some(*n),
        Operation::Oxorimm(n) => Some(*n),
        Operation::Oshlimm(n) => Some(*n),
        Operation::Oshrimm(n) => Some(*n),
        Operation::Oshruimm(n) => Some(*n),
        Operation::Oaddlimm(n) => Some(*n),
        Operation::Omullimm(n) => Some(*n),
        Operation::Oandlimm(n) => Some(*n),
        Operation::Oorlimm(n) => Some(*n),
        Operation::Oxorlimm(n) => Some(*n),
        Operation::Oshllimm(n) => Some(*n),
        Operation::Oshrlimm(n) => Some(*n),
        Operation::Oshrluimm(n) => Some(*n),
        _ => None,
    }
}

fn osel_condition_expr(cond: &Condition, args: &[RTLReg]) -> CsharpminorExpr {
    match cond {
        Condition::Ccomp(cmp) if args.len() >= 4 => CsharpminorExpr::Ebinop(
            CminorBinop::Ocmp(*cmp),
            Box::new(CsharpminorExpr::Evar(args[2])),
            Box::new(CsharpminorExpr::Evar(args[3])),
        ),
        Condition::Ccompu(cmp) if args.len() >= 4 => CsharpminorExpr::Ebinop(
            CminorBinop::Ocmpu(*cmp),
            Box::new(CsharpminorExpr::Evar(args[2])),
            Box::new(CsharpminorExpr::Evar(args[3])),
        ),
        Condition::Ccompl(cmp) if args.len() >= 4 => CsharpminorExpr::Ebinop(
            CminorBinop::Ocmpl(*cmp),
            Box::new(CsharpminorExpr::Evar(args[2])),
            Box::new(CsharpminorExpr::Evar(args[3])),
        ),
        Condition::Ccomplu(cmp) if args.len() >= 4 => CsharpminorExpr::Ebinop(
            CminorBinop::Ocmplu(*cmp),
            Box::new(CsharpminorExpr::Evar(args[2])),
            Box::new(CsharpminorExpr::Evar(args[3])),
        ),
        Condition::Ccompimm(cmp, imm) if args.len() >= 3 => CsharpminorExpr::Ebinop(
            CminorBinop::Ocmp(*cmp),
            Box::new(CsharpminorExpr::Evar(args[2])),
            Box::new(CsharpminorExpr::Econst(Constant::Ointconst(*imm))),
        ),
        Condition::Ccompuimm(cmp, imm) if args.len() >= 3 => CsharpminorExpr::Ebinop(
            CminorBinop::Ocmpu(*cmp),
            Box::new(CsharpminorExpr::Evar(args[2])),
            Box::new(CsharpminorExpr::Econst(Constant::Ointconst(*imm))),
        ),
        Condition::Ccomplimm(cmp, imm) if args.len() >= 3 => CsharpminorExpr::Ebinop(
            CminorBinop::Ocmpl(*cmp),
            Box::new(CsharpminorExpr::Evar(args[2])),
            Box::new(CsharpminorExpr::Econst(Constant::Olongconst(*imm))),
        ),
        Condition::Ccompluimm(cmp, imm) if args.len() >= 3 => CsharpminorExpr::Ebinop(
            CminorBinop::Ocmplu(*cmp),
            Box::new(CsharpminorExpr::Evar(args[2])),
            Box::new(CsharpminorExpr::Econst(Constant::Olongconst(*imm))),
        ),
        Condition::Ccompf(cmp) if args.len() >= 4 => CsharpminorExpr::Ebinop(
            CminorBinop::Ocmpf(*cmp),
            Box::new(CsharpminorExpr::Evar(args[2])),
            Box::new(CsharpminorExpr::Evar(args[3])),
        ),
        Condition::Ccompfs(cmp) if args.len() >= 4 => CsharpminorExpr::Ebinop(
            CminorBinop::Ocmpfs(*cmp),
            Box::new(CsharpminorExpr::Evar(args[2])),
            Box::new(CsharpminorExpr::Evar(args[3])),
        ),
        Condition::Cnotcompf(cmp) if args.len() >= 4 => CsharpminorExpr::Ebinop(
            CminorBinop::Ocmpnotf(*cmp),
            Box::new(CsharpminorExpr::Evar(args[2])),
            Box::new(CsharpminorExpr::Evar(args[3])),
        ),
        Condition::Cnotcompfs(cmp) if args.len() >= 4 => CsharpminorExpr::Ebinop(
            CminorBinop::Ocmpnotfs(*cmp),
            Box::new(CsharpminorExpr::Evar(args[2])),
            Box::new(CsharpminorExpr::Evar(args[3])),
        ),
        _ => CsharpminorExpr::Econst(Constant::Ointconst(1)),
    }
}

pub(crate) fn constant_from_operation(op: &Operation) -> Option<Constant> {
    match op {
        Operation::Ointconst(n) => Some(Constant::Ointconst(*n)),
        Operation::Olongconst(n) => Some(Constant::Olongconst(*n)),
        Operation::Ofloatconst(f) => Some(Constant::Ofloatconst(*f)),
        Operation::Osingleconst(f) => Some(Constant::Osingleconst(*f)),
        Operation::Oindirectsymbol(ident) => {
            if *ident == 0 {
                None
            } else {
                Some(Constant::Oaddrsymbol(*ident, 0))
            }
        }
        _ => None,
    }
}
pub(crate) fn unop_from_operation(op: &Operation) -> Option<CminorUnop> {
    match op {
        Operation::Ocast8unsigned => Some(CminorUnop::Ocast8unsigned),
        Operation::Ocast8signed => Some(CminorUnop::Ocast8signed),
        Operation::Ocast16unsigned => Some(CminorUnop::Ocast16unsigned),
        Operation::Ocast16signed => Some(CminorUnop::Ocast16signed),
        Operation::Oneg => Some(CminorUnop::Onegint),
        Operation::Onot => Some(CminorUnop::Onotint),
        Operation::Onegl => Some(CminorUnop::Onegl),
        Operation::Onotl => Some(CminorUnop::Onotl),
        Operation::Onegf => Some(CminorUnop::Onegf),
        Operation::Oabsf => Some(CminorUnop::Oabsf),
        Operation::Onegfs => Some(CminorUnop::Onegfs),
        Operation::Oabsfs => Some(CminorUnop::Oabsfs),
        Operation::Osingleoffloat => Some(CminorUnop::Osingleoffloat),
        Operation::Ofloatofsingle => Some(CminorUnop::Ofloatofsingle),
        Operation::Ointoffloat => Some(CminorUnop::Ointoffloat),
        Operation::Ofloatofint => Some(CminorUnop::Ofloatofint),
        Operation::Ointofsingle => Some(CminorUnop::Ointofsingle),
        Operation::Osingleofint => Some(CminorUnop::Osingleofint),
        Operation::Olongoffloat => Some(CminorUnop::Olongoffloat),
        Operation::Ofloatoflong => Some(CminorUnop::Ofloatoflong),
        Operation::Olongofsingle => Some(CminorUnop::Olongofsingle),
        Operation::Osingleoflong => Some(CminorUnop::Osingleoflong),
        Operation::Olowlong => Some(CminorUnop::Ointoflong),
        Operation::Ocast32signed => Some(CminorUnop::Olongofint),
        Operation::Ocast32unsigned => Some(CminorUnop::Olongofintu),
        _ => None,
    }
}
pub(crate) fn binop_imm_from_operation(op: &Operation) -> Option<(CminorBinop, i64)> {
    match op {
        Operation::Oaddimm(n) => Some((CminorBinop::Oadd, *n)),
        Operation::Omulimm(n) => Some((CminorBinop::Omul, *n)),
        Operation::Oandimm(n) => Some((CminorBinop::Oand, *n)),
        Operation::Oorimm(n) => Some((CminorBinop::Oor, *n)),
        Operation::Oxorimm(n) => Some((CminorBinop::Oxor, *n)),
        Operation::Oshlimm(n) => Some((CminorBinop::Oshl, *n)),
        Operation::Oshrimm(n) => Some((CminorBinop::Oshr, *n)),
        Operation::Oshruimm(n) => Some((CminorBinop::Oshru, *n)),
        Operation::Oaddlimm(n) => Some((CminorBinop::Oaddl, *n)),
        Operation::Omullimm(n) => Some((CminorBinop::Omull, *n)),
        Operation::Oandlimm(n) => Some((CminorBinop::Oandl, *n)),
        Operation::Oorlimm(n) => Some((CminorBinop::Oorl, *n)),
        Operation::Oxorlimm(n) => Some((CminorBinop::Oxorl, *n)),
        Operation::Oshllimm(n) => Some((CminorBinop::Oshll, *n)),
        Operation::Oshrlimm(n) => Some((CminorBinop::Oshrl, *n)),
        Operation::Oshrluimm(n) => Some((CminorBinop::Oshrlu, *n)),
        Operation::Oshrximm(n) => Some((CminorBinop::Odiv, 1i64 << *n)),
        Operation::Oshrxlimm(n) => Some((CminorBinop::Odivl, 1i64 << *n)),
        // Ororimm/Ororlimm are rotate-right (not shift-right), handled as Eop and expanded in csharp_expr_from_cminor.
        _ => None,
    }
}

pub(crate) fn binop_from_operation(op: &Operation) -> Option<CminorBinop> {
    use crate::x86::op::Condition;
    match op {
        Operation::Oadd => Some(CminorBinop::Oadd),
        Operation::Osub => Some(CminorBinop::Osub),
        Operation::Omul => Some(CminorBinop::Omul),
        Operation::Odiv => Some(CminorBinop::Odiv),
        Operation::Odivu => Some(CminorBinop::Odivu),
        Operation::Omod => Some(CminorBinop::Omod),
        Operation::Omodu => Some(CminorBinop::Omodu),
        Operation::Oand => Some(CminorBinop::Oand),
        Operation::Oor => Some(CminorBinop::Oor),
        Operation::Oxor => Some(CminorBinop::Oxor),
        Operation::Oshl => Some(CminorBinop::Oshl),
        Operation::Oshr => Some(CminorBinop::Oshr),
        Operation::Oshru => Some(CminorBinop::Oshru),
        Operation::Oaddl => Some(CminorBinop::Oaddl),
        Operation::Osubl => Some(CminorBinop::Osubl),
        Operation::Omull => Some(CminorBinop::Omull),
        Operation::Odivl => Some(CminorBinop::Odivl),
        Operation::Odivlu => Some(CminorBinop::Odivlu),
        Operation::Omodl => Some(CminorBinop::Omodl),
        Operation::Omodlu => Some(CminorBinop::Omodlu),
        Operation::Oandl => Some(CminorBinop::Oandl),
        Operation::Oorl => Some(CminorBinop::Oorl),
        Operation::Oxorl => Some(CminorBinop::Oxorl),
        Operation::Oshll => Some(CminorBinop::Oshll),
        Operation::Oshrl => Some(CminorBinop::Oshrl),
        Operation::Oshrlu => Some(CminorBinop::Oshrlu),
        Operation::Oaddf => Some(CminorBinop::Oaddf),
        Operation::Osubf => Some(CminorBinop::Osubf),
        Operation::Omulf => Some(CminorBinop::Omulf),
        Operation::Odivf => Some(CminorBinop::Odivf),
        Operation::Oaddfs => Some(CminorBinop::Oaddfs),
        Operation::Osubfs => Some(CminorBinop::Osubfs),
        Operation::Omulfs => Some(CminorBinop::Omulfs),
        Operation::Odivfs => Some(CminorBinop::Odivfs),
        Operation::Omaxf => Some(CminorBinop::Omaxf),
        Operation::Ominf => Some(CminorBinop::Ominf),
        Operation::Omulhs => Some(CminorBinop::Omulhs),
        Operation::Omulhu => Some(CminorBinop::Omulhu),
        Operation::Omullhs => Some(CminorBinop::Omullhs),
        Operation::Omullhu => Some(CminorBinop::Omullhu),
        Operation::Ocmp(cond) => match cond {
            Condition::Ccomp(cmp) => Some(CminorBinop::Ocmp(*cmp)),
            Condition::Ccompu(cmp) => Some(CminorBinop::Ocmpu(*cmp)),
            Condition::Ccompf(cmp) => Some(CminorBinop::Ocmpf(*cmp)),
            Condition::Cnotcompf(cmp) => Some(CminorBinop::Ocmpnotf(*cmp)),
            Condition::Ccompfs(cmp) => Some(CminorBinop::Ocmpfs(*cmp)),
            Condition::Cnotcompfs(cmp) => Some(CminorBinop::Ocmpnotfs(*cmp)),
            Condition::Ccompl(cmp) => Some(CminorBinop::Ocmpl(*cmp)),
            Condition::Ccomplu(cmp) => Some(CminorBinop::Ocmplu(*cmp)),
            _ => None,
        },
        _ => None,
    }
}

fn ocmp_imm_from_operation(op: &Operation) -> Option<(CminorBinop, i64, bool)> {
    use crate::x86::op::Condition;
    match op {
        Operation::Ocmp(cond) => match cond {
            Condition::Ccompimm(cmp, n) => Some((CminorBinop::Ocmp(*cmp), *n, false)),
            Condition::Ccompuimm(cmp, n) => Some((CminorBinop::Ocmpu(*cmp), *n, false)),
            Condition::Ccomplimm(cmp, n) => Some((CminorBinop::Ocmpl(*cmp), *n, true)),
            Condition::Ccompluimm(cmp, n) => Some((CminorBinop::Ocmplu(*cmp), *n, true)),
            Condition::Cmaskzero(n) => {
                Some((CminorBinop::Oand, *n, false))
            }
            Condition::Cmasknotzero(n) => {
                Some((CminorBinop::Oand, *n, false))
            }
            _ => None,
        },
        _ => None,
    }
}


fn is_long_binop(op: &CminorBinop) -> bool {
    matches!(
        op,
        CminorBinop::Oaddl
            | CminorBinop::Osubl
            | CminorBinop::Omull
            | CminorBinop::Odivl
            | CminorBinop::Odivlu
            | CminorBinop::Omodl
            | CminorBinop::Omodlu
            | CminorBinop::Oandl
            | CminorBinop::Oorl
            | CminorBinop::Oxorl
            | CminorBinop::Oshll
            | CminorBinop::Oshrl
            | CminorBinop::Oshrlu
            | CminorBinop::Omullhs
            | CminorBinop::Omullhu
            | CminorBinop::Ocmpl(_)
            | CminorBinop::Ocmplu(_)
    )
}

fn csharp_int_const(value: i64) -> CsharpminorExpr {
    CsharpminorExpr::Econst(Constant::Ointconst(value))
}

fn binop_expr(op: CminorBinop, lhs: CsharpminorExpr, rhs: CsharpminorExpr) -> CsharpminorExpr {
    CsharpminorExpr::Ebinop(op, Box::new(lhs), Box::new(rhs))
}

fn add_offset_sized(expr: CsharpminorExpr, ofs: i64, is_64bit: bool) -> CsharpminorExpr {
    if ofs == 0 {
        expr
    } else {
        let add_op = if is_64bit { CminorBinop::Oaddl } else { CminorBinop::Oadd };
        let imm = if is_64bit {
            CsharpminorExpr::Econst(Constant::Olongconst(ofs))
        } else {
            csharp_int_const(ofs)
        };
        binop_expr(add_op, expr, imm)
    }
}

pub(crate) fn addressing_to_csharp_expr(
    addressing: &Addressing,
    args: &[RTLReg],
) -> Option<CsharpminorExpr> {
    addressing_to_csharp_expr_sized(addressing, args, false)
}

pub(crate) fn addressing_to_csharp_expr_sized(
    addressing: &Addressing,
    args: &[RTLReg],
    is_64bit: bool,
) -> Option<CsharpminorExpr> {
    let add_op = if is_64bit { CminorBinop::Oaddl } else { CminorBinop::Oadd };
    let mul_op = if is_64bit { CminorBinop::Omull } else { CminorBinop::Omul };
    let make_int = |v: i64| -> CsharpminorExpr {
        if is_64bit {
            CsharpminorExpr::Econst(Constant::Olongconst(v))
        } else {
            csharp_int_const(v)
        }
    };
    match addressing {
        Addressing::Aindexed(ofs) => {
            let base = args.first().copied().map(CsharpminorExpr::Evar);
            match base {
                Some(expr) => Some(add_offset_sized(expr, *ofs, is_64bit)),
                None => {
                    None
                }
            }
        }
        Addressing::Aindexed2(ofs) => {
            let lhs = args.get(0).copied().map(CsharpminorExpr::Evar);
            let rhs = args.get(1).copied().map(CsharpminorExpr::Evar);
            let combined = match (lhs, rhs) {
                (Some(l), Some(r)) => binop_expr(add_op, l, r),
                (Some(l), None) => l,
                (None, Some(r)) => r,
                (None, None) => {
                    warn!(
                        "[ERROR] Aindexed2({}) with no base args - invalid addressing mode",
                        ofs
                    );
                    return None;
                }
            };
            Some(add_offset_sized(combined, *ofs, is_64bit))
        }
        Addressing::Ascaled(scale, ofs) => {
            let base = args.first().copied().map(CsharpminorExpr::Evar)?;
            let scaled = if *scale == 1 {
                base
            } else {
                binop_expr(mul_op, base, make_int(*scale))
            };
            Some(add_offset_sized(scaled, *ofs, is_64bit))
        }
        Addressing::Aindexed2scaled(scale, ofs) => {
            let base = args.get(0).copied().map(CsharpminorExpr::Evar);
            let idx = args.get(1).copied().map(CsharpminorExpr::Evar);
            let scaled_idx = match idx {
                Some(expr) if *scale != 1 => binop_expr(mul_op, expr, make_int(*scale)),
                Some(expr) => expr,
                None => return None,
            };
            let combined = match base {
                Some(b) => binop_expr(add_op, b, scaled_idx),
                None => scaled_idx,
            };
            Some(add_offset_sized(combined, *ofs, is_64bit))
        }
        Addressing::Aglobal(ident, ofs) => {
            if *ident == 0 {
                None
            } else {
                Some(CsharpminorExpr::Econst(Constant::Oaddrsymbol(*ident, *ofs)))
            }
        }
        Addressing::Abased(ident, ofs) => {
            let base = CsharpminorExpr::Econst(Constant::Oaddrsymbol(*ident, *ofs));
            match args.first() {
                Some(reg) => Some(binop_expr(add_op, base, CsharpminorExpr::Evar(*reg))),
                None => Some(base),
            }
        }
        Addressing::Abasedscaled(scale, ident, ofs) => {
            let base = CsharpminorExpr::Econst(Constant::Oaddrsymbol(*ident, *ofs));
            match args.first() {
                Some(reg) => {
                    let idx = CsharpminorExpr::Evar(*reg);
                    let scaled = if *scale == 1 {
                        idx
                    } else {
                        binop_expr(mul_op, idx, make_int(*scale))
                    };
                    Some(binop_expr(add_op, base, scaled))
                }
                None => Some(base),
            }
        }
        Addressing::Ainstack(ofs) => Some(CsharpminorExpr::Econst(Constant::Oaddrstack(*ofs))),
        Addressing::Unknown => None,
    }
}

pub(crate) fn cast_call_args_to_signature_with_node(
    args: Vec<ClightExpr>,
    sig_opt: &Option<Signature>,
) -> Vec<ClightExpr> {
    let sig = match sig_opt {
        Some(_) => crate::x86::types::resolve_signature(sig_opt),
        None => return args,
    };

    if sig.sig_args.is_empty() {
        return args;
    }

    let expected_types: Vec<ClightType> = sig
        .sig_args
        .iter()
        .map(crate::x86::types::clight_type_from_xtype)
        .collect();

    let mut result = Vec::with_capacity(args.len().max(expected_types.len()));
    for (i, arg) in args.into_iter().enumerate() {
        if i < expected_types.len() {
            result.push(crate::x86::types::cast_expr_to_type(arg, expected_types[i].clone()));
        } else {
            // Preserve extra args for varargs; narrowed at C AST emission
            result.push(arg);
        }
    }
    for i in result.len()..expected_types.len() {
        result.push(crate::x86::types::default_expr_for_type(&expected_types[i]));
    }
    result
}

pub(crate) fn csharp_expr_from_cminor(expr: &CminorExpr) -> Option<CsharpminorExpr> {
    csharp_expr_from_cminor_sized(expr, false)
}

pub(crate) fn csharp_expr_from_cminor_sized(
    expr: &CminorExpr,
    load_addr_64bit: bool,
) -> Option<CsharpminorExpr> {
    match expr {
        CminorExpr::Evar(reg) => Some(CsharpminorExpr::Evar(*reg)),
        CminorExpr::Econst(cst) => Some(CsharpminorExpr::Econst(cst.clone())),
        CminorExpr::Eunop(op, reg) => Some(CsharpminorExpr::Eunop(
            op.clone(),
            Box::new(CsharpminorExpr::Evar(*reg)),
        )),
        CminorExpr::Ebinop(op, lhs, rhs) => Some(CsharpminorExpr::Ebinop(
            op.clone(),
            Box::new(CsharpminorExpr::Evar(*lhs)),
            Box::new(CsharpminorExpr::Evar(*rhs)),
        )),
        CminorExpr::Eop(op, args) => {
            if let Operation::Osel(cond, _typ) = op {
                if args.len() >= 2 {
                    let true_val = Box::new(CsharpminorExpr::Evar(args[0]));
                    let false_val = Box::new(CsharpminorExpr::Evar(args[1]));
                    let cond_expr = osel_condition_expr(cond, args);
                    return Some(CsharpminorExpr::Econdition(
                        Box::new(cond_expr),
                        true_val,
                        false_val,
                    ));
                }
            }
            match args.len() {
            0 => {
                if let Some(cst) = constant_from_operation(op) {
                    Some(CsharpminorExpr::Econst(cst))
                } else {
                    match op {
                        Operation::Olea(addr) => {
                            addressing_to_csharp_expr_sized(addr, args, false)
                        }
                        Operation::Oleal(addr) => {
                            addressing_to_csharp_expr_sized(addr, args, true)
                        }
                        _ => {
                            if let Some(imm) = immediate_from_operation(op) {
                                Some(csharp_int_const(imm))
                            } else {
                                None
                            }
                        }
                    }
                }
            }
            1 => {
                let arg = CsharpminorExpr::Evar(args[0]);
                if *op == Operation::Omove {
                    Some(arg)
                } else if let Some(unop) = unop_from_operation(op) {
                    Some(CsharpminorExpr::Eunop(unop, Box::new(arg)))
                } else if let Some((binop, imm)) = binop_imm_from_operation(op) {
                    let imm_expr = if is_long_binop(&binop) {
                        CsharpminorExpr::Econst(Constant::Olongconst(imm))
                    } else {
                        CsharpminorExpr::Econst(Constant::Ointconst(imm))
                    };
                    Some(CsharpminorExpr::Ebinop(
                        binop,
                        Box::new(arg),
                        Box::new(imm_expr),
                    ))
                } else if let Some((binop, imm, is_long)) = ocmp_imm_from_operation(op) {
                    use crate::x86::op::Condition;
                    let imm_expr = if is_long {
                        CsharpminorExpr::Econst(Constant::Olongconst(imm))
                    } else {
                        CsharpminorExpr::Econst(Constant::Ointconst(imm))
                    };
                    if let Operation::Ocmp(Condition::Cmaskzero(_)) = op {
                        let and_expr = CsharpminorExpr::Ebinop(
                            binop, Box::new(arg), Box::new(imm_expr),
                        );
                        Some(CsharpminorExpr::Ebinop(
                            CminorBinop::Ocmpu(Comparison::Ceq),
                            Box::new(and_expr),
                            Box::new(csharp_int_const(0)),
                        ))
                    } else if let Operation::Ocmp(Condition::Cmasknotzero(_)) = op {
                        let and_expr = CsharpminorExpr::Ebinop(
                            binop, Box::new(arg), Box::new(imm_expr),
                        );
                        Some(CsharpminorExpr::Ebinop(
                            CminorBinop::Ocmpu(Comparison::Cne),
                            Box::new(and_expr),
                            Box::new(csharp_int_const(0)),
                        ))
                    } else {
                        Some(CsharpminorExpr::Ebinop(
                            binop,
                            Box::new(arg),
                            Box::new(imm_expr),
                        ))
                    }
                } else {
                    match op {
                        Operation::Olea(addr) => {
                            addressing_to_csharp_expr_sized(addr, args, false)
                        }
                        Operation::Oleal(addr) => {
                            addressing_to_csharp_expr_sized(addr, args, true)
                        }
                        // Rotate right: (x >> n) | (x << (width - n))
                        Operation::Ororimm(n) => {
                            let n = *n;
                            Some(CsharpminorExpr::Ebinop(
                                CminorBinop::Oor,
                                Box::new(CsharpminorExpr::Ebinop(
                                    CminorBinop::Oshru,
                                    Box::new(arg.clone()),
                                    Box::new(csharp_int_const(n)),
                                )),
                                Box::new(CsharpminorExpr::Ebinop(
                                    CminorBinop::Oshl,
                                    Box::new(arg),
                                    Box::new(csharp_int_const(32 - n)),
                                )),
                            ))
                        }
                        Operation::Ororlimm(n) => {
                            let n = *n;
                            Some(CsharpminorExpr::Ebinop(
                                CminorBinop::Oorl,
                                Box::new(CsharpminorExpr::Ebinop(
                                    CminorBinop::Oshrlu,
                                    Box::new(arg.clone()),
                                    Box::new(CsharpminorExpr::Econst(Constant::Olongconst(n))),
                                )),
                                Box::new(CsharpminorExpr::Ebinop(
                                    CminorBinop::Oshll,
                                    Box::new(arg),
                                    Box::new(CsharpminorExpr::Econst(Constant::Olongconst(64 - n))),
                                )),
                            ))
                        }
                        _ => {
                            warn!(
                                "[ERROR] csharp_expr_from_cminor: unhandled 1-arg operation {:?} -- expression dropped",
                                op
                            );
                            None
                        }
                    }
                }
            }
            2 => {
                let lhs = CsharpminorExpr::Evar(args[0]);
                let rhs = CsharpminorExpr::Evar(args[1]);
                if let Some(binop) = binop_from_operation(op) {
                    Some(CsharpminorExpr::Ebinop(binop, Box::new(lhs), Box::new(rhs)))
                } else {
                    match op {
                        Operation::Olea(addr) => {
                            addressing_to_csharp_expr_sized(addr, args, false)
                        }
                        Operation::Oleal(addr) => {
                            addressing_to_csharp_expr_sized(addr, args, true)
                        }
                        _ => {
                            warn!(
                                "[ERROR] csharp_expr_from_cminor: unhandled 2-arg operation {:?} -- expression dropped",
                                op
                            );
                            None
                        }
                    }
                }
            }
            _ => match op {
                Operation::Olea(addr) => {
                    addressing_to_csharp_expr_sized(addr, args, false)
                }
                Operation::Oleal(addr) => {
                    addressing_to_csharp_expr_sized(addr, args, true)
                }
                _ => {
                    warn!(
                        "[ERROR] csharp_expr_from_cminor: unhandled {}-arg operation {:?} -- expression dropped",
                        args.len(), op
                    );
                    None
                }
            },
        }}
        CminorExpr::Eload(chunk, addr, args) => {
            let addr_expr = addressing_to_csharp_expr_sized(addr, args, load_addr_64bit)?;
            Some(CsharpminorExpr::Eload(chunk.clone(), Box::new(addr_expr)))
        }
        CminorExpr::Eexternal(func, _sig, _args) => {
            let value = i64::try_from(*func).ok()?;

            Some(csharp_int_const(value))
        }
    }
}

pub(crate) fn csharp_builtin_arg_from(arg: &BuiltinArg<RTLReg>) -> BuiltinArg<CsharpminorExpr> {
    match arg {
        BuiltinArg::BA(reg) => BuiltinArg::BA(CsharpminorExpr::Evar(*reg)),
        BuiltinArg::BAInt(v) => BuiltinArg::BAInt(*v),
        BuiltinArg::BALong(v) => BuiltinArg::BALong(*v),
        BuiltinArg::BAFloat(v) => BuiltinArg::BAFloat(*v),
        BuiltinArg::BASingle(v) => BuiltinArg::BASingle(*v),
        BuiltinArg::BALoadStack(chunk, ofs) => BuiltinArg::BALoadStack(chunk.clone(), *ofs),
        BuiltinArg::BAAddrStack(ofs) => BuiltinArg::BAAddrStack(*ofs),
        BuiltinArg::BALoadGlobal(chunk, ident, ofs) => {
            BuiltinArg::BALoadGlobal(chunk.clone(), *ident, *ofs)
        }
        BuiltinArg::BAAddrGlobal(ident, ofs) => BuiltinArg::BAAddrGlobal(*ident, *ofs),
        BuiltinArg::BASplitLong(lo, hi) => BuiltinArg::BASplitLong(
            Box::new(csharp_builtin_arg_from(lo)),
            Box::new(csharp_builtin_arg_from(hi)),
        ),
        BuiltinArg::BAAddPtr(lhs, rhs) => BuiltinArg::BAAddPtr(
            Box::new(csharp_builtin_arg_from(lhs)),
            Box::new(csharp_builtin_arg_from(rhs)),
        ),
    }
}

pub(crate) fn strip_version_suffix(sym: &str) -> Symbol {
    let clean = sym.split('@').next().unwrap_or(sym);
    Box::leak(clean.to_string().into_boxed_str())
}

pub(crate) fn collect_unique_struct_fields<'a>(
    input: impl Iterator<Item = (&'a i64, &'a Ident, &'a MemoryChunk)>,
) -> impl Iterator<Item = Arc<Vec<(i64, Ident, MemoryChunk)>>> {
    let mut seen = std::collections::HashSet::new();

    let mut fields = Vec::new();

    for (offset, name, chunk) in input {
        let key = (*offset, *name);

        if !seen.contains(&key) {
            seen.insert(key);

            fields.push((*offset, *name, chunk.clone()));
        }
    }
    fields.sort_by_key(|(off, _, _)| *off);

    std::iter::once(Arc::new(fields))
}

pub(crate) fn extract_var_reads_from_stmt(stmt: &ClightStmt) -> Vec<Ident> {
    let mut reads = Vec::new();
    extract_var_reads_from_stmt_recursive(stmt, &mut reads, 0);
    reads.sort();
    reads.dedup();
    reads
}
fn extract_var_reads_from_stmt_recursive(stmt: &ClightStmt, reads: &mut Vec<Ident>, depth: usize) {
    if depth > RECURSION_MAX_DEPTH {
        warn!(
            "[WARNING] extract_var_reads_from_stmt: Max recursion depth ({}) exceeded. Variable read analysis may be incomplete.",
            RECURSION_MAX_DEPTH
        );
        return;
    }
    match stmt {
        ClightStmt::Sskip => {}
        ClightStmt::Sassign(lhs, rhs) => {
            extract_var_reads_from_expr(lhs, reads);

            extract_var_reads_from_expr(rhs, reads);
        }
        ClightStmt::Sset(_id, expr) => {
            extract_var_reads_from_expr(expr, reads);
        }
        ClightStmt::Scall(_dst, func, args) => {
            extract_var_reads_from_expr(func, reads);

            for arg in args {
                extract_var_reads_from_expr(arg, reads);
            }
        }
        ClightStmt::Sbuiltin(_dst, _ef, _tyl, args) => {
            for arg in args {
                extract_var_reads_from_expr(arg, reads);
            }
        }
        ClightStmt::Ssequence(stmts) => {
            for s in stmts {
                extract_var_reads_from_stmt_recursive(s, reads, depth + 1);
            }
        }
        ClightStmt::Sifthenelse(cond, then_s, else_s) => {
            extract_var_reads_from_expr(cond, reads);

            extract_var_reads_from_stmt_recursive(then_s, reads, depth + 1);

            extract_var_reads_from_stmt_recursive(else_s, reads, depth + 1);
        }
        ClightStmt::Sloop(body, cont) => {
            extract_var_reads_from_stmt_recursive(body, reads, depth + 1);
            extract_var_reads_from_stmt_recursive(cont, reads, depth + 1);
        }
        ClightStmt::Sbreak => {}
        ClightStmt::Scontinue => {}
        ClightStmt::Sreturn(opt_expr) => {
            if let Some(expr) = opt_expr {
                extract_var_reads_from_expr(expr, reads);
            }
        }
        ClightStmt::Sswitch(expr, cases) => {
            extract_var_reads_from_expr(expr, reads);

            for (_label, case_stmt) in cases {
                extract_var_reads_from_stmt_recursive(case_stmt, reads, depth + 1);
            }
        }
        ClightStmt::Slabel(_lbl, body) => {
            extract_var_reads_from_stmt_recursive(body, reads, depth + 1);
        }
        ClightStmt::Sgoto(_lbl) => {}
    }
}

fn extract_var_reads_from_expr(expr: &ClightExpr, reads: &mut Vec<Ident>) {
    match expr {
        ClightExpr::EconstInt(_, _)
        | ClightExpr::EconstLong(_, _)
        | ClightExpr::EconstFloat(_, _)
        | ClightExpr::EconstSingle(_, _) => {}
        ClightExpr::Evar(id, _) => {
            reads.push(*id);
        }
        ClightExpr::Etempvar(id, _) => {
            reads.push(*id);
        }
        ClightExpr::Ederef(inner, _)
        | ClightExpr::Eaddrof(inner, _)
        | ClightExpr::Eunop(_, inner, _)
        | ClightExpr::Ecast(inner, _) => {
            extract_var_reads_from_expr(inner, reads);
        }
        ClightExpr::Ebinop(_, l, r, _) => {
            extract_var_reads_from_expr(l, reads);

            extract_var_reads_from_expr(r, reads);
        }
        ClightExpr::Efield(base, _field, _ty) => {
            extract_var_reads_from_expr(base, reads);
        }
        ClightExpr::Esizeof(_ty1, _ty2) | ClightExpr::Ealignof(_ty1, _ty2) => {}
        ClightExpr::EvarSymbol(_, _) => {}
        ClightExpr::Econdition(cond, true_val, false_val, _) => {
            extract_var_reads_from_expr(cond, reads);
            extract_var_reads_from_expr(true_val, reads);
            extract_var_reads_from_expr(false_val, reads);
        }
    }
}

pub(crate) fn extract_var_writes_from_stmt(stmt: &ClightStmt) -> Vec<Ident> {
    let mut writes = Vec::new();
    extract_var_writes_from_stmt_recursive(stmt, &mut writes, 0);
    writes.sort();
    writes.dedup();
    writes
}

fn extract_var_writes_from_stmt_recursive(
    stmt: &ClightStmt,
    writes: &mut Vec<Ident>,
    depth: usize,
) {
    if depth > RECURSION_MAX_DEPTH {
        warn!(
            "[WARNING] extract_var_writes_from_stmt: Max recursion depth ({}) exceeded. Variable write analysis may be incomplete.",
            RECURSION_MAX_DEPTH
        );

        return;
    }
    match stmt {
        ClightStmt::Sskip => {}
        ClightStmt::Sassign(_lhs, _rhs) => {}
        ClightStmt::Sset(id, _expr) => {
            writes.push(*id);
        }
        ClightStmt::Scall(dst, _func, _args) => {
            if let Some(id) = dst {
                writes.push(*id);
            }
        }
        ClightStmt::Sbuiltin(dst, _ef, _tyl, _args) => {
            if let Some(id) = dst {
                writes.push(*id);
            }
        }
        ClightStmt::Ssequence(stmts) => {
            for s in stmts {
                extract_var_writes_from_stmt_recursive(s, writes, depth + 1);
            }
        }
        ClightStmt::Sifthenelse(_cond, then_s, else_s) => {
            extract_var_writes_from_stmt_recursive(then_s, writes, depth + 1);

            extract_var_writes_from_stmt_recursive(else_s, writes, depth + 1);
        }
        ClightStmt::Sloop(body, cont) => {
            extract_var_writes_from_stmt_recursive(body, writes, depth + 1);
            extract_var_writes_from_stmt_recursive(cont, writes, depth + 1);
        }
        ClightStmt::Sbreak
        | ClightStmt::Scontinue
        | ClightStmt::Sreturn(_)
        | ClightStmt::Sgoto(_) => {}
        ClightStmt::Sswitch(_expr, cases) => {
            for (_label, case_stmt) in cases {
                extract_var_writes_from_stmt_recursive(case_stmt, writes, depth + 1);
            }
        }
        ClightStmt::Slabel(_lbl, body) => {
            extract_var_writes_from_stmt_recursive(body, writes, depth + 1);
        }
    }
}
