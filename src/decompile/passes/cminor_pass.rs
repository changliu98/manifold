use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::{declare_io_from, run_pass};

use crate::x86::op::{Addressing, Comparison, Condition, Operation, TestResultCondition};
use crate::x86::types::*;
use ascent::ascent_par;
use either::Either;
use log::warn;
use std::convert::TryFrom;
use std::sync::Arc;

ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct CminorPassProgram;


    relation rtl_inst(Node, RTLInst);
    // Final authoritative RTL plus the post-signature, dependency-compatible
    // width/chunk alternatives published by RTLSupersetPass.  Keep rtl_inst in
    // the union so focused relation tests and partial pipelines remain valid.
    relation rtl_inst_superset(Node, RTLInst);
    #[local] relation rtl_inst_for_cminor(Node, RTLInst);
    rtl_inst_for_cminor(node, inst.clone()) <-- rtl_inst(node, inst);
    rtl_inst_for_cminor(node, inst.clone()) <-- rtl_inst_superset(node, inst);
    relation rtl_succ(Node, Node);
    relation rtl_expansion_edge(Node, Node);
    #[local] relation rtl_expansion_member(Node);
    rtl_expansion_member(src) <-- rtl_expansion_edge(src, _);
    rtl_expansion_member(dst) <-- rtl_expansion_edge(_, dst);
    // rtl_succ is post-optimization, while rtl_expansion_edge records the
    // pre-optimization provenance. Nop collapse may retarget either endpoint;
    // membership carries that provenance onto the authoritative optimized
    // edge without using node ids as a reachability proxy.
    #[local] relation rtl_optimized_expansion_edge(Node, Node);
    rtl_optimized_expansion_edge(src, dst) <--
        rtl_succ(src, dst),
        rtl_expansion_member(src);
    rtl_optimized_expansion_edge(src, dst) <--
        rtl_succ(src, dst),
        rtl_expansion_member(dst);
    relation instr_in_function(Node, Address);
    relation func_stacksz(Address, Address, Symbol, u64);
    relation call_return_reg(Node, RTLReg);
    relation stack_var(Address, Address, i64, RTLReg);
    relation renderable_stack_addr_result(Node, i64, RTLReg);

    relation cminor_stmt(Node, CminorStmt);
    relation cminor_fallthrough(Node, Node);

    // Track nodes where Olea(Ainstack) was resolved to a stack address constant via stack_var.
    #[local] relation stack_addr_resolved(Node);

    // The RTL frame analysis owns coordinate normalization.  Consume its
    // definition-keyed handoff before the legacy raw-offset/stack_var path so
    // a BP-relative local rebased into the common frame coordinate does not
    // fall back to a literal integer address.
    cminor_stmt(node, stmt), stack_addr_resolved(node) <--
        rtl_inst_for_cminor(node, ?RTLInst::Iop(op, args, dst)),
        if matches!(op, Operation::Olea(Addressing::Ainstack(_)) | Operation::Oleal(Addressing::Ainstack(_))),
        if args.is_empty(),
        renderable_stack_addr_result(node, normalized_ofs, dst),
        let stmt = CminorStmt::Sassign(
            *dst,
            CminorExpr::Econst(Constant::Oaddrstack(*normalized_ofs)),
        );

    // Olea(Ainstack(ofs)) with a known stack variable -> Econst(Oaddrstack(ofs))
    cminor_stmt(node, stmt), stack_addr_resolved(node) <--
        rtl_inst_for_cminor(node, ?RTLInst::Iop(op, args, dst)),
        if let Operation::Olea(Addressing::Ainstack(ofs)) = op,
        if args.is_empty(),
        instr_in_function(node, func_start),
        stack_var(func_start, node, *ofs, _stack_rtl),
        let stmt = CminorStmt::Sassign(*dst, CminorExpr::Econst(Constant::Oaddrstack(*ofs)));

    // Oleal(Ainstack(ofs)) with a known stack variable -> Econst(Oaddrstack(ofs))
    cminor_stmt(node, stmt), stack_addr_resolved(node) <--
        rtl_inst_for_cminor(node, ?RTLInst::Iop(op, args, dst)),
        if let Operation::Oleal(Addressing::Ainstack(ofs)) = op,
        if args.is_empty(),
        instr_in_function(node, func_start),
        stack_var(func_start, node, *ofs, _stack_rtl),
        let stmt = CminorStmt::Sassign(*dst, CminorExpr::Econst(Constant::Oaddrstack(*ofs)));


    cminor_stmt(node, CminorStmt::Snop) <--
        rtl_inst_for_cminor(node, ?RTLInst::Iop(Operation::Omove, args, dst)),
        if args.len() == 1 && args[0] == *dst;

    cminor_stmt(node, stmt) <--
        rtl_inst_for_cminor(node, ?RTLInst::Iop(op, args, dst)),
        if !(*op == Operation::Omove && args.len() == 1 && args[0] == *dst),
        !stack_addr_resolved(node),
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
        rtl_inst_for_cminor(node, ?RTLInst::Iload(chunk, addr, args, dst)),
        let converted = CminorExpr::Eload(chunk.clone(), addr.clone(), args.clone()),
        let stmt = CminorStmt::Sassign(*dst, converted);

    cminor_stmt(node, stmt) <--
        rtl_inst_for_cminor(node, ?RTLInst::Istore(chunk, addr, args, src)),
        let stmt = CminorStmt::Sstore(chunk.clone(), addr.clone(), args.clone(), *src);

    cminor_stmt(node, stmt) <--
        rtl_inst_for_cminor(node, ?RTLInst::Ibuiltin(name, args, res)),
        let stmt = CminorStmt::Sbuiltin(None, name.clone(), args.clone(), res.clone());

    cminor_stmt(node, stmt) <--
        rtl_inst_for_cminor(node, ?RTLInst::Icond(cond, args, Either::Right(ifso), Either::Right(ifnot))),
        let stmt = CminorStmt::Sifthenelse(cond.clone(), args.clone(), *ifso, *ifnot);

    cminor_stmt(node, stmt) <--
        rtl_inst_for_cminor(node, ?RTLInst::Icond(cond, args, Either::Left(_sym), Either::Right(ifnot))),
        let stmt = CminorStmt::Sjump(*ifnot);

    cminor_stmt(node, stmt) <--
        rtl_inst_for_cminor(node, ?RTLInst::Icond(cond, args, Either::Right(ifso), Either::Left(_sym))),
        let stmt = CminorStmt::Sjump(*ifso);

    cminor_stmt(node, CminorStmt::Snop) <--
        rtl_inst_for_cminor(node, ?RTLInst::Icond(_, _, Either::Left(_), Either::Left(_)));

    cminor_stmt(node, stmt) <--
        rtl_inst_for_cminor(node, ?RTLInst::Ijumptable(arg, targets)),
        let stmt = CminorStmt::Sjumptable(*arg, targets.clone());

    cminor_stmt(node, stmt) <--
        rtl_inst_for_cminor(node, ?RTLInst::Ibranch(Either::Right(target))),
        let stmt = CminorStmt::Sjump(*target);

    cminor_stmt(node, CminorStmt::Sbuiltin(None, "__builtin_unreachable".to_string(), vec![], BuiltinArg::BAInt(0))) <--
        rtl_inst_for_cminor(node, ?RTLInst::Ibranch(Either::Left(_sym)));

    cminor_stmt(node, stmt) <--
        rtl_inst_for_cminor(node, ?RTLInst::Ireturn(opt)),
        let stmt = CminorStmt::Sreturn(*opt);

    cminor_stmt(node, CminorStmt::Snop) <--
        rtl_inst_for_cminor(node, RTLInst::Inop);


    cminor_stmt(node, stmt) <--
        rtl_inst_for_cminor(node, ?RTLInst::Icall(sig, callee, args, dst, _succ)),
        let stmt = CminorStmt::Scall(*dst, sig.clone(), callee.clone(), args.clone());


    cminor_stmt(node, stmt) <--
        rtl_inst_for_cminor(node, ?RTLInst::Itailcall(sig, callee, args)),
        let stmt = CminorStmt::Stailcall(sig.clone(), callee.clone(), args.clone());

    // Derive fallthrough from rtl_succ for synthetic nodes whose addresses break
    // sort order.  Both marker bits count: bit 63 tags the second synthetic node
    // of an expansion (util::SYNTH_NODE_BIT2) and is just as out of order as bit
    // 62, so testing only bit 62 left an expansion's last node with no
    // fallthrough edge to the following real instruction.
    cminor_fallthrough(node, next) <--
        rtl_succ(node, next),
        if (*node & ((1u64 << 62) | (1u64 << 63)) != 0)
            || (*next & ((1u64 << 62) | (1u64 << 63)) != 0),
        cminor_stmt(node, stmt),
        if matches!(stmt,
            CminorStmt::Sassign(_, _) | CminorStmt::Sstore(_, _, _, _) |
            CminorStmt::Sbuiltin(_, _, _, _) | CminorStmt::Scall(_, _, _, _) |
            CminorStmt::Snop),
        cminor_stmt(next, _),
        instr_in_function(node, func),
        instr_in_function(next, func);

    // Multi-stage expansions publish their sequencing explicitly.  Their node
    // ids need not fit the legacy two-bit synth namespace, and CFG consumers
    // must not infer reachability from an address mask.
    cminor_fallthrough(node, next) <--
        rtl_optimized_expansion_edge(node, next),
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
    fn name(&self) -> &'static str {
        "cminor"
    }

    fn run(&self, db: &mut DecompileDB) {
        run_pass!(db, CminorPassProgram);
    }

    declare_io_from!(CminorPassProgram);
}

#[cfg(test)]
mod expansion_cfg_tests {
    use super::{csharp_expr_from_cminor, CminorPassProgram};
    use crate::x86::op::{Addressing, Comparison, Operation, TestResultCondition};
    use crate::x86::types::{
        CminorBinop, CminorExpr, CminorStmt, Constant, CsharpminorExpr, MemoryChunk, RTLInst,
    };
    use std::sync::Arc;

    fn eval_test_expr(expr: &CsharpminorExpr, lhs: u64, rhs: u64) -> u64 {
        match expr {
            CsharpminorExpr::Evar(1) => lhs,
            CsharpminorExpr::Evar(2) => rhs,
            CsharpminorExpr::Econst(Constant::Ointconst(value)) => (*value as u32) as u64,
            CsharpminorExpr::Econst(Constant::Olongconst(value)) => *value as u64,
            CsharpminorExpr::Ebinop(op, left, right) => {
                let left = eval_test_expr(left, lhs, rhs);
                let right = eval_test_expr(right, lhs, rhs);
                match op {
                    CminorBinop::Oand => ((left as u32) & (right as u32)) as u64,
                    CminorBinop::Oxor => ((left as u32) ^ (right as u32)) as u64,
                    CminorBinop::Oshru => ((left as u32) >> ((right as u32) & 31)) as u64,
                    CminorBinop::Oandl => left & right,
                    CminorBinop::Oxorl => left ^ right,
                    CminorBinop::Oshrlu => left >> (right & 63),
                    CminorBinop::Ocmpu(Comparison::Ceq) | CminorBinop::Ocmplu(Comparison::Ceq) => {
                        u64::from(left == right)
                    }
                    CminorBinop::Ocmpu(Comparison::Cne) | CminorBinop::Ocmplu(Comparison::Cne) => {
                        u64::from(left != right)
                    }
                    other => panic!("unexpected TEST lowering operation {other:?}"),
                }
            }
            other => panic!("unexpected TEST lowering expression {other:?}"),
        }
    }

    #[test]
    fn normalized_frame_address_becomes_an_addrstack_constant() {
        let node = 0x200;
        let dst = 0x9000;
        let mut prog = CminorPassProgram::default();
        prog.rtl_inst.push((
            node,
            RTLInst::Iop(
                Operation::Oleal(Addressing::Ainstack(-80)),
                Arc::new(Vec::new()),
                dst,
            ),
        ));
        prog.renderable_stack_addr_result.push((node, 16, dst));

        prog.run();

        assert!(prog.cminor_stmt.iter().any(|fact| {
            fact == &(
                node,
                CminorStmt::Sassign(dst, CminorExpr::Econst(Constant::Oaddrstack(16))),
            )
        }));
    }

    #[test]
    fn dependency_compatible_subword_signedness_alternatives_both_reach_cminor() {
        let node = 0x240;
        let base = 1;
        let dst = 3;
        let args = Arc::new(vec![base]);
        let mut prog = CminorPassProgram::default();
        prog.rtl_inst.push((
            node,
            RTLInst::Iload(
                MemoryChunk::MInt8Unsigned,
                Addressing::Aindexed(4),
                args.clone(),
                dst,
            ),
        ));
        prog.rtl_inst_superset.extend([
            (
                node,
                RTLInst::Iload(
                    MemoryChunk::MInt8Unsigned,
                    Addressing::Aindexed(4),
                    args.clone(),
                    dst,
                ),
            ),
            (
                node,
                RTLInst::Iload(MemoryChunk::MInt8Signed, Addressing::Aindexed(4), args, dst),
            ),
        ]);

        prog.run();

        let statements: Vec<_> = prog
            .cminor_stmt
            .iter()
            .filter_map(|(candidate_node, stmt)| (*candidate_node == node).then_some(stmt))
            .collect();
        assert!(statements.iter().any(|stmt| matches!(
            stmt,
            CminorStmt::Sassign(
                reg,
                CminorExpr::Eload(
                    MemoryChunk::MInt8Unsigned,
                    Addressing::Aindexed(4),
                    load_args,
                )
            ) if *reg == dst && load_args.as_slice() == [base]
        )));
        assert!(statements.iter().any(|stmt| matches!(
            stmt,
            CminorStmt::Sassign(
                reg,
                CminorExpr::Eload(
                    MemoryChunk::MInt8Signed,
                    Addressing::Aindexed(4),
                    load_args,
                )
            ) if *reg == dst && load_args.as_slice() == [base]
        )));
    }

    #[test]
    fn retargeted_expansion_tail_uses_optimized_successor() {
        let tail = 0x900;
        let collapsed = 0x100;
        let live = 0x700;
        let func = 0x400;
        let mut prog = CminorPassProgram::default();
        prog.rtl_inst
            .extend([(tail, RTLInst::Inop), (live, RTLInst::Inop)]);
        prog.rtl_expansion_edge.push((tail, collapsed));
        prog.rtl_succ.push((tail, live));
        prog.instr_in_function.extend([(tail, func), (live, func)]);

        prog.run();

        assert!(prog
            .cminor_fallthrough
            .iter()
            .any(|fact| fact == &(tail, live)));
        assert!(!prog
            .cminor_fallthrough
            .iter()
            .any(|fact| fact == &(tail, collapsed)));
    }

    #[test]
    fn test_flags_lowering_preserves_zero_sign_and_low_byte_parity() {
        let predicates = [
            TestResultCondition::Zero,
            TestResultCondition::NonZero,
            TestResultCondition::Sign,
            TestResultCondition::NonSign,
            TestResultCondition::EvenParity,
            TestResultCondition::OddParity,
        ];
        let cases = [
            (0_u64, u32::MAX as u64, 25_u8),
            (0x8000_0000, u32::MAX as u64, 22),
            (0x0101_0101, u32::MAX as u64, 42),
            (u32::MAX as u64, 0x7fff_ffff, 26),
        ];

        for (lhs, rhs, packed) in cases {
            for (bit, predicate) in predicates.into_iter().enumerate() {
                let lowered = csharp_expr_from_cminor(&CminorExpr::Eop(
                    Operation::Otestflags(predicate, 4, 0),
                    Arc::new(vec![1, 2]),
                ))
                .expect("TEST predicate lowers");
                assert_eq!(
                    eval_test_expr(&lowered, lhs, rhs),
                    u64::from((packed >> bit) & 1),
                    "{predicate:?} for lhs={lhs:#x} rhs={rhs:#x}",
                );
            }
        }

        // PF observes only the low byte: 0x100 has even low-byte parity even
        // though the full word contains one set bit.
        let parity = csharp_expr_from_cminor(&CminorExpr::Eop(
            Operation::Otestflags(TestResultCondition::EvenParity, 4, 0),
            Arc::new(vec![1, 2]),
        ))
        .unwrap();
        assert_eq!(eval_test_expr(&parity, 0x100, u32::MAX as u64), 1);

        // A legacy high-byte mask view is shifted down before the byte-width
        // TEST semantics are applied.
        let high8_sign = csharp_expr_from_cminor(&CminorExpr::Eop(
            Operation::Otestflags(TestResultCondition::Sign, 1, 8),
            Arc::new(vec![1, 2]),
        ))
        .unwrap();
        assert_eq!(eval_test_expr(&high8_sign, 0x80, 0x8000), 1);
    }
}

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
        Operation::Odivimm(n) => Some(*n),
        Operation::Odivuimm(n) => Some(*n),
        Operation::Omodimm(n) => Some(*n),
        Operation::Omoduimm(n) => Some(*n),
        Operation::Odivlimm(n) => Some(*n),
        Operation::Odivluimm(n) => Some(*n),
        Operation::Omodlimm(n) => Some(*n),
        Operation::Omodluimm(n) => Some(*n),
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
        // Mask test (from TEST/AND + CMOV): (reg & mask) == 0 / != 0, mirroring the Ocmp(Cmask*) lowering.
        Condition::Cmaskzero(mask) if args.len() >= 3 => CsharpminorExpr::Ebinop(
            CminorBinop::Ocmpu(Comparison::Ceq),
            Box::new(CsharpminorExpr::Ebinop(
                CminorBinop::Oand,
                Box::new(CsharpminorExpr::Evar(args[2])),
                Box::new(CsharpminorExpr::Econst(Constant::Ointconst(*mask))),
            )),
            Box::new(CsharpminorExpr::Econst(Constant::Ointconst(0))),
        ),
        Condition::Cmasknotzero(mask) if args.len() >= 3 => CsharpminorExpr::Ebinop(
            CminorBinop::Ocmpu(Comparison::Cne),
            Box::new(CsharpminorExpr::Ebinop(
                CminorBinop::Oand,
                Box::new(CsharpminorExpr::Evar(args[2])),
                Box::new(CsharpminorExpr::Econst(Constant::Ointconst(*mask))),
            )),
            Box::new(CsharpminorExpr::Econst(Constant::Ointconst(0))),
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
        Operation::Odivimm(n) => Some((CminorBinop::Odiv, *n)),
        Operation::Odivuimm(n) => Some((CminorBinop::Odivu, *n)),
        Operation::Omodimm(n) => Some((CminorBinop::Omod, *n)),
        Operation::Omoduimm(n) => Some((CminorBinop::Omodu, *n)),
        Operation::Odivlimm(n) => Some((CminorBinop::Odivl, *n)),
        Operation::Odivluimm(n) => Some((CminorBinop::Odivlu, *n)),
        Operation::Omodlimm(n) => Some((CminorBinop::Omodl, *n)),
        Operation::Omodluimm(n) => Some((CminorBinop::Omodlu, *n)),
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
            Condition::Cmaskzero(n) => Some((CminorBinop::Oand, *n, false)),
            Condition::Cmasknotzero(n) => Some((CminorBinop::Oand, *n, false)),
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

fn csharp_binop(op: CminorBinop, lhs: CsharpminorExpr, rhs: CsharpminorExpr) -> CsharpminorExpr {
    CsharpminorExpr::Ebinop(op, Box::new(lhs), Box::new(rhs))
}

fn test_flags_constant(width: usize, value: i64) -> CsharpminorExpr {
    let constant = if width == 8 {
        Constant::Olongconst(value)
    } else {
        Constant::Ointconst(value)
    };
    CsharpminorExpr::Econst(constant)
}

/// Lower the exact flags produced by x86 TEST into side-effect-free unsigned
/// arithmetic.  Parity is the even/odd parity of the low byte only; folding
/// the whole word would disagree whenever upper bytes contain an odd number
/// of set bits.
fn test_flags_expr(
    predicate: TestResultCondition,
    width: usize,
    rhs_shift: usize,
    lhs: CsharpminorExpr,
    rhs: CsharpminorExpr,
) -> Option<CsharpminorExpr> {
    if !matches!(width, 1 | 2 | 4 | 8)
        || !matches!(rhs_shift, 0 | 8)
        || (rhs_shift == 8 && width != 1)
    {
        return None;
    }

    let (and_op, xor_op, shr_op, cmp_eq, cmp_ne) = if width == 8 {
        (
            CminorBinop::Oandl,
            CminorBinop::Oxorl,
            CminorBinop::Oshrlu,
            CminorBinop::Ocmplu(Comparison::Ceq),
            CminorBinop::Ocmplu(Comparison::Cne),
        )
    } else {
        (
            CminorBinop::Oand,
            CminorBinop::Oxor,
            CminorBinop::Oshru,
            CminorBinop::Ocmpu(Comparison::Ceq),
            CminorBinop::Ocmpu(Comparison::Cne),
        )
    };

    let rhs_lane = if rhs_shift == 0 {
        rhs
    } else {
        csharp_binop(
            shr_op.clone(),
            rhs,
            test_flags_constant(width, rhs_shift as i64),
        )
    };
    let tested = csharp_binop(and_op.clone(), lhs, rhs_lane);
    let width_mask = match width {
        1 => 0xff,
        2 => 0xffff,
        // -1 is the exact all-ones value after the selected 32/64-bit C cast.
        4 | 8 => -1,
        _ => unreachable!("validated TEST width"),
    };
    let tested = csharp_binop(
        and_op.clone(),
        tested,
        test_flags_constant(width, width_mask),
    );
    let zero = test_flags_constant(width, 0);

    match predicate {
        TestResultCondition::Zero => Some(csharp_binop(cmp_eq, tested, zero)),
        TestResultCondition::NonZero => Some(csharp_binop(cmp_ne, tested, zero)),
        TestResultCondition::Sign | TestResultCondition::NonSign => {
            let sign = csharp_binop(
                and_op.clone(),
                csharp_binop(
                    shr_op,
                    tested,
                    test_flags_constant(width, (width * 8 - 1) as i64),
                ),
                test_flags_constant(width, 1),
            );
            let cmp = if predicate == TestResultCondition::Sign {
                cmp_ne
            } else {
                cmp_eq
            };
            Some(csharp_binop(cmp, sign, zero))
        }
        TestResultCondition::EvenParity | TestResultCondition::OddParity => {
            let byte = csharp_binop(and_op.clone(), tested, test_flags_constant(width, 0xff));
            let fold4 = csharp_binop(
                xor_op.clone(),
                byte.clone(),
                csharp_binop(shr_op.clone(), byte, test_flags_constant(width, 4)),
            );
            let fold2 = csharp_binop(
                xor_op.clone(),
                fold4.clone(),
                csharp_binop(shr_op.clone(), fold4, test_flags_constant(width, 2)),
            );
            let fold1 = csharp_binop(
                xor_op,
                fold2.clone(),
                csharp_binop(shr_op, fold2, test_flags_constant(width, 1)),
            );
            let odd = csharp_binop(and_op, fold1, test_flags_constant(width, 1));
            let cmp = if predicate == TestResultCondition::EvenParity {
                cmp_eq
            } else {
                cmp_ne
            };
            Some(csharp_binop(cmp, odd, zero))
        }
    }
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
        let add_op = if is_64bit {
            CminorBinop::Oaddl
        } else {
            CminorBinop::Oadd
        };
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
    let add_op = if is_64bit {
        CminorBinop::Oaddl
    } else {
        CminorBinop::Oadd
    };
    let mul_op = if is_64bit {
        CminorBinop::Omull
    } else {
        CminorBinop::Omul
    };
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
                None => None,
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
            let expected = expected_types[i].clone();
            // &sym is intrinsically a pointer: never narrow to a sub-64-bit int param, which would truncate the address.
            if matches!(&arg, ClightExpr::Eaddrof(_, _))
                && matches!(&expected, ClightType::Tint(_, _, _))
            {
                result.push(arg);
            } else {
                result.push(crate::x86::types::cast_expr_to_type(arg, expected));
            }
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
                            let and_expr =
                                CsharpminorExpr::Ebinop(binop, Box::new(arg), Box::new(imm_expr));
                            Some(CsharpminorExpr::Ebinop(
                                CminorBinop::Ocmpu(Comparison::Ceq),
                                Box::new(and_expr),
                                Box::new(csharp_int_const(0)),
                            ))
                        } else if let Operation::Ocmp(Condition::Cmasknotzero(_)) = op {
                            let and_expr =
                                CsharpminorExpr::Ebinop(binop, Box::new(arg), Box::new(imm_expr));
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
                                        Box::new(CsharpminorExpr::Econst(Constant::Olongconst(
                                            64 - n,
                                        ))),
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
                            Operation::Otestflags(predicate, width, rhs_shift) => {
                                test_flags_expr(*predicate, *width, *rhs_shift, lhs, rhs)
                            }
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
                    Operation::Olea(addr) => addressing_to_csharp_expr_sized(addr, args, false),
                    Operation::Oleal(addr) => addressing_to_csharp_expr_sized(addr, args, true),
                    _ => {
                        warn!(
                        "[ERROR] csharp_expr_from_cminor: unhandled {}-arg operation {:?} -- expression dropped",
                        args.len(), op
                    );
                        None
                    }
                },
            }
        }
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
    // Ascent aggregator input order is non-deterministic. Collect everything, then sort by (offset, name, chunk) before dedup-by-(offset, name) so the chunk we keep for a given field is the same across runs.
    let mut all: Vec<(i64, Ident, MemoryChunk)> = input
        .map(|(offset, name, chunk)| (*offset, *name, chunk.clone()))
        .collect();
    all.sort();

    let mut fields = Vec::with_capacity(all.len());
    let mut seen = std::collections::HashSet::new();
    for tuple in all {
        let key = (tuple.0, tuple.1);
        if seen.insert(key) {
            fields.push(tuple);
        }
    }

    std::iter::once(Arc::new(fields))
}

pub(crate) fn extract_var_reads_from_stmt(stmt: &ClightStmt) -> Vec<Ident> {
    let mut reads = Vec::new();
    extract_var_reads_from_stmt_recursive(stmt, &mut reads);
    reads.sort();
    reads.dedup();
    reads
}
fn extract_var_reads_from_stmt_recursive(stmt: &ClightStmt, reads: &mut Vec<Ident>) {
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
                extract_var_reads_from_stmt_recursive(s, reads);
            }
        }
        ClightStmt::Sifthenelse(cond, then_s, else_s) => {
            extract_var_reads_from_expr(cond, reads);

            extract_var_reads_from_stmt_recursive(then_s, reads);

            extract_var_reads_from_stmt_recursive(else_s, reads);
        }
        ClightStmt::Sloop(body, cont) => {
            extract_var_reads_from_stmt_recursive(body, reads);
            extract_var_reads_from_stmt_recursive(cont, reads);
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
                extract_var_reads_from_stmt_recursive(case_stmt, reads);
            }
        }
        ClightStmt::Slabel(_lbl, body) => {
            extract_var_reads_from_stmt_recursive(body, reads);
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
    extract_var_writes_from_stmt_recursive(stmt, &mut writes);
    writes.sort();
    writes.dedup();
    writes
}

fn extract_var_writes_from_stmt_recursive(stmt: &ClightStmt, writes: &mut Vec<Ident>) {
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
                extract_var_writes_from_stmt_recursive(s, writes);
            }
        }
        ClightStmt::Sifthenelse(_cond, then_s, else_s) => {
            extract_var_writes_from_stmt_recursive(then_s, writes);

            extract_var_writes_from_stmt_recursive(else_s, writes);
        }
        ClightStmt::Sloop(body, cont) => {
            extract_var_writes_from_stmt_recursive(body, writes);
            extract_var_writes_from_stmt_recursive(cont, writes);
        }
        ClightStmt::Sbreak
        | ClightStmt::Scontinue
        | ClightStmt::Sreturn(_)
        | ClightStmt::Sgoto(_) => {}
        ClightStmt::Sswitch(_expr, cases) => {
            for (_label, case_stmt) in cases {
                extract_var_writes_from_stmt_recursive(case_stmt, writes);
            }
        }
        ClightStmt::Slabel(_lbl, body) => {
            extract_var_writes_from_stmt_recursive(body, writes);
        }
    }
}
