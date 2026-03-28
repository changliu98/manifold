// Asm to Mach: parses x86 assembly into Mach IR (reverses CompCert's x86/Asmgen.v).


use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::{declare_io_from, run_pass};

use std::sync::Arc;
use crate::x86::asm::{Freg, Ireg, Preg, TestCond};
use crate::x86::mach::Mreg;
use crate::x86::op::{Addressing, Comparison, Condition, Operation, F32};
use crate::x86::types::*;
use ascent::aggregators;
use ascent::ascent_par;
use ascent::Dual;
use either::Either;


ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct AsmPassProgram;

    relation arg_constrained_as_ptr(Node, RTLReg);
    relation base_ident_to_symbol(Ident, Symbol);
    relation block_in_function(Node, Address);
    relation call_arg_struct_ptr(Node, usize, usize);
    relation call_return_reg(Node, RTLReg);
    relation emit_clight_stmt(Address, Node, ClightStmt);
    relation emit_function_return_type_candidate(Address, ClightType);
    relation emit_goto_target(Address, Node);
    relation emit_ifthenelse_body(Address, Node, Node, bool);
    relation emit_loop_body(Address, Node, Node);
    relation emit_loop_exit(Address, Node, Node, Condition, Arc<Vec<CsharpminorExpr>>, Node, Node);
    relation emit_switch_chain(Address, Node, RTLReg);
    relation func_param_struct_type_candidate(Address, usize, usize);
    relation func_return_struct_type(Address, usize);
    relation global_struct_catalog(u64, usize, usize, usize);
    relation ident_to_symbol(Ident, Symbol);
    relation ifthenelse_merge_point(Address, Node, Node);
    relation instr_in_function(Node, Address);
    relation known_extern_signature(Symbol, usize, XType, Arc<Vec<XType>>);
    relation known_func_param_is_ptr(Symbol, usize);
    relation known_func_returns_float(Symbol);
    relation known_func_returns_int(Symbol);
    relation known_func_returns_long(Symbol);
    relation known_func_returns_ptr(Symbol);
    relation known_func_returns_single(Symbol);
    relation main_function(Address);
    relation reg_rtl(Node, Mreg, RTLReg);
    relation reg_xtl(Node, Mreg, RTLReg);
    relation stack_var(Address, Address, i64, RTLReg);
    relation string_data(String, String, usize);
    relation struct_field(u64, i64, String, MemoryChunk);
    relation struct_id_to_canonical(usize, usize);

    relation block_in_function(Node, Address);
    relation instr_in_function(Node, Address);


    relation preg_of(Mreg, Preg);
    relation ireg_of(Preg, Ireg);
    relation freg_of(Preg, Freg);
    relation low_ireg(Ireg);

    low_ireg(Ireg::RAX);
    low_ireg(Ireg::RBX);
    low_ireg(Ireg::RCX);
    low_ireg(Ireg::RDX);


    preg_of(Mreg::AX, Preg::Ir(Ireg::RAX));
    preg_of(Mreg::BX, Preg::Ir(Ireg::RBX));
    preg_of(Mreg::CX, Preg::Ir(Ireg::RCX));
    preg_of(Mreg::DX, Preg::Ir(Ireg::RDX));
    preg_of(Mreg::SI, Preg::Ir(Ireg::RSI));
    preg_of(Mreg::DI, Preg::Ir(Ireg::RDI));
    preg_of(Mreg::BP, Preg::Ir(Ireg::RBP));
    preg_of(Mreg::R8, Preg::Ir(Ireg::R8));
    preg_of(Mreg::R9, Preg::Ir(Ireg::R9));
    preg_of(Mreg::R10, Preg::Ir(Ireg::R10));
    preg_of(Mreg::R11, Preg::Ir(Ireg::R11));
    preg_of(Mreg::R12, Preg::Ir(Ireg::R12));
    preg_of(Mreg::R13, Preg::Ir(Ireg::R13));
    preg_of(Mreg::R14, Preg::Ir(Ireg::R14));
    preg_of(Mreg::R15, Preg::Ir(Ireg::R15));

    preg_of(Mreg::X0, Preg::Fr(Freg::XMM0));
    preg_of(Mreg::X1, Preg::Fr(Freg::XMM1));
    preg_of(Mreg::X2, Preg::Fr(Freg::XMM2));
    preg_of(Mreg::X3, Preg::Fr(Freg::XMM3));
    preg_of(Mreg::X4, Preg::Fr(Freg::XMM4));
    preg_of(Mreg::X5, Preg::Fr(Freg::XMM5));
    preg_of(Mreg::X6, Preg::Fr(Freg::XMM6));
    preg_of(Mreg::X7, Preg::Fr(Freg::XMM7));
    preg_of(Mreg::X8, Preg::Fr(Freg::XMM8));
    preg_of(Mreg::X9, Preg::Fr(Freg::XMM9));
    preg_of(Mreg::X10, Preg::Fr(Freg::XMM10));
    preg_of(Mreg::X11, Preg::Fr(Freg::XMM11));
    preg_of(Mreg::X12, Preg::Fr(Freg::XMM12));
    preg_of(Mreg::X13, Preg::Fr(Freg::XMM13));
    preg_of(Mreg::X14, Preg::Fr(Freg::XMM14));
    preg_of(Mreg::X15, Preg::Fr(Freg::XMM15));

    preg_of(Mreg::FP0, Preg::ST0);


    ireg_of(Preg::Ir(Ireg::RAX), Ireg::RAX);
    ireg_of(Preg::Ir(Ireg::RBX), Ireg::RBX);
    ireg_of(Preg::Ir(Ireg::RCX), Ireg::RCX);
    ireg_of(Preg::Ir(Ireg::RDX), Ireg::RDX);
    ireg_of(Preg::Ir(Ireg::RSI), Ireg::RSI);
    ireg_of(Preg::Ir(Ireg::RDI), Ireg::RDI);
    ireg_of(Preg::Ir(Ireg::RBP), Ireg::RBP);
    ireg_of(Preg::Ir(Ireg::RSP), Ireg::RSP);
    ireg_of(Preg::Ir(Ireg::R8), Ireg::R8);
    ireg_of(Preg::Ir(Ireg::R9), Ireg::R9);
    ireg_of(Preg::Ir(Ireg::R10), Ireg::R10);
    ireg_of(Preg::Ir(Ireg::R11), Ireg::R11);
    ireg_of(Preg::Ir(Ireg::R12), Ireg::R12);
    ireg_of(Preg::Ir(Ireg::R13), Ireg::R13);
    ireg_of(Preg::Ir(Ireg::R14), Ireg::R14);
    ireg_of(Preg::Ir(Ireg::R15), Ireg::R15);

    freg_of(Preg::Fr(Freg::XMM0), Freg::XMM0);
    freg_of(Preg::Fr(Freg::XMM1), Freg::XMM1);
    freg_of(Preg::Fr(Freg::XMM2), Freg::XMM2);
    freg_of(Preg::Fr(Freg::XMM3), Freg::XMM3);
    freg_of(Preg::Fr(Freg::XMM4), Freg::XMM4);
    freg_of(Preg::Fr(Freg::XMM5), Freg::XMM5);
    freg_of(Preg::Fr(Freg::XMM6), Freg::XMM6);
    freg_of(Preg::Fr(Freg::XMM7), Freg::XMM7);
    freg_of(Preg::Fr(Freg::XMM8), Freg::XMM8);
    freg_of(Preg::Fr(Freg::XMM9), Freg::XMM9);
    freg_of(Preg::Fr(Freg::XMM10), Freg::XMM10);
    freg_of(Preg::Fr(Freg::XMM11), Freg::XMM11);
    freg_of(Preg::Fr(Freg::XMM12), Freg::XMM12);
    freg_of(Preg::Fr(Freg::XMM13), Freg::XMM13);
    freg_of(Preg::Fr(Freg::XMM14), Freg::XMM14);
    freg_of(Preg::Fr(Freg::XMM15), Freg::XMM15);

    relation isst0(Preg, Mreg);
    isst0(Preg::ST0, Mreg::FP0);


    relation symbols(Address, Symbol, Symbol);
    relation symbol_size(Address, usize, Symbol);
    relation builtins(Symbol);

    relation func_entry(Symbol, Address);

    relation next(Address, Address);
    relation op_register(Symbol, &'static str);
    relation op_fp_immediate(Symbol, usize);
    relation op_immediate(Symbol, i64, usize);
    relation block_boundaries(Address, Address, Address);
    relation reg_use(Address, Mreg);
    relation reg_def(Address, Mreg);
    relation reg_def_used(Address, Mreg, Address);

    relation stack_def(Address, Symbol, i64);
    relation stack_use(Address, Symbol, i64);
    relation stack_def_used(Address, Symbol, i64, Address, Symbol, i64);

    relation flags_and_jump_pair(Address, Address, &'static str);

    relation op_indirect(Symbol, &'static str, &'static str, &'static str, i64, i64, usize);

    relation code_in_block(Address, Address);

    relation block(Address);

    relation probability(Symbol, Symbol, F32);

    relation ddisasm_cfg_edge(Address, Address, Symbol);

    relation direct_call(Address, Address);

    relation ddisasm_function_entry(Address);

    relation direct_jump(Address, Address);

    relation stack_base_move(Address, Symbol, Symbol);

    // A function has a frame pointer (mov rsp,rbp); when BP is not the frame pointer, BP-relative accesses are regular loads/stores.
    #[local] relation func_has_frame_pointer(Address);
    func_has_frame_pointer(func) <--
        stack_base_move(addr, src, dst),
        if *src == "RSP" && *dst == "RBP",
        instr_in_function(addr, func);

    instr_in_function(addr, func)<--
        block_in_function(blockaddr, func),
        code_in_block(addr, blockaddr);

    instr_in_function(next_addr, func) <--
        instr_in_function(addr, func),
        next(addr, next_addr),
        func_span(_, func, end_addr),
        if *next_addr > *addr,
        if *next_addr < *end_addr,
        !ddisasm_function_entry(*next_addr),
        if *next_addr != *func;


    relation reg_x64(Symbol);
    relation jump_instr(Symbol);
    relation printasm_mnemonic(&'static str, &'static str);

    relation pcast(Address, Symbol, Symbol);
    pcast(addr, dst, src) <--
        instruction(addr, _, _, "CQO", src, dst, _, _, _, _);
    pcast(addr, dst, src) <--
        instruction(addr, _, _, "CDQ", src, dst, _, _, _, _);
    pcast(addr, dst, src) <--
        instruction(addr, _, _, "CWD", src, dst, _, _, _, _);


    relation pmov(Address, Symbol, Symbol);
    relation pmovzx(Address, Symbol, Symbol);
    pmov(addr, dst, src)<--
        instruction(addr, _, _, "MOV", src, dst, _, _, _, _);

    pmov(addr, dst, src)<--
        instruction(addr, _, _, "MOVZX", src, dst, _, _, _, _);

    pmov(addr, dst, src) <--
        instruction(addr, _, _, "MOVSX", src, dst, _, _, _, _);
    pmov(addr, dst, src) <--
        instruction(addr, _, _, "MOVSXD", src, dst, _, _, _, _);

    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVAPS", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVAPS", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVUPS", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVUPS", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVDQA", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVDQA", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVDQU", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVDQU", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVQ", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVQ", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVSD", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVSD", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVSS", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "VMOVSS", src, dst, _, _, _, _);
    pmov(addr, dst, src) <-- instruction(addr, _, _, "MOVABS", src, dst, _, _, _, _);


    relation pand(Address, Symbol, Symbol);
    pand(addr, dst, src)<--
        instruction(addr, _, _, "AND", src, dst, _, _, _, _);

    relation psetcc(Address, TestCond, Symbol);
    psetcc(addr, TestCond::CondNp, dst)<--
        instruction(addr, _, _, "SETNP", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondP, dst)<--
        instruction(addr, _, _, "SETP", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondE, dst)<--
        instruction(addr, _, _, "SETE", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondNe, dst)<--
        instruction(addr, _, _, "SETNE", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondB, dst)<--
        instruction(addr, _, _, "SETB", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondBe, dst)<--
        instruction(addr, _, _, "SETBE", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondAe, dst)<--
        instruction(addr, _, _, "SETAE", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondA, dst)<--
        instruction(addr, _, _, "SETA", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondL, dst)<--
        instruction(addr, _, _, "SETL", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondLe, dst)<--
        instruction(addr, _, _, "SETLE", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondGe, dst)<--
        instruction(addr, _, _, "SETGE", dst, _, _, _, _, _);

    psetcc(addr, TestCond::CondG, dst)<--
        instruction(addr, _, _, "SETG", dst, _, _, _, _, _);

    relation pxor(Address, Symbol, Symbol);
    pxor(addr, dst, src)<--
        instruction(addr, _, _, "XOR", src, dst, _, _, _, _);
    
    pxor(addr, dst, src)<--
        instruction(addr, _, _, "XORL", src, dst, _, _, _, _);

    relation por(Address, Symbol, Symbol);
    por(addr, dst, src)<--
        instruction(addr, _, _, "OR", src, dst, _, _, _, _);

    relation pneg(Address, Symbol);
    pneg(addr, dst)<--
        instruction(addr, _, _, "NEG", dst, _, _, _, _, _);

    relation psub(Address, Symbol, Symbol);
    psub(addr, dst, src)<--
        instruction(addr, _, _, "SUB", src, dst, _, _, _, _);

    relation padd(Address, Symbol, Symbol);
    padd(addr, dst, src)<--
        instruction(addr, _, _, "ADD", src, dst, _, _, _, _);

    relation pjcc(Address, TestCond, Symbol);
    pjcc(addr, TestCond::CondNp, dst)<--
        instruction(addr, _, _, "JNP", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondP, dst)<--
        instruction(addr, _, _, "JP", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondE, dst)<--
        instruction(addr, _, _, "JE", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondNe, dst)<--
        instruction(addr, _, _, "JNE", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondB, dst)<--
        instruction(addr, _, _, "JB", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondBe, dst)<--
        instruction(addr, _, _, "JBE", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondAe, dst)<--
        instruction(addr, _, _, "JAE", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondA, dst)<--
        instruction(addr, _, _, "JA", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondL, dst)<--
        instruction(addr, _, _, "JL", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondLe, dst)<--
        instruction(addr, _, _, "JLE", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondGe, dst)<--
        instruction(addr, _, _, "JGE", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondG, dst)<--
        instruction(addr, _, _, "JG", dst, _, _, _, _, _);

    relation pcmp(Address, Symbol, Symbol);
    pcmp(addr, dst, src)<--
        instruction(addr, _, _, "CMP", src, dst, _, _, _, _);

    #[local] relation pcmov(Address, TestCond, Symbol, Symbol);

    pcmov(addr, TestCond::CondE, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVE" || *inst == "CMOVZ";

    pcmov(addr, TestCond::CondNe, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVNE" || *inst == "CMOVNZ";

    pcmov(addr, TestCond::CondB, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVB" || *inst == "CMOVC" || *inst == "CMOVNAE";

    pcmov(addr, TestCond::CondAe, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVAE" || *inst == "CMOVNC" || *inst == "CMOVNB";

    pcmov(addr, TestCond::CondBe, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVBE" || *inst == "CMOVNA";

    pcmov(addr, TestCond::CondA, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVA" || *inst == "CMOVNBE";

    pcmov(addr, TestCond::CondL, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVL" || *inst == "CMOVNGE";

    pcmov(addr, TestCond::CondGe, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVGE" || *inst == "CMOVNL";

    pcmov(addr, TestCond::CondLe, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVLE" || *inst == "CMOVNG";

    pcmov(addr, TestCond::CondG, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVG" || *inst == "CMOVNLE";

    pcmov(addr, TestCond::CondP, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVP" || *inst == "CMOVPE";

    pcmov(addr, TestCond::CondNp, dst, src) <--
        instruction(addr, _, _, inst, src, dst, _, _, _, _),
        if *inst == "CMOVNP" || *inst == "CMOVPO";

    relation pconvert(Address, Symbol, Symbol);
    pconvert(addr, dst, src)<--
        instruction(addr, _, _, inst_str, src, dst, _, _, _, _),
        if inst_str.starts_with("CVT");

    relation pmul(Address, Symbol);
    pmul(addr, dst)<--
        instruction(addr, _, _, "IMUL", dst, "0", _, _, _, _);
    pmul(addr, dst)<--
        instruction(addr, _, _, "MUL", dst, "0", _, _, _, _);

    relation pimul(Address, Symbol, Symbol);
    pimul(addr, dst, src)<--
        instruction(addr, _, _, "IMUL", src, dst, _, _, _, _),
        if *dst != "0";

    relation ppush(Address, Symbol);
    ppush(addr, src)<--
        instruction(addr, _, _, "PUSH", src, _, _, _, _, _);

    relation ppop(Address, Symbol);
    ppop(addr, dst)<--
        instruction(addr, _, _, "POP", dst, _, _, _, _, _);

    relation pidiv(Address, Symbol, Symbol);
    pidiv(addr, src, dst)<--
        instruction(addr, _, _, "IDIV", src, dst, _, _, _, _);

    relation pudiv(Address, Symbol, Symbol);
    pudiv(addr, src, dst)<--
        instruction(addr, _, _, "DIV", src, dst, _, _, _, _);

    relation pdiv(Address, Symbol, Symbol);
    pdiv(addr, src, dst) <-- pidiv(addr, src, dst);
    pdiv(addr, src, dst) <-- pudiv(addr, src, dst);

    relation pnot(Address, Symbol);
    pnot(addr, dst)<--
        instruction(addr, _, _, "NOT", dst, _, _, _, _, _);

    relation psal(Address, Symbol, Symbol);
    psal(addr, dst, src)<--
        instruction(addr, _, _, "SAL", src, dst, _, _, _, _);
    psal(addr, dst, src)<--
        instruction(addr, _, _, "SHL", src, dst, _, _, _, _);

    relation psar(Address, Symbol, Symbol);
    psar(addr, dst, src)<--
        instruction(addr, _, _, "SAR", src, dst, _, _, _, _);

    relation pshr(Address, Symbol, Symbol);
    pshr(addr, dst, src)<--
        instruction(addr, _, _, "SHR", src, dst, _, _, _, _);

    relation pror(Address, Symbol, Symbol);
    pror(addr, dst, src)<--
        instruction(addr, _, _, "ROR", src, dst, _, _, _, _);

    relation prol(Address, Symbol, Symbol);
    prol(addr, dst, src)<--
        instruction(addr, _, _, "ROL", src, dst, _, _, _, _);

    relation pin(Address, Symbol, Symbol);
    pin(addr, dst, src)<--
        instruction(addr, _, _, "IN", src, dst, _, _, _, _);

    relation pout(Address, Symbol, Symbol);
    pout(addr, dst, src)<--
        instruction(addr, _, _, "OUT", src, dst, _, _, _, _);


    relation pmovsd(Address, Symbol, Symbol);
    pmovsd(addr, dst, src)<--
        instruction(addr, _, _, "MOVSD", src, dst, _, _, _, _);
    pmovsd(addr, dst, src)<--
        instruction(addr, _, _, "VMOVSD", src, dst, _, _, _, _);

    relation ppxor(Address, Symbol, Symbol);
    ppxor(addr, dst, src)<--
        instruction(addr, _, _, "PXOR", src, dst, _, _, _, _);
    ppxor(addr, dst, src)<--
        instruction(addr, _, _, "VPXOR", src, dst, _, _, _, _);

    relation pcvtsi2sd(Address, Symbol, Symbol);
    pcvtsi2sd(addr, dst, src)<--
        instruction(addr, _, _, mnemonic, src, dst, _, _, _, _),
        if mnemonic.starts_with("CVTSI2SD") || mnemonic.starts_with("VCVTSI2SD");

    relation pcvtsd2si(Address, Symbol, Symbol);
    pcvtsd2si(addr, dst, src)<--
        instruction(addr, _, _, mnemonic, src, dst, _, _, _, _),
        if mnemonic.starts_with("CVTSD2SI") || mnemonic.starts_with("CVTTSD2SI")
           || mnemonic.starts_with("VCVTSD2SI") || mnemonic.starts_with("VCVTTSD2SI");

    relation paddsd(Address, Symbol, Symbol);
    paddsd(addr, dst, src)<--
        instruction(addr, _, _, "ADDSD", src, dst, _, _, _, _);

    relation psubsd(Address, Symbol, Symbol);
    psubsd(addr, dst, src)<--
        instruction(addr, _, _, "SUBSD", src, dst, _, _, _, _);

    relation pmulsd(Address, Symbol, Symbol);
    pmulsd(addr, dst, src)<--
        instruction(addr, _, _, "MULSD", src, dst, _, _, _, _);

    relation pdivsd(Address, Symbol, Symbol);
    pdivsd(addr, dst, src)<--
        instruction(addr, _, _, "DIVSD", src, dst, _, _, _, _);

    relation pucomisd(Address, Symbol, Symbol);
    pucomisd(addr, dst, src)<--
        instruction(addr, _, _, "UCOMISD", src, dst, _, _, _, _);
    pucomisd(addr, dst, src)<--
        instruction(addr, _, _, "COMISD", src, dst, _, _, _, _);
    pucomisd(addr, dst, src)<--
        instruction(addr, _, _, "VUCOMISD", src, dst, _, _, _, _);
    pucomisd(addr, dst, src)<--
        instruction(addr, _, _, "VCOMISD", src, dst, _, _, _, _);

    relation pucomiss(Address, Symbol, Symbol);
    pucomiss(addr, dst, src)<--
        instruction(addr, _, _, "UCOMISS", src, dst, _, _, _, _);
    pucomiss(addr, dst, src)<--
        instruction(addr, _, _, "COMISS", src, dst, _, _, _, _);
    pucomiss(addr, dst, src)<--
        instruction(addr, _, _, "VUCOMISS", src, dst, _, _, _, _);
    pucomiss(addr, dst, src)<--
        instruction(addr, _, _, "VCOMISS", src, dst, _, _, _, _);

    relation paddss(Address, Symbol, Symbol);
    paddss(addr, dst, src)<--
        instruction(addr, _, _, "ADDSS", src, dst, _, _, _, _);

    relation psubss(Address, Symbol, Symbol);
    psubss(addr, dst, src)<--
        instruction(addr, _, _, "SUBSS", src, dst, _, _, _, _);

    relation pmulss(Address, Symbol, Symbol);
    pmulss(addr, dst, src)<--
        instruction(addr, _, _, "MULSS", src, dst, _, _, _, _);

    relation pdivss(Address, Symbol, Symbol);
    pdivss(addr, dst, src)<--
        instruction(addr, _, _, "DIVSS", src, dst, _, _, _, _);

    relation pcvtsd2ss(Address, Symbol, Symbol);
    pcvtsd2ss(addr, dst, src)<--
        instruction(addr, _, _, mnemonic, src, dst, _, _, _, _),
        if *mnemonic == "CVTSD2SS" || *mnemonic == "VCVTSD2SS";

    relation pcvtss2sd(Address, Symbol, Symbol);
    pcvtss2sd(addr, dst, src)<--
        instruction(addr, _, _, mnemonic, src, dst, _, _, _, _),
        if *mnemonic == "CVTSS2SD" || *mnemonic == "VCVTSS2SD";

    relation pcvtsi2ss(Address, Symbol, Symbol);
    pcvtsi2ss(addr, dst, src)<--
        instruction(addr, _, _, mnemonic, src, dst, _, _, _, _),
        if mnemonic.starts_with("CVTSI2SS") || mnemonic.starts_with("VCVTSI2SS");

    relation pcvtss2si(Address, Symbol, Symbol);
    pcvtss2si(addr, dst, src)<--
        instruction(addr, _, _, mnemonic, src, dst, _, _, _, _),
        if mnemonic.starts_with("CVTSS2SI") || mnemonic.starts_with("CVTTSS2SI")
           || mnemonic.starts_with("VCVTSS2SI") || mnemonic.starts_with("VCVTTSS2SI");

    relation pxorpd(Address, Symbol, Symbol);
    pxorpd(addr, dst, src)<--
        instruction(addr, _, _, "XORPD", src, dst, _, _, _, _);
    pxorpd(addr, dst, src)<--
        instruction(addr, _, _, "VXORPD", src, dst, _, _, _, _);

    relation pandpd(Address, Symbol, Symbol);
    pandpd(addr, dst, src)<--
        instruction(addr, _, _, "ANDPD", src, dst, _, _, _, _);
    pandpd(addr, dst, src)<--
        instruction(addr, _, _, "VANDPD", src, dst, _, _, _, _);

    relation pxorps(Address, Symbol, Symbol);
    pxorps(addr, dst, src)<--
        instruction(addr, _, _, "XORPS", src, dst, _, _, _, _);
    pxorps(addr, dst, src)<--
        instruction(addr, _, _, "VXORPS", src, dst, _, _, _, _);

    relation pandps(Address, Symbol, Symbol);
    pandps(addr, dst, src)<--
        instruction(addr, _, _, "ANDPS", src, dst, _, _, _, _);
    pandps(addr, dst, src)<--
        instruction(addr, _, _, "VANDPS", src, dst, _, _, _, _);

    relation pmaxsd(Address, Symbol, Symbol);
    pmaxsd(addr, dst, src)<--
        instruction(addr, _, _, "MAXSD", src, dst, _, _, _, _);
    pmaxsd(addr, dst, src)<--
        instruction(addr, _, _, "VMAXSD", src, dst, _, _, _, _);

    relation pminsd(Address, Symbol, Symbol);
    pminsd(addr, dst, src)<--
        instruction(addr, _, _, "MINSD", src, dst, _, _, _, _);
    pminsd(addr, dst, src)<--
        instruction(addr, _, _, "VMINSD", src, dst, _, _, _, _);

    relation pmovss(Address, Symbol, Symbol);
    pmovss(addr, dst, src)<--
        instruction(addr, _, _, "MOVSS", src, dst, _, _, _, _);
    pmovss(addr, dst, src)<--
        instruction(addr, _, _, "VMOVSS", src, dst, _, _, _, _);

    relation pswap(Address, Symbol);
    pswap(addr, dst)<--
        instruction(addr, _, _, "BSWAP", dst, _, _, _, _, _);

    relation plabel(Address, Symbol);


    relation pjcc2(Address, TestCond, TestCond, Symbol);
    pjcc2(addr, c1, c2, label) <--
        pjcc(addr2, c2, dummplabel),
        cond_neg(cond1, c1),
        next(addr2, addr3),
        plabel(addr3, dummplabel),
        pjcc(addr, cond1, label),
        next(addr, addr1);

    relation pret(Address);
    pret(addr) <--
        instruction(addr, _, _, "RET", _, _, _, _, _, _);

    relation pnop(Address);
    pnop(addr) <--
        instruction(addr, _, _, "NOP", _, _, _, _, _, _);

    relation pendbr64(Address);
    pendbr64(addr) <--
        instruction(addr, _, _, "ENDBR64", _, _, _, _, _, _);

    relation phlt(Address);
    phlt(addr) <--
        instruction(addr, _, _, "HLT", _, _, _, _, _, _);

    relation ptest(Address, Symbol, Symbol);
    ptest(addr, dst, src) <--
        instruction(addr, _, _, "TEST", src, dst, _, _, _, _);

    // TEST reg, reg is semantically CMP reg, 0: emit pcmp with a synthesized zero immediate
    pcmp(addr, dst, zero_sym), op_immediate(zero_sym, 0, 0) <--
        ptest(addr, dst, src),
        op_register(dst, r1),
        op_register(src, r2),
        if r1 == r2,
        let zero_sym = Box::leak(format!("__test_zero_{:x}", addr).into_boxed_str()) as &'static str;

    relation pbsr(Address, Symbol, Symbol);
    pbsr(addr, dst, src) <--
        instruction(addr, _, _, "BSR", src, dst, _, _, _, _);

    relation pbsf(Address, Symbol, Symbol);
    pbsf(addr, dst, src) <--
        instruction(addr, _, _, "BSF", src, dst, _, _, _, _);

    relation psqrt(Address, Symbol, Symbol);
    psqrt(addr, dst, src) <--
        instruction(addr, _, _, "SQRTSD", src, dst, _, _, _, _);
    psqrt(addr, dst, src) <--
        instruction(addr, _, _, "VSQRTSD", src, dst, _, _, _, _);

    relation psqrtss(Address, Symbol, Symbol);
    psqrtss(addr, dst, src) <--
        instruction(addr, _, _, "SQRTSS", src, dst, _, _, _, _);
    psqrtss(addr, dst, src) <--
        instruction(addr, _, _, "VSQRTSS", src, dst, _, _, _, _);

    relation psqrtsd(Address, Symbol, Symbol);
    psqrtsd(addr, res, a1) <--
        instruction(addr, _, _, "SQRTPD", a1, res, _, _, _, _);
    psqrtsd(addr, res, a1) <--
        instruction(addr, _, _, "VSQRTPD", a1, res, _, _, _, _);

    relation padc(Address, Symbol, Symbol);
    padc(addr, dst, src)<--
        instruction(addr, _, _, "ADC", src, dst, _, _, _, _);

    relation psbb(Address, Symbol, Symbol);
    psbb(addr, res, a1)<--
        instruction(addr, _, _, "SBB", a1, res, _, _, _, _);

    relation pjmp(Address, Symbol);
    pjmp(addr, dst)<--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondGe, dst)<--
        instruction(addr, _, _, "JNS", dst, _, _, _, _, _);

    pjcc(addr, TestCond::CondL, dst)<--
        instruction(addr, _, _, "JS", dst, _, _, _, _, _);

    relation plea(Address, Symbol, Symbol);
    plea(addr, dst, src)<--
        instruction(addr, _, _, "LEA", src, dst, _, _, _, _);

    pxor(addr, dst, src)<--
        instruction(addr, _, _, "PXOR", src, dst, _, _, _, _);

    relation cond_neg(TestCond, TestCond);

    cond_neg(TestCond::CondE, TestCond::CondNe);
    cond_neg(TestCond::CondNe, TestCond::CondE);

    cond_neg(TestCond::CondB, TestCond::CondAe);
    cond_neg(TestCond::CondBe, TestCond::CondA);
    cond_neg(TestCond::CondAe, TestCond::CondB);
    cond_neg(TestCond::CondA, TestCond::CondBe);

    cond_neg(TestCond::CondL, TestCond::CondGe);
    cond_neg(TestCond::CondLe, TestCond::CondG);
    cond_neg(TestCond::CondGe, TestCond::CondL);
    cond_neg(TestCond::CondG, TestCond::CondLe);

    cond_neg(TestCond::CondP, TestCond::CondNp);
    cond_neg(TestCond::CondNp, TestCond::CondP);

    pjcc2(addr, c1, c2, label) <--
        pjcc(addr, cond1, label),
        cond_neg(cond1, c1),
        next(addr, addr1),
        pjcc(addr1, c2, dummplabel),
        next(addr1, addr2),
        plabel(addr2, dummplabel);

    relation pcall(Address, Symbol);
    pcall(addr, func) <--
        instruction(addr, _, _, "CALL", func, _, _, _, _, _),
        next(addr, addr1),
        instruction(addr1, _, _, "PUSH", func, _, _, _, _, _);


    relation unrefinedinstruction(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize);
    relation symbol_table(Address, usize, Symbol, Symbol, Symbol, usize, Symbol, usize, Symbol);
    relation plt_entry(Address, Symbol);
    relation plt_block(Address, Symbol);
    relation code_in_refined_block(Address, Address);
    relation def_used_for_address(Address, Symbol, Symbol);
    relation data_access_pattern(Address, i64, i64, Address);
    relation code_pointer_in_data(Address, Address);
    relation pointer_to_external_symbol(Address, Symbol);
    relation global_symbol(Address, Symbol);
    relation arch_bit(i64);
    relation suppress_instruction(Address);
    relation vla_alloca(Address, Mreg, Mreg);

    relation mach_inst(Address, MachInst);
    relation func_stacksz(Address, Address, Symbol, u64);
    relation func_span(Symbol, Address, Address);
    relation resolved_addr_to_symbol(Address, Ident, i64);

    relation type_size(Typ, u64);
    relation ireg_hold_type(String, Typ);
    relation reg_64(&'static str);
    relation reg_is_64(&'static str, bool);
    relation reg_cx(&'static str);
    relation reg_sp(&'static str);
    relation reg_bp(&'static str);
    relation reg_ip(&'static str);
    relation reg_xmm(&'static str);
    relation type_to_memchunk(Typ, MemoryChunk);
    relation instruction(Address, usize, &'static str, &'static str, Symbol, Symbol, Symbol, Symbol, usize, usize);
    relation rip_target_addr(Address, Address);
    relation is_external_function(Address);
    relation function_symbol(Address, Symbol);
    relation mach_func(Address, Address);
    relation prev_instr(Address, Address);
    relation call_search(Address, Address, usize);
    relation is_tail_call_jmp(Address);
    relation stack_delta(Address, i64);
    lattice stack_offset(Address, Address, Dual<i64>);
    relation transl_store_inferred(Address, MemoryChunk, Addrmode, Arc<Vec<Mreg>>, Mreg);
    relation transl_store(Address, MemoryChunk, Addrmode, Arc<Vec<Mreg>>, Mreg);
    relation addrmode_needs_resolution(Addrmode, Address);
    relation addr_requiring_symbol(Address);
    relation mach_imm_stack_init(Address, i64, i64, Typ);
    relation mach_imm_indirect_store(Address, i64, Typ, Mreg, i64);
    relation transl_load_inferred(Address, MemoryChunk, Addrmode, Arc<Vec<Mreg>>, Mreg);
    relation transl_load(Address, MemoryChunk, Addrmode, Arc<Vec<Mreg>>, Mreg);
    relation expand_builtin_inline(Address, Symbol, Arc<Vec<BuiltinArg<Mreg>>>, BuiltinArg<Mreg>);
    relation expand_builtin_va_start_32(Address, Ireg);
    relation pallocframe(Address, i64);
    relation pfreeframe(Address, i64);
    relation potential_end_addr(Address, Address);
    relation next_function_addr(Address, Address);
    relation pallocframe_by_func(Symbol, Address, i64);

    type_size(Typ::Tint, 4);
    type_size(Typ::Tfloat, 8);
    type_size(Typ::Tsingle, 4);
    type_size(Typ::Tany32, 4);

    type_size(Typ::Tlong, 8) <-- arch_bit(64);
    type_size(Typ::Tany64, 8) <-- arch_bit(64);

    // 64-bit registers use Tany64 (not Tlong) to let downstream type inference determine the actual type from usage context.
    ireg_hold_type("RAX".to_string(), Typ::Tany64);
    ireg_hold_type("RBX".to_string(), Typ::Tany64);
    ireg_hold_type("RCX".to_string(), Typ::Tany64);
    ireg_hold_type("RDX".to_string(), Typ::Tany64);
    ireg_hold_type("RSI".to_string(), Typ::Tany64);
    ireg_hold_type("RDI".to_string(), Typ::Tany64);
    ireg_hold_type("RBP".to_string(), Typ::Tany64);
    ireg_hold_type("RSP".to_string(), Typ::Tany64);
    ireg_hold_type("R8".to_string(), Typ::Tany64);
    ireg_hold_type("R9".to_string(), Typ::Tany64);
    ireg_hold_type("R10".to_string(), Typ::Tany64);
    ireg_hold_type("R11".to_string(), Typ::Tany64);
    ireg_hold_type("R12".to_string(), Typ::Tany64);
    ireg_hold_type("R13".to_string(), Typ::Tany64);
    ireg_hold_type("R14".to_string(), Typ::Tany64);
    ireg_hold_type("R15".to_string(), Typ::Tany64);
    reg_64("RAX"); reg_64("RBX"); reg_64("RCX"); reg_64("RDX");
    reg_64("RSI"); reg_64("RDI"); reg_64("RBP"); reg_64("RSP");
    reg_64("R8");  reg_64("R9");  reg_64("R10"); reg_64("R11");
    reg_64("R12"); reg_64("R13"); reg_64("R14"); reg_64("R15");
    reg_is_64("RAX", true); reg_is_64("RBX", true); reg_is_64("RCX", true); reg_is_64("RDX", true);
    reg_is_64("RSI", true); reg_is_64("RDI", true); reg_is_64("RBP", true); reg_is_64("RSP", true);
    reg_is_64("R8", true);  reg_is_64("R9", true);  reg_is_64("R10", true); reg_is_64("R11", true);
    reg_is_64("R12", true); reg_is_64("R13", true); reg_is_64("R14", true); reg_is_64("R15", true);
    reg_is_64("EAX", false); reg_is_64("EBX", false); reg_is_64("ECX", false); reg_is_64("EDX", false);
    reg_is_64("ESI", false); reg_is_64("EDI", false); reg_is_64("EBP", false); reg_is_64("ESP", false);
    reg_is_64("R8D", false); reg_is_64("R9D", false); reg_is_64("R10D", false); reg_is_64("R11D", false);
    reg_is_64("R12D", false); reg_is_64("R13D", false); reg_is_64("R14D", false); reg_is_64("R15D", false);
    reg_cx("RCX"); reg_cx("ECX"); reg_cx("CX"); reg_cx("CL"); reg_cx("CH");
    reg_sp("RSP"); reg_sp("ESP"); reg_sp("SP"); reg_sp("SPL");
    reg_bp("RBP"); reg_bp("EBP"); reg_bp("BP"); reg_bp("BPL");
    reg_ip("RIP"); reg_ip("EIP"); reg_ip("IP");
    reg_xmm("XMM0"); reg_xmm("XMM1"); reg_xmm("XMM2"); reg_xmm("XMM3");
    reg_xmm("XMM4"); reg_xmm("XMM5"); reg_xmm("XMM6"); reg_xmm("XMM7");
    reg_xmm("XMM8"); reg_xmm("XMM9"); reg_xmm("XMM10"); reg_xmm("XMM11");
    reg_xmm("XMM12"); reg_xmm("XMM13"); reg_xmm("XMM14"); reg_xmm("XMM15");
    ireg_hold_type("EAX".to_string(), Typ::Tint);
    ireg_hold_type("EBX".to_string(), Typ::Tint);
    ireg_hold_type("ECX".to_string(), Typ::Tint);
    ireg_hold_type("EDX".to_string(), Typ::Tint);
    ireg_hold_type("ESI".to_string(), Typ::Tint);
    ireg_hold_type("EDI".to_string(), Typ::Tint);
    ireg_hold_type("EBP".to_string(), Typ::Tint);
    ireg_hold_type("ESP".to_string(), Typ::Tint);
    ireg_hold_type("R8D".to_string(), Typ::Tint);
    ireg_hold_type("R9D".to_string(), Typ::Tint);
    ireg_hold_type("R10D".to_string(), Typ::Tint);
    ireg_hold_type("R11D".to_string(), Typ::Tint);
    ireg_hold_type("R12D".to_string(), Typ::Tint);
    ireg_hold_type("R13D".to_string(), Typ::Tint);
    ireg_hold_type("R14D".to_string(), Typ::Tint);
    ireg_hold_type("R15D".to_string(), Typ::Tint);
    ireg_hold_type("XMM0".to_string(), Typ::Tfloat);
    ireg_hold_type("XMM1".to_string(), Typ::Tfloat);
    ireg_hold_type("XMM2".to_string(), Typ::Tfloat);
    ireg_hold_type("XMM3".to_string(), Typ::Tfloat);
    ireg_hold_type("XMM4".to_string(), Typ::Tfloat);
    ireg_hold_type("XMM5".to_string(), Typ::Tfloat);
    ireg_hold_type("XMM6".to_string(), Typ::Tfloat);
    ireg_hold_type("XMM7".to_string(), Typ::Tfloat);
    ireg_hold_type("XMM8".to_string(), Typ::Tfloat);
    ireg_hold_type("XMM9".to_string(), Typ::Tfloat);
    ireg_hold_type("XMM10".to_string(), Typ::Tfloat);
    ireg_hold_type("XMM11".to_string(), Typ::Tfloat);
    ireg_hold_type("XMM12".to_string(), Typ::Tfloat);
    ireg_hold_type("XMM13".to_string(), Typ::Tfloat);
    ireg_hold_type("XMM14".to_string(), Typ::Tfloat);
    ireg_hold_type("XMM15".to_string(), Typ::Tfloat);
    ireg_hold_type("FP0".to_string(), Typ::Tfloat);
    ireg_hold_type("FP1".to_string(), Typ::Tfloat);
    ireg_hold_type("FP2".to_string(), Typ::Tfloat);
    ireg_hold_type("FP3".to_string(), Typ::Tfloat);
    ireg_hold_type("FP4".to_string(), Typ::Tfloat);
    ireg_hold_type("FP5".to_string(), Typ::Tfloat);
    ireg_hold_type("FP6".to_string(), Typ::Tfloat);
    ireg_hold_type("FP7".to_string(), Typ::Tfloat);
    ireg_hold_type("AX".to_string(), Typ::Tint);
    ireg_hold_type("BX".to_string(), Typ::Tint);
    ireg_hold_type("CX".to_string(), Typ::Tint);
    ireg_hold_type("DX".to_string(), Typ::Tint);
    ireg_hold_type("SI".to_string(), Typ::Tint);
    ireg_hold_type("DI".to_string(), Typ::Tint);
    ireg_hold_type("BP".to_string(), Typ::Tint);
    ireg_hold_type("SP".to_string(), Typ::Tint);
    ireg_hold_type("R8W".to_string(), Typ::Tint);
    ireg_hold_type("R9W".to_string(), Typ::Tint);
    ireg_hold_type("R10W".to_string(), Typ::Tint);
    ireg_hold_type("R11W".to_string(), Typ::Tint);
    ireg_hold_type("R12W".to_string(), Typ::Tint);
    ireg_hold_type("R13W".to_string(), Typ::Tint);
    ireg_hold_type("R14W".to_string(), Typ::Tint);
    ireg_hold_type("R15W".to_string(), Typ::Tint);
    ireg_hold_type("AL".to_string(), Typ::Tint);
    ireg_hold_type("BL".to_string(), Typ::Tint);
    ireg_hold_type("CL".to_string(), Typ::Tint);
    ireg_hold_type("DL".to_string(), Typ::Tint);
    ireg_hold_type("SIL".to_string(), Typ::Tint);
    ireg_hold_type("DIL".to_string(), Typ::Tint);
    ireg_hold_type("BPL".to_string(), Typ::Tint);
    ireg_hold_type("SPL".to_string(), Typ::Tint);
    ireg_hold_type("R8B".to_string(), Typ::Tint);
    ireg_hold_type("R9B".to_string(), Typ::Tint);
    ireg_hold_type("R10B".to_string(), Typ::Tint);
    ireg_hold_type("R11B".to_string(), Typ::Tint);
    ireg_hold_type("R12B".to_string(), Typ::Tint);
    ireg_hold_type("R13B".to_string(), Typ::Tint);
    ireg_hold_type("R14B".to_string(), Typ::Tint);
    ireg_hold_type("R15B".to_string(), Typ::Tint);
    ireg_hold_type("AH".to_string(), Typ::Tint);
    ireg_hold_type("BH".to_string(), Typ::Tint);
    ireg_hold_type("CH".to_string(), Typ::Tint);
    ireg_hold_type("DH".to_string(), Typ::Tint);

    type_to_memchunk(Typ::Tint, MemoryChunk::MInt32);
    type_to_memchunk(Typ::Tlong, MemoryChunk::MInt64);
    type_to_memchunk(Typ::Tfloat, MemoryChunk::MFloat64);
    type_to_memchunk(Typ::Tsingle, MemoryChunk::MFloat32);
    type_to_memchunk(Typ::Tany32, MemoryChunk::MAny32);
    type_to_memchunk(Typ::Tany64, MemoryChunk::MAny64);

    resolved_addr_to_symbol(addr, ident, 0) <--
        symbols(addr, _, _),
        let ident = *addr as Ident;

    resolved_addr_to_symbol(immediate_addr, ident, offset) <--
        addr_requiring_symbol(immediate_addr),
        func_span(_, start, end),
        if *immediate_addr >= *start,
        if *immediate_addr < *end,
        let ident = *start as Ident,
        let offset = (*immediate_addr - *start) as i64;

    resolved_addr_to_symbol(plt_addr, ident, 0) <--
        plt_entry(plt_addr, _),
        let ident = *plt_addr as Ident;


    rip_target_addr(addr, target) <--
        plea(addr, _, am),
        instruction(addr, size, _, _, _, _, _, _, _, _),
        op_indirect(am, _, base_str, _, _, disp, _),
        reg_ip(*base_str),
        let target = (*addr as i64 + *size as i64 + disp) as Address;

    rip_target_addr(addr, target) <--
        pmov(addr, _, am),
        instruction(addr, size, _, _, _, _, _, _, _, _),
        op_indirect(am, _, base_str, _, _, disp, _),
        reg_ip(*base_str),
        let target = (*addr as i64 + *size as i64 + disp) as Address;

    rip_target_addr(addr, target) <--
        pmov(addr, am, _),
        instruction(addr, size, _, _, _, _, _, _, _, _),
        op_indirect(am, _, base_str, _, _, disp, _),
        reg_ip(*base_str),
        let target = (*addr as i64 + *size as i64 + disp) as Address;

    resolved_addr_to_symbol(target, ident, 0) <--
        rip_target_addr(_, target),
        symbols(target, _, _),
        let ident = *target as Ident;

    resolved_addr_to_symbol(target, ident, offset) <--
        rip_target_addr(_, target),
        func_span(_, start, end),
        if *target >= *start && *target < *end,
        let ident = *start as Ident,
        let offset = (target - start) as i64;


    plt_entry(addr, name) <--
        symbol_table(addr, _, _, _, _, _, section_name, _, name),
        if *section_name == ".plt" || *section_name == ".plt.got";

    is_external_function(addr) <-- plt_entry(addr, _);
    is_external_function(addr) <-- plt_block(addr, _);

    is_external_function(addr) <--
        symbol_table(addr, _, sym_type, _, _, _, section_name, _, _),
        if *sym_type == "FUNC",
        if *section_name == ".init" || *section_name == ".fini";

    function_symbol(addr, name) <--
        symbol_table(addr, _size, _type, _binding, _section_type, _section_idx, _section_name, _name_idx, name),
        if *_binding == "GLOBAL" || *_binding == "LOCAL",
        if *_type == "FUNC",
        if *addr > 0;

    function_symbol(addr, name) <--
        plt_entry(addr, name);

    function_symbol(addr, name) <--
        plt_block(addr, name);

    global_symbol(addr, name) <--
        symbol_table(addr, _size, _type, _binding, _section_type, _section_idx, _section_name, _name_idx, name),
        if *_binding == "GLOBAL" || *_binding == "LOCAL",
        if *_type == "OBJECT",
        if *addr > 0;

    global_symbol(target_addr, name_sym) <--
        rip_target_addr(_, target_addr),
        if *target_addr > 0,
        !symbol_table(target_addr, _, _, _, _, _, _, _, _),
        !function_symbol(target_addr, _),
        !plt_entry(target_addr, _),
        let name_string = format!("data_{:x}", target_addr),
        let name_sym = Box::leak(name_string.into_boxed_str()) as &'static str;

    symbols(addr, name, name) <--
        function_symbol(addr, name);

    symbols(addr, name, name) <--
        global_symbol(addr, name);


    instruction(addr, size, mnemonic, dst, src1, src2, src3, src4, prefix, suffix) <--
        unrefinedinstruction(addr, size, mnemonic, dst, src1, src2, src3, src4, prefix, suffix),
        code_in_refined_block(addr, _),
        !suppress_instruction(addr);

    mach_inst(addr, MachInst::Mbuiltin(
        "alloca".to_string(),
        vec![BuiltinArg::BA(*size_mreg)],
        BuiltinArg::BA(*result_mreg),
    )) <--
        vla_alloca(addr, size_mreg, result_mreg);

    mach_inst(addr, MachInst::Mcall(Either::Left(Mreg::from(Ireg::from(reg_str))))) <--
        instruction(addr, _, _, "CALL", dst, _, _, _, _, _),
        op_register(dst, reg_str);

    mach_inst(addr, MachInst::Mcall(Either::Right(Either::Right(*imm_str)))) <--
        instruction(addr, _, _, "CALL", dst, _, _, _, _, _),
        op_immediate(dst, imm_str, _),
        !symbols(*imm_str as Address, _, _);

    mach_inst(addr, MachInst::Mcall(Either::Left(Mreg::from(Ireg::from(base_str))))) <--
        instruction(addr, _, _, "CALL", dst, _, _, _, _, _),
        op_indirect(dst, _, base_str, _, _, _, _),
        if base_str != &"NONE";


    prev_instr(next_addr, curr_addr) <-- next(curr_addr, next_addr);

    mach_inst(addr, MachInst::Mtailcall(Either::Left(Mreg::from(Ireg::from(reg_str))))) <--
        padd(addr, rsp, imm),
        op_immediate(imm, _, _),
        op_register(rsp, "RSP"),
        next(addr, addr1),
        pjmp(addr1, dst),
        op_register(dst, reg_str);

    mach_inst(addr, MachInst::Mtailcall(Either::Right(Either::Right(*imm_str)))) <--
        padd(addr, rsp, imm),
        op_immediate(imm, _, _),
        op_register(rsp, "RSP"),
        next(addr, addr1),
        pjmp(addr1, dst),
        op_immediate(dst, imm_str, _);


    mach_inst(addr, MachInst::Mtailcall(Either::Right(Either::Left(sym)))), plabel(addr1, sym) <--
        padd(addr, rsp, imm),
        op_immediate(imm, _, _),
        op_register(rsp, "RSP"),
        next(addr, addr1),
        pjmp(addr1, sym),
        op_indirect(sym, _, _, _, _, _, _);

    is_tail_call_jmp(addr) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_immediate(dst, target_addr, _),
        func_entry(_, target_addr_addr),
        if *target_addr as u64 == *target_addr_addr;

    is_tail_call_jmp(addr) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_immediate(dst, target_addr, _),
        instr_in_function(addr, func),
        next(addr, next_addr),
        !instr_in_function(next_addr, func),
        // Exclude intra-function jumps (loop back-edges at function boundaries are not tail calls).
        !instr_in_function(*target_addr as u64, func);

    is_tail_call_jmp(addr) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_immediate(dst, target_addr, _),
        instr_in_function(addr, func),
        func_entry(_, target_func),
        if *target_addr as u64 == *target_func,
        if *target_func != *func;

    is_tail_call_jmp(addr) <--
        instruction(addr, _, _, "JMP", _, _, _, _, _, _),
        plt_entry(addr, _);

    mach_inst(addr, MachInst::Mtailcall(Either::Right(Either::Left(sym)))) <--
        instruction(addr, _, _, "JMP", _, _, _, _, _, _),
        plt_entry(addr, sym);

    mach_inst(addr, MachInst::Mtailcall(Either::Right(Either::Right(*target_addr)))) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        op_immediate(dst, target_addr, _),
        is_tail_call_jmp(addr);

    mach_inst(addr, MachInst::Mgoto(dst)) <--
        instruction(addr, _, _, "JMP", dst, _, _, _, _, _),
        !is_tail_call_jmp(addr);

    mach_inst(addr, MachInst::Mreturn) <--
        instruction(addr, _, _, "RET", _, _, _, _, _, _);


    mach_inst(addr, MachInst::Mbuiltin(
        "__builtin_unreachable".to_string(),
        vec![],
        BuiltinArg::BA(Mreg::from(Ireg::Unknown))
    )) <--
        phlt(addr),
        builtins("__builtin_unreachable");


    stack_delta(addr, -(*sz as i64)) <--
        ppush(addr, sym),
        op_register(sym, ireg_r),
        ireg_hold_type(ireg_r.to_string(), typ),
        type_size(typ, sz);

    stack_delta(addr, -(*bits / 8)) <--
        ppush(addr, sym),
        op_immediate(sym, _, _),
        arch_bit(bits);

    stack_delta(addr, *sz as i64) <--
        ppop(addr, ireg_sym),
        op_register(ireg_sym, ireg_r),
        ireg_hold_type(ireg_r.to_string(), typ),
        type_size(typ, sz);


    stack_offset(func_start, func_start, Dual(0)) <--
        func_span(_, func_start, _);

    stack_offset(func_start, curaddr, Dual(prev_ofs.0 + *delta)) <--
        stack_offset(func_start, prevaddr, prev_ofs),
        next(prevaddr, curaddr),
        instr_in_function(curaddr, func_start),
        stack_delta(prevaddr, delta);

    stack_offset(func_start, curaddr, prev_ofs) <--
        stack_offset(func_start, prevaddr, prev_ofs),
        next(prevaddr, curaddr),
        instr_in_function(curaddr, func_start),
        !stack_delta(prevaddr, _);


    transl_store_inferred(addr, *chunk, addrmode, regs.clone(), src) <--
        pmov(addr, dst, src_sym),
        op_register(src_sym, src_str),
        let src = Mreg::from(src_str),
        op_indirect(dst, _, r2, _, _scale, disp, _),
        if Mreg::from(r2) != Mreg::BP && Mreg::from(r2) != Mreg::SP,
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_r2, Ireg::from(r2)),
        preg_of(arg, preg_of_r2),
        let regs = Arc::new(vec![*arg]),
        ireg_hold_type(src_str.to_string(), typ),
        type_to_memchunk(typ, chunk);

    transl_store(addr, mc, addrmode, regs, src) <--
        transl_store_inferred(addr, mc, addrmode, regs, src);

    transl_store(addr, mc, addrmode, regs.clone(), dst_reg) <--
        pmov(addr, dst, src),
        op_register(src, dst_str),
        let dst_reg = Mreg::from(dst_str),
        op_indirect(dst, _, r2, _, _scale, disp, _),
        if Mreg::from(r2) != Mreg::BP && Mreg::from(r2) != Mreg::SP,
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_r2, Ireg::from(r2)),
        preg_of(arg, preg_of_r2),
        let regs = Arc::new(vec![*arg]),
        !transl_store_inferred(addr, _, addrmode, _, _),
        instruction(addr, _, mnem, _, _, _, _, _, _, _),
        let mnem_upper = mnem.to_ascii_uppercase(),
        let mc = if mnem_upper.contains("MOVB") || mnem_upper.ends_with("B") {
            MemoryChunk::MInt8Unsigned
        } else if mnem_upper.contains("MOVW") || mnem_upper.ends_with("W") {
            MemoryChunk::MInt16Unsigned
        } else if mnem_upper.contains("MOVL") || mnem_upper.ends_with("L") {
            MemoryChunk::MInt32
        } else if mnem_upper.contains("MOVQ") || mnem_upper.ends_with("Q") {
            MemoryChunk::MInt64
        } else if mnem_upper.contains("MOVSS") {
            MemoryChunk::MFloat32
        } else if mnem_upper.contains("MOVSD") {
            MemoryChunk::MFloat64
        } else {
            MemoryChunk::MAny64
        };


    addrmode_needs_resolution(am, target_addr) <--
        transl_store(_, _, am, _, _),
        if let Some(target_addr_i64) = addrmode_needs_symbol_resolution(am),
        let target_addr = target_addr_i64 as Address;

    addrmode_needs_resolution(am, target_addr) <--
        transl_load(_, _, am, _, _),
        if let Some(target_addr_i64) = addrmode_needs_symbol_resolution(am),
        let target_addr = target_addr_i64 as Address;


    addr_requiring_symbol(target_addr) <--
        addrmode_needs_resolution(_, target_addr);

    addr_requiring_symbol(target_addr) <--
        rip_target_addr(_, target_addr);
    mach_inst(addr, MachInst::Mstore(*memory_chunk, addressing, Arc::new(args), *src)) <--
        transl_store(addr, memory_chunk, addrmode, regs, src),
        addrmode_needs_resolution(*addrmode, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        let resolved = Some((*ident, *offset)),
        if let Ok((addressing, args)) = transl_addressing_rev(*addrmode, resolved);

    mach_inst(addr, MachInst::Mstore(*memory_chunk, addressing, Arc::new(args), *src)) <--
        transl_store(addr, memory_chunk, addrmode, regs, src),
        !addrmode_needs_resolution(*addrmode, _),
        if let Ok((addressing, args)) = transl_addressing_rev(*addrmode, None);

    mach_inst(addr, MachInst::Msetstack(src_reg, *disp, *typ)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        let src_reg = Mreg::from(srcstr),
        op_indirect(dst, _, r2, _, _, disp, _),
        if Mreg::from(r2) == Mreg::SP,
        stack_offset(_, addr, rsp_ofs),
        let ofs_adjusted = *disp + rsp_ofs.0,
        ireg_hold_type(srcstr.to_string(), typ);

    mach_inst(addr, MachInst::Msetstack(src_reg, *disp, *typ)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        let src_reg = Mreg::from(srcstr),
        op_indirect(dst, _, r2, _, _, disp, _),
        if Mreg::from(r2) == Mreg::BP,
        instr_in_function(addr, func),
        func_has_frame_pointer(func),
        ireg_hold_type(srcstr.to_string(), typ);

    mach_imm_stack_init(addr, disp, imm_int, ty) <--
        pmov(addr, dst, src),
        op_immediate(src, imm_sym, _),
        op_indirect(dst, _, base, _, _, disp, sz),
        if Mreg::from(base) == Mreg::BP,
        instr_in_function(addr, func),
        func_has_frame_pointer(func),
        let ty = if *sz <= 4 { Typ::Tint } else { Typ::Tany64 },
        let imm_int = *imm_sym as i64;

    mach_imm_stack_init(addr, ofs_adjusted, imm_int, ty) <--
        pmov(addr, dst, src),
        op_immediate(src, imm_sym, _),
        op_indirect(dst, _, base, _, _, disp, sz),
        if Mreg::from(base) == Mreg::SP,
        stack_offset(_, addr, rsp_ofs),
        let ofs_adjusted = *disp + rsp_ofs.0,
        let ty = if *sz <= 4 { Typ::Tint } else { Typ::Tany64 },
        let imm_int = *imm_sym as i64;

    mach_imm_indirect_store(addr, imm_int, ty, base_mreg, *disp) <--
        pmov(addr, dst, src),
        op_immediate(src, imm_sym, _),
        op_indirect(dst, _, r2, _, _scale, disp, sz),
        if Mreg::from(r2) != Mreg::BP && Mreg::from(r2) != Mreg::SP,
        let base_mreg = Mreg::from(r2),
        let ty = if *sz <= 4 { Typ::Tint } else { Typ::Tany64 },
        let imm_int = *imm_sym as i64;

    mach_inst(addr, MachInst::Mgetstack(*disp, *typ, Mreg::from(dststr))) <--
        pmov(addr, dst, src),
        op_indirect(src, _, r2, _, _, disp, _),
        if Mreg::from(r2) == Mreg::SP,
        op_register(dst, dststr),
        stack_offset(_, addr, rsp_ofs),
        let ofs_adjusted = *disp + rsp_ofs.0,
        ireg_hold_type(dststr.to_string(), typ);

    mach_inst(addr, MachInst::Mgetstack(*disp, *typ, Mreg::from(dststr))) <--
        pmov(addr, dst, src),
        op_indirect(src, _, r2, _, _, disp, _),
        if Mreg::from(r2) == Mreg::BP,
        op_register(dst, dststr),
        instr_in_function(addr, func),
        func_has_frame_pointer(func),
        ireg_hold_type(dststr.to_string(), typ);

    // BP-relative load when BP is NOT the frame pointer: treat as regular memory load
    mach_inst(addr, MachInst::Mload(*mc, Addressing::Aindexed(*disp), Arc::new(vec![Mreg::BP]), Mreg::from(dststr))) <--
        pmov(addr, dst, src),
        op_indirect(src, _, r2, _, _, disp, _),
        if Mreg::from(r2) == Mreg::BP,
        op_register(dst, dststr),
        instr_in_function(addr, func),
        !func_has_frame_pointer(func),
        ireg_hold_type(dststr.to_string(), typ),
        type_to_memchunk(typ, mc);

    // BP-relative load (mnemonic-based chunk) when BP is NOT the frame pointer
    mach_inst(addr, MachInst::Mload(mc, Addressing::Aindexed(*disp), Arc::new(vec![Mreg::BP]), Mreg::from(dststr))) <--
        pmov(addr, dst, src),
        op_indirect(src, _, r2, _, _, disp, _),
        if Mreg::from(r2) == Mreg::BP,
        op_register(dst, dststr),
        instr_in_function(addr, func),
        !func_has_frame_pointer(func),
        !ireg_hold_type(dststr.to_string(), _),
        instruction(addr, _, mnem, _, _, _, _, _, _, _),
        let mnem_upper = mnem.to_ascii_uppercase(),
        let mc = if mnem_upper.contains("MOVZB") {
            MemoryChunk::MInt8Unsigned
        } else if mnem_upper.contains("MOVSB") {
            MemoryChunk::MInt8Signed
        } else if mnem_upper.contains("MOVZW") {
            MemoryChunk::MInt16Unsigned
        } else if mnem_upper.contains("MOVSW") {
            MemoryChunk::MInt16Signed
        } else if mnem_upper.contains("MOVL") || mnem_upper.ends_with("L") {
            MemoryChunk::MInt32
        } else if mnem_upper.contains("MOVQ") || mnem_upper.ends_with("Q") {
            MemoryChunk::MInt64
        } else {
            MemoryChunk::MAny64
        };

    // BP-relative store when BP is NOT the frame pointer
    mach_inst(addr, MachInst::Mstore(*mc, Addressing::Aindexed(*disp), Arc::new(vec![Mreg::BP]), src_reg)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        let src_reg = Mreg::from(srcstr),
        op_indirect(dst, _, r2, _, _, disp, _),
        if Mreg::from(r2) == Mreg::BP,
        instr_in_function(addr, func),
        !func_has_frame_pointer(func),
        ireg_hold_type(srcstr.to_string(), typ),
        type_to_memchunk(typ, mc);

    // BP-relative store (mnemonic-based chunk) when BP is NOT the frame pointer
    mach_inst(addr, MachInst::Mstore(mc, Addressing::Aindexed(*disp), Arc::new(vec![Mreg::BP]), src_reg)) <--
        pmov(addr, dst, src),
        op_register(src, srcstr),
        let src_reg = Mreg::from(srcstr),
        op_indirect(dst, _, r2, _, _, disp, _),
        if Mreg::from(r2) == Mreg::BP,
        instr_in_function(addr, func),
        !func_has_frame_pointer(func),
        !ireg_hold_type(srcstr.to_string(), _),
        instruction(addr, _, mnem, _, _, _, _, _, _, _),
        let mnem_upper = mnem.to_ascii_uppercase(),
        let mc = if mnem_upper.contains("MOVB") || mnem_upper.ends_with("B") {
            MemoryChunk::MInt8Unsigned
        } else if mnem_upper.contains("MOVW") || mnem_upper.ends_with("W") {
            MemoryChunk::MInt16Unsigned
        } else if mnem_upper.contains("MOVL") || mnem_upper.ends_with("L") {
            MemoryChunk::MInt32
        } else if mnem_upper.contains("MOVQ") || mnem_upper.ends_with("Q") {
            MemoryChunk::MInt64
        } else {
            MemoryChunk::MAny64
        };

    // BP-relative immediate store when BP is NOT the frame pointer
    mach_imm_indirect_store(addr, imm_int, ty, Mreg::BP, *disp) <--
        pmov(addr, dst, src),
        op_immediate(src, imm_sym, _),
        op_indirect(dst, _, r2, _, _scale, disp, sz),
        if Mreg::from(r2) == Mreg::BP,
        instr_in_function(addr, func),
        !func_has_frame_pointer(func),
        let ty = if *sz <= 4 { Typ::Tint } else { Typ::Tany64 },
        let imm_int = *imm_sym as i64;


    #[local] relation cmp_jcc_link(Address, Address);
    cmp_jcc_link(addr0, addr1) <--
        pcmp(addr0, _, _),
        next(addr0, addr1),
        pjcc(addr1, _, _);
    cmp_jcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        pcmp(addr0, _, _);

    #[local] relation test_jcc_link(Address, Address);
    test_jcc_link(addr0, addr1) <--
        ptest(addr0, _, _),
        next(addr0, addr1),
        pjcc(addr1, _, _);
    test_jcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        ptest(addr0, _, _);

    #[local] relation cmp_cmov_link(Address, Address);
    cmp_cmov_link(addr0, addr1) <--
        pcmp(addr0, _, _),
        next(addr0, addr1),
        pcmov(addr1, _, _, _);
    cmp_cmov_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        pcmp(addr0, _, _),
        pcmov(addr1, _, _, _);

    #[local] relation fcmp_jcc_link(Address, Address);
    fcmp_jcc_link(addr0, addr1) <--
        pucomisd(addr0, _, _),
        next(addr0, addr1),
        pjcc(addr1, _, _);
    fcmp_jcc_link(addr0, addr1) <--
        pucomiss(addr0, _, _),
        next(addr0, addr1),
        pjcc(addr1, _, _);
    fcmp_jcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        pucomisd(addr0, _, _);
    fcmp_jcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        pucomiss(addr0, _, _);


    mach_inst(addr0, MachInst::Mcond(condition, Arc::new(vec![*arg1]), lbl)) <--
        pcmp(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, imm_val, _),
        reg_64(reg_str1),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        cmp_jcc_link(addr0, addr1),
        pjcc(addr1, test_cond, lbl),
        let base_cond = condition_for_testcond_sized(*test_cond, true),
        let condition = match base_cond {
            Condition::Ccomp(cmp) | Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, *imm_val),
            Condition::Ccompu(cmp) | Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, *imm_val),
            other => other,
        };

    mach_inst(addr0, MachInst::Mcond(condition, Arc::new(vec![*arg1]), lbl)) <--
        pcmp(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, imm_val, _),
        !reg_64(reg_str1),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        cmp_jcc_link(addr0, addr1),
        pjcc(addr1, test_cond, lbl),
        let base_cond = condition_for_testcond_sized(*test_cond, false),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, *imm_val),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, *imm_val),
            other => other,
        };

    mach_inst(addr0, MachInst::Mcond(condition, Arc::new(vec![*arg1, *arg2]), lbl)) <--
        pcmp(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, reg_str2),
        reg_64(reg_str1),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        ireg_of(preg_of_r2, Ireg::from(reg_str2)),
        preg_of(arg1, preg_of_r1),
        preg_of(arg2, preg_of_r2),
        cmp_jcc_link(addr0, addr1),
        pjcc(addr1, test_cond, lbl),
        let condition = condition_for_testcond_sized(*test_cond, true);

    mach_inst(addr0, MachInst::Mcond(condition, Arc::new(vec![*arg1, *arg2]), lbl)) <--
        pcmp(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, reg_str2),
        !reg_64(reg_str1),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        ireg_of(preg_of_r2, Ireg::from(reg_str2)),
        preg_of(arg1, preg_of_r1),
        preg_of(arg2, preg_of_r2),
        cmp_jcc_link(addr0, addr1),
        pjcc(addr1, test_cond, lbl),
        let condition = condition_for_testcond_sized(*test_cond, false);


    mach_inst(addr0, MachInst::Mcond(condition, Arc::new(vec![*arg1]), lbl)) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, reg_str2),
        if reg_str1 == reg_str2,
        reg_64(reg_str1),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        test_jcc_link(addr0, addr1),
        pjcc(addr1, test_cond, lbl),
        let base_cond = condition_for_testcond_sized(*test_cond, true),
        let condition = match base_cond {
            Condition::Ccomp(cmp) | Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, 0),
            Condition::Ccompu(cmp) | Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, 0),
            other => other,
        };

    mach_inst(addr0, MachInst::Mcond(condition, Arc::new(vec![*arg1]), lbl)) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, reg_str2),
        if reg_str1 == reg_str2,
        !reg_64(reg_str1),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        test_jcc_link(addr0, addr1),
        pjcc(addr1, test_cond, lbl),
        let base_cond = condition_for_testcond_sized(*test_cond, false),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, 0),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, 0),
            other => other,
        };


    mach_inst(addr0, MachInst::Mop(
        Operation::Osel(condition, typ),
        Arc::new(vec![*dst_mreg, *src_mreg, *cmp_arg1]),
        *dst_mreg
    )) <--
        pcmp(addr0, cmp_r1, cmp_r2),
        op_register(cmp_r1, cmp_reg_str),
        op_immediate(cmp_r2, imm_val, _),
        ireg_of(preg_of_cmp1, Ireg::from(cmp_reg_str)),
        preg_of(cmp_arg1, preg_of_cmp1),
        cmp_cmov_link(addr0, addr1),
        pcmov(addr1, cmov_cond, dst_sym, src_sym),
        op_register(dst_sym, dst_str),
        op_register(src_sym, src_str),
        !reg_xmm(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(dst_mreg, preg_of_dst),
        preg_of(src_mreg, preg_of_src),
        let neg_cond = negate_testcond(*cmov_cond),
        reg_is_64(cmp_reg_str, cmp_is_64),
        let base_cond = condition_for_testcond_sized(neg_cond, *cmp_is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, *imm_val),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, *imm_val),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, *imm_val),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, *imm_val),
            other => other,
        },
        reg_is_64(dst_str, dst_is_64),
        let typ = if *dst_is_64 { Typ::Tany64 } else { Typ::Tint };

    mach_inst(addr0, MachInst::Mop(
        Operation::Osel(condition, typ),
        Arc::new(vec![*dst_mreg, *src_mreg, *cmp_arg1, *cmp_arg2]),
        *dst_mreg
    )) <--
        pcmp(addr0, cmp_r1, cmp_r2),
        op_register(cmp_r1, cmp_str1),
        op_register(cmp_r2, cmp_str2),
        ireg_of(preg_of_cmp1, Ireg::from(cmp_str1)),
        ireg_of(preg_of_cmp2, Ireg::from(cmp_str2)),
        preg_of(cmp_arg1, preg_of_cmp1),
        preg_of(cmp_arg2, preg_of_cmp2),
        cmp_cmov_link(addr0, addr1),
        pcmov(addr1, cmov_cond, dst_sym, src_sym),
        op_register(dst_sym, dst_str),
        op_register(src_sym, src_str),
        !reg_xmm(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        ireg_of(preg_of_src, Ireg::from(src_str)),
        preg_of(dst_mreg, preg_of_dst),
        preg_of(src_mreg, preg_of_src),
        let neg_cond = negate_testcond(*cmov_cond),
        reg_is_64(cmp_str1, cmp_is_64),
        let condition = condition_for_testcond_sized(neg_cond, *cmp_is_64),
        reg_is_64(dst_str, dst_is_64),
        let typ = if *dst_is_64 { Typ::Tany64 } else { Typ::Tint };


    mach_inst(addr0, MachInst::Mcond(Condition::Cmaskzero(*mask_val), Arc::new(vec![*arg1]), lbl)) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, mask_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        test_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondE, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Cmasknotzero(*mask_val), Arc::new(vec![*arg1]), lbl)) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, mask_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        test_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondNe, lbl);


    #[local] relation sub_jcc_link(Address, Address);
    sub_jcc_link(addr0, addr1) <--
        psub(addr0, _, _),
        next(addr0, addr1),
        pjcc(addr1, _, _);
    sub_jcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        psub(addr0, _, _);

    mach_inst(addr0, MachInst::Mcond(condition, Arc::new(vec![*arg1]), lbl)) <--
        psub(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, imm_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        sub_jcc_link(addr0, addr1),
        pjcc(addr1, test_cond, lbl),
        reg_is_64(reg_str1, is_64),
        let base_cond = condition_for_testcond_sized(*test_cond, *is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, *imm_val),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, *imm_val),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, *imm_val),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, *imm_val),
            other => other,
        };

    mach_inst(addr0, MachInst::Mcond(condition, Arc::new(vec![*arg1, *arg2]), lbl)) <--
        psub(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, reg_str2),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        ireg_of(preg_of_r2, Ireg::from(reg_str2)),
        preg_of(arg1, preg_of_r1),
        preg_of(arg2, preg_of_r2),
        sub_jcc_link(addr0, addr1),
        pjcc(addr1, test_cond, lbl),
        reg_is_64(reg_str1, is_64),
        let condition = condition_for_testcond_sized(*test_cond, *is_64);


    #[local] relation and_jcc_link(Address, Address);
    and_jcc_link(addr0, addr1) <--
        pand(addr0, _, _),
        next(addr0, addr1),
        pjcc(addr1, _, _);
    and_jcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        pand(addr0, _, _);

    mach_inst(addr0, MachInst::Mcond(Condition::Cmaskzero(*mask_val), Arc::new(vec![*arg1]), lbl)) <--
        pand(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, mask_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        and_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondE, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Cmasknotzero(*mask_val), Arc::new(vec![*arg1]), lbl)) <--
        pand(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, mask_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        and_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondNe, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompimm(Comparison::Ceq, 0), Arc::new(vec![*arg1]), lbl)) <--
        pand(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        and_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondE, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompimm(Comparison::Cne, 0), Arc::new(vec![*arg1]), lbl)) <--
        pand(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        and_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondNe, lbl);


    #[local] relation cmp_setcc_link(Address, Address);
    cmp_setcc_link(addr0, addr1) <--
        pcmp(addr0, _, _),
        next(addr0, addr1),
        psetcc(addr1, _, _);
    cmp_setcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        pcmp(addr0, _, _),
        psetcc(addr1, _, _);

    #[local] relation test_setcc_link(Address, Address);
    test_setcc_link(addr0, addr1) <--
        ptest(addr0, _, _),
        next(addr0, addr1),
        psetcc(addr1, _, _);
    test_setcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        ptest(addr0, _, _),
        psetcc(addr1, _, _);

    #[local] relation sub_setcc_link(Address, Address);
    sub_setcc_link(addr0, addr1) <--
        psub(addr0, _, _),
        next(addr0, addr1),
        psetcc(addr1, _, _);
    sub_setcc_link(addr0, addr1) <--
        flags_and_jump_pair(addr0, addr1, _),
        psub(addr0, _, _),
        psetcc(addr1, _, _);

    mach_inst(addr0, MachInst::Mop(
        Operation::Ocmp(condition),
        Arc::new(vec![*arg1]),
        *dst_mreg
    )) <--
        pcmp(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, imm_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        cmp_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, dst_sym),
        op_register(dst_sym, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst),
        reg_is_64(reg_str1, is_64),
        let base_cond = condition_for_testcond_sized(*test_cond, *is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, *imm_val),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, *imm_val),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, *imm_val),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, *imm_val),
            other => other,
        };

    mach_inst(addr0, MachInst::Mop(
        Operation::Ocmp(condition),
        Arc::new(vec![*arg1, *arg2]),
        *dst_mreg
    )) <--
        pcmp(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, reg_str2),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        ireg_of(preg_of_r2, Ireg::from(reg_str2)),
        preg_of(arg1, preg_of_r1),
        preg_of(arg2, preg_of_r2),
        cmp_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, dst_sym),
        op_register(dst_sym, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst),
        reg_is_64(reg_str1, is_64),
        let condition = condition_for_testcond_sized(*test_cond, *is_64);

    mach_inst(addr0, MachInst::Mop(
        Operation::Ocmp(condition),
        Arc::new(vec![*arg1]),
        *dst_mreg
    )) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_register(r2, reg_str2),
        if reg_str1 == reg_str2,
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        test_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, dst_sym),
        op_register(dst_sym, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst),
        reg_is_64(reg_str1, is_64),
        let base_cond = condition_for_testcond_sized(*test_cond, *is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, 0),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, 0),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, 0),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, 0),
            other => other,
        };

    mach_inst(addr0, MachInst::Mop(
        Operation::Ocmp(Condition::Cmaskzero(*mask_val)),
        Arc::new(vec![*arg1]),
        *dst_mreg
    )) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, mask_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        test_setcc_link(addr0, addr_set),
        psetcc(addr_set, TestCond::CondE, dst_sym),
        op_register(dst_sym, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst);

    mach_inst(addr0, MachInst::Mop(
        Operation::Ocmp(Condition::Cmasknotzero(*mask_val)),
        Arc::new(vec![*arg1]),
        *dst_mreg
    )) <--
        ptest(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, mask_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        test_setcc_link(addr0, addr_set),
        psetcc(addr_set, TestCond::CondNe, dst_sym),
        op_register(dst_sym, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst);

    mach_inst(addr0, MachInst::Mop(
        Operation::Ocmp(condition),
        Arc::new(vec![*arg1]),
        *dst_mreg
    )) <--
        psub(addr0, r1, r2),
        op_register(r1, reg_str1),
        op_immediate(r2, imm_val, _),
        ireg_of(preg_of_r1, Ireg::from(reg_str1)),
        preg_of(arg1, preg_of_r1),
        sub_setcc_link(addr0, addr_set),
        psetcc(addr_set, test_cond, dst_sym),
        op_register(dst_sym, dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(dst_mreg, preg_of_dst),
        reg_is_64(reg_str1, is_64),
        let base_cond = condition_for_testcond_sized(*test_cond, *is_64),
        let condition = match base_cond {
            Condition::Ccomp(cmp) => Condition::Ccompimm(cmp, *imm_val),
            Condition::Ccompu(cmp) => Condition::Ccompuimm(cmp, *imm_val),
            Condition::Ccompl(cmp) => Condition::Ccomplimm(cmp, *imm_val),
            Condition::Ccomplu(cmp) => Condition::Ccompluimm(cmp, *imm_val),
            other => other,
        };

    mach_inst(addr0, MachInst::Mop(
        Operation::Oshrximm(*shift_n),
        Arc::new(args.clone()),
        *arg_mreg
    )) <--
        ptest(addr0, test_r1, test_r2),
        op_register(test_r1, test_reg1),
        op_register(test_r2, test_reg2),
        if test_reg1 == test_reg2,
        next(addr0, addr1),
        plea(addr1, lea_dst_sym, lea_src_sym),
        op_register(lea_dst_sym, lea_dst_str),
        op_indirect(lea_src_sym, _, base_reg, _, _, disp, _),
        if base_reg == test_reg1,
        if lea_dst_str != test_reg1,
        next(addr1, addr2),
        pcmov(addr2, TestCond::CondL, cmov_dst_sym, cmov_src_sym),
        op_register(cmov_dst_sym, cmov_dst_str),
        op_register(cmov_src_sym, cmov_src_str),
        if cmov_dst_str == test_reg1,
        if cmov_src_str == lea_dst_str,
        next(addr2, addr3),
        psar(addr3, sar_dst_sym, sar_src_sym),
        op_register(sar_dst_sym, sar_dst_str),
        op_immediate(sar_src_sym, shift_n, _),
        if sar_dst_str == test_reg1,
        if *disp == (1i64 << *shift_n) - 1,
        ireg_of(preg_of_arg, Ireg::from(test_reg1)),
        preg_of(arg_mreg, preg_of_arg),
        let args = vec![*arg_mreg];

    mach_inst(addr0, MachInst::Mop(
        Operation::Oshrxlimm(*shift_n),
        Arc::new(args.clone()),
        *arg_mreg
    )) <--
        pcast(addr0, _, _),
        instruction(addr0, _, _, mnem0, _, _, _, _, _, _),
        if *mnem0 == "CQO",
        next(addr0, addr1),
        pshr(addr1, shr_dst_sym, shr_src_sym),
        op_register(shr_dst_sym, shr_dst_str),
        op_immediate(shr_src_sym, shr_amount, _),
        next(addr1, addr2),
        plea(addr2, lea_dst_sym, lea_src_sym),
        op_register(lea_dst_sym, lea_dst_str),
        op_indirect(lea_src_sym, _, lea_base, lea_index, _scale, lea_disp, _),
        if *lea_disp == 0,
        if lea_base == lea_dst_str,
        if lea_index == shr_dst_str,
        next(addr2, addr3),
        psar(addr3, sar_dst_sym, sar_src_sym),
        op_register(sar_dst_sym, sar_dst_str),
        op_immediate(sar_src_sym, shift_n, _),
        if sar_dst_str == lea_dst_str,
        if *shr_amount == 64 - *shift_n,
        ireg_of(preg_of_arg, Ireg::from(lea_dst_str)),
        preg_of(arg_mreg, preg_of_arg),
        let args = vec![*arg_mreg];


    mach_inst(addr0, MachInst::Mcond(
        Condition::Cnotcompf(Comparison::Ceq),
        Arc::new(vec![arg1, arg2]),
        lbl
    )) <--
        pucomisd(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::from(r1_str),
        let arg2 = Mreg::from(r2_str),
        next(addr0, addr1),
        pjcc(addr1, TestCond::CondP, lbl),
        next(addr1, addr2),
        pjcc(addr2, TestCond::CondNe, lbl);

    mach_inst(addr0, MachInst::Mcond(
        Condition::Cnotcompfs(Comparison::Ceq),
        Arc::new(vec![arg1, arg2]),
        lbl
    )) <--
        pucomiss(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::from(r1_str),
        let arg2 = Mreg::from(r2_str),
        next(addr0, addr1),
        pjcc(addr1, TestCond::CondP, lbl),
        next(addr1, addr2),
        pjcc(addr2, TestCond::CondNe, lbl);


    transl_load_inferred(addr, *chunk, addrmode, regs.clone(), dst) <--
        pmov(addr, dst_sym, src),
        op_register(dst_sym, dst_str),
        let dst = Mreg::from(dst_str),
        op_indirect(src, _, r2, _, _scale, disp, _),
        if Mreg::from(r2) != Mreg::BP && Mreg::from(r2) != Mreg::SP,
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_r2, Ireg::from(r2)),
        preg_of(arg, preg_of_r2),
        let regs = Arc::new(vec![*arg]),
        ireg_hold_type(dst_str.to_string(), typ),
        type_to_memchunk(typ, chunk),
        instruction(addr, _, mnem, _, _, _, _, _, _, _),
        let mnem_upper = mnem.to_ascii_uppercase(),
        if !mnem_upper.contains("MOVZ") && !mnem_upper.contains("MOVS");

    transl_load(addr, mc, addrmode, regs, dst) <--
        transl_load_inferred(addr, mc, addrmode, regs, dst);

    transl_load(addr, mc, addrmode, regs.clone(), dst_reg) <--
        pmov(addr, dst, src),
        op_register(dst, dst_str),
        let dst_reg = Mreg::from(dst_str),
        op_indirect(src, _, r2, _, _scale, disp, _),
        if Mreg::from(r2) != Mreg::BP && Mreg::from(r2) != Mreg::SP,
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        ireg_of(preg_of_r2, Ireg::from(r2)),
        preg_of(arg, preg_of_r2),
        let regs = Arc::new(vec![*arg]),
        !transl_load_inferred(addr, _, addrmode, _, _),
        instruction(addr, _, mnem, _, _, _, _, _, _, _),
        let mnem_upper = mnem.to_ascii_uppercase(),
        let mc = if mnem_upper.contains("MOVZB") {
            MemoryChunk::MInt8Unsigned
        } else if mnem_upper.contains("MOVSB") {
            MemoryChunk::MInt8Signed
        } else if mnem_upper.contains("MOVB") || mnem_upper.ends_with("B") {
            MemoryChunk::MInt8Unsigned
        } else if mnem_upper.contains("MOVZW") {
            MemoryChunk::MInt16Unsigned
        } else if mnem_upper.contains("MOVSW") {
            MemoryChunk::MInt16Signed
        } else if mnem_upper.contains("MOVW") || mnem_upper.ends_with("W") {
            MemoryChunk::MInt16Unsigned
        } else if mnem_upper.contains("MOVL") || mnem_upper.ends_with("L") {
            MemoryChunk::MInt32
        } else if mnem_upper.contains("MOVQ") || mnem_upper.ends_with("Q") {
            MemoryChunk::MInt64
        } else if mnem_upper.contains("MOVSS") {
            MemoryChunk::MFloat32
        } else if mnem_upper.contains("MOVSD") {
            MemoryChunk::MFloat64
        } else {
            MemoryChunk::MAny64
        };

    mach_inst(addr, MachInst::Mload(*memory_chunk, addressing, Arc::new(args), *dst)) <--
        transl_load(addr, memory_chunk, addrmode, regs, dst),
        !addrmode_needs_resolution(*addrmode, _),
        if let Ok((addressing, args)) = transl_addressing_rev(*addrmode, None);

    mach_inst(addr, MachInst::Mload(*mc, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), dst)) <--
        pmov(addr, dst_sym, src),
        op_register(dst_sym, dst_str),
        let dst = Mreg::from(dst_str),
        op_indirect(src, _, base_str, _, _, disp, _),
        reg_ip(*base_str),
        rip_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        ireg_hold_type(dst_str.to_string(), typ),
        type_to_memchunk(typ, mc);

    mach_inst(addr, MachInst::Mstore(*mc, Addressing::Aglobal(*ident, *offset), Arc::new(vec![]), src)) <--
        pmov(addr, dst, src_sym),
        op_register(src_sym, src_str),
        let src = Mreg::from(src_str),
        op_indirect(dst, _, base_str, _, _, disp, _),
        reg_ip(*base_str),
        rip_target_addr(addr, target_addr),
        resolved_addr_to_symbol(target_addr, ident, offset),
        ireg_hold_type(src_str.to_string(), typ),
        type_to_memchunk(typ, mc);


    mach_inst(address, MachInst::Mop(Operation::Omove, Arc::new(args), *res)) <--
        pmov(address, rd, rs),
        op_register(rd, res_str),
        ireg_of(preg_of_r, Ireg::from(res_str)),
        preg_of(res, preg_of_r),
        op_register(rs, arg_str),
        ireg_of(preg_of_rs, Ireg::from(arg_str)),
        preg_of(arg, preg_of_rs),
        let args = vec![*arg];

    mach_inst(address, MachInst::Mop(Operation::Omove, Arc::new(vec![src]), dst)) <--
        pmov(address, rd, rs),
        op_register(rd, dst_str),
        reg_xmm(dst_str),
        op_register(rs, src_str),
        let dst = Mreg::from(dst_str),
        let src = Mreg::from(src_str);

    mach_inst(address, MachInst::Mop(Operation::Omove, Arc::new(vec![src]), dst)) <--
        pmov(address, rd, rs),
        op_register(rd, dst_str),
        op_register(rs, src_str),
        reg_xmm(src_str),
        let dst = Mreg::from(dst_str),
        let src = Mreg::from(src_str);

    mach_inst(address, MachInst::Mop(Operation::Ointconst(imm_int), Arc::new(args), *res)) <--
        pmov(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, res_str),
        !reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        let args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Olongconst(imm_int), Arc::new(args), *res)) <--
        pmov(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, res_str),
        reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        let args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Ointconst(0), Arc::new(args), *res)) <--
        pxor(address, r, r0),
        if r == r0,
        op_register(r, res_str),
        !reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        let args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Olongconst(0), Arc::new(args), *res)) <--
        pxor(address, r, r0),
        if r == r0,
        op_register(r, res_str),
        reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        let args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Oindirectsymbol(*imm_str as usize), Arc::new(args), *res)) <--
        pmov(address, r, symid),
        op_immediate(symid, imm_str, _),
        op_register(r, res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        if *imm_str != 0,
        symbols(*imm_str as Address, _, _),
        let args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Ointconst(*imm_str as i64), Arc::new(args), *res)) <--
        pmov(address, r, symid),
        op_immediate(symid, imm_str, _),
        op_register(r, res_str),
        !reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        let args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Olongconst(*imm_str as i64), Arc::new(args), *res)) <--
        pmov(address, r, symid),
        op_immediate(symid, imm_str, _),
        op_register(r, res_str),
        reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        let args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Ointconst(*imm_str), Arc::new(args), *res)) <--
        pmov(address, r, symid),
        op_immediate(symid, imm_str, _),
        op_register(r, res_str),
        !reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        if *imm_str != 0,
        !symbols(*imm_str as Address, _, _),
        let args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Olongconst(*imm_str), Arc::new(args), *res)) <--
        pmov(address, r, symid),
        op_immediate(symid, imm_str, _),
        op_register(r, res_str),
        reg_64(res_str),
        let res_ireg = Ireg::from(res_str),
        ireg_of(preg_of_r, res_ireg),
        preg_of(res, preg_of_r),
        if *imm_str != 0,
        !symbols(*imm_str as Address, _, _),
        let args = vec![];

    mach_inst(address, MachInst::Mop(cast_op, Arc::new(args.clone()), *res)) <--
        pmov(address, r, r1),
        op_register(r1, r1_str),
        op_register(r, r_str),
        reg_is_64(r1_str, r1_is_64),
        reg_is_64(r_str, r_is_64),
        if r1_is_64 != r_is_64,
        ireg_of(preg_of_r1, Ireg::from(r1_str)),
        preg_of(a1, preg_of_r1),
        ireg_of(preg_of_res, Ireg::from(r_str)),
        preg_of(res, preg_of_res),
        instruction(address, _, mnem, _, _, _, _, _, _, _),
        let mnem_upper = mnem.to_ascii_uppercase(),
        let args = vec![*a1],
        let cast_op = if mnem_upper.starts_with("MOVZX") || mnem_upper.starts_with("MOVZB") {
            if is_reg_8(r1_str) {
                Operation::Ocast8unsigned
            } else {
                Operation::Ocast16unsigned
            }
        } else if mnem_upper.starts_with("MOVSXD") || mnem_upper.starts_with("CDQE") {
            Operation::Ocast32signed
        } else if mnem_upper.starts_with("MOVSX") || mnem_upper.starts_with("MOVSB") || mnem_upper.starts_with("MOVSW") {
            if is_reg_8(r1_str) {
                Operation::Ocast8signed
            } else {
                Operation::Ocast16signed
            }
        } else {
            Operation::Ocast8signed
        };

    mach_inst(address, MachInst::Mop(Operation::Oneg, Arc::new(args), *res)) <--
        pneg(address, r),
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        psub(address, r, r2),
        instruction(address, _, mnem, _, _, _, _, _, _, _),
        op_register(r, r_str),
        op_register(r2, r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2],
        let mnem_upper = mnem.to_ascii_uppercase(),
        let op = if mnem_upper.ends_with("L") || mnem_upper.contains("SUBL") {
            Operation::Osub
        } else {
            Operation::Osubl
        };

    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        psbb(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_is_64(r_str, r_is_64),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2],
        let op = if *r_is_64 { Operation::Osubl } else { Operation::Osub };

    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        padc(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_is_64(r_str, r_is_64),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2],
        let op = if *r_is_64 { Operation::Oaddl } else { Operation::Oadd };

    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        psbb(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_is_64(r_str, r_is_64),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res],
        let op = if *r_is_64 { Operation::Oaddlimm(-imm_int) } else { Operation::Oaddimm(-imm_int) };

    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        padc(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_is_64(r_str, r_is_64),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res],
        let op = if *r_is_64 { Operation::Oaddlimm(imm_int) } else { Operation::Oaddimm(imm_int) };

    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        padd(address, r, r2),
        instruction(address, _, mnem, _, _, _, _, _, _, _),
        op_register(r, r_str),
        op_register(r2, r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2],
        let mnem_upper = mnem.to_ascii_uppercase(),
        let op = if mnem_upper.ends_with("L") || mnem_upper.contains("ADDL") {
            Operation::Oadd
        } else {
            Operation::Oaddl
        };

    mach_inst(address, MachInst::Mop(Operation::Olea(addressing), Arc::new(empty_args), *res)) <--
        plea(address, dst_reg, src_addr),
        op_register(dst_reg, dst_str),
        op_indirect(src_addr, _, base_str, _, _, offset, _),
        reg_sp(base_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(res, preg_of_dst),
        let addressing = Addressing::Ainstack(*offset),
        let empty_args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Olea(addressing), Arc::new(empty_args), *res)) <--
        pmov(address, dst_reg, src_addr),
        op_register(dst_reg, dst_str),
        op_indirect(src_addr, _, base_str, _, _, offset, _),
        reg_sp(base_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(res, preg_of_dst),
        let addressing = Addressing::Ainstack(*offset),
        let empty_args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Olea(addressing), Arc::new(empty_args), *res)) <--
        pmov(address, dst_reg, src_reg),
        op_register(src_reg, src_str),
        reg_sp(src_str),
        op_register(dst_reg, dst_str),
        !reg_sp(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(res, preg_of_dst),
        stack_offset(_, address, rsp_ofs),
        let addressing = Addressing::Ainstack(rsp_ofs.0),
        let empty_args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Ointconst(*symbol_addr), Arc::new(empty_args), *res)) <--
        pmov(address, dst_reg, src_addr),
        op_register(dst_reg, dst_str),
        op_immediate(src_addr, symbol_addr, _),
        !reg_64(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(res, preg_of_dst),
        symbols(*symbol_addr as Address, _, _),
        let empty_args = vec![];

    mach_inst(address, MachInst::Mop(Operation::Olongconst(*symbol_addr), Arc::new(empty_args), *res)) <--
        pmov(address, dst_reg, src_addr),
        op_register(dst_reg, dst_str),
        op_immediate(src_addr, symbol_addr, _),
        reg_64(dst_str),
        ireg_of(preg_of_dst, Ireg::from(dst_str)),
        preg_of(res, preg_of_dst),
        symbols(*symbol_addr as Address, _, _),
        let empty_args = vec![];

    mach_inst(addr, MachInst::Mcall(Either::Right(Either::Left(symbol_name)))) <--
        instruction(addr, _, _, "CALL", dst, _, _, _, _, _),
        op_immediate(dst, imm_addr, _),
        symbols(*imm_addr as Address, symbol_name, _);

    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        padd(address, r, n),
        instruction(address, _, mnem, _, _, _, _, _, _, _),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res],
        let mnem_upper = mnem.to_ascii_uppercase(),
        let op = if mnem_upper.ends_with("L") || mnem_upper.contains("ADDL") {
            Operation::Oaddimm(imm_int)
        } else {
            Operation::Oaddlimm(imm_int)
        };

    mach_inst(address, MachInst::Mop(Operation::Omul, Arc::new(args), *res)) <--
        pimul(address, r, r2),
        op_register(r, r_str),
        ireg_hold_type(r_str.to_string(), typ),
        if *typ == Typ::Tint,
        op_register(r2, r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];


    mach_inst(address, MachInst::Mop(Operation::Omulimm(imm_int), Arc::new(args), *res)) <--
        pimul(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];


    mach_inst(address, MachInst::Mop(Operation::Omul, Arc::new(args), *res)) <--
        pimul(address, r, mem),
        op_register(r, r_str),
        ireg_hold_type(r_str.to_string(), typ),
        if *typ == Typ::Tint,
        op_indirect(mem, _, base_str, _, _, disp, _),
        if !base_str.is_empty() && *base_str != "NONE",
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_base, Ireg::from(base_str)),
        preg_of(base_arg, preg_of_base),
        let args = vec![*res, *base_arg];

    mach_inst(address, MachInst::Mop(Operation::Omull, Arc::new(args), *res)) <--
        pimul(address, r, mem),
        op_register(r, r_str),
        ireg_hold_type(r_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        op_indirect(mem, _, base_str, _, _, disp, _),
        if !base_str.is_empty() && *base_str != "NONE",
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_base, Ireg::from(base_str)),
        preg_of(base_arg, preg_of_base),
        let args = vec![*res, *base_arg];

    mach_inst(address, MachInst::Mop(Operation::Omulhs, Arc::new(args), Mreg::DX)) <--
        pmul(address, r2),
        instruction(address, _, _, mnem, _, _, _, _, _, _),
        if mnem.contains("IMUL"),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tint,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    mach_inst(address, MachInst::Mop(Operation::Omulhu, Arc::new(args), Mreg::DX)) <--
        pmul(address, r2),
        instruction(address, _, _, mnem, _, _, _, _, _, _),
        if mnem.contains("MUL") && !mnem.contains("IMUL"),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tint,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    mach_inst(address, MachInst::Mop(Operation::Omullhs, Arc::new(args), Mreg::DX)) <--
        pmul(address, r2),
        instruction(address, _, _, mnem, _, _, _, _, _, _),
        if mnem.contains("IMUL"),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    mach_inst(address, MachInst::Mop(Operation::Omullhu, Arc::new(args), Mreg::DX)) <--
        pmul(address, r2),
        instruction(address, _, _, mnem, _, _, _, _, _, _),
        if mnem.contains("MUL") && !mnem.contains("IMUL"),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // 32-bit signed div: CDQ before IDIV -> Odiv (result in AX)
    mach_inst(address, MachInst::Mop(Operation::Odiv, Arc::new(args), Mreg::AX)) <--
        pidiv(address, r2, _),
        prev_instr(address, prevaddr),
        pcast(prevaddr, _, _),
        instruction(prevaddr, _, _, "CDQ", _, _, _, _, _, _),
        op_register(r2, r2_str),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // 32-bit unsigned div: xor EDX,EDX before DIV -> Odivu (result in AX)
    mach_inst(address, MachInst::Mop(Operation::Odivu, Arc::new(args), Mreg::AX)) <--
        pudiv(address, r2, _),
        prev_instr(address, prevaddr),
        pxor(prevaddr, r, *r),
        op_register(r, r_str),
        if *r_str == "EDX" || *r_str == "RDX",
        op_register(r2, r2_str),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // 32-bit signed mod: CDQ before IDIV -> Omod (result in DX)
    mach_inst(address, MachInst::Mop(Operation::Omod, Arc::new(args), Mreg::DX)) <--
        pidiv(address, r2, _),
        prev_instr(address, prevaddr),
        pcast(prevaddr, _, _),
        instruction(prevaddr, _, _, "CDQ", _, _, _, _, _, _),
        op_register(r2, r2_str),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // 32-bit unsigned mod: xor EDX,EDX before DIV -> Omodu (result in DX)
    mach_inst(address, MachInst::Mop(Operation::Omodu, Arc::new(args), Mreg::DX)) <--
        pudiv(address, r2, _),
        prev_instr(address, prevaddr),
        pxor(prevaddr, r, *r),
        op_register(r, r_str),
        if *r_str == "EDX" || *r_str == "RDX",
        op_register(r2, r2_str),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // Fallback: IDIV without CDQ predecessor, treat as signed 32-bit
    mach_inst(address, MachInst::Mop(Operation::Odiv, Arc::new(args), Mreg::AX)) <--
        pidiv(address, r2, _),
        prev_instr(address, prevaddr),
        !pcast(prevaddr, _, _),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tint,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    mach_inst(address, MachInst::Mop(Operation::Omod, Arc::new(args), Mreg::DX)) <--
        pidiv(address, r2, _),
        prev_instr(address, prevaddr),
        !pcast(prevaddr, _, _),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tint,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // Fallback: DIV without xor RDX predecessor, treat as unsigned 32-bit
    mach_inst(address, MachInst::Mop(Operation::Odivu, Arc::new(args), Mreg::AX)) <--
        pudiv(address, r2, _),
        prev_instr(address, prevaddr),
        !pxor(prevaddr, _, _),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tint,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    mach_inst(address, MachInst::Mop(Operation::Omodu, Arc::new(args), Mreg::DX)) <--
        pudiv(address, r2, _),
        prev_instr(address, prevaddr),
        !pxor(prevaddr, _, _),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tint,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];


    mach_inst(address, MachInst::Mop(Operation::Oand, Arc::new(args), *res)) <--
        pand(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];

    mach_inst(address, MachInst::Mop(Operation::Oandimm(imm_int), Arc::new(args), *res)) <--
        pand(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oor, Arc::new(args), *res)) <--
        por(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];

    mach_inst(address, MachInst::Mop(Operation::Oorimm(imm_int), Arc::new(args), *res)) <--
        por(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oxor, Arc::new(args), *res)) <--
        pxor(address, r, r2),
        if r!=r2,
        op_register(r, r_str),
        op_register(r2, r2_str),
        !reg_64(r_str),
        !reg_64(r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];

    mach_inst(address, MachInst::Mop(Operation::Oxorimm(imm_int), Arc::new(args), *res)) <--
        pxor(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        !reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Onot, Arc::new(args), *res)) <--
        pnot(address, r),
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oshl, Arc::new(args), *res)) <--
        psal(address, r, cxreg),
        op_register(cxreg, cxreg_str),
        reg_cx(cxreg_str),
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res, Mreg::CX];

    mach_inst(address, MachInst::Mop(Operation::Oshlimm(imm_int), Arc::new(args), *res)) <--
        psal(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oshr, Arc::new(args), *res)) <--
        psar(address, r, cxreg),
        op_register(cxreg, cxreg_str),
        reg_cx(cxreg_str),
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res, Mreg::CX];

    mach_inst(address, MachInst::Mop(Operation::Oshrimm(imm_int), Arc::new(args), *res)) <--
        psar(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oshru, Arc::new(args), *res)) <--
        pshr(address, r, cxreg),
        op_register(cxreg, cxreg_str),
        reg_cx(cxreg_str),
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res, Mreg::CX];

    mach_inst(address, MachInst::Mop(Operation::Oshruimm(imm_int), Arc::new(args), *res)) <--
        pshr(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Ororimm(imm_int), Arc::new(args), *res)) <--
        pror(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Ororimm(32 - imm_int), Arc::new(args), *res)) <--
        prol(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        !reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Ororlimm(64 - imm_int), Arc::new(args), *res)) <--
        prol(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oshldimm(imm_int), Arc::new(args), *res)) <--
        psal(address, r, r2),
        op_indirect(_, r, _, r_str, _, n, _),
        let imm_int = *n as i64,
        op_register(r2, r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];

    mach_inst(address, MachInst::Mop(Operation::Olea(addr), Arc::new(vec![]), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, r_str, _, scale, disp, _),
        reg_sp(*r_str),
        op_register(r, res_str),
        reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        let addr = Addressing::Ainstack(*disp);

    mach_inst(address, MachInst::Mop(Operation::Olea(addr), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, r_str, index_str, scale, disp, _),
        !reg_sp(*r_str), !reg_bp(*r_str),
        if *index_str == "NONE" || index_str.is_empty(),
        op_register(r, res_str),
        reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(arg, preg_of_r),
        let args = vec![*arg],
        let addr = Addressing::Aindexed(*disp);


    mach_inst(address, MachInst::Mop(Operation::Olea(addr), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, index_str, scale, disp, _),
        if *index_str != "NONE" && !index_str.is_empty(),
        !reg_sp(*base_str), !reg_bp(*base_str), !reg_ip(*base_str),
        if *scale == 1,
        op_register(r, res_str),
        reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        ireg_of(preg_of_base, Ireg::from(base_str)),
        preg_of(base_arg, preg_of_base),
        ireg_of(preg_of_index, Ireg::from(index_str)),
        preg_of(index_arg, preg_of_index),
        let args = vec![*base_arg, *index_arg],
        let addr = Addressing::Aindexed2(*disp);

    mach_inst(address, MachInst::Mop(Operation::Olea(addr), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, index_str, scale, disp, _),
        if *index_str != "NONE" && !index_str.is_empty(),
        !reg_sp(*base_str), !reg_bp(*base_str), !reg_ip(*base_str),
        if *scale > 1,
        op_register(r, res_str),
        reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        ireg_of(preg_of_base, Ireg::from(base_str)),
        preg_of(base_arg, preg_of_base),
        ireg_of(preg_of_index, Ireg::from(index_str)),
        preg_of(index_arg, preg_of_index),
        let args = vec![*base_arg, *index_arg],
        let addr = Addressing::Aindexed2scaled(*scale, *disp);

    mach_inst(address, MachInst::Mop(Operation::Olea(addr), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, index_str, scale, disp, _),
        if *index_str != "NONE" && !index_str.is_empty(),
        if *base_str == "NONE" || base_str.is_empty(),
        op_register(r, res_str),
        reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        ireg_of(preg_of_index, Ireg::from(index_str)),
        preg_of(index_arg, preg_of_index),
        let args = vec![*index_arg],
        let addr = Addressing::Ascaled(*scale, *disp);


    mach_inst(address, MachInst::Mop(Operation::Oindirectsymbol(*ident as usize), Arc::new(vec![]), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, _, _, disp, _),
        reg_ip(*base_str),
        rip_target_addr(address, target_addr),
        resolved_addr_to_symbol(target_addr, ident, _offset),
        op_register(r, res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res);

    mach_inst(address, MachInst::Mop(Operation::Olongconst(*target_addr as i64), Arc::new(vec![]), *res)) <--
        plea(address, r, am),
        op_indirect(am, _, base_str, _, _, disp, _),
        reg_ip(*base_str),
        rip_target_addr(address, target_addr),
        !resolved_addr_to_symbol(target_addr, _, _),
        op_register(r, res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res);


    mach_inst(address, MachInst::Mop(cast_op, Arc::new(args.clone()), *res)) <--
        pmov(address, r, r1),
        op_register(r1, r1_str),
        op_register(r, r_str),
        reg_is_64(r1_str, r1_is_64),
        reg_is_64(r_str, r_is_64),
        if r1_is_64 != r_is_64,
        ireg_of(preg_of_r1, Ireg::from(r1_str)),
        preg_of(a1, preg_of_r1),
        ireg_of(preg_of_res, Ireg::from(r_str)),
        preg_of(res, preg_of_res),
        instruction(address, _, mnem, _, _, _, _, _, _, _),
        let mnem_upper = mnem.to_ascii_uppercase(),
        let args = vec![*a1],
        let cast_op = if mnem_upper.starts_with("MOVSXD") || mnem_upper.starts_with("CDQE") {
            Operation::Ocast32signed
        } else if !*r1_is_64 && *r_is_64 {
            Operation::Ocast32unsigned
        } else {
            Operation::Olowlong
        };

    mach_inst(address, MachInst::Mop(Operation::Onegl, Arc::new(args), *res)) <--
        pneg(address, r),
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];


    mach_inst(address, MachInst::Mop(op, Arc::new(args), *res)) <--
        psub(address, r, n),
        instruction(address, _, mnem, _, _, _, _, _, _, _),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res],
        let mnem_upper = mnem.to_ascii_uppercase(),
        let op = if mnem_upper.ends_with("L") || mnem_upper.contains("SUBL") {
            Operation::Oaddimm(-imm_int)
        } else {
            Operation::Oaddlimm(-imm_int)
        };

    mach_inst(address, MachInst::Mop(Operation::Omull, Arc::new(args), *res)) <--
        pimul(address, r, r2),
        op_register(r, r_str),
        ireg_hold_type(r_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        op_register(r2, r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];

    mach_inst(address, MachInst::Mop(Operation::Omullimm(imm_int), Arc::new(args), *res)) <--
        pimul(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Omullhs, Arc::new(args), Mreg::DX)) <--
        pmul(address, r2),
        instruction(address, _, mnem, _, _, _, _, _, _, _),
        if mnem.contains("IMUL"),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX ,*a2];

    mach_inst(address, MachInst::Mop(Operation::Omullhu, Arc::new(args), Mreg::DX)) <--
        pmul(address, r2),
        instruction(address, _, mnem, _, _, _, _, _, _, _),
        if mnem.contains("MUL") && !mnem.contains("IMUL"),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX ,*a2];

    // 64-bit signed div: CQO before IDIV -> Odivl (result in AX)
    mach_inst(address, MachInst::Mop(Operation::Odivl, Arc::new(args), Mreg::AX)) <--
        pidiv(address, r2, _),
        prev_instr(address, prevaddr),
        pcast(prevaddr, _, _),
        instruction(prevaddr, _, _, "CQO", _, _, _, _, _, _),
        op_register(r2, r2_str),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // 64-bit unsigned div: xor RDX,RDX before DIV -> Odivlu (result in AX)
    mach_inst(address, MachInst::Mop(Operation::Odivlu, Arc::new(args), Mreg::AX)) <--
        pudiv(address, r2, _),
        prev_instr(address, prevaddr),
        pxor(prevaddr, r, *r),
        op_register(r, "RDX"),
        op_register(r2, r2_str),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // 64-bit signed mod: CQO before IDIV -> Omodl (result in DX)
    mach_inst(address, MachInst::Mop(Operation::Omodl, Arc::new(args), Mreg::DX)) <--
        pidiv(address, r2, _),
        prev_instr(address, prevaddr),
        pcast(prevaddr, _, _),
        instruction(prevaddr, _, _, "CQO", _, _, _, _, _, _),
        op_register(r2, r2_str),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // 64-bit unsigned mod: xor RDX,RDX before DIV -> Omodlu (result in DX)
    mach_inst(address, MachInst::Mop(Operation::Omodlu, Arc::new(args), Mreg::DX)) <--
        pudiv(address, r2, _),
        prev_instr(address, prevaddr),
        pxor(prevaddr, r, *r),
        op_register(r, "RDX"),
        op_register(r2, r2_str),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // Fallback: IDIV without CQO predecessor, treat as signed 64-bit
    mach_inst(address, MachInst::Mop(Operation::Odivl, Arc::new(args), Mreg::AX)) <--
        pidiv(address, r2, _),
        prev_instr(address, prevaddr),
        !pcast(prevaddr, _, _),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    mach_inst(address, MachInst::Mop(Operation::Omodl, Arc::new(args), Mreg::DX)) <--
        pidiv(address, r2, _),
        prev_instr(address, prevaddr),
        !pcast(prevaddr, _, _),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    // Fallback: DIV without xor RDX predecessor, treat as unsigned 64-bit
    mach_inst(address, MachInst::Mop(Operation::Odivlu, Arc::new(args), Mreg::AX)) <--
        pudiv(address, r2, _),
        prev_instr(address, prevaddr),
        !pxor(prevaddr, _, _),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    mach_inst(address, MachInst::Mop(Operation::Omodlu, Arc::new(args), Mreg::DX)) <--
        pudiv(address, r2, _),
        prev_instr(address, prevaddr),
        !pxor(prevaddr, _, _),
        op_register(r2, r2_str),
        ireg_hold_type(r2_str.to_string(), typ),
        if *typ == Typ::Tlong || *typ == Typ::Tany64,
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![Mreg::AX, *a2];

    mach_inst(address, MachInst::Mop(Operation::Oandl, Arc::new(args), *res)) <--
        pand(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];

    mach_inst(address, MachInst::Mop(Operation::Oandlimm(imm_int), Arc::new(args), *res)) <--
        pand(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oorl, Arc::new(args), *res)) <--
        por(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];

    mach_inst(address, MachInst::Mop(Operation::Oorlimm(imm_int), Arc::new(args), *res)) <--
        por(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oxorl, Arc::new(args), *res)) <--
        pxor(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_64(r_str),
        reg_64(r2_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        ireg_of(preg_of_r2, Ireg::from(r2_str)),
        preg_of(a2, preg_of_r2),
        let args = vec![*res, *a2];

    mach_inst(address, MachInst::Mop(Operation::Oxorlimm(imm_int), Arc::new(args), *res)) <--
        pxor(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        reg_64(r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Onotl, Arc::new(args), *res)) <--
        pnot(address, r),
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oshll, Arc::new(args), *res)) <--
        psal(address, r, cxreg),
        op_register(cxreg, cxreg_str),
        reg_cx(cxreg_str),
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res, Mreg::CX];

    mach_inst(address, MachInst::Mop(Operation::Oshllimm(imm_int), Arc::new(args), *res)) <--
        psal(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oshrl, Arc::new(args), *res)) <--
        psar(address, r, cxreg),
        op_register(cxreg, cxreg_str),
        reg_cx(cxreg_str),
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res, Mreg::CX];

    mach_inst(address, MachInst::Mop(Operation::Oshrlimm(imm_int), Arc::new(args), *res)) <--
        psar(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oshrlu, Arc::new(args), *res)) <--
        pshr(address, r, cxreg),
        op_register(cxreg, cxreg_str),
        reg_cx(cxreg_str),
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res, Mreg::CX];

    mach_inst(address, MachInst::Mop(Operation::Oshrluimm(imm_int), Arc::new(args), *res)) <--
        pshr(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Ororlimm(imm_int), Arc::new(args), *res)) <--
        pror(address, r, n),
        op_immediate(n, imm_str, _),
        let imm_int = *imm_str as i64,
        op_register(r, r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(res, preg_of_r),
        let args = vec![*res];

    mach_inst(address, MachInst::Mop(Operation::Oleal(addr), Arc::new(vec![]), *res)) <--
        plea(address, r, am),
        op_register(r, res_str),
        !reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        op_indirect(am, _, r_str, _, scale, disp, _),
        reg_sp(*r_str),
        let addr = Addressing::Ainstack(*disp);

    mach_inst(address, MachInst::Mop(Operation::Oleal(addr), Arc::new(args), *res)) <--
        plea(address, r, am),
        op_register(r, res_str),
        !reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        op_indirect(am, _, r_str, _, scale, disp, _),
        !reg_sp(*r_str), !reg_bp(*r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(arg, preg_of_r),
        let args = vec![*arg],
        let addr = Addressing::Aindexed(*disp);

    mach_inst(address, MachInst::Mop(Operation::Oleal(addr), Arc::new(vec![]), *res)) <--
        plea(address, r, am),
        padd(nextaddress, r_same, delta),
        next(address, nextaddress),
        op_register(r, res_str),
        op_register(r_same, res_str),
        !reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        op_indirect(am, _, r_str, _, scale, disp, _),
        reg_sp(*r_str),
        let addr = Addressing::Ainstack(*disp);

    mach_inst(address, MachInst::Mop(Operation::Oleal(addr), Arc::new(vec![]), *res)) <--
        plea(address, r, am),
        padd(nextaddress, r_same, delta),
        next(address, nextaddress),
        op_register(r, res_str),
        op_register(r_same, res_str),
        !reg_64(res_str),
        ireg_of(preg_of_res, Ireg::from(res_str)),
        preg_of(res, preg_of_res),
        op_indirect(am, _, r_str, _, scale, disp, _),
        !reg_sp(*r_str), !reg_bp(*r_str),
        ireg_of(preg_of_r, Ireg::from(r_str)),
        preg_of(arg, preg_of_r),
        let args = vec![*arg],
        let addr = Addressing::Aindexed(*disp);


    mach_inst(address, MachInst::Mop(Operation::Ointconst(0), Arc::new(vec![]), res)) <--
        ppxor(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        if *r_str == *r2_str,
        reg_xmm(r_str),
        let res = Mreg::from(r_str);

    mach_inst(address, MachInst::Mop(Operation::Ointconst(0), Arc::new(vec![]), res)) <--
        pxorpd(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        if *r_str == *r2_str,
        reg_xmm(r_str),
        let res = Mreg::from(r_str);

    mach_inst(address, MachInst::Mop(Operation::Ointconst(0), Arc::new(vec![]), res)) <--
        pxorps(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        if *r_str == *r2_str,
        reg_xmm(r_str),
        let res = Mreg::from(r_str);

    mach_inst(address, MachInst::Mop(Operation::Omove, Arc::new(args), res)) <--
        pmovsd(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(res_str),
        reg_xmm(arg_str),
        let res = Mreg::from(res_str),
        let arg = Mreg::from(arg_str),
        let args = vec![arg];

    mach_inst(addr, MachInst::Mload(MemoryChunk::MFloat64, addressing, Arc::new(args), dst)) <--
        pmovsd(addr, dst_sym, src),
        op_register(dst_sym, dst_str),
        reg_xmm(dst_str),
        let dst = Mreg::from(dst_str),
        op_indirect(src, _, r2, _, _scale, disp, _),
        if Mreg::from(r2) != Mreg::BP && Mreg::from(r2) != Mreg::SP,
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        if let Ok((addressing, args)) = transl_addressing_rev(addrmode, None);

    mach_inst(addr, MachInst::Mstore(MemoryChunk::MFloat64, addressing, Arc::new(args), src)) <--
        pmovsd(addr, dst, src_sym),
        op_register(src_sym, src_str),
        reg_xmm(src_str),
        let src = Mreg::from(src_str),
        op_indirect(dst, _, r2, _, _scale, disp, _),
        if Mreg::from(r2) != Mreg::BP && Mreg::from(r2) != Mreg::SP,
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        if let Ok((addressing, args)) = transl_addressing_rev(addrmode, None);

    mach_inst(address, MachInst::Mop(Operation::Ofloatoflong, Arc::new(args), res)) <--
        pcvtsi2sd(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(res_str),
        reg_64(arg_str),
        let res = Mreg::from(res_str),
        let arg = Mreg::from(arg_str),
        let args = vec![arg];

    mach_inst(address, MachInst::Mop(Operation::Ofloatofint, Arc::new(args), res)) <--
        pcvtsi2sd(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(res_str),
        reg_is_64(arg_str, false),
        let res = Mreg::from(res_str),
        let arg = Mreg::from(arg_str),
        let args = vec![arg];

    mach_inst(address, MachInst::Mop(Operation::Olongoffloat, Arc::new(args), res)) <--
        pcvtsd2si(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(arg_str),
        reg_64(res_str),
        let res = Mreg::from(res_str),
        let arg = Mreg::from(arg_str),
        let args = vec![arg];

    mach_inst(address, MachInst::Mop(Operation::Ointoffloat, Arc::new(args), res)) <--
        pcvtsd2si(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(arg_str),
        reg_is_64(res_str, false),
        let res = Mreg::from(res_str),
        let arg = Mreg::from(arg_str),
        let args = vec![arg];

    mach_inst(address, MachInst::Mop(Operation::Oaddf, Arc::new(args), res)) <--
        paddsd(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::from(r_str),
        let a2 = Mreg::from(r2_str),
        let args = vec![res, a2];

    mach_inst(address, MachInst::Mop(Operation::Osubf, Arc::new(args), res)) <--
        psubsd(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::from(r_str),
        let a2 = Mreg::from(r2_str),
        let args = vec![res, a2];

    mach_inst(address, MachInst::Mop(Operation::Omulf, Arc::new(args), res)) <--
        pmulsd(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::from(r_str),
        let a2 = Mreg::from(r2_str),
        let args = vec![res, a2];

    mach_inst(address, MachInst::Mop(Operation::Odivf, Arc::new(args), res)) <--
        pdivsd(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::from(r_str),
        let a2 = Mreg::from(r2_str),
        let args = vec![res, a2];


    mach_inst(address, MachInst::Mop(Operation::Oaddfs, Arc::new(args), res)) <--
        paddss(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::from(r_str),
        let a2 = Mreg::from(r2_str),
        let args = vec![res, a2];

    mach_inst(address, MachInst::Mop(Operation::Osubfs, Arc::new(args), res)) <--
        psubss(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::from(r_str),
        let a2 = Mreg::from(r2_str),
        let args = vec![res, a2];

    mach_inst(address, MachInst::Mop(Operation::Omulfs, Arc::new(args), res)) <--
        pmulss(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::from(r_str),
        let a2 = Mreg::from(r2_str),
        let args = vec![res, a2];

    mach_inst(address, MachInst::Mop(Operation::Odivfs, Arc::new(args), res)) <--
        pdivss(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::from(r_str),
        let a2 = Mreg::from(r2_str),
        let args = vec![res, a2];


    mach_inst(address, MachInst::Mop(Operation::Oaddf, Arc::new(args), res)) <--
        instruction(address, _, _, "VADDSD", src1, dst, src2, _, _, _),
        op_register(dst, dst_str),
        op_register(src1, src1_str),
        op_register(src2, src2_str),
        reg_xmm(dst_str),
        let res = Mreg::from(dst_str),
        let a1 = Mreg::from(src1_str),
        let a2 = Mreg::from(src2_str),
        let args = vec![a1, a2];

    mach_inst(address, MachInst::Mop(Operation::Osubf, Arc::new(args), res)) <--
        instruction(address, _, _, "VSUBSD", src1, dst, src2, _, _, _),
        op_register(dst, dst_str),
        op_register(src1, src1_str),
        op_register(src2, src2_str),
        reg_xmm(dst_str),
        let res = Mreg::from(dst_str),
        let a1 = Mreg::from(src1_str),
        let a2 = Mreg::from(src2_str),
        let args = vec![a1, a2];

    mach_inst(address, MachInst::Mop(Operation::Omulf, Arc::new(args), res)) <--
        instruction(address, _, _, "VMULSD", src1, dst, src2, _, _, _),
        op_register(dst, dst_str),
        op_register(src1, src1_str),
        op_register(src2, src2_str),
        reg_xmm(dst_str),
        let res = Mreg::from(dst_str),
        let a1 = Mreg::from(src1_str),
        let a2 = Mreg::from(src2_str),
        let args = vec![a1, a2];

    mach_inst(address, MachInst::Mop(Operation::Odivf, Arc::new(args), res)) <--
        instruction(address, _, _, "VDIVSD", src1, dst, src2, _, _, _),
        op_register(dst, dst_str),
        op_register(src1, src1_str),
        op_register(src2, src2_str),
        reg_xmm(dst_str),
        let res = Mreg::from(dst_str),
        let a1 = Mreg::from(src1_str),
        let a2 = Mreg::from(src2_str),
        let args = vec![a1, a2];

    mach_inst(address, MachInst::Mop(Operation::Oaddfs, Arc::new(args), res)) <--
        instruction(address, _, _, "VADDSS", src1, dst, src2, _, _, _),
        op_register(dst, dst_str),
        op_register(src1, src1_str),
        op_register(src2, src2_str),
        reg_xmm(dst_str),
        let res = Mreg::from(dst_str),
        let a1 = Mreg::from(src1_str),
        let a2 = Mreg::from(src2_str),
        let args = vec![a1, a2];

    mach_inst(address, MachInst::Mop(Operation::Osubfs, Arc::new(args), res)) <--
        instruction(address, _, _, "VSUBSS", src1, dst, src2, _, _, _),
        op_register(dst, dst_str),
        op_register(src1, src1_str),
        op_register(src2, src2_str),
        reg_xmm(dst_str),
        let res = Mreg::from(dst_str),
        let a1 = Mreg::from(src1_str),
        let a2 = Mreg::from(src2_str),
        let args = vec![a1, a2];

    mach_inst(address, MachInst::Mop(Operation::Omulfs, Arc::new(args), res)) <--
        instruction(address, _, _, "VMULSS", src1, dst, src2, _, _, _),
        op_register(dst, dst_str),
        op_register(src1, src1_str),
        op_register(src2, src2_str),
        reg_xmm(dst_str),
        let res = Mreg::from(dst_str),
        let a1 = Mreg::from(src1_str),
        let a2 = Mreg::from(src2_str),
        let args = vec![a1, a2];

    mach_inst(address, MachInst::Mop(Operation::Odivfs, Arc::new(args), res)) <--
        instruction(address, _, _, "VDIVSS", src1, dst, src2, _, _, _),
        op_register(dst, dst_str),
        op_register(src1, src1_str),
        op_register(src2, src2_str),
        reg_xmm(dst_str),
        let res = Mreg::from(dst_str),
        let a1 = Mreg::from(src1_str),
        let a2 = Mreg::from(src2_str),
        let args = vec![a1, a2];


    mach_inst(address, MachInst::Mop(Operation::Osingleoffloat, Arc::new(args), res)) <--
        pcvtsd2ss(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(res_str),
        let res = Mreg::from(res_str),
        let arg = Mreg::from(arg_str),
        let args = vec![arg];

    mach_inst(address, MachInst::Mop(Operation::Ofloatofsingle, Arc::new(args), res)) <--
        pcvtss2sd(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(res_str),
        let res = Mreg::from(res_str),
        let arg = Mreg::from(arg_str),
        let args = vec![arg];


    mach_inst(address, MachInst::Mop(Operation::Osingleofint, Arc::new(args), res)) <--
        pcvtsi2ss(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(res_str),
        reg_is_64(arg_str, false),
        let res = Mreg::from(res_str),
        let arg = Mreg::from(arg_str),
        let args = vec![arg];

    mach_inst(address, MachInst::Mop(Operation::Osingleoflong, Arc::new(args), res)) <--
        pcvtsi2ss(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(res_str),
        reg_64(arg_str),
        let res = Mreg::from(res_str),
        let arg = Mreg::from(arg_str),
        let args = vec![arg];

    mach_inst(address, MachInst::Mop(Operation::Ointofsingle, Arc::new(args), res)) <--
        pcvtss2si(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(arg_str),
        reg_is_64(res_str, false),
        let res = Mreg::from(res_str),
        let arg = Mreg::from(arg_str),
        let args = vec![arg];

    mach_inst(address, MachInst::Mop(Operation::Olongofsingle, Arc::new(args), res)) <--
        pcvtss2si(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(arg_str),
        reg_64(res_str),
        let res = Mreg::from(res_str),
        let arg = Mreg::from(arg_str),
        let args = vec![arg];


    mach_inst(address, MachInst::Mop(Operation::Onegf, Arc::new(args), res)) <--
        pxorpd(address, r, r2),
        op_register(r, r_str),
        reg_xmm(r_str),
        op_indirect(r2, _, _, _, _, _, _),
        let res = Mreg::from(r_str),
        let args = vec![res];

    mach_inst(address, MachInst::Mop(Operation::Oabsf, Arc::new(args), res)) <--
        pandpd(address, r, r2),
        op_register(r, r_str),
        reg_xmm(r_str),
        op_indirect(r2, _, _, _, _, _, _),
        let res = Mreg::from(r_str),
        let args = vec![res];

    mach_inst(address, MachInst::Mop(Operation::Onegfs, Arc::new(args), res)) <--
        pxorps(address, r, r2),
        op_register(r, r_str),
        reg_xmm(r_str),
        op_indirect(r2, _, _, _, _, _, _),
        let res = Mreg::from(r_str),
        let args = vec![res];

    mach_inst(address, MachInst::Mop(Operation::Oabsfs, Arc::new(args), res)) <--
        pandps(address, r, r2),
        op_register(r, r_str),
        reg_xmm(r_str),
        op_indirect(r2, _, _, _, _, _, _),
        let res = Mreg::from(r_str),
        let args = vec![res];


    mach_inst(address, MachInst::Mop(Operation::Omaxf, Arc::new(args), res)) <--
        pmaxsd(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::from(r_str),
        let a2 = Mreg::from(r2_str),
        let args = vec![res, a2];

    mach_inst(address, MachInst::Mop(Operation::Ominf, Arc::new(args), res)) <--
        pminsd(address, r, r2),
        op_register(r, r_str),
        op_register(r2, r2_str),
        reg_xmm(r_str),
        let res = Mreg::from(r_str),
        let a2 = Mreg::from(r2_str),
        let args = vec![res, a2];


    mach_inst(addr0, MachInst::Mcond(Condition::Ccompf(Comparison::Cgt), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomisd(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::from(r1_str),
        let arg2 = Mreg::from(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondA, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompf(Comparison::Cge), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomisd(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::from(r1_str),
        let arg2 = Mreg::from(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondAe, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompf(Comparison::Clt), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomisd(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::from(r1_str),
        let arg2 = Mreg::from(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondB, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompf(Comparison::Cle), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomisd(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::from(r1_str),
        let arg2 = Mreg::from(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondBe, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompf(Comparison::Ceq), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomisd(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::from(r1_str),
        let arg2 = Mreg::from(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondE, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Cnotcompf(Comparison::Ceq), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomisd(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::from(r1_str),
        let arg2 = Mreg::from(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondNe, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompfs(Comparison::Cgt), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomiss(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::from(r1_str),
        let arg2 = Mreg::from(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondA, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompfs(Comparison::Cge), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomiss(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::from(r1_str),
        let arg2 = Mreg::from(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondAe, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompfs(Comparison::Clt), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomiss(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::from(r1_str),
        let arg2 = Mreg::from(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondB, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompfs(Comparison::Cle), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomiss(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::from(r1_str),
        let arg2 = Mreg::from(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondBe, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Ccompfs(Comparison::Ceq), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomiss(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::from(r1_str),
        let arg2 = Mreg::from(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondE, lbl);

    mach_inst(addr0, MachInst::Mcond(Condition::Cnotcompfs(Comparison::Ceq), Arc::new(vec![arg1, arg2]), lbl)) <--
        pucomiss(addr0, r1, r2),
        op_register(r1, r1_str),
        op_register(r2, r2_str),
        reg_xmm(r1_str),
        let arg1 = Mreg::from(r1_str),
        let arg2 = Mreg::from(r2_str),
        fcmp_jcc_link(addr0, addr1),
        pjcc(addr1, TestCond::CondNe, lbl);


    mach_inst(address, MachInst::Mop(Operation::Omove, Arc::new(args), res)) <--
        pmovss(address, rd, rs),
        op_register(rd, res_str),
        op_register(rs, arg_str),
        reg_xmm(res_str),
        reg_xmm(arg_str),
        let res = Mreg::from(res_str),
        let arg = Mreg::from(arg_str),
        let args = vec![arg];

    mach_inst(addr, MachInst::Mload(MemoryChunk::MFloat32, addressing, Arc::new(args), dst)) <--
        pmovss(addr, dst_sym, src),
        op_register(dst_sym, dst_str),
        reg_xmm(dst_str),
        let dst = Mreg::from(dst_str),
        op_indirect(src, _, r2, _, _scale, disp, _),
        if Mreg::from(r2) != Mreg::BP && Mreg::from(r2) != Mreg::SP,
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        if let Ok((addressing, args)) = transl_addressing_rev(addrmode, None);

    mach_inst(addr, MachInst::Mstore(MemoryChunk::MFloat32, addressing, Arc::new(args), src)) <--
        pmovss(addr, dst, src_sym),
        op_register(src_sym, src_str),
        reg_xmm(src_str),
        let src = Mreg::from(src_str),
        op_indirect(dst, _, r2, _, _scale, disp, _),
        if Mreg::from(r2) != Mreg::BP && Mreg::from(r2) != Mreg::SP,
        let addrmode = Addrmode{
            base: Some(Ireg::from(r2)),
            index: None,
            disp: Displacement::from(*disp),
        },
        if let Ok((addressing, args)) = transl_addressing_rev(addrmode, None);

    expand_builtin_inline(addr, "__builtin_bswap", Arc::new(vec![]), BuiltinArg::BA(Mreg::from(Ireg::from(r_str)))) <--
        pswap(addr, res),
        op_register(res, r_str);

    expand_builtin_inline(
        addr,
        "__builtin_bswap",
        Arc::new(vec![BuiltinArg::BA(Mreg::from(Ireg::from(a1)))]),
        BuiltinArg::BA(Mreg::from(Ireg::from(r_str)))
    ) <--
        pmov(addr, res, a1),
        op_register(res, r_str),
        op_register(a1, a1_str),
        pswap(addr1, res),
        next(addr, addr1),
        if a1 != res;

    expand_builtin_inline(
        addr,
        "__builtin_clz",
        Arc::new(vec![BuiltinArg::BA(Mreg::from(Ireg::from(a1)))]),
        BuiltinArg::BA(Mreg::from(Ireg::from(r_str)))
    ) <--
        pbsr(addr, res, a1),
        op_register(res, r_str),
        op_register(a1, a1_str),
        pxor(addr1, res, n),
        op_immediate(n, imm_str, _),
        if *imm_str == 31,
        next(addr, addr1);

    expand_builtin_inline(
        addr,
        "__builtin_clzl",
        Arc::new(vec![BuiltinArg::BA(Mreg::from(Ireg::from(a1)))]),
        BuiltinArg::BA(Mreg::from(Ireg::from(r_str)))
    ) <--
        pbsr(addr, res, a1),
        op_register(res, r_str),
        op_register(a1, a1_str),
        pxor(addr1, res, n),
        op_immediate(n, imm_str, _),
        if *imm_str == 31,
        next(addr, addr1);

    expand_builtin_inline(
        addr,
        "__builtin_clzl",
        Arc::new(vec![BuiltinArg::BA(Mreg::from(Ireg::from(a1)))]),
        BuiltinArg::BA(Mreg::from(Ireg::from(r_str)))
    ) <--
        pbsr(addr, res, a1),
        op_register(res, r_str),
        op_register(a1, a1_str),
        pxor(addr1, res, n),
        op_immediate(n, imm_str, _),
        if *imm_str == 63,
        next(addr, addr1);

    expand_builtin_inline(
        addr,
        "__builtin_clzll",
        Arc::new(vec![BuiltinArg::BA(Mreg::from(Ireg::from(a1)))]),
        BuiltinArg::BA(Mreg::from(Ireg::from(r_str)))
    ) <--
        pbsr(addr, res, a1),
        op_register(res, r_str),
        op_register(a1, a1_str),
        pxor(addr1, res, n),
        op_immediate(n, imm_str, _),
        if *imm_str == 63,
        next(addr, addr1);

    expand_builtin_inline(
        addr,
        "__builtin_ctz",
        Arc::new(vec![BuiltinArg::BA(Mreg::from(Ireg::from(a1)))]),
        BuiltinArg::BA(Mreg::from(Ireg::from(r_str)))
    ) <--
        pbsf(addr, res, a1),
        op_register(res, r_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_ctzl",
        Arc::new(vec![BuiltinArg::BA(Mreg::from(Ireg::from(a1)))]),
        BuiltinArg::BA(Mreg::from(Ireg::from(r_str)))
    ) <--
        pbsf(addr, res, a1),
        op_register(res, r_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_ctzl",
        Arc::new(vec![BuiltinArg::BA(Mreg::from(Ireg::from(a1)))]),
        BuiltinArg::BA(Mreg::from(Ireg::from(r_str)))
    ) <--
        pbsf(addr, res, a1),
        op_register(res, r_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_ctzll",
        Arc::new(vec![BuiltinArg::BA(Mreg::from(Ireg::from(a1)))]),
        BuiltinArg::BA(Mreg::from(Ireg::from(r_str)))
    ) <--
        pbsf(addr, res, a1),
        op_register(res, r_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_ctzll",
        Arc::new(vec![
            BuiltinArg::BA(Mreg::from(Ireg::from(ah))),
            BuiltinArg::BA(Mreg::from(Ireg::from(al)))
        ]),
        BuiltinArg::BA(Mreg::from(Ireg::from(res_str)))
    ) <--
        ptest(addr, al, *al),
        op_register(ah, ah_str),
        op_register(al, al_str),
        next(addr, addr1),
        pjcc(addr1, TestCond::CondE, lbl1),
        next(addr1, addr2),
        pbsf(addr2, res, al),
        op_register(res, res_str),
        next(addr2, addr3),
        pjmp(addr3, lbl2),
        next(addr3, addr4),
        plabel(addr4, lbl1),
        next(addr4, addr5),
        next(addr5, addr6),
        next(addr6, addr7),
        pbsf(addr5, res, ah),
        padd(addr6, res, n),
        op_immediate(n, imm_str, _),
        if *imm_str == 32,
        plabel(addr7, lbl2);

    expand_builtin_inline(
        addr,
        "__builtin_fsqrt",
        Arc::new(vec![BuiltinArg::BA(Mreg::from(Ireg::from(a1)))]),
        BuiltinArg::BA(Mreg::from(Ireg::from(res_str)))
    ) <--
        psqrt(addr, res, a1),
        op_register(res, res_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_sqrt",
        Arc::new(vec![BuiltinArg::BA(Mreg::from(Ireg::from(a1)))]),
        BuiltinArg::BA(Mreg::from(Ireg::from(res_str)))
    ) <--
        psqrt(addr, res, a1),
        op_register(res, res_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_fsqrt",
        Arc::new(vec![BuiltinArg::BA(Mreg::from(Ireg::from(a1)))]),
        BuiltinArg::BA(Mreg::from(Ireg::from(res_str)))
    ) <--
        psqrtsd(addr, res, a1),
        op_register(res, res_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_sqrt",
        Arc::new(vec![BuiltinArg::BA(Mreg::from(Ireg::from(a1)))]),
        BuiltinArg::BA(Mreg::from(Ireg::from(res_str)))
    ) <--
        psqrtsd(addr, res, a1),
        op_register(res, res_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_fsqrt",
        Arc::new(vec![BuiltinArg::BA(Mreg::from(Ireg::from(a1)))]),
        BuiltinArg::BA(Mreg::from(Ireg::from(res_str)))
    ) <--
        psqrtss(addr, res, a1),
        op_register(res, res_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr,
        "__builtin_sqrt",
        Arc::new(vec![BuiltinArg::BA(Mreg::from(Ireg::from(a1)))]),
        BuiltinArg::BA(Mreg::from(Ireg::from(res_str)))
    ) <--
        psqrtss(addr, res, a1),
        op_register(res, res_str),
        op_register(a1, a1_str);

    expand_builtin_inline(
        addr1,
        "__builtin_negl",
        Arc::new(vec![
            BuiltinArg::BA(Mreg::from(Ireg::from(ah_str))),
            BuiltinArg::BA(Mreg::from(Ireg::from(al_str)))
        ]),
        BuiltinArg::BA(Mreg::from(Ireg::from(rh_str)))
    ) <--
        pneg(addr1, rl),
        next(addr1, addr2),
        padc(addr2, rh, _),
        next(addr2, addr3),
        pneg(addr3, rh),
        op_register(rh, rh_str),
        op_register(rl, rl_str),
        op_register(ah, ah_str),
        op_register(al, al_str);


    expand_builtin_inline(
        addr,
        "__builtin_va_start",
        Arc::new(vec![BuiltinArg::BA(Mreg::from(Ireg::from(*a)))]),
        BuiltinArg::BA(Mreg::from(Ireg::Unknown))
    ) <--
        expand_builtin_va_start_32(addr, a);

    expand_builtin_va_start_32(addr1, Ireg::from(reg2)) <--
        plea(addr1, rax, mem_addr),
        op_register(rax, "RAX"),
        op_indirect(mem_addr, "RSP", _, _, 1, ofs, _ ),
        next(addr1, addr2),
        pmov(addr2, r, rax),
        op_indirect(r, reg1, reg2, reg3, scale, disp, _),
        op_register(rax, "RAX");

    mach_inst(addr, MachInst::Mbuiltin((*name).to_string(), args.to_vec(), (*res).clone())) <--
        expand_builtin_inline(addr, name, args, res),
        builtins(*name);

    mach_inst(addr, MachInst::Mlabel((*lbl).to_string())) <--
        symbols(addr, lbl, _);


    pallocframe(addr, sz) <--
        psub(addr, rsp_sym, sz_sym),
        op_register(rsp_sym, rsp_str),
        reg_sp(rsp_str),
        op_immediate(sz_sym, sz, _);

    pfreeframe(addr1, sz_val) <--
        padd(addr1, rsp_sym, sz),
        op_register(rsp_sym, rsp_str),
        reg_sp(rsp_str),
        op_immediate(sz, sz_val, _),
        next(addr1, addr2),
        pret(addr2);

    pfreeframe(addr1, 0) <--
        ppop(addr1, rbp_sym),
        op_register(rbp_sym, rbp_str),
        reg_bp(rbp_str),
        next(addr1, addr2),
        pret(addr2);

    pfreeframe(addr1, sz_val) <--
        padd(addr1, rsp_sym, sz),
        op_register(rsp_sym, rsp_str),
        reg_sp(rsp_str),
        op_immediate(sz, sz_val, _),
        next(addr1, addr2),
        ppop(addr2, rbp_sym),
        op_register(rbp_sym, rbp_str),
        reg_bp(rbp_str),
        next(addr2, addr3),
        pret(addr3);

    pfreeframe(addr, 0), stack_offset(func_start, addr, Dual(0)) <--
        instruction(addr, _, _, "LEAVE", src, dst, _, _, _, _),
        instr_in_function(addr, func_start),
        next(prevaddr, addr),
        stack_offset(func_start, prevaddr, Dual(0));


    potential_end_addr(func_addr, next_addr) <--
        symbols(func_addr, _, _),
        function_symbol(next_addr, _),
        if next_addr > func_addr;

    next_function_addr(func_addr, end_addr) <--
        potential_end_addr(func_addr, _),
        agg end_addr = aggregators::min(next_addr) in potential_end_addr(func_addr, next_addr);

    pallocframe_by_func(func_name, alloc_address, stack_size) <--
        func_span(func_name, start_addr, end_addr),
        pallocframe(alloc_address, stack_size),
        if alloc_address >= start_addr,
        if alloc_address < end_addr;

    func_stacksz(start_addr, end_addr, *func_name, stack_size_u64) <--
        func_span(func_name, start_addr, end_addr),
        agg stack_size = aggregators::sum(sz) in pallocframe_by_func(func_name, _, sz),
        let stack_size_u64 = stack_size.max(0) as u64;

    func_stacksz(start_addr, end_addr, *func_name, 0u64) <--
        func_span(func_name, start_addr, end_addr),
        !pallocframe_by_func(func_name, _, _);


    relation is_arg_reg(Mreg);
    relation is_ret_reg(Mreg);

    // Emit both signed and unsigned memory chunk variants for byte/word load/store since x86 MOV doesn't encode signedness; downstream type inference narrows.

    // Load: byte signedness variants
    mach_inst(addr, MachInst::Mload(MemoryChunk::MInt8Signed, addressing.clone(), args.clone(), *dst)) <--
        mach_inst(addr, ?MachInst::Mload(MemoryChunk::MInt8Unsigned, addressing, args, dst));

    mach_inst(addr, MachInst::Mload(MemoryChunk::MInt8Unsigned, addressing.clone(), args.clone(), *dst)) <--
        mach_inst(addr, ?MachInst::Mload(MemoryChunk::MInt8Signed, addressing, args, dst));

    // Load: word signedness variants
    mach_inst(addr, MachInst::Mload(MemoryChunk::MInt16Signed, addressing.clone(), args.clone(), *dst)) <--
        mach_inst(addr, ?MachInst::Mload(MemoryChunk::MInt16Unsigned, addressing, args, dst));

    mach_inst(addr, MachInst::Mload(MemoryChunk::MInt16Unsigned, addressing.clone(), args.clone(), *dst)) <--
        mach_inst(addr, ?MachInst::Mload(MemoryChunk::MInt16Signed, addressing, args, dst));

    // Store: byte signedness variants
    mach_inst(addr, MachInst::Mstore(MemoryChunk::MInt8Signed, addressing.clone(), args.clone(), *src)) <--
        mach_inst(addr, ?MachInst::Mstore(MemoryChunk::MInt8Unsigned, addressing, args, src));

    mach_inst(addr, MachInst::Mstore(MemoryChunk::MInt8Unsigned, addressing.clone(), args.clone(), *src)) <--
        mach_inst(addr, ?MachInst::Mstore(MemoryChunk::MInt8Signed, addressing, args, src));

    // Store: word signedness variants
    mach_inst(addr, MachInst::Mstore(MemoryChunk::MInt16Signed, addressing.clone(), args.clone(), *src)) <--
        mach_inst(addr, ?MachInst::Mstore(MemoryChunk::MInt16Unsigned, addressing, args, src));

    mach_inst(addr, MachInst::Mstore(MemoryChunk::MInt16Unsigned, addressing.clone(), args.clone(), *src)) <--
        mach_inst(addr, ?MachInst::Mstore(MemoryChunk::MInt16Signed, addressing, args, src));

}

pub struct AsmPass;

impl IRPass for AsmPass {
    fn name(&self) -> &'static str { "asm" }

    fn run(&self, db: &mut DecompileDB) {
        run_pass!(db, AsmPassProgram);
    }

    declare_io_from!(AsmPassProgram);
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AddressingError {
    NeedsSymbolResolution { address: i64 },
    UnknownRegister { register: Ireg },
    UnsupportedPattern { addrmode: Addrmode },
    #[allow(dead_code)]
    InvalidRegisterCombination {
        base: Option<Ireg>,
        index: Option<(Ireg, i64)>,
    },
}

impl std::fmt::Display for AddressingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AddressingError::NeedsSymbolResolution { address } => {
                write!(f, "Address 0x{:x} needs symbol resolution", address)
            }
            AddressingError::UnknownRegister { register } => {
                write!(f, "Unknown register: {:?}", register)
            }
            AddressingError::UnsupportedPattern { addrmode } => {
                write!(f, "Unsupported addrmode pattern: {:?}", addrmode)
            }
            AddressingError::InvalidRegisterCombination { base, index } => {
                write!(
                    f,
                    "Invalid register combination: base={:?}, index={:?}",
                    base, index
                )
            }
        }
    }
}

#[inline]

// Returns true for valid general-purpose registers (excludes Unknown and RIP).
fn is_valid_gpr(r: Ireg) -> bool {
    !matches!(r, Ireg::Unknown | Ireg::RIP)
}

// Check if register name is an 8-bit GPR.
pub fn is_reg_8(name: &str) -> bool {
    matches!(name, "AL" | "BL" | "CL" | "DL" | "AH" | "BH" | "CH" | "DH"
        | "SIL" | "DIL" | "SPL" | "BPL"
        | "R8B" | "R9B" | "R10B" | "R11B" | "R12B" | "R13B" | "R14B" | "R15B")
}

// Returns the absolute address if the addrmode requires symbol resolution (RIP-relative or absolute).
pub fn addrmode_needs_symbol_resolution(am: &Addrmode) -> Option<i64> {
    match am {
        Addrmode {
            base: Some(Ireg::RIP),
            index: None,
            disp: Displacement::Const(n),
        } if *n != 0 => Some(*n),

        Addrmode {
            base: None,
            index: None,
            disp: Displacement::Const(n),
        } if *n != 0 => Some(*n),

        _ => None,
    }
}

// Reverse of CompCert's transl_addressing (see x86/Asmgen.v).
pub fn transl_addressing_rev(
    am: Addrmode,
    resolved_symbol: Option<(Ident, i64)>,
) -> Result<(Addressing, Vec<Mreg>), String> {
    transl_addressing_rev_inner(am, resolved_symbol).map_err(|e| e.to_string())
}

fn transl_addressing_rev_inner(
    am: Addrmode,
    resolved_symbol: Option<(Ident, i64)>,
) -> Result<(Addressing, Vec<Mreg>), AddressingError> {
    match am {
        Addrmode {
            base: Some(Ireg::RSP),
            index: None,
            disp: Displacement::Const(n),
        } => Ok((Addressing::Ainstack(n), vec![])),

        Addrmode {
            base: Some(Ireg::RBP),
            index: None,
            disp: Displacement::Const(n),
        } => Ok((Addressing::Ainstack(n), vec![])),

        Addrmode {
            base: None,
            index: None,
            disp: Displacement::Symbol { ident, ofs },
        } => Ok((Addressing::Aglobal(ident, ofs), vec![])),

        Addrmode {
            base: Some(Ireg::RIP),
            index: None,
            disp: Displacement::Symbol { ident, ofs },
        } => Ok((Addressing::Aglobal(ident, ofs), vec![])),

        Addrmode {
            base: Some(Ireg::RIP),
            index: None,
            disp: Displacement::Const(n),
        } => {
            if let Some((ident, offset)) = resolved_symbol {
                Ok((Addressing::Aglobal(ident, offset), vec![]))
            } else {
                Err(AddressingError::NeedsSymbolResolution { address: n })
            }
        }

        Addrmode {
            base: None,
            index: None,
            disp: Displacement::Const(n),
        } if n != 0 => {
            if let Some((ident, offset)) = resolved_symbol {
                Ok((Addressing::Aglobal(ident, offset), vec![]))
            } else {
                Err(AddressingError::NeedsSymbolResolution { address: n })
            }
        }

        Addrmode {
            base: None,
            index: None,
            disp: Displacement::Const(0),
        } => {
            if let Some((ident, offset)) = resolved_symbol {
                Ok((Addressing::Aglobal(ident, offset), vec![]))
            } else {
                Err(AddressingError::UnsupportedPattern { addrmode: am })
            }
        }

        Addrmode {
            base: Some(r1),
            index: None,
            disp: Displacement::Const(n),
        } if is_valid_gpr(r1) && r1 != Ireg::RSP => Ok((Addressing::Aindexed(n), vec![r1.into()])),

        Addrmode {
            base: Some(r1),
            index: Some((r2, 1)),
            disp: Displacement::Const(n),
        } if is_valid_gpr(r1) && is_valid_gpr(r2) => {
            Ok((Addressing::Aindexed2(n), vec![r1.into(), r2.into()]))
        }

        Addrmode {
            base: None,
            index: Some((r1, sc)),
            disp: Displacement::Const(n),
        } if is_valid_gpr(r1) => Ok((Addressing::Ascaled(sc, n), vec![r1.into()])),

        Addrmode {
            base: Some(r1),
            index: Some((r2, sc)),
            disp: Displacement::Const(n),
        } if is_valid_gpr(r1) && is_valid_gpr(r2) && sc != 1 => Ok((
            Addressing::Aindexed2scaled(sc, n),
            vec![r1.into(), r2.into()],
        )),

        Addrmode {
            base: Some(r1),
            index: None,
            disp: Displacement::Symbol { ident, ofs },
        } if is_valid_gpr(r1) => Ok((Addressing::Abased(ident, ofs), vec![r1.into()])),

        Addrmode {
            base: None,
            index: Some((r1, sc)),
            disp: Displacement::Symbol { ident, ofs },
        } if is_valid_gpr(r1) => Ok((Addressing::Abasedscaled(sc, ident, ofs), vec![r1.into()])),

        Addrmode {
            base: Some(r1),
            index: Some((r2, sc)),
            disp: Displacement::Symbol { ident, ofs },
        } if is_valid_gpr(r1) && is_valid_gpr(r2) => {
            if sc == 1 {
                log::debug!(
                    "Addressing base({:?}) + index({:?}) + symbol({}, {}): using Abased, index discarded",
                    r1, r2, ident, ofs
                );
                Ok((Addressing::Abased(ident, ofs), vec![r1.into()]))
            } else {
                log::warn!(
                    "Unsupported addressing: base({:?}) + {}*index({:?}) + symbol({}, {}). \
                     No CompCert mode can represent this pattern.",
                    r1, sc, r2, ident, ofs
                );
                Err(AddressingError::UnsupportedPattern { addrmode: am })
            }
        }

        Addrmode {
            base: Some(r1),
            index: Some((Ireg::Unknown, _)),
            disp: Displacement::Const(n),
        } if is_valid_gpr(r1) => Ok((Addressing::Aindexed(n), vec![r1.into()])),

        Addrmode {
            base: Some(Ireg::RIP),
            index: Some((r1, sc)),
            disp,
        } if is_valid_gpr(r1) => {
            match disp {
                Displacement::Symbol { ident, ofs } => {
                    if sc == 1 {
                        Ok((Addressing::Abased(ident, ofs), vec![r1.into()]))
                    } else {
                        Ok((Addressing::Abasedscaled(sc, ident, ofs), vec![r1.into()]))
                    }
                }
                Displacement::Const(n) => {
                    if let Some((ident, offset)) = resolved_symbol {
                        if sc == 1 {
                            Ok((Addressing::Abased(ident, offset), vec![r1.into()]))
                        } else {
                            Ok((Addressing::Abasedscaled(sc, ident, offset), vec![r1.into()]))
                        }
                    } else {
                        if sc == 1 {
                            Ok((Addressing::Aindexed(n), vec![r1.into()]))
                        } else {
                            Ok((Addressing::Ascaled(sc, n), vec![r1.into()]))
                        }
                    }
                }
            }
        }

        Addrmode {
            base: Some(Ireg::Unknown),
            ..
        } => Err(AddressingError::UnknownRegister {
            register: Ireg::Unknown,
        }),

        _ => Err(AddressingError::UnsupportedPattern { addrmode: am }),
    }
}
