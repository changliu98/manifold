// Mach to Linear: converts Mach IR instructions to Linear IR (reverses CompCert's Stacking pass).

#![allow(irrefutable_let_patterns)]

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::{declare_io_from, run_pass};

use std::sync::Arc;
use crate::x86::mach::Mreg;
use crate::x86::op::{Condition, Operation};
use crate::x86::types::*;
use ascent::ascent_par;
use either::Either;


ascent_par! {
    #![measure_rule_times]

    #[swap_db]
    pub struct MachPassProgram;

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
    relation func_span(Symbol, Address, Address);
    relation global_struct_catalog(u64, usize, usize, usize);
    relation ident_to_symbol(Ident, Symbol);
    relation ifthenelse_merge_point(Address, Node, Node);
    relation instr_in_function(Node, Address);
    relation is_external_function(Address);
    relation known_extern_signature(Symbol, usize, XType, Arc<Vec<XType>>);
    relation known_func_param_is_ptr(Symbol, usize);
    relation known_func_returns_float(Symbol);
    relation known_func_returns_int(Symbol);
    relation known_func_returns_long(Symbol);
    relation known_func_returns_ptr(Symbol);
    relation known_func_returns_single(Symbol);
    relation main_function(Address);
    relation reg_def_used(Address, Mreg, Address);
    relation reg_rtl(Node, Mreg, RTLReg);
    relation reg_xtl(Node, Mreg, RTLReg);
    relation stack_var(Address, Address, i64, RTLReg);
    relation string_data(String, String, usize);
    relation struct_field(u64, i64, String, MemoryChunk);
    relation struct_id_to_canonical(usize, usize);

    relation instr_in_function(Node, Address);


    relation next(Address, Address);
    relation mach_inst(Address, MachInst);
    relation direct_call(Address, Address);
    relation arch_bit(i64);

    relation linear_inst(Address, LinearInst);
    relation callee_save_spill(Address, Mreg, i64);
    relation callee_spill_pair((Address, Mreg));

    relation global_fe_ofs_arg(i64);
    relation lop(Address, Operation, MregArgs, Mreg);
    relation lcall(Address, Either<Mreg, Either<Symbol, i64>>);
    relation ltailcall(Address, Either<Mreg, Either<Symbol, i64>>);
    relation restore_callee_save_rec(Address, Arc<Vec<Mreg>>, i64);
    relation tail_call_candidate(Address, Symbol, Arc<Vec<Mreg>>);
    relation lgoto_converted_to_tailcall(Address, Symbol, Arc<Vec<Mreg>>, i64);
    relation lbuiltin(Address, String, Arc<Vec<BuiltinArg<Mreg>>>, BuiltinArg<Mreg>);
    relation llabel(Address, String);
    relation lgoto(Address, Symbol);
    relation lcond(Address, Condition, MregArgs, Symbol);
    relation lreturn(Address);

    global_fe_ofs_arg(32) <-- arch_bit(64);

    callee_save_spill(addr, dst, ofs) <--
        mach_inst(addr, machinst),
        if let (ofs, _typ, dst) = match machinst {
            MachInst::Mgetstack(ofs, typ, dst) => (ofs, typ, dst),
            _ => return,
        },
        global_fe_ofs_arg(global_ofs),
        if *ofs > *global_ofs;

    callee_spill_pair(pair) <--
        callee_save_spill(addr, reg, _),
        let pair = (*addr, *reg);

    linear_inst(addr, linst) <--
        mach_inst(addr, ?MachInst::Mgetstack(ofs, typ, dst)),
        let linst = LinearInst::Lgetstack(Slot::Local, *ofs, *typ, *dst);

    linear_inst(addr, linst) <--
        mach_inst(addr, ?MachInst::Mgetparam(ofs, typ, dst)),
        let linst = LinearInst::Lgetstack(Slot::Incoming, *ofs, *typ, *dst);

    linear_inst(addr, linst) <--
        mach_inst(addr, ?MachInst::Msetstack(src, ofs, typ)),
        let linst = LinearInst::Lsetstack(*src, Slot::Local, *ofs, *typ);


    lop(addr, op, args, res) <--
        mach_inst(addr, machinst),
        if let (op, args, res) = match machinst {
            MachInst::Mop(op, args, res) => (op, args, res),
            _ => return,
        };

    linear_inst(addr, linst) <--
        lop(addr, op, args, res),
        let linst = LinearInst::Lop(op.clone(), args.clone(), *res);


    linear_inst(addr, linst) <--
        mach_inst(addr, ?MachInst::Mload(chunk, addrmode, args, dst)),
        let linst = LinearInst::Lload(*chunk, addrmode.clone(), args.clone(), *dst);

    linear_inst(addr, linst) <--
        mach_inst(addr, ?MachInst::Mstore(chunk, addrmode, args, src)),
        let linst = LinearInst::Lstore(*chunk, addrmode.clone(), args.clone(), *src);

    // Use the symbol-resolved callee from mach_inst (handles PLT-resolved names)
    lcall(addr, symbol.clone()) <--
        mach_inst(addr, machinst),
        if let symbol = match machinst {
            MachInst::Mcall(symbol) => symbol,
            _ => return,
        };

    linear_inst(addr, linst) <--
        lcall(addr, symbol),
        let linst = LinearInst::Lcall(symbol.as_ref().map_left(|m| *m).map_right(|e| e.as_ref().map_left(|s| s.clone()).map_right(|i| *i as u64)));

    ltailcall(addr, symbol) <--
        mach_inst(addr, machinst),
        if let symbol = match machinst {
            MachInst::Mtailcall(symbol) => symbol,
            _ => return,
        };

    restore_callee_save_rec(addr, mregs, offset) <--
        mach_inst(addr, machinst),
        if let (ofs, typ, dst) = match machinst {
            MachInst::Mgetstack(ofs, typ, dst) => (ofs, typ, dst),
            _ => return,
        },
        next(addr, addr1),
        mach_inst(addr1, machinst1),
        if match machinst1 {
            MachInst::Mgetstack(_, _, _) => false,
            _ => true,
        },
        let mregs = Arc::new(vec![*dst]),
        let offset = ofs;


    tail_call_candidate(restore_addr, target, mregs) <--
        restore_callee_save_rec(restore_addr, mregs, _),
        next(restore_addr, jump_addr),
        lgoto(jump_addr, target_ref),
        if !mregs.is_empty(),
        let target = target_ref.clone();


    lgoto_converted_to_tailcall(goto_addr, target, mregs, offset) <--
        tail_call_candidate(restore_addr, target, mregs),
        next(restore_addr, goto_addr_ref),
        lgoto(goto_addr_ref, _),
        let goto_addr = *goto_addr_ref,
        restore_callee_save_rec(restore_addr, _, offset);

    linear_inst(addr, linst) <--
        lgoto_converted_to_tailcall(addr, target, mregs, offset),
        let linst = LinearInst::Ltailcall(Either::Right(Either::Left(target.clone())));


    linear_inst(addr, linst) <--
        ltailcall(addr, symbol),
        next(addr1, addr),
        restore_callee_save_rec(addr1, mregs, offset),
        let linst = LinearInst::Ltailcall(symbol.as_ref().map_left(|m| *m).map_right(|e| e.as_ref().map_left(|s| s.clone()).map_right(|i| *i as u64)));

    linear_inst(addr, linst) <--
        ltailcall(addr, symbol),
        next(addr1, addr),
        !restore_callee_save_rec(addr1, _, _),
        let linst = LinearInst::Ltailcall(symbol.as_ref().map_left(|m| *m).map_right(|e| e.as_ref().map_left(|s| s.clone()).map_right(|i| *i as u64)));

    linear_inst(addr, linst) <--
        ltailcall(addr, symbol),
        !next(_, addr),
        let linst = LinearInst::Ltailcall(symbol.as_ref().map_left(|m| *m).map_right(|e| e.as_ref().map_left(|s| s.clone()).map_right(|i| *i as u64)));


    lbuiltin(*addr, ef.clone(), Arc::new(args.clone()), dst.clone()) <--
        mach_inst(addr, machinst),
        if let (ef, args, dst) = match machinst {
            MachInst::Mbuiltin(ef, args, dst) => (ef, args, dst),
            _ => return,
        };

    linear_inst(addr, linst) <--
        lbuiltin(addr, ef, args, dst),
        let linst = LinearInst::Lbuiltin(ef.clone(), args.to_vec(), dst.clone());

    llabel(addr, lbl) <--
        mach_inst(addr, machinst),
        if let lbl = match machinst {
            MachInst::Mlabel(lbl) => lbl,
            _ => return,
        };

    linear_inst(addr, linst) <--
        llabel(addr, lbl),
        let linst = LinearInst::Llabel(lbl.clone());

    lgoto(addr, lbl) <--
        mach_inst(addr, ?MachInst::Mgoto(lbl));

    linear_inst(addr, linst) <--
        lgoto(addr, lbl),
        !lgoto_converted_to_tailcall(*addr, _, _, _),
        let linst = LinearInst::Lgoto(lbl.clone());

    lcond(addr, cond, args, lbl) <--
        mach_inst(addr, machinst),
        if let (cond, args, lbl) = match machinst {
            MachInst::Mcond(cond, args, lbl) => (cond, args, lbl),
            _ => return,
        };

    linear_inst(addr, linst) <--
        lcond(addr, cond, args, lbl),
        let linst = LinearInst::Lcond(*cond, args.clone(), lbl.clone());

    lreturn(addr) <--
        mach_inst(addr, machinst),
        if match machinst {
            MachInst::Mreturn => true,
            _ => return,
        };

    linear_inst(addr, linst) <--
        lreturn(addr),
        let linst = LinearInst::Lreturn;
}

pub struct MachPass;

impl IRPass for MachPass {
    fn name(&self) -> &'static str { "mach" }

    fn run(&self, db: &mut DecompileDB) {
        run_pass!(db, MachPassProgram);
    }

    declare_io_from!(MachPassProgram);
}
