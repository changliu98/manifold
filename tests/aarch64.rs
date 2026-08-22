// AArch64 frontend tests. Scoped to what exists today: ABI detection / AAPCS64 tables
// and the capstone arm64 decode layer. Full-pipeline assertions belong with the
// aarch64 normalizing frontend that produces mach_inst, and are not asserted here yet.
//
// No-ops when the cross toolchain is absent, matching tests/pe.rs.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use manifold::aarch64::mach::A64Mreg;
use manifold::abi::{Arch, BinaryFormat};
use manifold::decompile::elevator::DecompileDB;
use manifold::decompile::passes::aarch64_asm_pass::Aarch64AsmPass;
use manifold::decompile::passes::abi_pass::AbiPass;
use manifold::decompile::passes::pass::IRPass;
use manifold::mreg::Mreg;
use manifold::x86::op::{Addressing, Operation};
use manifold::x86::types::{Address, MachInst, Symbol};

fn command_exists(name: &str) -> bool {
    Command::new(name)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn build_fixture() -> Option<PathBuf> {
    if !command_exists("clang") || !command_exists("ld.lld") {
        eprintln!("skipping aarch64 test: clang/ld.lld unavailable");
        return None;
    }

    let dir = std::env::temp_dir().join(format!("manifold_a64_fixture_{}", std::process::id()));
    std::fs::create_dir_all(&dir).ok()?;
    let src = dir.join("fixture.c");
    let exe = dir.join("fixture.elf");

    std::fs::write(
        &src,
        r#"
// Eight register args plus a ninth that AAPCS64 must pass on the stack.
__attribute__((noinline)) long nine_args(long a, long b, long c, long d,
                                         long e, long f, long g, long h, long i) {
    return a + b + c + d + e + f + g + h + i;
}
// Forces a real frame: address-taken local, loop, indexed loads.
__attribute__((noinline)) long sum_array(long *p, long n) {
    long acc = 0;
    for (long k = 0; k < n; k++) acc += p[k];
    return acc;
}
__attribute__((noinline)) long frame_user(long n) {
    long buf[8];
    for (long k = 0; k < 8; k++) buf[k] = k * n;
    return sum_array(buf, 8) + nine_args(1, 2, 3, 4, 5, 6, 7, 8, 9);
}
typedef long (*unary_fn)(long);
__attribute__((noinline)) long add_one(long x) { return x + 1; }
__attribute__((noinline)) long apply_tail(unary_fn fn, long x) { return fn(x); }
void _start(void) { (void)frame_user(3); (void)apply_tail(add_one, 4); }
"#,
    )
    .ok()?;

    let ok = Command::new("clang")
        .args([
            "--target=aarch64-linux-gnu",
            "-O1",
            "-fno-pie",
            "-nostdlib",
            "-fuse-ld=lld",
        ])
        .arg(&src)
        .arg("-o")
        .arg(&exe)
        .status()
        .ok()?
        .success();
    if !ok {
        eprintln!("skipping aarch64 test: cross-link failed");
        return None;
    }
    Some(exe)
}

fn fixture() -> Option<&'static Path> {
    static FIXTURE: OnceLock<Option<PathBuf>> = OnceLock::new();
    FIXTURE.get_or_init(build_fixture).as_deref()
}

#[test]
fn aarch64_abi_is_detected_as_aapcs64() {
    let Some(exe) = fixture() else { return };
    let mut db = DecompileDB::default();
    manifold::decompile::disassembly::load_from_binary(&mut db, exe);
    let abi = db.abi();

    assert_eq!(abi.arch, Arch::Aarch64);
    assert_eq!(abi.format, BinaryFormat::Elf);
    assert!(abi.is_64bit());
    assert_eq!(abi.pointer_size, 8);
    assert_eq!(abi.int_arg_regs.len(), 8);
    assert_eq!(abi.int_arg_regs[0], Mreg::A64(A64Mreg::X0));
    assert_eq!(abi.ret_int_reg, Mreg::A64(A64Mreg::X0));
    assert_eq!(abi.ret_float_reg, Mreg::A64(A64Mreg::V0));
    assert!(!abi.uses_shared_arg_slots());
    assert_eq!(abi.first_stack_arg_position(), 8);

    // BL leaves the return address in X30 rather than pushing it, so the callee's
    // first stack argument sits at SP+0 -- unlike x86, where CALL pushes 8 bytes.
    assert_eq!(abi.return_addr_stack_size(), 0);
    assert_eq!(abi.incoming_sp_stack_arg_base(), 0);
}

#[test]
fn aarch64_abi_pass_publishes_aapcs64_tables() {
    let Some(exe) = fixture() else { return };
    let mut db = DecompileDB::default();
    manifold::decompile::disassembly::load_from_binary(&mut db, exe);
    AbiPass.run(&mut db);

    let a64 = |r: A64Mreg| Mreg::A64(r);
    assert!(db
        .rel_iter::<(Mreg, usize)>("abi_int_arg_position")
        .any(|(reg, pos)| *reg == a64(A64Mreg::X7) && *pos == 7));
    assert!(db
        .rel_iter::<(Mreg, usize)>("abi_float_arg_position")
        .any(|(reg, pos)| *reg == a64(A64Mreg::V3) && *pos == 3));
    assert!(db
        .rel_iter::<(Mreg,)>("is_callee_saved")
        .any(|(r,)| *r == a64(A64Mreg::X19)));
    assert!(db
        .rel_iter::<(Mreg,)>("is_caller_saved")
        .any(|(r,)| *r == a64(A64Mreg::X0)));
    // No shadow space and no pushed return address.
    assert!(db
        .rel_iter::<(i64,)>("abi_outgoing_stack_base")
        .any(|(v,)| *v == 0));
    assert!(db
        .rel_iter::<(i64,)>("abi_incoming_sp_stack_base")
        .any(|(v,)| *v == 0));
}

#[test]
fn aarch64_decode_populates_core_relations() {
    let Some(exe) = fixture() else { return };
    let mut db = DecompileDB::default();
    manifold::decompile::disassembly::load_from_binary(&mut db, exe);

    let insns: Vec<_> = db
        .rel_iter::<(
            u64,
            usize,
            Symbol,
            Symbol,
            Symbol,
            Symbol,
            Symbol,
            Symbol,
            usize,
            usize,
        )>("unrefinedinstruction")
        .collect();
    assert!(!insns.is_empty(), "no aarch64 instructions decoded");
    // AArch64 is fixed-width.
    assert!(
        insns.iter().all(|i| i.1 == 4),
        "every aarch64 instruction must decode as 4 bytes"
    );

    let mnemonics: std::collections::HashSet<&str> = insns.iter().map(|i| i.3).collect();
    for expected in ["RET", "BL", "STP", "LDP"] {
        assert!(
            mnemonics.contains(expected),
            "expected {expected} in decoded mnemonics: {mnemonics:?}"
        );
    }

    // Def/use is derived from opcode shape, since capstone gives no operand access
    // for arm64. A store's transferred register must be a USE, never a DEF.
    let str_addrs: Vec<u64> = insns
        .iter()
        .filter(|i| i.3 == "STR" || i.3 == "STP")
        .map(|i| i.0)
        .collect();
    assert!(!str_addrs.is_empty(), "fixture should contain stores");
    let defs: Vec<_> = db.rel_iter::<(Address, Mreg)>("reg_def").collect();
    let uses: Vec<_> = db.rel_iter::<(Address, Mreg)>("reg_use").collect();
    assert!(
        uses.iter().any(|(a, _)| str_addrs.contains(a)),
        "store operands must be recorded as reg_use"
    );

    // The zero register is never a value definition.
    assert!(
        !defs.iter().any(|(_, r)| *r == Mreg::A64(A64Mreg::ZR)),
        "XZR/WZR must never appear as a reg_def"
    );

    // BL writes the link register.
    let bl_addrs: Vec<u64> = insns.iter().filter(|i| i.3 == "BL").map(|i| i.0).collect();
    assert!(
        bl_addrs
            .iter()
            .all(|a| defs.contains(&&(*a, Mreg::A64(A64Mreg::X30)))),
        "every BL must define X30 (LR)"
    );

    // Frame setup: SP movement and the X29 frame-pointer establish.
    let adjusts: Vec<_> = db
        .rel_iter::<(Address, Symbol, i64)>("adjusts_stack")
        .collect();
    assert!(
        adjusts
            .iter()
            .any(|(_, base, delta)| *base == "SP" && *delta < 0),
        "frame allocation must be recorded as a negative SP adjustment"
    );
    // The frame pointer is established by `mov x29, sp` OR `add x29, sp, #N`; clang
    // emits the nonzero-offset form for any function whose frame record is not at the
    // bottom of the frame (`sub sp,#112; stp x29,x30,[sp,#80]; add x29,sp,#80`).
    let fp_setup: Vec<_> = db
        .rel_iter::<(Address, Symbol, Symbol, i64)>("stack_base_move_offset")
        .collect();
    if !fp_setup
        .iter()
        .any(|(_, src, dst, _)| *src == "SP" && *dst == "X29")
    {
        // Resolve each ADD/MOV's operand slots so the failure names the actual
        // operand shape capstone produced rather than just reporting absence.
        let regs: std::collections::HashMap<Symbol, Symbol> = db
            .rel_iter::<(Symbol, Symbol)>("op_register")
            .map(|(id, name)| (*id, *name))
            .collect();
        let imms: std::collections::HashMap<Symbol, i64> = db
            .rel_iter::<(Symbol, i64, usize)>("op_immediate")
            .map(|(id, v, _)| (*id, *v))
            .collect();
        let mut shapes: Vec<String> = insns
            .iter()
            .filter(|i| i.3 == "ADD" || i.3 == "MOV")
            .take(24)
            .map(|(a, _, _, m, o1, o2, o3, o4, _, _)| {
                let slot = |o: &Symbol| -> String {
                    if *o == "0" {
                        "-".into()
                    } else if let Some(r) = regs.get(o) {
                        format!("reg:{r}")
                    } else if let Some(v) = imms.get(o) {
                        format!("imm:{v}")
                    } else {
                        "mem/other".into()
                    }
                };
                format!(
                    "{a:#x} {m} [{}, {}, {}, {}]",
                    slot(o1),
                    slot(o2),
                    slot(o3),
                    slot(o4)
                )
            })
            .collect();
        shapes.sort();
        panic!(
            "frame-pointer establish not recorded. observed ADD/MOV operand shapes:\n{}",
            shapes.join("\n")
        );
    }
    // The offsetless relation states `dst := src`, so it must carry only the
    // zero-offset establishes -- a nonzero one there would claim X29 == SP.
    let base_moves: Vec<_> = db
        .rel_iter::<(Address, Symbol, Symbol)>("stack_base_move")
        .collect();
    for (addr, src, dst) in &base_moves {
        assert!(
            fp_setup
                .iter()
                .any(|(a, s, d, off)| a == addr && s == src && d == dst && *off == 0),
            "stack_base_move at {addr:#x} must correspond to a zero-offset establish"
        );
    }

    // Frame-relative accesses land in stack_def/stack_use, keyed on SP or X29.
    let sdefs: Vec<_> = db.rel_iter::<(Address, Symbol, i64)>("stack_def").collect();
    let suses: Vec<_> = db.rel_iter::<(Address, Symbol, i64)>("stack_use").collect();
    assert!(!sdefs.is_empty(), "fixture stores to its frame");
    assert!(!suses.is_empty(), "fixture loads from its frame");
    assert!(
        sdefs
            .iter()
            .chain(suses.iter())
            .all(|(_, b, _)| *b == "SP" || *b == "X29"),
        "aarch64 frame accesses must be based on SP or X29"
    );
}

// The normalizing frontend: AArch64 -> the SHARED Mach vocabulary. Asserts that the
// decomposition actually lands in the existing Operation/Addressing alphabet rather
// than merely that some facts were produced.
#[test]
fn aarch64_frontend_normalizes_into_shared_mach_vocabulary() {
    let Some(exe) = fixture() else { return };
    let mut db = DecompileDB::default();
    manifold::decompile::disassembly::load_from_binary(&mut db, exe);
    manifold::decompile::disassembly::load_preset(&mut db);
    AbiPass.run(&mut db);
    Aarch64AsmPass.run(&mut db);

    let insts: Vec<(Address, MachInst)> = db
        .rel_iter::<(Address, MachInst)>("mach_inst")
        .cloned()
        .collect();
    assert!(!insts.is_empty(), "frontend produced no mach_inst at all");

    let has = |f: &dyn Fn(&MachInst) -> bool| insts.iter().any(|(_, m)| f(m));

    // Control flow: the fixture returns, calls and branches conditionally.
    assert!(has(&|m| matches!(m, MachInst::Mreturn)), "no Mreturn");
    assert!(has(&|m| matches!(m, MachInst::Mcall(_))), "no Mcall for BL");
    assert!(has(&|m| matches!(m, MachInst::Mcond(..))), "no Mcond");
    assert!(
        has(&|m| matches!(m, MachInst::Mtailcall(either::Either::Left(Mreg::A64(_))))),
        "no register Mtailcall for BR through the function-pointer parameter"
    );

    // Memory: the frame-array loop stores to and loads from its frame.
    assert!(has(&|m| matches!(m, MachInst::Mstore(..))), "no Mstore");
    assert!(has(&|m| matches!(m, MachInst::Mload(..))), "no Mload");

    // Arithmetic decomposed into the shared 64-bit Operation alphabet.
    assert!(
        has(&|m| matches!(m, MachInst::Mop(Operation::Oaddl, ..))),
        "no Oaddl -- 64-bit ADD did not normalize"
    );
    assert!(
        has(&|m| matches!(m, MachInst::Mop(Operation::Omove, ..))),
        "no Omove -- register MOV did not normalize"
    );

    // Frame-relative access must reach Ainstack, which is what makes stack analysis
    // see an AArch64 frame the same way it sees an x86 one. 73% of AArch64 memory
    // operands are SP-relative, so this is the dominant addressing case.
    assert!(
        insts.iter().any(|(_, m)| matches!(
            m,
            MachInst::Mstore(_, Addressing::Ainstack(_), ..)
                | MachInst::Mload(_, Addressing::Ainstack(_), ..)
        )),
        "no Ainstack access -- SP-relative frame traffic did not normalize"
    );

    // Every mach_inst must be attributed to a function, or nothing downstream can
    // place it.
    let in_func: std::collections::HashSet<Address> = db
        .rel_iter::<(Address, Address)>("instr_in_function")
        .map(|(a, _)| *a)
        .collect();
    let orphans: Vec<Address> = insts
        .iter()
        .map(|(a, _)| *a)
        .filter(|a| !in_func.contains(a))
        .collect();
    assert!(
        orphans.is_empty(),
        "{} mach_inst not attributed to any function, e.g. {:#x?}",
        orphans.len(),
        &orphans[..orphans.len().min(5)]
    );

    // A frame was recovered with a nonzero size.
    assert!(
        db.rel_iter::<(Address, Address, Symbol, u64)>("func_stacksz")
            .any(|(_, _, _, sz)| *sz > 0),
        "no function recovered a nonzero frame size"
    );
}
