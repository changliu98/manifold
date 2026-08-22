// ARM32 frontend tests: ABI detection / AAPCS32 tables, the capstone ARM decode layer for
// both instruction sets (A32 and Thumb, including interworking between them), and the
// normalizing frontend that produces mach_inst.
//
// No-ops when the cross toolchain is absent, matching tests/aarch64.rs and tests/pe.rs.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use manifold::abi::{Arch, BinaryFormat};
use manifold::arm32::mach::A32Mreg;
use manifold::decompile::elevator::DecompileDB;
use manifold::decompile::passes::abi_pass::AbiPass;
use manifold::decompile::passes::arm32_asm_pass::Arm32AsmPass;
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

// Two fixtures: the default target, and an armv5te build whose lack of MOVW/MOVT forces
// literal pools into .text. The pool case is the one a linear sweep gets wrong.
const SOURCE: &str = r#"
// Four register args plus a fifth that AAPCS32 must pass on the stack.
__attribute__((noinline)) int five_args(int a, int b, int c, int d, int e) {
    return a + b + c + d + e;
}
// If-conversion: clang emits a predicated ALU instruction for this.
__attribute__((noinline)) int predicated(int x, int y) {
    int r = x;
    if (x > y) r = y + 1;
    return r;
}
// A predicated register move, the exact CMOV shape.
__attribute__((noinline)) int pick(int x, int y, int a, int b) {
    return x == y ? a : b;
}
__attribute__((noinline)) int sum_array(int *p, int n) {
    int acc = 0;
    for (int k = 0; k < n; k++) acc += p[k];
    return acc;
}
// Forces a real frame with callee-saved registers: PUSH {r4,..,lr} / POP {..,pc}.
__attribute__((noinline)) int frame_user(int n) {
    int buf[8];
    for (int k = 0; k < 8; k++) buf[k] = k * n;
    return sum_array(buf, 8) + five_args(1, 2, 3, 4, 5) + pick(n, 7, 1, 2);
}
// A constant too large for an A32 rotated immediate: armv5te must park it in a pool.
__attribute__((noinline)) int bigconst(int x) { return x + 0x12345678; }
typedef int (*unary_fn)(int);
__attribute__((noinline)) int add_one(int x) { return x + 1; }
__attribute__((noinline)) int apply_tail(unary_fn fn, int x) { return fn(x); }
void _start(void) { (void)frame_user(3); (void)bigconst(1); (void)apply_tail(add_one, 4); }
"#;

// One image holding an A32 function and two Thumb ones, calling each other through BLX so
// the frontend has to switch instruction sets on a real interworking edge. Written in
// assembly because the interesting cases -- a literal pool inside Thumb code, an IT block,
// a table branch -- are compiler-choice in C but pinned here.
const INTERWORK_ASM: &str = r#"
    .syntax unified
    .text
    .thumb
    .global thumb_leaf
    .thumb_func
thumb_leaf:
    push    {r4, r5, r7, lr}
    cmp     r0, r1
    ittee   eq
    moveq   r2, r3
    ldreq   r4, [r1]
    strne   r0, [r1]
    addne   r2, r1, #3
    cbz     r0, 1f
    movw    r5, #22136
    movt    r5, #4660
    add     r2, r5
    blx     arm_helper
1:  mov     r0, r2
    pop     {r4, r5, r7, pc}

    .global thumb_pool_user
    .thumb_func
thumb_pool_user:
    ldr     r0, .Lpool
    b       1f
    .align 2
.Lpool:
    .word   0x12345678
.Lbad:
    .word   0xffffffff
1:  adds    r0, #1
    bx      lr

    .arm
    .global arm_helper
    .type   arm_helper, %function
arm_helper:
    push    {r4, lr}
    mov     r4, r0
    add     r4, r4, #7
    mov     r0, r4
    pop     {r4, pc}

    .thumb
    .global thumb_switch
    .thumb_func
thumb_switch:
    cmp     r0, #5
    bhi     9f
    tbb     [pc, r0]
.Ltab:
    .byte   (3f-.Ltab)/2
    .byte   (4f-.Ltab)/2
    .byte   (5f-.Ltab)/2
    .byte   (6f-.Ltab)/2
    .byte   (7f-.Ltab)/2
    .byte   (8f-.Ltab)/2
    .align  1
3:  movs    r0, #11
    bx      lr
4:  movs    r0, #22
    bx      lr
5:  movs    r0, #33
    bx      lr
6:  movs    r0, #44
    bx      lr
7:  movs    r0, #55
    bx      lr
8:  movs    r0, #66
    bx      lr
9:  movs    r0, #0
    bx      lr

    .global _start
    .thumb_func
_start:
    movs    r0, #3
    movs    r1, #4
    bl      thumb_leaf
    bl      thumb_pool_user
    bl      thumb_switch
    b       .
"#;

fn build(target: &str, isa: &str, tag: &str) -> Option<PathBuf> {
    build_with(target, isa, tag, &[])
}

fn build_with(target: &str, isa: &str, tag: &str, extra: &[&str]) -> Option<PathBuf> {
    if !command_exists("clang") || !command_exists("ld.lld") {
        eprintln!("skipping arm32 test: clang/ld.lld unavailable");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("manifold_a32_{}_{}", tag, std::process::id()));
    std::fs::create_dir_all(&dir).ok()?;
    let src = dir.join("fixture.c");
    let exe = dir.join("fixture.elf");
    std::fs::write(&src, SOURCE).ok()?;

    let ok = Command::new("clang")
        .args([target, isa, "-O1", "-fno-pie", "-nostdlib", "-fuse-ld=lld"])
        .args(extra)
        .arg(&src)
        .arg("-o")
        .arg(&exe)
        .status()
        .ok()?
        .success();
    if !ok {
        eprintln!("skipping arm32 test: cross-link failed for {target} {isa}");
        return None;
    }
    Some(exe)
}

fn build_asm(tag: &str, extra: &[&str]) -> Option<PathBuf> {
    if !command_exists("clang") || !command_exists("ld.lld") {
        eprintln!("skipping arm32 test: clang/ld.lld unavailable");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("manifold_a32_{}_{}", tag, std::process::id()));
    std::fs::create_dir_all(&dir).ok()?;
    let src = dir.join("fixture.s");
    let exe = dir.join("fixture.elf");
    std::fs::write(&src, INTERWORK_ASM).ok()?;

    let ok = Command::new("clang")
        .args([
            "--target=arm-linux-gnueabihf",
            "-march=armv7-a",
            "-nostdlib",
            "-fuse-ld=lld",
        ])
        .args(extra)
        .arg(&src)
        .arg("-o")
        .arg(&exe)
        .status()
        .ok()?
        .success();
    if !ok {
        eprintln!("skipping arm32 interworking test: cross-assemble failed");
        return None;
    }
    Some(exe)
}

fn fixture() -> Option<&'static Path> {
    static F: OnceLock<Option<PathBuf>> = OnceLock::new();
    F.get_or_init(|| build("--target=arm-linux-gnueabihf", "-marm", "hf"))
        .as_deref()
}

fn pool_fixture() -> Option<&'static Path> {
    static F: OnceLock<Option<PathBuf>> = OnceLock::new();
    F.get_or_init(|| build("--target=armv5te-linux-gnueabi", "-marm", "v5"))
        .as_deref()
}

fn thumb_fixture() -> Option<&'static Path> {
    static F: OnceLock<Option<PathBuf>> = OnceLock::new();
    F.get_or_init(|| build("--target=arm-linux-gnueabihf", "-mthumb", "t2"))
        .as_deref()
}

fn interwork_fixture() -> Option<&'static Path> {
    static F: OnceLock<Option<PathBuf>> = OnceLock::new();
    F.get_or_init(|| build_asm("mix", &[])).as_deref()
}

// The same interworking image with no symbol table at all: every mapping symbol and every
// function symbol is gone, so the instruction set of each byte has to be recovered.
fn stripped_interwork_fixture() -> Option<&'static Path> {
    static F: OnceLock<Option<PathBuf>> = OnceLock::new();
    F.get_or_init(|| build_asm("mixstrip", &["-Wl,--strip-all"]))
        .as_deref()
}

fn load(exe: &Path) -> DecompileDB {
    let mut db = DecompileDB::default();
    manifold::decompile::disassembly::load_from_binary(&mut db, exe);
    db
}

fn frontend(exe: &Path) -> DecompileDB {
    let mut db = load(exe);
    manifold::decompile::disassembly::load_preset(&mut db);
    AbiPass.run(&mut db);
    Arm32AsmPass.run(&mut db);
    db
}

fn mach_insts(db: &DecompileDB) -> Vec<(Address, MachInst)> {
    db.rel_iter::<(Address, MachInst)>("mach_inst")
        .cloned()
        .collect()
}

type RawInsn = (
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
);

fn raw_insns(db: &DecompileDB) -> Vec<RawInsn> {
    db.rel_iter::<RawInsn>("unrefinedinstruction")
        .cloned()
        .collect()
}

// Address -> (size, mnemonic) for the decoded stream.
fn decoded_map(db: &DecompileDB) -> std::collections::HashMap<u64, (usize, &'static str)> {
    raw_insns(db)
        .into_iter()
        .map(|i| (i.0, (i.1, i.3)))
        .collect()
}

fn symbol_addr(db: &DecompileDB, want: &str) -> Option<u64> {
    db.rel_iter::<(Address, Symbol, Symbol)>("symbols")
        .find(|(_, name, _)| *name == want)
        .map(|(a, _, _)| *a)
}

#[test]
fn arm32_abi_is_detected_as_aapcs32() {
    let Some(exe) = fixture() else { return };
    let db = load(exe);
    let abi = db.abi();

    assert_eq!(abi.arch, Arch::Arm32);
    assert_eq!(abi.format, BinaryFormat::Elf);
    assert!(!abi.is_64bit());
    assert_eq!(abi.pointer_size, 4);
    assert_eq!(abi.stack_alignment, 8);
    assert_eq!(abi.int_arg_regs.len(), 4);
    assert_eq!(abi.int_arg_regs[0], Mreg::A32(A32Mreg::R0));
    assert_eq!(abi.int_arg_regs[3], Mreg::A32(A32Mreg::R3));
    assert_eq!(abi.ret_int_reg, Mreg::A32(A32Mreg::R0));
    assert!(!abi.uses_shared_arg_slots());
    assert_eq!(abi.first_stack_arg_position(), 4);

    // BL leaves the return address in LR rather than pushing it, so the callee's first
    // stack argument sits at SP+0 -- unlike x86, where CALL pushes the return address.
    assert_eq!(abi.return_addr_stack_size(), 0);
    assert_eq!(abi.incoming_sp_stack_arg_base(), 0);
    // R4-R11 callee-saved, R0-R3 and R12 call-clobbered.
    for r in [A32Mreg::R4, A32Mreg::R11] {
        assert!(
            abi.callee_saved.contains(&Mreg::A32(r)),
            "{r:?} must be callee-saved"
        );
    }
    for r in [A32Mreg::R0, A32Mreg::R12] {
        assert!(
            abi.caller_saved.contains(&Mreg::A32(r)),
            "{r:?} must be caller-saved"
        );
    }
}

#[test]
fn arm32_abi_pass_publishes_aapcs32_tables() {
    let Some(exe) = fixture() else { return };
    let mut db = load(exe);
    AbiPass.run(&mut db);

    assert!(db
        .rel_iter::<(Mreg, usize)>("abi_int_arg_position")
        .any(|(reg, pos)| *reg == Mreg::A32(A32Mreg::R3) && *pos == 3));
    assert!(db
        .rel_iter::<(Mreg,)>("is_callee_saved")
        .any(|(r,)| *r == Mreg::A32(A32Mreg::R4)));
    assert!(db
        .rel_iter::<(Mreg,)>("is_caller_saved")
        .any(|(r,)| *r == Mreg::A32(A32Mreg::R0)));
    assert!(db
        .rel_iter::<(i64,)>("abi_incoming_sp_stack_base")
        .any(|(v,)| *v == 0));
}

// rtl_pass bound the return value to the x86 literal Mreg::AX, so no non-x86
// frontend could ever recover one. The binding is now ABI-driven; this pins the
// relation that carries it, and that abi_pass declares it as an output (a relation
// the scheduler does not know is written can be silently empty in a parallel sub-DB).
#[test]
fn arm32_return_register_reaches_the_shared_pipeline() {
    let Some(exe) = fixture() else { return };
    let mut db = load(exe);
    AbiPass.run(&mut db);
    assert!(
        db.rel_iter::<(Mreg,)>("abi_ret_int_reg")
            .any(|(r,)| *r == Mreg::A32(A32Mreg::R0)),
        "AAPCS32 returns integers in R0"
    );
    assert!(
        AbiPass.outputs().contains(&"abi_ret_int_reg"),
        "abi_pass must declare abi_ret_int_reg, or rtl_pass may run without it"
    );
}

#[test]
fn arm32_decode_populates_core_relations() {
    let Some(exe) = fixture() else { return };
    let db = load(exe);

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
    assert!(!insns.is_empty(), "no arm32 instructions decoded");

    let mnemonics: std::collections::HashSet<&str> = insns.iter().map(|i| i.3).collect();
    for expected in ["BL", "PUSH", "POP"] {
        assert!(
            mnemonics.contains(expected),
            "expected {expected} in decoded mnemonics: {mnemonics:?}"
        );
    }
    // The condition never stays glued to the stem: an unsplit predicated instruction is
    // spelled STEM.CC, so MOVS and MULS can never be misread as MOV+VS and MUL+LS.
    for m in &mnemonics {
        if let Some((stem, cc)) = m.split_once('.') {
            assert!(!stem.is_empty(), "empty stem in {m}");
            assert!(
                manifold::decompile::disassembly::branch::is_arm_condition(cc),
                "{m} has a dotted suffix that is not a condition code"
            );
        }
    }

    // Frame setup: the PUSH that saves the callee-saved registers and the SUB SP both
    // register as negative SP adjustments.
    let adjusts: Vec<_> = db
        .rel_iter::<(Address, Symbol, i64)>("adjusts_stack")
        .collect();
    assert!(
        adjusts
            .iter()
            .any(|(_, base, delta)| *base == "SP" && *delta < 0),
        "frame allocation must be recorded as a negative SP adjustment"
    );

    // Frame-relative accesses land in stack_def/stack_use, keyed on SP or R11.
    let sdefs: Vec<_> = db.rel_iter::<(Address, Symbol, i64)>("stack_def").collect();
    let suses: Vec<_> = db.rel_iter::<(Address, Symbol, i64)>("stack_use").collect();
    assert!(!sdefs.is_empty(), "fixture stores to its frame");
    assert!(!suses.is_empty(), "fixture loads from its frame");
    assert!(
        sdefs
            .iter()
            .chain(suses.iter())
            .all(|(_, b, _)| *b == "SP" || *b == "R11"),
        "arm32 frame accesses must be based on SP or R11"
    );

    // The PC is control state, never a data definition.
    let defs: Vec<_> = db.rel_iter::<(Address, Mreg)>("reg_def").collect();
    assert!(
        defs.iter().any(|(_, r)| *r == Mreg::A32(A32Mreg::LR)),
        "every BL must define LR"
    );
}

// PUSH {r4,..,lr} is an STMDB alias: it decodes into one transfer per register at the offset
// that mode puts it, and the whole list is one SP adjustment. The transfers themselves are
// frame setup rather than program memory traffic -- see arm_frame_setup below.
#[test]
fn arm32_push_expands_per_register_and_is_marked_frame_setup() {
    let Some(exe) = fixture() else { return };
    let db = load(exe);

    let transfers: Vec<_> = db
        .rel_iter::<(Address, bool, Symbol, Symbol, i64, usize)>("arm_multi_transfer")
        .collect();
    assert!(!transfers.is_empty(), "no LDM/STM expansion at all");

    // Find one PUSH and check its whole expansion.
    let insns: std::collections::HashMap<u64, &str> = db
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
        .map(|i| (i.0, i.3))
        .collect();
    let push_addr = transfers
        .iter()
        .map(|t| t.0)
        .find(|a| insns.get(a) == Some(&"PUSH"))
        .expect("fixture must contain a PUSH");

    let mut rows: Vec<_> = transfers
        .iter()
        .filter(|t| t.0 == push_addr)
        .map(|t| (t.5, t.2, t.3, t.4))
        .collect();
    rows.sort();
    assert!(
        rows.len() >= 2,
        "a PUSH of a register list expands to one store per register"
    );
    let n = rows.len() as i64;
    for (seq, _reg, base, offset) in &rows {
        assert_eq!(*base, "SP", "PUSH is always SP-based");
        // STMDB: the lowest-numbered register sits at the lowest address, n words below
        // the old SP.
        assert_eq!(
            *offset,
            -n * 4 + *seq as i64 * 4,
            "slot offset for seq {seq}"
        );
    }
    // ...and the whole list is one SP adjustment.
    assert!(
        db.rel_iter::<(Address, Symbol, i64)>("adjusts_stack")
            .any(|(a, b, d)| *a == push_addr && *b == "SP" && *d == -n * 4),
        "PUSH must move SP by the size of its register list"
    );
    // ...and it is frame setup, not program-visible memory traffic. Those offsets are measured
    // against an SP this very instruction moves, so they name a different frame origin than the
    // settled-SP references in the body; they are the callee-save spills and return-address slot
    // CompCert's Stacking emits, which reversing Stacking removes.
    assert!(
        db.rel_iter::<(Address,)>("arm_frame_setup")
            .any(|(a,)| *a == push_addr),
        "a writeback push through SP is frame setup"
    );
    assert!(
        !db.rel_iter::<(Address, Symbol, i64)>("stack_def")
            .any(|(a, _, _)| *a == push_addr),
        "frame setup declares no frame slot store"
    );
}

// The invariant that keeps `*-8 = 0` out of the emitted C: nothing below the waist may name a
// frame slot the stack analysis cannot place. An Ainstack offset below zero is one, because the
// frame runs upward from the settled SP -- an unresolved one degrades to a bare integer in
// clight_pass and prints as a dereference of a constant.
#[test]
fn arm32_no_mach_inst_names_a_slot_below_the_frame() {
    for exe in [
        fixture(),
        thumb_fixture(),
        pool_fixture(),
        interwork_fixture(),
    ]
    .into_iter()
    .flatten()
    {
        let db = frontend(exe);
        let offending: Vec<_> = mach_insts(&db)
            .into_iter()
            .filter(|(_, mi)| {
                let am = match mi {
                    MachInst::Mstore(_, am, _, _) | MachInst::Mload(_, am, _, _) => am,
                    MachInst::Mop(Operation::Olea(am) | Operation::Oleal(am), _, _) => am,
                    _ => return false,
                };
                matches!(am, Addressing::Ainstack(o) if *o < 0)
            })
            .collect();
        assert!(
            offending.is_empty(),
            "{}: {} mach_inst(s) address a slot below the frame, first {:x?}",
            exe.display(),
            offending.len(),
            offending.first()
        );
    }
}

// `POP {..,pc}` and `BX LR` carry no branch mnemonic; classification has to look at the
// destination register, which is the one thing a mnemonic-keyed classifier cannot do.
#[test]
fn arm32_pc_writing_instructions_classify_as_returns() {
    use manifold::decompile::disassembly::branch::{self, BranchKind, PcSource};

    let Some(exe) = fixture() else { return };
    let db = load(exe);

    let transfers: Vec<_> = db.rel_iter::<(Address, bool)>("arm_pc_transfer").collect();
    assert!(
        !transfers.is_empty(),
        "fixture returns, so some instruction must write PC"
    );
    assert!(
        transfers.iter().any(|(_, is_ret)| *is_ret),
        "at least one PC write must be a restored return address"
    );

    let insns: std::collections::HashMap<u64, &str> = db
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
        .map(|i| (i.0, i.3))
        .collect();
    for (addr, is_ret) in &transfers {
        let mnem = insns.get(addr).copied().unwrap_or("");
        // No return here carries a branch mnemonic other than BX.
        let kind = branch::classify(
            Arch::Arm32,
            mnem,
            if *is_ret {
                PcSource::SavedReturnAddress
            } else {
                PcSource::Computed
            },
        )
        .kind;
        if *is_ret {
            assert_eq!(kind, BranchKind::Return, "{mnem} at {addr:#x}");
        }
    }
    // And the frontend turns them into Mreturn.
    let db = frontend(exe);
    assert!(
        mach_insts(&db)
            .iter()
            .any(|(_, m)| matches!(m, MachInst::Mreturn)),
        "no Mreturn recovered"
    );
}

// Predication is if-conversion; reversing it is a select when both candidate values are
// already in registers, and a real branch otherwise.
#[test]
fn arm32_predication_becomes_a_select_or_a_real_branch() {
    let Some(exe) = fixture() else { return };
    let db = frontend(exe);
    let insts = mach_insts(&db);
    assert!(!insts.is_empty(), "frontend produced no mach_inst at all");

    let has_select = insts
        .iter()
        .any(|(_, m)| matches!(m, MachInst::Mop(Operation::Osel(..), ..)));
    // A split predicated instruction leaves a synthetic guard branch, which reaches the
    // mach layer as an ordinary Mcond just like a real B<cond>.
    let raw: Vec<_> = db
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
    let has_guard = raw.iter().any(|i| i.3.starts_with("B."));
    assert!(
        has_select || has_guard,
        "the fixture is if-converted, so predication must surface as Osel or as a guard branch"
    );
    assert!(
        insts.iter().any(|(_, m)| matches!(m, MachInst::Mcond(..))),
        "no Mcond recovered"
    );

    // A guard branch is one byte wide and its operation half sits at the next address,
    // so the pair still covers exactly the encoded instruction.
    let by_addr: std::collections::HashMap<u64, usize> = raw.iter().map(|i| (i.0, i.1)).collect();
    for i in raw.iter().filter(|i| i.3.starts_with("B.") && i.1 == 1) {
        assert!(
            by_addr.contains_key(&(i.0 + 1)),
            "guard at {:#x} must be followed by its operation at +1",
            i.0
        );
        assert_eq!(
            by_addr[&(i.0 + 1)],
            3,
            "the operation takes the remaining 3 bytes"
        );
    }
}

// The normalizing frontend: A32 -> the SHARED Mach vocabulary.
#[test]
fn arm32_frontend_normalizes_into_shared_mach_vocabulary() {
    let Some(exe) = fixture() else { return };
    let db = frontend(exe);
    let insts = mach_insts(&db);
    let has = |f: &dyn Fn(&MachInst) -> bool| insts.iter().any(|(_, m)| f(m));

    assert!(has(&|m| matches!(m, MachInst::Mreturn)), "no Mreturn");
    assert!(has(&|m| matches!(m, MachInst::Mcall(_))), "no Mcall for BL");
    assert!(has(&|m| matches!(m, MachInst::Mcond(..))), "no Mcond");
    assert!(
        has(&|m| matches!(m, MachInst::Mtailcall(either::Either::Left(Mreg::A32(_))))),
        "no register Mtailcall for BX through the function-pointer parameter"
    );
    assert!(has(&|m| matches!(m, MachInst::Mstore(..))), "no Mstore");
    assert!(has(&|m| matches!(m, MachInst::Mload(..))), "no Mload");
    assert!(
        has(&|m| matches!(m, MachInst::Mop(Operation::Oadd, ..))),
        "no Oadd -- 32-bit ADD did not normalize"
    );
    assert!(
        has(&|m| matches!(m, MachInst::Mop(Operation::Omove, ..))),
        "no Omove -- register MOV did not normalize"
    );
    // A32 general registers are 32 bits, so nothing may land in the 64-bit half of the
    // shared alphabet.
    assert!(
        !has(&|m| matches!(
            m,
            MachInst::Mop(Operation::Oaddl | Operation::Osubl | Operation::Omull, ..)
        )),
        "a 32-bit architecture must not produce the long-width Operations"
    );

    // Frame-relative access must reach Ainstack, which is what makes stack analysis see
    // an A32 frame the same way it sees an x86 one.
    assert!(
        insts.iter().any(|(_, m)| matches!(
            m,
            MachInst::Mstore(_, Addressing::Ainstack(_), ..)
                | MachInst::Mload(_, Addressing::Ainstack(_), ..)
        )),
        "no Ainstack access -- SP-relative frame traffic did not normalize"
    );

    // Every mach_inst must be attributed to a function, or nothing downstream can place it.
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

    assert!(
        db.rel_iter::<(Address, Address, Symbol, u64)>("func_stacksz")
            .any(|(_, _, _, sz)| *sz > 0),
        "no function recovered a nonzero frame size"
    );
}

// A literal pool is data sitting inside .text. A linear sweep decodes it as garbage
// instructions; the frontend must carve it out and read the constant instead.
#[test]
fn arm32_literal_pools_are_not_decoded_as_instructions() {
    let Some(exe) = pool_fixture() else { return };
    let db = load(exe);

    let literals: Vec<_> = db.rel_iter::<(Address, i64)>("arm_literal_value").collect();
    assert!(
        !literals.is_empty(),
        "the armv5te build has no MOVW/MOVT, so 0x12345678 must come from a literal pool"
    );
    assert!(
        literals.iter().any(|(_, v)| *v == 0x12345678),
        "the pool constant must be read out of the image: {literals:?}"
    );

    // No instruction may start inside a pool word. Each pool word is exactly the target
    // of one of these PC-relative loads, so recompute the ranges and check the sweep.
    let addrs: std::collections::HashSet<u64> = db
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
        .map(|i| i.0)
        .collect();
    let indirect: std::collections::HashMap<&str, (&str, i64)> = db
        .rel_iter::<(Symbol, Symbol, Symbol, Symbol, i64, i64, usize)>("op_indirect")
        .map(|(id, _, base, _, _, disp, _)| (*id, (*base, *disp)))
        .collect();
    let mut pool_words = 0;
    for i in db.rel_iter::<(
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
    {
        let Some((base, disp)) = indirect.get(i.5) else {
            continue;
        };
        if *base != "PC" {
            continue;
        }
        // A32's PC reads as the instruction address plus 8.
        let target = (i.0 + 8).wrapping_add_signed(*disp);
        pool_words += 1;
        assert!(
            !addrs.contains(&target),
            "literal pool word at {target:#x} was decoded as an instruction"
        );
    }
    assert!(
        pool_words > 0,
        "no PC-relative loads found in the armv5te build"
    );

    // The constant reaches the mach layer as a constant, not as a load from code.
    let db = frontend(exe);
    assert!(
        mach_insts(&db)
            .iter()
            .any(|(_, m)| matches!(m, MachInst::Mop(Operation::Ointconst(0x12345678), ..))),
        "the pool constant did not normalize to Ointconst"
    );
}

// Thumb is a variable-width encoding: a linear sweep that assumes 4 bytes decodes every
// second instruction out of the middle of the previous one.
#[test]
fn arm32_thumb_decodes_at_two_byte_boundaries() {
    let Some(exe) = thumb_fixture() else { return };
    let db = load(exe);
    let by_addr = decoded_map(&db);
    assert!(!by_addr.is_empty(), "no thumb instructions decoded");

    // Every decoded instruction is 2 or 4 bytes -- never the 4-only stride A32 has. The
    // split half of a predicated instruction is the one exception, and it is 1 byte plus a
    // 1-byte guard that together cover a real 2-byte encoding.
    let guards: std::collections::HashSet<u64> = by_addr
        .iter()
        .filter(|(_, (size, mnem))| *size == 1 && mnem.starts_with("B."))
        .map(|(a, _)| *a)
        .collect();
    for (addr, (size, mnem)) in &by_addr {
        if guards.contains(addr) || guards.contains(&addr.wrapping_sub(1)) {
            continue;
        }
        assert!(
            *size == 2 || *size == 4,
            "{mnem} at {addr:#x} decoded as {size} bytes"
        );
    }
    assert!(
        by_addr.values().any(|(size, _)| *size == 2),
        "a Thumb build must contain 16-bit encodings"
    );
    // ...and consecutive 16-bit instructions really are 2 bytes apart.
    assert!(
        by_addr
            .iter()
            .any(|(a, (size, _))| *size == 2 && by_addr.contains_key(&(a + 2))),
        "no two adjacent 16-bit instructions"
    );
}

// A 32-bit Thumb-2 encoding must decode as ONE instruction. Read as two 16-bit ones it
// yields two plausible-looking but entirely wrong operations, with no decode error.
#[test]
fn arm32_thumb2_wide_encodings_decode_as_one_instruction() {
    let Some(exe) = thumb_fixture() else { return };
    let db = load(exe);
    let by_addr = decoded_map(&db);

    // MOVW/MOVT exist only as 32-bit encodings, so the fixture's 0x12345678 pins one.
    let wide: Vec<u64> = by_addr
        .iter()
        .filter(|(_, (_, mnem))| *mnem == "MOVW" || *mnem == "MOVT")
        .map(|(a, _)| *a)
        .collect();
    assert!(
        !wide.is_empty(),
        "no MOVW/MOVT decoded: {:?}",
        by_addr.len()
    );
    for addr in wide {
        assert_eq!(
            by_addr[&addr].0, 4,
            "MOVW/MOVT at {addr:#x} is a 32-bit encoding"
        );
        assert!(
            !by_addr.contains_key(&(addr + 2)),
            "the second halfword of the encoding at {addr:#x} was decoded as its own instruction"
        );
    }
}

// An IT block is Thumb's predication. Capstone folds the block's condition onto each
// covered instruction, so the existing guard/select reversal applies unchanged -- and the
// IT header itself, which computes nothing, must not become an operation.
#[test]
fn arm32_it_block_becomes_guard_or_select_and_never_an_operation() {
    let Some(exe) = interwork_fixture() else {
        return;
    };
    let db = frontend(exe);
    let raw = raw_insns(&db);

    let it_addrs: Vec<u64> = raw
        .iter()
        .filter(|i| i.3.starts_with("IT") && i.3[2..].bytes().all(|c| c == b'T' || c == b'E'))
        .map(|i| i.0)
        .collect();
    assert!(
        !it_addrs.is_empty(),
        "the fixture has an ITTEE, so an IT header must decode"
    );

    let with_mach: std::collections::HashSet<u64> =
        mach_insts(&db).iter().map(|(a, _)| *a).collect();
    for addr in &it_addrs {
        assert!(
            !with_mach.contains(addr),
            "the IT header at {addr:#x} became an operation"
        );
        // It also carries no condition of its own: spelled IT.EQ it would read as a
        // conditional instruction and be paired with the compare before it.
        let mnem = raw.iter().find(|i| i.0 == *addr).unwrap().3;
        assert!(
            !mnem.contains('.'),
            "IT header spelled with a condition: {mnem}"
        );
    }

    // The block's four instructions come back as a select and as guarded operations.
    let has_select = mach_insts(&db)
        .iter()
        .any(|(_, m)| matches!(m, MachInst::Mop(Operation::Osel(..), ..)));
    let has_guard = raw.iter().any(|i| i.3.starts_with("B.") && i.1 == 1);
    assert!(
        has_select,
        "MOVEQ Rd,Rm inside the IT block must reverse to Osel"
    );
    assert!(
        has_guard,
        "the conditional load/store must reverse to a guard branch"
    );
}

// A literal pool inside THUMB code. The pool is found through its referents, and a Thumb
// PC-relative load reads the PC as (addr+4) rounded down to a word -- get that wrong and
// the detected pool address is off, so the real pool words get decoded as instructions.
#[test]
fn arm32_thumb_literal_pools_are_not_decoded_as_instructions() {
    let Some(exe) = interwork_fixture() else {
        return;
    };
    let db = load(exe);

    let literals: Vec<_> = db.rel_iter::<(Address, i64)>("arm_literal_value").collect();
    assert!(
        literals.iter().any(|(_, v)| *v == 0x12345678),
        "the Thumb pool constant must be read out of the image: {literals:?}"
    );

    let by_addr = decoded_map(&db);
    let indirect: std::collections::HashMap<&str, (&str, i64)> = db
        .rel_iter::<(Symbol, Symbol, Symbol, Symbol, i64, i64, usize)>("op_indirect")
        .map(|(id, _, base, _, _, disp, _)| (*id, (*base, *disp)))
        .collect();
    let mut checked = 0;
    for i in raw_insns(&db) {
        let Some((base, disp)) = indirect.get(i.5) else {
            continue;
        };
        if *base != "PC" {
            continue;
        }
        // Thumb's PC reads as the instruction address plus 4, rounded down to a word.
        let target = ((i.0 + 4) & !3).wrapping_add_signed(*disp);
        checked += 1;
        assert!(
            !by_addr.contains_key(&target),
            "Thumb literal pool word at {target:#x} was decoded as an instruction"
        );
    }
    assert!(checked > 0, "no PC-relative Thumb loads found");

    let db = frontend(exe);
    assert!(
        mach_insts(&db)
            .iter()
            .any(|(_, m)| matches!(m, MachInst::Mop(Operation::Ointconst(0x12345678), ..))),
        "the Thumb pool constant did not normalize to Ointconst"
    );
}

// Interworking: one image, an A32 function and a Thumb one, reached from each other
// through BLX. Each must decode in ITS OWN instruction set.
#[test]
fn arm32_interworking_decodes_each_function_in_its_own_isa() {
    let Some(exe) = interwork_fixture() else {
        return;
    };
    let db = load(exe);
    let by_addr = decoded_map(&db);

    let arm_entry = symbol_addr(&db, "arm_helper").expect("arm_helper symbol");
    let thumb_entry = symbol_addr(&db, "thumb_leaf").expect("thumb_leaf symbol");

    // A function symbol's bit 0 is the callee's instruction set, not part of the address.
    assert_eq!(
        thumb_entry % 2,
        0,
        "the Thumb symbol's interworking bit must be stripped"
    );

    // The A32 body: every instruction 4 bytes, starting with the PUSH that saves LR.
    assert_eq!(
        by_addr.get(&arm_entry).map(|(s, m)| (*s, *m)),
        Some((4, "PUSH")),
        "arm_helper must decode as a 4-byte A32 PUSH"
    );
    for off in [0u64, 4, 8, 12, 16] {
        let a = arm_entry + off;
        assert_eq!(
            by_addr.get(&a).map(|(s, _)| *s),
            Some(4),
            "A32 instruction at {a:#x}"
        );
    }

    // The Thumb body: the entry PUSH is a 16-bit encoding.
    assert_eq!(
        by_addr.get(&thumb_entry).map(|(s, m)| (*s, *m)),
        Some((2, "PUSH")),
        "thumb_leaf must decode as a 2-byte Thumb PUSH"
    );

    // The BLX that crosses between them is a call to the other function's entry.
    let calls: std::collections::HashSet<u64> = db
        .rel_iter::<(Address, Address)>("direct_call")
        .map(|(_, callee)| *callee)
        .collect();
    assert!(
        calls.contains(&arm_entry),
        "the Thumb BLX to arm_helper must be a direct call"
    );
    assert!(
        calls.contains(&thumb_entry),
        "the BL to thumb_leaf must be a direct call"
    );
}

// The interesting corpus is stripped, so the instruction set has to be recovered rather
// than read off the mapping symbols. Recovering it must reproduce the same instruction
// boundaries the symbol-bearing build gives.
#[test]
fn arm32_isa_mode_is_recovered_without_symbols() {
    let (Some(full), Some(stripped)) = (interwork_fixture(), stripped_interwork_fixture()) else {
        return;
    };
    let db_full = load(full);
    let db_strip = load(stripped);
    assert!(
        db_strip
            .rel_iter::<(
                Address,
                usize,
                Symbol,
                Symbol,
                Symbol,
                usize,
                Symbol,
                usize,
                Symbol
            )>("symbol_table")
            .next()
            .is_none(),
        "the stripped fixture must have no symbols at all"
    );

    let thumb_entry = symbol_addr(&db_full, "thumb_leaf").expect("thumb_leaf symbol");
    let arm_entry = symbol_addr(&db_full, "arm_helper").expect("arm_helper symbol");
    let full = decoded_map(&db_full);
    let strip = decoded_map(&db_strip);

    // The Thumb entry is reached from _start's BL, the A32 one from a BLX that toggles the
    // state; both must come back at the same boundaries as the symbol-bearing build.
    for (name, entry) in [("thumb_leaf", thumb_entry), ("arm_helper", arm_entry)] {
        assert_eq!(
            strip.get(&entry).map(|(s, m)| (*s, *m)),
            full.get(&entry).map(|(s, m)| (*s, *m)),
            "{name} at {entry:#x} decoded differently once stripped"
        );
    }
    let agree = full.keys().filter(|a| strip.contains_key(a)).count();
    assert_eq!(
        agree,
        full.len(),
        "stripping changed {} of {} instruction boundaries",
        full.len() - agree,
        full.len()
    );
}

// Thumb's 16-bit data-processing encodings have no room for a separate destination:
// `ADD Rd, Rm` means `Rd := Rd + Rm`, and read as a two-register unary it silently loses
// the accumulation. Its SP form is how a Thumb prologue reserves the frame.
#[test]
fn arm32_thumb_two_operand_forms_recover_their_implicit_destination() {
    let Some(exe) = thumb_fixture() else { return };
    let db = frontend(exe);
    let insts = mach_insts(&db);

    let inplace: Vec<_> = db.rel_iter::<(Address,)>("arm_inplace_dest").collect();
    assert!(
        !inplace.is_empty(),
        "a Thumb build is full of two-operand ALU forms"
    );

    // `ADD Rd, Rm` reverses to an Oadd whose first argument IS its destination.
    assert!(
        insts.iter().any(|(_, m)| matches!(
            m,
            MachInst::Mop(Operation::Oadd, args, dst)
                if args.len() == 2 && args[0] == *dst
        )),
        "no in-place Oadd -- the two-operand 16-bit ADD did not normalize"
    );

    // `SUB SP, #imm` is the frame reservation and must register as a negative adjustment.
    assert!(
        db.rel_iter::<(Address, Symbol, i64)>("adjusts_stack")
            .any(|(_, base, delta)| *base == "SP" && *delta < 0),
        "the two-operand SUB SP, #imm did not register as a frame allocation"
    );
    assert!(
        db.rel_iter::<(Address, Address, Symbol, u64)>("func_stacksz")
            .any(|(_, _, _, sz)| *sz > 0),
        "no Thumb function recovered a nonzero frame size"
    );
}

// The whole normalizing frontend, run on a Thumb build: the shared Mach vocabulary must
// come out the same as it does for A32, since nothing above the decoder knows Thumb exists.
#[test]
fn arm32_thumb_normalizes_into_the_same_shared_mach_vocabulary() {
    let Some(exe) = thumb_fixture() else { return };
    let db = frontend(exe);
    let insts = mach_insts(&db);
    let has = |f: &dyn Fn(&MachInst) -> bool| insts.iter().any(|(_, m)| f(m));

    assert!(has(&|m| matches!(m, MachInst::Mreturn)), "no Mreturn");
    assert!(has(&|m| matches!(m, MachInst::Mcall(_))), "no Mcall for BL");
    assert!(has(&|m| matches!(m, MachInst::Mcond(..))), "no Mcond");
    assert!(has(&|m| matches!(m, MachInst::Mstore(..))), "no Mstore");
    assert!(has(&|m| matches!(m, MachInst::Mload(..))), "no Mload");
    assert!(
        has(&|m| matches!(m, MachInst::Mop(Operation::Omove, ..))),
        "no Omove -- register MOV did not normalize"
    );
    assert!(
        !has(&|m| matches!(
            m,
            MachInst::Mop(Operation::Oaddl | Operation::Osubl | Operation::Omull, ..)
        )),
        "a 32-bit architecture must not produce the long-width Operations"
    );
    assert!(
        insts.iter().any(|(_, m)| matches!(
            m,
            MachInst::Mstore(_, Addressing::Ainstack(_), ..)
                | MachInst::Mload(_, Addressing::Ainstack(_), ..)
        )),
        "no Ainstack access -- SP-relative frame traffic did not normalize"
    );

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
}

// Data inside a code section that decodes to NOTHING at all. capstone reports no
// instruction and stops; without a resynchronizing sweep everything after it is lost,
// which on a stripped firmware image means most of the program.
#[test]
fn arm32_sweep_resynchronizes_past_undecodable_bytes() {
    let Some(exe) = stripped_interwork_fixture() else {
        return;
    };
    let db = load(exe);
    let by_addr = decoded_map(&db);

    // Locate the fixture's pool through the PC-relative load that reads it; the word after
    // it is 0xffffffff, which no Thumb encoding decodes.
    let indirect: std::collections::HashMap<&str, (&str, i64)> = db
        .rel_iter::<(Symbol, Symbol, Symbol, Symbol, i64, i64, usize)>("op_indirect")
        .map(|(id, _, base, _, _, disp, _)| (*id, (*base, *disp)))
        .collect();
    let pool = raw_insns(&db)
        .iter()
        .find_map(|i| match indirect.get(i.5) {
            Some((base, disp)) if *base == "PC" => {
                Some(((i.0 + 4) & !3).wrapping_add_signed(*disp))
            }
            _ => None,
        })
        .expect("the fixture reads a literal pool");

    assert!(
        !by_addr.contains_key(&pool),
        "the pool word itself must not decode"
    );
    assert!(
        !by_addr.contains_key(&(pool + 4)),
        "0xffffffff decodes to nothing, so no instruction may start there"
    );
    assert!(
        by_addr.contains_key(&(pool + 8)),
        "the sweep must resynchronize: the instruction after the undecodable word is lost \
         otherwise, and with it the rest of the section"
    );
}

// `TBB [PC, Rn]` reads a table of branch offsets laid out immediately AFTER it, inside the
// code. Nothing in the encoding says how long that table is; it is pinned by its own
// contents, since an entry may only name a target past the end of the table.
#[test]
fn arm32_thumb_table_branch_tables_are_not_decoded_as_instructions() {
    let Some(exe) = stripped_interwork_fixture() else {
        return;
    };
    let db = load(exe);
    let by_addr = decoded_map(&db);

    let tbb: Vec<u64> = by_addr
        .iter()
        .filter(|(_, (_, mnem))| *mnem == "TBB" || *mnem == "TBH")
        .map(|(a, _)| *a)
        .collect();
    assert_eq!(tbb.len(), 1, "the fixture has exactly one TBB: {tbb:#x?}");
    let table = tbb[0] + 4;

    // The fixture's table is six single-byte entries; none of them may start an
    // instruction, and the first real target must.
    for off in 0..6u64 {
        assert!(
            !by_addr.contains_key(&(table + off)),
            "table byte at {:#x} was decoded as an instruction",
            table + off
        );
    }
    assert!(
        by_addr.contains_key(&(table + 6)),
        "the first case body right after the table must still decode"
    );
    // The table branch is a control transfer, so it does not fall through into its table.
    assert!(
        db.rel_iter::<(Address, bool)>("arm_pc_transfer")
            .any(|(a, is_ret)| *a == tbb[0] && !*is_ret),
        "TBB must register as a computed PC transfer"
    );
}

// CBZ/CBNZ exist only in Thumb and carry their own comparison: they test a register
// against zero WITHOUT reading the flags, so there is no flag setter to pair them with.
#[test]
fn arm32_thumb_compare_and_branch_carries_its_own_condition() {
    let Some(exe) = interwork_fixture() else {
        return;
    };
    let db = frontend(exe);
    let raw = raw_insns(&db);
    let cbz: Vec<u64> = raw
        .iter()
        .filter(|i| i.3 == "CBZ" || i.3 == "CBNZ")
        .map(|i| i.0)
        .collect();
    assert!(!cbz.is_empty(), "the fixture has a CBZ");

    for addr in &cbz {
        assert!(
            mach_insts(&db)
                .iter()
                .any(|(a, m)| a == addr && matches!(m, MachInst::Mcond(..))),
            "CBZ at {addr:#x} did not become an Mcond"
        );
    }
    // Its target is a real CFG edge, which needs the target to be read from the SECOND
    // operand slot -- every other ARM32 branch puts it first.
    let targets: std::collections::HashSet<u64> = db
        .rel_iter::<(Address, Address, Symbol)>("ddisasm_cfg_edge")
        .filter(|(src, _, _)| cbz.contains(src))
        .map(|(_, dst, _)| *dst)
        .collect();
    assert!(
        !targets.is_empty(),
        "the CBZ produced no CFG edge to its target"
    );
}
