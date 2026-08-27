use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use manifold::abi::{Arch, BinaryFormat};
use manifold::decompile::elevator::DecompileDB;
use manifold::decompile::passes::abi_pass::AbiPass;
use manifold::decompile::passes::pass::IRPass;
use manifold::mreg::Mreg;
use manifold::x86::types::{Address, Symbol};

fn command_exists(name: &str) -> bool {
    Command::new(name)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn build_fixture() -> Option<PathBuf> {
    if !command_exists("clang") || !command_exists("lld-link") {
        eprintln!("skipping PE test: clang/lld-link unavailable");
        return None;
    }

    let dir = std::env::temp_dir().join(format!("manifold_pe_fixture_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let dll_c = dir.join("imported.c");
    let exe_c = dir.join("fixture.c");
    let dll_obj = dir.join("imported.obj");
    let exe_obj = dir.join("fixture.obj");
    let dll = dir.join("imported.dll");
    let import_lib = dir.join("imported.lib");
    let exe = dir.join("fixture.exe");

    std::fs::write(
        &dll_c,
        "__declspec(dllexport) int Imported(int x) { return x + 11; }\n",
    )
    .unwrap();
    std::fs::write(
        &exe_c,
        r#"
__declspec(dllimport) int Imported(int);
int _fltused;
__declspec(dllexport) __declspec(noinline) int add_five(int a, int b, int c, int d, int e) {
    return a + b + c + d + e;
}
__declspec(dllexport) __declspec(noinline) int first_and_fifth(int a, int b, int c, int d, int e) {
    return a + e;
}
__declspec(dllexport) __declspec(noinline) double mixed_five(int a, double b, int c, double d, double e) {
    return a + b + c + d + e;
}
__declspec(dllexport) int exported(int x) {
    return add_five(x, 2, 3, 4, 5) + first_and_fifth(x, 20, 30, 40, 50) + Imported(x);
}
__declspec(dllexport) double exported_float(int x, double e) {
    return mixed_five(x, 2.5, 3, 4.5, e);
}
void entry(void) { (void)exported(7); }
"#,
    )
    .unwrap();

    let compile = |source: &Path, output: &Path| {
        Command::new("clang")
            .args(["--target=x86_64-pc-windows-msvc", "-O1", "-c"])
            .arg(source)
            .arg("-o")
            .arg(output)
            .status()
            .unwrap()
    };
    assert!(compile(&dll_c, &dll_obj).success());
    assert!(Command::new("lld-link")
        .args(["/dll", "/noentry", "/nodefaultlib"])
        .arg(format!("/out:{}", dll.display()))
        .arg(format!("/implib:{}", import_lib.display()))
        .arg(&dll_obj)
        .status()
        .unwrap()
        .success());
    assert!(compile(&exe_c, &exe_obj).success());
    assert!(Command::new("lld-link")
        .args(["/entry:entry", "/subsystem:console", "/nodefaultlib"])
        .arg(format!("/out:{}", exe.display()))
        .arg(&exe_obj)
        .arg(&import_lib)
        .status()
        .unwrap()
        .success());
    Some(exe)
}

fn fixture() -> Option<&'static Path> {
    static FIXTURE: OnceLock<Option<PathBuf>> = OnceLock::new();
    FIXTURE.get_or_init(build_fixture).as_deref()
}

#[test]
fn loader_stores_arch_width_with_the_declared_i64_relation_type() {
    let binary = Path::new("/bin/true");
    if !binary.exists() {
        return;
    }

    let mut db = DecompileDB::default();
    manifold::decompile::disassembly::load_from_binary(&mut db, binary);
    let widths: Vec<i64> = db
        .rel_iter::<(i64,)>("arch_bit")
        .map(|(width,)| *width)
        .collect();

    assert_eq!(widths, vec![if db.abi().is_64bit() { 64 } else { 32 }]);
}

#[test]
fn pe_loader_recovers_iat_exports_unwind_and_win64_abi() {
    let Some(exe) = fixture() else { return };
    let mut db = DecompileDB::default();
    manifold::decompile::disassembly::load_from_binary(&mut db, exe);

    assert_eq!(db.abi().format, BinaryFormat::Pe);
    assert!(db
        .rel_iter::<(Address, Symbol)>("pointer_to_external_symbol")
        .any(|(_, name)| *name == "Imported"));
    assert!(db
        .rel_iter::<(Address, Symbol, Symbol)>("symbols")
        .any(|(_, name, _)| *name == "exported"));
    assert!(db
        .rel_iter::<(Address, Address)>("known_function_range")
        .any(|(start, end)| start < end));
    assert!(db
        .rel_iter::<(Address,)>("known_function_entry")
        .any(|(address,)| *address >= 0x1_0000_0000));

    AbiPass.run(&mut db);
    assert!(db
        .rel_iter::<(Mreg, usize)>("abi_int_arg_position")
        .any(|(reg, pos)| *reg == Mreg::CX && *pos == 0));
    assert!(db
        .rel_iter::<(Mreg, usize)>("abi_float_arg_position")
        .any(|(reg, pos)| *reg == Mreg::X2 && *pos == 2));
    assert!(db
        .rel_iter::<(i64,)>("abi_outgoing_stack_base")
        .any(|(v,)| *v == 32));
    assert!(db
        .rel_iter::<(i64,)>("abi_incoming_sp_stack_base")
        .any(|(v,)| *v == 40));
    assert!(db
        .rel_iter::<(Mreg,)>("is_callee_saved")
        .any(|(r,)| *r == Mreg::SI));

    // ABI state is per decompilation: loading an ELF immediately afterward
    // must not retain the Windows calling convention.
    if Path::new("/bin/true").exists() {
        let mut elf = DecompileDB::default();
        manifold::decompile::disassembly::load_from_binary(&mut elf, Path::new("/bin/true"));
        assert_eq!(elf.abi().format, BinaryFormat::Elf);
        assert_eq!(db.abi().format, BinaryFormat::Pe);
    }
}

#[test]
fn pe_pipeline_emits_export_and_named_import_call() {
    let Some(exe) = fixture() else { return };
    let exe = exe.to_path_buf();
    std::thread::Builder::new()
        .name("pe-pipeline".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let mut db = DecompileDB::default();
            manifold::decompile::disassembly::load_from_binary(&mut db, &exe);
            manifold::decompile::disassembly::load_preset(&mut db);
            db.run_pipeline(&exe, false, false);

            let tu = db
                .cast_optimized_translation_unit
                .as_ref()
                .expect("PE pipeline must emit a translation unit");
            let text = manifold::decompile::passes::c_pass::print_translation_unit(tu);
            assert!(text.contains("exported("), "missing PE export in:\n{text}");
            assert!(
                text.contains("Imported("),
                "IAT call was not named in:\n{text}"
            );
            assert!(
                text.contains("add_five(p0, 2, 3, 4, 5)"),
                "Win64 stack argument value was not preserved in:\n{text}"
            );
            // Clang sees the callee body and is free to omit setup for its
            // unused b/c/d parameters even without inlining it. The binary
            // therefore contains only positions 0 and 4. The decompiler must
            // preserve that gap as five source-level arguments and keep the
            // real fifth value in the final slot.
            let sparse_call = text
                .lines()
                .find(|line| line.contains("= first_and_fifth("))
                .expect("missing call to first_and_fifth");
            let sparse_tail = sparse_call
                .split_once("first_and_fifth(")
                .map(|(_, tail)| tail)
                .expect("malformed first_and_fifth call");
            let mut nesting = 0_usize;
            let sparse_end = sparse_tail
                .char_indices()
                .find_map(|(index, ch)| match ch {
                    '(' => {
                        nesting += 1;
                        None
                    }
                    ')' if nesting == 0 => Some(index),
                    ')' => {
                        nesting -= 1;
                        None
                    }
                    _ => None,
                })
                .expect("unterminated first_and_fifth call");
            let sparse_args = &sparse_tail[..sparse_end];
            assert_eq!(
                sparse_args.split(',').count(),
                5,
                "Win64 sparse parameter slots were compacted in:\n{text}"
            );
            assert_eq!(
                sparse_args.rsplit(',').next().map(str::trim),
                Some("50"),
                "Win64 fifth argument moved out of position 4 in:\n{text}"
            );

            let sparse_body_start = text
                .match_indices("first_and_fifth(")
                .find_map(|(start, _)| {
                    let suffix = &text[start..];
                    let brace = suffix.find('{')?;
                    let semicolon = suffix.find(';').unwrap_or(usize::MAX);
                    (brace < semicolon).then_some(start + brace + 1)
                })
                .expect("missing first_and_fifth definition");
            let sparse_body = &text[sparse_body_start
                ..sparse_body_start
                    + text[sparse_body_start..]
                        .find("\n}")
                        .expect("unterminated first_and_fifth definition")];
            assert!(
                sparse_body.contains("p0") && sparse_body.contains("p4"),
                "Win64 sparse callee dataflow did not bind positions 0 and 4:\n{sparse_body}"
            );

            let mixed_call = text
                .lines()
                .find(|line| line.contains("= mixed_five(") || line.contains("return mixed_five("))
                .unwrap_or_else(|| panic!("missing call to mixed_five in:\n{text}"));
            let mixed_args = mixed_call
                .split_once("mixed_five(")
                .and_then(|(_, tail)| tail.trim().strip_suffix(");"))
                .expect("malformed mixed_five call");
            let mixed_args: Vec<&str> = mixed_args.split(',').map(str::trim).collect();
            assert_eq!(
                mixed_args.len(),
                5,
                "Win64 mixed GP/XMM slots did not form one five-argument sequence:\n{text}"
            );
            assert!(
                mixed_args[0].contains("p0"),
                "Win64 live-in RCX was not forwarded in slot 0:\n{text}"
            );
            assert!(
                mixed_args[4].contains("p1"),
                "Win64 live-in double was not preserved in stack slot 4:\n{text}"
            );
            let add_body_start = text
                .match_indices("add_five(")
                .find_map(|(start, _)| {
                    let suffix = &text[start..];
                    let brace = suffix.find('{')?;
                    let semicolon = suffix.find(';').unwrap_or(usize::MAX);
                    (brace < semicolon).then_some(start + brace + 1)
                })
                .expect("missing add_five definition");
            let add_body = &text[add_body_start
                ..add_body_start
                    + text[add_body_start..]
                        .find("\n}")
                        .expect("unterminated add_five definition")];
            for parameter in ["p0", "p1", "p2", "p3", "p4"] {
                assert!(
                    add_body.contains(parameter),
                    "Win64 parameter dataflow lost `{parameter}` in:\n{add_body}"
                );
            }
            assert!(
                add_body.matches('+').count() >= 4,
                "Win64 five-parameter reduction lost additions in:\n{add_body}"
            );

            let add_five = db
                .rel_iter::<(Address, Symbol, Symbol)>("symbols")
                .find_map(|(addr, name, _)| (*name == "add_five").then_some(*addr))
                .expect("missing add_five export");
            assert!(db
                .rel_iter::<(Address, usize)>("emit_function_param_count")
                .any(|(addr, count)| *addr == add_five && *count == 5));
            assert!(
                db.rel_iter::<(manifold::x86::types::Node, Address)>("call_target_func")
                    .filter(|(_, target)| *target == add_five)
                    .any(|(call, _)| db
                        .rel_iter::<(
                            manifold::x86::types::Node,
                            usize,
                            manifold::x86::types::RTLReg
                        )>("call_arg")
                        .any(|(arg_call, position, _)| arg_call == call && *position == 4)),
                "Win64 fifth argument was not recovered at shared position 4"
            );

            let first_and_fifth = db
                .rel_iter::<(Address, Symbol, Symbol)>("symbols")
                .find_map(|(addr, name, _)| (*name == "first_and_fifth").then_some(*addr))
                .expect("missing first_and_fifth export");
            assert!(db
                .rel_iter::<(Address, usize)>("emit_function_param_count")
                .any(|(addr, count)| *addr == first_and_fifth && *count == 5));

            let mixed_five = db
                .rel_iter::<(Address, Symbol, Symbol)>("symbols")
                .find_map(|(addr, name, _)| (*name == "mixed_five").then_some(*addr))
                .expect("missing mixed_five export");
            assert!(db
                .rel_iter::<(Address, usize)>("emit_function_param_count")
                .any(|(addr, count)| *addr == mixed_five && *count == 5));
        })
        .expect("failed to spawn PE pipeline test thread")
        .join()
        .expect("PE pipeline test thread panicked");
}

// PE32 (32-bit x86 Windows). cdecl, stdcall and fastcall coexist in one image, and the recovered
// convention comes from evidence the binary carries: the callee's RET imm16 and MSVC's name decoration.
// Like the PE32+ fixture above, this is a no-op when no 32-bit Windows toolchain is installed.

fn build_fixture32() -> Option<PathBuf> {
    if !command_exists("clang") || !command_exists("lld-link") {
        eprintln!("skipping PE32 test: clang/lld-link unavailable");
        return None;
    }

    let dir = std::env::temp_dir().join(format!("manifold_pe32_fixture_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let dll_c = dir.join("imported32.c");
    let exe_c = dir.join("fixture32.c");
    let dll_obj = dir.join("imported32.obj");
    let exe_obj = dir.join("fixture32.obj");
    let dll = dir.join("imported32.dll");
    let import_lib = dir.join("imported32.lib");
    let exe = dir.join("fixture32.exe");

    std::fs::write(
        &dll_c,
        "__declspec(dllexport) int __stdcall Imported32(int x) { return x + 11; }\n",
    )
    .unwrap();
    std::fs::write(
        &exe_c,
        r#"
__declspec(dllimport) int __stdcall Imported32(int);
int g_a, g_b;
__declspec(dllexport) __declspec(noinline) int __stdcall std_three(int a, int b, int c) {
    return a + b + c;
}
// Only the RET imm16 and the @12 decoration know this takes three arguments; the body reads one.
__declspec(dllexport) __declspec(noinline) int __stdcall std_unused(int a, int b, int c) {
    return a;
}
__declspec(dllexport) __declspec(noinline) int __fastcall fast_three(int a, int b, int c) {
    return a * b + c;
}
// cdecl: both arguments on the stack from position 0, caller cleans up, so no RET imm16 and no decorated byte count.
__declspec(dllexport) __declspec(noinline) void __cdecl cdecl_two(int a, int b) {
    g_a = a;
    g_b = b;
}
__declspec(dllexport) int __cdecl caller(int x) {
    cdecl_two(x, 6);
    return std_three(x, 2, 3) + std_unused(x, 20, 30)
         + fast_three(x, 4, 5) + Imported32(x);
}
void entry(void) { (void)caller(7); }
"#,
    )
    .unwrap();

    // A missing 32-bit Windows target must skip the test, not fail it.
    let compile = |source: &Path, output: &Path| -> bool {
        Command::new("clang")
            .args(["--target=i686-windows-msvc", "-O1", "-c"])
            .arg(source)
            .arg("-o")
            .arg(output)
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
    };
    if !compile(&dll_c, &dll_obj) {
        eprintln!("skipping PE32 test: clang has no i686-windows-msvc target");
        return None;
    }
    let linked = Command::new("lld-link")
        .args(["/dll", "/noentry", "/nodefaultlib", "/machine:x86"])
        .arg(format!("/out:{}", dll.display()))
        .arg(format!("/implib:{}", import_lib.display()))
        .arg(&dll_obj)
        .status()
        .map(|s| s.success())
        .unwrap_or(false);
    if !linked {
        eprintln!("skipping PE32 test: lld-link cannot link /machine:x86");
        return None;
    }
    if !compile(&exe_c, &exe_obj) {
        return None;
    }
    let linked = Command::new("lld-link")
        .args([
            "/entry:entry",
            "/subsystem:console",
            "/nodefaultlib",
            "/machine:x86",
        ])
        .arg(format!("/out:{}", exe.display()))
        .arg(&exe_obj)
        .arg(&import_lib)
        .status()
        .map(|s| s.success())
        .unwrap_or(false);
    if !linked {
        return None;
    }
    Some(exe)
}

fn fixture32() -> Option<&'static Path> {
    static FIXTURE32: OnceLock<Option<PathBuf>> = OnceLock::new();
    FIXTURE32.get_or_init(build_fixture32).as_deref()
}

fn symbol_address(db: &DecompileDB, name: &str) -> Address {
    db.rel_iter::<(Address, Symbol, Symbol)>("symbols")
        .find_map(|(addr, sym, _)| (*sym == name).then_some(*addr))
        .unwrap_or_else(|| panic!("missing PE32 export {name}"))
}

#[test]
fn pe32_loader_recovers_iat_exports_decorations_and_cdecl_abi() {
    let Some(exe) = fixture32() else { return };
    let mut db = DecompileDB::default();
    manifold::decompile::disassembly::load_from_binary(&mut db, exe);

    assert_eq!(db.abi().format, BinaryFormat::Pe);
    assert_eq!(db.abi().arch, Arch::X86_32);
    assert_eq!(db.abi().pointer_size, 4);

    // IAT naming: `_Imported32@4` is read as a stdcall import with one 4-byte argument, and the
    // pipeline sees the UNDECORATED identifier.
    assert!(
        db.rel_iter::<(Address, Symbol)>("pointer_to_external_symbol")
            .any(|(_, name)| *name == "Imported32"),
        "PE32 IAT slot was not named"
    );
    assert!(db
        .rel_iter::<(Symbol, i64)>("extern_decorated_arg_bytes")
        .any(|(name, bytes)| *name == "Imported32" && *bytes == 4));

    // Exports, also undecorated.
    for name in [
        "std_three",
        "std_unused",
        "fast_three",
        "cdecl_two",
        "caller",
    ] {
        assert!(
            db.rel_iter::<(Address, Symbol, Symbol)>("symbols")
                .any(|(_, sym, _)| *sym == name),
            "missing PE32 export {name}"
        );
    }

    // `_std_three@12` is stdcall with 12 argument bytes and no register arguments.
    let std_three = symbol_address(&db, "std_three");
    assert!(db
        .rel_iter::<(Address, i64)>("func_decorated_arg_bytes")
        .any(|(addr, bytes)| *addr == std_three && *bytes == 12));
    assert!(!db
        .rel_iter::<(Address, usize)>("func_decorated_reg_args")
        .any(|(addr, _)| *addr == std_three));

    // `@fast_three@12` is fastcall: two of those 12 bytes ride in ECX and EDX.
    let fast_three = symbol_address(&db, "fast_three");
    assert!(db
        .rel_iter::<(Address, i64)>("func_decorated_arg_bytes")
        .any(|(addr, bytes)| *addr == fast_three && *bytes == 12));
    assert!(db
        .rel_iter::<(Address, usize)>("func_decorated_reg_args")
        .any(|(addr, count)| *addr == fast_three && *count == 2));

    // `cdecl_two` keeps its plain name and leaves no decoration evidence at all.
    let cdecl_two = symbol_address(&db, "cdecl_two");
    assert!(!db
        .rel_iter::<(Address, i64)>("func_decorated_arg_bytes")
        .any(|(addr, _)| *addr == cdecl_two));

    // 32-bit PE has NO exception directory of RUNTIME_FUNCTION records, so there are no exact
    // function extents to fabricate; discovery runs on exports, the entry point and prologues.
    assert_eq!(
        db.rel_iter::<(Address, Address)>("known_function_range")
            .count(),
        0,
        "PE32 has no .pdata, so no function extents may be invented"
    );
    assert!(db
        .rel_iter::<(Address,)>("known_function_entry")
        .any(|(addr,)| *addr == std_three));

    AbiPass.run(&mut db);
    // cdecl is the image-wide default: every argument is on the stack and the first one is position 0.
    assert!(db
        .rel_iter::<(usize,)>("abi_first_stack_arg_position")
        .any(|(v,)| *v == 0));
    // ECX/EDX are the fastcall/thiscall slots, claimed per function rather than image-wide.
    assert!(db
        .rel_iter::<(bool,)>("abi_reg_args_per_function")
        .any(|(v,)| *v));
    assert!(db
        .rel_iter::<(Mreg, usize)>("abi_int_arg_position")
        .any(|(reg, pos)| *reg == Mreg::CX && *pos == 0));
    assert!(db
        .rel_iter::<(Mreg, usize)>("abi_int_arg_position")
        .any(|(reg, pos)| *reg == Mreg::DX && *pos == 1));
    // CALL pushes a 4-byte return address and Windows x86 has no shadow space.
    assert!(db
        .rel_iter::<(i64,)>("abi_incoming_sp_stack_base")
        .any(|(v,)| *v == 4));
    assert!(db
        .rel_iter::<(i64,)>("abi_outgoing_stack_base")
        .any(|(v,)| *v == 0));
    assert!(db
        .rel_iter::<(i64,)>("abi_pointer_size")
        .any(|(v,)| *v == 4));
    // Win64's shared GP/XMM ordinal slots are an x64 rule and must not leak onto PE32.
    assert!(db
        .rel_iter::<(bool,)>("abi_shared_arg_slots")
        .next()
        .is_none());
}

#[test]
fn pe32_recovers_per_function_calling_conventions() {
    let Some(exe) = fixture32() else { return };
    let exe = exe.to_path_buf();
    std::thread::Builder::new()
        .name("pe32-pipeline".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let mut db = DecompileDB::default();
            manifold::decompile::disassembly::load_from_binary(&mut db, &exe);
            manifold::decompile::disassembly::load_preset(&mut db);
            db.run_pipeline(&exe, false, false);

            let std_three = symbol_address(&db, "std_three");
            let std_unused = symbol_address(&db, "std_unused");
            let fast_three = symbol_address(&db, "fast_three");
            let cdecl_two = symbol_address(&db, "cdecl_two");

            // RET imm16 -> byte count, attributed to its own function through instr_in_function.
            // stdcall pops all three arguments; fastcall pops only the one that rode on the stack.
            assert!(
                db.rel_iter::<(Address, i64)>("func_callee_pop_bytes")
                    .any(|(addr, bytes)| *addr == std_three && *bytes == 12),
                "stdcall RET 12 was not attributed to std_three"
            );
            assert!(
                db.rel_iter::<(Address, i64)>("func_callee_pop_bytes")
                    .any(|(addr, bytes)| *addr == fast_three && *bytes == 4),
                "fastcall RET 4 was not attributed to fast_three"
            );
            // cdecl's caller cleans up, so the callee has no RET imm16 at all.
            assert!(
                !db.rel_iter::<(Address, i64)>("func_callee_pop_bytes")
                    .any(|(addr, _)| *addr == cdecl_two),
                "a cdecl callee must not claim callee cleanup"
            );

            // fastcall claims two leading register positions; cdecl and stdcall claim none.
            assert!(db
                .rel_iter::<(Address, usize)>("func_reg_arg_count")
                .any(|(addr, count)| *addr == fast_three && *count == 2));
            assert!(!db
                .rel_iter::<(Address, usize)>("func_reg_arg_count")
                .any(|(addr, count)| *addr == cdecl_two && *count > 0));

            let param_count = |addr: Address| -> Option<usize> {
                db.rel_iter::<(Address, usize)>("emit_function_param_count")
                    .find_map(|(a, c)| (*a == addr).then_some(*c))
            };
            assert_eq!(param_count(std_three), Some(3), "stdcall arity");
            assert_eq!(param_count(fast_three), Some(3), "fastcall arity");
            assert_eq!(param_count(cdecl_two), Some(2), "cdecl arity");
            // The decisive case: two of these three parameters are never read, so only the
            // callee-cleanup byte count can account for them.
            assert_eq!(
                param_count(std_unused),
                Some(3),
                "RET imm16 did not supply the unread stdcall parameters"
            );

            let tu = db
                .cast_optimized_translation_unit
                .as_ref()
                .expect("PE32 pipeline must emit a translation unit");
            let text = manifold::decompile::passes::c_pass::print_translation_unit(tu);
            assert!(text.contains("caller("), "missing PE32 export in:\n{text}");
            assert!(
                text.contains("Imported32("),
                "PE32 IAT call was not named in:\n{text}"
            );
        })
        .expect("failed to spawn PE32 pipeline test thread")
        .join()
        .expect("PE32 pipeline test thread panicked");
}
