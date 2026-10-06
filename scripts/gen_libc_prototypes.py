#!/usr/bin/env python3
"""Derive the x86-64 glibc prototype table from the platform's own headers.

Writes src/decompile/passes/abi_libc_prototypes.rs. Every entry is a declaration
that clang parsed from system headers: the exported symbol (asm-label redirects
such as fstat -> fstat64 or strerror_r -> __xpg_strerror_r are honored), its
fixed parameters and whether it is variadic. Types are projected onto the
decompiler's coarse XType vocabulary with the conventions of the hand-written
table in abi_pass.rs (size_t -> Xany64, any record/void pointer -> Xptr).
Functions whose signature has no XType (struct/union by value, long double,
__int128, vector types) are omitted rather than approximated.

The two glibc symbol families that 2.35 headers cannot declare are added as
exact prototype aliases, as the glibc ABI defines them: __isoc99_* (scanf
family) and __isoc23_* (glibc 2.38 C2x strtol/scanf families).

Usage: gen_libc_prototypes.py [--clang PATH] [--out PATH]
"""
import argparse, json, re, subprocess, sys, tempfile
from pathlib import Path

HEADERS = """
aio.h argp.h arpa/inet.h assert.h byteswap.h ctype.h dirent.h dlfcn.h endian.h err.h errno.h error.h
execinfo.h fcntl.h fenv.h fmtmsg.h fnmatch.h fts.h ftw.h getopt.h glob.h grp.h iconv.h ifaddrs.h
inttypes.h langinfo.h libgen.h libintl.h limits.h link.h locale.h malloc.h math.h mcheck.h mntent.h
monetary.h mqueue.h net/if.h netdb.h netinet/in.h nl_types.h obstack.h poll.h printf.h pthread.h pty.h
pwd.h regex.h sched.h search.h semaphore.h setjmp.h shadow.h signal.h spawn.h stdio.h stdio_ext.h
stdlib.h string.h strings.h sys/auxv.h sys/epoll.h sys/eventfd.h sys/file.h sys/fsuid.h sys/inotify.h
sys/ioctl.h sys/ipc.h sys/mman.h sys/mount.h sys/msg.h sys/personality.h sys/prctl.h sys/ptrace.h
sys/random.h sys/resource.h sys/select.h sys/sem.h sys/sendfile.h sys/shm.h sys/signalfd.h
sys/socket.h sys/stat.h sys/statfs.h sys/statvfs.h sys/syscall.h sys/sysinfo.h sys/sysmacros.h
sys/time.h sys/timeb.h sys/timerfd.h sys/times.h sys/timex.h sys/types.h sys/uio.h sys/un.h
sys/utsname.h sys/vfs.h sys/wait.h sys/xattr.h syslog.h termios.h time.h ucontext.h unistd.h utime.h
utmp.h utmpx.h wchar.h wctype.h wordexp.h
""".split()

# Exact prototype aliases defined by the glibc ABI (symbol -> source function).
ISOC99_SCANF = ["scanf", "fscanf", "sscanf", "vscanf", "vfscanf", "vsscanf",
                "wscanf", "fwscanf", "swscanf", "vwscanf", "vfwscanf", "vswscanf"]
ISOC23 = ISOC99_SCANF + ["strtol", "strtoul", "strtoll", "strtoull", "strtoimax", "strtoumax",
                         "wcstol", "wcstoul", "wcstoll", "wcstoull", "wcstoimax", "wcstoumax"]

QUALIFIERS = re.compile(r"\b(const|volatile|restrict|__restrict|_Nonnull|_Nullable|__attribute__\(\([^)]*\)\))\b")


def scalar(base):
    base = " ".join(base.split())
    table = {
        "void": "Xvoid", "_Bool": "Xbool", "bool": "Xbool",
        "char": "Xint8signed", "signed char": "Xint8signed", "unsigned char": "Xint8unsigned",
        "short": "Xint16signed", "short int": "Xint16signed", "signed short": "Xint16signed",
        "unsigned short": "Xint16unsigned", "unsigned short int": "Xint16unsigned",
        "int": "Xint", "signed int": "Xint", "signed": "Xint",
        "unsigned int": "Xintunsigned", "unsigned": "Xintunsigned",
        "long": "Xlong", "long int": "Xlong", "long long": "Xlong", "long long int": "Xlong",
        "unsigned long": "Xlongunsigned", "unsigned long int": "Xlongunsigned",
        "unsigned long long": "Xlongunsigned", "unsigned long long int": "Xlongunsigned",
        "double": "Xfloat", "float": "Xsingle",
    }
    if base in table:
        return table[base]
    if base.startswith("enum "):
        return "Xint"
    return None  # records by value, long double, __int128, vectors: no XType


def xtype(sugared, desugared):
    """Project one C type (sugared spelling for typedef names) onto XType."""
    s = QUALIFIERS.sub(" ", sugared).strip()
    if s == "size_t":
        return "Xany64"
    if s in ("ssize_t", "__ssize_t", "off_t", "__off_t", "off64_t", "__off64_t", "ptrdiff_t"):
        return "Xlong"
    t = QUALIFIERS.sub(" ", desugared or sugared).strip()
    if "(*" in t or "(^" in t:
        return "Xfuncptr"
    # Parameter arrays decay: T[] / T[N] is T *.
    t = re.sub(r"\[[^\]]*\]$", "*", t).strip()
    stars = 0
    while t.endswith("*"):
        stars += 1
        t = t[:-1].strip()
    t = " ".join(t.split())
    record = {"FILE": "LIBC_FILE_RECORD", "struct _IO_FILE": "LIBC_FILE_RECORD",
              "DIR": "LIBC_DIR_RECORD", "struct __dirstream": "LIBC_DIR_RECORD"}
    base = " ".join(QUALIFIERS.sub(" ", sugared).replace("*", " ").split())
    if stars == 1 and (base in record or t in record):
        return f"XstructPtr({record.get(base) or record[t]})"
    if stars == 0:
        return scalar(t)
    if t in ("char", "signed char", "unsigned char"):
        return {1: "Xcharptr", 2: "Xcharptrptr"}.get(stars, "Xptr")
    if stars == 1 and t in ("int", "unsigned int", "signed int"):
        return "Xintptr"
    if stars == 1 and t == "double":
        return "Xfloatptr"
    if stars == 1 and t == "float":
        return "Xsingleptr"
    if stars == 1 and "(" in t:
        return "Xfuncptr"
    return "Xptr"


def split_function_type(qual):
    """'RET (PARAMS)' -> (RET, variadic); None for unparseable shapes."""
    # Function-type attributes (noreturn, format, ...) follow the parameter list.
    q = re.sub(r"(\s*__attribute__\(\((?:[^()]|\([^()]*\))*\)\))+\s*$", "", qual.strip())
    if not q.endswith(")"):
        return None
    depth = 0
    for i in range(len(q) - 1, -1, -1):
        if q[i] == ")":
            depth += 1
        elif q[i] == "(":
            depth -= 1
            if depth == 0:
                ret, params = q[:i].strip(), q[i + 1:-1]
                if not ret or ret.endswith("("):
                    return None
                return ret, params.strip().endswith("...")
    return None


def declarations(clang, defines):
    """Top-level function declarations as (symbol, ret, [(sugared, canonical)], variadic).

    libclang's mangled name is the symbol a call binds to, so asm-label
    redirects (fstat -> fstat64, sscanf -> __isoc99_sscanf) are resolved by
    the compiler rather than by string matching. Any parse error aborts: an
    unknown typedef silently becomes `int` under clang's error recovery.
    """
    import clang.cindex as ci
    llvm = Path(clang).resolve().parents[1]
    if not ci.Config.loaded:
        ci.Config.set_library_file(str(llvm / "lib" / "libclang.so"))
    resource = subprocess.run([clang, "-print-resource-dir"], capture_output=True, text=True,
                              check=True).stdout.strip()
    source = "".join(f"#include <{h}>\n" for h in HEADERS)
    args = ["-x", "c", "-isystem", resource + "/include", *defines]
    tu = ci.Index.create().parse("all.c", args=args, unsaved_files=[("all.c", source)])
    errors = [d for d in tu.diagnostics if d.severity >= ci.Diagnostic.Error]
    if errors:
        raise SystemExit(f"header parse failed under {defines}: {errors[0]}")
    for cursor in tu.cursor.get_children():
        if cursor.kind != ci.CursorKind.FUNCTION_DECL:
            continue
        ret = cursor.result_type
        params = [(a.type.spelling, a.type.get_canonical().spelling) for a in cursor.get_arguments()]
        yield (cursor.mangled_name or cursor.spelling, (ret.spelling, ret.get_canonical().spelling),
               params, cursor.type.is_function_variadic())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--clang", default="clang", help="clang used to parse the system headers")
    ap.add_argument("--out", default=str(Path(__file__).resolve().parents[1] / "src/decompile/passes/abi_libc_prototypes.rs"))
    args = ap.parse_args()
    table, conflicts = {}, set()
    passes = [["-D_GNU_SOURCE"],
              ["-D_GNU_SOURCE", "-O2", "-D_FORTIFY_SOURCE=2"],   # __*_chk declarations
              ["-std=c11", "-D_FILE_OFFSET_BITS=64"],            # ISO/LFS asm-label redirects
              ["-std=c11", "-D_POSIX_C_SOURCE=200809L", "-D_XOPEN_SOURCE=700"]]  # XSI redirects (__xpg_*)
    for defines in passes:
        for symbol, (ret_sugar, ret_canonical), params, variadic in declarations(args.clang, defines):
            ret = xtype(ret_sugar, ret_canonical)
            ps = [xtype(sugared, canonical) for sugared, canonical in params]
            if ret is None or any(p is None for p in ps) or "Xvoid" in ps:
                continue
            entry = (ret, tuple(ps), variadic)
            if symbol in table and table[symbol] != entry:
                conflicts.add(symbol)
            table.setdefault(symbol, entry)
    for prefix, family in (("__isoc99_", ISOC99_SCANF), ("__isoc23_", ISOC23)):
        for base in family:
            if base in table:
                table.setdefault(prefix + base, table[base])
    for symbol in conflicts:
        table.pop(symbol, None)  # ambiguous across configurations: no claim
    clang_version = subprocess.run([args.clang, "--version"], capture_output=True, text=True).stdout.splitlines()[0]
    libc = subprocess.run(["ldd", "--version"], capture_output=True, text=True).stdout.splitlines()[0]
    lines = [
        "//! glibc prototypes derived from the platform headers (x86-64 LP64).",
        f"//! Generated by scripts/gen_libc_prototypes.py with {clang_version}; {libc}.",
        "//! Hand-written entries in abi_pass.rs take precedence; this table only",
        "//! fills symbols they do not name. Do not edit by hand.",
        "use crate::x86::types::XType::{self, *};",
        "use crate::x86::types::{LIBC_DIR_RECORD, LIBC_FILE_RECORD};",
        "",
        "/// (symbol, return type, fixed parameter types, variadic)",
        "#[rustfmt::skip]",
        "pub(super) const LIBC_PROTOTYPES: &[(&str, XType, &[XType], bool)] = &[",
    ]
    for symbol in sorted(table):
        ret, ps, variadic = table[symbol]
        lines.append(f'    ("{symbol}", {ret}, &[{", ".join(ps)}], {"true" if variadic else "false"}),')
    lines.append("];")
    Path(args.out).write_text("\n".join(lines) + "\n")
    print(f"{len(table)} prototypes ({len(conflicts)} ambiguous dropped) -> {args.out}")


if __name__ == "__main__":
    main()
