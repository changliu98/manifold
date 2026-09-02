// ABI pass: populates register conventions, known function signatures, and noreturn functions into DecompileDB.

use std::collections::BTreeSet;
use std::sync::Arc;

use crate::abi::LibcObject;
use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::x86::types::{Symbol, XType};

pub struct AbiPass;

impl IRPass for AbiPass {
    fn name(&self) -> &'static str {
        "abi"
    }

    fn run(&self, db: &mut DecompileDB) {
        populate_arg_ret_regs(db);
        populate_known_noreturn(db);
        populate_known_func_param_is_ptr(db);
        populate_known_func_returns(db);
        populate_hardcoded_signatures(db);
        populate_known_global_types(db);
        populate_known_func_param_pointee_size(db);
        populate_known_func_buffer_capacity(db);
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "is_arg_reg",
            "is_xmm_arg_reg",
            "is_float_arg_reg",
            "is_caller_saved",
            "is_callee_saved",
            "abi_int_arg_position",
            "abi_float_arg_position",
            "abi_shared_arg_slots",
            "abi_reg_args_per_function",
            "abi_first_stack_arg_position",
            "abi_outgoing_stack_base",
            "abi_incoming_sp_stack_base",
            "abi_incoming_bp_stack_base",
            "abi_stack_slot_size",
            "abi_pointer_size",
            "abi_ret_int_reg",
            "abi_ret_float_reg",
            "is_known_noreturn_function",
            "known_func_param_is_ptr",
            "known_func_returns_ptr",
            "known_func_returns_long",
            "known_extern_signature",
            "known_global_type",
            "known_varargs_function",
            "known_func_param_pointee_size",
            "known_func_param_byte_capacity",
            "known_func_param_element_capacity",
        ]
    }
}

/// Resolve raw direct call sites only after all architecture frontends have had
/// a chance to recover their PLT entries. AbiPass itself must stay before those
/// frontends because they consume its register/signature facts.
pub struct NoreturnSitePass;

impl IRPass for NoreturnSitePass {
    fn name(&self) -> &'static str {
        "noreturn-sites"
    }

    fn run(&self, db: &mut DecompileDB) {
        populate_known_noreturn_call_sites(db);
    }

    fn outputs(&self) -> &'static [&'static str] {
        &["known_noreturn_call_site"]
    }

    fn extra_reads(&self) -> &'static [&'static str] {
        &[
            "ddisasm_cfg_edge",
            "plt_entry",
            "plt_block",
            "symbol_resolved_addr",
        ]
    }
}

// Populate argument, return, and caller-saved register facts from the ABI config.
fn populate_arg_ret_regs(db: &mut DecompileDB) {
    let cfg = db.abi().clone();
    for (pos, reg) in cfg.int_arg_regs.iter().enumerate() {
        db.rel_push("is_arg_reg", (*reg,));
        db.rel_push("abi_int_arg_position", (*reg, pos));
    }
    for (pos, reg) in cfg.float_arg_regs.iter().enumerate() {
        db.rel_push("is_xmm_arg_reg", (*reg,));
        db.rel_push("is_float_arg_reg", (*reg,));
        db.rel_push("abi_float_arg_position", (*reg, pos));
    }
    for reg in &cfg.caller_saved {
        db.rel_push("is_caller_saved", (*reg,));
    }
    for reg in &cfg.callee_saved {
        db.rel_push("is_callee_saved", (*reg,));
    }
    if cfg.uses_shared_arg_slots() {
        db.rel_push("abi_shared_arg_slots", (true,));
    }
    // Windows x86-32: the register slots above belong to individual fastcall/thiscall functions, not to the image, whose default cdecl passes everything on the stack.
    if cfg.reg_args_are_per_function() {
        db.rel_push("abi_reg_args_per_function", (true,));
    }
    // The register a returned integer/pointer value arrives in. rtl_pass's return-value binding used to spell the x86 literal AX inline, which meant no non-x86 frontend could ever recover a return value.
    db.rel_push("abi_ret_int_reg", (cfg.ret_int_reg,));
    // Keep the FP return register distinct from the FP argument sequence.  In
    // particular, i386 cdecl returns through FP0 despite having no FP argument
    // registers at all.
    db.rel_push("abi_ret_float_reg", (cfg.ret_float_reg,));
    db.rel_push(
        "abi_first_stack_arg_position",
        (cfg.first_stack_arg_position(),),
    );
    db.rel_push("abi_outgoing_stack_base", (cfg.outgoing_stack_arg_base(),));
    db.rel_push(
        "abi_incoming_sp_stack_base",
        (cfg.incoming_sp_stack_arg_base(),),
    );
    db.rel_push(
        "abi_incoming_bp_stack_base",
        (cfg.incoming_bp_stack_arg_base(),),
    );
    db.rel_push("abi_stack_slot_size", (cfg.pointer_size as i64,));
    // sizeof(void*), kept distinct from the stack slot granularity above so a rule asking about pointer width says so.
    db.rel_push("abi_pointer_size", (cfg.pointer_size as i64,));
}

// Register the always-noreturn functions from abi's canonical exact-symbol
// sets; status-dependent error-family functions are decided at the call site.
fn populate_known_noreturn(db: &mut DecompileDB) {
    for name in crate::abi::always_noreturn_symbols() {
        db.rel_push("is_known_noreturn_function", (name as Symbol,));
    }
}

// Resolve unconditional direct calls to ABI-known noreturn targets from the raw
// CFG independently of canary trimming and before downstream CFG/dataflow
// consumers. Canary recovery removes the __stack_chk_fail statement, but the
// call's physical fallthrough is still infeasible.
fn populate_known_noreturn_call_sites(db: &mut DecompileDB) {
    let mut targets = BTreeSet::new();

    for &(addr, name) in db.rel_iter::<(u64, Symbol)>("plt_entry") {
        if crate::abi::is_always_noreturn(name) {
            targets.insert(addr);
        }
    }
    for &(addr, name) in db.rel_iter::<(u64, Symbol)>("plt_block") {
        if crate::abi::is_always_noreturn(name) {
            targets.insert(addr);
        }
    }
    for &(name, addr) in db.rel_iter::<(Symbol, u64)>("symbol_resolved_addr") {
        if crate::abi::is_always_noreturn(name) {
            targets.insert(addr);
        }
    }

    let sites: BTreeSet<_> = db
        .rel_iter::<(u64, u64, Symbol)>("ddisasm_cfg_edge")
        .filter(|(_, target, edge_type)| *edge_type == "call" && targets.contains(target))
        .map(|(site, _, _)| *site)
        .collect();
    for site in sites {
        db.rel_push("known_noreturn_call_site", (site,));
    }
}

// Register known pointer parameters for libc/coreutils/gnulib functions.
fn populate_known_func_param_is_ptr(db: &mut DecompileDB) {
    let entries: &[(Symbol, usize)] = &[
        ("strlen", 0),
        ("strcpy", 0),
        ("strcpy", 1),
        ("strcat", 0),
        ("strcat", 1),
        ("memset", 0),
        ("memcpy", 0),
        ("memcpy", 1),
        ("memmove", 0),
        ("memmove", 1),
        ("memchr", 0),
        ("memcmp", 0),
        ("memcmp", 1),
        ("strdup", 0),
        ("strndup", 0),
        ("strstr", 0),
        ("strstr", 1),
        ("strtol", 0),
        ("strtol", 1),
        ("strtoul", 0),
        ("strtoul", 1),
        // ABI-1: strerror(int) and malloc(size_t) take a SCALAR param 0; forcing it to pointer contradicted the signatures below and wrongly drove must_be_ptr/is_ptr/Xptr.
        ("free", 0),
        ("realloc", 0),
        ("reallocarray", 0),
        ("printf", 0),
        ("fprintf", 0),
        ("fprintf", 1),
        ("snprintf", 0),
        ("snprintf", 2),
        ("sprintf", 0),
        ("sprintf", 1),
        ("sscanf", 0),
        ("sscanf", 1),
        ("fopen", 0),
        ("fopen", 1),
        ("fclose", 0),
        ("fflush", 0),
        ("ferror", 0),
        ("feof", 0),
        ("fileno", 0),
        ("puts", 0),
        ("fputs", 0),
        ("fputs", 1),
        ("fputc", 1),
        ("fgets", 0),
        ("fgets", 2),
        ("fread", 0),
        ("fread", 3),
        ("fwrite", 0),
        ("fwrite", 3),
        ("fseek", 0),
        ("ftell", 0),
        ("__sprintf_chk", 0),
        ("__sprintf_chk", 3),
        ("__snprintf_chk", 0),
        ("__snprintf_chk", 4),
        ("__fprintf_chk", 0),
        ("__fprintf_chk", 2),
        ("__printf_chk", 1),
        ("__memcpy_chk", 0),
        ("__memcpy_chk", 1),
        ("__memmove_chk", 0),
        ("__memmove_chk", 1),
        ("__memset_chk", 0),
        ("__strcpy_chk", 0),
        ("__strcpy_chk", 1),
        ("__strcat_chk", 0),
        ("__strcat_chk", 1),
        ("strtok", 0),
        ("strtok", 1),
        ("getenv", 0),
        ("setenv", 0),
        ("setenv", 1),
        ("setlocale", 1),
        ("getopt_long", 1),
        ("getopt_long", 2),
        ("getopt_long", 3),
        ("getopt_long", 4),
        ("atexit", 0),
        ("signal", 1),
        ("opendir", 0),
        ("closedir", 0),
        ("readdir", 0),
        ("access", 0),
        ("chmod", 0),
        ("chown", 0),
        ("readlink", 0),
        ("readlink", 1),
        ("readlinkat", 1),
        ("readlinkat", 2),
        ("stat", 0),
        ("stat", 1),
        ("lstat", 0),
        ("lstat", 1),
        ("fstatat", 1),
        ("fstatat", 2),
        ("localtime", 0),
        ("localtime_r", 0),
        ("localtime_r", 1),
        ("localtime_rz", 0),
        ("localtime_rz", 1),
        ("localtime_rz", 2),
        ("strftime", 0),
        ("strftime", 2),
        ("strftime", 3),
        ("nstrftime", 0),
        ("nstrftime", 2),
        ("nstrftime", 3),
        ("time", 0),
        ("umaxtostr", 1),
        ("imaxtostr", 1),
        ("offtostr", 1),
        ("uinttostr", 1),
        ("timetostr", 1),
        ("human_readable", 1),
        ("quotearg_style", 1),
        ("quotearg_buffer", 0),
        ("quotearg_buffer", 2),
        ("quote", 0),
        // ABI-1: getpwuid(uid_t) and getgrgid(gid_t) take a SCALAR ID param 0; forcing it to pointer wrongly drove must_be_ptr/is_ptr/Xptr.
        ("error", 2),
        ("__errno_location", 0),
        ("dcgettext", 0),
        ("dcgettext", 1),
    ];
    for &(name, idx) in entries {
        db.rel_push("known_func_param_is_ptr", (name, idx));
    }
}

// Register known return types (ptr, long, int) for libc/coreutils functions.
fn populate_known_func_returns(db: &mut DecompileDB) {
    let returns_ptr: &[Symbol] = &[
        "malloc",
        "calloc",
        "realloc",
        "reallocarray",
        "strdup",
        "strndup",
        "strcpy",
        "strcat",
        "memcpy",
        "memset",
        "memmove",
        "memchr",
        "fopen",
        "getenv",
        "strchr",
        "strrchr",
        "strstr",
        "strtok",
        "realpath",
        "getcwd",
        "readdir",
        "opendir",
        "strerror",
        "setlocale",
        "localtime",
        "localtime_r",
        "getpwuid",
        "getgrgid",
        "__errno_location",
        "signal",
        "dcgettext",
        "fdopen",
        "freopen",
        "fdopendir",
        "mempcpy",
        "rawmemchr",
        "memrchr",
        "stpcpy",
        "textdomain",
        "bindtextdomain",
        "nl_langinfo",
        "dcngettext",
        "localeconv",
        "newlocale",
        "__ctype_b_loc",
        "__ctype_toupper_loc",
        "__ctype_tolower_loc",
        "canonicalize_file_name",
        "getpwnam",
        "getgrnam",
        "gmtime_r",
        "aligned_alloc",
        "xmalloc",
        "ximalloc",
        "xrealloc",
        "xirealloc",
        "xcalloc",
        "xicalloc",
        "xzalloc",
        "xizalloc",
        "xstrdup",
        "xstrndup",
        "xmemdup",
        "ximemdup",
        "ximemdup0",
        "xcharalloc",
        "xreallocarray",
        "xireallocarray",
        "xnmalloc",
        "xinmalloc",
        "xnrealloc",
        "x2realloc",
        "x2nrealloc",
        "xpalloc",
        "imalloc",
        "irealloc",
        "icalloc",
        "ireallocarray",
        "tzalloc",
        "umaxtostr",
        "imaxtostr",
        "offtostr",
        "uinttostr",
        "timetostr",
        "localtime_rz",
        "human_readable",
        "quotearg_style",
        "quote",
        // gnulib author-name helpers return const char *; without the returns-ptr fact the result defaults to int and gets read-cast (int), truncating the pointer.
        "proper_name",
        "proper_name_lite",
        "proper_name_utf8",
    ];
    for name in returns_ptr {
        db.rel_push("known_func_returns_ptr", (*name,));
    }

    let returns_long: &[Symbol] = &[
        "strlen",
        "ftell",
        "fread",
        "fwrite",
        "lseek",
        "read",
        "write",
        "readlink",
        "readlinkat",
        "strftime",
        "nstrftime",
        "quotearg_buffer",
        "__getdelim",
        "pathconf",
        "clock",
        "strtoimax",
    ];
    for name in returns_long {
        db.rel_push("known_func_returns_long", (*name,));
    }
}

// Register full extern signatures (param count, return type, param types) for known functions.
fn populate_hardcoded_signatures(db: &mut DecompileDB) {
    use XType::*;

    let signatures: &[(&str, usize, XType, &[XType])] = &[
        ("memset", 3, Xptr, &[Xptr, Xint, Xany64]),
        ("memcpy", 3, Xptr, &[Xptr, Xptr, Xany64]),
        ("memmove", 3, Xptr, &[Xptr, Xptr, Xany64]),
        ("memcmp", 3, Xint, &[Xptr, Xptr, Xany64]),
        ("strlen", 1, Xany64, &[Xcharptr]),
        ("strcpy", 2, Xcharptr, &[Xcharptr, Xcharptr]),
        ("strncpy", 3, Xcharptr, &[Xcharptr, Xcharptr, Xany64]),
        ("strcmp", 2, Xint, &[Xcharptr, Xcharptr]),
        ("strncmp", 3, Xint, &[Xcharptr, Xcharptr, Xany64]),
        ("strchr", 2, Xcharptr, &[Xcharptr, Xint]),
        ("strrchr", 2, Xcharptr, &[Xcharptr, Xint]),
        ("strcat", 2, Xcharptr, &[Xcharptr, Xcharptr]),
        ("strncat", 3, Xcharptr, &[Xcharptr, Xcharptr, Xany64]),
        ("strdup", 1, Xcharptr, &[Xcharptr]),
        ("strndup", 2, Xcharptr, &[Xcharptr, Xany64]),
        ("strstr", 2, Xcharptr, &[Xcharptr, Xcharptr]),
        ("strtol", 3, Xlong, &[Xcharptr, Xptr, Xint]),
        ("strtoul", 3, Xlongunsigned, &[Xcharptr, Xptr, Xint]),
        ("strerror", 1, Xcharptr, &[Xint]),
        ("printf", 1, Xint, &[Xcharptr]),
        ("fprintf", 2, Xint, &[Xptr, Xcharptr]),
        ("snprintf", 3, Xint, &[Xcharptr, Xany64, Xcharptr]),
        ("sprintf", 2, Xint, &[Xcharptr, Xcharptr]),
        ("puts", 1, Xint, &[Xcharptr]),
        ("fputs", 2, Xint, &[Xcharptr, Xptr]),
        ("fputc", 2, Xint, &[Xint, Xptr]),
        ("putchar", 1, Xint, &[Xint]),
        ("fwrite", 4, Xany64, &[Xptr, Xany64, Xany64, Xptr]),
        ("fread", 4, Xany64, &[Xptr, Xany64, Xany64, Xptr]),
        ("fopen", 2, Xptr, &[Xcharptr, Xcharptr]),
        ("fclose", 1, Xint, &[Xptr]),
        ("fflush", 1, Xint, &[Xptr]),
        ("ferror", 1, Xint, &[Xptr]),
        ("feof", 1, Xint, &[Xptr]),
        ("fileno", 1, Xint, &[Xptr]),
        (
            "__sprintf_chk",
            4,
            Xint,
            &[Xcharptr, Xint, Xany64, Xcharptr],
        ),
        (
            "__snprintf_chk",
            5,
            Xint,
            &[Xcharptr, Xany64, Xint, Xany64, Xcharptr],
        ),
        ("__fprintf_chk", 3, Xint, &[Xptr, Xint, Xcharptr]),
        ("__printf_chk", 2, Xint, &[Xint, Xcharptr]),
        ("__memcpy_chk", 4, Xptr, &[Xptr, Xptr, Xany64, Xany64]),
        ("__memmove_chk", 4, Xptr, &[Xptr, Xptr, Xany64, Xany64]),
        ("__memset_chk", 4, Xptr, &[Xptr, Xint, Xany64, Xany64]),
        ("__strcpy_chk", 3, Xcharptr, &[Xcharptr, Xcharptr, Xany64]),
        ("__strcat_chk", 3, Xcharptr, &[Xcharptr, Xcharptr, Xany64]),
        ("malloc", 1, Xptr, &[Xany64]),
        ("calloc", 2, Xptr, &[Xany64, Xany64]),
        ("realloc", 2, Xptr, &[Xptr, Xany64]),
        ("free", 1, Xvoid, &[Xptr]),
        ("reallocarray", 3, Xptr, &[Xptr, Xany64, Xany64]),
        ("alloca", 1, Xptr, &[Xany64]),
        ("exit", 1, Xvoid, &[Xint]),
        ("abort", 0, Xvoid, &[]),
        ("getenv", 1, Xcharptr, &[Xcharptr]),
        ("setenv", 3, Xint, &[Xcharptr, Xcharptr, Xint]),
        ("setlocale", 2, Xcharptr, &[Xint, Xcharptr]),
        (
            "getopt_long",
            5,
            Xint,
            &[Xint, Xcharptr, Xcharptr, Xptr, Xptr],
        ),
        ("atexit", 1, Xint, &[Xptr]),
        ("signal", 2, Xptr, &[Xint, Xptr]),
        ("raise", 1, Xint, &[Xint]),
        ("open", 2, Xint, &[Xcharptr, Xint]),
        ("close", 1, Xint, &[Xint]),
        ("read", 3, Xlong, &[Xint, Xptr, Xany64]),
        ("write", 3, Xlong, &[Xint, Xptr, Xany64]),
        ("lseek", 3, Xlong, &[Xint, Xlong, Xint]),
        ("stat", 2, Xint, &[Xcharptr, Xptr]),
        ("fstat", 2, Xint, &[Xint, Xptr]),
        ("lstat", 2, Xint, &[Xcharptr, Xptr]),
        ("fstatat", 4, Xint, &[Xint, Xcharptr, Xptr, Xint]),
        ("readlink", 3, Xlong, &[Xcharptr, Xcharptr, Xany64]),
        ("readlinkat", 4, Xlong, &[Xint, Xcharptr, Xcharptr, Xany64]),
        ("opendir", 1, Xptr, &[Xcharptr]),
        ("closedir", 1, Xint, &[Xptr]),
        ("readdir", 1, Xptr, &[Xptr]),
        ("access", 2, Xint, &[Xcharptr, Xint]),
        // mode_t/uid_t/gid_t are unsigned 32-bit in the libc prototypes.
        ("chmod", 2, Xint, &[Xcharptr, Xintunsigned]),
        ("chown", 3, Xint, &[Xcharptr, Xintunsigned, Xintunsigned]),
        ("isatty", 1, Xint, &[Xint]),
        ("time", 1, Xlong, &[Xptr]),
        ("localtime", 1, Xptr, &[Xptr]),
        ("localtime_r", 2, Xptr, &[Xptr, Xptr]),
        ("localtime_rz", 3, Xptr, &[Xptr, Xptr, Xptr]),
        ("strftime", 4, Xany64, &[Xptr, Xany64, Xptr, Xptr]),
        (
            "nstrftime",
            6,
            Xany64,
            &[Xptr, Xany64, Xptr, Xptr, Xint, Xint],
        ),
        (
            "human_readable",
            5,
            Xcharptr,
            &[Xany64, Xcharptr, Xint, Xany64, Xany64],
        ),
        ("umaxtostr", 2, Xcharptr, &[Xany64, Xcharptr]),
        ("imaxtostr", 2, Xcharptr, &[Xlong, Xcharptr]),
        ("offtostr", 2, Xcharptr, &[Xlong, Xcharptr]),
        ("uinttostr", 2, Xcharptr, &[Xany64, Xcharptr]),
        ("timetostr", 2, Xcharptr, &[Xlong, Xcharptr]),
        ("quotearg_style", 2, Xcharptr, &[Xint, Xcharptr]),
        (
            "quotearg_buffer",
            5,
            Xany64,
            &[Xcharptr, Xany64, Xcharptr, Xany64, Xptr],
        ),
        ("quote", 1, Xcharptr, &[Xcharptr]),
        // uid_t/gid_t are unsigned 32-bit; signed Xint here mis-signed comparisons and %u formatting.
        ("getpwuid", 1, Xptr, &[Xintunsigned]),
        ("getgrgid", 1, Xptr, &[Xintunsigned]),
        ("getuid", 0, Xint, &[]),
        ("getgid", 0, Xint, &[]),
        ("geteuid", 0, Xint, &[]),
        ("getegid", 0, Xint, &[]),
        ("error", 3, Xvoid, &[Xint, Xint, Xcharptr]),
        ("__errno_location", 0, Xptr, &[]),
        ("dcgettext", 3, Xcharptr, &[Xcharptr, Xcharptr, Xint]),
        (
            "__libc_start_main",
            6,
            Xint,
            &[Xptr, Xint, Xptr, Xptr, Xptr, Xptr],
        ),
        ("__cxa_finalize", 1, Xvoid, &[Xptr]),
        ("__stack_chk_fail", 0, Xvoid, &[]),
        ("__cxa_atexit", 3, Xint, &[Xptr, Xptr, Xptr]),
        ("__ctype_get_mb_cur_max", 0, Xany64, &[]),
        ("__ctype_b_loc", 0, Xptr, &[]),
        ("__ctype_toupper_loc", 0, Xptr, &[]),
        ("__ctype_tolower_loc", 0, Xptr, &[]),
        ("__fpending", 1, Xany64, &[Xptr]),
        ("__freading", 1, Xint, &[Xptr]),
        ("__fpurge", 1, Xvoid, &[Xptr]),
        ("__overflow", 2, Xint, &[Xptr, Xint]),
        ("__uflow", 1, Xint, &[Xptr]),
        (
            "__assert_fail",
            4,
            Xvoid,
            &[Xcharptr, Xcharptr, Xintunsigned, Xcharptr],
        ),
        ("__getdelim", 4, Xlong, &[Xptr, Xptr, Xint, Xptr]),
        ("_exit", 1, Xvoid, &[Xint]),
        ("textdomain", 1, Xcharptr, &[Xcharptr]),
        ("bindtextdomain", 2, Xcharptr, &[Xcharptr, Xcharptr]),
        ("nl_langinfo", 1, Xcharptr, &[Xint]),
        (
            "dcngettext",
            5,
            Xcharptr,
            &[Xcharptr, Xcharptr, Xcharptr, Xlongunsigned, Xint],
        ),
        ("localeconv", 0, Xptr, &[]),
        ("newlocale", 3, Xptr, &[Xint, Xcharptr, Xptr]),
        ("mbsinit", 1, Xint, &[Xptr]),
        ("mbrtoc32", 4, Xany64, &[Xptr, Xcharptr, Xany64, Xptr]),
        ("iswprint", 1, Xint, &[Xint]),
        ("iswcntrl", 1, Xint, &[Xint]),
        ("wcwidth", 1, Xint, &[Xint]),
        ("fputs_unlocked", 2, Xint, &[Xcharptr, Xptr]),
        ("fputc_unlocked", 2, Xint, &[Xint, Xptr]),
        ("fwrite_unlocked", 4, Xany64, &[Xptr, Xany64, Xany64, Xptr]),
        ("fread_unlocked", 4, Xany64, &[Xptr, Xany64, Xany64, Xptr]),
        ("fflush_unlocked", 1, Xint, &[Xptr]),
        ("clearerr_unlocked", 1, Xvoid, &[Xptr]),
        ("fseeko", 3, Xint, &[Xptr, Xlong, Xint]),
        ("fdopen", 2, Xptr, &[Xint, Xcharptr]),
        ("freopen", 3, Xptr, &[Xcharptr, Xcharptr, Xptr]),
        ("setvbuf", 4, Xint, &[Xptr, Xcharptr, Xint, Xany64]),
        ("strtoumax", 3, Xlongunsigned, &[Xcharptr, Xptr, Xint]),
        ("strtoimax", 3, Xlong, &[Xcharptr, Xptr, Xint]),
        ("strspn", 2, Xany64, &[Xcharptr, Xcharptr]),
        ("strcspn", 2, Xany64, &[Xcharptr, Xcharptr]),
        ("strcoll", 2, Xint, &[Xcharptr, Xcharptr]),
        ("stpcpy", 2, Xcharptr, &[Xcharptr, Xcharptr]),
        ("strnlen", 2, Xany64, &[Xcharptr, Xany64]),
        ("mempcpy", 3, Xptr, &[Xptr, Xptr, Xany64]),
        ("rawmemchr", 2, Xptr, &[Xptr, Xint]),
        ("memrchr", 3, Xptr, &[Xptr, Xint, Xany64]),
        ("fcntl", 2, Xint, &[Xint, Xint]),
        ("ioctl", 2, Xint, &[Xint, Xlongunsigned]),
        ("openat", 3, Xint, &[Xint, Xcharptr, Xint]),
        ("posix_fadvise", 4, Xint, &[Xint, Xlong, Xlong, Xint]),
        ("dup2", 2, Xint, &[Xint, Xint]),
        ("ftruncate", 2, Xint, &[Xint, Xlong]),
        ("fchdir", 1, Xint, &[Xint]),
        ("chdir", 1, Xint, &[Xcharptr]),
        ("getcwd", 2, Xcharptr, &[Xcharptr, Xany64]),
        ("dirfd", 1, Xint, &[Xptr]),
        ("fdopendir", 1, Xptr, &[Xint]),
        ("faccessat", 4, Xint, &[Xint, Xcharptr, Xint, Xint]),
        ("unlink", 1, Xint, &[Xcharptr]),
        ("unlinkat", 3, Xint, &[Xint, Xcharptr, Xint]),
        ("mkdir", 2, Xint, &[Xcharptr, Xintunsigned]),
        ("renameat", 4, Xint, &[Xint, Xcharptr, Xint, Xcharptr]),
        (
            "renameat2",
            5,
            Xint,
            &[Xint, Xcharptr, Xint, Xcharptr, Xintunsigned],
        ),
        ("linkat", 5, Xint, &[Xint, Xcharptr, Xint, Xcharptr, Xint]),
        ("fchown", 3, Xint, &[Xint, Xintunsigned, Xintunsigned]),
        (
            "fchownat",
            5,
            Xint,
            &[Xint, Xcharptr, Xintunsigned, Xintunsigned, Xint],
        ),
        ("pathconf", 2, Xlong, &[Xcharptr, Xint]),
        ("canonicalize_file_name", 1, Xcharptr, &[Xcharptr]),
        ("sigaction", 3, Xint, &[Xint, Xptr, Xptr]),
        ("sigprocmask", 3, Xint, &[Xint, Xptr, Xptr]),
        ("sigemptyset", 1, Xint, &[Xptr]),
        ("sigaddset", 2, Xint, &[Xptr, Xint]),
        ("sigismember", 2, Xint, &[Xptr, Xint]),
        ("kill", 2, Xint, &[Xint, Xint]),
        ("fork", 0, Xint, &[]),
        ("execvp", 2, Xint, &[Xcharptr, Xptr]),
        ("waitpid", 3, Xint, &[Xint, Xptr, Xint]),
        ("unsetenv", 1, Xint, &[Xcharptr]),
        ("aligned_alloc", 2, Xptr, &[Xany64, Xany64]),
        ("clock_gettime", 2, Xint, &[Xint, Xptr]),
        ("gettimeofday", 2, Xint, &[Xptr, Xptr]),
        ("gmtime_r", 2, Xptr, &[Xptr, Xptr]),
        ("clock", 0, Xlong, &[]),
        ("uname", 1, Xint, &[Xptr]),
        ("getpagesize", 0, Xint, &[]),
        ("umask", 1, Xint, &[Xintunsigned]),
        ("getpwnam", 1, Xptr, &[Xcharptr]),
        ("getgrnam", 1, Xptr, &[Xcharptr]),
        ("endpwent", 0, Xvoid, &[]),
        ("endgrent", 0, Xvoid, &[]),
        ("qsort", 4, Xvoid, &[Xptr, Xany64, Xany64, Xptr]),
        ("fnmatch", 3, Xint, &[Xcharptr, Xcharptr, Xint]),
        ("rpmatch", 1, Xint, &[Xcharptr]),
        ("strtok_r", 3, Xcharptr, &[Xcharptr, Xcharptr, Xptr]),
        ("gettext", 1, Xcharptr, &[Xcharptr]),
        (
            "ngettext",
            3,
            Xcharptr,
            &[Xcharptr, Xcharptr, Xlongunsigned],
        ),
        ("dgettext", 2, Xcharptr, &[Xcharptr, Xcharptr]),
        ("quotearg_n_style", 3, Xcharptr, &[Xint, Xint, Xcharptr]),
        ("quote_n", 2, Xcharptr, &[Xint, Xcharptr]),
        ("canonicalize_filename_mode", 2, Xcharptr, &[Xcharptr, Xint]),
        ("mmap", 6, Xptr, &[Xptr, Xany64, Xint, Xint, Xint, Xlong]),
        ("memchr", 3, Xptr, &[Xptr, Xint, Xany64]),
        ("atoi", 1, Xint, &[Xcharptr]),
        ("atol", 1, Xlong, &[Xcharptr]),
        ("getopt", 3, Xint, &[Xint, Xcharptr, Xcharptr]),
        ("putenv", 1, Xint, &[Xcharptr]),
        ("rmdir", 1, Xint, &[Xcharptr]),
        ("remove", 1, Xint, &[Xcharptr]),
        ("rename", 2, Xint, &[Xcharptr, Xcharptr]),
        ("dup", 1, Xint, &[Xint]),
        ("pipe", 1, Xint, &[Xptr]),
        ("fseek", 3, Xint, &[Xptr, Xlong, Xint]),
        ("fgetc", 1, Xint, &[Xptr]),
        ("getc", 1, Xint, &[Xptr]),
        ("getchar", 0, Xint, &[]),
        ("toupper", 1, Xint, &[Xint]),
        ("tolower", 1, Xint, &[Xint]),
        ("isspace", 1, Xint, &[Xint]),
        ("isdigit", 1, Xint, &[Xint]),
        ("isalpha", 1, Xint, &[Xint]),
        ("isalnum", 1, Xint, &[Xint]),
        ("mbstowcs", 3, Xany64, &[Xptr, Xcharptr, Xany64]),
        ("ftell", 1, Xlong, &[Xptr]),
        ("sysconf", 1, Xlong, &[Xint]),
        ("munmap", 2, Xint, &[Xptr, Xany64]),
        ("sscanf", 2, Xint, &[Xcharptr, Xcharptr]),
        // <math.h> (mirrors header_functions.json); Xfloat == C double, and the true fixed arity clamps call sites whose argument count was over-recovered.
        ("pow", 2, Xfloat, &[Xfloat, Xfloat]),
        ("fmod", 2, Xfloat, &[Xfloat, Xfloat]),
        ("atan2", 2, Xfloat, &[Xfloat, Xfloat]),
        ("sqrt", 1, Xfloat, &[Xfloat]),
        ("sin", 1, Xfloat, &[Xfloat]),
        ("cos", 1, Xfloat, &[Xfloat]),
        ("tan", 1, Xfloat, &[Xfloat]),
        ("asin", 1, Xfloat, &[Xfloat]),
        ("acos", 1, Xfloat, &[Xfloat]),
        ("atan", 1, Xfloat, &[Xfloat]),
        ("sinh", 1, Xfloat, &[Xfloat]),
        ("cosh", 1, Xfloat, &[Xfloat]),
        ("tanh", 1, Xfloat, &[Xfloat]),
        ("exp", 1, Xfloat, &[Xfloat]),
        ("log", 1, Xfloat, &[Xfloat]),
        ("log10", 1, Xfloat, &[Xfloat]),
        ("fabs", 1, Xfloat, &[Xfloat]),
        ("ceil", 1, Xfloat, &[Xfloat]),
        ("floor", 1, Xfloat, &[Xfloat]),
        ("round", 1, Xfloat, &[Xfloat]),
        // `f` (float) variants -- Xsingle == C float for ret/args.
        ("powf", 2, Xsingle, &[Xsingle, Xsingle]),
        ("fmodf", 2, Xsingle, &[Xsingle, Xsingle]),
        ("atan2f", 2, Xsingle, &[Xsingle, Xsingle]),
        ("sqrtf", 1, Xsingle, &[Xsingle]),
        ("sinf", 1, Xsingle, &[Xsingle]),
        ("cosf", 1, Xsingle, &[Xsingle]),
        ("tanf", 1, Xsingle, &[Xsingle]),
        ("asinf", 1, Xsingle, &[Xsingle]),
        ("acosf", 1, Xsingle, &[Xsingle]),
        ("atanf", 1, Xsingle, &[Xsingle]),
        ("sinhf", 1, Xsingle, &[Xsingle]),
        ("coshf", 1, Xsingle, &[Xsingle]),
        ("tanhf", 1, Xsingle, &[Xsingle]),
        ("expf", 1, Xsingle, &[Xsingle]),
        ("logf", 1, Xsingle, &[Xsingle]),
        ("log10f", 1, Xsingle, &[Xsingle]),
        ("fabsf", 1, Xsingle, &[Xsingle]),
        ("ceilf", 1, Xsingle, &[Xsingle]),
        ("floorf", 1, Xsingle, &[Xsingle]),
        ("roundf", 1, Xsingle, &[Xsingle]),
        // Long-double (l) variants; the prototype is header-suppressed, so the Xfloat shape only feeds arity normalization and float-typed args.
        ("powl", 2, Xfloat, &[Xfloat, Xfloat]),
        ("fmodl", 2, Xfloat, &[Xfloat, Xfloat]),
        ("atan2l", 2, Xfloat, &[Xfloat, Xfloat]),
        ("sqrtl", 1, Xfloat, &[Xfloat]),
        ("sinl", 1, Xfloat, &[Xfloat]),
        ("cosl", 1, Xfloat, &[Xfloat]),
        ("tanl", 1, Xfloat, &[Xfloat]),
        ("asinl", 1, Xfloat, &[Xfloat]),
        ("acosl", 1, Xfloat, &[Xfloat]),
        ("atanl", 1, Xfloat, &[Xfloat]),
        ("sinhl", 1, Xfloat, &[Xfloat]),
        ("coshl", 1, Xfloat, &[Xfloat]),
        ("tanhl", 1, Xfloat, &[Xfloat]),
        ("expl", 1, Xfloat, &[Xfloat]),
        ("logl", 1, Xfloat, &[Xfloat]),
        ("log10l", 1, Xfloat, &[Xfloat]),
        ("fabsl", 1, Xfloat, &[Xfloat]),
        ("ceill", 1, Xfloat, &[Xfloat]),
        ("floorl", 1, Xfloat, &[Xfloat]),
        ("roundl", 1, Xfloat, &[Xfloat]),
    ];

    for &(name, param_count, ret_type, param_types) in signatures {
        db.rel_push(
            "known_extern_signature",
            (name, param_count, ret_type, Arc::new(param_types.to_vec())),
        );
    }

    // Known variadic functions: (name, declared_param_count)
    let varargs: &[(&str, usize)] = &[
        ("printf", 1),
        ("fprintf", 2),
        ("sprintf", 2),
        ("snprintf", 3),
        ("scanf", 1),
        ("fscanf", 2),
        ("sscanf", 2),
        ("__printf_chk", 2),
        ("__fprintf_chk", 3),
        ("__sprintf_chk", 4),
        ("__snprintf_chk", 5),
        ("error", 3),
        ("error_at_line", 5),
        ("dprintf", 2),
        ("syslog", 2),
        ("open", 2),
        ("openat", 3),
        ("fcntl", 2),
        ("ioctl", 2),
        ("execl", 2),
        ("execlp", 2),
        ("execle", 2),
    ];
    for &(name, fixed_args) in varargs {
        db.rel_push("known_varargs_function", (name, fixed_args));
    }
}

// Which parameter of which external function points at a fixed-layout object,
// and which object it is.  An external callee has no body to project, so
// nothing in the binary reveals how much it writes through the pointer; without
// this the object is sized from the field or two the caller happens to read
// back and the callee runs off the end of the caller's declaration.
//
// The table names the OBJECT rather than a byte count, because only half of
// this knowledge is target-independent.  Which parameter `lstat` fills is a
// property of the libc interface and is the same everywhere; how many bytes
// that fills is a property of the target, and LibcLayout answers it.  Getting
// the size wrong in either direction costs something: under-sizing is the stack
// smash, and over-sizing is not the free margin it looks like, because both
// consumers of escaped_stack_region_extent take the MAX over the rows for a
// base (clight_pass.rs, from_relations.rs), so an oversized extent overrides
// the frame-clamped one and swallows the caller's neighbouring locals into the
// recovered struct.
fn populate_known_func_param_pointee_size(db: &mut DecompileDB) {
    // No glibc behind this image, no glibc layouts to assert.
    let Some(layout) = db.abi().libc_layout() else {
        return;
    };
    let entries: &[(Symbol, usize, LibcObject)] = &[
        ("stat", 1, LibcObject::Stat),
        ("lstat", 1, LibcObject::Stat),
        ("fstat", 1, LibcObject::Stat),
        ("fstatat", 2, LibcObject::Stat),
        ("statvfs", 1, LibcObject::Statvfs),
        ("fstatvfs", 1, LibcObject::Statvfs),
        ("statfs", 1, LibcObject::Statfs),
        ("fstatfs", 1, LibcObject::Statfs),
        ("localtime_r", 1, LibcObject::Tm), // localtime_r(const time_t*, struct tm*)
        ("localtime_rz", 2, LibcObject::Tm), // localtime_rz(timezone_t, const time_t*, struct tm*)
        ("gmtime_r", 1, LibcObject::Tm),    // gmtime_r(const time_t*, struct tm*)
        ("uname", 0, LibcObject::Utsname),
        ("gettimeofday", 0, LibcObject::Timeval),
        ("clock_gettime", 1, LibcObject::Timeval),
        ("nanosleep", 1, LibcObject::Timeval), // remaining-time out-parameter
        ("getrusage", 1, LibcObject::Rusage),
        ("times", 0, LibcObject::Tms),
        ("getrlimit", 1, LibcObject::Rlimit),
        ("sigemptyset", 0, LibcObject::Sigset),
        ("sigfillset", 0, LibcObject::Sigset),
        ("sigaddset", 0, LibcObject::Sigset),
        ("sigdelset", 0, LibcObject::Sigset),
        ("sigprocmask", 2, LibcObject::Sigset), // old-mask out-parameter
        ("sigaction", 2, LibcObject::Sigaction), // previous-action out-parameter
        ("tcgetattr", 1, LibcObject::Termios),
        ("pipe", 0, LibcObject::Pointer), // int[2]
        // The strto* end pointer is pointer-sized, but a 4-byte int slot is the
        // default when nothing writes it directly, so on a 64-bit target the
        // store still overruns.
        ("strtol", 1, LibcObject::Pointer),
        ("strtoul", 1, LibcObject::Pointer),
        ("strtoll", 1, LibcObject::Pointer),
        ("strtoull", 1, LibcObject::Pointer),
        ("strtoimax", 1, LibcObject::Pointer),
        ("strtoumax", 1, LibcObject::Pointer),
        ("strtod", 1, LibcObject::Pointer),
        ("strtof", 1, LibcObject::Pointer),
        ("strtold", 1, LibcObject::Pointer),
        // POSIX line readers update both caller-owned scalar objects: the
        // buffer pointer itself and its allocated size.  These are pointer-
        // sized writes, independent of how much character storage is allocated.
        ("getline", 0, LibcObject::Pointer),
        ("getline", 1, LibcObject::Pointer),
        ("getdelim", 0, LibcObject::Pointer),
        ("getdelim", 1, LibcObject::Pointer),
        ("__getdelim", 0, LibcObject::Pointer),
        ("__getdelim", 1, LibcObject::Pointer),
        // libselinux pointer out-parameters.  Each writes one `char *` into
        // caller storage; without the pointer-sized extent a default 4-byte
        // local is overwritten on LP64 targets.
        ("selabel_lookup", 1, LibcObject::Pointer),
        ("selabel_lookup_raw", 1, LibcObject::Pointer),
        ("getcon", 0, LibcObject::Pointer),
        ("getcon_raw", 0, LibcObject::Pointer),
        ("getfscreatecon", 0, LibcObject::Pointer),
        ("getfscreatecon_raw", 0, LibcObject::Pointer),
        ("getfilecon", 1, LibcObject::Pointer),
        ("getfilecon_raw", 1, LibcObject::Pointer),
        ("lgetfilecon", 1, LibcObject::Pointer),
        ("lgetfilecon_raw", 1, LibcObject::Pointer),
        ("fgetfilecon", 1, LibcObject::Pointer),
        ("fgetfilecon_raw", 1, LibcObject::Pointer),
        ("security_compute_create", 3, LibcObject::Pointer),
        ("security_compute_create_raw", 3, LibcObject::Pointer),
    ];
    for &(name, idx, obj) in entries {
        db.rel_push(
            "known_func_param_pointee_size",
            (name, idx, layout.size_of(obj)),
        );
    }
}

/// Parameters whose accessible byte extent is carried by another argument.
///
/// Unlike `known_func_param_pointee_size`, these are interface contracts rather
/// than target-specific libc layouts.  The RTL consumer still requires the
/// capacity arguments to be exact positive constants before allocating C
/// backing storage.  Element-capacity rows keep `fread`/`fwrite`'s checked
/// `size * nmemb` semantics explicit instead of pretending either argument is
/// independently a byte count.
fn populate_known_func_buffer_capacity(db: &mut DecompileDB) {
    let byte_capacities: &[(Symbol, usize, usize)] = &[
        ("read", 1, 2),
        ("write", 1, 2),
        ("pread", 1, 2),
        ("pread64", 1, 2),
        ("pwrite", 1, 2),
        ("pwrite64", 1, 2),
        ("recv", 1, 2),
        ("send", 1, 2),
        ("getrandom", 0, 1),
        ("readlink", 1, 2),
        ("readlinkat", 2, 3),
        // POSIX and GNU variants share the same writable buffer/count
        // parameters; only their return type differs.
        ("strerror_r", 1, 2),
        ("memcpy", 0, 2),
        ("memcpy", 1, 2),
        ("memmove", 0, 2),
        ("memmove", 1, 2),
        ("memcmp", 0, 2),
        ("memcmp", 1, 2),
        ("memset", 0, 2),
        ("__memcpy_chk", 0, 2),
        ("__memcpy_chk", 1, 2),
    ];
    for &fact in byte_capacities {
        db.rel_push("known_func_param_byte_capacity", fact);
    }

    let element_capacities: &[(Symbol, usize, usize, usize)] = &[
        ("fread", 0, 1, 2),
        ("fread_unlocked", 0, 1, 2),
        ("fwrite", 0, 1, 2),
        ("fwrite_unlocked", 0, 1, 2),
    ];
    for &fact in element_capacities {
        db.rel_push("known_func_param_element_capacity", fact);
    }
}

// Register known types for well-known global variables (stdout, optarg, etc.).
fn populate_known_global_types(db: &mut DecompileDB) {
    use XType::*;

    // REMOVED only Version, a GENERIC identifier that force-typed unrelated program types to char*; program_name and exit_failure are KEPT as specific gnulib names whose recovered evidence is too weak.
    let known_globals: &[(&str, XType)] = &[
        ("stdout", Xptr),
        ("stderr", Xptr),
        ("stdin", Xptr),
        ("optarg", Xcharptr),
        ("optind", Xint),
        ("opterr", Xint),
        ("optopt", Xint),
        ("exit_failure", Xint),
        ("program_name", Xcharptr),
        ("program_invocation_name", Xcharptr),
        ("program_invocation_short_name", Xcharptr),
        ("errno", Xint),
    ];

    for &(name, ref xtype) in known_globals {
        db.rel_push("known_global_type", (name, xtype.clone()));
    }
}

#[cfg(test)]
mod tests {
    use super::{populate_known_noreturn_call_sites, AbiPass, NoreturnSitePass};
    use crate::decompile::elevator::DecompileDB;
    use crate::decompile::passes::pass::IRPass;
    use crate::x86::types::Symbol;
    use std::collections::BTreeSet;

    #[test]
    fn publishes_configured_integer_and_float_return_registers() {
        let mut db = DecompileDB::default();
        // i386 is the important non-derivable case: it has no FP argument
        // registers, yet returns floating values through FP0.
        db.target_abi = Some(crate::abi::AbiConfig::cdecl_x86_32());
        let expected_int = db.abi().ret_int_reg;
        let expected_float = db.abi().ret_float_reg;

        AbiPass.run(&mut db);

        assert!(db
            .rel_iter::<(crate::mreg::Mreg,)>("abi_ret_int_reg")
            .any(|row| row == &(expected_int,)));
        assert!(db
            .rel_iter::<(crate::mreg::Mreg,)>("abi_ret_float_reg")
            .any(|row| row == &(expected_float,)));
        assert!(AbiPass.outputs().contains(&"abi_ret_float_reg"));
    }

    #[test]
    fn raw_known_noreturn_calls_are_classified_before_trimming() {
        let mut db = DecompileDB::default();
        db.rel_push("ddisasm_cfg_edge", (0x10_u64, 0x100_u64, "call" as Symbol));
        db.rel_push("ddisasm_cfg_edge", (0x20_u64, 0x200_u64, "call" as Symbol));
        db.rel_push("ddisasm_cfg_edge", (0x30_u64, 0x300_u64, "call" as Symbol));
        db.rel_push(
            "ddisasm_cfg_edge",
            (0x40_u64, 0x100_u64, "fallthrough" as Symbol),
        );
        db.rel_push("ddisasm_cfg_edge", (0x50_u64, 0x400_u64, "call" as Symbol));
        db.rel_push("ddisasm_cfg_edge", (0x60_u64, 0x500_u64, "call" as Symbol));
        db.rel_push("plt_entry", (0x100_u64, "__stack_chk_fail" as Symbol));
        db.rel_push("plt_entry", (0x200_u64, "puts" as Symbol));
        db.rel_push("plt_block", (0x300_u64, "_Exit" as Symbol));
        db.rel_push("plt_block", (0x400_u64, "__stack_chk_fail_local" as Symbol));
        db.rel_push("symbol_resolved_addr", ("abort" as Symbol, 0x500_u64));

        populate_known_noreturn_call_sites(&mut db);

        let sites: BTreeSet<_> = db
            .rel_iter::<(u64,)>("known_noreturn_call_site")
            .map(|(site,)| *site)
            .collect();
        assert_eq!(sites, BTreeSet::from([0x10, 0x30, 0x50, 0x60]));

        let pass = NoreturnSitePass;
        assert!(pass.outputs().contains(&"known_noreturn_call_site"));
        for input in [
            "ddisasm_cfg_edge",
            "plt_entry",
            "plt_block",
            "symbol_resolved_addr",
        ] {
            assert!(pass.extra_reads().contains(&input));
        }
    }

    #[test]
    fn strerror_r_publishes_its_exact_buffer_capacity_contract() {
        let mut db = DecompileDB::default();
        db.target_abi = Some(crate::abi::AbiConfig::sysv_x86_64());

        AbiPass.run(&mut db);

        assert!(db
            .rel_iter::<(Symbol, usize, usize)>("known_func_param_byte_capacity")
            .any(|row| row == &("strerror_r", 1, 2)));
    }
}
