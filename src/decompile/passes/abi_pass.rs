// ABI pass: populates register conventions, known function signatures, and noreturn functions into DecompileDB.

use std::sync::Arc;

use crate::decompile::elevator::DecompileDB;
use crate::decompile::passes::pass::IRPass;
use crate::x86::types::{Symbol, XType};

pub struct AbiPass;

impl IRPass for AbiPass {
    fn name(&self) -> &'static str { "abi" }

    fn run(&self, db: &mut DecompileDB) {
        populate_arg_ret_regs(db);
        populate_known_noreturn(db);
        populate_known_func_param_is_ptr(db);
        populate_known_func_returns(db);
        populate_hardcoded_signatures(db);
        populate_known_global_types(db);
    }

    fn outputs(&self) -> &'static [&'static str] {
        &[
            "is_arg_reg", "is_ret_reg", "is_xmm_arg_reg", "is_float_arg_reg",
            "is_caller_saved", "is_known_noreturn_function",
            "known_func_param_is_ptr", "known_func_returns_ptr",
            "known_func_returns_long", "known_func_returns_int",
            "known_func_returns_float", "known_func_returns_single",
            "known_extern_signature", "known_global_type",
            "known_varargs_function",
        ]
    }
}


// Populate argument, return, and caller-saved register facts from the ABI config.
fn populate_arg_ret_regs(db: &mut DecompileDB) {
    let cfg = crate::x86::abi::abi_config();
    for reg in &cfg.int_arg_regs {
        db.rel_push("is_arg_reg", (*reg,));
    }
    for reg in &cfg.float_arg_regs {
        db.rel_push("is_xmm_arg_reg", (*reg,));
        db.rel_push("is_float_arg_reg", (*reg,));
    }
    db.rel_push("is_ret_reg", (cfg.ret_int_reg,));
    for reg in &cfg.caller_saved {
        db.rel_push("is_caller_saved", (*reg,));
    }
}


// Register functions that never return (exit, abort, longjmp, etc.).
fn populate_known_noreturn(db: &mut DecompileDB) {
    let noreturn_funcs: &[Symbol] = &[
        "exit", "_exit", "_Exit",
        "abort",
        "__assert_fail", "__assert_perror_fail",
        "__stack_chk_fail",
        "pthread_exit",
        "longjmp", "_longjmp", "siglongjmp",
        "__cxa_throw", "__cxa_rethrow",
        "quick_exit", "thrd_exit",
    ];
    for name in noreturn_funcs {
        db.rel_push("is_known_noreturn_function", (*name,));
    }
}


// Register known pointer parameters for libc/coreutils/gnulib functions.
fn populate_known_func_param_is_ptr(db: &mut DecompileDB) {
    let entries: &[(Symbol, usize)] = &[
        ("strlen", 0),
        ("strcpy", 0), ("strcpy", 1),
        ("strcat", 0), ("strcat", 1),
        ("memset", 0),
        ("memcpy", 0), ("memcpy", 1),
        ("memmove", 0), ("memmove", 1),
        ("memchr", 0),
        ("memcmp", 0), ("memcmp", 1),
        ("strdup", 0), ("strndup", 0),
        ("strstr", 0), ("strstr", 1),
        ("strtol", 0), ("strtol", 1),
        ("strtoul", 0), ("strtoul", 1),
        ("strerror", 0),
        ("malloc", 0),
        ("free", 0),
        ("realloc", 0),
        ("reallocarray", 0),
        ("printf", 0),
        ("fprintf", 0), ("fprintf", 1),
        ("snprintf", 0), ("snprintf", 2),
        ("sprintf", 0), ("sprintf", 1),
        ("sscanf", 0), ("sscanf", 1),
        ("fopen", 0), ("fopen", 1),
        ("fclose", 0),
        ("fflush", 0),
        ("ferror", 0), ("feof", 0), ("fileno", 0),
        ("puts", 0),
        ("fputs", 0), ("fputs", 1),
        ("fputc", 1),
        ("fgets", 0), ("fgets", 2),
        ("fread", 0), ("fread", 3),
        ("fwrite", 0), ("fwrite", 3),
        ("fseek", 0),
        ("ftell", 0),
        ("__sprintf_chk", 0), ("__sprintf_chk", 3),
        ("__snprintf_chk", 0), ("__snprintf_chk", 4),
        ("__fprintf_chk", 0), ("__fprintf_chk", 2),
        ("__printf_chk", 1),
        ("__memcpy_chk", 0), ("__memcpy_chk", 1),
        ("__memmove_chk", 0), ("__memmove_chk", 1),
        ("__memset_chk", 0),
        ("__strcpy_chk", 0), ("__strcpy_chk", 1),
        ("__strcat_chk", 0), ("__strcat_chk", 1),
        ("strtok", 0), ("strtok", 1),
        ("getenv", 0), ("setenv", 0), ("setenv", 1),
        ("setlocale", 1),
        ("getopt_long", 1), ("getopt_long", 2), ("getopt_long", 3), ("getopt_long", 4),
        ("atexit", 0), ("signal", 1),
        ("opendir", 0), ("closedir", 0), ("readdir", 0),
        ("access", 0), ("chmod", 0), ("chown", 0),
        ("readlink", 0), ("readlink", 1),
        ("readlinkat", 1), ("readlinkat", 2),
        ("stat", 0), ("stat", 1), ("lstat", 0), ("lstat", 1),
        ("fstatat", 1), ("fstatat", 2),
        ("localtime", 0), ("localtime_r", 0), ("localtime_r", 1),
        ("localtime_rz", 0), ("localtime_rz", 1), ("localtime_rz", 2),
        ("strftime", 0), ("strftime", 2), ("strftime", 3),
        ("nstrftime", 0), ("nstrftime", 2), ("nstrftime", 3),
        ("time", 0),
        ("umaxtostr", 1),
        ("imaxtostr", 1),
        ("offtostr", 1),
        ("uinttostr", 1),
        ("timetostr", 1),
        ("human_readable", 1),
        ("quotearg_style", 1),
        ("quotearg_buffer", 0), ("quotearg_buffer", 2),
        ("quote", 0),
        ("getpwuid", 0),
        ("getgrgid", 0),
        ("error", 2),
        ("__errno_location", 0),
        ("dcgettext", 0), ("dcgettext", 1),
    ];
    for &(name, idx) in entries {
        db.rel_push("known_func_param_is_ptr", (name, idx));
    }
}


// Register known return types (ptr, long, int) for libc/coreutils functions.
fn populate_known_func_returns(db: &mut DecompileDB) {
    let returns_ptr: &[Symbol] = &[
        "malloc", "calloc", "realloc", "reallocarray",
        "strdup", "strndup", "strcpy", "strcat",
        "memcpy", "memset", "memmove", "memchr",
        "fopen", "getenv",
        "strchr", "strrchr", "strstr", "strtok",
        "realpath", "getcwd",
        "readdir", "opendir",
        "strerror", "setlocale",
        "localtime", "localtime_r",
        "getpwuid", "getgrgid",
        "__errno_location",
        "signal", "dcgettext",
        "fdopen", "freopen", "fdopendir",
        "mempcpy", "rawmemchr", "memrchr",
        "stpcpy", "textdomain", "bindtextdomain",
        "nl_langinfo", "dcngettext",
        "localeconv", "newlocale",
        "__ctype_b_loc", "__ctype_toupper_loc", "__ctype_tolower_loc",
        "canonicalize_file_name",
        "getpwnam", "getgrnam",
        "gmtime_r", "aligned_alloc",
        "xmalloc", "ximalloc", "xrealloc", "xirealloc",
        "xcalloc", "xicalloc", "xzalloc", "xizalloc",
        "xstrdup", "xstrndup",
        "xmemdup", "ximemdup", "ximemdup0",
        "xcharalloc",
        "xreallocarray", "xireallocarray",
        "xnmalloc", "xinmalloc",
        "xnrealloc",
        "x2realloc", "x2nrealloc",
        "xpalloc",
        "imalloc", "irealloc", "icalloc", "ireallocarray",
        "tzalloc",
        "umaxtostr", "imaxtostr", "offtostr",
        "uinttostr", "timetostr",
        "localtime_rz", "human_readable",
        "quotearg_style", "quote",
    ];
    for name in returns_ptr {
        db.rel_push("known_func_returns_ptr", (*name,));
    }

    let returns_long: &[Symbol] = &[
        "strlen", "ftell", "fread", "fwrite",
        "lseek", "read", "write",
        "readlink", "readlinkat",
        "strftime", "nstrftime",
        "quotearg_buffer",
        "__getdelim", "pathconf", "clock",
        "strtoimax",
    ];
    for name in returns_long {
        db.rel_push("known_func_returns_long", (*name,));
    }

    let returns_int: &[Symbol] = &[
        "printf", "fprintf", "snprintf", "sprintf",
        "__sprintf_chk", "__snprintf_chk", "__fprintf_chk", "__printf_chk",
        "strcmp", "strncmp", "memcmp",
        "fclose", "feof", "ferror", "fileno",
        "atoi",
        "fgetc", "getc", "getchar",
        "fputc", "putc", "putchar",
        "isalpha", "isdigit", "isspace",
        "tolower", "toupper",
        "close", "open", "access", "chmod", "chown",
        "isatty", "atexit", "raise", "fflush",
        "getopt_long",
        "fstatat", "stat", "fstat", "lstat",
        "fcntl", "ioctl", "openat", "dup2", "fchdir",
        "faccessat", "unlink", "unlinkat", "mkdir",
        "renameat", "fchown", "fchownat",
        "sigaction", "sigprocmask", "sigemptyset", "sigaddset", "sigismember",
        "kill", "fork", "execvp", "waitpid",
        "unsetenv", "clock_gettime", "gettimeofday",
        "uname", "getpagesize", "umask",
        "fputs_unlocked", "fputc_unlocked", "fflush_unlocked",
        "fseeko", "setvbuf",
        "mbsinit", "iswprint", "iswcntrl", "wcwidth",
        "strcoll", "fnmatch", "rpmatch",
        "__cxa_atexit", "__fpending", "__freading",
        "qsort", "posix_fadvise", "ftruncate",
        "dirfd",
    ];
    for name in returns_int {
        db.rel_push("known_func_returns_int", (*name,));
    }
}


// Register full extern signatures (param count, return type, param types) for known functions.
fn populate_hardcoded_signatures(db: &mut DecompileDB) {
    use XType::*;

    let signatures: &[(&str, usize, XType, &[XType])] = &[
        ("memset",   3, Xptr,   &[Xptr, Xint, Xany64]),
        ("memcpy",   3, Xptr,   &[Xptr, Xptr, Xany64]),
        ("memmove",  3, Xptr,   &[Xptr, Xptr, Xany64]),
        ("memcmp",   3, Xint,   &[Xptr, Xptr, Xany64]),
        ("strlen",   1, Xany64, &[Xcharptr]),
        ("strcpy",   2, Xcharptr, &[Xcharptr, Xcharptr]),
        ("strncpy",  3, Xcharptr, &[Xcharptr, Xcharptr, Xany64]),
        ("strcmp",    2, Xint,   &[Xcharptr, Xcharptr]),
        ("strncmp",  3, Xint,   &[Xcharptr, Xcharptr, Xany64]),
        ("strchr",   2, Xcharptr, &[Xcharptr, Xint]),
        ("strrchr",  2, Xcharptr, &[Xcharptr, Xint]),
        ("strcat",   2, Xcharptr, &[Xcharptr, Xcharptr]),
        ("strncat",  3, Xcharptr, &[Xcharptr, Xcharptr, Xany64]),
        ("strdup",   1, Xcharptr, &[Xcharptr]),
        ("strndup",  2, Xcharptr, &[Xcharptr, Xany64]),
        ("strstr",   2, Xcharptr, &[Xcharptr, Xcharptr]),
        ("strtol",   3, Xlong,  &[Xcharptr, Xptr, Xint]),
        ("strtoul",  3, Xlongunsigned, &[Xcharptr, Xptr, Xint]),
        ("strerror", 1, Xcharptr, &[Xint]),
        ("printf",   1, Xint,   &[Xcharptr]),
        ("fprintf",  2, Xint,   &[Xptr, Xcharptr]),
        ("snprintf", 3, Xint,   &[Xcharptr, Xany64, Xcharptr]),
        ("sprintf",  2, Xint,   &[Xcharptr, Xcharptr]),
        ("puts",     1, Xint,   &[Xcharptr]),
        ("fputs",    2, Xint,   &[Xcharptr, Xptr]),
        ("fputc",    2, Xint,   &[Xint, Xptr]),
        ("putchar",  1, Xint,   &[Xint]),
        ("fwrite",   4, Xany64, &[Xptr, Xany64, Xany64, Xptr]),
        ("fread",    4, Xany64, &[Xptr, Xany64, Xany64, Xptr]),
        ("fopen",    2, Xptr,   &[Xcharptr, Xcharptr]),
        ("fclose",   1, Xint,   &[Xptr]),
        ("fflush",   1, Xint,   &[Xptr]),
        ("ferror",   1, Xint,   &[Xptr]),
        ("feof",     1, Xint,   &[Xptr]),
        ("fileno",   1, Xint,   &[Xptr]),
        ("__sprintf_chk",  4, Xint, &[Xcharptr, Xint, Xany64, Xcharptr]),
        ("__snprintf_chk", 5, Xint, &[Xcharptr, Xany64, Xint, Xany64, Xcharptr]),
        ("__fprintf_chk",  3, Xint, &[Xptr, Xint, Xcharptr]),
        ("__printf_chk",   2, Xint, &[Xint, Xcharptr]),
        ("__memcpy_chk",   4, Xptr, &[Xptr, Xptr, Xany64, Xany64]),
        ("__memmove_chk",  4, Xptr, &[Xptr, Xptr, Xany64, Xany64]),
        ("__memset_chk",   4, Xptr, &[Xptr, Xint, Xany64, Xany64]),
        ("__strcpy_chk",   3, Xcharptr, &[Xcharptr, Xcharptr, Xany64]),
        ("__strcat_chk",   3, Xcharptr, &[Xcharptr, Xcharptr, Xany64]),
        ("malloc",   1, Xptr,   &[Xany64]),
        ("calloc",   2, Xptr,   &[Xany64, Xany64]),
        ("realloc",  2, Xptr,   &[Xptr, Xany64]),
        ("free",     1, Xvoid,  &[Xptr]),
        ("reallocarray", 3, Xptr, &[Xptr, Xany64, Xany64]),
        ("alloca",   1, Xptr,   &[Xany64]),
        ("exit",     1, Xvoid,  &[Xint]),
        ("abort",    0, Xvoid,  &[]),
        ("getenv",   1, Xcharptr, &[Xcharptr]),
        ("setenv",   3, Xint,   &[Xcharptr, Xcharptr, Xint]),
        ("setlocale", 2, Xcharptr, &[Xint, Xcharptr]),
        ("getopt_long", 5, Xint, &[Xint, Xcharptr, Xcharptr, Xptr, Xptr]),
        ("atexit",   1, Xint,   &[Xptr]),
        ("signal",   2, Xptr,   &[Xint, Xptr]),
        ("raise",    1, Xint,   &[Xint]),
        ("open",     2, Xint,   &[Xcharptr, Xint]),
        ("close",    1, Xint,   &[Xint]),
        ("read",     3, Xlong,  &[Xint, Xptr, Xany64]),
        ("write",    3, Xlong,  &[Xint, Xptr, Xany64]),
        ("lseek",    3, Xlong,  &[Xint, Xlong, Xint]),
        ("stat",     2, Xint,   &[Xcharptr, Xptr]),
        ("fstat",    2, Xint,   &[Xint, Xptr]),
        ("lstat",    2, Xint,   &[Xcharptr, Xptr]),
        ("fstatat",  4, Xint,   &[Xint, Xcharptr, Xptr, Xint]),
        ("readlink", 3, Xlong,  &[Xcharptr, Xcharptr, Xany64]),
        ("readlinkat", 4, Xlong, &[Xint, Xcharptr, Xcharptr, Xany64]),
        ("opendir",  1, Xptr,   &[Xcharptr]),
        ("closedir", 1, Xint,   &[Xptr]),
        ("readdir",  1, Xptr,   &[Xptr]),
        ("access",   2, Xint,   &[Xcharptr, Xint]),
        ("chmod",    2, Xint,   &[Xcharptr, Xint]),
        ("chown",    3, Xint,   &[Xcharptr, Xint, Xint]),
        ("isatty",   1, Xint,   &[Xint]),
        ("time",       1, Xlong, &[Xptr]),
        ("localtime",  1, Xptr,  &[Xptr]),
        ("localtime_r", 2, Xptr, &[Xptr, Xptr]),
        ("localtime_rz", 3, Xptr, &[Xptr, Xptr, Xptr]),
        ("strftime",   4, Xany64, &[Xptr, Xany64, Xptr, Xptr]),
        ("nstrftime",  6, Xany64, &[Xptr, Xany64, Xptr, Xptr, Xint, Xint]),
        ("human_readable", 5, Xcharptr, &[Xany64, Xcharptr, Xint, Xany64, Xany64]),
        ("umaxtostr",  2, Xcharptr, &[Xany64, Xcharptr]),
        ("imaxtostr",  2, Xcharptr, &[Xlong, Xcharptr]),
        ("offtostr",   2, Xcharptr, &[Xlong, Xcharptr]),
        ("uinttostr",  2, Xcharptr, &[Xany64, Xcharptr]),
        ("timetostr",  2, Xcharptr, &[Xlong, Xcharptr]),
        ("quotearg_style", 2, Xcharptr, &[Xint, Xcharptr]),
        ("quotearg_buffer", 4, Xany64, &[Xcharptr, Xany64, Xcharptr, Xany64]),
        ("quote",      1, Xcharptr, &[Xcharptr]),
        ("getpwuid",   1, Xptr, &[Xint]),
        ("getgrgid",   1, Xptr, &[Xint]),
        ("getuid",     0, Xint, &[]),
        ("getgid",     0, Xint, &[]),
        ("geteuid",    0, Xint, &[]),
        ("getegid",    0, Xint, &[]),
        ("error",      3, Xvoid, &[Xint, Xint, Xcharptr]),
        ("__errno_location", 0, Xptr, &[]),
        ("dcgettext",  3, Xcharptr, &[Xcharptr, Xcharptr, Xint]),
        ("__libc_start_main", 6, Xint, &[Xptr, Xint, Xptr, Xptr, Xptr, Xptr]),
        ("__cxa_finalize",    1, Xvoid,  &[Xptr]),
        ("__stack_chk_fail",  0, Xvoid,  &[]),
        ("__cxa_atexit",      3, Xint,   &[Xptr, Xptr, Xptr]),
        ("__ctype_get_mb_cur_max", 0, Xany64, &[]),
        ("__ctype_b_loc",     0, Xptr,   &[]),
        ("__ctype_toupper_loc", 0, Xptr, &[]),
        ("__ctype_tolower_loc", 0, Xptr, &[]),
        ("__fpending",        1, Xany64, &[Xptr]),
        ("__freading",        1, Xint,   &[Xptr]),
        ("__fpurge",          1, Xvoid,  &[Xptr]),
        ("__overflow",        2, Xint,   &[Xptr, Xint]),
        ("__uflow",           1, Xint,   &[Xptr]),
        ("__assert_fail",     4, Xvoid,  &[Xcharptr, Xcharptr, Xintunsigned, Xcharptr]),
        ("__getdelim",        4, Xlong,  &[Xptr, Xptr, Xint, Xptr]),
        ("_exit",             1, Xvoid,  &[Xint]),
        ("textdomain",        1, Xcharptr, &[Xcharptr]),
        ("bindtextdomain",    2, Xcharptr, &[Xcharptr, Xcharptr]),
        ("nl_langinfo",       1, Xcharptr, &[Xint]),
        ("dcngettext",        5, Xcharptr, &[Xcharptr, Xcharptr, Xcharptr, Xlongunsigned, Xint]),
        ("localeconv",        0, Xptr,   &[]),
        ("newlocale",         3, Xptr,   &[Xint, Xcharptr, Xptr]),
        ("mbsinit",           1, Xint,   &[Xptr]),
        ("mbrtoc32",          4, Xany64, &[Xptr, Xcharptr, Xany64, Xptr]),
        ("iswprint",          1, Xint,   &[Xint]),
        ("iswcntrl",          1, Xint,   &[Xint]),
        ("wcwidth",           1, Xint,   &[Xint]),
        ("fputs_unlocked",    2, Xint,   &[Xcharptr, Xptr]),
        ("fputc_unlocked",    2, Xint,   &[Xint, Xptr]),
        ("fwrite_unlocked",   4, Xany64, &[Xptr, Xany64, Xany64, Xptr]),
        ("fread_unlocked",    4, Xany64, &[Xptr, Xany64, Xany64, Xptr]),
        ("fflush_unlocked",   1, Xint,   &[Xptr]),
        ("clearerr_unlocked", 1, Xvoid,  &[Xptr]),
        ("fseeko",            3, Xint,   &[Xptr, Xlong, Xint]),
        ("fdopen",            2, Xptr,   &[Xint, Xcharptr]),
        ("freopen",           3, Xptr,   &[Xcharptr, Xcharptr, Xptr]),
        ("setvbuf",           4, Xint,   &[Xptr, Xcharptr, Xint, Xany64]),
        ("strtoumax",         3, Xlongunsigned, &[Xcharptr, Xptr, Xint]),
        ("strtoimax",         3, Xlong,  &[Xcharptr, Xptr, Xint]),
        ("strspn",            2, Xany64, &[Xcharptr, Xcharptr]),
        ("strcspn",           2, Xany64, &[Xcharptr, Xcharptr]),
        ("strcoll",           2, Xint,   &[Xcharptr, Xcharptr]),
        ("stpcpy",            2, Xcharptr, &[Xcharptr, Xcharptr]),
        ("strnlen",           2, Xany64, &[Xcharptr, Xany64]),
        ("mempcpy",           3, Xptr,   &[Xptr, Xptr, Xany64]),
        ("rawmemchr",         2, Xptr,   &[Xptr, Xint]),
        ("memrchr",           3, Xptr,   &[Xptr, Xint, Xany64]),
        ("fcntl",             2, Xint,   &[Xint, Xint]),
        ("ioctl",             2, Xint,   &[Xint, Xlongunsigned]),
        ("openat",            3, Xint,   &[Xint, Xcharptr, Xint]),
        ("posix_fadvise",     4, Xint,   &[Xint, Xlong, Xlong, Xint]),
        ("dup2",              2, Xint,   &[Xint, Xint]),
        ("ftruncate",         2, Xint,   &[Xint, Xlong]),
        ("fchdir",            1, Xint,   &[Xint]),
        ("chdir",             1, Xint,   &[Xcharptr]),
        ("getcwd",            2, Xcharptr, &[Xcharptr, Xany64]),
        ("dirfd",             1, Xint,   &[Xptr]),
        ("fdopendir",         1, Xptr,   &[Xint]),
        ("faccessat",         4, Xint,   &[Xint, Xcharptr, Xint, Xint]),
        ("unlink",            1, Xint,   &[Xcharptr]),
        ("unlinkat",          3, Xint,   &[Xint, Xcharptr, Xint]),
        ("mkdir",             2, Xint,   &[Xcharptr, Xint]),
        ("renameat",          4, Xint,   &[Xint, Xcharptr, Xint, Xcharptr]),
        ("renameat2",         5, Xint,   &[Xint, Xcharptr, Xint, Xcharptr, Xintunsigned]),
        ("fchown",            3, Xint,   &[Xint, Xint, Xint]),
        ("fchownat",          5, Xint,   &[Xint, Xcharptr, Xint, Xint, Xint]),
        ("pathconf",          2, Xlong,  &[Xcharptr, Xint]),
        ("canonicalize_file_name", 1, Xcharptr, &[Xcharptr]),
        ("sigaction",         3, Xint,   &[Xint, Xptr, Xptr]),
        ("sigprocmask",       3, Xint,   &[Xint, Xptr, Xptr]),
        ("sigemptyset",       1, Xint,   &[Xptr]),
        ("sigaddset",         2, Xint,   &[Xptr, Xint]),
        ("sigismember",       2, Xint,   &[Xptr, Xint]),
        ("kill",              2, Xint,   &[Xint, Xint]),
        ("fork",              0, Xint,   &[]),
        ("execvp",            2, Xint,   &[Xcharptr, Xptr]),
        ("waitpid",           3, Xint,   &[Xint, Xptr, Xint]),
        ("unsetenv",          1, Xint,   &[Xcharptr]),
        ("aligned_alloc",     2, Xptr,   &[Xany64, Xany64]),
        ("clock_gettime",     2, Xint,   &[Xint, Xptr]),
        ("gettimeofday",      2, Xint,   &[Xptr, Xptr]),
        ("gmtime_r",          2, Xptr,   &[Xptr, Xptr]),
        ("clock",             0, Xlong,  &[]),
        ("uname",             1, Xint,   &[Xptr]),
        ("getpagesize",       0, Xint,   &[]),
        ("umask",             1, Xint,   &[Xint]),
        ("getpwnam",          1, Xptr,   &[Xcharptr]),
        ("getgrnam",          1, Xptr,   &[Xcharptr]),
        ("endpwent",          0, Xvoid,  &[]),
        ("endgrent",          0, Xvoid,  &[]),
        ("qsort",             4, Xvoid,  &[Xptr, Xany64, Xany64, Xptr]),
        ("fnmatch",           3, Xint,   &[Xcharptr, Xcharptr, Xint]),
        ("rpmatch",           1, Xint,   &[Xcharptr]),
        ("strtok_r",          3, Xcharptr, &[Xcharptr, Xcharptr, Xptr]),
        ("gettext",           1, Xcharptr, &[Xcharptr]),
        ("ngettext",          3, Xcharptr, &[Xcharptr, Xcharptr, Xlongunsigned]),
        ("dgettext",          2, Xcharptr, &[Xcharptr, Xcharptr]),
        ("quotearg_n_style",  3, Xcharptr, &[Xint, Xint, Xcharptr]),
        ("quote_n",           2, Xcharptr, &[Xint, Xcharptr]),
        ("canonicalize_filename_mode", 2, Xcharptr, &[Xcharptr, Xint]),
        ("mmap",              6, Xptr,   &[Xptr, Xany64, Xint, Xint, Xint, Xlong]),
        ("memchr",            3, Xptr,   &[Xptr, Xint, Xany64]),
        ("atoi",              1, Xint,   &[Xcharptr]),
        ("atol",              1, Xlong,  &[Xcharptr]),
        ("getopt",            3, Xint,   &[Xint, Xcharptr, Xcharptr]),
        ("putenv",            1, Xint,   &[Xcharptr]),
        ("rmdir",             1, Xint,   &[Xcharptr]),
        ("remove",            1, Xint,   &[Xcharptr]),
        ("rename",            2, Xint,   &[Xcharptr, Xcharptr]),
        ("dup",               1, Xint,   &[Xint]),
        ("pipe",              1, Xint,   &[Xptr]),
        ("fseek",             3, Xint,   &[Xptr, Xlong, Xint]),
        ("fgetc",             1, Xint,   &[Xptr]),
        ("getc",              1, Xint,   &[Xptr]),
        ("getchar",           0, Xint,   &[]),
        ("toupper",           1, Xint,   &[Xint]),
        ("tolower",           1, Xint,   &[Xint]),
        ("isspace",           1, Xint,   &[Xint]),
        ("isdigit",           1, Xint,   &[Xint]),
        ("isalpha",           1, Xint,   &[Xint]),
        ("isalnum",           1, Xint,   &[Xint]),
        ("mbstowcs",          3, Xany64, &[Xptr, Xcharptr, Xany64]),
        ("ftell",             1, Xlong,  &[Xptr]),
        ("sysconf",           1, Xlong,  &[Xint]),
        ("munmap",            2, Xint,   &[Xptr, Xany64]),
        ("sscanf",            2, Xint,   &[Xcharptr, Xcharptr]),
    ];

    for &(name, param_count, ret_type, param_types) in signatures {
        db.rel_push("known_extern_signature", (
            name,
            param_count,
            ret_type,
            Arc::new(param_types.to_vec()),
        ));
    }

    // Known variadic functions: (name, declared_param_count)
    let varargs: &[(&str, usize)] = &[
        ("printf", 1), ("fprintf", 2), ("sprintf", 2), ("snprintf", 3),
        ("scanf", 1), ("fscanf", 2), ("sscanf", 2),
        ("__printf_chk", 2), ("__fprintf_chk", 3), ("__sprintf_chk", 4), ("__snprintf_chk", 5),
    ];
    for &(name, fixed_args) in varargs {
        db.rel_push("known_varargs_function", (name, fixed_args));
    }
}


// Register known types for well-known global variables (stdout, optarg, etc.).
fn populate_known_global_types(db: &mut DecompileDB) {
    use XType::*;

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
        ("Version", Xcharptr),
        ("program_invocation_name", Xcharptr),
        ("program_invocation_short_name", Xcharptr),
        ("__ctype_b_loc", Xptr),
        ("errno", Xint),
    ];

    for &(name, ref xtype) in known_globals {
        db.rel_push("known_global_type", (name, xtype.clone()));
    }
}
