use crate::aarch64::mach::A64Mreg;
use crate::arm32::mach::A32Mreg;
use crate::mreg::Mreg;

// Noreturn classification, the single source of truth shared by abi_pass,
// canary_vla_pass, linear_pass, cshminor_pass and structuring_pass so their
// lists cannot drift.

/// Explicit stack-protector failure aliases emitted by supported toolchains.
/// Keep this exact: substring matching can misclassify an ordinary wrapper.
pub const STACK_CHK_FAIL_FUNCS: &[&str] = &[
    "__stack_chk_fail",
    "__stack_chk_fail_local",
    "___stack_chk_fail",
];

pub fn is_stack_chk_fail(symbol: &str) -> bool {
    STACK_CHK_FAIL_FUNCS.contains(&symbol)
}

/// Other functions that NEVER return regardless of arguments.
pub const ALWAYS_NORETURN_FUNCS: &[&str] = &[
    // libc primitives
    "exit",
    "_exit",
    "_Exit",
    "abort",
    "__assert_fail",
    "__assert_perror_fail",
    "pthread_exit",
    "longjmp",
    "_longjmp",
    "siglongjmp",
    "__cxa_throw",
    "__cxa_rethrow",
    "quick_exit",
    "thrd_exit",
    // always-noreturn wrappers (declared _Noreturn at their source)
    "xalloc_die",
    "__chk_fail",
    "__fortify_fail",
    "assert_failed",
];

pub fn always_noreturn_symbols() -> impl Iterator<Item = &'static str> {
    ALWAYS_NORETURN_FUNCS
        .iter()
        .chain(STACK_CHK_FAIL_FUNCS.iter())
        .copied()
}

/// True for an always-noreturn function (the two exact symbol sets above).
pub fn is_always_noreturn(symbol: &str) -> bool {
    ALWAYS_NORETURN_FUNCS.contains(&symbol) || is_stack_chk_fail(symbol)
}

/// error-family functions that exit(status) only when status != 0, so they are noreturn exactly when arg 0 is a nonzero constant.
pub fn is_status_noreturn_callee(symbol: &str) -> bool {
    matches!(
        symbol,
        "error" | "error_at_line" | "verror" | "verror_at_line"
    )
}

/// THE shared status-aware noreturn predicate: always-noreturn callees, or error-family callees whose arg 0 is a known nonzero constant (exact, not heuristic).
pub fn call_is_noreturn(callee: &str, status_arg0_nonzero_const: impl FnOnce() -> bool) -> bool {
    is_always_noreturn(callee) || (is_status_noreturn_callee(callee) && status_arg0_nonzero_const())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryFormat {
    Elf,
    Pe,
    MachO,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Arch {
    X86_64,
    X86_32,
    Aarch64,
    Arm32,
}

/// The C data model of a target's toolchain: how wide `int`, `long` and a
/// pointer are.  This is deliberately NOT the same question as `pointer_size`,
/// and the two part company on Windows x64, which pairs a 64-bit pointer with a
/// 32-bit `long`.  A rule that wants to know how wide `long` is, or which C
/// spelling holds 64 bits, must ask the model; reading it off the pointer width
/// happens to work on the three Linux targets and is wrong on the fourth.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DataModel {
    /// 32-bit int, long and pointer: i386 and arm32 Linux.
    Ilp32,
    /// 32-bit int, 64-bit long and pointer: x86-64 and aarch64 Linux.
    Lp64,
    /// 32-bit int and long, 64-bit pointer: Windows x64.
    Llp64,
}

impl DataModel {
    pub fn pointer_size(self) -> usize {
        match self {
            DataModel::Ilp32 => 4,
            DataModel::Lp64 | DataModel::Llp64 => 8,
        }
    }

    pub fn long_size(self) -> usize {
        match self {
            DataModel::Ilp32 | DataModel::Llp64 => 4,
            DataModel::Lp64 => 8,
        }
    }

    /// True when plain `long` already holds 64 bits.  Where it does not, a
    /// 64-bit value has to be spelled `long long` or the declaration silently
    /// narrows to 32 bits and every later field of its struct shifts.
    pub fn long_holds_64bit(self) -> bool {
        self.long_size() == 8
    }
}

/// A fixed-layout glibc object that an external callee writes through an
/// out-parameter.  Naming the OBJECT keeps the two halves of that knowledge
/// apart: which parameter of which function points at one is a property of the
/// libc interface and the same everywhere, while how many bytes it occupies is
/// a property of the target and is not.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LibcObject {
    Stat,
    Statvfs,
    Statfs,
    Tm,
    Utsname,
    /// `struct timeval` and `struct timespec` alike; both are two words.
    Timeval,
    Rusage,
    Tms,
    Rlimit,
    Sigset,
    Sigaction,
    Termios,
    /// A pointer the callee writes back (a `char **` end pointer, an allocated
    /// buffer), not a struct.
    Pointer,
}

/// Sizes of the glibc objects above for one target.  Nothing in a binary
/// reveals these -- the callee whose write they bound has no body in the image
/// -- so they are MEASURED rather than derived: `sizeof` under gcc against
/// glibc 2.35, cross-compiled per target.
///
/// Every object here is fixed by the data model except `struct stat`, whose
/// aarch64 kernel-ABI layout is 128 bytes where x86-64 uses 144; i386 and arm32
/// agree with each other exactly.  That one exception is why this carries the
/// architecture as well as the model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LibcLayout {
    pub model: DataModel,
    pub arch: Arch,
}

impl LibcLayout {
    /// Size in bytes of `obj` on this target.
    pub fn size_of(&self, obj: LibcObject) -> usize {
        let lp64 = self.model.long_holds_64bit();
        let by_model = |wide: usize, narrow: usize| if lp64 { wide } else { narrow };
        match obj {
            // The lone object whose size the data model does not settle.
            LibcObject::Stat => match self.arch {
                Arch::Aarch64 => 128,
                Arch::X86_64 => 144,
                Arch::X86_32 | Arch::Arm32 => 88,
            },
            LibcObject::Statvfs => by_model(112, 72),
            LibcObject::Statfs => by_model(120, 64),
            LibcObject::Tm => by_model(56, 44),
            // Six NUL-terminated char arrays of _UTSNAME_LENGTH=65: no word-sized
            // field, so the same 390 bytes under either model.
            LibcObject::Utsname => 390,
            LibcObject::Timeval => by_model(16, 8),
            LibcObject::Rusage => by_model(144, 72),
            LibcObject::Tms => by_model(32, 16),
            LibcObject::Rlimit => by_model(16, 8),
            // A fixed 1024-bit mask, and a fixed cc_t array beside 32-bit flag
            // words: both measure the same under either model.
            LibcObject::Sigset => 128,
            LibcObject::Sigaction => by_model(152, 140),
            LibcObject::Termios => 60,
            LibcObject::Pointer => self.model.pointer_size(),
        }
    }
}

/// A stack-protector cookie read from a fixed offset off a segment base.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StackGuardSlot {
    pub segment: &'static str,
    pub offset: i64,
}

// Per-function calling conventions: Windows x86-32 mixes cdecl, stdcall, fastcall and thiscall in ONE image, so the convention belongs to each function, is recovered from evidence, and lives ALONGSIDE the image-wide AbiConfig rather than inside it.

/// A Windows x86-32 calling convention. cdecl is the image-wide default; the others are per-function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum CallConv {
    /// All arguments on the stack, CALLER cleans up.
    Cdecl,
    /// All arguments on the stack, CALLEE cleans up with RET imm16.
    Stdcall,
    /// First two DWORD arguments in ECX,EDX, the rest on the stack, CALLEE cleans up.
    Fastcall,
    /// `this` in ECX, the rest on the stack, CALLEE cleans up.
    Thiscall,
}

impl CallConv {
    /// Leading argument positions passed in integer registers: ECX, then EDX.
    pub fn register_arg_count(self) -> usize {
        match self {
            CallConv::Fastcall => 2,
            CallConv::Thiscall => 1,
            CallConv::Cdecl | CallConv::Stdcall => 0,
        }
    }

    /// True when the callee pops its own stack arguments before returning.
    pub fn callee_cleans_stack(self) -> bool {
        !matches!(self, CallConv::Cdecl)
    }
}

/// One MSVC-decorated name split into the undecorated C identifier and what the decoration proves.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecoratedName {
    pub undecorated: String,
    pub conv: CallConv,
    /// TOTAL argument bytes the decoration declares, register arguments included; None when undecorated.
    pub arg_bytes: Option<u32>,
}

/// Parse an MSVC C name decoration: `_foo@12` is stdcall with 12 argument bytes, `@foo@8` is fastcall with 8, `_foo` and `foo` are cdecl with no byte count; None for anything outside this scheme (C++ `?` mangling, ordinal imports, a bare `@name`).
pub fn parse_decorated_name(raw: &str) -> Option<DecoratedName> {
    // A leading '?' is MSVC C++ mangling, whose '@' separators are structure, not an argument byte count.
    if raw.is_empty() || raw.starts_with('?') {
        return None;
    }
    let (sigil, rest) = match raw.as_bytes()[0] {
        b'@' => (Some(b'@'), &raw[1..]),
        b'_' => (Some(b'_'), &raw[1..]),
        _ => (None, raw),
    };
    // The `@N` suffix is the argument byte count; anything else after '@' is not this scheme.
    let suffix = rest.rsplit_once('@').and_then(|(base, digits)| {
        if base.is_empty() || base.contains('@') || digits.is_empty() {
            return None;
        }
        digits.parse::<u32>().ok().map(|bytes| (base, bytes))
    });
    match (sigil, suffix) {
        // Fastcall is the only convention whose decoration uses the '@' sigil, and it always carries @N.
        (Some(b'@'), Some((base, bytes))) => Some(DecoratedName {
            undecorated: base.to_string(),
            conv: CallConv::Fastcall,
            arg_bytes: Some(bytes),
        }),
        // A leading '_' plus @N is stdcall; the byte count is exact evidence of callee cleanup.
        (Some(b'_'), Some((base, bytes))) => Some(DecoratedName {
            undecorated: base.to_string(),
            conv: CallConv::Stdcall,
            arg_bytes: Some(bytes),
        }),
        // No byte count: cdecl, whose C decoration is only the leading underscore. The '@' sigil is excluded because it belongs to fastcall alone and is meaningless without its @N.
        (None, None) | (Some(b'_'), None) if !rest.contains('@') => Some(DecoratedName {
            undecorated: rest.to_string(),
            conv: CallConv::Cdecl,
            arg_bytes: None,
        }),
        _ => None,
    }
}

/// Per-function ABI evidence, keyed by function address, that overrides the image-wide AbiConfig.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct FuncAbi {
    /// Leading argument positions this function takes in integer registers.
    pub reg_arg_count: usize,
    /// Stack bytes the callee pops (RET imm16); Some only where callee cleanup is PROVEN.
    pub callee_pop_bytes: Option<i64>,
    /// TOTAL argument bytes a decorated name declares, register arguments included.
    pub decorated_arg_bytes: Option<i64>,
}

impl FuncAbi {
    /// Argument SLOTS the evidence accounts for, or None when nothing pins them: a decorated name covers all arguments while RET imm16 covers only the stack ones, so the register arguments are added back; a multi-slot argument (double, long long) makes this an upper bound rather than an equality.
    pub fn evidenced_arg_slots(&self, slot_size: i64) -> Option<usize> {
        if slot_size <= 0 {
            return None;
        }
        if let Some(bytes) = self.decorated_arg_bytes {
            return Some((bytes / slot_size) as usize);
        }
        self.callee_pop_bytes
            .map(|bytes| self.reg_arg_count + (bytes / slot_size) as usize)
    }
}

#[derive(Debug, Clone)]
pub struct AbiConfig {
    pub format: BinaryFormat,
    pub arch: Arch,

    pub pointer_size: usize,

    pub int_arg_regs: Vec<Mreg>,

    pub float_arg_regs: Vec<Mreg>,

    pub ret_int_reg: Mreg,

    #[allow(dead_code)]
    pub ret_float_reg: Mreg,

    pub caller_saved: Vec<Mreg>,

    pub callee_saved: Vec<Mreg>,

    #[allow(dead_code)]
    pub stack_alignment: usize,

    #[allow(dead_code)]
    pub red_zone_size: usize,
}

impl AbiConfig {
    pub fn sysv_x86_64() -> Self {
        Self {
            format: BinaryFormat::Elf,
            arch: Arch::X86_64,
            pointer_size: 8,
            int_arg_regs: vec![Mreg::DI, Mreg::SI, Mreg::DX, Mreg::CX, Mreg::R8, Mreg::R9],
            float_arg_regs: vec![
                Mreg::X0,
                Mreg::X1,
                Mreg::X2,
                Mreg::X3,
                Mreg::X4,
                Mreg::X5,
                Mreg::X6,
                Mreg::X7,
            ],
            ret_int_reg: Mreg::AX,
            ret_float_reg: Mreg::X0,
            caller_saved: vec![
                Mreg::AX,
                Mreg::CX,
                Mreg::DX,
                Mreg::SI,
                Mreg::DI,
                Mreg::R8,
                Mreg::R9,
                Mreg::R10,
                Mreg::R11,
                Mreg::X0,
                Mreg::X1,
                Mreg::X2,
                Mreg::X3,
                Mreg::X4,
                Mreg::X5,
                Mreg::X6,
                Mreg::X7,
                Mreg::X8,
                Mreg::X9,
                Mreg::X10,
                Mreg::X11,
                Mreg::X12,
                Mreg::X13,
                Mreg::X14,
                Mreg::X15,
            ],
            callee_saved: vec![
                Mreg::BX,
                Mreg::BP,
                Mreg::R12,
                Mreg::R13,
                Mreg::R14,
                Mreg::R15,
            ],
            stack_alignment: 16,
            red_zone_size: 128,
        }
    }

    pub fn win64() -> Self {
        Self {
            format: BinaryFormat::Pe,
            arch: Arch::X86_64,
            pointer_size: 8,
            int_arg_regs: vec![Mreg::CX, Mreg::DX, Mreg::R8, Mreg::R9],
            float_arg_regs: vec![Mreg::X0, Mreg::X1, Mreg::X2, Mreg::X3],
            ret_int_reg: Mreg::AX,
            ret_float_reg: Mreg::X0,
            caller_saved: vec![
                Mreg::AX,
                Mreg::CX,
                Mreg::DX,
                Mreg::R8,
                Mreg::R9,
                Mreg::R10,
                Mreg::R11,
                Mreg::X0,
                Mreg::X1,
                Mreg::X2,
                Mreg::X3,
                Mreg::X4,
                Mreg::X5,
            ],
            callee_saved: vec![
                Mreg::BX,
                Mreg::BP,
                Mreg::SI,
                Mreg::DI,
                Mreg::R12,
                Mreg::R13,
                Mreg::R14,
                Mreg::R15,
                Mreg::X6,
                Mreg::X7,
                Mreg::X8,
                Mreg::X9,
                Mreg::X10,
                Mreg::X11,
                Mreg::X12,
                Mreg::X13,
                Mreg::X14,
                Mreg::X15,
            ],
            stack_alignment: 16,
            red_zone_size: 0,
        }
    }

    /// i386 System V (cdecl): every argument on the stack, integers returned in EAX (EDX:EAX for 64-bit), floats in x87 st(0).
    pub fn cdecl_x86_32() -> Self {
        Self {
            format: BinaryFormat::Elf,
            arch: Arch::X86_32,
            pointer_size: 4,
            // cdecl passes nothing in registers; first_stack_arg_position() is therefore 0.
            int_arg_regs: vec![],
            float_arg_regs: vec![],
            ret_int_reg: Mreg::AX,
            ret_float_reg: Mreg::FP0,
            // i386 has only XMM0-XMM7, all caller-saved.
            caller_saved: vec![
                Mreg::AX,
                Mreg::CX,
                Mreg::DX,
                Mreg::X0,
                Mreg::X1,
                Mreg::X2,
                Mreg::X3,
                Mreg::X4,
                Mreg::X5,
                Mreg::X6,
                Mreg::X7,
            ],
            callee_saved: vec![Mreg::BX, Mreg::BP, Mreg::SI, Mreg::DI],
            // gcc/clang have kept i386 SysV at 16 since gcc 4.5, matching the ABI revision.
            stack_alignment: 16,
            red_zone_size: 0,
        }
    }

    /// Windows x86-32: cdecl is the image-wide default, so nothing is claimed for registers up front; ECX/EDX are listed because they are the fastcall/thiscall slots individual functions claim.
    pub fn win32_x86() -> Self {
        let mut cfg = Self::cdecl_x86_32();
        cfg.format = BinaryFormat::Pe;
        // Ordinal 0 is ECX, ordinal 1 is EDX, shared by fastcall (both) and thiscall (ECX only).
        cfg.int_arg_regs = vec![Mreg::CX, Mreg::DX];
        // MSVC keeps the Windows x86 stack at pointer alignment; there is no 16-byte guarantee.
        cfg.stack_alignment = 4;
        cfg
    }

    /// AAPCS64 (ARM's standard AArch64 calling convention), as used by Linux ELF.
    pub fn aapcs64() -> Self {
        let gp = |n: u8| Mreg::A64(A64Mreg::gp(n));
        let v = |n: u8| Mreg::A64(A64Mreg::vec(n));
        Self {
            format: BinaryFormat::Elf,
            arch: Arch::Aarch64,
            pointer_size: 8,
            // NGRN/NSRN are independent counters, as in SysV x86-64 and unlike Win64.
            int_arg_regs: (0..8).map(gp).collect(),
            float_arg_regs: (0..8).map(v).collect(),
            ret_int_reg: gp(0),
            ret_float_reg: v(0),
            // X0-X17 are temporaries (X16/X17 are IP0/IP1); X18 is the platform register, a Linux temporary but reserved on Darwin/Windows, so it is in neither list.
            caller_saved: (0..18)
                .map(gp)
                .chain((0..8).map(v))
                .chain((16..32).map(v))
                .collect(),
            // V8-V15 are callee-saved only in their low 64 bits; modelling whole registers is the conservative direction for a saved-reg test.
            callee_saved: (19..=30).map(gp).chain((8..16).map(v)).collect(),
            stack_alignment: 16,
            red_zone_size: 0,
        }
    }

    /// AAPCS32 (ARM's standard 32-bit calling convention), as used by Linux ELF; the hard-float and soft-float variants differ only in how FP arguments travel, which the register tables below cover.
    pub fn aapcs32() -> Self {
        let gp = |n: u8| Mreg::A32(A32Mreg::gp(n));
        let s = |n: u8| Mreg::A32(A32Mreg::s(n));
        Self {
            format: BinaryFormat::Elf,
            arch: Arch::Arm32,
            pointer_size: 4,
            // R0-R3 are the core argument registers; a 64-bit argument takes an even-aligned pair.
            int_arg_regs: (0..4).map(gp).collect(),
            // VFP (hard-float) passes FP arguments in S0-S15 / D0-D7; the single-precision view is the finer one and the double view aliases it, so listing S covers both callers.
            float_arg_regs: (0..16).map(s).collect(),
            ret_int_reg: gp(0),
            ret_float_reg: s(0),
            // R0-R3 and R12 (IP, the intra-procedure-call scratch register) are call-clobbered; S0-S15 are the caller-saved half of the VFP file.
            caller_saved: (0..4)
                .map(gp)
                .chain(std::iter::once(gp(12)))
                .chain((0..16).map(s))
                .collect(),
            // R4-R11 are callee-saved (R9 is the platform register, callee-saved under the Linux base standard); S16-S31 are the callee-saved VFP half.
            callee_saved: (4..12).map(gp).chain((16..32).map(s)).collect(),
            // AAPCS requires the stack pointer to be 8-byte aligned at every public interface.
            stack_alignment: 8,
            red_zone_size: 0,
        }
    }

    pub fn is_64bit(&self) -> bool {
        matches!(self.arch, Arch::X86_64 | Arch::Aarch64)
    }

    /// The C data model of the target's toolchain.  Ask this, never
    /// `pointer_size`, for any question about the width of a C type: the two
    /// disagree on Windows x64, where a 64-bit pointer sits beside a 32-bit
    /// `long`.
    pub fn data_model(&self) -> DataModel {
        match (self.format, self.arch) {
            (BinaryFormat::Pe, Arch::X86_64) => DataModel::Llp64,
            (_, Arch::X86_64) | (_, Arch::Aarch64) => DataModel::Lp64,
            (_, Arch::X86_32) | (_, Arch::Arm32) => DataModel::Ilp32,
        }
    }

    /// The glibc object layouts for this target, or None where the recovered C
    /// will not be relinked against glibc at all.  A PE image shares the POSIX
    /// names through msvcrt but none of the layouts, so answering with the
    /// glibc table there would oversize every region it touches.
    pub fn libc_layout(&self) -> Option<LibcLayout> {
        if self.format != BinaryFormat::Elf {
            return None;
        }
        Some(LibcLayout {
            model: self.data_model(),
            arch: self.arch,
        })
    }

    /// Where the stack-protector cookie is read from, for the targets that keep
    /// it at a fixed offset from a segment base.  AArch64 and ARM reach theirs
    /// through the thread pointer with no fixed displacement a disassembly can
    /// match, so they name no slot rather than a wrong one.
    pub fn stack_guard_slot(&self) -> Option<StackGuardSlot> {
        match self.arch {
            Arch::X86_64 => Some(StackGuardSlot {
                segment: "FS",
                offset: 0x28,
            }),
            Arch::X86_32 => Some(StackGuardSlot {
                segment: "GS",
                offset: 0x14,
            }),
            Arch::Aarch64 | Arch::Arm32 => None,
        }
    }

    /// Windows x64 assigns integer and FP registers from the same four ordinal slots; SysV keeps independent GP and XMM sequences.
    pub fn uses_shared_arg_slots(&self) -> bool {
        self.format == BinaryFormat::Pe && self.arch == Arch::X86_64
    }

    /// True when int_arg_regs lists slots belonging to INDIVIDUAL functions rather than to the whole image: Windows x86-32's default cdecl passes nothing in registers and only a fastcall/thiscall function claims ECX/EDX, so register-argument questions must be asked per function.
    pub fn reg_args_are_per_function(&self) -> bool {
        self.format == BinaryFormat::Pe && self.arch == Arch::X86_32
    }

    pub fn first_stack_arg_position(&self) -> usize {
        if self.uses_shared_arg_slots() {
            4
        } else if self.reg_args_are_per_function() {
            // The image-wide default is cdecl, whose first argument is already on the stack.
            0
        } else {
            self.int_arg_regs.len()
        }
    }

    /// Offset from RSP immediately before CALL to the first stack argument.
    pub fn outgoing_stack_arg_base(&self) -> i64 {
        if self.uses_shared_arg_slots() {
            32
        } else {
            0
        }
    }

    /// Bytes the call instruction pushed below the incoming stack arguments: x86's CALL pushes the return address, while AArch64's BL and ARM's BL both leave it in the link register and push nothing.
    pub fn return_addr_stack_size(&self) -> i64 {
        match self.arch {
            Arch::Aarch64 | Arch::Arm32 => 0,
            _ => self.pointer_size as i64,
        }
    }

    /// Offset from the callee's entry SP to its first stack argument: past whatever the call pushed, plus Windows' shadow space.
    pub fn incoming_sp_stack_arg_base(&self) -> i64 {
        self.return_addr_stack_size() + self.outgoing_stack_arg_base()
    }

    /// Offset from the established frame pointer to the first stack argument (x86: incoming-SP base plus saved RBP; AArch64: 16 for the canonical stp x29,x30 frame record).
    pub fn incoming_bp_stack_arg_base(&self) -> i64 {
        match self.arch {
            // ARM32's push {fp,lr}; mov fp,sp frame record is the same two-slot shape as AArch64's stp x29,x30,[sp,#-16]!.
            Arch::Aarch64 | Arch::Arm32 => 2 * self.pointer_size as i64,
            _ => self.incoming_sp_stack_arg_base() + self.pointer_size as i64,
        }
    }
}

pub fn detect_abi(obj: &object::File) -> Result<AbiConfig, String> {
    use object::Object;

    let format = match obj.format() {
        object::BinaryFormat::Elf => BinaryFormat::Elf,
        object::BinaryFormat::Pe => BinaryFormat::Pe,
        object::BinaryFormat::MachO => BinaryFormat::MachO,
        _ => BinaryFormat::Unknown,
    };

    let arch = match obj.architecture() {
        object::Architecture::X86_64 => Arch::X86_64,
        object::Architecture::I386 => Arch::X86_32,
        object::Architecture::Aarch64 => Arch::Aarch64,
        object::Architecture::Arm => Arch::Arm32,
        other => return Err(format!("unsupported architecture {other:?}; manifold currently supports x86, aarch64 and arm32 binaries")),
    };

    // The ARM architectures are ELF-only for now: the PE .pdata RUNTIME_FUNCTION layout is x64-specific and there is no Mach-O metadata frontend. PE x86-32 and x86-64 are both supported, so there is deliberately no blanket "PE must be x86-64" test here.
    if matches!(arch, Arch::Aarch64 | Arch::Arm32) && format != BinaryFormat::Elf {
        return Err(format!(
            "unsupported {arch:?} target: only ELF images are supported, got {format:?}"
        ));
    }

    let mut config = match (format, arch) {
        (BinaryFormat::Pe, Arch::X86_64) => AbiConfig::win64(),
        (BinaryFormat::Pe, Arch::X86_32) => AbiConfig::win32_x86(),
        (_, Arch::X86_64) => AbiConfig::sysv_x86_64(),
        (_, Arch::X86_32) => AbiConfig::cdecl_x86_32(),
        (_, Arch::Aarch64) => AbiConfig::aapcs64(),
        (_, Arch::Arm32) => AbiConfig::aapcs32(),
    };

    config.format = format;
    Ok(config)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decorated_names_give_convention_and_arg_bytes() {
        let stdcall = parse_decorated_name("_StdFn@12").expect("stdcall decoration");
        assert_eq!(stdcall.conv, CallConv::Stdcall);
        assert_eq!(stdcall.arg_bytes, Some(12));
        assert_eq!(stdcall.undecorated, "StdFn");
        assert_eq!(stdcall.conv.register_arg_count(), 0);
        assert!(stdcall.conv.callee_cleans_stack());

        let fastcall = parse_decorated_name("@FastFn@12").expect("fastcall decoration");
        assert_eq!(fastcall.conv, CallConv::Fastcall);
        assert_eq!(fastcall.arg_bytes, Some(12));
        assert_eq!(fastcall.undecorated, "FastFn");
        assert_eq!(fastcall.conv.register_arg_count(), 2);

        // A plain name, with or without MSVC's cdecl underscore, carries no byte count.
        for raw in ["CdeclFn", "_CdeclFn"] {
            let cdecl = parse_decorated_name(raw).expect("cdecl decoration");
            assert_eq!(cdecl.conv, CallConv::Cdecl);
            assert_eq!(cdecl.arg_bytes, None);
            assert_eq!(cdecl.undecorated, "CdeclFn");
            assert!(!cdecl.conv.callee_cleans_stack());
        }

        // C++ mangling and malformed decorations are not this scheme.
        assert!(parse_decorated_name("?f@@YAXH@Z").is_none());
        assert!(parse_decorated_name("@FastFn").is_none());
        assert!(parse_decorated_name("_Std@notdigits").is_none());
        assert!(parse_decorated_name("").is_none());
    }

    #[test]
    fn evidenced_arg_slots_maps_bytes_to_argument_count() {
        // stdcall: the decoration counts all 12 bytes, and RET 12 pops exactly the same stack.
        let stdcall = FuncAbi {
            reg_arg_count: 0,
            callee_pop_bytes: Some(12),
            decorated_arg_bytes: Some(12),
        };
        assert_eq!(stdcall.evidenced_arg_slots(4), Some(3));

        // fastcall: RET 4 covers only the third argument, so the two register arguments are added back.
        let fastcall_ret_only = FuncAbi {
            reg_arg_count: 2,
            callee_pop_bytes: Some(4),
            decorated_arg_bytes: None,
        };
        assert_eq!(fastcall_ret_only.evidenced_arg_slots(4), Some(3));

        // The same function reached by its decorated name: @12 already counts ECX and EDX.
        let fastcall_decorated = FuncAbi {
            reg_arg_count: 2,
            callee_pop_bytes: Some(4),
            decorated_arg_bytes: Some(12),
        };
        assert_eq!(fastcall_decorated.evidenced_arg_slots(4), Some(3));

        // cdecl leaves no evidence at all: the caller cleans up, so there is no RET imm16.
        assert_eq!(FuncAbi::default().evidenced_arg_slots(4), None);
    }

    #[test]
    fn win32_x86_is_cdecl_by_default_with_per_function_register_slots() {
        let cfg = AbiConfig::win32_x86();
        assert_eq!(cfg.format, BinaryFormat::Pe);
        assert_eq!(cfg.arch, Arch::X86_32);
        assert_eq!(cfg.pointer_size, 4);
        assert!(cfg.reg_args_are_per_function());
        // cdecl: the first argument is on the stack even though ECX/EDX are listed for fastcall.
        assert_eq!(cfg.first_stack_arg_position(), 0);
        assert_eq!(cfg.int_arg_regs, vec![Mreg::CX, Mreg::DX]);
        // CALL pushes a 4-byte return address and there is no shadow space.
        assert_eq!(cfg.incoming_sp_stack_arg_base(), 4);
        assert_eq!(cfg.incoming_bp_stack_arg_base(), 8);
        assert_eq!(cfg.outgoing_stack_arg_base(), 0);
        assert!(!cfg.uses_shared_arg_slots());

        // i386 SysV keeps its own shape: no register slots at all.
        let elf = AbiConfig::cdecl_x86_32();
        assert!(!elf.reg_args_are_per_function());
        assert!(elf.int_arg_regs.is_empty());
        assert_eq!(elf.first_stack_arg_position(), 0);
    }

    /// The data model is NOT readable off the pointer width: Windows x64 pairs a
    /// 64-bit pointer with a 32-bit `long`, and a rule that inferred one from the
    /// other would silently mis-size every `long` in a PE image.
    #[test]
    fn data_model_is_not_the_pointer_width() {
        assert_eq!(AbiConfig::sysv_x86_64().data_model(), DataModel::Lp64);
        assert_eq!(AbiConfig::aapcs64().data_model(), DataModel::Lp64);
        assert_eq!(AbiConfig::cdecl_x86_32().data_model(), DataModel::Ilp32);
        assert_eq!(AbiConfig::aapcs32().data_model(), DataModel::Ilp32);

        let win64 = AbiConfig::win64();
        assert_eq!(win64.pointer_size, 8, "Windows x64 is a 64-bit pointer");
        assert_eq!(win64.data_model(), DataModel::Llp64);
        assert_eq!(win64.data_model().long_size(), 4, "but a 32-bit long");
        assert!(!win64.data_model().long_holds_64bit());
    }

    /// Every size here is `sizeof` measured with gcc against glibc 2.35,
    /// cross-compiled for the target.  They are the only evidence the pipeline
    /// has for how much an external callee writes through an out-parameter, so a
    /// drift here is a stack smash or a swallowed neighbouring local.
    ///
    /// The invariant the measurements established: the data model fixes every
    /// object EXCEPT `struct stat`, and i386 and arm32 agree with each other
    /// throughout.
    #[test]
    fn libc_object_sizes_match_the_measured_targets() {
        use LibcObject::*;
        let layout = |cfg: AbiConfig| cfg.libc_layout().expect("an ELF target has glibc layouts");

        for cfg in [AbiConfig::sysv_x86_64(), AbiConfig::aapcs64()] {
            let arch = cfg.arch;
            let l = layout(cfg);
            for (obj, want) in [
                (Statvfs, 112),
                (Statfs, 120),
                (Tm, 56),
                (Timeval, 16),
                (Rusage, 144),
                (Tms, 32),
                (Rlimit, 16),
                (Sigaction, 152),
                (Pointer, 8),
            ] {
                assert_eq!(l.size_of(obj), want, "{obj:?} on {arch:?}");
            }
        }

        for cfg in [AbiConfig::cdecl_x86_32(), AbiConfig::aapcs32()] {
            let arch = cfg.arch;
            let l = layout(cfg);
            for (obj, want) in [
                (Statvfs, 72),
                (Statfs, 64),
                (Tm, 44),
                (Timeval, 8),
                (Rusage, 72),
                (Tms, 16),
                (Rlimit, 8),
                (Sigaction, 140),
                (Pointer, 4),
            ] {
                assert_eq!(l.size_of(obj), want, "{obj:?} on {arch:?}");
            }
        }

        // Carry no word-sized field, so they do not move with the model.
        for cfg in [
            AbiConfig::sysv_x86_64(),
            AbiConfig::aapcs64(),
            AbiConfig::cdecl_x86_32(),
            AbiConfig::aapcs32(),
        ] {
            let arch = cfg.arch;
            let l = layout(cfg);
            for (obj, want) in [(Utsname, 390), (Sigset, 128), (Termios, 60)] {
                assert_eq!(l.size_of(obj), want, "{obj:?} on {arch:?}");
            }
        }

        // The one object the data model does NOT settle: aarch64 is LP64 like
        // x86-64 and still lays struct stat out 16 bytes smaller.
        assert_eq!(layout(AbiConfig::sysv_x86_64()).size_of(Stat), 144);
        assert_eq!(layout(AbiConfig::aapcs64()).size_of(Stat), 128);
        assert_eq!(layout(AbiConfig::cdecl_x86_32()).size_of(Stat), 88);
        assert_eq!(layout(AbiConfig::aapcs32()).size_of(Stat), 88);
    }

    /// msvcrt shares the POSIX names but none of the layouts, so a PE image must
    /// get no answer rather than glibc's.
    #[test]
    fn only_an_elf_target_has_glibc_layouts() {
        assert!(AbiConfig::sysv_x86_64().libc_layout().is_some());
        assert!(AbiConfig::win64().libc_layout().is_none());
        assert!(AbiConfig::win32_x86().libc_layout().is_none());
    }

    /// The stack cookie sits at a fixed segment offset only on x86; AArch64 and
    /// ARM reach theirs through the thread pointer, so naming a slot for them
    /// would match ordinary thread-local data.
    #[test]
    fn stack_guard_slot_is_x86_only() {
        let x64 = AbiConfig::sysv_x86_64()
            .stack_guard_slot()
            .expect("fs:0x28");
        assert_eq!((x64.segment, x64.offset), ("FS", 0x28));
        let x86 = AbiConfig::cdecl_x86_32()
            .stack_guard_slot()
            .expect("gs:0x14");
        assert_eq!((x86.segment, x86.offset), ("GS", 0x14));
        assert!(AbiConfig::aapcs64().stack_guard_slot().is_none());
        assert!(AbiConfig::aapcs32().stack_guard_slot().is_none());
    }
}
