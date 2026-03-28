

use std::sync::OnceLock;
use super::mach::Mreg;


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

    #[allow(dead_code)]
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
            int_arg_regs: vec![
                Mreg::DI, Mreg::SI, Mreg::DX, Mreg::CX, Mreg::R8, Mreg::R9,
            ],
            float_arg_regs: vec![
                Mreg::X0, Mreg::X1, Mreg::X2, Mreg::X3,
                Mreg::X4, Mreg::X5, Mreg::X6, Mreg::X7,
            ],
            ret_int_reg: Mreg::AX,
            ret_float_reg: Mreg::X0,
            caller_saved: vec![
                Mreg::AX, Mreg::CX, Mreg::DX,
                Mreg::SI, Mreg::DI,
                Mreg::R8, Mreg::R9, Mreg::R10, Mreg::R11,
                Mreg::X0, Mreg::X1, Mreg::X2, Mreg::X3,
                Mreg::X4, Mreg::X5, Mreg::X6, Mreg::X7,
                Mreg::X8, Mreg::X9, Mreg::X10, Mreg::X11,
                Mreg::X12, Mreg::X13, Mreg::X14, Mreg::X15,
            ],
            callee_saved: vec![
                Mreg::BX, Mreg::BP,
                Mreg::R12, Mreg::R13, Mreg::R14, Mreg::R15,
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
                Mreg::AX, Mreg::CX, Mreg::DX,
                Mreg::R8, Mreg::R9, Mreg::R10, Mreg::R11,
                Mreg::X0, Mreg::X1, Mreg::X2, Mreg::X3,
                Mreg::X4, Mreg::X5,
            ],
            callee_saved: vec![
                Mreg::BX, Mreg::BP,
                Mreg::SI, Mreg::DI,
                Mreg::R12, Mreg::R13, Mreg::R14, Mreg::R15,
                Mreg::X6, Mreg::X7, Mreg::X8, Mreg::X9,
                Mreg::X10, Mreg::X11, Mreg::X12, Mreg::X13,
                Mreg::X14, Mreg::X15,
            ],
            stack_alignment: 16,
            red_zone_size: 0,
        }
    }

    pub fn cdecl_x86_32() -> Self {
        Self {
            format: BinaryFormat::Elf,
            arch: Arch::X86_32,
            pointer_size: 4,
            int_arg_regs: vec![],
            float_arg_regs: vec![],
            ret_int_reg: Mreg::AX,
            ret_float_reg: Mreg::FP0,
            caller_saved: vec![
                Mreg::AX, Mreg::CX, Mreg::DX,
            ],
            callee_saved: vec![
                Mreg::BX, Mreg::BP, Mreg::SI, Mreg::DI,
            ],
            stack_alignment: 4,
            red_zone_size: 0,
        }
    }

    pub fn is_64bit(&self) -> bool {
        matches!(self.arch, Arch::X86_64)
    }
}


static ABI_CONFIG: OnceLock<AbiConfig> = OnceLock::new();

pub fn init_abi_config(config: AbiConfig) {
    ABI_CONFIG.set(config).expect("ABI config already initialized");
}

pub fn abi_config() -> &'static AbiConfig {
    ABI_CONFIG.get().expect("ABI config not initialized; call init_abi_config() first")
}

pub fn abi_config_initialized() -> bool {
    ABI_CONFIG.get().is_some()
}

#[allow(dead_code)]
pub fn ensure_abi_config_for_test() {
    let _ = ABI_CONFIG.set(AbiConfig::sysv_x86_64());
}


pub fn detect_abi(obj: &object::File) -> AbiConfig {
    use object::Object;

    let format = match obj.format() {
        object::BinaryFormat::Elf => BinaryFormat::Elf,
        object::BinaryFormat::Pe => BinaryFormat::Pe,
        object::BinaryFormat::MachO => BinaryFormat::MachO,
        _ => BinaryFormat::Unknown,
    };

    let is_64 = obj.is_64();

    let mut config = match (format, is_64) {
        (BinaryFormat::Pe, true) => AbiConfig::win64(),
        (_, true) => AbiConfig::sysv_x86_64(),
        (_, false) => AbiConfig::cdecl_x86_32(),
    };

    config.format = format;
    config
}
