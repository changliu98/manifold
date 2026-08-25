// Pipeline passes: each reverses one CompCert compilation stage (asm->mach->linear->ltl->rtl->cminor->csharpminor->clight->C).
pub mod aarch64_asm_pass;
pub mod abi_pass;
pub mod arm32_asm_pass;
pub mod asm_pass;
pub mod c_pass;
pub mod clight_emit_pass;
pub mod clight_pass;
pub mod clight_select;
pub mod cminor_pass;
pub mod csh_pass;
pub mod cshminor_pass;
pub mod linear_pass;
pub mod mach_pass;
pub mod pass;
pub mod rtl_dominator_pass;
pub mod rtl_optimize_pass;
pub mod rtl_pass;
