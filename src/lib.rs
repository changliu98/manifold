// Ascent's generated rule code clones through references, which these two lints flag at
// nearly every rule.
#![allow(suspicious_double_ref_op, noop_method_call)]
pub mod aarch64;
pub mod abi;
pub mod arm32;
pub mod debug;
pub mod decompile;
pub mod mreg;
pub mod util;
pub mod x86;
