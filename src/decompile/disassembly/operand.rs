
use std::sync::atomic::{AtomicUsize, Ordering};

// Global operand counter; starts at 1 because 0 means "no operand".
static NEXT_OP_ID: AtomicUsize = AtomicUsize::new(1);

// Allocate the next unique operand ID, returned as a leaked static string.
pub fn alloc_op_id() -> &'static str {
    let id = NEXT_OP_ID.fetch_add(1, Ordering::Relaxed);
    let s = id.to_string();
    Box::leak(s.into_boxed_str())
}

// Reset the operand counter (for use between test runs).
pub fn reset_op_counter() {
    NEXT_OP_ID.store(1, Ordering::Relaxed);
}

// Map a capstone register ID to the upper-case name matching ddisasm conventions.
pub fn capstone_reg_name(cs: &capstone::Capstone, reg_id: capstone::RegId) -> &'static str {
    let name = cs.reg_name(reg_id).unwrap_or_default().to_ascii_uppercase();
    Box::leak(name.into_boxed_str())
}

pub const NO_OP: &str = "0";
