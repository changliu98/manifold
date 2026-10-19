//! Shared conversion for the two existing stack-coordinate conventions.
//!
//! Negative frame-pointer displacements and post-allocation coordinates have
//! an affine translation fixed by the frame setup/allocation facts. Observed
//! object extents (including red-zone storage) must never move that origin.

use crate::decompile::elevator::DecompileDB;
use crate::x86::types::{Address, Node, Symbol};
use std::collections::{BTreeMap, BTreeSet};

#[cfg(test)]
pub(crate) const INPUTS: &[&str] = &["instr_in_function", "stack_base_move", "func_stacksz"];

#[derive(Default)]
pub(crate) struct FrameCoordinates {
    framed: BTreeSet<Address>,
    allocations: BTreeMap<Address, BTreeSet<i64>>,
}

impl FrameCoordinates {
    pub(crate) fn collect(db: &DecompileDB) -> Self {
        let mut owners = BTreeMap::<Node, BTreeSet<Address>>::new();
        for &(node, owner) in db.rel_iter::<(Node, Address)>("instr_in_function") {
            owners.entry(node).or_default().insert(owner);
        }
        let mut result = Self::default();
        for &(node, from, to) in db.rel_iter::<(Node, Symbol, Symbol)>("stack_base_move") {
            if from == "RSP" && to == "RBP" {
                if let Some(owners) = owners.get(&node).filter(|owners| owners.len() == 1) {
                    result.framed.extend(owners);
                }
            }
        }
        for &(owner, _, _, size) in db.rel_iter::<(Address, Address, Symbol, u64)>("func_stacksz") {
            if let Ok(size) = i64::try_from(size) {
                result.allocations.entry(owner).or_default().insert(size);
            }
        }
        result
    }

    pub(crate) fn allocation(&self, function: Address) -> Option<i64> {
        let sizes = self.allocations.get(&function)?;
        (sizes.len() == 1).then(|| *sizes.first().unwrap())
    }

    pub(crate) fn origin(&self, function: Address) -> Option<i64> {
        self.framed
            .contains(&function)
            .then(|| self.allocation(function))
            .flatten()
    }

    /// Convert a start, then add the extent in that same coordinate system.
    /// A red-zone object may have a negative result; that is not an error.
    pub(crate) fn start(&self, function: Address, offset: i64) -> Option<i64> {
        if offset < 0 && self.framed.contains(&function) {
            offset.checked_add(self.origin(function)?)
        } else {
            Some(offset)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn storage_depth_does_not_change_frame_origin() {
        let mut db = DecompileDB::default();
        db.rel_push("instr_in_function", (10_u64, 1_u64));
        db.rel_push("stack_base_move", (10_u64, "RSP", "RBP"));
        db.rel_push("func_stacksz", (1_u64, 100_u64, "frame", 168_u64));
        db.rel_push("stack_var", (1_u64, 20_u64, -176_i64, 3_u64));
        let frame = FrameCoordinates::collect(&db);
        assert_eq!(frame.origin(1), Some(168));
        assert_eq!(frame.start(1, -160), Some(8));
        assert_eq!(frame.start(1, 8), Some(8));
        assert_eq!(frame.start(1, -176), Some(-8));
    }

    #[test]
    fn ambiguous_allocations_never_select_the_largest_origin() {
        let mut db = DecompileDB::default();
        db.rel_push("instr_in_function", (10_u64, 1_u64));
        db.rel_push("stack_base_move", (10_u64, "RSP", "RBP"));
        for size in [32_u64, 64] {
            db.rel_push("func_stacksz", (1_u64, 100_u64, "frame", size));
        }
        let frame = FrameCoordinates::collect(&db);
        assert_eq!(frame.origin(1), None);
        assert_eq!(frame.start(1, -16), None);
        assert_eq!(frame.start(1, 16), Some(16));
    }
}
