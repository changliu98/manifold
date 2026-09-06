//! Reify an observed frame-cell read before scalar RTL optimization.
//!
//! Reverse Stacking initially represents reloads as copies of slot locals.
//! Once storage ownership is known, the cell's value is not its address. This
//! normalization consumes the completed RTL facts (avoiding a negation cycle
//! through escape/call analysis), and runs before copy propagation can erase
//! the physical read. No reaching writer or initial value is invented.

use crate::decompile::elevator::DecompileDB;
use crate::x86::op::{Addressing, Operation};
use crate::x86::types::*;
use ascent::ascent;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::Arc;

fn chunk(typ: &Typ, mnemonic: &str, width: usize) -> Option<MemoryChunk> {
    // Typ alone does not preserve a narrow load's signedness. Only reify the
    // decoder transfer forms whose extension/encoding is modeled here; other
    // ISA operations retain their ordinary pipeline interpretation.
    if !matches!(
        mnemonic,
        "MOV" | "MOVABS" | "MOVSX" | "MOVSXD" | "MOVZX" | "MOVSS" | "MOVSD" | "VMOVSS" | "VMOVSD"
    ) {
        return None;
    }
    match (typ, width) {
        (Typ::Tfloat, 8) => return Some(MemoryChunk::MFloat64),
        (Typ::Tsingle, 4) => return Some(MemoryChunk::MFloat32),
        (Typ::Tfloat | Typ::Tsingle, _) => return None,
        _ => {}
    }
    if matches!(mnemonic, "MOVSX" | "MOVSXD" | "MOVZX") {
        return super::rtl_pass::extending_load_chunk(mnemonic, width);
    }
    match width {
        1 => Some(MemoryChunk::MInt8Unsigned),
        2 => Some(MemoryChunk::MInt16Unsigned),
        4 => Some(MemoryChunk::MAny32),
        8 => Some(MemoryChunk::MAny64),
        _ => None,
    }
}

ascent! {
    struct ReloadViews;
    relation candidate(Node, RTLInst);
    relation reload(Node, i64, Typ);
    relation mnemonic(Node, Symbol);
    relation read(Address, Node, i64, usize);
    relation slot(Address, Node, i64, RTLReg);
    relation owner(Address, Node, i64, i64, RTLReg);

    relation ambiguous_read(Node);
    ambiguous_read(*node) <-- read(_, node, a, aw), read(_, node, b, bw), if (a, aw) != (b, bw);
    relation ambiguous_owner(Node);
    ambiguous_owner(*node) <--
        owner(af, node, ao, ab, ar), owner(bf, node, bo, bb, br),
        if (af, ao, ab, ar) != (bf, bo, bb, br);

    relation view(Address, Node, i64, i64, RTLReg, MemoryChunk);
    view(*func, *node, *offset, *base, *root, access) <--
        reload(node, offset, typ), mnemonic(node, mnemonic),
        read(func, node, offset, width), owner(func, node, offset, base, root),
        !ambiguous_read(node), !ambiguous_owner(node),
        if let Some(access) = chunk(typ, mnemonic, *width);

    relation replacement(Node, RTLInst, RTLInst, Address, i64, i64, RTLReg);
    replacement(*node, old.clone(), new, *func, *offset, *base, *root) <--
        candidate(node, old),
        if let RTLInst::Iop(Operation::Omove, args, destination) = old,
        if args.len() == 1,
        view(func, node, offset, base, root, access),
        slot(func, node, offset, local), if args[0] == *local,
        // The loaded value needs its own SSA definition. A storage-identity
        // collision is unsupported, not a license to store an address/value
        // back into the allocation's own name.
        if destination != local && destination != root,
        let new = RTLInst::Iload(*access, Addressing::Ainstack(*offset), Arc::new(vec![]), *destination);
}

pub(super) fn normalize(db: &mut DecompileDB) -> usize {
    let mut program = ReloadViews::default();
    program.candidate.extend(
        db.rel_iter::<(Node, RTLInst)>("rtl_inst_candidate")
            .cloned(),
    );
    program.reload.extend(
        db.rel_iter::<(Node, LTLInst)>("ltl_inst")
            .filter_map(|(node, inst)| {
                if let LTLInst::Lgetstack(_, offset, typ, _) = inst {
                    Some((*node, *offset, *typ))
                } else {
                    None
                }
            }),
    );
    program.mnemonic.extend(
        db.rel_iter::<(
            Address,
            usize,
            Symbol,
            Symbol,
            Symbol,
            Symbol,
            Symbol,
            Symbol,
            usize,
            usize,
        )>("instruction")
            .map(|row| (row.0, row.3)),
    );
    program.read.extend(
        db.rel_iter::<(Address, Node, i64, usize)>("frame_stack_read_bytes")
            .copied(),
    );
    program.slot.extend(
        db.rel_iter::<(Address, Node, i64, RTLReg)>("stack_var")
            .copied(),
    );
    program.owner.extend(
        db.rel_iter::<(Address, Node, i64, i64, RTLReg)>("frame_read_storage_owner")
            .copied(),
    );
    program.run();
    let mut choices: HashMap<(Node, RTLInst), HashSet<(RTLInst, Address, i64, i64, RTLReg)>> =
        HashMap::new();
    for (node, old, new, func, offset, base, root) in program.replacement {
        choices
            .entry((node, old))
            .or_default()
            .insert((new, func, offset, base, root));
    }
    let mut sites = BTreeSet::new();
    let mut count = 0;
    let rewritten: ascent::boxcar::Vec<_> = db
        .rel_iter::<(Node, RTLInst)>("rtl_inst_candidate")
        .map(|row| {
            if let Some(choices) = choices.get(row).filter(|c| c.len() == 1) {
                let (new, func, offset, base, root) = choices.iter().next().unwrap();
                sites.insert((*func, row.0, *offset, *base, *root));
                count += 1;
                (row.0, new.clone())
            } else {
                row.clone()
            }
        })
        .collect();
    db.rel_set("rtl_inst_candidate", rewritten);
    for site in sites {
        if !db
            .rel_iter::<(Address, Node, i64, i64, RTLReg)>("frame_read_storage_access_owner")
            .any(|old| *old == site)
        {
            db.rel_push("frame_read_storage_access_owner", site);
        }
    }
    if count > 0 {
        eprintln!("[storage-reads] reified-reloads={count}");
    }
    count
}

#[cfg(test)]
mod tests {
    use super::super::pass::IRPass;
    use super::*;
    use crate::mreg::Mreg;

    fn fixture() -> DecompileDB {
        let mut db = DecompileDB::default();
        db.rel_push(
            "rtl_inst_candidate",
            (
                20_u64,
                RTLInst::Iop(Operation::Omove, Arc::new(vec![90]), 91),
            ),
        );
        db.rel_push(
            "ltl_inst",
            (
                20_u64,
                LTLInst::Lgetstack(Slot::Local, 8, Typ::Tany64, Mreg::DI),
            ),
        );
        db.rel_push(
            "instruction",
            (20_u64, 4_usize, "", "MOV", "", "", "", "", 0_usize, 0_usize),
        );
        db.rel_push("frame_stack_read_bytes", (1_u64, 20_u64, 8_i64, 8_usize));
        db.rel_push("stack_var", (1_u64, 20_u64, 8_i64, 90_u64));
        db.rel_push(
            "frame_read_storage_owner",
            (1_u64, 20_u64, 8_i64, 8_i64, 90_u64),
        );
        db
    }

    #[test]
    fn full_width_base_reload_is_a_value_not_the_cell_address() {
        let mut db = fixture();
        assert_eq!(normalize(&mut db), 1);
        assert!(db.rel_iter::<(Node, RTLInst)>("rtl_inst_candidate").any(|(node, inst)|
            *node == 20 && matches!(inst, RTLInst::Iload(MemoryChunk::MAny64, Addressing::Ainstack(8), args, 91) if args.is_empty())));
        assert!(db
            .rel_iter::<(Address, Node, i64, i64, RTLReg)>("frame_read_storage_access_owner")
            .any(|row| *row == (1, 20, 8, 8, 90)));
        assert_eq!(normalize(&mut db), 0);
    }

    #[test]
    fn conflicting_owners_and_widths_do_not_authorize_reloads() {
        let mut width = fixture();
        width.rel_push("frame_stack_read_bytes", (1_u64, 20_u64, 8_i64, 4_usize));
        assert_eq!(normalize(&mut width), 0);
        let mut owner = fixture();
        owner.rel_push(
            "frame_read_storage_owner",
            (1_u64, 20_u64, 8_i64, 0_i64, 99_u64),
        );
        assert_eq!(normalize(&mut owner), 0);
    }

    #[test]
    fn unrelated_values_and_storage_identity_collisions_remain_unchanged() {
        for (source, destination) in [(99, 91), (90, 90)] {
            let mut db = fixture();
            let original = (
                20,
                RTLInst::Iop(Operation::Omove, Arc::new(vec![source]), destination),
            );
            db.rel_set(
                "rtl_inst_candidate",
                [original.clone()]
                    .into_iter()
                    .collect::<ascent::boxcar::Vec<(Node, RTLInst)>>(),
            );
            assert_eq!(normalize(&mut db), 0);
            assert!(db
                .rel_iter::<(Node, RTLInst)>("rtl_inst_candidate")
                .any(|row| *row == original));
        }
    }

    #[test]
    fn reload_chunks_preserve_extensions_and_floating_encodings() {
        assert_eq!(
            chunk(&Typ::Tint, "MOVSX", 1),
            Some(MemoryChunk::MInt8Signed)
        );
        assert_eq!(
            chunk(&Typ::Tint, "MOVZX", 2),
            Some(MemoryChunk::MInt16Unsigned)
        );
        assert_eq!(chunk(&Typ::Tfloat, "MOVSD", 8), Some(MemoryChunk::MFloat64));
        assert_eq!(
            chunk(&Typ::Tsingle, "MOVSS", 4),
            Some(MemoryChunk::MFloat32)
        );
        assert_eq!(chunk(&Typ::Tfloat, "MOVSD", 4), None);
        assert_eq!(chunk(&Typ::Tint, "LDRSB", 1), None);
        assert_eq!(chunk(&Typ::Tany64, "UNMODELED_LOAD", 8), None);
    }

    #[test]
    fn reload_normalization_declares_all_scheduler_reads_and_writes() {
        let pass = super::super::rtl_optimize_pass::RTLOptimizePass;
        for name in [
            "rtl_inst_candidate",
            "ltl_inst",
            "instruction",
            "frame_stack_read_bytes",
            "stack_var",
            "frame_read_storage_owner",
            "frame_read_storage_access_owner",
        ] {
            assert!(
                pass.inputs().contains(&name) || pass.extra_reads().contains(&name),
                "{name}"
            );
        }
        assert!(pass.outputs().contains(&"frame_read_storage_access_owner"));
    }
}
