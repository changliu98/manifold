//! Check a lowered memory capture against raw addressing and independent
//! frame/SSA facts, not against the address proposed by the lowering rule.
use crate::decompile::elevator::DecompileDB;
use crate::mreg::Mreg;
use crate::x86::{op::Addressing, types::*};

pub(crate) const INPUTS: &[&str] = &[
    "op_indirect",
    "instruction",
    "effect_capture",
    "reg_rtl",
    "frame_stack_read_bytes",
    "func_stacksz",
    "effect_frame_address_value",
    "xtl_canonical",
    "rtl_effect_value_alias",
    "settled_bp_frame_base",
];

pub(crate) fn matches(
    db: &DecompileDB,
    function: Address,
    node: Node,
    width: usize,
    inst: &RTLInst,
) -> bool {
    let RTLInst::Iload(chunk, address, args, _) = inst else {
        return false;
    };
    if crate::decompile::analysis::struct_recovery_pass::chunk_byte_size(chunk) != width {
        return false;
    }
    let memories: std::collections::BTreeSet<_> = db
        .rel_iter::<(Node, Symbol, usize)>("effect_capture")
        .filter_map(|&(n, m, w)| (n == node && w == width).then_some(m))
        .collect();
    if memories.len() != 1 {
        return false;
    }
    let memory = *memories.first().unwrap();
    let raw: Vec<_> = db
        .rel_iter::<(Symbol, Symbol, Symbol, Symbol, i64, i64, usize)>("op_indirect")
        .filter(|r| r.0 == memory)
        .collect();
    if raw.len() != 1 {
        return false;
    }
    let &(_, segment, base, index, scale, disp, decoded_width) = raw[0];
    if decoded_width != width || !(segment == "NONE" || segment.is_empty()) {
        return false;
    }
    let no_index = index == "NONE" || index.is_empty();
    let bp_frame = base == "RBP"
        && no_index
        && db
            .rel_iter::<(Address, Node, i64)>("settled_bp_frame_base")
            .any(|&(f, n, _)| f == function && n == node);
    if bp_frame && args.is_empty() && *address == Addressing::Ainstack(disp) {
        return true;
    }
    if base == "RIP" && no_index {
        let sizes: std::collections::BTreeSet<_> = db
            .rel_iter::<(
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
            .filter_map(|r| (r.0 == node).then_some(r.1))
            .collect();
        return sizes.len() == 1
            && args.is_empty()
            && *address
                == Addressing::Aglobal(
                    (node as i64)
                        .wrapping_add(*sizes.first().unwrap() as i64)
                        .wrapping_add(disp) as Ident,
                    0,
                );
    }
    let value = |name: &str, reg: RTLReg| {
        db.rel_iter::<(Node, Mreg, RTLReg)>("reg_rtl")
            .any(|&(n, m, r)| {
                n == node && m == Mreg::x86(name) && same_value(db, function, node, r, reg)
            })
    };
    let register_ok = |name: &str| {
        name == "NONE"
            || name.is_empty()
            || crate::decompile::passes::machine_storage_pass::register_bits(name) == Some(64)
    };
    if !register_ok(base) || !register_ok(index) {
        return false;
    }
    if base != "RSP"
        && no_index
        && args.len() == 1
        && *address == Addressing::Aindexed(disp)
        && value(base, args[0])
    {
        return true;
    }
    if base != "RSP"
        && !no_index
        && args.len() == 2
        && value(base, args[0])
        && value(index, args[1])
    {
        if *address == Addressing::Aindexed2scaled(scale, disp)
            || (scale == 1 && *address == Addressing::Aindexed2(disp))
        {
            return true;
        }
    }
    // Frame coordinate conventions are physical geometry, never reachability.
    let frames: std::collections::BTreeSet<_> = db
        .rel_iter::<(Address, Address, Symbol, u64)>("func_stacksz")
        .filter_map(|&(f, _, _, s)| (f == function).then(|| i64::try_from(s).ok()).flatten())
        .collect();
    if frames.len() != 1 {
        return false;
    }
    let frame = *frames.first().unwrap();
    let coordinate = |offset: i64| {
        if offset < 0 {
            offset.checked_add(frame)
        } else {
            Some(offset)
        }
    };
    let actual = match (address, args.as_slice()) {
        (Addressing::Ainstack(offset), []) => coordinate(*offset),
        (Addressing::Aindexed(delta), [root]) => {
            let roots: std::collections::BTreeSet<_> = db
                .rel_iter::<(Address, Node, i64, RTLReg)>("effect_frame_address_value")
                .filter_map(|&(f, _, offset, value)| {
                    (f == function
                        && (same_value(db, function, node, value, *root)
                            || db
                                .rel_iter::<(RTLReg, RTLReg)>("xtl_canonical")
                                .any(|&(a, b)| {
                                    a == value && same_value(db, function, node, b, *root)
                                })))
                    .then(|| offset.checked_add(*delta).and_then(coordinate))
                    .flatten()
                })
                .collect();
            (roots.len() == 1).then(|| *roots.first().unwrap())
        }
        _ => None,
    };
    actual.is_some_and(|actual| {
        (bp_frame && coordinate(disp) == Some(actual))
            || db
                .rel_iter::<(Address, Node, i64, usize)>("frame_stack_read_bytes")
                .any(|&(f, n, offset, w)| {
                    f == function && n == node && w == width && coordinate(offset) == Some(actual)
                })
    })
}

fn same_value(
    db: &DecompileDB,
    function: Address,
    node: Node,
    original: RTLReg,
    current: RTLReg,
) -> bool {
    original == current
        || db
            .rel_iter::<(Address, Node, RTLReg, RTLReg)>("rtl_effect_value_alias")
            .any(|&(f, n, a, b)| (f, n, a, b) == (function, node, original, current))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn bp_frame_capture_requires_a_settled_base_at_that_use() {
        let mut db = DecompileDB::default();
        db.rel_push("effect_capture", (50_u64, "memory" as Symbol, 4_usize));
        db.rel_push(
            "op_indirect",
            (
                "memory" as Symbol,
                "NONE" as Symbol,
                "RBP" as Symbol,
                "NONE" as Symbol,
                1_i64,
                -20_i64,
                4_usize,
            ),
        );
        let load = RTLInst::Iload(
            MemoryChunk::MInt32,
            Addressing::Ainstack(-20),
            Arc::new(vec![]),
            3,
        );
        assert!(!matches(&db, 1, 50, 4, &load));
        db.rel_push("settled_bp_frame_base", (1_u64, 49_u64, -8_i64));
        assert!(!matches(&db, 1, 50, 4, &load));
        db.rel_push("settled_bp_frame_base", (1_u64, 50_u64, -8_i64));
        assert!(matches(&db, 1, 50, 4, &load));
        let wrong = RTLInst::Iload(
            MemoryChunk::MInt32,
            Addressing::Ainstack(-16),
            Arc::new(vec![]),
            3,
        );
        assert!(!matches(&db, 1, 50, 4, &wrong));
    }

    #[test]
    fn capture_checks_decoded_width_address_and_reaching_value() {
        let mut db = DecompileDB::default();
        let node = 50_u64;
        db.rel_push("effect_capture", (node, "memory" as Symbol, 1_usize));
        db.rel_push(
            "op_indirect",
            (
                "memory" as Symbol,
                "NONE" as Symbol,
                "RDI" as Symbol,
                "RSI" as Symbol,
                4_i64,
                7_i64,
                1_usize,
            ),
        );
        db.rel_push("reg_rtl", (node, Mreg::x86("RDI"), 11_u64));
        db.rel_push("reg_rtl", (node, Mreg::x86("RSI"), 12_u64));
        let load = |chunk, scale, offset, args| {
            RTLInst::Iload(
                chunk,
                Addressing::Aindexed2scaled(scale, offset),
                Arc::new(args),
                13,
            )
        };
        assert!(matches(
            &db,
            1,
            node,
            1,
            &load(MemoryChunk::MInt8Unsigned, 4, 7, vec![11, 12])
        ));
        for wrong in [
            load(MemoryChunk::MInt32, 4, 7, vec![11, 12]),
            load(MemoryChunk::MInt8Unsigned, 4, 8, vec![11, 12]),
            load(MemoryChunk::MInt8Unsigned, 2, 7, vec![11, 12]),
            load(MemoryChunk::MInt8Unsigned, 4, 7, vec![12, 11]),
        ] {
            assert!(!matches(&db, 1, node, 1, &wrong));
        }
        let renamed = load(MemoryChunk::MInt8Unsigned, 4, 7, vec![21, 12]);
        db.rel_push("rtl_effect_value_alias", (1_u64, node + 1, 11_u64, 21_u64));
        db.rel_push("rtl_effect_value_alias", (2_u64, node, 11_u64, 21_u64));
        assert!(
            !matches(&db, 1, node, 1, &renamed),
            "another point or owner cannot donate an equality"
        );
        db.rel_push("rtl_effect_value_alias", (1_u64, node, 11_u64, 21_u64));
        assert!(matches(&db, 1, node, 1, &renamed));
        db.rel_set(
            "op_indirect",
            vec![(
                "memory" as Symbol,
                "FS" as Symbol,
                "RDI" as Symbol,
                "RSI" as Symbol,
                4_i64,
                7_i64,
                1_usize,
            )]
            .into_iter()
            .collect::<ascent::boxcar::Vec<_>>(),
        );
        assert!(!matches(
            &db,
            1,
            node,
            1,
            &load(MemoryChunk::MInt8Unsigned, 4, 7, vec![11, 12])
        ));
    }
}
