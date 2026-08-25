use csv;
use std::borrow::Borrow;

pub const DEFAULT_VAR: i64 = 775807;

pub fn leak<T: Borrow<TB> + 'static, TB: ?Sized>(x: T) -> &'static TB {
    let leaked: &'static T = Box::leak(Box::new(x));
    leaked.borrow()
}

/// Bit 62 marks an address as a synthetic IR node produced after a real address (e.g. arith_load/store fusion in rtl_pass emits the post-load op at this synthetic address). Used by passes that need to ignore the bit when consulting facts keyed by real addresses.
pub const SYNTH_NODE_BIT: u64 = 1u64 << 62;

/// Bit 63 marks the synth2 read-modify-write store node: the store half of an RMW emitted after both the real address and its synth1 use. Like SYNTH_NODE_BIT it must be masked off when consulting facts keyed by real addresses.
pub const SYNTH_NODE_BIT2: u64 = 1u64 << 63;

/// Marker for a semantic expansion with more than the two legacy synthetic
/// slots.  Bits 56..58 hold the explicit execution stage (1..7); bit 55 makes
/// the encoding distinguishable from real x86 addresses and unrelated value
/// namespaces.  Control flow still comes from CFG edges -- this encoding is
/// only an identity/order key for consumers that store nodes in sorted maps.
pub const MULTI_SYNTH_NODE_BIT: u64 = 1u64 << 55;
pub const MULTI_SYNTH_STAGE_SHIFT: u32 = 56;
pub const MULTI_SYNTH_STAGE_MASK: u64 = 7u64 << MULTI_SYNTH_STAGE_SHIFT;
pub const MULTI_SYNTH_NODE_MASK: u64 = MULTI_SYNTH_NODE_BIT | MULTI_SYNTH_STAGE_MASK;
/// Multi-stage node and value encodings reserve bits starting at bit 55 and
/// shift the originating address by eight bits.  Restrict admission to the
/// ordinary 48-bit x86 user-address domain so neither operation can erase or
/// overlap an address bit.  This is an identity-encoding bound, never a
/// reachability or dataflow comparison.
pub const MULTI_SYNTH_ADDRESS_LIMIT: u64 = 1u64 << 48;

#[inline]
pub fn multi_synth_address_is_encodable(address: u64) -> bool {
    address < MULTI_SYNTH_ADDRESS_LIMIT
}

#[inline]
pub fn multi_synth_stage(node: u64) -> Option<u64> {
    (node & MULTI_SYNTH_NODE_BIT != 0)
        .then_some((node & MULTI_SYNTH_STAGE_MASK) >> MULTI_SYNTH_STAGE_SHIFT)
        .filter(|stage| *stage != 0)
}

#[inline]
pub fn semantic_node_address(node: u64) -> u64 {
    let mut base = node & !(SYNTH_NODE_BIT | SYNTH_NODE_BIT2);
    if multi_synth_stage(node).is_some() {
        base &= !MULTI_SYNTH_NODE_MASK;
    }
    base
}

#[inline]
pub fn is_synthetic_node(node: u64) -> bool {
    node & (SYNTH_NODE_BIT | SYNTH_NODE_BIT2) != 0 || multi_synth_stage(node).is_some()
}

/// Map a Node address to an execution-order key.  A real instruction and all
/// valid combinations of its seven multi-stage and two legacy synthetic tags
/// remain unique, adjacent, and strictly before the next real address.  This
/// is presentation order only; reachability always comes from explicit CFG
/// edges.
#[inline]
pub fn exec_order_key(node: u64) -> u128 {
    let base = semantic_node_address(node) as u128;
    let stage = multi_synth_stage(node).unwrap_or(0) as u128;
    let legacy = match (node & SYNTH_NODE_BIT != 0, node & SYNTH_NODE_BIT2 != 0) {
        (false, false) => 0u128,
        (true, false) => 1,
        (false, true) => 2,
        (true, true) => 3,
    };
    let rank = if legacy == 0 {
        stage
    } else {
        8 + (legacy - 1) * 8 + stage
    };
    base * 32 + rank
}

/// Parse CSV data from an embedded string (compile-time `include_str!`).
pub fn parse_csv_str<T>(data: &'static str, delimiter: u8) -> Vec<T>
where
    for<'de> T: serde::de::Deserialize<'de> + 'static,
{
    let mut builder = csv::ReaderBuilder::new();
    builder.delimiter(delimiter);
    builder.has_headers(false);
    builder.double_quote(false);
    builder.quoting(false);

    let reader = builder.from_reader(data.as_bytes());
    reader.into_deserialize().filter_map(|x| x.ok()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multi_stage_nodes_keep_origin_and_semantic_order() {
        let base = 0x401177;
        let next = base + 1;
        let stages: Vec<u64> = (1u64..=7)
            .map(|stage| base | MULTI_SYNTH_NODE_BIT | (stage << MULTI_SYNTH_STAGE_SHIFT))
            .collect();

        assert!(stages.iter().all(|node| is_synthetic_node(*node)));
        assert!(stages
            .iter()
            .all(|node| semantic_node_address(*node) == base));
        assert!(stages
            .windows(2)
            .all(|pair| exec_order_key(pair[0]) < exec_order_key(pair[1])));
        assert!(exec_order_key(base) < exec_order_key(stages[0]));
        assert!(exec_order_key(*stages.last().unwrap()) < exec_order_key(next));
    }

    #[test]
    fn legacy_synth_order_remains_between_base_and_next() {
        let base = 0x1000;
        assert!(exec_order_key(base) < exec_order_key(base | SYNTH_NODE_BIT));
        assert!(exec_order_key(base | SYNTH_NODE_BIT) < exec_order_key(base | SYNTH_NODE_BIT2));
        assert!(
            exec_order_key(base | SYNTH_NODE_BIT2)
                < exec_order_key(base | SYNTH_NODE_BIT | SYNTH_NODE_BIT2)
        );
        assert!(exec_order_key(base | SYNTH_NODE_BIT | SYNTH_NODE_BIT2) < exec_order_key(base + 1));
        assert!(exec_order_key(base | SYNTH_NODE_BIT2) < exec_order_key(base + 1));
    }

    #[test]
    fn composite_synthetic_order_keys_are_injective() {
        let base = 0x2000;
        let stage = base | MULTI_SYNTH_NODE_BIT | (3 << MULTI_SYNTH_STAGE_SHIFT);
        let nodes = [
            base,
            stage,
            base | SYNTH_NODE_BIT,
            stage | SYNTH_NODE_BIT,
            base | SYNTH_NODE_BIT2,
            stage | SYNTH_NODE_BIT2,
            base | SYNTH_NODE_BIT | SYNTH_NODE_BIT2,
            stage | SYNTH_NODE_BIT | SYNTH_NODE_BIT2,
        ];
        let keys: std::collections::BTreeSet<_> = nodes.into_iter().map(exec_order_key).collect();
        assert_eq!(keys.len(), nodes.len());
    }

    #[test]
    fn multi_stage_encoding_rejects_addresses_that_occupy_reserved_bits() {
        let safe = MULTI_SYNTH_ADDRESS_LIMIT - 1;
        let unsafe_address = MULTI_SYNTH_NODE_BIT | 0x1234;
        assert!(multi_synth_address_is_encodable(safe));
        assert!(!multi_synth_address_is_encodable(unsafe_address));

        let encoded = unsafe_address | MULTI_SYNTH_NODE_BIT | (1u64 << MULTI_SYNTH_STAGE_SHIFT);
        assert_ne!(semantic_node_address(encoded), unsafe_address);
    }
}
