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

/// Map a Node address to an execution-order key: base*3 + rank keeps a real address and its two synth nodes adjacent and strictly between their base and the next real address, in u128.
#[inline]
pub fn exec_order_key(node: u64) -> u128 {
    let base = (node & !(SYNTH_NODE_BIT | SYNTH_NODE_BIT2)) as u128;
    let rank: u128 = if node & SYNTH_NODE_BIT2 != 0 {
        2
    } else if node & SYNTH_NODE_BIT != 0 {
        1
    } else {
        0
    };
    base * 3 + rank
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
