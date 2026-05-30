
use csv;
use std::borrow::Borrow;

pub const DEFAULT_VAR: i64 = 775807;

pub fn leak<T: Borrow<TB> + 'static, TB: ?Sized>(x: T) -> &'static TB {
    let leaked: &'static T = Box::leak(Box::new(x));
    leaked.borrow()
}

/// Bit 62 marks an address as a synthetic IR node produced after a real address (e.g. arith_load/store fusion in rtl_pass emits the post-load op at this synthetic address). Used by passes that need to ignore the bit when consulting facts keyed by real addresses.
pub const SYNTH_NODE_BIT: u64 = 1u64 << 62;

/// Map a Node address to an execution-order key. Synthetic addresses (bit 62 set) execute immediately after their base address; encoding real as `2 * addr` and synth as `2 * base + 1` keeps a synth strictly between its base and the next real address when sorted numerically. u128 is used so the synth encoding cannot overflow.
#[inline]
pub fn exec_order_key(node: u64) -> u128 {
    let base = (node & !SYNTH_NODE_BIT) as u128;
    if node & SYNTH_NODE_BIT != 0 {
        base * 2 + 1
    } else {
        base * 2
    }
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
