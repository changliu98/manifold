
use csv;
use std::borrow::Borrow;

pub const DEFAULT_VAR: i64 = 775807;

pub fn leak<T: Borrow<TB> + 'static, TB: ?Sized>(x: T) -> &'static TB {
    let leaked: &'static T = Box::leak(Box::new(x));
    leaked.borrow()
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
