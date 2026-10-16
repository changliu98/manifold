// gnulib's c_strtod returns 0.0 through `pxor %xmm0,%xmm0; ret` while RAX still holds the cached
// newlocale() result. That stale call result must not make the function an int/pointer return.

#[test]
fn c_strtod_returns_double() {
    assert!(
        OUTPUT.text.contains("double c_strtod("),
        "c_strtod should return double:\n{}",
        OUTPUT.text
    );
}
