#[test]
fn libclang_parallel_parses_dont_crash_or_diverge() {
    manifold::decompile::passes::clight_select::select::libclang_concurrent_check(200)
        .expect("libclang concurrent check failed");
}
