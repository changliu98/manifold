// Corpus calibration / robustness suite over the full deephistory Linux set.
//
// The full set (~203k x86-64 ELF binaries, see eval/deephistory/manifest_full.tsv)
// is far too large to decompile on every run, so this target REGISTERS the whole
// corpus as available and SAMPLES a runtime-configurable subset to decompile.
//
// Each sampled binary is decompiled in an isolated subprocess (the cargo-built
// `manifold` binary) with a per-binary timeout, so a hang / OOM / panic in one
// binary is recorded as a failure instead of taking down the test process.
//
// The corpus lives outside git (eval/ is git-ignored); when the manifest is
// absent this test is a no-op so normal checkouts and CI stay green.
//
// Pass criterion is robustness: the pipeline must exit successfully and emit a
// non-empty .c. Quality metrics (vs Ghidra / source GT) stay in the Python
// harness at eval/deephistory/compare.py.
//
// Control via environment variables (all optional):
//   CORPUS_SAMPLE         number of binaries to decompile, or "all". Unset/0 => skip (opt-in).
//   CORPUS_SEED           u64 seed for reproducible sampling (default 0).
//   CORPUS_COMPILER       filter: "gcc" or "clang".
//   CORPUS_OPT            filter: "O0".."O3" or "-O0".."-O3".
//   CORPUS_PKG            filter: substring match on package name.
//   CORPUS_GT_ONLY        if set, only binaries that have source ground truth (n_funcs>0).
//   CORPUS_TIMEOUT_SECS   per-binary timeout in seconds (default 180).
//   CORPUS_MIN_PASS_RATE  fail the test if pass rate drops below this (default 0.0 = report-only).
//   CORPUS_LIST           if set, print every available binary and exit without decompiling.
//
// Examples:
//   cargo test --release --test corpus -- --nocapture                         # reports availability, runs nothing
//   CORPUS_SAMPLE=20 cargo test --release --test corpus -- --nocapture        # 20 random binaries
//   CORPUS_SAMPLE=50 CORPUS_OPT=O0 CORPUS_COMPILER=gcc cargo test --release --test corpus -- --nocapture
//   CORPUS_LIST=1 cargo test --release --test corpus -- --nocapture | head    # list available

use std::collections::BTreeMap;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const MANIFEST: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/eval/deephistory/manifest_full.tsv");
const MANIFOLD_BIN: &str = env!("CARGO_BIN_EXE_manifold");

struct Entry {
    id: String,
    compiler: String,
    opt: String,
    package: String,
    n_funcs: u64,
    path: String,
}

// Self-contained seeded PRNG (xorshift64) so sampling is reproducible without an
// external dependency. A fixed scramble of the seed avoids the all-zero state.
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        let s = seed ^ 0x9E37_79B9_7F4A_7C15;
        Rng(if s == 0 { 0xDEAD_BEEF_CAFE_F00D } else { s })
    }
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % (n as u64)) as usize
    }
}

fn env_str(k: &str) -> Option<String> {
    std::env::var(k).ok().filter(|s| !s.is_empty())
}

fn load_manifest() -> Option<Vec<Entry>> {
    let text = std::fs::read_to_string(MANIFEST).ok()?;
    let mut out = Vec::new();
    for (i, line) in text.lines().enumerate() {
        if i == 0 {
            continue;
        }
        let f: Vec<&str> = line.split('\t').collect();
        if f.len() < 7 {
            continue;
        }
        out.push(Entry {
            id: f[0].to_string(),
            compiler: f[1].to_string(),
            opt: f[2].to_string(),
            package: f[3].to_string(),
            n_funcs: f[4].parse().unwrap_or(0),
            path: f[6].to_string(),
        });
    }
    Some(out)
}

fn norm_opt(s: &str) -> &str {
    s.trim_start_matches('-')
}

fn apply_filters(mut v: Vec<Entry>) -> Vec<Entry> {
    if let Some(c) = env_str("CORPUS_COMPILER") {
        v.retain(|e| e.compiler.eq_ignore_ascii_case(&c));
    }
    if let Some(o) = env_str("CORPUS_OPT") {
        let want = norm_opt(&o).to_string();
        v.retain(|e| norm_opt(&e.opt) == want);
    }
    if let Some(p) = env_str("CORPUS_PKG") {
        v.retain(|e| e.package.contains(&p));
    }
    if env_str("CORPUS_GT_ONLY").is_some() {
        v.retain(|e| e.n_funcs > 0);
    }
    v
}

fn report_available(all: &[Entry]) {
    let total = all.len();
    let gt = all.iter().filter(|e| e.n_funcs > 0).count();
    let mut by_comp: BTreeMap<&str, usize> = BTreeMap::new();
    let mut by_opt: BTreeMap<&str, usize> = BTreeMap::new();
    for e in all {
        *by_comp.entry(e.compiler.as_str()).or_default() += 1;
        *by_opt.entry(e.opt.as_str()).or_default() += 1;
    }
    eprintln!("[corpus] available calibration binaries: {total} ({gt} with source GT)");
    eprintln!("[corpus]   by compiler: {by_comp:?}");
    eprintln!("[corpus]   by opt:      {by_opt:?}");
}

enum Outcome {
    Ok(String),
    Fail(String),
    Skip(String),
}

fn tail_of(log: &Path, lines: usize) -> String {
    let Ok(text) = std::fs::read_to_string(log) else {
        return String::new();
    };
    let collected: Vec<&str> = text.lines().filter(|l| !l.trim().is_empty()).collect();
    let start = collected.len().saturating_sub(lines);
    let tail = collected[start..].join(" | ");
    if tail.is_empty() {
        String::new()
    } else {
        format!(" :: {tail}")
    }
}

fn run_one(e: &Entry, timeout: Duration) -> Outcome {
    let bin = Path::new(&e.path);
    if !bin.is_file() {
        return Outcome::Skip(format!("binary not on disk: {}", e.path));
    }
    let dir = std::env::temp_dir().join(format!("manifold_corpus_{}", e.id));
    std::fs::create_dir_all(&dir).ok();
    let out = dir.join("out.c");
    let _ = std::fs::remove_file(&out);
    let log = dir.join("log.txt");

    let mut cmd = Command::new(MANIFOLD_BIN);
    cmd.arg(&e.path).arg(&out);
    match std::fs::File::create(&log) {
        Ok(f) => {
            let f2 = match f.try_clone() {
                Ok(f2) => f2,
                Err(err) => return Outcome::Fail(format!("log clone failed: {err}")),
            };
            cmd.stdout(Stdio::from(f)).stderr(Stdio::from(f2));
        }
        Err(_) => {
            cmd.stdout(Stdio::null()).stderr(Stdio::null());
        }
    }

    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(err) => return Outcome::Fail(format!("spawn failed: {err}")),
    };

    let start = Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                if !status.success() {
                    return Outcome::Fail(format!("exit {:?}{}", status.code(), tail_of(&log, 4)));
                }
                let sz = std::fs::metadata(&out).map(|m| m.len()).unwrap_or(0);
                if sz == 0 {
                    return Outcome::Fail(format!("empty/no output{}", tail_of(&log, 4)));
                }
                return Outcome::Ok(format!("{} bytes in {:.1}s", sz, start.elapsed().as_secs_f64()));
            }
            Ok(None) => {
                if start.elapsed() > timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Outcome::Fail(format!("timeout >{}s", timeout.as_secs()));
                }
                std::thread::sleep(Duration::from_millis(50));
            }
            Err(err) => return Outcome::Fail(format!("wait error: {err}")),
        }
    }
}

#[test]
fn corpus_calibration() {
    let all = match load_manifest() {
        Some(v) if !v.is_empty() => v,
        _ => {
            eprintln!("[corpus] manifest not found or empty: {MANIFEST}");
            eprintln!("[corpus] generate it with: python3 eval/deephistory/gen_manifest_full.py");
            eprintln!("[corpus] skipping (corpus is local-only / git-ignored).");
            return;
        }
    };

    report_available(&all);

    if env_str("CORPUS_LIST").is_some() {
        for e in &all {
            println!(
                "{}\t{}\t{}\t{}\tn_funcs={}\t{}",
                e.id, e.compiler, e.opt, e.package, e.n_funcs, e.path
            );
        }
        return;
    }

    let sample_spec = env_str("CORPUS_SAMPLE").unwrap_or_default();
    if sample_spec.is_empty() || sample_spec == "0" {
        eprintln!(
            "[corpus] {} binaries available; set CORPUS_SAMPLE=N (or =all) to decompile a sample.",
            all.len()
        );
        return;
    }

    let pool = apply_filters(all);
    if pool.is_empty() {
        eprintln!("[corpus] no binaries match the CORPUS_* filters; nothing to run.");
        return;
    }

    let seed: u64 = env_str("CORPUS_SEED").and_then(|s| s.parse().ok()).unwrap_or(0);
    let n = if sample_spec.eq_ignore_ascii_case("all") {
        pool.len()
    } else {
        sample_spec
            .parse::<usize>()
            .unwrap_or_else(|_| panic!("CORPUS_SAMPLE must be a number or 'all', got {sample_spec:?}"))
            .min(pool.len())
    };

    // Seeded Fisher-Yates over indices, then take the first n.
    let mut idx: Vec<usize> = (0..pool.len()).collect();
    let mut rng = Rng::new(seed);
    for i in (1..idx.len()).rev() {
        let j = rng.below(i + 1);
        idx.swap(i, j);
    }
    idx.truncate(n);
    idx.sort_unstable();

    let timeout = Duration::from_secs(
        env_str("CORPUS_TIMEOUT_SECS").and_then(|s| s.parse().ok()).unwrap_or(180),
    );
    let min_pass: f64 = env_str("CORPUS_MIN_PASS_RATE").and_then(|s| s.parse().ok()).unwrap_or(0.0);

    eprintln!(
        "[corpus] running sample of {n} (seed={seed}, timeout={}s/bin) from pool of {}",
        timeout.as_secs(),
        pool.len()
    );

    let mut ok = 0usize;
    let mut failed: Vec<(String, String)> = Vec::new();
    let mut skipped: Vec<(String, String)> = Vec::new();

    for (k, &i) in idx.iter().enumerate() {
        let e = &pool[i];
        let (tag, detail) = match run_one(e, timeout) {
            Outcome::Ok(d) => {
                ok += 1;
                ("ok", d)
            }
            Outcome::Fail(d) => {
                failed.push((e.id.clone(), d.clone()));
                ("FAIL", d)
            }
            Outcome::Skip(d) => {
                skipped.push((e.id.clone(), d.clone()));
                ("skip", d)
            }
        };
        eprintln!(
            "[corpus] {:>4}/{:<4} {:5} id={} {} {} {} -- {}",
            k + 1,
            n,
            tag,
            e.id,
            e.compiler,
            e.opt,
            e.package,
            detail
        );
    }

    let run = ok + failed.len();
    let rate = if run == 0 { 1.0 } else { ok as f64 / run as f64 };

    eprintln!("\n[corpus] === summary ===");
    eprintln!(
        "[corpus] decompiled {ok}/{run} = {:.1}%  ({} skipped, threshold {:.0}%)",
        rate * 100.0,
        skipped.len(),
        min_pass * 100.0
    );
    if !failed.is_empty() {
        eprintln!("[corpus] failures:");
        for (id, d) in &failed {
            eprintln!("[corpus]   id={id}: {d}");
        }
    }
    if !skipped.is_empty() {
        eprintln!("[corpus] skipped (binary not on disk): {}", skipped.len());
    }

    assert!(
        rate >= min_pass,
        "corpus pass rate {:.1}% below CORPUS_MIN_PASS_RATE {:.1}%",
        rate * 100.0,
        min_pass * 100.0
    );
    // Catch a catastrophic regression: with a non-trivial sample, zero successes
    // means the pipeline is broken regardless of the (default 0.0) threshold.
    if run >= 3 {
        assert!(ok > 0, "0/{run} binaries decompiled successfully -- pipeline likely broken");
    }
}
