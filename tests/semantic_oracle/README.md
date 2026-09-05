# Focused executable semantic oracle

`scripts/semantic_oracle.py` is the fast behavior gate between the AST-focused
pipeline tests and the full Docker Coreutils campaign. It performs this chain
for every case and reference compiler:

```
checked-in C -> reference executable -> Manifold -> emitted C -> recovered executable
                              |                              |
                        exact observations <----------------+
```

The comparison is byte-exact over stdout and stderr and exact over the process
return code for every deterministic stimulus. A nonzero return code is an
observation, not automatically a failure. Each checked-in reference observation
must first match the newly compiled source, so compiler or fixture drift cannot
silently change the oracle.

## Run it

Use an already-built candidate (usually the fastest path):

```bash
scripts/semantic_oracle.py --manifold /candidate/target/debug/manifold
```

Use the Debug binary in another checkout, optionally building it first:

```bash
scripts/semantic_oracle.py --checkout /candidate
scripts/semantic_oracle.py --checkout /candidate --build-checkout
```

The caller's environment is preserved because a candidate may need a custom Z3
runtime. For example:

```bash
LD_LIBRARY_PATH="$MANIFOLD_Z3_PREFIX/lib" \
  scripts/semantic_oracle.py --manifold target/debug/manifold
```

Useful focused modes:

```bash
# A compiler matrix; recovered C is still linked with gcc by default.
scripts/semantic_oracle.py --manifold target/debug/manifold \
  --compiler gcc --compiler clang

# Compile recovered C with optimization enabled to expose UB-sensitive changes.
scripts/semantic_oracle.py --manifold target/debug/manifold \
  --compiler gcc --compiler clang --recompile-opt O2

# One mechanism, production-like symbol stripping, or sanitizer attribution.
scripts/semantic_oracle.py --manifold target/debug/manifold --case overflow_flags
scripts/semantic_oracle.py --manifold target/debug/manifold --strip
scripts/semantic_oracle.py --manifold target/debug/manifold --sanitizers
```

The command exits 0 only when every selected source/compiler variant reaches
behavioral equivalence. It exits 1 for a compile, decompile, recompile, or
behavior failure, and 2 for a configuration error. `--list` prints case names.

By default, artifacts are retained under
`/tmp/manifold-semantic-oracle-<UTC>-<pid>/`. Use `--output NEW_DIRECTORY` for a
stable location. `summary.json` is the machine-readable result. Each variant
also has `result.json`, its compiled binaries and emitted C, and separate
`*.command.json`, `*.stdout`, and `*.stderr` files for every stage and stimulus.
The summary deliberately reports recompilation separately from behavior:

- `recompiled_end_to_end`: emitted C linked to an executable;
- `behavior_equivalent_end_to_end`: exact behavior matched, counting earlier
  stage failures against the eligible fixture denominator;
- `behavior_equivalent_among_recompiled`: behavior matched among executables
  that actually linked;
- `stimuli_equivalent_among_compared`: individual observed runs that matched.

## Cases

The suite is intentionally small and mechanism-focused. It covers JO/JNO
overflow branches, passed and aliased stack addresses, byte-offset global data
combined with SIMD lane selection, narrow and wide out-parameter stores with
live surrounding bytes, an initialized aggregate copied with a relocated
pointer at byte offset +8, and one-past pointer identity at adjacent array
members. The aggregate case reloads its interior pointer through `base + 8` and
checks both pointer identity and pointee data. The JO/JNO and SIMD fixtures
include disassembly checks so a compiler upgrade cannot optimize away the
mechanism. Those checks protect fixture integrity; they are not the semantic
score.

Add a standalone C file under `cases/` and a manifest row with deterministic
stimuli and expected observations. Keep the program free of external state and
verify checked observations with both GCC and Clang when practical.

## What it does and does not prove

This is finite black-box differential testing. A pass means the recovered
executable matched all declared observations for these inputs; it is not a
proof of whole-program equivalence like a verified IR equivalence checker.
These tiny, mostly self-contained ELF programs also do not model Coreutils'
filesystem effects, locale, concurrency, signals, libraries, or full input
space. Run `--strip` to approach the integration campaign's symbol conditions,
but the default keeps symbols for speed and diagnostic clarity. The gate is a
candidate ranker and regression tripwire, not a replacement for the Docker
campaign.

`--sanitizers` rebuilds both the original source and emitted C with ASan+UBSan
and labels diagnostics as `recovered_only`, `shared`, `reference_only`, or
`clean`. Only recovered-only diagnostics are attributable to emitted C by this
comparison. Sanitizer builds change layout and optimization, and absence of a
diagnostic is not proof that undefined behavior is absent.

The harness itself has a small end-to-end test:

```bash
python3 -m unittest tests/semantic_oracle/test_harness.py
```
