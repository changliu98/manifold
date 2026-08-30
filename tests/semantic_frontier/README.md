# Semantic frontier cases

This manifest extends the focused semantic oracle with ABI and x86 flag
frontiers that occur across Coreutils and the function-level benchmark suites.
Run it with the existing harness, for example:

```bash
scripts/semantic_oracle.py \
  --manifest tests/semantic_frontier/cases.json \
  --manifold target/debug/manifold \
  --compiler gcc --compiler clang
```

Repeat with `--strip` for the symbol-stripped variants.  The checked-in
observations are deterministic under the harness's controlled locale and time
zone.  `binary_checks` make the reference build fail closed if a compiler no
longer emits the mechanism the case is intended to exercise.
