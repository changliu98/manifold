# Storage and ABI regression fixtures

These opt-in fixtures use the [semantic oracle](../semantic_oracle/README.md)
to compile source, decompile the executable, recompile recovered C, and compare
stdout, stderr, and exit status for the inputs recorded in each manifest.

- `cases.json`: escaped mixed-width objects, floating payloads, and updates
  across branches and library calls.
- `machine_views.json`: constant and indexed frame views, overlapping writes,
  and multiple observers.
- `selection_views.json`: sliding packet windows and overlapping byte lanes.
- `abi_effects.json`: variadic forwarding through stdio and file descriptors.
- `gp_variadic.json`: general-purpose-register variadic argument storage.

Run a manifest with a Debug build:

```sh
scripts/semantic_oracle.py --manifest tests/semantic_counterexamples/machine_views.json \
  --manifold target/debug/manifold --compiler gcc --compiler clang --recompile-opt O2
```

Use `--strip`, `--recompiler clang`, or `--sanitizers` for additional checks.
The harness accepts repeatable `--manifold-arg=--flag` arguments, including
`--ablate-storage-search`, `--ablate-existing-storage-views`, and
`--ablate-call-observer-isolation`, and records the executed command.

This corpus includes known failures: branch-merged and unsupported indexed
views, narrow return values in packet windows, floating-point variadic argument
recovery, and optimized direct reads from variadic register-save areas. The
oracle reports these failures normally; they are not expected-failure passes.
The mandatory GCC/Clang pipeline regression for committed storage refinement
is `tests/source/semantic_selection_epoch`.

Keep generated C, executables, logs, and result summaries outside the checkout;
the oracle's default output location is a new temporary directory.
