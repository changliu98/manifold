# Manifold

<p align="center">
  <img src="assets/manifold-logo-circle.svg" alt="Manifold logo" width="128">
</p>

An experimental x86-64 ELF and native AMD64 PE32+ binary decompiler using [Ascent](https://github.com/s-arash/ascent).

Manifold runs CompCert's compilation pipeline in reverse. Each pass undoes one CompCert
lowering step, raising the program through Mach, Linear, LTL, RTL, Cminor, Csharpminor and
Clight toward C. The decompilation knowledge is written as Ascent Datalog rules that derive
candidate statements and types, and a Z3 MaxSMT selection picks one consistent choice of
each across the program.

The end-to-end behavioral evaluation and quality claims are currently scoped to
stripped x86-64 Linux ELF binaries. AArch64 and ARM32 have target data models,
register/ABI definitions, Capstone decoding, CFG classification, and normalization
frontends into the shared Mach vocabulary, with focused frontend tests. They have not
yet received an end-to-end generated-C behavioral evaluation and are portability
structure, not claimed decompilation support. AMD64 PE32+ support is experimental and
covered separately from the Linux corpus.

## Prerequisites

- A Rust toolchain and a C compiler (Capstone is built from the bundled source).
- **Z3 >= 4.13** as a shared library, found through `pkg-config`. Many distributions
  ship an older Z3 (Ubuntu 22.04 has 4.8, too old for the `z3` crate's API). Build with
  `PKG_CONFIG_PATH=<z3-prefix>/lib/pkgconfig` and run with `<z3-prefix>/lib` on
  `LD_LIBRARY_PATH`, since the binary links the versioned `libz3.so.4.NN`.
- The pipeline tests also need `gcc` and `clang`.

## Quick Start

```bash
git clone --recursive <repo-url> && cd manifold
cargo build
cargo run --release -- /bin/ls ls.c
cargo run --release -- <binary> [output.c] [options]
RAYON_NUM_THREADS=32 cargo run --release -- /bin/ls ls.c   # Limit threads (default: all cores)
TRACE_NODE=0xcb76 cargo run -- /bin/ls                      # Trace a specific node through the pipeline
TRACE_FUNC=0x4015a0 cargo run -- /bin/ls                    # Trace the call nodes of one function
```

Without an output path, the C goes to `<binary>.optimized.c` next to the input.

| Option | Effect |
|--------|--------|
| `--trace` | Write the raw Clight C and the pipeline debug dumps |
| `--dump-ir` | Write each IR stage to its own file |
| `--dump-clight-json` | Export the selected Clight IR as JSON |
| `--dump-recovered-types` | Export the final C types and proven frame locations |
| `--measure-rule-times` | Write per-pass Ascent rule timings |
| `--dump-deps` | Write the pass dependency graph (no binary needed) |
| `--max-round-work=N` | Bound the program selection rounds to N times the open solves' Z3 work |

`manifold` with no arguments prints the full list, including the ablation switches used
in experiments.

## Tests

```bash
cargo test                                # all tests
cargo test --lib                          # library and solver unit tests
cargo test --test pipeline                # compile tests/source/* with gcc and clang, decompile, check the C AST
cargo test smoke -- --nocapture           # one pipeline case, both compilers
CORPUS_SAMPLE=20 cargo test --release --test corpus -- --nocapture   # opt-in local corpus sweep
```

## Project Structure

```
src/
+-- main.rs, lib.rs, util.rs       # Entry point, library root, utilities
+-- abi.rs, mreg.rs                # Target ABI facts, cross-architecture machine registers
+-- x86/                           # IR types (Node, Instruction, MemoryChunk), registers, operations
+-- aarch64/, arm32/               # AArch64 and ARM32 register models
+-- decompile/
|   +-- elevator.rs                # Pipeline orchestration and DecompileDB
|   +-- passes/*_pass.rs           # Translation passes
|   +-- passes/clight_select/      # Z3 MaxSMT statement/type selection
|   +-- passes/c_pass/             # C AST types, printer, conversion from relations
|   +-- analysis/                  # Analysis passes
|   +-- effects/                   # Machine-rooted effect contracts and their validation
|   +-- postselect/                # C AST transforms after selection (loops, variables, gotos)
|   +-- disassembly/               # Capstone-based disassembler
+-- debug/                         # Debug/trace output
+-- data/                          # Static data (builtins, extern signatures, headers)
ascent-plusplus/                   # Custom Ascent Datalog fork (submodule)
```

## Output Files

| File | Flag | Description |
|------|------|-------------|
| `<name>.optimized.c` | (default) | Primary decompiled output |
| `<name>.light.c` | `--trace` | Raw decompiled output |
| `<name>.{debug,dataflow,lost}.yaml` | `--trace` | Pipeline debug, register-to-variable mapping, unselected statements |
| `<name>.{asm,mach,linear,ltl,rtl,cminor,csharpminor,clight}` | `--dump-ir` | Per-stage IR dumps |
| `<name>.clight.json` | `--dump-clight-json` | Selected Clight IR |
| `<name>.types.json` | `--dump-recovered-types` | Recovered C types and frame locations |
| `debug/rule_times/<pass>.txt` | `--measure-rule-times` | Per-pass Ascent rule timing |
| `pipeline.dot`, `pipeline-detailed.dot` | `--dump-deps` | Pass dependency graph (summary, with rule dependencies) |
