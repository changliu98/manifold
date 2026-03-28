# Manifold

An experimental x86-64 ELF binary decompiler using [Ascent](https://github.com/s-arash/ascent).

## Quick Start

Prerequisites: **mold** linker, **libclang**, **libcapstone**

```bash
git clone --recursive <repo-url> && cd manifold
cargo build
cargo run --release -- /bin/ls ls.c
cargo run --release -- <binary> [output.c] [--trace] [--dump-ir] [--measure-rule-times]
RAYON_NUM_THREADS=32 cargo run --release -- /bin/ls ls.c   # Limit threads (default: all cores)
TRACE_NODE=0xcb76 cargo run -- /bin/ls         # Trace a specific node through pipeline
```

## Project Structure

```
src/
+-- main.rs, lib.rs, util.rs       # Entry point, library root, utilities
+-- x86/                           # IR types (Node, Instruction, MemoryChunk), registers, operations
+-- decompile/
|   +-- elevator.rs                # Pipeline orchestration and DecompileDB
|   +-- passes/*_pass.rs           # Translation passes
|   +-- passes/clight_select/      # CEGAR-based statement selection
|   +-- passes/c_pass/             # C AST types, printer, goto reduction
|   +-- analysis/                  # Analysis passes
|   +-- disassembly/               # Capstone-based disassembler
+-- debug/                         # Debug/trace output
+-- data/                          # Static data
ascent-plusplus/                   # Custom Ascent Datalog fork (submodule)
```

## Output Files

| File | Flag | Description |
|------|------|-------------|
| `<name>.optimized.c` | (default) | Primary decompiled output |
| `<name>.light.c` | `--trace` | Raw decompiled output |
| `<name>.{debug,dataflow,lost}.yaml` | `--trace` | Pipeline debug, register-to-variable mapping, unselected statements |
| `<name>.{asm,mach,linear,...}` | `--dump-ir` | Per-stage IR dumps |
| `debug/rule_times/<pass>.txt` | `--measure-rule-times` | Per-pass Ascent rule timing |
