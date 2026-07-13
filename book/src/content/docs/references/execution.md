---
title: "Execution model"
description: "The compilation pipeline, the two back ends, and runtime behavior guarantees."
---

## The pipeline

`prepoly program.pp` runs one pipeline: parse the entry file, load its imports
transitively (plus the embedded standard library), lower, and **type-check the
whole program**. Only when no diagnostics remain is anything executed —
diagnostics go to stderr and the process exits non-zero. `prepoly check`
stops after this stage and prints `ok`.

Execution then instantiates every reachable function at the concrete types it
is used with (**monomorphization**) and runs the program:

1. every module initializer (the top-level statements of each module) runs, in
   dependency order;
2. `main` is called, if defined.

When a concrete type becomes known only at runtime — for example a reflective
decode whose target arrives from external data — the needed specialization is
type-directed-compiled at that moment and cached. This is the "checked just
before it runs" character of the language: checking is ahead of execution,
per function instance.

## Two back ends

|                        | JIT (default)          | Interpreter                                                     |
| ---------------------- | ---------------------- | --------------------------------------------------------------- |
| Engine                 | LLVM-based native code | tree-walking, pure Rust                                         |
| Used by                | `prepoly file.pp`      | `prepoly repl`, wasm/playground, `--no-default-features` builds |
| Library plugins (fs, process, net, path) | yes  | yes (the plugins execute natively either way)                   |
| Concurrency            | yes                    | refused at runtime                                              |
| Runtime specialization | yes                    | refused at runtime                                              |

Both back ends implement the same semantics for the sequential language
surface and are tested against each other. The driver is built with the `jit`
cargo feature by default; without it (or on WebAssembly) only the interpreter
is available.

The interactive REPL accumulates definitions and re-runs the session history
each turn (deterministically, printing only the new output), always on the
interpreter.

## Runtime behavior guarantees

- **Integer overflow wraps** at the type's width, on both back ends. There is
  no overflow trap.
- **Division / remainder by zero** is caught: the interpreter reports a
  runtime error; the JIT panics with the same message. Signed
  `MIN / -1` is defined (wraps) rather than undefined.
- **Shifts** are computed at 64 bits with the shift amount masked to
  `0..63`, then truncated to the operand width — identical on both back ends
  (`1 << 40` on an `int32` is `0`, not undefined).
- **Array indexing is bounds-checked**; an out-of-range index is a runtime
  trap, on both back ends.
- **Floats** follow IEEE 754 (native hardware semantics).
- **Recursion depth** differs: the interpreter guards at a fixed depth
  (currently 8000 calls) and reports a clean error; the JIT uses the native
  stack, so runaway recursion aborts on stack overflow instead.
- On the JIT, a runtime panic **aborts** the process (JIT frames cannot be
  unwound); the interpreter unwinds and reports.
- A failed `!` at an entry point (module top level or `main`) prints
  `unhandled error: <payload>` (or the null-propagation message) to stderr
  and exits non-zero, on both back ends (see
  [Result](/references/types/#result)).

## Environment

- `PREPOLY_LOG` — tracing filter for compiler logs (`info`, `debug`, module
  filters).
- `PREPOLY_LOG_TYPE` — comma-separated named dumps (e.g. `mir`).

## Tooling summary

```bash
prepoly program.pp         # check + run (JIT)
prepoly check program.pp   # check only
prepoly repl [program.pp]  # interpreter / interactive REPL
ppls                       # LSP server (hover, diagnostics, completion,
                           # go-to-definition, semantic tokens)
```

The LSP server builds without LLVM, checks incrementally, and also targets
WebAssembly (it powers the browser playground). An editor setup for Neovim
ships in `editors/nvim/`.
