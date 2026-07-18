---
title: "Execution model"
description: "The compilation pipeline, the two back ends, and runtime behavior guarantees."
---

## The pipeline

`brass program.cz` parses the entry file, loads its imports transitively
(plus the embedded standard library), lowers, and **type-checks the whole
program**, but by default it checks **lazily**: type inference runs on a
dedicated checker thread, starting from the program's entry (the module
initializers, then `main`), while the main thread compiles and prepares
execution in parallel. When compilation reaches a function whose check has
not finished, it sends the function's path and the concrete argument types
of the call to the checker, which settles that body next.

Compilation is as lazy as checking: only the entry (the initializers and
`main`) compiles before execution starts. A call to a function whose
signature is annotation-determined compiles into a _deferred site_; the
first time execution actually reaches it, the function is monomorphized and
compiled on the spot, waiting for the checker first if its body is still
being inferred. A `spawn` pre-compiles everything the spawned task could
statically reach before the spawn runs, since worker threads never compile;
code only the main thread can reach stays on demand.

A lazy run's verdict covers **what the run executes**:

- A diagnostic in the entry (a module initializer, `main`, or top-level
  code) aborts the run before anything executes, with the same report the
  eager pipeline prints.
- A function first reached mid-run is settled, at the concrete argument
  types of the call that reached it, before it executes; a diagnostic in
  it stops the run at that moment, non-zero (output already produced
  stands).
- A function the run never calls, including one only reachable from a
  branch the run never takes, keeps checking in the background while the
  program runs, and what that finds is saved for the next run; it does not
  affect this run's outcome. The complete whole-program verdict is `brass
  check`'s (or `--eager`'s) job.
- The unit of this verdict is the **function body**: a diagnostic anywhere
  in a body the run needs is fatal, even inside a branch of it execution
  would never take.
- A well-typed program behaves identically either way; code the run never
  reaches simply no longer delays it.

`brass check` always checks **eagerly**: the whole program, on the calling
thread, before reporting; it prints nothing when the program is well-typed.
`--eager` gives a run the same check-everything-first behavior and also
compiles the whole program as one optimized unit before running it. The
interpreter back end and `brass repl` are eager too.

A `.czcache` hit (an already-checked program, see
[Performance & caching](/references/performance/)) skips checking entirely
but keeps compilation demand-driven: monomorphization starts from the
initializers and `main` only, and each reachable function is optimized and
translated to native code the first time execution calls it. See the
[performance guide](/guides/performance/) for choosing between the lazy
default and `--eager`.

Execution then instantiates every reachable function at the concrete types it
is used with (**monomorphization**) and runs the program:

1. every module initializer (the top-level statements of each module) runs, in
   dependency order;
2. `main` is called, if defined.

When a concrete type becomes known only at runtime, for example a reflective
decode whose target arrives from external data, the needed specialization is
type-directed-compiled at that moment and cached. This is the "checked just
before it runs" character of the language: checking is ahead of execution,
per function instance.

## Two back ends

|                                          | JIT (default)          | Interpreter                                                   |
| ---------------------------------------- | ---------------------- | ------------------------------------------------------------- |
| Engine                                   | LLVM-based native code | tree-walking, pure Rust                                       |
| Used by                                  | `brass file.cz`        | `brass repl`, wasm/playground, `--no-default-features` builds |
| Library plugins (fs, process, net, path) | yes                    | yes (the plugins execute natively either way)                 |
| Concurrency                              | yes                    | refused at runtime                                            |
| Runtime specialization                   | yes                    | refused at runtime                                            |

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
  `0..63`, then truncated to the operand width, identical on both back ends
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

- `BRASS_LOG`: tracing filter for compiler logs (`info`, `debug`, module
  filters).
- `BRASS_LOG_TYPE`: comma-separated named dumps (e.g. `mir`).

## Tooling summary

```bash
brass program.cz         # lazy check + run (JIT)
brass --eager program.cz # whole-program check + compile, then run
brass check program.cz   # check only (always whole-program)
brass repl [program.cz]  # interpreter / interactive REPL
czls                       # LSP server (hover, diagnostics, completion,
                           # go-to-definition, semantic tokens)
```

Driver options such as `--eager` are parsed before the program file. Everything
after that file is passed to the program verbatim, including flag-shaped values,
and can be read with `env.args()`:

```bash
brass --eager program.cz input.txt --verbose
```

The LSP server builds without LLVM, checks incrementally, and also targets
WebAssembly (it powers the browser playground). An editor setup for Neovim
ships in `editors/nvim/`.

Start-up time is dominated by type checking; see
[Performance & caching](/references/performance/) for the timing logs and the
`.czcache` analysis cache that eliminates it on unchanged programs.
