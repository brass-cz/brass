---
title: "Execution model"
description: "The compilation pipeline, the two back ends, and runtime behavior guarantees."
---

## Default native run

`brass program.cz` parses the entry file, loads its imports and embedded
`core` modules, and lowers them into one statically typed program. The default
native run then overlaps two demand-driven tasks:

- The checker starts from module initializers and `main`, and continues on a
  dedicated thread. When execution needs a function whose body is not yet
  settled for the call's argument types, it waits for that body to be checked.
- Native compilation starts from the same entry points. A reachable function
  is monomorphized, optimized, and translated to native code when it is first
  needed instead of before the run starts.

This scheduling changes latency, not the type system: no function body can
execute with unresolved or rejected types.

### The verdict of a normal run

A normal run reports errors in the code it needs:

- An error in a module initializer, top-level statement, or `main` prevents
  execution from starting.
- An error in a function reached later stops the run before that function
  executes. Output already produced remains visible and the process exits
  non-zero.
- The unit is a complete function body. An error in an untaken branch of a
  called function still rejects that function.
- An uncalled function does not affect the current run. Its check may continue
  in the background and a partial result may be cached for a later run.

Consequently, a successful run is not a complete whole-program verdict. Use
`brass check` in CI and whenever all code must be validated.

In one known case the demand-driven pipeline stops a program that the
whole-program commands accept: a very deep call chain of unannotated returns
whose inferred type differs from the default integer width. The run fails
with a defined error naming the function whose return type to annotate;
annotating it (or running with `--eager`) resolves the program.

### Complete checking and compilation

`brass check program.cz` checks the complete program without running it and
prints nothing on success. `brass --eager program.cz` performs the same
complete check before anything runs, then executes the program; native code
is still optimized and translated on first use, exactly as in a normal run.
The interpreter and REPL also check eagerly.

A valid full `.czcache` skips checking on an unchanged program. A partial
cache instead resumes an interrupted background check. Neither changes the
program's semantics; see [Performance and caching](/references/performance/).

### Monomorphization and reflection

A polymorphic function is instantiated for each concrete set of argument
types it is called with. Reflective `-> infer!` functions are different: the
target type must be known from the expected type at the call site, and the
front end specializes the reflective operation before execution. Native code
for either kind of concrete function may still be compiled on first use.

After preparation, execution order is:

1. module initializers, in dependency order;
2. `main`, if it is defined.

A `spawn` is an exception to first-use compilation: every function the new
task can statically reach is compiled before the task starts because worker
threads do not compile.

## Two back ends

|                                          | JIT (default)          | Interpreter                                                   |
| ---------------------------------------- | ---------------------- | ------------------------------------------------------------- |
| Engine                                   | LLVM-based native code | tree-walking, pure Rust                                       |
| Used by                                  | `brass file.cz`        | `brass repl`, wasm/playground, `--no-default-features` builds |
| Library plugins (fs, process, net, path) | yes                    | yes (the plugins execute natively either way)                 |
| Concurrency                              | yes                    | refused at runtime                                            |
| On-demand native compilation             | yes                    | not applicable                                                |

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
