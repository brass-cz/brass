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
- Declaration and signature errors are not ignored for uncalled functions.
  The up-front checks, including duplicate parameters, unresolved type
  annotations, and interface conformance, prevent execution from starting.
  Return contracts that depend on body inference are checked as that body
  settles, before it can execute. This does not require eagerly inferring
  every function body.
- An error in a function reached later stops the run before that function
  executes. Output already produced remains visible and the process exits
  non-zero.
- The unit is a complete function body. An error in an untaken branch of a
  called function still rejects that function.
- These body rules also apply to instance and static methods, including
  methods reached through a function compiled during execution. Their source
  diagnostics are checked before native compilation of the affected batch.
- An uncalled function's body errors do not affect the current run. Its check
  may continue in the background until the program exits. Declaration and
  signature errors are still subject to the checks above.
- Pattern contracts follow these same body rules: refutable `let`, `const`,
  and `for` patterns, duplicate bindings, and unreachable match arms reject
  a needed body before it executes. They do not reject a run that never
  needs that body. Patterns depending on generic arguments are checked for
  each concrete instance. Closure bodies are checked within their enclosing
  body, and module initializers are always needed.

As with other body diagnostics, uninstantiated reflective method templates
and statically pruned branches follow the checker's selection rules (see
[type tests](/references/types/#type-tests)).

Errors use the same diagnostic text and source locations as `brass check`, and
a run that stops on an error prints the checker's complete verdict, including
errors in bodies the run never reached. Match coverage is checked after the
relevant argument types are known, before the affected body can execute.
Checker warnings remain non-fatal in all modes.

Consequently, a successful run is not a complete whole-program verdict. Use
`brass check` in CI and whenever all code must be validated.

A reflective specialization discovered only after execution starts completes
checking and reports any source errors. If checking succeeds but the running
session cannot install the specialization, the run stops with a request to
rerun with `--eager`; it does not replay earlier side effects.

### Complete checking and compilation

`brass check program.cz` checks the complete program without running it and
prints nothing on success. `brass --eager program.cz` performs the same
complete check before anything runs, then executes the program; native code
is still optimized and translated on first use, exactly as in a normal run.
The interpreter and REPL also check eagerly.

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
| Engine                                   | LLVM-based native code | MIR interpreter, pure Rust                                    |
| Used by                                  | `brass file.cz`        | `brass repl`, wasm/playground, `--no-default-features` builds |
| Library plugins (fs, process, net, path) | yes                    | yes (the plugins execute natively either way)                 |
| Concurrency                              | yes                    | refused at runtime                                            |
| On-demand native compilation             | yes                    | not applicable                                                |

For a program that checks, a normal run, `--eager`, and the interpreter
produce the same output. The exceptions are concurrency, which the interpreter
refuses when execution reaches it, and the recursion limit below. The driver
is built with the `jit` cargo feature by default; without it (or on
WebAssembly) only the interpreter is available.

The interactive REPL accumulates definitions and validates the combined session
history each turn, but executes each input once: an `input()`, a print or any
other call from a prior turn is not repeated. To give a new input the values it
reads, the earlier inputs that only rebuild values run again ahead of it. Such
an input is a single statement of one of these forms:

- a `let`/`const` binding whose initializer has no side effects: literals
  (strings without `{..}` interpolation), names of available bindings and of
  functions, operators, field and index reads, ranges, array/record/variant
  constructions, and closure literals that assign or mutate no captured
  binding;
- an assignment to an available binding or to a field or element of one, with
  side-effect-free target and value;
- `push`, `insert`, `remove` or `pop` on an available array, with
  side-effect-free arguments.

A binding made any other way (its initializer calls a function, interpolates a
string, which may run a `display` method, branches, or propagates with `!`) is
not available to later inputs, since producing its value again would repeat
the effects. Neither is a binding that an input which is not run again may
have changed (assigned, mutated in place, or passed to a `ref(mut(T))`
parameter), nor one sharing a value with it (`let c = xs` names the same
array), since replaying it would show a stale value; a binding read from an
unavailable one is unavailable too. Using such a name reports that it is not
available in this input; binding the name again makes it available. Top-level
definitions (functions, types, imports) are always available. The REPL always
uses the interpreter.

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
  (8000 calls) and reports a clean error; the JIT uses the native stack, so
  runaway recursion aborts on stack overflow instead.
- On the JIT, a runtime panic **aborts** the process (JIT frames cannot be
  unwound); the interpreter unwinds and reports.
- A failed `!` at an entry point (module top level or `main`) prints the
  error to stderr and exits non-zero, on both back ends: the nested
  `[file:line:col] unhandled error: ...` trace when the payload is the prelude
  `Error` (see [Error traces](/references/syntax-sugar/#error-traces)),
  otherwise `runtime error: unhandled error: <payload>` or the
  null-propagation message.

## JIT object cache

Native runs share content-addressed objects in `$XDG_CACHE_HOME/brass/jit`,
falling back to `$HOME/.cache/brass/jit`. Changed compiler inputs get new keys,
so changed source cannot reuse stale code. Cleanup covers the whole shared
cache, not individual source files.

`brass cache info` shows the directory, configured enabled/disabled status,
object count, size, limit, and stale temp count. Sizes include exact bytes.
`brass cache clean` removes all published objects. It also removes temp
files older than 24 hours. It reports removed counts and object bytes. Fresh temps and unknown entries
stay intact. Both commands work with caching disabled. A missing directory
is empty. Concurrent readers see a miss; writers may repopulate the cache.
Management I/O errors exit with status 1. Builds without the JIT report that
no cache is available and exit successfully.

`brass --no-jit-cache program.cz` disables reads and writes for that run,
like `BRASS_JIT_CACHE=off`. It works with `--eager` and preserves stored
objects. Put the flag before the program filename. `brass cache` never
changes package downloads in `~/.brass/packages`. See
[Performance diagnostics](/references/performance/#jit-cache) for keys and
eviction.

## Environment

- `BRASS_LOG`: tracing filter for compiler logs (`info`, `debug`, module
  filters).
- `BRASS_CHANNEL_CHECK=1`: compare each streaming checker flush with an
  independent full-scan publisher, preserving diagnostics and owner order.
- `BRASS_MEMO_CHECK=1`: bypass elaboration memo reuse for differential checking.
- `BRASS_LAZY_COMPLETE=off|auto`: lazy checker policy (`auto` by default;
  unknown values use the default). `off` keeps pure demand settlement.
  `auto` may finish the same checker after a sustained runtime demand cascade,
  then lower a closed region of checked bodies with final, clean diagnostics.
  Bodies with uncertain dispatch, held diagnostics or keyed calls stay on the
  demand path, together with their callers. Reached region bodies pass the
  usual diagnostic gate.
- `BRASS_LOG_TYPE`: comma-separated named dumps (e.g. `mir`).
- `BRASS_PACKAGES`, `BRASS_INCLUDE`: module search roots (see
  [Module resolution](/references/modules/#module-resolution)).
- `BRASS_OPT`: native optimization tier (see
  [Performance diagnostics](/references/performance/)).
- `BRASS_JIT_CACHE=off|0`: disable JIT cache reads and writes; other values
  permit caching, which is enabled by default.
- `BRASS_JIT_CACHE_MAX_MB`: object cache cap in MiB (default 256); invalid
  values use the default. Zero permits immediate eviction.
- `XDG_CACHE_HOME`, `HOME`: select the JIT cache directory as described above;
  without either nonempty variable, caching is disabled.

## Tooling summary

```bash
brass program.cz         # lazy check + run (JIT)
brass --eager program.cz # whole-program check + compile, then run
brass check program.cz   # check only (always whole-program)
brass repl [program.cz]  # interpreter / interactive REPL
brass --no-jit-cache program.cz # run without cache reads or writes
brass cache info         # inspect the shared JIT object cache
brass cache clean        # remove all cached objects and stale temp files
czls                       # LSP server (hover, diagnostics, completion,
                           # go-to-definition, semantic tokens)
```

Driver options such as `--eager` and `--no-jit-cache` are parsed before the
program file. Everything after that file is passed to the program verbatim,
including flag-shaped values, and can be read with `env.args()`:

```bash
brass --eager program.cz input.txt --verbose
```

The first words `check`, `repl`, `cache`, and `help` are reserved commands.
Use `brass -- cache` to run a file literally named `cache`.

The LSP server builds without LLVM, checks incrementally, and also targets
WebAssembly (it powers the browser playground). An editor setup for Neovim
ships in `editors/nvim/`.

Start-up time is dominated by type checking; see
[Performance diagnostics](/references/performance/) for the timing logs that
break it down.
