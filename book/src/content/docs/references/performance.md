---
title: "Performance diagnostics"
description: "Timing diagnostics and native compilation modes."
---

Brass minimizes the delay before a normal run starts. Checking and native
compilation are demand-driven. These mechanisms do not change language
semantics; they only change when work is performed. Every run checks the
program from its sources; both default and `--eager` runs can reuse native
objects as described below. See the [performance guide](/guides/performance/)
for choosing a command and [Execution model](/references/execution/) for
checking guarantees.

## Timing logs

Enable performance diagnostics when a check or run is unexpectedly slow:

```bash
BRASS_LOG='brass::perf=debug' brass check app.cz
BRASS_LOG_TYPE=perf brass check app.cz
```

The debug filter prints phase totals and the slowest items. `BRASS_LOG_TYPE`
enables trace-level per-item events and is substantially more verbose.

| Phase                                                         | Work measured                                                          |
| ------------------------------------------------------------- | ---------------------------------------------------------------------- |
| `front/parse-stdlib`, `front/load-modules`, `front/lower-hir` | parsing, imports, and HIR lowering                                     |
| `front/context-check`                                         | checking every imported module (the context) before the entry          |
| `typeck/*`                                                    | type inference and function, method, and initializer checks            |
| `front/keyed-continuation`                                    | checking the methods generated for reflective `-> infer!` calls        |
| `back/lower-mir`, `back/monomorphize`                         | MIR lowering and concrete function instances                           |
| `back/codegen-fn`, `back/codegen`, `back/finalize`            | native-code preparation and JIT finalization                           |
| `back/orc-materialize`                                        | first-use native compilation                                           |

Function and method events include their names. Start with phase totals, then
inspect per-item output only for the phase that dominates.

Analysis files (`.czcache` and `.czctx`) from older releases are unused and
can be deleted. Old per-entry `.czobj` files beside entry files are unused too.

## JIT cache

`brass` and `brass --eager` store native objects in `$XDG_CACHE_HOME/brass/jit/`,
falling back to `$HOME/.cache/brass/jit/`. Each `<key>.czobj` file is keyed by SHA-256
of the exact LLVM bitcode, compiler identity, target triple, CPU features and
optimization tier. Source changes that alter a group's compiler input produce
a different key. A cached O2 object can also serve an O0 session. Checking and
IR generation still run; a hit skips optimization and native code generation.
Runtime-resolved instances in a default run use the same cache. Objects are
published during compilation, so they survive a native process exit.

The default size cap is 256 MiB. Set `BRASS_JIT_CACHE_MAX_MB` to override it;
after the first object is stored in a process, an over-cap cache is trimmed
to 80% of the cap by removing the least recently used objects. Hits refresh
file modification times. Set `BRASS_JIT_CACHE=off` (or `0`) to disable reads
and writes. Cache I/O failures are ignored, and invalid objects are recompiled.
`BRASS_LOG=brass::perf=debug` includes `jit cache hit` and `jit cache store`
events with the group's first symbol and key.

## Native compilation

During both default and `--eager` native runs:

- monomorphization begins at module initializers and `main`;
- a reachable concrete function is optimized and translated on first use;
- a function no executed path reaches is not compiled;
- functions reachable by a spawned task are compiled before that task starts.

In a wide program (more than a few dozen concrete instances), first-use
compilation works on small groups of functions rather than single ones:
functions are grouped in discovery order, so a group's members tend to call
each other, and entering any member compiles its whole group. Grouping
amortizes the fixed per-compilation overhead that would otherwise dominate,
while a group no executed path enters is still never compiled. A dead branch
that shares a group with executed code may therefore be compiled; it still
never runs.

First-use compilation runs at the lowest optimization level: the default run
is tuned for start-up latency, and translating a group without the optimizer
takes a few milliseconds where the optimized pipeline takes hundreds. Set
`BRASS_OPT=2` to compile every group, including runtime-resolved batches,
with the full optimizing pipeline instead -- the right trade for a long-running or compute-bound program whose
first execution of each hot function matters more than its start-up.

`--eager` uses the same first-use native compilation. Its difference is when
checking happens, not what native code is produced: the complete check (and
IR preparation for every checked instance) finishes before execution begins.
The [performance guide](/guides/performance/#when-to-use---eager) describes
when that is the right tool.
