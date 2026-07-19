---
title: "Performance and caching"
description: "Timing diagnostics, analysis caches, cache validity, and native compilation modes."
---

Brass minimizes the delay before a normal run starts. Checking and native
compilation are demand-driven, while reusable analysis is cached. These
mechanisms do not change language semantics; they only change when work is
performed. See the [performance guide](/guides/performance/) for choosing a
command and [Execution model](/references/execution/) for checking guarantees.

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
| `typeck/*`                                                    | type inference and function, method, and initializer checks            |
| `front/keyed-repass`                                          | the additional front-end pass required by reflective `-> infer!` calls |
| `back/lower-mir`, `back/monomorphize`                         | MIR lowering and concrete function instances                           |
| `back/codegen-fn`, `back/codegen`, `back/finalize`            | native-code preparation and JIT finalization                           |
| `back/orc-materialize`                                        | first-use native compilation during a demand-driven run                |
| `front/cache-hit`, `front/cache-save`                         | analysis cache loading and saving                                      |

Function and method events include their names. Start with phase totals, then
inspect per-item output only for the phase that dominates.

## Cache overview

Brass uses two analysis-cache locations:

| Cache      | Location                   | Purpose                                                            |
| ---------- | -------------------------- | ------------------------------------------------------------------ |
| `.czcache` | beside the entry file      | Reuse a complete check, or resume a partially completed normal run |
| `.czctx`   | the user's cache directory | Reuse checked dependencies when only the entry file changes        |

`BRASS_CACHE=off` disables cache reads and writes. Cache operations are
best-effort: an unavailable or read-only cache location does not prevent a
program from running or being checked.

## Entry analysis cache (`.czcache`)

For `app.cz`, the entry cache is `app.czcache`. It can contain one of two
kinds of result:

- A **full cache** records an error-free complete check. `brass check`, an
  eager run, or a normal run whose background checker finishes can produce
  it. An unchanged program skips checking entirely when this cache is valid.
- A **partial cache** records the settled portion of a normal run whose
  background checker had not finished when the program exited. The next
  normal run resumes from that point; it does not treat the program as fully
  checked.

Both kinds use the same filename and are distinguished internally. Therefore
the existence of `.czcache` alone does not prove that the whole program was
checked. The command result remains the authority: use `brass check` when a
complete verdict is required.

### Validity

An entry cache is used only when all inputs still identify the same program:

- the compiler version, release identity, and cache format match;
- the entry and every loaded source have the recorded contents;
- package names resolve consistently;
- imported native plugins still resolve and have the recorded contents.

Source contents are checked rather than modification times. Moving an
unchanged project or toolchain can therefore preserve a valid cache, while a
changed dependency invalidates it. Any mismatch is handled silently by
checking again. Cache files are not stable interchange formats and have no
cross-version compatibility guarantee.

## Context cache (`.czctx`)

The context cache accelerates the common case where the entry file changes
but its imports do not. A program's context is every module except the entry:
embedded `core`, imported `std` modules, and project dependencies.

Brass stores the context's inferred schemes and checked bodies under the user
cache directory (`$XDG_CACHE_HOME/brass` or `~/.cache/brass`). Its key includes
the compiler identity and the names and contents of every context module; the
entry contents are deliberately excluded. A valid seed lets the checker
validate only the changed entry against the saved context.

Reflective programs keep specialization-sensitive context entries separate.
A context with diagnostics is not cached, and a top-level name collision that
would change stored symbols causes a normal full check instead.

The language server uses the same context-cache mechanism and on-disk store,
so editor checks also benefit when dependencies remain unchanged. It may read
a valid full `.czcache` for a buffer that exactly matches the file on disk,
but it does not write entry caches because the driver performs additional
execution-specific rewrites.

## Native compilation

An analysis-cache hit removes checking work, not native compilation. During a
normal native run:

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

`--eager` uses the same first-use native compilation. Its difference is when
checking happens, not what native code is produced: the complete check (and
IR preparation for every checked instance) finishes before execution begins.
The [performance guide](/guides/performance/#when-to-use---eager) describes
when that is the right tool.
