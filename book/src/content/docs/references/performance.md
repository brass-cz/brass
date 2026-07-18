---
title: "Performance: timing logs and the analysis cache"
description: "Measuring where compile time goes, and how the .czcache analysis cache works."
---

## Where start-up time goes

Every piece of Brass code is type-checked before it executes -- lazily by
default, whole-program under `check`/`--eager` (see
[Execution model](/references/execution/)). On a library-heavy program that
check dominates start-up: parsing and HIR lowering are single-digit
milliseconds, MIR lowering and monomorphization a few more, while type
inference takes hundreds of milliseconds, and a program using reflective
(`-> infer!`) decoding runs the whole front end twice. The tools below make
that cost visible and avoid paying it repeatedly.

## Timing logs

The `perf` log type prints per-phase and per-item compile timings to stderr:

```bash
BRASS_LOG='brass::perf=debug' brass check app.cz   # phase totals + slowest items
BRASS_LOG_TYPE=perf brass check app.cz               # every item (TRACE)
```

At `debug`, each phase logs its total and its fifteen slowest items:

```text
front/parse-stdlib: total 0.36ms
front/load-modules: total 3.2ms
front/lower-hir: total 1.7ms
typeck/seed-schemes: total 86.0ms
typeck/method-bodies: total 77.9ms
typeck/fn-bodies: total 57.0ms (154 items)
typeck/fn-bodies:     19.1ms  resolve@url
...
front/typecheck: total 258.3ms
back/lower-mir: total 2.3ms
back/monomorphize: total 1.1ms
back/codegen: total 4.0ms
back/finalize: total 91.6ms
```

The phases:

| Phase | What it measures |
| --- | --- |
| `front/parse-stdlib`, `front/load-modules`, `front/lower-hir` | parsing and HIR lowering |
| `typeck/*` | type inference: scheme seeding, precompute passes, per-method and per-function body checks, module initializers, final resolution |
| `front/keyed-repass` | the second full front-end pass a reflective (`-> infer!`) program needs |
| `back/lower-mir`, `back/monomorphize` | MIR lowering and monomorphization |
| `back/codegen-fn`, `back/codegen`, `back/finalize` | per-function LLVM IR emission and the JIT engine build |
| `back/orc-materialize` | first-call native compilation of one function on a warm run (below; per-item, TRACE) |
| `front/cache-hit`, `front/cache-save` | the analysis cache (below) |

Per-function items (`typeck/fn-bodies`, `typeck/method-body`,
`back/codegen-fn`) name the function or `Type.method` they measure, so the
slowest bodies are identifiable directly. Collection is skipped entirely when
the target is disabled, so the instrumentation costs nothing in ordinary runs.

## The context seed (`.czctx`)

The `.czcache` above only helps while nothing changed. The context seed
handles the other case, where the entry file changed but its dependencies
did not, which is every ordinary edit-run cycle and every save in the editor.

A program's **context** is every module except the entry: the embedded
`core` library, the `std` tree, the project's dependencies. On a library-heavy program
that context is where almost all inference time goes, and it does not depend
on the entry at all. So the front end checks in two stages: the context alone
(once), and then the entry against the context's saved **inference tables**:
its type schemes, inferred function and method returns, and globals. With the
tables in hand, the entry-stage run skips every context body and costs roughly
what checking the entry alone costs.

- `brass` stores the tables as `ctx-<hash>.czctx` under the user cache
  directory (`$XDG_CACHE_HOME/brass` or `~/.cache/brass`), per user rather
  than per project, because one context (say, the standard library plus
  `http`) is shared by every program that imports it.
- `czls` keeps them in memory for the session *and* shares the same on-disk
  store, so a save re-checks only the document: the mechanism is one crate
  (`brass_cache` + the seed support in `brass_typeck`), used by both.
- The key is the compiler tag plus the module names and content hashes of
  every context source; the entry's bytes are deliberately not part of it.
  A reflective (`-> infer!`) program's second pass gets its own entry, keyed
  additionally by the requested specialization set, so it too is skipped when
  the same decoders are requested again.
- A context with any diagnostic yields no seed; the full pipeline runs and
  reports as before. An entry that declares a top-level name the context also
  defines drops the seed for that run (the collision changes the context's
  storage symbols), falling back to the full pipeline.

Measured on the `serv` HTTP-server project: an entry edit re-checks in ~20ms
(was ~300ms), an editor save publishes in ~10ms (was ~530ms). On `czpm` (a
reflective program): an entry edit re-checks in ~0.3s (was ~2.2s).

## The analysis cache (`.czcache`)

A clean run writes the front end's results next to the entry file:
`app.cz` produces `app.czcache` (an extension-less script such as `czpm`
produces `czpm.czcache`). The next run of the same entry reuses it and skips
type checking entirely, going straight from a cheap re-lowering to MIR:

```text
brass check app.cz     # cold: full pipeline, writes app.czcache
brass check app.cz     # warm: milliseconds
```

### What is cached

The cache stores what the checker computed, not what the cheap phases produce:

- **The final module ASTs**: after import canonicalization, qualified-use
  resolution, spawn auto-acquire, and reflective (`-> infer!`) specialization.
  Re-lowering these is deterministic and takes a few milliseconds, and caching
  the *post-specialization* graph means a reflective program's second
  front-end pass is skipped too.
- **The checker's channels**: the span-keyed tables the back ends consume
  (resolved expression types, view arguments, `fields(..)` loop expansions,
  `typeof` names, null-propagation sites). Spans reproduce exactly on a hit
  because the cached ASTs carry them and lowering never reassigns one.

### When the cache is reused

A `.czcache` records every on-disk source file the build read: the entry
file and each dependency, transitively. Each is identified by **contents**
(length and SHA-1) and by an **origin-relative reference**, never by machine
path or modification time:

- a project file is recorded relative to the entry file's directory;
- an include-served file relative to *some* include root (validation walks
  the current `BRASS_INCLUDE` roots in resolution order and judges the first
  candidate that exists, so a file that would shadow the recorded one is the
  one checked);
- a package file relative to the named `BRASS_PACKAGES` root -- the standard
  library's own sources among them, under the implicitly bound `std`
  package.
- a native plugin by its canonical import path and binary contents. A hit
  resolves the import again under the current roots, checks the discovered
  `.so`, `.dylib`, or `.dll`, and injects its current path into the cached
  wrapper before lowering.

On load, the cache is used only when the compiler tag matches (version, cache
format, release channel and commit; a working-tree build additionally pins its
own executable's modification time, since its commit does not identify its
source) and every recorded reference resolves to a file with the recorded
contents. Any mismatch falls back to the full pipeline silently.

One resolution-boundary limitation remains: a module cached from an include
root's `.cz` file does not notice a native plugin newly added under an earlier
include root. Plugin-backed entries do re-run ordinary source/plugin resolution,
so the reverse change (a `.cz` file newly shadowing a cached plugin) is rejected.

Content is what makes the scheme sound *and* portable: whichever file the
current roots resolve a reference to, equal bytes are the identical program,
so the whole project can move, the include root can move, and the resolution
environment's *values* need not match the build machine's. It also makes the
stamp exact rather than conservative: rewriting a file with the same bytes (a
checkout, a formatter that changed nothing) does not force a re-check.

Only an analysis with **no diagnostics** is ever written, so a valid cache
also implies the program is clean. Writes are best-effort (a read-only
directory is ignored) and atomic (temporary file + rename).

`BRASS_CACHE=off` disables both reading and writing.

### Distributed caches

Because stamps are origin-relative and content-addressed, a cache written when
a release is packed validates wherever the archive is unpacked: `czpm` ships
with its `bin/czpm.czcache`, whose source and plugin imports resolve through
the installed `std/` next to it, so the package manager starts warm from its
first run. Plugin wrappers store a logical import marker rather than the
packing machine's absolute library path; loading replaces it with the path
found in the installed toolchain. A released compiler is identified by channel
and commit, so every install of the same release reproduces the packing
machine's tag.

### Why the cache unit is the whole program

Per-module caches were considered and measured, and the unit deliberately
stays the entry program. Type inference in Brass is whole-program: spans are
offsets into one concatenated source map whose layout depends on the entry's
import order, inference variables come from one shared counter, and a type's
scheme links variables across every module that touches it, so a module's
inference results are meaningless outside the exact program they were computed
in. What is per-module, parsing and loading, measures 3–7ms of a 300ms–2s
build, about two percent, so a per-module cache could never repay its
complexity. The per-module idea survives in the validation instead: every
module's source is stamped individually, and any one changing invalidates
exactly as a per-module chain would.

### Shared with the language server

`czls` consults the same file: when a document's buffer matches the file on
disk and a valid `.czcache` exists, the full diagnostic pass is skipped. The
cache is only written after an error-free check, so the document is known
clean. The server never *writes* the cache, because its pipeline skips the
driver-only rewrites (spawn auto-acquire, keyed specialization); what it
checked is not byte-for-byte what the driver would run.

### File format

The format is binary and not intended to be read by humans; it favors load
speed and size. A file is:

```text
"PPCACHE\0"                      8-byte magic
len: u8, tag: [u8; len]          compiler tag (version/channel/commit/format;
                                 plus exe-mtime on working-tree builds only)
checksum: [u8; 20]               SHA-1 of the postcard body
payload                          postcard-encoded body
```

The payload is a [postcard](https://docs.rs/postcard/)-serialized structure
(varint-packed serde, no field names, no schema): the resolution environment,
the dependency stamps, the module ASTs, and the checker channels. See
`crates/brass_cache` for the authoritative definition. Because postcard
carries no schema, the header is the only compatibility gate: a tag mismatch
discards the file, and `FORMAT_VERSION` is bumped whenever the payload layout
changes. No cross-version compatibility is attempted; a stale cache is simply
rebuilt.

## Compilation on warm runs

A cache hit removes the check, not compilation, and the run compiles
**lazily**: monomorphization starts from the module initializers and `main`
(a function nothing reachable calls is not compiled at all), every reachable
instance is emitted as unoptimized IR up front (the `back/codegen-fn` items),
and a function is optimized and translated to native code only when execution
first calls it (each such event logs a `back/orc-materialize` item). Code
behind a branch the run never takes is never translated. A `spawn` is the
exception: everything the spawned task could statically reach is translated
before the spawn runs, because worker threads never compile.

`--eager` trades that start-up laziness for the best steady state: the whole
program is compiled as one unit, so calls are direct and small functions
inline into their callers; a lazy run's per-function units instead call each
other through a small indirection. See the
[performance guide](/guides/performance/) for choosing between them.
