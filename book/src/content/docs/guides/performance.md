---
title: "Performance"
description: "What a run pays at start-up, how compiled code runs, and when --eager is the right tool."
---

Brass optimizes for the edit-run cycle: a run starts executing before the
whole program is checked or compiled, and analysis results are cached so the
next run skips them. This chapter explains what that buys, what it costs, and
when to reach for `--eager` instead.

## What a run pays at start-up

`brass app.cz` interleaves everything it can:

- **Checking is lazy.** Type inference starts at the entry and settles other
  functions as compilation demands them; code the run never needs is checked
  in the background without delaying it (see
  [Execution model](/references/execution/)).
- **Compilation is lazy too.** A function is optimized and translated to
  native code the first time execution reaches it. A branch the run never
  takes is never compiled.
- **Analysis is cached.** A clean run (or `brass check`) writes
  `app.czcache`; later runs of the unchanged program skip type checking
  entirely and go straight to compiling on demand (see
  [Performance & caching](/references/performance/)).

So a warm run pays milliseconds of start-up plus native compilation of
exactly the functions it executes.

```bash
brass app.cz          # first run: checks and compiles as it executes
brass check app.cz    # whole-program verdict; writes app.czcache
brass app.cz          # warm run: no checking, compiles on demand
```

## How compiled code runs

Native code is optimized identically in every mode; what differs is the
**compilation unit**:

- On the default lazy run, each function is compiled separately, behind a
  small indirection that lets it compile on first call. Calls between
  functions stay indirect, and a function is never inlined into its callers.
- Under `--eager`, the whole program is compiled as one unit before it runs:
  calls are direct, and small hot functions inline away.

For most programs -- scripts, I/O-bound tools, anything whose time goes into
the runtime or the standard library -- the difference is not measurable. It
shows on **hot loops making very frequent calls to tiny functions**, where
the call indirection becomes the loop body: a tight loop calling a two-line
helper fifty million times ran about three times faster under `--eager` in
our measurements. Self-recursion is unaffected (a function calling itself
stays within its own unit), and loops that do their work inline lose nothing.

## When to use `--eager`

```bash
brass --eager app.cz
```

`--eager` checks the whole program first (the same verdict as `brass check`),
then compiles it as one optimized unit and runs it. The semantics are
identical to the default run; only where time is spent differs.

Reach for it when:

- the program is **compute-heavy and long-running**: seconds of runtime dwarf
  the up-front compile, and the tightest loops get direct, inlinable calls;
- you are **measuring performance**: an eager run also keeps first-call
  compilation out of your timings;
- you want the **whole-program verdict and the run** in one command.

Stay with the default when start-up latency matters: short scripts,
command-line tools, and large programs where any single run executes a small
slice of the code.

## Concurrency

`spawn` changes one thing: everything the spawned task could statically reach
is compiled before the spawn runs, because worker threads never compile. Code
only the main thread can reach stays on demand, so a spawning program still
starts lazily.

## Measuring

`BRASS_LOG='brass::perf=debug' brass app.cz` prints where the time went --
per phase, per function, and (on warm runs) one line per first-call
compilation. See [Performance & caching](/references/performance/) for the
phase list and the caches in detail.
