---
title: "Performance"
description: "What a run pays at start-up, how compiled code runs, and when --eager is the right tool."
---

The default command is tuned for short edit-run cycles. Start with
`brass app.cz`; use `brass check` when you need a complete check, and add
`--eager` when every diagnostic must be reported before the program starts.

## What a run pays at start-up

`brass app.cz` avoids waiting for work the run may not need:

- Each function is checked before it can execute. Unused functions do not
  delay the current run, so a successful run is only a verdict on the code it
  needed. Use `brass check` to check every function.
- Native code is compiled when it is needed. Code behind an untaken branch
  may never be compiled during that run.
- Analysis is cached. A completed check can be reused in full; if background
  checking stops when the program exits, the next run can resume from the
  partial result.

These details normally require no tuning. The practical commands are:

```bash
brass app.cz          # run with low start-up latency
brass check app.cz    # check the complete program without running it
brass --eager app.cz  # check the complete program, then run
```

## When to use `--eager`

```bash
brass --eager app.cz
```

`--eager` finishes the whole-program check before execution begins. Native
compilation is unchanged -- both commands optimize and translate functions on
first use -- so the flag buys a complete verdict up front, not different
generated code, at the cost of checking code the run may never need.

Reach for it when:

- you want a complete check and the run in one command;
- every diagnostic must appear before the program produces output or side
  effects (a default run stops at an error in code it reaches, which can be
  after earlier output);
- you are diagnosing a difference between a default run and `brass check`.

Stay with the default for scripts, command-line tools, I/O-bound programs, and
large applications that use only a small part of their code in one run. For a
fast repeated run, `brass check` once and let the full analysis cache carry
the later runs; see [Caches](#caches).

## Caches

Cache files are an implementation aid, not build artifacts you need to
manage. They are ignored when sources, dependencies, plugins, or the compiler
change. Set `BRASS_CACHE=off` when diagnosing cache behavior or comparing cold
runs. See [Performance and caching](/references/performance/) for cache kinds,
validation, and timing logs.

## Measuring

`BRASS_LOG='brass::perf=debug' brass app.cz` prints phase totals and the
slowest checked or compiled items. Measure before choosing `--eager`; most
programs should keep the default.
