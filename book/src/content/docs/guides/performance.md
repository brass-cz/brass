---
title: "Performance"
description: "What a run pays at start-up, how compiled code runs, and when --eager is the right tool."
---

The default command is tuned for short edit-run cycles. Start with
`brass app.cz`; use `brass check` to check own code completely, and add
`--eager` when selected diagnostics must be reported before the program starts.
All modes check dependency bodies only where reached or needed for shared
inference; importing a declaration does not by itself require its body.

## What a run pays at start-up

`brass app.cz` avoids waiting for work the run may not need:

- Each function is checked before it can execute. Unused functions do not
  delay the current run, so a successful run is only a verdict on the code it
  needed. Use `brass check` to check every own function.
- Native code is compiled when it is needed. Code behind an untaken branch
  may never be compiled during that run.
- Checking is never cached: each run checks what it needs from source. Native
  code is: a group of functions compiled once is reused from the JIT cache
  until its generated code changes, so a repeated run skips most native
  compilation. See [JIT cache](/references/performance/#jit-cache).

These details normally require no tuning. The practical commands are:

```bash
brass app.cz          # run with low start-up latency
brass check app.cz    # check own code + reached dependencies
brass --eager app.cz  # check own code + reached dependencies, then run
```

## When to use `--eager`

```bash
brass --eager app.cz
```

`--eager` finishes checking own code and reached dependencies before execution begins. Native
compilation is unchanged -- both commands optimize and translate functions on
first use -- so the flag buys the selected verdict up front, not different
generated code, at the cost of checking code the run may never need.

Reach for it when:

- you want a complete check and the run in one command;
- every selected diagnostic must appear before the program produces output or side
  effects (a default run stops at an error in code it reaches, which can be
  after earlier output);
- you are diagnosing a difference between a default run and `brass check`.

Stay with the default for scripts, command-line tools, I/O-bound programs, and
large applications that use only a small part of their code in one run.

## When to use `BRASS_OPT=2`

The default run translates functions at the lowest optimization level to keep
start-up short. A long-running or compute-bound program can set `BRASS_OPT=2`
to compile with the full optimizing pipeline instead: start-up slows by the
optimizer's cost per compiled group, and every function runs at full native
quality from its first call. See the
[native compilation reference](/references/performance/#native-compilation).

## Measuring

`BRASS_LOG='brass::perf=debug' brass app.cz` prints phase totals and the
slowest checked or compiled items; see
[Performance diagnostics](/references/performance/) for the phases. Measure before choosing `--eager`; most
programs should keep the default.
