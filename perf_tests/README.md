# perf_tests

Benchmarks comparing the driver's two JIT pipelines: **lazy** (the default:
type inference on a checker thread, per-function ORC materialization on
demand) and **eager** (`brass --eager`: whole-program check, then a full
module compile before execution).

## Run

```sh
perf_tests/run.sh
```

The script release-builds the driver (`./x cargo build --release -p
brass_driver`), runs every program in `cases/` under both pipelines with a
cold compilation cache (`BRASS_CACHE=off`) and a warm one, and writes
`results/<timestamp>/report.md` (also copied to `results/latest-report.md`).
Warm cells are same-mode primed: the per-entry analysis cache
(`<case>.czcache`, written next to the source) is reset and then primed by a
warmup run of the measured mode, because the two modes persist different
payloads -- an eager run writes the full analysis, while a lazy run persists
only the instances the execution actually reached (a partial cache the next
lazy run resumes from, re-checking the rest in the background). The
`XDG_CACHE_HOME` override isolates the shared context-seed cache (`.czctx`)
from the user's real one. Two metrics per run: **total** wall time and
**first** (time to the first output line -- every case prints `begin` as its
first statement, so this captures how soon execution starts). Lazy and eager
stdout are compared; any divergence is listed in the report as a bug.

Knobs (environment variables): `REPS` (default 5), `CASES=<regex>` to filter
case files, `CACHE_MODES="cold warm"`, `SKIP_BUILD=1`, `RUN_TIMEOUT` seconds.

## Cases

Each `cases/*.cz` file targets one characteristic where the pipelines can
differ; the first comment line of each file states what it measures. Broad
groups:

- compile-dominated: `02_wide_cold_unused`, `03_wide_all_called`,
  `06_infer_chain`, `07_mono_heavy`, `09_big_main` (cold-start cost, breadth
  of checking/compiling, inference deferral)
- runtime-dominated: `01_hot_loop`, `04_call_heavy`, `05_cross_module`,
  `08_recursion`, `11_closures_hot` (code quality, call/stub indirection)
- concurrency: `10_spawn_tasks` (spawn-reachable precompile)

Files marked `GENERATED` are produced by `gen_cases.py`; edit the size
constants there and rerun it to re-scale the corpus (the generated files are
checked in).

## Known pipeline divergence

An unannotated-return call chain of int64 functions deeper than 64 aborts
under the lazy pipeline (`deferred instance ... resolved with return type
int64 but its call site was compiled for int32`) while eager runs it fine;
`06_infer_chain` therefore uses an int32 chain. Reproduce with
`gen_cases.py`'s chain generator switched back to int64 at depth >= 65.
