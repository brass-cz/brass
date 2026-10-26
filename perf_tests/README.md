# perf_tests

Benchmarks comparing the driver's two JIT pipelines: **lazy** (the default:
type inference on a checker thread, per-function ORC materialization on
demand) and **eager** (`brass --eager`: whole-program check and IR for every
instance before execution; optimization and instruction selection still run
on first use).

## Run

```sh
perf_tests/run.sh
```

The script release-builds the driver (`./x cargo build --release -p
brass_driver`), runs every program in `cases/` under both pipelines, and writes
`results/<timestamp>/report.md` (also copied to `results/latest-report.md`).
Every run checks the case from source; only native objects persist, in the
JIT cache under `XDG_CACHE_HOME`. Each case/mode cell gets its own cache
directory: **cold** empties it before every run (the run compiles and stores
its objects), **warm** keeps what the cell's warmup run stored (the run links
cached objects instead of compiling). Two metrics per run: **total** wall
time and **first** (time to the first output line -- every case prints `begin`
as its first statement, so this captures how soon execution starts). Lazy and
eager stdout are compared; any divergence is listed in the report as a bug.

Knobs (environment variables): `REPS` (default 5), `CASES=<regex>` to filter
case files, `CACHE_MODES="cold warm"`, `SKIP_BUILD=1`, `RUN_TIMEOUT` seconds.

## Cases

Each `cases/*.cz` file targets one characteristic where the pipelines can
differ; the first comment line of each file states what it measures. Broad
groups:

- compile-dominated: `02_wide_cold_unused`, `03_wide_all_called`,
  `06_infer_chain`, `07_mono_heavy`, `09_big_main` (cold-start cost, breadth
  of checking/compiling, inference deferral)
- checker-dominated: `12_diamond_infer` (open-argument call-site
  re-elaboration blowup), `13_sum_candidates` (per-call-site sum-method
  candidate elaboration)
- runtime-dominated: `01_hot_loop`, `04_call_heavy`, `05_cross_module`,
  `08_recursion`, `11_closures_hot` (code quality, call/stub indirection)
- concurrency: `10_spawn_tasks` (spawn-reachable precompile)

`check_bench.sh` times `brass check` alone over the checker-dominated
cases plus the real czpm closure, isolating the front end from back-end
changes.

`czpm_bench.sh` measures `czpm run` on a small project with a path
dependency, from launch to the program's first output line, for each
combination of cold/warm JIT cache and default/`BRASS_OPT=2` compilation. Each
cell has its own launcher, project, `HOME`, and cache. The minimum over `REPS`
runs must stay under the ceilings in `thresholds.env` (overridable from the
environment); the script exits non-zero otherwise.

Files marked `GENERATED` are produced by `gen_cases.py`; edit the size
constants there and rerun it to re-scale the corpus (the generated files are
checked in).
