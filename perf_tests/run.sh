#!/usr/bin/env bash
# Benchmark harness comparing the two JIT pipelines of the Brass driver:
#   lazy  -- the default demand-driven pipeline (checker thread + per-function
#            ORC materialization)
#   eager -- `brass --eager`, whole-program check + IR for every instance
#            first; optimization and instruction selection still run on
#            first use
#
# For every program in cases/ it measures, over REPS repetitions per mode:
#   total  -- wall time of the whole run (compile + execute + exit)
#   first  -- time until the program's first output line appears (the lazy
#             pipeline's reason to exist: execution starts before the whole
#             program is checked/compiled)
# Every run checks the program from source; only native objects persist, in
# the JIT cache under XDG_CACHE_HOME. Each case/mode cell owns its own cache
# directory: "cold" empties it before every run (compile and store), "warm"
# keeps what the cell's warmup run stored (link cached objects). Lazy and eager
# stdout are also compared: a semantic divergence between the pipelines is a
# bug and is called out in the report.
#
# Usage: perf_tests/run.sh
#   REPS=5             repetitions per case/mode/cache (default 5)
#   CASES=regex        run only case files whose name matches (egrep)
#   CACHE_MODES="cold warm"  which JIT-cache states to measure
#   SKIP_BUILD=1       skip the release build of the driver
#
# Results land in perf_tests/results/<timestamp>/ (raw.csv + report.md); the
# report is also copied to perf_tests/results/latest-report.md.

set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
BRASS=./target/release/brass

REPS="${REPS:-5}"
CASES_RE="${CASES:-.}"
CACHE_MODES="${CACHE_MODES:-cold warm}"
SKIP_BUILD="${SKIP_BUILD:-0}"
RUN_TIMEOUT="${RUN_TIMEOUT:-180}"

if [[ "$SKIP_BUILD" != 1 ]]; then
    echo "== building the driver (release) =="
    ./x cargo build --release -p brass_driver || exit 1
fi
[[ -x "$BRASS" ]] || { echo "error: $BRASS not found" >&2; exit 1; }

RESULTS_DIR=perf_tests/results
STAMP="$(date +%Y%m%d-%H%M%S)"
RUN_DIR="$RESULTS_DIR/$STAMP"
TMP="$RUN_DIR/.tmp"
JIT_ROOT="$RUN_DIR/.jit-cache"
mkdir -p "$TMP" "$JIT_ROOT"
CSV="$RUN_DIR/raw.csv"
MISMATCHES="$RUN_DIR/mismatches.txt"
FAILURES="$RUN_DIR/failures.txt"
echo "case,cache,mode,rep,total_ms,first_ms,status" > "$CSV"
: > "$MISMATCHES"
: > "$FAILURES"

ms_between() { # start_epochrealtime end_epochrealtime -> milliseconds
    awk -v a="$1" -v b="$2" 'BEGIN { printf "%.1f", (b - a) * 1000 }'
}

# Run one case once. Sets R_TOTAL / R_FIRST / R_STATUS; stdout in $TMP/out.
# The first-output timestamp works because the runtime's stdout is
# line-buffered even on a pipe (Rust's LineWriter), so the reader side sees
# the first println as soon as the program emits it.
run_one() { # file mode(lazy|eager) cache(cold|warm)
    local file=$1 mode=$2 cache=$3
    local name xdg
    name=$(basename "$file" .cz)
    xdg="$JIT_ROOT/$name-$mode-$cache"
    [[ "$cache" == cold ]] && rm -rf -- "$xdg"
    local -a cmd=(timeout "$RUN_TIMEOUT" "$BRASS")
    [[ "$mode" == eager ]] && cmd+=(--eager)
    cmd+=("$file")
    local -a envv=(env -u BRASS_LOG -u BRASS_LOG_TYPE -u BRASS_JIT_CACHE "XDG_CACHE_HOME=$xdg")
    rm -f "$TMP/first" "$TMP/status"
    local t0 t1
    t0=$EPOCHREALTIME
    { "${envv[@]}" "${cmd[@]}" 2> "$TMP/err"; echo $? > "$TMP/status"; } | {
        if IFS= read -r first_line; then
            printf '%s\n' "$EPOCHREALTIME" > "$TMP/first"
            { printf '%s\n' "$first_line"; cat; } > "$TMP/out"
        else
            : > "$TMP/out"
        fi
    }
    t1=$EPOCHREALTIME
    R_STATUS=$(cat "$TMP/status" 2>/dev/null || echo 99)
    R_TOTAL=$(ms_between "$t0" "$t1")
    R_FIRST=""
    [[ -s "$TMP/first" ]] && R_FIRST=$(ms_between "$t0" "$(cat "$TMP/first")")
}

echo "== running benchmarks (REPS=$REPS, cache: $CACHE_MODES) =="
shopt -s nullglob
for file in perf_tests/cases/*.cz; do
    name=$(basename "$file" .cz)
    [[ "$name" =~ $CASES_RE ]] || continue
    for cache in $CACHE_MODES; do
        for mode in lazy eager; do
            # Warmup run: primes the OS page cache (and, for warm, this cell's
            # JIT cache), validates the case, and captures the output used for
            # the lazy-vs-eager comparison.
            run_one "$file" "$mode" "$cache"
            if [[ "$R_STATUS" != 0 ]]; then
                echo "  $name/$cache/$mode: FAILED (exit $R_STATUS)"
                {
                    echo "== $name/$cache/$mode (exit $R_STATUS)"
                    tail -5 "$TMP/err"
                } >> "$FAILURES"
                echo "$name,$cache,$mode,0,,,fail" >> "$CSV"
                continue
            fi
            cp "$TMP/out" "$TMP/expected-$name-$cache-$mode"
            for rep in $(seq 1 "$REPS"); do
                run_one "$file" "$mode" "$cache"
                [[ "$R_STATUS" == 0 ]] || { echo "$name,$cache,$mode,$rep,,,fail" >> "$CSV"; continue; }
                echo "$name,$cache,$mode,$rep,$R_TOTAL,$R_FIRST,ok" >> "$CSV"
            done
            echo "  $name/$cache/$mode: done"
        done
        # The two pipelines must agree on program output.
        if [[ -f "$TMP/expected-$name-$cache-lazy" && -f "$TMP/expected-$name-$cache-eager" ]] &&
            ! cmp -s "$TMP/expected-$name-$cache-lazy" "$TMP/expected-$name-$cache-eager"; then
            {
                echo "== $name ($cache): lazy and eager stdout differ"
                diff "$TMP/expected-$name-$cache-lazy" "$TMP/expected-$name-$cache-eager" | head -10
            } >> "$MISMATCHES"
        fi
    done
done

# ---------------------------------------------------------------------------
# Report generation: aggregate raw.csv into a markdown report.
# ---------------------------------------------------------------------------
REPORT="$RUN_DIR/report.md"
GIT_REV=$(git rev-parse --short HEAD 2>/dev/null || echo unknown)
CPU=$(lscpu 2>/dev/null | sed -n 's/^Model name: *//p' | head -1)

{
    echo "# Brass lazy vs eager benchmark"
    echo
    echo "- date: $(date -Iseconds)"
    echo "- commit: $GIT_REV"
    echo "- cpu: ${CPU:-unknown} ($(nproc 2>/dev/null || echo '?') threads)"
    echo "- reps per cell: $REPS (tables show min over reps; mean in parens)"
    echo "- lazy = default pipeline, eager = \`brass --eager\`"
    echo "- total = wall time of the whole run; first = time to first output line"
    echo "- cold = empty JIT cache before every run; warm = JIT cache primed by the cell's warmup run"
} > "$REPORT"

for cache in $CACHE_MODES; do
{
    echo
    if [[ "$cache" == cold ]]; then
        echo "## Cold JIT cache"
    else
        echo "## Warm JIT cache"
    fi
    echo
    echo "| case | eager total | lazy total | lazy/eager | eager first | lazy first |"
    echo "|------|------------:|-----------:|-----------:|------------:|-----------:|"
} >> "$REPORT"
awk -F, -v cache="$cache" '
    NR > 1 && $2 == cache && $7 == "ok" {
        key = $1 SUBSEP $3
        if (!(key in tmin) || $5 + 0 < tmin[key]) tmin[key] = $5 + 0
        tsum[key] += $5; tcnt[key]++
        if ($6 != "" && (!(key in fmin) || $6 + 0 < fmin[key])) fmin[key] = $6 + 0
        if (!seen[$1]++) order[++n] = $1
    }
    NR > 1 && $2 == cache && $7 == "fail" {
        failed[$1 SUBSEP $3] = 1
        if (!seen[$1]++) order[++n] = $1
    }
    function cell(key) {
        if (key in failed) return "FAILED"
        if (!(key in tcnt)) return "-"
        return sprintf("%.0f (%.0f)", tmin[key], tsum[key] / tcnt[key])
    }
    function fcell(key) {
        if (key in failed || !(key in fmin)) return "-"
        return sprintf("%.0f", fmin[key])
    }
    END {
        for (i = 1; i <= n; i++) {
            c = order[i]
            ek = c SUBSEP "eager"; lk = c SUBSEP "lazy"
            ratio = "-"
            if ((ek in tmin) && (lk in tmin) && tmin[ek] > 0)
                ratio = sprintf("%.2f", tmin[lk] / tmin[ek])
            printf "| %s | %s | %s | %s | %s | %s |\n",
                c, cell(ek), cell(lk), ratio, fcell(ek), fcell(lk)
        }
    }
' "$CSV" >> "$REPORT"
echo >> "$REPORT"
echo "(times in ms; lazy/eager < 1 means lazy is faster)" >> "$REPORT"
done

{
    echo
    echo "## Cases"
    echo
    for file in perf_tests/cases/*.cz; do
        name=$(basename "$file" .cz)
        [[ "$name" =~ $CASES_RE ]] || continue
        # First sentence of the leading comment block (skipping the GENERATED
        # marker line of machine-generated cases).
        desc=$(awk '
            /^\/\// {
                sub(/^\/\/ ?/, "")
                if ($0 ~ /^GENERATED/) next
                s = s $0 " "
                if (s ~ /\./) { sub(/\..*/, ".", s); print s; exit }
                next
            }
            { exit }
        ' "$file")
        echo "- **$name** -- $desc"
    done
    if [[ -s "$MISMATCHES" ]]; then
        echo
        echo "## Output mismatches (BUGS: the pipelines disagree)"
        echo
        echo '```'
        cat "$MISMATCHES"
        echo '```'
    fi
    if [[ -s "$FAILURES" ]]; then
        echo
        echo "## Failures"
        echo
        echo '```'
        cat "$FAILURES"
        echo '```'
    fi
} >> "$REPORT"

rm -rf "$TMP" "$JIT_ROOT"
cp "$REPORT" "$RESULTS_DIR/latest-report.md"
echo
echo "== report: $REPORT (copied to $RESULTS_DIR/latest-report.md) =="
echo
cat "$REPORT"
