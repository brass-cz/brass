#!/usr/bin/env bash
# Front-end-only benchmark: times `brass check` (whole analysis, no JIT, no
# execution) with a cold cache over the checker-shaped regression cases plus
# the real czpm closure. `run.sh` measures end-to-end pipelines; this script
# isolates the type-checking share so a checker regression cannot hide behind
# back-end wins (or the reverse).
#
# Usage: perf_tests/check_bench.sh
#   REPS=5        repetitions per target, minimum reported (default 5)
#   SKIP_BUILD=1  skip the release build of the driver
#
# Output: one line per target with min/mean seconds.

set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
BRASS=./target/release/brass
REPS="${REPS:-5}"
SKIP_BUILD="${SKIP_BUILD:-0}"

if [[ "$SKIP_BUILD" != "1" ]]; then
    ./x cargo build --release -p brass_driver >/dev/null
fi

# The czpm closure needs an entry file; synthesize the same three-line
# launcher the distribution installs, next to a scratch dir so its cache
# artifacts (suppressed anyway by BRASS_CACHE=off) never touch the repo.
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT
cat > "$SCRATCH/czpm.cz" <<'EOF'
import std.package_manager.exec.main

main()!
EOF

measure() {
    local label="$1" file="$2" packages="$3"
    local best="" sum=0 t
    for _ in $(seq "$REPS"); do
        t=$(env BRASS_CACHE=off BRASS_PACKAGES="$packages" sh -c \
            'start=$(date +%s.%N); '"$BRASS"' check '"$file"' >/dev/null 2>&1; end=$(date +%s.%N); echo "$end - $start" | bc')
        sum=$(echo "$sum + $t" | bc)
        if [[ -z "$best" ]] || (( $(echo "$t < $best" | bc) )); then
            best="$t"
        fi
    done
    printf '%-22s min %6.3fs  mean %6.3fs\n' "$label" "$best" "$(echo "$sum / $REPS" | bc -l)"
}

measure "12_diamond_infer" "perf_tests/cases/12_diamond_infer.cz" ""
measure "13_sum_candidates" "perf_tests/cases/13_sum_candidates.cz" ""
measure "czpm_closure" "$SCRATCH/czpm.cz" "std=$ROOT"
