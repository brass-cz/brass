#!/usr/bin/env bash
# End-to-end `czpm run` time to the child program's first stdout line.
# Each cache/optimization cell owns its launcher, project, and XDG cache so
# analysis and native-object artifacts cannot leak between measurements.

set -u -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BRASS="$ROOT/target/release/brass"
REPS="${REPS:-5}"
SKIP_BUILD="${SKIP_BUILD:-0}"
RUN_TIMEOUT="${RUN_TIMEOUT:-180}"

source "$ROOT/perf_tests/thresholds.env"

if [[ ! "$REPS" =~ ^[1-9][0-9]*$ ]]; then
    echo "error: REPS must be a positive integer" >&2
    exit 2
fi

if [[ "$SKIP_BUILD" != 1 ]]; then
    echo "== building the driver (release) =="
    "$ROOT/x" cargo build --release -p brass_driver || exit 1
fi
[[ -x "$BRASS" ]] || { echo "error: $BRASS not found" >&2; exit 1; }

TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/brass-czpm-bench.XXXXXX")"
trap 'rm -rf -- "$TMP_ROOT"' EXIT

case "$(uname -s)" in
    CYGWIN*|MINGW32*|MSYS*|MINGW*) PACKAGE_SEPARATOR=';' ;;
    *) PACKAGE_SEPARATOR=':' ;;
esac

ms_between() {
    awk -v a="$1" -v b="$2" 'BEGIN { printf "%.1f", (b - a) * 1000 }'
}

create_fixture() {
    local cell=$1
    mkdir -p "$cell/shim" "$cell/project" "$cell/helper" "$cell/home" "$cell/xdg"
    ln -s "$BRASS" "$cell/shim/brass"

    cat > "$cell/shim/czpm" <<'CZPM'
#!/usr/bin/env brass

import std.package_manager.exec.main

main()!
CZPM
    chmod +x "$cell/shim/czpm"

    cat > "$cell/project/package.toml" <<'MANIFEST'
[package]
name = "bench_app"
authors = ""
license = "MIT"

[dependencies]
helper = { path = "../helper" }
MANIFEST

    cat > "$cell/project/bench_app.cz" <<'BRASS'
import helper.{ message }

println(message())
BRASS

    cat > "$cell/helper/package.toml" <<'MANIFEST'
[package]
name = "helper"
authors = ""
license = "MIT"

[dependencies]
MANIFEST

    cat > "$cell/helper/helper.cz" <<'BRASS'
fun message() -> string {
    return "czpm bench ready"
}
BRASS
}

run_in_cell() {
    local cell=$1 cache=$2 opt=$3 packages=$4
    shift 4
    local -a envv=(
        env
        -u BRASS_CACHE
        -u BRASS_INCLUDE
        -u BRASS_JIT_CPU
        -u BRASS_LOG
        -u BRASS_LOG_TYPE
        -u BRASS_OBJ_PRECOMPILE
        -u BRASS_OPT
        -u XDG_CACHE_HOME
        "PATH=$cell/shim:$PATH"
        "HOME=$cell/home"
        "BRASS_PACKAGES=$packages"
    )
    if [[ "$cache" == cold ]]; then
        envv+=(BRASS_CACHE=off)
    else
        envv+=(XDG_CACHE_HOME="$cell/xdg")
    fi
    [[ "$opt" == o2 ]] && envv+=(BRASS_OPT=2)
    (
        cd "$cell/project"
        "${envv[@]}" "$@"
    )
}

prime_warm_cell() {
    local cell=$1 opt=$2
    local std_packages="std=$ROOT"
    local child_packages="${std_packages}${PACKAGE_SEPARATOR}helper=$cell/helper"

    run_in_cell "$cell" warm "$opt" "$std_packages" \
        "$BRASS" check "$cell/shim/czpm" >/dev/null || return
    run_in_cell "$cell" warm "$opt" "$child_packages" \
        "$BRASS" check "$cell/project/bench_app.cz" >/dev/null || return
    run_one "$cell" warm "$opt"
    [[ "$R_STATUS" == 0 ]]
}

# Sets R_FIRST, R_STATUS, and R_LINE for one `czpm run` invocation.
run_one() {
    local cell=$1 cache=$2 opt=$3
    local first_file="$cell/first"
    local status_file="$cell/status"
    local line_file="$cell/line"
    local error_file="$cell/stderr"
    local t0 t1

    rm -f -- "$first_file" "$status_file" "$line_file" "$error_file"
    t0=$EPOCHREALTIME
    {
        run_in_cell "$cell" "$cache" "$opt" "std=$ROOT" \
            timeout "$RUN_TIMEOUT" czpm run 2> "$error_file"
        echo $? > "$status_file"
    } | {
        if IFS= read -r first_line; then
            printf '%s\n' "$EPOCHREALTIME" > "$first_file"
            printf '%s\n' "$first_line" > "$line_file"
            cat >/dev/null
        fi
    }
    t1=$EPOCHREALTIME

    R_STATUS=$(cat "$status_file" 2>/dev/null || echo 99)
    R_LINE=$(cat "$line_file" 2>/dev/null || true)
    R_FIRST=""
    [[ -s "$first_file" ]] && R_FIRST=$(ms_between "$t0" "$(cat "$first_file")")
    if [[ "$R_STATUS" == 0 && ( -z "$R_FIRST" || "$R_LINE" != "czpm bench ready" ) ]]; then
        R_STATUS=98
    fi
}

echo "== czpm run TTFO (REPS=$REPS) =="
rows=()
failed=0
for cache in cold warm; do
    for opt in default o2; do
        cell="$TMP_ROOT/$cache-$opt"
        create_fixture "$cell"
        if [[ "$cache" == warm ]] && ! prime_warm_cell "$cell" "$opt"; then
            echo "error: failed to prime $cache/$opt" >&2
            tail -10 "$cell/stderr" >&2 2>/dev/null || true
            rows+=("$cache|$opt|-|-|-|FAIL")
            failed=1
            continue
        fi

        # Match the main perf harness: warm OS pages once before recorded reps.
        if ! run_one "$cell" "$cache" "$opt" || [[ "$R_STATUS" != 0 ]]; then
            echo "error: warmup failed for $cache/$opt (exit $R_STATUS)" >&2
            tail -10 "$cell/stderr" >&2 2>/dev/null || true
            rows+=("$cache|$opt|-|-|-|FAIL")
            failed=1
            continue
        fi

        samples=()
        for rep in $(seq 1 "$REPS"); do
            run_one "$cell" "$cache" "$opt"
            if [[ "$R_STATUS" != 0 ]]; then
                echo "error: $cache/$opt rep $rep failed (exit $R_STATUS)" >&2
                tail -10 "$cell/stderr" >&2 2>/dev/null || true
                failed=1
                break
            fi
            samples+=("$R_FIRST")
        done
        if [[ "${#samples[@]}" -ne "$REPS" ]]; then
            rows+=("$cache|$opt|-|-|-|FAIL")
            continue
        fi

        read -r minimum mean < <(
            printf '%s\n' "${samples[@]}" | awk '
                NR == 1 { min = $1 }
                { if ($1 < min) min = $1; sum += $1 }
                END { printf "%.1f %.1f\n", min, sum / NR }
            '
        )
        if [[ "$cache" == cold ]]; then
            threshold=$czpm_run_cold_ms
        else
            threshold=$czpm_run_warm_ms
        fi
        result=PASS
        if awk -v measured="$minimum" -v limit="$threshold" \
            'BEGIN { exit !(measured > limit) }'; then
            result=FAIL
            failed=1
        fi
        rows+=("$cache|$opt|$minimum|$mean|$threshold|$result")
    done
done

echo
echo '| cache | BRASS_OPT | min TTFO (ms) | mean TTFO (ms) | ceiling (ms) | result |'
echo '|-------|-----------|---------------:|----------------:|-------------:|--------|'
for row in "${rows[@]}"; do
    IFS='|' read -r cache opt minimum mean threshold result <<< "$row"
    [[ "$opt" == default ]] && opt=unset
    echo "| $cache | $opt | $minimum | $mean | $threshold | $result |"
done

exit "$failed"
