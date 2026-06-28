#!/usr/bin/env bash
# Build the compiler and run every example, printing its output.
set -euo pipefail

cd "$(dirname "$0")"
cargo build --quiet -p prepoly_driver
BIN=./target/debug/prepoly

examples=(
    examples/01_records.pp
    examples/02_sum_types.pp
    examples/03_interfaces.pp
    examples/04_sum_interface.pp
    examples/05_nullable_and_result.pp
    examples/06_structural_subtyping.pp
    examples/07_closures.pp
    examples/08_pattern_matching.pp
    examples/09_collections.pp
    examples/10_strings_and_conversions.pp
    examples/11_control_flow.pp
    examples/12_concurrency.pp
    examples/13_file_io.pp
    examples/14_type_safety.pp
    examples/15_numeric_conversions.pp
    examples/16_method_inference.pp
    examples/17_higher_order.pp
    examples/18_ufcs.pp
    examples/modules/main.pp
)

for ex in "${examples[@]}"; do
    echo "===== $ex ====="
    "$BIN" "$ex"
    echo
done
