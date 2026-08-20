#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
data_dir="$repo_root/src/formace_ext/tests/data"
test_dir=$(mktemp -d /tmp/fm_eco_test.XXXXXX)
trap 'rm -rf "$test_dir"' EXIT

make -C "$repo_root" -j4 ABC_USE_NO_READLINE=1 abc

run_mode() {
  local label=$1
  local expected_support=$2
  local expected_inputs=$3
  shift 3
  local mode_dir="$test_dir/$label"
  local result verify
  mkdir -p "$mode_dir"
  result=$(
    cd "$mode_dir"
    "$repo_root/abc" -c \
      "fm_eco -T 30 -c -u -v $* $data_dir/eco_minimum_F.v $data_dir/eco_minimum_G.v $data_dir/eco_minimum_weights.txt"
  )
  printf '%s\n' "$result"
  printf '%s' "$result" | rg -q "ForMACE fm_eco: support=$expected_support function=ITP"
  printf '%s' "$result" | rg -q "ForMACE fm_eco interpolant: inputs = $expected_inputs"
  printf '%s' "$result" | rg -q 'The ECO solution was verified successfully'
  printf '%s' "$result" | rg -q "Patch[[:space:]]+: in = $expected_inputs[[:space:]]+out = 1"
  printf '%s' "$result" | rg -q 'Networks are equivalent'
  test -s "$mode_dir/patch.v"
  test -s "$mode_dir/out.v"
  verify=$(
    cd "$mode_dir"
    "$repo_root/abc" -c "cec $data_dir/eco_minimum_G.v out.v"
  )
  printf '%s\n' "$verify"
  printf '%s' "$verify" | rg -q 'Networks are equivalent'
}

run_mode assumption_only assumption-only 3 -a
run_mode original original 2
run_mode minimum minimum 2 -m -w

minimum_log=$(
  cd "$test_dir/minimum"
  "$repo_root/abc" -c \
    "fm_eco -T 30 -c -u -m -w $data_dir/eco_minimum_F.v $data_dir/eco_minimum_G.v $data_dir/eco_minimum_weights.txt"
)
printf '%s' "$minimum_log" | rg -q \
  'ForMACE runeco MinUNSAT selected 2 new divisors \(with 0 previous, from 7 candidates\)'
printf '%s' "$minimum_log" | rg -q \
  'ForMACE runeco brute-force audit PASS: all 8 smaller subsets are SAT'

printf 'fm_eco assumption-only/original/minimum support ITP tests passed\n'
