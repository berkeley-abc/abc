#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
data_dir="$repo_root/src/formace_ext/tests/data"
test_dir=$(mktemp -d /tmp/fm_runeco_minimum.XXXXXX)
trap 'rm -rf "$test_dir"' EXIT

make -C "$repo_root" -j4 ABC_USE_NO_READLINE=1 abc

result=$(
  cd "$test_dir"
  "$repo_root/abc" -c \
    "runeco -T 30 -c -u -m -v -w $data_dir/eco_minimum_F.v $data_dir/eco_minimum_G.v $data_dir/eco_minimum_weights.txt"
)

printf '%s\n' "$result"
printf '%s' "$result" | rg -q \
  'ForMACE runeco MinUNSAT selected 2 new divisors \(with 0 previous, from 7 candidates\)'
printf '%s' "$result" | rg -q \
  'ForMACE runeco brute-force audit PASS: all 8 smaller subsets are SAT'
printf '%s' "$result" | rg -q 'Patch[[:space:]]+: in = 2[[:space:]]+out = 1'
printf '%s' "$result" | rg -q 'Networks are equivalent'

verify=$(
  cd "$test_dir"
  "$repo_root/abc" -c "cec $data_dir/eco_minimum_G.v out.v"
)
printf '%s\n' "$verify"
printf '%s' "$verify" | rg -q 'Networks are equivalent'

printf 'runeco MinUNSAT real-encoding minimum audit passed\n'
