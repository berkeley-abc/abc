#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
data_dir="$repo_root/src/formace_ext/tests/data"
test_dir=$(mktemp -d /tmp/fm_runeco_global.XXXXXX)
trap 'rm -rf "$test_dir"' EXIT

make -C "$repo_root" -j4 ABC_USE_NO_READLINE=1 abc

result=$(
  cd "$test_dir"
  "$repo_root/abc" -c \
    "runeco -T 30 -c -i -u -g -v $data_dir/eco_global_F.v $data_dir/eco_global_G.v $data_dir/eco_global_weights.txt"
)

printf '%s\n' "$result"
printf '%s' "$result" | rg -q \
  'ForMACE runeco: support=global-fixed-relations function=SOP unit_weights=yes'
printf '%s' "$result" | rg -q \
  'ForMACE runeco global MinUNSAT selected 2 divisors across 2 fixed target relations \(from 3 candidates\)'
printf '%s' "$result" | rg -q \
  'ForMACE runeco global support is sufficient for evolving target 1'
printf '%s' "$result" | rg -q \
  'ForMACE runeco global support is sufficient for evolving target 0'
printf '%s' "$result" | rg -q 'The ECO solution was verified successfully'
printf '%s' "$result" | rg -q 'Patch[[:space:]]+: in = 2[[:space:]]+out = 2'
printf '%s' "$result" | rg -q 'Networks are equivalent'

verify=$(
  cd "$test_dir"
  "$repo_root/abc" -c "cec $data_dir/eco_global_G.v out.v"
)
printf '%s\n' "$verify"
printf '%s' "$verify" | rg -q 'Networks are equivalent'

conflict=$(
  "$repo_root/abc" -c \
    "runeco -g -m $data_dir/eco_global_F.v $data_dir/eco_global_G.v $data_dir/eco_global_weights.txt"
)
printf '%s\n' "$conflict"
printf '%s' "$conflict" | rg -q \
  'runeco: -a, -m, and -g select different support algorithms and cannot be combined'

printf 'runeco global fixed-relation support test passed\n'
