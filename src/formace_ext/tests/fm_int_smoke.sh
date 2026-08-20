#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"

safe=src/formace_ext/tests/data/bmc_safe_two_latch.blif
unsafe=src/formace_ext/tests/data/bmc_unsafe_two_latch.blif
zero=src/formace_ext/tests/data/bmc_zero_boundary.blif

baseline=$(./abc -c "read_blif $safe; strash; int -F 10 -v")
printf '%s\n' "$baseline"
printf '%s' "$baseline" | rg -q 'Property proved\.'

fm_baseline=$(./abc -c "read_blif $safe; strash; fm_int -o -F 10 -v")
printf '%s\n' "$fm_baseline"
printf '%s' "$fm_baseline" | rg -q 'Property proved\.'

partition=$(./abc -c "read_blif $safe; strash; fm_int -o -S 2 -F 3 -a -i -I /tmp/fm_int_partition.aig -v")
printf '%s\n' "$partition"
printf '%s' "$partition" | rg -q 'partition: suffix k = 2, bad states = 1\.\.k'
printf '%s' "$partition" | rg -q 'Property proved\.'

for mode in m y; do
    result=$(./abc -c "read_blif $safe; strash; fm_int -$mode -F 10 -v")
    printf '%s\n' "$result"
    printf '%s' "$result" | rg -q 'Property proved\.'
    printf '%s' "$result" | rg -q "ForMACE .+CAMUS .+ selected 1"
done

zero_result=$(./abc -c "read_blif $zero; strash; fm_int -m -F 10 -v")
printf '%s\n' "$zero_result"
printf '%s' "$zero_result" | rg -q 'ForMACE minvar CAMUS minimum selected 0 of 2'
printf '%s' "$zero_result" | rg -q 'Property proved\.'

unsafe_result=$(./abc -c "read_blif $unsafe; strash; fm_int -m -F 10")
printf '%s\n' "$unsafe_result"
printf '%s' "$unsafe_result" | rg -q 'asserted in frame'

limited=$(./abc -c "read_blif $safe; strash; fm_int -m -L 1 -F 10")
printf '%s\n' "$limited"
printf '%s' "$limited" | rg -q 'Property UNDECIDED\.'

printf 'fm_int smoke test passed.\n'
