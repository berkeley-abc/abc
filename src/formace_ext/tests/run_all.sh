#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)

tests=(
  fm_camus_api_test.sh
  fm_minunsat_test.sh
  fm_inter_smoke.sh
  fm_int_smoke.sh
  fm_runeco_minimum_test.sh
)

for test_script in "${tests[@]}"; do
  printf '\n==> %s\n' "$test_script"
  bash "$repo_root/src/formace_ext/tests/$test_script"
done

printf '\nAll ForMACE extension tests passed.\n'
