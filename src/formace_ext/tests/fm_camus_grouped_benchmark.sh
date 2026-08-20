#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
test_bin=$(mktemp /tmp/fm_camus_grouped_benchmark.XXXXXX)
test_obj="${test_bin}.o"
trap 'rm -f "$test_bin" "$test_obj"' EXIT

if [[ $# -lt 2 || $# -gt 3 ]]; then
    printf 'usage: %s FILE.cnf FILE.groups [minimum-mus|minimum-all]\n' "$0" >&2
    exit 2
fi

make -C "$repo_root" ABC_USE_NO_READLINE=1 libabc.a
"${CC:-gcc}" -DABC_USE_STDINT_H=1 -I"$repo_root/src" \
  -c "$repo_root/src/formace_ext/tests/fm_camus_grouped_benchmark.c" -o "$test_obj"
"${CXX:-g++}" "$test_obj" "$repo_root/libabc.a" -lm -ldl -lpthread -o "$test_bin"
"$test_bin" "$@"
