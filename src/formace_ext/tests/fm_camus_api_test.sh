#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
test_bin=$(mktemp /tmp/fm_camus_api_test.XXXXXX)
test_obj="${test_bin}.o"
trap 'rm -f "$test_bin" "$test_obj"' EXIT

make -C "$repo_root" ABC_USE_NO_READLINE=1 libabc.a
"${CC:-gcc}" -DABC_USE_STDINT_H=1 -I"$repo_root/src" \
  -c "$repo_root/src/formace_ext/tests/fm_camus_api_test.c" -o "$test_obj"
"${CXX:-g++}" "$test_obj" "$repo_root/libabc.a" -lm -ldl -lpthread -o "$test_bin"
"$test_bin"
