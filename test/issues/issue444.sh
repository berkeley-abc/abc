#!/usr/bin/env bash
# Build libabc.a first. Check both MFS reconstruction paths and timing values.
issue_root=$(cd "$(dirname "$0")/../.." && pwd)
source "$issue_root/test/issues/common.sh"
"${CC:-cc}" -I "$issue_root/src" -DABC_USE_STDINT_H -c "$issue_root/test/issues/issue444.c" -o probe.o
"${CXX:-c++}" probe.o "$issue_root/libabc.a" -lm -ldl -lpthread -lreadline -o probe
./probe > abc.log 2>&1 || { cat abc.log; exit 1; }
expect_log 'The network is not changed'
expect_log 'The network has .* nodes changed'
expect_log 'Timing manager is given but there is no GIA of boxes'
echo 'PASS: Issue #444'
