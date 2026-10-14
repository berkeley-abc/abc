#!/usr/bin/env bash
# Build libabc.a first. Check alignment without relying on hardware faults.
issue_root=$(cd "$(dirname "$0")/../.." && pwd)
source "$issue_root/test/issues/common.sh"
"${CC:-cc}" -I "$issue_root/src" -DABC_USE_STDINT_H -c "$issue_root/test/issues/issue407.c" -o probe.o
"${CXX:-c++}" probe.o "$issue_root/libabc.a" -lm -ldl -lpthread -lreadline -o probe
./probe > abc.log 2>&1 || { cat abc.log; exit 1; }
expect_log 'PASS: Issue #407'
cat abc.log
