#!/usr/bin/env bash
# Build libabc.a first. Check the legacy full-adder detector's record contents.
issue_root=$(cd "$(dirname "$0")/../.." && pwd)
source "$issue_root/test/issues/common.sh"
"${CC:-cc}" -I "$issue_root/src" -DABC_USE_STDINT_H -c "$issue_root/test/issues/issue346.c" -o probe.o
"${CXX:-c++}" probe.o "$issue_root/libabc.a" -lm -ldl -lpthread -lreadline -o probe
./probe > abc.log 2>&1 || { cat abc.log; exit 1; }
expect_log 'PASS: Issue #346'
cat abc.log
