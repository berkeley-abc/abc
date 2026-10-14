#!/usr/bin/env bash
# Mapped GIAs may contain duplicate ANDs. Test speedup, remapping, and rehashing.
issue_root=$(cd "$(dirname "$0")/../.." && pwd)
source "$issue_root/test/issues/common.sh"
"${CC:-cc}" -I "$issue_root/src" -DABC_USE_STDINT_H -c "$issue_root/test/issues/issue208.c" -o probe.o
"${CXX:-c++}" probe.o "$issue_root/libabc.a" -lm -ldl -lpthread -lreadline -o probe
./probe > abc.log 2>&1 || { cat abc.log; exit 1; }
expect_log 'PASS: Issue #208 hash growth'
for k in 4 5 6; do
    run_abc "&read $issue_root/i10.aig; &if -K $k; &speedup; &cec $issue_root/i10.aig; &put; &get -s; &if -K $k; &cec $issue_root/i10.aig"
    test "$(grep -c 'Networks are equivalent' abc.log)" = 2 || { cat abc.log; exit 1; }
done
echo 'PASS: Issue #208 (hash growth and six equivalence checks)'
