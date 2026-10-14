#!/usr/bin/env bash
issue_root=$(cd "$(dirname "$0")/../.." && pwd)
source "$issue_root/test/issues/common.sh"
"${CC:-cc}" -I "$issue_root/src" -DABC_USE_STDINT_H -c "$issue_root/test/issues/issue98.c" -o probe.o
"${CXX:-c++}" probe.o "$issue_root/libabc.a" -lm -ldl -lpthread -lreadline -o probe
python3 - <<'PYFILE'
for name, size in [('small', 64), ('large', 2**32+64), ('negative', 2**31+64)]:
    with open(name, 'wb') as f:
        f.seek(size - 1)
        f.write(b'\0')
PYFILE
./probe small
./probe large reject
./probe negative reject
echo 'PASS: Issue #98'
