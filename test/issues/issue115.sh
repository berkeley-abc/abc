#!/usr/bin/env bash
issue_root=$(cd "$(dirname "$0")/../.." && pwd)
source "$issue_root/test/issues/common.sh"
"${CC:-cc}" -g -fsanitize=address,undefined -I "$issue_root/src" -DABC_USE_STDINT_H -c "$issue_root/test/issues/issue115.c" -o probe.o
"${CXX:-c++}" -fsanitize=address,undefined probe.o "$issue_root/libabc.a" -lm -ldl -lpthread -lreadline -o probe
./probe
