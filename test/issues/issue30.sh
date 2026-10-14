#!/usr/bin/env bash
issue_root=$(cd "$(dirname "$0")/../.." && pwd)
source "$issue_root/test/issues/common.sh"
"${CC:-cc}" -fsanitize=address -g -I "$issue_root/src" -DABC_USE_STDINT_H "$issue_root/test/issues/issue30.c" -o probe
./probe
