#!/usr/bin/env bash
source "$(dirname "$0")/common.sh"
ulimit -c 0
printf 'aig 1 0 1 1 0\n3 3\n2\nc\ninvalid init\n' > bad.aig
"$ABC" -s -c 'read_aiger bad.aig' > abc.log 2>&1 || :
expect_log 'initial value of latch number 0 is not recognized'
for init in 0 1 2; do
    printf 'aig 1 0 1 1 0\n3 %s\n2\nc\nvalid init\n' "$init" > valid.aig
    run_abc 'read_aiger valid.aig; print_stats'
    expect_log 'lat.*1'
done
echo 'PASS: Issue #72'
