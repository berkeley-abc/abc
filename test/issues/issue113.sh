#!/usr/bin/env bash
source "$(dirname "$0")/common.sh"
ulimit -c 0
printf 'aig 1 0 1 1 0\n3\n2\nc\nno PI\n' > toggle.aig
run_abc 'read toggle.aig; int'
expect_log 'Interpolation requires at least one primary input'
run_abc 'read toggle.aig; bmc; testcex -a'
expect_log 'asserted in frame 1'
expect_log 'correct'
printf 'aig 2 1 1 1 0\n5\n4\nc\nunused PI\n' > input.aig
run_abc 'read input.aig; int; testcex -a'
expect_log 'correct'
echo 'PASS: Issue #113 and zero-PI BMC'
