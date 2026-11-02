#!/usr/bin/env bash
# Original and reduced attachments to Issue #77; run across the crashing frame.
issue_root=$(cd "$(dirname "$0")/../.." && pwd)
source "$issue_root/test/issues/common.sh"
ulimit -c 0
run_abc "read $issue_root/test/issues/fixtures/issue77-segfault.aig; logic; undc; strash; zero; fold; bmc2 -F 16385"
expect_log 'Reached limit on the number of timeframes \(16385\)'
run_abc "read $issue_root/test/issues/fixtures/issue77-reduced.aig; logic; undc; strash; zero; fold; bmc2 -F 17000; testcex -a"
expect_log 'asserted in frame 16384'
expect_log 'The cex is correct'
echo 'PASS: Issue #77 (deep construction/cleanup and validated counterexample)'
