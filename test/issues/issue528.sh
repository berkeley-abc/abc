#!/usr/bin/env bash
# Reject legacy choice links safely; importing mapping choices must work.
design="$PWD/i10.aig"
source "$(dirname "$0")/common.sh"
for dch in dch 'dch -f'; do
    run_abc "read $design; strash; $dch; &get; &if -K 4"
    expect_log 'Choice nodes are not in the format required by &if.*&get -s'
    run_abc "read $design; strash; $dch; &get -s; &if -K 4; &put; cec -n $design"
    expect_log 'Networks are equivalent'
done
run_abc "read $design; &get; &if -K 4; &put; cec -n $design"
expect_log 'Networks are equivalent'
echo 'PASS: Issue #528'
