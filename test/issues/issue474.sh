#!/usr/bin/env bash
# Boundary recording requires a boundary manager, even on a single AND.
source "$(dirname "$0")/common.sh"
for flags in '-q' '-xq' '-vwqx'; do
    run_abc "read_truth 8; strash; &get; &fraig $flags"
    expect_log 'requires an initialized boundary miter'
done
for flags in '-x' '-xqq'; do
    run_abc "read_truth 8; strash; write_blif reference.blif; &get; &fraig $flags; &put; cec -n reference.blif"
    expect_log 'Networks are equivalent'
done
echo 'PASS: Issue #474'
