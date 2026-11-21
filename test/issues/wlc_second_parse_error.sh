#!/usr/bin/env bash
# Wlc_PrsReadName() names an undeclared operand, then its caller reports the same
# line again. The second report must keep the first message instead of aborting.
source "$(dirname "$0")/common.sh"
ulimit -c 0
expect_undeclared_operand() { # case-name right-hand-side
    printf 'module %s ( output parsed_output ) ;\n  assign parsed_output = %s ;\nendmodule\n' "$1" "$2" > "$1.v"
    run_abc "%read $1.v"
    expect_log "$1\.v \(line 2\): Name undeclared_operand is used but not declared\."
    echo "PASS: $1"
}
expect_undeclared_operand logic_not '! undeclared_operand'  # two reports
expect_undeclared_operand buffer   'undeclared_operand'     # one report, must stay correct
echo 'PASS: a second parse error keeps the first message'
