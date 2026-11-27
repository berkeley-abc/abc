#!/usr/bin/env bash
# Bytes >= 0x80 must be classified like any other regular character by the
# BLIF/PLA/bench/eqn file reader (the char map was indexed with a signed char).
source "$(dirname "$0")/common.sh"
printf '.model top\n.inputs a\xffb c\n.outputs y\n.names a\xffb c y\n11 1\n.end\n' > hi.blif
run_abc 'read_blif hi.blif; write_blif out.blif; print_stats'
expect_log 'i/o =    2/    1'
grep -q $'a\xffb' out.blif || { cat out.blif; echo 'name with 0xFF was truncated' >&2; exit 1; }
printf '.i 2\n.o 1\n.ilb a b\n.ob y\n11 1\n.e\n' > ok.pla
printf '.i 3\n.o 1\n.ilb a b c\n.ob y\n111 1\n\xc3\xa9\n.e\n' > hi.pla
run_abc 'read_pla ok.pla; print_stats'
expect_log 'i/o =    2/    1'
"$ABC" -s -c 'read_pla hi.pla' > abc.log 2>&1 || true
! grep -q 'runtime error\|AddressSanitizer' abc.log || { cat abc.log; exit 1; }
echo 'PASS: high-bit characters in the file reader'
