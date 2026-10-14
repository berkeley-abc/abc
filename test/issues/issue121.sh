#!/usr/bin/env bash
source "$(dirname "$0")/common.sh"
ulimit -c 0
cat > latch.genlib <<'EOF'
GATE not   1   dout=!din;                      PIN * NONINV 1 1 1 0 1 0
GATE and   1   dout=dina*dinb;                 PIN * NONINV 1 1 1 0 1 0
GATE cb    1   dout=dina+dinb;                 PIN * NONINV 1 1 1 0 1 0
GATE xor   1   dout=dina*!dinb+!dina*dinb;     PIN * NONINV 1 1 1 0 1 0
GATE dff   1   dout=din;                       PIN * NONINV 1 1 1 0 1 0
GATE zero   0   dout=CONST0;
GATE one    0   dout=CONST1;

LATCH andf 1 dout = dina + dinb*dout_NEXT;
PIN dina NONINV 1 1 1 0 1 0
PIN dinb NONINV 1 1 1 0 1 0
SEQ dout dout_NEXT RISING_EDGE
CONTROL clk 1 1 1 0 1 0
CONSTRAINT * 5.67 -0.59
EOF
run_abc 'read_library latch.genlib; print_library'
expect_log 'Skipping latch'
expect_log 'GATE.*xor'
# A latch before, between, and after combinational gates must be skipped.
sed -n '/^LATCH/,$p' latch.genlib > seq.txt
sed '/^LATCH/,$d' latch.genlib > comb.txt
cat seq.txt comb.txt seq.txt comb.txt seq.txt > mixed.genlib
run_abc 'read_library mixed.genlib; print_library'
expect_log 'GATE.*xor'
echo 'PASS: Issues #121 / #96'
