#!/usr/bin/env bash
source "$(dirname "$0")/common.sh"
ulimit -c 0
cat > dc.blif <<'EOF'
.model dc
.inputs d unused
.outputs y
.latch d q 2
.latch d r 1
.names q r y
11 1
.end
EOF
run_abc 'read_blif dc.blif; &get; &write reference.aig; read_blif dc.blif; &get -n; &write named.aig; &cec reference.aig'
expect_log 'Networks are equivalent'
grep -a -q 'q_init_val' named.aig
grep -a -q 'init_reset' named.aig
run_abc 'read_blif dc.blif; &get -n; &gla -F 30 -m'
if grep -Eq 'Assertion|failed' abc.log; then cat abc.log; exit 1; fi
echo 'PASS: Issue #39'
