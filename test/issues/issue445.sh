#!/usr/bin/env bash
# Name recovery must not abort a synthesis script after retiming.
source "$(dirname "$0")/common.sh"
cat > reference.blif <<'EOF'
.model registers
.inputs a b
.outputs y
.latch a qa 0
.latch b qb 0
.names qa qb y
11 1
.end
EOF
run_abc 'read_blif reference.blif; strash; retime -M 1; write_blif before.blif; dress reference.blif; write_blif after.blif'
expect_log 'Skipping "dress".*different combinational I/O counts'
test "$(grep -c '^.latch' before.blif)" = 1
diff <(sed '/^#/d' before.blif) <(sed '/^#/d' after.blif)

# Matching sequential interfaces still support name recovery.
run_abc 'read_blif reference.blif; strash; &get; &write reference.aig; read_blif reference.blif; dress reference.blif; write_blif matched.blif; strash; &get; &cec reference.aig'
expect_log 'Networks are equivalent'
test "$(grep -c '^.latch' matched.blif)" = 2
cat > extra-output.blif <<'EOF'
.model comb
.inputs a b
.outputs y z
.names a b y
11 1
.names a z
1 1
.end
EOF
run_abc 'read_truth 8; dress extra-output.blif; write_blif kept.blif'
expect_log 'Skipping "dress".*different combinational I/O counts'
test -s kept.blif

# A failed reference read is a command error, not a null dereference.
run_abc 'read_blif reference.blif; dress missing.blif; write_blif unexpected.blif'
expect_log 'Cannot open input file'
test ! -e unexpected.blif
echo 'PASS: Issue #445'
