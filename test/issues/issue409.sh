#!/usr/bin/env bash
# A mapped network and its EXDC cover use different function managers.
source "$(dirname "$0")/common.sh"
ulimit -c 0
cat > cells.genlib <<'EOF'
GATE zero 0 Y=CONST0;
GATE one 0 Y=CONST1;
GATE buf 1 Y=A; PIN * NONINV 1 999 1 0 1 0
GATE inv 1 Y=!A; PIN * INV 1 999 1 0 1 0
GATE nand2 1 Y=!(A*B); PIN * INV 1 999 1 0 1 0
GATE nor2 1 Y=!(A+B); PIN * INV 1 999 1 0 1 0
EOF
cat > mapped.blif <<'EOF'
.model top
.inputs a b
.outputs y
.gate nand2 A=a B=b Y=y
.exdc
.inputs a b
.outputs y
.names a b y
00 1
.end
EOF
cat > main.v <<'EOF'
module top(a,b,y); input a,b; output y; assign y = ~(a & b); endmodule
EOF
cat > exdc.v <<'EOF'
module top(a,b,y); input a,b; output y; assign y = ~(a | b); endmodule
EOF
run_abc 'read main.v; strash; write_aiger main.aig; read exdc.v; strash; write_aiger exdc.aig; read_genlib cells.genlib; read_blif mapped.blif; write_blif roundtrip.blif; strash; &get; &cec main.aig'
expect_log 'Networks are equivalent'
grep -q '^.exdc' roundtrip.blif
for input in mapped.blif roundtrip.blif; do
    run_abc "read_genlib cells.genlib; read_blif $input; exdc_get; strash; &get; &cec exdc.aig"
    expect_log 'Networks are equivalent'
done
cat > mirror.blif <<'EOF'
.model top
.inputs a b
.outputs y
.names a b y
11 0
.exdc
.inputs a b
.outputs y
.gate nor2 A=a B=b Y=y
.end
EOF
for input in mirror.blif mirror-roundtrip.blif; do
    run_abc "read_genlib cells.genlib; read_blif $input; write_blif mirror-roundtrip.blif; strash; &get; &cec main.aig"
    expect_log 'Networks are equivalent'
    run_abc "read_genlib cells.genlib; read_blif $input; exdc_get; strash; &get; &cec exdc.aig"
    expect_log 'Networks are equivalent'
done
echo 'PASS: Issue #409'
