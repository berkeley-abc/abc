#!/usr/bin/env bash
source "$(dirname "$0")/common.sh"
cat > cells.genlib <<'EOF'
GATE MUX3 1 ZN=!(I0*!S0*!S1+I1*S0*!S1+I2*S1);
PIN I0 INV 1 999 1 0 1 0
PIN I1 INV 1 999 1 0 1 0
PIN I2 INV 1 999 1 0 1 0
PIN S0 UNKNOWN 1 999 1 0 1 0
PIN S1 UNKNOWN 1 999 1 0 1 0

GATE INV 1 ZN=!I;
PIN I INV 1 999 1 0 1 0

GATE NOR2 1 ZN=!(!A1+B1);
PIN A1 NONINV 1 999 1 0 1 0
PIN B1 INV 1 999 1 0 1 0

GATE AOI3 1 ZN=!(A1*A2*A3+B1*B2);
PIN A1 INV 1 999 1 0 1 0
PIN A2 INV 1 999 1 0 1 0
PIN A3 INV 1 999 1 0 1 0
PIN B1 INV 1 999 1 0 1 0
PIN B2 INV 1 999 1 0 1 0

GATE AOI2 1 ZN=!(B1*B2+!A);
PIN A NONINV 1 999 1 0 1 0
PIN B1 INV 1 999 1 0 1 0
PIN B2 INV 1 999 1 0 1 0

EOF
cat > sop.v <<'EOF'
module test_MUX3 (
    a0,a1,a2,a3,a4,out  );
  input  a0,a1,a2,a3,a4;
  output out;
  assign out = !(a0&!a1&!a2|a3&a1&!a2|a4&a2);
endmodule

EOF
for expr in '~(s1 ? d2 : (s0 ? d1 : d0))' '~(s0 ? d0 : (d1 ? s1 : d2))'; do
    cat > nested.v <<EOF
module top ( s0, s1, d0, d1, d2, y );
input s0, s1, d0, d1, d2;
output y;
assign y = $expr;
endmodule
EOF
    run_abc 'read_library cells.genlib; read_verilog nested.v; strash; write_aiger ref.aig; amap -m; print_stats; strash; &get; &cec ref.aig'
    expect_log 'nd = *1 .*area = 1.00'
    expect_log 'Networks are equivalent'
done
# AMAP matches structure; rewrite exposes the MUXes in the expanded SOP.
run_abc 'read_library cells.genlib; read_verilog sop.v; strash; write_aiger ref.aig; rewrite; amap -m; print_stats; strash; &get; &cec ref.aig'
expect_log 'nd = *1 .*area = 1.00'
expect_log 'Networks are equivalent'
echo 'PASS: Issue #182 (three one-cell mappings and equivalence checks)'
