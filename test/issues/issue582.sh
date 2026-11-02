#!/usr/bin/env bash
# Liberty XOR binds more tightly than AND, including implicit AND.
source "$(dirname "$0")/common.sh"
cat > cells.lib <<'EOF'
cell(BUF) { area : 1;
  pin(A) { direction : input; }
  pin(Y) { direction : output; function : "A"; } }
cell(INV) { area : 1;
  pin(A) { direction : input; }
  pin(Y) { direction : output; function : "!A"; } }
cell(NAND2) { area : 1;
  pin(A) { direction : input; }
  pin(B) { direction : input; }
  pin(Y) { direction : output; function : "!(A*B)"; } }
cell(NOR2) { area : 1;
  pin(A) { direction : input; }
  pin(B) { direction : input; }
  pin(Y) { direction : output; function : "!(A+B)"; } }
EOF
cat > gate.blif <<'EOF'
.model top
.inputs a b c
.outputs y
.gate XA A=a B=b C=c Y=y
.end
EOF
while IFS=@ read -r expression reference; do
    cat > input.lib <<EOF
library(test) {
time_unit : "1ns";
capacitive_load_unit(1, pf);
cell(XA) { area : 1;
  pin(A) { direction : input; }
  pin(B) { direction : input; }
  pin(C) { direction : input; }
  pin(Y) { direction : output; function : "$expression"; } }
EOF
    cat cells.lib >> input.lib
    echo '}' >> input.lib
    printf 'module top(a,b,c,y); input a,b,c; output y; assign y = %s; endmodule\n' "$reference" > reference.v
    run_abc 'read_lib input.lib; write_genlib output.genlib; write_scl output.scl; write_lib output.lib; read_blif gate.blif; strash; cec -n reference.v'
    expect_log 'Networks are equivalent'
    for reload in 'read_genlib output.genlib' 'read_scl output.scl' 'read_lib output.lib'; do
        run_abc "$reload; read_blif gate.blif; strash; cec -n reference.v"
        expect_log 'Networks are equivalent'
    done
done <<'EOF'
A^B*C@(a ^ b) & c
A*B^C@a & (b ^ c)
A^B C@(a ^ b) & c
A B^C@a & (b ^ c)
A^B&C@(a ^ b) & c
A&B^C@a & (b ^ c)
(A^B)(B^C)@(a ^ b) & (b ^ c)
(A*B)^C@(a & b) ^ c
A^(B*C)@a ^ (b & c)
A+B^C@a | (b ^ c)
A^B+C@(a ^ b) | c
A'^B*C@((~a) ^ b) & c
A^B'*C@(a ^ (~b)) & c
A^!B*C@(a ^ (~b)) & c
A !B^C@a & ((~b) ^ c)
!(A^B)*C@(~(a ^ b)) & c
(A^B)'C@(~(a ^ b)) & c
EOF
# GENLIB retains its existing AND-before-XOR convention.
cat > input.genlib <<'EOF'
GATE zero 0 Y=CONST0;
GATE one 0 Y=CONST1;
GATE buf 1 Y=A; PIN * NONINV 1 999 1 0 1 0
GATE inv 1 Y=!A; PIN * INV 1 999 1 0 1 0
GATE nand2 1 Y=!(A*B); PIN * INV 1 999 1 0 1 0
GATE nor2 1 Y=!(A+B); PIN * INV 1 999 1 0 1 0
GATE XA 1 Y=A^B*C; PIN * UNKNOWN 1 999 1 0 1 0
EOF
echo 'module top(a,b,c,y); input a,b,c; output y; assign y = a ^ (b & c); endmodule' > reference.v
run_abc 'read_genlib input.genlib; read_blif gate.blif; strash; cec -n reference.v'
expect_log 'Networks are equivalent'
echo 'PASS: Issue #582'
