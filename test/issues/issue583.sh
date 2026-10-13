#!/usr/bin/env bash
# Conditional expressions must respect branch boundaries and right associativity.
source "$(dirname "$0")/common.sh"
while IFS=@ read -r expression reference; do
    printf 'module top(a,b,c,d,e,y); input a,b,c,d,e; output y; assign y = %s; endmodule\n' "$expression" > input.v
    printf 'module top(a,b,c,d,e,y); input a,b,c,d,e; output y; assign y = %s; endmodule\n' "$reference" > reference.v
    run_abc 'cec -n input.v reference.v'
    expect_log 'Networks are equivalent'
done <<'EOF'
a ? b & c : d@a ? (b & c) : d
a ? b | c : d@a ? (b | c) : d
a ? b ^ c : d@a ? (b ^ c) : d
a & b ? c : d@(a & b) ? c : d
a ? b : c & d@a ? b : (c & d)
a ? b ? c : a : c@a ? (b ? c : a) : c
a ? b : c ? d : e@a ? b : (c ? d : e)
a ? b ? c : d : e ? a : b@a ? (b ? c : d) : (e ? a : b)
~a ? ~b & c : d ^ e@(~a) ? ((~b) & c) : (d ^ e)
(a ? b : c) & d@d & (a ? b : c)
a ? b & (c ? d : e) : e@a ? (b & (c ? d : e)) : e
a ? b : c | ~~d@a ? b : (c | d)
EOF
for expression in 'a ? b' 'a : b' 'a ? : b' 'a ? b :' 'a ? (b : c) : d'; do
    printf 'module top(a,b,c,d,y); input a,b,c,d; output y; assign y = %s; endmodule\n' "$expression" > input.v
    run_abc 'read_verilog input.v'
    expect_log 'Parse_FormulaParser|Reading network.*failed'
done
echo 'PASS: Issue #583'
