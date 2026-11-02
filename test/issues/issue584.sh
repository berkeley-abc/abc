#!/usr/bin/env bash
# Positional connections follow the module header, including interleaved buses.
source "$(dirname "$0")/common.sh"
cat > reference.v <<'EOF'
module top(a,b,z); input a,b; output z; assign z = a & ~b; endmodule
EOF
while IFS=@ read -r header actual; do
    cat > sub.v <<EOF
module sub($header);
input y;
output o;
input x;
assign o = x & ~y;
endmodule
EOF
    for ports in "$actual" '.o(z),.x(a),.y(b)'; do
        printf 'module top(a,b,z); input a,b; output z; sub u(%s); endmodule\n' "$ports" > top.v
        for order in 'sub.v top.v' 'top.v sub.v'; do
            cat $order > input.v
            run_abc 'cec -n input.v reference.v'
            expect_log 'Networks are equivalent'
        done
    done
done <<'EOF'
x,y,o@a,b,z
y,x,o@b,a,z
o,x,y@z,a,b
o,y,x@z,b,a
x,o,y@a,z,b
y,o,x@b,z,a
EOF
cat > sub.v <<'EOF'
module sub(o,x,p,y);
input [2:0] y;
input [1:0] x;
output p;
output [1:0] o;
assign o[0] = x[0] & ~y[1];
assign o[1] = x[1] ^ y[2];
assign p = y[0];
endmodule
EOF
cat > reference.v <<'EOF'
module top(a,b,z,q);
input [1:0] a;
input [2:0] b;
output [1:0] z;
output q;
assign z[0] = a[0] & ~b[1];
assign z[1] = a[1] ^ b[2];
assign q = b[0];
endmodule
EOF
for ports in 'z,a,q,b' '{z[1],z[0]},{a[1],a[0]},q,b' '.y(b),.p(q),.x(a),.o(z)'; do
    cat > top.v <<EOF
module top(a,b,z,q);
input [1:0] a;
input [2:0] b;
output [1:0] z;
output q;
sub u($ports);
endmodule
EOF
    for order in 'sub.v top.v' 'top.v sub.v'; do
        cat $order > input.v
        run_abc 'cec -n input.v reference.v'
        expect_log 'Networks are equivalent'
    done
done
for ports in 'z,a,q' 'z,.x(a),q,b' 'z,a,q,b[0]'; do
    sed "s/sub u(.*);/sub u($ports);/" top.v > input.v
    cat sub.v >> input.v
    run_abc 'read_verilog input.v'
    expect_log 'Cannot match positional ports|Cannot mix named and positional ports'
done
echo 'PASS: Issue #584'
