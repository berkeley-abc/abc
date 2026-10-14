#!/usr/bin/env bash
# Unsupported module headers must fail cleanly and retain the current design.
issue_root=$(cd "$(dirname "$0")/../.." && pwd)
source "$issue_root/test/issues/common.sh"
cat > good.v <<'EOF'
module good(a,b,y);
input a,b;
output y;
assign y = a & b;
endmodule
EOF
cat > bad0.v <<'EOF'
module bad(input [7:0] a, input [7:0] b, output [7:0] y);
assign y = a + b;
endmodule
EOF
cat > bad1.v <<'EOF'
module bad(input a, output y);
assign y = a;
endmodule
EOF
cat > bad2.v <<'EOF'
module bad(a; y);
input a;
output y;
assign y = a;
endmodule
EOF
"${CC:-cc}" -I "$issue_root/src" -DABC_USE_STDINT_H -c "$issue_root/test/issues/issue300.c" -o probe.o
"${CXX:-c++}" probe.o "$issue_root/libabc.a" -lm -ldl -lpthread -lreadline -o probe
./probe > abc.log 2>&1 || { cat abc.log; exit 1; }
expect_log 'PASS: Issue #300'
test "$(grep -c 'Expected.*module port list' abc.log)" = 3
run_abc 'read good.v; strash; &get; &cec preserved.aig'
expect_log 'Networks are equivalent'
echo 'PASS: Issue #300'
