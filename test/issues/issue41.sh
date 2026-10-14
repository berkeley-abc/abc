#!/usr/bin/env bash
source "$(dirname "$0")/common.sh"
ulimit -c 0
cat > and.v <<'EOF'
module top ( a, b, y );
input a, b;
output y;
assign y = a & b;
endmodule
EOF
for flags in '' '-f'; do
    "$ABC" -s -c "read_verilog and.v; write_cnf $flags bad.cnf" > abc.log 2>&1 || :
    expect_log 'requires an AIG'
    test ! -e bad.cnf
    run_abc "read_verilog and.v; strash; write_cnf $flags good.cnf"
    grep -q '^p cnf' good.cnf
done
run_abc 'read_verilog and.v; write_cnf -n old.cnf'
grep -q '^p cnf' old.cnf
echo 'PASS: Issue #41'
