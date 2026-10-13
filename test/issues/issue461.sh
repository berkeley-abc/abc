#!/usr/bin/env bash
# Build libabc.a first. This probes the legacy RTL API without requiring Yosys.
issue_root=$(cd "$(dirname "$0")/../.." && pwd)
source "$issue_root/test/issues/common.sh"
cat > input.il <<'EOF'
module \comb
  wire input 1 \a
  wire input 2 \b
  wire output 3 \y
  cell $and \gate
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \a
    connect \B \b
    connect \Y \y
  end
end
module \seq
  wire input 1 \clk
  wire input 2 \d
  wire output 3 \q
  cell $dff \ff
    parameter \CLK_POLARITY 1'1
    parameter \WIDTH 1
    connect \CLK \clk
    connect \D \d
    connect \Q \q
  end
end
module \hier
  wire input 1 \clk
  wire input 2 \d
  wire output 3 \q
  cell \seq \child
    connect \clk \clk
    connect \d \d
    connect \q \q
  end
end
EOF
"${CC:-cc}" -I "$issue_root/src" -DABC_USE_STDINT_H -c "$issue_root/test/issues/issue461.c" -o probe.o
"${CXX:-c++}" probe.o "$issue_root/libabc.a" -lm -ldl -lpthread -lreadline -o probe
./probe input.il > abc.log 2>&1 || { cat abc.log; exit 1; }
expect_log 'Sequential designs are not supported by %collapse'
echo 'PASS: Issue #461'
