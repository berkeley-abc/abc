#!/usr/bin/env bash
# Incremental LUT packing may introduce inverters after its initial sweep.
source "$(dirname "$0")/common.sh"
for gates in and_nor or_nand; do
    if [ "$gates" = and_nor ]; then t=8; n=1; else t=e; n=7; fi
    for order in forward reverse; do
        cat > input.bench <<'EOF'
INPUT(a)
INPUT(b)
INPUT(c)
INPUT(d)
OUTPUT(o)
EOF
        if [ "$order" = reverse ]; then
            echo 'o = LUT 0x5101 (a, n, b, c)' >> input.bench
        fi
        printf 't = LUT 0x%s (c, d)\nn = LUT 0x%s (c, t)\n' "$t" "$n" >> input.bench
        if [ "$order" = forward ]; then
            echo 'o = LUT 0x5101 (a, n, b, c)' >> input.bench
        fi
        run_abc 'read_bench input.bench; lutpack; cec input.bench'
        expect_log 'Networks are equivalent'
    done
done
echo 'PASS: Issue #515'
