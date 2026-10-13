#!/usr/bin/env bash
# Reject directives after an early .end; valid EXDC and hierarchy still read.
source "$(dirname "$0")/common.sh"
cat > bad.blif <<'EOF'
.model test
.inputs a b
.outputs y
.exdc
.names a b
11 -
.end
.names a b y
11 1
.end
EOF
run_abc 'read_blif bad.blif'
expect_log 'Line 8: Directive outside a model'
for directive in '.names a y' '.inputs a' '.outputs y' '.latch a q' '.subckt sub a=a' '.blackbox'; do
    for prefix in '' '.model test\n.end\n'; do
        printf '%b%s\n' "$prefix" "$directive" > bad.blif
        run_abc 'read_blif bad.blif'
        expect_log 'Directive outside a model'
    done
done
cat > valid.blif <<'EOF'
.model test
.inputs a b
.outputs y z
.names a b y
11 1
.names a b z
1- 1
-1 1
.exdc
.inputs a b
.outputs y z
.names a b y
11 1
.names a b z
11 1
.end
EOF
for reader in '' '-n'; do
    run_abc "read_blif $reader valid.blif; write_verilog valid.v; print_exdc"
    expect_log 'EXDC network statistics'
    test -s valid.v
done
cat > hierarchy.blif <<'EOF'
.model top
.inputs a
.outputs y
.subckt sub a=a y=y
.end
.model sub
.inputs a
.outputs y
.names a y
1 1
.end
EOF
run_abc 'read_blif hierarchy.blif; strash; print_stats'
expect_log 'i/o = *1/ *1'
echo 'PASS: Issue #472'
