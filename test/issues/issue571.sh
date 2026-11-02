#!/usr/bin/env bash
# A complemented/plain divisor pair should save one AND without changing logic.
source "$(dirname "$0")/common.sh"
cat > input.eqn <<'EOF'
INORDER = x y z;
OUTORDER = f u;
f = (!x*!y)*z;
u = !x*z;
EOF
run_abc 'read_eqn input.eqn; strash; resub; print_stats; cec -n input.eqn'
expect_log 'and = *2 '
expect_log 'Networks are equivalent'
echo 'PASS: Issue #571'
