#!/usr/bin/env bash
source "$(dirname "$0")/common.sh"
ulimit -c 0
cat > sat.blif <<'EOF'
.model sat
.inputs a b
.outputs y
.names a b y
11 1
.end
EOF
if command -v valgrind > /dev/null; then
    valgrind --leak-check=full --errors-for-leak-kinds=definite --error-exitcode=99 "$ABC" -s -c 'read sat.blif; strash; dprove' > abc.log 2>&1 || { cat abc.log; exit 1; }
else
    run_abc 'read sat.blif; strash; dprove'
fi
expect_log 'SATISFIABLE'
echo 'PASS: Issue #124'
