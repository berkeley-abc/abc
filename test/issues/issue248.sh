#!/usr/bin/env bash
# Exercise LUT widths and larger cuts; every result must preserve the function.
issue_root=$(cd "$(dirname "$0")/../.." && pwd)
source "$issue_root/test/issues/common.sh"
for k in -1 0 1 7 8; do
    run_abc "&read $issue_root/i10.aig; &mfs2 -K $k; echo invalid_width_accepted"
    expect_log 'usage: &mfs2'
    expect_log '2 <= num <= 6'
    if grep -q '^invalid_width_accepted' abc.log; then
        cat abc.log
        exit 1
    fi
done
# Check the lower accepted widths on a small circuit as well.
cat > small.blif <<'EOF'
.model small
.inputs a b c
.outputs y
.names a b t
11 1
.names t c y
1- 1
-1 1
.end
EOF
run_abc 'read small.blif; strash; write_aiger small.aig'
for k in 2 3 4 5 6; do
    case "$k" in
        2|3) design=small.aig ;;
        *) design="$issue_root/i10.aig" ;;
    esac
    for options in '' '-N 10 -S 3'; do
        run_abc "&read $design; &mfs2 -K $k $options; &cec $design"
        expect_log 'Networks are equivalent'
    done
done
run_abc "&read $issue_root/i10.aig; &mfs2 -K 2; &cec $issue_root/i10.aig"
expect_log 'Networks are equivalent'
echo 'PASS: Issue #248 (invalid widths rejected; eleven equivalence checks)'
