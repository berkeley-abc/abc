#!/usr/bin/env bash
# Named outputs must retain polarity, including two outputs sharing a driver.
source "$(dirname "$0")/common.sh"
cat > shared.blif <<'EOF'
.model shared
.inputs a b
.outputs pos neg
.names a b root
11 1
.names root pos
1 1
.names root neg
0 1
.end
EOF
for output in pos neg; do
    case "$output" in pos) index=0 ;; neg) index=1 ;; esac
    run_abc "read shared.blif; strash; cone -O $index; write_aiger reference.aig"
    for mode in '' '-m' '-a'; do
        run_abc "read shared.blif; strash; cone $mode $output; strash; &get; &cec reference.aig"
        expect_log 'Networks are equivalent'
    done
done
# Internal node n5 is the regular AND, regardless of the inverted output.
run_abc 'read shared.blif; strash; cone -O 0; write_aiger reference.aig; read shared.blif; strash; cone n5; &get; &cec reference.aig'
expect_log 'Networks are equivalent'
echo 'PASS: Issue #221 (seven equivalence checks)'
