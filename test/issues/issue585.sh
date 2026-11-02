#!/usr/bin/env bash
# Retiming a node fed by a latch and its driver must preserve input positions.
source "$(dirname "$0")/common.sh"
for fanins in 'q x' 'x q' 'q q x' 'q x q'; do
    for cube in $(if [ ${#fanins} -eq 3 ]; then echo '10 01 11'; else echo '100 011 111'; fi); do
        cat > input.blif <<EOF
.model retime
.inputs a b
.outputs y
.latch a r 0
.latch b s 0
.names r s x
11 1
.latch x q 0
.names $fanins y
$cube 1
.end
EOF
        run_abc 'read_blif input.blif; retime -M 1; dsec input.blif'
        expect_log 'Networks are equivalent'
    done
done
echo 'PASS: Issue #585'
