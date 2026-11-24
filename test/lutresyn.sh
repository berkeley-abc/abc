#!/usr/bin/env bash
# Regression tests for the lutresyn command: the -M bound, the node-reduction
# rule, the -L budget, and functional equivalence.
set -eu
ABC=${ABC:-./abc}
case "$ABC" in /*) ;; *) ABC="$PWD/$ABC" ;; esac
TEST_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
AIG="$TEST_DIR/../i10.aig"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
fail() { echo "FAIL: $1" >&2; cat "$TMP/log"; exit 1; }

run() {
    "$ABC" -s -c "$1" > "$TMP/log" 2>&1 || fail "abc failed: $1"
}

# 1. -M 1 allows only single-LUT rewrites.
run "read $AIG; strash; if -K 6; lutresyn -M 1 -v; cec -n"
grep -Eq 'Round [0-9]+: removed [0-9]+ nodes \(cones 1:[0-9]+ 2:0 3:0\)' "$TMP/log" || fail "-M 1 produced a multi-LUT decomposition"
grep -q 'Networks are equivalent' "$TMP/log" || fail "-M 1 changed the function"

# 2. A committed rewrite must strictly reduce the LUT count, so in every
#    round the nodes removed are at least the number of accepted cones.
run "read $AIG; strash; if -K 6; lutresyn -M 2 -v; cec -n"
sed -nE 's/.*Round ([0-9]+): removed ([0-9]+) nodes \(cones 1:([0-9]+) 2:([0-9]+) 3:([0-9]+)\).*/\1 \2 \3 \4 \5/p' "$TMP/log" |
    awk '{ if ($2 < $3 + $4 + $5) { printf "Round %d removed %d nodes for %d cones\n", $1, $2, $3+$4+$5; bad = 1 } }
         END { exit bad }' || fail "a zero-gain rewrite was committed"
grep -q 'Networks are equivalent' "$TMP/log" || fail "-M 2 changed the function"

# 3. -L is the total level budget of the whole run, not a per-round one.
run "read $AIG; strash; if -K 6; ps; lutresyn -R 5 -L 1; ps; cec -n"
set -- $(grep -oE 'lev = *[0-9]+' "$TMP/log" | sed -E 's/[^0-9]+//g')
[ $# -eq 2 ] || fail "unexpected level readings"
[ $2 -le $(($1 + 1)) ] || fail "levels grew from $1 to $2 with -L 1"
grep -q 'Networks are equivalent' "$TMP/log" || fail "-R 5 changed the function"

# 4. Alternative cones are tried when the greedy cone is rejected.
run "read $AIG; strash; if -K 6; lutresyn -M 2 -v; ps; cec -n"
grep -Eq 'Extra cuts tried [0-9]+, accepted [1-9]' "$TMP/log" || fail "no alternative cone was accepted"
nd=$(grep -o 'nd = *[0-9]*' "$TMP/log" | tail -1 | grep -o '[0-9]*$' || true)
[ -n "$nd" ] && [ "$nd" -le 588 ] || fail "expected at most 588 nodes, got $nd"
grep -q 'Networks are equivalent' "$TMP/log" || fail "alternative cones changed the function"

# 5. -Q allows absorbing nodes that have fanouts outside the cone.
run "read $AIG; strash; if -K 6; lutresyn -M 2 -Q 2; ps; cec -n"
nd=$(grep -o 'nd = *[0-9]*' "$TMP/log" | tail -1 | grep -o '[0-9]*$' || true)
[ -n "$nd" ] && [ "$nd" -le 583 ] || fail "expected at most 583 nodes with -Q 2, got $nd"
grep -q 'Networks are equivalent' "$TMP/log" || fail "-Q 2 changed the function"

echo 'PASS: lutresyn'
