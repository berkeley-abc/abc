#!/usr/bin/env bash
# Regression test for &sopb building an AND of a literal and its complement.
# In sopb_shared_leaf.aig a mapped node's cut collapses to one of its own leaves,
# so Gia_ManFromIfAig() gives the node that leaf's literal. A later cut has both
# as leaves, and Gia_ManBuildFromMiniInt() called Gia_ManAppendAnd() on x and !x,
# which fails its same-variable assertion.
set -eu
ABC=${ABC:-./abc}
TEST_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
AIG="$TEST_DIR/sopb_shared_leaf.aig"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
fail() { echo "FAIL: $1" >&2; exit 1; }

"$ABC" -s -c "&r $AIG; &sopb -C 3; &w $TMP/sopb.aig; echo SOPB_DONE" > "$TMP/sopb.log" 2>&1 || true
grep -q '^SOPB_DONE' "$TMP/sopb.log" || { cat "$TMP/sopb.log"; fail "&sopb did not complete"; }

"$ABC" -s -c "&cec $AIG $TMP/sopb.aig; echo CEC_DONE" > "$TMP/cec.log" 2>&1 || true
grep -q '^CEC_DONE' "$TMP/cec.log" || { cat "$TMP/cec.log"; fail "incomplete CEC"; }
grep -q 'Networks are equivalent' "$TMP/cec.log" || { cat "$TMP/cec.log"; fail "&sopb changed the function"; }

echo 'PASS: &sopb on a cut with two leaves sharing a literal'
