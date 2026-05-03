#!/usr/bin/env bash
# Regression test for berkeley-abc/abc#479
#
# After "strash", a primary input wired directly to a primary output becomes
# a dangling PI: it shows up in the DIMACS header's variable count but the
# Tseitin encoder emits no clause mentioning it.  Such a free variable
# silently doubles the model count of the written formula, breaking #SAT
# and uniform sampling.
#
# The fix in Cnf_DataWriteIntoFile() detects DIMACS variables that are
# declared in the header but unreferenced in any clause, and emits a unit
# clause pinning each of them to false.  The two cases below exercise that
# behaviour against the abc binary.

set -eu

ABC=${ABC:-./abc}
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

fail() { echo "FAIL: $1" >&2; exit 1; }

run_case() {
    local name=$1 input=$2
    local in="$TMP/$name.in.cnf" out="$TMP/$name.out.cnf"
    printf '%s' "$input" > "$in"
    "$ABC" -q "read_cnf $in; strash; write_cnf $out" > /dev/null

    # Extract declared variable count from the header.
    local header
    header=$(grep -m1 '^p cnf ' "$out")
    local nVars
    nVars=$(echo "$header" | awk '{print $3}')

    # Every variable 1..nVars must appear (positive or negated) in some clause.
    local v
    for v in $(seq 1 "$nVars"); do
        if ! grep -Eq "(^|[ \t-])$v( |$)" "$out"; then
            cat "$out" >&2
            fail "$name: variable $v declared in header but never used in any clause"
        fi
    done
    echo "PASS: $name ($header)"
}

# Case 1: original reproducer from issue #479 -- a single PI wired directly
# to a single PO.  Before the fix, the output was "p cnf 3 2" with clauses
# "-3 0" and "2 0", leaving variable 1 unconstrained.
run_case "pi_to_po_direct" "p cnf 1 1
1 0
"

# Case 2: two independent PIs, each a direct wire to its own PO.  Both PIs
# end up dangling after strash.
run_case "two_pis_two_pos" "p cnf 2 2
1 0
2 0
"

echo "All regression tests passed."
