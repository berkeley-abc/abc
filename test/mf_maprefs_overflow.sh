#!/usr/bin/env bash
# Regression test for the 16-bit Mf_Obj_t::nMapRefs overflow.
#
# nMapRefs counts the selected best cuts that have an object as a cut leaf,
# so it is a fanout count and a large AIG can push it past 65535.  Once it
# wraps, "was this the first reference" (Mf_ObjMapRefInc returning zero) and
# "was that the last" (Mf_ObjMapRefDec returning zero) both lie, the
# exact-area round's incremental ref/deref walks diverge from the truth, and
# a node that is still a leaf of a live best cut can end up reading zero
# references.  Mf_ManDeriveCnf then gives it no CNF variable and writes
# Abc_Var2Lit(-1, c) into its users' clauses, while Mf_ManDeriveMappingGia
# takes the best cut of a node that selected none and reads its stale
# iCutSet.
#
# The witness needs no large AIG, only one node with exactly 65536 mapping
# references: x is a 6-input AND, so no K=6 cut can absorb it, and each of
# the N two-input ANDs above it must keep x as a cut leaf.  At N=65535 the
# mapping succeeds; at N=65536 x's counter reads zero.

set -eu

ABC=${ABC:-./abc}
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

fail() { echo "FAIL: $1" >&2; exit 1; }

if ! command -v python3 > /dev/null; then
    echo "SKIP: python3 is needed to write the witness AIGER"
    exit 0
fi

# Binary AIGER with N fanouts over a single 6-input AND.
gen_aiger() {
    python3 - "$1" "$2" <<'PY'
import sys
N, out = int(sys.argv[1]), sys.argv[2]
nc = 6
c = list(range(1, nc + 1))
d = list(range(nc + 1, nc + N + 1))
t0 = nc + N + 1
a1, a2, a3, a4, x = t0, t0 + 1, t0 + 2, t0 + 3, t0 + 4
y0 = t0 + 5
I, A = nc + N, 5 + N
lit = lambda v: 2 * v

def enc(n, f):
    while n & ~0x7f:
        f.write(bytes([(n & 0x7f) | 0x80])); n >>= 7
    f.write(bytes([n]))

gates = [(a1, c[1], c[0]), (a2, c[3], c[2]), (a3, c[5], c[4]),
         (a4, a2, a1), (x, a4, a3)]
gates += [(y0 + i, x, d[i]) for i in range(N)]
with open(out, 'wb') as f:
    f.write(f"aig {I + A} {I} 0 {N} {A}\n".encode())
    for i in range(N):
        f.write(f"{lit(y0 + i)}\n".encode())
    for (lhs, r0, r1) in gates:
        L, R0, R1 = lit(lhs), lit(r0), lit(r1)
        assert L > R0 >= R1
        enc(L - R0, f); enc(R0 - R1, f)
PY
}

run_case() {
    local refs=$1 aig="$TMP/refs$1.aig"
    gen_aiger "$refs" "$aig"
    if ! "$ABC" -q "&read $aig; &mf -K 6 -c" > "$TMP/log" 2>&1; then
        cat "$TMP/log" >&2
        fail "$refs mapping references: &mf -K 6 -c did not complete"
    fi
    echo "PASS: $refs mapping references"
}

# One below the 16-bit ceiling, which has always worked.
run_case 65535
# Exactly at it: the counter wraps to zero and the node looks unreferenced.
run_case 65536

echo "All regression tests passed."
