#!/usr/bin/env bash
# &acec must retain every primary output after matching arithmetic boxes.
set -eu

ABC=${1:-${ABC:-./abc}}
case "$ABC" in /*) ;; *) ABC="$PWD/$ABC" ;; esac
FIXTURE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)/acec_output_coverage.blif
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

check() {
    name=$1
    expected=$2
    "$ABC" -s -c "read_blif $TMP/$name.blif; strash; write_aiger $TMP/$name.aig" > "$TMP/convert.log" 2>&1
    "$ABC" -s -c "&acec -v $TMP/reference.aig $TMP/$name.aig" > "$TMP/$name.log" 2>&1
    if ! grep -q 'Matching of adder trees in LHS and RHS succeeded' "$TMP/$name.log" ||
       ! grep -q "^Networks are $expected" "$TMP/$name.log"; then
        cat "$TMP/$name.log"
        echo "FAIL: $name (expected $expected)" >&2
        exit 1
    fi
    echo "PASS: $name"
}

cp "$FIXTURE" "$TMP/reference.blif"
"$ABC" -s -c "read_blif $TMP/reference.blif; strash; write_aiger $TMP/reference.aig" > "$TMP/convert.log" 2>&1
cp "$FIXTURE" "$TMP/identity.blif"
check identity equivalent

# Invert each output's function while preserving the interface.  The first
# two inversions use a BLIF off-set cover; the last two invert a one-input gate.
for name in sum high tail0 tail1; do
    awk -v target="$name" '
        /^\.names/ { selected=($NF == target) }
        /^\./ { print; next }
        selected && NF {
            if (target == "sum" || target == "high") $NF = 0;
            else $1 = 1 - $1;
        }
        { print }
    ' "$FIXTURE" > "$TMP/$name.blif"
    check "$name" 'NOT EQUIVALENT'
done

# The replacement commands retain the same interface and distinguish a real
# output mismatch from an undecided proof. Use a changed Boolean structure too.
"$ABC" -s -c "read_blif $TMP/reference.blif; strash; dc2; write_aiger $TMP/rebuilt.aig" > "$TMP/rebuild.log" 2>&1
for name in identity rebuilt sum high tail0 tail1; do
    case "$name" in identity|rebuilt) expected=equivalent ;; *) expected='NOT EQUIVALENT' ;; esac
    "$ABC" -s -c "&acec2 -T 10 $TMP/reference.aig $TMP/$name.aig" > "$TMP/new_$name.log" 2>&1
    if ! grep -q "^Networks are $expected" "$TMP/new_$name.log"; then
        cat "$TMP/new_$name.log"
        echo "FAIL: &acec2 $name (expected $expected)" >&2
        exit 1
    fi
    echo "PASS: &acec2 $name"
done
"$ABC" -s -c "&r $TMP/reference.aig; &atree2 -L 0 -J $TMP/profile.json" > "$TMP/profile.log" 2>&1
if ! grep -q '"full_adders":1,' "$TMP/profile.json"; then
    cat "$TMP/profile.log" "$TMP/profile.json"
    echo 'FAIL: &atree2 missed the fixture full adder' >&2
    exit 1
fi
echo 'PASS: &atree2 full-adder profile'
