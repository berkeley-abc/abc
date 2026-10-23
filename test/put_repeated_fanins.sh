#!/usr/bin/env bash
# Check output-polarity normalization with repeated LUT fanins.
set -eu
ABC=${ABC:-./abc}
TEST_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
fail() { echo "FAIL: $1" >&2; exit 1; }
if ! command -v python3 > /dev/null; then
    echo "SKIP: python3 is needed to generate repeated-fanin variants"
    exit 0
fi
cp "$TEST_DIR/put_repeated_fanins.blif" "$TMP/minimal.blif"
python3 - "$TMP" <<'PY'
import pathlib, sys
out = pathlib.Path(sys.argv[1])
for copies in (1, 2, 3, 4):
    for first in (False, True):
        fanins = ['p'] * copies
        cube = ['-'] * (copies - 1) + ['1']
        if first:
            fanins.insert(0, 'c'); cube.insert(0, '1')
        else:
            fanins.append('c'); cube.append('1')
        text = '.model repeated\n.inputs a b c\n.outputs p y z\n.names a b p\n10 0\n'
        text += '.names ' + ' '.join(fanins) + ' y\n' + ''.join(cube) + ' 1\n'
        text += '.names p c z\n10 1\n.end\n'
        (out / ('repeat%d_%d.blif' % (copies, first))).write_text(text)
(out / 'two_drivers.blif').write_text('''\
.model two_drivers
.inputs a b c
.outputs p q y
.names a b p
10 0
.names b c q
10 0
.names p p q q c y
-1-11 1
.end
''')
text = (out / 'minimal.blif').read_text()
(out / 'positive.blif').write_text(text.replace('10 0', '10 1'))
(out / 'no_po.blif').write_text(text.replace('.outputs p y', '.outputs y'))
PY
check_equivalent() {
    "$ABC" -s -c "&cec $TMP/before.aig $TMP/after.aig; echo PUT_CEC_DONE" > "$TMP/cec.log" 2>&1
    grep -q 'PUT_CEC_DONE' "$TMP/cec.log" || { cat "$TMP/cec.log"; fail "$1: incomplete CEC"; }
    grep -q 'Networks are equivalent' "$TMP/cec.log" || { cat "$TMP/cec.log"; fail "$1: equivalence"; }
    if grep -q 'NOT EQUIVALENT' "$TMP/cec.log"; then cat "$TMP/cec.log"; fail "$1: mismatch"; fi
}
for input in "$TMP"/*.blif; do
    name=$(basename "$input" .blif)
    for put in '&put' '&put -o'; do
        "$ABC" -s -c "read_blif $input; strash; &get; &w $TMP/before.aig; read_blif $input; &get -m; $put; strash; &get; &w $TMP/after.aig; echo PUT_DONE" > "$TMP/convert.log" 2>&1
        grep -q 'PUT_DONE' "$TMP/convert.log" || { cat "$TMP/convert.log"; fail "$name: incomplete conversion"; }
        check_equivalent "$name $put"
    done
    # Exercise serialization and a second mapped conversion as well.
    "$ABC" -s -c "read_blif $input; &get -m; &put; write_blif $TMP/roundtrip.tmp; read_blif $TMP/roundtrip.tmp; &get -m; &put; strash; &get; &w $TMP/after.aig; echo PUT_DONE" > "$TMP/convert.log" 2>&1
    grep -q 'PUT_DONE' "$TMP/convert.log" || { cat "$TMP/convert.log"; fail "$name: incomplete round trip"; }
    check_equivalent "$name repeated round trip"
    echo "PASS: $name"
done
echo 'All repeated-fanin output-polarity tests passed.'
