#!/usr/bin/env bash
# Verify that diagnostic switches preserve sequential resubstitution results,
# exact Build attribution remains visible, and drw cut-size modes stay sound.
set -eu
ABC=${ABC:-./abc}
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
fail() { echo "FAIL: $1" >&2; exit 1; }
if ! command -v python3 > /dev/null; then
    echo "SKIP: python3 is needed to write the witness AIGER files"
    exit 0
fi
python3 - "$TMP" <<'PY'
import pathlib, random, sys
out = pathlib.Path(sys.argv[1])
class Aig:
    def __init__(self, inputs, regs):
        self.inputs, self.regs = inputs, regs
        self.gates, self.next, self.outputs = [], [], []
    def land(self, a, b):
        self.gates.append((a, b))
        return 2 * (self.inputs + self.regs + len(self.gates))
    def lor(self, a, b):
        return self.land(a ^ 1, b ^ 1) ^ 1
    def write(self, name):
        def encode(value):
            data = bytearray()
            while value > 127:
                data.append((value & 127) | 128)
                value >>= 7
            data.append(value)
            return data
        with (out / (name + '.aig')).open('wb') as f:
            f.write(('aig %d %d %d %d %d\n' % (
                self.inputs + self.regs + len(self.gates), self.inputs,
                self.regs, len(self.outputs), len(self.gates))).encode())
            for value in self.next + self.outputs:
                f.write(('%d\n' % value).encode())
            for i, (a, b) in enumerate(self.gates, self.inputs + self.regs + 1):
                a, b = sorted((a, b), reverse=True)
                f.write(encode(2 * i - a) + encode(a - b))
# Twelve disjoint distributivity cones require real Build replacements.
p = Aig(12, 24)
p.next = [2 * (i % 12 + 1) for i in range(24)]
for i in range(12):
    a, b, c = 2 * (i + 1), 2 * (13 + 2 * i), 2 * (14 + 2 * i)
    p.outputs.append(p.lor(p.land(a, b), p.land(a, c)))
p.write('factor')
# A reproducible mixed network also exercises ODC discovery/proof/commit.
r = random.Random(100)
p = Aig(10, 8)
pool = list(range(2, 38, 2))
for i in range(80):
    a, b, c = [r.choice(pool) ^ r.randrange(2) for _ in range(3)]
    if i % 3 == 0:
        x = p.lor(p.land(a, b ^ 1), p.land(a ^ 1, b))
    elif i % 3 == 1:
        x = p.lor(p.land(c, a), p.land(c ^ 1, b))
    else:
        x = p.land(a, b)
    pool.append(x)
p.next = [r.choice(pool[-20:]) for _ in range(8)]
p.outputs = pool[-8:]
p.write('mixed')
PY
for fixture in factor mixed; do
    for mode in strict odc; do
        flags=""
        if [ "$mode" = strict ]; then flags="-s"; fi
        for diagnostics in quiet p v pv; do
            extra=""
            if [ "$diagnostics" != quiet ]; then extra="-$diagnostics"; fi
            prefix="$TMP/${fixture}_${mode}_${diagnostics}"
            "$ABC" -q "&read $TMP/$fixture.aig; &sresub $flags $extra; &write -s $prefix.aig" > "$prefix.log" 2>&1
            [ -s "$prefix.aig" ] || fail "$fixture $mode $diagnostics: missing result"
            case "$diagnostics" in
                quiet) [ ! -s "$prefix.log" ] || { cat "$prefix.log"; fail "normal run is noisy"; } ;;
                p)
                    grep -q '^sresub build reduction:' "$prefix.log" || fail "missing Build profile"
                    if grep -v '^sresub build reduction:' "$prefix.log" | grep -q '[^[:space:]]'; then
                        cat "$prefix.log"; fail "-p printed extra diagnostics"
                    fi ;;
                v) grep -q '^stran-root summary:' "$prefix.log" || fail "missing verbose summary" ;;
                pv)
                    grep -q '^stran-root summary:' "$prefix.log" || fail "missing verbose summary"
                    grep '^sresub build reduction:' "$prefix.log" > "$prefix.build"
                    cmp "$prefix.build" "$TMP/${fixture}_${mode}_p.log" || fail "verbose changed Build attribution" ;;
            esac
            cmp "$prefix.aig" "$TMP/${fixture}_${mode}_quiet.aig" || fail "diagnostics changed result"
        done
        "$ABC" -q "dsec -T 20 $TMP/$fixture.aig $TMP/${fixture}_${mode}_quiet.aig" > "$TMP/equiv.log" 2>&1
        grep -q 'Networks are equivalent' "$TMP/equiv.log" || { cat "$TMP/equiv.log"; fail "sequential equivalence"; }
        echo "PASS: $fixture $mode quiet/-p/-v/-pv and sequential equivalence"
    done
done
grep -q 'selected=12 .*ordered-and-gain=12$' "$TMP/factor_strict_p.log" || fail "nonzero exact Build witness changed"
grep -Eq '^stran-root ODC fanout summary:.* selected=[1-9][0-9]* .* gain=[1-9][0-9]* ' "$TMP/mixed_odc_v.log" || fail "mixed fixture did not exercise an ODC commit"
for k in 4 6 10; do
    "$ABC" -q "read_aiger $TMP/factor.aig; strash; drw -K $k; write_aiger $TMP/drw$k.aig" > "$TMP/drw.log" 2>&1
    [ -s "$TMP/drw$k.aig" ] || fail "drw -K $k missing result"
    "$ABC" -q "dsec -T 20 $TMP/factor.aig $TMP/drw$k.aig" > "$TMP/equiv.log" 2>&1
    grep -q 'Networks are equivalent' "$TMP/equiv.log" || { cat "$TMP/equiv.log"; fail "drw equivalence"; }
    echo "PASS: drw -K $k and sequential equivalence"
done
# Negative-unate polarity branches must be mutually exclusive: this cone
# is exactly ~a & b and should reduce to one AND, independent of c.
cat > "$TMP/negative-unate.blif" <<'BLIF'
.model negative_unate
.inputs a b c
.outputs z
.names b c t0
01 1
.names a t0 t1
0- 1
-1 1
.names a c t2
10 1
.names b t2 t3
10 1
.names t1 t3 z
11 1
.end
BLIF
"$ABC" -q "read_blif $TMP/negative-unate.blif; strash; write_aiger $TMP/negative-before.aig; drw -K 4; write_aiger $TMP/negative-after.aig" > "$TMP/negative.log" 2>&1
python3 - "$TMP/negative-after.aig" <<'PY_AIG'
import pathlib, sys
header = pathlib.Path(sys.argv[1]).read_bytes().splitlines()[0].split()
assert header[0] == b'aig' and int(header[5]) == 1, header
PY_AIG
"$ABC" -q "cec $TMP/negative-before.aig $TMP/negative-after.aig" > "$TMP/equiv.log" 2>&1
grep -q 'Networks are equivalent' "$TMP/equiv.log" || { cat "$TMP/equiv.log"; fail "negative-unate equivalence"; }
echo "PASS: negative-unate drw reduces to one AND and remains equivalent"
# Omitting -K, or setting it to zero, keeps the original rewriting mode.
for options in "" "-r" "-K 0" "-K 0 -r"; do
    "$ABC" -q "read_aiger $TMP/factor.aig; strash; drw $options -v; write_aiger $TMP/rewrite.aig" > "$TMP/rewrite.log" 2>&1
    [ -s "$TMP/rewrite.aig" ] || fail "rewriting failed: $options"
    if grep -q 'DAR_RESUB' "$TMP/rewrite.log"; then fail "rewriting entered resub: $options"; fi
    rm "$TMP/rewrite.aig"
done
for options in "-K" "-K -1" "-K 3" "-K 11" "-K bad" "-K 999999999999999999999" "-k 6" "-K 6 -z"; do
    status=0
    "$ABC" -q "read_aiger $TMP/factor.aig; strash; drw $options; write_aiger $TMP/invalid-drw.aig" > "$TMP/invalid-drw.log" 2>&1 || status=$?
    [ "$status" -lt 128 ] || fail "invalid drw arguments caused a signal: $options"
    grep -q 'usage: drw' "$TMP/invalid-drw.log" || fail "missing invalid drw diagnostic: $options"
    [ ! -e "$TMP/invalid-drw.aig" ] || fail "invalid drw arguments continued: $options"
done
echo "PASS: drw rewriting mode and invalid -K arguments"
"$ABC" -q '&scorr -h' > "$TMP/scorr-help.log" 2>&1 || :
grep -q -- '-Z num' "$TMP/scorr-help.log" || fail "&scorr lost -Z"
"$ABC" -q '&scorr2 -h' > "$TMP/scorr2-help.log" 2>&1 || :
if grep -q -- '-Z' "$TMP/scorr2-help.log"; then fail "&scorr2 still advertises -Z"; fi
"$ABC" -q "&read $TMP/factor.aig; &scorr2 -Z 1; &write -s $TMP/invalid-scorr2.aig" > "$TMP/scorr2-invalid.log" 2>&1 || :
grep -q 'usage: &scorr2' "$TMP/scorr2-invalid.log" || fail "&scorr2 accepted -Z"
[ ! -e "$TMP/invalid-scorr2.aig" ] || fail "&scorr2 -Z continued"
echo "PASS: &scorr retains -Z and &scorr2 rejects it"
# ABC's batch wrapper may return zero after a command error. Check the
# diagnostic and lack of output, and reject signals explicitly.
for options in "-f" "-f 0" "-f -1" "-f bad" "-f 2147483646" "-f 2147483647" "-c -1" "-c bad" "-c 999999999999999999999" "-x" "unexpected"; do
    prefix="$TMP/invalid"
    rm -f "$prefix.aig"
    status=0
    "$ABC" -q "&read $TMP/factor.aig; &sresub $options; &write -s $prefix.aig" > "$prefix.log" 2>&1 || status=$?
    [ "$status" -lt 128 ] || fail "invalid sresub arguments caused a signal: $options"
    grep -Eq 'usage: &sresub|&sresub:.*(frame|depth)' "$prefix.log" || fail "missing invalid-argument diagnostic: $options"
    [ ! -e "$prefix.aig" ] || fail "invalid sresub arguments continued: $options"
done
for setting in ABC_SRESUB_LOCAL_DOMAIN=bad ABC_STRAN_STRICT_TEMPORAL_DOMAIN=bad ABC_STRAN_STRICT_TEMPORAL_DOMAIN=1; do
    prefix="$TMP/invalid-env"
    rm -f "$prefix.aig"
    status=0
    env "$setting" "$ABC" -q "&read $TMP/factor.aig; &sresub -s; &write -s $prefix.aig" > "$prefix.log" 2>&1 || status=$?
    [ "$status" -lt 128 ] || fail "invalid sresub environment caused a signal: $setting"
    grep -q '&sresub: ABC_SRESUB_LOCAL_DOMAIN' "$prefix.log" || fail "missing environment diagnostic: $setting"
    [ ! -e "$prefix.aig" ] || fail "invalid sresub environment continued: $setting"
done
for setting in ABC_CEX_MODE=1 ABC_CEX_COMPRESS=0; do
    status=0
    env "$setting" "$ABC" -q "&read $TMP/factor.aig; &sresub" > "$TMP/invalid-odc.log" 2>&1 || status=$?
    [ "$status" -lt 128 ] || fail "incompatible ODC options caused a signal: $setting"
    grep -q '&sresub: ODC signature guide requires' "$TMP/invalid-odc.log" || fail "missing ODC option diagnostic: $setting"
done
echo "PASS: invalid sresub arguments and environment reject without signals"
echo "All cleanup regression tests passed."
