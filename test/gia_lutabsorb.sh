#!/usr/bin/env bash
# Regression tests for &lutabsorb (mapping-level LUT absorption in ABC9).
set -eu
ABC=${ABC:-./abc}
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
fail() { echo "FAIL: $1" >&2; exit 1; }

cat > "$TMP/basic.blif" <<'EOF'
.model basic
.inputs a b c d e
.outputs y z
.names a b u
11 1
.names u c w
11 1
.names u w v
11 1
.names v d y
1- 1
-1 1
.names w e z
11 1
.end
EOF

cat > "$TMP/rounds.blif" <<'EOF'
.model rounds
.inputs a b c d e
.outputs w v
.names a b l
11 1
.names l c u
11 1
.names u d w
11 1
.names u e v
11 1
.end
EOF

cat > "$TMP/co.blif" <<'EOF'
.model co
.inputs a b c d e
.outputs w v u
.names a b l
11 1
.names l c u
11 1
.names u d w
11 1
.names u e v
11 1
.end
EOF

cat > "$TMP/three.blif" <<'EOF'
.model three
.inputs a b c d e f
.outputs t s
.names a b l
11 1
.names l c u
11 1
.names u d w
11 1
.names u e v
11 1
.names u f s
11 1
.names w v t
11 1
.end
EOF

cat > "$TMP/lut6_unit.lut" <<'EOF'
1 1 1
2 1 2
3 1 3
4 1 4
5 1 5
6 1 6
EOF

cat > "$TMP/lut6_exp.lut" <<'EOF'
1 1 1
2 2 2
3 4 3
4 8 4
5 16 5
6 32 6
EOF

run_abs() { # $1 = blif, $2 = extra options
    "$ABC" -s -c "read_blif $1; &get -m; &lutabsorb -v $2" > "$TMP/run.log" 2>&1 || true
}
expect() { # $1 = fixed string, $2 = message
    grep -Fq "$1" "$TMP/run.log" || { cat "$TMP/run.log"; fail "$2"; }
}
absent() { # $1 = fixed string, $2 = message
    if grep -Fq "$1" "$TMP/run.log"; then cat "$TMP/run.log"; fail "$2"; fi
}

# 1. Default (4-input unit library): absorb u then w in the same pass.
run_abs "$TMP/basic.blif" ""
expect "Round 1: removed 2 LUTs, area gain 2.00." "basic: round output"
expect "lutabsorb: K=4 M=8 R=1  LUTs 5 -> 3 (-2)" "basic: summary"
expect "area gain 2.00" "basic: area gain"
echo "PASS: basic absorption"

# 2. -K disables the library.
run_abs "$TMP/basic.blif" "-K 6"
expect "lutabsorb: K=6 M=8 R=1  LUTs 5 -> 3 (-2)" "-K: summary"
absent "area gain" "-K: library must be disabled"
echo "PASS: -K disables the library"

# 3. -M bounds the fanout count.
run_abs "$TMP/three.blif" "-M 2"
expect "lutabsorb: K=4 M=2 R=1  LUTs 6 -> 6 (-0)" "-M 2: summary"
run_abs "$TMP/three.blif" "-M 3"
expect "lutabsorb: K=4 M=3 R=1  LUTs 6 -> 5 (-1)" "-M 3: summary"
echo "PASS: -M bounds the fanout count"

# 4. -R repeats passes; the second pass picks up a new opportunity.
run_abs "$TMP/rounds.blif" "-R 1"
expect "lutabsorb: K=4 M=8 R=1  LUTs 4 -> 3 (-1)" "-R 1: summary"
run_abs "$TMP/rounds.blif" "-R 3"
expect "Round 1: removed 1 LUTs" "-R 3: round 1"
expect "Round 2: removed 1 LUTs" "-R 3: round 2"
expect "Round 3: removed 0 LUTs" "-R 3: round 3"
expect "lutabsorb: K=4 M=8 R=3  LUTs 4 -> 2 (-2)" "-R 3: summary"
echo "PASS: -R repeats passes"

# 5. A LUT that drives a CO is never absorbed.
run_abs "$TMP/co.blif" "-R 3"
expect "lutabsorb: K=4 M=8 R=3  LUTs 4 -> 4 (-0)" "CO driver: summary"
echo "PASS: CO driver is skipped"

# 6. Custom LUT libraries.
"$ABC" -s -c "read_lut $TMP/lut6_unit.lut; read_blif $TMP/basic.blif; &get -m; &lutabsorb -v" > "$TMP/run.log" 2>&1 || true
expect "lutabsorb: K=6 M=8 R=1  LUTs 5 -> 3 (-2)" "unit 6-LUT lib: summary"
expect "area gain 2.00" "unit 6-LUT lib: area gain"
"$ABC" -s -c "read_lut $TMP/lut6_exp.lut; read_blif $TMP/basic.blif; &get -m; &lutabsorb -v" > "$TMP/run.log" 2>&1 || true
expect "lutabsorb: K=6 M=8 R=1  LUTs 5 -> 5 (-0)" "exp 6-LUT lib: summary"
expect "area gain 0.00" "exp 6-LUT lib: area gain"
echo "PASS: custom LUT libraries"

# 7. Equivalence after remapping, checked through &put.
check_equiv() { # $1 = blif, $2 = message
    "$ABC" -s -c "read_blif $1; &get -m; &lutabsorb; &put; write_blif $TMP/out.blif; echo ABS_DONE" > "$TMP/put.log" 2>&1 || true
    grep -Fq ABS_DONE "$TMP/put.log" || { cat "$TMP/put.log"; fail "$2: &put did not complete"; }
    "$ABC" -s -c "read_blif $1; cec -n $TMP/out.blif; echo CEC_DONE" > "$TMP/cec.log" 2>&1 || true
    grep -Fq CEC_DONE "$TMP/cec.log" || { cat "$TMP/cec.log"; fail "$2: incomplete CEC"; }
    grep -Fq "Networks are equivalent" "$TMP/cec.log" || { cat "$TMP/cec.log"; fail "$2: not equivalent"; }
}
check_equiv "$TMP/basic.blif" "basic"
check_equiv "$TMP/rounds.blif" "rounds"
echo "PASS: equivalence through &put"

# 8. The command requires a mapping.
"$ABC" -s -c "read_blif $TMP/basic.blif; &get; &lutabsorb" > "$TMP/nomap.log" 2>&1 || true
grep -Fq "no LUT mapping" "$TMP/nomap.log" || { cat "$TMP/nomap.log"; fail "no-mapping error missing"; }
echo "PASS: no-mapping error"

# 9. Smoke test on an &if-produced mapping.
"$ABC" -s -c "read_blif $TMP/basic.blif; &get; &if -K 6; &lutabsorb -K 6 -v; &put; write_blif $TMP/if_out.blif; echo IF_DONE" > "$TMP/if.log" 2>&1 || true
grep -Fq IF_DONE "$TMP/if.log" || { cat "$TMP/if.log"; fail "&if flow did not complete"; }
"$ABC" -s -c "read_blif $TMP/basic.blif; cec -n $TMP/if_out.blif; echo CEC_DONE" > "$TMP/if_cec.log" 2>&1 || true
grep -Fq "Networks are equivalent" "$TMP/if_cec.log" || { cat "$TMP/if_cec.log"; fail "&if flow not equivalent"; }
echo "PASS: &if smoke test"

# 10. A no-op run must not invalidate derived mapping data (packing).
"$ABC" -s -c "read_blif $TMP/co.blif; &get -m; &pack; &ps" > "$TMP/pack_before.log" 2>&1 || true
grep -Fq "Packing (N=2)" "$TMP/pack_before.log" || { cat "$TMP/pack_before.log"; fail "packing fixture did not produce packing info"; }
"$ABC" -s -c "read_blif $TMP/co.blif; &get -m; &pack; &lutabsorb -R 3; &ps" > "$TMP/pack_after.log" 2>&1 || true
grep -Fq "LUTs 4 -> 4 (-0)" "$TMP/pack_after.log" || { cat "$TMP/pack_after.log"; fail "packing fixture was not a no-op"; }
grep -Fq "Packing (N=2)" "$TMP/pack_after.log" || { cat "$TMP/pack_after.log"; fail "no-op &lutabsorb dropped packing data"; }
echo "PASS: no-op run preserves packing"

echo "All &lutabsorb tests passed."
