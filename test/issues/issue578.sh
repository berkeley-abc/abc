#!/usr/bin/env bash
# Invalid truth tables and GENLIB byte order marks must not crash the readers.
source "$(dirname "$0")/common.sh"
for truth in a3f0 '1000 10x0'; do
    printf '%s\n' "$truth" > input.truth
    run_abc 'read_truth -xf input.truth'
    expect_log 'Reading truth table has failed'
done
for truth in g '8 g'; do
    printf '%s\n' "$truth" > input.truth
    run_abc 'read_truth -f input.truth'
    expect_log 'Reading truth table has failed'
done
run_abc 'read_truth 0x8; print_stats'
expect_log 'i/o = *2/ *1'
cat > plain.genlib <<'EOF'
GATE zero 0 Y=CONST0;
GATE one 0 Y=CONST1;
GATE buf 1 Y=A; PIN * NONINV 1 999 1 0 1 0
GATE inv 1 Y=!A; PIN * INV 1 999 1 0 1 0
GATE nand2 1 Y=!(A*B); PIN * INV 1 999 1 0 1 0
GATE nor2 1 Y=!(A+B); PIN * INV 1 999 1 0 1 0
EOF
printf '\357\273\277' > bom.genlib
cat plain.genlib >> bom.genlib
for library in plain bom; do
    run_abc "read_genlib -v $library.genlib; read_truth 8; strash; map; print_stats"
    expect_log 'Entered genlib library with 6 gates'
    expect_log 'area ='
done
printf '' > empty.genlib
run_abc 'read_genlib empty.genlib'
expect_log 'Reading genlib library has failed'
echo 'PASS: Issue #578'
