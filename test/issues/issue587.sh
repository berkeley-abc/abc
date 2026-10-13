#!/usr/bin/env bash
# Optional latch controls must not be mistaken for an initial value.
source "$(dirname "$0")/common.sh"
write_latch() {
    printf '.model hold\n.inputs d\n.outputs q\n.latch q q %s\n.end\n' "$1" > input.blif
}
for reader in '' '-n'; do
    for controls in '' 're NIL' 're clk' 're 1'; do
        write_latch "$controls"
        run_abc "read_blif $reader input.blif; write_blif output.blif; undc; strash; zero; pdr"
        grep -Eq '^\.latch .* 2$' output.blif
        expect_log 'asserted in frame 0'
        for init in 0 1 2 3; do
            write_latch "$controls $init"
            run_abc "read_blif $reader input.blif; write_blif output.blif"
            expected=$init
            if [ "$init" = 3 ]; then expected=2; fi
            grep -Eq "^\.latch .* $expected$" output.blif
        done
    done
    for init in bad -1 4 10; do
        write_latch "re NIL $init"
        run_abc "read_blif $reader input.blif"
        expect_log 'Initial state.*incorrect|unknown reset value'
    done
done
echo 'PASS: Issue #587'
