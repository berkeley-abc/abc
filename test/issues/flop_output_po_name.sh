#!/usr/bin/env bash
# "&get -n" and "&r" normalize flops with don't-care or 1 init values. A flop
# output that is also a PO (as in "yosys abc -dff") then differs from that PO,
# so the flop output is renamed and the PO keeps its name.
source "$(dirname "$0")/common.sh"
ulimit -c 0
cat > flops.blif <<'EOF'
.model flops
.inputs d e
.outputs q p y
.latch d q 2
.latch e p 1
.names q p y
11 1
.end
EOF
run_abc 'read_blif flops.blif; &get -n; &w normalized.aig'
run_abc 'read_blif flops.blif; &get -n; &if -K 4; &put; write_blif lut.blif'
run_abc 'read_blif flops.blif; &get -n; &put; write_blif aig.blif'
for f in lut aig; do
    run_abc "dsec $f.blif normalized.aig"
    expect_log 'Networks are equivalent'
    grep -q '^\.outputs q p y$' $f.blif
    grep -q '^\.latch .* q_lo ' $f.blif
    grep -q '^\.latch .* p_inv ' $f.blif
done
# A strashed network keeps don't-care init values as 0 and complements 1-valued flops.
run_abc 'read_blif flops.blif; strash; &get -n; &if -K 4; &put; write_blif strash.blif; dsec strash.blif flops.blif'
expect_log 'Networks are equivalent'
grep -q '^\.latch .* q ' strash.blif
grep -q '^\.latch .* p_inv ' strash.blif
# AIGER: input d, latch q with init 1, and output q.
printf 'aig 2 1 1 1 0\n2 1\n4\ni0 d\nl0 q\no0 q\n' > init1.aig
run_abc '&r init1.aig; &if -K 4; &put; write_blif init1.blif; dsec init1.blif init1.aig'
expect_log 'Networks are equivalent'
grep -q '^\.latch .* q_inv ' init1.blif
# The new name must differ from the existing names.
cat > taken.blif <<'EOF'
.model taken
.inputs d q_lo
.outputs q y
.latch d q 2
.names q_lo d y
11 1
.end
EOF
run_abc 'read_blif taken.blif; &get -n; &w taken.aig; &if -K 4; &put; write_blif taken-out.blif; dsec taken-out.blif taken.aig'
expect_log 'Networks are equivalent'
grep -q '^\.latch .* q_lo1 ' taken-out.blif
# A network with choices gives a GIA without flops, so nothing is renamed.
cat > adder.blif <<'EOF'
.model adder
.inputs a b c
.outputs s q
.latch n q 1
.names a b c s
100 1
010 1
001 1
111 1
.names a b c n
11- 1
1-1 1
-11 1
.end
EOF
run_abc 'read_blif adder.blif; strash; dch; ps; &get -n; &put; write_blif choices.blif'
expect_log 'choice = +[1-9]'
test -s choices.blif
echo 'PASS: flop outputs that are also POs'
