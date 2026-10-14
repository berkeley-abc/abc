#!/usr/bin/env bash
# "buffer" must keep a CO that has the name of a CI (a latch output or a PI that is also a PO)
# driven by that CI, so that the network can be written out.
source "$(dirname "$0")/common.sh"
cat > mini.lib <<'EOF'
library(mini) {
  delay_model : table_lookup;
  time_unit : "1ns";
  capacitive_load_unit(1, pf);
  lu_table_template(t) { variable_1 : input_net_transition; variable_2 : total_output_net_capacitance; index_1("0.1"); index_2("0.1"); }
EOF
cell() { # name function input-pins...
    local name=$1 function=$2 pin; shift 2
    echo "  cell($name) { area : 1;"
    for pin; do echo "    pin($pin) { direction : input; capacitance : 0.01; }"; done
    echo "    pin(Y) { direction : output; function : \"$function\"; max_capacitance : 1;"
    for pin; do
        echo "      timing() { related_pin : \"$pin\"; cell_rise(t) { values(\"0.1\"); } cell_fall(t) { values(\"0.1\"); }"
        echo "        rise_transition(t) { values(\"0.1\"); } fall_transition(t) { values(\"0.1\"); } }"
    done
    echo "    }"
    echo "  }"
}
{ cell BUF A A; cell INV '!A' A; cell AND2 'A * B' A B; echo "}"; } >> mini.lib
printf 'set_driving_cell BUF\nset_load 10\n' > mini.constr
# a latch output q that is also a PO
cat > latch.blif <<'EOF'
.model m
.inputs a b x
.outputs q y z
.latch a q 0
.names q x y
11 1
.names q b z
10 1
.end
EOF
# a latch output q that drives only the PO q
cat > only.blif <<'EOF'
.model m
.inputs a b
.outputs q y
.latch a q 0
.names a b y
11 1
.end
EOF
# a PI a that is also a PO
cat > pi.blif <<'EOF'
.model m
.inputs a b
.outputs a y z
.names a b y
11 1
.names a b z
10 1
.end
EOF
# The driving cell and the output load, with -N 1 -G 1, make "buffer" buffer every CI, even one with a single fanout.
# "buffer" must succeed, keep the function and leave a network that write_blif can write.
run_case() {
    run_abc "read_lib mini.lib; read_blif $1.blif; read_constr mini.constr; strash; map; buffer -N 1 -G 1; $2 $1.blif; write_blif $1.out.blif"
    expect_log 'Networks are equivalent'
    [ -s "$1.out.blif" ] || { cat abc.log; echo "Missing: $1.out.blif" >&2; exit 1; }
}
run_case latch dsec
run_case only dsec
run_case pi cec
echo 'PASS: buffer keeps a CO on the CI of the same name'
