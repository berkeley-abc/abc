#!/usr/bin/env bash
source "$(dirname "$0")/common.sh"
ulimit -c 0
cat > cover.blif <<'EOF'
# Benchmark "netlist" written by ABC on Wed Feb 17 18:04:55 2021
.model netlist
.inputs ys__n0 ys__n1 ys__n5 ys__n6 ys__n8 ys__n9 ys__n13 ys__n14 ys__n16 \
 ys__n17 ys__n20 ys__n21 ys__n23 ys__n24 ys__n29 ys__n31 ys__n32
.outputs ys__n30
.names ys__n8 ys__n9 new_n19_
10 1
.names ys__n20 ys__n21 new_n20_
10 1
.names new_n19_ new_n20_ new_n21_
00 1
.names ys__n5 ys__n6 new_n22_
10 1
.names ys__n5 ys__n6 new_n23_
01 1
.names new_n22_ new_n23_ new_n24_
00 1
.names ys__n5 ys__n6 new_n25_
11 1
.names ys__n5 ys__n6 new_n26_
00 1
.names new_n25_ new_n26_ new_n27_
00 1
.names ys__n13 ys__n14 new_n28_
00 1
.names ys__n13 ys__n14 new_n29_
11 1
.names new_n28_ new_n29_ new_n30_
00 1
.names new_n84_ new_n30_ new_n31_
00 1
.names ys__n23 ys__n24 new_n32_
01 1
.names ys__n0 ys__n1 new_n33_
10 1
.names ys__n0 ys__n1 new_n34_
01 1
.names new_n33_ new_n34_ new_n35_
00 1
.names new_n32_ new_n35_ new_n36_
01 1
.names new_n31_ new_n36_ new_n37_
11 1
.names new_n21_ new_n37_ new_n38_
11 1
.names ys__n8 ys__n9 new_n39_
01 1
.names ys__n16 ys__n17 new_n40_
10 1
.names new_n39_ new_n40_ new_n41_
00 1
.names ys__n31 ys__n32 new_n42_
10 1
.names ys__n31 ys__n32 new_n43_
01 1
.names ys__n23 ys__n24 new_n44_
10 1
.names new_n43_ new_n44_ new_n45_
00 1
.names new_n42_ new_n45_ new_n46_
01 1
.names ys__n16 ys__n17 new_n47_
01 1
.names ys__n20 ys__n21 new_n48_
01 1
.names ys__n29 new_n48_ new_n49_
00 1
.names new_n47_ new_n49_ new_n50_
01 1
.names new_n46_ new_n50_ new_n51_
11 1
.names new_n41_ new_n51_ new_n52_
11 1
.names new_n38_ new_n52_ new_n53_
11 1
.names new_n21_ new_n41_ new_n54_
11 1
.names ys__n29 new_n33_ new_n55_
00 1
.names new_n30_ new_n55_ new_n56_
01 1
.names new_n84_ new_n56_ new_n57_
01 1
.names new_n43_ new_n47_ new_n58_
00 1
.names new_n48_ new_n58_ new_n59_
01 1
.names new_n32_ new_n34_ new_n60_
00 1
.names new_n42_ new_n44_ new_n61_
00 1
.names new_n60_ new_n61_ new_n62_
11 1
.names new_n59_ new_n62_ new_n63_
11 1
.names new_n57_ new_n63_ new_n64_
11 1
.names new_n54_ new_n64_ new_n65_
11 1
.names ys__n29 new_n19_ new_n66_
00 1
.names new_n33_ new_n39_ new_n67_
00 1
.names new_n40_ new_n42_ new_n68_
00 1
.names new_n67_ new_n68_ new_n69_
11 1
.names new_n66_ new_n69_ new_n70_
11 1
.names ys__n13 ys__n14 new_n71_
10 1
.names new_n34_ new_n43_ new_n72_
00 1
.names new_n71_ new_n72_ new_n73_
01 1
.names new_n47_ new_n48_ new_n74_
00 1
.names ys__n13 ys__n14 new_n75_
01 1
.names new_n22_ new_n75_ new_n76_
00 1
.names new_n74_ new_n76_ new_n77_
11 1
.names new_n32_ new_n44_ new_n78_
00 1
.names new_n20_ new_n23_ new_n79_
00 1
.names new_n78_ new_n79_ new_n80_
11 1
.names new_n77_ new_n80_ new_n81_
11 1
.names new_n73_ new_n81_ new_n82_
11 1
.names new_n70_ new_n82_ new_n83_
11 1
.names new_n27_ new_n24_ new_n84_
1- 1
-0 1
.names new_n83_ new_n65_ new_n53_ new_n85_
1-- 1
-1- 1
--1 1
.names new_n85_ ys__n30
0 1
.end
EOF
for limit in 2 3 4 5 6 8; do
    run_abc "read_blif cover.blif; strash; write_aiger ref.aig; cover -I 40 -P $limit; write_blif covered.blif; strash; &get; &cec ref.aig"
    expect_log 'Networks are equivalent'
    awk -v limit="$limit" '
      /^\./ { if (count > limit) exit 1; count=0; inside=($1==".names"); next }
      inside && /^[01-]/ { count++ }
      END { if (count > limit) exit 1 }
    ' covered.blif
done
echo 'PASS: Issue #120 (six bounds and equivalence checks)'
