#!/usr/bin/env bash
source "$(dirname "$0")/common.sh"
ulimit -c 0
cat > cells.lib <<'EOF'
// test comment
/* test comment */
library(demo) {
  cell(BUF) {
    area: 6;
    pin(A) { direction: input; }
    pin(Y) { direction: output;
              function: "A"; }
  }
  cell(NOT) {
    area: 3;
    pin(A) { direction: input; }
    pin(Y) { direction: output;
              function: "A'"; }
  }
  cell(NAND) {
    dont_use : "false";
    area: 4;
    pin(A) { direction: input; }
    pin(B) { direction: input; }
    pin(Y) { direction: output;
             function: "(A*B)'"; }
  }
  cell(NOR) {
    area: 4;
    pin(A) { direction: input; }
    pin(B) { direction: input; }
    pin(Y) { direction: output;
             function: "(A+B)'"; }
  }
  cell(DFF) {
    area: 18;
    ff(IQ, IQN) { clocked_on: C;
                  next_state: D; }
    pin(C) { direction: input;
                 clock: true; }
    pin(D) { direction: input; }
    pin(Q) { direction: output;
              function: "IQ"; }
  }
  cell(DFFSR) {
    area: 18;
    ff("IQ", "IQN") { clocked_on: C;
                  next_state: D;
                      preset: S;
                       clear: R; }
    pin(C) { direction: input;
                 clock: true; }
    pin(D) { direction: input; }
    pin(Q) { direction: output;
              function: "IQ"; }
    pin(S) { direction: input; }
    pin(R) { direction: input; }
    ; // empty statement
  }
}
EOF
for value in false '"false"' true '"true"'; do
    sed "s/\"false\"/$value/" cells.lib > test.lib
    run_abc 'read_lib -w -v test.lib'
    case "$value" in
        *false*) if grep -q 'skipped cell "NAND"' abc.log; then cat abc.log; exit 1; fi ;;
        *true*) expect_log 'skipped cell "NAND"' ;;
    esac
done
run_abc 'read_lib -w -v -X NAND cells.lib'
expect_log 'skipped cell "NAND"'
echo 'PASS: Issue #140'
