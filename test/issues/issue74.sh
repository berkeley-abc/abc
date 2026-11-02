#!/usr/bin/env bash
source "$(dirname "$0")/common.sh"
ulimit -c 0
printf -v zeros '%0128d' 0
for bounds in '127:0' '0:127' '128:0' '1267:0' '0:128'; do
    cat > bus.v <<EOF
module top ( a, y );
input [$bounds] a;
output [$bounds] y;
assign y = 128'b$zeros;
endmodule
EOF
    "$ABC" -s -c 'read_verilog bus.v; print_stats' > abc.log 2>&1 || :
    case "$bounds" in
        '127:0'|'0:127') expect_log 'i/o.*128.*128' ;;
        *) expect_log 'Bus indices must be between 0 and 127' ;;
    esac
done
echo 'PASS: Issue #74'
