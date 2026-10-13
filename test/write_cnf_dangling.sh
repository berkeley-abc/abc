#!/usr/bin/env bash
# Issue #479: discard the reserved CNF slot, but preserve free source inputs.
source "$(dirname "$0")/issues/common.sh"

count_models() {
    awk '
        BEGIN { clauses = 0; count = 0 }
        /^c/ { next }
        /^p/ { vars = $3; expected = $4; next }
        {
            for (i = 1; i <= NF; i++)
                if ($i == 0) clauses++;
                else lits[clauses, ++sizes[clauses]] = $i;
        }
        END {
            if (vars > 16 || clauses != expected) exit 1;
            for (a = 0; a < 2^vars; a++) {
                good = 1;
                for (c = 0; c < clauses && good; c++) {
                    satisfied = 0;
                    for (i = 1; i <= sizes[c]; i++) {
                        lit = lits[c, i]; v = lit < 0 ? -lit : lit;
                        if (v < 1 || v > vars) exit 1;
                        bit = int(a / 2^(v-1)) % 2;
                        if (bit == (lit > 0)) satisfied = 1;
                    }
                    if (!satisfied) good = 0;
                }
                count += good;
            }
            print count + 0;
        }
    ' "$1"
}

run_case() {
    local name=$1 expected=$2 input=$3 format=${4:-cnf} flags count
    printf '%s\n' "$input" > "input.$format"
    if [ "$format" = cnf ]; then
        test "$(count_models input.cnf)" = "$expected"
    fi
    for flags in '' '-f' '-c' '-fc'; do
        run_abc "read_$format input.$format; strash; write_cnf $flags output.cnf; write_cnf $flags output.cnf.gz"
        gzip -dc output.cnf.gz > compressed.cnf
        cmp output.cnf compressed.cnf
        count=$(count_models output.cnf)
        if [ "$count" != "$expected" ]; then
            cat output.cnf
            echo "FAIL: $name $flags: expected $expected models, got $count" >&2
            exit 1
        fi
    done
}

run_case positive 1 'p cnf 1 1
1 0'
run_case negative 1 'p cnf 1 1
-1 0'
run_case two_units 1 'p cnf 2 2
1 0
2 0'
run_case disjunction 3 'p cnf 2 1
1 2 0'
run_case free_input 2 'p cnf 2 1
1 0'
run_case free_inputs 4 'p cnf 3 1
2 0'
run_case redundant_input 2 'p cnf 2 2
1 2 0
1 -2 0'
run_case constant_true 2 '.model constant_true
.inputs a
.outputs y
.names y
1
.end' blif
run_case unsatisfiable 0 'p cnf 1 2
1 0
-1 0'
echo 'PASS: Issue #479'
