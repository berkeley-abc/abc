#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)
data_dir="$repo_root/src/formace_ext/tests/data"
abc_bin=${ABC_BIN:-"$repo_root/abc"}

make -C "$repo_root" -j4 ABC_USE_NO_READLINE=1 abc

plain=$(
  "$abc_bin" -c "fm_minunsat -v $data_dir/minunsat_clauses.cnf"
)
printf '%s\n' "$plain"
printf '%s' "$plain" | rg -q \
  'status=UNSAT mode=clauses vars=2 clauses=4 hard=0 candidates=4 minimum=2'
printf '%s' "$plain" | rg -q '^selected_clauses=1 2$'
printf '%s' "$plain" | rg -q '^fm_minunsat stats:'
printf '%s' "$plain" | rg -q 'disjoint_lower=2$'

raw=$(
  "$abc_bin" -c "fm_minunsat -r $data_dir/minunsat_clauses.cnf"
)
printf '%s\n' "$raw"
printf '%s' "$raw" | rg -q 'candidates=4 minimum=2'
printf '%s' "$raw" | rg -q '^selected_clauses=1 2$'

json=$(
  "$abc_bin" -c \
    "fm_minunsat -j -A core-only-seed -g $data_dir/minunsat_grouped.groups $data_dir/minunsat_grouped.cnf"
)
printf '%s\n' "$json"
printf '%s' "$json" | rg -q \
  '"variant":"core-only-seed","seed_strategy":"raw-core","status":"ok"'
printf '%s' "$json" | rg -q '"minimum":1,"selected":\[1\]'
printf '%s' "$json" | rg -q '"minimize_seed":0'
printf '%s' "$json" | rg -q '"disjoint_lower":1'
printf '%s' "$json" | rg -q \
  '"cadical_plain":0,"cadical_ilb":1,"cadical_stable_only":0'

legacy_json=$(
  "$abc_bin" -c \
    "fm_minunsat -j -A cadical-plain-stable -g $data_dir/minunsat_grouped.groups $data_dir/minunsat_grouped.cnf"
)
printf '%s\n' "$legacy_json"
printf '%s' "$legacy_json" | rg -q \
  '"cadical_plain":1,"cadical_ilb":1,"cadical_stable_only":1'

grouped=$(
  "$abc_bin" -c \
    "fm_minunsat -g $data_dir/minunsat_grouped.groups $data_dir/minunsat_grouped.cnf"
)
printf '%s\n' "$grouped"
printf '%s' "$grouped" | rg -q \
  'status=UNSAT mode=groups vars=2 clauses=5 hard=1 candidates=3 minimum=1'
printf '%s' "$grouped" | rg -q '^selected_groups=1$'

hard_unsat=$(
  "$abc_bin" -c \
    "fm_minunsat -g $data_dir/minunsat_hard_unsat.groups $data_dir/minunsat_hard_unsat.cnf"
)
printf '%s\n' "$hard_unsat"
printf '%s' "$hard_unsat" | rg -q \
  'status=UNSAT mode=groups vars=2 clauses=3 hard=2 candidates=1 minimum=0'
printf '%s' "$hard_unsat" | rg -q '^selected_groups=$'

sat_output=$(
  "$abc_bin" -c "fm_minunsat $data_dir/minunsat_sat.cnf" 2>&1 || true
)
printf '%s\n' "$sat_output"
printf '%s' "$sat_output" | rg -q 'status=SAT; no UNSAT subset exists'

printf 'fm_minunsat command tests passed\n'
