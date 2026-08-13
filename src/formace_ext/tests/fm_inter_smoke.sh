#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "$script_dir/../../.." && pwd)
abc_bin=${ABC_BIN:-"$repo_dir/abc"}
work_dir=$(mktemp -d "${TMPDIR:-/tmp}/fm_inter_smoke.XXXXXX")
trap 'rm -rf "$work_dir"' EXIT

onset="$script_dir/data/on_xor_unused.blif"
offset="$script_dir/data/off_xnor_unused.blif"
offset_inv="$work_dir/off_xor.blif"

"$abc_bin" -c "read_blif $offset; strash -i; write_blif $offset_inv"

run_mode() {
    local mode=$1
    local output="$work_dir/$mode.blif"

    "$abc_bin" -c "fm_inter $mode -L 3 $onset $offset; write_blif $output"
    rg -q '^\.inputs x y z$' "$output"
    ! rg -q '^\.names.*\bz\b' "$output"
    "$abc_bin" -c "miter -i $onset $output; iprove" | rg -q 'UNSATISFIABLE'
    "$abc_bin" -c "miter -i $output $offset_inv; iprove" | rg -q 'UNSATISFIABLE'
}

run_mode -m
run_mode -c
run_mode -y

edge_onset="$script_dir/data/on_x.blif"
edge_offset="$script_dir/data/off_notx.blif"
edge_output="$work_dir/edge.blif"
edge_hybrid_output="$work_dir/edge_hybrid.blif"
edge_offset_inv="$work_dir/edge_offset_inv.blif"
"$abc_bin" -c "read_blif $edge_offset; strash -i; write_blif $edge_offset_inv"
"$abc_bin" -c "fm_inter -m -L 1 $edge_onset $edge_offset; write_blif $edge_output"
"$abc_bin" -c "miter -i $edge_onset $edge_output; iprove" | rg -q 'UNSATISFIABLE'
"$abc_bin" -c "miter -i $edge_output $edge_offset_inv; iprove" | rg -q 'UNSATISFIABLE'
"$abc_bin" -c "fm_inter -y -L 1 $edge_onset $edge_offset; write_blif $edge_hybrid_output"
"$abc_bin" -c "miter -i $edge_onset $edge_hybrid_output; iprove" | rg -q 'UNSATISFIABLE'
"$abc_bin" -c "miter -i $edge_hybrid_output $edge_offset_inv; iprove" | rg -q 'UNSATISFIABLE'

printf 'fm_inter smoke tests passed\n'
