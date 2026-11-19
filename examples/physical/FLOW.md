# Practical-flow reproduction

For routed evaluation of these endpoints, use the separate
[OpenROAD runner](openroad/README.md) with `--cohort flow`.

AGR is both a standalone synthesis block and a replacement for optimization
slots in a conventional synthesis recipe. The primary practical comparison uses
`C -> S -> S -> R -> S` for every design:

| Flow | Each S slot |
|---|---|
| AGR | One `agr` invocation (three invocations in the complete flow) |
| PA slots | `pa_place`, two RS/RW/RF cycles, and normalization (six cycles total) |
| ABC-C | Repeated C macros until the corresponding slot CPU target is met |
| ABC-mix | Cycle E, E, R, B until that slot CPU target is met |

C is the fixed `compress2rs` expansion below. R is the same expansion without
`-l`, used as the fixed `resyn2rs` expansion. E is `&get; &dc2; &put`, and B is
`balance`. The runner expands all commands itself and ignores user startup files.
An ABC-mix slot may end after any complete macro, including inside E,E,R,B.
There is no endpoint-quality selection, rollback, or per-design recipe tuning.

All four flows start from the same saved `dc2`-preprocessed AIGs as the standalone
comparison. Do not repeat this preprocessing on those inputs. ABC-mix's `&dc2`
macros are additional measured synthesis work. Input preparation and the exact
bundled Liberty library are documented in [REPRODUCE.md](REPRODUCE.md).

## Run all four flows

Build ABC and extract the library as described in [REPRODUCE.md](REPRODUCE.md), then run:

```sh
python3 examples/physical/reproduce_flow.py \
  --abc build/abc \
  --inputs /path/to/paper/inputs \
  --liberty build/merged_asap7_final.lib \
  --paper-inputs \
  --output results/practical-default
```

For a short correctness check add `--designs ctrl,router`. For other
combinational AIGs omit `--paper-inputs`; that switch checks the archived input
and Liberty hashes, not historical flow-output identity.

The runner first measures the three AGR and PA2 slots, alternating the order of
these two flows between designs. Each native slot receives the larger CPU time
of its corresponding AGR/PA2 slots. Native work stops at a macro boundary after
meeting its target. C and R outside the slots are identical across the four
flows. Individual slot-budget compliance is recorded; it does not imply that
total flow CPU is identical, since the intervening R acts on different graphs.

One ABC process executes each complete flow. Synthesis CPU includes every C/R
macro, every slot command, guidance placement, incremental evaluation, and
normalization at macro boundaries. Process CPU also includes input/library
loading and output. All flows use the same executable and final mapper.
There is no technology mapping inside the synthesis recipe: E's `&get` and
`&put` only transfer AIG representations. Final mapping, independent fresh
AIG/mapped placement, and source/mapping CEC are separately recorded.

Outputs include `protocol.json`, exact `commands.abc` and logs for every run,
`results.csv`, `summary.json`, `REPORT.md`, and `recipes.json`. Summaries use
complete matched-design cohorts and retain regressions, failures, and unproved
CEC endpoints. Failed attempts cannot be silently rerun in the same directory.
Resume requires unchanged inputs, executable, scripts, and arguments. Run the
suite serially without competing synthesis/backend workloads.

## Direct ABC commands

These definitions are typed directly into ABC; no external alias file is
required. Boundary normalization matches the runner. AGR already includes its
final normalization.

```text
read preprocessed.aig
strash
read_lib build/merged_asap7_final.lib
alias flow_c "strash; balance -l; resub -K 6 -l; rewrite -l; resub -K 6 -N 2 -l; refactor -l; resub -K 8 -l; balance -l; resub -K 8 -N 2 -l; rewrite -l; resub -K 10 -l; rewrite -z -l; resub -K 10 -N 2 -l; balance -l; resub -K 12 -l; refactor -z -l; resub -K 12 -N 2 -l; rewrite -z -l; balance -l; strash"
alias flow_r "strash; balance; resub -K 6; rewrite; resub -K 6 -N 2; refactor; resub -K 8; balance; resub -K 8 -N 2; rewrite; resub -K 10; rewrite -z; resub -K 10 -N 2; balance; resub -K 12; refactor -z; resub -K 12 -N 2; rewrite -z; balance; strash"
alias flow_agr "strash; agr"
alias flow_pa2 "strash; pa_place; pa_rs -K 8 -N 2; pa_rw; pa_rf; pa_rs -K 8 -N 2; pa_rw; pa_rf; strash"
flow_c; flow_agr; flow_agr; flow_r; flow_agr
write_aiger agr_flow.aig
```

For PA, reread the original input and run the same skeleton:

```text
read preprocessed.aig
strash
flow_c; flow_pa2; flow_pa2; flow_r; flow_pa2
write_aiger pa_flow.aig
```

Use the runner for CPU-budgeted ABC-C/ABC-mix. Their repetition counts depend on
measured slot CPU, not on a fixed count copied from another computer. The exact
executed native commands are saved alongside their results.

To replay previously selected work, including the archived practical study:

```sh
python3 examples/physical/reproduce_flow.py \
  --abc build/abc \
  --inputs /path/to/paper/inputs \
  --liberty build/merged_asap7_final.lib \
  --paper-inputs \
  --replay-recipes examples/physical/reference_flow_recipes.json \
  --output results/practical-fixed-work
```

Use a previous run's `recipes.json` in place of the included reference file to
replay that run. Fixed-work replay preserves the declared macro sequence; it
makes no new equal-CPU guarantee. New matching uses measured CPU rather than
reusing historical targets. The archived study used a separate process per
macro and older binaries; exact old PPA/timing reproduction additionally requires
those archived tools. This runner measures the current integrated build.

## Interpreting frontend HPWL

Mapped HPWL is a **frontend placement proxy**, not routed wirelength or a
fixed-terminal physical result. `pa_place` places the mapped cells and sums
bounding-box wirelength using one coordinate per internal cell. It uses
Liberty cell areas for density/footprint modeling, without LEF pin offsets,
routing layers, obstacles, or routed parasitics. The canvas follows the same
area/utilization rule for each endpoint; it is not a common fixed-size core.

I/O connectivity is retained but explicit PI/PO terminal coordinates are
eliminated. On a PI-driven net, the box spans the internal sinks; the PI endpoint
adds no distance. PO endpoints add no driver-to-terminal distance. Thus a PI
with only one sink and a cell driving only a PO contribute zero terminal wire
cost. This is the freely located I/O model, not fixed boundary pins or an I/O
placer that assigns package locations. Shared PI nets still constrain the
relative positions of their internal sinks. See `BuildNetlist`, `CollectNetPins`,
and `Hpwl` in `src/ext-pa/paPlace.cpp`.

The proxy is useful for consistent frontend comparisons and fast iteration.
Final physical claims require a backend with common core/pin constraints and
routing. Cell delay from `stime` also excludes routed interconnect delay.
These scripts do not invoke OpenROAD.

## Completed historical practical-flow evidence

The archived primary study has all 20 designs and four flows. Positive values
below are paired geometric-mean reductions achieved by AGR:

| Reference | Mapped HPWL | Mapped area | Cell delay |
|---|---:|---:|---:|
| PA slots | 3.79% | 1.58% | 1.42% |
| ABC-C slots | 6.45% | 3.07% | 0.80% |
| ABC-mix slots | 6.64% | 1.43% | 0.12% |

| Flow | Process CPU mean / geomean (s) |
|---|---:|
| AGR | 9.55 / 3.35 |
| PA slots | 9.90 / 3.28 |
| ABC-C slots | 11.51 / 2.95 |
| ABC-mix slots | 12.24 / 3.73 |

AGR mapped HPWL improves/ties/regresses on 10/2/8 designs versus PA,
14/2/4 versus ABC-C, and 12/3/5 versus ABC-mix. Its process CPU geomean is
higher than PA and ABC-C despite the lower arithmetic mean. No design is
removed from the aggregate. Timing is one complete serial observation per
flow/design on the original machine; it is not a variability estimate.

[reference_flow_results.json](reference_flow_results.json) preserves all 80
frontend rows, fixed recipes, archived binary/input hashes, serial CPU values,
and source-equivalence status. All 80 archived source endpoints passed CEC;
those proofs do not substitute for checking new-build outputs. These historical
flow measurements are separate from the newly regenerated single-invocation
results in `reference_results.json`. The included current-build runner must be
used to obtain updated flow comparisons; no historical number is labelled as a
new-build result.

The current runner was checked on `ctrl` and `router`: all eight endpoints and
16 source/mapping CEC checks completed. Fixed-work replay and failure-safe
four-flow aggregation are covered by the accompanying checks:

```sh
python3 test/physical/reproduction_test.py
python3 test/physical/flow_reproduction_test.py
```
