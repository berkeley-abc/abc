# AGR choices and mapped-cost selection

`agr -c -b -r -m -W 0.25` retains alternatives that ordinary AGR discards,
combines them as structural choices, and selects an equivalent plain AIG using
mapped area and cell delay. It requires a loaded Liberty library. The ordinary
`agr` command remains available; this branch also fixes its incremental timing
propagation, unconstrained-slack handling, deletion-cone accounting, and placement
coordinates at the canvas boundary.

This extension builds on PR #611 at
`267220beeac61151c306b27c81ced1a3bd8a01bf`. It adds a synthesis portfolio and
internal mapping effort. The complete gain is not an isolated measurement of
AGR's geometric search policy.

## Operation

- `-c` retains whole-pass checkpoints from one AGR invocation.
- `-b` adds area/LUT/DSD/SOP balancing and bounded LUT MFS/FX alternatives on
  the common input and the ordinary AGR endpoint.
- `-r` adds one and two `compress2rs` cycles on the input, and one cycle after
  each MFS/FX alternative.
- `-m` merges equivalent structures with DCH. The legacy FRAIG engine remains
  available without this option.
- `-W 0.25` minimizes `mapped_area * cell_delay^0.25`. With the default `-D 0`,
  both costs must be no worse than the ordinary corrected-AGR endpoint.
- `-H 3` additionally rejects a candidate whose mapped HPWL exceeds the
  ordinary AGR endpoint's by more than 3%. The grid is chosen from the mapped
  common input once and reused; placement uses the command's `-s` step.
- `-T 300` budgets 300 seconds for the choice stage after ordinary AGR. On
  expiry it returns that ordinary endpoint, discarding partial search results.
  A positive budget requires `-c -m`; zero leaves the stage unlimited.

The bounded followup configuration is `agr -c -b -r -m -W 0.25 -H 3 -T 300`.
Both new controls are optional and disabled by default. The HPWL guard uses a
private ABC placement, without changing the caller's placement state. Its
canvas scales with mapped area; it is not a guarantee about routed wirelength
on a fixed die. The deadline is cooperative: it is checked between transforms,
mapping calls, placement stages, and DCH SAT queries. A running primitive can
overshoot the allowance. The elapsed-time measurements here are from Linux.

The choice mapper explores six fixed NF relaxation settings
(0, 5, 10, 20, 40, 100), independently and as a sequential shaping chain.
Every cover is strashed and evaluated by the common plain-AIG NF mapper and
Liberty timing engine. Selection uses no physical-flow measurements. The final
network preserves the caller's port names/order; the user's `&`-space, saved AIG,
and `fraig_store` are preserved. Rejected individual local edits are not retained.
See [the command notes](../../../test/physical/CHOICES.txt) for the optional
`-D`, `-C`, and `-f` cost/quality controls.

## Recorded ABC results before the bounded followup

The tables in this section are the archived, unguarded results at `32e58a47b`.
They predate `-H`, `-T`, and the two placement-consistency fixes. They remain
unchanged so that improvements to the implementation do not silently change
the version associated with a numerical claim.

The [bounded followup](followup-20261117/) records the current implementation on
all 20 EPFL designs, the independent 24-design holdout, and the backend mapping
check. It also reports the updated tradeoffs and the stronger conventional
comparison. The [physical followup](routed-20261117/) contains 99 verified
OpenROAD runs, including all 20 designs for the published references and a
19-design external conventional comparison. Its all-20 geometric means exceed
5% in each of final HPWL, routed wirelength, area, delay and default-activity
power against PA2, CPU-matched ABC and original AGR. The conventional portfolio
retains a delay advantage. The original tables below remain historical evidence.

The primary experiment uses one fixed command and guidance step 0.28 on 19 EPFL
combinational designs. Every method receives the same confirmed `dc2` input,
then common `&fraig -C 10000` preprocessing. The library is the unmodified
[PR611 ASAP7 library](../data/merged_asap7_final.lib.gz). Fresh mapped HPWL uses
one bin count per design, derived from the common input and held fixed across
methods, at measurement step 0.28 and utilization 0.70.

Positive values below are `100 * (1 - geometric_mean(candidate / reference))`.

| Reference | Mapped HPWL | Mapped area | Cell delay |
|---|---:|---:|---:|
| Original PA2 | 11.26% | 16.61% | 21.13% |
| Original PR AGR | 7.34% | 13.01% | 20.78% |
| CPU-matched published RS–RW–RF | 11.61% | 17.30% | 24.86% |
| CPU-matched compress2rs | 6.83% | 12.47% | 19.59% |
| PA2 with timing fixes | 10.09% | 15.89% | 20.22% |
| AGR with timing fixes | 3.27% | 11.87% | 20.59% |

The native command takes 971.97 seconds total process CPU across these designs
(median 3.90 seconds, maximum 265.87 seconds), including its final mapping and
excluding equivalence checks. Ordinary AGR takes 56.23 seconds and PA2 47.53
seconds under the same accounting. Each CPU-budgeted reference receives the
native command's complete process allowance, stops at a complete macro boundary,
and receives additional time for final mapping. Matching CPU time does not give
a repeated script the same search diversity as the new command.

Versus PA2, median area/delay improvements are 9.58%/7.79%; removing the best two
designs separately for each metric leaves 11.19%/13.72%. Paired-design 95%
bootstrap intervals are [9.16%, 24.99%] and [8.53%, 33.25%]. Without `div`, area
and delay improve 16.92%/21.89%. Area improves on 18 designs and ties on one;
delay improves on 15, ties on one, and regresses on `adder` (33.69%), `bar`
(4.12%), and `int2float` (0.37%). These are aggregate improvements, not a
per-design guarantee.

Across guidance steps 0.26–0.30, the average HPWL/area/delay improvements versus
PA2 are 9.99%/15.67%/20.71%. Versus original AGR, they are
5.21%/12.15%/20.68%; its per-step HPWL improvement ranges from 1.37% to 7.47%.
Settings are averaged within each design before bootstrapping designs.

Inside the paper's `C-S-S-R-S` flow, replacing all three slots gives
6.41%/14.10%/25.66% HPWL/area/delay improvements over PA2 slots, and
3.02%/12.50%/23.17% over original AGR slots. These flow comparisons use more
search effort and do not yet have a new matched-CPU flow reference.

The equal external recipe-bank control gives AGR, PA2, and compress2rs the same
16 valid recipe positions, choice groups, and selector. Relative to plain PA2,
their area/delay gains are 13.22%/17.20%, 12.10%/17.42%, and 13.15%/18.37%.
The new native command improves 3.99%/3.38% over the conventional bank. Its bank
and selector differ, so this difference does not isolate an AGR-specific effect.

## Scope and limitations

The archived tables are frontend measurements. Mapped HPWL uses an area-scaled
ABC canvas; cell delay excludes routed parasitics. They do not establish the
five-metric routed target. The followup uses the bounded command and a separately
recorded backend campaign; do not combine its results with these older endpoints.

The archived cohort is a development set, not a holdout. `hyp` exceeded 1800 seconds in
a separate full-native choice-merge trial on the earlier `dc2 + &fraig -C 1000`
input; it is not in the 19-design aggregates. These experiments are not an
all-20 reproduction of the paper: common redundancy removal, search effort, and
the cohort differ. Uniform `&fraig -C 10000` removes the large residual `div`
redundancy for all methods before the comparison. An older limit of 1000 did not.

The failed external-MFS `square` candidate remains in the historical records.
The current implementation fixes its cause: actual deletion can extend beyond
the cut-bounded MFFC when a replacement stops using a cut leaf. The planner now
simulates ABC's recursive reference decrements, including newly created and
redirected references. A separate `sqrt` failure came from scoring an unclipped
reused coordinate which commit later clipped to the canvas. Scoring and commit
now use the same coordinates. Neither fix relaxes the consistency checks.

The original failing `sqrt` flow also passes with only the coordinate correction
applied to PR611. A build with `ABC_AGR_ENABLE_AUDIT` passes exact HPWL and density
checks after every local edit for both reproductions at steps 0.26–0.30. See
[`placement_consistency.py`](../../../test/physical/placement_consistency.py).
An early prototype also discarded FX's plain-AIG result; the implementation
handles it correctly and tests parity with public ABC commands.

## Data and verification

[results-20261117](results-20261117/) contains 665 observations: 133 primary,
380 sensitivity, 95 practical-flow, and 57 selected portfolio endpoints. Some
observations reuse identical, previously proved endpoints; these are not 665
independent synthesis trials. Every row links to successful source and mapping
CEC records by input/output hashes. The 19 common inputs also have CEC records.
The committed outputs and hashes are evidence records, not standalone SAT
certificates. Benchmark/netlist files and complete experiment logs remain in the
research archive; benchmark inputs remain external as in PR611.

The source includes the three timing-cache regression cases. They fail on the
original implementation and pass after the fixes. The rebuilt implementation
passes 34 existing integration checks, 44 choice checks, and five deletion-cone
checks against the actual ABC mutator. Coverage includes cost and HPWL guards,
deadline fallback, port preservation, caller-state preservation, and MFS/FX cost
parity. The ten benchmark placement-consistency cases are additional checks.

Recompute the statistics and audit the recorded evidence with Python's standard
library; this requires neither ABC nor OpenROAD:

```sh
python3 examples/physical/choices/analyze.py --check
```

The [protocol](results-20261117/protocol.json) records recipes, file/binary
hashes, the fixed bin-count rule, CPU policy, and bootstrap settings. The
[summary](results-20261117/summary.json) includes medians, leave-two-out and
paired bootstrap intervals beside every geomean, plus summed HPWL reductions.

Numerical endpoints were generated at `32e58a47b`. Commit `561a76fb5` changes
only profiling counters to process CPU time. The original internal `cpu_seconds`
diagnostic used `Abc_Clock()`, which is wall time on this Linux build; native
process CPU was measured externally throughout. Both reference campaigns were
rerun with the corrected [process-CPU harness](cpu_budget.cpp), and their OS
user+system times were cross-checked against the promised allowance. Superseded
wall-clock-budgeted runs are not included in this result bundle.

## Reproducing endpoints

Build this branch and the original PR611 revision separately using the same
Release settings; see [REPRODUCE.md](../REPRODUCE.md). Use at most 12 build/run
workers. Extract the exact library as described there. For each raw EPFL input,
use the **original PR611 binary** to prepare a common input once:

```text
read raw_design.aig; strash; dc2; write_aiger dc2.aig
read dc2.aig; strash; &get; &fraig -C 10000; &put; strash
write_aiger common.aig
```

If starting from a saved `dc2` input, omit the additional `dc2`. Input hashes in
`results-20261117/inputs.json` identify this campaign's files; they need not match
the unavailable authors' research archive. The stronger common input is used
for every method. Run this branch's command after loading the library:

```text
read common.aig; strash; read_lib merged_asap7_final.lib
agr -c -b -r -m -W 0.25
write_aiger optimized.aig
&get; &nf; &put; stime
```

To reproduce the bounded followup instead, use the current implementation and
append `-H 3 -T 300`. Record timeouts explicitly and retain their plain endpoints
in the aggregate. In particular, do not silently drop `hyp` when it times out.

The original AGR/PA2 references use the original PR611 binary and the exact
commands in `protocol.json`. Corrected AGR uses this branch without choice
flags. The optional corrected-PA2 control applies
[corrected-pa-control.patch](corrected-pa-control.patch) to a separate PR611
checkout; that patch is evidence for the control, not a change to PA in this PR.
Every saved endpoint is measured by the original PR611 mapper and library.
Verify source-to-endpoint and endpoint-to-mapped-function equivalence, and
reject failed/unknown proofs.

The process-CPU reference harness links against the original PR611 `libabc.a`.
For a 64-bit Linux build, using the same compiler definitions as that ABC build:

```sh
c++ -O3 -DNDEBUG -std=c++17 -DLIN64 -DSIZEOF_VOID_P=8 \
  -DSIZEOF_LONG=8 -DSIZEOF_INT=4 -I/path/to/pr611/src \
  examples/physical/choices/cpu_budget.cpp /path/to/pr611/libabc.a \
  -lpthread -lm -ldl -lrt -o /tmp/abc-choice-budget
```

Its five arguments are bootstrap commands, one complete macro, CPU seconds,
finish/mapping commands, and the command saving the first-cycle endpoint. The
CSV files record both the CPU allowance and realized cycle count. Cycle replay
can reproduce fixed work; CPU-based stopping can differ on another machine.
The harness includes initialization in the allowance and runs final mapping
after it. Clear user ABC startup overrides and use one numerical thread per run.
