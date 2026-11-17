# Physical results of bounded AGR choices

The frozen command is `agr -c -b -r -m -W 0.25 -H 3 -T 300`, from
`d04b3c72fffe5f999320e41323aecfe46a8fba50`, at guidance step 0.28.
All arms receive common `dc2` followed by `&fraig -C 10000` and the exact
PR611 ASAP7 library. These are single-invocation endpoints with additional
search. This is not a new Table II slot-replacement experiment.

**Coverage: 99/99 verified physical runs.**
The design cohort has 20 EPFL circuits for the three published references
and 19 for the external conventional portfolio, which has no `hyp` endpoint.
The native `hyp` choice stage times out and returns ordinary corrected AGR;
that verified endpoint remains in the 20-design physical comparison.

## Geometric-mean improvements

Positive percentages mean less cost: `100 * (1 - geometric_mean(native / reference))`.
Every row uses paired designs with all methods in that cohort completed.

| Reference | Designs | HPWL | Routed WL | Area | Delay | Power |
|---|---:|---:|---:|---:|---:|---:|
| Original PA2 | 20 | 8.27% | 8.87% | 14.23% | 11.90% | 20.75% |
| Original AGR | 20 | 6.57% | 7.19% | 11.19% | 10.72% | 16.67% |
| CPU-matched RS–RW–RF | 20 | 9.76% | 10.01% | 14.92% | 13.45% | 20.61% |
| External conventional portfolio | 19 | 5.05% | 4.89% | 2.75% | -4.79% | 3.52% |

The full-20 point estimates meet the 5% target in all five metrics against
both original PA2 and the process-CPU-matched reference.
They also meet it against original AGR.
This is a geometric-mean target, not a per-design or confidence-bound guarantee.

## Design sensitivity

For native versus PA2, the paired-design bootstrap uses 5,000 samples and
seed 20261116. It measures sensitivity to the circuit cohort, not run-to-run
placement noise. Removing the two largest gains is performed separately
for each metric. Full statistics for every reference are in `summary.json`.

| Metric | Geomean | Median design | Without best two | Paired 95% interval | Improved / total |
|---|---:|---:|---:|---:|---:|
| Final HPWL | 8.27% | 5.98% | 6.93% | [5.06%, 11.45%] | 17/20 |
| Routed wirelength | 8.87% | 5.21% | 6.37% | [4.48%, 13.62%] | 15/20 |
| Final area | 14.23% | 6.69% | 9.48% | [7.03%, 22.17%] | 18/20 |
| Final delay | 11.90% | 3.41% | 3.87% | [2.06%, 23.21%] | 15/20 |
| Default-activity power | 20.75% | 6.13% | 10.83% | [6.21%, 35.11%] | 13/20 |

Selected per-design changes versus PA2:

| Design | HPWL | Routed WL | Area | Delay | Power |
|---|---:|---:|---:|---:|---:|
| adder | 12.56% | 12.89% | 16.02% | -28.94% | 14.86% |
| max | 1.59% | 1.16% | -1.53% | -4.29% | -1.33% |
| square | 11.60% | 8.80% | 2.24% | -4.27% | -1.81% |
| hyp | 0.70% | -0.99% | 0.21% | 2.69% | -4.05% |

The wire guard compares an ABC placement estimate with ordinary corrected
AGR, not PA2, and cannot guarantee a routed improvement. In particular,
the adder timing regression remains visible. There is no same-build
guard-disabled routed ablation here, so these numbers do not isolate the
guard’s causal contribution.

## References, attribution and paper comparison

The CPU reference receives each design’s full native process-CPU allowance
and stops at a complete RS–RW–RF cycle, without endpoint-quality selection.
Across 20 designs, native synthesis uses 1112.67 process-CPU seconds, versus
101.97 for original AGR and 99.22 for PA2; the matched reference uses 1116.86.
Its loop converges. Matching CPU time does not match structural diversity.
The external conventional endpoint comes from the earlier equal external
recipe-bank experiment with compress2rs substituted for AGR. It supplies
a stronger conventional comparison, but its bank and selector differ from
the native command. Native-versus-control differences do not isolate AGR
or geometric guidance. The complete pipeline gain must not be credited to
AGR alone; the control’s delay advantage is retained in the table.

The independent 24-circuit MCNC/ISCAS holdout remains a frontend result:
20.24% mapped-area and 14.77% cell-delay gains over original PA2, or
11.68% and 11.60% without t481. It has not been routed. See the separate
[frontend and holdout evidence](../followup-20261117/README.md).

The supplied `paper2.tex` reports Table I final HPWL/wirelength/area/delay/
power gains of 5.62%/5.92%/4.74%/4.54%/3.53% over budgeted ABC, and
HPWL/wirelength/area gains of 3.40%/3.28%/3.23% over PA2. Its Table II
final-HPWL gains are 2.32% over mixed ABC and 1.43% over PA slots.
The new results use extra search, common redundancy removal, and a declared
backend protocol change. They are not a reproduction of those numerical
tables or evidence for a 5% gain within the original Table II flow.
`summary.json` also compares rerun original AGR with PA2 and budgeted ABC
under this same backend, separating that baseline from the native pipeline.

## Common backend and validation

Every arm goes through the pinned ORFS Yosys/ABC mapping stage and the same
OpenROAD flow. Die/core sizes and pins are generated once from the common
input. Density is 0.60, reference utilization 0.50 (0.40 for dec), and
OpenROAD port buffering is disabled. Actual utilization varies with area.
Yosys constant-output buffers remain in every arm. Tool/library hashes
and exact physical controls are recorded in `protocol.json` and
[the shared backend package](../followup-20261117/backend/README.md).

The target uses all-net final HPWL including physical terminals, detailed
routed wirelength, final cell area, delay with parasitics, and default-activity
power. Core-only HPWL is a separate diagnostic. Power has no workload VCD.
There is one physical run per frozen endpoint, with no selection using
OpenROAD results. All runs are confined to a shared pool of 12 cores.

A successful result requires source-to-endpoint, endpoint-to-actual-mapped
function, and mapped-to-final-netlist CEC; a fixed-boundary audit; and zero
final DRC errors and unrouted nets. Proof records link by content hashes.
They retain successful CEC output, not standalone SAT certificates.

The original AGR sqrt mapping check reached the 600-second GIA proof
timeout. Classical CEC then proved the exact same source and mapped graph.
Routing resumed from the existing floorplan; no synthesis endpoint, physical
setting, or routed result was selected by this recovery. The failed attempt
and successful alternate-engine proof remain in the external archive.

The initial setup attempt stopped at mapping validation because a copied
package lacked its sibling Liberty gzip. Packaging was repaired and the
campaign restarted in a new directory, with unchanged physical settings.

## Runtime and recomputation

`summary.json` records stage wall time and reserved core-seconds per method.
The machine is an AMD Ryzen AI Max+ 395 shared workstation, with jobs pinned
to 12 logical CPUs spanning 12 distinct physical cores. This is not an
exclusive-machine runtime benchmark.
Reserved core-seconds are a scheduling cost, not measured process CPU.
Flow-stage times exclude separate CEC; wrapper times include it. The sqrt
recovery wrapper time also includes waiting for its reserved cores.

```sh
python3 examples/physical/choices/analyze_followup.py --check
python3 examples/physical/choices/analyze_routed.py --check
```

These commands audit the committed records and recompute paired statistics;
they do not rerun synthesis, routing or CEC. Full endpoint files, databases
and execution logs remain in the research archive. The data bundle contains
each expected endpoint; missing or failed proofs/runs are coverage failures
and are never assigned a fictitious zero gain.
