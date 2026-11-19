# Validation and reference results

Upstream base: `0aabbb13f4a10cd8dc9c96ae3c743ec8fc3045a7`.
Local correctness checks use macOS arm64 and Apple Clang; upstream CI covers
Linux and macOS Make/CMake builds, with and without ABC namespaces, and MSVC.

```sh
python3 test/physical/regression.py --abc build/abc
python3 src/ext-pa/tests/regression.py --abc build/abc --lib demo.lib
python3 test/physical/reproduction_test.py
python3 test/physical/flow_reproduction_test.py
```

The integration suite has 34 checks, or 37 with `--reference /path/to/upstream/abc`.
It covers equivalence, repeated use, command errors, native-command handoffs,
and mapped-cluster transfer. The two reproduction suites contain eight checks.
The PA suite covers equivalence, timing dependencies, edge cases and state errors.

`test/physical/endpoint_manifest.json` records input/library hashes and 52
canonical endpoints: 20 AGR, 20 PA, and six designs at each sensitivity step
0.26 and 0.30. A canonical payload includes the AIGER header, outputs and AND
encoding, excluding symbol/comment trailers. Exact payload replay is distinct
from a new equivalence proof. Do not add another `strash` after AGR when checking
serialization identity.

The cleanup replay preserves all 60 standalone optimized and mapped payloads
and all six reported QoR metrics across 20 designs. The practical-flow smoke
replays eight endpoints on `ctrl`/`router`, with source and mapping CEC.
Fixed-work correctness replays do not establish new CPU-matched performance.

## Backend setup validation

The [OpenROAD package](openroad/README.md) was checked against all 20 archived
design configurations in both the single-block and practical-flow cohorts:
SDC, die/core, pin commands/order, density, corner, and resource limits match.
The mapping override retains the historical executable Tcl commands.
A `ctrl` dry-run and one-pass mapping/initial-floorplan smoke check passed,
including mapped-netlist CEC. Reading saved global/final databases reproduced
their HPWL exactly and verified the frozen pin rectangles and die/core.
No global-placement or routing experiment was rerun for this validation.

The public source revisions and build patch were verified; validation used the
archived tool binaries. A fresh Docker source build was not repeated. Binary
hashes from the historical build are reference provenance, not a promise of
bit-identical recompilation with different system dependencies.

## New-build frontend reference

The serial default-step campaign completed all 60 metric endpoints: 20 designs
each for AGR, PA2 and CPU-budgeted native ABC. All 40 AGR/PA2 payloads match the
retained manifest, including `hyp`. Native ABC met or exceeded the larger of the
AGR/PA2 synthesis CPU budgets on every design, with complete-cycle overshoot.
Hardware: Apple M3 Pro, 36 GiB memory; each ABC job ran serially.

Paired geometric-mean changes below use all 20 designs; negative favors AGR:

| AGR versus | AIG nodes | Levels | AIG HPWL | Mapped area | Cell delay | Mapped HPWL |
|---|---:|---:|---:|---:|---:|---:|
| PA2 | -2.59% | -2.71% | -4.87% | -5.22% | -0.03% | -6.50% |
| CPU-budgeted ABC | -3.13% | -6.15% | -8.89% | -6.41% | -5.25% | -10.33% |

| Flow | Synthesis CPU mean / geomean (s) | Process CPU mean / geomean (s) |
|---|---:|---:|
| AGR | 2.5283 / 0.6140 | 2.7174 / 1.0283 |
| PA2 | 2.8278 / 0.6000 | 3.0076 / 1.0385 |
| CPU-budgeted ABC | 3.0066 / 0.6883 | 3.1853 / 1.1056 |

AGR's synthesis-CPU geometric mean is slightly higher than PA2's. Mapped HPWL
regresses on nine designs versus PA2 and five versus native ABC; the reference
JSON lists every regression. No design or failed proof is removed to improve
the aggregate.

Of 120 requested source/output and mapping CEC checks, 114 passed. All six
`hyp` checks reached their limits and remain **unproved**; no counterexample
was reported. Thus the complete measured cohort is 20 designs, while the
cohort with both new CEC proofs for all three flows is 19. Exact retained
payload identity is additional evidence for AGR/PA2 on `hyp`, not a newly
completed proof of the native or mapped endpoints.

The complete per-design values, proof outcomes and fixed-work recipes are in
`reference_results.json` and `reference_cycles.json`. Practical-flow records
and their historical binary provenance are documented in [FLOW.md](FLOW.md).
See [REPRODUCE.md](REPRODUCE.md) for commands, input requirements and timing
boundaries. These frontend checks do not reproduce routed physical results.
