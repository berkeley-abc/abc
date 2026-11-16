# Integration validation

Base: upstream ABC `0aabbb13f4a10cd8dc9c96ae3c743ec8fc3045a7`.
The integration was checked on macOS arm64 with Apple Clang. The AGR naming
migration was rebuilt using CMake Release and the normal Make build
(`-O -g`, assertions enabled), with Readline disabled. The separate local
ABC checkout was also rebuilt with byte-identical AGR sources.

| Check | Result |
|---|---:|
| Final compact AGR, step 0.28, retained EPFL endpoints | 20/20 identical AIG payloads |
| Two-round PA recipe, step 0.28, retained EPFL endpoints | 20/20 identical AIG payloads |
| AGR step sensitivity, 0.26 and 0.30 | 12/12 identical AIG payloads |
| Direct endpoint CEC, eight designs per flow | 16/16 equivalent |
| Integration regression script, Release build | 37/37 passed |
| Integration regression script, assertion-enabled Make build | 37/37 passed |
| Main local checkout: endpoint reproduction | 52/52 identical AIG payloads |
| Main local checkout: integration regression | 37/37 passed |
| Audit/profile-enabled AGR compilation | 9 units, both CMake targets passed |
| Ordinary ABC synthesis versus unmodified upstream | Identical AIG payload |
| Retained PA regression | 30 CEC, 24 edge, 20 input/state cases passed |
| PA private AIG manager and copied helpers | Layout and seven helpers match upstream |

The 20-design endpoint checks include `hyp`. The sensitivity checks use the same
six designs at both steps: `ctrl`, `int2float`, `log2`, `router`, `sqrt`, and
`voter`. Direct CEC covers `adder`, `ctrl`, `int2float`, `log2`, `router`, `sin`,
`sqrt`, and `voter` for each flow. The remaining endpoints were checked for exact
payload reproduction, not independently re-proved in this cleanup pass.

`test/physical/endpoint_manifest.json` records the input, library, and canonical
endpoint hashes. A payload comparison includes the AIGER header, outputs,
and AND encoding, while excluding symbol/comment trailers. AGR includes the
paper flow's final `strash`; applying another `strash` can change serialization
order and is not the endpoint recipe used here. The PA recipe includes its
explicit final normalization. The maintained PA timing-dependency fixes were
retained and still reproduce all 20 saved PA endpoints.

The regression script exercises the `agr` command and its legacy `tg` alias,
including exact alias payload identity, repeated calls, rereading networks, undo,
AGR-to-native and AGR/PA handoffs, immediate mapping, mapped PA placement transfer,
cluster-aware PA rewriting/refactoring, invalid arguments, and CEC of each
successful endpoint. It requires only Python's standard library and ABC's
included demonstration Liberty file.

These integration checks validate source cleanup, functional handoff, and
reproduction of the retained AIGs. Build/test timings are not performance
measurements. The separately measured frontend reference below uses the newer
upstream mapper. Historical PPA reproduction additionally requires the archived
mapping/backend versions and physical setup; OpenROAD was not rerun.

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

`reference_results.json` and `reference_cycles.json` in this directory retain
the measurements and replay counts. The runner's four unit checks pass,
including CPU-clock units and failure-safe aggregation. Two-design smoke and
fixed-cycle replays produced six identical endpoints and passed all 12 CEC
checks in each run; resuming reused those saved records. The all-design
geomeans and per-design budget compliance were independently checked.

No synthesis algorithm or physical-backend result was changed for this
reproduction work. See `REPRODUCE.md` for commands and exact timing boundaries.

## AGR naming migration

All 33 extension files have the same algorithm tokens as the retained TG
version after prefix substitution. The only executable addition is the legacy
`tg` alias, which calls the same handler as `agr`. Header guards, symbols,
source filenames, compile-time diagnostics, log prefixes, recipes, and tests
use AGR. Tension remains the name of the residual-conflict metric.

The 23 maintained PA source files are unchanged. All 52 canonical endpoint
hashes were rechecked after the rename; previous direct CEC proofs remain
applicable to those identical AIG payloads. The regression suite reruns CEC
on its generated endpoint cases. Historical validation/source snapshots retain
their original identifiers rather than being relabelled as new experiments.
