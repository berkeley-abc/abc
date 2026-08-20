# ForMACE Change Log

This file records ForMACE-specific changes made in this ABC fork.

## 2026-08-20

- Added paper-derived disjoint-MCS bootstrapping and certified packing lower
  bounds to the shared minimum-UNSAT engine, plus inclusion-subsumption of
  learned correction sets.
- Added combined-OR MSS growth and bounded greedy/direct/WalkSAT-style
  lower-bound candidate repair for `runeco -g`; all heuristic candidates must
  hit every learned correction and pass every target SAT oracle. Reduced maps
  are now constructed lazily only when those candidates cannot be found.
- Reduced exact Unit14 `runeco -g` runtime from 229.18s to 76.49s while
  retaining the exact seven-input result, evolving-target sufficiency, final
  miter proof, and CEC. On grouped k=11 inputs, `msmie.3.prop1-func-interl`
  improved from 93.20s to 62.56s CPU and `mcs.3.prop1-back-serstep` from
  313.22s to 39.63s CPU with unchanged exact minima.

- Added `runeco -g` for exact minimum-cardinality support shared across a
  fixed family of multi-target two-copy ECO relations. The multi-oracle
  implementation is equivalent to `(B_0 OR ... OR B_(k-1)) AND Eq_S` without
  constructing one large selector CNF.
- Added `Fm_CamusFindMinimumCommonMus()`: each SAT candidate is grown to an
  MSS, its complementary MCS is learned by one shared hitting-set map, and all
  still-SAT target managers contribute corrections in a batch.
- Added exact dynamic map reduction by learned-MCS incidence equivalence and
  dominance. The quotient is rebuilt after every correction, preserving the
  full candidate universe while reducing current map symmetry.
- Added evolving-target sufficiency checks, final patched-miter verification,
  independent CEC coverage, mutually exclusive `-a`/`-m`/`-g` parsing, and a
  two-target regression with an exact two-of-three shared support.
- Documented the guarantee boundary: `-g` is globally minimum for the recorded
  fixed target relations, not over all possible joint patch-function choices.

## 2026-08-19

- Added the extension-owned `fm_eco` command for DAC'18 ECO patch construction
  with Craig interpolation.
- Made support selection orthogonal to function construction: `fm_eco` uses
  ABC's original support heuristic by default and exact grouped MinUNSAT with
  `-m`, completing the original/minimum x SOP/ITP four-method matrix.
- Reused the existing Acb windowing, miter, reverse target loop, support
  selectors, output generation, and CEC instead of creating a second ECO
  implementation.
- Added constant-partition handling, selector-free proof construction with
  only chosen divisor variables shared, internal patched-miter checking, and
  useful command failure status.
- Added `fm_eco_test.sh` for original- and minimum-support interpolants and
  retained the exhaustive real-encoding support audit under `-m -w`.
- Added the resumable `try/tools/0819_ECO_Simple/run_eco_2017.py` experiment
  runner. All four methods pass internal and independent CEC on ICCAD'17
  `unit1` and `unit2`.
- Made exact CAMUS hitting-set search incremental: one reusable map solver and
  sequential counter now receive new MCS clauses incrementally, while the
  proven hitting-set lower bound is retained across refinements.
- Added `runeco -v`/`fm_eco -v` CAMUS phase and search counters. On ICCAD'17
  `unit9`, the incremental map reduced `sop_minimum` wall time from 126.35s to
  44.72s and 44.44s in two runs while preserving the exact eight-input result
  and both equivalence checks.
- Changed the production guarded-formula CaDiCaL configuration to enable
  preprocessing and normal phase switching while retaining `ilb=2`. The
  tuning matrix was faster in seven of eight cases (0.32x geometric-mean wall
  time) with identical exact minima. Added `cadical-plain-stable` to preserve
  the former production configuration as an explicit ablation.
- Added `runeco -a` and `fm_eco -a` assumption-only support ablations. They
  retain `sat_solver_minimize_assumptions()` while skipping `Acb_FindSupport()`,
  extending the ECO runner to a six-method matrix with aggregate Markdown,
  CSV, and JSON tables for all selected ICCAD'17 cases.

## 2026-08-18

- Added the production `fm_minunsat` ABC command for exact clause-level
  minimum UNSAT directly from DIMACS CNF, without an AIG conversion.
- Added optional group-file input with a hard/background first group,
  multi-clause unit-cost optional groups, strict clause-assignment validation,
  resource limits, raw-core/all-candidate seed choices, and phase statistics.
- Exposed every exact ablation configuration through `fm_minunsat -A` and
  added `-j` machine-readable output so experiments invoke the production ABC
  executable rather than compiling a private benchmark driver.
- Added independent CaDiCaL `plain`, `ilb=2`, and `stabilizeonly=1` switches
  plus all three pairwise configurations, enabling a separate complete `2^3`
  solver-tuning matrix without changing the original ablation variants.
- Added command-level regressions for clause-level minimum, raw-core seeding,
  grouped hard clauses, hard-only UNSAT, SAT input, and multiline DIMACS.
- Added runtime-configurable, exact minimum-UNSAT ablations for failed-core
  shrinking, MUS upper-bound seeding, model-guided MSS growth, MCS growth,
  map-bound search, and CaDiCaL tuning. Production defaults are unchanged.
- Added a raw-core seed variant that uses the first failed-assumption core as
  a valid upper bound without paying for deletion minimization.
- Added per-phase minimum-UNSAT counters/timers and extended the independent
  exhaustive oracle to cover all seven production/ablation configurations.
- Kept the extension tree focused on C sources, user guides, regression
  tests, and fixtures by moving the MinUNSAT ECO runner and results to the
  workspace's `try/tools` and `try/results` areas.
- Added `tests/run_all.sh` as the single entry point for the complete focused
  regression suite.
- Added extension-local Git exceptions so the small Verilog and BLIF fixtures
  required by the smoke tests are present in a clean checkout.

## 2026-08-11

- Audited `runeco -m` end to end. Confirmed that it minimizes the number of
  additional divisor-equality groups for the current target, conditional on
  accumulated support; it is not a global multi-target support optimizer.
- Added an independent exhaustive Boolean oracle covering 512 deterministic
  random grouped CNFs with sparse/non-contiguous candidate vectors. The oracle
  uses neither CaDiCaL nor `Fm_CamusSolve()` and agrees with
  `Fm_CamusFindMinimumMus()` on every case.
- Extended `runeco -m -w` with an exhaustive real-encoding audit for iterations
  containing at most 16 remaining candidates. It verifies the returned set is
  UNSAT and that every smaller candidate subset is SAT.
- Added `fm_runeco_minimum_test.sh` and a self-contained single-target ECO
  fixture. The exact selector returns two of seven candidates, the audit proves
  all eight smaller subsets SAT, the generated patch passes internal checking,
  and an independent CEC also passes.
- Consolidated the extension documentation into one entry-point README,
  focused `fm_inter`, `fm_int`, and CAMUS guides, this changelog, and one ECO
  experiment report.
- Removed completed implementation plans and overlapping design notes after
  preserving their current operational and architectural content in the
  focused guides.

## 2026-08-06

- Added an explicit fixed-partition experiment mode to `fm_int`: `-o` runs
  the original ABC interpolator, `-S k` starts at suffix depth `k`, and `-a`
  ORs the bad property over suffix states 1 through `k`.  Combining
  `-S k -F k+1` executes one query with
  `A=I(s0) and T0` and
  `B=T1..T(k-1) and Bad`, matching the external fixed-depth workflow.
- Extended verbose Hybrid reporting to include its baseline-support candidate
  count and expanded the smoke suite for baseline/fixed-partition operation.

## 2026-07-27

- Recreated the ForMACE extension setup in `abc_formace_ext`.
- Added project rules in `FORMACE_RULES.md`.
- Added this change log in `FORMACE_CHANGELOG.md`.
- Added experimental extension directory `src/extformace_ext/`.
- Added `src/extformace_ext/module.make` so ABC's Makefile can build the extension module.
- Added `src/extformace_ext/formace.c` with a self-registering `fm_summary` command.
- The extension registers through `Abc_FrameAddInitializer()` from inside `src/extformace_ext/formace.c`, avoiding direct edits to original ABC source files.
- Added `upstream` remote pointing to `https://github.com/berkeley-abc/abc.git`; kept `origin` as `git@github.com:elvis517/abc_formace_ext.git`.
- Set `upstream` push URL to `DISABLED` to avoid accidental pushes to Berkeley ABC.
- Built ABC successfully with `make -j4 ABC_USE_NO_READLINE=1`.
- Verified the extension command with `./abc -c "read i10.aig; fm_summary -v"`.
- Verified command usage with `./abc -c "fm_summary -h"`.
- Renamed the extension source directory from `src/extformace_ext/` to `src/formace_ext/` so it can be tracked and pushed without force-adding an upstream-ignored `src/ext*` path.
- Updated the top-level `Makefile` to include `src/formace_ext` in `MODULES`.
- Updated `src/formace_ext/module.make` to compile `src/formace_ext/formace.c`.
- Ran `make -j4 ABC_USE_NO_READLINE=1` after the rename; Make reported the existing `abc` binary was already up to date.
- Re-verified `./abc -c "read i10.aig; fm_summary -v"` after the rename.
- Re-verified `./abc -c "fm_summary -h"` after the rename.

## 2026-07-28

- Added `src/formace_ext/FM_BMC_INTERPOLATION_PLAN.md`, which records the
  design boundary for ForMACE interpolation-based model checking before code
  changes.
- Added the read-only `fm_int` command in `src/formace_ext/formace.c` with
  `-m` exact latch-boundary minvar mode and `-y` baseline-support hybrid mode.
  It uses ABC's existing interpolation BMC wrapper and leaves the current
  network unchanged.
- Added opt-in ForMACE parameters and a selected forward latch-connector path
  in `src/proof/int/int.h`, `src/proof/int/intInt.h`,
  `src/proof/int/intMan.c`, `src/proof/int/intCore.c`, and
  `src/proof/int/intM114.c`.  The upstream `int` command retains its existing
  all-latch behavior because the new parameters default to disabled.
- The selected connector path omits both equality clauses and proof-global
  variables for unselected latches, expands compact interpolants back to the
  complete latch interface, and handles a valid zero-latch boundary with a
  constant interpolant.
- Added `src/formace_ext/FM_BMC_INTERPOLATION.md`, three sequential BLIF
  fixtures, and `src/formace_ext/tests/fm_int_smoke.sh`.
- Built successfully with `make -j4 ABC_USE_NO_READLINE=1`.
- Verified upstream `int`, `fm_int -m`, and `fm_int -y` on the two-latch safe
  fixture; both ForMACE modes selected one latch boundary and proved it.
- Verified `fm_int -m` selects zero boundaries and proves the constant-safe
  fixture, reports a frame-1 counterexample on the unsafe fixture, and returns
  `Property UNDECIDED` when `-L` is below the required candidate count.
- Ran `bash src/formace_ext/tests/fm_int_smoke.sh` successfully.

- Added the ForMACE-owned `fm_inter` command in `src/formace_ext/formace.c`.
  The existing upstream `inter` command and its source files were not changed.
- Added `fm_inter -m` for exact minimum-cardinality selection of shared PI
  equality groups and `fm_inter -y` for the baseline-support hybrid search.
- Reused ABC's internal AIG/CNF/SAT proof interpolation path with an explicit
  selected shared-variable vector, while leaving unselected paired PIs private
  to their respective partitions.
- Added validation that inputs are combinational and single-output and that
  paired PIs agree by both order and name.
- Preserved the full onset PI interface in the output network so standard ABC
  `miter` verification works; unselected PIs are functionally unused and the
  command prints the actual selected and resulting support names.
- Added a safe root-clause-conflict fallback: when the onset support is already
  contained in the selected set, the onset is returned as a valid interpolant.
- Added the implementation plan `src/formace_ext/FM_INTERPOLATION_PLAN.md` and
  user manual `src/formace_ext/FM_INTERPOLATION.md`.
- Updated `src/minvar_ext.md` with the implemented first-integration status
  and the CAMUS follow-up boundary.
- Added reproducible BLIF fixtures and
  `src/formace_ext/tests/fm_inter_smoke.sh`. The test covers minvar, hybrid,
  selected-support reduction, ABC `miter`/`iprove` verification, and the
  root-conflict fallback.
- Built successfully with `make -j4 ABC_USE_NO_READLINE=1`.
- Ran `bash src/formace_ext/tests/fm_inter_smoke.sh` successfully.
- Ran `./abc -c "fm_inter -h"` successfully and verified that `-L 0` rejects
  the three-candidate smoke test without replacing the current network.
- Re-ran the unchanged upstream `inter` command on the smoke-test pair.

## 2026-08-01

- Added `src/formace_ext/FM_CAMUS_PLAN.md` before implementation.  It records
  the CAMUS integration boundary, the guarded-group contract, the staged
  implementation plan, and why the extension uses in-memory ABC APIs instead
  of DIMACS/process I/O or a vendored CAMUS executable.
- Added the ForMACE-owned guarded constraint-group API in
  `src/formace_ext/fm_camus.h` and `src/formace_ext/fm_camus.c`.  The API
  keeps a single ABC `sat_solver` in memory and finds one subset-minimal MUS
  by selector assumptions and deletion minimization.
- Updated `src/formace_ext/module.make` so the API is included in both `abc`
  and `libabc.a`; no upstream ABC source file was changed for this work.
- Added `src/formace_ext/tests/fm_camus_api_test.c` and
  `src/formace_ext/tests/fm_camus_api_test.sh`. The test compiles a separate
  executable against `libabc.a` and calls the API directly, without CNF files
  or a CAMUS process. It now distinguishes a subset-minimal MUS from a
  minimum-cardinality MUS.
- Added `src/formace_ext/FM_CAMUS.md`, documenting API ownership, semantics,
  test execution, and the next supported integration steps.
- Built successfully with `make -j4 ABC_USE_NO_READLINE=1 libabc.a`.
- Ran `bash src/formace_ext/tests/fm_camus_api_test.sh` successfully.
- Integrated the API into `fm_inter -c`.  This mode derives the paired A/B
  CNFs once, represents each PI equality pair as one guarded constraint group,
  and calls `Fm_CamusFindMus()` to select a subset-minimal interpolation
  boundary without rebuilding the SAT solver for each deletion trial.
- Kept `fm_inter -m` unchanged: it remains exact minimum-cardinality search,
  while `-c` explicitly means subset-minimal CAMUS-style selection.
- Extended `src/formace_ext/tests/fm_inter_smoke.sh` to test `fm_inter -c` and
  both standard interpolation obligations on the existing three-PI fixture.
- Built successfully with `make -j4 ABC_USE_NO_READLINE=1` and ran the updated
  `fm_inter` smoke test successfully.
- Added `Fm_CamusFindMinimumMus()`, which seeds an upper bound with one MUS
  and performs in-memory branch and bound over guarded PI groups.
- Replaced `fm_inter -m`'s prior repeated-CNF exhaustive subset search with
  the new CAMUS-style branch-and-bound minimum search.  `fm_inter -y` now uses
  the same search over its baseline-support candidates, so it is locally
  minimum unless it falls back to all PIs.  `fm_inter -c` remains the explicit
  subset-minimal (not necessarily minimum) MUS mode.
- Strengthened the direct API test with a five-group instance where deletion
  minimization returns the larger MUS `{2,3,4}`, while branch and bound proves
  and returns the minimum `{0,1}`.
- Added `src/formace_ext/FM_BMC_CAMUS_PLAN.md` before modifying the sequential
  interpolation path. It defines the fixed per-frame CNF background, guarded
  latch-equality groups, and the boundary/proof separation.
- Updated `src/proof/int/intM114.c` so each forward `fm_int` minvar or hybrid
  interpolation iteration builds one in-memory guarded CAMUS solver. `-m`
  uses branch and bound across all latch groups; `-y` uses it over baseline
  interpolant support and therefore obtains a local minimum for that support.
  ABC's existing proof solver is still used once for the selected result.
- Added `Fm_CamusSetLimits()` so CAMUS selection queries observe the existing
  `fm_int` conflict and wall-time limits.
- Updated `src/formace_ext/FM_BMC_INTERPOLATION.md`,
  `src/formace_ext/FM_BMC_INTERPOLATION_PLAN.md`, and
  `src/formace_ext/tests/fm_int_smoke.sh` to document and require the verbose
  CAMUS per-step minimum-selection messages.
- Built successfully with `make -j4 ABC_USE_NO_READLINE=1` and ran `fm_int`,
  `fm_inter`, and direct CAMUS API smoke tests successfully.

## 2026-08-05

- Replaced the `Fm_CamusMan_t` internal ABC `sat_solver` with the bundled
  CaDiCaL 2.2.0 `cadical_solver`. The public `Fm_Camus*` interface and all
  `fm_inter`/`fm_int` call sites remain compatible.
- Configured each CAMUS manager for the repeated assumption workload with
  CaDiCaL `plain`, `ilb=2`, and `stabilizeonly=1` settings.
- Added `Fm_CamusBackendName()` and made the direct API regression assert a
  `cadical-` backend signature.
- Integrated CaDiCaL failed-assumption cores into `Fm_CamusFindMus()`. The
  first UNSAT solve now shrinks candidates to a core before deletion
  minimization, and later UNSAT deletion trials can shrink again.
- Extended ABC's CaDiCaL C wrapper with configuration and option hooks, an
  absolute `abctime` terminator, and safe saturation of 64-bit conflict limits
  at `INT_MAX` instead of integer wraparound.
- Fixed saved-assumption lifecycle in `cadical_solver_solve()`: every solve,
  including an assumption-free solve, clears the previous assumption vector
  so `cadical_solver_final()` cannot return a stale core.
- Strengthened the direct API test to check backend identity, semantic
  subset-minimality, exact minimum cardinality, a conflict budget exceeding
  32 bits, expired-deadline termination, ordinary SAT queries, and the empty
  MUS for root-UNSAT background.
- Diagnosed the minimum-MUS slowdown as the raw guarded-subset lattice search,
  not CaDiCaL SAT performance. Replaced that search with an implicit
  hitting-set loop: minimum hitting sets are checked by the persistent
  CaDiCaL instance, SAT candidates are grown to MSSes, and their complements
  become on-demand MCS constraints.
- Added model-guided MSS growth and a CaDiCaL map solver with binary bound
  search and sequential-counter AtMost constraints. Production managers also
  explicitly disable CaDiCaL's internal assumption/core validation
  sub-options, matching the standalone backend.
- Migrated `formace.c`'s two proof-independent UNSAT validation helpers to
  CaDiCaL. Its only remaining MiniSat-derived instance is the interpolation
  proof builder, which requires ABC's `sat_solver_store` proof interface and
  is not part of CAMUS selection.
- Added exhaustive-oracle minimum checks on sixteen six-group formulas and a
  reusable grouped-DIMACS benchmark driver. On the depth-5 `msmie.3` artifact
  (73,316 clauses, 153 optional groups), three exact searches returned the
  same 26-group minimum in 5.038, 5.181, and 5.147 seconds; the replaced
  subset-lattice search exceeded 60 seconds. End-to-end
  `fm_int -m -F 5 -L 153` reached its frame limit in 6.97 seconds instead of
  exceeding 120 seconds in the old search.
- Added `FM_CAMUS_CADICAL.md` as the authoritative architecture, algorithm,
  build, resource-limit, consumer, and verification guide. Updated the CAMUS,
  combinational interpolation, BMC interpolation, and minvar documents to
  describe the active CaDiCaL boundary and the separate proof-solver role.
- Built `libabc.a` and `abc` successfully with
  `make -j2 ABC_USE_NO_READLINE=1`.
- Passed `fm_camus_api_test.sh`, `fm_inter_smoke.sh`, and `fm_int_smoke.sh`.

## Build And Verification Notes

- First full ABC builds can take several minutes.
- Prefer incremental builds after editing only `src/formace_ext/`.
- Suggested build command:

```bash
make -j4 ABC_USE_NO_READLINE=1
```

- Latest successful sample output:

```text
ForMACE summary for "i10":
  pi      = 257
  po      = 224
  latches = 0
  nodes   = 2675
  levels  = 50
  objects = 3157
  type    = strashed AIG
  seq     = combinational
```
