# CAMUS/CaDiCaL API and architecture

## Status

The ForMACE guarded-group API is fully backed by ABC's bundled CaDiCaL 2.2.0.
The public `Fm_Camus*` C API is unchanged, so both current consumers migrate
together:

| Consumer | Selection operation | CaDiCaL-backed API |
| --- | --- | --- |
| `fm_inter -c` | one subset-minimal shared-PI set | `Fm_CamusFindMus()` |
| `fm_inter -m` | global minimum-cardinality shared-PI set | `Fm_CamusFindMinimumMus()` |
| `fm_inter -y` | minimum within baseline support | `Fm_CamusFindMinimumMus()` |
| `fm_int -m` | minimum latch boundary per iteration | `Fm_CamusFindMinimumMus()` |
| `fm_int -y` | minimum within interpolant latch support | `Fm_CamusFindMinimumMus()` |

There is no CAMUS subprocess, DIMACS interchange, or MiniSat instance inside
`fm_camus.c`. Clauses, assumptions, failed cores, and results remain in
memory.

## Architecture

```text
fm_inter / fm_int
        |
        | zero-based group IDs and ABC-encoded clauses
        v
Fm_Camus* guarded-group API
        |
        | persistent selectors, assumptions, failed cores
        v
ABC cadical_solver C wrapper
        |
        v
Bundled CaDiCaL 2.2.0 C++ solver
```

The proof-producing interpolation solver is intentionally outside this
stack. The CAMUS manager selects a boundary; the existing ABC interpolation
path then rebuilds the selected formula to obtain a proof and interpolant.
This prevents private selector variables from entering interpolation proofs.
The two proof-independent combinational validation checks in `formace.c` also
use CaDiCaL. The remaining MiniSat-derived solver is only
`ForMace_AigInter()`, where ABC's proof-store API is required.

## Guarded-group representation

`Fm_CamusStart(nVars, nGroups)` reserves caller variables `0 .. nVars-1` and
one private selector variable for each group. A caller clause `C` in group
`g` is stored as:

```text
C OR NOT selector(g)
```

Solving with group `g` enabled passes `selector(g)` as a positive CaDiCaL
assumption. Groups omitted from the assumption vector remain disabled. One
CaDiCaL instance is retained for the manager lifetime, so learned clauses are
reused by deletion minimization, MSS growth, and implicit-MCS queries.

Inputs and outputs use zero-based group IDs. Clause literals use ABC's normal
non-negative encoding (`Abc_Var2Lit`, `Abc_Lit2Var`); the existing
`cadical_solver` wrapper translates them to CaDiCaL's signed, one-based
literals.

## CaDiCaL configuration

Production manager construction keeps CaDiCaL's preprocessing/inprocessing and
normal focused/stable phase switching enabled, while retaining incremental
lazy backtracking for the repeated related assumption queries:

```text
preprocessing/inprocessing = CaDiCaL defaults
ilb           = 2
search phases = CaDiCaL default switching
checkassumptions = 0
checkconstraint  = 0
checkfailed      = 0
```

This is the `cadical-preprocessing-default-phases` configuration from the
solver-tuning matrix. It was faster than the former `plain` plus stable-only
configuration in seven of eight benchmark/depth pairs, including all four
depth-8 pairs, while returning the same exact minima. The former configuration
remains available to ablation drivers as `cadical-plain-stable`. The internal
validation sub-options are disabled in the production manager; semantic
regression tests validate cores and results externally.

The exact minimum path does need cardinality, but on its smaller hitting-set
map formula rather than on the guarded circuit formula. Each minimum search
constructs one incremental CaDiCaL map solver and one sequential counter up to
the seed upper bound. AtMost bounds are selected by assumptions on the final
counter row, and each discovered MCS is added permanently to the same solver.
The minimum hitting-set cardinality from one refinement is retained as the
next lower bound because adding an MCS cannot decrease that minimum. Learned
clauses, the counter, and all prior MCSes are therefore reused throughout the
search.

## API behavior

Include `formace_ext/fm_camus.h`:

```c
Fm_CamusMan_t * Fm_CamusStart( int nVars, int nGroups );
void            Fm_CamusStop( Fm_CamusMan_t * p );
const char *    Fm_CamusBackendName( void );
void            Fm_CamusSetLimits( Fm_CamusMan_t * p,
                                    ABC_INT64_T nConfLimit,
                                    abctime nTimeOut );

int             Fm_CamusAddBackground( Fm_CamusMan_t * p,
                                        int * pLits, int nLits );
int             Fm_CamusAddGroup( Fm_CamusMan_t * p, int iGroup,
                                   int * pLits, int nLits );
int             Fm_CamusSolve( Fm_CamusMan_t * p,
                                Vec_Int_t * vEnabled );
Vec_Int_t *     Fm_CamusFindMus( Fm_CamusMan_t * p,
                                  Vec_Int_t * vEnabled );
Vec_Int_t *     Fm_CamusFindMinimumMus( Fm_CamusMan_t * p,
                                         Vec_Int_t * vEnabled );
Vec_Int_t *     Fm_CamusFindMinimumCommonMus( Fm_CamusMan_t ** ppMans,
                                               int nMans,
                                               Vec_Int_t * vCandidates,
                                               Vec_Int_t * vSeedCommon,
                                               int fVerbose );
```

`Fm_CamusBackendName()` returns the linked solver signature, currently
`cadical-2.2.0`. `Fm_CamusSolve()` returns the usual ABC values `l_True`,
`l_False`, and `l_Undef`.

`Fm_CamusFindMus()` works as follows:

1. Normalize and validate the candidate group vector.
2. Solve under all candidate selector assumptions.
3. On UNSAT, read CaDiCaL's `failed()` assumptions immediately.
4. Convert that core back to group IDs.
5. Deletion-minimize the core, using any later failed core to skip additional
   groups when possible.

The result is subset-minimal but is not necessarily globally smallest.

`Fm_CamusFindMinimumMus()` uses an implicit hitting-set loop:

1. Obtain one MUS as a valid upper bound.
2. Greedily enumerate pairwise-disjoint MCSes by making all preceding
   complements mandatory during the next MSS grow. Their count is a certified
   initial lower bound.
3. Compute a minimum hitting set of the MCSes discovered so far with the
   persistent CaDiCaL map solver, assumption-selected cardinality bounds, and
   the retained monotone lower bound.
4. Ask the persistent CaDiCaL instance whether that hitting set is UNSAT.
5. If it is UNSAT, its hitting-set lower bound and UNSAT upper bound coincide,
   so it is a global minimum.
6. If it is SAT, grow it to a maximal satisfiable subset (MSS), using selector
   values from each model to enable groups in bulk and incremental trials for
   the rest. Its candidate complement is a new MCS; add it incrementally to
   the map solver and repeat without rebuilding the counter or solver.

Learned correction sets are kept as an inclusion-minimal antichain. A
deterministic multi-start packing of pairwise-disjoint learned sets may raise
the lower bound further; because the actual disjoint sets are the certificate,
this acceleration does not weaken exactness.

This applies the CAMUS MUS/MCS duality without eagerly enumerating every MCS.
It replaces the slow raw subset-lattice traversal while retaining an exact
result. The `-L` limits remain useful guards because the worst case is still
exponential. Both guarded-formula and map-solver queries observe the deadline.

### Multi-manager common minimum

`Fm_CamusFindMinimumCommonMus()` solves the related problem of finding one
minimum group set that is UNSAT in every manager. The managers share the same
group universe, so one group is selected and counted once across all branches.
This is the multi-oracle equivalent of minimizing `S` for

```text
(B_0 OR ... OR B_(k-1)) AND Eq_S.
```

It deletion-minimizes a supplied common seed, bootstraps pairwise-disjoint
MCSes using the combined OR oracle, and validates each candidate in every
persistent manager. A failed candidate learns one combined-oracle MCS plus
branch-local MCSes from the SAT managers. Corrections form an inclusion-
minimal antichain and are repacked for certified lower bounds.

Unlike the single-manager path, the common path rebuilds an exact temporary
map over the current MCS-incidence equivalence/dominance quotient. At an
already certified lower bound, exact-checked greedy and local repair may
provide the next hitting set. The reduced map is built lazily only when those
candidates fail. These candidate generators never raise the lower bound; all
feasibility decisions still come from the guarded managers.

An empty result is valid when the background is already UNSAT. `NULL` means
SAT input, invalid input, timeout/resource exhaustion, or another failure;
callers must not interpret `NULL` as an empty MUS.

## Resource limits

`Fm_CamusSetLimits()` passes the conflict budget to CaDiCaL and installs a
terminator for ABC's absolute `abctime` deadline. The wrapper accepts
`ABC_INT64_T`; because CaDiCaL's public conflict-limit parameter is an `int`,
larger finite values are safely saturated at `INT_MAX` instead of wrapping.

The CaDiCaL wrapper also clears its saved assumption vector on every solve,
including assumption-free solves. This is required so `cadical_solver_final()`
never reports a stale core.

## Build integration

The top-level ABC `Makefile` already builds both modules:

```text
src/formace_ext
src/sat/cadical
```

`src/formace_ext/module.make` adds `fm_camus.c` and the direct
`fm_minunsat.c` DIMACS command to `abc` and `libabc.a`. `fm_camus.c` includes
`sat/cadical/cadicalSolver.h`; no extra library, runtime path, or external
solver installation is required.

Build with:

```bash
make -j4 ABC_USE_NO_READLINE=1
```

## Verification

Run all focused integration tests from the ABC fork root:

```bash
bash src/formace_ext/tests/fm_camus_api_test.sh
bash src/formace_ext/tests/fm_minunsat_test.sh
bash src/formace_ext/tests/fm_inter_smoke.sh
bash src/formace_ext/tests/fm_int_smoke.sh
bash src/formace_ext/tests/fm_runeco_minimum_test.sh
bash src/formace_ext/tests/fm_runeco_global_test.sh
```

The direct API test asserts the `cadical-` backend signature, validates a
failed-core-derived MUS, proves subset-minimality by removing each member, and
checks exact minimum cardinality on 512 deterministic random grouped formulas
against an independent exhaustive truth-assignment/subset oracle. The oracle
does not call CaDiCaL or `Fm_CamusSolve()`. The test also retains sixteen
SAT-oracle enumeration cases, exercises a conflict limit larger than 32 bits,
checks an already-expired absolute deadline, and verifies the root-UNSAT empty
MUS. It additionally checks the disjoint lower-bound certificate and requires
exactly two solver constructions: one guarded-formula solver and one
persistent map solver.

The `runeco` test exercises the actual two-copy ECO encoding. It enables the
`-w` audit, which exhaustively checks every smaller group subset when an `-m`
iteration has at most 16 remaining candidates, and then independently runs CEC
on the emitted patch.

For a grouped-DIMACS performance check, run:

```bash
bash src/formace_ext/tests/fm_camus_grouped_benchmark.sh \
  FILE.cnf FILE.groups minimum-all
```

The first group-map line is loaded as permanent background and later lines
become optional groups. On the existing depth-5 `msmie.3` artifact (73,316
clauses and 153 optional groups), three exact runs returned the same 26-group
minimum in 5.038, 5.181, and 5.147 seconds. The old subset-lattice search did
not finish under a 60-second guard. An end-to-end `fm_int -m -F 5 -L 153` run
on `msmie.3` completed its four selection iterations and reached the frame
limit in 6.97 seconds; the old search did not finish in 120 seconds.

The other suites verify both interpolation implications, support selection,
minimum and hybrid BMC modes, zero-boundary interpolation, unsafe behavior,
and resource-guard behavior.

## Implementation files

- `src/formace_ext/fm_camus.h`: stable public grouped-constraint API.
- `src/formace_ext/fm_camus.c`: CaDiCaL-backed manager and MUS searches.
- `src/formace_ext/formace.c`: combinational `fm_inter` consumers.
- `src/proof/int/intM114.c`: sequential `fm_int` consumers.
- `src/sat/cadical/cadicalSolver.h/.c`: ABC C wrapper, limits, saved
  assumptions, and core access.
- `src/sat/cadical/ccadical.h` and `cadical_ccadical.cpp`: configuration hook
  for the CaDiCaL C++ API.
- `src/formace_ext/tests/fm_camus_grouped_benchmark.*`: reproducible grouped
  CNF correctness/performance driver.

## Remaining scope

The API returns one subset-minimal MUS or one minimum-cardinality MUS. Its
minimum search discovers only the MCSes needed for that result; it does not
expose bounded all-MCS/all-MUS enumeration. Enumeration would require result
and memory budgets plus the standalone native AtMost batching.
