# Lightweight placement for ABC

This extension provides a deterministic, in-core placement estimate for an
ABC strashed AIG or a technology-mapped standard-cell network. It is
intentionally small and keeps placement state outside Abc_Obj_t, so the
upstream ABC data structures remain unchanged. Ordinary optimization modes
retain their original search; physical modes are opt-in.

The upstream implementations and parsers for `rw`, `rf`, `rs`, and `strash`
are unchanged. This directory owns their separate `pa_rw`, `pa_rf`, `pa_rs`,
and `pa_strash` variants. The `paAbc*.c` and `paRwrEva.c` files are renamed
copies of the corresponding ABC passes and evaluator; placement state,
candidate scoring, and command registration live only in this extension.

## Build

The extension is discovered by ABC's existing `src/ext-*` build support.
Build with `make -j` or:

```
cmake -S . -B build-cmake -DABC_SKIP_TESTS=ON -DCMAKE_BUILD_TYPE=Release
cmake --build build-cmake --target abc -j
```

`ABC_SKIP_TESTS` avoids fetching ABC's optional GoogleTest dependency. The PA
regression checks below require only Python 3 and the built executable.
The `paInit.cpp` registrar and placement implementation are compiled into
the ABC library. `src/base/main/mainInit.c` explicitly initializes and shuts
down the module in both Make and CMake builds. As with ABC's
current-network interface, PA state is used serially, not concurrently by
multiple threads in one process.

## Paper flow

The paper's bounded timing setting is explicit: `pa_rw -t -S 2 -E 0` and
`pa_rf -t -S 2 -E 0`. Resubstitution uses `pa_rs -N 2 -t -S 2` and maintains
strict timing for its nonlocal divisors. The general `-t` default remains
strict (`-E 2`); use the explicit paper commands to reproduce bounded results.

Starting from `read design.aig; strash; dc2`, load the target Liberty file with
`read_lib library.lib`. Define **P** as this fixed six-command sequence:

```
pa_rs -N 2 -t -S 2; pa_rw -t -S 2 -E 0; pa_rf -t -S 2 -E 0;
pa_rs -N 2 -t -S 2; pa_rw -t -S 2 -E 0; pa_rf -t -S 2 -E 0
```

PA runs `pa_place; P`. PA-unmap first runs PA, then repeats exactly five times:
`&get; &nf; &put; pa_place; pa_strash; P_c`, where **P_c** is **P** with `-c`
added to all six commands. If the input is already DC2-preprocessed, omit the
initial `dc2`. Final evaluation maps the saved optimized AIG using
`&get; &nf; &put; stime; pa_place; pa_stats`. Use the same library and final
placement settings across flows.

## Commands

    read design.aig
    strash
    pa_place
    pa_stats

For placement after technology mapping:

    read design.aig
    strash
    read_lib library.lib
    &get
    &nf
    &put
    pa_place

pa_place supports options for iteration count, bin count, utilization, step
size, density weight, and momentum. Run pa_place -h for the current defaults.
`-I` sets the minimum iterations, `-E` caps additional iterations (500 by
default), and `-R` controls the final capacity-constrained refinement rounds
(12 by default; 0 disables that refinement). An iteration cap can stop before
the density target is reached; inspect the reported overflow. These effort
controls are intended for guidance-placement experiments. Final HPWL comparisons
should use the same full placement settings for every synthesized netlist.

For placement-aware AIG optimization, place once and retain the coordinates
across accepted logic edits:

```
read design.aig
strash
pa_place
pa_rw
pa_rf
```

`pa_rs` and `pa_rs -t` use the same placement/HPWL evaluator for
resubstitution. `pa_rs -N 2` enables up to two added ANDs per candidate (the
native default is one); PA mode defaults to minimum node gain zero.

`pa_rf` also defaults to minimum node gain zero, preserving positive-score
physical replacements that do not save nodes. An explicit `pa_rf -M <num>`
requires at least that many saved nodes for every candidate, including
constants and the optional balanced form. `-z` overrides `-M` to allow zero
gain, matching the command's existing option precedence.

The `pa_rw`, `pa_rf`, and `pa_rs` commands select the HPWL-aware path;
ordinary `rw`, `rf`, and `rs` are the unmodified upstream commands. The optional
`-t` switch enables a continuous local-slack timing score (`pa_rw -t`,
`pa_rf -t`). `-T` retains the more expensive full-cone timing score for
controlled comparison.
Without `-t`, candidate selection is unchanged. The timing variant can also
be combined with `-c` after mapped-cell unmapping.

`pa_rw -t -E <mode>` and `pa_rf -t -E <mode>` control timing effort without
changing the score weights or placement algorithm. Mode 2 (the default) keeps
full incremental arrivals, lazy required times, and affected-path candidate
evaluation. Mode 0 retains the bounded traversal-frontier arrival proxy and
freezes required budgets within a command. Mode 1 uses the same bounded
candidate/arrival work as mode 0 but maintains required times lazily. Modes 0
and 1 are deliberate timing approximations, not exact STA. Resubstitution
keeps mode 2 because its divisor set can extend outside the current cone.
These controlled modes require `-t`; `-T` remains a separate full-cone ablation.


For placement-aware optimization **after unmapping a placed cell netlist**:

```
read design.aig
strash
read_lib library.lib
&get
&nf
&put
pa_place
pa_strash
pa_stats
pa_rw -c
pa_rf -c
pa_rs -N 2 -c
pa_stats
```

`pa_strash` assigns each new AIG node the center of the mapped cell
that generated it; shared nodes take the center of the last cell that visits
them. Coordinates are uniformly scaled to the AIG density canvas so the
relative mapped placement and co-located nodes are preserved. `pa_stats`
reports coordinate coverage and the recomputed AIG HPWL/overflow.

Transforms may legitimately remove every AND. The placement sidecar then
retains a valid empty state with no fillers; later PA commands and `pa_stats`
remain valid. A new zero-area canvas (including mapped zero-area cells) uses
finite unit dimensions. `pa_place` still requires at least one initial internal
node; empty states created by optimization or `pa_strash` are supported.

`-c` requires this inherited placement and uses the same shared evaluator
for rewrite, refactor, and resubstitution. It can be combined with `-t`
and `-S 2`. The command resets the cluster mode on return, so a later
command without `-c` uses ordinary incremental placement. For each candidate, the original
MFFC nodes are grouped by nearly equal coordinates (within 0.001 in both
axes). After the usual HPWL-optimal region placement, each new virtual AND
is snapped to the cluster center maximizing
`cluster_size / (squared_distance + 0.001)`. The evaluator then recomputes
the candidate's exact affected-net HPWL and updates density at those snapped
coordinates. Overflow never rejects a candidate. The local placement uses
one deterministic pass.

## Design

The default physical model follows the settings observed in the integrated
RePlAce flow used for comparison:

1. A mapped standard cell is 1 unit high and uses its Liberty area as its
   width. An unmapped AIG node is 1 unit high and 2 or 3 units wide, derived
   deterministically from its two edge polarities.
2. Core area is cell area divided by 0.70, with integer core dimensions and a
   power-of-two bin grid selected from core area and average cell area. The
   automatic grid is capped at 128 bins per dimension, matching the RePlAce
   comparison setting; larger experimental grids remain available through
   `-B`.
3. Filler area occupies the remaining whitespace, so the electrostatic charge
   has the same full-core density target as RePlAce.

Optimization starts from a small deterministic cluster at the core center.
A weighted-average wirelength model sharpens as overflow falls. Cell and
filler rectangles use area-preserving density smoothing, and a separable
cosine/sine spectral solver computes the electrostatic field with Neumann
boundaries. FFT bit permutations, twiddles, cosine phases, and Laplacian
coefficients are planned once and reused on every iteration.

The optimizer combines pin-count and cell-area preconditioning with a
Lipschitz step estimate and Nesterov extrapolation. Its initial density
penalty is normalized to the wirelength and density gradient norms, then
increased in stages as overflow falls. It runs at least 500 iterations and
continues until it reaches the 9.5% pre-refinement overflow target, followed
by a short target-density relaxation. A 512-bin grid uses a slower final
penalty ramp because large designs benefit from extra wirelength recovery.
A final capacity-constrained coordinate pass accepts HPWL-reducing moves only
when the resulting overflow is at most 9.9%. If the analytical/spreading phase
fails to reach that density, refinement does not guarantee recovery; the actual
overflow is always reported. For each moved cell, the other pins' extrema are
cached across the six trial positions and rebuilt for the next cell. Extremal
pins in the smooth wirelength gradient use exp(0) = 1 directly. Both optimizations
retain the full-effort arithmetic and search, without reducing placement work.

The objective structure and physical defaults are inspired by analytic
placement methods such as ePlace and RePlAce. This implementation was written
independently and does not copy or link OpenROAD, OpenDB, OpenSTA, or RePlAce
source code.

The placement manager owns coordinates in a sidecar rather than adding fields
to ABC's core graph types. Ordinary queries use object IDs. A structural
transform brackets accepted edits with `Pa_ManBeginEdit` and
`Pa_ManFinishEdit`, reads existing nodes by object pointer, and assigns every
new node a coordinate before finishing the edit. The finish operation rebuilds
the ID index, nets, density, metrics, and structural fingerprint after ABC
compacts object IDs. A physical pass validates the fingerprint once at entry,
uses constant-time sidecar queries while it owns the graph, and restores the
fingerprint at exit.

## HPWL-aware candidate evaluation

The default evaluator uses fixed-pin extrema and caches live geometry, net
HPWL, and density-bin values between commits. Every accepted edit invalidates
these caches; every pass resets their version so ID reassignment and mapped
unmapping cannot reuse stale entries. Candidate density deltas and entity
lookups use generation-tagged arrays instead of per-entry hash allocations.
The candidate search, score, six-by-six endpoint sampling, and zero-sweep
placement are unchanged.

Before constructing a physical plan, small graphs pass an allocation-free
structural screen. It simulates simplification, live and internal virtual
hashing, and ABC's zero-fanout lookup rule. It rejects old-root reuse, level
violations, or a virtual-node count already exceeding the maximum removable
count. It does not use ABC's approximate count as the exact gain. Larger
graphs and surviving MFFC reuse still go through the complete plan. No top-K
shortlist or candidate budget is imposed. The `ABC_PA_SCREEN_AUDIT` diagnostic
checks rejected candidates against the full evaluator in an audit build.


Rewrite and refactor share `paRewrite.cpp`. Candidate evaluation is virtual:
it does not create an ABC object until the winning replacement is committed.
A symbolic topological pass applies ABC's AND simplifications and structural
hashing, including reuse of nodes inside the old MFFC and hashing among newly
created candidate nodes. It then finds which old MFFC nodes actually survive
and builds affected driver nets from the canonical result. Reused existing
nodes are movable: their old density is removed, their new coordinates are
optimized with the new nodes, and every incident net enters the HPWL delta.
At commit, ABC hashes the graph for real. The incremental HPWL delta is used
only when every symbolic node maps to the predicted real node and phase, the
predicted old nodes disappear, and the direct root fanouts retain their
predicted input literals. A mismatch triggers a global placement-netlist
rebuild and actual-score check instead of trusting the virtual delta. A full
global HPWL recomputation also audits accumulated local deltas before the
physical command returns.

Movable candidate nodes are placed in two stages. A forward pass propagates median
rectangles from leaves to root, and a reverse pass chooses a concrete point in
each rectangle. This is the optimal-region construction for a strict candidate
tree. A decomposition graph can contain shared nodes and reconvergent
hyperedges, so the resulting seed is a heuristic for those cases. The HPWL
of the complete local hypergraph is measured exactly at the chosen coordinates;
no post-seeding refinement sweeps run by default.

The actually removed MFFC nodes and moved existing nodes have their old density
subtracted before a candidate is placed. Within each propagated median rectangle,
a small deterministic grid is compared by footprint-weighted local bin density,
then distance from the rectangle center. Candidate nodes enter the density
workspace only when their points are fixed in the reverse pass. Root
replacements also model any cell-width and density change caused by complemented
edges at their direct fanouts. Density chooses a point in the region; it is not
a weighted score term or a candidate feasibility test. Density samples reuse a
scratch buffer; overflow deltas are computed only when explicitly requested
by a diagnostic caller. The paper flow uses this single placement pass; no coordinate-refinement
sweeps are performed during candidate evaluation.

The HPWL-only candidate score is

```
node_gain + 0.25 * HPWL_reduction / mean_net_HPWL
```

The scale is fixed at the start of each command. `-t` adds

```
W * (c_logic * clip(delta_logic_slack, -2, 2)
   + c_wire  * clip(delta_wire_slack,  -2, 2)
   + c_fanout * clip(delta_fanout_slack, -2, 2))
```

Each criticality is `1 / (1 + max(0, old_slack))`. Fanout slack is the worst
normalized slack across the old root's direct fanouts, measured before and
after the candidate. `W` defaults to 0.5; `-W` is an experimental shared
weight, not a per-design setting. There are no timing buckets or hard slack
cutoffs in `-t`. `-T` retains the older full-cone score as a slow ablation.

Experimental `-S` score ablations are shared by rw/rf/rs. `-S 0` retains the
original score and remains the default. `-S 1` orders candidates by node gain
first and uses a bounded physical score as a tie-breaker. `-S 2` (requires
`-t`) replaces each old-criticality/clipped slack term by the difference
of `Phi(s)`, with `Phi(s)=log1p(s)` for positive slack and `Phi(s)=s` otherwise.
Its derivative is the original criticality, so the score accounts for the
entire transition into critical slack without saturation or a hard rejection.
The existing timing weight is unchanged. These modes are controlled
experiments; routed results determine whether either should replace the default.

Logic arrival adds one per AND; geometric arrival adds Euclidean edge length.
These are separate path maxima, not a cell STA model. The geometric scale is
maximum output wire arrival divided by maximum output logic arrival. Primary
input edges have zero geometric length because this AIG model does not place
I/O pins. Output budgets and the scale stay fixed within a command.

A pass starts with one timing build. At default effort 2, the `pa_rw`, `pa_rf`,
and `pa_rs` timing modes refresh the current MFFC boundary and candidate DAG, evaluate paths
between moved reused nodes, and propagate committed arrival changes through
all affected fanouts. This also covers resubstitution divisors outside the
original root's fanin cone. When ABC maintains
levels (the normal command mode), unrestricted propagation uses
reusable buckets indexed by current structural level. Nodes at the same level
have no dependencies on one another, so they need no heap ordering. Each affected node is recomputed
after its affected fanins, preventing the repeated updates that a FIFO causes
on long reconvergent paths. The level-update-disabled fallback retains the
original worklist. Required-time maintenance and full fanout coverage are
unchanged.

Candidate timing also seeds every direct logical fanout of the replaced root
before querying arrivals, even when no reused node moves. The dependency
closure includes indirect reconvergent paths between those fanouts. Merely
visiting direct fanouts in topological order would still allow cached arrivals
inside a connecting path to remain stale. This correction preserves the score
formula and is enabled by default at exact timing effort.
The evaluator is shared by `pa_rw`, `pa_rf` (including its balanced alternative),
and `pa_rs`; the correction applies to all three operators.

Timing effort 1/2 and timing-scored resubstitution maintain required
times lazily. Reuse and new fanouts can change the downstream budget even
during a forward traversal. An edit marks changed required dependencies
dirty, stopping at already-dirty cones. Before evaluating
a later root, only dirty required values read at its fanout boundary are
recomputed. Neither mode performs unconditional per-edit global timing builds.

`pa_rf -a` optionally evaluates an additional arrival-balanced factored form.
Only uncomplemented singly-used AND associations are flattened; shared and
complemented boundaries are preserved. The earliest-arriving terms are paired,
and the ordinary and balanced forms compete under the same physical score.
An unchanged balanced form is skipped. This flag is experimental until routed
PPA establishes its benefit.

Physical resubstitution evaluates all truth-matching candidates within the
native bounded divisor search, instead of accepting the first area-saving
match. The simulation cut and the actual candidate divisor boundary are kept
separate. The actual divisors protect nodes during MFFC marking; candidate
hashing then determines the true removed and added sets. Equivalent three-leaf
associations are ranked separately because they can have different geometry.
The upstream `rs` command retains its native first-match behavior.

These are structural timing proxies. Full placement, mapped STA, routed delay,
area, wirelength, and activity-based power determine whether a variant is useful.

Candidates that add nodes or have nonpositive score are rejected. Overflow is
never used to reject a logic candidate. The chosen graph is instantiated once;
coordinates for both newly created and reused movable AIG nodes are written to
the sidecar, and the AIG and placement state are committed together. The
symbolic build tracks ABC's hash-table behavior, including its zero-fanout
lookup bypass, and checks each resulting node and literal phase against actual
materialization. Before accepting a candidate whose result reuses an existing
AIG node, the evaluator checks whether `Abc_AigReplace()` would hash a direct
root fanout to another node and propagate replacement beyond the modeled local
boundary. This is an HPWL-accounting guard, not an overflow test. Any
unexpected materialization or boundary mismatch triggers an immediate global
placement refresh and requires a positive actual score before processing can
continue. It also triggers a global timing rebuild because the true edit cone
is unknown. The `-T` ablation rebuilds global timing after every accepted edit
and includes the measured endpoint term.

## Scope

This is a placement estimator for placement-aware logic transforms. It is not
a detailed placer or a replacement for OpenROAD global placement. Fixed macro
handling, row legalization, congestion, timing parasitics, and DEF/LEF
round-tripping are deliberately outside this module. Primary I/O locations
are not modeled, so the reported HPWL is an internal-node placement estimate.

## Correctness builds and production evaluation

Normal builds do not define `ABC_PA_ENABLE_AUDIT`. Redundant candidate-truth,
per-edit full HPWL/density, full timing-cache, and required-use diagnostics
are compiled out in this production configuration. Runtime and PPA experiments
must record the binary hash and use this build.

For a separate audit build, add `-DABC_PA_ENABLE_AUDIT` to both C and C++
compiler flags (for CMake, `CMAKE_C_FLAGS` and `CMAKE_CXX_FLAGS`). Then enable
the desired diagnostics through these environment variables:

```
ABC_PA_CANDIDATE_AUDIT=1
ABC_PA_SCREEN_AUDIT=1
ABC_PA_FACTOR_CACHE_AUDIT=1
ABC_PA_PLACEMENT_AUDIT=1
ABC_PA_TIMING_AUDIT=1
ABC_PA_TIMING_SEED_AUDIT=1
ABC_PA_REQUIRED_AUDIT=1
```

The timing-cache audit checks clean cached values against a full calculation;
required values marked dirty are checked when consumed in lazy modes. The
required-use diagnostic checks the fanout requirements read at each root against
a full calculation. End-to-end CEC verifies the resulting AIG. Diagnostic runs
are excluded from runtime comparisons.
The timing-seed audit recomputes candidate scores and queried boundary arrivals
with every actual node marked affected. It checks dependency/cache handling
within the same timing model, not agreement with mapped STA. The audit suite
includes separate deterministic RW, RF and RS counterexamples that fail without
the root-fanout seed correction, despite producing equivalent final circuits.
It also exercises full-cone timing and a mixed operator sequence.
The resubstitution truth audit aborts on any mismatch and prints its summary
even without `-v`; the regression requires a summary for every audited pass.
Production retains the normal pass-boundary coordinate rebuild and HPWL
consistency check, plus commit identity/boundary guards; these maintain the
live placement state rather than re-running the independent test references.

## Exact runtime optimizations

PA commits use `paAig.cpp`, a renamed copy of ABC's replacement wrapper and
seven private helpers. It retains structural hashing, deletion, and level
worklist order. The reverse-level updater caches each high-fanout driver's
maximum sink level and the number of sinks attaining that maximum during one
replacement. A lost last maximum invalidates that entry and triggers an exact
rescan. This removes repeated scans without changing reverse levels or
candidate decisions. Plain ABC commands still call the upstream replacement.
The opaque manager layout is copied verbatim; run
`python3 src/ext-pa/tests/check_aig_copy.py` after any upstream update.

For controlled comparisons, defining `ABC_PA_DISABLE_REVERSE_CACHE` sends PA
commits to the upstream replacement. Defining `ABC_PA_ENABLE_PROFILE` adds inclusive
phase CPU timers and operation counters; it is absent by default and must remain absent
for runtime measurements. `ABC_PA_REVERSE_AUDIT=1` in an audit build checks
cached reverse maxima against complete fanout scans. Neither profiling nor
that redundant audit runs in the production configuration.

Full placement retains its iteration schedule, density forces, spreading, and
capacity-constrained refinement. Wirelength gradients reuse identical
exponentials at both extremes and specialize two-pin nets without changing
pin accumulation order. Persistent gradient buffers avoid repeated allocation.
Density upper boundaries use an exact IEEE predecessor when applicable,
with `nextafter` as the general fallback. Candidate placement prepares each
sample axis once and accumulates the same footprint costs directly; the
sampling grid, density tie-breaking, and score are unchanged.

Only placement-aware refactor (`pa_rf`) memoizes the pure `Kit_TruthToGraph`
step within each command. Upstream `rf` retains the original factoring call and
never allocates or accesses this cache. The synthesis speedups are restricted
to placement-aware commands; plain `rw`, `rf`, and `rs` retain their ordinary
algorithms. The direct-mapped cache checks the complete ordered truth
table and variable count; collisions only cause misses. It stores independent
unbound graphs and returns a fresh copy before any network objects are attached.
There are at most 1024 entries of 16 KiB payload each, freed at command end.
No candidate is skipped or changed by this cache. In audit builds,
`ABC_PA_FACTOR_CACHE_AUDIT=1` recomputes every hit and checks that the factored
graph is identical. Production builds omit this redundant work.

## Runtime measurement

Use `pa_time -c; <flow>; pa_time` to record process CPU and monotonic elapsed
seconds separately. Start the timer after common input/library loading, and
stop it before final evaluation. The native ABC `time` command uses wall time
on Unix despite the name of its `Extra_CpuTimeDouble` helper. Do not label its
output as CPU time. Suspend/resume intervals count toward elapsed time but not
process CPU. This diagnostic command adds no work unless explicitly invoked.

## Regression checks

```
python3 src/ext-pa/tests/regression.py --abc build-cmake/abc
python3 src/ext-pa/tests/regression.py --abc build-cmake/abc --lib library.lib
```

The self-contained suite generates shared, reconvergent networks, checks
HPWL-only and all timing efforts, mapped coordinate transfer, command-state
invalidation, and malformed input. It formally checks every optimized network
against its input. Edge cases cover all-AND removal, buffer-only unmapping,
zero-area mapped libraries, explicit refactor minimum gains, and continued
commands on empty placement states. Add `--audit` when using a build configured with
the compiler definition `ABC_PA_ENABLE_AUDIT` to check incremental HPWL/density, timing, structural
screening, candidate truth, factoring-cache hits, and reverse-level maxima.
Tests run sequentially and retain their logs in the printed directory; their
times are not benchmark measurements.
