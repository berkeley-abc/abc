# Cube-based PLA decomposition and verification

`&decpla input.pla` constructs and verifies an AIG by default, replacing the
current &-space GIA only on success. `-p` only validates the PLA and prints its
statistics; it leaves the current AIG unchanged. Compatibility checks, support
minimization with `-m`, and verification with `-c` also leave ABC networks unchanged.
The command is independent of SN.

Use these commands at the ABC prompt, or quote them when passing them to `abc -c`:

```
&decpla example.pla
&decpla -w example.pla
&decpla -x example.pla
&decpla -p example.pla
&decpla -m -o reduced.pla example.pla
&decpla -m -S 42 -o alternative.pla example.pla
&decpla -m -b -o baseline.pla example.pla
&decpla original.pla reduced.pla
&decpla example.pla; &w result.aig
&decpla -K 10 -O 3 -S 0 example.pla; &w best.aig
&decpla -c example.pla
```

The `-p`, `-m`, and `-c` modes are mutually exclusive and take one input
file. Supplying two PLAs without a mode selects compatibility checking.
`-o output.pla` requires `-p` to copy the validated PLA or `-m` to write its
minimized supports. Use `-O 3` for shuffled output synthesis order and
`&w output.aig` after decomposition to save the resulting AIG.
`-b` and `-S` apply to decomposition or `-m` and cannot be combined.
The former `-d` option is no longer accepted; decomposition is the default.

The parser requires `.i`, `.o`, explicit `.type fr`, and `.e` (or `.end`).
Optional `.p` is checked against the number of rows. Optional `.ilb` and `.ob`
must contain unique labels. Comments begin with `#`. Input and output row
characters are `0`, `1`, and `-`. An output `1` contributes to its On cover,
`0` to Off, and `-` contributes neither. Uncovered points are unspecified.
Other PLA types/directives are rejected rather than interpreted as FR.
Dimensions must be positive and at most 1,000,000; lines are dynamically sized.
Contradictory On/Off covers are rejected. PLA output with `-o` does not
overwrite existing files. AIG export follows the standard `&w` behavior.

Each cube uses two bits per input: `00` don't-care, `01` zero, `10` one.
`11` is a contradiction, never a stored literal. Covers are contiguous packed
cube arrays, independently maintained for each output and polarity.

`-m` selects a weighted hitting set of the On/Off cube-pair conflict sets.
Singleton separators are mandatory. Each remaining variable receives a score
of `floor(2^20 / conflict-set-size)` from each uncovered pair it separates.
The highest-scoring variable is retained; tied scores are resolved by a local
seeded PRNG. `-S seed` defaults to zero, accepts unsigned 32-bit values, and
does not affect ABC's global random state. Identical input and seed reproduce
the result; different seeds may, but need not, produce different supports.
Outputs are processed in file order. Duplicate constraints contribute their
multiplicity to scores. The heuristic is not guaranteed to beat the baseline.

The conflict cache is capped at 8 MiB per output. If the full cache would
exceed that limit, or its allocation fails, the algorithm streams cube pairs
again for each selection pass. Both paths produce identical decisions. This
bounds extra pair storage, not runtime or the original cover storage.

`-m -b` retains the original input-order deletion baseline. It is also used
after weighted selection to prune redundant selections. A variable is erased
from both covers only if the resulting covers remain disjoint. Thus the
result may specify previously unspecified points, but every completion of it
satisfies the original requirements. This is an inclusion-minimal support,
not a guarantee of globally minimum support. Duplicate/subsumed cubes are
removed afterward. The writer retains the full declared interface, including
unused inputs. Reported literal support is the union of literals in the cover,
not an exact functional-support calculation for arbitrary redundant covers.

Two-file mode checks compatibility, not equality: On of either side must
be disjoint from Off of the other. Inputs are matched by labels when both
files have labels; otherwise equal-size positional interfaces are required.
Mixed labeled/unlabeled interfaces are refused. Labeled private inputs are
independent variables in the union interface. Outputs must match completely,
by name when labeled, otherwise by position. A conflict or error returns a
nonzero command status. Compatibility is not transitive and is not sufficient
on its own to prove that an implementation satisfies a specification.

## Verified decomposition

Default decomposition operates on private copies of each original output specification:

1. Minimize support (`-b` selects the input-order baseline).
2. Try completed cached functions, in both polarities, across all outputs.
3. On bounded small problems, compare a disjoint XOR completion with
   ordinary decomposition. Keep it only when AIG AND count does not grow
   and shared AND/XOR gate count shrinks, with at most two extra AIG levels locally.
4. Try cached nodes used by earlier outputs as AND/OR divisors. Prove that
   an OR divisor is zero on every Off cube, then synthesize the exact residual
   `(On & !divisor, Off)`. Complementing the specification gives AND division.
   Compare against ordinary decomposition and retain a divisor only when it
   reduces additional AIG nodes with at most two extra AIG levels locally.
5. Try strong OR and AND bi-decompositions. Seed pairs and greedy expansion
   seek balanced exclusive variable groups; shared variables remain allowed.
   If strong grouping fails, try a weak split with one exclusive group empty.
   Bounded exact cube subtraction must prove progress before accepting it.
   Reuse-aware ranking evaluates both first-component orders of strong
   splits and favors a component that is already available and verified.
6. Complete the left function first, then derive the right ISF using that
   *actual* completion. OR feasibility is `On & exists_A(Off) & exists_B(Off) = 0`.
   AND uses the dual specification. The right On cover is
   `exists_A(On & !left)` and the right Off cover is `exists_A(Off)`.
   For bounded small covers, build both completion orders in each
   feasible polarity and retain the smaller result, breaking ties by depth.
7. Try disjoint XOR decomposition on supports of at most eight variables
   before falling back to Shannon MUX decomposition. A temporary care table
   induces bipartite parity constraints for each variable partition. Conflicting
   cycles reject a partition; consistent components become child cube ISFs.
   Each XOR costs three AIG AND nodes, not one.
   The Shannon variable minimizes the sum of literal counts in each
   cofactor's smaller literal-count cover. Constant cofactors cost zero.
   Ties prefer constant and single-cube cofactors, then fewer total cubes,
   then the existing seeded variable order. The scan counts each cube's
   literals once and subtracts the split literal when present, without
   constructing trial covers or assuming further simplification.
   Single-cube completions are constructed directly; at recursion depth 128,
   a balanced SOP completion prevents unbounded recursion.
8. Extract common factors across maximal uncomplemented AND trees, including
   products inside SOP cones. Retain a replacement only when the total reachable AND count
   decreases and global AIG depth increases by at most one.
9. Clean dangling speculative nodes and try internal-node resubstitution
   using the original PLA care constraints. Accept smaller graphs only.
10. Verify the completed AIG against every original On/Off cube. Only a
    successful proof permits installation in &-space. The resulting AIG
    can then be saved with `&w`. `-o` remains reserved for PLA output in
    `-p` or `-m` mode and cannot be combined with decomposition.

For an output with at most 2048 total On/Off cubes, at most 256 declared
inputs, and at most 8192 current AIG objects, default decomposition considers
up to four supports: the usual weighted selection, then deletion in forward
input order, reverse input order, and a shuffled input order derived from
`-S` and the original output index. The shuffled order varies across outputs
without depending on the synthesis schedule. The weighted support remains
the baseline. Identical support sets skip the alternative build regardless
of deletion order. If the weighted result needs at most one new AND beyond
completed outputs, alternatives are skipped to limit search effort.
Each distinct support is decomposed from the same starting graph, functional
cache, and grouping random state, in a separate AIG. A rejected trial therefore
cannot leave dangling nodes that change subsequent search.
Only the selected graph, cache, random state, and decomposition counters are
retained. Split, reuse, XOR, divisor, and completion statistics describe the
search for the selected support; discarded support trials do not inflate them.
The `support trials` counter still includes all distinct alternatives tried.

Selection compares additional AIG nodes beyond those already required by
completed outputs. Every alternative is limited to two extra levels relative
to the weighted result; this limit is not relaxed after a new winner is found.
The smallest eligible implementation wins, with lower depth breaking ties.
These are local bounds, so changed sharing or postprocessing can still
increase the final whole-design area. The existing `-b` option uses only
input-order deletion and bypasses these trials. Other options, including
reuse and XOR settings, apply to all alternatives. The summary reports
extra distinct `support trials` and the number of outputs for which an
alternative is locally selected. Support minimization with `-m` is unchanged.

The AIG uses structural hashing. A persistent cache additionally attempts
functional compatibility of completed functions whose conservative supports
fit the current ISF. It stores at most 512 functions / 8 MiB of support metadata
and tests up to 32 eligible recent candidates. Successful reuse and repeated
registration refresh an entry's recency. At either limit, a new function
replaces the least recently used entry, so later outputs can still register.
Constants and PI literals use direct completion shortcuts instead of cache
slots. `-r` disables this functional reuse, not structural hashing.
The implementation deliberately avoids eagerly expanding both cube covers
of every CSF: ternary cube simulation proves easy cases, and incremental SAT
handles ambiguous ones. A reuse SAT timeout is a miss, never a match.

Divisor search is also enabled by default and disabled by `-r`. It examines
up to 64 recent cached nodes that are reachable from earlier completed
outputs, in both polarities. Simulation on 32 On and 32 Off care points ranks
candidates by covered care points; it only rejects candidates. Up to eight
candidates receive exact cube/SAT proofs and bounded residual filtering.
The residual must have fewer On cubes in the chosen polarity. Nodes from
discarded trials are not considered free shared divisors.

The ordinary and divisor completions are compared without nested divisor
searches. A baseline root is excluded from residual reuse because it would
trivially satisfy the weaker residual specification and conceal smaller
completions. Area counts each distinct AND not already needed by earlier
outputs. The local two-level allowance is not a global timing constraint:
earlier output choices and subsequent reuse can change the final depth.
The `divisors` statistic counts accepted local replacements, not final gates.
Cached trial results remain subject to the cache limits. Discarded trial
nodes do not count against the committed node limit.

Completion trials consider both orders of each feasible strong partition
in both polarities (OR and its AND dual), starting with the heuristic's
preferred choice. Swapping a weak partition would produce a constant first
component and repeat the unchanged specification, so only its useful order
is built. Trials allow at most 128 total On/Off cubes at recursion depths
zero through two, or at most 16 cubes deeper in the recursion. These counts
are taken after support minimization. Completion trials do not nest.
Each trial starts from the same grouping random state; the selected trial's
ending state is retained. The structurally hashed graph and its bounded
functional cache can retain candidates from earlier trials.

Selection counts distinct ANDs not already used by earlier outputs, with
fewer levels breaking area ties. This local comparison does not guarantee
global improvement, because later sharing and completion choices can change.
The summary reports `completion trials` and `alternatives selected`.

XOR trials use the existing XOR feature (`-x` disables both trials and the
fallback). They are limited to eight support variables, 64 total On/Off
cubes, recursion depths zero through two, at most 4096 current AIG objects,
and at most 512 outputs. Nested trials are suppressed inside the XOR children;
the ordinary baseline still tries XORs in eligible descendants. The baseline
starts after the common support minimization, reuse scan and single-cube
checks. Both alternatives start with the same grouping random state and
functional cache; only the winner's ending state and cache are retained.
Internal-node harvesting follows the chosen cone and skips dangling nodes.
The cost includes already completed outputs, so sharing is counted. XOR
recognition counts each two-input AND or XOR as one gate; a product used
elsewhere remains charged even if it also belongs to an XOR implementation.
The returned graph is still an AIG: an XOR alternative must not increase its
AND count, must strictly reduce the AND/XOR gate count, and must fit `-N`.
As with other local trials, later sharing can improve or worsen the final
whole-design result; the local area and depth checks are not global guarantees.

Common-factor extraction runs after all outputs are completed, on designs
with at most 512 outputs. It collects output roots and complemented-edge
boundaries throughout the reachable graph. Each eligible product contains
at most 32 distinct boundary literals; these can be inputs or complemented
internal signals. Uncomplemented shared nodes can be flattened, while their
other uses remain represented in the full graph. The pass extracts a frequent
literal/factor pair, up to 64 factors within the existing work budget. Only
products that received a factor are reassembled and balanced; untouched rows
keep their original trees and sharing. Other output cones are retained,
including any existing uses of their internal nodes. Comparing the union of
all output cones prevents counting those nodes as savings. This pass needs
no command-line option.

Internal-node resubstitution then tries replacing an AND by an existing
signal or its complement, including constants and inputs. A divisor may
occur later in the old topological order, provided it does not depend on
the node being replaced. The trial rebuilds all fanouts of the node, so a
shared internal signal is changed consistently across outputs.
Targets are ranked by removable cone size (MFFC), with higher node IDs
breaking ties. Divisors are ranked by increasing level and then node ID,
in both polarities, so constants and inputs are tried first. After an
accepted replacement, simulation is refreshed and pending targets are
mapped through the cleaned graph. Already visited, deleted and merged
targets are skipped, so failed roots do not consume the visit budget again.

For each output, 64 points sampled from its original On/Off cubes provide
a rejection filter. Flipping a candidate root and simulating its fanouts
identifies the points where that root is observable. Simulation never
accepts a replacement: every original cube at every affected output must
pass a fresh-solver proof. Unaffected output cones retain their behavior.
Inconclusive proofs reject the candidate, and the usual full verification
checks all original cubes again before returning the final AIG.

Each accepted replacement strictly reduces the cleaned AIG AND count and
does not increase the AND/XOR gate count. Global AIG depth may rise by at
most one relative to the graph entering this postpass. Search is bounded
to 20,000 AIG objects, 128 outputs, eight trial divisors per visited root,
512 candidate builds, 64 accepted replacements, and 4096 distinct root visits.
MFFC ranking, simulation, candidate scans, graph copies, and cone-based cube evaluation
share a work budget of 64 times the existing search work limit. Trial SAT
queries use at most 100 conflicts, or the user's smaller limit. Exhaustion
stops improvement and keeps the last verified replacement, rather than
failing decomposition. The summary reports accepted internal replacements
and candidate builds. This pass is part of internal-node reuse: it is on
by default and disabled by `-r` or by clearing API feature bit 4.

Cone-restricted evaluation and cone-based work accounting are always enabled,
including in the default run; no command-line switch or feature bit is needed.
Cube evaluation collects each candidate's input/AND cone once and evaluates
only that cone for subsequent cubes and either polarity. Reuse and
completed-left filtering charge this cone size to the work budget. Unrelated
outputs and discarded speculative nodes do not consume that evaluation
budget. Filtering also selects split variables from the prepared cone.

Weak AND/OR decomposition and bounded XOR decomposition are enabled by
default. `-w` toggles weak decomposition, and `-x` toggles XOR decomposition;
specifying either once disables it, and specifying it twice restores it.
These switches apply only to decomposition. The former `-F` command-line
feature mask is no longer accepted.

Reuse-aware grouping and first-component order, together with caching of
internal AIG nodes, are included whenever reuse is enabled. They do not
require separate command-line switches. `-r` disables functional reuse.

Internal-divisor harvesting uses at most 256 cache slots, leaving the remaining
slots for roots. Support traversal is bounded.

The C API retains `Decpla_Options_t.Features` for experiments: bits 1, 2, 4,
and 8 select weak splits, reuse-aware selection, internal-node reuse, and
XOR respectively. Their sum, 15, remains the API default. Additional bits 16
(early reuse), 32 (BDC leaves), and 64 (final root reuse) are available only
through this API and are disabled by default. Early reuse can exploit a
different support than the one selected by minimization, but still has to
satisfy every cube. BDC leaves receive explicit On and care truth tables;
unspecified points are not silently assigned zero.

Final root reuse is limited to AIGs with at most 8192 objects. It filters divisors
using 64 sampled care points, then proves every original cube before accepting
a replacement (at most eight candidate proofs per output). The sample is only
a rejection filter. Cost counts nodes not already needed by other outputs.
The original solution is retained if cleanup reveals a worse node/level pair.
This optional pass has cone-traversal overhead and is not intended as the final
large-design resubstitution implementation.

Intersections/projections use absorption with a cap of 1024 cubes per
intermediate cover and 200,000 elementary word-work units per search phase.
Exhaustion rejects the candidate, not the specification. The completed-left
restriction uses bounded cube splitting instead of constructing a potentially
exponential global complement. The support-selection cache retains its
separate 8-MiB limit. These are local bounds, **not a wall-clock deadline**:
support minimization, original cover storage, final verification, and the
number of recursive calls are not bounded by the cube-work counter.

`-N` limits committed AND nodes (default 200,000). The count is the union of
the cones of completed outputs, checked after each output is committed.
Shared nodes count once, and discarded speculative nodes do not count.
The temporary graph can be larger; unused nodes are removed by final cleanup.
The summary reports constructed and committed counts separately.
`-C` limits conflicts per final SAT query (default
10,000) during decomposition. Standalone `-c` uses the default limit and does
not accept `-C`. Final verification reports mismatch or inconclusive separately;
neither result installs an AIG. This verification uses a fresh solver, with
the original PLA, rather than trusting the decomposition's intermediate ISFs.
No unspecified point is assumed zero by the proof.

`-S` also controls grouping order. `-O 3` shuffles the order in which outputs
are synthesized, without changing their interface order. `-K attempts` tries
consecutive seeds, retaining the verified candidate with the fewest ANDs,
then the fewest levels. It compares raw AIGs, before any downstream synthesis.
The default is one attempt. Attempts run serially; there is no built-in
multicore option.
PI/PO ordering is always the original PLA order; the binary AIG does not carry
the PLA's labels. `-c original.pla` verifies the current ordinary combinational
AND/inverter GIA positionally, useful after `&b; &resyn3; &b`.

The `time = ...` in each successful decomposition summary is CPU time for
that attempt, including any output-sizing prepass and final verification.
It excludes initial PLA reading and AIG file output; final verification is
not timed separately. To time verification of a saved AIG without rerunning
decomposition, use:

```
&r result.aig; time -c; &decpla -c original.pla; time
```

This measures the verification command, including PLA reading, validation,
and statistics, after the AIG has been loaded.

`-O mode` selects the output synthesis schedule: 0 is file order (default),
1 smallest-first, 2 largest-first, and 3 seeded random order. The exported
output order always remains the original PLA order.

Smallest/largest use the raw AND count obtained by independently decomposing
and verifying each output with the same decomposition options and seed, but
with no cross-output cache. This sizing prepass is included in runtime. It estimates
standalone implementation size, not a minimum-size guarantee or the incremental
cost after sharing. Equal-size outputs retain file order. Sizes may vary with
the seed. `-K` repeats the sizing prepass for each attempted seed. A failed
prepass rejects the attempt without installing a partial design.

By default the seed controls both random ordering and recursive decomposition choices.
Changing the schedule also changes the traversal-dependent sequence of these
choices, so an order experiment measures that interaction as well as sharing.

Use `-Q seed` with `-O 3` to give output permutation its own random
stream, independent of `-S`. For a factorial experiment, first save support
variants using `&decpla -m -S support_seed -o support.pla original.pla`, then
run `&decpla -O 3 -Q order_seed -S grouping_seed support.pla`. The projected
supports are inclusion-minimal, so subsequent minimization cannot remove more
variables. Different seeds need not yield distinct supports or networks.
Grouping choices remain traversal-dependent, but no longer consume the
output-order random stream. Always verify final results against `original.pla`,
not just the projected specification. Without `-Q`, legacy seeded behavior
is unchanged. `-K` varies `-S` while an explicit `-Q` remains fixed.

This is a first end-to-end implementation, not a claim to reproduce GTS.
There is no shared-variable XOR search or timing-aware grouping cost yet.
None of the new heuristics dominates the original on every benchmark. For
quality experiments, preserve the baseline, try several decomposition options
and seeds, and compare after identical downstream synthesis and fresh PLA verification.
Choosing the smallest raw AIG is not equivalent to choosing the best mapped
or optimized result.
The initial implementation still uses exhaustive cube-pair scans and
quadratic cover compaction, and is not yet tuned for the largest files.
It uses ABC's internal SAT solver; no SN, Slang, or external tools are needed.

## Build portability

The current DECPLA sources pass native Ubuntu GCC Make builds, Clang CMake
builds, and GCC/Clang CMake builds with `ABC_USE_NAMESPACE=xxx`. The existing
CI rewrite example, embedding demo, CTest cases where configured, and DECPLA
decomposition/verification checks pass. The package also passes C89 declaration
ordering checks. All six C files and both headers are listed in `abclib.dsp`;
Make and CMake include the package through `module.make`.

All six DECPLA files and the initialization hook compile as 32-bit Windows
COFF objects in C, C++, and namespace C++, using Clang with MinGW headers and
the Windows CI preprocessor definitions. This is a compile check, not a native
MSVC build or execution test. Native macOS and MSVC runners were unavailable.
The Clang builds above ran on Ubuntu and do not establish native macOS results.

Compiling the entire repository as C++ without a namespace still fails at
link time with the same 32 unresolved symbols on upstream master and with
DECPLA enabled; the package adds none. The normal mixed C/C++ build and the
namespace C++ builds pass. No GitHub workflow changes or additional production
dependencies were required.

## Research notes after the GT comparison

These are hypotheses to revisit, not confirmed descriptions of GT's algorithm.
The support-search idea in item 2 is now partly implemented in DECPLA. The main
suspicion is that GT makes better choices of completion and support, while
processing care constraints more cheaply. Its public descriptions do not
identify the exact search method.

1. **Recognize simple functions before expensive decomposition.** GT reports
   14 gates at three levels in 0.2 seconds for the BGP/EVPN example, despite
   398 declared inputs and 18 outputs. The care constraints therefore admit
   small implementations. Test constants, literals, and small combinations of
   inputs before expensive support selection. The synthetic BGP input includes
   a rule tag that separates its cubes; correlations involving these fields
   might permit simple completions. That possibility needs checking.

2. **Keep more freedom when choosing support.** DECPLA greedily selects a
   hitting set, projects away other variables, and then decomposes. Projection
   can exclude a cheaper implementation using another support, possibly even
   a larger one. GT may consider several supports or choose support and logic
   together. Minimum support and minimum gate count are different objectives;
   the GT support paper explicitly distinguishes them.
   A bounded comparison of weighted and deletion-based supports is now
   implemented for decomposition, as described above. It does not enumerate
   all supports or guarantee a globally best completion.

3. **Construct useful intermediate functions directly.** One possible search
   builds a pool of signals and scores AND/OR/XOR combinations against the
   unresolved care constraints, reusing useful signals throughout the network.
   This might expose factorizations missed by recursive variable partitions.
   It is a speculative architecture, not an established account of GT.

4. **Spend some depth to reduce area.** On the single-output
   `Example_250_1_2000`, GT reports 431 gates at 28 levels, while the initial
   four-support DECPLA comparison produced 1,257 gates at 21 levels
   (1,384 AIG ANDs at 23 AIG levels). Cross-output sharing cannot explain
   this gap. Completion selection, factoring, or restructuring within one
   output must contribute.

5. **Avoid repeated scans over every On/Off cube pair.** Support selection
   repeatedly visits opposite-care pairs and scores separating variables.
   Compressed constraints, bit-parallel signatures, or incremental separation
   tests could reduce runtime substantially. The stopped runs were not
   profiled, so this remains a likely bottleneck rather than a measured one.

The next experiments should distinguish support-selection losses from
decomposition losses before adding another expensive optimization pass:

- Measure time spent in consistency checking, support selection, cover
  compaction, recursive decomposition, postprocessing, and final verification.
- Check for simple low-support completions before enumerating all opposite-care
  pairs; validate candidates against the original cube constraints.
- Extend the current four-support comparison with further distinct choices
  and compare gate counts, rather than selecting solely by support cardinality.
- If a substantial area gap remains, evaluate direct construction of shared
  intermediate functions and broader completion search with a small depth
  allowance.

The initial two-support experiment compared weighted selection and forward
input-order deletion on a 15-case short suite. Four cases improved in AIG node
count, while PicoRV32 grew by three nodes; the remaining cases were unchanged.
Trials with a 2048-cube bound reached the useful telemetry alternative that
the initial 512-cube bound missed. Keeping separate graphs for the two alternatives
avoided changes caused solely by rejected speculative nodes.

The follow-up with four supports adds reverse and seeded shuffled deletion.
Against two supports on the same 15 cases, PCIe completion decreased from
98 to 80 AIG nodes (8 to 9 levels), and PicoRV32 decreased from 75 to 73 nodes
(4 levels). The other 13 cases were unchanged in nodes and levels. Geomeans
changed by -1.52% AIG nodes, +0.79% AIG levels, and +11.83% wall time; summed
case time increased from 102.391 to 107.120 seconds. Both variants were rerun
in the same batch, and all outputs verified. These are single-run timings;
the shortest cases include substantial process-startup overhead.

The subsequent counter, factoring, shuffle, and cutoff fixes were checked on
the same 15 cases. Six designs shrank, CAN grew by one AND, and eight retained
their area. Geomean AIG nodes decreased 0.72%, while levels increased 3.14%;
ACL and telemetry traded additional depth for area. Repeated timings showed
essentially unchanged total CPU time. The one-new-AND cutoff removed 12 of
144 support trials without changing any node or level result in this suite.

Keep experiments bounded: the current preference is to exclude cases expected
to take more than one minute. The full BGP/EVPN, 5G UPF/GTP-U, security telemetry,
PTP/TSN, and QUIC DDoS cases were all stopped at approximately 60 seconds.
The initial four-support comparison of `Example_250_1_2000` completed and
verified in 6.536 seconds of wall time.
Use two-input AND/XOR gate counts and corresponding levels for GT comparisons.
The current DECPLA objective prioritizes AIG AND count; report that separately
when evaluating changes to the implementation.
GT and DECPLA runtimes use different machines and may use different timing
boundaries. Preserve the C-only implementation and C/C++/namespace portability.

References for returning to this discussion:

- [GT benchmark results](https://www.gtsynt.com/benchmarks.html).
- [GT support and implementation-size study](https://www.gtsynt.com/implementation-size-pdbfs.html).
- [GT care-domain synthesis description](https://www.gtsynt.com/design-from-semantics.html).
