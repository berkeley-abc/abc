# Acyclic word-level partitioning

The `parter` package splits local word-level workloads while preserving an
acyclic hierarchy. Production code is native C and has no external runtime
dependency. It also builds as C++ and inside ABC's C++ namespace.

## Acknowledgments and algorithmic references

This implementation is inspired by prior work on balanced bipartitioning,
FM refinement, and multilevel acyclic partitioning:

- C. M. Fiduccia and R. M. Mattheyses,
  [A Linear-Time Heuristic for Improving Network Partitions](https://doi.org/10.1109/DAC.1982.1585498),
  DAC 1982, pp. 175-181: single-vertex moves, incremental gains, move locking,
  and best-prefix rollback.
- The [UMpack FMPart and MLPart packages](https://github.com/i-markov/UMpack-32-June2026):
  we acknowledge Andrew E. Caldwell, Andrew B. Kahng, and Igor L. Markov,
  named as authors in the MLPart driver and credited in both packages'
  source headers. Their work provided algorithmic references for two-way
  hypergraph partitioning, seeded starts, and multilevel coarsening and
  refinement. The source notices also credit Saurabh N. Adya, Jarrod A. Roy,
  and David A. Papa for subsequent University of Michigan work. See the
  [MLPart author banner](https://github.com/i-markov/UMpack-32-June2026/blob/main/MLPart/MLPartTest2.cxx)
  and the [FMPart](https://github.com/i-markov/UMpack-32-June2026/blob/main/FMPart/fmPart.cxx)
  and [MLPart](https://github.com/i-markov/UMpack-32-June2026/blob/main/MLPart/mlPart.cxx)
  source credits.
- Julien Herrmann et al.,
  [Multilevel Algorithms for Acyclic Partitioning of Directed Acyclic Graphs](https://doi.org/10.1137/18M1176865),
  2019, and Orlando Moreira, Merten Popp, and Christian Schulz,
  [Graph Partitioning with Acyclicity Constraints](https://arxiv.org/abs/1704.00705),
  2017: references for preserving an acyclic quotient during partitioning.

ABC implements these ideas with indexed arrays, a weighted hypernet-cut
objective, and directed move constraints for SN. The references are
algorithmic inspiration, not linked dependencies. In particular, the
selection trees used here do not claim the original FM algorithm's
linear-time pass bound.

## Indexed graph

Objects and nets have separate integer ID spaces. Object weights, net weights,
drivers, and connectivity live in parallel arrays. Input nets, output nets,
and net consumers use contiguous spans with end offsets. The explicit driver
array is authoritative, including when a single-output object's original net
ID happens to equal its object ID.

Graph construction copies and validates its inputs, sorts and deduplicates
consumers, and removes internal self-dependencies. Contraction preserves net
IDs and sums object weights. Empty net slots are allowed. External drivers use
`PRT_NONE`. All weights must be finite and nonnegative.

Topological ordering and iterative strongly connected component discovery use
stable ID ordering. Graph connectivity stays immutable during refinement.
Failing constructors and analyses do not publish partial results.

## SN feasibility preview

`@partition -p [-M name_or_mID | -a] [-A cap] [-D flop_area] [-R sram_area] [-v]`
examines the current top and its reachable masters, or all definitions with
`-a`. The default local area cap is 100000 AND equivalents, with eight per
flop bit and one half per SRAM bit. Child contents are excluded. Unknown
masters are reported separately. Preview never changes the design.

The adapter groups owner/FAN objects, register and loop pairs, and memories
with all their ports before finding SCCs over every data and control fanin.
Each SCC is indivisible without introducing new loop boundaries. The report
identifies the largest mandatory group, largest SCC, and cost above the cap.
PI nets keep their original signal IDs; constants are copied locally and do
not contribute to cut cost.

## Transactional extraction

`Prt_SnExtract` accepts hand-assigned part labels. It replaces the selected
master with a wrapper and appends part definitions. Original master IDs,
ordered ports, widths, signedness, state, mapped gates, and repeated uses
survive. Each crossing word signal gets one output port and one input per
consuming part. Constants are reproduced locally. Outputless parts receive
an unused constant output so their instances remain representable in SN.
Unused source constants and their annotations remain in the wrapper.
Generated interface and instance names avoid all existing source names.

Assignments must keep mandatory groups together and induce an acyclic
quotient. Extraction checks the complete design on a private clone and
publishes only on success. `Prt_SnExtractMapped` additionally returns exact
object correspondence, useful when checking state whose traversal order
changes after partitioning. Positional state-boundary comparison alone is
not sufficient in that case.

The command manager retains its explicit top. The binary `.sn` format does
not store that selection: after saving a partitioned design, read it with
`@read -M original_top file.sn`, since appended parts change the last-module
default.

## Acyclic FM refinement

`Prt_Bisect` starts from a seeded topological prefix; `Prt_Refine` accepts an
existing acyclic two-way assignment. Two indexed selection trees ordered by fixed object weight, separate directed
movability counters, move locking, and best-prefix rollback refine the
width-weighted hypernet cut. A net is charged once when its distinct driver
and consumers span both parts. External-source nets use their consumers.
Gain updates skip a net when its pre-move leaving-side count exceeds two and
its joining-side count exceeds one, since
its contribution is zero for every unlocked pin. Selection queries the best
eligible move within the admissible weight prefix of each direction in
logarithmic time, preserving gain and object-ID tie-breaks. Heavy blocked
moves are never repeatedly removed and reinserted.

Moves preserve the direction from part zero to part one. Both parts remain
nonempty. The requested balance tolerance is relative to half the total
weight. If a balanced prefix is unavailable, relaxed mode allows its initial
imbalance but never worsens it; prefixes improve balance first, then cut.
Hard-balance mode fails if the requested bound cannot be met. Zero weights
are valid, and zero passes returns only initialization. Cancellation leaves
caller labels and statistics unchanged.

## Measured size caps

`@partition` applies partitioning by default. `-p` retains the preview mode.
`-A` selects the local cap, `-B` the balance tolerance in percent (10), `-P`
the maximum FM passes (4), `-S` the seed (1), and `-J` the maximum bisections
(1024). Each accepted bisection strictly reduces the original movable-object
membership of its children. An explicit work queue avoids C recursion.

The driver prechecks indivisible SCCs and retains masters with an SCC above
the cap (or fewer than two groups), reporting them separately from unknown
masters. This also applies if recharacterization exposes an indivisible
oversized generated part. Other reachable masters can still be split.
The final measured cap is verified for every selected known master except
these explicitly retained masters.

Before FM, an input-port feasibility bound checks groups with more than
65,535 incoming signals. A signal can become internal only if its driver
joins the group. Fractionally filling the remaining area with driver groups,
ignoring their dependencies, gives an upper bound on how many inputs could
be removed. If even that bound leaves too many inputs, the command rejects
before search. This bound uses the same estimated object areas as FM; it is
not a complete port-constrained partitioner. Exact input/output limits are
still checked during extraction.

The driver clones the design once. Each extraction validates the changed
wrapper and appended parts, and generated-master characterization validates
only that master. Initial and final whole-design validation and final
characterization guard publication. The independent public extraction and
single-master characterization APIs retain their full validation and
ownership contracts. Only the explicitly private batch APIs require a
previously checked design and discarding the whole private design on failure.
First-owner AIG weights can increase after splitting when sharing is lost;
the command reports the initial and final summed local area. Unknown and indivisible masters
remain unchanged and are counted separately. Failure, cancellation, and exhausted
budgets publish no partial hierarchy. Generated input/output bit counts are
cumulative over all bisections, including interfaces of intermediate wrappers.

`Prt_SnPartition` provides the same transaction to native callers. Its
optional cancellation callback and log stream have no global state.
## Optional multilevel refinement

`-C levels` enables up to 16 coarsening levels; the default is zero. Each
level matches vertices at equal strict DAG rank using shared nets, or matches
a vertex with its sole distinct successor. These are separate contraction
batches. The quotient is independently checked for acyclicity; original net
IDs and word weights survive. Matching bounds high-fanout candidate probes
and retains a level only if it removes at least one fifth of the vertices.

After bisection, every uncoarsening level runs FM. The flat result remains the
baseline: the multilevel candidate is retained only when cut decreases and
balance excess does not increase. This guarantee applies to that bisection,
not to the entire recursive partition tree or its recharacterized area.
`Prt_BisectMulti` exposes the option.

## Placement integration

The partitioner has no dependency on the planner or placer. When combined
with the placement branch, run characterization and floorplanning again
on the new hierarchy before placement. A failed partition preserves any
installed placement in the original design. Successful changes invalidate
the affected copied geometry through SN's existing mutation notifications.
Manual child outlines and pin constraints may need updating after a split.
