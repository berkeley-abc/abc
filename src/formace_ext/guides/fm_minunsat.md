# Minimum UNSAT for DIMACS CNF

`fm_minunsat` computes an exact minimum-cardinality UNSAT subset directly
from a DIMACS CNF file. It uses the in-process ForMACE/CaDiCaL grouped-CNF
API; converting the CNF to an AIG is unnecessary.

## Clause-level use

From the ABC fork root:

```bash
./abc -c "fm_minunsat input.cnf"
```

Without a group file, every clause is an optional unit-cost group. The result
therefore minimizes the number of CNF clauses. Clause IDs in
`selected_clauses` are one-based DIMACS clause positions.

Example output:

```text
fm_minunsat: status=UNSAT mode=clauses vars=2 clauses=4 hard=0 candidates=4 minimum=2 backend=cadical-2.2.0
selected_clauses=1 2
```

If the complete CNF is SAT, there is no UNSAT subset and the command reports
`status=SAT`.

## Hard clauses and multi-clause groups

Use `-g` when some clauses are mandatory or one selectable feature expands to
several CNF clauses:

```bash
./abc -c "fm_minunsat -g input.groups input.cnf"
```

The group file contains one group per nonempty, non-comment line. Entries are
space-separated, one-based CNF clause IDs:

```text
c The first data line is always hard/background.
1 2 3
4 5
6
7 8 9
```

- The first data line lists hard clauses. They are active in every SAT query
  and do not count toward `minimum`.
- Each later line is one optional unit-cost group. `selected_groups=1` means
  the first optional line (`4 5` above), not CNF clause 1.
- Every CNF clause must occur exactly once. Duplicate, missing, or
  out-of-range IDs are rejected.
- A line containing only `0` represents an empty group. This is mainly useful
  as the first line when grouped input has no hard clauses.
- Lines beginning with `c` or `#` are comments.

If the hard clauses alone are UNSAT, the exact answer is zero and the command
prints an empty `selected_groups=` line.

## Search controls

```text
-C num   conflict limit for each SAT query
-T num   total wall-clock deadline in seconds
-r       use the first failed-assumption core directly as the seed upper bound
-u       use all candidates as the seed upper bound
-A name  select a complete experiment configuration
-j       emit one machine-readable JSON result
-v       print phase statistics
```

The default seed is deletion-minimized before exact search. `-r` skips that
strict seed minimization, which can be faster on some instances. The core is
only an upper bound: the final result is still an exact global minimum.
Likewise, `-u` changes only the starting upper bound, not the meaning of the
answer. `-r` and `-u` are mutually exclusive.

For reproducible ablations, `-A` exposes every exact feature configuration
without rebuilding ABC:

```bash
./abc -c "fm_minunsat -j -A full -g input.groups input.cnf"
./abc -c "fm_minunsat -j -A core-only-seed -g input.groups input.cnf"
./abc -c "fm_minunsat -j -A no-mus-seed -g input.groups input.cnf"
```

The supported names are `full`, `no-core-shrink`, `no-mus-seed`,
`core-only-seed`, `no-model-absorb`, `no-mss-growth`, `linear-map-bounds`, and
`default-cadical`. The additional solver-only names are
`cadical-preprocessing`, `cadical-no-ilb`, `cadical-default-phases`,
`cadical-preprocessing-no-ilb`, `cadical-preprocessing-default-phases`, and
`cadical-no-ilb-default-phases`. Together with `full` and `default-cadical`,
they form the complete eight-way composition matrix for preprocessing, ILB,
and stable-only search. JSON includes the effective feature switches,
upper-bound strategy, selected groups, exact cardinality, phase times, and
solve counters.

The optimization is unit-weighted by optional group. For a different cost
model, encode the desired selectable units as groups or use the C API for a
specialized consumer.
