# `fm_eco`: ECO patch construction with interpolation

`fm_eco` reuses ABC's DAC'18 `runeco` implementation for structural pruning,
candidate divisors, the ECO miter, target ordering, support selection, patch
emission, and final equivalence checking. Its difference is the
patch-function builder: `runeco` enumerates an SOP, while `fm_eco` derives a
Craig interpolant and synthesizes its AIG/GIA.

## Usage

```text
fm_eco [-T seconds] [-o out.v] [-acrimuvwh] F.v G.v [weights.txt]
```

Important options:

- `-u`: assign unit weight to every eligible positive-weight divisor;
- `-a`: keep `sat_solver_minimize_assumptions()` but skip the iterative
  `Acb_FindSupport()` improvement phase;
- `-m`: use exact grouped MinUNSAT support selection;
- without `-a` or `-m`: use ABC's original support heuristic;
- `-c`: check target-set feasibility before constructing functions;
- `-i`: restrict candidate support to primary inputs;
- `-w`: print proof details and audit minimum support when the remaining
  candidate count is at most 16;
- `-o`: select the integrated output filename; `patch.v` is also emitted.

This produces the six-method support-selection experiment:

| Command | Support | Function |
|---|---|---|
| `runeco -u -a` | assumption minimization only | SOP |
| `runeco -u` | original | SOP |
| `runeco -u -m` | exact MinUNSAT | SOP |
| `runeco -u -g` | exact common support for fixed target relations | SOP |
| `fm_eco -u -a` | assumption minimization only | ITP |
| `fm_eco -u` | original | ITP |
| `fm_eco -u -m` | exact MinUNSAT | ITP |

`runeco` treats `-a`, `-m`, and `-g` as mutually exclusive. The assumption-only mode is expected to
return a sufficient, subset-minimal support, but it does not perform ABC's
multi-start alternative-support search and has no minimum-cardinality
guarantee.

### Shared fixed-relation mode

`runeco -g` records one two-copy ambiguity relation `B_i` for each target
along a deterministic reference SOP trajectory. It then finds a minimum
support `S` such that every `B_i AND Eq_S` is UNSAT. This is equivalent to

```text
(B_0 OR B_1 OR ... OR B_(k-1)) AND Eq_S
```

being UNSAT. The implementation keeps one persistent guarded SAT manager per
target and a shared implicit minimum-hitting-set search. A SAT candidate is
grown to an MSS; its complement is learned as an MCS clause. All SAT targets
contribute corrections in the same refinement. The map removes dynamic
symmetry by quotienting equal learned-MCS incidence patterns and discarding
patterns dominated by a strict incidence superset; the quotient is rebuilt
after every new MCS, so this does not restrict the exact candidate universe.

Before ordinary refinement, the combined OR oracle greedily produces
pairwise-disjoint MCSes. Their count is a certified support lower bound.
Learned corrections are kept as an inclusion-minimal antichain and later
packed again for stronger certified bounds. At a proven bound, greedy and
bounded local-repair searches may propose a hitting set, but it is accepted
only after it hits every learned MCS and passes every target SAT manager. The
exact reduced map remains the fallback and is constructed lazily only when no
such candidate is found.

After selection, every evolving target relation is checked again with the
common support as mandatory. The command fails instead of silently adding an
input if the fixed support is insufficient, and retains the final miter and
CEC checks.

On Unit14, the current algorithm proved an exact seven-signal support for 12
fixed relations and 1,851 physical candidates. End-to-end time fell from
229.18 to 76.49 seconds. Common CAMUS used 30.40 seconds in exact-map work,
28.70 seconds in MSS/MCS growth, and 0.64 seconds in validation. The current
bottleneck is therefore shared between the size-6-to-7 map proof and roughly
118,000 growth oracle calls; target-validation caching is presently lower
priority.

## Formula

Let `M(n,x)=1` mean that implementation and specification mismatch when the
current target has value `n`. A divisor set `D` is sufficient when

```text
M(0,x0) AND M(1,x1) AND [D(x0)=D(x1)]
```

is UNSAT. The `-m` mode makes each divisor equality a two-clause optional
CAMUS group and calls `Fm_CamusFindMinimumMus()`.

After support selection, `fm_eco` rebuilds a selector-free proof formula:

```text
A(d,x0) = M(0,x0)
B(d,x1) = M(1,x1) AND [d=D(x1)].
```

Only the ordered selected-divisor variables `d` are shared. ABC's proof
interpolator derives `I(d)` with `A => I` and `B => !I`; `I` becomes the
target replacement. Constant A/B partitions produce constant patches without
requesting a zero-boundary proof interpolant.

## Guarantees

For a single target, completed `-m` search proves minimum input cardinality
within ABC's structurally generated candidate window. For multiple targets,
the algorithm processes targets in reverse order and accumulated support is
mandatory. The guarantee is therefore minimum **additional** support for the
current target and evolving miter, not a globally minimum final union.

For completed `runeco -g` search, the result is a global minimum-cardinality
common support for the recorded fixed `B_i` relations. It is not an absolute
minimum over all possible joint choices of patch functions: changing an
earlier function can change later care relations. That stronger problem is a
joint functional-synthesis/QBF/DQBF problem.

Neither mode minimizes interpolant area, gates, proof size, original weighted
cost, or runtime. `-u` is used when comparing support cardinality.

## Verification

Each completed run checks the fully substituted ECO miter and then runs CEC
between the emitted integrated output and `G.v`. The experiment runner performs
a second independent CEC in a new ABC invocation.

Run the focused regression with:

```bash
bash src/formace_ext/tests/fm_eco_test.sh
bash src/formace_ext/tests/fm_runeco_global_test.sh
```
