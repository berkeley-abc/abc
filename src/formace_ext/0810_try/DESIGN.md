# Design: MinUNSAT-guided ECO patch reconstruction

## Question

Can the existing ForMACE MinUNSAT/CAMUS method replace the patch-function
construction portion of ABC `runeco`?

## Prototype boundary

ABC's current `runeco` implementation first selects a common set of candidate
divisors and then constructs each target function through SAT cube enumeration.
This experiment preserves `runeco`'s valid patch and candidate interface, but
reconstructs every patch output independently with `fm_inter -m`:

1. Extract one output cone from `runeco`'s `patch.v` while preserving the full
   patch input interface.
2. Let that Boolean function be the onset and its complement be the offset.
3. The equality of each corresponding patch input is one guarded MinUNSAT
   group. A minimum UNSAT group set is therefore a minimum-cardinality set of
   inputs sufficient to distinguish the function's onset from its offset.
4. Use ABC proof interpolation with exactly that selected shared vocabulary to
   reconstruct the output function.
5. Combine the independently reconstructed outputs into a replacement patch,
   insert it into the original targeted G1, and prove equivalence to R2.

For a Boolean function `f(d)`, the paired problem is:

```text
f(d_A) = 1
f(d_B) = 0
d_A[i] = d_B[i]  for each enabled input group i
```

All groups enabled makes the formula UNSAT. A minimum-cardinality UNSAT set is
a minimum functional support for `f` within the candidate `runeco` divisors.
The interpolant over that support is a valid replacement for `f` on all input
assignments.

## What this proves and what it does not

If final CEC succeeds, the experiment proves that MinUNSAT-selected support and
proof interpolation can replace cube-enumerated patch output functions for the
tested case.

This first prototype does **not** replace `runeco`'s earlier divisor discovery,
nor does it search all G1 nodes globally. Its minimum guarantee is per output
and relative to the candidate inputs already present in `patch.v`. Optimizing
the union of supports across all patch outputs is a different weighted/grouped
objective and is left as a follow-up.

## Isolation and rollback

All new code, reports, and generated results live below `0810_try`. No upstream
ABC source file is modified by this experiment. The work is developed on Git
branch `experiment/0810-minunsat-eco`, so after committing this directory the
experiment can be hidden with:

```sh
git switch master
```

The pre-existing uncommitted ForMACE changes are deliberately not staged or
committed by this experiment.
