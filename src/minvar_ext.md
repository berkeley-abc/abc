# Minvar and Hybrid Interpolation Extension

## Purpose

Explore two interpolation modes for ABC when the input is an UNSAT pair of
circuits or formulas:

- `minvar`: search for a minimum sufficient set of shared variables before
  interpolation.
- `hybrid`: obtain a normal interpolant first, then search only among the
  variables used by that interpolant.

The extension should preserve the usual interpolation result and make the
tradeoff between runtime and shared-variable count visible to the user.

## Starting Point: ABC Interpolation

ABC already has an `inter` command for two networks representing an onset and
an offset. Internally, ABC converts the circuits to CNF, connects matching
inputs, solves the combined problem, and derives a proof-based interpolant as
an ABC network.

This existing path should be treated as the baseline first. It will help us
understand the expected circuit interface, variable naming, interpolant
orientation, output format, and correctness checks.

ABC's public circuit interpolation path currently regards all corresponding
circuit inputs as shared. The minvar and hybrid modes need a more deliberate
partition: selected boundary variables remain shared, while other variables
become private to one side.

The `inter -r` relation option should be examined separately. It may be useful,
but it should not automatically be considered equivalent to our relative
interpolation problem.

## ABC `inter` Smoke-Test Notes

Observed command shape:

```text
inter [-r -v] <onset.blif> <offset.blif>
```

The command also supports one-file and zero-file forms:

- One file: current network is the onset, the file is the offset.
- Zero files: current network is the onset, and ABC complements it to form the
  offset.

Important input behavior from the code and small tests:

- The inputs are ABC networks, normally BLIF for this command, not raw CNF.
- The two networks are read with ABC's normal IO path and strashed before
  interpolation.
- The public command requires the same number of outputs. Single-output
  interpolation also requires the same number of primary inputs.
- PI names are not checked by the interpolation call; corresponding PIs are
  connected by order. For a ForMACE extension, the A/B boundary order should
  be made explicit instead of relying on incidental file order.
- The onset and offset should be disjoint when their outputs are asserted. If
  the combined SAT problem is satisfiable, ABC reports that interpolation has
  failed.
- For multi-output networks, ABC processes each output cone separately and
  appends the resulting interpolants.

Small successful test:

```text
A/onset  = x & y
B/offset = !x | !y
result   = x & y
```

ABC verified the result with its suggested `miter -i ...; iprove` checks for
both `A => I` and `I => !B`.

One edge case appeared in a tiny one-input example:

```text
A/onset  = x
B/offset = !x
```

This can make the instance UNSAT while ABC is still adding equality clauses
between corresponding PIs. The current ABC path asserts in that clause-add
case instead of returning a clean interpolant. This is not necessarily a
problem for normal examples, but an integrated extension should avoid or
harden this path for degenerate reduced partitions.

The `-r` option adds an extra input named `New` and computes a relation-style
interpolant. It is useful to understand, but it should remain separate from
our `minvar` and `hybrid` meaning unless we later prove the objectives match.

Internal location to remember:

- Command wrapper: `src/base/abci/abc.c`, `Abc_CommandInter`.
- Network wrapper: `src/base/abci/abcDar.c`, `Abc_NtkInter` and
  `Abc_NtkInterOne`.
- AIG/CNF/proof path: `src/aig/aig/aigInter.c`, `Aig_ManInter`.
- The selected shared-variable list is currently `vVarsAB`, populated with
  every corresponding CI. This is the likely low-level hook if we want an
  ABC-native selected-variable interpolation path.

## Conceptual Workflow

1. Define the A/B problem contract, including circuit format, input naming,
   shared boundary variables, private variables, output convention, and the
   meaning of a valid interpolant.
2. Establish a small ABC-only baseline using the existing interpolation
   command.
3. Build a paired CNF representation that preserves variable identity and
   records the equality groups connecting the two sides.
4. Use CAMUS/MUS processing to identify a sufficient set of equality groups.
5. Reconstruct the reduced A/B partition and compute the final interpolant.
6. Expose `minvar` and `hybrid` as extension-level choices after the data flow
   is stable.
7. Check correctness, variable support, runtime, and fallback behavior on
   small examples before using larger circuits.

## Mode Ideas

### Minvar

Search over all candidate shared variables. Select a minimum-cardinality set
that keeps the combined A/B problem UNSAT, then interpolate using only that
shared vocabulary.

This is the stronger optimization mode, but it may be expensive because the
MUS/MCS search can dominate the total runtime.

### Hybrid

First compute a baseline interpolant using the ordinary interpolation path.
Use its support as the candidate set for the MUS search, then interpolate
again with the reduced partition.

This should usually be cheaper than full minvar search. The baseline support
may not contain the globally best solution, however, so the mode needs a
clear fallback policy when the restricted search cannot preserve UNSAT.

## CAMUS Role

CAMUS is a MUS/MCS optimization backend, not the interpolant generator. The
first version should use its existing command-line tools and file formats,
with a small orchestration layer responsible for preparing inputs and reading
the selected groups.

Direct changes to CAMUS should only be considered later if process overhead,
incremental solving, or tighter integration becomes a real bottleneck.

## Implementation Direction

There are two likely interpolation backends for the reduced partition:

- Adapt ABC's internal proof/interpolation interfaces so the selected shared
  variables are passed explicitly.
- Use the existing external interpolation workflow after ABC exports the
  required paired CNF files.

The ABC-native route is attractive for a self-contained extension, but it
requires careful handling of CNF variable maps, clause ownership, proof data,
and the selected shared-variable list. The external route is easier to
validate against the existing minimum-interpolation project and may be the
best prototype boundary.

## Open Questions

- Are the inputs two combinational circuits, BMC partitions, or both?
- Should the extension accept circuits directly, CNF files, or an intermediate
  representation?
- Should the final interpolant be returned as an ABC network, written to a
  file, or both?
- Is the optimization objective the number of variables, a weighted cost, or
  eventually circuit size as well?
- Should hybrid fall back to the baseline interpolant or escalate to full
  minvar search?
- Can ABC's internal interpolation API be reused without modifying upstream
  ABC source files?

## Initial Success Criteria

Before adding substantial code, we should be able to demonstrate that:

- ABC produces and validates a normal interpolant for a small circuit pair.
- The paired CNF and equality-group mapping are unambiguous.
- CAMUS returns a selected group set that preserves UNSAT.
- The reduced partition contains no unintended shared variables.
- Both modes report their selected support and fall back cleanly when needed.

This document is a planning boundary. Implementation should remain inside
`src/formace_ext/` whenever possible, with each substantive change recorded
in `FORMACE_CHANGELOG.md`.
