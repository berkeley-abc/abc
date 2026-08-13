# `fm_int`: interpolation model checking

`fm_int` is the ForMACE extension for ABC's interpolation-based model checking
engine.  It uses the existing `int` flow and can select the latch boundary and
an explicit fixed-depth first-query partition.

It is different from ordinary bounded model checking (`bmc` and `&bmc`):
`fm_int` iterates interpolants and may prove an unbounded safety property.

## Input

The current ABC network must be:

- structurally hashed (`strash` it after reading);
- sequential, with at least one latch and primary input;
- free of constraints; and
- a single-property-output safety miter.

The command does not replace the current network.  It updates ABC's normal
proof status, frame count, and counterexample when one is found.

## Usage

```text
fm_int (-o | -m | -y) [-CFSTK num] [-I file] [-L num] [-airtcgvh]
```

```bash
./abc -c "read_blif design.blif; strash; fm_int -m -F 100 -v"
./abc -c "read_blif design.blif; strash; fm_int -y -L 12 -T 60"
./abc -c "read_aiger design.aig; strash; fm_int -m -S 5 -a -F 6 -L 227 -v"
```

- `-o`: original ABC proof interpolation without boundary minimization.  This
  makes the baseline available with the same explicit partition as `-m/-y`.
- `-m`: at every forward interpolation iteration, uses the in-memory
  CaDiCaL-backed CAMUS implicit-hitting-set API to find an exact
  minimum-cardinality set of latch-boundary equality groups.
- `-y`: first derives ABC's baseline interpolant, then searches only the
  latch support of that interpolant using the same exact API. It is
  therefore locally minimum for that support. If the restricted support is not
  enough to keep the current A/B formula UNSAT, it retains the baseline
  interpolant.
- `-L num`: maximum candidates for the exact search, default `16`.  Exceeding
  the limit returns `Property UNDECIDED`; it does not claim a proof or change
  the current network.
- `-C`, `-F`, `-T`, `-K`: ABC conflict, frame, time, and induction-depth
  limits.
- `-S k`: start directly with a suffix containing states `s1` through `sk`.
  With `-F k+1`, this executes exactly one interpolation query.
- `-a`: use `Bad(s1) or ... or Bad(sk)` instead of only `Bad(sk)` in that
  suffix.
- `-I file` and `-i`: select and enable interpolant/invariant dumping.
- `-r`, `-t`, `-c`, `-g`, `-v`: compatible forward-`int` controls for
  rewriting, transition looping, containment-check toggling, SAT bias, and
  verbose output.

`fm_int` deliberately does not expose backward interpolation or the alternate
MiniSat-1.14p engine in this first version.  Their connector arrangement does
not match the forward latch-boundary selection implemented here.

## Semantics

For the fixed first-query command `-S k -F k+1`, the depth convention is `k`
transitions from `s0` through `sk`, and the partition is:

```text
A = I(s0) and T0(s0,i0,s1)
B = T1 .. T(k-1) and Bad(sk)                   # without -a
B = T1 .. T(k-1) and (Bad(s1) or ... Bad(sk)) # with -a
```

ABC prints `Bmc = k+1` for this call because its statistic counts timeframes;
the BMC transition depth remains `k`.

In an `int` step, ABC connects each transition latch input to the matching
initial latch state of the suffix timeframes.  A selected latch retains both
equality clauses and is global to proof interpolation.  An unselected latch
has neither equality clauses nor a global proof variable, making its A and B
copies private.

The proof interpolant is then expanded back to every latch CI before ABC runs
containment and the next iteration.  Unselected latch CIs remain in the
interface but are functionally unused.  This preserves the native `int`
iteration contract while reducing the shared boundary.

An empty selected boundary is valid.  When A and B are already independent and
UNSAT, `fm_int` derives the appropriate constant interpolant instead of asking
ABC's proof interpolator to construct an AIG with zero global variables.

The persistent CaDiCaL implicit-hitting-set manager is used only to choose the boundary. It contains
the fixed per-step CNFs as background and each latch equality pair as one
selector-guarded group. The existing ABC proof-producing solver is then built
once for the chosen groups, so selector variables do not enter the proof.

The proof-producing path remains MiniSat-derived because it provides ABC's
proof store and interpolation data. This is not a remaining CAMUS dependency:
CaDiCaL now handles every `Fm_Camus*` selection query, while the proof solver
serves a separate role after selection.

## Verification

Run the focused regression suite from the repository root:

```bash
bash src/formace_ext/tests/fm_int_smoke.sh
```

It checks baseline `int`, CAMUS minvar and CAMUS-hybrid proof on a two-latch
safe design, the zero-boundary constant case, a frame-1 counterexample, and
the `-L` resource guard. The verbose checks require the CAMUS per-step
selection messages.
