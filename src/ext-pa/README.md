# Placement-aware synthesis (PA)

PA is the traversal-based physical synthesis reference. Its placer, incremental
candidate evaluator and RW/RF/RS copies are isolated here; native ABC commands
are unchanged. Start with [frontend reproduction](../../examples/physical/REPRODUCE.md)
for the build, external inputs, two-round comparison and measurement commands.
The saved paper inputs are already DC2-preprocessed.

## Paper flow

The final commands always use the paper's integrated root-slack timing score.
RW/RF use bounded timing updates; RS keeps strict dependency updates for its
nonlocal divisors. No timing, scoring or extra-candidate policy switches are
needed. Native operator controls and the paper's explicit cluster mode remain.

Starting from `read design.aig; strash; dc2`, load the target Liberty file with
`read_lib library.lib`. Define **P** as this fixed six-command sequence:

```
pa_rs -K 8 -N 2; pa_rw; pa_rf;
pa_rs -K 8 -N 2; pa_rw; pa_rf
```

PA runs `pa_place; P`. PA-unmap first runs PA, then repeats exactly five times:
`&get; &nf; &put; pa_place; pa_strash; P_c`, where **P_c** is **P** with `-c`
added to all six commands. If the input is already DC2-preprocessed, omit the
initial `dc2`. Final evaluation maps the saved optimized AIG using
`&get; &nf; &put; stime; pa_place; pa_stats`. Use the same library and final
placement settings across flows.

## Commands and clustered feedback

`pa_place` creates placement; `pa_stats` reports HPWL/overflow and `pa_time`
reports the structural timing proxy. Run each command with `-h` for its controls.
`pa_rw`, `pa_rf` and `pa_rs` retain native operator controls and add `-c`.
The default minimum node gain for RF/RS is zero, permitting equal-size
positive-score changes. `pa_rs -N 2` permits candidates adding up to two ANDs.

After mapping, `pa_place; pa_strash` transfers cell centers to the AIG and scales
them to its density canvas. Plain `strash` does not transfer coordinates.
Subsequent PA commands with `-c` snap candidate nodes to inherited clusters;
commands without it use ordinary incremental placement. The cluster mode is
reset after each command. Use identical mapping and feedback counts in comparisons.

## Candidate evaluation

Candidates are evaluated virtually before creating ABC objects. Structural
hashing determines actual removal, reuse and gain; all incident nets of moved
reused nodes enter the HPWL delta. Forward median rectangles and reverse point
selection place the candidate, with density choosing points within rectangles.
This placement is optimal for a strict candidate tree and heuristic for a
reconvergent graph; HPWL is measured on the resulting local hypergraph.
Commit checks the realized topology before accepting the predicted delta.

The fixed candidate score is

```
S = node_gain + 0.25 * HPWL_reduction / mean_net_HPWL
  + 0.5 * (Phi(new_logic_slack) - Phi(old_logic_slack)
         + Phi(new_wire_slack)  - Phi(old_wire_slack)
         + Phi(new_fanout_slack) - Phi(old_fanout_slack))
Phi(s) = log1p(s) if s > 0, otherwise s
```

The fanout term is used when a finite boundary slack is available. Its slack
is the minimum over the root's immediate fanouts. The derivative of `Phi` is
`1 / (1 + max(0, s))`, so the score integrates criticality across the entire
slack change without clipping a timing loss. HPWL normalization is fixed at
the start of each command. There are no selectable alternative scores.

Logic arrival adds one per AND; geometric arrival adds Euclidean edge length.
These are separate path maxima, not a cell STA model. The geometric scale is
maximum output wire arrival divided by maximum output logic arrival. Primary
input edges have zero geometric length because this AIG model does not place
I/O pins. Output budgets and the scale stay fixed within a command.

Each pass starts with one timing build. RW/RF use bounded candidate timing and
refresh replacement and boundary arrivals up to their traversal frontier,
while required budgets remain frozen. RS admits nonlocal divisors and therefore
updates every affected dependency and lazily refreshes required values before
use. These are fixed operator-specific choices, not user-selectable efforts.
When levels are maintained, unrestricted RS propagation uses reusable buckets
indexed by structural level; otherwise it uses the dependency worklist.

## Source and validation

- `paPlace.cpp`, `paSpectral.cpp`: global placement and density.
- `paRewrite.cpp`, `paAig.cpp`: virtual candidates, local placement and timing.
- `paAbc*.c`, `paRwrEva.c`: isolated operator generation and traversal.
- `paStrash.c`: mapped-cell coordinate transfer.
- `paCommands.c`, `paInit.cpp`: command interface and lifecycle.

[Validation instructions](../../examples/physical/VALIDATION.md) cover the
regression and reproduction checks. An optional `ABC_PA_ENABLE_AUDIT` build
supports `tests/regression.py --audit` for additional internal consistency checks.
Use the ordinary Release build for runtime comparisons. Placement state is
serial and external to ABC objects. A valid empty state is retained when an
optimization removes all internal nodes.
