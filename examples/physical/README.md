# Placement-aware synthesis: AGR and PA

This integration retains the final adaptive geometric restructuring (AGR) flow and the
prior placement-aware (PA) implementation as separate ABC extensions. Ordinary
ABC `rewrite`, `refactor`, `resub`, placement, and mapping implementations are
unchanged. Both extensions are registered by `src/base/main/mainInit.c`.

## Build and run

Use ABC's normal Make build, or CMake:

```sh
make -j4
# Alternatively:
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DABC_SKIP_TESTS=ON
cmake --build build -j4
```

From the repository root, supply your combinational AIG and Liberty library:

```text
read design.aig
strash
read_lib cells.lib
agr
write_aiger agr.aig
```

`agr.abc` is only a convenience script containing `agr`. The built-in guidance
step is 0.28 bin widths; no option is needed to reproduce that setting. For PA2,
use the direct two-round commands in [REPRODUCE.md](REPRODUCE.md), also provided
in `pa2.abc`. Both recipes include placement and synthesis, and neither calls a
technology mapper internally. Map both outputs with the same library and command
sequence. The reproduction runner uses `&get; &nf; &put; stime`. Measure fresh AIG HPWL and mapped
HPWL with a separate `pa_place` on each endpoint; the incremental optimization
coordinates are not a fresh-placement evaluation.

The legacy command `tg` remains an alias for `agr` so saved recipes continue
to work. It invokes the same implementation and parameters.

Use `agr -h` or the individual `pa_* -h` commands for help. `agr` returns a
normalized, structurally hashed AIG ready for ordinary ABC commands, mapping,
or another AGR invocation. No extra `strash` is required after `agr`. An extra
normalization can change AIG serialization order without changing its function.

## Adaptive geometric restructuring

`agr [-s step] [-v]` performs one floating-IO global placement, followed by two
synthesis blocks. Each block runs broad RS, RW, and RF passes followed by up to
four compact RW/RF rounds. There is no intermediate global placement or
mapping-based checkpoint selection. `-s` controls the initial placement step
(default 0.28); it is a sensitivity parameter, not a per-design policy selector.

For a node, remove that node from each incident net's bounding box. Along each
axis, the distance to an interval is zero inside it and the distance to the
nearest endpoint outside it. Tension is the minimum sum of these distances over
the node's position, summed over both axes. It measures incompatible incident
net regions. The implementation evaluates this interval-median expression in
batches, preserving arithmetic order. Root priority also includes half the
fanin tensions for single-fanout fanins.

Structural classes diversify compact selection. Context memory discounts
previously explored unchanged neighborhoods; changed topology or quantized
geometry makes them eligible again. Before each block’s broad RS/RW/RF sequence, the flow freezes a
compact cap of `ceil(4*sqrt(N))`; each compact round also applies the 25% eligible
root limit. The broad RW pass uses ten tension-ranked productivity buckets with
filter 0.25. Compact rounds use ten buckets with filter 0.5: a bucket closes when
its Laplace-smoothed acceptance rate is below that fraction of the overall
rate. Complete-round yield checks can end a compact block early.

Candidates include bounded four-input library alternatives, factored forms,
and geometry-expanded cuts. Ordered truth tables and live boundaries establish
Boolean validity. Candidate evaluation reconstructs the affected hypergraph,
places new nodes with the density-aware PA evaluator, and accounts for actual
structural reuse. The final policy does not permit net node growth. Its score
combines nodes saved, normalized local HPWL gain (weight 0.25), and the paper
root-slack timing term (weight 0.5). RW/RF use bounded timing; RS maintains the
full dependencies required by its nonlocal divisors. Only accepted edits update
the graph and placement. Cached candidate construction never replaces a live
physical or legality check.

## PA reproduction

PA keeps its own placement manager and commands: `pa_place`, `pa_stats`,
`pa_time`, `pa_rw`, `pa_rf`, `pa_rs`, and `pa_strash`. The `pa2.abc` recipe is two
RS→RW→RF rounds: `pa_rs -K 8 -N 2; pa_rw; pa_rf`, repeated twice. The
paper timing score is always enabled, with bounded RW/RF updates and strict RS
dependencies. Only native operator controls and PA's explicit `-c` cluster mode
remain. This recipe is separate from AGR's search policy.

Mapped feedback is also retained. After placing a mapped network with
`pa_place`, `pa_strash` transfers mapped-cell centers to its AIG nodes. The
`-c` option on subsequent PA synthesis commands uses those inherited clusters.
Plain `strash` does not perform that placement transfer. Use identical mapping,
placement, and feedback counts when comparing flows.

## Source guide

| Component | Source |
|---|---|
| AGR command, placement lifecycle and density grid | `src/ext-agr/agrPlace.cpp` |
| Broad operator passes and RW productivity filter | `agrBroad.h`, `agrRewrite.c` |
| Compact search, cuts and candidate selection | `agrCompact.h`, `agrGeometryCut.h`, `agrInit.cpp` |
| Tension, structural invalidation and context memory | `agrTensionKernel.h`, `agrScan.h`, `agrHistory.h` |
| Truth/care checks and divisor/factor helpers | `agrCare.h`, `agrGlobalCare.h`, `agrDivisors.h`, `agrDsd.h` |
| Live candidate placement, scoring and commitment | `agrEvaluate.cpp`, `agrAig.cpp` |
| Native-generator RW/RF/RS integration | `agrRewrite.c`, `agrRewriteEval.c`, `agrRefactor.c`, `agrResub.c` |
| Spectral density solver and scratch storage | `agrDensity.cpp`, `agrSpeed.h` |
| Independent PA implementation | `src/ext-pa/` |

The AGR library data is derived from ABC's rewriting forest; original ABC author
and license notices are retained. Experimental commands, environment-selected
policies, mapping-guided selection, placement-trajectory variants, and local LP
variants are excluded from the integration. Benchmark outputs and manuscript
artifacts are maintained separately from the source tree.

## Validation

For all-design frontend measurements and CPU-budgeted native ABC, use
[reproduce.py](reproduce.py). [REPRODUCE.md](REPRODUCE.md) documents inputs,
direct commands, timing boundaries, cycle replay, failure handling, and outputs.
The driver runs serially and never launches OpenROAD.

Run `python3 test/physical/regression.py --abc ./abc` for equivalence, repeated
use, command validation, mapping/unmapping, and native-command handoff checks.
An optional `--reference` executable checks that native synthesis produces the
same AIG payload as an unmodified ABC build. See `VALIDATION.md` for the recorded
integration checks and the endpoint-reproduction scope.
