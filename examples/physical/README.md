# Placement-aware synthesis: AGR and PA

This integration retains the final adaptive geometric restructuring (AGR) flow and the
prior placement-aware (PA) implementation as separate ABC extensions. Ordinary
ABC `rewrite`, `refactor`, `resub`, placement, and mapping implementations are
unchanged. Both extensions are registered by `src/base/main/mainInit.c`.

## Reproduction

- [REPRODUCE.md](REPRODUCE.md): build, inputs, direct AGR/PA commands, CPU-budgeted ABC baseline, fresh endpoint evaluation, and fixed-work replay.
- [FLOW.md](FLOW.md): AGR and PA inside conventional synthesis flows, with CPU-budgeted native controls.
- [VALIDATION.md](VALIDATION.md): validation scope and frontend reference measurements.
- [PA documentation](../../src/ext-pa/README.md): prior-work mapping/unmapping and cluster mode.

The default placement guidance step is 0.28; no option is required. AGR includes
final normalization. The legacy `tg` alias calls the same implementation.
The runners use Python's standard library and do not launch OpenROAD.

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

The AGR library data derives from ABC's rewriting forest. Original author and
license notices are preserved. PA and AGR own separate state and implementations;
native ABC synthesis and mapping commands are unchanged.
