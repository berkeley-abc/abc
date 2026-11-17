# SCMap standard-cell mapping

`&scmap` maps the current GIA into the loaded standard-cell library using
rise/fall seed construction and bounded shared-cover refinement. It is a
separate command; `&nf`, `map`, and their defaults are unchanged.

```text
read_lib -G 250 -a cells.lib
read design.aig
strash
&get
&scmap
&put
stime -c
```

`-q` enables quality seed selection and electrical window search. `-L N`
adds up to N full-flow candidate evaluations and implies `-q`; zero disables
lookahead. `-v` prints statistics, `-w` prints additional detail, and `-h`
shows usage. The command requires Liberty timing
information and an unboxed GIA without explicit arrival-time constraints.
It accepts choice graphs; alternatives contribute cuts at their representatives.
Quality and lookahead additionally require a combinational GIA with at least
one output and no explicit input or output timing constraints.

## Delay target

`-D <delay>` specifies a positive delay target in picoseconds; decimal values
are accepted. For example, `&scmap -q -L 64 -D 1200` searches for lower area
under a 1200 ps target. Once a cover meets the target, selection prioritizes
area rather than additional delay reduction. Before feasibility, selection
prioritizes lower delay. Omitting `-D` preserves the existing objectives.

In normal mode the constraint uses SCMap's electrical timing model. With
`-q` or `-L`, seed selection and window acceptance use the fixed private-copy
MFS/buffering/sizing flow described below; model predictions only screen the
window candidates. The requested target is calibrated to the model using
the selected seed's measured delay, and also guides seed construction.
The two relaxed seeds remain unconstrained to preserve their diversity.
Area recovery retains the requested target instead of
tightening it to every newly achieved delay. The returned network is still
unsized. Its raw `stime` result need not equal the evaluated downstream delay.

Quality mode also runs the complete corresponding search without `-D` and
retains it as a candidate. This adds search cost, but prevents a targeted
result from being both larger and slower at the evaluated endpoint. If the
untargeted result meets the target, the selected result also meets it and
has no greater area. Lookahead switches to area-ranked roots when an accepted
move first reaches the target. These guarantees do not apply to arbitrary
later optimization or to normal, model-only mode.

As with `&nf`, an unattainable target does not make mapping fail: SCMap returns
the best cover it found and prints a warning when the target is missed. This
is a heuristic target, not a guarantee for arbitrary postprocessing or
OpenROAD. Recheck timing after the complete intended flow.

## Reproducing the ABC evaluation

Build with `make -j4` (add `ABC_USE_NO_READLINE=1` if readline is unavailable).
Run scripts with `./abc -s -f run.abc`; `-s` avoids user startup aliases.
The paper uses the 20 EPFL combinational AIGs and three libraries: ASAP7 RVT FF,
Nangate45, and SKY130HD. Use the same input AIG and Liberty files for every
mapper. Library corners, excluded cells, and input preprocessing affect QoR;
substituting another library revision does not reproduce the exact tables.
Benchmark and Liberty files are external to this source distribution.

For Nangate45 or SKY130HD, create `library.abc` containing
`read_lib -G 250 -a /path/to/cells.lib`. For the evaluated ASAP7 library, load
these files in order from its NLDM directory:

```text
read_lib -G 250 -a -X "*x1p*_ASAP7*" -X "*xp*_ASAP7*" -X "SDF*" -X "ICG*" -w asap7sc7p5t_AO_RVT_FF_nldm_211120.lib.gz
read_lib -G 250 -a -X "*x1p*_ASAP7*" -X "*xp*_ASAP7*" -X "SDF*" -X "ICG*" -m -w asap7sc7p5t_INVBUF_RVT_FF_nldm_220122.lib.gz
read_lib -G 250 -a -X "*x1p*_ASAP7*" -X "*xp*_ASAP7*" -X "SDF*" -X "ICG*" -m -w asap7sc7p5t_OA_RVT_FF_nldm_211120.lib.gz
read_lib -G 250 -a -X "*x1p*_ASAP7*" -X "*xp*_ASAP7*" -X "SDF*" -X "ICG*" -m -w asap7sc7p5t_SIMPLE_RVT_FF_nldm_211120.lib.gz
read_lib -G 250 -a -X "*x1p*_ASAP7*" -X "*xp*_ASAP7*" -X "SDF*" -X "ICG*" -m -w asap7sc7p5t_SEQ_RVT_FF_nldm_220123.lib
```

Use absolute paths as needed. The first read initializes the library; `-m`
merges each subsequent part. Keep this setup identical for SCMap and gain NF.
The following `run.abc` records the three independent endpoints for one input:

```text
source library.abc
read design.aig
strash
&get
&scmap
&put
write_blif mapped.blif
topo
echo MAPPING
stime -c

read_blif mapped.blif
topo
upsize -c
dnsize -c
write_blif sized.blif
echo SIZING_ONLY
stime -c

read_blif mapped.blif
topo
buffer -c
topo
stime -c
upsize -c
dnsize -c
write_blif buffered_sized.blif
echo BUFFERED_SIZED
stime -c
```

For gain NF, replace only `&scmap` with `&nf`. Use a separate output directory
for each design/library/mapper. Both downstream branches restart from
`mapped.blif`; do not buffer the sizing-only result. `stime -c` reports area,
delay, and gate count. Check equivalence against the input with, for example,
`cec -n design.aig buffered_sized.blif` after loading the same library.
Here `-n` matches ports by order, since GIA export can rename them.
For preprocessed-input studies, supply the identical saved preprocessed input
to each mapper; the script above is the raw-AIG experiment.

Report per-design ratios to gain NF and their geometric mean over matched
20-design cohorts, separately for each library and endpoint. Measure CPU with
a process CPU clock around the mapper and downstream stages; report library
loading separately and exclude CEC from flow CPU. ABC's `time` output is not a
portable process-CPU measurement. An external process timer includes startup,
library parsing, and I/O and should be labeled accordingly. Use the same
compiler/build, host, and measurement boundaries for every mapper.

## Algorithm

1. Enumerate six-input priority cuts, retaining area-efficient and shallow
   alternatives. Construct two rise/fall covers with complementary fixed arc
   costs: gain-scaled transition costs and common-load family-average costs.
   Each seed uses four global construction rounds and bounded exact shared-area
   recovery. Evaluate both complete covers with the electrical model; select
   the least-delay seed within the first seed's logic area.
2. Fit each cell's NLDM arc on its own sample grid. Delay is affine in load and
   input slew, and output slew is linear in load. Family-average sink
   capacitances account for upstream loading. Precompute merged load responses
   over direct drive, physical sizes, and virtual buffer realizations; retain
   the associated rise/fall responses. A fixed unit-delay component regularizes
   the model. These virtual realizations guide selection, not netlist emission.
3. Refine the selected cover using broad inexpensive repair, two bounded delay
   rounds, and area recovery. Shortlist ordinary critical-root replacements and
   moves that reduce the load on critical drivers. Exact shared references
   account for implementations activated or removed by a replacement. Focused
   trials propagate changed arrivals, slews, and loads to affected outputs;
   lazy required bounds reject losing trials. Screening tails guide proposals,
   while propagated output timing decides acceptance.

The default mapper uses only its internal electrical model. Without `-D`, quality mode
refines six SCMap seeds and compares private copies after
`mfsmap -e -R 2 -N 500 -C 1000 -M 2000 -I 10 -O 10` followed by
`buffer -c; topo; stime -c; upsize -c; dnsize -c`. It selects a lower
area-delay product with a 5% guard on each metric, anchored to the first
refined cover, not compounded across selections. In addition to the original
G and C seeds, it tries a G seed with gain 4, a C seed with common load 4 times
mean input capacitance, and G/C seeds with 5% relaxed refinement targets.
It does not select NF or NF3 covers. Window search uses
transition-specific family capacitances, slack-based root ranking, and output
timing pressure. Timing moves may spend 2% mapped area; area recovery holds
the achieved delay. Checkpoints at phase boundaries and at 0.5%, 1%, 1.5%,
and 2% cumulative added mapped area retain the lowest realized area-delay
product. Cumulative additions do not subtract intervening area savings.
The search continues from its current cover, while the retained checkpoint
must not increase final delay or exceed 2% final area growth relative to the
window input. The unchanged input is always available as a fallback.

Lookahead prescreens candidates electrically and runs the fixed downstream
flow on at most two candidates per root. An accepted move must improve delay
by at least 0.3%, or reduce area by at least 0.3% without increasing delay.
It allows at most 1% final area growth relative to its input (the result of the
preceding window stage, not the original seed). Failed optional
refinement retains the preceding valid mapping with a warning.
Already measured seed and checkpoint metrics are reused within the same call
when the cover and downstream flow are unchanged. Detailed (`-w`) lookahead records
both electrical predictions and realized changes for calibration; predictions
rank candidates but do not by themselves establish realized improvement.

All modes emit an ordinary unsized mapped network. Private-copy evaluation
does not replace the frame network or commit its physical buffers. Subsequent
`mfsmap`, `buffer`, `upsize`, and `dnsize` remain separate operations. The
realized bounds apply only to the stated fixed flow and library, not arbitrary
postprocessing or place and route; evaluate the complete intended flow.

## Implementation

- `src/aig/gia/giaScmap.c`: cut enumeration, library fitting, merged responses,
  shared-reference/load transactions, and incremental timing.
- `src/aig/gia/giaScmapSeed.h`: paired seed construction and seed area recovery.
- `src/aig/gia/giaScmapRefine.h`: broad repair, candidate screening, bounded
  refinement, output-score caching, and trial snapshots.
- `src/aig/gia/giaScmapQuality.h`: private-copy seed evaluation and the window
  electrical model, included by `giaScmap.c`.
- `src/aig/gia/giaScmapWindow.h`: window search and full-flow lookahead,
  included by `giaNf3.c` to share its candidate generation and reference counts.
- `src/aig/gia/giaScmapInt.h`: the private interface between these units.
- `src/aig/gia/giaScmap.h`: default, quality, lookahead, and delay-target entry points.
- `src/base/abcc/abcMapCell.c`: command registration and argument checks.

Private implementation functions have translation-unit scope except for the
internal interface in `giaScmapInt.h`. Floating-point multiply-add contraction
is disabled locally in `giaScmap.c`: separately rounded costs preserve near-tied
search decisions across builds. No global compiler options or stock commands
are changed. Optional `SCM_DF_VERIFY` and `SCM_DF_ROUND_VERIFY`
compile-time checks compare incremental timing with independent full traversals;
they are diagnostics, not selection policies.

## Regression check

Put the library-loading commands in a text file, then run:

```sh
python3 test/scmap.py --abc ./abc --library-commands library.abc
```

This checks constants, complements, shared logic, repeated outputs, choice
construction, repeated invocation, deterministic output, and equivalence.
Library files and benchmark data are supplied externally.
