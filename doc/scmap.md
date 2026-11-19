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

Only diagnostic options are exposed: `-v` prints statistics, `-w` prints
additional detail, and `-h` shows usage. Options affect diagnostics only. The command requires Liberty timing
information and an unboxed GIA without explicit arrival-time constraints.
It accepts choice graphs; alternatives contribute cuts at their representatives.

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

The mapper emits an ordinary mapped network. It never invokes downstream STA,
buffering, or sizing to select a cover. Subsequent `buffer`, `upsize`, and
`dnsize` remain independent ABC operations. The internal surrogate does not
impose a physical timing guarantee; evaluate the complete intended flow.

## Implementation

- `src/aig/gia/giaScmap.c`: cut enumeration, library fitting, merged responses,
  shared-reference/load transactions, and incremental timing.
- `src/aig/gia/giaScmapSeed.h`: paired seed construction and seed area recovery.
- `src/aig/gia/giaScmapRefine.h`: broad repair, candidate screening, bounded
  refinement, output-score caching, and trial snapshots.
- `src/aig/gia/giaScmap.h`: the single public mapping entry point.
- `src/base/abcc/abcMapCell.c`: command registration and argument checks.

Private headers are included only by `giaScmap.c`. Internal functions have
translation-unit scope. Floating-point multiply-add contraction is disabled
locally in this compilation unit: separately rounded costs preserve near-tied
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
