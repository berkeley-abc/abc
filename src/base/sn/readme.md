# Simple Netlist in ABC

This directory contains the Slang-independent Simple Netlist (SN) representation and algorithms.

The external `sn_slang` executable parses and elaborates Verilog/SystemVerilog using Mike Popoloski's excellent
[slang SystemVerilog compiler](https://github.com/MikePopoloski/slang) and writes a binary `.sn` design. ABC does
not link slang or require its C++20 dependencies.

The frontend architecture benefited from [yosys-slang](https://github.com/povik/yosys-slang), developed by
Martin Povišer. It has been both an inspiration and a helpful practical guideline for working from slang's
elaborated model, particularly for lvalue analysis, procedural state, timing patterns, memory eligibility, resolved
nets, and diagnostics. The SN representation and lowering are independently developed, with warm thanks to Martin
for his work and advice.

ABC holds the SN design and the `&`-space GIA as independent representations. Commands move data between them only
when explicitly requested:

| Command | Reads | Writes |
| --- | --- | --- |
| `@slang`, `@read` | HDL or `.sn` | Current SN design |
| `@map_*`, `@opt_mux`, `@collapse` | SN | New SN design revision |
| `@blast` | SN | Current `&`-space GIA plus a saved boundary |
| `&...` commands | GIA | GIA |
| `@put` | GIA plus saved boundary | Module selected by the preceding `@blast` |
| `@write` | SN | `.sn` or Verilog |

`@status` reports both representations, the monotonically increasing SN revision, and whether the saved boundary is
compatible with the current SN design and GIA. In particular, reading or transforming SN does not clear or update an
old `&`-space network; it makes that network unavailable for `@put` until another combinational `@blast` records a
matching boundary.

## Commands

The commands appear under `New word level commands` in ABC's `help` output.

```text
set snslang /path/to/sn_slang
@slang -M top rtl1.sv rtl2.sv
@status
@check
@ps -v
@map_mem -v
@check
@map_dsp -v
@check
@map_add -v
@check
@opt_mux -v
@check
@blast -M top -c -v
&resyn3
&if -m -K 6
&ps
@status
@put -v
@check
@collapse -v
@check
@write mapped_logic.v
@write mapped_logic.sn
```

`@slang` uses `sn_slang` from `PATH` unless the `snslang` setting overrides it. It accepts `-M` for the top module,
repeatable `-D NAME` or `-D NAME=value` preprocessor definitions, `-F` for one additional source file, and any number
of positional source files. For example, `-D WIDTH=8 -D SIGNED=1` defines two macros. `-T` is not used because ABC
conventionally reserves it for a time limit. `-v` prints the external command and frontend timing. A module declared
inside SystemVerilog `` `celldefine`` / `` `endcelldefine``, or marked by a nonzero `black_box` or `syn_black_box`
module attribute, is imported as an opaque technology primitive with its elaborated PI/PO interface; its simulation
body is not lowered. For example, both `` `celldefine`` around a module definition and
`(* syn_black_box = 1 *) module macro (...);` create an opaque leaf. An explicit zero or false attribute does not.
The declaration is still required: slang must know every port's name, direction, width, and signedness, so an
undefined-module inst remains an error. Undefined-module patterns and include-directory options remain unsupported.

`@read` and `@write` provide binary persistence. `@write` selects SN or Verilog output from the `.sn`, `.v`, or
`.sv` extension. `@read -M module` selects the top stored in a multi-top design; otherwise the last top is used.
Before installing external binary data, `@read` validates the encoding and runs the same non-aborting structural and
semantic checks as `@check`. A failed `@write` removes its incomplete output file. Every design installed in ABC is
topologically ordered. The current writer emits binary format version 6; the reader also accepts version 5 and treats
its modules as ordinary non-black-box modules because that format predates module flags.

`@status` prints the current design and top names, SN revision, selected technology, hierarchy form, last extraction
mode/module/revision, saved boundary hash, current GIA dimensions, and `@put` compatibility. A new `@read` or `@slang`
design starts at revision 1. Each transformation that installs a replacement SN design, and each successful `@put`,
advances the revision; `&` commands do not. An optimization that finds no profitable rewrite leaves the design and its
revision unchanged.

`@blast` gives every GIA input and output a unique ordered name containing the retained SN signal name, bit index, and
interface index. It also hashes the selected module identity and all saved boundary occurrences, primitives, registers,
loops, and input/output endpoint records. Before insertion, `@put` verifies the SN revision, module ID and name,
boundary hash, GIA dimensions, and ordered GIA-name signature. It rejects a GIA whose interface was reordered, renamed,
or stripped of names, even if its input and output counts still match. The GIA must also remain combinational, with zero
registers. Normal interface-preserving `&` synthesis commands retain the names and remain compatible.

MiniAIG has only an edge-triggered register convention. Therefore `@blast` and `@map_lut` explicitly reject any
level-sensitive `SN_REG_LATCH` reachable from the selected module until a semantics-preserving latch flow is available.

`@check` performs a non-aborting consistency audit of the complete SN design. It validates core and type-specific
attribute vectors, fanin storage, object IDs, widths, names, constants, topology, state pairing, memory-port ownership,
instance/FAN ordering, hierarchy recursion, LUTs, gates, and mapped primitive interfaces. `@check -v` adds one summary
line per module. Memory, DSP, and carry mapping commands run the same checker transactionally before and after each
transformation, so an invalid result is diagnosed and rejected without replacing the current design.

`@ps` prints compact statistics for every module definition by default. `@ps -M module` prints the selected module
instead and uses it as the root for optional hierarchy and detailed reports. `@ps -v` adds the selected hierarchy and
keeps opaque definitions annotated with `[blackbox]`. Like `%ps -d`, `@ps -d` prints occurrences by object type and
output/input width signature. It also reports every reachable black-box type, its instance-occurrence multiplicity,
PI/PO port and bit counts, and totals for abstract AIG inputs and outputs. Counts cover the elaborated hierarchy rooted
at the selected module (or the current design top when `-M` is absent), including repeated insts. Hierarchical totals
are accumulated over the module DAG rather than by recursively revisiting every inst, so statistics remain practical
for deeply repeated hierarchy. Memory is reported as used/allocated storage with rounded K, M, or G suffixes.

`@map_mem`, `@map_dsp`, and `@map_add` map into the initial AMD/Xilinx UltraScale+ technology description.
Transformations are transactional and keep the original user-visible top-module name. `@map_add` replaces word-level
addition and subtraction of at least three bits by chains of behavioral `__sn_CARRY4` primitive insts. Propagate,
operand inversion, extension, and final slicing remain ordinary SN logic for subsequent LUT mapping. Run DSP mapping
before carry mapping so future DSP preadder and postadder recognition is not hidden. `@collapse` flattens user hierarchy
while retaining mapped hard-block leaf instances.

Opaque `SN_MODULE_BLACKBOX` insts are preserved by hierarchy collapse even when ordinary user hierarchy is flattened.
During `@blast`, each opaque output is an additional GIA input and each opaque input is an additional GIA output, in
natural port and LSB-first bit order. A black-box `SN_PO` has `SN_INVALID_ID` as its sole fanin, explicitly recording
that its value has no SN implementation; no zero-valued placeholder is created. `@write` emits the preserved interface
as a port-only `(* blackbox *)` module. Internally an opaque module contains only its declared `SN_PI` and `SN_PO`
objects; an `inout` is a same-named PI/PO pair. Its body and descendants are absent from SN. `@check` permits the
invalid PO fanin only for this boundary representation, and `@ps -v` / `@ps -d` expose the retained black boxes and
their reachable occurrence counts.

`SN_CAST` is a one-fanin operator whose object width and signedness define the result type. It does not permute bits.
An equal-width cast only changes the signedness annotation; widening sign-extends a signed result and zero-extends an
unsigned result; narrowing discards high bits and retains the LSB-first low-order portion. `sn_slang` adds casts for
explicit and implicit slang conversions, `$signed` / `$unsigned`, dynamic selected-value normalization, packed-value
updates, and final normalization of `SN_MUX` data branches to the mux result width. Memory, DSP, and carry mapping may
also introduce casts while adapting word-level values to primitive interfaces. The Verilog writer uses `$signed` or
`$unsigned` on a result-width wire, and the bit-blaster implements the same extension or truncation directly.

`@opt_mux` restructures register mux cones by collecting root-to-terminal paths, grouping structurally identical
LSB-first word values, and ORing the corresponding path conditions. A register-output terminal is converted into an
explicit enable when the path controls are provably exclusive. The pass currently recognizes ordinary `SN_MUX`
trees and packed `SN_PMUX` alternatives; separately created casts, slices, repetitions, concatenations, and constants
are compared structurally. Rewritten modules are restored at their stable hierarchy IDs and retain every register
pair so that the canonical transition interface remains unchanged. The default profitability filter requires at
least 4-bit data, six paths, two eliminated paths, and a path-to-distinct-terminal ratio of at least 2:1. This avoids
increasing logic for narrow control muxes while retaining the intended wide datapath transformations.

`@blast` traverses hierarchy directly without first allocating a flat SN module. Sequential extraction is the
default; `-c` selects combinational extraction. `-t` emits the same effective next-state functions as a purely
combinational transition AIG for equivalence checking.
`-M module` selects the module to
extract; the default is the current SN top. ABC records the selected module and the exact LSB-first boundary mapping,
then installs the resulting GIA as the current `&` network. The user may apply any `&`-space combinational synthesis
and mapping commands that preserve the number and order of combinational inputs and outputs. Nothing requires the
logic to be put back into SN: omitting `@put` leaves the SN design unchanged.

Adders use a Brent-Kung parallel-prefix network by default. `@blast -r` selects ripple-carry adders instead. This
choice also applies to adder networks used while blasting subtraction and other arithmetic operators; `-b` separately
selects Booth rather than the direct-unsigned/Baugh-Wooley multiplier. Signed and unsigned relational operators use
a balanced, delay-oriented comparator by default; `@blast -d` toggles to the minimum-node topology implemented by ABC's
`&gencomp`. Equality comparison remains balanced in both modes. Ripple adders and multiplier compressor trees share
the seven-node full-adder construction from `Wlc_BlastFullAdder()`. Direct unsigned, signed Baugh-Wooley, and radix-4
Booth partial products use the delay-aware, level-ordered matrix reduction adapted from `Wlc_BlastReduceMatrix()`,
followed by the selected Brent-Kung or ripple final adder. The radix-4 Booth recoding, signed correction, rectangular
operand handling, and unsigned zero extension follow `Wlc_BlastBooth()`. Binary mux trees use `Mini_AigMuxMulti()`,
while AND/OR reductions and equality aggregation use balanced `Mini_AigAndMulti()` trees over copied temporary
literals. One-hot priority muxes use a balanced sum-of-products tree; their result for a multi-hot select remains
intentionally undefined. Variable shifts instantiate only the useful barrel stages and combine all higher shift bits
into one balanced overshift condition.

Unnamed constants are interned by width, signedness, and packed value within each module. Concatenations whose inputs
are all constant are folded into one packed `SN_CONST`, including tables wider than the per-object fanin-count limit.
When such a constant drives an `SN_BMUX`, blasting reads one output-bit column at a time and simplifies constant and
equal mux branches before creating MiniAIG nodes; it never materializes the complete packed table as an integer-literal
array. The Verilog writer splits very large constants into bounded-size hexadecimal concatenation chunks.

In combinational mode (`@blast -c`), flop outputs become additional inputs, while raw data and synchronous control
inputs become separate outputs for later stitching; clock and asynchronous controls remain outside this boundary.
Mapped RAM/DSP and CARRY4 outputs and inputs are likewise exposed as additional cloud endpoints. `@put` checks the saved
interface and reconnects registers and mapped primitive instances. With the default sequential `@blast`, the AIG
transition functions elaborate synchronous reset, set, and enable controls in SN priority order; clock and asynchronous
controls remain outside the transition relation. Sequential-AIG insertion is deliberately rejected for now.

`@map_lut` applies this combinational extraction and reconstruction module by module while preserving the natural SN
hierarchy. Child instances, registers, and mapped RAM/DSP/CARRY4 instances are partition boundaries, matching the broad
structure of Yosys's per-module ABC flow. `@map_lut -S "&resyn3; &if -m -K 6"` supplies an inline per-partition ABC
script; `-F script.abc` sources it from a file. The default is the same `&resyn3; &if -m -K 6` sequence. Every script
must preserve CI/CO order and leave a LUT-mapped GIA. Generic-memory modules left unsupported by `@map_mem` remain
unchanged and are reported as skipped partitions. Mapped nodes wider than the physical SN LUT6 primitive are
decomposed deterministically by Shannon expansion. The pass maps a duplicate design and commits it only after every
reachable non-primitive module succeeds. `-P num` runs the independent partition jobs concurrently using `num - 1`
pthread workers and one coordinating process. `-P 1` uses the current ABC process directly, so its last partition
becomes the current `&`-space GIA; use `-P 2` or more when the preexisting `&`-space network must remain untouched.
SN pthread support is compiled out on Windows, where `-P 1` remains fully supported and larger values are rejected.
`@map_lut -E prefix` stops at the same partition boundary, writes each nontrivial job as
`prefix_<module-id>_<module-name>.aig` with a `.txt` interface-statistics sidecar, and does not run synthesis or modify
the SN design. This mode cannot be combined with `-S` or `-F`, currently requires `-P 1`, and is intended for
developing or benchmarking an external per-partition synthesis flow.
Generated clock and asynchronous-control cones remain outside the mapped cloud and are copied with per-occurrence
memoization when registers are reconnected.

The transition AIG orders state bits canonically by depth-first natural instance type ID, natural `SN_REG_OUT` type
ID within each occurrence, and LSB-first bit index. Both hierarchy duplication and mux sharing preserve these IDs.
Consequently, the transition AIGs made before and after `@opt_mux` have identical CI/CO order and can be compared
directly with `&cec before.aig after.aig`. For large, structurally different cones, explicitly constructing the miter
is often much faster: `&r before.aig; &miter after.aig; &cec -m`. Transition-AIG insertion through `@put` is
deliberately rejected.

`@put` replaces only the module selected by the preceding `@blast`. Its module ID, name, and port interface remain
stable, so parent instances and every other module in an uncollapsed hierarchical design are preserved. The current
GIA determines the reconstructed representation:

- An unmapped GIA becomes explicit one-bit `SN_BIT_AND` and `SN_BIT_NOT` objects.
- A LUT-mapped GIA becomes `SN_LUT` objects with truth tables transferred through MiniLUT.
- A cell-mapped GIA becomes `SN_GATE` objects annotated with current genlib gate IDs and cell names through ABC's
  mini-mapping format. Insertion requires the current genlib to contain every referenced gate.

For example, `@blast -c; &resyn3; &if -m -K 6; @put` implements the former canned LUT-mapping flow without hiding
the ABC script. `@blast -c; &dc2; @put` reinserts an optimized unmapped AIG, while
`read_genlib library.genlib; @blast -c; &nf; @put` reinserts standard cells. The Verilog writer emits LUT and gate
instances as well as ordinary SN logic.

Mapped RAM/DSP/CARRY4 instances are reconstructed as technology leaf instances. SN loop-breaker pairs connect their
output ports while the new flat module is built and are placed into a legal order by the final topological reorder.
Temporary primitive-output loop pairs are pruned after reconnection unless an actual feedback dependency remains, so
acyclic datapaths do not gain artificial loop-breakers. Explicit loop boundaries extracted from the original SN module
are reconstructed unchanged; they are not currently re-proved unnecessary after `&`-space optimization. Generic
unmapped memory endpoints are recorded and abstracted by `@blast`, but `@put` currently rejects them because the
boundary does not yet retain enough per-memory-port ownership data. This check prevents silent loss or misconnection
of stateful memories.

## Source files

The package uses ABC-style filenames:

```text
sn.h          core representation, hierarchy, serialization, and Verilog writer
snCheck.h     non-aborting design, module, hierarchy, and technology-interface consistency checker
snTech.h      target technology descriptions
snMapMem.h    memory mapping support
snMapDsp.h    DSP mapping support
snMapAdd.h    CARRY4 mapping support
snMapTech.h   combined hierarchy mapping
snMapLut.h    natural-hierarchy LUT-mapping harness
snPth.h       bounded pthread worker harness
snBlast.h     direct hierarchical MiniAIG construction
snMux.h       register mux-path sharing and restructuring
snBoundary.h  saved boundary and combinational register reconnection
snMiniAig.h   unmapped MiniAIG reconstruction
snMiniLut.h   MiniLUT analysis and SN_LUT reconstruction
snMiniGate.h  mini-mapping and SN_GATE reconstruction
snCom.c       ABC manager ownership and command handlers
```

The external frontend must compile against this directory through a configured include path. Representation changes
are made here first and must update the binary-format version when serialization compatibility changes.
