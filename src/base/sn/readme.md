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

`@write -n file.v` preserves unique signal, gate and module-instance names, escaping Verilog keywords and
punctuation. Duplicate, unnamed or unrepresentable names fall back to collision-free generated identifiers;
signals and instances share one collision check. Port names are always retained. A single-output gate's name
identifies its instance, not also its output wire. This option is Verilog-only and does not mutate SN.
Preserved instance names enable name-checked boundary proofs after Verilog re-import; the frontend retains
generate-scope and instance-array indices so repeated instances do not collapse to the same leaf name.
Unused named output pins are emitted explicitly open. Direct same-named register/output aliases use
`output reg`; other native register declarations carry a name-only `sn_register_name` annotation for
sn_slang re-import. Cell `sn_state_name` and `sn_state_phase` annotations are retained by both ordinary and named output. Neither annotation
encodes physical initialization or a proof of equivalence; malformed phases remain explicit refusals.

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
@map_dff -v
@check
@map_srl -v
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
topologically ordered. The current writer emits binary format version 15, in which every register control and
initialization slot lives on `REG_IN` and memory initialization on `MEM_IN`, while each state OUT object has its
paired IN as its only fanin, and slice, repetition, global constant ID, LUT truth-table offset, and gate metadata live in
each object's data word (`obj_data`) instead of per-type vectors, as do register flags and memory depths (on the
OUT object), each state IN object's link to its OUT, and each inst's module ID. The reader also accepts versions 5
to 12: it interns legacy constant-word spans into global payload IDs, folds the older per-type vectors and pair indices
into the data words, moves version 5-7 `REG_OUT` /
`MEM_OUT` slots to the IN partners while loading, and treats version 5 modules as ordinary non-black-box modules
because that format predates module flags.

Version 13 added an optional embedded Liberty source before the modules. Version 14 stores an ordered list of
independent embedded libraries; the reader still accepts v13. Gate IDs are zero-based parser-order cell indices,
concatenated in library-file order. Duplicate cell names across files are rejected. Each model retains its own
types, templates, units, and defaults. No scalar library-cell modules are created. A single-output gate is
an unsigned one-bit signal; a multi-output gate is a zero-width structural owner with adjacent one-bit FANs.
The parsed model is reference-counted across design copies; derived `snExpr.h` multi-root AND graphs are compiled
on the first blast and are not serialized. This self-contained encoding avoids accidental rebinding to a different
library but adds the library's source size to each SN file. Scalar combinational output functions referencing
input pins are supported. Compilation uses nominal powered, two-state behavior: output-pin `power_down_function`
and `x_function` remain in the parsed model but do not disable compilation or modify the nominal `function`.
This does not model power-off corruption or preserve X behavior; equivalence claims must exclude those conditions.
Pins with `three_state`, missing functions, or malformed attributes remain unsupported. FF-level
`power_down_function` is likewise retained but ignored under the powered-only assumption. Scalar FFs also compile output and transition graphs: the latter implement sampled
clock edges, next-state functions, and asynchronous clear/preset with independent IQ/IQN collision values.
There are three AIG state bits per FF (IQ, phase-encoded IQN, previous clock). Zero AIG initialization represents
IQ=0, IQN=1, previous clock=0; unknown initialization is not modeled. Every relevant clock/control event must
be sampled. This is not delay-accurate simulation. Multi-bit banks, statetables, dual-clock/power-down
behavior and X/T/unspecified collisions remain unsupported. Mixing these sampled FFs with clock-abstracted SN
state is rejected. LOOP pairs remain explicit combinational CI/CO constraints in sampled-cell mode, just as in
word-level blasting. They are not registers and must be reconnected or solved to a fixed point before claiming
functional simulation. This permits vector-net merge trees with apparent word-level feedback; blasting alone
does not prove absence of bit-level combinational cycles. Uncut evaluation cycles fail with a safe diagnostic.
Valid scalar Liberty latches are retained as opaque gate boundaries, not compiled as sampled FFs. All signal
inputs and outputs are exposed, preserving the cell ID and its pin order for `@put`; multi-output gates keep FANs.
Malformed cells and three-state outputs remain rejected. This is an explicit abstraction, not latch simulation.
The written AIG is not a closed sequential model when LOOP, latch, or opaque-macro ports remain. Outside the trace tool,
ABC simulation and equivalence commands treat those cut inputs as free unless the caller supplies the constraints;
`&cec`/`dsec` do not automatically close them. `@blast -c` and `-t` expose the sampled transition relation, but `@put`/partition reconstruction
of sampled state is not implemented. `@blast -f` instead keeps every scalar flip-flop cell opaque, exactly like a
latch (`sn_library_ff_boundary`, option `opaque_sequential_gates`): its pins become ordinary CIs/COs, the
combinational cloud between the flops is exposed, and `@put` re-instantiates the same cells. This is the mode for
re-synthesizing or re-mapping a mapped netlist: `@read netlist.sn; @blast -c -f; ...; @put`. Missing functions and unsupported behavior fail blasting explicitly.
Mio reconstruction into a library-backed design is rejected until
there is an explicit checked binding between the two gate-ID namespaces.
The existing SN memory totals exclude shared library/model/graph storage; `@ps` labels that exclusion explicitly,
reports parser-warning counts (including embedded sources), and reports unsupported-cell counts after compilation.
`@status` also reports the embedded libraries' warning count.
Interface pin/count queries use precomputed per-cell indices. Blasting reuses one expression scratch allocation
per hierarchy frame, borrowing it only after recursively evaluating gate dependencies.

In the maintainer's full development workspace, `test/sn/sn_iwls_trace.cc` is an ISCAS-specific test utility
built by the sibling sn_slang CMake project against ABC headers, not by ABC's default build. Test sources
and fixtures are not included in this source changeset or the minimal frontend distribution.
The utility recognizes `blif_clk_net` and `blif_reset_net`, solves LOOP cuts with
FF state held fixed, and rejects non-convergent traces. Opaque SRAM/macros require an external model and are not
functionally checked by this utility.

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

MiniAIG has only an edge-triggered register convention. `@blast` therefore keeps an instantiated module containing
an `SN_REG_LATCH` as an opaque boundary, like a stateful memory macro. If a latch occurs directly in the selected
root module, its output is instead exposed as an additional combinational input and its data and dynamic controls as
additional combinational outputs. In `@blast -c; ...; @put`, the saved boundary restores the opaque module instance
or recreates a root latch with its original flag, data input, enable, initialization, and metadata. Latch bits are
never included in MiniAIG's register count. The module-by-module `@map_lut` command continues to reject reachable
latches.

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
Memory mapping handles ROMs: a memory with constant initialization — including one with no write port at all —
maps into tiles that carry their slice of the initialization image, named by a content hash so each distinct ROM
content is its own primitive; a write-free tile keeps its write port permanently disabled. Masked-off and
uninitialized bits are zero, SN's two-state value of uninitialized storage. That zero-start convention is a
synthesis convention, not a claim about the source: a register or memory whose SystemVerilog initialization is
unknown keeps a zero `INIT_MASK`, so the unknown is preserved in the representation and only the sequential
analyses (`@map_dff`, the transition AIG, cleanup) assume the zero start. The behavioral primitives written by the
mapping commands (`__sn_CARRY4`, `__sn_SRL_*`, `__sn_DSP48E2_*`, memory tiles) model the function of the physical
cell; the primitive counts are equivalence-preserving estimates of the physical implementation, not a placed
netlist, and `@blast -p` expands them for verification against the unmapped design.
Memory mapping absorbs read-port registers: a plain register (no set, reset, initialization, or clock inversion)
fed exclusively by an asynchronous memory read becomes the registered read port of a `_rtile_` or `_rtdp_tile_`
primitive, matching the physical primitive's registered output, and a source read that is already clocked maps the
same way. The absorbed register's clock and enable drive the tile's read port; with depth tiling the bank-select
index is held in a small register under the same enable so the output mux tracks the registered data. A dual-port
plan registers either both reads or neither, and a registered dual-port read must share its port's write clock.
Transformations are transactional and keep the original user-visible top-module name. `@map_add` replaces word-level
addition and subtraction of at least three bits by chains of behavioral `__sn_CARRY4` primitive insts. Propagate,
operand inversion, extension, and final slicing remain ordinary SN logic for subsequent LUT mapping. `@map_add -W num`
raises the minimum mapped adder width when narrow additions are better left in LUTs. A single-fanout chain of
additions and subtractions collapses into one carry-save compressor tree with a single final carry chain, the way
multi-operand accumulation maps efficiently onto FPGAs: every leaf is recorded with the extension signedness of the
operator that consumed it and its accumulated negation, constant leaves fold into one addend, and the tree stays
exact modulo the result width. Run DSP mapping
before carry mapping so post-adder recognition is not hidden. `@collapse` flattens user hierarchy
while retaining mapped hard-block leaf instances.

`@map_srl` extracts shift registers in two forms. A memory whose writes shift entry k-1 into entry k under one
clock and one shared enable, fed externally only at entry zero and observed through up to four asynchronous tap
reads, becomes one behavioral `__sn_SRL_*` primitive with one tap output per read. A chain of three or more plain
registers on one clock and one shared enable — no set, reset, or initialization — whose interior stages are read
only by their successors becomes one `__sn_SRLC_*` chain primitive. Both are the shift-register idioms FPGA
synthesis maps onto SRL cells; extraction removes the shift muxing and tap decode from the soft logic and the
chain flops from the register count. Run `@map_dff` first: its constant folding equalizes structurally different
but semantically equal enables, which the recognition compares structurally. Recognition runs before general
memory planning, so BRAM tiling never claims a shift register.

DSP mapping uses the post-adder. A multi-DSP multiplier chains its aligned partial products through
multiply-accumulate primitives (`__sn_DSP48E2_mac_*`, computing `Y = (A * B << shift) + C`), so the partial sum
costs no fabric adders when the result fits the DSP product width. An addition whose only use of a mapped
multiplier is that sum absorbs into the same chain through the C input, which removes the accumulator carry chains
of multiply-accumulate loops. Operand chunking chooses per multiplier between full-port chunks, whose unsigned
non-top chunks need gated sign-correction terms in fabric, and one-bit-narrower zero-extended chunks that need
none; zero extension wins whenever it does not increase the DSP count. `@blast -p` expands mapped memory, DSP, and
carry primitives so a mapped design can be verified directly against its unmapped original.

`@map_dff` optimizes word-level registers ahead of flip-flop technology mapping and belongs before `@map_lut`, so
the LUT mapper covers the final combinational cloud. An inductive stuck-at-zero analysis assumes every register with
zero initialization holds zero, propagates the assumption, and demotes refuted candidates until the survivors form a
genuine invariant; those registers become constants. A local rule additionally folds registers whose initialization,
next-state data, and reachable set or reset agree on one constant. Registers with identical controls, polarity
flags, initialization, and next-state data merge into one, interleaved with combinational subexpression sharing to a
fixed point so next-state cones that become identical after earlier merges are found as well. Cones that lose their
last fanout are swept. Set and reset controls are judged by their polarity flags: an active-low control tied to
constant zero fires permanently and is never treated as absent. The pass is hierarchical and transactional; `@check`
verifies the structural invariants of its result on every design, and the simulation and equivalence regressions in
`abc/test/sn` and `sn_slang/tests` cover its behavior. Shift-register extraction is `@map_srl`; flop-cell
legalization is a planned extension.

Memory mapping preserves read-to-write feedback through explicit `SN_LOOP_OUT` / `SN_LOOP_IN` ordering
boundaries when replacing state objects with atomic primitive instances would otherwise introduce a parent-level
cycle. Feed-forward instance inputs remain directly connected. These boundaries retain the original wires in
emitted Verilog; they do not add clock cycles or storage.

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
Selecting an opaque black-box module itself is rejected with a diagnostic in all three modes. Blast its enclosing
design to expose the opaque instance boundary. A rejected selection preserves the current GIA and saved extraction.
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

Constant payloads are interned design-wide, independently of modules, widths, signedness, and node names. Each
constant node stores a global payload ID in `obj_data` and its own interpretation in `width_signed`. Payloads are
unsigned LSB-first 32-bit words with high zero words omitted; zero has no words. `SN_CONST0` and `SN_CONST1`
also carry payload IDs. `sn_const_word(module, object, index)` supplies implicit zero padding and truncates to
the node width; signed extension belongs to the consuming operation. For example, payload `0xff` represents
8-bit signed -1 or 16-bit signed 255; 16-bit signed -1 requires payload `0xffff`.

Every call to `sn_module_add_const` creates a new node, even for identical constants in the same module.
There are no per-module records or object-reuse lookups; AIG structural hashing shares the resulting logic.
`const_entries` holds payload offsets/counts indexed by global ID; `const_buckets` and the entry hash/next fields
are a derived chained hash rebuilt lazily after loading or duplication, without scanning modules. Binary v12
serializes the payload descriptors, but not the hash chains. LUT truth tables retain separate two-word offsets.

Concatenations whose inputs are all constant are folded into one packed `SN_CONST`, including tables wider than
the per-object fanin-count limit.
When such a constant drives an `SN_BMUX`, blasting reads one output-bit column at a time and simplifies constant and
equal mux branches before creating MiniAIG nodes; it never materializes the complete packed table as an integer-literal
array. The Verilog writer splits very large constants into bounded-size hexadecimal concatenation chunks.

In combinational mode (`@blast -c`), flop outputs become additional inputs, while raw data and synchronous control
inputs become separate outputs for later stitching; clock and asynchronous controls remain outside this boundary.
Latch outputs, raw data, and dynamic controls form the same kind of retained boundary in every blast mode, but are
always combinational AIG endpoints rather than MiniAIG registers.
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
Parallel workers locate the current executable using `/proc/self/exe` on Linux and `_NSGetExecutablePath` on
macOS; insufficient path-buffer capacity is reported as an error. The header compile regression uses an ABC
namespace and the Windows SDK's `interface` macro to catch include-order portability regressions.
`@map_lut -E prefix` stops at the same partition boundary, writes each nontrivial job as
`prefix_<module-id>_<module-name>.aig` with a `.txt` interface-statistics sidecar, and does not run synthesis or modify
the SN design. This mode cannot be combined with `-S` or `-F`, currently requires `-P 1`, and is intended for
developing or benchmarking an external per-partition synthesis flow.
Generated clock and asynchronous-control cones remain outside the mapped cloud and are copied with per-occurrence
memoization when registers are reconnected.

The transition AIG orders state bits canonically by depth-first natural instance order (each module's `SN_INST`
list), natural `SN_REG_OUT` list order within each occurrence, and LSB-first bit index. Both hierarchy duplication
and mux sharing preserve these orders.
Consequently, the transition AIGs made before and after `@opt_mux` have identical CI/CO order and can be compared
directly with `&cec before.aig after.aig`. For large, structurally different cones, explicitly constructing the miter
is often much faster: `&r before.aig; &miter after.aig; &cec -m`. Transition-AIG insertion through `@put` is
deliberately rejected.

`@put` replaces only the module selected by the preceding `@blast`. Its module ID, name, and port interface remain
stable, so parent instances and every other module in an uncollapsed hierarchical design are preserved. The current
GIA determines the reconstructed representation:

- An unmapped GIA becomes explicit one-bit `SN_BIT_AND` and `SN_BIT_NOT` objects.
- A LUT-mapped GIA becomes `SN_LUT` objects with truth tables transferred through MiniLUT.
- A cell-mapped GIA becomes compact `SN_GATE` objects. With `@read_lib`, reconstruction uses checked
  physical pin permutations and parser-order IDs in the attached SN library. Synthetic constants become
  SN constants; no Liberty functions expand into SN operators. Legacy library-free designs retain the
  old Mio-ID path (which is not a self-contained library representation).

For example, `@blast -c; &resyn3; &if -m -K 6; @put` implements the former canned LUT-mapping flow without hiding
the ABC script. `@blast -c; &dc2; @put` reinserts an optimized unmapped AIG, while
`read_genlib library.genlib; @blast -c; &nf; @put` reinserts standard cells. The Verilog writer emits LUT and gate
instances as well as ordinary SN logic.

For a self-contained standard-cell result, use
`@read design.sn; @read_lib target.lib; @blast -c -f; &nf; @put; @check; @write mapped.sn; @write -n mapped.v`.

An ordered `@read_lib` target may also be a `.snlib` model. ABC loads its functions and verifies that its
recorded Liberty source is available with exactly the stored byte size and hash before reading SCL timing.
Missing or changed sources refuse transactionally; names and file timestamps are not identity checks.
This supports functional-only models too, but does not claim self-contained binary SCL timing or guess a
replacement corner. Source paths are used as recorded (relative paths resolve against the current directory).
`@read_lib` selects an ordered list of text Liberty files (`@read_lib a.lib b.lib ...`);
`-m` also enables two-output combinational cells. Existing FFs,
latches and opaque macros remain in the design bundle without becoming mapping targets. It prepares SN,
SCL, Mio and Amap representations and checks physical interfaces and Boolean functions before replacing
any live library. Failed loading leaves the design, library handles and saved extraction intact. A model
already present by source size/hash keeps its IDs; a disjoint model is appended. Other duplicate cell
names are conservatively refused. Legacy Mio-ID gates must be regenerated from source before attaching
an SN library. A mapped main network must be cleared before replacing the ABC library it references.

The SCL reader normalizes supported time/capacitance units before merging. Unknown explicit units are
refused. Mixed nominal corners retain the selected vocabulary for functional/area mapping, but disable
SCL timing and sizing rather than invent a common corner. The supplied ASAP7 files differ in nominal
voltage (0.7/0.77 V) and temperature (0/25 C), so their corpus results are area-only. Diagnostics name the
conflicting files and values. Cells above 16 inputs or two outputs remain in the SN bundle but are
explicitly excluded from SCL mapping targets; genuine binding/function mismatches still refuse loading.
Sequential-only files contribute interfaces without requiring a combinational genlib. `.snlib` timing
reuse requires the exact recorded text source, checked by size and hash as described above.

`@ps -a` reports physical cell counts, a histogram, and combinational/sequential/opaque/macro areas from
the SN library, independently of SCL. Hierarchical occurrences multiply definition counts; multi-output
FANs never count as extra cells. Missing areas and external boxes are listed, not counted as zero-cost
known cells. Native unmapped operators/register bits are reported separately. Areas use native Liberty
units; comparing totals requires the same macro coverage in both flows.
The inventory separately reports constant objects, physical zero-input tie owners, clock-gating cell and
clock-pin annotations, and PG pins. It is not clock-tree recognition, PG connectivity or power analysis.

Binding exhaustively checks functions through 16 inputs (larger cells require a later SAT adapter),
including reordered asymmetric pins. Load the target before extraction; changing its mapping vocabulary
after `@blast` invalidates cell-mapped reinsertion. Rebuilt SN files embed the functional library and can
be read and blasted in a fresh ABC process without the source Liberty file. Structural Verilog still
requires the library. The writer omits duplicate declarations of exact Liberty-backed opaque interfaces;
unrelated black-box declarations and mismatching interfaces are not suppressed.

`@put -n` explicitly selects the mapped **main network**; the default still selects the GIA. For example,
`@read_lib -m target.lib; @blast -c -f; &put; amap; @put -n` uses the area mapper; replace `amap` by `map`
or `emap -m` for the other main-space mappers. `@status` reports eligibility for each workspace separately.
The main network must retain the current extraction's provenance token (carried in ABC's `pSpec`), exact
ordered CI/CO names and library vocabulary, and must contain no state or boxes. Loading an unrelated network,
re-extracting SN, or changing/dropping boundary ports invalidates reinsertion. Main-network edits after
`&put` are consumed by `@put -n`; an older GIA is never silently substituted. Mapping operations which
discard provenance must restore its documented transfer in the mapper, not bypass this check.

Both mapped adapters use the physical-cell reconstructor in `snNtk.h`. It checks each used gate once and
compares twin fanin nets under both pin permutations before sharing an owner. Pairing consumes both
adjacent nodes in physical object order, with reciprocal gate links, before DFS reconstruction; consecutive
pairs cannot overlap. Either output may be visited
first; a lone mapped output of a two-output cell still creates the full owner and FAN interface. Physical
buffers are retained, ABC barrier buffers are bypassed, and synthetic constants remain SN constants.
Physical tie cells retain their library IDs even when ABC designates them as its constant nodes; `dont_use`
still excludes them from binding. This is preservation, not automatic tie insertion or electrical legalization.
Reconstruction and consistency checking occur on a replacement design, installed only on success.

### `@map_cell`: hierarchical standard-cell mapping

`@read_lib target.lib; @map_cell` maps each reachable non-primitive hierarchy definition in process with
`nf`. Shared definitions and stable module IDs remain shared; child instances, native state and retained
sequential cells are partition cuts. Generic memories must be mapped first. Mapping checks ordered partition
port names and physical library binding, then installs a checked replacement transactionally; both existing
ABC workspaces remain unchanged. `-v` reports each definition's mapping progress and runtime. Port correspondence is not CEC. `snMapCell.h` exposes the borrowed-MiniAIG /
owned-network callback for this harness. There is no parallel or BLIF worker protocol yet.
This path uses default per-definition nf without a technology-independent synthesis script. The flat
experiment manifest separately supports `synthesis: none|dc2|syn2`; raw mapping-only area is not a tuned
synthesis result. See the [controlled comparison](../../../../sn_slang/results/README.md).

For a common-corner SCL target, main-network buffering/sizing can precede reinsertion:
`@blast -c -f; &nf; &put; topo; buffer -N 4; upsize -I 10; dnsize -I 3; @put -n`.
`topo` is required for non-topological mapper results (notably `emap`). The frontend's W6 harness exercises
this path for all four mappers, with fresh-process SN and Verilog CEC. Its default loads/constraints are not
a matched physical timing experiment; mixed-corner targets deliberately lack SCL sizing support.

Mapped RAM/DSP/CARRY4 instances are reconstructed as technology leaf instances. SN loop-breaker pairs connect their
output ports while the new flat module is built and are placed into a legal order by the final topological reorder.
Temporary primitive-output loop pairs are pruned after reconnection unless an actual feedback dependency remains, so
acyclic datapaths do not gain artificial loop-breakers. The feedback analysis treats the IN-to-OUT edge of every
register, memory, and loop pair as a cut, as the frontend does, so a primitive whose feedback is already broken by
an existing pair (a flop cell feeding logic that feeds its own D input through a frontend loop pair) does not
receive a second, redundant pair; the rebuilt module has exactly the loop pairs of the original hierarchy. Explicit loop boundaries extracted from the original SN module
are reconstructed unchanged; they are not currently re-proved unnecessary after `&`-space optimization. Generic
unmapped memory endpoints are recorded and abstracted by `@blast`, but `@put` currently rejects them because the
boundary does not yet retain enough per-memory-port ownership data. This check prevents silent loss or misconnection
of stateful memories.

### Boundary names

`@blast` names every GIA CI/CO canonically after its hierarchical owner rather than its position
(`sn_blast_boundary_bit_name`): `a[3]` for a top port bit, `u0.u3.ff/Q` for a gate pin, `u0.mem/data[7]` for an
instance port bit, `u0.state[2]` / `u0.state/d[2]` / `u0.state/enable[0]` for register outputs, next-state, and
control bits, and `u0.fb[0]` / `u0.fb/d[0]` for a loop pair. An unnamed loop is named `loop:` plus the canonical
name of bit 0 of its driver (a named signal, or a gate/instance output reached through slices, buffers, casts, and
concatenations). Reconstruction gives rebuilt gates, instances, registers, and loops the same hierarchical names, so
the blast of a module before `@put` and the blast of the rebuilt module can be compared with `cec`, which matches
CIs/COs by name, even though the topological reorder permutes their positions. sn_slang names the loop pairs it
creates for instance feedback after the instance input they feed (`inst/port`). Names that had to fall back to an
object ID, and names that received a `#n` suffix to stay unique, are counted and reported by `@blast -v`; such bits
cannot be matched reliably.

`@ps` reports the number of loop pairs per module when there are any.

`@blast -c -f; @stitch` makes a proof-only GIA by reconnecting LOOP cut inputs to their paired drivers.
The iterative dependency check refuses any observable combinational cycle and leaves the GIA unchanged
on refusal. State, latch, macro and other non-LOOP cuts remain independent; this is not a closed sequential
model. Successful stitching disables `@put` until a fresh `@blast`, because its interface no longer
matches the reconstruction boundary. The original SN design is never changed. Ariane136 still has a
reachable cache miss-handler cycle after joining wires, so this command does not yet resolve its large
Verilog round-trip proof gap.

`@blast -a -t` is a separate checked clock abstraction: outputs and next-state functions with one
free corresponding-state input per eligible bit. It follows hierarchy, buffers and inversions,
joins acyclic LOOP wires, and requires one free top-level clock root and one effective edge.
Dynamic gated/generated clocks, mixed edges, residual observable cycles, memories, latches and
opaque macros refuse transactionally. The preflight lists native/cell state and cut counts.
`@blast -a -z` instead exports a conventional sequential AIG, explicitly assuming zero for
unspecified **encoded** state bits. Without `-z`, sequential export requires explicit native
initial values; Liberty cells have no implicit power-up guarantee. Explicit native ones are
phase-normalized. The ordinary sampled `@blast` mode is unchanged, and `@put` cannot consume an
analysis projection.

The shared sequential descriptor uses `proof_conditions` bits for eligibility; diagnostic wording does
not admit a cell. Reset-inactive and dual-async requirements are discharged by checking the composed
controls under the explicit input contract. Latches additionally require the state-action mode.
Unobserved LOOP bits omitted by cone-of-influence reduction are counted in the report; their cycles
are not checked. `CLOSED` refers only to retained behavior, not a global acyclicity certificate.
After an analysis export or `@stitch`, `@status` identifies the analysis instead of showing a stale
reinsertion boundary.

`-N` selects full instance/register names for state and next-state symbols instead of the default
candidate index-order pairing. This is useful when preserving cells through mapping and Verilog re-import;
legalization supplies `sn_state_name` to match a physical cell to its original register bit. The frontend
preserves the writer's `sn_state_phase` and `sn_state_name` annotations, independently of generic metadata retention. Names
and phase select a correspondence hypothesis which still requires transition CEC; they are not a proof.

`-R reset=0,reset_n=1` constrains distinct scalar top inputs constantly. Asynchronous cells are
accepted only when their composed control functions prove inactive under these constraints,
including both controls of a dual-async cell. This is a reset-inactive analysis contract, never
an approximation of between-edge reset behavior. Vector ports and bit selections are not supported.
Each export logs the clock and all input constraints; add `-v` for the per-bit input and state
occurrence/object/bit/phase manifest. Outputs use the current state and active clock level; D
updates the next state. Canonical PI/PO symbols and explicit state/next indices support checked
interface matching. State index pairing across designs is only a hypothesis until transition CEC
and initial correspondence have been checked.

Legalization records `sn_state_phase`: source logical Q = physical IQ XOR phase. Preserved cell
and FAN annotations survive combinational reconstruction and SN serialization. This metadata
selects the proof encoding, not hardware behavior or a power-up requirement. Without it, cell
state defaults to the first physical output's polarity. Duplicate/malformed phase attributes
are rejected. Both ordinary and named Verilog output preserve this optional proof correspondence metadata;
`-n` is still needed to retain general instance and hierarchy names.
`sn_state_name` is a nonempty printable logical bit identity, separate from the physical instance name;
`@put` and `@collapse` qualify it by occurrence path when flattening. Duplicate/malformed annotations
or duplicate final boundary names refuse named-state proof export. Neither annotation changes hardware.

`@blast -q [-M top] [-u] [-R reset_n=1]` is a separate combinational **state-action signature**.
It exposes arbitrary corresponding state and retains clock inputs; FF/latch CIs have distinct
`ff-state:`/`latch-state:` labels. Each state has an `ff-action:`/`latch-action:` guarded update and an
`ff-clock:`/`latch-gate:` trigger output. FF clocks are edge-polarity normalized; latch updates retain
state when the gate is inactive. This permits function comparison through exact legalization, mapping
and Verilog re-import without pretending transparent latches are edge-triggered flops.
Plain native/cell latches are supported, including behavioral child modules; async FF controls must
prove inactive under the explicit constant-input contract. Generic memories and residual cycles still
refuse. `-u` cuts declared opaque modules, with free outputs and observed inputs, not invented SRAM state.
This is **not** a time-step, settling, glitch/timing or sequential-AIG model, and not an independent RTL
translation proof. It cannot be combined with `-a`, `-t`, `-z` or ordinary blast modes and cannot feed
`@put`. Ordinary `-a` latch/domain refusals remain unchanged. The proof harness records `action_cec`
only, requiring explicit `state_actions: true, run_sec: false`; it never runs SEC on these signatures.

`sn_slang/scripts/run_clock_cec.py` records transition CEC and independent `dsec` results with
explicit reset-inactive/shared-initial-state contracts. All four mappings of the 30 stateful
IWLS RTL designs pass both checks; the supplied mapped s27 also passes. The s953 RTL is stateless
with undriven outputs and remains unverified. Results are in `build/clock_iwls_w5/`, with follow-ups
in `build/clock_s5378_w5_phase_v2/` and `build/clock_s38417_w5_no_retime/`. The first follow-up fixes
lost phase correspondence; the second disables optional solver retiming to avoid timeouts.
The NanGate45 Ariane136 checkpoint has 19,839 FF cells, 136 opaque macros and 26,198 LOOP bits;
it is correctly refused as a closed model.

`@blast -a -u -t` explicitly permits declared black-box module cuts. Behavioral child modules containing
native latches are not eligible, even though ordinary combinational extraction treats them as boundaries.
Macro outputs remain free inputs, and all macro
inputs are observed outputs; every cut is named and logged. The result is labeled **CONDITIONAL**, never
a closed sequential model or a model of SRAM contents. Clocks driven by macros, transparent latches,
generic memories and residual cycles still refuse. A cycle refusal identifies one participating boundary bit
when available, not an arbitrary upstream cut. Duplicate cut names refuse rather than guess a pairing.
The original Ariane136 RTL-to-legalized transition CEC passes with `rst_ni=1` and these SRAM cuts
(`sn_slang/build/clock_ariane136_w7_v5/`). This is not a proof against the supplied commercial netlist.
That historical import predates the incomplete-`always_comb` hold fix. Corrected Ariane136 contains
three real latch bits and refuses this edge-triggered mode. Corrected Ariane136 and MemPool each pass
the three state-action comparisons (native SN to legalized cells, remapping, Verilog reimport) in all
three libraries; `sn_slang/build/mp_rtl_comparison_w7_v7/` records the 18 checks and their exact scope.
The corrected hierarchical Ariane136 chain also passes, with the same conditional contract, in
`sn_slang/build/state_actions_hierarchy_chain_w6/`. These checks include the actual latch state; they
do not reuse the historical pre-fix edge-triggered proofs.

`snSeq.h` provides `sn_library_seq_info`: separate preservation, sampled, one-state abstraction and
mapping eligibility, with an owned expression graph and borrowed raw state/collision record. Signed
pin projections are recognized semantically (exhaustive fallback through 12 inputs including state).
The graph uses complementary state variables only under its stated abstraction contract; dual-async
collision semantics are not collapsed. A dual-async physical candidate is eligible for mapping only
when unused controls are verified tied inactive; jointly active source controls remain unsupported.

`@read_lib target.lib; @map_ff -i` surveys the selected target cells. `@map_ff` then legalizes native
SN register bits into compact `SN_GATE` instances, including complemented outputs, either clock edge,
one asynchronous clear/preset, synchronous reset/set/enable muxes, and plain transparent latches.
It chooses the minimum-area legal cell deterministically and assigns every physical input. Explicit
initialization, jointly active asynchronous source controls, dynamic asynchronous reset values and
unverified scan ties are refused transactionally. Shared module definitions and source annotations
are retained. Latch data is cofactored while its gate is asserted, removing frontend hold-branch
artifacts without expanding Liberty functions into SN operators. Clock inversions and inactive
control ties are reported. A retained source cell is not a target unless selected by `@read_lib`.

Do not introduce an implicit zero-initialization assumption before legalization. The IWLS validation
uses `@map_dff -c -m` to disable constant-register folding and register merging. Its 31 RTL designs
legalize and all 124 four-mapper SN/Verilog boundary proofs pass; vendor-model event comparisons have
known-output coverage for 30 designs. The supplied s953 RTL leaves its outputs undriven, so it remains
unverified. See `sn_slang/build/iwls_mapping_w4_v2/`. Event traces and combinational boundary proofs
are complementary evidence, not a universal sequential equivalence claim.

## Source files

The package uses ABC-style filenames:

```text
sn.h          core representation, hierarchy, serialization, and Verilog writer
snCheck.h     non-aborting design, module, hierarchy, and technology-interface consistency checker
snTech.h      target technology descriptions
snLiberty.h   stand-alone Liberty (.lib) parser: syntax tree, Boolean expressions, typed library model
snExpr.h      immutable-after-build local AIGs, explicit output roots, simulation and callback replay
snLibrary.h   shared parsed-library ownership, canonical scalar interfaces, derived function compilation
snMapMem.h    memory mapping support
snMapDsp.h    DSP mapping support
snMapAdd.h    CARRY4 mapping support
snMapTech.h   combined hierarchy mapping
snMapLut.h    natural-hierarchy LUT-mapping harness
snMapCell.h   checked in-process natural-hierarchy standard-cell mapping harness
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

`snLiberty.h` reads Liberty libraries without depending on the SN representation or ABC runtime; it includes ABC's
namespace header, so the external frontend needs the ABC source include path. Its syntax layer keeps every group,
simple attribute, and complex attribute as an item with text
spans (comments of both styles, line continuations, and escaped quotes handled; `define` and `include_file`
statements recorded but not executed), and parses the Boolean expressions of `function`, `three_state`, `when`,
`next_state`, `clocked_on`, `clear`, `preset`, `enable`, and `data_in` with the precedence of the Liberty Reference
Manual (inversion, then XOR, then AND, then OR; juxtaposition is AND; `\"1A\"` names pins that start with a
digit). The model layer (`sn_lib_t`) resolves cells with scalar, bus, bundle, and power/ground pins (bus bits
expanded from `type` groups, nested per-bit overrides applied), `ff`, `ff_bank`, `latch`, `latch_bank`,
`statetable`, and `test_cell` groups including the `clear_preset_var` collision values, timing arcs with their
lookup tables resolved against templates (`sn_lib_table_lookup` interpolates and extrapolates linearly),
`internal_power` and `leakage_power` groups, area, capacitance and transition limits, and the library header
(units, `default_*` values, operating conditions, wire loads, `voltage_map`, `define`, `bus_naming_style`).
Everything it does not interpret stays reachable through the syntax tree. Missing and malformed attributes are
distinct states: a value that is present but unusable (a non-numeric number, an unparsable expression, an
unknown direction, a bus type with an impossible width or range, an unsorted table axis, a bad bank width) is
warned about, counted in `malformed_count`, left absent rather than inherited from a bus or bundle, and marks
its pin, state group, table, type, or cell `invalid` (`invalid_cells` totals them), and a malformed Boolean
yields false rather than an inherited value; unknown timing types keep
their name under `SN_LIB_TIMING_OTHER`. An interface must not be built from an invalid cell. Bus bits follow
the library's `bus_naming_style` and nested `pin(A[3:2])` range overrides are applied; `sn_lib_table_lookup3`
interpolates all three axes and the x/y helper returns NAN for three-dimensional tables. Only a syntax error
(including an unterminated comment or a read error), a missing `library` group, or memory exhaustion is fatal;
`sn_lib_ok` covers all three, and an allocation-injection test (`abc/test/sn/sn_liberty_oom_test.cc`) fails
every allocation in turn to keep that contract honest. The vendor tests read IWLS 2005 GSCLib, the sky130 library shipped with
OpenROAD, and the gf180, STM 90 nm, and Faraday libraries under `~/Projects/libs`; the cell functions of three
of them were compared exhaustively against ABC's own genlib conversions. Completeness for every Liberty
construct is not claimed: `include_file` is recorded but not executed, a second `library` group in a file is
ignored with a warning, and bus-level expressions are shared with the bits without bit selection. See
`sn_slang/sn_liberty_review.md` in the sibling frontend project for the September 7 correctness review and
its resolution.

Binary format version 15 embeds each library model of a design as its functional-only binary encoding
(below) instead of the Liberty text that versions 13 and 14 carried, so `@read` no longer re-parses the
library and a design imported from a `.snlib` file writes the same bytes as one imported from the `.lib` it
was made from. Versions 13 and 14 are still read.

A parsed model can be saved as a binary file (`sn_lib_write_binary_file`, `sn_lib_load_binary`) and reloaded
without re-parsing the text. The file holds the model only, not the syntax tree, so a loaded model has
`syntax == NULL` and no item ids; everything the model interprets is preserved bit for bit, cell IDs and all
indices are identical, and downstream consumers behave the same as with a text-parsed model. The file records
the size and hash of the library text it came from (`sn_lib_binary_identity`, `sn_lib_source_identity`) and ends
with a payload hash, so truncated, damaged, or foreign files are rejected before decoding. A functional-only file
(`sn_lib_binary_options_t.functional_only`) drops timing, power, leakage, tables, and templates and is a small
fraction of the full file: sky130 hs (72 MB text, 0.44 s to parse) becomes a 39 MB full file that loads in
36 ms or a 2 MB functional file that loads in 2 ms; NanGate45 (6.7 MB, 47 ms) becomes 5.4 MB in 4 ms or 1 MB
in 1 ms.

The frontend adapter in `sn_slang/src/sn_slang_liberty.h` generates interface-only Verilog before slang
elaboration. Scalar cells become compact `SN_GATE` objects; `snLibrary.h` compiles their supported functions
into shared expression graphs, and blasting expands those graphs into AIG nodes. No scalar gate module or
elementary SN function network is created. Vector macros use opaque module interfaces. The parser itself
remains independent of SN representation details. See the reviewed
[mapping roadmap](../../../../sn_slang/sequential_cells_plan.md) for binding ABC mapper results back to SN
and for the separate sequential-mapping and clock-abstraction work.

The maintainer's local unit tests live in `abc/test/sn/sn_test.cc`. These tests, their CMake registration,
binary fixtures, and temporary experiment artifacts are deliberately excluded from this source changeset;
the minimal sn_slang distribution likewise contains no test sources or fixtures. The coverage descriptions
here refer to the full development workspace, not files or test targets supplied to release users.
Those tests cover the checker's rejection of corrupted invariants, mapping and blasting behavior,
register optimization (including control polarity and constant negation), and the binary upgrade chain: the
version-7 fixture in `abc/test/sn/fixtures` must match `uart_v11.sn`, the same RTL written by the current frontend
and writer. A representation change that touches an invariant must update the corresponding corruption test there;
a format change should add a fixture pair. Behavioral coverage of the mapping passes lives in the sn_slang tree
(`map_dff_polarity_sim`, `map_srl_chains_sim`, `map_mem_registered_sim` simulate the RTL against the mapped design).
