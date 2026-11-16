# Frontend reproduction

The commands below reproduce the retained AGR and two-round PA algorithms and
generate new CPU-budgeted native ABC baselines. The runner evaluates all three
with the **same built executable**, mapper, Liberty library, and fresh-placement
policy. It does not invoke OpenROAD. It requires Python 3 on macOS or Linux and
has no Python package dependencies.

## Build and inputs

From the ABC checkout root:

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DABC_SKIP_TESTS=ON
cmake --build build -j4
python3 test/physical/regression.py --abc build/abc
python3 test/physical/reproduction_test.py
```

The normal `make -j4` build is also supported. Use the same build type for every
comparison. If Readline is unavailable, add `-DREADLINE_FOUND=FALSE` to CMake.

Provide one combinational binary AIGER file per design and a Liberty library.
The paper uses 20 saved, preprocessed EPFL AIGs and `merged_asap7_final.lib`.
Raw benchmark downloads are not necessarily byte-identical to these inputs.
`test/physical/endpoint_manifest.json` records their SHA-256 hashes and retained
AGR/PA2 endpoint hashes. The benchmark/library files are external inputs, not
embedded in the ABC source patch. In the accompanying research archive they
are in `review/pa_tg_20261107/inputs/`; pass that directory directly to the runner.
Keep any original benchmark and library license files with redistributed data.

## Direct synthesis commands

AGR uses the built-in placement step of 0.28 bin widths. This sets the initial
displacement scale of the placement update; it is not a synthesis effort limit.
No parameter is necessary for the primary reproduction:

```text
read design.aig
strash
read_lib cells.lib
agr
write_aiger agr.aig
```

The two-round PA reference uses the paper score and timing policy by default.
RW/RF timing is bounded; RS keeps strict dependency updates. The paper's `-c`
cluster mode remains optional after mapped placement and `pa_strash`. Other
operator controls retain their native ABC meanings. The direct recipe is:

```text
read design.aig
strash
read_lib cells.lib
pa_place
pa_rs -K 8 -N 2
pa_rw
pa_rf
pa_rs -K 8 -N 2
pa_rw
pa_rf
strash
write_aiger pa2.aig
```

The native ABC comparison repeats this complete cycle:

```text
resub -K 8 -N 2 -F 0
rewrite
refactor
```

It starts from the same input, runs at least one cycle, and stops at the first
cycle boundary where synthesis CPU reaches the larger of AGR's and PA2's CPU
for that design. It then normalizes and writes its endpoint. There is no
placement-guided acceptance, endpoint quality selection, or rollback. RS uses
the same cut/node/ODC limits as PA. Native ABC's timing behavior is its usual
level-preserving structural behavior; it does not have PA's physical score.
"Equal-time" thus means equal-or-longer CPU, with complete-cycle overshoot.

## Run the suite

```sh
python3 examples/physical/reproduce.py \
  --abc build/abc \
  --inputs /path/to/paper/inputs \
  --liberty /path/to/paper/inputs/merged_asap7_final.lib \
  --paper-inputs \
  --output results/frontend-default
```

The default is every `.aig` in the input directory. `--paper-inputs` rejects
mismatched inputs/libraries and checks known AGR/PA2 endpoint hashes. To use
different circuits, omit that flag. For a quick check, add `--designs ctrl,router`.
The primary paper suite has 20 designs, including `hyp`.

No step option is necessary. For separately labelled sensitivity runs use, for
example, `--step 0.26 --output results/frontend-step026`. This changes guidance
placement for AGR/PA, while fresh measurement placement remains fixed. Do not
choose the best guidance step separately for each design.

The worker is serial, alternates AGR/PA ordering across designs, disables user
ABC startup scripts, clears `ABC_*` overrides, and fixes common numerical thread
counts to one. Run without other synthesis/backend workers. Output-directory
locking prevents duplicate workers. Existing completed results may be resumed
with identical arguments and script/binary hashes. Failed records are preserved;
an interrupted attempt requires a new, explicitly labelled output directory.

CPU-based stopping can produce different native ABC cycle counts on another
machine. To reproduce the **same native work and endpoint**, use:

```sh
python3 examples/physical/reproduce.py \
  --abc build/abc --inputs /path/to/paper/inputs \
  --liberty /path/to/paper/inputs/merged_asap7_final.lib --paper-inputs \
  --replay-cycles results/frontend-default/budgets.json \
  --output results/frontend-fixed-cycles
```

Fixed-cycle replay does not promise CPU equality on the new machine. The output
protocol identifies it explicitly. Every executed command is also saved, so an
individual endpoint can be replayed without the controller.

The included `reference_cycles.json` is the measured 20-design workload from the
new-build reference run. Pass it to `--replay-cycles` instead of a private output
file to replay that workload. `reference_results.json` contains all per-design
metrics, endpoint hashes, CPU observations, proof status and paired summaries.
See `VALIDATION.md` for its aggregate results. That saved measurement record
retains its original explicit command spelling; the current simplified commands
select the identical fixed policy, as verified by endpoint replay. The reference timings are
host-specific measurements, not numeric assertions for another machine.

## Fresh measurements and equivalence

Each endpoint is evaluated in independent ABC processes. AIG measurement:

```text
read optimized.aig
strash
print_stats
pa_place
pa_stats
```

Mapped measurement:

```text
read optimized.aig
strash
read_lib cells.lib
&get
&nf
&put
stime
write_blif mapped.blif
pa_place
pa_stats
```

Mapped HPWL is a frontend proxy, not routed wirelength. The evaluator uses
internal cell coordinates without detailed pin offsets. Explicit PI/PO terminal
coordinates are omitted: PI-driven nets retain the box of their internal sinks,
while PI endpoints and PO endpoints add no terminal distance. This represents
freely located I/O, not fixed boundary pins.

These use the retained frontend's default, I/O-unconstrained placement policy;
canvas sizing follows the same policy for every endpoint. They do not impose
the backend's fixed physical pins or fixed core. Optimization coordinates never
serve as final HPWL. The driver requires fresh overflow at or below 10%, records
AIG nodes/levels/HPWL and mapped area/cell-delay/HPWL, and saves the mapped netlist.
Cell delay is in ps and excludes routed interconnect delay. HPWL and area use
the placer's and Liberty/ABC's respective units; ratios require identical inputs
and measurement settings.

The driver also strashes the mapped result into `mapped_function.aig` and checks
both source-to-optimized and optimized-to-mapped-function equivalence. CEC uses
a 60-second limit by default (`--cec-timeout` changes it). A timeout is recorded
as **unproved**, never equivalent. Counterexamples invalidate the endpoint.
The summary reports the matched metric cohort and fully verified cohort separately.
Use a labelled verification follow-up for timeouts; do not silently replace them.

## Timing and interpretation

The runner measures live process user+system CPU using OS counters, validated
against Python's own process-CPU clock. On macOS it converts Mach time units;
on Linux it uses the process CPU clock. ABC's `time` command uses wall time on
POSIX and is deliberately not used for CPU budgeting.

* **Synthesis CPU:** initial guidance placement, all candidate generation and
  evaluation, incremental updates, and final normalization. Any future internal
  mapping performed inside the optimization command is charged here too.
* **Process CPU:** the entire synthesis process, additionally including startup,
  common input loading/strashing, Liberty loading and output writing. All three arms load the library;
  native ABC's transformations do not consult it.
* **Evaluation and CEC CPU:** separately recorded, excluded from optimization
  budgets consistently. Evaluation includes the one common endpoint mapping and
  fresh AIG/mapped placement. Neither AGR nor PA2 internally maps candidates.

The lightweight controller observes complete commands/cycles; its process-side
command-handling overhead is included. It never restarts ABC between cycles.
CPU columns refer to ABC processes; Python orchestration and report generation
are outside these columns. The native baseline still receives at least the full
reference ABC synthesis CPU before stopping.
Timeouts and the cycle safety cap produce recorded failures, not early successful
endpoints. Synthesis/measurement wall limits default to 600 seconds per process.

Outputs include `protocol.json` (versions, hashes and settings), `status.json`,
`budgets.json`, `results.json`, `results.csv`, `summary.json`, and `REPORT.md`.
Per-design directories retain commands, logs, process timing, AIGs, mapped BLIFs,
and verification records. Summary comparisons use matched designs, include every
per-design regression, and report arithmetic/geometric CPU means. No measurement
or timing is substituted from historical runs.

The integration reproduces the retained synthesis endpoints. New upstream
mapping or placement changes can alter downstream metrics, so new-build results
must be labelled separately from published/archived paper numbers. Use this suite
to compare future variants against unchanged AGR, PA2, and native ABC on the same
build. OpenROAD is unnecessary for this development loop; final routed PPA claims
still require subsequent physical implementation.

For an intentionally changed AGR algorithm, omit `--paper-inputs`: that option
also enforces the retained algorithm's endpoint hashes. The ordinary protocol
still records every input/library hash, which must match the baseline. Keep the
changed binary and output directory separate, and do not interpret an expected
new AIG as an integration regression against the frozen endpoint manifest.

## Practical synthesis flows

Use [FLOW.md](FLOW.md) and `reproduce_flow.py` for the common
`C -> S -> S -> R -> S` comparison with three AGR slots, three PA2 slots,
and CPU-budgeted repeated-compression or mixed native ABC slots. The guide
includes direct command expansions, fixed-work replay, all-design historical
results, and the precise I/O-unconstrained meaning of the HPWL proxy.
