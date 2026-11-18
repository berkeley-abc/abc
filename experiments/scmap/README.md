# Reproducing the fast SCMap comparison

This is the revised, preprocessed-input comparison, not the original raw-AIG
evaluation. It covers 19 EPFL combinational designs (all except `hyp`) on
ASAP7 RVT FF, Nangate45 typical and SKY130HD TT. It schedules 285 ABC flows,
57 independent `&nf` floorplan calibrations and 285 measured OpenROAD routes.
The unit of comparison is a design/library pair; all five arms stay together.

| Arm | Measured mapper | Difference from default |
|---|---|---|
| nf | `&nf` | Reference mapper. |
| scmap | `&scmap` | Default electrical mapper. |
| Q | `&scmap -q` | Screen seed covers and window checkpoints, then confirm finalists. |
| R | `&scmap -r` | Widen the seed search and try a cover-based remap. |
| T | `&scmap -T <floor_ps>` | Try more remapping and recover area under an adaptive target. |

Every arm reads the **same** Liberty files with `read_lib -G 250 -a`;
the ASAP7 exclusions and merge order are in [common.py](common.py).
From the raw AIG the shared prefix is
`strash; &get; &nf; &put; topo; strash; &get; &dch2 -p`. This first
`&nf` is preprocessing; only the terminal mapper changes. We hash the
intermediate BLIF and check that all arms have the same prefix.
For T, the floor is 0.88 times this pair's *fresh* reference delay after
sizing. T reports the effective target: the larger of the floor and
its own untargeted delay plus 0.01 ps. Verbose flags only record diagnostics.
None of these arms runs single-edit full-flow lookahead.

The shared suffix is `&put; topo; stime -c`, then
`mfsmap -e -R 2 -N 500 -C 1000 -M 2000 -I 10 -O 10; topo; stime -c`,
then `buffer -c; topo; stime -c; upsize -c; dnsize -c; stime -c`.
We save BLIF at all three endpoints and independently check each against
the raw AIG using `cec -n`. The command timer records process CPU, not
concurrent wall time. Mapping CPU includes the terminal mapper, `&put`
and `topo`; complete ABC CPU also includes loading, preprocessing, I/O
and the suffix, but excludes equivalence proofs.

## Inputs and build

Use Linux, Python 3.11 or newer, Git, GCC/G++, CMake, Ninja, `taskset`,
Yosys (campaign: 0.33) and OpenROAD. [inputs.json](inputs.json) pins the ABC,
EPFL and OpenROAD revisions and SHA-256 hashes of every selected AIG, Liberty,
LEF, platform variable, track, PDN, RC and extraction file. Fetch these from
their upstream repositories; no third-party libraries or binaries are vendored.
Use the ABC checkout containing this directory. For example, from its root:

```sh
kit=$PWD/experiments/scmap
work=$PWD/scmap-work
mkdir -p "$work"
git clone --filter=blob:none https://github.com/lsils/benchmarks.git "$work/benchmarks"
git -C "$work/benchmarks" checkout 40fa98f9a9ef0439f263bbf78c682aabfb717889
git clone --filter=blob:none https://github.com/The-OpenROAD-Project/OpenROAD.git "$work/OpenROAD"
git -C "$work/OpenROAD" checkout 61fa3981efaf7f969ece4cb7098a44be29b80422
git -C "$work/OpenROAD" submodule update --init --recursive
python3 "$kit/build.py" --source "$PWD" --build "$work/release" -j 4
```

Build OpenROAD following its [pinned build instructions](https://github.com/The-OpenROAD-Project/OpenROAD/blob/61fa3981efaf7f969ece4cb7098a44be29b80422/docs/user/Build.md),
or supply an existing executable of that revision. The runner checks the
OpenROAD version and all pinned input digests before dispatch. Copy the
**same** ABC release, timing executable and build manifest to all shards;
independent compiles can differ even just in the compiled-in timestamp.

## Run and collect

```sh
python3 "$kit/campaign.py" plan --shards 2 --shard 0
python3 "$kit/campaign.py" run --shards 2 --shard 0 --cores 64 \
    --out "$work/shard-0" --runner "$work/release/timed_commands" \
    --benchmarks "$work/benchmarks" --platforms "$work/OpenROAD" \
    --openroad "$work/OpenROAD/build/bin/openroad"
```

Run shard 1 with `--shard 1` and a separate output directory. Shards 0 and 1
own 29 and 28 pairs respectively. For one machine omit both shard options and
set `--cores` to the available physical cores (at least four). For a small
end-to-end check add, for example, `--libraries nangate45 --designs ctrl`.
The scheduler counts a physical core only once, pins each ABC job to one,
and gives each physical job four distinct cores (one thread for STA).

Calibration uses the reference final netlist at nominal 30% utilization.
Only a documented baseline placement/global-routing congestion error permits
20%, then 15%. Measured arms reuse its die/core, pin placement, driver, PO
load (four driver input capacitances), detailed-routing seed 42, and period
(105% of the calibrated extracted delay, rounded **up** to 0.001 ps).
The same [flow](flow.tcl) does placement, repair, detailed routing and RC
extraction. Qualification requires a routed design, zero DRC and antenna
violations, equivalence of both exported and routed logic using actual Liberty
functions, and [timing replay](replay.tcl) with complete connected-signal
parasitics. Timing/electrical misses are still reported, not discarded.

Each shard writes its immutable input/tool manifest, dependency graph,
per-command timings, ABC scripts, netlists, proof logs, calibration, ODB,
SPEF and SDC. A job is accepted only after its verified result is sealed
with a hash. Rerun the same command at the same paths to resume interrupted
work; `--retry-failed` explicitly retries failures and retains failed attempts.
Failed calibration blocks its dependent routes, not the other pairs.

```sh
python3 "$kit/collect.py" "$work/shard-0" "$work/shard-1" \
    --check-artifacts --out "$work/report"
```

The [evidence](evidence/) contains a dated snapshot, not an estimate of
unfinished jobs. `measurements.csv` has one row per arm and pair;
`calibrations.csv` has one row per pair; `snapshot.json` records coverage
and tool provenance. Blank values are unmeasured. Time columns distinguish
ABC process CPU from OpenROAD wall time (placement through extraction;
export, proof and replay are outside that time). For an area or delay
comparison divide each candidate by **that pair's** measured `nf` value and
take the geometric mean of the paired ratios. Report the matched count;
never substitute calibrations or earlier measurements for missing routes.
