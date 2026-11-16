# OpenROAD reproduction

This optional backend accepts the **unmapped `optimized.aig`** produced by
[standalone reproduction](../REPRODUCE.md) or [practical flows](../FLOW.md).
It maps that endpoint once, then places, repairs and routes it. It does not run
ORFS's full logic-synthesis recipe or repeat the common `dc2` preprocessing.
Frontend experiments do not require OpenROAD.

## Toolchain and physical settings

Use Docker with Linux/amd64 support, including on Apple Silicon. Build the
pinned public sources in a new directory (this builds tools, not benchmarks):

```sh
bash examples/physical/openroad/build-image.sh /path/to/new/orfs-build
```

This produces `agr-openroad:paper`. It pins ORFS at
`1ff0d0814e153b15ba5cdcf591e11b0e2589f169`, OpenROAD at
`f9a6acaf77a58c03a8d1284d3fd64b33d0cfd3bc`, Yosys at
`5bafeb77dc71e054fa331ab9efa613e6fb0a1c49`, and its ABC at
`131a50dd773f21ebbfc51da1d182438382a04209`. The recursive source checkout includes
the ASAP7 technology files. Dependency/tool compilation is limited to four
threads. Allow several GB of disk/RAM and time for this one-time build.

The historical image's `0c19e9` tag was local, **not a downloadable Docker Hub
release**. The source-build route avoids depending on that private tag.
[toolchain.json](toolchain.json) records the original binary hashes and source
revisions. A fresh build can have different binary hashes because its compiler
and system dependencies differ. The runner records actual hashes and requires
the saved flow-script hashes and tool versions: OpenROAD
`24Q3-12068-gf9a6acaf77`, Yosys `0.60`. If the archived image is already installed,
`--image sha256:17bf7b7c1d734a2da29c2af635677bc11cf446d250111e248a35fb994834cf42`
uses it directly. This ID is local provenance, not a registry pull digest.

Only `synth.tcl`, `abc_speed.script` and `io_placement.tcl` override the image.
The mapping script executes `&get -n; &st; &nf; &put` once. Yosys only translates
the exported gate-level Verilog, maps it, and handles tie/buffer cells.

| Setting | Paper value |
|---|---|
| Platform | ASAP7 7.5-track RVT, `CORNER=BC`, `LIB_MODEL=NLDM` |
| Liberty | Five RVT FF NLDM files in the image; 0.77 V, 0 degrees C, 1 ps |
| Excluded synthesis cells | `*x1p*_ASAP7*`, `*xp*_ASAP7*`, `SDF*`, `ICG*` |
| Die/core | Frozen per design in [designs.json](designs.json), identical across methods |
| Reference utilization | 50%; 40% for `dec`. Actual utilization depends on the netlist |
| Placement density | 0.50 |
| Physical IO | Frozen primary pin layout, identical across methods; M4/M5 |
| Placement seed | `OR_SEED=0` |
| Signal routing layers | M2 through M7; image defaults for repair, routing and extraction |
| Virtual-clock period | 5000 ps; `div`/`sqrt`: 60000 ps; `hyp`: 300000 ps |
| SDC IO delays | Zero; no extra input-driver/output-load constraints in SDC |
| Power | OpenROAD/OpenSTA default activity, without a VCD |

[constraint.sdc](constraint.sdc) is expanded with the period for each design:

```tcl
create_clock -name virtual_clk -period 5000
set_input_delay 0 -clock virtual_clk [all_inputs]
set_output_delay 0 -clock virtual_clk [all_outputs]
```

ORFS still supplies its standard **mapping** constraints: driver
`BUFx2_ASAP7_75t_R` and load 3.898 fF. These are distinct from the SDC IO delays.
The image's BC configuration labels temperature as 25 C; the actual FF Liberty
tables used have the 0 C operating condition. Both are preserved unchanged.
The backend uses the image's original Liberty files and dont-use filter, not
the frontend's merged serialization; see [library details](../REPRODUCE.md#exact-liberty-library).

AGR/PA guidance placement in ABC uses floating IO. The physical backend first
runs global placement with IO skipped, installs the saved pins, then runs
placement with fixed IO. The backend canvas/pins are not fed back into synthesis.
Do not derive a smaller canvas independently for each optimized netlist.

## Check, map, then route

From the ABC checkout root, after frontend reproduction, for example:

```sh
python3 examples/physical/openroad/run.py \
  --abc build/abc --design ctrl --cohort single \
  --aig results/standalone/ctrl/agr/optimized.aig \
  --output results/backend-single/ctrl/agr --stage check
```

`check` exports Verilog, verifies all expected ports, writes the exact config,
SDC and pins, records image binary hashes, checks versions/script hashes, and runs
`make -n` through the initial-floorplan target. It does **not** place or route the design.

Use the same arguments with `--stage floorplan` to perform the single endpoint
map and initial floorplan. This also runs ABC CEC between the input AIG and the
mapped netlist. The proof copy removes Yosys attributes and resolves the two
library-defined tie cells; the backend netlist itself is unchanged. A failed or
timed-out proof does not authorize routing. Source-to-optimized equivalence is
checked by the frontend runners and must also pass.

Finally, replace the stage with `--stage finish` to execute placement through
routing/final reporting. Nothing runs in the background. To reproduce all
standalone methods, repeat for `agr`, `pa2` and `abc_budget`, using a separate
output directory for each endpoint and design. The 20 benchmark names are in
`designs.json`; preserve their AIG port ordering and names.

For practical flows use `--cohort flow`, and the endpoints from
`reproduce_flow.py` (`agr`, `pa2`, `abc_c`, `abc_mix`). For example:

```sh
python3 examples/physical/openroad/run.py \
  --abc build/abc --design ctrl --cohort flow \
  --aig results/practical-default/ctrl/agr/optimized.aig \
  --output results/backend-flow/ctrl/agr --stage check
```

Then run `floorplan` and `finish` explicitly as above. The two cohorts share the
same physical boundaries, SDC and flow; `--cohort` selects the recorded resource
limits. Most runs use 2 cores, larger designs 3; flow `hyp` uses 10 cores/24 GiB,
and single-block `hyp` uses 3 cores/30 GiB. These limits are listed per design in
`designs.json`. Provision sufficient Docker VM RAM plus host reserve. The runner
launches one container at a time; external parallelism must reserve the sum of
all requested memory and cores. Run `hyp` alone on memory-limited machines.

Mapping plus routing has a cumulative 7200-second active-time limit using the
host monotonic clock (excluding system sleep on macOS). Queue time and CEC are
excluded. Attempts and failures are retained; the runner refuses to overwrite
a recorded stage. Use a new, labelled directory for a justified retry, rather
than deleting the failed result. Keep the same input, binary and package when
continuing from one stage to the next.

## Outputs and comparison

`metrics.json` contains final instance area, delay (clock period minus worst
setup slack), default-activity power, routed wirelength, DRC count, and HPWL at
global placement, detailed placement, routing and final reporting. HPWL sums
signal-net terminal bounding boxes, **including physical IO** and excluding
power/ground nets. It is different from the ABC-side mapped-HPWL proxy, which
uses abstract placement rather than routed physical pin geometry.

The runner checks the die/core and pin rectangles against the frozen layout at
all four reported stages. A nonzero final routing DRC count is a failed run.
Raw ORFS logs, metrics, databases, generated inputs, commands and CEC logs remain
in the output directory. Compare complete matched-design cohorts and retain
failed/time-limited runs in the coverage report; do not substitute zeros.

These scripts reproduce the backend setup. Exact paper endpoint identity also
requires the recorded frontend inputs and recipes: fresh CPU-budgeted ABC
baselines can choose different macro counts on different machines. Use the
fixed-recipe replay described in the frontend guides when comparing archived
endpoints. Setup validation uses the archived experimental binaries; rebuilding all tools
from source and rerunning full physical experiments are separate operations.
