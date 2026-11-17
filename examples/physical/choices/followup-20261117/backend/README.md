# Followup physical controls

`designs.json` freezes the die, core, pins, clock period and per-job resources
for all 20 designs. `common-inputs.json` records the common graph and neutral
mapping hashes used to generate those controls. One original-NF mapping of the
common input determines each die at 50% utilization (40% for `dec`). A single
neutral placement at density 0.60, followed by M4/M5 pin placement, determines
the pins. Every compared synthesis method receives exactly that geometry.

`backend.patch` changes the published backend to density 0.60, disables OpenROAD
port buffering, adds a separate core-net HPWL diagnostic, and anchors extraction
of total HPWL. The latter prevents the core-only tag from being mistaken for the
all-net metric. The experiment's native wrapper makes the same extraction
correction. Yosys can still insert library buffers for constant outputs.

To make a separate package from the repository root, choose a new directory:

```sh
mkdir /tmp/abc-choice-backend
cp -R examples/physical/openroad /tmp/abc-choice-backend/openroad
cp -R examples/physical/data /tmp/abc-choice-backend/data
cp examples/physical/choices/followup-20261117/backend/designs.json \
  /tmp/abc-choice-backend/openroad/designs.json
patch -p1 -d /tmp/abc-choice-backend/openroad \
  < examples/physical/choices/followup-20261117/backend/backend.patch
```

Follow the published OpenROAD instructions with this package's `run.py` and
the independently verified plain-AIG endpoints. Use the same package for every
arm. The pinned toolchain, mapping script, libraries, routing settings and
power activity assumptions are unchanged. The research campaign uses native
builds of those pinned sources in place of Docker; actual executable hashes
are retained in its execution records.

Source-to-endpoint, endpoint-to-mapped and mapped-to-final-netlist equivalence
must pass before counting a result. The published runner supplies the first
backend mapping check; final-netlist CEC is an additional campaign check.
Report total final HPWL and default-activity power, with core-only HPWL clearly
separate. A failed proof, nonzero final DRC count, unrouted net, or timeout is
a coverage failure, not a zero-gain numerical observation.

This file records a reproducible protocol change from the paper. It does not
claim that the ongoing routed campaign has completed or met the target.
