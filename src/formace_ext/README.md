# ForMACE ABC extension

This directory contains the ForMACE additions to ABC: variable-minimizing
combinational interpolation, interpolation-based safety checking with a
minimized latch boundary, interpolation-based ECO patch construction, and the
shared CaDiCaL-backed grouped-constraint solver.

## Commands

- `fm_summary` reports basic statistics for the current ABC network.
- `fm_minunsat input.cnf` computes an exact minimum-cardinality UNSAT clause
  subset directly from DIMACS. `-g input.groups` enables hard clauses and
  multi-clause optional groups; no CNF-to-AIG conversion is needed.
- `fm_inter` builds a combinational interpolant from an onset/offset pair.
  It supports exact minimum-cardinality (`-m`), subset-minimal (`-c`), and
  baseline-support hybrid (`-y`) boundary selection.
- `fm_int` extends ABC's forward interpolation model checker with original
  (`-o`), exact minimum-boundary (`-m`), and hybrid (`-y`) modes.
- `fm_eco` runs the DAC'18 ECO flow with Craig-interpolant patch functions.
  Its default uses ABC's original support selector; `-m` selects exact
  minimum-cardinality additional support with grouped MinUNSAT, while `-a`
  keeps assumption minimization but skips `Acb_FindSupport()` for ablation.
- The upstream `runeco` command also has a ForMACE `-g` mode for exact
  minimum-cardinality support shared by all fixed target relations. It uses
  the multi-oracle equivalent of `(B_0 OR ... OR B_(k-1)) AND Eq_S`, then
  constructs SOP patch functions over the selected common support.

The upstream `inter` and `int` commands retain their normal behavior.

## Build and test

From the ABC repository root:

```bash
make -j4 ABC_USE_NO_READLINE=1
bash src/formace_ext/tests/fm_camus_api_test.sh
bash src/formace_ext/tests/fm_minunsat_test.sh
bash src/formace_ext/tests/fm_inter_smoke.sh
bash src/formace_ext/tests/fm_int_smoke.sh
bash src/formace_ext/tests/fm_runeco_minimum_test.sh
bash src/formace_ext/tests/fm_runeco_global_test.sh
bash src/formace_ext/tests/fm_eco_test.sh
```

Or run the complete focused suite with one command:

```bash
bash src/formace_ext/tests/run_all.sh
```

The grouped-DIMACS benchmark driver is optional:

```bash
bash src/formace_ext/tests/fm_camus_grouped_benchmark.sh \
  FILE.cnf FILE.groups minimum-all
```

## Documentation

- [Combinational interpolation](guides/fm_inter.md)
- [Interpolation model checking](guides/fm_int.md)
- [Minimum UNSAT for DIMACS CNF](guides/fm_minunsat.md)
- [Interpolation-based ECO](guides/fm_eco.md)
- [CAMUS/CaDiCaL minimum-search algorithms, API, and architecture](guides/camus.md)
- [Change log](CHANGELOG.md)

## Source layout

- `formace.c`: command registration and the `fm_summary`, `fm_inter`, and
  `fm_int` command implementations.
- `fm_minunsat.h`, `fm_minunsat.c`: DIMACS/group parsing and the direct
  `fm_minunsat` shell command.
- `fm_eco.h`, `fm_eco.c`: `fm_eco` parsing and selector-free ECO proof
  interpolation.
- `fm_camus.h`, `fm_camus.c`: the in-memory grouped-constraint API and exact
  or subset-minimal MUS selection.
- `module.make`: ABC build integration.
- `tests/`: focused C/API tests, shell regression tests, and small fixtures.

Reusable experiment runners live outside the ABC source tree under the
workspace's `try/tools/` directory. In particular, the MinUNSAT ECO runner is
`try/tools/0810_minunsat_eco/run_minunsat_eco.py`.

Keep generated build products and test output out of source control. Prefer
extension-local changes; changes to upstream ABC internals should remain
narrow and opt-in so ordinary ABC commands are unaffected.
