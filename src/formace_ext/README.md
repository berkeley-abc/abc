# ForMACE ABC extension

This directory contains the ForMACE additions to ABC: variable-minimizing
combinational interpolation, interpolation-based safety checking with a
minimized latch boundary, and the shared CaDiCaL-backed grouped-constraint
solver.

## Commands

- `fm_summary` reports basic statistics for the current ABC network.
- `fm_inter` builds a combinational interpolant from an onset/offset pair.
  It supports exact minimum-cardinality (`-m`), subset-minimal (`-c`), and
  baseline-support hybrid (`-y`) boundary selection.
- `fm_int` extends ABC's forward interpolation model checker with original
  (`-o`), exact minimum-boundary (`-m`), and hybrid (`-y`) modes.

The upstream `inter` and `int` commands retain their normal behavior.

## Build and test

From the ABC repository root:

```bash
make -j4 ABC_USE_NO_READLINE=1
bash src/formace_ext/tests/fm_camus_api_test.sh
bash src/formace_ext/tests/fm_inter_smoke.sh
bash src/formace_ext/tests/fm_int_smoke.sh
```

The grouped-DIMACS benchmark driver is optional:

```bash
bash src/formace_ext/tests/fm_camus_grouped_benchmark.sh \
  FILE.cnf FILE.groups minimum-all
```

## Documentation

- [Combinational interpolation](guides/fm_inter.md)
- [Interpolation model checking](guides/fm_int.md)
- [CAMUS/CaDiCaL API and architecture](guides/camus.md)
- [Change log](CHANGELOG.md)
- [MinUNSAT ECO experiment](0810_try/REPORT.md)

## Source layout

- `formace.c`: command registration and the `fm_summary`, `fm_inter`, and
  `fm_int` command implementations.
- `fm_camus.h`, `fm_camus.c`: the in-memory grouped-constraint API and exact
  or subset-minimal MUS selection.
- `module.make`: ABC build integration.
- `tests/`: focused C/API tests, shell regression tests, and small fixtures.
- `0810_try/`: the reproducible MinUNSAT-guided ECO experiment.

Keep generated build products and test output out of source control. Prefer
extension-local changes; changes to upstream ABC internals should remain
narrow and opt-in so ordinary ABC commands are unaffected.
