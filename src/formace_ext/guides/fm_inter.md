# `fm_inter`: combinational interpolation

## What Was Added

`fm_inter` is a ForMACE extension command for single-output combinational
interpolation. It keeps ABC's upstream `inter` command unchanged.

It has three modes:

- `-m` (`minvar`) searches all paired primary inputs for an exact
  minimum-cardinality shared set before interpolation using the in-memory
  CaDiCaL-backed CAMUS implicit-hitting-set API.
- `-c` finds one CAMUS-style subset-minimal shared set.  It can be faster, but
  is not guaranteed to have minimum cardinality.
- `-y` (`hybrid`) derives a normal ABC interpolant first, searches only over
  that interpolant's PI support with the same exact minimum search,
  and falls back to all PIs if the restricted set does not preserve UNSAT.

The output replaces ABC's current network. It preserves the onset's complete
PI interface for ordinary ABC verification, while only the reported
interpolant support is functionally used.

## Build

From the ABC fork root:

```bash
make -j4 ABC_USE_NO_READLINE=1
```

## Use

Pass onset and offset networks explicitly:

```bash
./abc -c "fm_inter -m onset.blif offset.blif; write_blif minvar.blif"
./abc -c "fm_inter -c onset.blif offset.blif; write_blif mus.blif"
./abc -c "fm_inter -y onset.blif offset.blif; write_blif hybrid.blif"
```

`fm_inter` also follows ABC's one-file convention: the current network is the
onset and the argument is the offset. With no network arguments, ABC reads the
current network's external spec and complements it as the offset.

Useful options:

```text
-m       exact minvar search over all paired PIs
-c       CAMUS-style subset-minimal shared-PI search
-y       hybrid search from baseline interpolant support
-L num   maximum candidate PIs for exact search (default: 16)
-v       print ABC proof-interpolation statistics
-h       print usage
```

For example, the included small pair has an irrelevant `z` input:

```bash
./abc -c "fm_inter -m -L 3 src/formace_ext/tests/data/on_xor_unused.blif src/formace_ext/tests/data/off_xnor_unused.blif; ps"
```

It reports `x y z` as minvar candidates and `x y` as both the selected set and
the resulting interpolant support.

## Verify A Result

For a saved result `result.blif`, check onset implication and offset exclusion:

```bash
./abc -c "read_blif offset.blif; strash -i; write_blif offset_inv.blif"
./abc -c "miter -i onset.blif result.blif; iprove"
./abc -c "miter -i result.blif offset_inv.blif; iprove"
```

Both proof commands should report `UNSATISFIABLE` for the supplied smoke-test
examples.

## Current Scope And Limits

- Both input networks must be combinational, single-output, and have the same
  PI count, PI order, and PI names.
- `minvar` is an exact CAMUS-style implicit-hitting-set search. `-L` prevents an
  accidental exponential search; increase it only for deliberately small test
  cases.
- `hybrid` is minimum-cardinality only within its baseline-support candidates;
  it can fall back to global minvar if that support is insufficient.
- A root-clause conflict can prevent ABC's proof store from producing a proof.
  When the onset depends only on the selected PIs, the extension returns that
  onset as a valid interpolant; otherwise it reports failure and leaves the
  current network unchanged.
- Multi-output and sequential circuits are not in this first integration.
- All three selection modes invoke the ForMACE-owned, CaDiCaL 2.2.0-backed
  CAMUS API. They do not invoke the historical CAMUS executable or create
  DIMACS files. See [the CAMUS guide](camus.md) for the integration
  architecture.

## Smoke Test

```bash
bash src/formace_ext/tests/fm_inter_smoke.sh
```

The script runs `minvar`, CAMUS MUS, `hybrid`, and the root-conflict fallback,
checks the selected support, and verifies each result with ABC `miter` and
`iprove`.
