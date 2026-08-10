# 0810 MinUNSAT ECO experiment

This isolated prototype tests whether ForMACE's exact MinUNSAT support selection
and interpolation can reconstruct the output functions produced by ABC
`runeco`. It reads the existing `0808_ECO/testNN/patch.v` files, reconstructs
each patch output with `fm_inter -m`, assembles a replacement patch, and runs
CEC both against the repaired R2 design and against the original `runeco`
result.

The experiment does not modify ABC source files. Its inputs are the existing
`runeco` results and ICCAD 2021 ECO benchmark checkout.

## Run

From the ABC repository root:

```sh
make -j4 ABC_USE_NO_READLINE=1
python3 src/formace_ext/0810_try/run_minunsat_eco.py \
  --output-timeout 300 --verify-timeout 180
```

Use `--case test01` for a focused run. Run `--help` to override the ABC binary,
baseline, benchmark, results directory, or MinUNSAT input limit.

Machine-readable summaries are kept in `results/summary.csv` and
`results/output_details.csv`. Per-case generated BLIF/Verilog/log files are
ignored by Git because they are reproducible and currently occupy about 7 MB.

## Result

All 8 cases and all 105 patch outputs were reconstructed, and every integrated
design passed both CEC checks. MinUNSAT selected 461 of 461 structurally used
per-output inputs, so it proved that `runeco`'s functions already had minimum
functional support within their candidate interfaces. See `REPORT.md` for the
size results and interpretation.

## Undo

This work is isolated on branch `experiment/0810-minunsat-eco`. Switching back
to `master` hides the committed experiment while preserving unrelated local
work:

```sh
git switch master
```

The ignored generated case directories can be regenerated at any time. If they
are no longer wanted, remove only
`src/formace_ext/0810_try/results/test01` through `test08`.
