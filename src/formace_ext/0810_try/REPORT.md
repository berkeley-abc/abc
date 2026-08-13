# MinUNSAT-guided ECO patch reconstruction

Run date: 2026-08-10

## Purpose and method

This isolated experiment tests whether ForMACE's exact MinUNSAT support
selection and interpolation can reconstruct the output functions produced by
ABC `runeco`. It preserves `runeco`'s patch and candidate interface while
reconstructing every patch output independently with `fm_inter -m`:

1. Extract one output cone from `patch.v` while preserving its full input
   interface.
2. Treat the function as the onset and its complement as the offset.
3. Treat each corresponding cross-copy input equality as one guarded group.
4. Find a minimum-cardinality UNSAT group set and interpolate over that
   selected vocabulary.
5. Assemble the outputs into a replacement patch and prove equivalence to R2
   and to the original `runeco` result.

For a Boolean function `f(d)`, the grouped problem is:

```text
f(d_A) = 1
f(d_B) = 0
d_A[i] = d_B[i]  for each enabled input group i
```

A minimum UNSAT group set is a minimum functional support for `f` relative to
the candidate divisors already present in `patch.v`. This experiment does not
replace `runeco` divisor discovery, search all G1 nodes, or optimize the union
of support across outputs.

## Reproduce

The inputs are the existing `0808_ECO/testNN/patch.v` results and the ICCAD
2021 ECO benchmark checkout. From the ABC repository root:

```bash
make -j4 ABC_USE_NO_READLINE=1
python3 src/formace_ext/0810_try/run_minunsat_eco.py \
  --output-timeout 300 --verify-timeout 180
```

Use `--case test01` for one case. Run the script with `--help` to override the
ABC binary, baseline, benchmark, results directory, or MinUNSAT input limit.
The committed machine-readable results are `results/summary.csv`,
`results/summary.json`, `results/output_details.csv`, and
`results/output_details.json`. Per-case BLIF, Verilog, and log files are
reproducible and ignored by Git.

## Outcome

The method is functionally viable: all 105 patch outputs across the 8 available
ICCAD ECO cases were rebuilt by `fm_inter -m`, and every result was equivalent
to both R2 and the baseline `runeco`-patched design.

It is not yet a beneficial direct replacement for `runeco`'s cube-based
function construction. Exact MinUNSAT removed no support variables in these
cases, and the proof interpolants can be substantially larger.

| Case | Outputs | Support, original -> selected | AIG ANDs, runeco -> MinUNSAT/interpolation | CEC |
|---|---:|---:|---:|---|
| test01 | 1 | 3 -> 3 | 2 -> 2 | PASS |
| test02 | 13 | 47 -> 47 | 41 -> 86 | PASS |
| test03 | 13 | 225 -> 225 | 1,823 -> 26,378 | PASS |
| test04 | 3 | 2 -> 2 | 0 -> 0 | PASS |
| test05 | 3 | 1 -> 1 | 0 -> 0 | PASS |
| test06 | 19 | 57 -> 57 | 48 -> 48 | PASS |
| test07 | 24 | 59 -> 59 | 48 -> 48 | PASS |
| test08 | 29 | 67 -> 67 | 30 -> 31 | PASS |
| **Total** | **105** | **461 -> 461** | **1,992 -> 26,593** | **8/8 PASS** |

The aggregate gate count is dominated by test03. Even without test03, the
prototype changes 169 AIG ANDs to 215. The measured interpolation time was
4.417 seconds in total; CEC took 4.359 seconds. These timings describe this
local run and are not intended as benchmark-quality performance measurements.

## Interpretation

For each output function `f(d)`, the experiment makes two copies of the
candidate inputs, constrains one copy to the onset and one to the offset, and
treats each cross-copy input equality as a guarded group. A minimum UNSAT set
of equality groups is exactly a minimum-cardinality functional support for that
output relative to the supplied candidate divisors. Interpolation over the
selected equality variables then gives an equivalent implementation.

Because every selected support count equals its original structural support
count, the tested `runeco` output functions contain no dispensable support
variables. That is useful negative evidence: applying the current MinUNSAT
objective after patch generation cannot improve divisor count on these cases.

The large test03 result also shows that minimizing support cardinality does not
minimize circuit area. A useful next experiment would move MinUNSAT earlier,
into divisor selection, use a global/weighted objective across patch outputs,
or add an implementation-cost-aware synthesis pass after interpolation.

## Verification performed

- Rebuilt ABC with the current local ForMACE extension.
- Passed `src/formace_ext/tests/fm_camus_api_test.sh`.
- Passed `src/formace_ext/tests/fm_inter_smoke.sh` for exact, subset-minimal,
  hybrid, and root-conflict cases.
- Ran independent CEC of every reconstructed integrated design against R2.
- Ran independent CEC of every reconstructed integrated design against the
  corresponding baseline `runeco` integrated design.

Detailed per-case and per-output data are in the committed CSV and JSON files
under `results/`.

## Isolation

The experiment runner, report, and generated results live below `0810_try` and
do not modify ABC source files. The original work was developed on branch
`experiment/0810-minunsat-eco`; switching branches can hide the committed
experiment without disturbing unrelated local work.
