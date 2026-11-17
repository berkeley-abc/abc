# Recorded ABC experiments, 17 November 2026

See the [method, results, limitations and reproduction instructions](../README.md).

| File | Contents |
|---|---|
| `primary.csv` | 19 designs × seven primary/reference arms |
| `sensitivity.csv` | 19 designs × five steps × four arms |
| `flow.csv` | 19 designs × five `C-S-S-R-S` arms |
| `portfolio.csv` | 19 designs × three equal-bank policies; HPWL was not measured |
| `inputs.json` | Common preprocessing hashes, CEC links and fixed bin counts |
| `proofs.json` | Hash-bound successful CEC outputs; local paths are replaced |
| `protocol.json` | Exact recipes, binaries/library, CPU and measurement policies |
| `summary.json` | Recomputable paired statistics and process CPU totals |
| `*_regression.json`, `timing_cache_checks.json` | Existing and added regression results |
| `files.sha256.json` | Content digests for the recorded data |

CSV delay is in ps; area and HPWL use the original ABC mapper/placer units.
An empty field means that quantity was not measured or not applicable. In
particular, selected portfolio CPU is not the cost of generating its full bank.
`abc_budget` denotes the published RS–RW–RF macro; `compress_budget` denotes
repeated compress2rs. Both use process-CPU stopping and complete-macro overshoot.
`source_proof` and `mapping_proof` are keys into `proofs.json`.

Some observations reuse identical inputs/endpoints and cached hash-bound proofs.
Recorded CEC outputs do not replace rerunning equivalence on the external AIGs.
No routed metric, power result, or successful `hyp` result is present here.
