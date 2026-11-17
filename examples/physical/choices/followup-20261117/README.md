# Bounded-choice followup

These measurements use `d04b3c72fffe5f999320e41323aecfe46a8fba50` and the frozen
command `agr -c -b -r -m -W 0.25 -H 3 -T 300`, at step 0.28. They include both
placement-consistency fixes. Every method receives common `dc2` and
`&fraig -C 10000` preprocessing and the exact PR611 library. Positive percentages
are `100 * (1 - geometric_mean(candidate / reference))`.

## Frontend results

| Reference | Designs | Mapped area | Cell delay |
|---|---:|---:|---:|
| Original PA2 | 20 | 14.98% | 12.99% |
| Original AGR | 20 | 11.46% | 12.16% |
| CPU-matched published RS–RW–RF | 20 | 15.74% | 16.94% |
| External conventional portfolio | 19 | 2.93% | −6.35% |

The conventional portfolio uses the earlier fixed external recipe bank; it has
no `hyp` endpoint. Its bank and selector differ from the native command. The
negative delay value means that native is slower. The full gain is a search and
resynthesis result, not an isolated geometric contribution by AGR.

On the same 19 designs as the archived experiment, mapped HPWL/area/delay improve
14.55%/15.70%/13.19% over PA2, 10.78%/12.05%/12.80% over original AGR, and
14.90%/16.39%/17.29% over the newly CPU-matched reference. HPWL is remeasured with
the original ABC binary, fixed common-input bins, and preserved BLIF order. It
is an area-scaled ABC estimate, not a measurement on the backend die.

`hyp` reaches its choice deadline after 301.05 seconds and returns plain
corrected AGR. Its mapped area and delay are 14317.55 and 313688.00 ps, identical
to that plain endpoint. It contributes zero gain from the extra choice stage
and remains in the 20-design area/delay aggregate. Source and mapping proofs
pass for every included endpoint. There is no newly recorded external mapped
HPWL measurement for `hyp` in this bundle.

Across 20 designs, the native command uses 1112.67 process-CPU seconds, versus
101.97 for original AGR and 99.22 for PA2. The 19-design native total is 750.39
seconds. CPU-matched RS–RW–RF uses 1116.86 seconds and receives each design's full
native allowance plus final mapping. Its repeated script converges; that is not
an equal-search comparison. Proof time is excluded from these CPU totals.

The gains are not uniform. Against PA2 on all 20 designs, median area/delay
improvements are 5.86%/3.06%; removing the best two designs separately for each
metric leaves 9.85%/4.25%. Paired-design 95% bootstrap intervals are
[7.34%, 23.14%] and [2.09%, 25.13%]. Area improves on 18 designs and ties on one;
delay improves on 13 and ties on one. The summary records these statistics for
every comparison.

## Independent holdout

The guarded policy was frozen before evaluating the supplied 24 MCNC/ISCAS
circuits. No parameter or placement-step selection uses their results. All 24
common inputs were independently regenerated with the pinned original ABC;
their AIGER graph payloads match the supplied inputs. The PA2, AGR and
compress2rs-twice controls were rerun with the original binary, with process CPU
measured and source/mapping equivalence checked.

| Reference | Mapped area | Cell delay |
|---|---:|---:|
| Original PA2 | 20.24% | 14.77% |
| PA2, excluding `t481` | 11.68% | 11.60% |
| Original AGR | 19.32% | 15.21% |
| compress2rs twice | 16.88% | 14.20% |
| Earlier unguarded native command | −1.16% | −5.01% |

Against PA2, median area/delay improvements are 10.87%/7.39%. Area improves on
22 designs and ties on two; delay improves on 20, ties on one, and regresses on
three. Native uses 50.94 process-CPU seconds, versus 13.27 for PA2, 15.34 for AGR,
and 6.74 for compress2rs twice. No holdout case reaches the time limit. These are
frontend results; the holdout has not been routed.

## Backend mapping check

The compatibility check uses all 19 **earlier unguarded** native endpoints. The
ORFS-pinned ABC gives exactly the same mapped area and cell delay as the frontend
ABC, under both the frontend mapping script and the backend mapping script:
38 proved mappings, with zero area/delay difference.

The complete ORFS Yosys synthesis handoff was also checked on all 19 endpoints.
All proofs pass, but the handoff is not identical to mapping an AIG directly.
`router` gains 27 buffers on constant outputs, raising area from 5.41 to 7.38
(36.41%) while retaining the same logic-cell multiset. The largest cell-delay
change is +6.59% on `bar`. These effects are included when every arm goes through
the actual backend; the compatibility check is not a routed result.

The new backend settings are recorded in [backend](backend/): one common-input
die and pin layout per design, density 0.60, and port buffering disabled. They
apply to every method. This is a declared protocol change from the original
paper, whose settings remain in `examples/physical/openroad`.

## Evidence and recomputation

`frontend.json`, `holdout.json`, and `mapper.json` contain 99, 120, and 57
measurement records. `proofs.json` contains successful CEC verdict excerpts and
hash links, not standalone SAT certificates. Inputs, endpoint graphs and full
logs remain in the external research archive. Reused endpoints and alternative
measurements are not independent trials. The old 19-design preprocessing proofs
are explicitly linked to the unchanged `results-20261117` archive.

```sh
python3 examples/physical/choices/analyze_followup.py --check
```

This checks the recorded evidence, input/endpoint hashes, CPU allowances and
summary statistics. `validation.json` records 34 integration checks, 44 choice
checks, five deletion-boundary tests, and ten benchmark cases with exact HPWL
and density audited after every edit. The isolated original-PR `sqrt` run with
only the coordinate correction also has a successful equivalence record.

The separate five-arm OpenROAD campaign is still in progress. This frontend
bundle makes no full-cohort claim about routed HPWL, wirelength, area, delay or
power.
