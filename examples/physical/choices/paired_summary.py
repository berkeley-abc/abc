"""Paired design summaries. Bootstrap intervals describe cohort sensitivity."""
import math
import random
import statistics


def percentile(values, probability):
    values = sorted(values)
    position = probability * (len(values) - 1)
    lower = int(position)
    upper = min(lower + 1, len(values) - 1)
    return values[lower] + (values[upper] - values[lower]) * (position - lower)


def summarize(candidate, reference, metrics, designs, replicates=20000, seed=20261116):
    """Keep the same paired circuit sample for every metric in each replicate."""
    if not designs:
        raise ValueError('An explicit nonempty paired cohort is required')
    randomizer = random.Random(seed)
    samples = [[randomizer.randrange(len(designs)) for _ in designs]
               for _ in range(replicates)]
    result = dict(designs=designs, n=len(designs), bootstrap_replicates=replicates,
                  bootstrap_seed=seed, interval='paired-design percentile 95%; cohort sensitivity, not run noise',
                  positive_means='candidate reduction relative to reference', metrics={})
    for metric in metrics:
        ratios = [candidate[d][metric] / reference[d][metric] for d in designs]
        if not all(math.isfinite(x) and x > 0 for x in ratios):
            raise ValueError('Metrics must be finite and strictly positive: ' + metric)
        logs = [math.log(x) for x in ratios]
        reduction = lambda xs: 100 * -math.expm1(statistics.fmean(xs))
        excluded = sorted(range(len(designs)), key=lambda i: (logs[i], designs[i]))[:2]
        retained = [v for i, v in enumerate(logs) if i not in excluded]
        bootstrap = [reduction([logs[i] for i in sample]) for sample in samples]
        result['metrics'][metric] = dict(
            geomean_reduction_pct=reduction(logs),
            median_design_reduction_pct=statistics.median([100 * (1 - r) for r in ratios]),
            leave_top_two_out_reduction_pct=reduction(retained) if retained else None,
            excluded_top_two_designs=[designs[i] for i in excluded],
            paired_bootstrap_95_pct=[percentile(bootstrap, .025), percentile(bootstrap, .975)],
            improved_designs=sum(r < 1 for r in ratios), unchanged_designs=sum(r == 1 for r in ratios),
            design_reductions_pct={d: 100 * (1 - r) for d, r in zip(designs, ratios)})
    return result
