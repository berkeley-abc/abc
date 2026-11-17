#!/usr/bin/env python3
"""Audit the recorded evidence and recompute paired ABC result summaries."""
import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
import statistics

from paired_summary import summarize

METRICS = ['mapped_hpwl', 'mapped_area', 'mapped_delay_ps']
ARMS = {
    'primary': ['native', 'paper_pa2', 'paper_agr', 'corrected_pa2',
                'corrected_agr', 'abc_budget', 'compress_budget'],
    'flow': ['native_slots', 'last_slot', 'paper_pa2', 'paper_agr', 'corrected_agr'],
    'sensitivity': ['native', 'paper_pa2', 'paper_agr', 'corrected_pa2'],
    'portfolio': ['agr', 'pa', 'compress'],
}


def analyze(folder):
    def load(name):
        return json.loads((folder / name).read_text())
    protocol = load('protocol.json')
    designs = protocol['designs']
    inputs = {x['design']: x for x in load('inputs.json')}
    proofs = load('proofs.json')
    assert len(designs) == len(set(designs)) == 19
    assert set(designs) == set(inputs)
    for proof in proofs.values():
        assert proof['status'] == 'passed'
        assert 'Networks are equivalent' in proof['output']
        for key in ['left_sha256', 'right_sha256', 'binary_sha256']:
            assert len(proof[key]) == 64 and int(proof[key], 16) >= 0
    for x in inputs.values():
        proof = proofs[x['preprocessing_proof']]
        assert proof['left_sha256'] == x['dc2_input_sha256']
        assert proof['right_sha256'] == x['common_input_sha256']
    tables = {}
    for name, arms in ARMS.items():
        with (folder / (name + '.csv')).open() as stream:
            rows = list(csv.DictReader(stream))
        assert len(rows) == protocol['expected_rows'][name]
        steps = protocol['guidance_steps'] if name == 'sensitivity' else [.28]
        index = {}
        for row in rows:
            for key in [*METRICS, 'guidance_step', 'mapped_gates', 'fixed_bins',
                        'process_cpu_s', 'target_cpu_s', 'synthesis_cpu_s', 'cycles']:
                if row[key] != '':
                    row[key] = float(row[key])
            key = row['design'], row['arm'], row['guidance_step']
            assert key not in index
            index[key] = row
            assert row['common_input_sha256'] == inputs[row['design']]['common_input_sha256']
            source, mapped = proofs[row['source_proof']], proofs[row['mapping_proof']]
            assert source['left_sha256'] == row['common_input_sha256']
            assert source['right_sha256'] == mapped['left_sha256'] == row['endpoint_sha256']
            assert mapped['right_sha256'] == row['mapped_function_sha256']
            for metric in METRICS[1:] if name == 'portfolio' else METRICS:
                assert math.isfinite(row[metric]) and row[metric] > 0
            if name != 'portfolio':
                assert row['fixed_bins'] == inputs[row['design']]['fixed_bins']
        assert set(index) == {(d, a, s) for d in designs for a in arms for s in steps}
        tables[name] = index
    primary = tables['primary']
    for d in designs:
        for ref in ['abc_budget', 'compress_budget']:
            r = primary[d, ref, .28]
            assert r['target_cpu_s'] == primary[d, 'native', .28]['process_cpu_s']
            assert r['synthesis_cpu_s'] >= r['target_cpu_s']
            assert r['process_cpu_s'] >= r['target_cpu_s'] - .02  # OS rounding
    comparisons = {}

    def cohort(table, arm, step=.28):
        return {d: table[d, arm, step] for d in designs}

    def compare(key, candidate, reference, metrics=METRICS, ds=designs):
        result = summarize(candidate, reference, metrics, ds,
                           replicates=protocol['statistics']['bootstrap_replicates'],
                           seed=protocol['statistics']['seed'])
        # Per-design values are already available in the CSV files.
        for metric, values in result['metrics'].items():
            values.pop('design_reductions_pct')
            if metric == 'mapped_hpwl':
                values['summed_reduction_pct'] = 100 * (1 - sum(candidate[d][metric] for d in ds) /
                                                       sum(reference[d][metric] for d in ds))
        comparisons[key] = result

    candidate = cohort(primary, 'native')
    for ref in ARMS['primary'][1:]:
        compare('primary/native_vs_' + ref, candidate, cohort(primary, ref))
    compare('primary/native_vs_paper_pa2_without_div', candidate, cohort(primary, 'paper_pa2'),
            ds=[d for d in designs if d != 'div'])
    for arm in ['native_slots', 'last_slot']:
        for ref in ['paper_pa2', 'paper_agr', 'corrected_agr']:
            compare('flow/' + arm + '_vs_' + ref, cohort(tables['flow'], arm), cohort(tables['flow'], ref))
    for ref in ARMS['sensitivity'][1:]:
        for step in protocol['guidance_steps']:
            compare(f'sensitivity/{step:.2f}/native_vs_{ref}', cohort(tables['sensitivity'], 'native', step),
                    cohort(tables['sensitivity'], ref, step))
        def averaged(arm):
            return {d: {m: math.exp(statistics.fmean(math.log(tables['sensitivity'][d, arm, s][m])
                                                   for s in protocol['guidance_steps']))
                        for m in METRICS} for d in designs}
        compare('sensitivity/five_step_mean/native_vs_' + ref, averaged('native'), averaged(ref))
    for arm in ARMS['portfolio']:
        selected = cohort(tables['portfolio'], arm)
        compare('portfolio/native_vs_' + arm, candidate, selected, METRICS[1:])
        compare('portfolio/' + arm + '_vs_paper_pa2', selected, cohort(primary, 'paper_pa2'), METRICS[1:])
    for ref in ['pa', 'compress']:
        compare('portfolio/agr_vs_' + ref, cohort(tables['portfolio'], 'agr'),
                cohort(tables['portfolio'], ref), METRICS[1:])
    runtime = {}
    for arm in ARMS['primary']:
        values = [primary[d, arm, .28]['process_cpu_s'] for d in designs]
        runtime[arm] = dict(total_s=sum(values), median_s=statistics.median(values), maximum_s=max(values))
    return dict(rows={name: len(table) for name, table in tables.items()},
                recorded_proofs=len(proofs), comparisons=comparisons, process_cpu=runtime,
                scope='Recorded evidence audit and statistical recomputation; does not rerun synthesis or CEC.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results', type=Path, default=Path(__file__).with_name('results-20261117'))
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', action='store_true', help='Check committed file hashes and summary')
    args = parser.parse_args()
    result = analyze(args.results)
    if args.check:
        hashes = json.loads((args.results / 'files.sha256.json').read_text())
        for name, digest in hashes.items():
            assert hashlib.sha256((args.results / name).read_bytes()).hexdigest() == digest, name
        def equivalent(left, right):
            if isinstance(left, dict):
                return left.keys() == right.keys() and all(equivalent(left[k], right[k]) for k in left)
            if isinstance(left, list):
                return len(left) == len(right) and all(equivalent(a, b) for a, b in zip(left, right))
            if isinstance(left, float):
                return math.isclose(left, right, rel_tol=1e-12, abs_tol=1e-9)
            return left == right
        assert equivalent(result, json.loads((args.results / 'summary.json').read_text()))
        print('All 665 observations, proof links, CPU allowances and summary statistics checked.')
    elif args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    else:
        print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
