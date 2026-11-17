#!/usr/bin/env python3
"""Audit the bounded-choice followup and recompute paired frontend statistics."""
import argparse
import hashlib
import json
import math
from pathlib import Path

from paired_summary import summarize


def analyze(folder):
    def load(name):
        return json.loads((folder / (name + '.json')).read_text())
    protocol, proofs = load('protocol'), load('proofs')
    inputs = {(r['cohort'], r['design']): r for r in load('inputs')}
    archived = json.loads((folder.parent / 'results-20261117/proofs.json').read_text())
    for proof in proofs.values():
        assert proof['status'] == 'passed' and 'Networks are equivalent' in proof['output_excerpt']
        for name in ['left_sha256', 'right_sha256', 'binary_sha256', 'original_log_sha256']:
            assert len(proof[name]) == 64 and int(proof[name], 16) >= 0
    for (cohort, _), row in inputs.items():
        if 'archived_preprocessing_proof' in row:
            proof = archived[row['archived_preprocessing_proof']]
            assert proof['status'] == 'passed'
        else:
            proof = proofs[row['preprocessing_proof'] if cohort == 'epfl' else row['preprocessing_identity_proof']]
        assert proof['right_sha256'] == row['common_input_sha256']
        assert proof['left_sha256'] == row['dc2_input_sha256' if cohort == 'epfl' else 'regenerated_common_sha256']
        if cohort == 'holdout':
            assert row['preprocessing_payload_matches']
    tables = {}
    for name, cohort in [('frontend', 'epfl'), ('holdout', 'holdout')]:
        rows = load(name)
        assert len(rows) == protocol['rows'][name]
        index = {}
        for row in rows:
            key = row['design'], row['arm']
            assert key not in index
            index[key] = row
            assert row['common_input_sha256'] == inputs[cohort, row['design']]['common_input_sha256']
            source, mapped = proofs[row['source_proof']], proofs[row['mapping_proof']]
            assert source['left_sha256'] == row['common_input_sha256']
            assert source['right_sha256'] == mapped['left_sha256'] == row['endpoint_sha256']
            assert mapped['right_sha256'] == row['mapped_function_sha256']
            for metric in ['mapped_area', 'mapped_delay_ps']:
                assert math.isfinite(row[metric]) and row[metric] > 0
            if 'mapped_hpwl' in row:
                assert math.isfinite(row['mapped_hpwl']) and row['mapped_hpwl'] > 0
                assert row['fixed_bins'] == inputs[cohort, row['design']]['fixed_bins']
        tables[name] = index
    epfl, holdout = tables['frontend'], tables['holdout']
    refs = ['paper_pa2', 'paper_agr', 'abc_budget', 'conventional_portfolio']
    assert set(epfl) == {(d, a) for d in protocol['epfl_designs'] for a in ['native', *refs]
                         if (d, a) != ('hyp', 'conventional_portfolio')}
    assert set(holdout) == {(d, a) for d in protocol['holdout_designs']
                            for a in ['native', 'paper_pa2', 'paper_agr', 'compress2rs_twice', 'unguarded_native']}
    for design in protocol['epfl_designs']:
        native, reference = epfl[design, 'native'], epfl[design, 'abc_budget']
        assert reference['target_cpu_s'] == native['process_cpu_s']
        assert reference['synthesis_cpu_s'] >= reference['target_cpu_s']
        assert reference['process_cpu_s'] >= reference['target_cpu_s'] - .02
    comparisons = {}

    def compare(label, table, reference, designs, metrics):
        result = summarize({d: table[d, 'native'] for d in designs},
                           {d: table[d, reference] for d in designs}, metrics, designs,
                           replicates=protocol['bootstrap_replicates'], seed=protocol['bootstrap_seed'])
        for value in result['metrics'].values():
            value.pop('design_reductions_pct')
        comparisons[label] = result

    for ref in refs:
        ds = protocol['external_portfolio_designs']
        metrics = ['mapped_area', 'mapped_delay_ps']
        if ref != 'conventional_portfolio':
            compare('epfl20/native_vs_' + ref, epfl, ref, protocol['epfl_designs'], metrics)
            metrics = ['mapped_hpwl', *metrics]
        compare('epfl19/native_vs_' + ref, epfl, ref, ds, metrics)
    for ref in ['paper_pa2', 'paper_agr', 'compress2rs_twice', 'unguarded_native']:
        ds = protocol['holdout_designs']
        compare('holdout24/native_vs_' + ref, holdout, ref, ds, ['mapped_area', 'mapped_delay_ps'])
        compare('holdout_without_t481/native_vs_' + ref, holdout, ref,
                [d for d in ds if d != 't481'], ['mapped_area', 'mapped_delay_ps'])
    mapper = load('mapper')
    assert len(mapper) == protocol['rows']['mapper']
    for row in mapper:
        proof = proofs[row['proof']]
        assert proof['left_sha256'] == row['endpoint_sha256']
        assert proof['right_sha256'] == row['mapped_function_sha256']
        if row['kind'] == 'abc_binary':
            assert row['area_change_pct'] == row['delay_change_pct'] == 0
    runtimes = {}
    for cohort, table in tables.items():
        runtimes[cohort] = {}
        for arm in sorted({a for d, a in table}):
            rows = [row for (d, a), row in table.items() if a == arm]
            values = [row['process_cpu_s'] for row in rows if 'process_cpu_s' in row]
            runtimes[cohort][arm] = dict(measured=len(values), expected=len(rows),
                                        total_s=sum(values) if len(values) == len(rows) else None)
    return dict(recorded_rows=protocol['rows'], recorded_proofs=len(proofs), comparisons=comparisons,
                timeouts=[d for d in protocol['epfl_designs'] if epfl[d, 'native'].get('timed_out')],
                process_cpu=runtimes,
                scope='Recorded frontend evidence and paired-design summaries; not a rerun of CEC or OpenROAD.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results', type=Path, default=Path(__file__).with_name('followup-20261117'))
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = analyze(args.results)
    if args.check:
        hashes = json.loads((args.results / 'files.sha256.json').read_text())
        for name, digest in hashes.items():
            assert hashlib.sha256((args.results / name).read_bytes()).hexdigest() == digest, name
        assert json.loads((args.results / 'summary.json').read_text()) == result
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(dict(rows=result['recorded_rows'], proofs=result['recorded_proofs'],
                          timeouts=result['timeouts'], checked=args.check)))


if __name__ == '__main__':
    main()
