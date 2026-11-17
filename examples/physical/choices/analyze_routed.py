#!/usr/bin/env python3
"""Audit the physical comparison and report complete-cohort target checks."""
import argparse
import hashlib
import json
import math
from pathlib import Path

from paired_summary import summarize

METRICS = ['final_hpwl_um', 'routed_wirelength_um', 'area_um2', 'delay_ps', 'power_w']


def analyze(folder):
    load = lambda path: json.loads(path.read_text())
    protocol, rows, proofs = [load(folder / (name + '.json')) for name in ['protocol', 'results', 'proofs']]
    front_folder = folder.parent / 'followup-20261117'
    frontend = {(r['design'], r['arm']): r for r in load(front_folder / 'frontend.json')}
    frontend_proofs = load(front_folder / 'proofs.json')
    controls = load(front_folder / 'backend/designs.json')
    assert protocol['metric_names'] == METRICS
    assert protocol['epfl_designs'] == sorted(controls) and len(controls) == 20
    assert protocol['conventional_designs'] == sorted(d for d in controls if d != 'hyp')
    assert len(rows) == protocol['expected_runs'] == len(frontend) == 99
    index, failed = {}, []
    for identity, proof in proofs.items():
        assert hashlib.sha256(json.dumps(proof, sort_keys=True).encode()).hexdigest() == identity
        assert proof['status'] == 'passed' and 'Networks are equivalent' in proof['output_excerpt']
        for key in ['left_sha256', 'right_sha256', 'binary_sha256', 'original_log_sha256']:
            assert len(proof[key]) == 64 and int(proof[key], 16) >= 0
    seen = set()
    for row in rows:
        key = row['design'], row['arm']
        assert key not in seen and key in frontend
        seen.add(key)
        source = frontend[key]
        assert row['common_input_sha256'] == source['common_input_sha256']
        assert row['endpoint_sha256'] == source['endpoint_sha256']
        assert row['frontend_source_proof'] == source['source_proof']
        if row['status'] != 'passed':
            failed.append(dict(design=key[0], arm=key[1], reason=row['failure_excerpt']))
            continue
        initial = frontend_proofs[row['frontend_source_proof']]
        mapped, final = proofs[row['mapping_proof']], proofs[row['final_proof']]
        assert initial['left_sha256'] == row['common_input_sha256']
        assert initial['right_sha256'] == mapped['left_sha256'] == row['endpoint_sha256']
        assert mapped['right_sha256'] == final['left_sha256']
        assert mapped['interface'] == final['interface']
        assert row['fixed_boundary_audit'] == 'passed'
        assert row['cores'] == controls[row['design']]['resources']['single']['cores']
        assert row['drc_errors'] == row['unrouted_nets'] == 0
        assert row['stage_hpwl_um']['6_final'] == row['final_hpwl_um']
        assert row['stage_core_hpwl_um']['6_final'] == row['core_only_hpwl_um']
        for metric in protocol['metric_names']:
            assert math.isfinite(row[metric]) and row[metric] > 0
        assert set(row['flow_stage_wall_s']) == {'floorplan', 'finish'}
        assert all(math.isfinite(t) and t > 0 for t in row['flow_stage_wall_s'].values())
        index[key] = row
    assert seen == set(frontend)
    comparisons = {}
    def compare(label, candidate, reference, expected, designs):
        summary = summarize({d: index[d, candidate] for d in designs}, {d: index[d, reference] for d in designs},
                            protocol['metric_names'], designs, replicates=5000, seed=20261116)
        for name, metric in summary['metrics'].items():
            metric.pop('design_reductions_pct')
            metric['summed_reduction_pct'] = 100 * (1 - sum(index[d, candidate][name] for d in designs)
                                                    / sum(index[d, reference][name] for d in designs))
        comparisons[label] = dict(complete=designs == expected,
            missing_designs=[d for d in expected if d not in designs], **summary)
    for label, expected, refs in [
        ('published20', protocol['epfl_designs'], ['paper_pa2', 'paper_agr', 'abc_budget']),
        ('common19', protocol['conventional_designs'], ['paper_pa2', 'paper_agr', 'abc_budget', 'conventional_portfolio'])]:
        ds = [d for d in expected if all((d, a) in index for a in ['native', *refs])]
        if not ds:
            continue
        for ref in refs:
            compare(label + '/native_vs_' + ref, 'native', ref, expected, ds)
        if label == 'published20':
            for ref in ['paper_pa2', 'abc_budget']:
                compare(label + '/original_agr_vs_' + ref, 'paper_agr', ref, expected, ds)
    def target(reference):
        value = comparisons.get('published20/native_vs_' + reference)
        return bool(value and value['complete'] and all(m['geomean_reduction_pct'] >= 5 for m in value['metrics'].values()))
    runtime = {}
    for arm in sorted({a for _, a in frontend}):
        available = [r for (d, a), r in index.items() if a == arm]
        expected = sum(a == arm for _, a in frontend)
        runtime[arm] = dict(verified_designs=len(available), expected_designs=expected,
            flow_stage_wall_s=sum(sum(r['flow_stage_wall_s'].values()) for r in available),
            reserved_core_s=sum(r['cores'] * sum(r['flow_stage_wall_s'].values()) for r in available),
            driver_wall_s=sum(r['wall_s'] for r in available),
            interpretation='Sums over completed designs, not elapsed campaign time or process CPU.')
    return dict(expected_runs=len(frontend), verified_runs=len(index), failed=failed,
        recorded_backend_proofs=len(proofs), comparisons=comparisons, runtime=runtime,
        five_percent_all_metric_geomean_target=dict(versus_pa2=target('paper_pa2'),
            versus_cpu_matched=target('abc_budget'), versus_original_agr=target('paper_agr'),
            primary_target_met=target('paper_pa2') and target('abc_budget'),
            interpretation='Point estimates on all 20 designs. Not a per-design guarantee, confidence-bound claim, or Table II result.'),
        scope='Recorded physical evidence audit and paired-design statistics; does not rerun routing or CEC. Default-activity power; separate core-only HPWL is not the target metric.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results', type=Path, default=Path(__file__).with_name('routed-20261117'))
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', action='store_true')
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
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(dict(expected=result['expected_runs'], verified=result['verified_runs'],
        failed=len(result['failed']), target=result['five_percent_all_metric_geomean_target'], checked=args.check)))


if __name__ == '__main__':
    main()
