#!/usr/bin/env python3
"""Checks for CPU accounting and failure-safe frontend summaries."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('reproduce', ROOT / 'examples/physical/reproduce.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class ReproductionTests(unittest.TestCase):
    def test_cpu_units(self):
        check = runner.check_clock()
        self.assertAlmostEqual(check['live_cpu_s'], check['process_time_s'], delta=0.002)

    def test_overflow_and_missing_metrics_are_not_success(self):
        for text in ('', 'pa_stats: HPWL 100 -> 80 overflow 0.4 -> 0.2'):
            with self.assertRaises(ValueError):
                runner.parse_metrics(text)
        text = 'and = 100 lev = 12\npa_stats: HPWL 100 -> 80 overflow 0.4 -> 0.09'
        self.assertEqual(runner.parse_metrics(text)['nodes'], 100)

    def test_unmatched_and_invalid_endpoints_are_excluded(self):
        rows = []
        for design in ('complete', 'missing', 'invalid'):
            for flow in runner.FLOWS:
                if design == 'missing' and flow == 'abc_budget':
                    continue
                row = {'design': design, 'flow': flow, 'status': 'ok', 'metric_status': 'ok',
                       'verified': True, 'target_cpu_s': 1, 'cycles': 1}
                for key in ('aig_nodes', 'aig_levels', 'aig_hpwl', 'mapped_area', 'mapped_delay_ps',
                            'mapped_hpwl', 'synthesis_cpu_s', 'process_cpu_s'):
                    row[key] = 11 if flow == 'agr' else 10
                if design == 'invalid' and flow == 'agr':
                    row.update(status='failed', verified=False, cec={'source': 'failed'})
                rows.append(row)
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp)
            runner.summarize(output, rows, ['complete', 'missing', 'invalid'])
            result = json.loads((output / 'summary.json').read_text())
            self.assertEqual(result['matched_designs'], ['complete'])
            metric = result['comparisons']['agr_vs_pa2']['mapped_hpwl']
            self.assertAlmostEqual(metric['change_pct'], 10)
            self.assertEqual(metric['regressions'], ['complete'])

    def test_unproved_is_not_verified(self):
        rows = []
        for flow in runner.FLOWS:
            row = {'design': 'd', 'flow': flow, 'status': 'ok', 'metric_status': 'ok',
                   'verified': False, 'cec': {'source': 'unproved', 'mapping': 'passed'},
                   'target_cpu_s': 1, 'cycles': 1}
            for key in ('aig_nodes', 'aig_levels', 'aig_hpwl', 'mapped_area', 'mapped_delay_ps',
                        'mapped_hpwl', 'synthesis_cpu_s', 'process_cpu_s'):
                row[key] = 1
            rows.append(row)
        with tempfile.TemporaryDirectory() as tmp:
            runner.summarize(Path(tmp), rows, ['d'])
            result = json.loads((Path(tmp) / 'summary.json').read_text())
            self.assertEqual(result['matched_designs'], ['d'])
            self.assertEqual(result['fully_verified_designs'], [])
            self.assertEqual(len(result['unproved_endpoints']), 3)


if __name__ == '__main__':
    unittest.main()
