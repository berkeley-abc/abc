#!/usr/bin/env python3
"""Checks that flow replay preserves slot policies and complete matched cohorts."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'examples/physical'))
import reproduce_flow as runner


class FlowTests(unittest.TestCase):
    def recipes(self):
        return {'d': {'agr': [['A']] * 3, 'pa2': [['P']] * 3,
                      'abc_c': [['C', 'C']] * 3,
                      'abc_mix': [['E', 'E', 'R', 'B', 'E']] * 3}}

    def test_macro_boundary_replay(self):
        runner.validate_replay(self.recipes(), ['d'])

    def test_replay_cannot_add_physical_effort(self):
        r = self.recipes()
        r['d']['agr'][0] = ['A', 'A']
        with self.assertRaises(ValueError):
            runner.validate_replay(r, ['d'])

    def test_replay_cannot_change_native_policy(self):
        r = self.recipes()
        r['d']['abc_mix'][1] = ['E', 'R']
        with self.assertRaises(ValueError):
            runner.validate_replay(r, ['d'])
        with self.assertRaises(ValueError):
            runner.validate_replay({}, ['d'])

    def test_four_way_matched_cohort(self):
        rows = []
        for d in ('complete', 'missing'):
            for flow in runner.FLOWS:
                if d == 'missing' and flow == 'abc_mix':
                    continue
                row = dict(design=d, flow=flow, status='ok', metric_status='ok',
                           verified=True, target_cpu_s=1, cycles=1, slots=[['C']] * 3)
                for m in ('aig_nodes', 'aig_levels', 'aig_hpwl', 'mapped_area',
                          'mapped_delay_ps', 'mapped_hpwl', 'synthesis_cpu_s', 'process_cpu_s'):
                    row[m] = 11 if flow == 'agr' else 10
                rows.append(row)
        with tempfile.TemporaryDirectory() as tmp:
            runner.summarize(Path(tmp), rows, ['complete', 'missing'])
            s = json.loads((Path(tmp) / 'summary.json').read_text())
            self.assertEqual(s['matched_designs'], ['complete'])
            self.assertEqual(set(s['comparisons']), {'agr_vs_' + f for f in runner.FLOWS[1:]})
            self.assertEqual(s['comparisons']['agr_vs_abc_mix']['mapped_hpwl']['regressions'], ['complete'])


if __name__ == '__main__':
    unittest.main()
