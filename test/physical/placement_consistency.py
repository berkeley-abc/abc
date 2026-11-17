#!/usr/bin/env python3
"""Replay the sqrt in-flow and square don't-care placement failures.

Inputs must already have the common dc2 preprocessing. Compile ABC with
ABC_AGR_ENABLE_AUDIT to check exact HPWL/density after every local edit.
No placement step is selected by the test; every requested step must pass.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

C = ('balance -l; resub -K 6 -l; rewrite -l; resub -K 6 -N 2 -l; '
     'refactor -l; resub -K 8 -l; balance -l; resub -K 8 -N 2 -l; '
     'rewrite -l; resub -K 10 -l; rewrite -z -l; resub -K 10 -N 2 -l; '
     'balance -l; resub -K 12 -l; refactor -z -l; resub -K 12 -N 2 -l; '
     'rewrite -z -l; balance -l')
R = C.replace(' -l', '')
MFS = '&get; &if -K 6; &mfs -e -W 4 -M 1000 -C 20000 -L 1; &st; &put'


def quote(path):
    value = str(path.resolve())
    if any(c in value for c in '\n\r"'):
        raise ValueError('Unsupported character in path')
    return '"' + value + '"'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('abc', 'library', 'sqrt-input', 'square-input', 'output'):
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--steps', type=float, nargs='+', default=[.26, .27, .28, .29, .30])
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    rows = []
    for design, source in [('sqrt', args.sqrt_input), ('square', args.square_input)]:
        for step in args.steps:
            label = f'{design}-{step:.2f}'
            graph = out / (label + '.aig')
            agr = f'agr -s {step}'
            recipe = f'{C}; strash; {agr}; strash; {agr}; strash; {R}; strash; {agr}' if design == 'sqrt' else f'{MFS}; {agr}'
            command = f'read {quote(source)}; strash; read_lib {quote(args.library)}; {recipe}; strash; write_aiger {quote(graph)}'
            (out / (label + '.abc')).write_text(command + '\n')
            result = subprocess.run([str(args.abc.resolve()), '-s', '-c', command],
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    text=True, timeout=1800)
            (out / (label + '.log')).write_text(result.stdout)
            assert result.returncode == 0 and graph.exists(), label
            assert not re.search(r'Error:|AGR_PLACEMENT_AUDIT|has failed', result.stdout), label
            proof = subprocess.run([str(args.abc.resolve()), '-s', '-c',
                                    f'cec -n -p -T 120 {quote(source)} {quote(graph)}'],
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True, timeout=300)
            (out / (label + '-cec.log')).write_text(proof.stdout)
            assert proof.returncode == 0 and 'Networks are equivalent' in proof.stdout, label
            rows.append(dict(design=design, step=step, status='passed'))
    (out / 'summary.json').write_text(json.dumps(rows, indent=2) + '\n')
    print(len(rows), 'placement consistency cases passed')


if __name__ == '__main__':
    main()
