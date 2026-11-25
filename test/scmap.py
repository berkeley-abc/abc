#!/usr/bin/env python3
"""Exercise SCMap mapping and command validation with a supplied Liberty library."""
import argparse
from pathlib import Path
import subprocess
import tempfile
import json


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--abc', type=Path, default=Path('./abc'))
    ap.add_argument('--library-commands', required=True, type=Path)
    args = ap.parse_args()
    abc = args.abc.resolve()
    library = '; '.join(s for s in args.library_commands.read_text().splitlines() if s.strip() and not s.lstrip().startswith('#'))
    circuits = {
        'constants': '.inputs a\n.outputs z o a_copy\n.names z\n.names o\n1\n.names a a_copy\n1 1\n',
        'phases': '.inputs a b\n.outputs p n\n.names a b p\n11 1\n.names p n\n0 1\n',
        'shared': '.inputs a b c\n.outputs x y z\n.names a b p\n10 1\n01 1\n.names p c x\n11 1\n.names p c y\n00 0\n.names p z\n1 1\n',
        'repeated': '.inputs a b\n.outputs x y\n.names a b n\n11 1\n.names n x\n1 1\n.names n y\n1 1\n',
    }
    def run(commands):
        proc = subprocess.run([str(abc), '-s', '-c', commands], capture_output=True, text=True, timeout=120)
        text = proc.stdout + proc.stderr
        if proc.returncode:
            raise RuntimeError(text)
        return text
    with tempfile.TemporaryDirectory(prefix='scmap-test-') as directory:
        work = Path(directory)
        for name, body in circuits.items():
            source = work / (name + '.blif')
            source.write_text('.model test\n' + body + '.end\n')
            for choices in [False, True]:
                copies = []
                for repetition in range(2):
                    target = work / f'{name}-{choices}-{repetition}.blif'
                    commands = library + f'; read_blif {json.dumps(str(source))}; strash; '
                    if choices:
                        commands += 'dch; '
                    commands += '&get; &scmap; &scmap; &put; '
                    commands += f'write_blif {json.dumps(str(target))}; cec -n -T 0 {json.dumps(str(source))} {json.dumps(str(target))}'
                    text = run(commands)
                    if 'Networks are equivalent' not in text or not target.exists():
                        raise AssertionError(text)
                    copies.append([s for s in target.read_text().splitlines() if s and not s.startswith(('#', '.model'))])
                assert copies[0] == copies[1], (name, choices, 'nondeterministic mapping')
        assert 'Empty GIA network' in run('&scmap')
        for option in ['-N 13', '-X 4', 'unexpected']:
            assert 'usage: &scmap' in run('&scmap ' + option)
    print('SCMap regression checks passed')


if __name__ == '__main__':
    main()
