#!/usr/bin/env python3
"""Integration checks for the isolated physical-synthesis extensions."""
import argparse
import io
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]


def payload(path):
    """Ignore AIGER symbol/comment trailers, retaining the complete AIG body."""
    stream = io.BytesIO(path.read_bytes())
    header = stream.readline().split()
    assert header[0] == b'aig' and len(header) == 6, header
    for _ in range(int(header[3]) + int(header[4])):
        stream.readline()
    for _ in range(2 * int(header[5])):
        while True:
            byte = stream.read(1)
            assert byte, 'truncated AIGER'
            if byte[0] < 128:
                break
    return stream.getvalue()[:stream.tell()]


def fixture(path):
    rng = random.Random(1701)
    names = [f'i{i}' for i in range(12)]
    lines = ['.model physical_test', '.inputs ' + ' '.join(names)]
    for i in range(120):
        a, b = rng.sample(names, 2)
        name = f'n{i}'
        lines.append(f'.names {a} {b} {name}')
        lines.extend(rng.choice([['11 1'], ['1- 1', '-1 1'], ['10 1', '01 1']]))
        names.append(name)
    lines.insert(2, '.outputs ' + ' '.join(names[-16:]))
    lines.append('.end')
    path.write_text('\n'.join(lines) + '\n')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--abc', required=True, type=Path)
    ap.add_argument('--reference', type=Path, help='unmodified upstream ABC')
    ap.add_argument('--output', type=Path, help='retain logs and JSON summary here')
    args = ap.parse_args()
    binary = args.abc.resolve()
    reference = args.reference.resolve() if args.reference else None
    temporary = tempfile.TemporaryDirectory(prefix='abc-physical-') if not args.output else None
    work = Path(temporary.name) if temporary else args.output.resolve()
    work.mkdir(parents=True, exist_ok=True)
    fixture(work / 'input.blif')
    (work / 'cells.lib').write_bytes((ROOT / 'demo.lib').read_bytes())
    (work / 'sequential.blif').write_text('.model sequential\n.inputs a\n.outputs q\n.latch a q\n.end\n')
    env = {k: v for k, v in os.environ.items() if not k.startswith('ABC_')}
    env['OMP_NUM_THREADS'] = '1'
    records = []

    def run(label, commands, exe=binary, expect=None):
        result = subprocess.run([str(exe), '-s', '-c', commands], cwd=work,
                                env=env, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=90)
        (work / (label + '.log')).write_text(result.stdout)
        assert result.returncode >= 0, (label, result.returncode)
        if expect:
            assert expect in result.stdout, (label, result.stdout[-2000:])
        records.append({'check': label, 'status': 'passed'})
        return result.stdout

    def cec(name, left='input.aig'):
        run('cec_' + name, f'cec {left} {name}.aig', expect='Networks are equivalent')

    setup = 'read input.blif; strash; read_lib cells.lib; '
    run('input', setup + 'write_aiger input.aig')
    pa = 'pa_place -s 0.28;' + ';'.join([
        'pa_rs -K 8 -N 2',
        'pa_rw', 'pa_rf'] * 2)
    flows = {
        'agr': 'agr',
        'legacy_alias': 'tg',
        'repeat': 'agr; agr',
        'native_handoff': 'agr; rewrite; refactor; resub -K 8 -N 2',
        'pa2': pa,
        'agr_after_pa': pa + '; strash; agr',
        'pa_after_agr': 'agr;' + pa,
        'mapping': 'agr; &get -n; &nf; &put; strash',
        'cluster_feedback': 'agr; &get -n; &nf; &put; pa_place; pa_strash; '
                            'pa_rw -c; pa_rf -c',
        'undo': 'set backup; agr; undo',
        'reread': 'agr; read input.blif; strash; agr',
    }
    for name, flow in flows.items():
        run(name, setup + flow + f'; strash; write_aiger {name}.aig')
        assert (work / (name + '.aig')).is_file(), name
        cec(name)
    assert payload(work / 'legacy_alias.aig') == payload(work / 'agr.aig'), 'legacy alias changed the graph'
    assert payload(work / 'undo.aig') == payload(work / 'input.aig'), 'undo lost original graph'
    assert payload(work / 'reread.aig') == payload(work / 'agr.aig'), 'state leaked across reads'
    run('empty', 'agr', expect='there is no current network')
    run('unstrashed', 'read input.blif; agr', expect='must be a strashed combinational AIG')
    run('sequential', 'read sequential.blif; strash; agr', expect='agr:')
    for step in ['0', '-1', 'nan', 'inf', 'invalid']:
        run('invalid_' + step, setup + 'agr -s ' + step, expect='must be finite and positive')
    run('unknown_option', setup + 'agr -x', expect='usage: agr')
    run('missing_argument', setup + 'agr -s', expect='usage: agr')
    run('help', 'agr -h', expect='usage: agr')
    if reference:
        native = setup + 'balance; rewrite; refactor; resub -K 8 -N 2; strash; '
        run('native_integrated', native + 'write_aiger native_integrated.aig')
        run('native_reference', native + 'write_aiger native_reference.aig', exe=reference)
        assert payload(work / 'native_integrated.aig') == payload(work / 'native_reference.aig')
        records.append({'check': 'native_payload_parity', 'status': 'passed'})
    (work / 'summary.json').write_text(json.dumps(records, indent=2) + '\n')
    print(f'{len(records)} checks passed')
    if args.output:
        print(f'Logs: {work}')
    if temporary:
        temporary.cleanup()


if __name__ == '__main__':
    main()
