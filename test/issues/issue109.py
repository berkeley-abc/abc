#!/usr/bin/env python3
"""Prove compact temporal decomposition against an explicit prefix circuit."""
import os, subprocess, tempfile
from pathlib import Path
abc = str(Path(os.environ.get('ABC', './abc')).resolve())

def network(n, used, frames, depth, reference=False, dense=False):
    pis = [f'x{i}' for i in range(n)]
    active = used or [0]
    history = list(range(n)) if dense else active
    if reference:
        pis += [f'h{f}_{i}' for f in range(frames) for i in history]
    lines = ['.model shift', '.inputs ' + ' '.join(pis), '.outputs y', '.names zero', '.names one', '1']
    def logic(inputs, out):
        if not inputs: lines.extend([f'.names {out}', '1'])
        elif len(inputs) == 1: lines.extend([f'.names {inputs[0]} {out}', '1 1'])
        else: lines.extend(['.names ' + ' '.join(inputs) + ' ' + out, '10 1', '01 1'])
    logic([f'x{i}' for i in used], 'data')
    if reference:
        lines += ['.latch one reset 0']
        for f in range(frames): logic([f'h{f}_{i}' for i in used], f'data{f}')
        for i in range(depth):
            init = f'data{frames-i-1}' if i < frames else 'zero'
            lines += [f'.names reset r{i} {init} q{i}', '11- 1', '0-1 1']
        for i in range(depth): lines += [f'.latch {"data" if i==0 else "q"+str(i-1)} r{i} 0']
    else:
        for i in range(depth): lines += [f'.latch {"data" if i==0 else "q"+str(i-1)} q{i} 0']
    lines += [f'.names q{depth-1} y', '1 1', '.end']
    return '\n'.join(lines) + '\n'

with tempfile.TemporaryDirectory() as tmp:
    p = Path(tmp)
    def run(script):
        r = subprocess.run([abc, '-s', '-c', script], cwd=p, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=30)
        assert r.returncode == 0, r.stdout
        return r.stdout
    count = 0
    for n, used, frames, depth in [(1,[0],2,5), (4,[3],2,5), (7,[1,5],3,6),
                                   (4,[],2,5), (4,[1],4,7), (4,[3],2,2)]:
        (p/'source.blif').write_text(network(n,used,frames,depth))
        (p/'reference.blif').write_text(network(n,used,frames,depth,True))
        (p/'dense.blif').write_text(network(n,used,frames,depth,True,True))
        run('read source.blif; strash; write_aiger source.aig; read reference.blif; strash; write_aiger reference.aig')
        out = run(f'read source.aig; tempor -F {frames}; write_aiger result.aig; &get; &cec reference.aig')
        assert 'Networks are equivalent' in out, out
        header = (p/'result.aig').read_bytes().split(b'\n',1)[0].split()
        assert int(header[2]) == n + frames * max(1,len(used)), header
        out = run(f'read source.aig; tempor -F {frames}; bmc2 -F 20; cexsave; read source.aig; cexload; tempor -c; testcex -a')
        assert 'The cex is correct' in out, out
        if depth > frames:
            out = run('read dense.blif; strash; bmc2 -F 20; cexsave; read source.aig; cexload; tempor -c; testcex -a')
            assert 'The cex is correct' in out, out
        count += 1
print(f'PASS: Issue #109 ({count} equivalence proofs, compact and legacy CEX checks)')
