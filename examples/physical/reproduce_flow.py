#!/usr/bin/env python3
"""Serial C-S-S-R-S comparison with AGR, PA2, and CPU-budgeted native slots."""
import argparse
import fcntl
import json
import os
from pathlib import Path
import platform
import re

import reproduce as base

FLOWS = ('agr', 'pa2', 'abc_c', 'abc_mix')
SKELETON = ('C', 'S', 'S', 'R', 'S')
C = ('balance -l; resub -K 6 -l; rewrite -l; resub -K 6 -N 2 -l; '
     'refactor -l; resub -K 8 -l; balance -l; resub -K 8 -N 2 -l; '
     'rewrite -l; resub -K 10 -l; rewrite -z -l; resub -K 10 -N 2 -l; '
     'balance -l; resub -K 12 -l; refactor -z -l; resub -K 12 -N 2 -l; '
     'rewrite -z -l; balance -l')
MACROS = {'C': C, 'R': C.replace(' -l', ''), 'E': '&get; &dc2; &put',
          'B': 'balance', 'A': 'agr',
          'P': 'pa_place; ' + base.PA_CYCLE + '; ' + base.PA_CYCLE}
FILLERS = {'abc_c': ('C',), 'abc_mix': ('E', 'E', 'R', 'B')}


def validate_replay(replay, designs):
    for d in designs:
        for f in FLOWS:
            slots = replay.get(d, {}).get(f)
            if not isinstance(slots, list) or len(slots) != 3:
                raise ValueError(f'Missing three replay slots: {d}/{f}')
            for slot in slots:
                if not isinstance(slot, list) or not slot:
                    raise ValueError(f'Empty or invalid replay slot: {d}/{f}')
                expected = ('A',) if f == 'agr' else ('P',) if f == 'pa2' else FILLERS[f]
                if any(m != expected[i % len(expected)] for i, m in enumerate(slot)):
                    raise ValueError(f'Replay changes the declared slot policy: {d}/{f}')
                if f in ('agr', 'pa2') and len(slot) != 1:
                    raise ValueError(f'Replay changes the physical slot count: {d}/{f}')


def synth(args, design, flow, targets, fixed, env):
    root = args.output / design / flow
    root.mkdir(parents=True)
    graph = root / 'optimized.aig'
    row = dict(design=design, flow=flow, slot_targets_cpu_s=targets,
               target_cpu_s=sum(targets) if targets else None,
               recipe=[], slots=[], slot_cpu_s=[], cycles=0)
    session = None
    error = None
    try:
        session = base.Session(args.abc, root / 'synthesis', env, args.timeout)
        session.send('echo FRONTEND_READY')
        session.send(f'read {base.quote(args.inputs / (design + ".aig"))}; '
                     f'strash; read_lib {base.quote(args.liberty)}')
        begin = session.clock.read()

        def macro(name):
            # Each saved macro boundary is normalized. AGR normalizes internally.
            command = 'strash; ' + MACROS[name]
            if name != 'A':
                command += '; strash'
            session.send(command)
            row['recipe'].append(name)

        for token in SKELETON:
            if token != 'S':
                macro(token)
                continue
            slot_id = len(row['slots'])
            start = session.clock.read()
            selected = []
            if fixed:
                for name in fixed[slot_id]:
                    macro(name)
                    selected.append(name)
            elif flow in ('agr', 'pa2'):
                selected = ['A' if flow == 'agr' else 'P']
                macro(selected[0])
            else:
                cycle = FILLERS[flow]
                for i in range(args.max_macros):
                    name = cycle[i % len(cycle)]
                    macro(name)
                    selected.append(name)
                    if session.clock.read() - start >= targets[slot_id]:
                        break
                else:
                    raise RuntimeError('Native macro safety cap reached before CPU target')
            elapsed = session.clock.read() - start
            row['slots'].append(selected)
            row['slot_cpu_s'].append(elapsed)
            if flow in FILLERS and not fixed and elapsed < targets[slot_id]:
                raise RuntimeError('Native slot failed its CPU target')
        row['synthesis_cpu_s'] = session.clock.read() - begin
        row['cycles'] = sum(map(len, row['slots']))
        session.send(f'write_aiger {base.quote(graph)}; print_stats')
        row.update(status='ok', payload_sha256=base.payload_hash(graph),
                   endpoint_sha256=base.sha(graph))
    except Exception as exc:
        error = str(exc)
        row.update(status='failed', error=error)
    finally:
        if session:
            rec = session.close(error)
            row['process_cpu_s'] = rec['process_cpu_s']
            if rec['returncode'] != 0:
                row.update(status='failed', error=error or 'Nonzero synthesis exit')
    base.save(root / 'synthesis.json', row)
    return row


def summarize(output, rows, designs):
    base.summarize(output, rows, designs, flows=FLOWS)
    recipes = {}
    for row in rows:
        if row['status'] == 'ok':
            recipes.setdefault(row['design'], {})[row['flow']] = row['slots']
    base.save(output / 'recipes.json', recipes)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for flag in ('abc', 'inputs', 'liberty', 'output'):
        ap.add_argument('--' + flag, type=Path, required=True)
    ap.add_argument('--designs', default='all')
    ap.add_argument('--paper-inputs', action='store_true', help='validate input/library hashes only')
    ap.add_argument('--timeout', type=int, default=3600)
    ap.add_argument('--cec-timeout', type=int, default=60)
    ap.add_argument('--max-macros', type=int, default=100000)
    ap.add_argument('--replay-recipes', type=Path, help='fixed native work; not new CPU matching')
    args = ap.parse_args()
    for key in ('abc', 'inputs', 'liberty', 'output'):
        setattr(args, key, getattr(args, key).resolve())
    if min(args.timeout, args.cec_timeout, args.max_macros) <= 0:
        ap.error('limits must be positive')
    designs = sorted(p.stem for p in args.inputs.glob('*.aig')) if args.designs == 'all' else sorted(set(args.designs.split(',')))
    if not designs or any(not re.fullmatch(r'[A-Za-z0-9_-]+', d) for d in designs):
        ap.error('input stems must contain only letters, digits, underscores, or hyphens')
    hashes = {d: base.sha(args.inputs / (d + '.aig')) for d in designs}
    if args.paper_inputs:
        manifest = json.loads((Path(__file__).resolve().parents[2] / 'test/physical/endpoint_manifest.json').read_text())
        if base.sha(args.liberty) != manifest['library_sha256']:
            ap.error('library hash differs from paper manifest')
        for d in designs:
            entries = [r for r in manifest['endpoint_checks'] if r['design'] == d]
            if not entries or any(r['input_sha256'] != hashes[d] for r in entries):
                ap.error('input hash differs from paper manifest: ' + d)
    replay = json.loads(args.replay_recipes.read_text()) if args.replay_recipes else {}
    if args.replay_recipes:
        validate_replay(replay, designs)
    env = {k: v for k, v in os.environ.items() if not k.startswith(('ABC_', 'ASAN_', 'UBSAN_'))}
    env.update(OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', VECLIB_MAXIMUM_THREADS='1')
    protocol = dict(version=1, runner_sha256=base.sha(__file__), helper_sha256=base.sha(base.__file__),
                    binary=str(args.abc), binary_sha256=base.sha(args.abc),
                    inputs=str(args.inputs), liberty=str(args.liberty),
                    input_sha256=hashes, library_sha256=base.sha(args.liberty), designs=designs,
                    platform=platform.platform(), skeleton=SKELETON, macros=MACROS,
                    paper_inputs=args.paper_inputs, timeout=args.timeout, cec_timeout=args.cec_timeout,
                    max_macros=args.max_macros, replay_recipes=replay,
                    budget='max AGR/PA2 CPU at each corresponding slot; stop at native macro boundaries',
                    normalization='strash before each macro; after each native/PA macro; AGR includes final strash',
                    accounting='one process per flow; synthesis includes every macro, guidance placement, and boundary normalization; endpoint evaluation/CEC separate',
                    mapper=base.MAPPER, measurement='fresh independent AIG/mapped placement',
                    environment={k: env[k] for k in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS')})
    # JSON-roundtrip tuples so protocol comparison works on resume.
    protocol = json.loads(json.dumps(protocol))
    args.output.mkdir(parents=True, exist_ok=True)
    lock = (args.output / '.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    if (args.output / 'protocol.json').exists():
        if json.loads((args.output / 'protocol.json').read_text()) != protocol:
            raise RuntimeError('Configuration changed; use a new output directory')
    else:
        base.save(args.output / 'protocol.json', protocol)
        base.save(args.output / 'clock_check.json', base.check_clock())
    rows = []
    for i, design in enumerate(designs):
        order = ('agr', 'pa2') if i % 2 == 0 else ('pa2', 'agr')
        current = {}
        for flow in (*order, 'abc_c', 'abc_mix'):
            path = args.output / design / flow / 'result.json'
            if path.exists():
                row = json.loads(path.read_text())
                if row.get('endpoint_sha256') and base.sha(path.parent / 'optimized.aig') != row['endpoint_sha256']:
                    raise RuntimeError('Saved endpoint changed: ' + str(path))
            else:
                if path.parent.exists():
                    raise RuntimeError('Incomplete attempt preserved; use a labelled new output directory: ' + str(path.parent))
                targets = None
                if flow in FILLERS:
                    if any(current[f]['status'] != 'ok' for f in ('agr', 'pa2')):
                        row = dict(design=design, flow=flow, status='blocked', error='Reference synthesis failed')
                        path.parent.mkdir(parents=True)
                        base.save(path, row)
                        current[flow] = row
                        rows.append(row)
                        summarize(args.output, rows, designs)
                        continue
                    targets = [max(current[f]['slot_cpu_s'][j] for f in ('agr', 'pa2')) for j in range(3)]
                base.save(args.output / 'status.json', dict(state='running', design=design, flow=flow, finished=len(rows)))
                row = synth(args, design, flow, targets, replay.get(design, {}).get(flow), env)
                if row['status'] == 'ok':
                    try:
                        base.evaluate(args, row, env)
                    except Exception as exc:
                        row.update(metric_status='failed', error=str(exc))
                base.save(path, row)
            current[flow] = row
            rows.append(row)
            summarize(args.output, rows, designs)
            print(design, flow, row.get('synthesis_cpu_s'), row.get('mapped_hpwl'), row.get('cec'), row.get('error', ''), flush=True)
    base.save(args.output / 'status.json', dict(state='finished', endpoints=len(rows), requested=len(FLOWS) * len(designs)))


if __name__ == '__main__':
    main()
