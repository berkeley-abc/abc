#!/usr/bin/env python3
"""Serial AGR / PA2 / CPU-budgeted native ABC frontend reproduction (POSIX)."""
import argparse
import csv
import ctypes
import hashlib
import io
import json
import math
import os
from pathlib import Path
import platform
import re
import resource
import selectors
import subprocess
import sys
import time

PA_CYCLE = 'pa_rs -K 8 -N 2; pa_rw; pa_rf'
ABC_CYCLE = 'resub -K 8 -N 2 -F 0; rewrite; refactor'
MAPPER = '&get; &nf; &put; stime'
FLOWS = ('agr', 'pa2', 'abc_budget')
NUM = r'[\d.eE+\-]+'
ERROR = re.compile(r'Error:|unknown command|has failed|Assertion.*failed|runtime error:|^usage:', re.I | re.M)
ANSI = re.compile(r'\x1b\[[0-9;]*m')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, obj):
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(obj, indent=2, allow_nan=False) + '\n')
    tmp.replace(path)


def quote(path):
    text = str(path)
    if any(c in text for c in '\n\r"'):
        raise ValueError('ABC paths cannot contain quotes or newlines')
    return '"' + text + '"'


def payload_hash(path):
    stream = io.BytesIO(path.read_bytes())
    h = stream.readline().split()
    if len(h) != 6 or h[0] != b'aig' or int(h[3]) != 0:
        raise ValueError('Expected a combinational binary AIGER endpoint')
    for _ in range(int(h[4])):
        if not stream.readline():
            raise ValueError('Truncated AIG outputs')
    for _ in range(2 * int(h[5])):
        while True:
            b = stream.read(1)
            if not b:
                raise ValueError('Truncated AIG AND encoding')
            if b[0] < 128:
                break
    return hashlib.sha256(stream.getvalue()[:stream.tell()]).hexdigest()


class ProcessCPU:
    """Live user+system CPU; ABC's `time` command is wall time on POSIX."""
    def __init__(self, pid):
        self.pid = pid
        if sys.platform == 'darwin':
            class Timebase(ctypes.Structure):
                _fields_ = [('numer', ctypes.c_uint32), ('denom', ctypes.c_uint32)]
            tb = Timebase()
            system = ctypes.CDLL('/usr/lib/libSystem.B.dylib')
            if system.mach_timebase_info(ctypes.byref(tb)) != 0:
                raise OSError('mach_timebase_info failed')
            self.scale = tb.numer / tb.denom / 1e9
            self.lib = ctypes.CDLL('/usr/lib/libproc.dylib', use_errno=True)
            self.func = self.lib.proc_pid_rusage
            self.func.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p]
            self.func.restype = ctypes.c_int
            self.buffer = ctypes.create_string_buffer(256)
        elif sys.platform.startswith('linux'):
            self.lib = ctypes.CDLL(None, use_errno=True)
            cid = ctypes.c_int()
            if self.lib.clock_getcpuclockid(pid, ctypes.byref(cid)) != 0:
                raise OSError('clock_getcpuclockid failed')
            self.clock_id = cid.value
        else:
            raise RuntimeError('Live CPU budgeting supports macOS and Linux')

    def read(self):
        if sys.platform == 'darwin':
            if self.func(self.pid, 0, ctypes.byref(self.buffer)) != 0:
                raise OSError(ctypes.get_errno(), 'proc_pid_rusage failed')
            # rusage_info_v0 starts with a 16-byte UUID, then two Mach-time fields.
            return sum(ctypes.c_uint64.from_buffer(self.buffer, i).value
                       for i in (16, 24)) * self.scale
        return time.clock_gettime(self.clock_id)


def check_clock():
    clock = ProcessCPU(os.getpid())
    a, b = clock.read(), time.process_time()
    while time.process_time() - b < 0.03:
        pass
    live, reference = clock.read() - a, time.process_time() - b
    if abs(live - reference) > max(0.002, reference * 0.05):
        raise RuntimeError(f'CPU-clock validation failed: {live} vs {reference}')
    return {'live_cpu_s': live, 'process_time_s': reference}


class Session:
    def __init__(self, binary, directory, env, timeout):
        directory.mkdir(parents=True, exist_ok=False)
        self.directory = directory
        self.log = (directory / 'run.log').open('wb')
        self.commands = (directory / 'commands.abc').open('w')
        self.events = []
        self.before = resource.getrusage(resource.RUSAGE_CHILDREN)
        self.started = time.monotonic()
        self.deadline = self.started + timeout
        self.p = subprocess.Popen([str(binary), '-s'], cwd=directory, env=env,
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT)
        self.clock = ProcessCPU(self.p.pid)
        self.selector = selectors.DefaultSelector()
        self.selector.register(self.p.stdout, selectors.EVENT_READ)

    def send(self, commands):
        marker = f'FRONTEND_DONE_{len(self.events):06d}'
        line = commands + '; echo ' + marker + '\n'
        self.commands.write(line)
        self.commands.flush()
        start = self.clock.read()
        self.p.stdin.write(line.encode())
        self.p.stdin.flush()
        data = b''
        pattern = re.compile(rb'(?:^|\n)' + marker.encode() + rb'\s*\r?\n')
        while not pattern.search(data):
            remaining = self.deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError('ABC session exceeded its wall-time limit')
            if not self.selector.select(min(remaining, 1)):
                continue
            chunk = os.read(self.p.stdout.fileno(), 65536)
            if not chunk:
                raise RuntimeError('ABC exited before command completion')
            self.log.write(chunk)
            self.log.flush()
            data += chunk
            text = ANSI.sub('', data.decode(errors='replace'))
            if ERROR.search(text):
                raise RuntimeError('ABC reported an error; see ' + str(self.directory / 'run.log'))
        elapsed = self.clock.read() - start
        self.events.append({'commands': commands, 'cpu_s': elapsed})
        return ANSI.sub('', data.decode(errors='replace'))

    def close(self, error=None):
        try:
            if self.p.poll() is None:
                if error:
                    self.p.kill()
                else:
                    self.p.stdin.write(b'quit\n')
                    self.p.stdin.flush()
            self.p.communicate(timeout=10)
        except (BrokenPipeError, subprocess.TimeoutExpired):
            self.p.kill()
            self.p.communicate()
        self.selector.close()
        self.commands.close()
        self.log.close()
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        record = {'returncode': self.p.returncode, 'error': error,
                  'process_cpu_s': after.ru_utime + after.ru_stime - self.before.ru_utime - self.before.ru_stime,
                  'wall_s': time.monotonic() - self.started, 'events': self.events}
        save(self.directory / 'record.json', record)
        return record


def batch(binary, directory, commands, env, timeout):
    directory.mkdir(parents=True, exist_ok=False)
    (directory / 'commands.abc').write_text(commands + '\n')
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.monotonic()
    error = None
    with (directory / 'run.log').open('w') as log:
        try:
            r = subprocess.run([str(binary), '-s', '-f', str(directory / 'commands.abc')],
                               cwd=directory, env=env, stdout=log, stderr=subprocess.STDOUT,
                               timeout=timeout)
            code = r.returncode
        except subprocess.TimeoutExpired:
            code, error = None, 'timeout'
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    text = ANSI.sub('', (directory / 'run.log').read_text(errors='replace'))
    if code != 0 or ERROR.search(text):
        error = error or 'ABC command failed'
    record = {'returncode': code, 'error': error,
              'process_cpu_s': after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime,
              'wall_s': time.monotonic() - start}
    save(directory / 'record.json', record)
    return text, record


def parse_metrics(text, mapped=False):
    h = re.search(rf'pa_stats: HPWL {NUM} -> ({NUM})\s+overflow {NUM} -> ({NUM})', text)
    if not h or not all(math.isfinite(float(x)) for x in h.groups()):
        raise ValueError('Missing or nonfinite placement metrics')
    if float(h[2]) > 0.10000001:
        raise ValueError('Fresh placement exceeds 10% overflow')
    result = {'hpwl': float(h[1]), 'overflow': float(h[2])}
    if mapped:
        m = re.search(rf'Gates\s*=\s*(\d+).*?Area\s*=\s*({NUM}).*?Delay\s*=\s*({NUM})\s*ps', text, re.S)
        if not m:
            raise ValueError('Missing mapped metrics')
        result.update(gates=int(m[1]), area=float(m[2]), delay_ps=float(m[3]))
    else:
        m = re.search(r'and\s*=\s*(\d+).*?lev\s*=\s*(\d+)', text)
        if not m:
            raise ValueError('Missing AIG metrics')
        result.update(nodes=int(m[1]), levels=int(m[2]))
    if not all(math.isfinite(v) for v in result.values()):
        raise ValueError('Nonfinite metric')
    return result


def synth(args, design, flow, target, fixed_cycles, env, expected):
    root = args.output / design / flow
    root.mkdir(parents=True, exist_ok=True)
    graph = root / 'optimized.aig'
    result = {'design': design, 'flow': flow, 'target_cpu_s': target}
    src = args.inputs / (design + '.aig')
    session = None
    error = None
    try:
        session = Session(args.abc, root / 'synthesis', env, args.timeout)
        session.send('echo FRONTEND_READY')
        session.send(f'read {quote(src)}; strash; read_lib {quote(args.liberty)}')
        begin = session.clock.read()
        step = '' if args.step is None else f' -s {args.step:.9g}'
        cycles = 0
        if flow == 'agr':
            session.send('agr' + step)
        elif flow == 'pa2':
            session.send('pa_place' + step + '; ' + PA_CYCLE + '; ' + PA_CYCLE + '; strash')
        else:
            while True:
                session.send(ABC_CYCLE)
                cycles += 1
                elapsed = session.clock.read() - begin
                if (fixed_cycles is not None and cycles >= fixed_cycles) or (fixed_cycles is None and elapsed >= target):
                    break
                if cycles >= args.max_cycles:
                    raise RuntimeError('Native cycle safety cap reached before CPU target')
            session.send('strash')
        result.update(synthesis_cpu_s=session.clock.read() - begin, cycles=cycles)
        session.send(f'write_aiger {quote(graph)}; print_stats')
        result['payload_sha256'] = payload_hash(graph)
        result['endpoint_sha256'] = sha(graph)
        if expected:
            result['retained_payload_match'] = result['payload_sha256'] == expected
            if not result['retained_payload_match']:
                raise RuntimeError('Endpoint differs from the retained paper manifest')
        result['status'] = 'ok'
    except Exception as exc:
        error = str(exc)
        result.update(status='failed', error=error)
    finally:
        if session is not None:
            rec = session.close(error)
            result['process_cpu_s'] = rec['process_cpu_s']
            if rec['returncode'] != 0:
                result.update(status='failed', error=error or 'Nonzero synthesis exit')
    save(root / 'synthesis.json', result)
    return result


def evaluate(args, row, env):
    root = args.output / row['design'] / row['flow']
    graph = root / 'optimized.aig'
    read = f'read {quote(graph)}; strash; '
    row['evaluation_cpu_s'] = 0.0
    for kind in ('aig', 'mapped'):
        command = read + 'print_stats; '
        if kind == 'mapped':
            command += f'read_lib {quote(args.liberty)}; {MAPPER}; write_blif {quote(root / "mapped.blif")}; '
        command += 'pa_place; pa_stats'
        if kind == 'mapped':
            command += f'; strash; write_aiger {quote(root / "mapped_function.aig")}'
        text, rec = batch(args.abc, root / (kind + '_evaluation'), command, env, args.timeout)
        row['evaluation_cpu_s'] += rec['process_cpu_s']
        if rec['error']:
            raise RuntimeError(kind + ': ' + rec['error'])
        row.update({kind + '_' + k: v for k, v in parse_metrics(text, kind == 'mapped').items()})
    row['metric_status'] = 'ok'
    row['cec_cpu_s'] = 0.0
    proofs = {}
    pairs = [('source', args.inputs / (row['design'] + '.aig'), graph),
             ('mapping', graph, root / 'mapped_function.aig')]
    for name, left, right in pairs:
        command = f'cec -T {args.cec_timeout} {quote(left)} {quote(right)}'
        text, rec = batch(args.abc, root / ('cec_' + name), command, env, args.cec_timeout + 10)
        passed = rec['error'] is None and 'Networks are equivalent' in text
        proof = dict(rec, status='passed' if passed else 'unproved')
        if 'NOT EQUIVALENT' in text.upper():
            proof['status'] = 'failed'
        save(root / ('cec_' + name) / 'proof.json', proof)
        proofs[name] = proof['status']
        row['cec_cpu_s'] += rec['process_cpu_s']
    row['cec'] = proofs
    row['verified'] = all(v == 'passed' for v in proofs.values())
    if 'failed' in proofs.values():
        row.update(status='failed', error='Equivalence check found a counterexample')


def geomean(values):
    return math.exp(sum(math.log(v) for v in values) / len(values)) if values and min(values) > 0 else None


def summarize(output, rows, designs):
    save(output / 'results.json', rows)
    fields = ['design', 'flow', 'status', 'metric_status', 'verified', 'cycles', 'target_cpu_s',
              'synthesis_cpu_s', 'process_cpu_s', 'evaluation_cpu_s', 'cec_cpu_s',
              'aig_nodes', 'aig_levels', 'aig_hpwl', 'mapped_gates', 'mapped_area',
              'mapped_delay_ps', 'mapped_hpwl', 'aig_overflow', 'mapped_overflow',
              'retained_payload_match', 'error']
    with (output / 'results.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fields, extrasaction='ignore')
        writer.writeheader()
        writer.writerows(rows)
    valid = {(r['design'], r['flow']): r for r in rows
             if r.get('metric_status') == 'ok' and r.get('status') == 'ok'}
    cohort = [d for d in designs if all((d, f) in valid for f in FLOWS)]
    metrics = ['aig_nodes', 'aig_levels', 'aig_hpwl', 'mapped_area', 'mapped_delay_ps', 'mapped_hpwl', 'synthesis_cpu_s', 'process_cpu_s']
    summary = {'requested_designs': designs, 'matched_designs': cohort,
               'fully_verified_designs': [d for d in cohort if all(valid[d, f].get('verified') for f in FLOWS)],
               'missing_or_failed': [{'design': d, 'flow': f} for d in designs for f in FLOWS if (d, f) not in valid],
               'unproved_endpoints': [{'design': r['design'], 'flow': r['flow'], 'cec': r.get('cec')}
                                     for r in rows if r.get('metric_status') == 'ok' and not r.get('verified')],
               'flows': {}, 'comparisons': {}}
    for flow in FLOWS:
        stats = {m: geomean([valid[d, flow][m] for d in cohort]) for m in metrics}
        for m in ('synthesis_cpu_s', 'process_cpu_s'):
            stats[m + '_mean'] = sum(valid[d, flow][m] for d in cohort) / len(cohort) if cohort else None
        summary['flows'][flow] = stats
    for ref in ('pa2', 'abc_budget'):
        comp = {}
        for m in metrics:
            pairs = [(d, valid[d, 'agr'][m] / valid[d, ref][m]) for d in cohort if valid[d, ref][m] > 0 and valid[d, 'agr'][m] > 0]
            gm = geomean([r for _, r in pairs])
            comp[m] = {'designs': [d for d, _ in pairs], 'change_pct': 100 * (gm - 1) if gm else None,
                       'per_design_pct': {d: 100 * (r - 1) for d, r in pairs},
                       'regressions': [d for d, r in pairs if r > 1.0000001]}
        summary['comparisons']['agr_vs_' + ref] = comp
    save(output / 'summary.json', summary)
    save(output / 'budgets.json', {r['design']: {'target_cpu_s': r['target_cpu_s'], 'cycles': r.get('cycles')}
                                  for r in rows if r['flow'] == 'abc_budget' and r['status'] == 'ok'})
    lines = ['# Frontend baseline reproduction', '',
             f'Matched designs: {len(cohort)}/{len(designs)}. Fully verified across all three flows: {len(summary["fully_verified_designs"])}.',
             'Negative changes favor AGR. These are new-build frontend measurements, not historical paper PPA or OpenROAD results.', '',
             '| AGR versus | AIG nodes | Levels | AIG HPWL | Mapped area | Cell delay | Mapped HPWL |',
             '|---|---:|---:|---:|---:|---:|---:|---:|']
    for ref in ('pa2', 'abc_budget'):
        comp = summary['comparisons']['agr_vs_' + ref]
        vals = [comp[m]['change_pct'] for m in metrics[:6]]
        lines.append('| ' + ref + ' | ' + ' | '.join('n/a' if v is None else f'{v:+.2f}%' for v in vals) + ' |')
    lines += ['', '| Flow | Synthesis CPU mean / geomean (s) | Process CPU mean / geomean (s) |', '|---|---:|---:|']
    for flow, stats in summary['flows'].items():
        pairs = []
        for m in ('synthesis_cpu_s', 'process_cpu_s'):
            pairs.append('n/a' if stats[m] is None else f'{stats[m + "_mean"]:.4f} / {stats[m]:.4f}')
        lines.append('| ' + flow + ' | ' + ' | '.join(pairs) + ' |')
    lines += ['', 'Synthesis CPU includes placement and every restructuring operation. Process CPU additionally includes common input/library loading and output writing. Fresh endpoint mapping/placement and CEC CPU are separate columns in results.csv.',
              'All per-design metrics and regressions are in results.csv and summary.json. Failed and unproved runs remain recorded; no failed result is a zero gain.', '',
              'Missing/failed: ' + json.dumps(summary['missing_or_failed']),
              'Unproved: ' + json.dumps(summary['unproved_endpoints'])]
    (output / 'REPORT.md').write_text('\n'.join(lines) + '\n')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--abc', type=Path, required=True)
    ap.add_argument('--inputs', type=Path, required=True, help='directory of combinational .aig inputs')
    ap.add_argument('--liberty', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True, help='new directory, or matching resumable run')
    ap.add_argument('--designs', default='all', help='all, or comma-separated input stems')
    ap.add_argument('--step', type=float, help='guidance sensitivity override; omitted uses built-in 0.28')
    ap.add_argument('--paper-inputs', action='store_true', help='require archived paper input/library hashes and retained endpoints')
    ap.add_argument('--timeout', type=int, default=600, help='wall limit per synthesis or metric process')
    ap.add_argument('--cec-timeout', type=int, default=60, help='seconds per equivalence check')
    ap.add_argument('--max-cycles', type=int, default=100000)
    ap.add_argument('--replay-cycles', type=Path, help='budgets.json from a prior run; fixes ABC work, not current CPU equality')
    args = ap.parse_args()
    for name in ('abc', 'inputs', 'liberty', 'output'):
        setattr(args, name, getattr(args, name).resolve())
    if args.step is not None and (not math.isfinite(args.step) or args.step <= 0):
        ap.error('--step must be finite and positive')
    if min(args.timeout, args.cec_timeout, args.max_cycles) <= 0:
        ap.error('limits must be positive')
    designs = sorted(p.stem for p in args.inputs.glob('*.aig')) if args.designs == 'all' else sorted(set(args.designs.split(',')))
    if not designs or any(not re.fullmatch(r'[A-Za-z0-9_-]+', d) for d in designs):
        ap.error('input stems must contain only letters, digits, underscores, or hyphens')
    hashes = {d: sha(args.inputs / (d + '.aig')) for d in designs}
    manifest_path = Path(__file__).resolve().parents[2] / 'test/physical/endpoint_manifest.json'
    manifest = json.loads(manifest_path.read_text()) if args.paper_inputs else None
    expected = {}
    if manifest:
        if sha(args.liberty) != manifest['library_sha256']:
            ap.error('library hash differs from paper manifest')
        for d in designs:
            entries = [r for r in manifest['endpoint_checks'] if r['design'] == d]
            if not entries or any(r['input_sha256'] != hashes[d] for r in entries):
                ap.error('input hash differs from paper manifest: ' + d)
            for r in entries:
                if r['step'] == (args.step if args.step is not None else 0.28):
                    expected[d, r['flow']] = r['aig_payload_sha256']
    replay = json.loads(args.replay_cycles.read_text()) if args.replay_cycles else {}
    if args.replay_cycles and any(d not in replay or not isinstance(replay[d].get('cycles'), int) or replay[d]['cycles'] < 1 for d in designs):
        ap.error('replay file must contain a positive cycle count for every design')
    env = {k: v for k, v in os.environ.items() if not k.startswith(('ABC_', 'ASAN_', 'UBSAN_'))}
    env.update(OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', VECLIB_MAXIMUM_THREADS='1')
    protocol = {'version': 1, 'runner_sha256': sha(__file__), 'binary_sha256': sha(args.abc),
                'binary': str(args.abc), 'inputs': str(args.inputs), 'input_sha256': hashes,
                'liberty': str(args.liberty), 'library_sha256': sha(args.liberty),
                'platform': platform.platform(), 'machine': platform.machine(),
                'designs': designs, 'guidance_step_override': args.step, 'default_step': 0.28,
                'paper_inputs': args.paper_inputs, 'timeout': args.timeout, 'cec_timeout': args.cec_timeout,
                'max_cycles': args.max_cycles, 'replay_cycles': replay,
                'agr': 'agr', 'pa_cycle': PA_CYCLE, 'abc_cycle': ABC_CYCLE, 'mapper': MAPPER,
                'measurement_placement': 'pa_place; pa_stats', 'budget': 'max measured AGR and PA2 synthesis CPU per design; complete native cycles',
                'environment': {k: env[k] for k in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS')}}
    args.output.mkdir(parents=True, exist_ok=True)
    import fcntl
    lock = (args.output / '.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    if (args.output / 'protocol.json').exists():
        if json.loads((args.output / 'protocol.json').read_text()) != protocol:
            raise RuntimeError('Configuration changed; use a new output directory')
    else:
        save(args.output / 'protocol.json', protocol)
        save(args.output / 'clock_check.json', check_clock())
    rows = []
    for index, design in enumerate(designs):
        order = ('agr', 'pa2') if index % 2 == 0 else ('pa2', 'agr')
        current = {}
        for flow in (*order, 'abc_budget'):
            path = args.output / design / flow / 'result.json'
            if path.exists():
                row = json.loads(path.read_text())
                graph = path.parent / 'optimized.aig'
                if row.get('endpoint_sha256') and sha(graph) != row['endpoint_sha256']:
                    raise RuntimeError('Saved endpoint changed: ' + str(graph))
            else:
                target = None
                if flow == 'abc_budget':
                    if any(current.get(f, {}).get('status') != 'ok' for f in ('agr', 'pa2')):
                        row = {'design': design, 'flow': flow, 'status': 'blocked', 'error': 'Reference synthesis failed'}
                        path.parent.mkdir(parents=True, exist_ok=True)
                        save(path, row)
                        rows.append(row)
                        summarize(args.output, rows, designs)
                        continue
                    target = max(current[f]['synthesis_cpu_s'] for f in ('agr', 'pa2'))
                root = path.parent
                if root.exists():
                    raise RuntimeError('Incomplete attempt preserved; use a labelled new output directory: ' + str(root))
                save(args.output / 'status.json', {'state': 'running', 'design': design, 'flow': flow, 'finished': len(rows)})
                row = synth(args, design, flow, target, replay.get(design, {}).get('cycles'), env, expected.get((design, flow)))
                if row['status'] == 'ok':
                    try:
                        evaluate(args, row, env)
                    except Exception as exc:
                        row.update(metric_status='failed', error=str(exc))
                save(path, row)
            current[flow] = row
            rows.append(row)
            summarize(args.output, rows, designs)
            print(design, flow, row.get('synthesis_cpu_s'), row.get('mapped_hpwl'), row.get('cec'), row.get('error', ''), flush=True)
    save(args.output / 'status.json', {'state': 'finished', 'endpoints': len(rows), 'requested': 3 * len(designs)})


if __name__ == '__main__':
    main()
