"""Shared inputs, process timing and immutable result records."""
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time

HERE = Path(__file__).resolve().parent
ARMS = ('nf', 'scmap', 'Q', 'R', 'T')
ARITH = 'adder bar div log2 max multiplier sin sqrt square'.split()
CTRL = 'arbiter cavlc ctrl dec i2c int2float mem_ctrl priority router voter'.split()
DESIGNS = sorted(ARITH + CTRL)
LIBS = ('asap7', 'nangate45', 'sky130hd')
FLOOR = .88
UTIL = (.30, .20, .15)
THREADS = 4
ANSI = re.compile(r"\x1b\[[0-9;]*m")
STATS = re.compile(r'WireLoad = "([^"]*)".*?Gates =\s*(\d+).*?Area =\s*([\d.eE+-]+).*?Delay =\s*([\d.eE+-]+) ps')


def require(condition, message):
    if not condition:
        raise ValueError(str(message))


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(value, indent=2) + '\n')
    tmp.replace(path)


def seal(work):
    write(work/'verified.json', {'result_sha256': digest(work/'result.json')})


def sealed(work):
    if not (work/'verified.json').exists():
        return False
    require(read(work/'verified.json')['result_sha256'] == digest(work/'result.json'), work)
    return True


def retry(work):
    if work.exists():
        work.rename(work.with_name(work.name + f'.interrupted-{time.time_ns()}'))


def benchmark(root, design):
    require(design in DESIGNS, design)
    return root / ('arithmetic' if design in ARITH else 'random_control') / (design + '.aig')


def library_files(root):
    asap = root/'test/asap7'
    return {
        'asap7': [asap / name for name in (
            'asap7sc7p5t_AO_RVT_FF_nldm_211120.lib.gz',
            'asap7sc7p5t_INVBUF_RVT_FF_nldm_220122.lib.gz',
            'asap7sc7p5t_OA_RVT_FF_nldm_211120.lib.gz',
            'asap7sc7p5t_SIMPLE_RVT_FF_nldm_211120.lib.gz',
            'asap7sc7p5t_SEQ_RVT_FF_nldm_220123.lib')],
        'nangate45': [root/'test/Nangate45/Nangate45_typ.lib'],
        'sky130hd': [root/'test/sky130hd/sky130_fd_sc_hd__tt_025C_1v80.lib'],
    }


def quote(path):
    return json.dumps(str(path))


def setup(root, lib):
    plan = []
    for i, path in enumerate(library_files(root)[lib]):
        flags = '-G 250 -a'
        if lib == 'asap7':
            flags += ' -X "*x1p*_ASAP7*" -X "*xp*_ASAP7*" -X "SDF*" -X "ICG*"'
            flags += ' -m -w' if i else ' -w'
        plan.append(('library', f'read_lib {flags} {quote(path)}'))
    return plan


def invoke(args, work, plan, tag, cpu, timeout):
    script, timings = work/(tag+'.abc'), work/(tag+'.tsv')
    script.write_text('\n'.join(cmd for _, cmd in plan) + '\n')
    start = time.monotonic()
    with (work/(tag+'.log')).open('w') as stream:
        proc = subprocess.Popen(['taskset', '-c', str(cpu), args.runner, script, timings],
                                cwd=work, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            raise
    text = ANSI.sub('', (work/(tag+'.log')).read_text(errors='replace'))
    blocks = {int(m[1]): m[2] for m in re.finditer(r'^@@BEGIN (\d+) [^\n]*\n(.*?)^@@END \1 status=0$', text, re.M|re.S)}
    with timings.open() as stream:
        times = list(csv.DictReader(stream, delimiter='\t'))
    require(proc.returncode == 0 and set(blocks) == set(range(1, len(plan)+1)), f'{script}: see {tag}.log')
    require([(int(t['line']), t['command'], int(t['status'])) for t in times] ==
            [(i, cmd, 0) for i, (_, cmd) in enumerate(plan, 1)], timings)
    return blocks, text, time.monotonic()-start, times
