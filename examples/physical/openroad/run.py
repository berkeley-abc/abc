#!/usr/bin/env python3
"""Pinned mapping-only OpenROAD backend for one saved combinational AIG."""
import argparse
import gzip
import hashlib
import json
import re
import shlex
import subprocess
import time
import uuid
from pathlib import Path

HERE = Path(__file__).resolve().parent
FLOW = '/OpenROAD-flow-scripts/flow'
TOOLS = '/OpenROAD-flow-scripts/tools/install'
MANIFEST = json.loads((HERE / 'toolchain.json').read_text())
DESIGNS = json.loads((HERE / 'designs.json').read_text())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2, allow_nan=False) + '\n')


def abc(args, command, log, timeout=600):
    try:
        p = subprocess.run([str(args.abc), '-s', '-c', command], cwd=args.output,
                           text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, timeout=timeout)
    except subprocess.TimeoutExpired as e:
        log.write_bytes(e.stdout or b'')
        raise RuntimeError(f'ABC timeout; proof is not passed: {log}') from e
    log.write_text(p.stdout)
    if p.returncode or re.search(r'Error:|has failed|blackbox|unknown command', p.stdout, re.I):
        raise RuntimeError(f'ABC failed: {log}')
    return p.stdout


def prepare(args):
    d = DESIGNS[args.design]
    # Stable top-level name across methods; each run has its own work directory.
    name = 'paper_' + args.design
    args.name = name
    resources = d['resources'][args.cohort]
    args.cores = resources['cores']
    args.memory = resources['memory_gib']
    if any(c in str(args.output) + str(args.aig) for c in '\n\r"'):
        raise ValueError('Paths cannot contain quotes or newlines')
    for f, expected in MANIFEST['overrides'].items():
        if sha(HERE / f) != expected:
            raise ValueError('Changed backend override: ' + f)
    identity = dict(design=args.design, cohort=args.cohort, image=args.image, aig_sha256=sha(args.aig),
                    abc_sha256=sha(args.abc), cores=args.cores, memory_gib=args.memory,
                    package_sha256={p.name: sha(p) for p in HERE.iterdir() if p.is_file()})
    args.output.mkdir(parents=True, exist_ok=True)
    protocol = args.output / 'protocol.json'
    folder = args.output / 'designs/asap7' / name
    if protocol.exists():
        saved = json.loads(protocol.read_text())
        if saved['identity'] != identity:
            raise ValueError('Inputs/setup changed; use a new output directory')
        for f, expected in saved['generated_sha256'].items():
            if sha(folder / f) != expected:
                raise ValueError('Changed generated input: ' + f)
        return
    folder.mkdir(parents=True, exist_ok=False)
    raw = folder / 'raw.v'
    abc(args, f'read "{args.aig}"; strash; write_verilog "{raw}"', args.output / 'export.log')
    verilog, count = re.subn(r'(?m)^module\s+\S+\s*\(', f'module {name} (', raw.read_text(), count=1)
    if count != 1:
        raise ValueError('Expected one combinational top-level module')
    ports = set()
    for declaration in re.findall(r'\b(?:input|output)\s+([^;]+);', verilog):
        ports.update(x.strip() for x in declaration.split(','))
    if ports != {r.split()[0] for r in d['pins_dbu']}:
        raise ValueError('AIG port names do not match the frozen paper pin layout')
    (folder / 'generic.v').write_text(verilog)
    raw.unlink()
    (folder / 'constraint.sdc').write_text((HERE / 'constraint.sdc').read_text().replace('@PERIOD_PS@', str(d['period_ps'])))
    pins = []
    records = d['pins_dbu'] if args.cohort == 'single' else sorted(d['pins_dbu'])
    for r in records:
        port, layer, xl, yl, xh, yh = r.split()
        x, y = (int(xl) + int(xh)) / 2000, (int(yl) + int(yh)) / 2000
        fmt = 'g' if args.cohort == 'single' else '.6f'
        pins.append(f'place_pin -pin_name {port} -layer {layer} -location {{{x:{fmt}} {y:{fmt}}}} -force_to_die_boundary')
    (folder / 'pins.tcl').write_text('\n'.join(pins) + '\n')
    values = dict(DESIGN_NAME=name, PLATFORM='asap7',
                  VERILOG_FILES=f'$(DESIGN_HOME)/asap7/{name}/generic.v',
                  SDC_FILE=f'$(DESIGN_HOME)/asap7/{name}/constraint.sdc',
                  PLACE_DENSITY='0.50', ABC_AREA=0, CORNER='BC', LIB_MODEL='NLDM',
                  ASAP7_USE_VT='RVT', CORE_UTILIZATION='',
                  DIE_AREA=' '.join(map(str, d['die_um'])),
                  CORE_AREA=' '.join(map(str, d['core_um'])), OR_SEED=0)
    (folder / 'config.mk').write_text(''.join(f'export {k} = {v}\n' for k, v in values.items()))
    save(protocol, dict(identity=identity, generated_sha256={f: sha(folder / f) for f in
                         ['generic.v', 'constraint.sdc', 'pins.tcl', 'config.mk']}))


def container(args, shell, stage, limit=7200):
    log = args.output / (stage + '.log')
    record = args.output / (stage + '.json')
    if record.exists():
        raise ValueError(f'Attempt already recorded: {record}; use a new output directory')
    image_id = subprocess.check_output(['docker', 'image', 'inspect', args.image,
                                        '--format', '{{.Id}}'], text=True).strip()
    image_record = args.output / 'image.json'
    if image_record.exists() and json.loads(image_record.read_text())['id'] != image_id:
        raise ValueError('Docker image changed between stages; use a new output directory')
    save(image_record, dict(requested=args.image, id=image_id))
    name = 'agr-backend-' + uuid.uuid4().hex[:12]
    cmd = ['docker', 'run', '--rm', '--name', name, '--platform', MANIFEST['platform'],
           '--cpus', str(args.cores), '--memory', f'{args.memory}g', '--memory-swap', f'{args.memory}g',
           '--env', f'OMP_NUM_THREADS={args.cores}', '--env', 'OPENBLAS_NUM_THREADS=1',
           '--mount', f'type=bind,source={args.output},target=/work/flow',
           '--mount', f'type=bind,source={HERE},target=/repro,readonly']
    for f in MANIFEST['overrides']:
        cmd += ['--mount', f'type=bind,source={HERE / f},target={FLOW}/scripts/{f},readonly']
    cmd += ['--workdir', '/work/flow', '--entrypoint', '/bin/bash', image_id, '-lc',
            'set -euo pipefail\n' + shell]
    save(args.output / (stage + '-command.json'), cmd)
    start = time.monotonic()
    status = 'failed'
    p = None
    try:
        with log.open('w') as stream:
            p = subprocess.Popen(cmd, stdout=stream, stderr=subprocess.STDOUT)
            while p.poll() is None:
                if time.monotonic() - start >= limit:
                    status = 'timeout'
                    raise TimeoutError(f'Backend active-time limit reached: {log}')
                time.sleep(1)
        if p.returncode:
            raise RuntimeError(f'Backend failed: {log}')
        status = 'ok'
    finally:
        if p is not None and p.poll() is None:
            subprocess.run(['docker', 'rm', '-f', name], stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL, timeout=30)
            p.wait(timeout=30)
        save(record, dict(status=status, returncode=p.returncode if p else None,
                          active_seconds=time.monotonic() - start))


def make(args, target, dry=False):
    values = [f'FLOW_HOME={FLOW}', 'WORK_HOME=/work/flow', 'DESIGN_HOME=/work/flow/designs',
              f'DESIGN_CONFIG=/work/flow/designs/asap7/{args.name}/config.mk',
              f'NUM_CORES={args.cores}', f'OPENROAD_EXE={TOOLS}/OpenROAD/bin/openroad',
              f'YOSYS_EXE={TOOLS}/yosys/bin/yosys', 'PYTHON_EXE=/usr/bin/python3']
    return shlex.join(['make', '-C', FLOW, '-j1', *(['-n'] if dry else []), target, *values]) + '\n'


def verify_image():
    files = {f'{FLOW}/{k}': v for k, v in MANIFEST['inherited_files'].items()}
    checks = ''.join(f'{v}  {k}\n' for k, v in files.items())
    script = "sha256sum -c <<'CHECKSUMS'\n" + checks + 'CHECKSUMS\n'
    # Source builds can change binary hashes with compiler/dependency versions.
    script += 'sha256sum ' + ' '.join(f'{TOOLS}/{k}' for k in MANIFEST['binaries']) + '\n'
    script += f'{TOOLS}/OpenROAD/bin/openroad -version | grep -F {shlex.quote(MANIFEST["openroad_version"])}\n'
    script += f'{TOOLS}/yosys/bin/yosys -V | grep -F "Yosys {MANIFEST["yosys_version"]} "\n'
    return script


def prove_mapping(args):
    mapped = args.output / 'results/asap7' / args.name / 'base/1_2_yosys.v'
    proof = args.output / 'mapping_cec.log'
    # Remove metadata and resolve library-defined tie cells in a proof-only copy.
    # The actual backend netlist remains untouched.
    lib = gzip.decompress((HERE.parent / 'data/merged_asap7_final.lib.gz').read_bytes()).decode()
    (args.output / 'proof.lib').write_text(lib)
    text = re.sub(r'\(\*.*?\*\)', '', mapped.read_text(), flags=re.S)
    for cell, pin, value in [('TIEHIx1_ASAP7_75t_R', 'H', '1'), ('TIELOx1_ASAP7_75t_R', 'L', '0')]:
        block = lib.split('cell (' + cell + ') {', 1)[1].split('\n  cell (', 1)[0]
        if f'function : "{value}";' not in block:
            raise ValueError('Unexpected tie-cell function')
        text = re.sub(rf'\b{cell}\s+\S+\s*\(\s*\.{pin}\s*\(\s*([^()]+?)\s*\)\s*\)\s*;',
                      lambda m: f"assign {m[1]} = 1'b{value};", text)
    (args.output / 'proof.v').write_text(text)
    abc(args, 'read_lib proof.lib; read_verilog -m proof.v; strash; write_aiger proof.aig',
        args.output / 'proof_convert.log')
    text = abc(args, f'cec "{args.aig}" proof.aig', proof)
    if 'Networks are equivalent' not in text or 'NOT EQUIVALENT' in text.upper():
        raise RuntimeError(f'Mapping equivalence not proved: {proof}')
    save(args.output / 'mapping_cec.json', dict(status='passed', aig_sha256=sha(args.aig),
                                              mapped_sha256=sha(mapped)))


def collect(args):
    logs = args.output / 'logs/asap7' / args.name / 'base'
    final = json.loads((logs / '6_report.json').read_text())
    route = json.loads((logs / '5_2_route.json').read_text())
    text = (args.output / 'finish.log').read_text()
    d = DESIGNS[args.design]
    boxes = re.findall(r'^PAPER_BOX (.*)$', text, re.M)
    expected = ' '.join(str(round(x * 1000)) for x in d['die_um'] + d['core_um'])
    pins = re.findall(r'^PAPER_PIN (.*)$', text, re.M)
    if boxes != [expected] * 4 or sorted(pins) != sorted(d['pins_dbu'] * 4):
        raise ValueError('Placed/routed boundary differs from frozen dimensions or pins')
    hpwl = {s: float(v) for s, v in re.findall(r'AUDIT_STAGE (\S+) HPWL_UM ([\d.eE+-]+)', text)}
    if set(hpwl) != {'3_3_place_gp', '3_5_place_dp', '5_2_route', '6_final'}:
        raise ValueError('Missing stage HPWL')
    save(args.output / 'metrics.json', dict(design=args.design, stage_hpwl_um=hpwl,
         final_area_um2=final['finish__design__instance__area'],
         final_delay_ps=d['period_ps'] - final['finish__timing__setup__ws'],
         default_activity_power_w=final['finish__power__total'],
         routed_wirelength_um=route['detailedroute__route__wirelength'],
         routed_drc_errors=route['detailedroute__route__drc_errors'], fixed_boundary_audit='passed'))
    if route['detailedroute__route__drc_errors'] != 0:
        raise RuntimeError('Routing has DRC errors; metrics retained but run is not successful')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--abc', type=Path, required=True)
    ap.add_argument('--aig', type=Path, required=True, help='optimized, unmapped endpoint')
    ap.add_argument('--design', choices=sorted(DESIGNS), required=True)
    ap.add_argument('--cohort', choices=['single', 'flow'], default='single')
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--image', default=MANIFEST['image'], help='image built with build-image.sh')
    ap.add_argument('--stage', choices=['prepare', 'check', 'floorplan', 'finish'], default='check')
    args = ap.parse_args()
    for k in ['abc', 'aig', 'output']:
        setattr(args, k, getattr(args, k).resolve())
    prepare(args)
    result = f'/work/flow/results/asap7/{args.name}/base'
    report = f'/work/flow/logs/asap7/{args.name}/base/6_report.log'
    if args.stage == 'check':
        container(args, verify_image() + make(args, result + '/2_1_floorplan.odb', dry=True), 'check', limit=120)
    elif args.stage == 'floorplan':
        container(args, verify_image() + make(args, result + '/2_1_floorplan.odb'), 'floorplan')
        try:
            prove_mapping(args)
        except Exception as e:
            save(args.output / 'mapping_cec.json', dict(status='unproved', error=str(e)))
            raise
    elif args.stage == 'finish':
        prior = json.loads((args.output / 'floorplan.json').read_text())
        proof = json.loads((args.output / 'mapping_cec.json').read_text())
        mapped = args.output / 'results/asap7' / args.name / 'base/1_2_yosys.v'
        if (prior['status'] != 'ok' or proof['status'] != 'passed'
                or proof['aig_sha256'] != sha(args.aig) or proof['mapped_sha256'] != sha(mapped)):
            raise ValueError('Successful unchanged floorplan and mapping proof required')
        remaining = 7200 - prior['active_seconds']
        if remaining <= 0:
            raise TimeoutError('No backend runtime allowance remains')
        script = verify_image() + make(args, report)
        for stage in ['3_3_place_gp', '3_5_place_dp', '5_2_route', '6_final']:
            script += f'ODB_PATH={result}/{stage}.odb STAGE={stage} {TOOLS}/OpenROAD/bin/openroad -exit /repro/audit.tcl\n'
        container(args, script, 'finish', limit=remaining)
        record = args.output / 'finish.json'
        final = json.loads(record.read_text())
        try:
            collect(args)
            final['validation'] = 'passed'
        except Exception as e:
            final.update(status='failed', validation=str(e))
            raise
        finally:
            save(record, final)
    print(f'{args.stage}: {args.output}')


if __name__ == '__main__':
    main()
