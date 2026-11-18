"""Fixed-floorplan routing, raw Liberty verification and extracted timing replay."""
import json
import math
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time

from common import (THREADS, UTIL, benchmark, digest, invoke, library_files, quote, read,
                    require, retry, seal, sealed, setup, write)

CONGESTION = re.compile(r'\[ERROR (?:GRT|GPL)-\d+\][^\n]*(?:congest|overflow|utilization)', re.I)
PLATFORMS = {
    "asap7": dict(vars_file="asap7/asap7.vars", driver="BUFx2_ASAP7_75t_R",
        step=.27, margin=1.08, minimum=10,
        physical_only="FILLER* TAPCELL*", area_exclude="FILLER* TAPCELL*", buffer_patterns="BUF*"),
    "nangate45": dict(vars_file="Nangate45/Nangate45.vars", driver="BUF_X2",
        step=1.4, margin=5.6, minimum=56,
        physical_only="FILLCELL* TAPCELL* ANTENNA*", area_exclude="FILLCELL* TAPCELL*", buffer_patterns="BUF* CLKBUF*"),
    "sky130hd": dict(vars_file="sky130hd/sky130hd.vars", driver="sky130_fd_sc_hd__buf_2",
        step=2.72, margin=10.88, minimum=81.6,
        physical_only="sky130_fd_sc_hd__fill_* sky130_fd_sc_hd__tap* sky130_fd_sc_hd__decap_* sky130_fd_sc_hd__diode_*",
        area_exclude="sky130_fd_sc_hd__fill_* sky130_fd_sc_hd__tap* sky130_fd_sc_hd__decap_*",
        buffer_patterns="sky130_fd_sc_hd__buf_* sky130_fd_sc_hd__clkbuf_*"),
}


def tcl(value):
    value = str(value)
    assert not any(c in value for c in "{}\\\n"), value
    return "{"+value+"}"


def coverage(log):
    missing = re.search(r"Found (\d+) unannotated drivers\.", log)
    partial = re.search(r"Found (\d+) partially unannotated drivers\.", log)
    assert missing and partial
    section = log[missing.end():partial.start()]
    names = [s.strip() for s in section.splitlines() if s.strip()]
    disconnected = re.findall(r"^SCM_DISCONNECTED_CONSTANT (.+)$", log, re.M)
    outputs = re.findall(r"^SCM_DISCONNECTED_OUTPUT (.+)$", log, re.M)
    assert len(names) == int(missing[1])
    # OpenSTA escapes slashes embedded in flat instance names only in reports.
    normalized = [s.replace("\\/", "/") for s in names]
    assert all("\\" not in s for s in normalized), names
    annotation = dict(unannotated=sum(s not in disconnected+outputs for s in normalized),
                      partially_unannotated=int(partial[1]))
    assert not any(annotation.values()), annotation
    return dict(annotation=annotation, raw_unannotated=int(missing[1]),
                disconnected_constant_drivers=disconnected, disconnected_output_drivers=outputs,
                raw_unannotated_names=names)


def verify(args, work, lib, design, netlist, tag, cpu):
    yosys = args.yosys
    model = work/(tag+"-model.blif")
    structure = work/(tag+"-model.json")
    script = work/(tag+"-model.ys")
    libraries = library_files(args.platforms)[lib]
    # Existing explicit tie-cell models remain part of the checked Verilog.
    # All other cells, including individual multi-output pins, use Liberty.
    lines = ["read_verilog "+json.dumps(str(netlist))]
    lines += ["read_liberty -nooverwrite -ignore_miss_func -ignore_miss_dir "+json.dumps(str(path))
              for path in libraries]
    lines += ["hierarchy -check -auto-top", args.flatten, "proc", "opt_clean",
              "check -assert", "write_json "+json.dumps(str(structure)),
              "write_blif "+json.dumps(str(model))]
    script.write_text("\n".join(lines)+"\n")
    started = time.monotonic()
    timeout = getattr(args, 'physical_cec_timeout', 120)
    with (work/(tag+"-model.log")).open("w") as stream:
        result = subprocess.run(["taskset", "-c", str(cpu), str(yosys), "-Q", "-T", "-s", str(script)],
            stdout=stream, stderr=subprocess.STDOUT, timeout=timeout, check=False)
    assert result.returncode == 0, (work, tag, "Liberty expansion")
    modules = read(structure)["modules"]
    assert len(modules) == 1
    top = next(iter(modules.values()))
    assert not int(top.get("attributes", {}).get("blackbox", "0"), 2)
    assert not top.get("memories")
    allowed = {"$_NOT_", "$_BUF_", "$_AND_", "$_OR_", "$_XOR_", "$_XNOR_",
               "$_NAND_", "$_NOR_", "$_ANDNOT_", "$_ORNOT_", "$_MUX_"}
    for cell in top["cells"].values():
        assert cell["type"] in allowed, cell["type"]
        for bits in cell["connections"].values():
            assert all(isinstance(bit, int) or bit in ["0", "1"] for bit in bits)
    for port in top["ports"].values():
        assert all(isinstance(bit, int) or bit in ["0", "1"] for bit in port["bits"])
    assert not any(line.startswith((".subckt", ".gate", ".latch", ".blackbox"))
                   for line in model.read_text().splitlines())
    source = benchmark(args.benchmarks, design)
    reference = work/(tag+"-reference.blif")
    plan = [("read", "read "+quote(source)), ("read", "strash"), ("read", "short_names"),
            ("write", "write_blif "+quote(reference)), ("read", "read_blif "+quote(model)),
            ("read", "strash"), ("proof", f"cec -T {timeout} "+quote(reference))]
    blocks, _, _, _ = invoke(args, work, plan, tag, cpu, timeout+30)
    assert "Networks are equivalent" in blocks[len(plan)], (work, tag)
    return dict(status="PASS", wall_s=time.monotonic()-started, sha256=digest(netlist),
                log=tag+".log", engine="liberty-names", model_sha256=digest(model),
                yosys_sha256=digest(yosys), libraries={str(path):digest(path) for path in libraries},
                script_sha256=digest(script), helper_sha256=digest(Path(__file__)))


def export(args, lib, design, arm, cpu):
    old = args.out/'abc'/lib/design/arm
    require(sealed(old), old)
    prior = read(old/'result.json')
    row = prior['rows'][-1]
    blif = old/'final.blif'
    require(row['endpoint'] == 'final' and row['cec'] == 'PASS' and row['sha256'] == digest(blif), old)
    work = args.out/'inputs'/lib/design/arm
    if not sealed(work):
        retry(work)
        work.mkdir(parents=True)
        net = work/'final.v'
        plan = setup(args.platforms, lib) + [('read','read_blif '+quote(blif)),
                ('read','topo'), ('write','write_verilog '+quote(net))]
        invoke(args, work, plan, 'export', cpu, 120)
        proof = verify(args, work, lib, design, net, 'cec_export', cpu)
        top = re.search(r"\bmodule\s+(\\\S+|\w+)\s*\(", net.read_text())[1].lstrip("\\")
        write(work/'result.json', dict(source_result_sha256=digest(old/'result.json'),
              abc_area=row['area'], abc_delay_ps=row['delay_ps'], netlist=str(net), top=top, proof=proof,
              original_sha256=prior['source_sha256'], prefix_sha256=prior['prefix_normalized_sha256']))
        seal(work)
    item = read(work/'result.json')
    require(item['source_result_sha256'] == digest(old/'result.json') and
            item['proof']['status'] == 'PASS' and item['proof']['sha256'] == digest(item['netlist']), work)
    if arm != 'nf':
        control = read(work.parent/'nf/result.json')
        require(all(control[k] == item[k] for k in ('original_sha256','prefix_sha256','top')), work)
    return item


def road(args, work, config, cpus, tag="openroad"):
    work.mkdir(parents=True, exist_ok=(tag == "export"))
    script = work/(tag+".tcl")
    shutil.copyfile(args.flow, script)
    conf = work/(tag+"-config.tcl")
    conf.write_text("\n".join("set "+k+" "+tcl(v) for k,v in config.items())+"\n")
    command = ["taskset", "-c", ",".join(map(str, cpus)), str(args.openroad), "-exit", str(script)]
    env = dict(os.environ, SCM_CONFIG=str(conf), OMP_NUM_THREADS=str(args.threads),
               OPENBLAS_NUM_THREADS="1", MKL_NUM_THREADS="1")
    started = time.monotonic()
    with (work/(tag+".log")).open("w") as stream:
        proc = subprocess.Popen(command, cwd=work, env=env, stdout=stream, stderr=subprocess.STDOUT,
                                start_new_session=True)
        try:
            proc.wait(timeout=90 if tag == "export" else args.timeout)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
    text = (work/(tag+".log")).read_text(errors="replace")
    records = [dict(re.findall(r"(\w+)=([^ ]+)", line)) for line in text.splitlines()
               if line.startswith("SCM_PHYSICAL ")]
    result = dict(command=command, returncode=proc.returncode, wall_s=time.monotonic()-started,
        config=config.copy(), cpus=cpus, rows=records, script_sha256=digest(script),
        netlist_sha256=digest(Path(config["netlist"])),
        errors=[line for line in text.splitlines() if "[ERROR" in line or line.startswith("Error")])
    done = "SCM_EXPORT_DONE" if tag == "export" else "SCM_PHYSICAL_DONE"
    result["status"] = "PASS" if proc.returncode == 0 and done in text and not result["errors"] else "FAIL"
    write(work/(tag+"-result.json"), result)
    assert result["status"] == "PASS", (work, result["errors"][-3:])
    if tag == "openroad":
        assert "SCM_ROUTE routed=1 drvs=0 antennas=0" in text and records[-1]["stage"] == "extracted"
        for row in records:
            assert all(math.isfinite(float(row[k])) and float(row[k]) > 0 for k in ["area", "delay_ps"])
    return result


def route_and_check(args, work, lib, design, config, cpus):
    result = road(args, work, config, cpus)
    road(args, work, dict(config, mode="export"), cpus, "export")
    assert (work/"ports_initial.tsv").read_bytes() == (work/"ports_routed.tsv").read_bytes()
    result["cec"] = verify(args, work, lib, design, work/"logic.v", "cec_routed", cpus[0])
    result["timing_met"] = float(result["rows"][-1]["delay_ps"]) <= config["period_ps"] + .001
    result["artifacts"] = {name:digest(work/name) for name in ["logic.v", "routed.odb", "routed.spef", "routed.sdc", "ports_routed.tsv"]}
    result["status"] = "PASS"
    write(work/"result.json", result)
    return result


def replay(opt, work, result, cpu):
    log = work/'replay.log'
    with log.open('w') as stream:
        subprocess.run(['taskset','-c',str(cpu),opt.openroad,'-exit',opt.replay], check=True, timeout=600,
                       cwd=work, stdout=stream, stderr=subprocess.STDOUT, env=dict(os.environ,
                       SCM_CONFIG=str(work/'openroad-config.tcl'), SCM_REPLAY_MODE='recorded',
                       OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1'))
    msg = log.read_text()
    require('SCM_REPLAY_DONE' in msg and '[ERROR' not in msg, work)
    period, delay = map(float,re.search(r'SCM_REPLAY period_ps=(\S+) delay_ps=(\S+)',msg).groups())
    for got, expected in [(delay,float(result['rows'][-1]['delay_ps'])), (period,result['config']['period_ps'])]:
        require(math.isclose(got,expected,rel_tol=2e-6,abs_tol=.002), ('STA replay',work,got,expected))
    checks = {k:None if v == 'unavailable' else float(v) for k,v in
              re.findall(r'SCM_ELECTRICAL type=(\w+) normalized_slack=(\S+)',msg)}
    require(set(checks) == {'slew','capacitance','fanout'}, work)
    result.update(replay=dict(status='PASS', reproduced_delay_ps=delay, electrical=checks,
                  log_sha256=digest(log), **coverage(msg)), electrical_met=all(v is not None and v>=0 for v in checks.values()))
    result['feasible'] = result['timing_met'] and result['electrical_met']
    result['artifacts']['routed_exact.sdc'] = digest(work/'routed_exact.sdc')
    result['artifacts']['ports_initial.tsv'] = digest(work/'ports_initial.tsv')
    write(work/'result.json', result)


def validate_route(work, r, config):
    require(r['config'] == config and r['status'] == r['cec']['status'] == r['replay']['status'] == 'PASS', work)
    require(r['netlist_sha256'] == digest(config['netlist']) and r['replay']['log_sha256'] == digest(work/'replay.log'), work)
    for name, sha in r['artifacts'].items():
        require(digest(work/name) == sha, (work, name))


def measure(opt, work, lib, design, config, cpus, anchor=None):
    if not sealed(work):
        retry(work)
        r = route_and_check(opt, work, lib, design, config, cpus)
        replay(opt, work, r, cpus[0])
        if anchor:
            require((work/'ports_initial.tsv').read_bytes() == (anchor/'ports_initial.tsv').read_bytes(), work)
        validate_route(work, r, config)
        seal(work)
    else:
        r = read(work/'result.json')
        validate_route(work, r, config)
    return r


def calibration(opt, lib, design, inp, cpus):
    base = opt.out/'calibrations'/lib/design
    platform = PLATFORMS[lib]
    for util in UTIL:
        work = base/f'util-{util:.2f}'
        margin, step = platform['margin'], platform['step']
        w = math.ceil(max(platform['minimum'], math.sqrt(inp['abc_area']/util))/step)*step
        config = {k:v for k,v in platform.items() if k not in ('minimum','margin','step')}
        config.update(library=lib, or_test=str(opt.platforms/'test'), threads=THREADS, seed=42,
                      liberties=' '.join(map(str,library_files(opt.platforms)[lib])), netlist=inp['netlist'], top=inp['top'],
                      period_ps=2*inp['abc_delay_ps'], mode='calibration', pins=str(work/'pins.tcl'),
                      die=f'0 0 {w+2*margin:.6f} {w+2*margin:.6f}',
                      core=f'{margin} {margin} {w+margin:.6f} {w+margin:.6f}')
        rejected = work/'congestion.json'
        if rejected.exists():
            previous = read(rejected)
            require(previous['config'] == config and previous['log'] == digest(work/'openroad.log'), work)
            continue
        try:
            r = measure(opt,work,lib,design,config,cpus)
        except Exception:
            log = work/'openroad.log'
            if not log.exists() or sealed(work) or not CONGESTION.search(log.read_text(errors='replace')):
                raise
            write(rejected,dict(config=config,log=digest(log)))
            continue
        pins = digest(config['pins'])
        control = base/'control.json'
        config = dict(config,mode='route',period_ps=math.ceil(1.05*float(r['rows'][-1]['delay_ps'])*1000)/1000)
        record = dict(config=config, result_sha256=digest(work/'result.json'), pins_sha256=pins, utilization=util)
        if control.exists():
            require(record == read(control), 'calibration changed: '+str(control))
        else:
            write(control,record)
        return config, work, pins
    raise ValueError(f'{lib}/{design}: NF congestion at every prespecified utilization')


def run(args, lib, design, arm, cpus):
    base = args.out/'calibrations'/lib/design
    if arm == 'calibration':
        item = export(args, lib, design, 'nf', cpus[0])
        calibration(args, lib, design, item, cpus)
        return
    control = read(base/'control.json')
    config = control['config']
    anchor = Path(config['pins']).parent
    require(sealed(anchor) and digest(anchor/'result.json') == control['result_sha256'] and
            digest(config['pins']) == control['pins_sha256'], base)
    item = export(args, lib, design, arm, cpus[0])
    measure(args, args.out/'routes'/lib/design/arm, lib, design,
            dict(config, netlist=item['netlist']), cpus, anchor)
