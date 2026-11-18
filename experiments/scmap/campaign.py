"""Run or resume a disjoint shard of the five-arm synthesis/routing campaign."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from datetime import datetime, timezone
import fcntl
import json
import os
from pathlib import Path
import shutil
import subprocess
import traceback

from common import ARMS, DESIGNS, FLOOR, HERE, LIBS, THREADS, UTIL, digest, read, require, write
import physical
import synthesis

# Decreasing raw AIG size. Alternate ends in the work queue so a few expensive
# cases start early without holding all the small designs behind them.
SIZE_ORDER = 'mem_ctrl div log2 multiplier sqrt square voter arbiter max sin bar i2c adder dec priority cavlc router ctrl int2float'.split()


def jobs(args):
    pairs = [(lib, design) for design in SIZE_ORDER for lib in LIBS]
    pairs = [(lib, d) for i, (lib, d) in enumerate(pairs) if i % args.shards == args.shard
             and (not args.designs or d in args.designs) and (not args.libraries or lib in args.libraries)]
    order = []
    while pairs:
        order.append(pairs.pop())
        if pairs:
            order.append(pairs.pop(0))
    result = {}
    for lib, design in order:
        base = f'{lib}/{design}/'
        nf, cal = base+'abc/nf', base+'physical/calibration'
        for arm in ARMS:
            result[base+'abc/'+arm] = ([] if arm == 'nf' else [nf])
        result[cal] = [nf]
        for arm in ARMS:
            result[base+'physical/'+arm] = [cal, base+'abc/'+arm]
    return result


def physical_cpus(limit):
    unique = {}
    for cpu in sorted(os.sched_getaffinity(0)):
        topo = Path(f'/sys/devices/system/cpu/cpu{cpu}/topology')
        key = tuple((topo/name).read_text().strip() for name in ('physical_package_id','core_id'))
        unique.setdefault(key, cpu)
    return list(unique.values())[:limit]


def fingerprint(args):
    inventory = read(HERE/'inputs.json')
    build = read(args.runner.with_name('build.json'))
    require(build['runner'] == digest(args.runner) and build['abc_revision'] == inventory['abc']['revision']
            and build['timer_source'] == digest(HERE/'timed_commands.c'), 'runner does not match build')
    for name in ('benchmarks','platforms'):
        for rel, sha in inventory[name]['files'].items():
            require(digest(getattr(args,name)/rel) == sha, f'changed {name} input: {rel}')
    road_version = subprocess.check_output([args.openroad,'-version'],text=True).strip()
    require(road_version == inventory['platforms']['openroad_version'], 'OpenROAD version: '+road_version)
    args.yosys = Path(shutil.which('yosys') or 'missing-yosys').resolve(strict=True)
    help_text = subprocess.check_output([args.yosys,'-Q','-T','-p','help flatten'],text=True)
    args.flatten = 'flatten -noscopeinfo' if '-noscopeinfo' in help_text else 'flatten'
    args.flow, args.replay = HERE/'flow.tcl', HERE/'replay.tcl'
    args.threads, args.physical_cec_timeout = THREADS, 600
    return dict(abc=build, inventory_sha256=digest(HERE/'inputs.json'),
                openroad_version=road_version, openroad_sha256=digest(args.openroad),
                yosys_version=subprocess.check_output([args.yosys,'-V'],text=True).strip(),
                yosys_sha256=digest(args.yosys), flatten=args.flatten, threads=THREADS, sta_threads=1,
                seed=42, nf_floor=FLOOR, utilizations=UTIL,
                scripts={p.name:digest(p) for p in [HERE/name for name in
                    ('campaign.py','synthesis.py','common.py','physical.py','flow.tcl','replay.tcl')]})


def schedule(args, graph, cpus):
    states = dict.fromkeys(graph,'queued')
    failure_dir = args.out/'failures'
    for job in states:
        if (failure_dir/job/'failure.json').is_file() and not args.retry_failed:
            states[job] = 'failed'
    free, running = set(cpus), {}
    started = datetime.now(timezone.utc).isoformat()
    def snapshot():
        write(args.out/'progress.json', dict(started_utc=started, updated_utc=datetime.now(timezone.utc).isoformat(),
              states=states, counts={s:list(states.values()).count(s) for s in ('queued','running','pass','failed','blocked')}))
    def task(job, slot):
        require(shutil.disk_usage(args.out).free >= 8*(1<<30), 'less than 8 GiB free')
        lib, design, stage, arm = job.split('/')
        (synthesis if stage == 'abc' else physical).run(args, lib, design, arm, slot)
    with ThreadPoolExecutor(max_workers=len(cpus)) as pool:
        while True:
            ready = []
            for job, deps in graph.items():
                if states[job] != 'queued':
                    continue
                if any(states[d] in ('failed','blocked') for d in deps):
                    states[job] = 'blocked'
                elif all(states[d] == 'pass' for d in deps):
                    ready.append(job)
            # Start physical work as soon as its exact dependencies are ready.
            # Give measured routes precedence over additional calibrations.
            ready.sort(key=lambda j: 2 if '/abc/' in j else int(j.endswith('/calibration')))
            for job in ready:
                n = 1 if '/abc/' in job else THREADS
                if len(free) < n:
                    continue
                slot = sorted(free)[:n]
                free.difference_update(slot)
                states[job] = 'running'
                running[pool.submit(task,job,slot)] = job, slot
            snapshot()
            if not running:
                require(all(s != 'queued' for s in states.values()), 'unschedulable dependency')
                break
            for future in wait(running, return_when=FIRST_COMPLETED).done:
                job, slot = running.pop(future)
                free.update(slot)
                try:
                    future.result()
                    states[job] = 'pass'
                    failure = failure_dir/job/'failure.json'
                    if failure.exists():
                        failure.rename(failure.with_name('prior-failure-'+str(failure.stat().st_mtime_ns)+'.json'))
                except Exception as exc:
                    states[job] = 'failed'
                    write(failure_dir/job/'failure.json', dict(job=job, error=repr(exc), trace=traceback.format_exc()))
                print(states[job].upper(), job, flush=True)
    return int(any(s != 'pass' for s in states.values()))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('action', choices=('plan','run'))
    p.add_argument('--out', type=Path)
    p.add_argument('--runner', type=Path)
    p.add_argument('--openroad', type=Path)
    p.add_argument('--benchmarks', type=Path)
    p.add_argument('--platforms', type=Path, help='OpenROAD source/platform checkout')
    p.add_argument('--cores', type=int, default=4)
    p.add_argument('--shards', type=int, default=1)
    p.add_argument('--shard', type=int, default=0)
    p.add_argument('--designs', nargs='+', choices=DESIGNS)
    p.add_argument('--libraries', nargs='+', choices=LIBS)
    p.add_argument('--timeout', type=int, default=21600)
    p.add_argument('--retry-failed', action='store_true')
    args = p.parse_args()
    require(__debug__ and 0 <= args.shard < args.shards and args.cores >= THREADS, 'invalid shard, core limit or python -O')
    graph = jobs(args)
    require(graph, 'empty shard')
    if args.action == 'plan':
        print(json.dumps(graph, indent=2))
        return 0
    for name in ('out','runner','openroad','benchmarks','platforms'):
        require(getattr(args,name), f'run needs --{name}')
        setattr(args,name,getattr(args,name).resolve())
    cpus = physical_cpus(args.cores)
    require(len(cpus) >= THREADS, 'four distinct physical cores needed for routing')
    os.sched_setaffinity(0,cpus)
    args.out.mkdir(parents=True, exist_ok=True)
    with (args.out/'.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        manifest = fingerprint(args)
        manifest.update(shard=args.shard, shards=args.shards, timeout=args.timeout)
        # JSON round trip before comparing (e.g., Python tuples become lists).
        for name, value in [('manifest.json',manifest), ('jobs.json',graph)]:
            path = args.out/name
            if path.exists():
                require(read(path) == json.loads(json.dumps(value)), f'changed provenance or plan: {name}')
            else:
                write(path,value)
        print(f'Starting {len(graph)} jobs on {len(cpus)} physical cores',flush=True)
        return schedule(args, graph, cpus)


if __name__ == '__main__':
    raise SystemExit(main())
