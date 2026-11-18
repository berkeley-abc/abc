"""Time the common ABC flow and prove each of its three mapped endpoints."""
import hashlib
import math
import re

from common import FLOOR, STATS, benchmark, digest, invoke, quote, read, require, retry, seal, sealed, setup, write


def normalized(path):
    lines = (s for s in path.read_text().splitlines() if s and not s.startswith('#'))
    return hashlib.sha256('\n'.join(lines).encode()).hexdigest()


def run(args, library, design, arm, cpus):
    source = benchmark(args.benchmarks, design)
    base = args.out/'abc'/library/design/'nf'
    work = base.parent/arm
    if sealed(work):
        r = read(work/'result.json')
        require(r['source_sha256'] == digest(source), work)
        for row in r['rows']:
            require(row['cec'] == 'PASS' and row['sha256'] == digest(work/(row['endpoint']+'.blif')), work)
        return
    retry(work)
    work.mkdir(parents=True)
    baseline = None
    if arm != 'nf':
        require(sealed(base), base)
        baseline = read(base/'result.json')
    mapper = {'nf':'&nf', 'scmap':'&scmap', 'Q':'&scmap -q -v', 'R':'&scmap -r -v'}.get(arm)
    if arm == 'T':
        floor = FLOOR * baseline['rows'][-1]['delay_ps']
        mapper = f'&scmap -v -T {floor:.9g}'
    require(mapper is not None, arm)
    init = setup(args.platforms, library)
    plan = init + [('prefix', c) for c in ['read '+quote(source), 'strash', '&get', '&nf',
            '&put', 'topo', 'write_blif prefix.blif', 'strash', '&get', '&dch2 -p -v']]
    plan += [('mapping', mapper), ('mapping','&put'), ('mapping','topo'),
             ('write','write_blif mapping.blif'), ('metric_mapping','stime -c'),
             ('post','mfsmap -e -R 2 -N 500 -C 1000 -M 2000 -I 10 -O 10'), ('post','topo'),
             ('write','write_blif post.blif'), ('metric_post','stime -c')]
    plan += [('backend', c) for c in ['buffer -c','topo','stime -c','upsize -c','dnsize -c']]
    plan += [('write','write_blif final.blif'), ('metric_final','stime -c')]
    blocks, log, wall, times = invoke(args, work, plan, 'run', cpus[0], args.timeout)
    require(not re.search(r'Error:|SC[WQ]_FAIL|GP_FAIL|DF_FAIL|runtime error:|Critical delay violation|Assertion', log), work/'run.log')
    prefix = normalized(work/'prefix.blif')
    if baseline:
        require(prefix == baseline['prefix_normalized_sha256'], f'{work}: mismatched prefix')
    r = dict(library=library, design=design, arm=arm, source_sha256=digest(source),
             prefix_normalized_sha256=prefix, process_wall_s=wall, mapper=mapper, rows=[], cpu_by_stage={},
             optional_fallbacks=[s for s in log.splitlines() if 'SCMap:' in s and ('retaining' in s or 'could not be' in s)])
    if arm == 'T':
        found = re.findall(r'SCMAP_AUTO_TARGET floor=(\S+) untargeted_delay=(\S+) target=(\S+)', log)
        require(len(found) == 1, work)
        got, untargeted, target = map(float, found[0])
        require(math.isclose(got, floor, rel_tol=2e-6) and
                math.isclose(target, max(floor, untargeted+.01), rel_tol=2e-6), work)
        r.update(floor_ps=got, untargeted_delay_ps=untargeted, target_ps=target,
                 nf_record_sha256=digest(base/'result.json'))
    for i, ((stage, cmd), timing) in enumerate(zip(plan, times), 1):
        r['cpu_by_stage'][stage] = r['cpu_by_stage'].get(stage, 0) + float(timing['cpu_seconds'])
        if not stage.startswith('metric_'):
            continue
        (wire, gates, area, delay), = STATS.findall(blocks[i])
        endpoint = stage.removeprefix('metric_')
        blif = work/(endpoint+'.blif')
        area, delay = float(area), float(delay)
        require(all(math.isfinite(x) and x > 0 for x in (area, delay)), blif)
        proof = init + [('proof', 'cec -n -T 600 '+quote(blif)+' '+quote(source))]
        tag = 'cec_'+endpoint
        verdict, _, proof_wall, _ = invoke(args, work, proof, tag, cpus[0], 2430)
        require('Networks are equivalent' in verdict[len(proof)], work/(tag+'.log'))
        r['rows'].append(dict(endpoint=endpoint, area=area, delay_ps=delay, gates=int(gates), wireload=wire,
                              sha256=digest(blif), normalized_sha256=normalized(blif), cec='PASS', cec_wall_s=proof_wall))
    require([v['endpoint'] for v in r['rows']] == ['mapping','post','final'], work)
    write(work/'result.json', dict(r, status='PASS'))
    seal(work)
