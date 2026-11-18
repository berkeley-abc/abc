"""Export portable, paired measurements from sealed records, including missing rows."""
import argparse
import csv
from datetime import datetime, timezone
from pathlib import Path

from common import ARMS, DESIGNS, HERE, LIBS, benchmark, digest, read, require, sealed, write


def csv_file(path, fields, rows):
    with path.open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fields, lineterminator='\n')
        writer.writeheader()
        writer.writerows(rows)


def record(work):
    if not (work/'result.json').exists() or not sealed(work):
        return None
    return read(work/'result.json')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('roots', type=Path, nargs='+', help='campaign output directory on each shard (or local mirrors)')
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--check-artifacts', action='store_true', help='also rehash local BLIF, ODB, SPEF, SDC and proof artifacts')
    p.add_argument('--stopped', action='store_true', help='inputs are the last checkpoints of a stopped campaign')
    a = p.parse_args()
    roots, manifests, states, shard_ids, observed = {}, [], {}, {}, {}
    locked = read(HERE/'inputs.json')
    for root in a.roots:
        manifest = read(root/'manifest.json')
        require(manifest['inventory_sha256'] == digest(HERE/'inputs.json'), 'wrong inputs')
        manifests.append(manifest)
        shard_ids[root] = manifest['shard']
        graph = read(root/'jobs.json')
        require(not states.keys() & graph.keys(), 'overlapping shards')
        status = read(root/'progress.json')
        observed[manifest['shard']] = status['updated_utc']
        progress = status['states']
        require(graph.keys() == progress.keys(), 'different progress/job inventories')
        states.update(progress)
        for job in graph:
            lib, design, stage, arm = job.split('/')
            roots[lib,design] = root
    if a.stopped:
        states = {k:{'running':'interrupted','queued':'not_run'}.get(v,v) for k,v in states.items()}
    protocol = {k:v for k,v in manifests[0].items() if k != 'shard'}
    require(all({k:v for k,v in m.items() if k != 'shard'} == protocol for m in manifests),
            'toolchains, protocol, or scripts differ between shards')
    rows, calibrations = [], []
    for lib in LIBS:
        for design in DESIGNS:
            root = roots.get((lib,design))
            if root is None:
                continue
            key = f'{lib}/{design}/'
            path = root/'calibrations'/lib/design
            cal = {'shard':shard_ids[root], 'library':lib, 'design':design, 'status':states[key+'physical/calibration']}
            control = None
            if (path/'control.json').exists():
                control = read(path/'control.json')
                work = path/f"util-{control['utilization']:.2f}"
                cr = record(work)
                if cr:
                    require(digest(work/'result.json') == control['result_sha256'], work)
                    cal.update(status='pass', utilization=control['utilization'], period_ps=control['config']['period_ps'],
                               delay_ps=cr['rows'][-1]['delay_ps'], area=cr['rows'][-1]['area'],
                               pins_sha256=control['pins_sha256'], result_sha256=control['result_sha256'])
                    if a.check_artifacts:
                        require(digest(work/'pins.tcl') == control['pins_sha256'], work)
                        for name, sha in cr['artifacts'].items():
                            require(digest(work/name) == sha, work/name)
            if cal['status'] == 'pass' and 'result_sha256' not in cal:
                cal['status'] = 'syncing'
            calibrations.append(cal)
            nf = record(root/'abc'/lib/design/'nf')
            for arm in ARMS:
                row = {'shard':shard_ids[root], 'library':lib, 'design':design, 'arm':arm, 'abc_status':states[key+'abc/'+arm],
                       'route_status':states[key+'physical/'+arm]}
                work = root/'abc'/lib/design/arm
                abc = record(work)
                if abc:
                    require(abc['status'] == 'PASS' and abc['arm'] == arm and abc['library'] == lib and
                            abc['design'] == design and all(v['cec'] == 'PASS' for v in abc['rows']), work)
                    require(abc['source_sha256'] == locked['benchmarks']['files'][str(benchmark(Path(),design))], work)
                    require(nf and nf['prefix_normalized_sha256'] == abc['prefix_normalized_sha256'], work)
                    if arm == 'T':
                        require(abc['nf_record_sha256'] == digest(work.parent/'nf/result.json'), work)
                    row.update(abc_status='pass', abc_cpu_s=sum(abc['cpu_by_stage'].values()),
                               mapping_cpu_s=abc['cpu_by_stage']['mapping'], abc_record_sha256=digest(work/'result.json'),
                               prefix_sha256=abc['prefix_normalized_sha256'], target_ps=abc.get('target_ps',''))
                    for v in abc['rows']:
                        row[v['endpoint']+'_area'] = v['area']
                        row[v['endpoint']+'_delay_ps'] = v['delay_ps']
                        if a.check_artifacts:
                            require(digest(work/(v['endpoint']+'.blif')) == v['sha256'], work)
                elif row['abc_status'] == 'pass':
                    row['abc_status'] = 'syncing'
                route = root/'routes'/lib/design/arm
                rr = record(route)
                inp = record(root/'inputs'/lib/design/arm)
                if rr and inp and abc and 'result_sha256' in cal:
                    require(inp['source_result_sha256'] == row['abc_record_sha256'] and inp['proof']['status'] == 'PASS'
                            and inp['proof']['sha256'] == rr['netlist_sha256'], route)
                    require(rr['status'] == rr['replay']['status'] == rr['cec']['status'] == 'PASS'
                            and rr['config'] == dict(control['config'], netlist=inp['netlist']), route)
                    require(rr['rows'][-1]['stage'] == 'extracted',route)
                    if a.check_artifacts:
                        require(digest(route/'replay.log') == rr['replay']['log_sha256'], route)
                        require(digest(root/'inputs'/lib/design/arm/'final.v') == inp['proof']['sha256'], route)
                        for name, sha in rr['artifacts'].items():
                            require(digest(route/name) == sha, route/name)
                    row.update(route_status='pass', routed_area=rr['rows'][-1]['area'], routed_delay_ps=rr['rows'][-1]['delay_ps'],
                               route_wall_s=rr['wall_s'], timing_met=rr['timing_met'], electrical_met=rr['electrical_met'],
                               route_record_sha256=digest(route/'result.json'))
                elif row['route_status'] == 'pass':
                    row['route_status'] = 'syncing'
                rows.append(row)
    a.out.mkdir(parents=True, exist_ok=True)
    fields = 'shard library design arm abc_status route_status mapping_area mapping_delay_ps post_area post_delay_ps final_area final_delay_ps mapping_cpu_s abc_cpu_s target_ps routed_area routed_delay_ps route_wall_s timing_met electrical_met prefix_sha256 abc_record_sha256 route_record_sha256'
    csv_file(a.out/'measurements.csv',fields.split(),rows)
    csv_file(a.out/'calibrations.csv','shard library design status utilization period_ps delay_ps area pins_sha256 result_sha256'.split(),calibrations)
    tally = lambda items,field: {s:sum(v[field] == s for v in items) for s in
                                 ('pass','failed','blocked','running','queued','syncing','interrupted','not_run')}
    counts = dict(abc=tally(rows,'abc_status'), routes=tally(rows,'route_status'), calibrations=tally(calibrations,'status'))
    write(a.out/'snapshot.json',dict(as_of_utc=datetime.now(timezone.utc).isoformat(), shard_observations_utc=observed,
                                    contains_all_57_pairs=len(calibrations)==57, stopped=a.stopped, counts=counts, protocol=protocol))
    print({kind:v['pass'] for kind,v in counts.items()})


if __name__ == '__main__':
    main()
