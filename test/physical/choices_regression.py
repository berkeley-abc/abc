#!/usr/bin/env python3
"""Check choice-mode equivalence, plain-mode parity and caller-state isolation."""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import subprocess


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--abc',type=Path,required=True)
    parser.add_argument('--reference',type=Path,required=True)
    parser.add_argument('--library',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    spec=importlib.util.spec_from_file_location('regression',Path(__file__).with_name('regression.py'))
    regression=importlib.util.module_from_spec(spec);spec.loader.exec_module(regression)
    regression.fixture(out/'input.blif');checks=[]

    def run(name,command,binary=args.abc,expect=None):
        result=subprocess.run([str(binary),'-s','-c',command],cwd=out,text=True,
                              stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
        (out/(name+'.log')).write_text(result.stdout)
        assert result.returncode==0,(name,result.returncode,result.stdout[-1500:])
        if expect:assert expect in result.stdout,(name,result.stdout[-1500:])
        checks.append(name)
        return re.sub(r'\x1b\[[0-9;]*m','',result.stdout)

    setup=f'read input.blif; strash; read_lib "{args.library}"; '
    run('input',setup+'write_aiger input.aig')
    original=run('plain_reference',setup+'agr; write_aiger reference.aig; &get; &nf; &put; stime',args.reference)
    run('plain_parity',setup+'agr; write_aiger plain.aig')
    assert regression.payload(out/'plain.aig')==regression.payload(out/'reference.aig')
    # Both user-owned &-space graphs and fraig_store must survive the command.
    text=run('state_isolation',setup+'fraig_store; &get; &saveaig; &w before.aig; set progressbar saved_value; agr -c -v; write_aiger choices.aig; &w after.aig; &loadaig; &w saved.aig; &get; &nf; &put; stime; fraig_restore; strash; write_aiger restored.aig; set',expect='AGR_CHOICES')
    assert regression.payload(out/'before.aig')==regression.payload(out/'after.aig')==regression.payload(out/'saved.aig')
    assert 'saved_value' in text
    m=re.search(r'AGR_CHOICES.*?base_area=([\d.e+-]+) base_delay=([\d.e+-]+) area=([\d.e+-]+) delay=([\d.e+-]+)',text)
    reported=re.findall(r'Gates\s*=.*?Area\s*=\s*([\d.e+-]+).*?Delay\s*=\s*([\d.e+-]+)',text)
    baseline=re.search(r'Gates\s*=.*?Area\s*=\s*([\d.e+-]+).*?Delay\s*=\s*([\d.e+-]+)',original)
    assert m and reported and baseline
    assert abs(float(m[1])-float(baseline[1]))<.0051 and abs(float(m[2])-float(baseline[2]))<.0051
    assert abs(float(m[3])-float(reported[0][0]))<.0051 and abs(float(m[4])-float(reported[0][1]))<.0051
    for name in ['choices','restored']:
        run('cec_'+name,f'cec input.aig {name}.aig',expect='Networks are equivalent')
    run('repeat',setup+'agr -c; agr -c -D 0; write_aiger repeated.aig',expect='AGR_CHOICES')
    run('cec_repeat','cec input.aig repeated.aig',expect='Networks are equivalent')
    diverse=run('diverse',setup+'agr -c -b -v; write_aiger diverse.aig',expect='AGR_CHOICES')
    assert 'name=input_mfs_fx ' in diverse and 'name=agr_mfs_fx ' in diverse
    standalone=run('mfs_fx_parity',setup+'&get; &if -K 6; &mfs -e -W 4 -M 1000 -C 20000 -L 1; &fx; &st; &put; &get; &nf; &put; stime')
    cost=re.search(r'name=input_mfs_fx area=([\d.e+-]+) delay=([\d.e+-]+)',diverse)
    expected=re.search(r'Gates\s*=.*?Area\s*=\s*([\d.e+-]+).*?Delay\s*=\s*([\d.e+-]+)',standalone)
    assert cost and expected
    assert all(abs(float(cost[i])-float(expected[i]))<.0051 for i in [1,2])
    run('cec_diverse','cec input.aig diverse.aig',expect='Networks are equivalent')
    text=run('compressed_state',setup+'fraig_store; &get; &saveaig; &w compressed-before.aig; agr -c -b -r -m -C 20 -f -v; write_aiger compressed.aig; &w compressed-after.aig; &loadaig; &w compressed-saved.aig; fraig_restore; strash; write_aiger compressed-restored.aig',expect='input_compress2rs_2')
    assert regression.payload(out/'compressed-before.aig')==regression.payload(out/'compressed-after.aig')==regression.payload(out/'compressed-saved.aig')
    assert 'name=input_mfs_fx_compress2rs ' in text and 'name=agr_mfs_fx_compress2rs ' in text
    assert 'sat_conflicts=20' in text
    counts=re.findall(r'merge=started snapshots=\d+ contributors=(\d+)',text)
    assert len(counts)==2 and all(1<=int(x)<=8 for x in counts)
    for name in ['compressed','compressed-restored']:
        run('cec_'+name,f'cec input.aig {name}.aig',expect='Networks are equivalent')
    run('requires_diversity',setup+'agr -c -r',expect='-r requires -c -b')
    run('reject_conflicts_zero',setup+'agr -c -C 0',expect='positive integer')
    run('reject_conflicts_fraction',setup+'agr -c -C 2.5',expect='positive integer')
    run('requires_choices_conflicts',setup+'agr -C 20',expect='-C requires -c')
    run('requires_choices_filter',setup+'agr -f',expect='-f requires -c')
    text=run('modern',setup+'agr -c -b -r -m -C 20; write_aiger modern.aig',expect='engine=dch')
    run('cec_modern','cec input.aig modern.aig',expect='Networks are equivalent')
    run('requires_choices_modern',setup+'agr -m',expect='-m requires -c')
    weighted=run('weighted',setup+'agr -c -b -r -m -W 0.25 -v; write_aiger weighted.aig; write_blif weighted.blif; &get; &nf; &put; stime',expect='delay_weight=0.25')
    m=re.search(r'AGR_CHOICES.*?base_area=([\d.e+-]+) base_delay=([\d.e+-]+) area=([\d.e+-]+) delay=([\d.e+-]+)',weighted)
    assert m and float(m[3])<=float(m[1])+1e-5 and float(m[4])<=float(m[2])+1e-5
    def ports(path,kind):
        text=path.read_text().replace('\\\n',' ')
        return re.search(r'^\.'+kind+r'\s+([^\n]+)',text,re.M)[1].split()
    for kind in ['inputs','outputs']:
        assert ports(out/'weighted.blif',kind)==ports(out/'input.blif',kind)
    run('cec_weighted','cec input.aig weighted.aig',expect='Networks are equivalent')
    guarded=run('wire_guard',setup+'agr -c -b -r -m -W 0.25 -H 3 -T 60 -v; write_aiger guarded.aig',expect='AGR_CHOICE_WIRE_RESULT')
    wire=re.search(r'AGR_CHOICE_WIRE_RESULT base_hpwl=([\d.e+-]+) hpwl=([\d.e+-]+) growth_limit_pct=3 bins=(\d+)',guarded)
    assert wire and float(wire[2])<=1.03*float(wire[1])+1e-6
    measured=run('wire_guard_measure',f'read guarded.aig; read_lib "{args.library}"; &get; &nf; &put; pa_place -B {wire[3]} -s 0.28; pa_stats')
    actual=re.search(r'pa_stats: HPWL [\d.e+-]+ -> ([\d.e+-]+)',measured)
    assert actual and abs(float(actual[1])-float(wire[2]))<.00051
    run('cec_guarded','cec input.aig guarded.aig',expect='Networks are equivalent')
    run('unlimited_parity',setup+'agr -c -b -r -m -W 0.25 -T 0; write_aiger unlimited.aig',expect='AGR_CHOICES')
    assert regression.payload(out/'unlimited.aig')==regression.payload(out/'weighted.aig')
    timeout=run('choice_timeout',setup+'fraig_store; &get; &w timeout-before.aig; agr -c -b -r -m -W 0.25 -H 3 -T 0.000000001; write_aiger timeout.aig; &w timeout-after.aig; fraig_restore; strash; write_aiger timeout-restored.aig',expect='retaining the plain AGR endpoint')
    assert 'timed_out=1' in timeout
    assert regression.payload(out/'timeout.aig')==regression.payload(out/'plain.aig')
    assert regression.payload(out/'timeout-before.aig')==regression.payload(out/'timeout-after.aig')
    for name in ['timeout','timeout-restored']:
        run('cec_'+name,f'cec input.aig {name}.aig',expect='Networks are equivalent')
    run('requires_choices_wire',setup+'agr -H 3',expect='-H requires -c')
    run('reject_wire_nan',setup+'agr -c -H nan',expect='finite percentage')
    run('reject_wire_negative',setup+'agr -c -H -1',expect='finite percentage')
    run('requires_choices_time',setup+'agr -T 1',expect='-T requires -c')
    run('requires_dch_time',setup+'agr -c -T 1',expect='requires the interruptible DCH engine')
    run('reject_time_negative',setup+'agr -c -m -T -1',expect='nonnegative time budget')
    run('reject_time_nan',setup+'agr -c -m -T nan',expect='nonnegative time budget')
    run('reject_delay_weight_nan',setup+'agr -c -W nan',expect='finite weight')
    run('reject_delay_weight_large',setup+'agr -c -W 2',expect='finite weight')
    run('requires_lib','read input.aig; agr -c',expect='requires a Liberty library')
    run('reject_nan',setup+'agr -c -D nan',expect='finite percentage')
    run('reject_negative',setup+'agr -c -D -1',expect='finite percentage')
    run('requires_choices',setup+'agr -D 5',expect='-D requires -c')
    (out/'summary.json').write_text(json.dumps(dict(checks=checks,status='passed'),indent=2)+'\n')
    print(len(checks),'choice checks passed')


if __name__=='__main__':main()
