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
    run('diverse',setup+'agr -c -b -v; write_aiger diverse.aig',expect='AGR_CHOICES')
    run('cec_diverse','cec input.aig diverse.aig',expect='Networks are equivalent')
    run('requires_lib','read input.aig; agr -c',expect='requires a Liberty library')
    run('reject_nan',setup+'agr -c -D nan',expect='finite percentage')
    run('reject_negative',setup+'agr -c -D -1',expect='finite percentage')
    run('requires_choices',setup+'agr -D 5',expect='-D requires -c')
    (out/'summary.json').write_text(json.dumps(dict(checks=checks,status='passed'),indent=2)+'\n')
    print(len(checks),'choice checks passed')


if __name__=='__main__':main()
