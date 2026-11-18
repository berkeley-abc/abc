"""Build ABC and the command timer with identical release options."""
import argparse
import gzip
from pathlib import Path
import shlex
import subprocess

from common import HERE, digest, read, require, write


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source', type=Path, required=True)
    p.add_argument('--build', type=Path, required=True)
    p.add_argument('--archive', type=Path, help='Use the unpacked git archive rather than a Git checkout')
    p.add_argument('-j', type=int, choices=range(1, 65), default=4)
    a = p.parse_args()
    src, out = a.source.resolve(), a.build.resolve()
    locked = read(HERE/'inputs.json')['abc']
    revision = locked['revision']
    if a.archive:
        with gzip.open(a.archive, 'rb') as stream:
            actual = subprocess.check_output(['git','get-tar-commit-id'], input=stream.read(1024)).decode().strip()
        require(actual == revision, 'wrong source archive')
    else:
        subprocess.run(['git','-C',src,'diff','--exit-code',revision,'--','src','Makefile','CMakeLists.txt'], check=True)
    for name, sha in locked['files'].items():
        require(digest(src/name) == sha, name)
    subprocess.run(['cmake','-G','Ninja','-S',src,'-B',out,'-DCMAKE_BUILD_TYPE=Release',
                   '-DCMAKE_EXPORT_COMPILE_COMMANDS=ON','-DABC_SKIP_TESTS=ON',
                   '-DREADLINE_FOUND=FALSE'], check=True)
    subprocess.run(['cmake','--build',out,'--target','abc','-j',str(a.j)], check=True)
    entry, = [e for e in read(out/'compile_commands.json') if e['file'].endswith('/giaScmap.c')
              and 'libabc.dir/' in e['command']]
    flags = shlex.split(entry['command'])
    require({'-O3','-DNDEBUG'} <= set(flags) and not any(
        f.startswith(('-fsanitize','-DSCM_','-UNDEBUG')) for f in flags), 'not a release build')
    for opt in ('-o','-c'):
        i = flags.index(opt)
        del flags[i:i+2]
    obj, exe = out/'timer.o', out/'timed_commands'
    subprocess.run(flags+['-c',HERE/'timed_commands.c','-o',obj], cwd=out, check=True)
    subprocess.run(['c++',obj,out/'libabc.a','-lpthread','-lm','-ldl','-lrt','-o',exe], check=True)
    write(out/'build.json', dict(abc_revision=revision, compiler=subprocess.check_output(
        [flags[0],'--version'], text=True).splitlines()[0], flags=[v.replace(str(src),'<abc>').replace(str(out),'<build>') for v in flags],
        runner=digest(exe), abc=digest(out/'abc'), timer_source=digest(HERE/'timed_commands.c')))


if __name__ == '__main__':
    main()
