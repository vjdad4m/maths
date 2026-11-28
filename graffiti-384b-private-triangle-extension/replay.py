"""Strict Lean 4.19 replay for the threshold-free private-triangle extension for Graffiti.pc #384b."""
import argparse
from hashlib import sha256
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parent
MATHLIB='c44e0c8ee63ca166450922a373c7409c5d26b00b'
AXIOMS={'propext','Classical.choice','Quot.sound'}
TERMINALS=('TwoEarCompletion', 'ThinPairExample')
def digest(p):return sha256(p.read_bytes()).hexdigest()
def read_manifest(path):
    return {f:h for h,f in (r.split() for r in path.read_text().splitlines())}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    modes=parser.add_mutually_exclusive_group()
    modes.add_argument('--checked',type=Path,metavar='WORKSPACE',help='verify and reuse the recorded predecessor objects')
    modes.add_argument('--cold',action='store_true',help='compile every project source (default)')
    args=parser.parse_args()
    env=os.environ.copy()
    deps=ROOT.parent/'graff384b-codex/.deps'
    binpath=Path(env.get('TRIANGLE_LEAN_BIN',deps/'lean-4.19.0-linux/bin')).resolve()
    mathlib=Path(env.get('TRIANGLE_MATHLIB',deps/'mathlib4')).resolve()
    env['PATH']=str(binpath)+os.pathsep+env['PATH']
    version=subprocess.check_output([binpath/'lean','--version'],text=True).strip()
    assert 'version 4.19.0,' in version and 'commit 6caaee842e94,' in version
    assert subprocess.check_output(['git','-C',mathlib,'rev-parse','HEAD'],text=True).strip()==MATHLIB
    lib=subprocess.check_output([binpath/'lake','env','printenv','LEAN_PATH'],text=True,cwd=mathlib,env=env).strip()
    stage=Path(tempfile.mkdtemp(prefix='.triangle-replay.',dir=ROOT))
    build=stage/'build';build.mkdir();baseline=stage/'baseline';baseline.mkdir()
    env['LEAN_PATH']=os.pathsep.join(map(str,[build,baseline]+[(mathlib/x).resolve() for x in lib.split(os.pathsep)]))
    print(version,'\nMathlib',MATHLIB,'\nReplay directory',stage,flush=True)
    fresh=read_manifest(ROOT/'SOURCES.sha256');prior=read_manifest(ROOT/'PREDECESSORS.sha256')
    sources={};old=set()
    for name,h in (fresh|prior).items():
        f=ROOT/name;m=f.stem
        assert m not in sources and digest(f)==h,name
        assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',f.read_text()),name
        sources[m]=f
        if name in prior:old.add(m)
    cache={m:(h,r) for m,h,r in (l.split('\t') for l in (ROOT/'CHECKED-OBJECTS.tsv').read_text().splitlines())}
    assert set(cache)==old
    if args.checked:
        for m,(h,r) in cache.items():
            assert not Path(r).is_absolute() and '..' not in Path(r).parts
            source=(args.checked/r).resolve();assert digest(source)==h,source
            (baseline/(m+'.olean')).symlink_to(source)
        print('Matched',len(old),'predecessor objects to the source closure.',flush=True)
    visited=set();built=set();reports=0
    def compile_one(m):
        nonlocal reports
        if m in visited:return
        visited.add(m);src=sources[m];s=src.read_text()
        for d in re.findall(r'^import\s+(\S+)',s,re.M):
            if d.split('.')[0] not in ('Mathlib','Lean','Init','Std','Aesop','Batteries'):compile_one(d)
        if args.checked and m in old:return
        print('Checking',m,flush=True)
        cmd=[binpath/'lean','-j1','-s','65536','-DElab.async=false','-DwarningAsError=true',
             '-o',build/(m+'.olean'),src.name]
        result=subprocess.run(cmd,env=env,cwd=src.parent,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        (stage/(m+'.log')).write_text(result.stdout)
        print(result.stdout,end='',flush=True)
        result.check_returncode()
        assert (build/(m+'.olean')).stat().st_size and not re.search(r'\b(?:error|warning):|sorryAx|Lean\.ofReduceBool',result.stdout)
        lines=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",result.stdout,re.M)
        assert all(set(ax.split(', '))<=AXIOMS for _,ax in lines),m
        if m not in old:
            expected=re.findall(r'^#print axioms ([\w.]+)$',s,re.M)
            assert expected and expected==[nm for nm,_ in lines],m
            reports+=len(expected)
        built.add(m)
    for m in TERMINALS:compile_one(m)
    assert visited==set(sources) and built==(visited-old if args.checked else visited)
    print('Verified',len(fresh),'new modules and',reports,'standard-axiom reports.',flush=True)
if __name__=='__main__':main()
