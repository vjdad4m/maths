"""Replay the leaf-cut and pair-alternative supplement to Graffiti.pc 384b."""
from pathlib import Path
import argparse
import hashlib
import os
import re
import subprocess
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
SOURCE = 'graffiti-384b-zero-nonleaf-sources.zip'
SOURCE_SHA = '3530c6cdc9ff175a10c1c9d12b24b533bd24ff11db14d53cf578be4c22b0c35a'
MODULES = ['IsolateBasic384b','LeafCritical','LeafExposure','PairAlternative','PairExample']
ALLOWED = {'propext','Quot.sound','Classical.choice'}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def sums(path):
    return dict((f,h) for h,f in [r.split() for r in path.read_text().splitlines()])

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--predecessor-log',type=Path,help='reuse a complete cold run after verifying all 48 project object hashes')
    args = p.parse_args()
    stage = Path(tempfile.mkdtemp(prefix='.leaf.',dir=HERE))
    src = HERE/SOURCE
    assert digest(src)==SOURCE_SHA
    base = stage/'predecessor'
    with zipfile.ZipFile(src) as archive:
        archive.extractall(base)
    lean = Path(os.environ['CROSSFOUR_LEAN_BIN']).resolve()
    ml = Path(os.environ['CROSSFOUR_MATHLIB']).resolve()
    env = dict(os.environ,CROSSFOUR_LEAN_BIN=str(lean),CROSSFOUR_MATHLIB=str(ml))
    env['PATH'] = str(lean)+os.pathsep+env['PATH']
    print('Leaf replay',stage,flush=True)
    ver = subprocess.check_output([lean/'lean','--version'],text=True)
    assert 'version 4.19.0,' in ver and 'commit 6caaee842e94,' in ver
    print(ver.strip(),flush=True)
    assert subprocess.check_output(['git','-C',ml,'rev-parse','HEAD'],text=True).strip()=='c44e0c8ee63ca166450922a373c7409c5d26b00b'
    if args.predecessor_log:
        log = args.predecessor_log.resolve().read_text()
    else:
        result = subprocess.run(['python3','-B',base/'replay_linkage.py'],cwd=base,env=env,capture_output=True,text=True,stderr=None)
        log = result.stdout
        (stage/'PredecessorCold.log').write_text(log)
        print(log,flush=True)
        result.check_returncode()
    assert 'Verified 14 fresh modules and 30 standard-axiom reports.' in log
    assert 'Verified 10 supplementary objects and 15 standard-axiom reports.' in log
    d0 = Path(re.search(r'^Odd-stars replay (.+)$',log,re.M).group(1))/'build'
    d1 = Path(re.search(r'^Linkage replay (.+)$',log,re.M).group(1))/'build'
    with zipfile.ZipFile(base/'graffiti-384b-odd-stars-sources.zip') as archive:
        baseline = stage/'old-manifests'
        for f in ['CHECKED-OBJECTS.tsv','NEW-OBJECTS.sha256']:
            archive.extract(f,baseline)
    old = (baseline/'CHECKED-OBJECTS.tsv').read_text().splitlines()
    assert len(old)==24
    for row in old:
        name,h,_ = row.split('\t');assert digest(d0/(name+'.olean'))==h
    for directory,expected,count in [(d0,sums(baseline/'NEW-OBJECTS.sha256'),14),(d1,sums(base/'OBJECTS.sha256'),10)]:
        assert len(expected)==count
        for name,h in expected.items():
            assert digest(directory/name)==h
    print('Authenticated 48 predecessor objects.',flush=True)
    obj = stage/'build';obj.mkdir()
    path = subprocess.check_output([lean/'lake','env','printenv','LEAN_PATH'],cwd=ml,env=env,text=True).strip().split(os.pathsep)
    env['LEAN_PATH'] = os.pathsep.join(str(x) for x in [obj,d1,d0,*((ml/p).resolve() for p in path)])
    shas = sums(HERE/'SOURCES.sha256')
    objs = sums(HERE/'OBJECTS.sha256')
    assert len(MODULES)==len(shas)==len(objs)
    total = 0
    for name in MODULES:
        source = name+'.lean';target = name+'.olean'
        f = HERE/source
        assert digest(f)==shas[source]
        assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',f.read_text())
        (stage/source).write_bytes(f.read_bytes())
        r = subprocess.run([lean/'lean','-j1','-s','65536','-DElab.async=false','-DwarningAsError=true','-o',obj/target,source],cwd=stage,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        (stage/(name+'.log')).write_text(r.stdout)
        print(r.stdout,end='',flush=True)
        r.check_returncode()
        assert not re.search(r'\b(?:warning|error):|sorryAx',r.stdout)
        targets = re.findall(r'^#print axioms ([\w.]+)$',f.read_text(),re.M)
        reports = re.findall(r"^'(.+)' depends on axioms: \[([^\]]*)\]$",r.stdout,re.M)
        assert targets and targets==[x for x,_ in reports]
        for _,dependencies in reports:
            assert set(re.split(r',\s*',dependencies))<=ALLOWED
        assert digest(obj/target)==objs[target]
        total+=len(reports)
    print(f'Verified {len(MODULES)} leaf-stage modules and {total} standard-axiom reports.',flush=True)

if __name__=='__main__':
    main()
