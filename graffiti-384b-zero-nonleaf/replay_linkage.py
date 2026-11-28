"""Replay the #384b disjoint-arms supplement against the frozen odd-stars sources."""
import argparse, hashlib, os, re, subprocess, tempfile, zipfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = 'graffiti-384b-odd-stars-sources.zip'
BASE_SHA = 'e1202b8603b238e8260f3932804afd940e5c15e3ef5ddc57f053daf8a792f992'
ML_REV = 'c44e0c8ee63ca166450922a373c7409c5d26b00b'
HALL_SHA = '9cc20c593653b25aac64e2085d1311e3b0c042b51ad02d984527962785c4583f'
NAMES = ['HallFiniteBase', 'HallArms', 'OrbitArms', 'OriginalArms', 'ParityArms', 'TerminalArms', 'ShortestArms', 'CycleSquareArms', 'PendantAudit', 'ZeroLeaf384b']
ALLOWED = {'propext','Classical.choice','Quot.sound'}
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def read_sums(path):
    return {name:sha for sha,name in [line.split() for line in path.read_text().splitlines()]}
def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-log',type=Path,help='authenticate an existing complete cold or checked base replay')
    args = parser.parse_args()
    stage=Path(tempfile.mkdtemp(prefix='.linkage.',dir=HERE))
    base=stage/'base'
    source=HERE/BASE
    assert digest(source)==BASE_SHA
    with zipfile.ZipFile(source) as archive:
        archive.extractall(base)
    ml=Path(os.environ['CROSSFOUR_MATHLIB']).resolve()
    lean=Path(os.environ['CROSSFOUR_LEAN_BIN']).resolve()
    env=dict(os.environ,CROSSFOUR_MATHLIB=str(ml),CROSSFOUR_LEAN_BIN=str(lean))
    env['PATH']=str(lean)+os.pathsep+env['PATH']
    print('Linkage replay',stage,flush=True)
    ver=subprocess.check_output([lean/'lean','--version'],text=True).strip()
    assert 'version 4.19.0,' in ver and 'commit 6caaee842e94,' in ver
    assert subprocess.check_output(['git','-C',ml,'rev-parse','HEAD'],text=True).strip()==ML_REV
    print(ver,flush=True)
    if args.baseline_log:
        log=args.baseline_log.resolve().read_text()
    else:
        proc=subprocess.run(['python3','-B',str(base/'replay.py'),'--cold'],cwd=base,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        log=proc.stdout
        (stage/'BaseCold.log').write_text(log)
        print(log,flush=True)
        proc.check_returncode()
    assert re.search(r'^Verified 14 fresh modules and \d+ standard-axiom reports\.$',log,re.M)
    base_stage=Path(re.search(r'^Odd-stars replay (.+)$',log,re.M).group(1))
    prior={}
    for line in (base/'CHECKED-OBJECTS.tsv').read_text().splitlines():
        name,sha,_=line.split('\t')
        p=base_stage/'build'/(name+'.olean')
        if not p.is_file():p=base_stage/'prior'/(name+'.olean')
        assert digest(p)==sha,p
        prior[name]=p
    new=read_sums(base/'NEW-OBJECTS.sha256')
    assert len(prior)==24 and len(new)==14
    for name,sha in new.items():
        assert digest(base_stage/'build'/name)==sha
    print('Authenticated all 38 baseline objects.',flush=True)
    obj=stage/'build';obj.mkdir()
    paths=subprocess.check_output([lean/'lake','env','printenv','LEAN_PATH'],env=env,cwd=ml,text=True).strip().split(os.pathsep)
    env['LEAN_PATH']=os.pathsep.join(str(p) for p in [obj,base_stage/'build',base_stage/'prior',*((ml/p).resolve() for p in paths)])
    assert digest(ml/'Mathlib/Combinatorics/Hall/Finite.lean')==HALL_SHA
    assert digest(HERE/'HallFiniteBase.lean')==HALL_SHA
    shas=read_sums(HERE/'SOURCES.sha256')
    objects=read_sums(HERE/'OBJECTS.sha256')
    reports=0
    for name in NAMES:
        source_name=name+'.lean';object_name=name+'.olean'
        f=HERE/source_name
        assert digest(f)==shas[source_name]
        assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',f.read_text())
        (stage/source_name).write_bytes(f.read_bytes())
        p=subprocess.run([lean/'lean','-j1','-s','65536','-DElab.async=false','-DwarningAsError=true','-o',obj/object_name,source_name],env=env,cwd=stage,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        (stage/(name+'.log')).write_text(p.stdout)
        print(p.stdout,end='',flush=True)
        p.check_returncode()
        assert not re.search(r'\b(?:error|warning):|sorryAx',p.stdout)
        declared=re.findall(r'^#print axioms ([\w.\']+)$',f.read_text(),re.M)
        found=re.findall(r"^'(.+)' depends on axioms: \[([^\]]*)\]$",p.stdout,re.M)
        assert declared==[x for x,_ in found]
        for _,deps in found: assert set(re.split(r',\s*',deps))<=ALLOWED
        assert digest(obj/object_name)==objects[object_name]
        reports+=len(found)
    print(f'Verified {len(NAMES)} supplementary objects and {reports} standard-axiom reports.',flush=True)
if __name__=='__main__':
    main()