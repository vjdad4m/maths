"""Replay the upper triangle-skeleton profile of Graffiti.pc 384b."""
from pathlib import Path
import argparse,hashlib,os,re,subprocess,tempfile,zipfile

HERE=Path(__file__).resolve().parent
BASE='graffiti-384b-leaf-cuts-sources.zip'
BASE_SHA='d43ebb35933cb048eb6322e4e38c819a1d6c42db02ccb92beb2f83d3c441d8f1'
NAMES=['ShorePairs','ShoreCounts','ShoreRanks','FixedCubics','ShoreCliquePivot','UpperClique']
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def sums(path):
    return {n:s for s,n in [r.split() for r in path.read_text().splitlines()]}
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--leaf-log',type=Path,help='reuse the full previously cold-replayed project chain, comparing all 53 object hashes')
    a=p.parse_args()
    stage=Path(tempfile.mkdtemp(prefix='.shore.',dir=HERE))
    source=HERE/BASE
    assert sha(source)==BASE_SHA
    base=stage/'leaf'
    with zipfile.ZipFile(source) as z:z.extractall(base)
    ml=Path(os.environ['CROSSFOUR_MATHLIB']).resolve()
    lean=Path(os.environ['CROSSFOUR_LEAN_BIN']).resolve()
    env=dict(os.environ,CROSSFOUR_MATHLIB=str(ml),CROSSFOUR_LEAN_BIN=str(lean))
    env['PATH']=str(lean)+os.pathsep+env['PATH']
    print('Shore replay',stage,flush=True)
    ver=subprocess.check_output([lean/'lean','--version'],text=True)
    assert 'version 4.19.0,' in ver and 'commit 6caaee842e94,' in ver
    print(ver.strip(),flush=True)
    assert subprocess.check_output(['git','-C',ml,'rev-parse','HEAD'],text=True).strip()=='c44e0c8ee63ca166450922a373c7409c5d26b00b'
    if a.leaf_log:
        log=a.leaf_log.resolve().read_text()
    else:
        p=subprocess.run(['python3','-B',base/'replay_leaf.py'],cwd=base,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        log=p.stdout
        (stage/'LeafCold.log').write_text(log)
        print(log,flush=True)
        p.check_returncode()
    for s in ['Verified 14 fresh modules and 30 standard-axiom reports.','Verified 10 supplementary objects and 15 standard-axiom reports.','Verified 5 leaf-stage modules and 18 standard-axiom reports.']:
        assert s in log
    paths=[Path(re.search('^'+label+' replay (.+)$',log,re.M).group(1))/'build' for label in ['Odd-stars','Linkage','Leaf']]
    old=stage/'old'
    with zipfile.ZipFile(base/'graffiti-384b-zero-nonleaf-sources.zip') as z:
        for n in ['OBJECTS.sha256','graffiti-384b-odd-stars-sources.zip']:z.extract(n,old)
    with zipfile.ZipFile(old/'graffiti-384b-odd-stars-sources.zip') as z:
        for n in ['CHECKED-OBJECTS.tsv','NEW-OBJECTS.sha256']:z.extract(n,old)
    oldest={n+'.olean':s for n,s,_ in [row.split('\t') for row in (old/'CHECKED-OBJECTS.tsv').read_text().splitlines()]}
    for folder,manifest,count in [(paths[0],oldest,24),(paths[0],sums(old/'NEW-OBJECTS.sha256'),14),(paths[1],sums(old/'OBJECTS.sha256'),10),(paths[2],sums(base/'OBJECTS.sha256'),5)]:
        assert len(manifest)==count
        for n,expected in manifest.items():assert sha(folder/n)==expected
    print('Authenticated all 53 predecessor objects.',flush=True)
    obj=stage/'build';obj.mkdir()
    lp=subprocess.check_output([lean/'lake','env','printenv','LEAN_PATH'],cwd=ml,env=env,text=True).strip().split(os.pathsep)
    env['LEAN_PATH']=os.pathsep.join(str(v) for v in [obj,*reversed(paths),*((ml/l).resolve() for l in lp)])
    sources=sums(HERE/'SOURCES.sha256');objects=sums(HERE/'OBJECTS.sha256');reports=0
    assert len(sources)==len(objects)==len(NAMES)
    for n in NAMES:
        f=n+'.lean';o=n+'.olean'
        assert sha(HERE/f)==sources[f]
        data=(HERE/f).read_text()
        assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',data)
        (stage/f).write_bytes((HERE/f).read_bytes())
        r=subprocess.run([lean/'lean','-j1','-s','65536','-DElab.async=false','-DwarningAsError=true','-o',obj/o,f],cwd=stage,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        print(r.stdout,end='',flush=True)
        (stage/(n+'.log')).write_text(r.stdout)
        r.check_returncode()
        assert not re.search(r'\b(?:warning|error):|sorryAx',r.stdout)
        labels=re.findall(r'^#print axioms ([\w.]+)$',data,re.M)
        checked=re.findall(r"^'(.+)' depends on axioms: \[([^\]]*)\]$",r.stdout,re.M)
        assert labels and labels==[name for name,_ in checked]
        for _,ax in checked:assert set(re.split(r',\s*',ax))<=ALLOWED
        reports+=len(checked);assert sha(obj/o)==objects[o]
    print(f'Verified {len(NAMES)} shore-stage objects and {reports} standard-axiom reports.',flush=True)
if __name__=='__main__':main()
