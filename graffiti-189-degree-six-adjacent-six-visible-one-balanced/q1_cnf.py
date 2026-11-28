"""Produce exact candidate DIMACS clauses. The semantic link to Lean remains necessary."""
from itertools import combinations
from pathlib import Path
import json
P=Path(__file__).resolve().parent
E=list(combinations(range(6),2))
cases=[(2,2,3,3),(1,2,2,4),(1,2,3,3)]
def produce(mode,i):
    x,y,L,R=cases[i]
    modefile=P/'q1-templates'/f'{mode}{i}.json'
    roots=[]
    def atleast(row,n,name,guard=None):
        if n<=0:return
        for bad in combinations(row,len(row)-n+1):
            roots.append(dict(name=name,row=row,k=n,guard=guard,
                clause=([guard+1] if guard is not None else [])+[a+1 for a in bad]))
    for p in range(6):
        row=[j for j,(a,b) in enumerate(E) if p in (a,b)]
        k=5-L if p<x else 5-R if p<x+y else 4
        if mode=='sparse':
            atleast(row+[15+p],k,f'row{p}')
        else:
            atleast(row,k-1,f'row{p}')
            atleast(row,(5 if p<x+y else 4)-int(mode=='isolated'),f'inactive{p}',15+p)
    if mode=='sparse':
        atleast(list(range(15,21)),3,'bal')
    else:
        atleast(list(range(15,15+x)),1,'activeA')
        atleast(list(range(15+x,15+x+y)),1,'activeB')
    if i==1 and mode!='isolated':
        roots.append(dict(name='exception',clause=[-(a+1) if (28700>>a)&1 else a+1 for a in range(15)]))
    for j,(mask,path) in enumerate(json.loads(modefile.read_text())):
        roots.append(dict(name=f'template{j}',path=path,clause=[-(a+1) for a in range(21) if (mask>>a)&1]))
    out=P/'q1-templates'/f'{mode}{i}'
    out.with_suffix('.roots.json').write_text(json.dumps(roots,indent=1)+'\n')
    out.with_suffix('.cnf').write_text(f'p cnf 21 {len(roots)}\n'+''.join(' '.join(map(str,r['clause']))+' 0\n' for r in roots))
    print(mode,i,len(roots))
for m in ('sparse','dense','isolated'):
    for i in range(3):produce(m,i)
