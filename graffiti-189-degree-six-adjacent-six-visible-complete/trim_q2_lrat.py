from pathlib import Path
import json
from collections import Counter
p=Path('q2-probe')
cnf=(p/'board.cnf').read_text().splitlines()
_,_,n,_=cnf[0].split()
C=[tuple(map(int,l.split()[:-1])) for l in cnf[1:]]
A={}
for s in (p/'board.lrat').read_text().splitlines():
 i,*t=s.split()
 if t[0]=='d':continue
 t=list(map(int,t)); j=t.index(0)
 A[int(i)]=(t[:j],t[j+1:-1])
end=next(i for i,(c,_) in A.items() if not c)
keep=set()
def see(i):
 if i in keep:return
 keep.add(i)
 if i>len(C):
  _,r=A[i]
  assert all(x>0 for x in r),(i,r)
  for j in r:see(j)
see(end)
roots=sorted(i for i in keep if i<=len(C))
derived=sorted(i for i in keep if i>len(C))
idx={v:i+1 for i,v in enumerate(roots+derived)}
print('trimmed:',len(roots),'root,',len(derived),'derived')
P=[C[i-1] for i in roots]
print(Counter('route' if i>len(C)-50 else 'd2-cap' if all(x<=-57 for x in C[i-1]) else 'd2-witness' if any(x>56 for x in C[i-1]) else 'degree' for i in roots))
(p/'core.cnf').write_text(f'p cnf {n} {len(roots)}\n'+''.join(' '.join(map(str,[*c,0]))+'\n' for c in P))
(p/'core.lrat').write_text(''.join(' '.join(map(str,[idx[i],*A[i][0],0,*(idx[j] for j in A[i][1]),0]))+'\n' for i in derived))
(p/'core-roots.json').write_text(json.dumps([(i,C[i-1]) for i in roots]))
