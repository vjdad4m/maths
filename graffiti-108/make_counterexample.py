from itertools import combinations
import json
V=list(combinations(range(7),3))
m=[sum(1<<i for i in v) for v in V]
A=lambda u,v: not m[u]&m[v]
def find(u,v):
 for a in range(35):
  if A(u,a):
   for b in range(35):
    if A(a,b) and A(b,v):return (a,b)
 return (0,0)
rs=[[find(u,v) for v in range(35)] for u in range(35)]
out=[]
out.append('def triples : Array Nat := #'+str(m))
out.append('def routes : Array (Array (Nat × Nat)) := #['+',\n'.join('#'+str(row) for row in rs)+']')
open('generated.inc','w').write('\n'.join(out)+'\n')
