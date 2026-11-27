"""Deterministic labelled inputs. Deleting the last two vertices leaves a bipartite graph."""
from random import Random
from pathlib import Path
import subprocess
rng=Random(18019169)
folder=Path(__file__).resolve().parent
def encode(n, edges):
    bits=[(min(i,j),max(i,j)) in edges for j in range(1,n) for i in range(j)]
    bits.extend([False]*((-len(bits))%6))
    return chr(63+n)+''.join(chr(63+sum(int(bits[k+a])<<(5-a) for a in range(6))) for k in range(0,len(bits),6))
def candidate(n, sample):
    m=n-2
    sz=rng.randint(max(2,m//2-1),min(m-2,m//2+1))
    parts=[list(range(sz)),list(range(sz,m))]
    E=set()
    def link(x,y):E.add(tuple(sorted((x,y))))
    if sample%3==0:
        # A long alternating backbone; attach unused surplus vertices to its interior.
        path=[v for pair in zip(*parts) for v in pair]
        for a,b in zip(path,path[1:]):link(a,b)
        for side in (0,1):
            for a in set(parts[side])-set(path):link(a,rng.choice(parts[1-side]))
    else:
        # Grow a random bipartite tree without imposing a universal vertex.
        first=rng.choice(parts[0]);seen={first}
        while len(seen)<m:
            a,b=rng.choice(parts[0]),rng.choice(parts[1])
            if (a in seen)!=(b in seen):link(a,b);seen.update((a,b))
    for a in parts[0]:
        for b in parts[1]:
            if rng.random() < [0.03,0.10,0.25,0.43][sample%4]:link(a,b)
    k=rng.randrange(2,min(4,len(parts[0]),len(parts[1]))+1)
    for j in (m,m+1):
        for part in parts:
            for v in rng.sample(part,k):link(j,v)
    if sample%7==0:link(m,m+1)
    return encode(n,E)
for n,total in [(10,4000),(11,4000),(12,3000),(13,1500),(14,600),(15,250),(16,100)]:
    data=''.join(candidate(n,i)+'\n' for i in range(total))
    proc=subprocess.run([str(folder/'.build/search')],input=data,text=True,capture_output=True)
    print('n',n,proc.stdout.strip(),flush=True)
    if proc.returncode:raise SystemExit(proc.returncode)
