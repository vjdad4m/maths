#!/usr/bin/env python3
"""Diagnostic only, not Lean. CEGAR for the exact q2 color shape + d2 cap."""
import argparse,itertools,subprocess
from functools import lru_cache
from pathlib import Path

def pairs(s):return itertools.combinations(s,2)
def pa(a,b): return min(a,b),max(a,b)
A,b,s=6,7,8
P=range(6);L=(9,10);R=(11,12,13);W=(14,15);H=L+R+W
vertices=range(16)
fixed={pa(A,b),pa(A,s),pa(b,s)}|{pa(A,i) for i in (0,3,4,5)}|{pa(b,i) for i in (1,2,3,4,5)}
edges=sorted(set(pairs(P))|set(pairs(H))|{pa(i,w) for i in P for w in W}|{pa(0,i) for i in L}|{pa(k,i) for k in (1,2) for i in R})
blocks={p:i+1 for i,p in enumerate(edges)}
nx=len(edges)
d2={p:i+nx+1 for i,p in enumerate(pairs(vertices))}
def at_least(vs,k):
 if k<=0:return
 assert len(vs)>=k,(vs,k)
 yield from itertools.combinations(vs,len(vs)-k+1)

def roots():
 for v in vertices:
  if v==s: continue
  n=[i for p,i in blocks.items() if v in p]
  d=sum(v in p for p in fixed)
  yield from at_least(n,6-d)
 for a in L: yield (blocks[pa(0,a)],)
 for r in R: yield (blocks[pa(1,r)],blocks[pa(2,r)])
 for w in W:
  yield tuple(blocks[pa(i,w)] for i in (0,3,4,5))
  yield tuple(blocks[pa(i,w)] for i in (1,2,3,4,5))
 possible=set(edges)|fixed
 # Indicator implication: a nonedge joined by a two-step walk must count as distance two.
 for f,g in pairs(vertices):
  if (f,g) in fixed:continue
  for h in vertices:
   e1,e2=pa(f,h),pa(h,g)
   if e1 not in possible or e2 not in possible:continue
   clause=[d2[(f,g)]]
   if (f,g) in blocks:clause.append(blocks[f,g])
   if e1 in blocks:clause.append(-blocks[e1])
   if e2 in blocks:clause.append(-blocks[e2])
   yield tuple(clause)
 for u in vertices:
  for js in itertools.combinations([v for v in vertices if v!=u and pa(u,v) not in fixed],7):
   yield tuple(-d2[pa(u,v)] for v in js)

def longest(a):
 @lru_cache(None)
 def walk(u,remain):
  if remain==0:return (u,)
  ns=a[u]&remain
  cand=[]
  while ns:
   d=ns&-ns; ns-=d; j=d.bit_length()-1
   cand.append((pa(u,j) not in fixed,(a[j]&remain).bit_count(),j,d))
  for _,__,j,d in sorted(cand):
   p=walk(j,remain^d)
   if p:return (u,*p)
 for i in sorted(vertices,key=lambda j:a[j].bit_count()):
  p=walk(i,65535^(1<<i))
  if p:return p

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--steps',type=int,default=100);p.add_argument('--solver',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
 a.out.mkdir(exist_ok=True)
 base=list(dict.fromkeys(roots()))
 print(f'edge variables={nx}, root clauses={len(base)}',flush=True)
 prev=a.out/'routes.txt'; activated={}
 if prev.is_file():
  for line in prev.read_text().splitlines():
   path=tuple(map(int,line.split()))
   activated[tuple(sorted(-blocks[pa(i,j)] for i,j in zip(path,path[1:]) if pa(i,j) in blocks))]=path
 file=a.out/'board.cnf'
 for it in range(a.steps):
  with file.open('w') as f:
   f.write(f'p cnf {nx+len(d2)} {len(base)+len(activated)}\n')
   f.writelines(' '.join(map(str,c))+' 0\n' for c in itertools.chain(base,activated))
  res=subprocess.run([str(a.solver.resolve()),'-q',str(file)],capture_output=True,text=True)
  if res.returncode==20:
   print('UNSAT',len(activated),flush=True)
   break
  assert res.returncode==10,(res.returncode,res.stdout,res.stderr)
  var={int(t) for line in res.stdout.splitlines() if line.startswith('v ') for t in line.split()[1:] if int(t)>0}
  ep=fixed|{p for p,i in blocks.items() if i in var}
  adj=[0]*16
  for i,j in ep:adj[i]|=1<<j;adj[j]|=1<<i
  path=longest(adj)
  if path is None:
   (a.out/'relaxed-nontraceable.txt').write_text(str(sorted(ep)))
   print('Nontraceable relaxed board after',len(activated),flush=True)
   break
  cl=tuple(sorted(-blocks[pa(i,j)] for i,j in zip(path,path[1:]) if pa(i,j) in blocks))
  assert cl not in activated
  activated[cl]=path
  with prev.open('a') as f: print(*path,file=f)
  if it%10==0:print('routes',len(activated),flush=True)
