#!/usr/bin/env python3
from pathlib import Path
from itertools import combinations
import json
import probe_q2 as q
p=Path('q2-probe')
cut=json.loads((p/'core-roots.json').read_text())
rt=[tuple(map(int,line.split())) for line in (p/'routes.txt').read_text().splitlines()]
base={}
def put(c,k):
  base.setdefault(tuple(c),k)
for u in q.vertices:
 if u==q.s:continue
 n=[(x,i) for x,i in q.blocks.items() if u in x]
 d=sum(u in x for x in q.fixed)
 lookup={i: (x[0] if x[1]==u else x[1]) for x,i in n}
 for co in q.at_least(list(lookup),6-d):
  put(co,('degree',u,[lookup[i] for i in co]))
for v in q.L:put((q.blocks[q.pa(0,v)],),('hit',0,[v],f"l{v}"))
for v in q.R:put((q.blocks[q.pa(1,v)],q.blocks[q.pa(2,v)]),('hit',v,[1,2],f"r{v}"))
for v in q.W:
 for col,js in [('a',[0,3,4,5]),('b',[1,2,3,4,5])]:
  put(tuple(q.blocks[q.pa(j,v)] for j in js),('hit',v,js,f"b{v}{col}"))
possible=set(q.edges)|q.fixed
for f,g in q.pairs(q.vertices):
 if (f,g) in q.fixed:continue
 for h in q.vertices:
  e1,e2=q.pa(f,h),q.pa(h,g)
  if e1 not in possible or e2 not in possible:continue
  co=[q.d2[f,g]]
  if (f,g) in q.blocks:co.append(q.blocks[f,g])
  if e1 in q.blocks:co.append(-q.blocks[e1])
  if e2 in q.blocks:co.append(-q.blocks[e2])
  put(co,('witness',f,g,h))
for u in q.vertices:
 for js in combinations([v for v in q.vertices if v!=u and q.pa(u,v) not in q.fixed],7):
  put(tuple(-q.d2[q.pa(u,v)] for v in js),('budget',u,js))
for order in rt:
 co=tuple(sorted(-q.blocks[q.pa(i,j)] for i,j in zip(order,order[1:]) if q.pa(i,j) in q.blocks))
 put(co,('path',order))

def lst(items):return '['+','.join(map(str,items))+']'
def atom(i):return f'.pos {i-1}' if i>0 else f'.neg {-i-1}'
def cl(c):return lst(map(atom,c))
def render(c,r):
 tag,*rest=r
 d='(by decide)'
 if tag=='degree':
  u,js=rest; return f'sat_degree M {u} {lst(js)} {d} {d} {d}'
 if tag=='budget':
  u,js=rest; return f'sat_budget M {u} {lst(js)} {d} {d} {d}'
 if tag=='witness':
  u,v,w=rest; return f'sat_witness M (u:={u}) (v:={v}) (w:={w}) {d} {d} {d}'
 if tag=='path':
  order,=rest
  return f'sat_superset (d:={cl(c)}) {d} (sat_path M no {lst(order)} {d} {d} {d})'
 if tag=='hit':
  u,js,field=rest
  if field[0]=='l':
   v,=js; pr=f'⟨{v}, (by decide), M.{field}⟩'
  elif field[0]=='r':
   pr=f'(by rcases M.{field} with e|e; exact ⟨1,(by decide),e.symm⟩; exact ⟨2,(by decide),e.symm⟩)'
  else:
   pr=f'(by obtain ⟨j,q,e⟩ := M.{field}; exact ⟨j, by simpa [Finset.mem_insert,Finset.mem_singleton] using q,e.symm⟩)'
  return f'sat_hit (u:={u}) (xs:={lst(js)}) {pr} {d}'
 raise ValueError(r)
def specProof(rows):
 if len(rows)==1:
  c,k=rows[0]; f=cl(c)
  return 'Fmla.one '+f,f'AllLow.fmla_one _ {f} ({render(c,k)})'
 d=len(rows)//2; fl,pl=specProof(rows[:d]); fr,pr=specProof(rows[d:])
 return f'Fmla.and ({fl}) ({fr})',f'AllLow.fmla_and _ _ _ ({pl}) ({pr})'
rows=[(tuple(c),base[tuple(c)]) for _,c in cut]
prefix='Graffiti189LongestPath.CrossSaturation.ThresholdSix.Q2'
mods=[]; sub=[]
def save_ranges(r):
 if len(r)>96:
  d=len(r)//2; l,b=save_ranges(r[:d]); rr,c=save_ranges(r[d:]); return f'Fmla.and ({l}) ({rr})',f'AllLow.fmla_and _ _ _ ({b}) ({c})'
 ix=len(mods); name=f'SixSingletonQ2RootChunk{ix:02d}189'; mods.append(name)
 f,pr=specProof(r)
 has_path=any(x[1][0]=='path' for x in r)
 narg=' (no : ¬Traceable G)' if has_path else ''
 pr=pr.replace(') (AllLow',')\n  (AllLow')
 src=f'''import SixSingletonQ2Roots189

namespace {prefix}
open Sat SimpleGraph Graffiti189Ore PortCertificates
set_option maxRecDepth 8192
set_option maxHeartbeats 24000000
abbrev chunk{ix:02d} : Fmla := {f}

theorem satisfies_chunk{ix:02d} {{G : SimpleGraph Vertex}} [DecidableRel G.Adj] (M : Data G){narg} :
    (value G).satisfies_fmla chunk{ix:02d} :=
  {pr}
end {prefix}
'''
 Path(name+'.lean').write_text(src)
 return f'chunk{ix:02d}',f'satisfies_chunk{ix:02d} M'+(' no' if has_path else '')
f,term=save_ranges(rows)
fin='\n'.join('import '+m for m in ['SixSingletonQ2Cert189',*mods])
fin+=f'''

namespace {prefix}
open Sat SimpleGraph Graffiti189Ore PortCertificates
set_option maxRecDepth 32768
set_option maxHeartbeats 60000000

theorem traceable_of_data {{G : SimpleGraph Vertex}} [DecidableRel G.Adj] (M : Data G) : Traceable G := by
  by_contra no
  have p : (value G).satisfies_fmla ({f}) :=
    {term}
  exact exclusion (value G) p

#print axioms traceable_of_data
end {prefix}
'''
Path('SixSingletonQ2Semantic189.lean').write_text(fin)
Path('Q2-ROOTS.txt').write_text('\n'.join(mods)+'\n')
print(len(rows),len(mods))
