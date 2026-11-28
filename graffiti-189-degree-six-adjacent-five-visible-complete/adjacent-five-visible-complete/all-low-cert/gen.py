from pathlib import Path
from itertools import combinations
import json
P=Path(__file__).parent
W=P.parent
paths=json.loads((P/'templates.json').read_text())
req=[[i for i in range(18) if (m>>i)&1] for m,_ in paths]
C=[[0,1,3,4,5],[0,2,6,7,8],[1,2,9,10,11]]
D=[[3,6,9,12,13],[4,7,10,14,15],[5,8,11,16,17]]
simple=[c[:2] for c in C]
thresholds=[(f'c{i}',2,c) for i,c in enumerate(C)]+[(f'd{i}',4 if i==0 else 3,c) for i,c in enumerate(D)]
clauses=[]
for i,l in enumerate(simple):clauses.append(('or',f'n{i}',l,l))
for fld,k,row in thresholds:
  for bad in combinations(row,len(row)-k+1):
    clauses.append(('count',fld,list(bad),row))
for i,l in enumerate(req):clauses.append(('tail',i,l,[]))
p=(P/'cover.cnf')
with p.open('w') as f:
  f.write(f'p cnf 18 {len(clauses)}\n')
  for typ,fl,root,row in clauses:
    f.write(' '.join(str((x+1)*(-1 if typ=='tail' else 1)) for x in root)+' 0\n')
mods='''import SixSingletonFivePortPairCert189
import DiversityElevenMathlibRup384b

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates.AllLow
open Sat
set_option maxRecDepth 32768
set_option maxHeartbeats 14000000

packed_rup no_bad_cover
  (include_str "all-low-cert/cover.cnf")
  (include_str "all-low-cert/cover.lrat")

abbrev Bit := Nat→Bool
private def valuation (B : Bit) : Sat.Valuation := fun i=>B i=true
private theorem fOne (v : Sat.Valuation) (c : Sat.Clause) (h : v.satisfies c) :
    v.satisfies (Sat.Fmla.one c) := (Sat.Fmla.satisfies_one v c).mpr h
private theorem fAnd (v : Sat.Valuation) (f g : Sat.Fmla) (a : v.satisfies f) (b : v.satisfies g) :
    v.satisfies (Sat.Fmla.and f g) := (Sat.Fmla.satisfies_and v f g).mpr ⟨a,b⟩
'''
# Use precisely the global satisfy connectors from the established checker, with its types.
orig=(W.parent/'graff384b-diversity11-middle/src/DiversityElevenCircuitBits384b.lean').read_text()
a=orig.index('theorem fmla_and'); b=orig.index('theorem fmla_one')
end=orig.index('\n', orig.index('exact', b)) if 'exact' in orig[b:] else -1
import re
z=re.search(r'theorem fmla_and.*?(?=\n(?:#print|end))',orig[a:],re.S)
conn=z.group(0)
mods=mods[:mods.index('private theorem fOne')]+conn+'\n'
mods+='\nstructure PortModel (B : Bit) : Prop where\n'
for i,l in enumerate(simple):mods+=f'  n{i} : B {l[0]}=true ∨ B {l[1]}=true\n'
for fld,k,row in thresholds: mods+=f'  {fld} : {k}≤'+'+'.join(f'marks (B {j})' for j in row)+'\n'
mods+='\ndef requirement : Fin '+str(len(paths))+' → List Nat := !['+','.join('['+','.join(map(str,l))+']' for l in req)+']\n'
mods+='def visit : Fin '+str(len(paths))+' → List (Fin 11) := !['+','.join('['+','.join(map(str,j))+']' for _,j in paths)+']\n'
mods+='private abbrev Found (B : Bit) := ∃ k,∀ i∈requirement k,B i=true\n'
mods+='private theorem mark_le_one (a : Bool) : marks a≤1 := by cases a <;> decide\n'
mods+='private theorem mark_zero (a : Bool) (h : ¬a=true) : marks a=0 := by cases a <;> simp_all [marks]\n'
terms=[]
for j,(typ,fld,l,row) in enumerate(clauses):
  assumptions=''.join(f'(.{"neg" if typ=="tail" else "pos"} {i})' for i in l)
  clausestr='['+', '.join(f'.{"neg" if typ=="tail" else "pos"} {i}' for i in l)+']'
  if typ!='tail':
    mods+=f'\nprivate theorem r{j} (B : Bit) (M : PortModel B) : (valuation B).satisfies {clausestr} := by\n'
    mods+='  change '+' → '.join(f'(¬ B {i}=true)' for i in l)+' → False\n'
  else:
    mods+=f'\nprivate theorem r{j} (B : Bit) (no : ¬ Found B) : (valuation B).satisfies {clausestr} := by\n'
    mods+='  change '+' → '.join(f'(B {i}=true)' for i in l)+' → False\n'
  hs=[f'h{i}' for i in l]
  mods+='  intro '+' '.join(hs)+'\n'
  if typ=='or':
    mods+=f'  exact M.{fld}.elim {hs[0]} {hs[1]}\n'
  elif typ=='count':
    mods+=f'  have N := M.{fld}\n'
    mods+='  rw ['+', '.join(f'mark_zero _ {i}' for i in hs)+'] at N\n'
    for i in row:
      if i not in l: mods+=f'  have u{i} := mark_le_one (B {i})\n'
    mods+='  omega\n'
  else:
    mods+=f'  apply no ⟨{fld},?_⟩\n'
    mods+='  intro i m\n'
    mods+='  change i∈['+','.join(map(str,l))+'] at m\n'
    mods+='  simp only [List.mem_cons,List.not_mem_nil,or_false] at m\n'
    mods+='  rcases m with '+'|'.join('m' for i in l)+'\n'
    for i in l:mods+=f'  · exact m.symm ▸ h{i}\n'
  terms.append(f'(fmla_one _ _ (r{j} B '+('no' if typ=='tail' else 'M')+'))')
def tree(xs):
  if len(xs)==1:return xs[0]
  m=len(xs)//2
  return f'(fmla_and _ _ _ {tree(xs[:m])} {tree(xs[m:])})'
mods+='\ntheorem has_template (B : Bit) (M : PortModel B) : Found B := by\n  by_contra no\n'
mods+='  exact no_bad_cover (valuation B) '+tree(terms)+'\n'
mods+='\n#print axioms no_bad_cover\n#print axioms has_template\nend Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates.AllLow\n'
(W/'SixSingletonFiveAllLowCert189.lean').write_text(mods)
print(len(clauses), len(paths),len(mods))
