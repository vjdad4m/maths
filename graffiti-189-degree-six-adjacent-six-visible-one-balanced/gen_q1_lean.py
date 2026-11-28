"""Generate Lean semantic root proofs from the finite q1 model metadata (not a proof until replay)."""
from pathlib import Path
import json
P=Path(__file__).resolve().parent
def gen(mode,i):
    stem=f'{mode}{i}'
    rs=json.loads((P/'q1-templates'/f'{stem}.roots.json').read_text())
    paths=json.loads((P/'q1-templates'/f'{stem}.json').read_text())
    tag=f'Q1{mode.title()}{i}'
    ns=f'Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates.{tag}'
    name=f'SixSingleton{tag}Cert189'
    s=f'''import SixSingletonFiveAllLowCert189

namespace {ns}
open Sat AllLow
set_option maxRecDepth 32768
set_option maxHeartbeats 18000000

packed_rup exclusion
  (include_str "q1-templates/{stem}.cnf")
  (include_str "q1-templates/{stem}.lrat")

abbrev Bit := Nat→Bool
private def valuation (B : Bit) : Sat.Valuation := fun j=>B j=true
structure Model (B : Bit) : Prop where
'''
    rows={}
    for r in rs:
        if 'row' in r: rows.setdefault(r['name'],r)
    for nm,r in rows.items():
        guard=f'(¬ B {r["guard"]}=true) → ' if r.get('guard') is not None else ''
        score='+'.join(f'marks (B {j})' for j in r['row'])
        s+=f'  {nm} : {guard}{r["k"]}≤{score}\n'
    N=len(paths);sz=len(paths[0][1])
    s+=f'\ndef requirement : Fin {N} → List Nat := !['+','.join('['+','.join(str(j) for j in range(21) if m>>j&1)+']' for m,_ in paths)+']\n'
    s+=f'def visit : Fin {N} → List (Fin {sz}) := !['+','.join('['+','.join(map(str,l))+']' for _,l in paths)+']\n'
    s+='abbrev Found (B : Bit) := ∃ k,∀ j∈requirement k,B j=true\n'
    exclusion=any(r['name']=='exception' for r in rs)
    if exclusion:
        s+='def Bad (B : Bit) : Prop := '+' ∧ '.join(f'B {j}={"true" if (28700>>j)&1 else "false"}' for j in range(15))+'\n'
        s+='private theorem false_of_no (a : Bool) (h : ¬a=true) : a=false := by cases a <;> simp_all\n'
    s+='private theorem mark_le_one (a : Bool) : marks a≤1 := by cases a <;> decide\n'
    s+='private theorem mark_zero (a : Bool) (h : ¬a=true) : marks a=0 := by cases a <;> simp_all [marks]\n'
    terms=[]
    for n,r in enumerate(rs):
        nm=r['name'];lit=r['clause']
        idx=[abs(k)-1 for k in lit]
        cl='['+', '.join(f'.{"pos" if k>0 else "neg"} {j}' for k,j in zip(lit,idx))+']'
        tail=nm.startswith('template')
        ban=nm=='exception'
        arg='no : ¬ Found B' if tail else 'nb : ¬ Bad B' if ban else 'M : Model B'
        s+=f'\nprivate theorem r{n} (B : Bit) ({arg}) : (valuation B).satisfies {cl} := by\n'
        s+='  change '+' → '.join(f'({"¬ " if k>0 else ""}B {j}=true)' for k,j in zip(lit,idx))+' → False\n'
        hs=[f'h{j}' for j in idx]
        s+='  intro '+' '.join(hs)+'\n'
        if tail:
            t=int(nm.removeprefix('template'))
            s+=f'  apply no ⟨{t},?_⟩\n  intro j m\n'
            s+='  change j∈['+','.join(map(str,idx))+'] at m\n'
            s+='  simp only [List.mem_cons,List.not_mem_nil,or_false] at m\n'
            s+='  rcases m with '+'|'.join('m' for _ in idx)+'\n'
            for h in hs:s+=f'  · exact m.symm ▸ {h}\n'
        elif ban:
            s+='  exact nb ⟨'+','.join(h if k<0 else f'false_of_no _ {h}' for k,h in zip(lit,hs))+'⟩\n'
        else:
            guard=r.get('guard')
            call=f' h{guard}' if guard is not None else ''
            s+=f'  have N := M.{nm}{call}\n'
            s+='  rw ['+', '.join(f'mark_zero _ h{j}' for j in idx if j!=guard)+'] at N\n'
            for j in r['row']:
                if j not in idx:s+=f'  have u{j} := mark_le_one (B {j})\n'
            s+='  omega\n'
        terms.append(f'(fmla_one _ _ (r{n} B '+ ('no' if tail else 'nb' if ban else 'M')+'))')
    def tree(xs):
        if len(xs)==1:return xs[0]
        a=len(xs)//2
        return f'(fmla_and _ _ _ {tree(xs[:a])} {tree(xs[a:])})'
    s+='\ntheorem has_template (B : Bit) (M : Model B) '+('(nb : ¬ Bad B) ' if exclusion else '')+': Found B := by\n  by_contra no\n'
    s+='  exact exclusion (valuation B) '+tree(terms)+'\n'
    s+=f'\n#print axioms exclusion\n#print axioms has_template\nend {ns}\n'
    (P/f'{name}.lean').write_text(s)
    print(name,len(rs),len(paths),len(s))
for m in ('sparse','dense','isolated'):
    for i in range(3):gen(m,i)
