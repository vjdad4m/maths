#!/usr/bin/env python3
from itertools import combinations
from pathlib import Path
pairs=list(combinations(range(6),2))
for mode in ('sparse','dense','isolated'):
 for ix,(x,y) in enumerate(((2,2),(1,2),(1,2))):
  name="Q1"+mode.capitalize()+str(ix)
  var=[f"some ({a},{b})" for a,b in pairs]
  var.extend(("none" if mode!='sparse' else f"some ({i},9)") for i in range(6))
  fixed=[(6,7),(6,8),(7,8)]
  fixed += [(6,i) for i in range(6) if not x<=i<x+y]
  fixed += [(7,i) for i in range(6) if i>=x]
  if mode=='isolated':fixed += [(9,i) for i in range(6)]
  n=9 if mode=='dense' else 10
  decl=f"""import SixSingleton{name}Cert189
import SixSingletonQ1TemplateWalk189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates.{name}
open Q1Template SimpleGraph Finset
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000

def fixed : List (Fin {n} × Fin {n}) := {str(fixed)}
def ends : Fin 21 → Option (Fin {n} × Fin {n}) := ![{','.join(var)}]
def start ({('_i' if mode=='sparse' else 'i')} : Fin {len(__import__('json').loads(Path(f'q1-templates/{mode}{ix}.json').read_text()))}) : Fin {n} :=
  {( '(visit i).headD 0' if mode!='sparse' else '9' )}
private theorem ok : ∀ i, (visit i).Nodup ∧ (∀ u,u∈visit i) ∧
    (visit i).Chain' (Allows fixed ends (requirement i)) ∧
    (visit i).head? = some (start i) {('∧ ∀ u, start i = u → 15 + u.val ∈ requirement i' if mode!='sparse' else '')} := by
  decide

{('theorem start_port : ∀ i, (start i).val < 6 := by decide' if mode!='sparse' else '')}

theorem from_template {{V : Type*}} [Fintype V] [DecidableEq V] {{G : SimpleGraph V}}
    (f : Fin {n}→V) (inj : Function.Injective f)
    (base : ∀ u v,(u,v)∈fixed → G.Adj (f u) (f v))
    (B : Bit)
    (edge : ∀ k u v,ends k=some (u,v) → B k.val=true → G.Adj (f u) (f v))
    (found : Found B) :
    ∃ i t, RouteOn G (univ.image f) (f (start i)) t {('∧ B (15+(start i).val)=true' if mode!='sparse' else '')} := by
  obtain ⟨i,hi⟩ := found
  obtain ⟨nd,cov,ch,hd{(',active' if mode!='sparse' else '')}⟩ := ok i
  obtain ⟨t,r⟩ := lift_template f inj fixed ends _ B base edge hi _ nd cov ch _ hd
  exact ⟨i,t,r{(',hi _ (active _ rfl)' if mode!='sparse' else '')}⟩

#print axioms from_template
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates.{name}
"""
  Path(f'SixSingleton{name}Walk189.lean').write_text(decl)
