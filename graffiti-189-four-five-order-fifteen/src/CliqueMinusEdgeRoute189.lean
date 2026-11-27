import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- A clique with one pair allowed to be missing is Hamilton-connected
from order five on. The connector avoids the two end vertices and the
possible exceptional pair. -/
theorem route_between_in_clique_except_pair
    (A : Finset V) (large : 5≤A.card) {e f : V}
    (near : ∀ s∈A,∀ t∈A,s≠t →
      ¬((s=e ∧ t=f) ∨ (s=f ∧ t=e)) → G.Adj s t)
    {r w : V} (ra : r∈A) (wa : w∈A) (rw' : r≠w) :
    RouteOn G A r w := by
  classical
  have small : ({r,w,e,f} : Finset V).card≤4 := by
    have a := card_insert_le r ({w,e,f} : Finset V)
    have b := card_insert_le w ({e,f} : Finset V)
    have c := card_insert_le e ({f} : Finset V)
    rw [card_singleton] at c
    omega
  have out : ¬A⊆({r,w,e,f} : Finset V) := by
    intro sub
    have h := card_le_card sub
    omega
  obtain ⟨x,xa,xx⟩ := not_subset.mp out
  have xr : x≠r := fun h=>xx (by simp [h])
  have xw : x≠w := fun h=>xx (by simp [h])
  have xe : x≠e := fun h=>xx (by simp [h])
  have xf : x≠f := fun h=>xx (by simp [h])
  have easy {B : Finset V} (sub : B⊆A) (out : e∉B) : CompleteOn G B := by
    intro u ub v vb uv
    apply near _ (sub ub) _ (sub vb) uv
    rintro (⟨rfl,_⟩|⟨_,rfl⟩)
    · exact out ub
    exact out vb
  have step (ea : e∈A) : G.Adj e x :=
    near e ea x xa xe.symm (fun h=>h.elim (fun q=>xf q.2) (fun q=>xe q.2))
  have left (ea : e∈A) {v : V} (va : v∈A) (ve : v≠e) (xv : x≠v) : RouteOn G A e v := by
    let B := A.erase e
    have cl : CompleteOn G B := easy (erase_subset e A) (by simp [B])
    obtain ⟨p,pp,ps⟩ := path_between_in_clique B cl
      (mem_erase.mpr ⟨xe,xa⟩) (mem_erase.mpr ⟨ve,va⟩) xv
    have path : RouteOn G B x v := ⟨p,pp,ps⟩
    have eq : insert e B=A := insert_erase ea
    exact eq ▸ path.prefix (step ea) (by simp [B])
  by_cases re : r=e
  · rw [re]
    exact left (re ▸ ra) wa (fun h=>rw' (re.trans h.symm)) xw
  by_cases we : w=e
  · rw [we]
    exact (left (we ▸ wa) ra re xr).reverse
  by_cases ea : e∈A
  · have general {u v : V} (ua : u∈A) (va : v∈A) (uv : u≠v)
        (ue : u≠e) (ve : v≠e) (uf : u≠f) (xu : x≠u) (xv : x≠v) :
        RouteOn G A u v := by
      let B := (A.erase u).erase e
      have sub : B⊆A := (erase_subset _ _).trans (erase_subset _ _)
      have c := easy sub (by simp [B])
      have xx : x∈B := mem_erase.mpr ⟨xe,mem_erase.mpr ⟨xu,xa⟩⟩
      have vv : v∈B := mem_erase.mpr ⟨ve,mem_erase.mpr ⟨uv.symm,va⟩⟩
      obtain ⟨p,pp,ps⟩ := path_between_in_clique B c xx vv xv
      have path : RouteOn G B x v := ⟨p,pp,ps⟩
      have de : e∈A.erase u := mem_erase.mpr ⟨ue.symm,ea⟩
      have eq : insert e B=A.erase u := insert_erase de
      have p' : RouteOn G (A.erase u) e v := eq ▸ path.prefix (step ea) (by simp [B])
      have adj : G.Adj u e := near u ua e ea ue (fun h=>h.elim (fun h=>ue h.1) (fun h=>uf h.1))
      exact insert_erase ua ▸ p'.prefix adj (by simp)
    by_cases rf : r=f
    · have wf : w≠f := fun e=>rw' (rf.trans e.symm)
      exact (general wa ra rw'.symm we re wf xw xr).reverse
    exact general ra wa rw' re we rf xr xw
  obtain ⟨p,pp,ps⟩ := path_between_in_clique A (easy (Subset.rfl) ea) ra wa rw'
  exact ⟨p,pp,ps⟩

#print axioms route_between_in_clique_except_pair
end Graffiti189LongestPath.CrossSaturation
