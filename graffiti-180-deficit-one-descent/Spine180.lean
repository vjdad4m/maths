import CutChain180

set_option warningAsError true
namespace Minimal180.DescentOne
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Shortest-path properties of the disagreement set in the previous cut reduction. -/
structure Spine (J : SimpleGraph V) (r : V) (D : Finset V) (t : V) : Prop where
  root : r∉D
  tip : t∈D
  minimum : ∀ i∈D, J.dist t r≤J.dist i r
  single : ∀ i∈D, ∀ j∈D, J.dist i r=J.dist j r → i=j
  prior : ∀ i∈D, i≠t → ∃ q∈D, Arc J r q i
  onward : ∀ v∈D, ∀ i j, J.Adj v i → J.Adj v j → J.dist i r=J.dist v r+1 → J.dist j r=J.dist v r+1 → i=j
  other : (D.erase t).Nonempty

theorem failed_spine {J : SimpleGraph V} {S T : Finset V} {x y w : V}
    {r : ↥S} {odd : Bool} {A : Finset V} (h : TightCut J S T x y w r odd A)
    (one : bipartiteNum J+1=Fintype.card V) :
    let G := J⊔edge x y
    let P := parity G r.val odd
    let D := (A∪P)\(A∩P)
    let U := eligible A P r.val
    ¬weightedLeaves J U<weightedLeaves G U →
      U=A∪P ∧ w∉A∪P ∧ ∃ t∈({x,y}:Finset V), t∈P ∧ J.Adj t w ∧ Spine J r.val D t := by
  classical
  intro G P D U ng
  obtain ⟨rt,_,_⟩ := h.defect_one_entry one ng
  change r.val∉D at rt
  obtain ⟨nw,xp,yp,miss,_⟩ := h.defect_one_support one ng
  obtain ⟨_,t,ends,td,low,single,pred⟩ := h.defect_one_chain one ng
  have cover : U=A∪P := by
    ext i
    constructor
    · intro v
      exact mem_union.mpr (eligible_iff.mp v).1
    · intro v
      apply eligible_iff.mpr
      refine ⟨mem_union.mp v,?_⟩
      by_cases ir : i=r.val
      · subst i
        exact Or.inr (mem_inter.mp (Classical.byContradiction (fun no => rt (mem_sdiff.mpr ⟨v,no⟩))))
      · exact Or.inl ir
  have which : t=x ∨ t=y := by simpa only [mem_insert,mem_singleton] using ends
  have tp : t∈P := which.elim (fun e => e ▸ xp) (fun e => e ▸ yp)
  have tw : J.Adj t w := which.elim (fun e => e ▸ h.leftSpoke) (fun e => e ▸ h.rightSpoke.symm)
  refine ⟨cover,nw,t,ends,tp,tw,rt,td,low,single,pred,?_,?_⟩
  · intro v vd i j vi vj di dj
    have vr : v≠r.val := fun e => rt (show r.val∈D from e ▸ vd)
    exact h.outward_unique one (fun e => miss e.le) (mem_sdiff.mp vd).1 vr vi vj di dj
  · obtain ⟨v,va,vp⟩ := Finset.not_subset.mp miss
    exact ⟨v,mem_erase.mpr ⟨fun e => vp (e ▸ tp),mem_sdiff.mpr ⟨mem_union_left _ va,fun e => vp (mem_inter.mp e).2⟩⟩⟩

namespace Spine
variable {J : SimpleGraph V} {r t : V} {D : Finset V} (h : Spine J r D t)
include h
omit [Fintype V] in
theorem first_step : ∃ s∈D, Arc J r t s := by
  classical
  obtain ⟨s,se,low⟩ := exists_min_image (D.erase t) (fun a => J.dist a r) h.other
  obtain ⟨st,sd⟩ := mem_erase.mp se
  obtain ⟨p,pd,ps⟩ := h.prior s sd st
  have pt : p=t := by
    by_contra no
    have a := low p (mem_erase.mpr ⟨no,pd⟩)
    have b := ps.2.1
    omega
  exact ⟨s,sd,pt ▸ ps⟩

omit [Fintype V] in
theorem last_step : ∃ v∈D, v≠t ∧ ∀ i∈D,J.dist i r≤J.dist v r := by
  classical
  obtain ⟨v,vd,last⟩ := exists_max_image D (fun a => J.dist a r) ⟨t,h.tip⟩
  refine ⟨v,vd,?_,last⟩
  intro vt
  obtain ⟨s,sd,ts⟩ := h.first_step
  have cap := last s sd
  have step := ts.2.1
  rw [vt] at cap
  omega

end Spine
#print axioms failed_spine
#print axioms Spine.first_step
end Minimal180.DescentOne
