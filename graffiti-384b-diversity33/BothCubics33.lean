import SupportedEar33

namespace Graffiti384b.ForcedCubics
open Finset SimpleGraph EarAnchor HighEar EarOnClique33 CliquePivot33 RootCut
open private CliquePivot33.full_cubic from CliquePivot33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- For every possible set of credits, tightness forces both cubic scores
outside the credited set. Additional edges outside triangles are allowed. -/
theorem both_required {e a c : V} (n : Fintype.card V=32) (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {C R : Finset V} (cl : H.IsNClique 5 C) (hi : 16≤gamma H)
    (tight : Tight H R) : Available H R := by
  classical
  apply Classical.byContradiction; intro lack
  have apart := (scarce_cliques H lack de ac.ne ea ec pos inj tight cl).1
  have thin : additional H e a c=∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro w m
    obtain ⟨we,aw,cw⟩ := (additional_mem H).mp m
    exact lack (shared_requires_both H de ea ec ac aw cw we pos inj tight cl)
  by_cases other : ∃ u,u∉R ∧ H.degree u=3
  · obtain ⟨u,ur,du⟩ := other
    have uniq {v : V} (vr : v∉R) (dv : H.degree v=3) : v=u := by
      rcases cubic_scores H de dv pos inj with s|s <;> rcases cubic_scores H de du pos inj with t|t
      · exact inj (s.trans t.symm)
      · exact (lack ⟨v,u,dv,s,vr,du,t,ur⟩).elim
      · exact (lack ⟨u,v,du,t,ur,dv,s,vr⟩).elim
      · exact inj (s.trans t.symm)
    let N := H.neighborFinset u
    let M := C\N
    have safe : ∀ x∈M,Safe H R x := by
      intro x xm v dv vr edge
      have vu := uniq vr dv
      subst v
      exact (mem_sdiff.mp xm).2 ((H.mem_neighborFinset _ _).mpr edge)
    have ns : N.card=3 := (card_neighborFinset_eq_degree ..).trans du
    have rem : M.card+(C∩N).card=5 := (card_sdiff_add_card_inter C N).trans cl.2
    have cap : (C∩N).card≤N.card := card_le_card inter_subset_right
    have ms : 2≤M.card := by omega
    obtain ⟨an,cn,sz,contacts⟩ := palette H de ea ec ac thin pos inj tight cl apart
      (show M⊆C from sdiff_subset) safe ms
    have f : C.filter (H.Adj u)=C∩N := by ext w; simp [N]
    have many : 3≤nbr H u C := by change 3≤(C.filter (H.Adj u)).card; rw [f]; omega
    have nc := (CliquePivot33.full_cubic H cl du many).1
    obtain ⟨da,dc⟩ := EarPalette.extremal_endpoints H n de ea ec ac pos inj ⟨C,cl⟩ hi
    have au : a≠u := by intro eq; subst a; omega
    have cu : c≠u := by intro eq; subst c; omega
    have ⟨sa,sc⟩ := supported_endpoints H n de ea ec ac pos inj cl hi
    have capA := supported_degree H e pos a
    have capC := supported_degree H e pos c
    have ascore : trianglesAt H a≠2 := by omega
    have cscore : trianglesAt H c≠2 := by omega
    obtain ⟨p,pm,q,qm,_,ap,cq⟩ := (contacts.resolve_left ascore).resolve_left cscore
    obtain ⟨v,vu,vr,dv⟩ := contact_frame H de du ea ec ac.ne au cu pos inj tight cl an cn nc pm qm ap cq
    exact vu (uniq vr dv)
  · have safe : ∀ x∈C,Safe H R x := by
      intro x xm v dv vr _
      exact other ⟨v,vr,dv⟩
    have h := (palette H de ea ec ac thin pos inj tight cl apart (Subset.rfl : C⊆C) safe
      (by rw [cl.2]; decide)).2.2.1
    rw [cl.2] at h
    contradiction

end Graffiti384b.ForcedCubics
#print axioms Graffiti384b.ForcedCubics.both_required
