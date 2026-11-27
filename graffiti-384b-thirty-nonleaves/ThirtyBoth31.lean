import ThirtyTransversal31
namespace Graffiti384b.ThirtyCore
open Finset SimpleGraph PositiveCore33 HighEar EarAnchor EarOnClique33 CliquePivot33 RootCut
open private OneEar.deg2 from OneEarFinish384b
open private PositiveCore33.gamma_mono from LeafReduction33
open private CliquePivot33.full_cubic from CliquePivot33
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- When the ear is the only common neighbor of its endpoints, each endpoint
has at least five neighbors on triangle edges at any half-tight order. -/
theorem thin_supported {e a c : V} (thin : additional G e a c=∅) (de : G.degree e=2)
    (ea : G.Adj e a) (ec : G.Adj e c) (ac : G.Adj a c)
    (pos : ∀ v,0<trianglesAt G v) (inj : Function.Injective (trianglesAt G))
    {C : Finset V} (cl : G.IsNClique 5 C) (half : Fintype.card V≤2*gamma G) :
    5≤(backbone G e).degree a ∧ 5≤(backbone G e).degree c := by
  classical
  let J := backbone G e
  have le : J≤G := fun _ _ h => ((backbone_adj G).mp h).1
  have jc : J.IsNClique 5 C := by
    refine ⟨?_,cl.2⟩
    intro u um v vm ne
    obtain ⟨w,wm,wu⟩ := exists_ne_of_one_lt_card (by rw [card_erase_of_mem vm,cl.2]; decide : 1<(C.erase v).card) u
    obtain ⟨wv,wc⟩ := mem_erase.mp wm
    exact (backbone_adj G).mpr ⟨cl.1 um vm ne,w,cl.1 um wc wu.symm,cl.1 vm wc wv.symm⟩
  have ja : J.Adj e a := (backbone_adj G).mpr ⟨ea,c,ec,ac⟩
  have jb : J.Adj e c := (backbone_adj G).mpr ⟨ec,a,ea,ac.symm⟩
  have ab : J.Adj a c := (backbone_adj G).mpr ⟨ac,e,ea.symm,ec.symm⟩
  have sub : J.neighborFinset e⊆G.neighborFinset e := fun w wm =>
    (G.mem_neighborFinset _ _).mpr (le ((J.mem_neighborFinset _ _).mp wm))
  have cap := card_le_card sub
  rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,de] at cap
  have low := OneEar.deg2 J ac.ne ja jb
  have dj : J.degree e=2 := by omega
  have pj (u : V) : 0<trianglesAt J u := (backbone_scores G e u) ▸ pos u
  have ij : Function.Injective (trianglesAt J) := fun u v eq =>
    inj ((backbone_scores G e u).symm.trans (eq.trans (backbone_scores G e v)))
  have tj : additional J e a c=∅ := eq_empty_iff_forall_not_mem.mpr (by
    intro w wm
    obtain ⟨we,aw,cw⟩ := (additional_mem J).mp wm
    have m := (additional_mem G).mpr ⟨we,le aw,le cw⟩
    rw [thin] at m
    exact Finset.not_mem_empty _ m)
  have larger := PositiveCore33.gamma_mono G J le
  exact HighEar.endpoint_profile J dj ja jb ab pj ij (by omega) ⟨C,jc⟩ (by simp [tj])

variable (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Every half-tight positive graph with distinct triangle counts, an ear
and a five-clique requires both cubic scores outside the credited set. -/
theorem both_required {e a c : V} (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {C R : Finset V} (cl : H.IsNClique 5 C) (half : Fintype.card V≤2*gamma H)
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
    obtain ⟨da,dc⟩ := CubicShore.endpoints H de ea ec ac pos inj half ⟨C,cl⟩
    have au : a≠u := by intro eq; subst a; omega
    have cu : c≠u := by intro eq; subst c; omega
    have ⟨sa,sc⟩ := thin_supported H thin de ea ec ac pos inj cl half
    have capA := ForcedCubics.supported_degree H e pos a
    have capC := ForcedCubics.supported_degree H e pos c
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

end Graffiti384b.ThirtyCore
#print axioms Graffiti384b.ThirtyCore.thin_supported
#print axioms Graffiti384b.ThirtyCore.both_required
