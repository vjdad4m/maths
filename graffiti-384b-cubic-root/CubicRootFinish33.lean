import PrivateFrame33

namespace Graffiti384b.RootCut
open Finset SimpleGraph EarAnchor HighEar EarOnClique33 CliquePivot33 EarExchange33
open private EarOnClique33.scarce_at_root from EarOnClique33
open private HighEar.unique_other from HighEarShared33
open private CliquePivot33.full_cubic from CliquePivot33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- A cubic attachment root always saves a vertex in the relaxed problem
on an extremal positive core with injective triangle counts. -/
theorem cubic_root {r e a c : V} (dr : H.degree r=3) (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (half : Fintype.card V≤2*gamma H) {C : Finset V} (cl : H.IsNClique 5 C) : ¬Tight H {r} := by
  classical
  intro tight
  have lack := EarOnClique33.scarce_at_root H dr de pos inj
  have apart := (scarce_cliques H lack de ac.ne ea ec pos inj tight cl).1
  have thin : additional H e a c=∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro w m
    obtain ⟨we,aw,cw⟩ := (additional_mem H).mp m
    exact lack (shared_requires_both H de ea ec ac aw cw we pos inj tight cl)
  by_cases other : ∃ u,u≠r ∧ H.degree u=3
  · obtain ⟨u,ur,du⟩ := other
    have uniq {v : V} (vr : v∉({r}:Finset V)) (dv : H.degree v=3) : v=u :=
      HighEar.unique_other H de dr pos inj (fun eq => vr (mem_singleton.mpr eq)) ur dv du
    let N := H.neighborFinset u
    let M := C\N
    have safe : ∀ x∈M,Safe H {r} x := by
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
    obtain ⟨nc,us⟩ := CliquePivot33.full_cubic H cl du many
    have rs : trianglesAt H r=2 := (cubic_scores H de dr pos inj).resolve_right
      (fun h => ur (inj (us.trans h.symm)))
    obtain ⟨da,dc⟩ := CubicShore.endpoints H de ea ec ac pos inj half ⟨C,cl⟩
    have high {v : V} (d : 4≤H.degree v) : v≠u ∧ trianglesAt H v≠2 := by
      refine ⟨fun h => by subst v; omega,?_⟩
      intro eq
      have same := inj (eq.trans rs.symm)
      subst v; omega
    obtain ⟨au,ascore⟩ := high da
    obtain ⟨cu,cscore⟩ := high dc
    obtain ⟨p,pm,q,qm,_,ap,cq⟩ := (contacts.resolve_left ascore).resolve_left cscore
    obtain ⟨v,vu,vr,dv⟩ := contact_frame H de du ea ec ac.ne au cu pos inj tight cl an cn nc pm qm ap cq
    exact vu (uniq vr dv)
  · have safe : ∀ x∈C,Safe H {r} x := by
      intro x xm v dv vr _
      exact other ⟨v,fun eq => vr (mem_singleton.mpr eq),dv⟩
    have h := (palette H de ea ec ac thin pos inj tight cl apart (Subset.rfl : C⊆C) safe
      (by rw [cl.2]; decide)).2.2.1
    rw [cl.2] at h
    contradiction

/-- Exact value after reattaching the leaf in the diversity-33 cubic-root case. -/
theorem attachment_value (n : Fintype.card V=33) (t : (types H).card=33) {z b : V}
    (leaf : H.neighborFinset z={b}) :
    let P := ({z} : Finset V)ᶜ
    let G := H.induce (P : Set V)
    ∀ r e a c : P,r.val=b → G.degree r=3 → G.degree e=2 → G.Adj e a → G.Adj e c →
      G.Adj a c → (∀ v,0<trianglesAt G v) → Function.Injective (trianglesAt G) →
      gamma G=16 → (∃ C,G.IsNClique 5 C) → gamma H=16 := by
  let P := ({z} : Finset V)ᶜ
  let G := H.induce (P : Set V)
  change ∀ r e a c : P,_
  intro r e a c rb dr de ea ec ac pos inj g five
  obtain ⟨C,cl⟩ := five
  have ord : Fintype.card P=32 := by rw [Fintype.card_coe]; simp [P,card_compl,n]
  have half : 2*gamma G=Fintype.card P := by change gamma G=16 at g; omega
  have sol := (exchange_iff G r half).mp (cubic_root G dr de ea ec ac pos inj half.ge cl)
  have up := (EarRoot33.attachment_iff H n t leaf r rb g).mpr sol
  change gamma G=16 at g
  have lo : gamma G≤gamma H := EarAnchorFinish.leaf_lower H leaf
  have cap : bound H=16 := by unfold bound; rw [t,n]
  omega

end Graffiti384b.RootCut
#print axioms Graffiti384b.RootCut.cubic_root
#print axioms Graffiti384b.RootCut.attachment_value
