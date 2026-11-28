import EJApexSections189

namespace Graffiti189Ore
open Finset SimpleGraph SimpleGraph.Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
set_option linter.unusedSectionVars false

/-- Easwar–Johari, Lemma 3.2 (arXiv:2609.11719v1): an added nonedge
with disjoint neighborhoods and degree sum at least order−2 is safe. -/
theorem traceable_disjoint_neighbor_one_edge (hc : G.Connected) {u v : V}
    (only : ∀ x y,H.Adj x y → G.Adj x y ∨ s(x,y)=s(u,v))
    (_uv : ¬G.Adj u v)
    (dis : ∀ w,¬(G.Adj u w ∧ G.Adj v w))
    (degree : Fintype.card V≤G.degree u+G.degree v+2)
    (ht : Traceable H) : Traceable G := by
  classical
  rcases traceable_or_open_one_edge only ht with out|⟨p,hp,all⟩
  · exact out
  let K := cap G (fun _=>True)
  let A (i : ℕ) := K.Adj (some u) (p.getVert (i+1))
  let B (i : ℕ) := K.Adj (some v) (p.getVert i)
  by_cases overlap : ∃ i,i<p.length ∧ A i ∧ B i
  · obtain ⟨i,il,a,b⟩ := overlap
    exact cap_traceability_of_overlap hp all il a b
  have no (i : ℕ) (il : i<p.length) : ¬(A i ∧ B i) := fun e=>overlap ⟨i,il,e⟩
  have len : p.length=Fintype.card V := by
    have e : p.support.toFinset=univ := eq_univ_of_forall (fun z=>List.mem_toFinset.mpr (all z))
    have h := congrArg Finset.card e
    rw [List.toFinset_card_of_nodup hp.support_nodup,length_support,card_univ,Fintype.card_option] at h
    omega
  have sum : p.length≤K.degree (some u)+K.degree (some v) := by
    change p.length≤(cap G (fun _=>True)).degree (some u)+(cap G (fun _=>True)).degree (some v)
    rw [degree_cap_universal,degree_cap_universal]
    omega
  have cover : ∀ i,i<p.length → A i ∨ B i :=
    endpoint_marks_cover p hp all sum no
  let k := (p.takeUntil none (all none)).length
  have kp : 0<k := by
    apply not_nil_iff_lt_length.mp
    intro h
    exact Option.some_ne_none _ (Walk.Nil.eq h)
  have kl : k<p.length := length_takeUntil_lt (all none) (by simp)
  have pivot : p.getVert k=none := by
    have e := getVert_takeUntil (all none) (show k≤(p.takeUntil none (all none)).length by rfl)
    simpa [k] using e.symm
  have first : A 0 := by
    have e := p.adj_getVert_succ (show 0<p.length by omega)
    simpa only [A,Nat.zero_add,getVert_zero] using e
  have last : B (p.length-1) := by
    have e := p.adj_getVert_succ (show p.length-1<p.length by omega)
    have add : p.length-1+1=p.length := by omega
    rw [add,getVert_length] at e
    exact e.symm
  have switch (i : ℕ) (il : i+1<p.length) (ai : A i) (bi : B (i+1)) : i+1=k := by
    have pivot' : p.getVert (i+1)=none := by
      change K.Adj (some u) (p.getVert (i+1)) at ai
      change K.Adj (some v) (p.getVert (i+1)) at bi
      generalize eq : p.getVert (i+1)=q at ai bi ⊢
      cases q with
      | none => rfl
      | some w => exact (dis w ⟨ai,bi⟩).elim
    exact hp.getVert_injOn (Nat.le_of_lt il) (Nat.le_of_lt kl) (pivot'.trans pivot.symm)
  obtain ⟨left,right⟩ := unique_switch_endpoint_marks p.length k ⟨kp,kl⟩
    A B cover no first last switch
  exact traceable_of_single_apex_switch hc p hp all left right

#print axioms traceable_disjoint_neighbor_one_edge
end Graffiti189Ore
