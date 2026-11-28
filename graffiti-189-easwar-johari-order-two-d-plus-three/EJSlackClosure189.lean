import EJGateBoth189

namespace Graffiti189Ore
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath.SmallOrder
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem endpoint_marks_cover_except {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (all : ∀ v,v∈p.support)
    (degree : p.length ≤ G.degree a+G.degree b+1)
    (no : ∀ i : ℕ, i < p.length → ¬(G.Adj a (p.getVert (i+1)) ∧ G.Adj b (p.getVert i)))
    {t : ℕ} (tl : t < p.length)
    (hole : ¬(G.Adj a (p.getVert (t+1)) ∨ G.Adj b (p.getVert t))) :
    ∀ i : ℕ, i < p.length → i≠t → G.Adj a (p.getVert (i+1)) ∨ G.Adj b (p.getVert i) := by
  classical
  let A := (range p.length).filter (fun i=>G.Adj a (p.getVert (i+1)))
  let B := (range p.length).filter (fun i=>G.Adj b (p.getVert i))
  have ⟨ca,cb⟩ := endpoint_mark_cards p hp all
  change A.card=G.degree a at ca
  change B.card=G.degree b at cb
  have d : Disjoint A B := disjoint_left.mpr (fun i ai bi=>
    no i (mem_range.mp (mem_filter.mp ai).1) ⟨(mem_filter.mp ai).2,(mem_filter.mp bi).2⟩)
  have sub : A∪B⊆(range p.length).erase t := by
    intro i hi
    have m := mem_union.mp hi
    apply mem_erase.mpr
    exact m.elim (fun h=>⟨fun e=>hole (.inl (e ▸ (mem_filter.mp h).2)),(mem_filter.mp h).1⟩)
      (fun h=>⟨fun e=>hole (.inr (e ▸ (mem_filter.mp h).2)),(mem_filter.mp h).1⟩)
  have eq := eq_of_subset_of_card_le sub (by
    rw [card_union_of_disjoint d,card_erase_of_mem (mem_range.mpr tl),card_range,ca,cb]
    omega)
  intro i il ne
  have m : i∈A∪B := eq.symm ▸ mem_erase.mpr ⟨ne,mem_range.mpr il⟩
  rcases mem_union.mp m with (ai : i∈A) | (bi : i∈B)
  · exact Or.inl ((mem_filter.mp ai).2)
  · exact Or.inr ((mem_filter.mp bi).2)

theorem traceable_of_open_slack (hc : G.Connected) (conn : DeletionTwoConnected G)
    {u v : V} (p : (cap G (fun _=>True)).Walk (some u) (some v)) (hp : p.IsPath)
    (all : ∀ v,v∈p.support)
    (ready : (Fintype.card V ≤ G.degree u+G.degree v+2 ∧ (CommonNeighbors G u v).card ≤ 1) ∨
      (Fintype.card V ≤ G.degree u+G.degree v+3 ∧ (CommonNeighbors G u v).card=0)) :
    Traceable G := by
  classical
  let K := cap G (fun _=>True)
  let A (i : ℕ) := K.Adj (some u) (p.getVert (i+1))
  let B (i : ℕ) := K.Adj (some v) (p.getVert i)
  by_cases overlap : ∃ i,i < p.length ∧ A i ∧ B i
  · obtain ⟨i,il,a,b⟩ := overlap
    exact cap_traceability_of_overlap hp all il a b
  have no (i : ℕ) (il : i < p.length) : ¬(A i ∧ B i) := fun e=>overlap ⟨i,il,e⟩
  have len : p.length=Fintype.card V := by
    have e : p.support.toFinset=univ := eq_univ_of_forall (fun z=>List.mem_toFinset.mpr (all z))
    have h := congrArg Finset.card e
    rw [List.toFinset_card_of_nodup hp.support_nodup,length_support,card_univ,Fintype.card_option] at h
    omega
  have du : K.degree (some u)=G.degree u+1 := degree_cap_universal G u
  have dv : K.degree (some v)=G.degree v+1 := degree_cap_universal G v
  let k := (p.takeUntil none (all none)).length
  have kp : 0 < k := by
    apply not_nil_iff_lt_length.mp
    intro h
    exact Option.some_ne_none _ (Walk.Nil.eq h)
  have kl : k < p.length := length_takeUntil_lt (all none) (by simp)
  have pivot : p.getVert k=none := by
    have e := getVert_takeUntil (all none) (show k ≤ (p.takeUntil none (all none)).length by rfl)
    simpa [k] using e.symm
  have first : A 0 := by
    have e := p.adj_getVert_succ (show 0 < p.length by omega)
    simpa only [A,Nat.zero_add,getVert_zero] using e
  have last : B (p.length-1) := by
    have e := p.adj_getVert_succ (show p.length-1 < p.length by omega)
    have add : p.length-1+1=p.length := by omega
    rw [add,getVert_length] at e
    exact e.symm
  have prev : A (k-1) := by
    change K.Adj (some u) (p.getVert (k-1+1))
    rw [show k-1+1=k by omega,pivot]
    simp [K,cap]
  have next : B k := by
    change K.Adj (some v) (p.getVert k)
    rw [pivot]
    simp [K,cap]
  have common (i : ℕ) (il : i+1 < p.length) (a : A i) (b : B (i+1)) (ne : i+1≠k) :
      ∃ w∈CommonNeighbors G u v,p.getVert (i+1)=some w := by
    change K.Adj (some u) (p.getVert (i+1)) at a
    change K.Adj (some v) (p.getVert (i+1)) at b
    cases e : p.getVert (i+1) with
    | none => exact (ne (hp.getVert_injOn (Nat.le_of_lt il) (Nat.le_of_lt kl) (e.trans pivot.symm))).elim
    | some w =>
      rw [e] at a b
      exact ⟨w,mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr a,(mem_neighborFinset _ _ _).mpr b⟩,rfl⟩
  have single (cover : ∀ i : ℕ, i < p.length → A i ∨ B i)
      (switch : ∀ i : ℕ, i+1 < p.length → A i → B (i+1) → i+1=k) : Traceable G := by
    obtain ⟨left,right⟩ := unique_switch_endpoint_marks p.length k ⟨kp,kl⟩
      A B cover no first last switch
    exact traceable_of_single_apex_switch hc p hp all left right
  rcases ready with ⟨sum,card⟩ | ⟨sum,card⟩
  · have size : p.length ≤ K.degree (some u) + K.degree (some v) := by omega
    have cover : ∀ i : ℕ, i < p.length → A i ∨ B i :=
      endpoint_marks_cover p hp all size no
    by_cases extra : ∃ i,i+1 < p.length ∧ A i ∧ B (i+1) ∧ i+1≠k
    · obtain ⟨j,jl,ja,jb,jk⟩ := extra
      obtain ⟨w,wm,we⟩ := common j jl ja jb jk
      apply traceable_of_mark_gate conn p hp all kp kl jl jk pivot
        (fun i il _=>cover i il) no
      refine .inl ⟨cover,?_,by omega⟩
      intro i il a b
      by_cases ik : i+1=k
      · exact .inl ik
      obtain ⟨z,zm,ze⟩ := common i il a b ik
      have eq := card_le_one.mp card z zm w wm
      have vw : (some z : Option V) = some w := congrArg Option.some eq
      exact .inr (hp.getVert_injOn (Nat.le_of_lt il) (Nat.le_of_lt jl) (ze.trans (vw.trans we.symm)))
    exact single cover (fun i il a b=>Classical.byContradiction (fun ne=>extra ⟨i,il,a,b,ne⟩))
  · have empty : CommonNeighbors G u v=∅ := card_eq_zero.mp card
    have switch (i : ℕ) (il : i+1 < p.length) (a : A i) (b : B (i+1)) : i+1=k := by
      by_contra ne
      obtain ⟨w,wm,_⟩ := common i il a b ne
      simp [empty] at wm
    by_cases absent : ∃ t,t < p.length ∧ ¬(A t ∨ B t)
    · obtain ⟨t,tl,hole⟩ := absent
      have size : p.length ≤ K.degree (some u) + K.degree (some v) + 1 := by omega
      have tk : t≠k := fun e=>hole (.inr (e.symm ▸ next))
      have tp : t+1≠k := fun e=>hole (.inl ((show k-1=t by omega) ▸ prev))
      exact traceable_of_mark_gate conn p hp all kp kl tl tk pivot
        (endpoint_marks_cover_except p hp all size no tl hole) no (.inr ⟨tp,switch⟩)
    exact single (fun i il=>Classical.byContradiction (fun ne=>absent ⟨i,il,ne⟩)) switch

end Graffiti189Ore

namespace Graffiti189LongestPath.SmallOrder
open Graffiti189Ore Graffiti189LongestPath
universe u

/-- Easwar–Johari Lemma 3.3, combined with ordinary Ore closure. -/
theorem safe_three_edge_closure_proven : SafeThreeEdgeClosure.{u} := by
  intro W fw eq J K dj dk hc conn x y xy no only ready ht
  rcases ready with ordinary | slack
  · exact traceable_closure_one only ordinary ht
  rcases traceable_or_open_one_edge only ht with out | ⟨p,hp,all⟩
  · exact out
  exact traceable_of_open_slack hc conn p hp all slack

theorem traceable_at_order_le_two_d_add_three {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hc : G.Connected) (conn : DeletionTwoConnected G)
    (d : ℕ) (cap : ∀ v,(EvenFrom G v).card ≤ d+1)
    (degree : ∀ u v : V,u≠v → d ≤ G.degree u ∨ d ≤ G.degree v)
    (bound : Fintype.card V ≤ 2*d+3) : Traceable G :=
  traceable_at_order_le_two_d_add_three_of_edge_closure safe_three_edge_closure_proven
    hc conn d cap degree bound

#print axioms safe_three_edge_closure_proven
#print axioms traceable_at_order_le_two_d_add_three
end Graffiti189LongestPath.SmallOrder
