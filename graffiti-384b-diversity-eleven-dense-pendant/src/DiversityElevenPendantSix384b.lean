import DiversityElevenSixTriangleRange384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open private Repair.nbr_add from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Reduce the eight-vertex pendant board to six, by keeping (p) and
omitting (q) with two already-known retained neighbors. The constraints
on the six-vertex board distinguish zero and one fixed support. -/
theorem exact_of_pendant_six (select : SixSelector)
    (t : (types G).card=11) (nine : (high G).card=9)
    {e f a p q : V} (ea : G.Adj e a) (ef : G.Adj e f) (ah : a∈high G)
    (el : e∉high G) (fl : f∉high G)
    (ph : p∈(high G).erase a) (qh : q∈(high G).erase a)
    (qa : G.Adj q a) (qp : G.Adj q p)
    (scores : Set.InjOn (trianglesAt G) (high G : Set V))
    (mins : ∀ v∈high G, 2≤trianglesAt G v)
    (h0 : let U := (((high G).erase a).erase p).erase q
      ∀ v∈U, ¬G.Adj v a → ¬G.Adj v p →
        3≤nbr G v U ∧
        ∀ x y, G.Adj v x → G.Adj v y → G.Adj x y → x∈U ∧ y∈U)
    (h1 : let U := (((high G).erase a).erase p).erase q
      ∀ v∈U, ((G.Adj v a ∧ ¬G.Adj v p) ∨ (G.Adj v p ∧ ¬G.Adj v a)) →
        2≤nbr G v U) : gamma G≤bound G := by
  classical
  let B := (high G).erase a
  let U := (B.erase p).erase q
  let Z := U.filter (fun v => ¬G.Adj v a ∧ ¬G.Adj v p)
  have qB : q∈B.erase p := mem_erase.mpr ⟨qp.ne,qh⟩
  have size : U.card=6 := by dsimp [U,B]; rw [card_erase_of_mem qB,card_erase_of_mem ph,card_erase_of_mem ah,nine]
  have uh (v : V) (vm : v∈U) : v∈high G :=
    (mem_erase.mp (mem_erase.mp (mem_erase.mp vm).2).2).2
  have tag (v : V) (vm : v∈Z) : v∈U ∧ ¬G.Adj v a ∧ ¬G.Adj v p := mem_filter.mp vm
  obtain ⟨b,bU,c,cU,bc,ret⟩ := six_pair_of_triangle_closed G select size
    (fun v vm => (h0 v (tag v vm).1 (tag v vm).2.1 (tag v vm).2.2).1)
    (fun v vm => mins v (uh v (tag v vm).1))
    (fun x xm y ym he => scores (uh x (tag x xm).1) (uh y (tag y ym).1) he)
    (fun v vm => (h0 v (tag v vm).1 (tag v vm).2.1 (tag v vm).2.2).2)
  let K : Finset V := {p,b,c}
  have kp : p∉({b,c}:Finset V) := by
    intro hp
    simp only [mem_insert,mem_singleton] at hp
    exact hp.elim (Ne.symm ((mem_erase.mp (mem_erase.mp bU).2).1))
      (Ne.symm ((mem_erase.mp (mem_erase.mp cU).2).1))
  have kd : Disjoint ({b,c}:Finset V) {p} :=
    disjoint_left.mpr (fun z zb zp => kp ((mem_singleton.mp zp) ▸ zb))
  have ke : ({b,c}:Finset V)∪{p}=K := by rw [union_comm,←insert_eq]
  have kin : K⊆B := by
    intro v vm
    simp only [K,mem_insert,mem_singleton] at vm
    rcases vm with rfl|rfl|rfl
    · exact ph
    · exact (mem_erase.mp (mem_erase.mp bU).2).2
    · exact (mem_erase.mp (mem_erase.mp cU).2).2
  have kcard : K.card=3 := by dsimp [K]; rw [card_insert_of_not_mem kp,card_pair bc]
  apply exact_of_pendant_triple G t nine ea ef ah el fl kin kcard
  intro v vm
  obtain ⟨vB,vK⟩ := mem_sdiff.mp vm
  have vp : v≠p := fun eq => vK (eq ▸ mem_insert_self ..)
  have vb : v≠b := fun eq => vK (eq ▸ mem_insert_of_mem (mem_insert_self ..))
  have vc : v≠c := fun eq => vK (eq ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
  have kc : nbr G v K=nbr G v {b,c}+(if G.Adj v p then 1 else 0) := by
    rw [←ke,Repair.nbr_add G v kd]
    unfold nbr
    rw [filter_singleton]
    split <;> simp
  rw [kc]
  by_cases vq : v=q
  · subst v
    simp [qa,qp]
  have vU : v∈U := mem_erase.mpr ⟨vq,mem_erase.mpr ⟨vp,vB⟩⟩
  have both (h : G.Adj v b ∧ G.Adj v c) : 2≤nbr G v {b,c} := by
    unfold nbr
    have ff : ({b,c}:Finset V).filter (G.Adj v)={b,c} := by
      apply filter_eq_self.mpr
      intro z zm
      simp only [mem_insert,mem_singleton] at zm
      rcases zm with rfl|rfl
      · exact h.1
      · exact h.2
    rw [ff,card_pair bc]
  have one (h : G.Adj v b ∨ G.Adj v c) : 1≤nbr G v {b,c} := by
    apply card_pos.mpr
    rcases h with h|h
    · exact ⟨b,mem_filter.mpr ⟨mem_insert_self ..,h⟩⟩
    · exact ⟨c,mem_filter.mpr ⟨mem_insert_of_mem (mem_singleton_self _),h⟩⟩
  have r := ret v vU vb vc
  by_cases va : G.Adj v a <;> by_cases vP : G.Adj v p
  · simp [va,vP]
  · have n := one (r.2 (fun hz => (tag v hz).2.1 va) (h1 v vU (Or.inl ⟨va,vP⟩)))
    simp [va,vP]; omega
  · have n := one (r.2 (fun hz => (tag v hz).2.2 vP) (h1 v vU (Or.inr ⟨vP,va⟩)))
    simp [va,vP]; omega
  · exact by simpa [va,vP] using both (r.1 (mem_filter.mpr ⟨vU,va,vP⟩))

#print axioms exact_of_pendant_six
end Graffiti384b.DiversityEleven
