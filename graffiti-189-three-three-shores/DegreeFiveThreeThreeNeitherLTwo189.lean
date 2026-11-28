import DegreeFiveActualCut189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem cap_insert_pair {S L T : Finset V} {p q : V}
    (s : S=insert p (insert q (L∪T))) :
    S.card≤2+L.card+T.card := by
  rw [s]
  have h := card_insert_le p (insert q (L∪T))
  have k := card_insert_le q (L∪T)
  have n := card_union_le L T
  omega

theorem nonport_lt_five_of_shore_small {S : Finset V} {x : V}
    (xs : x∈S) (sub : G.neighborFinset x⊆S.erase x) (cap : S.card≤5) :
    ¬5≤G.degree x := by
  have h := card_le_card sub
  rw [card_neighborFinset_eq_degree,card_erase_of_mem xs] at h
  omega

theorem three_three_two_visible_local_impossible
    {S L T T₃ T₄ : Finset V} {p q f b u : V}
    (shape : S=insert p (insert q (L∪T)))
    (L2 : L.card=2) (atThree : T₃.card≤2)
    (fS : f∈S) (fNonportCut : G.neighborFinset f⊆insert b (S.erase f))
    (uL : u∈L) (uf : u≠f) (uNonport : G.neighborFinset u⊆S.erase u)
    (dis : Disjoint L T) (sub₃ : T₃⊆T)
    (d₃ : ∀ x∈T₃,
      G.neighborFinset x⊆
        (L∪T₃.erase x∪T₄) ∪ (if x=f then ({b} : Finset V) else ∅))
    (first : T.Nonempty → T₃.Nonempty)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (case₄ : (T=T₃ ∧ T₄=∅) ∨ (T₄.card≤1 ∧ ∀ x∈S,5≤G.degree x)) :
    False := by
  classical
  have uS : u∈S := by rw [shape]; exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ uL))
  have tS (x : V) (xt : x∈T) : x∈S := by
    rw [shape]
    exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ xt))
  have hS := cap_insert_pair shape
  have bound (x : V) (x₃ : x∈T₃) :
      G.degree x≤L.card+(T₃.card-1)+T₄.card+(if x=f then 1 else 0) := by
    have n := card_le_card (d₃ x x₃)
    rw [card_neighborFinset_eq_degree] at n
    have c₁ := card_union_le L (T₃.erase x)
    have c₂ := card_union_le (L∪T₃.erase x) T₄
    have c₃ := card_union_le (L∪T₃.erase x∪T₄) (if x=f then ({b} : Finset V) else ∅)
    rw [card_erase_of_mem x₃] at c₁
    by_cases e : x=f
    · rw [if_pos e] at c₃ n ⊢
      rw [card_singleton] at c₃
      omega
    rw [if_neg e] at c₃ n ⊢
    rw [card_empty] at c₃
    omega
  rcases case₄ with ⟨eq,h₄⟩|⟨cap,high⟩
  · have low (x : V) (xt : x∈T) : ¬5≤G.degree x := by
      have m : x∈T₃ := eq ▸ xt
      have n := bound x m
      rw [h₄,card_empty] at n
      split at n <;> omega
    have t1 : T.card≤1 := by
      apply Classical.byContradiction
      intro n
      obtain ⟨x,xt,y,yt,xy⟩ := one_lt_card.mp (by omega : 1<T.card)
      exact (degree x y xy).elim (low x xt) (low y yt)
    have uLow := nonport_lt_five_of_shore_small uS uNonport (by omega)
    by_cases non : T.Nonempty
    · obtain ⟨x,xt⟩ := non
      have ux : u≠x := fun e=>disjoint_left.mp dis uL (e.symm ▸ xt)
      exact (degree u x ux).elim uLow (low x xt)
    have t0 : T.card=0 := card_eq_zero.mpr
      (Finset.eq_empty_iff_forall_not_mem.mpr (fun x hx=>non ⟨x,hx⟩))
    have fLow : ¬5≤G.degree f := by
      have m := (card_le_card fNonportCut).trans (card_insert_le b (S.erase f))
      rw [card_neighborFinset_eq_degree,card_erase_of_mem fS] at m
      omega
    exact (degree u f uf).elim uLow fLow
  · have all (x : V) (xt : x∈T₃) : x=f := by
      apply Classical.byContradiction
      intro ne
      have n := bound x xt
      have h := high x (tS x (sub₃ xt))
      rw [if_neg ne] at n
      omega
    have noFirst : ¬T₃.Nonempty := by
      rintro ⟨x,xt⟩
      have e := all x xt
      have fx : f∈T₃ := e ▸ xt
      have sub : T₃⊆{f} := fun y yt=>mem_singleton.mpr (all y yt)
      have c := card_le_card sub
      rw [card_singleton] at c
      have n := bound f fx
      rw [if_pos rfl] at n
      have h := high f fS
      omega
    have t0 : T.card=0 := card_eq_zero.mpr
      (Finset.eq_empty_iff_forall_not_mem.mpr (fun x hx=>noFirst (first ⟨x,hx⟩)))
    exact nonport_lt_five_of_shore_small uS uNonport (by omega) (high u uS)

#print axioms three_three_two_visible_local_impossible
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
