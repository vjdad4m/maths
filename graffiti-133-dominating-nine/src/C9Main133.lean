import C9GraphLift133
import C9MaskClassification133
import C9TokenTransfer133
import FinalEight133

namespace Graffiti133C9
open SimpleGraph Graffiti133 Graffiti133NoFive Graffiti133Camby
open scoped BigOperators
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem dominating_nine_budget (H : Hole G 9) (h4 : FourCycleFree G)
    (h9 : NoPath G 9)
    (dom : ∀ x, Outside H.c x → ∃ i, G.Adj x (H.c i)) :
    (∑ x, localIndependence G x) ≤ 4 * Fintype.card V := by
  apply graph_budget H h4 profileContacts profile_at_least_two
    (fun x hx => by
      obtain ⟨i,hi⟩ := classify_profile H h4 h9 x hx (dom x hx)
      exact ⟨i,hx,hi⟩)
    profileOK profileEdge
  · intro x y i j ne hx hy ij
    exact (classify_pair H h4 h9 pairTests hx.1 hy.1 ne ij.ne hx.2 hy.2).1
  · intro x y i j e hx hy ij
    exact (classify_pair H h4 h9 pairTests hx.1 hy.1 e.ne ij.ne hx.2 hy.2).2 e
  · exact budget_direct

theorem dominating_nine_average (H : Hole G 9) (h4 : FourCycleFree G)
    (h9 : NoPath G 9)
    (dom : ∀ x, Outside H.c x → ∃ i, G.Adj x (H.c i)) :
    averageLocal G ≤ 4 := by
  have bd := dominating_nine_budget H h4 h9 dom
  haveI : Nonempty V := ⟨H.c 0⟩
  have hn : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  unfold averageLocal
  apply (div_le_iff₀ hn).2
  exact_mod_cast bd

theorem dominating_P7free_of_mean_gt_four (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G) (h9 : NoPath G 9) (avg : 4 < averageLocal G) :
    ∃ D, CD G D ∧ NoPathIn G D 7 := by
  classical
  rcases connected_domination_decomposition G hc 7 (by decide) h9 with h|⟨H,dom⟩
  · exact h
  · exact (not_lt_of_ge (dominating_nine_average H h4 h9 dom) avg).elim

theorem radius_four_real_five_with_dominating_nine (hc : G.Connected) (h4 : FourCycleFree G)
    (hr : radius G=4) (ha : averageLocal G≤5)
    (H : Hole G 9) (dom : ∀ x, Outside H.c x → ∃ i, G.Adj x (H.c i)) :
    ∃ k : Nat, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h9 : NoPath G 9
  · exact Graffiti133FinalEight.conjecture133_full_real_four G hc (dominating_nine_average H h4 h9 dom)
  · obtain ⟨f,hf⟩ := Classical.not_not.mp h9
    refine ⟨9,?_,f,hf⟩
    simp only [rhs133, if_pos h4, pow_one, hr]
    change (4 : ℚ)+averageLocal G≤9
    exact (add_le_add_left ha 4).trans (by norm_num)

theorem dominating_nine_P9_of_mean_gt_four (H : Hole G 9) (h4 : FourCycleFree G)
    (avg : 4 < averageLocal G) (dom : ∀ x, Outside H.c x → ∃ i, G.Adj x (H.c i)) :
    ∃ f : Fin 9 → V, InducedPath G f := by
  classical
  by_contra no
  exact (not_lt_of_ge (dominating_nine_average H h4 no dom)) avg

theorem radius_four_floor_five_with_dominating_nine (hc : G.Connected) (h4 : FourCycleFree G)
    (hr : radius G≤4) (ha : ⌊averageLocal G⌋≤5)
    (H : Hole G 9) (dom : ∀ x, Outside H.c x → ∃ i, G.Adj x (H.c i)) :
    ∃ k : Nat, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h9 : NoPath G 9
  · apply Graffiti133FinalEight.conjecture133_full_floor_four G hc
    have q := dominating_nine_average H h4 h9 dom
    have ht : (⌊averageLocal G⌋ : ℚ) ≤ (4 : ℚ) := (Int.floor_le _).trans q
    exact_mod_cast ht
  · obtain ⟨f,hf⟩ := Classical.not_not.mp h9
    refine ⟨9,?_,f,hf⟩
    simp only [catalogueRhs133,if_pos h4,pow_one]
    omega

#print axioms dominating_nine_P9_of_mean_gt_four
#print axioms radius_four_floor_five_with_dominating_nine
#print axioms dominating_P7free_of_mean_gt_four
#print axioms radius_four_real_five_with_dominating_nine
end Graffiti133C9
