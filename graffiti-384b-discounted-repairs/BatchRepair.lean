import Proof384b

namespace Graffiti384b
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An entire batch of deficient vertices can be skipped if each has
enough support among the original sample and the retained repairs. -/
theorem batch_repair_saves (s K : Finset V)
    (sub : K ⊆ univ.filter (fun v => v ∉ s ∧ nbr G v s < 2))
    (supports : ∀ x ∈ K, 2 ≤ nbr G x s +
      nbr G x ((univ.filter (fun v => v ∉ s ∧ nbr G v s < 2)) \ K)) :
    gamma G ≤ s.card + (univ.filter (fun v => v ∉ s ∧ nbr G v s < 2)).card - K.card := by
  classical
  let B := univ.filter (fun v => v ∉ s ∧ nbr G v s < 2)
  let R := B \ K
  have dis : Disjoint s R := disjoint_left.mpr fun x xs xr =>
    (mem_filter.mp (mem_sdiff.mp xr).1).2.1 xs
  have hw : TwoDominates G (s ∪ R) := by
    intro x notin
    have xs : x ∉ s := fun h => notin (mem_union_left _ h)
    by_cases hK : x ∈ K
    · have dd : Disjoint (s.filter (G.Adj x)) (R.filter (G.Adj x)) :=
        disjoint_left.mpr (fun v vs vr =>
          (disjoint_left.mp dis) (mem_filter.mp vs).1 (mem_filter.mp vr).1)
      change 2 ≤ ((s ∪ R).filter (G.Adj x)).card
      rw [filter_union, card_union_of_disjoint dd]
      exact supports x hK
    · have enough : 2 ≤ nbr G x s := by
        by_contra! small
        exact notin (mem_union_right _ (show x ∈ R from
          mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, xs, small⟩, hK⟩))
      exact enough.trans (card_le_card (filter_subset_filter _ subset_union_left))
  have g : gamma G ≤ (s ∪ R).card := Nat.sInf_le ⟨s ∪ R, hw, rfl⟩
  have rr : R.card + K.card = B.card := card_sdiff_add_card_eq_card sub
  have rs : R.card = B.card - K.card := by omega
  have ks : K.card ≤ B.card := card_le_card sub
  rw [card_union_of_disjoint dis, rs] at g
  change gamma G ≤ s.card + B.card - K.card
  omega

#print axioms batch_repair_saves
end Graffiti384b
