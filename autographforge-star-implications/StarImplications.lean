import StarCone

namespace StarCone
open SimpleGraph Finset

def ClawFree {U : Type*} (G : SimpleGraph U) : Prop :=
  ∀ v a b c : U, G.Adj v a → G.Adj v b → G.Adj v c →
    a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

theorem witness_not_claw_free : ¬ ClawFree graph := by
  intro h
  have e := h 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact (by decide : ¬ (graph.Adj 1 2 ∨ graph.Adj 1 3 ∨ graph.Adj 2 3)) e

theorem witness_tree : graph.IsTree := by
  have reach (v : V) : graph.Reachable v 0 := by
    by_cases h : v = 0
    · subst v; exact .refl _
    · exact (show graph.Adj v 0 from Or.inr ⟨rfl,h⟩).reachable
  refine isTree_iff_connected_and_card.mpr ⟨⟨fun x y => (reach x).trans (reach y).symm⟩,?_⟩
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,← edgeFinset_card]
  decide

theorem row2900_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U]
    (G : SimpleGraph U) [DecidableRel G.Adj],
    (11/12 : ℚ) * forcing G 1 + 1/12 < (forcing G 2 : ℚ) → ¬ G.IsTree) := by
  intro claim
  apply claim V graph _ witness_tree
  rw [star_forcing.1,star_forcing.2]
  norm_num

theorem row2901_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U]
    (G : SimpleGraph U) [DecidableRel G.Adj],
    (11/13 : ℚ) * restrained G - 9/13 < (forcing G 2 : ℚ) → ¬ G.IsTree) := by
  intro claim
  have h := row2417_false
  apply h
  intro U _ _ G _ _ ht
  exact le_of_not_gt (fun bad => claim U G bad ht)

theorem row2918_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U]
    (G : SimpleGraph U) [DecidableRel G.Adj],
    (13/14 : ℚ) * forcing G 1 + 1/14 ≤ (forcing G 2 : ℚ) → ClawFree G) := by
  intro claim
  apply witness_not_claw_free
  apply claim V graph
  rw [star_forcing.1,star_forcing.2]
  norm_num

theorem row6567_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U]
    (G : SimpleGraph U) [DecidableRel G.Adj],
    (forcing G 1 : ℚ) < (12/11 : ℚ) * forcing G 2 - 1/11 → ClawFree G) := by
  intro claim
  apply witness_not_claw_free
  apply claim V graph
  rw [star_forcing.1,star_forcing.2]
  norm_num

theorem row6613_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U]
    (G : SimpleGraph U) [DecidableRel G.Adj],
    (forcing G 1 : ℚ) ≤ (14/13 : ℚ) * forcing G 2 - 1/13 → ClawFree G) := by
  intro claim
  apply witness_not_claw_free
  apply claim V graph
  rw [star_forcing.1,star_forcing.2]
  norm_num

#print axioms row2900_false
#print axioms row2901_false
#print axioms row2918_false
#print axioms row6567_false
#print axioms row6613_false
end StarCone
