import Partial133
import Mathlib.Combinatorics.SimpleGraph.Operations

namespace Graffiti133Bicycle
open SimpleGraph Finset
open scoped Classical
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private def univIso : G.induce (↑(Finset.univ : Finset V) : Set V) ≃g G where
  toEquiv :=
    { toFun := Subtype.val
      invFun := fun v => ⟨v,Finset.mem_univ v⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := Iff.rfl

private def eraseIso (S : Finset V) (x : (↑S : Set V)) :
    ((G.induce (↑S : Set V)).induce {y : (↑S : Set V) | y ≠ x}) ≃g
      G.induce (↑(S.erase x.val) : Set V) where
  toEquiv :=
    { toFun := fun y => ⟨y.val.val, Finset.mem_erase.mpr
        ⟨fun e => y.property (Subtype.ext e),y.val.property⟩⟩
      invFun := fun y => ⟨⟨y.val,(Finset.mem_erase.mp y.property).2⟩,
        fun e => (Finset.mem_erase.mp y.property).1 (congrArg Subtype.val e)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := Iff.rfl

/-- Choose an induced positive-excess graph of globally minimum order.
The two concluding assertions record proper-subset and vertex-deletion budgets. -/
theorem choose_minimum_positive_excess (over : Fintype.card V < G.edgeFinset.card) :
    ∃ S : Finset V,
      S.card < (G.induce (↑S : Set V)).edgeFinset.card ∧
      (∀ T : Finset V, T.card < S.card → (G.induce (↑T : Set V)).edgeFinset.card ≤ T.card) ∧
      (∀ x : (↑S : Set V), ((G.induce (↑S : Set V)).induce {y : (↑S : Set V) | y ≠ x}).edgeFinset.card ≤
        Fintype.card {y : (↑S : Set V) // y ≠ x}) := by
  classical
  let p (S : Finset V) := S.card < (G.induce (↑S : Set V)).edgeFinset.card
  let candidates : Finset (Finset V) := Finset.univ.powerset.filter p
  have mem (S : Finset V) : S∈candidates ↔ p S := by simp [candidates]
  have wit : candidates.Nonempty := by
    refine ⟨Finset.univ,(mem _).mpr ?_⟩
    change (Finset.univ : Finset V).card <
      (G.induce (↑(Finset.univ : Finset V) : Set V)).edgeFinset.card
    rwa [Finset.card_univ,(univIso G).card_edgeFinset_eq]
  obtain ⟨S,hs,minS⟩ := Finset.exists_min_image candidates Finset.card wit
  have sm (T : Finset V) (small : T.card < S.card) :
      (G.induce (↑T : Set V)).edgeFinset.card ≤ T.card := by
    apply Nat.le_of_not_gt
    intro contra
    exact (Nat.not_le_of_lt small) (minS _ ((mem _).mpr contra))
  refine ⟨S,(mem _).mp hs,sm,?_⟩
  intro x
  let e := eraseIso G S x
  have cs : Fintype.card {y : (↑S : Set V) // y≠x} = (S.erase x.val).card :=
    (Fintype.card_congr e.toEquiv).trans (Fintype.card_coe _)
  rw [e.card_edgeFinset_eq,cs]
  exact sm _ (Finset.card_erase_lt_of_mem x.property)

#print axioms choose_minimum_positive_excess
end Graffiti133Bicycle
