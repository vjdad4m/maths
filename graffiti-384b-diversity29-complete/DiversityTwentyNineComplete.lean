import CompleteFourRoots
import OriginalSix30

namespace Graffiti384b.Diversity29
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Graffiti.pc #384b at triangle-count diversity 29, for every finite simple graph. -/
theorem original_bound (t : (types G).card = 29) : gamma G ≤ bound G := by
  apply Nat.le_of_not_gt
  intro bad
  have quota := EarMix.remaining_nonleaves G t bad
  have exactBound := PrivatePatch.twenty_nine_nonleaves G t quota
  exact (not_lt_of_ge (show gamma G ≤ bound G by simpa only [bound, t] using exactBound)) bad

theorem numerical_bound (t : (types G).card = 29) : gamma G ≤ Fintype.card V - 15 := by
  simpa only [bound, t] using original_bound G t

/-- A two-dominating set that omits at least fifteen vertices. -/
theorem exists_set (t : (types G).card = 29) :
    ∃ D : Finset V, TwoDominates G D ∧ D.card + 15 ≤ Fintype.card V := by
  obtain ⟨D, dom, size⟩ := Nat.sInf_mem
    (show {k : ℕ | ∃ d, TwoDominates G d ∧ d.card = k}.Nonempty from
      ⟨_, univ, fun _ outside => (outside (mem_univ _)).elim, rfl⟩)
  have enoughVertices : (types G).card ≤ Fintype.card V :=
    (card_image_le (s := (univ : Finset V)) (f := trianglesAt G)).trans_eq card_univ
  change D.card = gamma G at size
  have upper := numerical_bound G t
  exact ⟨D, dom, by omega⟩

end Graffiti384b.Diversity29
#print axioms Graffiti384b.Diversity29.original_bound
#print axioms Graffiti384b.Diversity29.numerical_bound
#print axioms Graffiti384b.Diversity29.exists_set
