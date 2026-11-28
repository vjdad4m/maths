import CycleDomination

namespace CycleBatch
open SimpleGraph PathCycleSharpness

/-- The three claims below use the same pinned witness C43. -/
theorem row3378_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U)
    [DecidableRel G.Adj], 3 * (burning G : ℚ) - 2 < (cover G : ℚ) → ¬ Subcubic G) := by
  intro claim
  apply claim V C _ subcubic
  rw [burning43,cover43]
  norm_num

theorem row4293_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U)
    [DecidableRel G.Adj], (burning G : ℚ) < (1/3 : ℚ) * cover G + 2/3 → ¬ Subcubic G) := by
  intro claim
  apply claim V C _ subcubic
  rw [burning43,cover43]
  norm_num

def Regular {U : Type} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] : Prop :=
  ∃ k : ℕ, G.IsRegularOfDegree k

theorem row4298_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U)
    [DecidableRel G.Adj] (o : ℕ), outerNumber G = some o →
    (burning G : ℚ) < (1/6 : ℚ) * o + 5/3 → ¬ Regular G) := by
  intro claim
  apply claim V C 41 outer43 _ ⟨2, regular⟩
  rw [burning43]
  norm_num

#print axioms row3378_false
#print axioms row4293_false
#print axioms row4298_false
end CycleBatch
