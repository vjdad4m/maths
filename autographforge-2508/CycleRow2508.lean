import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row2508 : 2 ≤ Fintype.card V ∧ C.Connected ∧ Subcubic C ∧
    ∃ o, outerNumber C = some o ∧ ¬ ((o : ℚ) ≤ (12/13 : ℚ) * C.edgeFinset.card + 3/13) := by
  refine ⟨by decide,connected,subcubic,41,outer43,?_⟩
  rw [size43]
  norm_num

#print axioms row2508
end CycleBatch
