import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row2471 : 2 ≤ Fintype.card V ∧ ClawFree C ∧ TriangleFree C ∧
    ∃ o, outerNumber C = some o ∧ ¬ ((o : ℚ) ≤ (7/4 : ℚ) * totalNumber C) := by
  refine ⟨by decide,clawfree,triangle,41,outer43,?_⟩
  norm_num [total43]

#print axioms row2471
end CycleBatch
