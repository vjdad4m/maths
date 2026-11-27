import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row2396 : 2 ≤ Fintype.card V ∧ ClawFree C ∧ Subcubic C ∧
    ∃ o, outerNumber C = some o ∧ ¬ ((o : ℚ) ≤ (3/2 : ℚ) * totalNumber C + 2) := by
  refine ⟨by decide,clawfree,subcubic,41,outer43,?_⟩
  norm_num [total43]

#print axioms row2396
end CycleBatch
