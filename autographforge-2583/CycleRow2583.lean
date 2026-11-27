import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row2583 : 2 ≤ Fintype.card V ∧ ClawFree C ∧
    ∃ o, outerNumber C = some o ∧ ¬ ((o : ℚ) ≤ (7/3 : ℚ) * slater C + 7/3) := by
  refine ⟨by decide,clawfree,41,outer43,?_⟩
  norm_num [slater43]

#print axioms row2583
end CycleBatch
