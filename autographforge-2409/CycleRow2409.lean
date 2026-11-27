import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row2409 : 2 ≤ Fintype.card V ∧ ClawFree C ∧ Subcubic C ∧
    ¬ ((cover C : ℚ) ≤ (3/5 : ℚ) * diameter C + 18/5) := by
  refine ⟨by decide,clawfree,subcubic,?_⟩
  norm_num [cover43,diameter43]

#print axioms row2409
end CycleBatch
