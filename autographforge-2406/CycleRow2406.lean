import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row2406 : 2 ≤ Fintype.card V ∧ ClawFree C ∧ Planar C ∧
    ¬ ((cover C : ℚ) ≤ (11/12 : ℚ) * rainbow2 C + 7/6) := by
  refine ⟨by decide,clawfree,planar,?_⟩
  norm_num [rainbow43,cover43]

#print axioms row2406
end CycleBatch
