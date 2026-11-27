import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row1656 : 2 ≤ Fintype.card V ∧ ClawFree C ∧ (∃ d, C.IsRegularOfDegree d) ∧
    ¬ (mean C ≤ (8/17 : ℚ) * cover C + 9/17) := by
  refine ⟨by decide,clawfree,⟨2,regular⟩,?_⟩
  norm_num [mean43,cover43]

#print axioms row1656
end CycleBatch
