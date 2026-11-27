import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row1606 : 2 ≤ Fintype.card V ∧ ClawFree C ∧ (∃ d, C.IsRegularOfDegree d) ∧
    ¬ ((cover C : ℚ) ≤ 3 * burning C - 4) := by
  refine ⟨by decide,clawfree,⟨2,regular⟩,?_⟩
  norm_num [cover43,burning43]

#print axioms row1606
end CycleBatch
