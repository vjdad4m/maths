import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row2394 : 2 ≤ Fintype.card V ∧ (∃ d, C.IsRegularOfDegree d) ∧
    ∃ o, outerNumber C = some o ∧ ¬ ((o : ℚ) ≤ (3/2 : ℚ) * totalNumber C + 2) := by
  refine ⟨by decide,⟨2,regular⟩,41,outer43,?_⟩
  norm_num [total43]

#print axioms row2394
end CycleBatch
