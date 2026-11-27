import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row2411 : 2 ≤ Fintype.card V ∧ (∃ d, C.IsRegularOfDegree d) ∧ TriangleFree C ∧
    ¬ (mean C ≤ (8/17 : ℚ) * cover C + 9/17) := by
  refine ⟨by decide,⟨2,regular⟩,triangle,?_⟩
  norm_num [mean43,cover43]

#print axioms row2411
end CycleBatch
