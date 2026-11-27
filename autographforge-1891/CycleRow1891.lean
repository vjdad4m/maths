import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row1891 : 2 ≤ Fintype.card V ∧ Eulerian C ∧ (∃ d, C.IsRegularOfDegree d) ∧
    ¬ (mean C ≤ (8/17 : ℚ) * cover C + 9/17) := by
  refine ⟨by decide,eulerian,⟨2,regular⟩,?_⟩
  norm_num [mean43,cover43]

#print axioms row1891
end CycleBatch
