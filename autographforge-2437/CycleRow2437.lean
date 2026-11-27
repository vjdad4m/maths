import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row2437 : 2 ≤ Fintype.card V ∧ C.Connected ∧ Subcubic C ∧
    ¬ (cover C ≤ 10) := by
  refine ⟨by decide,connected,subcubic,?_⟩
  norm_num [cover43]

#print axioms row2437
end CycleBatch
