import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row2194 : 2 ≤ Fintype.card V ∧ Subcubic C ∧
    ¬ ((cover C : ℚ) ≤ 3 * burning C - 2) := by
  refine ⟨by decide,subcubic,?_⟩
  norm_num [cover43,burning43]

#print axioms row2194
end CycleBatch
