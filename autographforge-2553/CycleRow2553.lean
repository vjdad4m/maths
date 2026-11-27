import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row2553 : 2 ≤ Fintype.card V ∧ Eulerian C ∧
    ¬ ((cover C : ℚ) ≤ 2 * burning C + 6) := by
  refine ⟨by decide,eulerian,?_⟩
  norm_num [cover43,burning43]

#print axioms row2553
end CycleBatch
