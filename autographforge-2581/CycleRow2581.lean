import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row2581 : 2 ≤ Fintype.card V ∧ Planar C ∧ Subcubic C ∧
    ∃ o, outerNumber C = some o ∧ ¬ ((o : ℚ) ≤ (7/4 : ℚ) * diameter C + 3/4) := by
  refine ⟨by decide,planar,subcubic,41,outer43,?_⟩
  norm_num [diameter43]

#print axioms row2581
end CycleBatch
