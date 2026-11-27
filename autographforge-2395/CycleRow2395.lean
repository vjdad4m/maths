import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row2395 : 2 ≤ Fintype.card V ∧ Planar C ∧ Subcubic C ∧
    ∃ o, outerNumber C = some o ∧ ¬ ((o : ℚ) ≤ (3/2 : ℚ) * totalNumber C + 2) := by
  refine ⟨by decide,planar,subcubic,41,outer43,?_⟩
  norm_num [total43]

#print axioms row2395
end CycleBatch
