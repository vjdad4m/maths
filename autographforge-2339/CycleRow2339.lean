import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row2339 : 2 ≤ Fintype.card V ∧ C.CliqueFree 4 ∧ ClawFree C ∧
    ∃ o, outerNumber C = some o ∧ ¬ ((o : ℚ) ≤ (3/2 : ℚ) * totalNumber C + 2) := by
  refine ⟨by decide,k4free,clawfree,41,outer43,?_⟩
  norm_num [total43]

#print axioms row2339
end CycleBatch
