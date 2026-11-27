import CycleDomination
import CyclePlane

namespace CycleBatch
open SimpleGraph PathCycleSharpness

theorem row2562 : 2 ≤ Fintype.card V ∧ ClawFree C ∧
    ∃ o, outerNumber C = some o ∧ ¬ ((o : ℚ) ≤ (3/2 : ℚ) * radius C + 3) := by
  refine ⟨by decide,clawfree,41,outer43,?_⟩
  norm_num [radius43]

#print axioms row2562
end CycleBatch
