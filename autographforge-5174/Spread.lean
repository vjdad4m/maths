import Regular
import Obstructions

namespace RegularCover5174
open Finset TriangleMatching1078 BullCover1125

/-- At minimum degree one, allowing degree three already requires the
additive correction. The claw attains the degree-error bound exactly. -/
theorem degree_spread_sharp :
    (∀ v, 1 ≤ claw.degree v ∧ claw.degree v ≤ 3) ∧
    claw.degree 0 = 3 ∧ claw.degree 1 = 1 ∧
    edgeCoverValue claw = some 3 ∧ lineDomination claw = 1 ∧
    (∑ v, (claw.degree v - (1+1))) = 1 := by
  obtain ⟨iso,cover,dom⟩ := claw_values
  exact ⟨by decide,by decide,by decide,by simp [edgeCoverValue,iso,cover],dom,by decide⟩

#print axioms degree_spread_sharp
end RegularCover5174
