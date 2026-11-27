import ModelSeparated
import FastTreeCheck

namespace Graffiti199Depleted.WiderOmission

open CompactOmission
set_option maxRecDepth 4096
set_option maxHeartbeats 3800000

theorem clausesSeparated_valid2 :
    ∀ t : Fin (clausesSeparated 2).length, ((clausesSeparated 2).get t).Valid (familySeparated 2).pattern :=
  fastClauses_sound (by decide +kernel)

#print axioms clausesSeparated_valid2

theorem coveredSeparated_valid2 :
    (coveredSeparated 2).Valid (familySeparated 2).pattern
      (MaskOrClause (familySeparated 2) (clausesSeparated 2) (residuesSeparated 2)) 0 0 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · refine ⟨by decide +kernel, ?_, ?_⟩
      · decide +kernel
      · refine ⟨by decide +kernel, ?_, ?_⟩
        · decide +kernel
        · decide +kernel
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · refine ⟨by decide +kernel, ?_, ?_⟩
      · refine ⟨by decide +kernel, ?_, ?_⟩
        · decide +kernel
        · decide +kernel
      · refine ⟨by decide +kernel, ?_, ?_⟩
        · decide +kernel
        · decide +kernel

#print axioms coveredSeparated_valid2

theorem routesSeparated_2 : ValidRoutesSeparated 2 := by
  intro i
  fin_cases i <;> decide +kernel

#print axioms routesSeparated_2

end Graffiti199Depleted.WiderOmission
