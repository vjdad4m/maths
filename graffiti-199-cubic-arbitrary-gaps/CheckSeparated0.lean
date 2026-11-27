import ModelSeparated
import FastTreeCheck

namespace Graffiti199Depleted.WiderOmission

open CompactOmission
set_option maxRecDepth 4096
set_option maxHeartbeats 3800000

theorem clausesSeparated_valid0 :
    ∀ t : Fin (clausesSeparated 0).length, ((clausesSeparated 0).get t).Valid (familySeparated 0).pattern :=
  fastClauses_sound (by decide +kernel)

#print axioms clausesSeparated_valid0

theorem coveredSeparated_valid0 :
    (coveredSeparated 0).Valid (familySeparated 0).pattern
      (MaskOrClause (familySeparated 0) (clausesSeparated 0) (residuesSeparated 0)) 0 0 := by
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

#print axioms coveredSeparated_valid0

theorem routesSeparated_0 : ValidRoutesSeparated 0 := by
  intro i
  fin_cases i <;> decide +kernel

#print axioms routesSeparated_0

end Graffiti199Depleted.WiderOmission
