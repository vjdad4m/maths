import ModelSeparated
import FastTreeCheck

namespace Graffiti199Depleted.WiderOmission

open CompactOmission
set_option maxRecDepth 4096
set_option maxHeartbeats 3800000

theorem clausesSeparated_valid1 :
    ∀ t : Fin (clausesSeparated 1).length, ((clausesSeparated 1).get t).Valid (familySeparated 1).pattern :=
  fastClauses_sound (by decide +kernel)

#print axioms clausesSeparated_valid1

theorem coveredSeparated_valid1 :
    (coveredSeparated 1).Valid (familySeparated 1).pattern
      (MaskOrClause (familySeparated 1) (clausesSeparated 1) (residuesSeparated 1)) 0 0 := by
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

#print axioms coveredSeparated_valid1

theorem routesSeparated_1 : ValidRoutesSeparated 1 := by
  intro i
  fin_cases i <;> decide +kernel

#print axioms routesSeparated_1

end Graffiti199Depleted.WiderOmission
