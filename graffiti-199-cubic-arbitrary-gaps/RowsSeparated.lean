import CheckSeparated0
import CheckSeparated1
import CheckSeparated2

namespace Graffiti199Depleted.WiderOmission
open CompactOmission
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

private theorem clausesSeparated_valid (m : Fin 3) :
    ∀ i : Fin (clausesSeparated m).length, ((clausesSeparated m).get i).Valid (familySeparated m).pattern := by
  fin_cases m
  · exact clausesSeparated_valid0
  · exact clausesSeparated_valid1
  · exact clausesSeparated_valid2

private theorem coveredSeparated_valid (m : Fin 3) :
    (coveredSeparated m).Valid (familySeparated m).pattern
      (MaskOrClause (familySeparated m) (clausesSeparated m) (residuesSeparated m)) 0 0 := by
  fin_cases m
  · exact coveredSeparated_valid0
  · exact coveredSeparated_valid1
  · exact coveredSeparated_valid2

theorem classificationSeparated (m : Fin 3) (row : ℕ) :
    (∃ T, SixTree ((familySeparated m).pattern.edge row) T) ∨
      ∃ tag ∈ residuesSeparated m, ∀ i j,
        (familySeparated m).pattern.edge row i j = (familySeparated m).pattern.edge tag i j :=
  classified_with_full_mask (clausesSeparated_valid m) (coveredSeparated_valid m) row

theorem familySeparated_consistent (m : Fin 3) : SparseConsistent layoutSeparated [2,5] m (familySeparated m) := by
  fin_cases m <;> decide

#print axioms classificationSeparated
#print axioms familySeparated_consistent

theorem certifiedRouteSeparated (m : Fin 3) {tag : ℕ} (h : tag ∈ residuesSeparated m) :
    SegmentRoute seamsSeparated (edgeSeparated m tag) (routeSeparated m tag) := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp h
  fin_cases m
  · exact routesSeparated_0 i
  · exact routesSeparated_1 i
  · exact routesSeparated_2 i


#print axioms certifiedRouteSeparated

end Graffiti199Depleted.WiderOmission
