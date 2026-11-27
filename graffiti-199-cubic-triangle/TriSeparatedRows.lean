import TriSeparatedCheck0
import TriSeparatedCheck1
import TriSeparatedCheck2

namespace Graffiti199Depleted.WiderOmission

open CompactOmission

def exceptionalSeparated (m : Fin 3) : List ℕ :=
  ![[53579,66049],[67585,39100],[91088,67585]] m

theorem classifyTriSeparated (m : Fin 3) (row : ℕ) :
    (∃ T, SixTree (edgeTriSeparated m row) T) ∨
      (∃ P, SegmentRoute seamsTriSeparated (edgeTriSeparated m row) P) ∨
      ∃ tag ∈ exceptionalSeparated m, ∀ i j, edgeTriSeparated m row i j = edgeTriSeparated m tag i j := by
  fin_cases m
  · exact classified_by_root_routes validTriSeparated0 row
  · exact classified_by_root_routes validTriSeparated1 row
  · exact classified_by_root_routes validTriSeparated2 row

theorem consistentTriSeparated (m : Fin 3) :
    TriangleConsistent layoutTriSeparated [2,5] m (familyTriSeparated m) := by
  fin_cases m <;> decide +kernel

#print axioms classifyTriSeparated

end Graffiti199Depleted.WiderOmission
