import TriShortCheck0
import TriShortCheck1
import TriShortCheck2

namespace Graffiti199Depleted.WiderOmission
open CompactOmission
set_option maxRecDepth 8192
set_option maxHeartbeats 13000000

theorem classifyTriShort (m : Fin 3) (row : ℕ) :
    (∃ T, SixTree (edgeTriShort m row) T) ∨
      ∃ tag ∈ residuesTriShort m, ∀ i j, edgeTriShort m row i j = edgeTriShort m tag i j := by
  fin_cases m
  · exact classified_with_full_mask soundTriShort0 validTriShort0 row
  · exact classified_with_full_mask soundTriShort1 validTriShort1 row
  · exact classified_with_full_mask soundTriShort2 validTriShort2 row

theorem consistentTriShort (m : Fin 3) :
    TriangleConsistent layoutTriShort [4] m (familyTriShort m) := by
  fin_cases m <;> decide +kernel

theorem routedTriShort (m : Fin 3) {tag : ℕ} (h : tag ∈ residuesTriShort m) :
    SegmentRoute seamsTriShort (edgeTriShort m tag) (routeTriShort m tag) ∨ exceptionalTriShort m tag := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp h
  fin_cases m
  · exact routesTriShort0 i
  · exact routesTriShort1 i
  · exact routesTriShort2 i

end Graffiti199Depleted.WiderOmission
