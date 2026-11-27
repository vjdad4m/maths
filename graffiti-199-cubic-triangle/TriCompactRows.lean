import TriCompactCheck0
import TriCompactCheck1
import TriCompactCheck2

namespace Graffiti199Depleted.WiderOmission
open CompactOmission
set_option maxRecDepth 8192
set_option maxHeartbeats 13000000

theorem classifyTriCompact (m : Fin 3) (row : ℕ) :
    (∃ T, SixTree (edgeTriCompact m row) T) ∨
      ∃ tag ∈ residuesTriCompact m, ∀ i j, edgeTriCompact m row i j = edgeTriCompact m tag i j := by
  fin_cases m
  · exact classified_with_full_mask soundTriCompact0 validTriCompact0 row
  · exact classified_with_full_mask soundTriCompact1 validTriCompact1 row
  · exact classified_with_full_mask soundTriCompact2 validTriCompact2 row

theorem consistentTriCompact (m : Fin 3) :
    TriangleConsistent layoutTriCompact [] m (familyTriCompact m) := by
  fin_cases m <;> decide +kernel

theorem routedTriCompact (m : Fin 3) {tag : ℕ} (h : tag ∈ residuesTriCompact m) :
    SegmentRoute seamsTriCompact (edgeTriCompact m tag) (routeTriCompact m tag) ∨ exceptionalTriCompact m tag := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp h
  fin_cases m
  · exact routesTriCompact0 i
  · exact routesTriCompact1 i
  · exact routesTriCompact2 i

end Graffiti199Depleted.WiderOmission
