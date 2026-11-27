import Roman
import ThetaDrawing

namespace Theta659
open SimpleGraph TriangleMatching1078 AutoGraphForge378

/-- Both source optima are explicit for every family member with k ≥ 2. -/
theorem family (k : ℕ) (hk : 2 ≤ k) :
    Fintype.card (V k) = 2*k+2 ∧ (graph k).Connected ∧ Planar (graph k) ∧
    TriangleFree (graph k) ∧ (graph k).Colorable 2 ∧ lineDomination (graph k) = k ∧
    minMaximalMatching (graph k) = k ∧ romanNumber (graph k) = 4 := by
  have hi : minMaximalMatching (graph k) ≤ k := Nat.sInf_le middle_matching
  have lo := @edge_lower k
  have cmp := lineDomination_le_matching (graph k)
  exact ⟨order k,connected (by omega),planar k,triangle_free,bipartite,by omega,by omega,roman_exact hk⟩

/-- At k = m+4, the excess of the proposed left side is exactly m+1. -/
theorem unbounded (m : ℕ) :
    2 ≤ Fintype.card (V (m+4)) ∧ (graph (m+4)).Connected ∧ Planar (graph (m+4)) ∧
    TriangleFree (graph (m+4)) ∧ lineDomination (graph (m+4)) + 1 =
      romanNumber (graph (m+4)) + (m+1) := by
  obtain ⟨sz,conn,plane,tri,_,edge,_,roman⟩ := family (m+4) (by omega)
  exact ⟨by omega,conn,plane,tri,by omega⟩

theorem row659_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → Planar G → TriangleFree G →
    lineDomination G + 1 ≤ romanNumber G) := by
  intro claim
  obtain ⟨sz,_,plane,tri,h⟩ := unbounded 0
  have := claim _ _ sz plane tri
  omega

#print axioms packing_lower
#print axioms planar
#print axioms family
#print axioms unbounded
#print axioms row659_false
end Theta659
