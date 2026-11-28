import AdjacentCutFiveTopArithmetic189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent.AdjProfile
def symmetricProfile (x : AdjProfile) : Prop :=
  x.ea=0 ∧ x.eb=0 ∧ x.oa=0 ∧ x.ob=0

set_option maxHeartbeats 2000000 in
theorem compact_at_seventeen (x y : AdjProfile) (xy : x.size≤y.size)
    (sz : x.size+y.size=15)
    (lx : x.localOK) (ly : y.localOK) (cut : x.cutOK y)
    (cx : x.crossOK y) (cy : y.crossOK x) :
    (x.size=4 ∧ x.oc=4) ∨ (x.symmetricProfile ∧ y.symmetricProfile) := by
  have s : x.size=4 ∨ x.size=5 ∨ x.size=6 ∨ x.size=7 := by
    have x4 := lx.1
    omega
  rcases s with z|z|z|z
  · left
    refine ⟨z,?_⟩
    simp only [localOK,cutOK,crossOK,size] at *
    omega
  all_goals
    right
    have no : x.oa+x.ob+y.oa+y.ob=0 := by
      simp only [localOK,cutOK,crossOK,size] at *
      omega
    simp only [localOK,symmetricProfile] at lx ly ⊢
    omega
#print axioms compact_at_seventeen
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent.AdjProfile
