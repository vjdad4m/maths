import Mathlib.Data.Nat.Basic

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
structure AdjProfile where
  ea : ℕ
  eb : ℕ
  ec : ℕ
  oa : ℕ
  ob : ℕ
  oc : ℕ

namespace AdjProfile
def size (x : AdjProfile) : ℕ := x.ea+x.eb+x.ec+x.oa+x.ob+x.oc
def localOK (x : AdjProfile) : Prop :=
  4≤x.size ∧ 2≤x.oa+x.ob+x.oc ∧ 1≤x.oa+x.oc ∧ 1≤x.ob+x.oc ∧
  (x.ea>0 → x.oa>0) ∧ (x.eb>0 → x.ob>0) ∧ (x.size=4 → 3≤x.oc)
def cutOK (x y : AdjProfile) : Prop :=
  x.ea+x.ec+x.ob+y.ea+y.ec+y.ob≤5 ∧
  x.eb+x.ec+x.oa+y.eb+y.ec+y.oa≤5
def crossOK (x y : AdjProfile) : Prop :=
  (x.ea>0 → y.ea+y.ec+y.ob+1≤5) ∧
  (x.eb>0 → y.eb+y.ec+y.oa+1≤5) ∧
  (x.ec>0 → y.ea+y.eb+y.ec+2≤5) ∧
  (x.oa>0 → y.eb+y.oa+y.oc+1≤5) ∧
  (x.ob>0 → y.ea+y.ob+y.oc+1≤5) ∧
  (x.oc>0 → y.oa+y.ob+y.oc≤5)

set_option maxHeartbeats 1000000 in
theorem compact_top_pair (x y : AdjProfile) (xy : x.size≤y.size)
    (lo : 16≤x.size+y.size) (hi : x.size+y.size≤17)
    (lx : x.localOK) (ly : y.localOK) (cut : x.cutOK y)
    (cx : x.crossOK y) (cy : y.crossOK x) : x.size=4 ∧ x.oc=4 := by
  simp only [localOK,cutOK,crossOK,size] at *
  omega
#print axioms compact_top_pair
end AdjProfile
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
