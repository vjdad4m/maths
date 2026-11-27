import DegreeFiveBalancedTwoThreeClose189
import DegreeFiveLowThreeThree189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore from DegreeFiveActualCut189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- The entire common-(3,3) and exclusive-(2,3) profile is traceable. -/
theorem traceable_of_balanced_three_three_opposite_two_three
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (shared : 2 ≤ (sharedPortSet C).card)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (cA : (portColor C a).card=3) (cB : (portColor C b).card=3)
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=3) :
    ∃ s t : V,∃ q : G.Walk s t,q.IsPath ∧ ∀ z,z∈q.support := by
  obtain ⟨_,z,zc,za,zb,low⟩ :=
    low_nonporter_of_three_three_opposite_two_three hc two even degree cd shared none cA cB pA pB
  exact traceable_of_balanced_two_three_with_low_nonporter hc two even conn degree cd
    cover shared none pA pB zc za zb low

#print axioms traceable_of_balanced_three_three_opposite_two_three
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
