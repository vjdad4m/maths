import DegreeFiveBalancedThreeThreeClose189
import DegreeFiveBalancedThreeFourClose189
import DegreeFiveReverseClose189
import DegreeFiveBalancedFourFour189
import DegreeFiveTwoThreeRange189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore from DegreeFiveActualCut189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- An exclusively attached two-three shore opposite a shore with
at least two common contacts guarantees traceability. -/
theorem traceable_of_exclusive_two_three_opposite_common
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (shared : 2 ≤ (sharedPortSet C).card)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=3) :
    ∃ s t : V,∃ q : G.Walk s t,q.IsPath ∧ ∀ z,z∈q.support := by
  obtain ⟨a3,a4,b3,b4⟩ :=
    common_contact_range_opposite_two_three hc two even degree conn cd cover shared none pA pB
  by_cases aSmall : (portColor C a).card=3
  · by_cases bSmall : (portColor C b).card=3
    · exact traceable_of_balanced_three_three_opposite_two_three hc two even conn degree cd
        cover shared none aSmall bSmall pA pB
    have bLarge : (portColor C b).card=4 := by omega
    exact traceable_of_balanced_three_four_opposite_two_three hc two even conn degree cd
      cover shared none aSmall bLarge pA pB
  have aLarge : (portColor C a).card=4 := by omega
  by_cases bSmall : (portColor C b).card=3
  · exact traceable_of_balanced_four_three_opposite_two_three hc two even conn degree cd
      cover shared none aLarge bSmall pA pB
  have bLarge : (portColor C b).card=4 := by omega
  exact traceable_of_balanced_four_four hc two even conn degree cd cover shared none
    aLarge bLarge pA (by omega)

#print axioms traceable_of_exclusive_two_three_opposite_common
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
