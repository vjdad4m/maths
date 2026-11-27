import DegreeFiveTwoTwo33Close189
import DegreeFiveTwoTwo43Close189
import DegreeFiveBalancedFourFour189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off shore_disjoint from DegreeFiveActualCut189
open private secondShore charge_at_high_port anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor two_shore_budget from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- The entire exclusive 2+2 profile opposite a common shore is traceable. -/
theorem traceable_of_exclusive_two_two_opposite_common
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (shared : 2≤(sharedPortSet C).card)
    (none : ∀ z∈Shore D,¬(G.Adj a z ∧ G.Adj b z))
    (pA : (portColor D a).card=2) (pB : (portColor D b).card=2) :
    ∃ s t : V,∃ q : G.Walk s t,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  obtain ⟨_,a3,a4,b3,b4,_,_,_⟩ :=
    two_two_common_shore_geometry hc two even conn degree cd cover shared none pA pB
  by_cases A3 : (portColor C a).card=3
  · by_cases B3 : (portColor C b).card=3
    · exact traceable_of_balanced_three_three_opposite_two_two hc two even conn degree cd
        cover shared none A3 B3 pA pB
    have B4 : (portColor C b).card=4 := by omega
    let C' := swapCut C
    let D' := swapCut D
    have C_eq : Shore C'=Shore C := shore_swapCut C
    have D_eq : Shore D'=Shore D := shore_swapCut D
    have cc (c : V) : portColor C' c=portColor C c := by simp [portColor,C_eq]
    have dp (c : V) : portColor D' c=portColor D c := by simp [portColor,D_eq]
    have sh : sharedPortSet C'=sharedPortSet C := by
      simp [sharedPortSet,C_eq,and_comm]
    have cd' : C'≠D' := fun h=>cd (swapCut.injective h)
    have none' (w : V) (wd : w∈Shore D') (p : G.Adj b w ∧ G.Adj a w) : False :=
      none w (D_eq ▸ wd) ⟨p.2,p.1⟩
    have cover' (w : V) : w=b ∨ w=a ∨ w∈Shore C' ∨ w∈Shore D' := by
      rw [C_eq,D_eq]
      rcases cover w with h|h|h|h
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr (.inl h))
      exact .inr (.inr (.inr h))
    have rev : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
    exact traceable_of_balanced_four_three_opposite_two_two (a:=b) (b:=a) hc rev even
      conn degree cd' cover' (by rwa [sh]) none' (by rwa [cc]) (by rwa [cc])
      (by rwa [dp]) (by rwa [dp])
  have A4 : (portColor C a).card=4 := by omega
  by_cases B3 : (portColor C b).card=3
  · exact traceable_of_balanced_four_three_opposite_two_two hc two even conn degree cd
      cover shared none A4 B3 pA pB
  have B4 : (portColor C b).card=4 := by omega
  exact traceable_of_balanced_four_four hc two even conn degree cd cover shared none
    A4 B4 pA (by omega)

#print axioms traceable_of_exclusive_two_two_opposite_common
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
