import SixSevenClosed189
import SixDistanceThreeNineteen189
import SixTwelveClosed189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private six_min_shore from SixDistanceThreeShort189
open private no_common_far from SixDistanceThreeShort189
open private shore_sum_with_cover from AdjacentCutFiveMixedFourteenSixteen189
set_option linter.unusedSectionVars false
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}

/-- At order at most twenty, the only remaining distance-three profile
has a six-shore and a twelve-shore with no wholly hidden nonport. -/
theorem traceable_or_six_twelve_at_six_distance_three_order_twenty
    (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cut : 2≤Nat.card (Cmp G a b)) (n : Fintype.card V≤20) :
    (∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support) ∨
      ∃ C D : Cmp G a b,C≠D ∧ (Shore C).card=6 ∧ (Shore D).card=12 ∧
        (∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D) ∧
        ∀ z∈Shore D,¬G.Adj a z → ¬G.Adj b z → G.dist a z=2 ∨ G.dist b z=2 := by
  classical
  by_cases n19 : Fintype.card V≤19
  · exact .inl (traceable_at_six_distance_three_order_nineteen hc far ab even conn degree cut n19)
  obtain ⟨C,D,cd,cover⟩ := actual_two_shores (component_card_eq_two_at_six hc ab even conn degree cut)
  have c := six_min_shore far ab conn C degree
  have d := six_min_shore far ab conn D degree
  have sum := shore_sum_with_cover ab cd cover
  have residual (A B : Cmp G a b) (hAB : A≠B)
      (cv : ∀ {z : V},z≠a → z≠b → z∈Shore A ∨ z∈Shore B)
      (hA : (Shore A).card=6) (hB : (Shore B).card=12) :
      ∀ z∈Shore B,¬G.Adj a z → ¬G.Adj b z → G.dist a z=2 ∨ G.dist b z=2 := by
    intro z zb az bz
    by_contra nez
    have zrole : sixClassSpec G a b z 7 :=
      ⟨az,bz,fun k=>nez (.inl k),fun k=>nez (.inr k)⟩
    have kn : ¬(G.Adj a z ∧ G.Adj b z) := no_common_far far
    have zm := (mem_sixBucket kn 7).mpr ⟨zb,zrole⟩
    exact no_six_twelve_shores_of_hidden_nonport hc far ab conn even degree hAB cv hA hB (card_pos.mpr ⟨z,zm⟩)
  have cv' : ∀ {z : V},z≠a → z≠b → z∈Shore D ∨ z∈Shore C := fun za zb=>(cover za zb).symm
  by_cases c10 : (Shore C).card≤10
  · by_cases d10 : (Shore D).card≤10
    · exact .inl (traceable_at_distance_three_two_shores_le_ten hc far ab even conn degree cd cover c10 d10)
    by_cases c6 : (Shore C).card=6
    · have d12 : (Shore D).card=12 := by omega
      exact .inr ⟨C,D,cd,c6,d12,cover,residual C D cd cover c6 d12⟩
    exact (no_seven_eleven_shores hc far ab even conn degree cd cover (by omega) (by omega)).elim
  by_cases d6 : (Shore D).card=6
  · have c12 : (Shore C).card=12 := by omega
    exact .inr ⟨D,C,cd.symm,d6,c12,cv',residual D C cd.symm cv' d6 c12⟩
  exact (no_seven_eleven_shores hc far ab even conn degree cd.symm cv' (by omega) (by omega)).elim

#print axioms traceable_or_six_twelve_at_six_distance_three_order_twenty
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
