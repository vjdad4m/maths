import SixThirteenComplete189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private six_min_shore from SixDistanceThreeShort189
open private shore_sum_with_cover from AdjacentCutFiveMixedFourteenSixteen189
set_option linter.unusedSectionVars false
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}

/-- At order at most 21, the only remaining distance-three profiles
are a seven-shore opposite a twelve-shore or an eight-shore opposite
an eleven-shore. -/
theorem traceable_or_seven_twelve_eight_eleven_at_six_distance_three_order_twenty_one
    (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cut : 2≤Nat.card (Cmp G a b)) (n : Fintype.card V≤21) :
    (∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support) ∨
      ∃ C D : Cmp G a b,C≠D ∧
        (∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D) ∧
        (((Shore C).card=7 ∧ (Shore D).card=12) ∨
         ((Shore C).card=8 ∧ (Shore D).card=11)) := by
  classical
  by_cases n20 : Fintype.card V≤20
  · exact .inl (traceable_at_six_distance_three_order_twenty hc far ab even conn degree cut n20)
  obtain ⟨C,D,cd,cover⟩ := actual_two_shores (component_card_eq_two_at_six hc ab even conn degree cut)
  have c := six_min_shore far ab conn C degree
  have d := six_min_shore far ab conn D degree
  have sum := shore_sum_with_cover ab cd cover
  have cv' : ∀ {z : V},z≠a → z≠b → z∈Shore D ∨ z∈Shore C :=
    fun za zb=>(cover za zb).symm
  by_cases c10 : (Shore C).card≤10
  · by_cases d10 : (Shore D).card≤10
    · exact .inl (traceable_at_distance_three_two_shores_le_ten hc far ab even conn degree cd cover c10 d10)
    by_cases c6 : (Shore C).card=6
    · exact (no_six_thirteen_shores hc far ab even conn degree cd cover c6 (by omega)).elim
    exact .inr ⟨C,D,cd,cover,by omega⟩
  by_cases d6 : (Shore D).card=6
  · exact (no_six_thirteen_shores hc far ab even conn degree cd.symm cv' d6 (by omega)).elim
  exact .inr ⟨D,C,cd.symm,cv',by omega⟩

#print axioms traceable_or_seven_twelve_eight_eleven_at_six_distance_three_order_twenty_one
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
