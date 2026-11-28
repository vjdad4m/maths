import SixElevenClosed189

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

/-- A threshold-six graph with an actual distance-three two-cut is
traceable through order 19. The asymmetric 6+11 profile is impossible. -/
theorem traceable_at_six_distance_three_order_nineteen
    (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cut : 2≤Nat.card (Cmp G a b)) (n : Fintype.card V≤19) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  obtain ⟨C,D,cd,cover⟩ := actual_two_shores (component_card_eq_two_at_six hc ab even conn degree cut)
  have c := six_min_shore far ab conn C degree
  have d := six_min_shore far ab conn D degree
  have sum := shore_sum_with_cover ab cd cover
  by_cases c10 : (Shore C).card≤10
  · by_cases d10 : (Shore D).card≤10
    · exact traceable_at_distance_three_two_shores_le_ten hc far ab even conn degree cd cover c10 d10
    · exact (no_six_eleven_shores hc far ab conn even degree cd cover (by omega) (by omega)).elim
  exact (no_six_eleven_shores hc far ab conn even degree cd.symm (fun za zb=>(cover za zb).symm)
    (by omega) (by omega)).elim

#print axioms traceable_at_six_distance_three_order_nineteen
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
