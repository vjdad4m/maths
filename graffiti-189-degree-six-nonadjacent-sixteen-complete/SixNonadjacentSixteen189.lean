import SixSingletonThreeActual189
import SixNearOrderSixteen189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_nonempty shore_disjoint from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private shore_sum_with_cover from AdjacentCutFiveMixedFourteenSixteen189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- At order sixteen, the degree-six nonadjacent actual two-cut branch is
traceable, with no conditions on the shapes of its two shores. -/
theorem traceable_at_six_nonadjacent_order_sixteen
    (hc : G.Connected) (ab : a≠b) (non : ¬G.Adj a b)
    (even : ∀ x,(EvenFrom G x).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cut : 2≤Nat.card (Cmp G a b)) (n : Fintype.card V=16) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  by_cases far : 3≤G.dist a b
  · exact traceable_at_six_distance_three_order_seventeen hc far ab even conn degree cut (by omega)
  have low := hc.one_lt_dist_of_ne_of_not_adj ab non
  have two : G.dist a b=2 := by omega
  obtain ⟨C,D,cd,cover⟩ := actual_two_shores (component_card_eq_two_at_six hc ab even conn degree cut)
  have oneCase {C D : Cmp G a b} (cd : C≠D)
      (cov : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
      (one : (Shore C).card=1) :
      ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
    have sum := shore_sum_with_cover ab cd cov
    exact traceable_of_nonadjacent_singleton_thirteen hc two even conn degree cd cov one (by omega)
  by_cases c1 : (Shore C).card=1
  · exact oneCase cd cover c1
  by_cases d1 : (Shore D).card=1
  · exact oneCase cd.symm (fun za zb=>(cover za zb).symm) d1
  have every (K : Cmp G a b) : 2≤(Shore K).card := by
    obtain ⟨z,zK⟩ := shore_nonempty K
    have za : z≠a := fun h=>(shore_off K).1 (h ▸ zK)
    have zb : z≠b := fun h=>(shore_off K).2 (h ▸ zK)
    rcases cover za zb with zC|zD
    · have e : K=C := Classical.byContradiction (fun no=>disjoint_left.mp (shore_disjoint no) zK zC)
      subst K
      have pp : 0<(Shore C).card := card_pos.mpr ⟨z,zK⟩
      omega
    have e : K=D := Classical.byContradiction (fun no=>disjoint_left.mp (shore_disjoint no) zK zD)
    subst K
    have pp : 0<(Shore D).card := card_pos.mpr ⟨z,zK⟩
    omega
  exact traceable_at_six_nonsingleton_shores_order_sixteen hc ab even conn degree cut (by omega) every

#print axioms traceable_at_six_nonadjacent_order_sixteen
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
