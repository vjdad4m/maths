import SixAdjacentSixteenSingletonComplete189
import SixNonadjacentSixteen189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair Graffiti189Ore
open private Shore shore_off shore_nonempty shore_disjoint from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private shore_sum_with_cover from AdjacentCutFiveMixedFourteenSixteen189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- At order sixteen, an actual two-vertex separator with connected singleton
deletions suffices at degree six, whether or not it is an edge. -/
theorem traceable_at_six_actual_two_cut_order_sixteen
    (hc : G.Connected) (ab : a≠b) (even : ∀ x,(EvenFrom G x).card≤7)
    (conn : DeletionConnected G) (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cut : 2≤Nat.card (Cmp G a b)) (n : Fintype.card V=16) : Traceable G := by
  classical
  by_cases adj : G.Adj a b
  · obtain ⟨C,D,cd,cover⟩ := actual_two_shores (component_card_eq_two_at_six hc ab even conn degree cut)
    have oneCase {K L : Cmp G a b} (kl : K≠L)
        (cov : ∀ {z : V},z≠a → z≠b → z∈Shore K ∨ z∈Shore L)
        (one : (Shore K).card=1) : Traceable G := by
      have sum := shore_sum_with_cover ab kl cov
      exact traceable_of_adjacent_singleton_thirteen hc adj even conn degree kl cov one (by omega)
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
        have pos : 0<(Shore C).card := card_pos.mpr ⟨z,zK⟩
        omega
      have e : K=D := Classical.byContradiction (fun no=>disjoint_left.mp (shore_disjoint no) zK zD)
      subst K
      have pos : 0<(Shore D).card := card_pos.mpr ⟨z,zK⟩
      omega
    exact traceable_at_six_nonsingleton_shores_order_sixteen hc ab even conn degree cut (by omega) every
  exact traceable_at_six_nonadjacent_order_sixteen hc ab adj even conn degree cut n

#print axioms traceable_at_six_actual_two_cut_order_sixteen
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
