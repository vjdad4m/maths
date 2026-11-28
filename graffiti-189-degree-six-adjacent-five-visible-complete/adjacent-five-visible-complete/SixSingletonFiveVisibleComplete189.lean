import SixSingletonFiveThreeActualAllLow189
import SixSingletonFiveThreeHasHigh189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark from SixSingletonGeometry189
open private nearBal from SixSingletonFiveGeometry189
open private m5_dark_nonbalance_high from SixSingletonFiveResidualTwoLow189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Complete five-visible adjacent singleton+13 case for the degree-six threshold. -/
theorem traceable_of_adjacent_singleton_thirteen_five_visible
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13)
    (v5 : (Vis D).card=5) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  by_cases q3 : (nearBal D).card=3
  · by_cases high : ∃ h∈nearBal D,4≤(inside G (Dark D) h).card
    · obtain ⟨h,hh,h4⟩ := high
      exact traceable_of_adjacent_singleton_thirteen_five_three_balanced_has_high hc ab even conn degree
        sd cover one d13 v5 q3 hh h4
    by_cases min3 : ∀ z∈Dark D,3≤(inside G (Dark D) z).card
    · exact traceable_of_adjacent_singleton_thirteen_five_three_balanced_dark_min_three hc ab even conn degree
        sd cover one d13 v5 q3 min3
    push_neg at min3 high
    obtain ⟨z,zd,zl⟩ := min3
    have zb : z∈nearBal D := by
      by_contra not
      have p := m5_dark_nonbalance_high hc ab even conn degree sd cover one d13 v5 z zd not
      omega
    exact traceable_of_adjacent_singleton_thirteen_five_three_balanced_all_low hc ab even conn degree
      sd cover one d13 v5 q3 zb (by omega) (fun w wm=>by have h := high w wm; omega)
  exact traceable_of_adjacent_singleton_thirteen_five_unless_small_balances hc ab even conn degree
    sd cover one d13 v5 (fun p=>(q3 p).elim)

#print axioms traceable_of_adjacent_singleton_thirteen_five_visible
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
