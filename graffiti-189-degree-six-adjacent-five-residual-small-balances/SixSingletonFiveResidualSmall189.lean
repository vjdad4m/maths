import SixSingletonFiveThreeActualMinThree189
import SixSingletonFiveResidualTwoLow189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark from SixSingletonGeometry189
open private nearBal from SixSingletonFiveGeometry189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- A five-visible counterexample requires three balances, at least two
of dark degree at most three, and a dark vertex of degree at most two. -/
theorem traceable_of_adjacent_singleton_thirteen_five_unless_small_balances
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13)
    (v5 : (Vis D).card=5)
    (exception : (nearBal D).card=3 →
      ((nearBal D).filter (fun z=>(inside G (Dark D) z).card≤3)).card≤1 ∨
        ∀ z∈Dark D,3≤(inside G (Dark D) z).card) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  by_cases q3 : (nearBal D).card=3
  · rcases exception q3 with b|d
    · exact traceable_of_adjacent_singleton_thirteen_five_unless_two_low hc ab even conn degree
        sd cover one d13 v5 (fun _=>b)
    exact traceable_of_adjacent_singleton_thirteen_five_three_balanced_dark_min_three hc ab even conn degree
      sd cover one d13 v5 q3 d
  exact traceable_of_adjacent_singleton_thirteen_five_unless_two_low hc ab even conn degree
    sd cover one d13 v5 (fun p=>(q3 p).elim)

#print axioms traceable_of_adjacent_singleton_thirteen_five_unless_small_balances
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
