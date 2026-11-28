import SixSingletonFiveTwoDeepActual189
import SixSingletonFiveThreeActualDense189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore from AdjacentCutFiveActual189
open private Cmp aPorts bPorts DeletionConnected from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark from SixSingletonGeometry189
open private nearBal deep from SixSingletonFiveGeometry189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- The five-visible adjacent singleton+13 profiles all have a spanning path
except possibly when there are three balanced depth-two dark vertices and
one of them has induced dark degree at most three. -/
theorem traceable_of_adjacent_singleton_thirteen_five_unless_three_sparse
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13)
    (v5 : (Vis D).card=5)
    (exception : (nearBal D).card=3 → ∀ z∈Dark D,4≤(inside G (Dark D) z).card) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have ⟨dp,cap⟩ : (deep D).card≤1 ∧ (nearBal D).card≤2+(deep D).card := by
    rcases adjacent_singleton_thirteen_even_profile hc ab even conn degree sd cover one d13 with
      ⟨_,_,_,i,j⟩|⟨v,_,_,_,_,_⟩
    · exact ⟨i,j⟩
    omega
  by_cases low : (nearBal D).card≤1
  · exact traceable_of_adjacent_singleton_thirteen_five_at_most_one_balance hc ab even conn degree
      sd cover one d13 v5 low
  by_cases two : (nearBal D).card=2
  · by_cases dz : (deep D).card=0
    · exact traceable_of_adjacent_singleton_thirteen_five_two_balanced_no_deep hc ab even conn degree
        sd cover one d13 v5 two dz
    have d1 : (deep D).card=1 := by omega
    exact traceable_of_adjacent_singleton_thirteen_five_two_balanced_with_deep hc ab even conn degree
      sd cover one d13 v5 two d1
  have three : (nearBal D).card=3 := by omega
  exact traceable_of_adjacent_singleton_thirteen_five_three_balanced_dark_dense hc ab even conn degree
    sd cover one d13 v5 three (exception three)

#print axioms traceable_of_adjacent_singleton_thirteen_five_unless_three_sparse
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
