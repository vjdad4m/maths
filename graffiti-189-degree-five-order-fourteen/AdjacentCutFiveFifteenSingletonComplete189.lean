import AdjacentCutFiveFifteenSingletonBalancedThree189
import DegreeFiveNonadjacentComplete189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore from AdjacentCutFiveActual189
open private classSet from AdjacentCutFiveTopProfiles189
open private commonFive from AdjacentCutFiveFifteenSingletonBalancedBase189
open private compact_graph_singleton_fifteen_profile from AdjacentCutFiveFifteenSingletonProfiles189
open private bal_frame_exists from AdjacentCutFiveFifteenSingletonBalancedData189
open private traceable_balanced_exactly_two_common from AdjacentCutFiveFifteenSingletonBalancedTwo189
open private balanced_exactly_three_common from AdjacentCutFiveFifteenSingletonBalancedThree189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

/-- Full order-fifteen adjacent singleton cut case at the degree-five threshold. -/
theorem traceable_of_adjacent_singleton_twelve_shores
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (one : (Shore C).card=1) (big : (Shore D).card=12) :
    ∃ x y,∃ P : G.Walk x y,P.IsPath ∧ ∀ z,z∈P.support := by
  classical
  have route (h : ∃ x y : V,x≠y ∧ ¬G.Adj x y ∧ ¬(G.induce {z : V | z≠x ∧ z≠y}).Connected) :
      ∃ x y,∃ P : G.Walk x y,P.IsPath ∧ ∀ z,z∈P.support := by
    obtain ⟨x,y,ne,no,cut⟩ := h
    exact FiveActualCut.traceable_at_actual_five_nonadjacent_cut hc ne no even conn degree cut
  rcases alternate_cut_or_balanced_of_adjacent_singleton_twelve_shores hc ab even conn degree cd cover one big with h|h
  · exact route h
  obtain ⟨s,SC,as',bs',_⟩ := compact_graph_singleton_fifteen_profile hc ab even conn degree cd one big
  have sc : s∈Shore C := by simp [SC]
  obtain ⟨ea,eb,ec,oa,ob,oc⟩ := h
  obtain ⟨F⟩ := bal_frame_exists hc ab even degree cd cover sc SC as' bs' ea eb ec oa ob oc
  have sub : commonFive D⊆classSet D 5 := filter_subset _ _
  have upper := (card_le_card sub).trans F.threeC.le
  have lower := F.commonAtLeast
  by_cases two : (commonFive D).card=2
  · exact traceable_balanced_exactly_two_common F hc ab even cd sc SC as' bs' cover two
  have three : (commonFive D).card=3 := by omega
  exact (balanced_exactly_three_common F hc ab even cd sc SC as' bs' cover three).elim route id

#print axioms traceable_of_adjacent_singleton_twelve_shores
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
