import AdjacentCutFiveThreeReduction189
import AdjacentCutFiveSortedCombinator189
import AdjacentCutFiveShort46189
import AdjacentCutFiveShort47189
import AdjacentCutFiveShort56189
import AdjacentCutFiveShort57189
import AdjacentCutFiveCompact555189
namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
theorem sorted_profile_exclusion : SortedProfileExclusion :=
  open Graffiti189AdjacentThreeProfile in
  exact_sorted_arithmetic_from_checker shortTest sound_short_test short46 short47 short56 short57 no_555

open SimpleGraph Finset
open private CutGraph from AdjacentCutFiveActual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem three_components_impossible_at_adjacent_cut (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (three : Nat.card (CutGraph (G := G) a b).ConnectedComponent = 3) : False :=
  three_components_impossible_at_adjacent_cut_of_profile_exclusion sorted_profile_exclusion hc ab even conn degree three

theorem component_card_le_two_at_adjacent_cut (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y) :
    Nat.card (CutGraph (G := G) a b).ConnectedComponent≤2 :=
  component_card_le_two_at_adjacent_cut_of_profile_exclusion sorted_profile_exclusion hc ab even conn degree

theorem component_card_eq_two_at_genuine_adjacent_cut (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (cut : 2≤Nat.card (CutGraph (G := G) a b).ConnectedComponent) :
    Nat.card (CutGraph (G := G) a b).ConnectedComponent=2 :=
  le_antisymm (component_card_le_two_at_adjacent_cut hc ab even conn degree) cut

#print axioms sorted_profile_exclusion
#print axioms three_components_impossible_at_adjacent_cut
#print axioms component_card_le_two_at_adjacent_cut
#print axioms component_card_eq_two_at_genuine_adjacent_cut
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
