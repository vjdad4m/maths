import AdjacentCutFiveThreeSingletonClose189
import AdjacentCutFiveThreeNonSingleton189
import AdjacentCutFiveThreeFourCommon189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_nonempty from AdjacentCutFiveActual189
open private degree_le_shore_add_one from AdjacentCutFiveComponents189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem exists_high_shore_five_to_seven_of_three_at_adjacent_cut (hc : G.Connected)
    (ab : G.Adj a b) (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (three : Nat.card (CutGraph (G := G) a b).ConnectedComponent = 3) :
    ∃ C : (CutGraph (G := G) a b).ConnectedComponent,
      5 ≤ (Shore C).card ∧ (Shore C).card ≤ 7 ∧ ∀ z∈Shore C,5 ≤ G.degree z := by
  classical
  have noSingleton := three_components_no_singleton_at_adjacent_cut hc ab even conn degree three
  obtain ⟨D,four,seven,high⟩ :=
    exists_small_high_shore_of_three_no_singleton hc ab even conn degree three noSingleton
  have allFour (C : (CutGraph (G:=G) a b).ConnectedComponent) : 4≤(Shore C).card := by
    obtain ⟨x,xc⟩ := shore_nonempty C
    have Cpos := card_pos.mpr (shore_nonempty C)
    have n1 := noSingleton C
    have k := card_erase_add_one xc
    obtain ⟨y,ym⟩ : ((Shore C).erase x).Nonempty := card_pos.mp (by omega)
    rcases degree y x (mem_erase.mp ym).1 with dy|dx
    · have h := degree_le_shore_add_one C (mem_erase.mp ym).2
      omega
    · have h := degree_le_shore_add_one C xc
      omega
  refine ⟨D,?_,seven,high⟩
  by_cases large : 5≤(Shore D).card
  · exact large
  · exfalso
    have d4 : (Shore D).card=4 := by omega
    let J := CutGraph (G := G) a b
    haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
    letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
    change Nat.card J.ConnectedComponent = 3 at three
    rw [Nat.card_eq_fintype_card] at three
    let T : Finset J.ConnectedComponent := univ.erase D
    have t2 : T.card=2 := by simp [T,three]
    obtain ⟨C,E,ce,tEq⟩ := card_eq_two.mp t2
    have cd : C≠D := (mem_erase.mp (show C∈T by simp [tEq])).1
    have ed : E≠D := (mem_erase.mp (show E∈T by simp [tEq])).1
    exact four_common_shore_impossible_with_two_other_large_shores hc ab even conn degree
      cd.symm ed.symm ce d4 high (allFour C) (allFour E)

#print axioms exists_high_shore_five_to_seven_of_three_at_adjacent_cut
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
