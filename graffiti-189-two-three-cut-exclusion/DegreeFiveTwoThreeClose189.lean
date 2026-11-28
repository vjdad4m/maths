import DegreeFiveTwoThreeVisThree189
import DegreeFiveActualCutSwap189





namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint shore_nonempty shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp two_shore_budget count_cut_degree_on_two_shores portColor from DegreeFiveThreeForeignImpossible189
open private four_in_nonsingleton second_positive_of_small_ports anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private nonport_neighbors_subset nonport_degree_bound_small from DegreeFiveThreeFiveShapes189
open private nonport_mem_second_iff_neighbor_port from DegreeFiveOneFiveFarProfile189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

open private boundary_has_at_least_two dark dark_boundary_is_visible visible_in_nonports
  from DegreeFiveTwoThreeBase189

open private cut_a_touches_all_at_two_three two_port_shore_size_at_least_six
  visible_at_least_two_of_dark from DegreeFiveTwoThreeBase189
open private distance_two_at_cut_lower from DegreeFiveTwoThreeVisTwo189
open private swapCut from DegreeFiveActualCutSwap189

private theorem impossible_two_three_when_first_high
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C2 : (cutPorts C).card=2) (D3 : (cutPorts D).card=3)
    (high : 5≤G.degree a) : False := by
  classical
  have ab : a≠b := by intro h; rw [h,dist_self] at two; omega
  have ⟨cAll,dAll⟩ := cut_a_touches_all_at_two_three two cd cover C2 D3 high
  have c6 := two_port_shore_size_at_least_six degree C2
  have dP : (cutPorts D).card≤(Shore D).card := card_le_card (filter_subset _ _)
  have d4 := four_in_nonsingleton degree (show 2≤(Shore D).card by omega)
  have dPos := second_positive_of_small_ports (shore_off D).1 (shore_hit_a ab conn D) hc d4
    (show (cutPorts D).card≤3 by omega) (.inl rfl)
  have tally := distance_two_at_cut_lower two cd
  have acap := distanceTwo_le_of_even 5 a (even a)
  have F : (dark C).card+(secondShore C a).card+(cutPorts C).card=(Shore C).card := by
    have left := card_sdiff_add_card_eq_card (visible_in_nonports cAll)
    have right := card_sdiff_add_card_eq_card (show cutPorts C⊆Shore C from filter_subset _ _)
    change (dark C).card+(secondShore C a).card=(Shore C\cutPorts C).card at left
    omega
  have qPos : (dark C).Nonempty := card_pos.mp (by omega)
  have a2 := visible_at_least_two_of_dark hc conn cAll qPos
  by_cases h : (secondShore C a).card=2
  · exact no_two_visible_on_two_port_shore hc two even conn degree cd C2 D3 cAll dAll dPos (by omega) h
  exact no_three_visible_on_two_port_shore hc two even conn degree cd C2 D3 cAll dAll dPos qPos (by omega)

/-- No degree-five candidate graph admits an actual distance-two
two-component cut with two total contacts on one shore and three on
the other. Common contacts need not be assumed. -/
theorem impossible_actual_five_two_three_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C2 : (cutPorts C).card=2) (D3 : (cutPorts D).card=3) : False := by
  classical
  have ab : a≠b := by intro h; rw [h,dist_self] at two; omega
  rcases degree a b ab with ha|hb
  · exact impossible_two_three_when_first_high hc two even conn degree cd cover C2 D3 ha
  let X := swapCut C
  let Y := swapCut D
  have eqC : Shore X=Shore C := shore_swapCut C
  have eqD : Shore Y=Shore D := shore_swapCut D
  have px : cutPorts X=cutPorts C := by simp [cutPorts,eqC,or_comm]
  have py : cutPorts Y=cutPorts D := by simp [cutPorts,eqD,or_comm]
  have noneq : X≠Y := fun h=>cd (swapCut.injective h)
  have cf : ∀ z : V,z=b ∨ z=a ∨ z∈Shore X ∨ z∈Shore Y := by
    intro z
    rw [eqC,eqD]
    rcases cover z with h|h|h|h
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr (.inl h))
    exact .inr (.inr (.inr h))
  have two' : G.dist b a=2 := by rwa [dist_comm]
  exact impossible_two_three_when_first_high hc two' even conn degree noneq cf
    (by rwa [px]) (by rwa [py]) hb

#print axioms impossible_actual_five_two_three_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
