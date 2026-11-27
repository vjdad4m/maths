import DegreeFiveNearSevenTerminal189
import DegreeFiveFreeOreThreeForeign189
import DegreeFiveThreeFourShapes189
import DegreeFiveFourSmallTermGeneric189
import DegreeFiveTwoFourClose189
import DegreeFiveThreeFiveAll189
import DegreeFiveNearPortEight189



namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private shores_add_two_le_graph_order from DegreeFiveBothFourFiveFifteenClose189
open private pair_deletion_min_degree_two from DegreeFiveThreeFiveAll189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff from DegreeFiveBothFiveResidual189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem traceable_of_actual_five_three_four_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C3 : (cutPorts C).card=3) (D4 : (cutPorts D).card=4)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    ∃ r t : V,∃ q : G.Walk r t,q.IsPath ∧ ∀ p,p∈q.support := by
  classical
  have ab : a≠b := by intro e; rw [e,dist_self] at two; omega
  have lb := shores_add_two_le_graph_order ab cd
  have cBound : (cutPorts C).card≤(Shore C).card := card_le_card (filter_subset _ _)
  have min2 := pair_deletion_min_degree_two (G:=G) (by omega) conn
  have near (u : V) (uk : u∈sharedPortSet C) :
      (secondShore C u).card≤1 ∧ ∀ v∈Shore C,G.dist u v≤2 := by
    obtain ⟨uc,au,bu⟩ := mem_filter.mp uk
    exact (four_foreign_near_with_exception hc two even conn cd cover D4 uc au bu).1
  have xk : x∈sharedPortSet C := mem_filter.mpr ⟨xc,ax,bx⟩
  have d2 : 2≤(cutPorts D).card := by omega
  have c2 : 2≤(cutPorts C).card := by omega
  have c3 : 3≤(cutPorts C).card := by omega
  have free8 (small : (Shore C).card≤8) (large : 5≤(Shore C).card) :
      WingRealizes G a b (Shore C) .aFree ∨ WingRealizes G a b (Shore C) .bFree := by
    obtain ⟨r,rp,t,path⟩ := port_rooted_of_near_shore_at_most_eight hc degree large small c3 near
    rcases (cut_mem_iff.mp rp).2 with ar|br
    · exact .inl ⟨r,t,ar,path⟩
    exact .inr ⟨r,t,br,path⟩
  apply traceable_of_complementary_wings ab (shore_disjoint cd) (shore_off C).1 (shore_off C).2
    (shore_off D).1 (shore_off D).2 cover
  rcases three_four_shore_cardinality_cases hc two even conn degree cd cover C3 D4 xc ax bx with
    ⟨c4,d8,dh⟩|⟨c6,d7⟩|⟨c7,s,d6⟩|⟨c8,d4⟩
  · exact .inl ⟨terminal_route_on_four_vertices_with_two_ports degree c2 c4 xc ax bx,
      free_port_route_small_shore_three_foreign hc even degree min2 cd c3 d2 (.inr ⟨d8,dh⟩)⟩
  · exact .inl ⟨terminal_route_on_two_or_three_port_near_six hc degree c2 (by omega)
      c6 xc ax bx (near x xk),free_port_route_small_shore_three_foreign hc even degree min2 cd c3 d2 d7⟩
  · rcases s with eq|no
    · exact .inr ⟨terminal_mask_of_very_small_four_port_shore degree D4 eq,free8 (by omega) (by omega)⟩
    exact .inl ⟨terminal_route_on_three_port_near_seven hc degree min2 C3 c7 near no xc ax bx,
      free_port_route_at_most_six degree d2 d6⟩
  exact .inr ⟨terminal_mask_of_very_small_four_port_shore degree D4 d4,free8 (by omega) (by omega)⟩

#print axioms traceable_of_actual_five_three_four_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
