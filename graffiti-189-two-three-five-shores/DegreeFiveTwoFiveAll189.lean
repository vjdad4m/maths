import DegreeFiveOppositeFiveDoubleCharge189
import DegreeFiveTwoOrThreeTerminal189
import DegreeFiveNearAllPortTerminal189


namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private four_in_nonsingleton from DegreeFiveDistanceTwoThreeClose189
open private nonport_degree_bound_small from DegreeFiveThreeFiveShapes189
open private shores_add_two_le_graph_order from DegreeFiveBothFourFiveFifteenClose189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Opposite five-port saturation forces the (2,5) profiles to be the
six- and five-vertex shores. Both admit the required terminal/free masks. -/
theorem traceable_of_actual_five_two_five_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C2 : (cutPorts C).card=2) (D5 : (cutPorts D).card=5)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    ∃ r t : V,∃ q : G.Walk r t,q.IsPath ∧ ∀ p,p∈q.support := by
  classical
  have ab : a≠b := by intro e; rw [e,dist_self] at two; omega
  have ub := opposite_five_order_bound_by_double_charges hc two even cd cover D5 xc ax bx
  rw [C2] at ub
  have lb := shores_add_two_le_graph_order ab cd
  have cs : 4≤(Shore C).card := four_in_nonsingleton degree
    (C2 ▸ (card_le_card (show cutPorts C⊆Shore C from filter_subset _ _)))
  have ds : 5≤(Shore D).card := D5 ▸ (card_le_card (show cutPorts D⊆Shore D from filter_subset _ _))
  let E := Shore C \ cutPorts C
  have es : E.card+2=(Shore C).card := by
    have h : E.card+(cutPorts C).card=(Shore C).card :=
      card_sdiff_add_card_eq_card (filter_subset _ _)
    rwa [C2] at h
  have c6 : (Shore C).card=6 := by
    apply Classical.byContradiction
    intro e
    have small : (Shore C).card≤5 := by omega
    obtain ⟨u,ue,v,ve,uv⟩ := one_lt_card.mp (show 1<E.card by omega)
    obtain ⟨uc,un⟩ := mem_sdiff.mp ue
    obtain ⟨vc,vn⟩ := mem_sdiff.mp ve
    have p := nonport_degree_bound_small uc un
    have q := nonport_degree_bound_small vc vn
    exact (degree u v uv).elim (fun h=>by omega) (fun h=>by omega)
  have d5 : (Shore D).card=5 := by omega
  have cTerm := terminal_route_on_two_or_three_port_small_shore hc even degree cd
    (show 2≤(cutPorts C).card by omega) (show (cutPorts C).card≤3 by omega) D5 (.inr c6) xc ax bx
  obtain ⟨r,t,ar,bt,p⟩ := terminal_mask_of_five_vertex_all_port_shore degree D5 d5 yd ay by'
  exact traceable_of_complementary_wings ab (shore_disjoint cd) (shore_off C).1 (shore_off C).2
    (shore_off D).1 (shore_off D).2 cover (.inl ⟨cTerm,.inl ⟨r,t,ar,p⟩⟩)

#print axioms traceable_of_actual_five_two_five_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
