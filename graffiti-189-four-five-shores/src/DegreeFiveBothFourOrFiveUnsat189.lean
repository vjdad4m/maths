import DegreeFiveBothFourFourAll189
import DegreeFiveBothFourFiveAll189


namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off shore_closed shore_disjoint shore_connected shore_hit_a shore_hit_b
  from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff residue residue_count residual_neighbor_bound from DegreeFiveBothFiveResidual189
open private shores_add_two_le_graph_order from DegreeFiveBothFourFiveFifteenClose189




variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Both-common distance-two cuts with at least four contacts per
shore and with one unsaturated shore are traceable. -/
theorem traceable_of_both_common_four_or_five_ports_one_four
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C4 : (cutPorts C).card=4) (D4 : 4≤(cutPorts D).card)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    ∃ r t : V,∃ q : G.Walk r t,q.IsPath ∧ ∀ p,p∈q.support := by
  classical
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  have dUpper := foreign_ports_le_five_at_common hc even xc ax bx
    (T:=({D} : Finset (Cmp (G:=G) (a:=a) (b:=b)))) (by simpa using cd)
  rw [sum_singleton] at dUpper
  apply traceable_of_complementary_wings ab (shore_disjoint cd) (shore_off C).1 (shore_off C).2
    (shore_off D).1 (shore_off D).2 cover
  by_cases d5 : (cutPorts D).card=5
  · exact four_five_both_common_masks hc two even conn degree cd cover C4 d5 xc ax bx yd ay by'
  have d4 : (cutPorts D).card=4 := by omega
  exact four_four_both_common_masks hc two even conn degree cd cover C4 d4 xc ax bx yd ay by'

#print axioms traceable_of_both_common_four_or_five_ports_one_four
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
