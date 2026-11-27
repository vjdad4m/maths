import DegreeFiveNearSixTerm189
import DegreeFiveFreeOreSmallNear189
import DegreeFiveFourFourTerminal189


namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- The exact both-common degree-five distance-two (2,4) profile is
traceable; no finite graph enumeration is used. -/
theorem traceable_of_actual_five_two_four_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C2 : (cutPorts C).card=2) (D4 : (cutPorts D).card=4)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    ∃ r t : V,∃ q : G.Walk r t,q.IsPath ∧ ∀ p,p∈q.support := by
  classical
  have ab : a≠b := by intro e; rw [e,dist_self] at two; omega
  have near (u : V) (uk : u∈sharedPortSet C) :
      (secondShore C u).card≤1 ∧ ∀ v∈Shore C,G.dist u v≤2 := by
    obtain ⟨uc,au,bu⟩ := mem_filter.mp uk
    exact (four_foreign_near_with_exception hc two even conn cd cover D4 uc au bu).1
  have xk : x∈sharedPortSet C := mem_filter.mpr ⟨xc,ax,bx⟩
  apply traceable_of_complementary_wings ab (shore_disjoint cd) (shore_off C).1 (shore_off C).2
    (shore_off D).1 (shore_off D).2 cover
  rcases two_four_shore_cardinality_cases hc two even conn degree cd cover C2 D4 xc ax bx with
    ⟨c6,d6⟩|⟨c7,d4⟩
  · exact .inl ⟨terminal_route_on_two_or_three_port_near_six hc degree (by omega) (by omega)
      c6 xc ax bx (near x xk),free_port_route_at_most_six degree (by omega) d6⟩
  exact .inr ⟨terminal_mask_of_very_small_four_port_shore degree D4 d4,
    free_port_route_at_near_seven hc degree (by omega) c7 near⟩

#print axioms traceable_of_actual_five_two_four_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
