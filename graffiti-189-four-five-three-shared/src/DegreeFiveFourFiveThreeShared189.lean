import DegreeFiveNearPortEight189
import DegreeFiveFourThreeTerminal189
import DegreeFiveBothFourFiveFifteenClose189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off shore_closed shore_disjoint shore_connected shore_hit_a shore_hit_b
  from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff common_sub_ports from DegreeFiveBothFiveResidual189
open private shores_add_two_le_graph_order from DegreeFiveBothFourFiveFifteenClose189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Both-common (4,5) is traceable throughout the range when the
four-port shore has at least three common contacts. -/
theorem four_five_at_least_three_shared_masks
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C4 : (cutPorts C).card=4) (D5 : (cutPorts D).card=5)
    (shared : 3≤(sharedPortSet C).card)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    ComplementaryWings G a b (Shore C) (Shore D) := by

  classical
  have cLower : 4≤(cutPorts C).card := by omega
  have dLower : 4≤(cutPorts D).card := by omega
  have nUpper := both_common_nonsaturated_order_le_fifteen hc two even conn cd cover
    cLower dLower (.inl C4) xc ax bx yd ay by'
  by_cases n15 : Fintype.card V=15
  · obtain ⟨term,free,_⟩ := four_five_order_fifteen_masks hc two even conn degree cd cover
      C4 D5 n15 xc ax bx yd ay by'
    exact .inl ⟨term,.inl free⟩
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  have sum := shores_add_two_le_graph_order ab cd
  have c4 : 4≤(Shore C).card := by rw [←C4]; exact card_le_card (filter_subset _ _)
  have d5 : 5≤(Shore D).card := by rw [←D5]; exact card_le_card (filter_subset _ _)
  have cUniv (u : V) (uk : u∈sharedPortSet C) : ∀ w∈Shore C,u≠w → G.Adj u w := by
    obtain ⟨uc,au,bu⟩ := mem_filter.mp uk
    exact common_universal_in_shore_at_five hc even cd uc au bu D5
  have cCap := card_le_card (common_sub_ports C)
  have terminal : WingRealizes G a b (Shore C) .terminal := by
    by_cases k4 : (sharedPortSet C).card=4
    · have pure : sharedPortSet C=cutPorts C :=
        eq_of_subset_of_card_le (common_sub_ports C) (by omega)
      exact terminal_mask_at_four_universal_common_ports degree C4 pure (by omega) cUniv
    have k3 : (sharedPortSet C).card=3 := by omega
    exact terminal_mask_at_four_ports_three_shared_short degree C4 k3 (by omega) cUniv
  have cross {u v : V} (uc : u∈Shore C) (vd : v∈Shore D) : ¬G.Adj u v := by
    intro e
    rcases shore_closed C u uc v e with rfl|rfl|vC
    · exact (shore_off D).1 vd
    · exact (shore_off D).2 vd
    exact disjoint_left.mp (shore_disjoint cd) vC vd
  let T : Split G a b := ⟨Shore D,Shore C,shore_disjoint cd.symm,shore_off D,shore_off C,
    shore_connected D,(fun _ vd _ uc e=>cross uc vd e.symm),shore_hit_a ab conn D,shore_hit_b ab conn D,
    (fun z=>(cover z).imp id (fun h=>h.imp id Or.symm))⟩
  have near (u : V) (uk : u∈sharedPortSet D) :
      (secondShore D u).card≤1 ∧ ∀ w∈Shore D,G.dist u w≤2 := by
    obtain ⟨ud,au,bu⟩ := mem_filter.mp uk
    exact Split.Five.near_universal_at_four_foreign T hc even conn ud au bu cLower
  obtain ⟨r,rp,t,path⟩ := port_rooted_of_near_shore_at_most_eight hc degree d5 (by omega)
    (by omega) near
  rcases (cut_mem_iff.mp rp).2 with ar|br
  · exact .inl ⟨terminal,.inl ⟨r,t,ar,path⟩⟩
  exact .inl ⟨terminal,.inr ⟨r,t,br,path⟩⟩

#print axioms four_five_at_least_three_shared_masks
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
