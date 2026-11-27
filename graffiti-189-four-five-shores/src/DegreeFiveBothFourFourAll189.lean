import DegreeFiveFourFourTerminal189
import DegreeFiveBothFourteen189
import DegreeFiveBothFourFiveFifteenClose189


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

/-- Four ports on each shore, both with a common neighbor of the two
cut vertices: the graph has complementary spanning wings. -/
theorem four_four_both_common_masks
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C4 : (cutPorts C).card=4) (D4 : (cutPorts D).card=4)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    ComplementaryWings G a b (Shore C) (Shore D) := by

  classical
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  have nUpper := both_common_four_four_order_le_fourteen hc two even conn cd cover C4 D4 xc ax bx yd ay by'
  have sum := shores_add_two_le_graph_order ab cd
  have c4 : 4≤(Shore C).card := by rw [←C4]; exact card_le_card (filter_subset _ _)
  have d4 : 4≤(Shore D).card := by rw [←D4]; exact card_le_card (filter_subset _ _)
  have cross {u v : V} (uc : u∈Shore C) (vd : v∈Shore D) : ¬G.Adj u v := by
    intro e
    rcases shore_closed C u uc v e with rfl|rfl|vC
    · exact (shore_off D).1 vd
    · exact (shore_off D).2 vd
    exact disjoint_left.mp (shore_disjoint cd) vC vd
  let S : Split G a b := ⟨Shore C,Shore D,shore_disjoint cd,shore_off C,shore_off D,
    shore_connected C,(fun _ uc _ vd=>cross uc vd),shore_hit_a ab conn C,shore_hit_b ab conn C,cover⟩
  let T : Split G a b := ⟨Shore D,Shore C,shore_disjoint cd.symm,shore_off D,shore_off C,
    shore_connected D,(fun _ vd _ uc e=>cross uc vd e.symm),shore_hit_a ab conn D,shore_hit_b ab conn D,
    (fun z=>(cover z).imp id (fun h=>h.imp id Or.symm))⟩
  have nearC (u : V) (uk : u∈sharedPortSet C) :
      (secondShore C u).card≤1 ∧ ∀ w∈Shore C,G.dist u w≤2 := by
    obtain ⟨uc,au,bu⟩ := mem_filter.mp uk
    exact Split.Five.near_universal_at_four_foreign S hc even conn uc au bu (show 4≤(cutPorts D).card by omega)
  have nearD (u : V) (uk : u∈sharedPortSet D) :
      (secondShore D u).card≤1 ∧ ∀ w∈Shore D,G.dist u w≤2 := by
    obtain ⟨ud,au,bu⟩ := mem_filter.mp uk
    exact Split.Five.near_universal_at_four_foreign T hc even conn ud au bu (show 4≤(cutPorts C).card by omega)
  have free (H : Cmp (G:=G) (a:=a) (b:=b)) (h4 : (cutPorts H).card=4) (small : (Shore H).card≤8)
      (near : ∀ u∈sharedPortSet H,(secondShore H u).card≤1 ∧ ∀ w∈Shore H,G.dist u w≤2) :
      WingRealizes G a b (Shore H) .aFree ∨ WingRealizes G a b (Shore H) .bFree := by
    by_cases hSmall : (Shore H).card=4
    · obtain ⟨r,t,ar,_,p⟩ := terminal_mask_of_very_small_four_port_shore degree h4 hSmall
      exact .inl ⟨r,t,ar,p⟩
    have sub : (cutPorts H).card≤(Shore H).card := card_le_card (filter_subset _ _)
    obtain ⟨r,rp,t,path⟩ := port_rooted_of_near_shore_at_most_eight hc degree (by omega) small
      (show 3≤(cutPorts H).card by omega) near
    rcases (cut_mem_iff.mp rp).2 with ar|br
    · exact .inl ⟨r,t,ar,path⟩
    exact .inr ⟨r,t,br,path⟩
  have cf := free C C4 (by omega) nearC
  have df := free D D4 (by omega) nearD
  by_cases cLow : ∃ u∈Shore C,¬5≤G.degree u
  · obtain ⟨u,uc,ul⟩ := cLow
    by_cases small : (Shore D).card≤7
    · have high (v : V) (vd : v∈Shore D) : 5≤G.degree v :=
        (degree u v (fun e=>(disjoint_left.mp (shore_disjoint cd) uc (e.symm ▸ vd)))).resolve_left ul
      exact .inr ⟨terminal_mask_of_high_four_port_shore hc D4 small high nearD yd ay by',cf⟩
    exact .inl ⟨terminal_mask_of_very_small_four_port_shore degree C4 (by omega),df⟩
  by_cases small : (Shore C).card≤7
  · have high (u : V) (uc : u∈Shore C) : 5≤G.degree u :=
      Classical.byContradiction (fun n=>cLow ⟨u,uc,n⟩)
    exact .inl ⟨terminal_mask_of_high_four_port_shore hc C4 small high nearC xc ax bx,df⟩
  exact .inr ⟨terminal_mask_of_very_small_four_port_shore degree D4 (by omega),cf⟩

#print axioms four_four_both_common_masks
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
