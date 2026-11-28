import DegreeFiveThreeThreeVisTwo189






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

open private firstDark firstDark_iff_distance_three dark_dist_ge_three cross_ports_at_distance_two
  distance_two_at_cut_lower from DegreeFiveTwoThreeVisTwo189
open private visible_at_least_two_of_dark from DegreeFiveTwoThreeBase189

private theorem order_four_of_one_visible
    (hc : G.Connected)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (C3 : (cutPorts C).card=3) (allC : ∀ z∈cutPorts C,G.Adj a z)
    (one : (secondShore C a).card=1) :
    (Shore C).card=4 ∧ ∃ x∈Shore C,¬5≤G.degree x := by
  classical
  have no : dark C=∅ := by
    apply card_eq_zero.mp
    apply Classical.byContradiction
    intro h
    have t := visible_at_least_two_of_dark hc conn allC (card_pos.mp (by omega))
    omega
  have h := card_sdiff_add_card_eq_card (visible_in_nonports allC)
  change (dark C).card+(secondShore C a).card=(Shore C\cutPorts C).card at h
  rw [no,card_empty,one] at h
  have h' : (Shore C\cutPorts C).card+(cutPorts C).card=(Shore C).card :=
    card_sdiff_add_card_eq_card (filter_subset _ _)
  have d4 : (Shore C).card=4 := by omega
  obtain ⟨x,xA⟩ := card_pos.mp (show 0<(secondShore C a).card by omega)
  obtain ⟨xc,xp⟩ := mem_sdiff.mp (visible_in_nonports allC xA)
  have q := nonport_degree_bound_small xc xp
  exact ⟨d4,x,xc,by omega⟩

theorem three_three_universal_cut_shape
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (C3 : (cutPorts C).card=3) (D3 : (cutPorts D).card=3)
    (allC : ∀ z∈cutPorts C,G.Adj a z) (allD : ∀ z∈cutPorts D,G.Adj a z) :
    ((Shore C).card=4 ∧ (secondShore D a).card=3 ∧ ∀ z∈Shore D,5≤G.degree z) ∨
    ((Shore D).card=4 ∧ (secondShore C a).card=3 ∧ ∀ z∈Shore C,5≤G.degree z) := by
  classical
  have ab : a≠b := by intro h; rw [h,dist_self] at two; omega
  have pos (X : Cmp (G:=G) (a:=a) (b:=b)) (x3 : (cutPorts X).card=3) :
      1≤(secondShore X a).card := by
    have b := card_le_card (show cutPorts X⊆Shore X from filter_subset _ _)
    have g := four_in_nonsingleton degree (show 2≤(Shore X).card by omega)
    exact second_positive_of_small_ports (shore_off X).1 (shore_hit_a ab conn X)
      hc g (by omega) (.inl rfl)
  have cp := pos C C3
  have dp := pos D D3
  have l := distance_two_at_cut_lower two cd
  have h := distanceTwo_le_of_even 5 a (even a)
  have sides (X Y : Cmp (G:=G) (a:=a) (b:=b)) (neq : X≠Y)
      (x3 : (cutPorts X).card=3) (y3 : (cutPorts Y).card=3)
      (xall : ∀ z∈cutPorts X,G.Adj a z) (yall : ∀ z∈cutPorts Y,G.Adj a z)
      (x1 : (secondShore X a).card=1) :
      (Shore X).card=4 ∧ (secondShore Y a).card=3 ∧ ∀ z∈Shore Y,5≤G.degree z := by
    obtain ⟨sz,u,ux,low⟩ := order_four_of_one_visible hc conn x3 xall x1
    have high (z : V) (zy : z∈Shore Y) : 5≤G.degree z :=
      (degree u z (fun e=>disjoint_left.mp (shore_disjoint neq) ux (e.symm ▸ zy))).resolve_left low
    have xPos := pos X x3
    have yPos := pos Y y3
    have lt := distance_two_at_cut_lower two neq
    have v1 : (secondShore Y a).card≠1 := by
      intro h
      obtain ⟨_,v,vy,low⟩ := order_four_of_one_visible hc conn y3 yall h
      exact low (high v vy)
    have v2 : (secondShore Y a).card≠2 := fun v2=>
      no_two_visible_on_all_high_three_port_shore hc two even conn degree neq.symm y3 x3
        yall xall xPos v2 high
    exact ⟨sz,by omega,high⟩
  by_cases c1 : (secondShore C a).card=1
  · exact .inl (sides C D cd C3 D3 allC allD c1)
  by_cases d1 : (secondShore D a).card=1
  · exact .inr (sides D C cd.symm D3 C3 allD allC d1)
  have c2 : (secondShore C a).card=2 := by omega
  have d2 : (secondShore D a).card=2 := by omega
  by_cases cH : ∀ u∈Shore C,5≤G.degree u
  · exact (no_two_visible_on_all_high_three_port_shore hc two even conn degree cd C3 D3 allC allD dp c2 cH).elim
  push_neg at cH
  obtain ⟨u,uc,ul⟩ := cH
  have dH (v : V) (vd : v∈Shore D) : 5≤G.degree v :=
    (degree u v (fun e=>disjoint_left.mp (shore_disjoint cd) uc (e.symm ▸ vd))).resolve_left (by omega)
  exact (no_two_visible_on_all_high_three_port_shore hc two even conn degree cd.symm D3 C3 allD allC cp d2 dH).elim

#print axioms three_three_universal_cut_shape
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
