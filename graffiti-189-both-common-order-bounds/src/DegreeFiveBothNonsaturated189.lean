import DegreeFivePureShoreVisible189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off shore_closed shore_disjoint shore_connected shore_hit_a shore_hit_b
  from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor two_shore_budget from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff common_sub_ports from DegreeFiveBothFiveResidual189
open private common_side_color_cover from DegreeFiveBothAtLeastFour189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem graph_order_le_shores_add_two
    {C D : Cmp (G:=G) (a:=a) (b:=b)}
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D) :
    Fintype.card V≤(Shore C).card+(Shore D).card+2 := by
  classical
  let U := Shore C∪Shore D
  have cv : (univ : Finset V)⊆insert a (insert b U) := by
    intro z _
    rcases cover z with rfl|rfl|zc|zd
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_insert_self _ _)
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ zc))
    exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ zd))
  have uCap : U.card≤(Shore C).card+(Shore D).card := card_union_le _ _
  have q := (card_le_card cv).trans (card_insert_le _ _)
  have r := card_insert_le b U
  rw [card_univ] at q
  omega

private theorem at_most_fifteen_when_first_four
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C4 : (cutPorts C).card=4) (D4 : 4≤(cutPorts D).card)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    Fintype.card V≤15 := by
  classical
  apply Classical.byContradiction
  intro fail
  have h4 : 4≤(cutPorts C).card := le_of_eq C4.symm
  obtain ⟨sum,weight⟩ := both_common_order_le_sixteen_at_four_or_more_ports hc two even conn
    cd cover h4 D4 xc ax bx yd ay by'
  have cardGraph := graph_order_le_shores_add_two cover
  have s14 : (Shore C).card+(Shore D).card=14 := by omega
  have kC := card_le_card (common_sub_ports C)
  have kD := card_le_card (common_sub_ports D)
  have purity : sharedPortSet D=cutPorts D :=
    eq_of_subset_of_card_le (common_sub_ports D) (by omega)
  have pure (z : V) (zp : z∈cutPorts D) : G.Adj a z ∧ G.Adj b z := by
    have zk : z∈sharedPortSet D := purity.symm ▸ zp
    exact (mem_filter.mp zk).2
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
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
  have nearD (z : V) (zp : z∈cutPorts D) :
      (secondShore D z).card≤1 ∧ ∀ w∈Shore D,G.dist z w≤2 :=
    Split.Five.near_universal_at_four_foreign T hc even conn (cut_mem_iff.mp zp).1
      (pure z zp).1 (pure z zp).2 h4
  have visible := pure_shore_visible_from_first_cut hc two even cd h4 D4 pure nearD
  have dcap := (card_le_card visible).trans (card_union_le _ _)
  have nearC := (Split.Five.near_universal_at_four_foreign S hc even conn xc ax bx D4).2
  have ccap := common_side_color_cover hc nearC ax (shore_off C).1
  have foreign : cutPorts D⊆DistanceTwo G x := by
    intro z zp
    obtain ⟨zd,hit⟩ := cut_mem_iff.mp zp
    have ne : x≠z := fun e=>disjoint_left.mp (shore_disjoint cd) xc (e.symm ▸ zd)
    exact hit.elim (fun h=>d2 hc ne (cross xc zd) ax.symm h)
      (fun h=>d2 hc ne (cross xc zd) bx.symm h)
  have dis : Disjoint (secondShore C x) (cutPorts D) :=
    (shore_disjoint cd).mono inter_subset_left (filter_subset _ _)
  have q := (card_le_card (union_subset
    (show secondShore C x⊆DistanceTwo G x from inter_subset_right) foreign)).trans
      (distanceTwo_le_of_even 5 x (even x))
  rw [card_union_of_disjoint dis] at q
  have a2 := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
  have colors : portColor C a⊆cutPorts C := fun z zp=>
    cut_mem_iff.mpr ⟨(mem_filter.mp zp).1,.inl (mem_filter.mp zp).2⟩
  have c4 := card_le_card colors
  omega

/-- At least four ports on both common shores gives order at most sixteen.
If either port total is four, equality is impossible: equality forces pure
common contacts, and the corresponding near-universal shore has no hidden
nonport with which to use the last order slot. -/
theorem both_common_nonsaturated_order_le_fifteen
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C4 : 4≤(cutPorts C).card) (D4 : 4≤(cutPorts D).card)
    (nonsaturated : (cutPorts C).card=4 ∨ (cutPorts D).card=4)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    Fintype.card V≤15 := by
  rcases nonsaturated with c4|d4
  · exact at_most_fifteen_when_first_four hc two even conn cd cover c4 D4 xc ax bx yd ay by'
  have cover' (z : V) : z=a ∨ z=b ∨ z∈Shore D ∨ z∈Shore C :=
    (cover z).imp id (fun h=>h.imp id Or.symm)
  exact at_most_fifteen_when_first_four hc two even conn cd.symm cover' d4 C4 yd ay by' xc ax bx

#print axioms both_common_nonsaturated_order_le_fifteen
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
