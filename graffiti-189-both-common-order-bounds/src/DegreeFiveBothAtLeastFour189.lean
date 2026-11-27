import DegreeFiveBothFiveCounts189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off shore_closed shore_disjoint shore_connected shore_hit_a shore_hit_b
  from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor two_shore_budget from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem common_side_color_cover
    (hc : G.Connected) {C : Cmp (G:=G) (a:=a) (b:=b)} {x : V}
    (near : ∀ w∈Shore C,G.dist x w≤2)
    {c : V} (cx : G.Adj c x) (co : c∉Shore C) :
    (Shore C).card≤(portColor C c).card+(secondShore C c).card+(secondShore C x).card := by
  classical
  let A := portColor C c
  let B := secondShore C c
  let X := secondShore C x
  have sub : Shore C⊆(A∪B)∪X := by
    intro w wc
    by_cases cw : G.Adj c w
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨wc,cw⟩))
    have xw : x≠w := fun h=>cw (h ▸ cx)
    by_cases adj : G.Adj x w
    · have ne : c≠w := fun h=>co (h.symm ▸ wc)
      exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨wc,d2 hc ne cw cx adj⟩))
    have lo := hc.one_lt_dist_of_ne_of_not_adj xw adj
    have hi := near w wc
    exact mem_union_right _ (mem_inter.mpr ⟨wc,by simp [DistanceTwo,show G.dist x w=2 by omega]⟩)
  have first := (card_le_card sub).trans (card_union_le _ _)
  have second := card_union_le A B
  change (Shore C).card≤A.card+B.card+X.card
  omega

/-- When both shores have common porters and at least four total ports,
the two-side order cut-off sixteen does not require saturation at five. -/
theorem both_common_order_le_sixteen_at_four_or_more_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C4 : 4≤(cutPorts C).card) (D4 : 4≤(cutPorts D).card)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    (Shore C).card+(Shore D).card≤14 ∧
    2*((Shore C).card+(Shore D).card)+(cutPorts C).card+(cutPorts D).card ≤
      28+(sharedPortSet C).card+(sharedPortSet D).card := by
  classical
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
  have xNear := (Split.Five.near_universal_at_four_foreign S hc even conn xc ax bx D4).2
  have yNear := (Split.Five.near_universal_at_four_foreign T hc even conn yd ay by' C4).2
  have xCover (z : V) (zc : z∈Shore C) : G.dist x z≤2 := xNear z zc
  have yCover (z : V) (zd : z∈Shore D) : G.dist y z≤2 := yNear z zd
  have q (c : V) (ac : G.Adj a c) (bc : G.Adj b c)
      {U W : Cmp (G:=G) (a:=a) (b:=b)} (uw : U≠W)
      (uc : c∈Shore U) (cross' : ∀ w∈Shore W,¬G.Adj c w) :
      (secondShore U c).card+(cutPorts W).card≤5 := by
    have far : cutPorts W⊆DistanceTwo G c := by
      intro z zz
      obtain ⟨zw,hit⟩ := mem_filter.mp zz
      have ne : c≠z := fun e=>disjoint_left.mp (shore_disjoint uw) uc (e.symm ▸ zw)
      exact hit.elim (fun h=>d2 hc ne (cross' z zw) ac.symm h)
        (fun h=>d2 hc ne (cross' z zw) bc.symm h)
    have d : Disjoint (secondShore U c) (cutPorts W) :=
      (shore_disjoint uw).mono inter_subset_left (filter_subset _ _)
    have h := (card_le_card (union_subset
      (show secondShore U c⊆DistanceTwo G c from inter_subset_right) far)).trans
      (distanceTwo_le_of_even 5 c (even c))
    rwa [card_union_of_disjoint d] at h
  have xx := q x ax bx cd xc (fun _ z=>cross xc z)
  have yy := q y ay by' cd.symm yd (fun _ z e=>cross z yd e.symm)
  have xa := common_side_color_cover hc xCover ax (shore_off C).1
  have xb := common_side_color_cover hc xCover bx (shore_off C).2
  have ya := common_side_color_cover hc yCover ay (shore_off D).1
  have yb := common_side_color_cover hc yCover by' (shore_off D).2
  have ba : G.dist b a=2 := by rwa [SimpleGraph.dist_comm]
  have aa := two_shore_budget cd ⟨(shore_off C).2,(shore_off D).2⟩ two even
  have bb := two_shore_budget cd ⟨(shore_off C).1,(shore_off D).1⟩ ba even
  have tally (U : Cmp (G:=G) (a:=a) (b:=b)) :
      (portColor U a).card+(portColor U b).card=(cutPorts U).card+(sharedPortSet U).card := by
    have h := card_union_add_card_inter (portColor U a) (portColor U b)
    have u : portColor U a∪portColor U b=cutPorts U := by
      ext z
      simp [portColor,cutPorts,and_or_left]
    have i : portColor U a∩portColor U b=sharedPortSet U := by
      ext z
      simp [portColor,sharedPortSet,and_assoc,and_left_comm]
    rw [u,i] at h
    exact h.symm
  have hC := tally C
  have hD := tally D
  have atop (U : Cmp (G:=G) (a:=a) (b:=b)) : (portColor U a).card≤(cutPorts U).card :=
    card_le_card (fun _ wm=>mem_filter.mpr ⟨(mem_filter.mp wm).1,.inl (mem_filter.mp wm).2⟩)
  have aC := atop C
  have aD := atop D
  constructor <;> omega

theorem graph_order_le_sixteen_of_both_common_four_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C4 : 4≤(cutPorts C).card) (D4 : 4≤(cutPorts D).card)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    Fintype.card V≤16 := by
  classical
  have cap := (both_common_order_le_sixteen_at_four_or_more_ports hc two even conn cd cover
    C4 D4 xc ax bx yd ay by').1
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

#print axioms both_common_order_le_sixteen_at_four_or_more_ports
#print axioms graph_order_le_sixteen_of_both_common_four_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
