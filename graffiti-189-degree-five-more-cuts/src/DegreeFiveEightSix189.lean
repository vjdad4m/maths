import DegreeFiveSurplus189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 foreign_subset from CrossSaturation189
open private left_boundary from AdjacentCut189
open private count_cut_a from DegreeFiveBridgeSize189
open private not_common secondA_right_and_left_le_five from DegreeFiveFourPort189
open private distance_three_has_bridge from DegreeFiveBalancedUniform189
open private right_inner_le_of_mixed mixed_left_b_in_second from DegreeFiveSurplus189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Split G a b)
set_option linter.unusedSectionVars false

private theorem no_bridge_neighbor_cover (far : 3≤G.dist a b)
    (bridge : ¬portBridge S) (c d : V) (eq : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    {u : V} (up : u∈S.L.filter (G.Adj c)) :
    G.neighborFinset u ⊆ insert c (((S.L.filter (G.Adj c)).erase u) ∪
      S.L.filter (fun z=> ¬G.Adj a z ∧ ¬G.Adj b z)) := by
  classical
  obtain ⟨ul,cu⟩ := mem_filter.mp up
  have cd : 3≤G.dist c d := by
    rcases eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact far
    rwa [SimpleGraph.dist_comm]
  intro y yn
  have uy := (mem_neighborFinset G u y).mp yn
  have cover : y=c ∨ y=d ∨ y∈S.L := by
    rcases left_boundary S u ul y uy with ya|yb|yl
    · rcases eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact .inl ya
      exact .inr (.inl ya)
    · rcases eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact .inr (.inl yb)
      exact .inl yb
    exact .inr (.inr yl)
  rcases cover with rfl|rfl|yl
  · exact mem_insert_self _ _
  · exact (not_common cd cu uy.symm).elim
  apply mem_insert_of_mem
  by_cases cy : G.Adj c y
  · exact mem_union_left _ (mem_erase.mpr ⟨uy.ne.symm,mem_filter.mpr ⟨yl,cy⟩⟩)
  have dy : ¬ G.Adj d y := by
    intro dy
    rcases eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact bridge ⟨u,ul,y,yl,cu,uy,dy⟩
    exact bridge ⟨y,yl,u,ul,dy,uy.symm,cu⟩
  apply mem_union_right
  rcases eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact mem_filter.mpr ⟨yl,cy,dy⟩
  exact mem_filter.mpr ⟨yl,dy,cy⟩

theorem no_bridge_b_shore_card_cost (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (four : S.foreignA.card=4) (A2 : 2≤S.localA.card) (A4 : S.localA.card≤4)
    (B2 : 3≤(S.L.filter (G.Adj b)).card)
    (bridge : ¬portBridge S) :
    6≤(S.L.filter (G.Adj b)).card+
      (S.L.filter (fun z=> ¬G.Adj a z ∧ ¬G.Adj b z)).card := by
  classical
  let B := S.L.filter (G.Adj b)
  let I := S.L.filter (fun z=> ¬G.Adj a z ∧ ¬G.Adj b z)
  change 6≤B.card+I.card
  by_contra! sum
  have choose (P : Finset V) (h : 2≤P.card) : ∃ x∈P,5≤G.degree x := by
    obtain ⟨x,xp,y,yp,xy⟩ := one_lt_card.mp (show 1<P.card by omega)
    rcases degree x y xy with high|high
    · exact ⟨x,xp,high⟩
    exact ⟨y,yp,high⟩
  obtain ⟨u,up,uh⟩ := choose S.localA A2
  have uc := no_bridge_neighbor_cover S far bridge a b (.inl ⟨rfl,rfl⟩) up
  change G.neighborFinset u ⊆ insert a (S.localA.erase u ∪ I) at uc
  have touch : ∃ w∈I,G.Adj u w := by
    by_contra! no
    have sub : G.neighborFinset u⊆insert a (S.localA.erase u) := by
      intro x hx
      rcases mem_insert.mp (uc hx) with rfl|hx'
      · exact mem_insert_self _ _
      rcases mem_union.mp hx' with h|h
      · exact mem_insert_of_mem h
      exact (no _ h ((mem_neighborFinset G u x).mp hx)).elim
    have bound := (card_le_card sub).trans (card_insert_le a _)
    rw [card_neighborFinset_eq_degree,card_erase_of_mem up] at bound
    omega
  obtain ⟨w,wi,uw⟩ := touch
  have touchB {v : V} (vp : v∈B) (vh : 5≤G.degree v) : G.Adj v w := by
    let P := insert b (B.erase v ∪ I)
    have sub : G.neighborFinset v⊆P :=
      no_bridge_neighbor_cover S far bridge b a (.inr ⟨rfl,rfl⟩) vp
    have q := card_insert_le b (B.erase v ∪ I)
    have r := card_union_le (B.erase v) I
    rw [card_erase_of_mem vp] at r
    change P.card≤_ at q
    have pos : 0<B.card := card_pos.mpr ⟨v,vp⟩
    have cap : P.card≤G.degree v := by omega
    have e := eq_of_subset_of_card_le sub (by rwa [card_neighborFinset_eq_degree])
    exact (mem_neighborFinset G v w).mp (e.symm ▸ mem_insert_of_mem (mem_union_right _ wi) : _)
  let H := B.filter (fun z=>5≤G.degree z)
  have highCount : B.card≤H.card+1 := by
    have lo : (B.filter (fun z=>¬5≤G.degree z)).card≤1 := by
      apply card_le_one.mpr
      intro x hx y hy
      exact Classical.byContradiction (fun xy =>
        (degree x y xy).elim (mem_filter.mp hx).2 (mem_filter.mp hy).2)
    have eq := filter_card_add_filter_neg_card_eq_card (s:=B) (fun z=>5≤G.degree z)
    change H.card + _ = B.card at eq
    omega
  obtain ⟨ul,au⟩ := mem_filter.mp up
  have d2s : H⊆DistanceTwo G u := by
    intro v vh
    obtain ⟨vp,vh⟩ := mem_filter.mp vh
    obtain ⟨vl,bv⟩ := mem_filter.mp vp
    exact d2 hc (fun e=>not_common far au (e.symm ▸ bv))
      (fun e=>bridge ⟨u,ul,v,vl,au,e,bv⟩) uw (touchB vp vh).symm
  have dis : Disjoint H S.foreignA := by
    apply disjoint_left.mpr
    intro x xh xp
    exact disjoint_left.mp S.dis (mem_filter.mp (mem_filter.mp xh).1).1 (mem_filter.mp xp).1
  have total := card_le_card (union_subset d2s (foreign_subset S hc ul au))
  rw [card_union_of_disjoint dis,four] at total
  have cap := distanceTwo_le_of_even 5 u (even u)
  change 3≤B.card at B2
  omega


theorem no_eight_six_of_left_bridge (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (a8 : G.degree a=8) (b6 : G.degree b=6) (bridge : portBridge S) : False := by
  classical
  let T := switch S rightConnected rightA rightB
  have far' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  have ar := foreign_a_ports_le_four S hc far even
  have al := foreign_a_ports_le_four T hc far even
  change S.localA.card≤4 at al
  have ca := count_cut_a S far
  have ar4 : S.foreignA.card=4 := by omega
  have al4 : S.localA.card=4 := by omega
  have br := foreign_a_ports_le_four S.flip hc far' even
  have bl := foreign_a_ports_le_four T.flip hc far' even
  have cb := count_cut_a S.flip far'
  let BL := S.L.filter (G.Adj b)
  let BR := S.R.filter (G.Adj b)
  change BR.card≤4 at br
  change BL.card≤4 at bl
  change G.degree b=BL.card+BR.card at cb
  have rightNo : ¬portBridge T := by
    intro q
    have ll := card_le_card (mixed_left_b_in_second S hc far even ar4 bridge)
    have rr := card_le_card (mixed_left_b_in_second T hc far even al4 q)
    change BL.card≤(secondA G S.L a).card at ll
    change BR.card≤(secondA G S.R a).card at rr
    have cap := secondA_right_and_left_le_five S even
    omega
  let I := S.R.filter (fun z => ¬G.Adj a z ∧ ¬G.Adj b z)
  have l := right_inner_le_of_mixed S hc far even ar4 bridge
  change I.card+BL.card≤5 at l
  have bp : 2≤BR.card := by omega
  by_cases h : BR.card=2
  · obtain ⟨x,xp,y,yp,xy⟩ := one_lt_card.mp (show 1<BR.card by omega)
    have high : ∃ u ∈ BR,5≤G.degree u := by
      rcases degree x y xy with h|h
      · exact ⟨x,xp,h⟩
      exact ⟨y,yp,h⟩
    obtain ⟨u,up,uh⟩ := high
    have sub := no_bridge_neighbor_cover T far rightNo b a (.inr ⟨rfl,rfl⟩) (u:=u) up
    change G.neighborFinset u⊆insert b (BR.erase u ∪ I) at sub
    have q := (card_le_card sub).trans (card_insert_le b _)
    have r := card_union_le (BR.erase u) I
    rw [card_neighborFinset_eq_degree] at q
    rw [card_erase_of_mem up] at r
    omega
  have sum := no_bridge_b_shore_card_cost T hc far even degree al4
    (show 2≤T.localA.card by change 2≤S.foreignA.card; omega)
    (show T.localA.card≤4 by exact ar) (show 3≤BR.card by omega) rightNo
  change 6≤BR.card+I.card at sum
  have fourB : S.flip.foreignA.card=4 := by change BR.card=4; omega
  have flipBridge : portBridge S.flip := by
    obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := bridge
    exact ⟨y,yl,x,xl,by',xy.symm,ax⟩
  have r := right_inner_le_of_mixed S.flip hc far' even fourB flipBridge
  have e : (S.R.filter (fun z => ¬G.Adj b z ∧ ¬G.Adj a z)) =
      S.R.filter (fun z => ¬G.Adj a z ∧ ¬G.Adj b z) := by ext z; simp [and_comm]
  change (S.R.filter (fun z => ¬G.Adj b z ∧ ¬G.Adj a z)).card+S.localA.card≤5 at r
  rw [e] at r
  change I.card+S.localA.card≤5 at r
  omega

theorem no_eight_six_at_distance_three_cut (hc : G.Connected) (eq : G.dist a b=3)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (a8 : G.degree a=8) (b6 : G.degree b=6) : False := by
  have far : 3≤G.dist a b := by omega
  rcases distance_three_has_bridge S hc eq rightConnected rightA rightB with l|r
  · exact no_eight_six_of_left_bridge S hc far even degree rightConnected rightA rightB a8 b6 l
  exact no_eight_six_of_left_bridge (switch S rightConnected rightA rightB)
    hc far even degree S.leftConnected S.leftA S.leftB a8 b6 r

#print axioms no_bridge_b_shore_card_cost
#print axioms no_eight_six_at_distance_three_cut
end Graffiti189LongestPath.CrossSaturation.Split.Five

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore mem_shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b ab_ne order_ge_three_from_dist from DegreeFiveActualCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false


theorem no_eight_six_at_actual_five_distance_three_cut {a b : V} (hc : G.Connected)
    (far : 3≤G.dist a b) (even : ∀ x, (EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (cut : ¬(G.induce {z : V | z≠a ∧ z≠b}).Connected)
    (a8 : G.degree a=8) (b6 : G.degree b=6) : False := by
  classical
  have ab := ab_ne far
  let J := G.induce {x : V | x≠a ∧ x≠b}
  have hi := component_card_le_two_at_cut_distance_ge_three hc far even conn degree
  have lo := component_card_gt_one_of_disconnected a b (order_ge_three_from_dist hc far) cut
  change 1<Nat.card J.ConnectedComponent at lo
  change Nat.card J.ConnectedComponent≤2 at hi
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  have n : Fintype.card Bool=Fintype.card J.ConnectedComponent := by
    rw [Fintype.card_bool,←Nat.card_eq_fintype_card]
    omega
  let C := Fintype.equivOfCardEq n
  let L := Shore (C false)
  let R := Shore (C true)
  have dis : Disjoint L R := shore_disjoint (fun h=>Bool.false_ne_true (C.injective h))
  have cover (x : V) : x=a ∨ x=b ∨ x∈L ∨ x∈R := by
    by_cases xa : x=a
    · exact .inl xa
    by_cases xb : x=b
    · exact .inr (.inl xb)
    obtain ⟨i,e⟩ := C.surjective (J.connectedComponentMk ⟨x,xa,xb⟩)
    cases i
    · exact .inr (.inr (.inl (mem_shore.mpr ⟨⟨xa,xb⟩,e.symm⟩)))
    · exact .inr (.inr (.inr (mem_shore.mpr ⟨⟨xa,xb⟩,e.symm⟩)))
  have cross (x : V) (xl : x∈L) (y : V) (yr : y∈R) : ¬G.Adj x y := by
    intro xy
    have yr' : y∈Shore (C true) := yr
    rcases shore_closed (C false) x xl y xy with e|e|e
    · exact (shore_off (C true)).1 (e ▸ yr')
    · exact (shore_off (C true)).2 (e ▸ yr')
    exact disjoint_left.mp dis e yr
  let S : Split G a b :=
    ⟨L,R,dis,shore_off (C false),shore_off (C true),shore_connected (C false),cross,
      shore_hit_a ab conn (C false),shore_hit_b ab conn (C false),cover⟩
  have cap := cut_distance_le_three_at_actual_five_cut hc even conn degree cut
  have exactDist : G.dist a b=3 := by omega
  exact Split.Five.no_eight_six_at_distance_three_cut S hc exactDist even degree
    (shore_connected (C true)) (shore_hit_a ab conn (C true)) (shore_hit_b ab conn (C true)) a8 b6

#print axioms no_eight_six_at_actual_five_distance_three_cut
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
