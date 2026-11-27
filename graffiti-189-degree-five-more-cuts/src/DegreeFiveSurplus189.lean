import DegreeFiveBalancedUniform189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private distance_three_has_bridge from DegreeFiveBalancedUniform189
open private d2 foreign_subset from CrossSaturation189
open private left_boundary from AdjacentCut189
open private count_cut_a from DegreeFiveBridgeSize189
open private not_common secondA_right_and_left_le_five from DegreeFiveFourPort189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem right_cover_of_mixed_opposite_four (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6) (four : S.foreignA.card=4)
    (bridge : portBridge S) :
    S.R ⊆ S.foreignA ∪ (S.R.filter (G.Adj b)) ∪ secondA G S.R a := by
  classical
  obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := bridge
  have rad := (saturated_at_opposite_four S hc far even four xl ax).2
  have xne : x≠b := fun e=>S.leftOff.2 (e ▸ xl)
  have xb := d2 hc xne (fun e=>not_common far ax e.symm) xy by'.symm
  have db : G.dist x b = 2 := by simpa [DistanceTwo] using xb
  intro z zr
  by_cases az : G.Adj a z
  · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨zr,az⟩))
  by_cases bz : G.Adj b z
  · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨zr,bz⟩))
  have za : a≠z := fun e=>S.rightOff.1 (e.symm ▸ zr)
  have zb : b≠z := fun e=>S.rightOff.2 (e.symm ▸ zr)
  have da := hc.one_lt_dist_of_ne_of_not_adj za az
  have dc := hc.one_lt_dist_of_ne_of_not_adj zb bz
  have cross := cross_metric S.L hc xl (fun zl=>disjoint_left.mp S.dis zl zr)
    (left_boundary S)
  have xa := dist_eq_one_iff_adj.mpr ax.symm
  have d := rad z
  rw [cross,xa,db] at d
  have exacta : G.dist a z=2 := by omega
  exact mem_union_right _ (mem_inter.mpr ⟨zr,by simp [DistanceTwo,exacta]⟩)

theorem left_cover_of_mixed_opposite_four (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6) (four : S.foreignA.card=4)
    (bridge : portBridge S) : S.L ⊆ S.localA ∪ secondA G S.L a := by
  classical
  obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := bridge
  have univ := bridge_four_forces_universal S hc far even four xl ax xy by'
  intro z zl
  by_cases az : G.Adj a z
  · exact mem_union_left _ (mem_filter.mpr ⟨zl,az⟩)
  have xz := (univ _ zl).resolve_left (fun e=>az (e.symm ▸ ax))
  have ne : a≠z := fun e=>S.leftOff.1 (e.symm ▸ zl)
  exact mem_union_right _ (mem_inter.mpr ⟨zl,d2 hc ne az ax xz⟩)

theorem shore_sum_le_of_mixed_opposite_four (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6) (four : S.foreignA.card=4)
    (bridge : portBridge S) :
    S.L.card+S.R.card ≤ G.degree a+(S.R.filter (G.Adj b)).card+5 := by
  classical
  have l := (card_le_card (left_cover_of_mixed_opposite_four S hc far even four bridge)).trans
    (card_union_le _ _)
  have r := (card_le_card (right_cover_of_mixed_opposite_four S hc far even four bridge)).trans
    (card_union_le _ _)
  have s := card_union_le S.foreignA (S.R.filter (G.Adj b))
  have cap := secondA_right_and_left_le_five S even
  have eq := count_cut_a S far
  omega

theorem no_bridge_four_shore_needs_two_inner (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (four : S.foreignA.card=4) (A2 : 2≤S.localA.card) (A4 : S.localA.card≤4)
    (B3 : 3≤(S.L.filter (G.Adj b)).card) (B4 : (S.L.filter (G.Adj b)).card≤4)
    (bridge : ¬portBridge S) :
    2≤(S.L.filter (fun z => ¬ G.Adj a z ∧ ¬ G.Adj b z)).card := by
  classical
  let I := S.L.filter (fun z => ¬ G.Adj a z ∧ ¬ G.Adj b z)
  let B := S.L.filter (G.Adj b)
  change 2≤I.card
  by_contra! small
  have bound (c d : V) (P : Finset V)
      (pc : P = S.L.filter (G.Adj c)) (pc4 : P.card≤4)
      (cd : 3≤G.dist c d) (eq : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
      {u : V} (up : u∈P) (high : 5≤G.degree u) :
      ∃ w∈I,G.Adj u w := by
    obtain ⟨ul,cu⟩ := mem_filter.mp (pc ▸ up)
    by_contra! no
    have sub : G.neighborFinset u ⊆ insert c (P.erase u) := by
      intro v vn
      have uv := (mem_neighborFinset G u v).mp vn
      have same : v=c ∨ v=d ∨ v∈S.L := by
        rcases left_boundary S u ul v uv with va|vb|vl
        · rcases eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          · exact .inl va
          · exact .inr (.inl va)
        · rcases eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          · exact .inr (.inl vb)
          · exact .inl vb
        exact .inr (.inr vl)
      rcases same with rfl|rfl|vl
      · exact mem_insert_self _ _
      · exact (not_common cd cu uv.symm).elim
      by_cases cv : G.Adj c v
      · exact mem_insert_of_mem (mem_erase.mpr ⟨uv.ne.symm,pc.symm ▸ mem_filter.mpr ⟨vl,cv⟩⟩)
      have dv : ¬ G.Adj d v := by
        intro dv
        rcases eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact bridge ⟨u,ul,v,vl,cu,uv,dv⟩
        · exact bridge ⟨v,vl,u,ul,dv,uv.symm,cu⟩
      have vi : v∈I := by
        rcases eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact mem_filter.mpr ⟨vl,cv,dv⟩
        · exact mem_filter.mpr ⟨vl,dv,cv⟩
      exact (no v vi uv).elim
    have h := (card_le_card sub).trans (card_insert_le c (P.erase u))
    rw [card_neighborFinset_eq_degree,card_erase_of_mem up] at h
    omega
  have age (positive : 1<S.localA.card) : ∃ u∈S.localA,5≤G.degree u := by
    obtain ⟨u,up,v,vp,uv⟩ := one_lt_card.mp positive
    rcases degree u v uv with h|h
    · exact ⟨u,up,h⟩
    exact ⟨v,vp,h⟩

  obtain ⟨u,up,uhi⟩ := age (by omega)
  obtain ⟨w,wi,uw⟩ := bound a b S.localA rfl A4 far (.inl ⟨rfl,rfl⟩) up uhi
  let H := B.filter (fun z=>5≤G.degree z)
  have hi : 2≤H.card := by
    have lo : (B.filter (fun z=>¬5≤G.degree z)).card≤1 := by
      apply card_le_one.mpr
      intro x hx y hy
      by_contra xy
      exact (degree x y xy).elim (mem_filter.mp hx).2 (mem_filter.mp hy).2
    have eq := filter_card_add_filter_neg_card_eq_card (s:=B) (fun z=>5≤G.degree z)
    change H.card + _ = B.card at eq
    change 3≤B.card at B3
    omega
  obtain ⟨y,yp,z,zp,yz⟩ := one_lt_card.mp (show 1<H.card by omega)
  have far' : 3≤G.dist b a := by rwa [SimpleGraph.dist_comm]
  have touch {v : V} (vh : v∈H) : G.Adj v w := by
    obtain ⟨vp,vhi⟩ := mem_filter.mp vh
    obtain ⟨t,ti,vt⟩ := bound b a B rfl B4 far' (.inr ⟨rfl,rfl⟩) vp vhi
    have tw : t=w := by
      by_contra neq
      have : 1<I.card := one_lt_card.mpr ⟨t,ti,w,wi,neq⟩
      omega
    exact tw ▸ vt
  obtain ⟨ul,au⟩ := mem_filter.mp up
  have localD2 {v : V} (vh : v∈H) : v∈DistanceTwo G u ∧ v∉S.foreignA := by
    have vl := (mem_filter.mp (mem_filter.mp vh).1).1
    have bv := (mem_filter.mp (mem_filter.mp vh).1).2
    have uv : u≠v := fun e=>not_common far au (e.symm ▸ bv)
    have no : ¬G.Adj u v := fun e=>bridge ⟨u,ul,v,vl,au,e,bv⟩
    exact ⟨d2 hc uv no uw (touch vh).symm,fun e=>disjoint_left.mp S.dis vl (mem_filter.mp e).1⟩
  obtain ⟨yd,yn⟩ := localD2 yp
  obtain ⟨zd,zn⟩ := localD2 zp
  have zs : z∉insert y S.foreignA := fun e=>(mem_insert.mp e).elim (Ne.symm yz) zn
  have sub : insert z (insert y S.foreignA) ⊆ DistanceTwo G u := by
    intro t ht
    rcases mem_insert.mp ht with rfl|ht
    · exact zd
    rcases mem_insert.mp ht with rfl|ht
    · exact yd
    exact foreign_subset S hc ul au ht
  have k := card_le_card sub
  rw [card_insert_of_not_mem zs,card_insert_of_not_mem yn,four] at k
  have c := distanceTwo_le_of_even 5 u (even u)
  omega

private theorem mixed_left_b_in_second (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6) (four : S.foreignA.card=4)
    (bridge : portBridge S) :
    S.L.filter (G.Adj b) ⊆ secondA G S.L a := by
  intro z zp
  obtain ⟨zl,bz⟩ := mem_filter.mp zp
  exact (mem_union.mp (left_cover_of_mixed_opposite_four S hc far even four bridge zl)).resolve_left
    (fun za=>not_common far (mem_filter.mp za).2 bz)

private theorem right_inner_le_of_mixed (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6) (four : S.foreignA.card=4)
    (bridge : portBridge S) :
    (S.R.filter (fun z => ¬G.Adj a z ∧ ¬G.Adj b z)).card+
      (S.L.filter (G.Adj b)).card≤5 := by
  classical
  have r : S.R.filter (fun z => ¬G.Adj a z ∧ ¬G.Adj b z) ⊆ secondA G S.R a := by
    intro z zi
    obtain ⟨zr,na,nb⟩ := mem_filter.mp zi
    have q := mem_union.mp (right_cover_of_mixed_opposite_four S hc far even four bridge zr)
    exact q.resolve_left (fun h=>(mem_union.mp h).elim (fun e=>na (mem_filter.mp e).2)
      (fun e=>nb (mem_filter.mp e).2))
  have nr := card_le_card r
  have nl := card_le_card (mixed_left_b_in_second S hc far even four bridge)
  have cap := secondA_right_and_left_le_five S even
  omega

theorem no_eight_seven_of_left_bridge (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (a8 : G.degree a=8) (b7 : 7≤G.degree b) (bridge : portBridge S) : False := by
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
  have many := no_bridge_four_shore_needs_two_inner T hc far even degree al4
    (show 2≤T.localA.card by change 2≤S.foreignA.card; omega)
    (show T.localA.card≤4 by exact ar) (show 3≤BR.card by omega) br rightNo
  change 2≤(S.R.filter (fun z => ¬G.Adj a z ∧ ¬G.Adj b z)).card at many
  have l := right_inner_le_of_mixed S hc far even ar4 bridge
  change _ +BL.card≤5 at l
  have fourB : S.flip.foreignA.card=4 := by change BR.card=4; omega
  have flipBridge : portBridge S.flip := by
    obtain ⟨x,xl,y,yl,ax,xy,by'⟩ := bridge
    exact ⟨y,yl,x,xl,by',xy.symm,ax⟩
  have r := right_inner_le_of_mixed S.flip hc far' even fourB flipBridge
  have e : (S.R.filter (fun z => ¬G.Adj b z ∧ ¬G.Adj a z)) =
      S.R.filter (fun z => ¬G.Adj a z ∧ ¬G.Adj b z) := by ext z; simp [and_comm]
  change (S.R.filter (fun z => ¬G.Adj b z ∧ ¬G.Adj a z)).card+S.localA.card≤5 at r
  rw [e] at r
  omega

theorem no_eight_seven_at_distance_three_cut (hc : G.Connected) (eq : G.dist a b=3)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (rightConnected : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ x∈S.R,G.Adj a x) (rightB : ∃ x∈S.R,G.Adj b x)
    (a8 : G.degree a=8) (b7 : 7≤G.degree b) : False := by
  have far : 3≤G.dist a b := by omega
  rcases distance_three_has_bridge S hc eq rightConnected rightA rightB with l|r
  · exact no_eight_seven_of_left_bridge S hc far even degree rightConnected rightA rightB a8 b7 l
  exact no_eight_seven_of_left_bridge (switch S rightConnected rightA rightB)
    hc far even degree S.leftConnected S.leftA S.leftB a8 b7 r

#print axioms right_cover_of_mixed_opposite_four
#print axioms shore_sum_le_of_mixed_opposite_four
#print axioms no_bridge_four_shore_needs_two_inner
#print axioms no_eight_seven_at_distance_three_cut
end Graffiti189LongestPath.CrossSaturation.Split.Five

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore mem_shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b ab_ne order_ge_three_from_dist from DegreeFiveActualCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false


theorem no_eight_seven_at_actual_five_distance_three_cut {a b : V} (hc : G.Connected)
    (far : 3≤G.dist a b) (even : ∀ x, (EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (cut : ¬(G.induce {z : V | z≠a ∧ z≠b}).Connected)
    (a8 : G.degree a=8) (b7 : 7≤G.degree b) : False := by
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
  exact Split.Five.no_eight_seven_at_distance_three_cut S hc exactDist even degree
    (shore_connected (C true)) (shore_hit_a ab conn (C true)) (shore_hit_b ab conn (C true)) a8 b7

#print axioms no_eight_seven_at_actual_five_distance_three_cut
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
