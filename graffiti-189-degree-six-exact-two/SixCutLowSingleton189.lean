import SixCutHighShore189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore mem_shore shore_off shore_closed shore_disjoint shore_connected shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private Cmp DeletionConnected aPorts bPorts aTwos bTwos split_at_shore two_local_counts
  from SixCutFar189
open private three_shores port_cost each_foreign_port_is_distance_two distinct_shore_twos_dis
  from SixCutHighShore189
open private Vis vis_sub vis_card_ge_two degree_le_shore_add_one from AdjacentCutFiveComponents189
open private d2 from CrossSaturation189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (shore_swapCut)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem a_sub_vis (C : Cmp G a b) : aPorts C⊆Vis C :=
  fun _ h=>mem_filter.mpr ⟨(mem_filter.mp h).1,.inl (mem_filter.mp h).2⟩
private theorem b_sub_vis (C : Cmp G a b) : bPorts C⊆Vis C :=
  fun _ h=>mem_filter.mpr ⟨(mem_filter.mp h).1,.inr (mem_filter.mp h).2⟩

private theorem b_port_cost (hc : G.Connected) (C : Cmp G a b) {x : V} (xp : x∈bPorts C) :
    G.degree x≤(bPorts C).card+(bTwos C).card+if G.Adj a x then 1 else 0 := by
  simpa only [aPorts,bPorts,aTwos,bTwos,shore_swapCut] using
    (port_cost (a:=b) (b:=a) hc (swapCut C) (x:=x) (by simpa only [aPorts,bPorts,shore_swapCut] using xp))

private theorem singleton_low_of_three (hc : G.Connected) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (big : 3≤Nat.card (Cmp G a b)) :
    ∃ (S : Cmp G a b) (s : V),Shore S={s} ∧ G.Adj a s ∧ G.Adj b s ∧ G.degree s<6 := by
  classical
  obtain ⟨⟨S,lowS⟩,⟨T,lowT⟩⟩ := exists_shore_without_high_ports_at_six hc ab even conn degree big
  obtain ⟨s,ss,as'⟩ := shore_hit_a ab conn S
  obtain ⟨t,ts,bt⟩ := shore_hit_b ab conn T
  have sl := lowS s (mem_filter.mpr ⟨ss,as'⟩)
  have tl := lowT t (mem_filter.mpr ⟨ts,bt⟩)
  have st : s=t := by by_contra n; rcases degree s t n with h|h <;> omega
  subst t
  have ST : S=T := by by_contra not; exact disjoint_left.mp (shore_disjoint not) ss ts
  subst T
  have visS : Vis S⊆{s} := by
    intro z hz
    have ⟨zs,port⟩ := mem_filter.mp hz
    have l : G.degree z<6 := port.elim (fun az=>lowS z (mem_filter.mpr ⟨zs,az⟩))
      (fun bz=>lowT z (mem_filter.mpr ⟨zs,bz⟩))
    have eq : z=s := by by_contra n; rcases degree z s n with h|h <;> omega
    exact mem_singleton.mpr eq
  have sm := card_le_card visS
  rw [card_singleton] at sm
  have ss' : Shore S⊆{s} := by
    have h : (Shore S).card≤1 := by
      by_contra n
      have t := vis_card_ge_two ab conn S (by omega)
      omega
    intro z zs
    exact mem_singleton.mpr (card_le_one.mp h z zs s ss)
  exact ⟨S,s,Subset.antisymm ss' (singleton_subset_iff.mpr ss),as',bt,sl⟩

private theorem two_other_shores (S : Cmp G a b) (h : 3≤Nat.card (Cmp G a b)) :
    ∃ C D : Cmp G a b, S≠C ∧ S≠D ∧ C≠D := by
  obtain ⟨C,D,E,cd,ce,de⟩ := three_shores h
  by_cases sc : S=C
  · subst S; exact ⟨D,E,cd,ce,de⟩
  by_cases sd : S=D
  · subst S; exact ⟨C,E,cd.symm,de,ce⟩
  exact ⟨C,D,sc,sd,cd⟩

private theorem two_has_dark (K : Cmp G a b) (high : ∀ z∈Shore K,6≤G.degree z)
    (vis : (Vis K).card≤4) (ne : (Shore K).Nonempty) :
    ∃ z∈Shore K,z∉Vis K := by
  obtain ⟨u,uk⟩ := ne
  have h := high u uk
  have lo := degree_le_shore_add_one K uk
  by_contra n
  push_neg at n
  have m := card_le_card n
  omega

private theorem dark_degree {z : V} (C : Cmp G a b) (zc : z∈Shore C) (zn : z∉Vis C) :
    G.neighborFinset z⊆(Shore C).erase z := by
  intro w hw
  have zw := (mem_neighborFinset _ _ _).mp hw
  rcases shore_closed C z zc w zw with rfl|rfl|wc
  · exact (zn (mem_filter.mpr ⟨zc,.inl zw.symm⟩)).elim
  · exact (zn (mem_filter.mpr ⟨zc,.inr zw.symm⟩)).elim
  exact mem_erase.mpr ⟨zw.ne.symm,wc⟩

private theorem dark_shore_size (C : Cmp G a b) {z : V} (zc : z∈Shore C) (zn : z∉Vis C)
    (h : 6≤G.degree z) : 7≤(Shore C).card := by
  have c := card_le_card (dark_degree C zc zn)
  rw [card_neighborFinset_eq_degree] at c
  have e := card_erase_add_one zc
  omega

private theorem singleton_distance {S : Cmp G a b} {s : V} (sS : Shore S={s})
    (hc : G.Connected) (as' : G.Adj a s) (bs' : G.Adj b s) {z : V} (zs : z≠s) :
    G.dist s z=1+min (G.dist a z) (G.dist b z) := by
  have ss : s∈Shore S := by simp [sS]
  have zn : z∉Shore S := by simpa only [sS,mem_singleton] using zs
  have e := cross_metric (Shore S) hc ss zn (shore_closed S)
  rw [dist_eq_one_iff_adj.mpr as'.symm,dist_eq_one_iff_adj.mpr bs'.symm] at e
  omega

private theorem common_dark_neighbors (X : Cmp G a b) {x : V}
    (hc : G.Connected) (xc : x∈Shore X) (ax : G.Adj a x) (bx : G.Adj b x) :
    let U := ((Shore X)\Vis X).filter (G.Adj x)
    G.degree x≤(Vis X).card+1+U.card ∧ U⊆aTwos X ∧ U⊆bTwos X := by
  classical
  dsimp only
  let U := ((Shore X)\Vis X).filter (G.Adj x)
  have xv : x∈Vis X := mem_filter.mpr ⟨xc,.inl ax⟩
  have sub : G.neighborFinset x ⊆ insert a (insert b (((Vis X).erase x)∪U)) := by
    intro z zm
    have xz := (mem_neighborFinset _ _ _).mp zm
    rcases shore_closed X x xc z xz with rfl|rfl|zs
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_insert_self _ _)
    apply mem_insert_of_mem
    apply mem_insert_of_mem
    by_cases zv : z∈Vis X
    · exact mem_union_left _ (mem_erase.mpr ⟨xz.ne.symm,zv⟩)
    exact mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨zs,zv⟩,xz⟩)
  refine ⟨?_,?_,?_⟩
  · have n := card_le_card sub
    change G.degree x≤(Vis X).card+1+U.card
    rw [card_neighborFinset_eq_degree] at n
    have i := card_insert_le a (insert b (((Vis X).erase x)∪U))
    have j := card_insert_le b (((Vis X).erase x)∪U)
    have c := card_union_le ((Vis X).erase x) U
    have e := card_erase_add_one xv
    omega
  · intro z zu
    have ⟨h,xz⟩ := mem_filter.mp zu
    have ⟨zs,zn⟩ := mem_sdiff.mp h
    have an : a≠z := fun eq=>(shore_off X).1 (eq.symm ▸ zs)
    exact mem_inter.mpr ⟨zs,d2 hc an (fun az=>zn (mem_filter.mpr ⟨zs,.inl az⟩)) ax xz⟩
  · intro z zu
    have ⟨h,xz⟩ := mem_filter.mp zu
    have ⟨zs,zn⟩ := mem_sdiff.mp h
    have bn : b≠z := fun eq=>(shore_off X).2 (eq.symm ▸ zs)
    exact mem_inter.mpr ⟨zs,d2 hc bn (fun bz=>zn (mem_filter.mpr ⟨zs,.inr bz⟩)) bx xz⟩

private theorem intersect_of_two_sets {A B C D : Finset V}
    (ab : Disjoint A B) (ac : A⊆C) (ad : A⊆D) (bc : B⊆C) (bd : B⊆D) :
    A.card+B.card≤(C∩D).card :=
  two_local_counts A B ab (C∩D) (subset_inter ac ad) (subset_inter bc bd)

private theorem order_bound_from_singleton_overlap (hc : G.Connected)
    (even : ∀ x,(EvenFrom G x).card≤7) {s : V} {S : Cmp G a b}
    (sS : Shore S={s}) (as' : G.Adj a s) (bs' : G.Adj b s)
    (ov : 4≤(PositiveEven G a∩PositiveEven G b).card) : Fintype.card V≤17 := by
  classical
  have pos (x : V) : (PositiveEven G x).card≤6 := by
    have m : x∈EvenFrom G x := by simp [EvenFrom,dist_self]
    have p := card_erase_of_mem m
    have q := even x
    change ((EvenFrom G x).erase x).card≤6
    omega
  let A := PositiveEven G a∪PositiveEven G b
  let B := PositiveEven G s
  have cover : (univ : Finset V)⊆insert a (insert b (insert s (A∪B))) := by
    intro z _
    by_cases za : z=a
    · simp [za]
    by_cases zb : z=b
    · simp [zb]
    by_cases zs : z=s
    · simp [zs]
    by_cases ea : Even (G.dist a z)
    · have j : z∈PositiveEven G a := mem_erase.mpr ⟨za,mem_filter.mpr ⟨mem_univ _,ea⟩⟩
      simp [A,j]
    by_cases eb : Even (G.dist b z)
    · have j : z∈PositiveEven G b := mem_erase.mpr ⟨zb,mem_filter.mpr ⟨mem_univ _,eb⟩⟩
      simp [A,j]
    have e : Even (G.dist s z) := by
      rw [singleton_distance sS hc as' bs' zs]
      simp only [Nat.even_iff] at ea eb ⊢
      omega
    have j : z∈B := mem_erase.mpr ⟨zs,mem_filter.mpr ⟨mem_univ _,e⟩⟩
    simp [j]
  have n := card_le_card cover
  rw [card_univ] at n
  have t := card_union_add_card_inter (PositiveEven G a) (PositiveEven G b)
  change A.card+(PositiveEven G a∩PositiveEven G b).card=_ at t
  have n₁ := card_insert_le a (insert b (insert s (A∪B)))
  have n₂ := card_insert_le b (insert s (A∪B))
  have n₃ := card_insert_le s (A∪B)
  have u := card_union_le A B
  have pa := pos a
  have pb := pos b
  have ps := pos s
  change B.card≤6 at ps
  omega

private theorem no_two_common_shores (hc : G.Connected) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card≤7) {S C D : Cmp G a b} (sc : S≠C) (sd : S≠D) (cd : C≠D)
    {s : V} (sS : Shore S={s}) (as' : G.Adj a s) (bs' : G.Adj b s)
    (v6 : (Vis C).card+(Vis D).card≤6)
    (C7 : 7≤(Shore C).card) (D7 : 7≤(Shore D).card)
    (highC : ∀ z∈Shore C,6≤G.degree z) (highD : ∀ z∈Shore D,6≤G.degree z)
    {x y : V} (xc : x∈Shore C) (yd : y∈Shore D)
    (ax : G.Adj a x) (bx : G.Adj b x) (ay : G.Adj a y) (by' : G.Adj b y) : False := by
  classical
  let P := ((Shore C)\Vis C).filter (G.Adj x)
  let Q := ((Shore D)\Vis D).filter (G.Adj y)
  obtain ⟨costX,pa,pb⟩ := common_dark_neighbors C hc xc ax bx
  obtain ⟨costY,qa,qb⟩ := common_dark_neighbors D hc yd ay by'
  change G.degree x≤(Vis C).card+1+P.card at costX
  change G.degree y≤(Vis D).card+1+Q.card at costY
  have darkSub {H : Cmp G a b} {z : V} : (Shore H\Vis H).filter (G.Adj z)⊆Shore H :=
    fun _ h=>(mem_sdiff.mp (mem_filter.mp h).1).1
  have dPQ : Disjoint P Q := (shore_disjoint cd).mono darkSub darkSub
  have inc {t z : V} (h : z∈DistanceTwo G t) : z∈PositiveEven G t := by
    have e := (mem_filter.mp h).2
    exact mem_erase.mpr ⟨by intro eq; rw [eq,dist_self] at e; omega,
      mem_filter.mpr ⟨mem_univ _,by rw [e]; decide⟩⟩
  have i : P.card+Q.card≤(PositiveEven G a∩PositiveEven G b).card :=
    intersect_of_two_sets dPQ
      (fun _ h=>inc (mem_inter.mp (pa h)).2) (fun _ h=>inc (mem_inter.mp (pb h)).2)
      (fun _ h=>inc (mem_inter.mp (qa h)).2) (fun _ h=>inc (mem_inter.mp (qb h)).2)
  have X6 := highC x xc
  have Y6 := highD y yd
  have n := order_bound_from_singleton_overlap hc even sS as' bs' (by omega : 4≤_)
  let W := Shore C∪Shore D
  have w : W.card=(Shore C).card+(Shore D).card := card_union_of_disjoint (shore_disjoint cd)
  have ss : s∈Shore S := by simp [sS]
  have sw : s∉W := by
    intro j
    rcases mem_union.mp j with c|d
    · exact disjoint_left.mp (shore_disjoint sc) ss c
    exact disjoint_left.mp (shore_disjoint sd) ss d
  have aw : a∉W := by simp [W,(shore_off C).1,(shore_off D).1]
  have bw : b∉W := by simp [W,(shore_off C).2,(shore_off D).2]
  have nsum : W.card+3≤Fintype.card V := by
    have k := card_le_card (subset_univ (insert a (insert b (insert s W))))
    rw [card_univ,card_insert_of_not_mem (by simp [aw,as'.ne,ab]),
      card_insert_of_not_mem (by simp [bw,bs'.ne]),card_insert_of_not_mem sw] at k
    omega
  have c7 : (Shore C).card=7 := by omega
  have d7 : (Shore D).card=7 := by omega
  have allDark (K : Cmp G a b) (k7 : (Shore K).card=7)
      (kh : ∀ z∈Shore K,6≤G.degree z) {p : V} (pk : p∈Vis K) :
      ((Shore K)\Vis K).filter (G.Adj p)=Shore K\Vis K := by
    apply Subset.antisymm (filter_subset _ _)
    intro z zm
    have ⟨zk,zp⟩ := mem_sdiff.mp zm
    have sub := dark_degree K zk zp
    have e := card_erase_add_one zk
    have f := kh z zk
    have g : (#(G.neighborFinset z))≥6 := by rwa [card_neighborFinset_eq_degree]
    have eq := eq_of_subset_of_card_le sub (by omega)
    have nor : p≠z := fun en=>zp (en ▸ pk)
    have m : p∈G.neighborFinset z := eq.symm ▸ (mem_erase.mpr ⟨nor,vis_sub K pk⟩)
    exact mem_filter.mpr ⟨zm,((mem_neighborFinset _ _ _).mp m).symm⟩
  have Pe : P.card=(Shore C).card-(Vis C).card := by
    change (((Shore C)\Vis C).filter (G.Adj x)).card=_
    rw [allDark C c7 highC (mem_filter.mpr ⟨xc,.inl ax⟩),card_sdiff (vis_sub C)]
  have Qe : Q.card=(Shore D).card-(Vis D).card := by
    change (((Shore D)\Vis D).filter (G.Adj y)).card=_
    rw [allDark D d7 highD (mem_filter.mpr ⟨yd,.inl ay⟩),card_sdiff (vis_sub D)]
  have inter := card_le_card (inter_subset_left :
      PositiveEven G a∩PositiveEven G b ⊆ PositiveEven G a)
  have ep := even a
  have ea : a∈EvenFrom G a := by simp [EvenFrom,dist_self]
  have e := card_erase_of_mem ea
  change (PositiveEven G a).card=_ at e
  omega

#print axioms singleton_low_of_three
#print axioms no_two_common_shores
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
