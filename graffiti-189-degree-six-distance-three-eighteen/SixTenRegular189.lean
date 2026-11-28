import SixDistanceThreeShort189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_closed shore_connected shore_disjoint shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private Cmp DeletionConnected aPorts bPorts aTwos bTwos two_local_counts from SixCutFar189
open private port_cost each_foreign_port_is_distance_two distinct_shore_twos_dis
  from SixCutHighShore189
open private no_common_far shore_inside_five from SixDistanceThreeShort189
open private d2 from CrossSaturation189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (shore_swapCut)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem same_color_upper (hc : G.Connected) (ab : a≠b) (conn : DeletionConnected G)
    (even : ∀ x,(EvenFrom G x).card≤7) {C D : Cmp G a b} (cd : C≠D) :
    (aPorts D).card≤6 := by
  obtain ⟨x,xc,ax⟩ := shore_hit_a ab conn C
  have sub : aPorts D⊆DistanceTwo G x :=
    fun _ h=>each_foreign_port_is_distance_two hc cd (mem_filter.mpr ⟨xc,ax⟩) h
  exact (card_le_card sub).trans (distanceTwo_le_of_even 6 x (even x))

private theorem neighbor_subset_of_dark (D : Cmp G a b) {z : V}
    (zd : z∈Shore D) (az : ¬G.Adj a z) (bz : ¬G.Adj b z) :
    G.neighborFinset z⊆inside G (Shore D) z := by
  intro x xn
  have zx := (mem_neighborFinset _ _ _).mp xn
  rcases shore_closed D z zd x zx with rfl|rfl|xd
  · exact (az zx.symm).elim
  · exact (bz zx.symm).elim
  exact mem_filter.mpr ⟨xd,zx⟩

private theorem bridge_exists_of_only_ports (D : Cmp G a b)
    (ab : a≠b) (conn : DeletionConnected G) (far : 3≤G.dist a b)
    (allP : ∀ z∈Shore D,G.Adj a z ∨ G.Adj b z) :
    ∃ x∈aPorts D,∃ y∈bPorts D,G.Adj x y := by
  obtain ⟨x,xd,ax⟩ := shore_hit_a ab conn D
  obtain ⟨y,yd,by'⟩ := shore_hit_b ab conn D
  let U : Set V := ↑(Shore D)
  obtain ⟨p⟩ := (shore_connected D).preconnected (⟨x,xd⟩ : U) (⟨y,yd⟩ : U)
  by_contra no
  have run {z w : U} (q : (G.induce U).Walk z w) : G.Adj a z.val → G.Adj a w.val := by
    induction q with
    | nil => exact id
    | @cons t u w tu q ih =>
      intro az
      apply ih
      rcases allP u.val (Finset.mem_coe.mp u.property) with au|bu
      · exact au
      exact (no ⟨t.val,mem_filter.mpr ⟨t.property,az⟩,u.val,mem_filter.mpr ⟨u.property,bu⟩,tu⟩).elim
  exact no_common_far far ⟨run p ax,by'⟩

private theorem all_local_nonadj_are_two (hc : G.Connected) {D : Cmp G a b}
    (n : (Shore D).card=10) (regular : ∀ z∈Shore D,(inside G (Shore D) z).card=5)
    {x z : V} (xd : x∈Shore D) (zd : z∈Shore D) (ne : x≠z) (not : ¬G.Adj x z) :
    z∈DistanceTwo G x := by
  classical
  let A := inside G (Shore D) x
  let B := inside G (Shore D) z
  have a5 : A.card=5 := regular x xd
  have b5 : B.card=5 := regular z zd
  have sA : A⊆(Shore D).erase x := by
    intro v hv
    have h := mem_filter.mp hv
    exact mem_erase.mpr ⟨h.2.ne.symm,h.1⟩
  have sB : B⊆(Shore D).erase x := by
    intro v hv
    have h := mem_filter.mp hv
    exact mem_erase.mpr ⟨fun e=>not (e ▸ h.2).symm,h.1⟩
  have meet : (A∩B).Nonempty := by
    by_contra! empty
    have d : Disjoint A B := by rw [disjoint_iff_inter_eq_empty]; exact not_nonempty_iff_eq_empty.mp empty
    have t := two_local_counts A B d _ sA sB
    rw [card_erase_of_mem xd,n] at t
    omega
  obtain ⟨v,h⟩ := meet
  exact d2 hc ne not (mem_filter.mp (mem_inter.mp h).1).2 (mem_filter.mp (mem_inter.mp h).2).2.symm

private theorem single_opposing_port_of_bridge (hc : G.Connected) (far : 3≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤7) {C D : Cmp G a b} (cd : C≠D)
    (n : (Shore D).card=10) (regular : ∀ z∈Shore D,(inside G (Shore D) z).card=5)
    {x y : V} (xp : x∈aPorts D) (yp : y∈bPorts D) (xy : G.Adj x y) :
    (aPorts C).card≤1 := by
  classical
  have ⟨xd,ax⟩ := mem_filter.mp xp
  have ⟨yd,by'⟩ := mem_filter.mp yp
  let F := (Shore D).erase x \ inside G (Shore D) x
  have F4 : F.card=4 := by
    have ss : inside G (Shore D) x⊆(Shore D).erase x :=
      fun _ h=>mem_erase.mpr ⟨(mem_filter.mp h).2.ne.symm,(mem_filter.mp h).1⟩
    change ((Shore D).erase x \ inside G (Shore D) x).card=4
    rw [card_sdiff ss,card_erase_of_mem xd,n,regular x xd]
  have fSub : F⊆DistanceTwo G x := by
    intro z f
    have ⟨e,not⟩ := mem_sdiff.mp f
    have ⟨ne,zd⟩ := mem_erase.mp e
    exact all_local_nonadj_are_two hc n regular xd zd ne.symm
      (fun xz=>not (mem_filter.mpr ⟨zd,xz⟩))
  have cSub : aPorts C⊆DistanceTwo G x := fun _ q=>each_foreign_port_is_distance_two hc cd.symm xp q
  have bTwo : b∈DistanceTwo G x := d2 hc (fun e=>(shore_off D).2 (e ▸ xd))
    (fun bx=>no_common_far far ⟨ax,bx.symm⟩) xy by'.symm
  have d : Disjoint F (aPorts C) :=
    (shore_disjoint cd.symm).mono (fun _ h=>(mem_erase.mp (mem_sdiff.mp h).1).2)
      (filter_subset _ _)
  let A := F∪aPorts C
  have bb : b∉A := by
    intro bm
    rcases mem_union.mp bm with ff|cr
    · exact (shore_off D).2 (mem_erase.mp (mem_sdiff.mp ff).1).2
    exact (shore_off C).2 (mem_filter.mp cr).1
  have s : insert b A⊆DistanceTwo G x := insert_subset bTwo (union_subset fSub cSub)
  have cnt := card_le_card s
  rw [card_insert_of_not_mem bb] at cnt
  have e : A.card=F.card+(aPorts C).card := card_union_of_disjoint d
  have k := distanceTwo_le_of_even 6 x (even x)
  omega

private theorem atleast_two_opposite_bridge_ports (hc : G.Connected)
    (far : 3≤G.dist a b) (D : Cmp G a b)
    (allP : ∀ z∈Shore D,G.Adj a z ∨ G.Adj b z)
    (regular : ∀ z∈Shore D,(inside G (Shore D) z).card=5)
    (ac : 4≤(aPorts D).card) (am : (aPorts D).card≤6)
    {x y : V} (xp : x∈aPorts D) (yp : y∈bPorts D) (xy : G.Adj x y) :
    2≤(bTwos D).card := by
  classical
  let A := (aPorts D).filter (fun x=>∃ y∈bPorts D,G.Adj x y)
  have xA : x∈A := mem_filter.mpr ⟨xp,y,yp,xy⟩
  have ua : A⊆bTwos D := by
    intro u h
    have ⟨up,v,vp,uv⟩ := mem_filter.mp h
    have ⟨ud,au⟩ := mem_filter.mp up
    have bv := (mem_filter.mp vp).2
    have bn : b≠u := fun e=>(shore_off D).2 (e.symm ▸ ud)
    exact mem_inter.mpr ⟨ud,d2 hc bn (fun bu=>no_common_far far ⟨au,bu⟩) bv uv.symm⟩
  apply le_trans _ (card_le_card ua)
  by_contra sm
  have sg : A={x} :=
    (eq_of_subset_of_card_le (singleton_subset_iff.mpr xA) (by simp; omega)).symm
  have reg {z : V} (zp : z∈aPorts D) (zx : z≠x) :
      inside G (Shore D) z ⊆ (aPorts D).erase z := by
    intro u uin
    have ⟨ud,zu⟩ := mem_filter.mp uin
    rcases allP u ud with au|bu
    · exact mem_erase.mpr ⟨zu.ne.symm,mem_filter.mpr ⟨ud,au⟩⟩
    have za : z∈A := mem_filter.mpr ⟨zp,u,mem_filter.mpr ⟨ud,bu⟩,zu⟩
    exact (zx (mem_singleton.mp (sg ▸ za))).elim
  have wn : ((aPorts D).erase x).Nonempty := by
    have w := card_erase_add_one xp
    exact card_pos.mp (by omega)
  obtain ⟨w,wm⟩ := wn
  have wp := (mem_erase.mp wm).2
  have wd := (mem_filter.mp wp).1
  have w5 := regular w wd
  have s := card_le_card (reg wp (mem_erase.mp wm).1)
  have e := card_erase_add_one wp
  have a6 : (aPorts D).card=6 := by omega
  have full {z : V} (zp : z∈aPorts D) (zx : z≠x) :
      inside G (Shore D) z=(aPorts D).erase z := by
    have k := regular z (mem_filter.mp zp).1
    have e := card_erase_add_one zp
    exact eq_of_subset_of_card_le (reg zp zx) (by omega)
  have border : (aPorts D).erase x ⊆ inside G (Shore D) x := by
    intro z zu
    have ⟨zx,zp⟩ := mem_erase.mp zu
    have j : x∈inside G (Shore D) z := (full zp zx).symm ▸ (mem_erase.mpr ⟨zx.symm,xp⟩)
    exact mem_filter.mpr ⟨(mem_filter.mp zp).1,(mem_filter.mp j).2.symm⟩
  have ny : y∉(aPorts D).erase x := by
    intro j
    exact no_common_far far ⟨(mem_filter.mp (mem_erase.mp j).2).2,(mem_filter.mp yp).2⟩
  have ult : insert y ((aPorts D).erase x)⊆inside G (Shore D) x :=
    insert_subset (mem_filter.mpr ⟨(mem_filter.mp yp).1,xy⟩) border
  have n := card_le_card ult
  have ex := card_erase_add_one xp
  rw [card_insert_of_not_mem ny,regular x (mem_filter.mp xp).1] at n
  omega

private theorem ten_shore_has_above_five (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (even : ∀ x,(EvenFrom G x).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D) (ten : (Shore D).card=10)
    (high : ∀ z∈Shore D,6≤G.degree z) :
    ∃ z∈Shore D,6≤(inside G (Shore D) z).card := by
  classical
  by_contra bad
  push_neg at bad
  have regular (z : V) (zd : z∈Shore D) : (inside G (Shore D) z).card=5 := by
    have kv := bad z zd
    have gl := shore_inside_five far D zd (high z zd)
    omega
  have allP (z : V) (zd : z∈Shore D) : G.Adj a z ∨ G.Adj b z := by
    by_contra! none
    have u := card_le_card (neighbor_subset_of_dark D zd none.1 none.2)
    rw [card_neighborFinset_eq_degree,regular z zd] at u
    have e := high z zd
    omega
  have far' : 3≤G.dist b a := by rwa [dist_comm]
  have capA := same_color_upper hc ab conn even cd
  have capB : (bPorts D).card≤6 := by
    have k := same_color_upper (a:=b) (b:=a) hc ab.symm conn even
      (C:=swapCut C) (D:=swapCut D) (fun e=>cd (swapCut.injective e))
    simpa only [aPorts,bPorts,shore_swapCut] using k
  have und : Disjoint (aPorts D) (bPorts D) :=
    disjoint_left.mpr (fun _ ja jb=>no_common_far far ⟨(mem_filter.mp ja).2,(mem_filter.mp jb).2⟩)
  have union : aPorts D∪bPorts D=Shore D := by
    apply Subset.antisymm (union_subset (filter_subset _ _) (filter_subset _ _))
    intro z zd
    exact (allP z zd).elim (fun h=>mem_union_left _ (mem_filter.mpr ⟨zd,h⟩))
      (fun h=>mem_union_right _ (mem_filter.mpr ⟨zd,h⟩))
  have count := card_union_of_disjoint und
  rw [union,ten] at count
  obtain ⟨x,xp,y,yp,xy⟩ := bridge_exists_of_only_ports D ab conn far allP
  have sa := single_opposing_port_of_bridge hc far even cd ten regular xp yp xy
  have b₂ := atleast_two_opposite_bridge_ports hc far D allP regular (by omega) capA xp yp xy
  have sor : (bPorts C).card≤1 ∧ 2≤(aTwos D).card := by
    have c' : swapCut C≠swapCut D := fun e=>cd (swapCut.injective e)
    have ten' : (Shore (swapCut D)).card=10 := by rwa [shore_swapCut]
    have reg' (z : V) (zm : z∈Shore (swapCut D)) : (inside G (Shore (swapCut D)) z).card=5 := by
      rw [shore_swapCut] at zm ⊢
      exact regular z zm
    have all' (z : V) (zm : z∈Shore (swapCut D)) : G.Adj b z ∨ G.Adj a z := by
      rw [shore_swapCut] at zm
      exact (allP z zm).symm
    have yp' : y∈aPorts (swapCut D) := by simpa only [aPorts,bPorts,shore_swapCut] using yp
    have xp' : x∈bPorts (swapCut D) := by simpa only [aPorts,bPorts,shore_swapCut] using xp
    have Bc : (aPorts (swapCut D)).card=(bPorts D).card := by simp only [aPorts,bPorts,shore_swapCut]
    have s := single_opposing_port_of_bridge hc far' even c' ten' reg' yp' xp' xy.symm
    have t := atleast_two_opposite_bridge_ports hc far' (swapCut D) all' reg'
      (by omega) (by omega) yp' xp' xy.symm
    exact ⟨by simpa only [aPorts,bPorts,shore_swapCut] using s,
      by simpa only [aTwos,bTwos,shore_swapCut] using t⟩
  obtain ⟨u,uc,au⟩ := shore_hit_a ab conn C
  obtain ⟨v,vc,bv⟩ := shore_hit_b ab conn C
  have uv : u≠v := fun e=>no_common_far far ⟨au,e.symm ▸ bv⟩
  rcases degree u v uv with u6|v6
  · have uCost := port_cost hc C (mem_filter.mpr ⟨uc,au⟩)
    rw [if_neg (fun bu=>no_common_far far ⟨au,bu⟩),add_zero] at uCost
    have p := two_local_counts _ _ (distinct_shore_twos_dis cd) (DistanceTwo G a)
      inter_subset_right inter_subset_right
    have l := distanceTwo_le_of_even 6 a (even a)
    omega
  have vCost :
      G.degree v≤(bPorts C).card+(bTwos C).card+(if G.Adj a v then 1 else 0) := by
    have z : v∈aPorts (swapCut C) := by
      simp only [aPorts,shore_swapCut,mem_filter]
      exact ⟨vc,bv⟩
    simpa only [aPorts,bPorts,aTwos,bTwos,shore_swapCut] using
      (port_cost (a:=b) (b:=a) hc (swapCut C) z)
  rw [if_neg (fun av=>no_common_far far ⟨av,bv⟩),add_zero] at vCost
  have p : (bTwos C).card+(bTwos D).card≤(DistanceTwo G b).card :=
    two_local_counts _ _ ((shore_disjoint cd).mono inter_subset_left inter_subset_left)
      (DistanceTwo G b) inter_subset_right inter_subset_right
  have l := distanceTwo_le_of_even 6 b (even b)
  omega

#print axioms ten_shore_has_above_five
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
