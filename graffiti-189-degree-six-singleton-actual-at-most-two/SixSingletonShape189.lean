import SixSingletonGeometry189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore mem_shore shore_off shore_closed shore_disjoint shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private Cmp DeletionConnected aPorts bPorts two_local_counts from SixCutFar189
open private Vis vis_sub from AdjacentCutFiveComponents189
open private singleton_distance from SixCutLowSingleton189
open private predecessor_of_positive_dist from AdjacentCutFiveSixteenSingletonDepth189
open private Dark Common strictA strictB bal port_union_vis singleton_neighborhood_exact
  a_port_lower_singleton_dist_two vis_six_of_nonadjacent_singleton all_dark_depth_two_of_visible_six
  from SixSingletonGeometry189
open private d2 from CrossSaturation189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (depth shore_swapCut)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem step_at_depth_two (hc : G.Connected) {D : Cmp G a b} {z : V}
    (zd : z∈Dark D) (m : G.dist a z=2) :
    ∃ v∈aPorts D,G.Adj v z := by
  have ⟨dm,dn⟩ := mem_sdiff.mp zd
  have m' : G.dist z a=2 := by rwa [dist_comm]
  obtain ⟨u,zu,um⟩ := predecessor_of_positive_dist hc (x:=z) (t:=a) (by omega)
  have ud : u∈Shore D := by
    rcases shore_closed D z dm u zu with e|e|e
    · exact (dn (mem_filter.mpr ⟨dm,.inl (e ▸ zu.symm)⟩)).elim
    · exact (dn (mem_filter.mpr ⟨dm,.inr (e ▸ zu.symm)⟩)).elim
    exact e
  have d : G.dist a u=1 := by rw [dist_comm]; omega
  exact ⟨u,mem_filter.mpr ⟨ud,dist_eq_one_iff_adj.mp d⟩,zu.symm⟩

private theorem no_port_domination (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7)
    {D : Cmp G a b} (d7 : (Dark D).card=7)
    (depth2 : ∀ z∈Dark D,depth G a b z=2) :
    ¬aPorts D⊆bPorts D := by
  intro sub
  have darkTwo : Dark D⊆DistanceTwo G b := by
    intro z zd
    have step := depth2 z zd
    change min (G.dist a z) (G.dist b z)=2 at step
    have no : ¬G.Adj b z := fun bz=>(mem_sdiff.mp zd).2 (mem_filter.mpr ⟨(mem_sdiff.mp zd).1,.inr bz⟩)
    have ne : b≠z := fun e=>(shore_off D).2 (e.symm ▸ (mem_sdiff.mp zd).1)
    by_cases two : G.dist b z=2
    · exact mem_filter.mpr ⟨mem_univ _,two⟩
    have a2 : G.dist a z=2 := by omega
    obtain ⟨v,vp,vz⟩ := step_at_depth_two hc zd a2
    exact d2 hc ne no (mem_filter.mp (sub vp)).2 vz
  have p := card_le_card darkTwo
  have q := distanceTwo_le_of_even 6 b (even b)
  omega

private theorem port_diff_one {D : Cmp G a b} (sz : (Vis D).card=6)
    (b5 : 5≤(bPorts D).card) (neq : ¬aPorts D⊆bPorts D) :
    (aPorts D\bPorts D).card=1 := by
  have e : Vis D\bPorts D = aPorts D\bPorts D := by rw [←port_union_vis]; ext z; simp; tauto
  have sub : bPorts D⊆Vis D := by rw [←port_union_vis]; exact subset_union_right
  have p : (aPorts D\bPorts D).Nonempty := by
    obtain ⟨u,ua,ub⟩ := not_subset.mp neq
    exact ⟨u,mem_sdiff.mpr ⟨ua,ub⟩⟩
  have pos := card_pos.mpr p
  have n := card_sdiff sub
  rw [e,sz] at n
  omega

private theorem common_partition {D : Cmp G a b} {x y : V}
    (xs : aPorts D\bPorts D={x}) (ys : bPorts D\aPorts D={y}) :
    Vis D=insert x (insert y (Common D)) := by
  rw [←port_union_vis]
  ext z
  have p : z=x ↔ z∈aPorts D ∧ z∉bPorts D := by rw [←mem_sdiff, xs,mem_singleton]
  have q : z=y ↔ z∈bPorts D ∧ z∉aPorts D := by rw [←mem_sdiff,ys,mem_singleton]
  simp only [Common,mem_union,mem_insert,p,q,mem_inter]
  tauto

private theorem class_partition (D : Cmp G a b) :
    (strictA D∪strictB D)∪bal D=Dark D := by
  ext z
  constructor
  · intro m
    rcases mem_union.mp m with h|h
    · rcases mem_union.mp h with l|r
      · exact (mem_filter.mp l).1
      exact (mem_filter.mp r).1
    exact (mem_filter.mp h).1
  intro m
  rcases lt_trichotomy (G.dist a z) (G.dist b z) with l|e|r
  · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨m,l⟩))
  · exact mem_union_right _ (mem_filter.mpr ⟨m,e⟩)
  exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨m,r⟩))

private theorem class_strict_dis (D : Cmp G a b) : Disjoint (strictA D) (strictB D) := by
  apply disjoint_left.mpr
  intro z za zb
  have p := (mem_filter.mp za).2
  have q := (mem_filter.mp zb).2
  omega

private theorem class_bal_dis (D : Cmp G a b) : Disjoint (strictA D∪strictB D) (bal D) := by
  apply disjoint_left.mpr
  intro z zp zb
  have p := (mem_filter.mp zb).2
  rcases mem_union.mp zp with a|b
  · have q := (mem_filter.mp a).2
    omega
  have q := (mem_filter.mp b).2
  omega

private theorem strict_port_data (hc : G.Connected) {D : Cmp G a b} {x : V}
    (xonly : aPorts D\bPorts D={x})
    (near : ∀ z∈Dark D,depth G a b z=2) (Dhigh : ∀ z∈Shore D,6≤G.degree z) :
    (∀ z∈strictA D,G.Adj x z) ∧
      ∀ z∈strictA D,5≤(inside G (Dark D) z).card := by
  classical
  have qual {z : V} (zs : z∈strictA D) :
      z∈Dark D ∧ G.dist a z=2 ∧ 2<G.dist b z := by
    have zd := (mem_filter.mp zs).1
    have p := near z zd
    have l := (mem_filter.mp zs).2
    change min (G.dist a z) (G.dist b z)=2 at p
    exact ⟨zd,by omega,by omega⟩
  have noB {z v : V} (zs : z∈strictA D) (vb : G.Adj b v) : ¬G.Adj v z := by
    intro vz
    have t := G.dist_le (Walk.cons vb (Walk.cons vz .nil))
    simp at t
    have q := (qual zs).2.2
    omega
  constructor
  · intro z zs
    have ⟨zd,two,_⟩ := qual zs
    obtain ⟨v,vp,vz⟩ := step_at_depth_two hc zd two
    have vb : v∉bPorts D := fun vb=>noB zs (mem_filter.mp vb).2 vz
    have e : v=x := by
      have m : v∈aPorts D\bPorts D := mem_sdiff.mpr ⟨vp,vb⟩
      simpa only [xonly,mem_singleton] using m
    exact e ▸ vz
  intro z zs
  have ⟨zd,_,_⟩ := qual zs
  have ⟨dd,dark⟩ := mem_sdiff.mp zd
  have sub : G.neighborFinset z⊆insert x (inside G (Dark D) z) := by
    intro v vn
    have zv := (mem_neighborFinset _ _ _).mp vn
    have vd : v∈Shore D := by
      rcases shore_closed D z dd v zv with e|e|e
      · exact (dark (mem_filter.mpr ⟨dd,.inl (e ▸ zv.symm)⟩)).elim
      · exact (dark (mem_filter.mpr ⟨dd,.inr (e ▸ zv.symm)⟩)).elim
      exact e
    by_cases vv : v∈Vis D
    · have ap : G.Adj a v := ((mem_filter.mp vv).2).resolve_right (fun bv=>noB zs bv zv.symm)
      have pb : v∉bPorts D := fun m=>noB zs (mem_filter.mp m).2 zv.symm
      have r : v∈aPorts D\bPorts D := mem_sdiff.mpr ⟨mem_filter.mpr ⟨vd,ap⟩,pb⟩
      exact mem_insert.mpr (.inl (by simpa only [xonly,mem_singleton] using r))
    exact mem_insert_of_mem (mem_filter.mpr ⟨mem_sdiff.mpr ⟨vd,vv⟩,zv⟩)
  have c := card_le_card sub
  rw [card_neighborFinset_eq_degree] at c
  have s := card_insert_le x (inside G (Dark D) z)
  have h := Dhigh z dd
  omega

private theorem at_least_two_strict (_hc : G.Connected) (ab2 : G.dist a b=2)
    (even : ∀ z,(EvenFrom G z).card≤7)
    {D : Cmp G a b} (d7 : (Dark D).card=7)
    (near : ∀ z∈Dark D,depth G a b z=2) :
    2≤(strictA D).card ∧ 2≤(strictB D).card := by
  classical
  have n : (strictA D).card+(strictB D).card+(bal D).card=7 := by
    have p := card_union_of_disjoint (class_bal_dis D)
    rw [class_partition,d7,card_union_of_disjoint (class_strict_dis D)] at p
    omega
  have allA : strictA D⊆DistanceTwo G a := by
    intro z zm
    have ⟨zD,l⟩ := mem_filter.mp zm
    have r := near z zD
    change min (G.dist a z) (G.dist b z)=2 at r
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have allB : strictB D⊆DistanceTwo G b := by
    intro z zm
    have ⟨zD,l⟩ := mem_filter.mp zm
    have r := near z zD
    change min (G.dist a z) (G.dist b z)=2 at r
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have via {t : V} (T : Finset V) (d : Disjoint T (bal D))
      (sub : T⊆DistanceTwo G t)
      (evenT : (DistanceTwo G t).card≤6) {o : V} (ot : G.dist t o=2)
      (no : o∉T) (noBal : o∉bal D) (eq : ∀ z∈bal D,G.dist t z=2) :
      T.card+(bal D).card≤5 := by
    have h : insert o (T∪bal D)⊆DistanceTwo G t :=
      insert_subset (mem_filter.mpr ⟨mem_univ _,ot⟩)
        (union_subset sub (fun z zm=>mem_filter.mpr ⟨mem_univ _,eq z zm⟩))
    have c := card_le_card h
    rw [card_insert_of_not_mem (by simp [no,noBal]),card_union_of_disjoint d] at c
    omega
  have nonA : a∉Dark D := fun sm=>(shore_off D).1 (mem_sdiff.mp sm).1
  have nonB : b∉Dark D := fun sm=>(shore_off D).2 (mem_sdiff.mp sm).1
  have da : Disjoint (strictA D) (bal D) := (class_bal_dis D).mono_left subset_union_left
  have db : Disjoint (strictB D) (bal D) := (class_bal_dis D).mono_left subset_union_right
  have M := via (t:=a) (strictA D) da allA (distanceTwo_le_of_even 6 a (even a)) ab2
    (fun h=>nonB (mem_filter.mp h).1) (fun h=>nonB (mem_filter.mp h).1)
    (fun z zm=>by
      have ⟨d,e⟩ := mem_filter.mp zm
      have p := near z d
      change min (G.dist a z) (G.dist b z)=2 at p
      omega)
  have bb2 : G.dist b a=2 := by rwa [dist_comm]
  have N := via (t:=b) (strictB D) db allB (distanceTwo_le_of_even 6 b (even b)) bb2
    (fun h=>nonA (mem_filter.mp h).1) (fun h=>nonA (mem_filter.mp h).1)
    (fun z zm=>by
      have ⟨d,e⟩ := mem_filter.mp zm
      have p := near z d
      change min (G.dist a z) (G.dist b z)=2 at p
      omega)
  omega

#print axioms no_port_domination
#print axioms strict_port_data
#print axioms at_least_two_strict
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
