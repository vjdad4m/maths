import SixSingletonFiveLabel189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore mem_shore shore_off shore_closed shore_disjoint shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private Cmp DeletionConnected aPorts bPorts from SixCutFar189
open private Vis vis_sub from AdjacentCutFiveComponents189
open private shore_sum_with_cover from AdjacentCutFiveMixedFourteenSixteen189
open private Dark Common strictA strictB bal singleton_neighborhood_exact a_port_lower_singleton_dist_two
  vis_six_of_nonadjacent_singleton all_dark_depth_two_of_visible_six from SixSingletonGeometry189
open private no_port_domination port_diff_one common_partition class_partition class_strict_dis class_bal_dis
  strict_port_data at_least_two_strict from SixSingletonShape189
open private card_preimage_label inside_label from SixSingletonLabel189
open private d2 from CrossSaturation189
open private step_at_depth_two from SixSingletonShape189
open private singleton_distance from SixCutLowSingleton189
open private visible_subset_singleton_even from SixSingletonGeometry189
open private positive_even_cap from TwoCutOrderCenters189
open private two_local_counts from SixCutFar189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (shore_swapCut depth label_degree label_even traceable_label)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3500000

private noncomputable def nearLeft (D : Cmp G a b) : Finset V :=
  (strictA D).filter (fun z=>depth G a b z=2)
private noncomputable def nearRight (D : Cmp G a b) : Finset V :=
  (strictB D).filter (fun z=>depth G a b z=2)
private noncomputable def nearBal (D : Cmp G a b) : Finset V :=
  (bal D).filter (fun z=>depth G a b z=2)
private noncomputable def deep (D : Cmp G a b) : Finset V :=
  (Dark D).filter (fun z=>depth G a b z=3)
private noncomputable def mainCore (D : Cmp G a b) : Finset V :=
  (nearLeft D∪nearRight D)∪deep D

private theorem strict_port_data_subclass (hc : G.Connected) {D : Cmp G a b} {x : V}
    (xonly : aPorts D\bPorts D={x})
    (T : Finset V) (ts : T⊆strictA D)
    (near : ∀ z∈T,depth G a b z=2) (Dhigh : ∀ z∈Shore D,6≤G.degree z) :
    (∀ z∈T,G.Adj x z) ∧
      ∀ z∈T,5≤(inside G (Dark D) z).card := by
  classical
  have qual {z : V} (zs : z∈T) :
      z∈Dark D ∧ G.dist a z=2 ∧ 2<G.dist b z := by
    have zd := (mem_filter.mp (ts zs)).1
    have p := near z zs
    have l := (mem_filter.mp (ts zs)).2
    change min (G.dist a z) (G.dist b z)=2 at p
    exact ⟨zd,by omega,by omega⟩
  have noB {z v : V} (zs : z∈T) (vb : G.Adj b v) : ¬G.Adj v z := by
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

private theorem depth_bounds (hc : G.Connected) (D : Cmp G a b)
    (upper : ∀ z∈Shore D,depth G a b z≤3) {z : V} (zd : z∈Dark D) :
    depth G a b z=2 ∨ depth G a b z=3 := by
  have ⟨d,n⟩ := mem_sdiff.mp zd
  have p := upper z d
  have ⟨za,zb⟩ := (mem_shore.mp d).choose
  have an : ¬G.Adj a z := fun h=>n (mem_filter.mpr ⟨d,.inl h⟩)
  have bn : ¬G.Adj b z := fun h=>n (mem_filter.mpr ⟨d,.inr h⟩)
  have A := hc.one_lt_dist_of_ne_of_not_adj za.symm an
  have B := hc.one_lt_dist_of_ne_of_not_adj zb.symm bn
  change min (G.dist a z) (G.dist b z)≤3 at p
  change min (G.dist a z) (G.dist b z)=2 ∨ min (G.dist a z) (G.dist b z)=3
  omega

private theorem deep_at_most_one (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7)
    {S D : Cmp G a b} (sd : S≠D) {s : V}
    (sS : Shore S={s}) (as' : G.Adj a s) (bs' : G.Adj b s) (v5 : (Vis D).card=5) :
    (deep D).card≤1 := by
  classical
  have ss : s∈Shore S := by simp [sS]
  have pv := visible_subset_singleton_even sd hc ss as' bs'
  have dw : deep D⊆PositiveEven G s := by
    intro z zm
    have ⟨d,h⟩ := mem_filter.mp zm
    have n : z≠s := fun e=>disjoint_left.mp (shore_disjoint sd) ss
      (e ▸ (mem_sdiff.mp d).1)
    have e := singleton_distance sS hc as' bs' n
    change G.dist s z=1+depth G a b z at e
    have d4 : G.dist s z=4 := by omega
    exact mem_erase.mpr ⟨n,mem_filter.mpr ⟨mem_univ _,by rw [d4]; decide⟩⟩
  have apart : Disjoint (Vis D) (deep D) := disjoint_left.mpr
    (fun _ h j=>(mem_sdiff.mp (mem_filter.mp j).1).2 h)
  have bound := two_local_counts _ _ apart _ pv dw
  have cap := positive_even_cap (d:=6) (even s)
  omega

private theorem shallow_partition (hc : G.Connected) (D : Cmp G a b)
    (upper : ∀ z∈Shore D,depth G a b z≤3) :
    mainCore D∪nearBal D=Dark D := by
  ext z
  constructor
  · intro zm
    rcases mem_union.mp zm with h|h
    · rcases mem_union.mp h with n|n
      · rcases mem_union.mp n with l|r
        · exact (mem_filter.mp (mem_filter.mp l).1).1
        exact (mem_filter.mp (mem_filter.mp r).1).1
      exact (mem_filter.mp n).1
    exact (mem_filter.mp (mem_filter.mp h).1).1
  intro zm
  rcases depth_bounds hc D upper zm with two|three
  · rcases lt_trichotomy (G.dist a z) (G.dist b z) with h|h|h
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _
        (mem_filter.mpr ⟨mem_filter.mpr ⟨zm,h⟩,two⟩)))
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨zm,h⟩,two⟩)
    exact mem_union_left _ (mem_union_left _ (mem_union_right _
      (mem_filter.mpr ⟨mem_filter.mpr ⟨zm,h⟩,two⟩)))
  exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨zm,three⟩))

private theorem nearLeft_two {D : Cmp G a b} {z : V} (zm : z∈nearLeft D) :
    G.dist a z=2 := by
  have r := (mem_filter.mp zm).2
  have l := (mem_filter.mp (mem_filter.mp zm).1).2
  change min (G.dist a z) (G.dist b z)=2 at r
  omega

private theorem nearRight_two {D : Cmp G a b} {z : V} (zm : z∈nearRight D) :
    G.dist b z=2 := by
  have r := (mem_filter.mp zm).2
  have l := (mem_filter.mp (mem_filter.mp zm).1).2
  change min (G.dist a z) (G.dist b z)=2 at r
  omega

private theorem nearBal_two {D : Cmp G a b} {z : V} (zm : z∈nearBal D) :
    G.dist a z=2 ∧ G.dist b z=2 := by
  have r := (mem_filter.mp zm).2
  have l := (mem_filter.mp (mem_filter.mp zm).1).2
  change min (G.dist a z) (G.dist b z)=2 at r
  omega

private theorem near_counts (hc : G.Connected) (D : Cmp G a b)
    (upper : ∀ z∈Shore D,depth G a b z≤3)
    (dark8 : (Dark D).card=8) (deep1 : (deep D).card≤1) (bal1 : (nearBal D).card≤1)
    (even : ∀ z,(EvenFrom G z).card≤7) {x y : V}
    (xv : x∈Vis D) (yv : y∈Vis D)
    (xd : G.dist b x=2) (yd : G.dist a y=2) :
    2≤(nearLeft D).card ∧ 2≤(nearRight D).card ∧ 6≤(nearLeft D∪nearRight D).card := by
  classical
  have count := card_union_le (mainCore D) (nearBal D)
  rw [shallow_partition hc D upper,dark8] at count
  have core := card_union_le (nearLeft D∪nearRight D) (deep D)
  change (mainCore D).card≤_ at core
  have lr := card_union_le (nearLeft D) (nearRight D)
  have divA : Disjoint (nearLeft D) (nearBal D) := by
    apply disjoint_left.mpr
    intro z zl zb
    have d := nearBal_two zb
    have l := (mem_filter.mp (mem_filter.mp zl).1).2
    omega
  have divB : Disjoint (nearRight D) (nearBal D) := by
    apply disjoint_left.mpr
    intro z zl zb
    have d := nearBal_two zb
    have l := (mem_filter.mp (mem_filter.mp zl).1).2
    omega
  have countA : (nearLeft D).card+(nearBal D).card≤5 := by
    have not : y∉nearLeft D∪nearBal D := by
      intro h
      rcases mem_union.mp h with h|h <;> exact (mem_sdiff.mp (mem_filter.mp (mem_filter.mp h).1).1).2 yv
    have n : insert y (nearLeft D∪nearBal D)⊆DistanceTwo G a :=
      insert_subset (mem_filter.mpr ⟨mem_univ _,yd⟩)
        (union_subset (fun _ h=>mem_filter.mpr ⟨mem_univ _,nearLeft_two h⟩)
          (fun _ h=>mem_filter.mpr ⟨mem_univ _,(nearBal_two h).1⟩))
    have hh := card_le_card n
    rw [card_insert_of_not_mem not,card_union_of_disjoint divA] at hh
    have cap := distanceTwo_le_of_even 6 a (even a)
    omega
  have countB : (nearRight D).card+(nearBal D).card≤5 := by
    have not : x∉nearRight D∪nearBal D := by
      intro h
      rcases mem_union.mp h with h|h <;> exact (mem_sdiff.mp (mem_filter.mp (mem_filter.mp h).1).1).2 xv
    have n : insert x (nearRight D∪nearBal D)⊆DistanceTwo G b :=
      insert_subset (mem_filter.mpr ⟨mem_univ _,xd⟩)
        (union_subset (fun _ h=>mem_filter.mpr ⟨mem_univ _,nearRight_two h⟩)
          (fun _ h=>mem_filter.mpr ⟨mem_univ _,(nearBal_two h).2⟩))
    have hh := card_le_card n
    rw [card_insert_of_not_mem not,card_union_of_disjoint divB] at hh
    have cap := distanceTwo_le_of_even 6 b (even b)
    omega
  omega

private theorem deep_internal_degree (_hc : G.Connected) (D : Cmp G a b)
    {u : V} (ud : u∈deep D) (hi : 6≤G.degree u) : 5≤(inside G (Dark D) u).card := by
  classical
  have ⟨dark,dep⟩ := mem_filter.mp ud
  have ⟨du,no⟩ := mem_sdiff.mp dark
  have sub : G.neighborFinset u⊆inside G (Dark D) u := by
    intro z zm
    have uz := (mem_neighborFinset _ _ _).mp zm
    have zd : z∈Shore D := by
      rcases shore_closed D u du z uz with p|p|p
      · exact (no (mem_filter.mpr ⟨du,.inl (p ▸ uz.symm)⟩)).elim
      · exact (no (mem_filter.mpr ⟨du,.inr (p ▸ uz.symm)⟩)).elim
      exact p
    have zNo : z∉Vis D := by
      intro p
      have nu := dep
      change min (G.dist a u) (G.dist b u)=3 at nu
      rcases (mem_filter.mp p).2 with az|bz
      · have k := G.dist_le (Walk.cons az (Walk.cons uz.symm .nil))
        simp at k
        omega
      have k := G.dist_le (Walk.cons bz (Walk.cons uz.symm .nil))
      simp at k
      omega
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨zd,zNo⟩,uz⟩
  have n := card_le_card sub
  rw [card_neighborFinset_eq_degree] at n
  omega

#print axioms near_counts
#print axioms deep_internal_degree
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
