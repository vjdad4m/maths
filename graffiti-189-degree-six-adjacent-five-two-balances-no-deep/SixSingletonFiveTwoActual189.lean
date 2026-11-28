import SixSingletonFiveTwoCore189
import SixSingletonPositiveProfiles189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_closed shore_disjoint shore_hit_a shore_hit_b
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
open private nearLeft nearRight nearBal deep mainCore strict_port_data_subclass deep_at_most_one
  shallow_partition near_counts deep_internal_degree from SixSingletonFiveGeometry189
open private near_disjoint from SixSingletonPositiveProfiles189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (shore_swapCut depth label_degree label_even traceable_label)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3500000

/-- Five visible vertices, exactly two balanced dark vertices and no deeper
dark vertex, under the additional internal dark minimum-degree bound four. -/
theorem traceable_of_adjacent_singleton_thirteen_five_two_balanced_dark_dense
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13)
    (v5 : (Vis D).card=5) (q2 : (nearBal D).card=2)
    (noDeep : (deep D).card=0) (dense : ∀ z∈Dark D,4≤(inside G (Dark D) z).card) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have ne : a≠b := ab.ne
  obtain ⟨s,sS⟩ := card_eq_one.mp one
  have ss : s∈Shore S := by simp [sS]
  obtain ⟨sa',saS,asa⟩ := shore_hit_a ne conn S
  obtain ⟨sb',sbS,bsb⟩ := shore_hit_b ne conn S
  have as' : G.Adj a s := (show sa'=s by simpa only [sS,mem_singleton] using saS) ▸ asa
  have bs' : G.Adj b s := (show sb'=s by simpa only [sS,mem_singleton] using sbS) ▸ bsb
  have s2 : G.degree s=2 := by
    rw [←card_neighborFinset_eq_degree,singleton_neighborhood_exact sS as' bs',
      card_insert_of_not_mem (by simpa using ne),card_singleton]
  have high {z : V} (ne : z≠s) : 6≤G.degree z := (degree z s ne).resolve_right (by omega)
  have hiD (z : V) (zd : z∈Shore D) : 6≤G.degree z :=
    high (fun h=>disjoint_left.mp (shore_disjoint sd) ss (h ▸ zd))
  have profile := adjacent_singleton_thirteen_visible_profile hc ab even conn degree sd cover one d13
  have ⟨ae,be,upper⟩ :
      (aPorts D\bPorts D).card=1 ∧ (bPorts D\aPorts D).card=1 ∧
        ∀ z∈Shore D,depth G a b z≤3 := by
    rcases profile with ⟨n,l,r,up⟩|⟨n,_,_,_,_,_⟩
    · exact ⟨l,r,up⟩
    omega
  have part := shallow_partition hc D upper
  have swapDark : Dark (swapCut D)=Dark D := by
    simp only [Dark,Vis,shore_swapCut]
    congr 1
    ext z
    simp only [mem_filter]
    rw [or_comm (a:=G.Adj b z) (b:=G.Adj a z)]
  obtain ⟨x,xonly⟩ := card_eq_one.mp ae
  obtain ⟨y,yonly⟩ := card_eq_one.mp be
  have xp : x∈aPorts D\bPorts D := by simp [xonly]
  have yp : y∈bPorts D\aPorts D := by simp [yonly]
  have xx := mem_sdiff.mp xp
  have yy := mem_sdiff.mp yp
  have xyz : x≠y := fun e=>xx.2 (e.symm ▸ yy.1)
  have cX : x∉Common D := fun h=>xx.2 (mem_inter.mp h).2
  have cY : y∉Common D := fun h=>yy.2 (mem_inter.mp h).1
  have VP := common_partition xonly yonly
  have c4 : (Common D).card=3 := by
    rw [VP,card_insert_of_not_mem (by simp [xyz,cX]),card_insert_of_not_mem cY] at v5
    omega
  have size : Fintype.card V=16 := by
    have k := shore_sum_with_cover ne sd cover
    omega
  have shell (z : V) :
      z=a ∨ z=b ∨ z=s ∨ z=x ∨ z=y ∨ z∈Common D ∨ z∈Dark D := by
    by_cases za : z=a
    · exact .inl za
    by_cases zb : z=b
    · exact .inr (.inl zb)
    rcases cover za zb with zs|zd
    · exact .inr (.inr (.inl (by simpa only [sS,mem_singleton] using zs)))
    by_cases p : z∈Vis D
    · rw [VP] at p
      rcases mem_insert.mp p with p|p
      · exact .inr (.inr (.inr (.inl p)))
      rcases mem_insert.mp p with p|p
      · exact .inr (.inr (.inr (.inr (.inl p))))
      exact .inr (.inr (.inr (.inr (.inr (.inl p)))))
    exact .inr (.inr (.inr (.inr (.inr (.inr (mem_sdiff.mpr ⟨zd,p⟩))))))
  have d8 : (Dark D).card=8 := by
    change (Shore D\Vis D).card=8
    rw [card_sdiff (vis_sub D),d13,v5]
  obtain ⟨e,fa,fb,fs,fx,fy,fK,fD⟩ := singleton_five_board_label size a b s x y (Common D) (Dark D) c4 d8 shell
  let J := G.comap e
  let iso : J ≃g G := SimpleGraph.Iso.comap e G
  let L : Finset I5 := univ.filter (fun i=>e i∈nearLeft D)
  let R : Finset I5 := univ.filter (fun i=>e i∈nearRight D)
  let M : Finset I5 := univ.filter (fun i=>e i∈mainCore D)
  have Lm (i : I5) : i∈L↔e i∈nearLeft D := by simp [L]
  have Rm (i : I5) : i∈R↔e i∈nearRight D := by simp [R]
  have Mm (i : I5) : i∈M↔e i∈mainCore D := by simp [M]
  have Left := strict_port_data_subclass hc xonly (nearLeft D) (filter_subset _ _)
    (fun z m=>(mem_filter.mp m).2) hiD
  have Right :
      (∀ z∈nearRight D,G.Adj y z) ∧
        ∀ z∈nearRight D,5≤(inside G (Dark D) z).card := by
    have eq : nearLeft (swapCut D)=nearRight D := by
      unfold nearLeft nearRight strictA strictB
      rw [swapDark]
      simp only [depth,min_comm]
    have s := strict_port_data_subclass (a:=b) (b:=a) hc (D:=swapCut D) (x:=y)
      (by simpa only [aPorts,bPorts,shore_swapCut] using yonly) (nearLeft (swapCut D))
      (filter_subset _ _) (fun z m=>(mem_filter.mp m).2)
      (fun z m=>hiD z (by simpa only [shore_swapCut] using m))
    simpa only [swapDark,eq] using s
  have n2 := adjacent_five_positive_profile_counts hc ab even conn degree sd cover one d13 v5 (by omega)
  have l3r3 : (nearLeft D).card=3 ∧ (nearRight D).card=3 := by
    rcases n2 with h|h|h
    · exact ⟨h.2.2.1,h.2.2.2⟩
    · have v := h.2.1
      omega
    · have v := h.2.1
      omega
  have L6 : 6≤(L∪R).card := by
    have eq : L∪R=univ.filter (fun i=>e i∈nearLeft D∪nearRight D) := by
      ext i
      simp only [mem_union,mem_filter,mem_univ,true_and,Lm,Rm]
    rw [eq,card_preimage_label]
    rw [card_union_of_disjoint (near_disjoint D).1,l3r3.1,l3r3.2]
  have lk : L⊆M := fun i h=>(Mm _).mpr (mem_union_left _ (mem_union_left _ ((Lm _).mp h)))
  have rk : R⊆M := fun i h=>(Mm _).mpr (mem_union_left _ (mem_union_right _ ((Rm _).mp h)))
  have coreSub : mainCore D⊆Dark D := fun i h=>part ▸ (mem_union_left _ h : i∈mainCore D∪nearBal D)
  have mk : M⊆SingletonFive16.D := fun i h=>(fD _).mpr (coreSub ((Mm _).mp h))
  have ld : Disjoint L R := disjoint_left.mpr (fun i il ir=>
    disjoint_left.mp (class_strict_dis D) (mem_filter.mp ((Lm _).mp il)).1 (mem_filter.mp ((Rm _).mp ir)).1)
  have onlyBal {i : V} (ib : i∈nearBal D) : i∉mainCore D := by
    intro h
    have q := (mem_filter.mp ib).2
    have r := (mem_filter.mp (mem_filter.mp ib).1).2
    rcases mem_union.mp h with z|z
    · rcases mem_union.mp z with zl|zr
      · have e := (mem_filter.mp (mem_filter.mp zl).1).2
        omega
      have e := (mem_filter.mp (mem_filter.mp zr).1).2
      omega
    have e := (mem_filter.mp z).2
    omega
  have balCard : (SingletonFive16.D\M).card=2 := by
    have eq : SingletonFive16.D\M=univ.filter (fun i=>e i∈nearBal D) := by
      ext i
      constructor
      · intro h
        have ⟨id,im⟩ := mem_sdiff.mp h
        have ic : e i∈mainCore D∪nearBal D := part.symm ▸ (fD _).mp id
        exact mem_filter.mpr ⟨mem_univ _,(mem_union.mp ic).resolve_left (fun k=>im ((Mm _).mpr k))⟩
      intro h
      have m := (mem_filter.mp h).2
      have k : e i∈Dark D := part ▸ (mem_union_right _ m : e i∈mainCore D∪nearBal D)
      exact mem_sdiff.mpr ⟨(fD _).mpr k,fun m'=>onlyBal m ((Mm _).mp m')⟩
    rw [eq,card_preimage_label]
    exact q2
  have lifted (i j : I5) : J.Adj i j ↔ G.Adj (e i) (e j) := Iff.rfl
  have port_pull {j : I5} (p : e j∈Vis D) : j∈SingletonFive16.P := by
    rw [VP] at p
    rcases mem_insert.mp p with h|h
    · exact mem_insert.mpr (.inl (e.injective (h.trans fx.symm)))
    rcases mem_insert.mp h with h|h
    · exact mem_insert_of_mem (mem_insert.mpr (.inl (e.injective (h.trans fy.symm))))
    exact mem_insert_of_mem (mem_insert_of_mem ((fK _).mpr h))
  have cBound (u : I5) (uc : u∈SingletonFive16.K) (z : I5) (uz : J.Adj u z) :
      z∈insert SingletonFive16.a (insert SingletonFive16.b (SingletonFive16.P∪(SingletonFive16.D\M))) := by
    have uk := (fK _).mp uc
    have ⟨ua,ub⟩ := mem_inter.mp uk
    have uD := (mem_filter.mp ua).1
    have uA := (mem_filter.mp ua).2
    have uB := (mem_filter.mp ub).2
    have edge := (lifted _ _).mp uz
    rcases shore_closed D (e u) uD (e z) edge with q|q|q
    · exact mem_insert.mpr (.inl (e.injective (q.trans fa.symm)))
    · exact mem_insert_of_mem (mem_insert.mpr (.inl (e.injective (q.trans fb.symm))))
    apply mem_insert_of_mem
    apply mem_insert_of_mem
    by_cases vv : e z∈Vis D
    · exact mem_union_left _ (port_pull vv)
    have dz : e z∈Dark D := mem_sdiff.mpr ⟨q,vv⟩
    have az : ¬G.Adj a (e z) := fun h=>vv (mem_filter.mpr ⟨q,.inl h⟩)
    have bz : ¬G.Adj b (e z) := fun h=>vv (mem_filter.mpr ⟨q,.inr h⟩)
    have na : a≠e z := fun h=>(shore_off D).1 (h.symm ▸ q)
    have nb : b≠e z := fun h=>(shore_off D).2 (h.symm ▸ q)
    have da := (mem_filter.mp (d2 hc na az uA edge)).2
    have db := (mem_filter.mp (d2 hc nb bz uB edge)).2
    have bal' : e z∈nearBal D := mem_filter.mpr ⟨mem_filter.mpr ⟨dz,da.trans db.symm⟩,
      by simp [depth,da,db]⟩
    exact mem_union_right _ (mem_sdiff.mpr ⟨(fD _).mpr dz,fun h=>onlyBal bal' ((Mm _).mp h)⟩)
  have dBound (u : I5) (ud : u∈SingletonFive16.D) (z : I5) (uz : J.Adj u z) :
      z∈SingletonFive16.D∪SingletonFive16.P := by
    have ⟨dz,dark⟩ := mem_sdiff.mp ((fD _).mp ud)
    have edge := (lifted _ _).mp uz
    rcases shore_closed D (e u) dz (e z) edge with r|r|r
    · exact (dark (mem_filter.mpr ⟨dz,.inl (r ▸ edge.symm)⟩)).elim
    · exact (dark (mem_filter.mpr ⟨dz,.inr (r ▸ edge.symm)⟩)).elim
    by_cases p : e z∈Vis D
    · exact mem_union_right _ (port_pull p)
    exact mem_union_left _ ((fD _).mpr (mem_sdiff.mpr ⟨r,p⟩))
  have frame : SingletonFive16.ProfileTwo J L R M := by
    refine ⟨lk,rk,mk,L6,ld,?_,?_,balCard,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,cBound,dBound⟩
    · change 2≤(univ.filter (fun i : I5=>e i∈nearLeft D)).card
      rw [card_preimage_label]
      omega
    · change 2≤(univ.filter (fun i : I5=>e i∈nearRight D)).card
      rw [card_preimage_label]
      omega
    · apply (lifted _ _).mpr; rw [fs,fa]; exact as'.symm
    · apply (lifted _ _).mpr; rw [fs,fb]; exact bs'.symm
    · apply (lifted _ _).mpr; rw [fa,fx]; exact (mem_filter.mp xx.1).2
    · apply (lifted _ _).mpr; rw [fb,fy]; exact (mem_filter.mp yy.1).2
    · intro z hz
      apply (lifted _ _).mpr
      rw [fa]
      exact (mem_filter.mp (mem_inter.mp ((fK _).mp hz)).1).2
    · intro z hz
      apply (lifted _ _).mpr
      rw [fb]
      exact (mem_filter.mp (mem_inter.mp ((fK _).mp hz)).2).2
    · intro z hz
      apply (lifted _ _).mpr
      rw [fx]
      exact Left.1 _ ((Lm _).mp hz)
    · intro z hz
      apply (lifted _ _).mpr
      rw [fy]
      exact Right.1 _ ((Rm _).mp hz)
    · intro z hz
      change 5≤(inside (G.comap e) SingletonFive16.D z).card
      rw [inside_label e _ _ fD]
      rcases mem_union.mp ((Mm _).mp hz) with h|h
      · rcases mem_union.mp h with l|r
        · exact Left.2 _ l
        exact Right.2 _ r
      exact deep_internal_degree hc D h (hiD _ (mem_sdiff.mp (mem_filter.mp h).1).1)
    · intro z hz
      rw [label_degree iso]
      exact hiD _ (mem_sdiff.mp ((fD _).mp hz)).1
    · intro z hz
      rw [label_degree iso]
      exact hiD _ (mem_filter.mp (mem_inter.mp ((fK _).mp hz)).1).1
  apply traceable_label iso
  apply SingletonFive16.traceable_of_two_balanced_dark_dense frame (iso.connected_iff.mpr hc)
  · intro z
    rw [label_even iso hc]
    exact even _
  · intro z hz
    change 4≤(inside (G.comap e) SingletonFive16.D z).card
    rw [inside_label e _ _ fD]
    exact dense _ ((fD _).mp hz)

#print axioms traceable_of_adjacent_singleton_thirteen_five_two_balanced_dark_dense
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
