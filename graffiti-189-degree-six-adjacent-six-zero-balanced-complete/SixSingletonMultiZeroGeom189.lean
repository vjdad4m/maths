import SixSingletonAdjacentSlots189
import SixSingletonMultiZeroBoard189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore mem_shore shore_off shore_closed shore_disjoint shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private Cmp DeletionConnected aPorts bPorts from SixCutFar189
open private Vis vis_sub from AdjacentCutFiveComponents189
open private Dark Common strictA strictB bal singleton_neighborhood_exact port_union_vis from SixSingletonGeometry189
open private step_at_depth_two class_partition class_strict_dis from SixSingletonShape189
open private nearBal from SixSingletonFiveGeometry189
open private shore_sum_with_cover from AdjacentCutFiveMixedFourteenSixteen189
open private d2 from CrossSaturation189
open private predecessor_of_positive_dist from AdjacentCutFiveSixteenSingletonDepth189
open FiveAdjacent (depth)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private noncomputable def EA (D : Cmp G a b) := aPorts D\bPorts D
private noncomputable def EB (D : Cmp G a b) := bPorts D\aPorts D

structure ZeroBalanceData (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {a b : V} (D : Cmp G a b) (s : V) : Prop where
  sa : G.Adj s a
  sb : G.Adj s b
  dark7 : (Dark D).card=7
  darkPart : strictA D∪strictB D=Dark D
  visiblePart : EA D∪EB D∪Common D=Vis D
  cover : ∀ z : V,z=a ∨ z=b ∨ z=s ∨ z∈Vis D ∨ z∈Dark D
  eA : ∀ x∈EA D,G.Adj a x ∧ ¬G.Adj b x
  eB : ∀ x∈EB D,G.Adj b x ∧ ¬G.Adj a x
  common : ∀ c∈Common D,G.Adj a c ∧ G.Adj b c
  rootsA : ∀ z∈strictA D,∃ x∈EA D,G.Adj x z
  rootsB : ∀ z∈strictB D,∃ x∈EB D,G.Adj x z
  xSense : ∀ x∈EA D,∀ z∈Dark D,G.Adj x z → z∈strictA D
  ySense : ∀ y∈EB D,∀ z∈Dark D,G.Adj y z → z∈strictB D
  darkFour : ∀ z∈Dark D,4≤(inside G (Dark D) z).card
  commonFour : ∀ c∈Common D,4≤(inside G (Vis D) c).card
  inactiveA : ∀ x∈EA D, (¬∃ z∈strictA D,G.Adj x z) → ∀ c∈Common D,G.Adj x c
  inactiveB : ∀ y∈EB D, (¬∃ z∈strictB D,G.Adj y z) → ∀ c∈Common D,G.Adj y c

theorem isolate_zero_balance_geometry
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cov : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13)
    (v6 : (Vis D).card=6) (zero : (nearBal D).card=0) :
    ∃ s,ZeroBalanceData G D s := by
  classical
  obtain ⟨s,sS⟩ := card_eq_one.mp one
  have ss : s∈Shore S := by simp [sS]
  obtain ⟨p,ps,ap⟩ := shore_hit_a ab.ne conn S
  obtain ⟨q,qs,bq⟩ := shore_hit_b ab.ne conn S
  have as' : G.Adj a s := (show p=s by simpa only [sS,mem_singleton] using ps) ▸ ap
  have bs' : G.Adj b s := (show q=s by simpa only [sS,mem_singleton] using qs) ▸ bq
  have s2 : G.degree s=2 := by
    rw [←card_neighborFinset_eq_degree,singleton_neighborhood_exact sS as' bs',
      card_insert_of_not_mem (by simpa using ab.ne),card_singleton]
  have high (z : V) (zd : z∈Shore D) : 6≤G.degree z := by
    have ne : z≠s := fun e=>disjoint_left.mp (shore_disjoint sd) ss (e ▸ zd)
    exact (degree z s ne).resolve_right (by omega)
  have profile := adjacent_singleton_thirteen_visible_profile hc ab even conn degree sd cov one d13
  have ⟨A2,B2,near⟩ :
      (EA D).card≤2 ∧ (EB D).card≤2 ∧ ∀ z∈Dark D,depth G a b z=2 := by
    rcases profile with ⟨n,_,_,_⟩|⟨_,_,aa,_,bb,nu⟩
    · omega
    exact ⟨aa,bb,nu⟩
  have eq : bal D=nearBal D := by
    apply Subset.antisymm _ (filter_subset _ _)
    intro z zm
    exact mem_filter.mpr ⟨zm,near z (mem_filter.mp zm).1⟩
  have nb : bal D=∅ := card_eq_zero.mp (show (bal D).card=0 from by rw [eq,zero])
  have dp : strictA D∪strictB D=Dark D := by
    have r := class_partition D
    simpa [nb] using r
  have vp : EA D∪EB D∪Common D=Vis D := by
    rw [←port_union_vis]
    ext z
    simp only [EA,EB,Common,mem_union,mem_sdiff,mem_inter]
    tauto
  have d7 : (Dark D).card=7 := by
    change (Shore D\Vis D).card=7
    rw [card_sdiff (vis_sub D),d13,v6]
  have jA {z : V} (zA : z∈strictA D) : G.dist a z=2 ∧ 2<G.dist b z := by
    have ne := near z (mem_filter.mp zA).1
    have lt := (mem_filter.mp zA).2
    change min (G.dist a z) (G.dist b z)=2 at ne
    omega
  have jB {z : V} (zB : z∈strictB D) : G.dist b z=2 ∧ 2<G.dist a z := by
    have ne := near z (mem_filter.mp zB).1
    have lt := (mem_filter.mp zB).2
    change min (G.dist a z) (G.dist b z)=2 at ne
    omega
  have rootA (z : V) (zl : z∈strictA D) : ∃ x∈EA D,G.Adj x z := by
    obtain ⟨x,xa,xz⟩ := step_at_depth_two hc (mem_filter.mp zl).1 (jA zl).1
    have nb : x∉bPorts D := by
      intro h
      have k := G.dist_le (Walk.cons (mem_filter.mp h).2 (Walk.cons xz .nil))
      simp at k
      have q := (jA zl).2
      omega
    exact ⟨x,mem_sdiff.mpr ⟨xa,nb⟩,xz⟩
  have rootB (z : V) (zr : z∈strictB D) : ∃ x∈EB D,G.Adj x z := by
    have ⟨zd,zn⟩ := mem_sdiff.mp (mem_filter.mp zr).1
    have b2 : G.dist z b=2 := by rw [dist_comm]; exact (jB zr).1
    obtain ⟨u,zu,um⟩ := predecessor_of_positive_dist hc (x:=z) (t:=b) (by omega)
    have du : u∈Shore D := by
      rcases shore_closed D z zd u zu with e|e|e
      · exact (zn (mem_filter.mpr ⟨zd,.inl (e ▸ zu.symm)⟩)).elim
      · exact (zn (mem_filter.mpr ⟨zd,.inr (e ▸ zu.symm)⟩)).elim
      exact e
    have d : G.dist b u=1 := by rw [dist_comm]; omega
    have bu := dist_eq_one_iff_adj.mp d
    have an : u∉aPorts D := by
      intro h
      have k := G.dist_le (Walk.cons (mem_filter.mp h).2 (Walk.cons zu.symm .nil))
      simp at k
      have p := (jB zr).2
      omega
    exact ⟨u,mem_sdiff.mpr ⟨mem_filter.mpr ⟨du,bu⟩,an⟩,zu.symm⟩
  have ax (x : V) (xm : x∈EA D) : G.Adj a x ∧ ¬G.Adj b x :=
    ⟨(mem_filter.mp (mem_sdiff.mp xm).1).2,fun h=>(mem_sdiff.mp xm).2
      (mem_filter.mpr ⟨(mem_filter.mp (mem_sdiff.mp xm).1).1,h⟩)⟩
  have by' (y : V) (ym : y∈EB D) : G.Adj b y ∧ ¬G.Adj a y :=
    ⟨(mem_filter.mp (mem_sdiff.mp ym).1).2,fun h=>(mem_sdiff.mp ym).2
      (mem_filter.mpr ⟨(mem_filter.mp (mem_sdiff.mp ym).1).1,h⟩)⟩
  have xSense (x : V) (xm : x∈EA D) (z : V) (zd : z∈Dark D) (xz : G.Adj x z) :
      z∈strictA D := by
    have c : z∈strictA D∪strictB D := dp.symm ▸ zd
    refine (mem_union.mp c).resolve_right ?_
    intro zr
    have p := G.dist_le (Walk.cons (ax x xm).1 (Walk.cons xz .nil))
    simp at p
    have h := (jB zr).2
    omega
  have ySense (y : V) (ym : y∈EB D) (z : V) (zd : z∈Dark D) (yz : G.Adj y z) :
      z∈strictB D := by
    have c : z∈strictA D∪strictB D := dp.symm ▸ zd
    refine (mem_union.mp c).resolve_left ?_
    intro zl
    have p := G.dist_le (Walk.cons (by' y ym).1 (Walk.cons yz .nil))
    simp at p
    have h := (jA zl).2
    omega
  have common (c : V) (ck : c∈Common D) : G.Adj a c ∧ G.Adj b c :=
    ⟨(mem_filter.mp (mem_inter.mp ck).1).2,(mem_filter.mp (mem_inter.mp ck).2).2⟩
  have cNo (c : V) (ck : c∈Common D) (z : V) (zd : z∈Dark D) : ¬G.Adj c z := by
    intro cz
    have ca := G.dist_le (Walk.cons (common c ck).1 (Walk.cons cz .nil))
    have cb := G.dist_le (Walk.cons (common c ck).2 (Walk.cons cz .nil))
    simp at ca cb
    have p : z∈strictA D∪strictB D := dp.symm ▸ zd
    rcases mem_union.mp p with l|r
    · have h := (jA l).2
      omega
    have h := (jB r).2
    omega
  have locality {z : V} (zd : z∈Dark D) {w : V} (zw : G.Adj z w) :
      w∈Shore D := by
    have ⟨r,n⟩ := mem_sdiff.mp zd
    rcases shore_closed D z r w zw with e|e|e
    · exact (n (mem_filter.mpr ⟨r,.inl (e ▸ zw.symm)⟩)).elim
    · exact (n (mem_filter.mpr ⟨r,.inr (e ▸ zw.symm)⟩)).elim
    exact e
  have darkDegree (z : V) (zd : z∈Dark D) : 4≤(inside G (Dark D) z).card := by
    have f {P : Finset V} (p : P.card≤2)
        (h : ∀ w∈Vis D,G.Adj z w → w∈P) : 4≤(inside G (Dark D) z).card := by
      have sub : G.neighborFinset z⊆inside G (Dark D) z∪P := by
        intro w wm
        have zw := (mem_neighborFinset _ _ _).mp wm
        by_cases r : w∈Vis D
        · exact mem_union_right _ (h w r zw)
        exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨locality zd zw,r⟩,zw⟩)
      have c := card_le_card sub
      rw [card_neighborFinset_eq_degree] at c
      have u := card_union_le (inside G (Dark D) z) P
      have h := high z (mem_sdiff.mp zd).1
      omega
    have op : z∈strictA D∪strictB D := dp.symm ▸ zd
    rcases mem_union.mp op with za|zb
    · apply f A2
      intro w wv zw
      rw [←vp] at wv
      rcases mem_union.mp wv with s|s
      · rcases mem_union.mp s with a|b
        · exact a
        exact (disjoint_left.mp (class_strict_dis D) za (ySense w b z zd zw.symm)).elim
      exact (cNo w s z zd zw.symm).elim
    apply f B2
    intro w wv zw
    rw [←vp] at wv
    rcases mem_union.mp wv with s|s
    · rcases mem_union.mp s with a|b
      · exact (disjoint_left.mp (class_strict_dis D) (xSense w a z zd zw.symm) zb).elim
      exact b
    exact (cNo w s z zd zw.symm).elim
  have commonLocal (c : V) (ck : c∈Common D) : 4≤(inside G (Vis D) c).card := by
    have cd := (mem_filter.mp (mem_inter.mp ck).1).1
    have sub : G.neighborFinset c⊆insert a (insert b (inside G (Vis D) c)) := by
      intro z zm
      have cz := (mem_neighborFinset _ _ _).mp zm
      rcases shore_closed D c cd z cz with e|e|zz
      · exact mem_insert.mpr (.inl e)
      · exact mem_insert_of_mem (mem_insert.mpr (.inl e))
      have v : z∈Vis D := Classical.byContradiction (fun n=>cNo c ck z (mem_sdiff.mpr ⟨zz,n⟩) cz)
      exact mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨v,cz⟩))
    have n := card_le_card sub
    rw [card_neighborFinset_eq_degree] at n
    have i := card_insert_le a (insert b (inside G (Vis D) c))
    have j := card_insert_le b (inside G (Vis D) c)
    have h := high c cd
    omega
  have all_vis_of_inactive {z t u : V} (zd : z∈Shore D) (zv : z∈Vis D)
      (h1 : t=a ∧ u=b ∨ t=b ∧ u=a) (not : ¬G.Adj z u)
      (noDark : ∀ w∈Dark D,¬G.Adj z w) :
      (Vis D).erase z⊆G.neighborFinset z := by
    have sub : G.neighborFinset z⊆insert t ((Vis D).erase z) := by
      intro w wm
      have zw := (mem_neighborFinset _ _ _).mp wm
      rcases shore_closed D z zd w zw with e|e|wd
      · rcases h1 with r|r
        · exact mem_insert.mpr (.inl (e.trans r.1.symm))
        exact (not (r.2 ▸ e ▸ zw)).elim
      · rcases h1 with r|r
        · exact (not (r.2.symm ▸ e ▸ zw)).elim
        exact mem_insert.mpr (.inl (e.trans r.1.symm))
      have wv : w∈Vis D := Classical.byContradiction (fun p=>noDark w (mem_sdiff.mpr ⟨wd,p⟩) zw)
      exact mem_insert_of_mem (mem_erase.mpr ⟨zw.ne.symm,wv⟩)
    have cap := card_insert_le t ((Vis D).erase z)
    have v := card_erase_add_one zv
    have r : (insert t ((Vis D).erase z)).card≤6 := by omega
    have eq := eq_of_subset_of_card_le sub (by rw [card_neighborFinset_eq_degree]; exact r.trans (high z zd))
    rw [eq]
    intro w wm
    exact mem_insert_of_mem wm
  have cover (z : V) : z=a ∨ z=b ∨ z=s ∨ z∈Vis D ∨ z∈Dark D := by
    by_cases za : z=a
    · exact .inl za
    by_cases zb : z=b
    · exact .inr (.inl zb)
    rcases cov za zb with zS|zD
    · exact .inr (.inr (.inl (by simpa only [sS,mem_singleton] using zS)))
    by_cases zv : z∈Vis D
    · exact .inr (.inr (.inr (.inl zv)))
    exact .inr (.inr (.inr (.inr (mem_sdiff.mpr ⟨zD,zv⟩))))
  refine ⟨s,as'.symm,bs'.symm,d7,dp,vp,cover,ax,by',common,rootA,rootB,xSense,ySense,darkDegree,commonLocal,?_,?_⟩
  · intro x xm no c ck
    have xd := (mem_filter.mp (mem_sdiff.mp xm).1).1
    have xv : x∈Vis D := mem_filter.mpr ⟨xd,.inl (ax x xm).1⟩
    have noDark : ∀ z∈Dark D,¬G.Adj x z := fun z zm e=>no ⟨z,xSense x xm z zm e,e⟩
    have ne : c≠x := fun e=>(ax x xm).2 (e ▸ (common c ck).2)
    have cv : c∈Vis D := mem_filter.mpr ⟨(mem_filter.mp (mem_inter.mp ck).1).1,.inl (common c ck).1⟩
    exact (mem_neighborFinset _ _ _).mp (all_vis_of_inactive xd xv (t:=a) (u:=b) (.inl ⟨rfl,rfl⟩)
      (fun h=>(ax x xm).2 h.symm) noDark (mem_erase.mpr ⟨ne,cv⟩))
  intro y ym no c ck
  have yd := (mem_filter.mp (mem_sdiff.mp ym).1).1
  have yv : y∈Vis D := mem_filter.mpr ⟨yd,.inr (by' y ym).1⟩
  have noDark : ∀ z∈Dark D,¬G.Adj y z := fun z zm e=>no ⟨z,ySense y ym z zm e,e⟩
  have ne : c≠y := fun e=>(by' y ym).2 (e ▸ (common c ck).1)
  have cv : c∈Vis D := mem_filter.mpr ⟨(mem_filter.mp (mem_inter.mp ck).1).1,.inl (common c ck).1⟩
  exact (mem_neighborFinset _ _ _).mp (all_vis_of_inactive yd yv (t:=b) (u:=a) (.inr ⟨rfl,rfl⟩)
    (fun h=>(by' y ym).2 h.symm) noDark (mem_erase.mpr ⟨ne,cv⟩))

#print axioms isolate_zero_balance_geometry
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
