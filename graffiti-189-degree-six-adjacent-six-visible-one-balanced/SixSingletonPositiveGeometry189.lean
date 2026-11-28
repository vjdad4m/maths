import SixSingletonPositiveProfiles189
import SixSingletonMultiZeroGeom189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_off shore_closed shore_disjoint shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private Cmp DeletionConnected aPorts bPorts from SixCutFar189
open private Vis vis_sub from AdjacentCutFiveComponents189
open private Dark Common strictA strictB bal singleton_neighborhood_exact port_union_vis from SixSingletonGeometry189
open private step_at_depth_two class_partition from SixSingletonShape189
open private nearLeft nearRight nearBal from SixSingletonFiveGeometry189
open private predecessor_of_positive_dist from AdjacentCutFiveSixteenSingletonDepth189
open private EA EB from SixSingletonMultiZeroGeom189
open FiveAdjacent (depth)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

structure SixVisibleData (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {a b : V} (D : Cmp G a b) (s : V) : Prop where
  sa : G.Adj s a
  sb : G.Adj s b
  sOff : s∉Shore D
  dark7 : (Dark D).card=7
  darkPart : strictA D∪strictB D∪nearBal D=Dark D
  nearA : nearLeft D = strictA D
  nearB : nearRight D = strictB D
  visiblePart : EA D∪EB D∪Common D=Vis D
  cover : ∀ z : V,z=a ∨ z=b ∨ z=s ∨ z∈Vis D ∨ z∈Dark D
  eA : ∀ x∈EA D,G.Adj a x ∧ ¬G.Adj b x
  eB : ∀ x∈EB D,G.Adj b x ∧ ¬G.Adj a x
  common : ∀ c∈Common D,G.Adj a c ∧ G.Adj b c
  rootsA : ∀ z∈strictA D,∃ x∈EA D,G.Adj x z
  rootsB : ∀ z∈strictB D,∃ x∈EB D,G.Adj x z
  strictA_local : ∀ z∈strictA D,6-(EA D).card≤(inside G (Dark D) z).card
  strictB_local : ∀ z∈strictB D,6-(EB D).card≤(inside G (Dark D) z).card
  highDark : ∀ z∈Dark D,6≤G.degree z
  darkBound : ∀ z∈Dark D,G.neighborFinset z⊆inside G (Dark D) z∪inside G (Vis D) z
  commonBound : ∀ c∈Common D,G.neighborFinset c⊆insert a (insert b (inside G (Vis D) c∪inside G (nearBal D) c))
  aBound : ∀ x∈EA D,G.neighborFinset x⊆insert a (inside G (Vis D) x∪inside G (strictA D) x∪inside G (nearBal D) x)
  bBound : ∀ y∈EB D,G.neighborFinset y⊆insert b (inside G (Vis D) y∪inside G (strictB D) y∪inside G (nearBal D) y)
  highCommon : ∀ c∈Common D,6≤G.degree c
  highEA : ∀ x∈EA D,6≤G.degree x
  highEB : ∀ y∈EB D,6≤G.degree y

theorem isolate_six_visible_geometry
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S D : Cmp G a b} (sd : S≠D)
    (cov : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13) (v6 : (Vis D).card=6) :
    ∃ s,SixVisibleData G D s := by
  classical
  obtain ⟨s,sS⟩ := card_eq_one.mp one
  have ss : s∈Shore S := by simp [sS]
  obtain ⟨u,us,au⟩ := shore_hit_a ab.ne conn S
  obtain ⟨v,vs,bv⟩ := shore_hit_b ab.ne conn S
  have as' : G.Adj a s := (show u=s by simpa only [sS,mem_singleton] using us) ▸ au
  have bs' : G.Adj b s := (show v=s by simpa only [sS,mem_singleton] using vs) ▸ bv
  have s2 : G.degree s=2 := by
    rw [←card_neighborFinset_eq_degree,singleton_neighborhood_exact sS as' bs',
      card_insert_of_not_mem (by simpa using ab.ne),card_singleton]
  have high (z : V) (zd : z∈Shore D) : 6≤G.degree z := by
    have ne : z≠s := fun e=>disjoint_left.mp (shore_disjoint sd) ss (e ▸ zd)
    exact (degree z s ne).resolve_right (by omega)
  have near : ∀ z∈Dark D,depth G a b z=2 := by
    rcases adjacent_singleton_thirteen_visible_profile hc ab even conn degree sd cov one d13 with
      ⟨n,_,_,_⟩|⟨_,_,_,_,_,h⟩
    · omega
    exact h
  have eq : bal D=nearBal D := by
    apply Subset.antisymm _ (filter_subset _ _)
    intro z zm
    exact mem_filter.mpr ⟨zm,near z (mem_filter.mp zm).1⟩
  have dp : strictA D∪strictB D∪nearBal D=Dark D := by rw [←eq,class_partition]
  have nearA : nearLeft D=strictA D := by
    apply Subset.antisymm (filter_subset _ _) _
    intro z h
    exact mem_filter.mpr ⟨h,near z (mem_filter.mp h).1⟩
  have nearB : nearRight D=strictB D := by
    apply Subset.antisymm (filter_subset _ _) _
    intro z h
    exact mem_filter.mpr ⟨h,near z (mem_filter.mp h).1⟩
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
  have noAB {x z : V} (xA : x∈EA D) (zB : z∈strictB D) : ¬G.Adj x z := by
    intro xz
    have p := G.dist_le (Walk.cons (ax x xA).1 (Walk.cons xz .nil))
    simp at p
    have h := (jB zB).2
    omega
  have noBA {x z : V} (xB : x∈EB D) (zA : z∈strictA D) : ¬G.Adj x z := by
    intro xz
    have p := G.dist_le (Walk.cons (by' x xB).1 (Walk.cons xz .nil))
    simp at p
    have h := (jA zA).2
    omega
  have common (c : V) (ck : c∈Common D) : G.Adj a c ∧ G.Adj b c :=
    ⟨(mem_filter.mp (mem_inter.mp ck).1).2,(mem_filter.mp (mem_inter.mp ck).2).2⟩
  have cNo {c z : V} (ck : c∈Common D) (zr : z∈strictA D∪strictB D) : ¬G.Adj c z := by
    intro cz
    have ca := G.dist_le (Walk.cons (common c ck).1 (Walk.cons cz .nil))
    have cb := G.dist_le (Walk.cons (common c ck).2 (Walk.cons cz .nil))
    simp at ca cb
    rcases mem_union.mp zr with l|r
    · have h := (jA l).2
      omega
    have h := (jB r).2
    omega
  have locality {z : V} (zd : z∈Dark D) {w : V} (zw : G.Adj z w) : w∈Shore D := by
    have ⟨r,n⟩ := mem_sdiff.mp zd
    rcases shore_closed D z r w zw with e|e|e
    · exact (n (mem_filter.mpr ⟨r,.inl (e ▸ zw.symm)⟩)).elim
    · exact (n (mem_filter.mpr ⟨r,.inr (e ▸ zw.symm)⟩)).elim
    exact e
  have darkBound (z : V) (zd : z∈Dark D) : G.neighborFinset z⊆inside G (Dark D) z∪inside G (Vis D) z := by
    intro w wm
    have zw := (mem_neighborFinset _ _ _).mp wm
    by_cases wv : w∈Vis D
    · exact mem_union_right _ (mem_filter.mpr ⟨wv,zw⟩)
    exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨locality zd zw,wv⟩,zw⟩)
  have localBound (z : V) (zd : z∈Dark D) (P : Finset V)
      (h : inside G (Vis D) z⊆P) : 6-P.card≤(inside G (Dark D) z).card := by
    have sub := (darkBound z zd).trans (union_subset_union (Subset.refl _) h)
    have a := card_le_card sub
    rw [card_neighborFinset_eq_degree] at a
    have b := card_union_le (inside G (Dark D) z) P
    have c := high z (mem_sdiff.mp zd).1
    omega
  have localA (z : V) (za : z∈strictA D) : 6-(EA D).card≤(inside G (Dark D) z).card := by
    apply localBound z (mem_filter.mp za).1 (EA D)
    intro w wm
    obtain ⟨wv,zw⟩ := mem_filter.mp wm
    rw [←vp] at wv
    rcases mem_union.mp wv with w|w
    · exact (mem_union.mp w).resolve_right (fun wb=>noBA wb za zw.symm)
    exact (cNo w (mem_union_left _ za) zw.symm).elim
  have localB (z : V) (zb : z∈strictB D) : 6-(EB D).card≤(inside G (Dark D) z).card := by
    apply localBound z (mem_filter.mp zb).1 (EB D)
    intro w wm
    obtain ⟨wv,zw⟩ := mem_filter.mp wm
    rw [←vp] at wv
    rcases mem_union.mp wv with w|w
    · exact (mem_union.mp w).resolve_left (fun wa=>noAB wa zb zw.symm)
    exact (cNo w (mem_union_right _ zb) zw.symm).elim
  have cb (c : V) (ck : c∈Common D) :
      G.neighborFinset c⊆insert a (insert b (inside G (Vis D) c∪inside G (nearBal D) c)) := by
    have cd := (mem_filter.mp (mem_inter.mp ck).1).1
    intro z zm
    have cz := (mem_neighborFinset _ _ _).mp zm
    rcases shore_closed D c cd z cz with e|e|zz
    · exact mem_insert.mpr (.inl e)
    · exact mem_insert_of_mem (mem_insert.mpr (.inl e))
    apply mem_insert_of_mem
    apply mem_insert_of_mem
    by_cases zv : z∈Vis D
    · exact mem_union_left _ (mem_filter.mpr ⟨zv,cz⟩)
    have d : z∈Dark D := mem_sdiff.mpr ⟨zz,zv⟩
    have zb := (mem_union.mp (dp.symm ▸ d)).resolve_left (fun q=>cNo ck q cz)
    exact mem_union_right _ (mem_filter.mpr ⟨zb,cz⟩)
  have boundsA (x : V) (xm : x∈EA D) :
      G.neighborFinset x⊆insert a (inside G (Vis D) x∪inside G (strictA D) x∪inside G (nearBal D) x) := by
    intro z zm
    have xz := (mem_neighborFinset _ _ _).mp zm
    have xd := (mem_filter.mp (mem_sdiff.mp xm).1).1
    rcases shore_closed D x xd z xz with e|e|zd
    · exact mem_insert.mpr (.inl e)
    · exact ((ax x xm).2 (e ▸ xz.symm)).elim
    apply mem_insert_of_mem
    by_cases zv : z∈Vis D
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨zv,xz⟩))
    have d : z∈Dark D := mem_sdiff.mpr ⟨zd,zv⟩
    rcases mem_union.mp (dp.symm ▸ d) with q|q
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr
        ⟨(mem_union.mp q).resolve_right (fun h=>noAB xm h xz),xz⟩))
    exact mem_union_right _ (mem_filter.mpr ⟨q,xz⟩)
  have boundsB (x : V) (xm : x∈EB D) :
      G.neighborFinset x⊆insert b (inside G (Vis D) x∪inside G (strictB D) x∪inside G (nearBal D) x) := by
    intro z zm
    have xz := (mem_neighborFinset _ _ _).mp zm
    have xd := (mem_filter.mp (mem_sdiff.mp xm).1).1
    rcases shore_closed D x xd z xz with e|e|zd
    · exact ((by' x xm).2 (e ▸ xz.symm)).elim
    · exact mem_insert.mpr (.inl e)
    apply mem_insert_of_mem
    by_cases zv : z∈Vis D
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨zv,xz⟩))
    have d : z∈Dark D := mem_sdiff.mpr ⟨zd,zv⟩
    rcases mem_union.mp (dp.symm ▸ d) with q|q
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr
        ⟨(mem_union.mp q).resolve_left (fun h=>noBA xm h xz),xz⟩))
    exact mem_union_right _ (mem_filter.mpr ⟨q,xz⟩)
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
  exact ⟨s,as'.symm,bs'.symm,fun m=>disjoint_left.mp (shore_disjoint sd) ss m,
    d7,dp,nearA,nearB,vp,cover,ax,by',common,rootA,rootB,localA,localB,
    (fun u ud=>high u (mem_sdiff.mp ud).1),darkBound,cb,boundsA,boundsB,
    (fun c cm=>high c (mem_filter.mp (mem_inter.mp cm).1).1),
    (fun x xm=>high x (mem_filter.mp (mem_sdiff.mp xm).1).1),
    (fun y ym=>high y (mem_filter.mp (mem_sdiff.mp ym).1).1)⟩

#print axioms isolate_six_visible_geometry
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
