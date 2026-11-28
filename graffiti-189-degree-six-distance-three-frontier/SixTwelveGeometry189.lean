import SixElevenPartition189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_disjoint shore_off shore_closed shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private no_common_far shore_inside_five from SixDistanceThreeShort189
open private d2 from CrossSaturation189
open private each_foreign_port_is_distance_two from SixCutHighShore189
open private in_positive_even_of_dist_two from TwoCutDistanceCaps189
open private neighbor_subset_of_dark from SixTenRegular189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (cross_metric shore_swapCut)
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}

theorem dark_inside_six {D : Cmp G a b} {x : V} (xd : x∈Shore D)
    (na : ¬G.Adj a x) (nb : ¬G.Adj b x) (high : 6≤G.degree x) :
    6≤(inside G (Shore D) x).card := by
  have u := card_le_card (neighbor_subset_of_dark D xd na nb)
  rw [G.card_neighborFinset_eq_degree] at u
  exact high.trans u

theorem nonedge_charge_with_exclusions (hc : G.Connected)
    (D : Finset V) {x y : V} (xd : x∈D) (yd : y∈D) (xy : x≠y) (no : ¬G.Adj x y)
    (E : Finset V) (eb : ∀ e∈E,e∈D ∧ e≠x ∧ e≠y ∧ ¬G.Adj x e ∧ ¬G.Adj y e)
    (lower : D.card < (inside G D x).card+(inside G D y).card+E.card+2) :
    y∈DistanceTwo G x := by
  classical
  let X := inside G D x
  let Y := inside G D y
  obtain ⟨z,zx,zy⟩ : ∃ z∈X,z∈Y := by
    by_contra h
    have dis : Disjoint X Y := disjoint_left.mpr (fun z zx zy=>h ⟨z,zx,zy⟩)
    have sub : (X∪Y)∪E⊆(D.erase x).erase y := by
      intro z hz
      rcases mem_union.mp hz with hz|hz
      · rcases mem_union.mp hz with a|b
        · obtain ⟨zd,xz⟩ := mem_filter.mp a
          exact mem_erase.mpr ⟨fun e=>no (e ▸ xz),mem_erase.mpr ⟨xz.ne.symm,zd⟩⟩
        · obtain ⟨zd,yz⟩ := mem_filter.mp b
          exact mem_erase.mpr ⟨yz.ne.symm,mem_erase.mpr ⟨fun e=>no ((e ▸ yz).symm),zd⟩⟩
      · obtain ⟨zd,zx,zy,_,_⟩ := eb z hz
        exact mem_erase.mpr ⟨zy,mem_erase.mpr ⟨zx,zd⟩⟩
    have disE : Disjoint (X∪Y) E := disjoint_left.mpr (fun z zU zE=>
      (mem_union.mp zU).elim (fun zx => (eb z zE).2.2.2.1 (mem_filter.mp zx).2)
        (fun zy => (eb z zE).2.2.2.2 (mem_filter.mp zy).2))
    have q := card_le_card sub
    rw [card_union_of_disjoint disE,card_union_of_disjoint dis,
      card_erase_of_mem (mem_erase.mpr ⟨xy.symm,yd⟩),card_erase_of_mem xd] at q
    change D.card < X.card+Y.card+E.card+2 at lower
    have card2 := one_lt_card.mpr ⟨x,xd,y,yd,xy⟩
    omega
  exact d2 hc xy no (mem_filter.mp zx).2 (mem_filter.mp zy).2.symm

theorem twelve_dark_nonedge_charge (hc : G.Connected) (far : 3≤G.dist a b)
    {D : Cmp G a b} (twelve : (Shore D).card=12) {x y : V}
    (xd : x∈Shore D) (yd : y∈Shore D) (xy : x≠y) (no : ¬G.Adj x y)
    (hx : 6≤G.degree x) (hy : 6≤G.degree y)
    (dark : (¬G.Adj a x ∧ ¬G.Adj b x) ∨ (¬G.Adj a y ∧ ¬G.Adj b y)) :
    y∈DistanceTwo G x := by
  apply nonedge_charge_with_exclusions hc (Shore D) xd yd xy no ∅ (by simp)
  have l := shore_inside_five far D xd hx
  have r := shore_inside_five far D yd hy
  rw [card_empty,twelve]
  rcases dark with j|j
  · have p := dark_inside_six xd j.1 j.2 hx
    omega
  · have p := dark_inside_six yd j.1 j.2 hy
    omega

theorem twelve_excluded_nonedge_charge (hc : G.Connected) (far : 3≤G.dist a b)
    {D : Cmp G a b} (twelve : (Shore D).card=12) {x y w : V}
    (xd : x∈Shore D) (yd : y∈Shore D) (wd : w∈Shore D) (xy : x≠y)
    (no : ¬G.Adj x y) (wx : w≠x) (wy : w≠y)
    (xw : ¬G.Adj x w) (yw : ¬G.Adj y w)
    (hx : 6≤G.degree x) (hy : 6≤G.degree y) :
    y∈DistanceTwo G x := by
  apply nonedge_charge_with_exclusions hc (Shore D) xd yd xy no {w}
    (by intro z zm; rcases mem_singleton.mp zm with rfl; exact ⟨wd,wx,wy,xw,yw⟩)
  have l := shore_inside_five far D xd hx
  have r := shore_inside_five far D yd hy
  rw [card_singleton,twelve]
  omega

theorem small_dark_cross_four (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D) (six : (Shore C).card=6)
    {u z : V} (ud : u∈Shore D) (zc : z∈Shore C)
    (ua : G.dist a u=2) (ub : 3≤G.dist b u) (bz : G.Adj b z) : G.dist u z=4 := by
  obtain ⟨r,rc,ar⟩ := shore_hit_a ab conn C
  have az : ¬G.Adj a z := fun h=>no_common_far far ⟨h,bz⟩
  have rz : r≠z := fun eq=>az (eq ▸ ar)
  have za : z≠a := fun eq=>(shore_off C).1 (eq ▸ zc)
  have just : G.dist a z=2 :=
    (mem_cutSeen.mp (visible_of_adj_port (S:=Shore C) hc za zc ar
      (cut_shore_six_clique far C six degree r rc z zc rz) az)).2
  have zb := dist_eq_one_iff_adj.mpr bz
  have out : z∉Shore D := fun zd=>disjoint_left.mp (shore_disjoint cd) zc zd
  have e := cross_metric (Shore D) hc ud out (shore_closed D)
  have ub' : 3≤G.dist u b := by rwa [dist_comm]
  have ua' : G.dist u a=2 := by rwa [dist_comm]
  rw [e,ua',just,zb]
  omega

theorem mem_positive_four {u v : V} (h : G.dist u v=4) : v∈PositiveEven G u := by
  classical
  have ne : v≠u := fun e=>by rw [e,dist_self] at h; omega
  exact mem_erase.mpr ⟨ne,mem_filter.mpr ⟨mem_univ _,by rw [h]; decide⟩⟩

theorem small_port_even_budget (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (even : ∀ x,(EvenFrom G x).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D) (six : (Shore C).card=6)
    (H : Finset V) (hvis : ∀ x∈H,x∈Shore D ∧ G.dist b x=2 ∧ 3≤G.dist a x) :
    (cutPorts G (Shore D) a).card+H.card≤5 := by
  classical
  obtain ⟨x,xc,ax⟩ := shore_hit_a ab conn C
  obtain ⟨z,zc,bz⟩ := shore_hit_b ab conn C
  have zx : x≠z := fun h=>no_common_far far ⟨ax,h.symm ▸ bz⟩
  have xb := d2 hc (show x≠b from fun e=>(shore_off C).2 (e ▸ xc))
    (fun h=>no_common_far far ⟨ax,h.symm⟩) (cut_shore_six_clique far C six degree x xc z zc zx) bz.symm
  have dt (u : V) (hu : u∈H) : u∈PositiveEven G x := by
    obtain ⟨ud,ub,ua⟩ := hvis u hu
    have ud' : u∈Shore (swapCut D) := by rwa [shore_swapCut]
    have xc' : x∈Shore (swapCut C) := by rwa [shore_swapCut]
    have cd' : swapCut C≠swapCut D := fun e=>cd (swapCut.injective e)
    have far' : 3≤G.dist b a := by rwa [dist_comm]
    have h := small_dark_cross_four hc far' ab.symm conn degree cd'
      (by rwa [shore_swapCut]) ud' xc' ub ua ax
    exact mem_positive_four (by rwa [dist_comm])
  have dh : Disjoint (cutPorts G (Shore D) a) H := disjoint_left.mpr (fun u ua uh=>by
    have aa := (mem_filter.mp ua).2
    have aa' := dist_eq_one_iff_adj.mpr aa
    have hu := (hvis u uh).2.2
    omega)
  have dc : Disjoint (cutPorts G (Shore D) a) ({b}:Finset V) :=
    disjoint_left.mpr (fun u up ue=>(shore_off D).2 ((mem_singleton.mp ue) ▸ (mem_filter.mp up).1))
  have dd : Disjoint H ({b}:Finset V) :=
    disjoint_left.mpr (fun u up ue=>(shore_off D).2 ((mem_singleton.mp ue) ▸ (hvis u up).1))
  have q := even_budget_three even x _ H {b} dh dc dd (by
    intro u uu
    have h : u∈DistanceTwo G x := each_foreign_port_is_distance_two hc cd (mem_filter.mpr ⟨xc,ax⟩) uu
    exact in_positive_even_of_dist_two (mem_filter.mp h).2)
    dt (by intro u uu; rw [mem_singleton.mp uu]; exact in_positive_even_of_dist_two (mem_filter.mp xb).2)
  rw [card_singleton] at q
  omega

theorem port_even_from_local_twos (hc : G.Connected)
    (even : ∀ x,(EvenFrom G x).card≤7) {C D : Cmp G a b} (cd : C≠D)
    {u : V} (ud : u∈Shore D) (au : G.Adj a u) (H T : Finset V)
    (hD : H⊆Shore D) (h2 : H⊆DistanceTwo G u)
    (tC : Disjoint T (Shore C)) (tD : Disjoint T (Shore D)) (t2 : T⊆DistanceTwo G u) :
    (cutPorts G (Shore C) a).card+H.card+T.card≤6 := by
  classical
  have psub : cutPorts G (Shore C) a⊆Shore C := filter_subset _ _
  apply even_budget_three even u _ H T
    ((shore_disjoint cd).mono psub hD) (tC.symm.mono_left psub) (tD.symm.mono_left hD)
  · intro x xx
    have h : x∈DistanceTwo G u :=
      each_foreign_port_is_distance_two hc cd.symm (mem_filter.mpr ⟨ud,au⟩) xx
    exact in_positive_even_of_dist_two (mem_filter.mp h).2
  · exact fun x hx=>in_positive_even_of_dist_two (mem_filter.mp (h2 hx)).2
  · exact fun x hx=>in_positive_even_of_dist_two (mem_filter.mp (t2 hx)).2

theorem dark_one_even_twelve (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (even : ∀ x,(EvenFrom G x).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D) (six : (Shore C).card=6)
    (twelve : (Shore D).card=12) {u : V} (ud : u∈Shore D) (uh : 6≤G.degree u)
    (ua : G.dist a u=2) (ub : 3≤G.dist b u)
    (H : Finset V) (loc : ∀ x∈H,x∈Shore D ∧ 6≤G.degree x ∧ G.Adj b x) :
    (cutPorts G (Shore C) b).card+H.card+1≤6 := by
  classical
  have hsub : H⊆Shore D := fun x hx=>(loc x hx).1
  have psub : cutPorts G (Shore C) b⊆Shore C := filter_subset _ _
  have aoffC : Disjoint (cutPorts G (Shore C) b) ({a}:Finset V) :=
    disjoint_left.mpr (fun x xp xe=>(shore_off C).1 ((mem_singleton.mp xe) ▸ psub xp))
  have aoffD : Disjoint H ({a}:Finset V) :=
    disjoint_left.mpr (fun x xp xe=>(shore_off D).1 ((mem_singleton.mp xe) ▸ hsub xp))
  have q := even_budget_three even u _ H {a}
    ((shore_disjoint cd).mono psub hsub) aoffC aoffD ?_ ?_ ?_
  · rwa [card_singleton] at q
  · intro z zp
    obtain ⟨zc,bz⟩ := mem_filter.mp zp
    exact mem_positive_four (small_dark_cross_four hc far ab conn degree cd six ud zc ua ub bz)
  · intro z zh
    obtain ⟨zd,hd,bz⟩ := loc z zh
    have pos : u≠z := fun e=>by rw [e,dist_eq_one_iff_adj.mpr bz] at ub; omega
    have no : ¬G.Adj u z := by
      intro yes
      have du := G.dist_le (Walk.cons bz (Walk.cons yes.symm .nil))
      simp at du
      omega
    have na : ¬G.Adj a u := fun e=>by have x := dist_eq_one_iff_adj.mpr e; omega
    have nb : ¬G.Adj b u := fun e=>by have x := dist_eq_one_iff_adj.mpr e; omega
    exact in_positive_even_of_dist_two ((mem_filter.mp
      (twelve_dark_nonedge_charge hc far twelve ud zd pos no uh hd (.inl ⟨na,nb⟩))).2)
  · intro z zz
    rw [mem_singleton.mp zz]
    apply in_positive_even_of_dist_two
    rwa [dist_comm]

#print axioms twelve_dark_nonedge_charge
#print axioms twelve_excluded_nonedge_charge
#print axioms small_port_even_budget
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
