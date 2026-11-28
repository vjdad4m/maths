import SixSingletonFourCoreOre189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.Singleton16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d2 from CrossSaturation189
open private two_local_counts three_local_counts from SixCutFar189
open private cannot_miss_two_on_seven from SixSingletonThreeCore189
open private erase_internal_deg from SixSingletonDarkOre189
open private d7 k4 p6 finish_standard finish_standard_swap finish_balance_end finish_isolated_dark from SixSingletonSplice189
open FiveAdjacent (terminal_route_on_of_local_ore)
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

structure Frame3 (G : SimpleGraph V) [DecidableRel G.Adj] (L R : Finset V) : Prop where
  left_sub : L⊆D
  right_sub : R⊆D
  lr_dis : Disjoint L R
  l2 : 2≤L.card
  r2 : 2≤R.card
  strict4 : (L∪R).card=4
  sa : G.Adj s a
  sb : G.Adj s b
  ax : G.Adj a x
  by' : G.Adj b y
  ac : ∀ z∈K,G.Adj a z
  bc : ∀ z∈K,G.Adj b z
  xL : ∀ z∈L,G.Adj x z
  yR : ∀ z∈R,G.Adj y z
  dark5 : ∀ z∈L∪R,5≤(inside G D z).card
  darkHigh : ∀ z∈D,6≤G.degree z
  commonHigh : ∀ z∈K,6≤G.degree z
  commonBounds : ∀ z∈K,∀ w,G.Adj z w → w∈insert a (insert b (P∪(D\(L∪R))))
  darkBounds : ∀ z∈D,∀ w,G.Adj z w → w∈P∪D

private theorem common_min_two_of_three {L R : Finset V} (F : Frame3 G L R)
    (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7) :
    ∀ c∈K,2≤(inside G K c).card := by
  classical
  intro c ck
  by_contra bad
  let S := L∪R
  let W := D\S
  let O := insert x (insert y W)
  let E := O.filter (G.Adj c)
  have Ssub : S⊆D := union_subset F.left_sub F.right_sub
  have S4 : S.card=4 := F.strict4
  have wcount : W.card=7-S.card := by
    change (D\S).card=_
    rw [card_sdiff Ssub,d7]
  have w3 : W.card=3 := by omega
  have os : O.card≤W.card+2 := by
    have o1 := card_insert_le x (insert y W)
    have o2 := card_insert_le y W
    change O.card≤(insert y W).card+1 at o1
    omega
  have eO : E⊆O := filter_subset _ _
  have Ocover {z : V} (h : z∈P∪W) : z∈K ∨ z∈O := by
    rcases mem_union.mp h with p|w
    · rcases mem_insert.mp p with p|p
      · exact .inr (mem_insert.mpr (.inl p))
      rcases mem_insert.mp p with p|p
      · exact .inr (mem_insert_of_mem (mem_insert.mpr (.inl p)))
      exact .inl p
    exact .inr (mem_insert_of_mem (mem_insert_of_mem w))
  have neigh (v : V) (vk : v∈K) (z : V) (vz : G.Adj v z) :
      z=a ∨ z=b ∨ z∈K ∨ z∈O := by
    rcases mem_insert.mp (F.commonBounds v vk z vz) with e|e
    · exact .inl e
    rcases mem_insert.mp e with e|e
    · exact .inr (.inl e)
    exact .inr (.inr (Ocover e))
  have cSub : G.neighborFinset c⊆insert a (insert b ((inside G K c)∪E)) := by
    intro z zm
    have cz := (mem_neighborFinset _ _ _).mp zm
    rcases neigh c ck z cz with h|h|h|h
    · exact mem_insert.mpr (.inl h)
    · exact mem_insert_of_mem (mem_insert.mpr (.inl h))
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨h,cz⟩)))
    exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ (mem_filter.mpr ⟨h,cz⟩)))
  have e3 : 3≤E.card := by
    have n := card_le_card cSub
    rw [card_neighborFinset_eq_degree] at n
    have p := card_insert_le a (insert b ((inside G K c)∪E))
    have q := card_insert_le b ((inside G K c)∪E)
    have r := card_union_le (inside G K c) E
    have k := F.commonHigh c ck
    omega
  have pair : (G.Adj c x ∧ G.Adj c y) ∨ (∃ u∈W,∃ v∈W,u≠v ∧ G.Adj c u ∧ G.Adj c v) := by
    by_cases h : G.Adj c x ∧ G.Adj c y
    · exact .inl h
    apply Or.inr
    push_neg at h
    let T := W.filter (G.Adj c)
    have ins : ∃ u : V,E⊆insert u T := by
      by_cases hx : G.Adj c x
      · refine ⟨x,?_⟩
        intro z zm
        have em : z∈O.filter (G.Adj c) := zm
        obtain ⟨p,cz⟩ := mem_filter.mp em
        rcases mem_insert.mp p with p|p
        · exact mem_insert.mpr (.inl p)
        rcases mem_insert.mp p with p|p
        · exact (h hx (p ▸ cz)).elim
        exact mem_insert_of_mem (mem_filter.mpr ⟨p,cz⟩)
      refine ⟨y,?_⟩
      intro z zm
      have em : z∈O.filter (G.Adj c) := zm
      obtain ⟨p,cz⟩ := mem_filter.mp em
      rcases mem_insert.mp p with p|p
      · exact (hx (p ▸ cz)).elim
      rcases mem_insert.mp p with p|p
      · exact mem_insert.mpr (.inl p)
      exact mem_insert_of_mem (mem_filter.mpr ⟨p,cz⟩)
    obtain ⟨u,uu⟩ := ins
    have q := card_le_card uu
    have w := card_insert_le u T
    have m : 1<T.card := by omega
    obtain ⟨u,um,v,vm,uv⟩ := one_lt_card.mp m
    exact ⟨u,(mem_filter.mp um).1,v,(mem_filter.mp vm).1,uv,(mem_filter.mp um).2,(mem_filter.mp vm).2⟩
  have noStrict {z : V} (zs : z∈S) : ¬G.Adj c z := by
    intro cz
    have zd := Ssub zs
    have zW : z∉W := fun m=>(mem_sdiff.mp m).2 zs
    have h := neigh c ck z cz
    rcases h with e|e|e|e
    · exact (by decide : a∉D) (e ▸ zd)
    · exact (by decide : b∉D) (e ▸ zd)
    · exact disjoint_left.mp (by decide : Disjoint K D) e zd
    rcases mem_insert.mp e with f|f
    · exact (by decide : x∉D) (f ▸ zd)
    rcases mem_insert.mp f with g|g
    · exact (by decide : y∉D) (g ▸ zd)
    exact zW g
  have sTwo : s∈DistanceTwo G c := by
    have cs : c≠s := fun e=>(by decide : s∉K) (e ▸ ck)
    have no : ¬G.Adj c s := by
      intro v
      rcases neigh c ck s v with e|e|e|e
      · exact (by decide : s≠a) e
      · exact (by decide : s≠b) e
      · exact (by decide : s∉K) e
      rcases mem_insert.mp e with q|q
      · exact (by decide : s≠x) q
      rcases mem_insert.mp q with q|q
      · exact (by decide : s≠y) q
      exact (by decide : s∉D) (mem_sdiff.mp q).1
    exact d2 hc cs no (F.ac c ck).symm F.sa.symm
  have strictTwo : S⊆DistanceTwo G c := by
    intro z zs
    have cd : c≠z := fun e=>disjoint_left.mp (by decide : Disjoint K D) ck (e.symm ▸ Ssub zs)
    rcases pair with ⟨cx,cy⟩|⟨u,uw,v,vw,uv,cu,cv⟩
    · rcases mem_union.mp zs with l|r
      · exact d2 hc cd (noStrict zs) cx (F.xL z l)
      exact d2 hc cd (noStrict zs) cy (F.yR z r)
    have zu : z≠u := fun e=>(mem_sdiff.mp uw).2 (e ▸ zs)
    have zv : z≠v := fun e=>(mem_sdiff.mp vw).2 (e ▸ zs)
    rcases cannot_miss_two_on_seven D d7 (Ssub zs) (mem_sdiff.mp uw).1 (mem_sdiff.mp vw).1
      zu zv uv (F.dark5 z zs) with h|h
    · exact d2 hc cd (noStrict zs) cu h.symm
    exact d2 hc cd (noStrict zs) cv h.symm
  have sS : s∉S := fun p=>(by decide : s∉D) (Ssub p)
  have upper := distanceTwo_le_of_even 6 c (even c)
  let Q := (K.erase c)\inside G K c
  have q2 : 2≤Q.card := by
    have sub : inside G K c⊆K.erase c := fun z h=>
      mem_erase.mpr ⟨(mem_filter.mp h).2.ne.symm,(mem_filter.mp h).1⟩
    change 2≤((K.erase c)\inside G K c).card
    rw [card_sdiff sub,card_erase_of_mem ck,k4]
    omega
  have choice : ∃ z∈Q,z∉DistanceTwo G c := by
    by_cases poss : ∃ z∈Q,z∉DistanceTwo G c
    · exact poss
    exfalso
    have qsub : Q⊆DistanceTwo G c := fun z zm=>Classical.byContradiction (fun h=>poss ⟨z,zm,h⟩)
    have qs : Disjoint Q (insert s S) := by
      apply disjoint_left.mpr
      intro z zq zz
      have zk := (mem_erase.mp (mem_sdiff.mp zq).1).2
      rcases mem_insert.mp zz with h|h
      · exact (by decide : s∉K) (h ▸ zk)
      exact disjoint_left.mp (by decide : Disjoint K D) zk (Ssub h)
    have v := two_local_counts Q (insert s S) qs _ qsub (insert_subset sTwo strictTwo)
    rw [card_insert_of_not_mem sS,S4] at v
    omega
  obtain ⟨t,tq,tn⟩ := choice
  have ⟨tc,tk⟩ := mem_erase.mp (mem_sdiff.mp tq).1
  have no : ¬G.Adj c t := fun h=>(mem_sdiff.mp tq).2 (mem_filter.mpr ⟨tk,h⟩)
  have notShared {z : V} (cz : G.Adj c z) (tz : G.Adj t z) : False :=
    tn (d2 hc tc.symm no cz tz.symm)
  let E' := O.filter (G.Adj t)
  have outside : E.card+E'.card≤O.card :=
    two_local_counts E E' (disjoint_left.mpr (fun _ m n=>notShared (mem_filter.mp m).2 (mem_filter.mp n).2))
      O (filter_subset _ _) (filter_subset _ _)
  have ksubC : inside G K c⊆(K.erase c).erase t :=
    fun _ h=>mem_erase.mpr ⟨fun e=>no (e ▸ (mem_filter.mp h).2),
      mem_erase.mpr ⟨(mem_filter.mp h).2.ne.symm,(mem_filter.mp h).1⟩⟩
  have ksubT : inside G K t⊆(K.erase c).erase t :=
    fun _ h=>mem_erase.mpr ⟨(mem_filter.mp h).2.ne.symm,
      mem_erase.mpr ⟨fun e=>no (e ▸ (mem_filter.mp h).2).symm,(mem_filter.mp h).1⟩⟩
  have localCount := two_local_counts _ _
    (disjoint_left.mpr (fun _ m n=>notShared (mem_filter.mp m).2 (mem_filter.mp n).2))
    _ ksubC ksubT
  rw [card_erase_of_mem (mem_erase.mpr ⟨tc,tk⟩),card_erase_of_mem ck,k4] at localCount
  change (inside G K c).card+(inside G K t).card≤2 at localCount
  have tSub : G.neighborFinset t⊆insert a (insert b ((inside G K t)∪E')) := by
    intro z zm
    have tz := (mem_neighborFinset _ _ _).mp zm
    rcases neigh t tk z tz with h|h|h|h
    · exact mem_insert.mpr (.inl h)
    · exact mem_insert_of_mem (mem_insert.mpr (.inl h))
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨h,tz⟩)))
    exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ (mem_filter.mpr ⟨h,tz⟩)))
  have bound (v : V) (X : Finset V) (s' : G.neighborFinset v⊆insert a (insert b ((inside G K v)∪X))) :
      G.degree v≤(inside G K v).card+X.card+2 := by
    have m := card_le_card s'
    rw [card_neighborFinset_eq_degree] at m
    have j := card_insert_le a (insert b ((inside G K v)∪X))
    have k := card_insert_le b ((inside G K v)∪X)
    have g := card_union_le (inside G K v) X
    omega
  have cc := bound c E cSub
  have tt := bound t E' tSub
  have ch := F.commonHigh c ck
  have th := F.commonHigh t tk
  omega

private theorem balance_common_if_low {L R : Finset V} (F : Frame3 G L R)
    {w : V} (wd : w∈D) (low : (inside G D w).card≤2) :
    ∃ c∈K,G.Adj w c := by
  classical
  by_contra no
  have h : G.neighborFinset w⊆insert x (insert y (inside G D w)) := by
    intro z zm
    have wz := (mem_neighborFinset _ _ _).mp zm
    rcases mem_union.mp (F.darkBounds w wd z wz) with zp|zd
    · rcases mem_insert.mp zp with e|e
      · exact mem_insert.mpr (.inl e)
      rcases mem_insert.mp e with e|e
      · exact mem_insert_of_mem (mem_insert.mpr (.inl e))
      exact (no ⟨z,e,wz⟩).elim
    exact mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨zd,wz⟩))
  have q := card_le_card h
  rw [card_neighborFinset_eq_degree] at q
  have i := card_insert_le x (insert y (inside G D w))
  have j := card_insert_le y (inside G D w)
  have high := F.darkHigh _ wd
  omega

private theorem every_port_of_isolated_dark {L R : Finset V} (F : Frame3 G L R)
    {w : V} (wd : w∈D) (no : ∀ z∈D,¬G.Adj w z) :
    P⊆G.neighborFinset w := by
  have h : G.neighborFinset w⊆P := by
    intro z zm
    have wz := (mem_neighborFinset _ _ _).mp zm
    exact (mem_union.mp (F.darkBounds w wd z wz)).resolve_right (fun zd=>no z zd wz)
  exact (eq_of_subset_of_card_le h (by rw [p6,card_neighborFinset_eq_degree]; exact F.darkHigh w wd)).ge

private theorem common_needs_balance_if_no_exclusive {L R : Finset V} (F : Frame3 G L R)
    (noX : ¬∃ c∈K,G.Adj x c) (noY : ¬∃ c∈K,G.Adj y c) :
    ∃ w∈D\(L∪R),∃ c∈K,G.Adj w c := by
  classical
  have cK : (5:V)∈K := by decide
  by_contra no
  have h : G.neighborFinset 5⊆insert a (insert b (K.erase 5)) := by
    intro z zm
    have e := (mem_neighborFinset _ _ _).mp zm
    rcases mem_insert.mp (F.commonBounds 5 cK z e) with p|p
    · exact mem_insert.mpr (.inl p)
    rcases mem_insert.mp p with p|p
    · exact mem_insert_of_mem (mem_insert.mpr (.inl p))
    rcases mem_union.mp p with p|p
    · rcases mem_insert.mp p with p|p
      · exact (noX ⟨5,cK,p ▸ e.symm⟩).elim
      rcases mem_insert.mp p with p|p
      · exact (noY ⟨5,cK,p ▸ e.symm⟩).elim
      exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨e.ne.symm,p⟩))
    exact (no ⟨z,p,5,cK,e.symm⟩).elim
  have k := card_le_card h
  rw [card_neighborFinset_eq_degree] at k
  have high := F.commonHigh 5 cK
  have q : (insert a (insert b (K.erase 5))).card=5 := by decide
  omega

/-- The three-balanced normalized board with one exclusive port per color
does not depend on whether the cut terminals are adjacent. -/
theorem traceable_of_unique_board_three_balanced {L R : Finset V} (F : Frame3 G L R)
    (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  let S := L∪R
  let W := D\S
  have sub : S⊆D := union_subset F.left_sub F.right_sub
  have S4 : S.card=4 := F.strict4
  have lpos : L.Nonempty := card_pos.mp (by have h:=F.l2; omega)
  have rpos : R.Nonempty := card_pos.mp (by have h:=F.r2; omega)
  obtain ⟨l,ll⟩ := lpos
  obtain ⟨r,rr⟩ := rpos
  have lr : l≠r := fun e=>disjoint_left.mp F.lr_dis ll (e.symm ▸ rr)
  have comm := common_min_two_of_three F hc even
  have rootedK (z : V) (zk : z∈K) : ∃ t∈K,RouteOn G K z t :=
    rooted_high_residual_Ore_at_d 2 K (by decide) comm zk
  by_cases all : ∀ w∈D,w∉S → 3≤(inside G D w).card
  · have route {u v : V} (ud : u∈D) (vd : v∈D) (uv : u≠v) :=
      small_dark_core_terminal_ore D S sub (by rw [d7]; decide) d7.le S4.symm.le
        (fun z mz=>by rw [d7]; exact F.dark5 z mz) all ud vd uv
    have p := route (F.left_sub ll) (F.right_sub rr) lr
    by_cases Y : ∃ c∈K,G.Adj y c
    · obtain ⟨c,ck,yc⟩ := Y
      obtain ⟨t,tk,Q⟩ := rootedK c ck
      exact finish_standard p Q F.sa F.ax (F.xL l ll) (F.yR r rr).symm yc (F.bc t tk).symm
    by_cases X : ∃ c∈K,G.Adj x c
    · obtain ⟨c,ck,xc⟩ := X
      obtain ⟨t,tk,Q⟩ := rootedK c ck
      exact finish_standard_swap p Q F.sb F.by' (F.yR r rr) (F.xL l ll).symm xc (F.ac t tk).symm
    obtain ⟨w,ww,c,ck,wc⟩ := common_needs_balance_if_no_exclusive F X Y
    have wp := mem_sdiff.mp ww
    have nw : l≠w := fun e=>wp.2 (mem_union_left _ (e ▸ ll))
    obtain ⟨t,tk,Q⟩ := rootedK c ck
    exact finish_balance_end (route (F.left_sub ll) wp.1 nw) Q F.sa F.ax (F.xL l ll) wc (F.bc t tk).symm F.by'
  push_neg at all
  obtain ⟨w,wd,ws,lo⟩ := all
  obtain ⟨c,ck,wc⟩ := balance_common_if_low F wd (by omega)
  obtain ⟨t,tk,Q⟩ := rootedK c ck
  by_cases e : ∃ z∈D,G.Adj w z
  · obtain ⟨z,zl,R⟩ := dark_three_low_balance_end D S L sub subset_union_left F.l2 d7 S4 F.dark5
      wd ws (by omega) e
    exact finish_balance_end R Q F.sa F.ax (F.xL z zl) wc (F.bc t tk).symm F.by'
  push_neg at e
  have Z6 : (D.erase w).card=6 := by rw [card_erase_of_mem wd,d7]
  have deg4 (v : V) (vm : v∈D.erase w) : 4≤(inside G (D.erase w) v).card := by
    by_cases vs : v∈S
    · have low := erase_internal_deg (G:=G) D w v
      have hi := F.dark5 v vs
      omega
    have vv := (mem_erase.mp vm).1
    have vD := (mem_erase.mp vm).2
    have subS : S⊆inside G (D.erase w) v := by
      intro z zs
      have zw : z≠w := fun f=>ws (f ▸ zs)
      have zv : z≠v := fun f=>vs (f ▸ zs)
      have hit := cannot_miss_two_on_seven D d7 (sub zs) wd vD zw zv vv.symm (F.dark5 z zs)
      exact mem_filter.mpr ⟨mem_erase.mpr ⟨zw,sub zs⟩,
        (hit.resolve_left (fun h=>e z (sub zs) h.symm)).symm⟩
    have h := card_le_card subS
    omega
  have lW : l∈D.erase w :=
    mem_erase.mpr ⟨fun h=>ws (mem_union_left _ (h ▸ ll)),F.left_sub ll⟩
  have rW : r∈D.erase w :=
    mem_erase.mpr ⟨fun h=>ws (mem_union_right _ (h ▸ rr)),F.right_sub rr⟩
  have dark := terminal_route_on_of_local_ore (G:=G) _ lW rW lr (by
    intro p pm q qm _ _
    have p4 := deg4 p pm
    have q4 := deg4 q qm
    omega)
  have wy := (mem_neighborFinset _ _ _).mp (every_port_of_isolated_dark F wd e (by decide : y∈P))
  exact finish_isolated_dark wd dark Q F.sa F.ax (F.xL l ll) (F.yR r rr).symm wy.symm wc (F.bc t tk).symm

#print axioms common_min_two_of_three
#print axioms traceable_of_unique_board_three_balanced
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.Singleton16
