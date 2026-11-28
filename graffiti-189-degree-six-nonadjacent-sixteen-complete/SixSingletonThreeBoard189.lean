import SixSingletonThreeCore189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.Singleton16
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private d2 from CrossSaturation189
open private two_local_counts from SixCutFar189
open private cannot_miss_two_on_seven from SixSingletonThreeCore189
open private finish_balance_end finish_isolated_dark d7 k4 from SixSingletonSplice189
open FiveAdjacent (terminal_route_on_of_local_ore)
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Three-balanced normalized geometry: every pairwise support fact is
literal Fin 16 data, while the geometric fields are exact graph statements. -/
structure ThreeBoard (G : SimpleGraph V) [DecidableRel G.Adj] (L R : Finset V) : Prop where
  Lsub : L⊆D
  Rsub : R⊆D
  lr : Disjoint L R
  l2 : L.card=2
  r2 : R.card=2
  sa : G.Adj s a
  sb : G.Adj s b
  ax : G.Adj a x
  by' : G.Adj b y
  ac : ∀ z∈K,G.Adj a z
  bc : ∀ z∈K,G.Adj b z
  xL : ∀ z∈L,G.Adj x z
  yR : ∀ z∈R,G.Adj y z
  dark5 : ∀ z∈L∪R,5≤(inside G D z).card
  commonHigh : ∀ z∈K,6≤G.degree z
  exclusiveHigh : 6≤G.degree x ∧ 6≤G.degree y
  commonBounds : ∀ z∈K,∀ w,G.Adj z w → w∈insert a (insert b (P∪(D\(L∪R))))
  ab2 : G.dist a b=2
  xno : ¬G.Adj b x
  yno : ¬G.Adj a y
  sxno : ¬G.Adj s x
  syno : ¬G.Adj s y
  a2 : ∀ z∈L∪(D\(L∪R)),G.dist a z=2
  b2 : ∀ z∈R∪(D\(L∪R)),G.dist b z=2
  behindA : ∀ z∈L,2<G.dist b z
  behindB : ∀ z∈R,2<G.dist a z

private theorem board_cover : ∀ z : V,z=a ∨ z=b ∨ z=s ∨ z=x ∨ z=y ∨ z∈K ∨ z∈D := by decide

private theorem no_adj_exclusive_and_common {L R : Finset V} (F : ThreeBoard G L R)
    (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7) :
    ¬G.Adj x y ∧ (∀ c∈K,¬G.Adj x c) ∧ (∀ c∈K,¬G.Adj y c) := by
  classical
  let W := D\(L∪R)
  have Ssub : L∪R⊆D := union_subset F.Lsub F.Rsub
  have W3 : W.card=3 := by
    change (D\(L∪R)).card=3
    rw [card_sdiff Ssub,d7,card_union_of_disjoint F.lr,F.l2,F.r2]
  have nearA : DistanceTwo G a=insert b (L∪W) := by
    have q : insert b (L∪W)⊆DistanceTwo G a := by
      apply insert_subset (show b∈DistanceTwo G a from mem_filter.mpr ⟨mem_univ _,F.ab2⟩)
      intro z zm
      exact mem_filter.mpr ⟨mem_univ _,F.a2 z zm⟩
    have lw : Disjoint L W :=
      disjoint_left.mpr (fun u ul uw=>(mem_sdiff.mp uw).2 (mem_union_left _ ul))
    have size : (insert b (L∪W)).card=6 := by
      have bOff : b∉L∪W := fun h=>(by decide : b∉D)
        ((mem_union.mp h).elim (fun h=>F.Lsub h) (fun b=>(mem_sdiff.mp b).1))
      rw [card_insert_of_not_mem bOff,card_union_of_disjoint lw,F.l2,W3]
    exact (eq_of_subset_of_card_le q (by rw [size]; exact distanceTwo_le_of_even 6 a (even a))).symm
  have nearB : DistanceTwo G b=insert a (R∪W) := by
    have ba2 : G.dist b a=2 := by rw [dist_comm]; exact F.ab2
    have q : insert a (R∪W)⊆DistanceTwo G b := by
      apply insert_subset (show a∈DistanceTwo G b from mem_filter.mpr ⟨mem_univ _,ba2⟩)
      intro z zm
      exact mem_filter.mpr ⟨mem_univ _,F.b2 z zm⟩
    have lw : Disjoint R W :=
      disjoint_left.mpr (fun u ur uw=>(mem_sdiff.mp uw).2 (mem_union_right _ ur))
    have size : (insert a (R∪W)).card=6 := by
      have off : a∉R∪W := fun h=>(by decide : a∉D)
        ((mem_union.mp h).elim (fun h=>F.Rsub h) (fun b=>(mem_sdiff.mp b).1))
      rw [card_insert_of_not_mem off,card_union_of_disjoint lw,F.r2,W3]
    exact (eq_of_subset_of_card_le q (by rw [size]; exact distanceTwo_le_of_even 6 b (even b))).symm
  have aNo : y∉DistanceTwo G a := by
    rw [nearA]
    intro h
    rcases mem_insert.mp h with e|e
    · exact (by decide : y≠b) e
    exact (by decide : y∉D) ((mem_union.mp e).elim (fun h=>F.Lsub h) (fun h=>(mem_sdiff.mp h).1))
  have bNo : x∉DistanceTwo G b := by
    rw [nearB]
    intro h
    rcases mem_insert.mp h with e|e
    · exact (by decide : x≠a) e
    exact (by decide : x∉D) ((mem_union.mp e).elim (fun h=>F.Rsub h) (fun h=>(mem_sdiff.mp h).1))
  refine ⟨?_,?_,?_⟩
  · exact fun xy=>aNo (d2 hc (by decide) F.yno F.ax xy)
  · exact fun c ck ec=>bNo (d2 hc (by decide) F.xno (F.bc c ck) ec.symm)
  exact fun c ck ec=>aNo (d2 hc (by decide) F.yno (F.ac c ck) ec.symm)

private theorem connect_all_balances {L R : Finset V} (F : ThreeBoard G L R)
    (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7) :
    ∀ w∈D\(L∪R),G.Adj x w ∧ G.Adj y w := by
  classical
  let W := D\(L∪R)
  have ws : W.card=3 := by
    change (D\(L∪R)).card=3
    rw [card_sdiff (union_subset F.Lsub F.Rsub),d7,card_union_of_disjoint F.lr,F.l2,F.r2]
  obtain ⟨xy,xc,yc⟩ := no_adj_exclusive_and_common F hc even
  have classify (z : V) (zd : z∈D) : z∈L ∨ z∈R ∨ z∈W := by
    by_cases p : z∈L∪R
    · exact (mem_union.mp p).imp id Or.inl
    exact .inr (.inr (mem_sdiff.mpr ⟨zd,p⟩))
  have one : G.neighborFinset x⊆insert a (L∪W) := by
    intro z zm
    have xz := (mem_neighborFinset _ _ _).mp zm
    rcases board_cover z with rfl|rfl|rfl|rfl|rfl|zk|zd
    · exact mem_insert_self _ _
    · exact (F.xno xz.symm).elim
    · exact (F.sxno xz.symm).elim
    · exact (G.loopless _ xz).elim
    · exact (xy xz).elim
    · exact (xc _ zk xz).elim
    rcases classify z zd with zl|zr|zw
    · exact mem_insert_of_mem (mem_union_left _ zl)
    · have q := G.dist_le (Walk.cons F.ax (Walk.cons xz .nil))
      simp at q
      have p := F.behindB z zr
      omega
    exact mem_insert_of_mem (mem_union_right _ zw)
  have ot : G.neighborFinset y⊆insert b (R∪W) := by
    intro z zm
    have yz := (mem_neighborFinset _ _ _).mp zm
    rcases board_cover z with rfl|rfl|rfl|rfl|rfl|zk|zd
    · exact (F.yno yz.symm).elim
    · exact mem_insert_self _ _
    · exact (F.syno yz.symm).elim
    · exact (xy yz.symm).elim
    · exact (G.loopless _ yz).elim
    · exact (yc _ zk yz).elim
    rcases classify z zd with zl|zr|zw
    · have q := G.dist_le (Walk.cons F.by' (Walk.cons yz .nil))
      simp at q
      have p := F.behindA z zl
      omega
    · exact mem_insert_of_mem (mem_union_left _ zr)
    exact mem_insert_of_mem (mem_union_right _ zw)
  have cap1 : (insert a (L∪W)).card≤6 := by
    have i := card_insert_le a (L∪W)
    have j := card_union_le L W
    have k := F.l2
    omega
  have cap2 : (insert b (R∪W)).card≤6 := by
    have i := card_insert_le b (R∪W)
    have j := card_union_le R W
    have k := F.r2
    omega
  have eq1 := eq_of_subset_of_card_le one (by
    rw [card_neighborFinset_eq_degree]; exact cap1.trans F.exclusiveHigh.1)
  have eq2 := eq_of_subset_of_card_le ot (by
    rw [card_neighborFinset_eq_degree]; exact cap2.trans F.exclusiveHigh.2)
  exact fun w wm=>⟨(mem_neighborFinset _ _ _).mp (eq1.symm ▸ mem_insert_of_mem (mem_union_right _ wm)),
    (mem_neighborFinset _ _ _).mp (eq2.symm ▸ mem_insert_of_mem (mem_union_right _ wm))⟩

private theorem common_complete_three {L R : Finset V} (F : ThreeBoard G L R)
    (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7) :
    CompleteOn G K ∧ ∃ w∈D\(L∪R),∃ c∈K,G.Adj w c ∧ ((L∪R).filter (G.Adj w)).card≤3 := by
  classical
  let S := L∪R
  let W := D\S
  have Ssub : S⊆D := union_subset F.Lsub F.Rsub
  have S4 : S.card=4 := by change (L∪R).card=4; rw [card_union_of_disjoint F.lr,F.l2,F.r2]
  have KK : K.card=4 := k4
  obtain ⟨_,xc,yc⟩ := no_adj_exclusive_and_common F hc even
  have xys (c : V) (ck : c∈K) : ({s,x,y}:Finset V)⊆DistanceTwo G c := by
    have sn : ¬G.Adj c s := by
      intro g
      have h := F.commonBounds c ck s g
      have wsub : W⊆D := sdiff_subset
      have h' : s∈insert a (insert b (P∪D)) := by
        rcases mem_insert.mp h with p|p
        · exact mem_insert.mpr (.inl p)
        rcases mem_insert.mp p with q|q
        · exact mem_insert_of_mem (mem_insert.mpr (.inl q))
        exact mem_insert_of_mem (mem_insert_of_mem (union_subset_union_right wsub q))
      exact (by decide : s∉insert a (insert b (P∪D))) h'
    have sc : c≠s := fun h=>(by decide : s∉K) (h ▸ ck)
    have xC : c≠x := fun h=>(by decide : x∉K) (h ▸ ck)
    have yC : c≠y := fun h=>(by decide : y∉K) (h ▸ ck)
    have ps := d2 hc sc sn (F.ac c ck).symm F.sa.symm
    have px := d2 hc xC (fun e=>xc c ck e.symm) (F.ac c ck).symm F.ax
    have py := d2 hc yC (fun e=>yc c ck e.symm) (F.bc c ck).symm F.by'
    exact insert_subset ps (insert_subset px (singleton_subset_iff.mpr py))
  have cstr {c u : V} (ck : c∈K) (us : u∈S) : ¬G.Adj c u := by
    intro un
    have U := F.commonBounds c ck u un
    have ud := Ssub us
    rcases mem_insert.mp U with r|r
    · exact (by decide : a∉D) (r ▸ ud)
    rcases mem_insert.mp r with r|r
    · exact (by decide : b∉D) (r ▸ ud)
    rcases mem_union.mp r with r|r
    · exact disjoint_left.mp (by decide : Disjoint P D) r ud
    exact (mem_sdiff.mp r).2 us
  have noPair {c u v : V} (ck : c∈K) (uw : u∈W) (vw : v∈W) (uv : u≠v)
      (cu : G.Adj c u) (cv : G.Adj c v) : False := by
    have sub : S⊆DistanceTwo G c := by
      intro z zs
      have zd := Ssub zs
      have cz : c≠z := fun h=>disjoint_left.mp (by decide : Disjoint K D) ck (h.symm ▸ zd)
      have zu : z≠u := fun h=>(mem_sdiff.mp uw).2 (h ▸ zs)
      have zv : z≠v := fun h=>(mem_sdiff.mp vw).2 (h ▸ zs)
      rcases cannot_miss_two_on_seven D d7 zd (mem_sdiff.mp uw).1 (mem_sdiff.mp vw).1
        zu zv uv (F.dark5 z zs) with h|h
      · exact d2 hc cz (cstr ck zs) cu h.symm
      exact d2 hc cz (cstr ck zs) cv h.symm
    have e : Disjoint ({s,x,y}:Finset V) S := (by decide : Disjoint ({s,x,y}:Finset V) D).mono_right Ssub
    have u := two_local_counts _ _ e _ (xys c ck) sub
    have q := distanceTwo_le_of_even 6 c (even c)
    have r : ({s,x,y}:Finset V).card=3 := by decide
    omega
  have neighbor (c : V) (ck : c∈K) : ∃ w∈W,G.Adj c w := by
    by_cases no : ∃ w∈W,G.Adj c w
    · exact no
    exfalso
    have sub : G.neighborFinset c⊆insert a (insert b (K.erase c)) := by
      intro z zz
      have cz := (mem_neighborFinset _ _ _).mp zz
      rcases mem_insert.mp (F.commonBounds c ck z cz) with r|r
      · exact mem_insert.mpr (.inl r)
      rcases mem_insert.mp r with r|r
      · exact mem_insert_of_mem (mem_insert.mpr (.inl r))
      rcases mem_union.mp r with p|p
      · rcases mem_insert.mp p with p|p
        · exact (xc c ck (p ▸ cz).symm).elim
        rcases mem_insert.mp p with p|p
        · exact (yc c ck (p ▸ cz).symm).elim
        exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨cz.ne.symm,p⟩))
      exact (no ⟨z,p,cz⟩).elim
    have m := card_le_card sub
    rw [card_neighborFinset_eq_degree] at m
    have i := card_insert_le a (insert b (K.erase c))
    have j := card_insert_le b (K.erase c)
    have n := card_erase_add_one ck
    have high := F.commonHigh c ck
    omega
  have eqN (c : V) (ck : c∈K) (w : V) (wm : w∈W) (cw : G.Adj c w) :
      G.neighborFinset c=insert a (insert b (insert w (K.erase c))) := by
    have sub : G.neighborFinset c⊆insert a (insert b (insert w (K.erase c))) := by
      intro z zz
      have cz := (mem_neighborFinset _ _ _).mp zz
      rcases mem_insert.mp (F.commonBounds c ck z cz) with r|r
      · exact mem_insert.mpr (.inl r)
      rcases mem_insert.mp r with r|r
      · exact mem_insert_of_mem (mem_insert.mpr (.inl r))
      rcases mem_union.mp r with p|p
      · rcases mem_insert.mp p with p|p
        · exact (xc c ck (p ▸ cz).symm).elim
        rcases mem_insert.mp p with p|p
        · exact (yc c ck (p ▸ cz).symm).elim
        exact mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨cz.ne.symm,p⟩)))
      have nw : z=w := Classical.byContradiction (fun e=>noPair ck p wm e cz cw)
      exact mem_insert_of_mem (mem_insert_of_mem (mem_insert.mpr (.inl nw)))
    apply eq_of_subset_of_card_le sub
    rw [card_neighborFinset_eq_degree]
    have i := card_insert_le a (insert b (insert w (K.erase c)))
    have j := card_insert_le b (insert w (K.erase c))
    have k := card_insert_le w (K.erase c)
    have n := card_erase_add_one ck
    have high := F.commonHigh c ck
    omega
  constructor
  · intro c ck v vk cv
    obtain ⟨w,wm,cw⟩ := neighbor c ck
    have h : v∈G.neighborFinset c := (eqN c ck w wm cw).symm ▸
      mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨cv.symm,vk⟩)))
    exact (mem_neighborFinset _ _ _).mp h
  have ck : (5:V)∈K := by decide
  obtain ⟨w,wm,cw⟩ := neighbor 5 ck
  let H := S.filter (G.Adj w)
  have sub : H⊆DistanceTwo G 5 := by
    intro z zz
    have ⟨zs,wz⟩ := mem_filter.mp zz
    have ne : (5:V)≠z := fun e=>disjoint_left.mp (by decide : Disjoint K D) ck (e.symm ▸ Ssub zs)
    exact d2 hc ne (cstr ck zs) cw wz
  have e : Disjoint ({s,x,y}:Finset V) H :=
    (by decide : Disjoint ({s,x,y}:Finset V) D).mono_right (fun _ p=>Ssub (mem_filter.mp p).1)
  have h := two_local_counts _ _ e _ (xys 5 ck) sub
  have q := distanceTwo_le_of_even 6 5 (even 5)
  have r : ({s,x,y}:Finset V).card=3 := by decide
  exact ⟨w,wm,5,ck,cw.symm,by change H.card≤3; omega⟩

/-- The normalized three-balanced singleton graph is traceable. -/
theorem traceable_of_normalized_singleton_three_balanced {L R : Finset V}
    (F : ThreeBoard G L R) (hc : G.Connected) (even : ∀ z,(EvenFrom G z).card≤7) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  let S := L∪R
  let W := D\S
  have Ssub : S⊆D := union_subset F.Lsub F.Rsub
  have S4 : S.card=4 := by change (L∪R).card=4; rw [card_union_of_disjoint F.lr,F.l2,F.r2]
  have W3 : W.card=3 := by change (D\S).card=3; rw [card_sdiff Ssub,d7,S4]
  have cover : S∪W=D := union_sdiff_of_subset Ssub
  have dis : Disjoint S W := disjoint_left.mpr (fun i j k=>(mem_sdiff.mp k).2 j)
  have allPort := connect_all_balances F hc even
  obtain ⟨clique,w,wm,c,ck,wc,wcap⟩ := common_complete_three F hc even
  obtain ⟨t,Q,qp,qs⟩ := rooted_path_in_clique K clique ck
  have tk : t∈K := (qs t).mp Q.end_mem_support
  have Q' : RouteOn G K c t := ⟨Q,qp,qs⟩
  by_cases touch : ∃ z∈S,G.Adj w z
  · obtain ⟨p,pm,_,R⟩ := dark_three_balanced_route_to_mark D S W d7 S4 W3 cover dis F.dark5 wm touch wcap
    exact finish_balance_end R Q' F.sa F.ax (allPort p pm).1 wc (F.bc t tk).symm F.by'
  push_neg at touch
  have wd := (mem_sdiff.mp wm).1
  have wN := (mem_sdiff.mp wm).2
  have Z6 : (D.erase w).card=6 := by rw [card_erase_of_mem wd,d7]
  have deg4 (v : V) (vm : v∈D.erase w) : 4≤(inside G (D.erase w) v).card := by
    by_cases vs : v∈S
    · have eq : inside G (D.erase w) v=inside G D v := by
        ext z
        constructor
        · intro h
          exact mem_filter.mpr ⟨(mem_erase.mp (mem_filter.mp h).1).2,(mem_filter.mp h).2⟩
        intro h
        have ⟨zd,vz⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨mem_erase.mpr ⟨fun e=>touch v vs (e ▸ vz).symm,zd⟩,vz⟩
      rw [eq]
      exact (by decide : 4≤5).trans (F.dark5 v vs)
    have vv := (mem_erase.mp vm).1
    have vD := (mem_erase.mp vm).2
    have sub : S⊆inside G (D.erase w) v := by
      intro z zs
      have zw : z≠w := fun e=>wN (e ▸ zs)
      have zv : z≠v := fun e=>vs (e ▸ zs)
      have hit := cannot_miss_two_on_seven D d7 (Ssub zs) wd vD zw zv vv.symm (F.dark5 z zs)
      exact mem_filter.mpr ⟨mem_erase.mpr ⟨zw,Ssub zs⟩,
        (hit.resolve_left (fun h=>touch z zs h.symm)).symm⟩
    have h := card_le_card sub
    omega
  have route {u v : V} (um : u∈D.erase w) (vm : v∈D.erase w) (ne : u≠v) :
      RouteOn G (D.erase w) u v :=
    terminal_route_on_of_local_ore _ um vm ne (by
      intro p pm q qm _ _
      have dp := deg4 p pm
      have dq := deg4 q qm
      omega)
  have liftL {u : V} (ul : u∈L) : u∈D.erase w :=
    mem_erase.mpr ⟨fun e=>wN (mem_union_left _ (e ▸ ul)),F.Lsub ul⟩
  have liftR {u : V} (ur : u∈R) : u∈D.erase w :=
    mem_erase.mpr ⟨fun e=>wN (mem_union_right _ (e ▸ ur)),F.Rsub ur⟩
  by_cases hit : ∃ z∈D,G.Adj w z
  · obtain ⟨z,zd,wz⟩ := hit
    obtain ⟨l,ll,lz⟩ := exists_ne_of_one_lt_card (s:=L) (by rw [F.l2]; decide) z
    have arm := (route (liftL ll) (mem_erase.mpr ⟨wz.ne.symm,zd⟩) lz).suffix wz.symm (not_mem_erase _ _)
    rw [insert_erase wd] at arm
    exact finish_balance_end arm Q' F.sa F.ax (F.xL l ll) wc (F.bc t tk).symm F.by'
  have Lpos : L.Nonempty := card_pos.mp (by rw [F.l2]; decide)
  have Rpos : R.Nonempty := card_pos.mp (by rw [F.r2]; decide)
  obtain ⟨l,ll⟩ := Lpos
  obtain ⟨r,rr⟩ := Rpos
  have nr : l≠r := fun e=>disjoint_left.mp F.lr ll (e.symm ▸ rr)
  exact finish_isolated_dark wd (route (liftL ll) (liftR rr) nr) Q' F.sa F.ax (F.xL l ll)
    (F.yR r rr).symm (allPort w wm).2 wc (F.bc t tk).symm

#print axioms traceable_of_normalized_singleton_three_balanced
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.Singleton16
