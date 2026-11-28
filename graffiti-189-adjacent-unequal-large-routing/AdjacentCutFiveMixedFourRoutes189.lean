import AdjacentCutFiveMixedForeignFive189
import AdjacentCutFiveMixedDarkEnd189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_closed shore_off shore_disjoint from AdjacentCutFiveActual189
open private Vis positive_cap foreign_pos_even from AdjacentCutFiveComponents189
open private d2 mem_positive from AdjacentCutFiveBound189
open private lift_side_path from DegreeFiveSmallSides189
open private universal_of_five_spent from AdjacentCutFiveMixedForeignFive189
open private MixedRootCases from AdjacentCutFiveMixedSevenEight189
open private inside_neighbor_of_nonsingle degree_two_if_nonadjacent from AdjacentCutFiveMixedTwoAugment189
open private augment_both_one_or_two from AdjacentCutFiveMixedBothTerminals189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev RouteCmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem four_common_exclusive_univ (hc : G.Connected)
    (even : ∀ x,(EvenFrom G x).card≤6) {C D : RouteCmp G a b} (cd : C≠D)
    (c4 : (Shore C).card=4)
    {s t x : V} (st : G.Adj s t) (xs : G.Adj s x) (nt : ¬G.Adj t x) (xd : x∈Shore D)
    (toC : t∉Shore C) (toD : t∉Shore D) (sall : ∀ z∈Shore C,G.Adj s z) :
    ∀ z∈Shore D,z=x ∨ G.Adj x z := by
  classical
  have apart : Disjoint (insert t (Shore C)) (Shore D) := by
    apply disjoint_left.mpr
    intro z zm zd
    rcases mem_insert.mp zm with rfl|h
    · exact toD zd
    · exact disjoint_left.mp (shore_disjoint cd) h zd
  refine universal_of_five_spent hc even xd (F:=insert t (Shore C)) ?_ apart ?_
  · simp [card_insert_of_not_mem toC,c4]
  intro z zm
  rcases mem_insert.mp zm with hz|zc
  · rw [hz]
    have xt : x≠t := fun e=>toD (e ▸ xd)
    have dst := (mem_filter.mp (d2 hc xt (fun e=>nt e.symm) xs.symm st)).2
    exact mem_positive.mpr ⟨xt.symm,by rw [dst]; decide⟩
  exact foreign_pos_even hc cd.symm xd zc xs (sall z zc)

private theorem four_common_sees_visible (hc : G.Connected)
    (even : ∀ x,(EvenFrom G x).card≤6) {C D : RouteCmp G a b} (cd : C≠D)
    (c4 : (Shore C).card=4) (common : ∀ z∈Shore C,G.Adj a z ∧ G.Adj b z)
    {x : V} (univX : ∀ z∈Shore D,z=x ∨ G.Adj x z)
    {w : V} (wm : w∈Vis D) :
    (Shore D).card≤(inside G (Shore D) w).card+2 := by
  classical
  obtain ⟨wd,wp⟩ := mem_filter.mp wm
  let N := (Shore D).filter (fun z=>z≠w ∧ ¬G.Adj w z)
  have sep : Disjoint (Shore C) N :=
    (shore_disjoint cd).mono_right (filter_subset _ _)
  have ns : N⊆PositiveEven G w := by
    intro z zm
    obtain ⟨zd,zw,nwz⟩ := mem_filter.mp zm
    have wx : G.Adj w x := by
      rcases univX w wd with e|e
      · subst x
        exact (nwz ((univX z zd).resolve_left zw)).elim
      · exact e.symm
    have xz : G.Adj x z := (univX z zd).resolve_left (fun zx=>nwz (zx.symm ▸ wx))
    have g := (mem_filter.mp (d2 hc zw.symm nwz wx xz)).2
    exact mem_positive.mpr ⟨zw,by simp [g]⟩
  have cs : Shore C⊆PositiveEven G w := by
    intro z zc
    rcases wp with wa|wb
    · exact foreign_pos_even hc cd.symm wd zc wa (common z zc).1
    · exact foreign_pos_even hc cd.symm wd zc wb (common z zc).2
  have e := (card_le_card (union_subset cs ns)).trans (positive_cap w even)
  rw [card_union_of_disjoint sep,c4] at e
  have sub : Shore D⊆insert w (N∪inside G (Shore D) w) := by
    intro z zd
    by_cases zw : z=w
    · exact mem_insert.mpr (.inl zw)
    by_cases wz : G.Adj w z
    · exact mem_insert_of_mem (mem_union_right _ (mem_filter.mpr ⟨zd,wz⟩))
    · exact mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨zd,zw,wz⟩))
  have h := (card_le_card sub).trans (card_insert_le _ _)
  have j := card_union_le N (inside G (Shore D) w)
  omega

private theorem visible_at_least_five_of_universal (hc : G.Connected)
    (even : ∀ x,(EvenFrom G x).card≤6)
    {D : RouteCmp G a b} (d10 : (Shore D).card=10)
    {s x : V} (sx : G.Adj s x) (so : s∉Shore D)
    (port : ∀ z∈Shore D,G.Adj s z → z∈Vis D)
    (univX : ∀ z∈Shore D,z=x ∨ G.Adj x z) :
    5≤(Vis D).card := by
  classical
  have sub : Vis D⊆Shore D := fun _ h=>(mem_filter.mp h).1
  have ds : Shore D \ (Vis D)⊆PositiveEven G s := by
    intro z zm
    obtain ⟨zd,zk⟩ := mem_sdiff.mp zm
    have n : ¬G.Adj s z := fun e=>zk (port z zd e)
    have sz : s≠z := fun e=>so (e.symm ▸ zd)
    have xz := (univX z zd).resolve_left (fun e=>n (e.symm ▸ sx))
    have dst := (mem_filter.mp (d2 hc sz n sx xz)).2
    exact mem_positive.mpr ⟨sz.symm,by rw [dst]; decide⟩
  have c := (card_le_card ds).trans (positive_cap s even)
  have p := card_sdiff_add_card_eq_card sub
  omega

private theorem near_universal_route_of_ten_shore
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {D : RouteCmp G a b} (d10 : (Shore D).card=10)
    (k5 : 5≤(Vis D).card)
    (near : ∀ w∈Vis D,(Shore D).card≤(inside G (Shore D) w).card+2) :
    ∃ x∈Vis D,∃ t,RouteOn G (Shore D) x t := by
  classical
  let S := Shore D
  let U := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let K : Finset U := univ.filter (fun x=>x.val∈Vis D)
  let high (x : U) := 5≤G.degree x.val
  have sc : Fintype.card U=10 := (show Fintype.card U=S.card from Fintype.card_coe S).trans d10
  have kc : K.card=(Vis D).card := by
    apply card_bij (fun u _=>u.val)
    · exact fun u h=>(mem_filter.mp h).2
    · exact fun u _ v _ h=>Subtype.ext h
    · intro u h
      exact ⟨⟨u,(mem_filter.mp h).1⟩,mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩
  have kh : 5≤K.card := kc.symm ▸ k5
  have near' (u : U) (uk : u∈K) : 8≤J.degree u := by
    have h := near u.val (mem_filter.mp uk).2
    rw [inside_card_eq_degree_induce (G:=G) S u,d10] at h
    change 8≤(G.induce (↑S : Set V)).degree u
    omega
  have hk (u : U) (uk : u∈K) : high u := by
    have sub : inside G S u.val ⊆ G.neighborFinset u.val :=
      fun z h=>(mem_neighborFinset G u.val z).mpr (mem_filter.mp h).2
    have h := card_le_card sub
    rw [inside_card_eq_degree_induce (G:=G) S u,card_neighborFinset_eq_degree] at h
    have p := near' u uk
    change 8≤(G.induce (↑S : Set V)).degree u at p
    change 5≤G.degree u.val
    omega
  have dark (u : U) (uk : u∉K) : ¬G.Adj a u.val ∧ ¬G.Adj b u.val := by
    constructor
    · exact fun e=>uk (mem_filter.mpr ⟨mem_univ _,mem_filter.mpr ⟨u.property,.inl e⟩⟩)
    · exact fun e=>uk (mem_filter.mpr ⟨mem_univ _,mem_filter.mpr ⟨u.property,.inr e⟩⟩)
  have allN (u : U) (uk : u∉K) : G.neighborFinset u.val ⊆ S := by
    intro z zm
    have adj := (mem_neighborFinset G u.val z).mp zm
    rcases shore_closed D u.val u.property z adj with rfl|rfl|h
    · exact ((dark u uk).1 adj.symm).elim
    · exact ((dark u uk).2 adj.symm).elim
    exact h
  have dh (u : U) (uh : high u) : 5≤J.degree u := by
    by_cases k : u∈K
    · exact (by omega : 5≤8).trans (near' u k)
    have inc : G.neighborFinset u.val⊆inside G S u.val :=
      fun _ m=>mem_filter.mpr ⟨allN u k m,(mem_neighborFinset G _ _).mp m⟩
    have q := card_le_card inc
    rw [card_neighborFinset_eq_degree,inside_card_eq_degree_induce (G:=G) S u] at q
    exact uh.trans q
  let H : SimpleGraph U :=
    ⟨fun u v=>J.Adj u v ∨ (u≠v ∧ high u ∧ high v ∧ (u∈K ∨ v∈K)),
      by
        intro u v
        rintro (e|⟨ne,uH,vH,k⟩)
        · exact .inl e.symm
        exact .inr ⟨ne.symm,vH,uH,k.symm⟩,
      by intro u; rintro (e|⟨n,_,_,_⟩); exact J.loopless u e; exact n rfl⟩
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have sub : J≤H := fun _ _ h=>.inl h
  have ore (u v : U) (uv : H.Adj u v) (notJ : ¬J.Adj u v) :
      Fintype.card U≤J.degree u+J.degree v := by
    change J.Adj u v ∨ (u≠v ∧ high u ∧ high v ∧ (u∈K ∨ v∈K)) at uv
    obtain ⟨_,uH,vH,h⟩ := uv.resolve_left notJ
    rcases h with uk|vk
    · have p := near' u uk
      have q := dh v vH
      omega
    have p := near' v vk
    have q := dh u uH
    omega
  have lift {x t : U} (xK : x∈K) (p : RouteOn H univ x t) :
      ∃ x∈Vis D,∃ t,RouteOn G S x t := by
    obtain ⟨q,qp,qs⟩ := p
    obtain ⟨w,r,rp,rs⟩ := Graffiti189Ore.rooted_closure sub x ore
      ⟨t,q,qp,fun u=>(qs u).mpr (mem_univ _)⟩
    exact ⟨x.val,(mem_filter.mp xK).2,w.val,lift_side_path S r rp rs⟩
  by_cases n : ∀ u : U, high u
  · let R := (univ : Finset U) \ K
    have part : K∪R=(univ : Finset U) := union_sdiff_of_subset (subset_univ _)
    have dis : Disjoint K R := disjoint_left.mpr (fun _ hm hr=>(mem_sdiff.mp hr).2 hm)
    have rc : R.card≤K.card := by
      have p := card_sdiff_add_card_eq_card (subset_univ K)
      rw [card_univ] at p
      change R.card+K.card=Fintype.card U at p
      omega
    have join : ∀ x∈K,∀ y∈K∪R,x≠y → H.Adj x y :=
      fun x xk y _ xy=>Or.inr ⟨xy,hk x xk,n y,.inl xk⟩
    obtain ⟨x,xk⟩ := card_pos.mp (show 0<K.card by omega)
    obtain ⟨t,p,_⟩ := universal_route_from_singletons K R xk dis join rc
    exact lift xk (part ▸ p)
  push_neg at n
  obtain ⟨l,nl⟩ := n
  have h' (u : U) (ne : u≠l) : high u := (degree u.val l.val
    (fun e=>ne (Subtype.ext e))).resolve_right nl
  have lk : l∉K := fun h=>nl (hk l h)
  let R := ((univ : Finset U).erase l) \ K
  have sub' : K⊆(univ : Finset U).erase l := by
    intro u um
    exact mem_erase.mpr ⟨fun e=>lk (e ▸ um),mem_univ _⟩
  have ru : K∪R=(univ : Finset U).erase l := union_sdiff_of_subset sub'
  have dis : Disjoint K R := disjoint_left.mpr (fun _ hm hr=>(mem_sdiff.mp hr).2 hm)
  have lr : l∉R := fun h=>(mem_erase.mp (mem_sdiff.mp h).1).1 rfl
  have rc : R.card+1≤K.card := by
    have p := card_sdiff_add_card_eq_card sub'
    rw [card_erase_of_mem (mem_univ _),card_univ] at p
    change R.card+K.card=Fintype.card U-1 at p
    omega
  have join : ∀ x∈K,∀ y∈K∪R,x≠y → H.Adj x y := by
    intro x xk y ym ne
    rw [ru] at ym
    exact .inr ⟨ne,hk x xk,h' y (mem_erase.mp ym).1,.inl xk⟩
  have edges : (∃ v∈K,H.Adj v l) ∨ ∃ p∈R,∃ q∈R,p≠q ∧ H.Adj p l ∧ H.Adj l q := by
    by_cases e : ∃ v∈K,J.Adj v l
    · obtain ⟨v,vk,vl⟩ := e
      exact .inl ⟨v,vk,sub vl⟩
    have sz : 2≤(G.neighborFinset l.val).card := by
      rw [card_neighborFinset_eq_degree]
      exact degree_two_if_nonadjacent (u:=l.val) (v:=a) conn
        (fun h=>(shore_off D).1 ((congrArg (fun z : V => z∈S) h).mp l.property)) (fun h=>(dark l lk).1 h.symm)
    obtain ⟨u,um,v,vm,uv⟩ := one_lt_card.mp sz
    let u' : U := ⟨u,allN l lk um⟩
    let v' : U := ⟨v,allN l lk vm⟩
    have lu : J.Adj l u' := (mem_neighborFinset G l.val u).mp um
    have lv : J.Adj l v' := (mem_neighborFinset G l.val v).mp vm
    have ur : u'∈R := mem_sdiff.mpr ⟨mem_erase.mpr ⟨lu.ne.symm,mem_univ _⟩,fun h=>e ⟨u',h,lu.symm⟩⟩
    have vr : v'∈R := mem_sdiff.mpr ⟨mem_erase.mpr ⟨lv.ne.symm,mem_univ _⟩,fun h=>e ⟨v',h,lv.symm⟩⟩
    exact .inr ⟨u',ur,v',vr,fun h=>uv (congrArg Subtype.val h),sub lu.symm,sub lv⟩
  obtain ⟨x,xk,t,p⟩ := universal_route_with_one_dark_exception K R dis join rc (by omega) lk lr edges
  have eq : insert l (K∪R)=(univ : Finset U) := by rw [ru,insert_erase (mem_univ _)]
  exact lift xk (eq ▸ p)

/-- An order-four all-common shore and an order-ten opposite shore with
an exclusive port give a spanning path at the degree-five threshold. -/
theorem traceable_of_adjacent_four_common_ten_non_twin (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : RouteCmp G a b} (cd : C≠D)
    (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (c4 : (Shore C).card=4) (d10 : (Shore D).card=10)
    (common : ∀ z∈Shore C,G.Adj a z ∧ G.Adj b z)
    (ex : ∃ x∈Shore D,(G.Adj a x ∧ ¬G.Adj b x) ∨ (G.Adj b x ∧ ¬G.Adj a x)) :
    ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨x,xd,ep⟩ := ex
  have geom : 5≤(Vis D).card ∧ ∀ w∈Vis D,(Shore D).card≤(inside G (Shore D) w).card+2 := by
    rcases ep with ⟨ax,bx⟩|⟨bx,ax⟩
    · have uni := four_common_exclusive_univ hc even cd c4 ab ax bx xd
        (shore_off C).2 (shore_off D).2 (fun z zm=>(common z zm).1)
      exact ⟨visible_at_least_five_of_universal hc even d10 ax (shore_off D).1
        (fun _ zd az=>mem_filter.mpr ⟨zd,.inl az⟩) uni,
        fun _ w=>four_common_sees_visible hc even cd c4 common uni w⟩
    · have uni := four_common_exclusive_univ hc even cd c4 ab.symm bx ax xd
        (shore_off C).1 (shore_off D).1 (fun z zm=>(common z zm).2)
      exact ⟨visible_at_least_five_of_universal hc even d10 bx (shore_off D).2
        (fun _ zd bz=>mem_filter.mpr ⟨zd,.inr bz⟩) uni,
        fun _ w=>four_common_sees_visible hc even cd c4 common uni w⟩
  obtain ⟨r,rm,t,q⟩ := near_universal_route_of_ten_shore conn degree d10 geom.1 geom.2
  have casesAny {x : V} (add : ∀ u∈Shore C,G.Adj x u) : MixedRootCases C x := by
    by_cases h : ∀ u∈Shore C,5≤G.degree u
    · obtain ⟨u,um⟩ := card_pos.mp (show 0<(Shore C).card by omega)
      exact .inl ⟨h,u,um,add u um⟩
    push_neg at h
    obtain ⟨l,lm,ld⟩ := h
    exact .inr ⟨l,lm,fun u _ e=>(degree u l e).resolve_right (by omega),
      .inl ⟨add l lm,inside_neighbor_of_nonsingle lm (by omega)⟩⟩
  have run {x y : V} (xy : G.Adj x y) (xo : ∀ K : RouteCmp G a b,x∉Shore K)
      (yo : ∀ K : RouteCmp G a b,y∉Shore K)
      (cov : ∀ {z : V}, z≠x → z≠y → z∈Shore C ∨ z∈Shore D)
      (bd : ∀ u∈Shore C,∀ z,G.Adj u z → z=x ∨ z=y ∨ z∈Shore C)
      (root : MixedRootCases C x) (yr : G.Adj y r) :
      ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
    obtain ⟨s,p⟩ := augment_both_one_or_two xy (xo C) (yo C) (by omega) bd root
    have apart : Disjoint (insert y (insert x (Shore C))) (Shore D) := by
      apply disjoint_left.mpr
      intro u um ud
      rcases mem_insert.mp um with rfl|um
      · exact yo D ud
      rcases mem_insert.mp um with rfl|um
      · exact xo D ud
      exact disjoint_left.mp (shore_disjoint cd) um ud
    obtain ⟨w,wp,ws⟩ := p.reverse.join q apart yr
    refine ⟨s,t,w,wp,fun v=>(ws v).mpr ?_⟩
    by_cases e : v=x
    · simp [e]
    by_cases f : v=y
    · simp [f]
    rcases cov e f with h|h <;> simp [h]
  rcases (mem_filter.mp rm).2 with ar|br
  · exact run ab.symm (fun K=>(shore_off K).2) (fun K=>(shore_off K).1)
      (fun nb na=>cover na nb) (fun u um z uz=>by simpa only [or_left_comm] using shore_closed C u um z uz)
      (casesAny (fun u um=>(common u um).2)) ar
  · exact run ab (fun K=>(shore_off K).1) (fun K=>(shore_off K).2) cover
      (shore_closed C) (casesAny (fun u um=>(common u um).1)) br

#print axioms traceable_of_adjacent_four_common_ten_non_twin
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
