import AdjacentCutFiveMixedTwoAugment189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_closed shore_off shore_connected shore_disjoint shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private Vis vis_card_ge_two from AdjacentCutFiveComponents189
open private inside_lower_of_boundary rooted_side from AdjacentCutFiveMixedRouteSmall189
open private root_of_completed_side rooted_partition_one rooted_partition_two inside_neighbor_of_nonsingle degree_two_if_nonadjacent from AdjacentCutFiveMixedTwoAugment189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev RouteCmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem augment_both_one_or_two {C : RouteCmp G a b} {x y : V}
    (xy : G.Adj x y) (xoff : x∉Shore C) (yoff : y∉Shore C) (hi : (Shore C).card≤8)
    (bd : ∀ u∈Shore C, ∀ z,G.Adj u z → z=x ∨ z=y ∨ z∈Shore C)
    (cases' : (∀ u∈Shore C,5≤G.degree u) ∧ (∃ u∈Shore C,G.Adj x u) ∨
      ∃ l∈Shore C,(∀ u∈Shore C,u≠l → 5≤G.degree u) ∧
        ((G.Adj x l ∧ ∃ v∈Shore C, G.Adj l v) ∨
         ∃ u∈Shore C,∃ v∈Shore C,u≠l ∧ u≠v ∧ G.Adj x u ∧ G.Adj l v)) :
    ∃ t,RouteOn G (insert y (insert x (Shore C))) y t := by
  classical
  let S := insert y (insert x (Shore C))
  let W := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let x' : W := ⟨x,mem_insert_of_mem (mem_insert_self _ _)⟩
  let y' : W := ⟨y,mem_insert_self _ _⟩
  let B : Finset W := univ.erase y'
  have sz : Fintype.card W≤10 := by
    have sc : Fintype.card W=S.card := Fintype.card_coe S
    rw [sc]
    have k := card_insert_le y (insert x (Shore C))
    have j := card_insert_le x (Shore C)
    change (insert y (insert x (Shore C))).card≤10
    omega
  have high (u : W) (um : u.val∈Shore C) (du : 5≤G.degree u.val) : 5≤J.degree u := by
    have e := inside_lower_of_boundary (G:=G) S ∅ (u:=u.val) (fun z uz=>by
      rcases bd u.val um z uz with rfl|rfl|h
      · exact .inl (mem_insert_of_mem (mem_insert_self _ _))
      · exact .inl (mem_insert_self _ _)
      · exact .inl (mem_insert_of_mem (mem_insert_of_mem h)))
    rw [inside_card_eq_degree_induce (G:=G) S u,card_empty,add_zero] at e
    change 5≤(G.induce (↑S : Set V)).degree u
    omega
  have lift (A : Finset W) (route : ∃ w,RouteOn (completeWith J A) B x' w) :
      ∃ w, RouteOn (completeWith J A) univ y' w := by
    obtain ⟨w,p⟩ := route
    have he : (completeWith J A).Adj y' x' :=
      completeWith_mono J A (show J.Adj y' x' from xy.symm)
    have eq : insert y' B=(univ : Finset W) := insert_erase (mem_univ _)
    exact ⟨w,eq ▸ p.prefix he (not_mem_erase _ _)⟩
  rcases cases' with ⟨d,u,um,xu⟩|⟨l,lm,d,e⟩
  · let A : Finset W := univ.filter (fun z=>z.val∈Shore C)
    have abs : x'∉A := by simpa [A,x'] using xoff
    let u' : W := ⟨u,mem_insert_of_mem (mem_insert_of_mem um)⟩
    have all : insert x' A=B := by
      ext z
      rcases mem_insert.mp z.property with p|p
      · have e : z=y' := Subtype.ext p
        subst z
        have neq : y'≠x' := fun h=>xy.ne.symm (congrArg Subtype.val h)
        simp [B,neq,A,y',yoff]
      rcases mem_insert.mp p with q|q
      · have e : z=x' := Subtype.ext q
        subst z
        have neq : x'≠y' := fun h=>xy.ne (congrArg Subtype.val h)
        simp [B,neq]
      · have neq : z≠y' := fun h=>yoff (show y∈Shore C by rw [← show z.val=y from congrArg Subtype.val h]; exact q)
        simp [A,q,B,neq]
    refine root_of_completed_side S y y'.property A ?_ (lift A (rooted_partition_one A (J:=J)
      (show J.Adj x' u' from xu) (by simp [A,u',um]) abs all))
    intro u hu v hv _ _
    change Fintype.card W≤J.degree u+J.degree v
    have up := (mem_filter.mp hu).2
    have vp := (mem_filter.mp hv).2
    have ux := high u up (d u.val up)
    have vx := high v vp (d v.val vp)
    omega
  · let A : Finset W := univ.filter (fun z=>z.val∈Shore C ∧ z.val≠l)
    let l' : W := ⟨l,mem_insert_of_mem (mem_insert_of_mem lm)⟩
    have xabs : x'∉A := fun h=>xoff (mem_filter.mp h).2.1
    have labs : l'∉A := fun h=>(mem_filter.mp h).2.2 rfl
    have xl' : x'≠l' := fun h=>xoff (show x∈Shore C by rw [show x=l from congrArg Subtype.val h]; exact lm)
    have all : insert x' (insert l' A)=B := by
      ext z
      rcases mem_insert.mp z.property with p|p
      · have e : z=y' := Subtype.ext p
        subst z
        have neq : y'≠x' := fun h=>xy.ne.symm (congrArg Subtype.val h)
        have nl : y'≠l' := fun h=>yoff (show y∈Shore C by rw [show y=l from congrArg Subtype.val h]; exact lm)
        simp [B,neq,nl,A,y',yoff]
      rcases mem_insert.mp p with q|q
      · have e : z=x' := Subtype.ext q
        subst z
        have neq : x'≠y' := fun h=>xy.ne (congrArg Subtype.val h)
        simp [B,neq]
      · have neq : z≠y' := fun h=>yoff (show y∈Shore C by rw [← show z.val=y from congrArg Subtype.val h]; exact q)
        by_cases e : z.val=l
        · have h : z=l' := Subtype.ext e
          simp [h,B,h ▸ neq]
        · simp [A,q,e,B,neq]
    have split : (J.Adj x' l' ∧ ∃ v∈A,J.Adj l' v) ∨
        ∃ u∈A,∃ v∈A,u≠v ∧ J.Adj x' u ∧ J.Adj l' v := by
      rcases e with ⟨xl,v,vm,lv⟩|⟨u,um,v,vm,ul,uv,xu,lv⟩
      · exact .inl ⟨xl,⟨v,mem_insert_of_mem (mem_insert_of_mem vm)⟩,by simp [A,vm,lv.ne.symm],lv⟩
      · exact .inr ⟨⟨u,mem_insert_of_mem (mem_insert_of_mem um)⟩,by simp [A,um,ul],
          ⟨v,mem_insert_of_mem (mem_insert_of_mem vm)⟩,by simp [A,vm,lv.ne.symm],fun e=>uv (congrArg Subtype.val e),xu,lv⟩
    refine root_of_completed_side S y y'.property A ?_ (lift A (rooted_partition_two A xabs labs xl' all split))
    intro u hu v hv _ _
    change Fintype.card W≤J.degree u+J.degree v
    have up := (mem_filter.mp hu).2
    have vp := (mem_filter.mp hv).2
    have ux := high u up.1 (d u.val up.1 up.2)
    have vx := high v vp.1 (d v.val vp.1 vp.2)
    omega

private theorem small_cut_root_of_high {C : RouteCmp G a b} {x : V}
    (xm : x∈Shore C) (hi : (Shore C).card≤6)
    (degree : ∀ u∈Shore C,5≤G.degree u) :
    ∃ t,RouteOn G (Shore C) x t := by
  classical
  let S := Shore C
  let W := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let A : Finset W := univ
  let x' : W := ⟨x,xm⟩
  have sz : Fintype.card W≤6 := by
    have sc : Fintype.card W=S.card := Fintype.card_coe S
    rwa [sc]
  have high (u : W) : 3≤J.degree u := by
    have bound (z : V) (uz : G.Adj u.val z) : z∈S ∨ z∈({a,b}:Finset V) := by
      rcases shore_closed C u.val u.property z uz with rfl|rfl|h
      · exact .inr (by simp)
      · exact .inr (by simp)
      · exact .inl h
    have h := inside_lower_of_boundary (G:=G) S {a,b} bound
    rw [inside_card_eq_degree_induce (G:=G) S u] at h
    have h2 : ({a,b}:Finset V).card≤2 := (card_insert_le a {b}).trans (by simp)
    have d := degree u.val u.property
    change 3≤(G.induce (↑S : Set V)).degree u
    omega
  refine root_of_completed_side S x xm A (fun u _ v _ _ _=>by
    change Fintype.card W≤J.degree u+J.degree v
    have h := high u
    have k := high v
    omega) ?_
  obtain ⟨t,p,pp,ps⟩ := rooted_path_in_clique A (completeWith_of_mem J A)
    (show x'∈A from mem_univ _)
  exact ⟨t,p,pp,ps⟩

/-- Allocate both terminals to the larger shore. No parity or twin assumption. -/
theorem traceable_of_mixed_adjacent_two_shores_small_eight (ab : G.Adj a b)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : RouteCmp G a b} (cd : C≠D)
    (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (clo : 2≤(Shore C).card) (chi : (Shore C).card≤6)
    (dlo : 2≤(Shore D).card) (dhi : (Shore D).card≤8) :
    ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have db {u : V} (um : u∈Shore D) := shore_closed D u um
  have dbs {u : V} (um : u∈Shore D) :
      ∀ z,G.Adj u z → z=b ∨ z=a ∨ z∈Shore D := by
    intro z uz
    simpa only [or_left_comm] using db um z uz
  have glue {x y s t z : V} (_xy : G.Adj x y) (xoff : x∉Shore C) (yoff : y∉Shore C)
      (cov : ∀ {v : V},v≠x → v≠y → v∈Shore C ∨ v∈Shore D)
      (p : RouteOn G (Shore C) z s) (yz : G.Adj y z)
      (q : RouteOn G (insert y (insert x (Shore D))) y t) :
      ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
    have apart : Disjoint (Shore C) (insert y (insert x (Shore D))) := by
      apply disjoint_left.mpr
      intro v vm vn
      rcases mem_insert.mp vn with rfl|vn
      · exact yoff vm
      rcases mem_insert.mp vn with rfl|vn
      · exact xoff vm
      exact disjoint_left.mp (shore_disjoint cd) vm vn
    obtain ⟨w,wp,ws⟩ := p.reverse.join q apart yz.symm
    refine ⟨s,t,w,wp,fun v=>(ws v).mpr ?_⟩
    by_cases e : v=x
    · simp [e]
    by_cases f : v=y
    · simp [f]
    rcases cov e f with h|h <;> simp [h]
  by_cases h : ∀ u∈Shore D,5≤G.degree u
  · have cdeg {u : V} (uc : u∈Shore C) :
        G.degree u≤(inside G (Shore C) u).card+2 := by
      have q := inside_lower_of_boundary (G:=G) (Shore C) {a,b} (u:=u)
        (fun w uw=>by
          rcases shore_closed C u uc w uw with rfl|rfl|k
          · exact .inr (by simp)
          · exact .inr (by simp)
          · exact .inl k)
      simpa [ab.ne] using q
    obtain ⟨v,hv,w,hw,vw⟩ := one_lt_card.mp (vis_card_ge_two ab.ne conn C clo)
    obtain ⟨s,t,port,p⟩ := rooted_side (Shore C) (fun z=>G.Adj a z ∨ G.Adj b z)
      (fun z=>5≤G.degree z) (shore_connected C)
      ⟨v,(mem_filter.mp hv).1,w,(mem_filter.mp hw).1,vw,(mem_filter.mp hv).2,(mem_filter.mp hw).2⟩
      (fun u _ v _ uv=>degree u v uv) (by
        intro u uc v vc _ _ hu hv
        have du := cdeg uc
        have dv := cdeg vc
        omega)
    rcases port with as'|bs'
    · obtain ⟨z,q⟩ := augment_both_one_or_two ab.symm (shore_off D).2 (shore_off D).1 dhi
        (fun _=>dbs) (.inl ⟨h,shore_hit_b ab.ne conn D⟩)
      exact glue ab.symm (shore_off C).2 (shore_off C).1 (fun nb na=>cover na nb) p as' q
    · obtain ⟨z,q⟩ := augment_both_one_or_two ab (shore_off D).1 (shore_off D).2 dhi
        (fun _=>db) (.inl ⟨h,shore_hit_a ab.ne conn D⟩)
      exact glue ab (shore_off C).1 (shore_off C).2 cover p bs' q
  push_neg at h
  obtain ⟨l,lm,dl⟩ := h
  have hi (u : V) (_ : u∈Shore D) (ul : u≠l) : 5≤G.degree u :=
    (degree u l ul).resolve_right (by omega)
  have ch (u : V) (um : u∈Shore C) : 5≤G.degree u :=
    (degree u l (fun e=>disjoint_left.mp (shore_disjoint cd) um (e.symm ▸ lm))).resolve_right (by omega)
  obtain ⟨s,sm,bs⟩ := shore_hit_b ab.ne conn C
  obtain ⟨t,p⟩ := small_cut_root_of_high sm chi ch
  have ra (e : (G.Adj a l ∧ ∃ v∈Shore D,G.Adj l v) ∨
      ∃ u∈Shore D,∃ v∈Shore D,u≠l ∧ u≠v ∧ G.Adj a u ∧ G.Adj l v) :
      ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
    obtain ⟨z,q⟩ := augment_both_one_or_two ab (shore_off D).1 (shore_off D).2 dhi
      (fun _=>db) (.inr ⟨l,lm,hi,e⟩)
    exact glue ab (shore_off C).1 (shore_off C).2 cover p bs q
  by_cases al : G.Adj a l
  · exact ra (.inl ⟨al,inside_neighbor_of_nonsingle lm dlo⟩)
  by_cases bl : G.Adj b l
  · obtain ⟨u,um,au⟩ := shore_hit_a ab.ne conn C
    obtain ⟨v,p'⟩ := small_cut_root_of_high um chi ch
    obtain ⟨z,q⟩ := augment_both_one_or_two ab.symm (shore_off D).2 (shore_off D).1 dhi
      (fun _=>dbs) (.inr ⟨l,lm,hi,.inl ⟨bl,inside_neighbor_of_nonsingle lm dlo⟩⟩)
    exact glue ab.symm (shore_off C).2 (shore_off C).1 (fun nb na=>cover na nb) p' au q
  obtain ⟨u,um,au⟩ := shore_hit_a ab.ne conn D
  have bnd : G.neighborFinset l ⊆ Shore D := by
    intro v vm
    have lv := (mem_neighborFinset G l v).mp vm
    rcases db lm v lv with rfl|rfl|e
    · exact (al lv.symm).elim
    · exact (bl lv.symm).elim
    · exact e
  have sz : 2≤(G.neighborFinset l).card := by
    rw [card_neighborFinset_eq_degree]
    exact degree_two_if_nonadjacent (u:=l) (v:=a) conn (fun e=>(shore_off D).1 (e ▸ lm)) (fun e=>al e.symm)
  obtain ⟨v,vm,w,wm,vw⟩ := one_lt_card.mp sz
  have ext : ∃ r∈G.neighborFinset l,u≠r := by
    by_cases hu : u=v
    · exact ⟨w,wm,fun e=>vw (hu.symm.trans e)⟩
    · exact ⟨v,vm,hu⟩
  obtain ⟨r,rm,ur⟩ := ext
  exact ra (.inr ⟨u,um,r,bnd rm,fun e=>al (e ▸ au),ur,au,(mem_neighborFinset G l r).mp rm⟩)

#print axioms traceable_of_mixed_adjacent_two_shores_small_eight
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
