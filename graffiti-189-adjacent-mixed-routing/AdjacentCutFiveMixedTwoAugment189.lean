import AdjacentCutFiveMixedRouteSmall189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_closed shore_off shore_connected shore_disjoint shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private lift_side_path from DegreeFiveSmallSides189
open private inside_lower_of_boundary from AdjacentCutFiveMixedRouteSmall189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev RouteCmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem root_of_completed_side (S : Finset V) (x : V) (xm : x∈S)
    (A : Finset ↑(↑S : Set V))
    (ore : ∀ u∈A,∀ v∈A, u≠v → ¬(G.induce (↑S : Set V)).Adj u v →
      Fintype.card ↑(↑S : Set V)≤(G.induce (↑S : Set V)).degree u+
                                 (G.induce (↑S : Set V)).degree v)
    (route : ∃ t, RouteOn (completeWith (G.induce (↑S : Set V)) A) univ ⟨x,xm⟩ t) :
    ∃ t,RouteOn G S x t := by
  classical
  let J := G.induce (↑S : Set V)
  classical
  let H := completeWith J A
  have sub : J≤H := completeWith_mono J A
  have ok (u v : ↑(↑S : Set V)) (uv : H.Adj u v) (no : ¬J.Adj u v) :
      Fintype.card ↑(↑S : Set V)≤J.degree u+J.degree v := by
    change J.Adj u v ∨ _ at uv
    obtain ⟨ua,va,ne⟩ := uv.resolve_left no
    exact ore u ua v va ne no
  obtain ⟨t,p,pp,ps⟩ := route
  obtain ⟨r,q,qp,qs⟩ := Graffiti189Ore.rooted_closure sub ⟨x,xm⟩ ok
    ⟨t,p,pp,fun z=>(ps z).mpr (mem_univ _)⟩
  exact ⟨r.val,lift_side_path S q qp qs⟩

private theorem rooted_partition_one {W : Type*} [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} [DecidableRel J.Adj]
    (A : Finset W) {B : Finset W} {x u : W} (xu : J.Adj x u) (um : u∈A) (xn : x∉A)
    (all : insert x A=B) :
    ∃ v,RouteOn (completeWith J A) B x v := by
  classical
  let H := completeWith J A
  have sub : J≤H := completeWith_mono J A
  obtain ⟨v,p,pp,ps⟩ := rooted_path_in_clique A (completeWith_of_mem J A) um
  have h : RouteOn H A u v := ⟨p,pp,ps⟩
  exact ⟨v,all ▸ h.prefix (sub xu) xn⟩

private theorem rooted_partition_two {W : Type*} [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} [DecidableRel J.Adj] (A : Finset W) {B : Finset W}
    {x l : W} (xn : x∉A) (ln : l∉A) (xl : x≠l)
    (all : insert x (insert l A)=B)
    (split : (J.Adj x l ∧ ∃ v∈A,J.Adj l v) ∨
       ∃ u∈A,∃ v∈A,u≠v ∧ J.Adj x u ∧ J.Adj l v) :
    ∃ v,RouteOn (completeWith J A) B x v := by
  classical
  let H := completeWith J A
  have sub : J≤H := completeWith_mono J A
  have xni : x∉insert l A := fun h=>(mem_insert.mp h).elim xl xn
  rcases split with ⟨e,v,vm,lv⟩|⟨u,um,v,vm,uv,xu,lv⟩
  · obtain ⟨w,p,pp,ps⟩ := rooted_path_in_clique A (completeWith_of_mem J A) vm
    have h : RouteOn H A v w := ⟨p,pp,ps⟩
    exact ⟨w,all ▸ (h.prefix (sub lv) ln).prefix (sub e) xni⟩
  · obtain ⟨p,pp,ps⟩ := path_between_in_clique A (completeWith_of_mem J A) um vm uv
    have h : RouteOn H A u v := ⟨p,pp,ps⟩
    exact ⟨l,all ▸ (h.suffix (sub lv.symm) ln).prefix (sub xu) xni⟩

private theorem augment_degree {C : RouteCmp G a b} {x y : V} (u : V) (_um : u∈Shore C)
    (bd : ∀ z,G.Adj u z → z=x ∨ z=y ∨ z∈Shore C) :
    G.degree u≤(inside G (insert x (Shore C)) u).card+1 := by
  classical
  have h := inside_lower_of_boundary (G:=G) (insert x (Shore C)) {y} (u:=u)
    (fun z uz=>by
      rcases bd z uz with rfl|rfl|h
      · exact .inl (mem_insert_self _ _)
      · exact .inr (mem_singleton_self _)
      · exact .inl (mem_insert_of_mem h))
  simpa using h

private theorem augment_one_or_two {C : RouteCmp G a b} {x y : V}
    (xoff : x∉Shore C) (hi : (Shore C).card≤7)
    (bd : ∀ u∈Shore C, ∀ z,G.Adj u z → z=x ∨ z=y ∨ z∈Shore C)
    (cases' : (∀ u∈Shore C,5≤G.degree u) ∧ (∃ u∈Shore C,G.Adj x u) ∨
      ∃ l∈Shore C,(∀ u∈Shore C,u≠l → 5≤G.degree u) ∧
        ((G.Adj x l ∧ ∃ v∈Shore C, G.Adj l v) ∨
         ∃ u∈Shore C,∃ v∈Shore C,u≠l ∧ u≠v ∧ G.Adj x u ∧ G.Adj l v)) :
    ∃ t,RouteOn G (insert x (Shore C)) x t := by
  classical
  let S := insert x (Shore C)
  let W := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let x' : W := ⟨x,mem_insert_self _ _⟩
  have sz : Fintype.card W≤8 := by
    have sc : Fintype.card W=S.card := Fintype.card_coe S
    rw [sc]
    exact (card_insert_le _ _).trans (by omega)
  have high (u : W) (um : u.val∈Shore C) (du : 5≤G.degree u.val) : 4≤J.degree u := by
    have e := augment_degree u.val um (bd u.val um)
    rw [inside_card_eq_degree_induce (G:=G) S u] at e
    change 4≤(G.induce (↑S : Set V)).degree u
    omega
  rcases cases' with ⟨d,u,um,xu⟩|⟨l,lm,d,e⟩
  · let A : Finset W := univ.filter (fun z=>z.val∈Shore C)
    have abs : x'∉A := by simpa [A,x'] using xoff
    let u' : W := ⟨u,mem_insert_of_mem um⟩
    have all : insert x' A=(univ : Finset W) := by
      ext z
      have p := mem_insert.mp z.property
      rcases p with q|q
      · simp [show z=x' from Subtype.ext q]
      · simp [A,q]
    refine root_of_completed_side S x x'.property A ?_ (rooted_partition_one A (J:=J)
      (show J.Adj x' u' from xu) (by simp [A,u',um]) abs all)
    intro u hu v hv _ _
    change Fintype.card W≤J.degree u+J.degree v
    have up := (mem_filter.mp hu).2
    have vp := (mem_filter.mp hv).2
    have ux := high u up (d u.val up)
    have vx := high v vp (d v.val vp)
    omega
  · let A : Finset W := univ.filter (fun z=>z.val∈Shore C ∧ z.val≠l)
    let l' : W := ⟨l,mem_insert_of_mem lm⟩
    have xabs : x'∉A := fun h=>xoff (mem_filter.mp h).2.1
    have labs : l'∉A := fun h=>(mem_filter.mp h).2.2 rfl
    have xl' : x'≠l' := fun h=>xoff (show x∈Shore C by rw [show x=l from congrArg Subtype.val h]; exact lm)
    have all : insert x' (insert l' A)=(univ : Finset W) := by
      ext z
      rcases mem_insert.mp z.property with p|p
      · simp [show z=x' from Subtype.ext p]
      by_cases q : z.val=l
      · simp [show z=l' from Subtype.ext q]
      · simp [A,p,q]
    have split : (J.Adj x' l' ∧ ∃ v∈A,J.Adj l' v) ∨
        ∃ u∈A,∃ v∈A,u≠v ∧ J.Adj x' u ∧ J.Adj l' v := by
      rcases e with ⟨xl,v,vm,lv⟩|⟨u,um,v,vm,ul,uv,xu,lv⟩
      · exact .inl ⟨xl,⟨v,mem_insert_of_mem vm⟩,by simp [A,vm,lv.ne.symm],lv⟩
      · exact .inr ⟨⟨u,mem_insert_of_mem um⟩,by simp [A,um,ul],
          ⟨v,mem_insert_of_mem vm⟩,by simp [A,vm,lv.ne.symm],fun e=>uv (congrArg Subtype.val e),xu,lv⟩
    refine root_of_completed_side S x x'.property A ?_ (rooted_partition_two A xabs labs xl' all split)
    intro u hu v hv _ _
    change Fintype.card W≤J.degree u+J.degree v
    have up := (mem_filter.mp hu).2
    have vp := (mem_filter.mp hv).2
    have ux := high u up.1 (d u.val up.1 up.2)
    have vx := high v vp.1 (d v.val vp.1 vp.2)
    omega

private theorem inside_neighbor_of_nonsingle {C : RouteCmp G a b} {l : V}
    (lm : l∈Shore C) (lo : 2≤(Shore C).card) : ∃ v∈Shore C,G.Adj l v := by
  classical
  let S := ↑(↑(Shore C) : Set V)
  obtain ⟨u,um,v,vm,uv⟩ := one_lt_card.mp lo
  have ex : ∃ w∈Shore C,l≠w := by
    by_cases e : l=u
    · exact ⟨v,vm,e.trans_ne uv⟩
    · exact ⟨u,um,e⟩
  obtain ⟨w,wm,lw⟩ := ex
  obtain ⟨p⟩ := (shore_connected C).preconnected (⟨l,lm⟩ : S) ⟨w,wm⟩
  have e : (⟨l,lm⟩ : S) ≠ ⟨w,wm⟩ := fun h=>lw (congrArg Subtype.val h)
  cases p with
  | nil => exact (e rfl).elim
  | @cons _ q _ edge _ => exact ⟨q.val,q.property,edge⟩

private theorem degree_two_if_nonadjacent
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    {u v : V} (uv : u≠v) (no : ¬G.Adj u v) : 2≤G.degree u := by
  classical
  by_contra h
  let N := G.neighborFinset u
  have cap : N.card<2 := Nat.lt_of_not_ge h
  let T := (↑N : Set V)ᶜ
  have uh : u∈T := fun e=>G.loopless _ ((mem_neighborFinset G u u).mp e)
  have vh : v∈T := fun e=>no ((mem_neighborFinset G u v).mp e)
  obtain ⟨q⟩ := (conn N cap).preconnected (⟨u,uh⟩ : T) ⟨v,vh⟩
  have ne : (⟨u,uh⟩ : T) ≠ ⟨v,vh⟩ := fun e=>uv (congrArg Subtype.val e)
  cases q with
  | nil => exact ne rfl
  | @cons _ w _ e q =>
    exact w.property ((mem_neighborFinset G u w.val).mpr e)

/-- Two adjacent terminals and two shores of size two through seven are traceable
at the degree-five threshold without using an even-distance or twin assumption. -/
theorem traceable_of_mixed_adjacent_two_shores_le_seven (ab : G.Adj a b)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : RouteCmp G a b} (cd : C≠D)
    (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (clo : 2≤(Shore C).card) (chi : (Shore C).card≤7)
    (dlo : 2≤(Shore D).card) (dhi : (Shore D).card≤7) :
    ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have side {K : RouteCmp G a b} {z : V} (zm : z∈Shore K) :=
    shore_closed K z zm
  have sw {K : RouteCmp G a b} {z : V} (zm : z∈Shore K) :
      ∀ w,G.Adj z w → w=b ∨ w=a ∨ w∈Shore K := by
    intro w zw
    simpa only [or_left_comm] using shore_closed K z zm w zw
  have run {K L : RouteCmp G a b} (kl : K≠L)
      (cov : ∀ {z : V}, z≠a → z≠b → z∈Shore K ∨ z∈Shore L)
      (km : 2≤(Shore K).card) (kx : (Shore K).card≤7) (lx : (Shore L).card≤7)
      (lh : ∀ z∈Shore L,5≤G.degree z) :
      ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
    have join {x y s t : V} (xy : G.Adj x y)
        (xL : x∉Shore L) (yK : y∉Shore K)
        (cov' : ∀ {z : V},z≠x → z≠y → z∈Shore K ∨ z∈Shore L)
        (p : RouteOn G (insert x (Shore K)) x s)
        (q : RouteOn G (insert y (Shore L)) y t) :
        ∃ u v,∃ w : G.Walk u v,w.IsPath ∧ ∀ z,z∈w.support := by
      have apart : Disjoint (insert x (Shore K)) (insert y (Shore L)) := by
        apply disjoint_left.mpr
        intro z zm zn
        rcases mem_insert.mp zm with rfl|zm
        · exact (mem_insert.mp zn).elim xy.ne xL
        rcases mem_insert.mp zn with rfl|zn
        · exact yK zm
        · exact disjoint_left.mp (shore_disjoint kl) zm zn
      obtain ⟨w,wp,ws⟩ := p.reverse.join q apart xy
      refine ⟨s,t,w,wp,fun z=>(ws z).mpr ?_⟩
      by_cases e : z=x
      · simp [e]
      by_cases f : z=y
      · simp [f]
      rcases cov' e f with h|h <;> simp [h]
    have ra (e : (∀ u∈Shore K,5≤G.degree u) ∧ (∃ u∈Shore K,G.Adj a u) ∨
      ∃ l∈Shore K,(∀ u∈Shore K,u≠l → 5≤G.degree u) ∧
        ((G.Adj a l ∧ ∃ v∈Shore K, G.Adj l v) ∨
         ∃ u∈Shore K,∃ v∈Shore K,u≠l ∧ u≠v ∧ G.Adj a u ∧ G.Adj l v)) :
        ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
      obtain ⟨s,p⟩ := augment_one_or_two (y:=b) (shore_off K).1 kx (fun _=>side) e
      obtain ⟨t,q⟩ := augment_one_or_two (y:=a) (shore_off L).2 lx (fun _=>sw)
        (.inl ⟨lh,shore_hit_b ab.ne conn L⟩)
      exact join ab (shore_off L).1 (shore_off K).2 cov p q
    by_cases h : ∀ u∈Shore K,5≤G.degree u
    · exact ra (.inl ⟨h,shore_hit_a ab.ne conn K⟩)
    push_neg at h
    obtain ⟨l,lm,dl⟩ := h
    have hi (u : V) (_ : u∈Shore K) (ul : u≠l) : 5≤G.degree u :=
      (degree u l ul).resolve_right (by omega)
    by_cases al : G.Adj a l
    · exact ra (.inr ⟨l,lm,hi,.inl ⟨al,inside_neighbor_of_nonsingle lm km⟩⟩)
    by_cases bl : G.Adj b l
    · obtain ⟨s,p⟩ := augment_one_or_two (y:=a) (shore_off K).2 kx (fun _=>sw)
        (.inr ⟨l,lm,hi,.inl ⟨bl,inside_neighbor_of_nonsingle lm km⟩⟩)
      obtain ⟨t,q⟩ := augment_one_or_two (y:=b) (shore_off L).1 lx (fun _=>side)
        (.inl ⟨lh,shore_hit_a ab.ne conn L⟩)
      exact join ab.symm (shore_off L).2 (shore_off K).1 (fun zb za=>cov za zb) p q
    obtain ⟨u,um,au⟩ := shore_hit_a ab.ne conn K
    have bnd : G.neighborFinset l ⊆ Shore K := by
      intro v vm
      have lv := (mem_neighborFinset G l v).mp vm
      rcases shore_closed K l lm v lv with rfl|rfl|e
      · exact (al lv.symm).elim
      · exact (bl lv.symm).elim
      · exact e
    have sz : 2≤(G.neighborFinset l).card := by
      rw [card_neighborFinset_eq_degree]
      exact degree_two_if_nonadjacent (u:=l) (v:=a) conn (fun e=>(shore_off K).1 (e ▸ lm)) (fun e=>al e.symm)
    obtain ⟨v,vm,w,wm,vw⟩ := one_lt_card.mp sz
    have ext : ∃ r∈G.neighborFinset l,u≠r := by
      by_cases hu : u=v
      · exact ⟨w,wm,fun e=>vw (hu.symm.trans e)⟩
      · exact ⟨v,vm,hu⟩
    obtain ⟨r,rm,ur⟩ := ext
    exact ra (.inr ⟨l,lm,hi,.inr
      ⟨u,um,r,bnd rm,fun e=>al (e ▸ au),ur,au,(mem_neighborFinset G l r).mp rm⟩⟩)
  by_cases d : ∀ z∈Shore D,5≤G.degree z
  · exact run cd cover clo chi dhi d
  push_neg at d
  obtain ⟨l,lm,dl⟩ := d
  exact run cd.symm (fun na nb=>(cover na nb).symm) dlo dhi chi (fun z zm=>
    (degree z l (fun e=>disjoint_left.mp (shore_disjoint cd) zm (e.symm ▸ lm))).resolve_right (by omega))

#print axioms traceable_of_mixed_adjacent_two_shores_le_seven
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
