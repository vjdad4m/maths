import ReplicaBudget

open Finset
namespace KelmansCactus.CenterRigidity
open Substitute

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
private theorem restrict_local {P : Finset (Finset V)} {A D : Finset V}
    (p : Assemble.LocalPart G P A) (closed : ∀ x∈D, ∀ y∈A, G.Adj x y → y∈D) :
    Closed G (A∩D) := by
  classical
  let Q := P.filter fun t => t ⊆ D
  have sub : Q ⊆ P := filter_subset _ _
  refine ⟨Q,⟨fun t h => p.tile t (sub h),
    fun t ht s hs ne => p.disj t (sub ht) s (sub hs) ne,?_⟩⟩
  ext v
  constructor
  · intro hv
    obtain ⟨t,ht,vt⟩ := mem_biUnion.mp hv
    have hh := mem_filter.mp ht
    exact mem_inter.mpr ⟨p.tile_sub G hh.1 vt,hh.2 vt⟩
  · intro hv
    obtain ⟨va,vd⟩ := mem_inter.mp hv
    obtain ⟨t,ht,vt⟩ := mem_biUnion.mp (p.cover.symm ▸ va)
    have ta := p.tile_sub G ht
    obtain ⟨_,c,ct,star⟩ := p.tile t ht
    have cd : c∈D := by
      by_cases e : v=c
      · exact e ▸ vd
      · exact closed v vd c (ta ct) (star v vt e).symm
    have td : t ⊆ D := by
      intro u ut
      by_cases e : u=c
      · exact e.symm ▸ cd
      · exact closed c cd u (ta ut) (star u ut e)
    exact mem_biUnion.mpr ⟨t,mem_filter.mpr ⟨ht,td⟩,vt⟩

omit [Fintype V] in
/-- When the difference region is retiled, its connected components
contain a multiple of three of the old uncovered vertices. In particular,
with exactly three holes one component must contain all of them. -/
theorem three_holes_join {W H : Finset V} (inc : H ⊆ W) (cnt : H.card=3)
    (old : Closed G (W\H)) (fresh : Closed G W) {a b : V} (ha : a∈H) (hb : b∈H) :
    (G.induce (W : Set V)).Reachable ⟨a,inc ha⟩ ⟨b,inc hb⟩ := by
  classical
  let E := G.induce (W : Set V)
  let D := W.filter (fun v => ∃ h : v∈W, E.Reachable ⟨a,inc ha⟩ ⟨v,h⟩)
  have aD : a∈D := mem_filter.mpr ⟨inc ha,inc ha,SimpleGraph.Reachable.rfl⟩
  have close (u : V) (hu : u∈D) (v : V) (hv : v∈W) (e : G.Adj u v) : v∈D := by
    obtain ⟨_,hu',walk⟩ := mem_filter.mp hu
    have good : E.Adj ⟨u,hu'⟩ ⟨v,hv⟩ := e
    exact mem_filter.mpr ⟨hv,hv,walk.trans good.reachable⟩
  have sub : D ⊆ W := filter_subset _ _
  obtain ⟨P,hP⟩ := old
  obtain ⟨Q,hQ⟩ := fresh
  have prev := restrict_local hP (fun v vv u hu e => close v vv u (mem_sdiff.mp hu).1 e)
  have curr := restrict_local hQ close
  have eprev : (W\H)∩D = D\H := by
    ext x
    simp only [mem_inter,mem_sdiff]
    have hh := fun h : x∈D => sub h
    tauto
  have ecurr : W∩D = D := inter_eq_right.mpr sub
  rw [eprev] at prev
  rw [ecurr] at curr
  have nprev := ReplicaBudget.closed_card prev
  have ncurr := ReplicaBudget.closed_card curr
  have cut := card_sdiff_add_card_inter D H
  have inc' : D∩H ⊆ H := inter_subset_right
  have cap := card_le_card inc'
  have pos : 0 < (D∩H).card := card_pos.mpr ⟨a,mem_inter.mpr ⟨aD,ha⟩⟩
  have full : (D∩H).card = H.card := by omega
  have eq : D∩H=H := eq_of_subset_of_card_le inc' full.ge
  have bd : b∈D := (mem_inter.mp (eq.symm ▸ hb)).1
  obtain ⟨_,_,walk⟩ := mem_filter.mp bd
  exact walk

/-- An oriented packing, with a designated centre for every tile. -/
structure Layout (G : SimpleGraph V) (C S : Finset V) (block : V→Finset V) : Prop where
  shape : ∀ c∈C, (block c).card=3 ∧ c∈block c ∧ ∀ v∈block c, v≠c → G.Adj c v
  apart : (C : Set V).PairwiseDisjoint block
  covers : C.biUnion block=S

omit [Fintype V] in
theorem layout_parts {C S : Finset V} {B : V→Finset V}
    (p : Layout G C S B) : Assemble.LocalPart G (C.image B) S := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro t ht
    obtain ⟨c,hc,rfl⟩ := mem_image.mp ht
    obtain ⟨h,cb,st⟩ := p.shape c hc
    exact ⟨h,c,cb,st⟩
  · intro t ht u hu ne
    obtain ⟨c,hc,rfl⟩ := mem_image.mp ht
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hu
    exact p.apart hc hd (fun er => ne (congrArg B er))
  · rw [← p.covers]
    ext x
    constructor
    · intro hx
      obtain ⟨t,ht,tx⟩ := mem_biUnion.mp hx
      obtain ⟨c,hc,rfl⟩ := mem_image.mp ht
      exact mem_biUnion.mpr ⟨c,hc,tx⟩
    · intro hx
      obtain ⟨c,hc,tx⟩ := mem_biUnion.mp hx
      exact mem_biUnion.mpr ⟨B c,mem_image.mpr ⟨c,hc,rfl⟩,tx⟩


omit [Fintype V] in
theorem layout_local {C S : Finset V} {B : V→Finset V}
    (p : Layout G C S B) : Closed G S :=
  ⟨C.image B,layout_parts p⟩

omit [Fintype V] in
/-- Every actual packing can be given an orientation in Layout; if tiles
already come with chosen centres, use these choices in the same proof. -/
theorem layout_of_tiles {P : Finset (Finset V)} {S : Finset V}
    (p : Assemble.LocalPart G P S) (center : ↥P → V)
    (hc : ∀ t : ↥P, center t ∈ t.val ∧ ∀ x∈t.val, x≠center t → G.Adj (center t) x) :
    ∃ C B, Layout G C S B ∧ C = P.attach.image center ∧ ∀ t : ↥P, B (center t)=t.val := by
  classical
  have inj : Function.Injective center := by
    intro t u e
    by_contra! ne
    have h1 := (hc t).1
    have h2 : center t∈u.val := e.symm ▸ (hc u).1
    exact disjoint_left.mp (p.disj _ t.property _ u.property (fun eq => ne (Subtype.ext eq))) h1 h2
  let C := P.attach.image center
  let B (c : V) : Finset V := if h : ∃ t : ↥P, center t=c then (Classical.choose h).val else ∅
  have by_t (t : ↥P) : B (center t)=t.val := by
    have ho : ∃ u : ↥P, center u=center t := ⟨t,rfl⟩
    have he := inj (Classical.choose_spec ho)
    simp only [B,dif_pos ho,he]
  refine ⟨C,B,⟨?_,?_,?_⟩,rfl,by_t⟩
  · intro c cc
    obtain ⟨t,_,rfl⟩ := mem_image.mp cc
    rw [by_t]
    exact ⟨(p.tile _ t.property).1,(hc t).1,(hc t).2⟩
  · intro x hx y hy ne
    obtain ⟨t,_,rfl⟩ := mem_image.mp hx
    obtain ⟨u,_,rfl⟩ := mem_image.mp hy
    change Disjoint (B (center t)) (B (center u))
    rw [by_t,by_t]
    exact p.disj _ t.property _ u.property (fun e => ne (congrArg center (Subtype.ext e)))
  · rw [← p.cover]
    ext x
    constructor
    · intro hx
      obtain ⟨c,cc,xc⟩ := mem_biUnion.mp hx
      obtain ⟨t,_,rfl⟩ := mem_image.mp cc
      rw [by_t] at xc
      exact mem_biUnion.mpr ⟨t.val,t.property,xc⟩
    · intro hx
      obtain ⟨t,ht,xt⟩ := mem_biUnion.mp hx
      let u : ↥P := ⟨t,ht⟩
      exact mem_biUnion.mpr ⟨center u,mem_image.mpr ⟨u,mem_attach _ _,rfl⟩,(by_t u).symm ▸ xt⟩

#print axioms layout_of_tiles


omit [Fintype V] in
/-- The orientation of a new partition can preserve every centre of
every surviving old tile. This upgrades centre-change lower bounds
to lower bounds on the number of old tiles that must be removed. -/
theorem keep_common_tiles {C S D : Finset V} {B : V→Finset V} {P : Finset (Finset V)}
    (old : Layout G C S B) (fresh : Assemble.LocalPart G P D) :
    ∃ C' B', Layout G C' D B' ∧
      (C\C') ⊆ C.filter (fun c => B c∉P) := by
  classical
  have inj {c d : V} (hc : c∈C) (hd : d∈C) (h : B c=B d) : c=d := by
    by_contra! ne
    have h1 := (old.shape c hc).2.1
    have h2 : c∈B d := h ▸ h1
    exact disjoint_left.mp (old.apart hc hd ne) h1 h2
  let k (t : ↥P) : V := if h : ∃ c∈C, B c=t.val then Classical.choose h
    else Classical.choose (fresh.tile _ t.property).2
  have hk (t : ↥P) : k t ∈ t.val ∧ ∀ x∈t.val, x≠k t → G.Adj (k t) x := by
    unfold k
    split
    · rename_i h
      obtain ⟨hm,ht⟩ := Classical.choose_spec h
      have ss := (old.shape _ hm).2
      have cent : Classical.choose h∈t.val :=
        (congrArg (fun A : Finset V => Classical.choose h ∈ A) ht).mp ss.1
      refine ⟨cent,?_⟩
      intro x hx ne
      exact ss.2 x ((congrArg (fun A : Finset V => x∈A) ht).mpr hx) ne
    · exact Classical.choose_spec (fresh.tile _ t.property).2
  obtain ⟨C',B',lp,hc',_⟩ := layout_of_tiles fresh k hk
  refine ⟨C',B',lp,?_⟩
  intro c cc
  have h := mem_sdiff.mp cc
  refine mem_filter.mpr ⟨h.1,?_⟩
  intro found
  let t : ↥P := ⟨B c,found⟩
  have tf : ∃ x∈C, B x=t.val := ⟨c,h.1,rfl⟩
  have eq : k t=c := by
    unfold k
    rw [dif_pos tf]
    have hv := Classical.choose_spec tf
    exact inj hv.1 h.1 hv.2
  have into : k t∈C' := hc'.symm ▸ mem_image.mpr ⟨t,mem_attach _ _,rfl⟩
  exact h.2 (eq ▸ into)

#print axioms keep_common_tiles

omit [Fintype V] in
private theorem block_no_other_center {C S : Finset V} {B : V→Finset V}
    (p : Layout G C S B) {x c : V} (hc : c∈C) (hx : x∈C) (xb : x∈B c) : x=c := by
  by_contra ne
  exact disjoint_left.mp (p.apart hx hc ne) (p.shape x hx).2.1 xb

omit [Fintype V] in
private theorem same_block {C C' S S' : Finset V} {B B' : V→Finset V}
    (p : Layout G C S B) (q : Layout G C' S' B') {c j : V}
    (hc : c∈C) (hc' : c∈C') (hj : j∈C') (ne : j≠c)
    (rigid : ∀ v, G.Adj c v → v∈B c ∨ v=j) : B' c=B c := by
  apply eq_of_subset_of_card_le
  · intro v hv
    by_cases h : v=c
    · exact h.symm ▸ (p.shape c hc).2.1
    · rcases rigid v ((q.shape c hc').2.2 v hv h) with h | h
      · exact h
      · have jv := block_no_other_center q hc' hj (h ▸ hv)
        exact (ne jv).elim
  · rw [(p.shape c hc).1,(q.shape c hc').1]

/-- If all but E exceptional old centres have a single potential third
neighbour, paired injectively to another old centre, then changing d old
centres leaves a retiling region of size at most 6d+3|E|+3. Three old
holes must be connected in this small region. No distance-preserving
hypothesis on the ambient graph or order is needed here. -/
theorem rigidity_region {C C' H E : Finset V} {B B' : V→Finset V} (mate : V→V)
    (old : Layout G C (univ\H) B) (fresh : Layout G C' univ B')
    (hex : H.card=3)
    (mat : ∀ c∈C\E, mate c∈C ∧ mate c≠c)
    (mi : Set.InjOn mate (↑(C\E) : Set V))
    (rigid : ∀ c∈C\E, ∀ v, G.Adj c v → v∈B c ∨ v=mate c)
    : ∃ W : Finset V, ∃ inc : H⊆W,
      W.card ≤ 6*(C\C').card+3*E.card+3 ∧
      (∀ a b : V, ∀ ha : a∈H, ∀ hb : b∈H,
        (G.induce (W : Set V)).Reachable ⟨a,inc ha⟩ ⟨b,inc hb⟩) := by
  classical
  let D := C\C'
  let M := (C\E).filter (fun c => mate c ∈ D)
  let U := D∪M∪(C∩E)
  let W := H ∪ U.biUnion B
  have sD : D ⊆ C := sdiff_subset
  have sM : M ⊆ C\E := filter_subset _ _
  have sU : U ⊆ C := union_subset (union_subset sD (sM.trans sdiff_subset)) inter_subset_left
  have mate_inj : Set.InjOn mate (↑M : Set V) := by
    intro x hx y hy eq
    exact mi (sM hx) (sM hy) eq
  have boundM : M.card≤D.card := by
    rw [← card_image_of_injOn mate_inj]
    apply card_le_card
    intro x hx
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hx
    exact (mem_filter.mp hc).2
  have boundU : U.card≤2*D.card+E.card := by
    have u₁ := card_union_le D M
    have u₂ := card_union_le (D∪M) (C∩E)
    have u₃ := card_le_card (inter_subset_right : C∩E ⊆ E)
    change U.card≤_ at u₂
    omega
  have boundW : W.card≤3*U.card+3 := by
    have dis : (U : Set V).PairwiseDisjoint B := fun x hx y hy ne => old.apart (sU hx) (sU hy) ne
    have hu : (U.biUnion B).card=U.card*3 := by
      rw [card_biUnion dis]
      calc
        _ = ∑ c ∈ U, 3 := sum_congr rfl (fun c hc => (old.shape c (sU hc)).1)
        _ = _ := by simp
    have h := card_union_le H (U.biUnion B)
    rw [hex,hu] at h
    change (H ∪ U.biUnion B).card ≤ _
    omega
  have fixed {c : V} (hc : c∈C) (nu : c∉U) : c∈C' ∧ B' c=B c := by
    have nd : c∉D := fun hd => nu (mem_union_left _ (mem_union_left _ hd))
    have ne : c∉E := fun he => nu (mem_union_right _ (mem_inter.mpr ⟨hc,he⟩))
    have hc' : c∈C' := by
      by_cases hh : c∈C'
      · exact hh
      · exact (nd (mem_sdiff.mpr ⟨hc,hh⟩)).elim
    have inE : c∈C\E := mem_sdiff.mpr ⟨hc,ne⟩
    have pf := mat c inE
    have hj : mate c∈C' := by
      by_cases hh : mate c∈C'
      · exact hh
      · have cd := mem_sdiff.mpr ⟨pf.1,hh⟩
        exact (nu (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨inE,cd⟩)))).elim
    exact ⟨hc',same_block old fresh hc hc' hj pf.2 (rigid c inE)⟩
  have hW : H ⊆ W := subset_union_left
  have Wold : Closed G (W\H) := by
    apply layout_local (C:=U) (B:=B)
    refine ⟨fun c hc => old.shape c (sU hc),fun c hc d hd e => old.apart (sU hc) (sU hd) e,?_⟩
    ext v
    constructor
    · intro hv
      obtain ⟨t,ht,tv⟩ := mem_biUnion.mp hv
      have out : v∈univ\H := old.covers ▸ mem_biUnion.mpr ⟨t,sU ht,tv⟩
      exact mem_sdiff.mpr ⟨mem_union_right _ hv,(mem_sdiff.mp out).2⟩
    · intro hv
      exact (mem_union.mp (mem_sdiff.mp hv).1).resolve_left (mem_sdiff.mp hv).2
  let J := C'\(C\U)
  have sJ : J ⊆ C' := sdiff_subset
  have Wnew : Closed G W := by
    apply layout_local (C:=J) (B:=B')
    refine ⟨fun v hv => fresh.shape v (sJ hv),fun v hv w hw e => fresh.apart (sJ hv) (sJ hw) e,?_⟩
    ext v
    constructor
    · intro hv
      obtain ⟨c,hc,vc⟩ := mem_biUnion.mp hv
      by_cases h : v∈H
      · exact mem_union_left _ h
      · have r : v∈univ\H := mem_sdiff.mpr ⟨mem_univ _,h⟩
        obtain ⟨t,ht,vt⟩ := mem_biUnion.mp (old.covers.symm ▸ r)
        by_cases ut : t∈U
        · exact mem_union_right _ (mem_biUnion.mpr ⟨t,ut,vt⟩)
        · have ft := fixed ht ut
          have vn : v∈B' t := ft.2.symm ▸ vt
          have dif : c≠t := by
            intro e
            exact (mem_sdiff.mp hc).2 (mem_sdiff.mpr ⟨e.symm ▸ ht,e.symm ▸ ut⟩)
          exact (disjoint_left.mp (fresh.apart (sJ hc) ft.1 dif) vc vn).elim
    · intro hv
      obtain ⟨c,hc,cv⟩ := mem_biUnion.mp (fresh.covers.symm ▸ mem_univ v)
      refine mem_biUnion.mpr ⟨c,mem_sdiff.mpr ⟨hc,?_⟩,cv⟩
      intro no
      obtain ⟨cc,nu⟩ := mem_sdiff.mp no
      have same := (fixed cc nu).2
      have vc : v∈B c := same ▸ cv
      rcases mem_union.mp hv with h | h
      · have vp : v∈univ\H := old.covers ▸ mem_biUnion.mpr ⟨c,cc,vc⟩
        exact (mem_sdiff.mp vp).2 h
      · obtain ⟨d,hd,dv⟩ := mem_biUnion.mp h
        exact disjoint_left.mp (old.apart cc (sU hd) (fun e => nu (e.symm ▸ hd))) vc dv
  refine ⟨W,hW,?_,?_⟩
  · change W.card≤6*D.card+3*E.card+3
    omega
  · intro a b ha hb
    exact three_holes_join hW hex Wold Wnew ha hb

theorem rigidity_budget {C C' H E : Finset V} {B B' : V→Finset V} (mate : V→V)
    (old : Layout G C (univ\H) B) (fresh : Layout G C' univ B')
    (hex : H.card=3)
    (mat : ∀ c∈C\E, mate c∈C ∧ mate c≠c)
    (mi : Set.InjOn mate (↑(C\E) : Set V))
    (rigid : ∀ c∈C\E, ∀ v, G.Adj c v → v∈B c ∨ v=mate c)
    {a b : V} (ha : a∈H) (hb : b∈H) :
    ∃ W : Finset V, ∃ h : a∈W, ∃ j : b∈W,
      (G.induce (W : Set V)).Reachable ⟨a,h⟩ ⟨b,j⟩ ∧
        W.card ≤ 6*(C\C').card+3*E.card+3 := by
  obtain ⟨W,inc,cap,reach⟩ := rigidity_region mate old fresh hex mat mi rigid
  exact ⟨W,inc ha,inc hb,reach a b ha hb,cap⟩

omit [Fintype V] in
private theorem walk_rise {T : Type*} {K : SimpleGraph T} (f : T→Nat)
    (adj : ∀ x y, K.Adj x y → f y≤f x+1)
    {x y : T} (p : K.Walk x y) : f y ≤ f x+p.length := by
  induction p with
  | nil => simp
  | @cons u v w uv p ih =>
    have h := adj u v uv
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- A Lipschitz integer potential supplies an explicit lower bound on
the number of original centres which every new factor must abandon. -/
theorem rigidity_potential {C C' H E : Finset V} {B B' : V→Finset V} (mate : V→V)
    (old : Layout G C (univ\H) B) (fresh : Layout G C' univ B')
    (hex : H.card=3)
    (mat : ∀ c∈C\E, mate c∈C ∧ mate c≠c)
    (mi : Set.InjOn mate (↑(C\E) : Set V))
    (rigid : ∀ c∈C\E, ∀ v, G.Adj c v → v∈B c ∨ v=mate c)
    {a b : V} (ha : a∈H) (hb : b∈H)
    (rank : V→ℕ) (near : ∀ x y, G.Adj x y → rank y≤rank x+1) :
    rank b ≤ rank a + (6*(C\C').card+3*E.card+2) := by
  obtain ⟨W,aW,bW,reach,cap⟩ := rigidity_budget mate old fresh hex mat mi rigid ha hb
  obtain ⟨p,hp⟩ := reach.exists_isPath
  have rise := walk_rise (fun x : (W : Set V) => rank x.val) (fun x y e => near x.val y.val e) p
  have size := hp.length_lt
  change p.length < Fintype.card (↥W) at size
  rw [Fintype.card_coe] at size
  change rank b≤rank a+p.length at rise
  omega

#print axioms three_holes_join
#print axioms rigidity_budget
#print axioms rigidity_potential

omit [Fintype V] in
theorem remove_subpacking {P K : Finset (Finset V)} {S : Finset V}
    (p : Assemble.LocalPart G P S) (sub : K⊆P) :
    Assemble.LocalPart G (P\K) (S\K.biUnion id) := by
  refine ⟨fun t h => p.tile t (mem_sdiff.mp h).1,
    fun s ss t tt ne => p.disj s (mem_sdiff.mp ss).1 t (mem_sdiff.mp tt).1 ne,?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨t,tP,tv⟩ := mem_biUnion.mp hv
    obtain ⟨t₀,t₁⟩ := mem_sdiff.mp tP
    refine mem_sdiff.mpr ⟨p.tile_sub G t₀ tv,?_⟩
    intro hvK
    obtain ⟨u,uk,uv⟩ := mem_biUnion.mp hvK
    have tu : t≠u := fun e => t₁ (e.symm ▸ uk)
    exact disjoint_left.mp (p.disj t t₀ u (sub uk) tu) tv uv
  · intro hv
    obtain ⟨vS,vK⟩ := mem_sdiff.mp hv
    obtain ⟨t,tp,tv⟩ := mem_biUnion.mp (p.cover.symm ▸ vS)
    exact mem_biUnion.mpr ⟨t,mem_sdiff.mpr ⟨tp,fun tk => vK (mem_biUnion.mpr ⟨t,tk,tv⟩)⟩,tv⟩

/-- Cancelling tiles shared by a near-packing and a full packing leaves
all three old holes connected in the difference region. Its size is
bounded sharply by three times the number of removed tiles plus three. -/
theorem changed_tile_region {P F : Finset (Finset V)} {H : Finset V}
    (old : Assemble.LocalPart G P (univ\H)) (fresh : Assemble.LocalPart G F univ)
    (size : H.card=3) :
    ∃ W : Finset V, ∃ inc : H⊆W,
      W.card = 3*(P\F).card+3 ∧
      (∀ a b : V, ∀ ha : a∈H, ∀ hb : b∈H,
        (G.induce (W : Set V)).Reachable ⟨a,inc ha⟩ ⟨b,inc hb⟩) := by
  let K := P∩F
  let X := K.biUnion id
  let W := univ\X
  have p := remove_subpacking old (show K⊆P from inter_subset_left)
  have f := remove_subpacking fresh (show K⊆F from inter_subset_right)
  have eq : (univ\H)\K.biUnion id = W\H := by
    ext x
    simp only [W,X,mem_sdiff,mem_univ,true_and]
    exact and_comm
  rw [eq] at p
  have ep : P\K = P\F := by
    ext x
    simp only [K,mem_sdiff,mem_inter]
    tauto
  rw [ep] at p
  have subH : H⊆W := by
    intro x hx
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    intro hm
    obtain ⟨t,ht,tx⟩ := mem_biUnion.mp hm
    exact (mem_sdiff.mp (old.tile_sub G (mem_inter.mp ht).1 tx)).2 hx
  have cap : (W\H).card=3*(P\F).card := by
    have pair : ((P\F : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id :=
      fun u uh v vh n => p.disj u uh v vh n
    rw [← p.cover,card_biUnion pair]
    calc
      _ = ∑ _t ∈ P\F, 3 := sum_congr rfl (fun t ht => (p.tile t ht).1)
      _ = _ := by simp [mul_comm]
  have sum := card_sdiff_add_card_eq_card subH
  refine ⟨W,subH,by omega,?_⟩
  intro a b ha hb
  exact three_holes_join subH size ⟨_,p⟩ ⟨_,f⟩ ha hb

#print axioms changed_tile_region
end KelmansCactus.CenterRigidity
