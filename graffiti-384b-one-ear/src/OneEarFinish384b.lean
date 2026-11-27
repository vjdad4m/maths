import CrossFour34_384b
import OneEarRoute384b
import OneEarCut384b

universe u
namespace Graffiti384b.OneEar
open Finset SimpleGraph LowSample
open private Repair.triangles_le_choose from Repair384b
open private Prune.links Prune.outside_zero from Prune384b
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private LowSample.two_degree from LowSample384b
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem deg2 {v x y : V} (xy : x≠y) (vx : G.Adj v x) (vy : G.Adj v y) : 2≤G.degree v := by
  have sub := insert_subset ((G.mem_neighborFinset _ _).mpr vx)
    (singleton_subset_iff.mpr ((G.mem_neighborFinset _ _).mpr vy))
  have h := card_le_card sub
  rwa [card_pair xy,card_neighborFinset_eq_degree] at h

private theorem positive (normal : TrianglePrune.Normal G) (v : V) (degree : 2≤G.degree v) : 0 < trianglesAt G v := by
  apply Nat.pos_of_ne_zero
  intro zero
  have small : (G.neighborFinset v).card≤1 := card_le_one.mpr (fun a ha b hb =>
    normal.2.1 v zero a b ((G.mem_neighborFinset _ _).mp ha) ((G.mem_neighborFinset _ _).mp hb))
  rw [card_neighborFinset_eq_degree] at small
  omega

private theorem route_of_reach {e a b : V} (ear : G.neighborFinset e={a,b}) (eb : G.Adj e b) (ab : G.Adj a b)
    (reach : (opened G {e,a,b}).Reachable a b) : ∃ n, 2≤n ∧ Nonempty (Route G e a b n) := by
  classical
  let K : Finset V := {e,a,b}
  let H := opened G K
  obtain ⟨p,hp⟩ := reach.exists_isPath
  let f := p.getVert
  have one : 1≤p.length := by
    by_contra! short
    have zero : p.length=0 := by omega
    exact ab.ne (p.getVert_zero.symm.trans (zero ▸ p.getVert_length))
  have two : 2≤p.length := by
    by_contra! short
    have l : p.length=1 := by omega
    have edge := p.adj_getVert_succ (i:=0) (by omega)
    rw [p.getVert_zero,show 0+1=p.length by omega,p.getVert_length] at edge
    exact edge.2 ⟨by simp [K],by simp [K]⟩
  have st (i : ℕ) (hi : i < p.length) : H.Adj (f i) (f (i+1)) := p.adj_getVert_succ hi
  have iso {v : V} (edge : H.Adj e v) : False := by
    have vm := (G.mem_neighborFinset _ _).mpr edge.1
    rw [ear] at vm
    exact edge.2 ⟨by simp [K],mem_insert_of_mem vm⟩
  let r : Route G e a b p.length := {
    atIdx := f
    start := p.getVert_zero
    finish := p.getVert_length
    step := fun i hi => (st i hi).1
    unique := fun i hi j hj eq => hp.getVert_injOn hi hj eq
    avoid := by
      intro i hi eq
      by_cases lt : i < p.length
      · exact iso (eq ▸ st i lt)
      · have endv : f i=b := (show i=p.length by omega) ▸ p.getVert_length
        exact eb.ne (eq.symm.trans endv)
  }
  exact ⟨p.length,two,⟨r⟩⟩

/-- It is enough for positive-positive edges to be supported and for all but one
nonleaf to have positive triangle count. -/
theorem supported (support : ∀ u v,G.Adj u v → 0<trianglesAt G u → 0<trianglesAt G v →
      ∃ z,G.Adj u z ∧ G.Adj v z)
    (zeros : ∀ u v,2≤G.degree u → 2≤G.degree v → trianglesAt G u=0 → trianglesAt G v=0 → u=v)
    {e : V} (only : twos G={e}) (pe : 0<trianglesAt G e) (q : (types G).card≤(nonleaves G).card) :
    gamma G≤bound G := by
  classical
  have et : e∈twos G := only ▸ mem_singleton_self _
  obtain ⟨a,b,ear,ea,eb,ab⟩ := SharedExact34.ear_pair G (LowSample.two_degree G et) pe
  by_cases reach : (opened G {e,a,b}).Reachable a b
  · obtain ⟨n,two,⟨r⟩⟩ := route_of_reach G ear eb ab reach
    by_cases ev : n%2=0
    · exact r.close only q ea eb ab.ne ev
    have interior {a b : V} (p : Route G e a b n) : 2≤G.degree (p.atIdx 1) :=
      deg2 G (fun eq => by have := p.unique 0 (by omega) 2 (by omega) eq; omega)
        (p.step 0 (by omega)).symm (p.step 1 (by omega))
    have finishEnd {a b : V} (p : Route G e a b n) (ea : G.Adj e a) (eb : G.Adj e b) (ab : G.Adj a b)
        (ear : G.neighborFinset e={a,b}) (pos : 0<trianglesAt G (p.atIdx 1)) : gamma G≤bound G := by
      have near := p.step 0 (by omega)
      rw [p.start] at near
      have pa := (TrianglePrune.triangle_iff G a).mpr ⟨e,b,ea.symm,ab,eb⟩
      obtain ⟨z,az,uz⟩ := support a _ near pa pos
      have ze : z≠e := by
        intro eq
        have m := (G.mem_neighborFinset _ _).mpr (show G.Adj e (p.atIdx 1) from eq ▸ uz.symm)
        rw [ear,mem_insert,mem_singleton] at m
        rcases m with ua|ub
        · exact near.ne ua.symm
        · have idx := p.unique 1 (by omega) n le_rfl (ub.trans p.finish.symm)
          omega
      exact change_parity p two only q ea eb ab.ne ze az uz
    by_cases pos : 0<trianglesAt G (r.atIdx 1)
    · exact finishEnd r ea eb ab ear pos
    have other : 0<trianglesAt G (r.reverse.atIdx 1) := by
      apply Nat.pos_of_ne_zero
      intro zero
      have same := zeros _ _ (interior r) (interior r.reverse) (by omega) zero
      have := r.unique 1 (by omega) (n-1) (by omega) same
      omega
    exact finishEnd r.reverse eb ea ab.symm (ear.trans (pair_comm ..)) other
  · exact separated G only q ear ab reach

/-- A normalized graph with just one degree-two vertex has the catalogue bound
whenever its diversity does not exceed its number of nonleaves. -/
theorem exact (normal : TrianglePrune.Normal G) {e : V} (only : twos G={e})
    (q : (types G).card≤(nonleaves G).card) : gamma G≤bound G := by
  have et : e∈twos G := only ▸ mem_singleton_self _
  exact supported G normal.2.2 (fun u v _ _ => normal.1 u v) only
    (positive G normal e (LowSample.two_degree G et).ge) q

theorem least_order (res : Minimal.Residual G) : Fintype.card V≤33 := by
  have cap := Frontier34.minimum_order G res
  by_contra! large
  have n : Fintype.card V=34 := by omega
  obtain ⟨_,e,one⟩ := CrossFour34.single_ear G res n
  obtain ⟨q,t,_⟩ := Frontier34.boundary G res n
  exact (not_lt_of_ge (exact G res.2.2.2.1 one (by omega))) res.2.2.1

theorem bounded_failure (hc : G.Connected) (hn : 2 < Fintype.card V) (fail : bound G < gamma G) :
    ∃ m≤33, Minimal.FailingOrder.{u} m := by
  obtain ⟨W,fw,ew,J,d,res⟩ := Minimal.residual_witness G hc hn fail
  letI := fw
  letI := ew
  letI := d
  exact ⟨Fintype.card W,least_order J res,W,fw,ew,J,d,rfl,res.1.1,res.2.1,res.2.2.1⟩


/-- Retain triangles and every edge incident to a zero-score vertex. -/
private def trim : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ((∃ z,G.Adj u z ∧ G.Adj v z) ∨ trianglesAt G u=0 ∨ trianglesAt G v=0)
  symm := by
    rintro u v ⟨uv,⟨z,uz,vz⟩|z|z⟩
    · exact ⟨uv.symm,Or.inl ⟨z,vz,uz⟩⟩
    · exact ⟨uv.symm,Or.inr (Or.inr z)⟩
    · exact ⟨uv.symm,Or.inr (Or.inl z)⟩
  loopless := fun _ h => h.1.ne rfl

private instance : DecidableRel (trim G).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

private theorem trim_scores (v : V) : trianglesAt (trim G) v = trianglesAt G v := by
  let J := trim G
  change (Prune.links J v).card=(Prune.links G v).card
  congr 1
  ext p
  simp only [Prune.links,mem_filter,mem_powersetCard]
  constructor
  · rintro ⟨⟨sub,sz⟩,edges⟩
    exact ⟨⟨fun w wm => (G.mem_neighborFinset _ _).mpr ((J.mem_neighborFinset _ _).mp (sub wm)).1,sz⟩,
      fun u um w wm ne => (edges u um w wm ne).1⟩
  · rintro ⟨⟨sub,sz⟩,edges⟩
    have adj (u : V) (um : u∈p) := (G.mem_neighborFinset _ _).mp (sub um)
    refine ⟨⟨?_,sz⟩,?_⟩
    · intro u um
      obtain ⟨w,wm,ne⟩ := exists_ne_of_one_lt_card (by omega : 1<p.card) u
      exact (J.mem_neighborFinset _ _).mpr ⟨adj u um,Or.inl ⟨w,adj w wm,edges u um w wm ne.symm⟩⟩
    · intro u um w wm ne
      exact ⟨edges u um w wm ne,Or.inl ⟨v,(adj u um).symm,(adj w wm).symm⟩⟩

private theorem two_zeros {u v l : V} (n : Fintype.card V=34) (t : (types G).card=33)
    (lu : l≠u) (lv : l≠v) (lz : trianglesAt G l=0) (uz : trianglesAt G u=0) (vz : trianglesAt G v=0) : u=v := by
  classical
  by_cases uv : u=v
  · exact uv
  let K : Finset V := {l,u,v}
  have sz : K.card=3 := by simp [K,lu,lv,uv]
  have sub : types G⊆insert 0 (Kᶜ.image (trianglesAt G)) := by
    intro j jm
    obtain ⟨x,_,rfl⟩ := mem_image.mp jm
    by_cases xm : x∈K
    · simp only [K,mem_insert,mem_singleton] at xm
      rcases xm with rfl|rfl|rfl <;> simp [*]
    · exact mem_insert_of_mem (mem_image.mpr ⟨x,mem_compl.mpr xm,rfl⟩)
  have h := (card_le_card sub).trans (card_insert_le ..)
  have small := card_image_le (f:=trianglesAt G) (s:=Kᶜ)
  rw [card_compl,sz,n] at small
  omega

private theorem spanning_repair (q : (types G).card≤(nonleaves G).card)
    (ears : ∀ v,G.degree v=2 → 0<trianglesAt G v)
    (zero : ∀ u v,2≤G.degree u → 2≤G.degree v → trianglesAt G u=0 → trianglesAt G v=0 → u=v)
    (pair : ∀ u v,u≠v → (trim G).degree u=2 → (trim G).degree v=2 →
      0<trianglesAt (trim G) u → 0<trianglesAt (trim G) v → gamma (trim G)≤bound (trim G)) :
    gamma G≤bound G := by
  classical
  let J := trim G
  have sc := trim_scores G
  have ty : types J = types G := congrArg (fun f : V → ℕ => univ.image f) (funext sc)
  have unchanged {v : V} (zero : trianglesAt G v=0) : J.degree v=G.degree v := by
    have eq : J.neighborFinset v=G.neighborFinset v := by ext u; simp [J,trim,zero]
    simpa only [card_neighborFinset_eq_degree] using congrArg Finset.card eq
  have dg (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) (pos : 0<trianglesAt H v) : 2≤H.degree v := by
    obtain ⟨a,b,va,vb,ab⟩ := (TrianglePrune.triangle_iff H v).mp pos
    exact deg2 H ab.ne va vb
  have non : nonleaves J=nonleaves G := by
    ext v
    by_cases z : trianglesAt G v=0
    · simp [nonleaves,unchanged z]
    · have p := Nat.pos_of_ne_zero z
      have pj : 0<trianglesAt J v := by rwa [sc]
      simp [nonleaves,dg G v p,dg J v pj]
  have jq : (types J).card≤(nonleaves J).card := by rw [ty,non]; exact q
  have jpos {v : V} (vm : v∈twos J) : 0<trianglesAt J v := by
    rw [sc]
    apply Nat.pos_of_ne_zero
    intro z
    have both := unchanged z
    have pos := ears v (both ▸ LowSample.two_degree J vm)
    omega
  have sup (u v : V) (edge : J.Adj u v) (pu : 0<trianglesAt J u) (pv : 0<trianglesAt J v) :
      ∃ z,J.Adj u z ∧ J.Adj v z := by
    rw [sc] at pu pv
    obtain ⟨z,uz,vz⟩ := edge.2.resolve_right (by omega)
    exact ⟨z,⟨uz,Or.inl ⟨v,edge.1,vz.symm⟩⟩,⟨vz,Or.inl ⟨u,edge.1.symm,uz.symm⟩⟩⟩
  have zeros (u v : V) (du : 2≤J.degree u) (dv : 2≤J.degree v)
      (uz : trianglesAt J u=0) (vz : trianglesAt J v=0) : u=v := by
    rw [sc] at uz vz
    exact zero u v (unchanged uz ▸ du) (unchanged vz ▸ dv) uz vz
  have win : gamma J≤bound J := by
    by_cases many : 1<(twos J).card
    · obtain ⟨u,um⟩ := card_pos.mp (by omega : 0<(twos J).card)
      obtain ⟨v,vm,vu⟩ := exists_ne_of_one_lt_card many u
      exact pair u v vu.symm (LowSample.two_degree J um) (LowSample.two_degree J vm)
        (jpos um) (jpos vm)
    by_cases one : (twos J).card=1
    · obtain ⟨e,single⟩ := card_eq_one.mp one
      exact supported J sup zeros single (jpos (single ▸ mem_singleton_self _)) (by omega)
    have inc : high J⊆nonleaves J := fun v vm => mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp vm).2; omega⟩
    have sum : (twos J).card+(high J).card=(nonleaves J).card := card_sdiff_add_card_eq_card inc
    exact exact_of_high J (by omega)
  have existsD : {k : ℕ | ∃ d, TwoDominates J d ∧ d.card=k}.Nonempty :=
    ⟨univ.card,univ,(fun v no => (no (mem_univ v)).elim),rfl⟩
  obtain ⟨D,good,size⟩ := Nat.sInf_mem existsD
  have inG : TwoDominates G D := fun v out => (good v out).trans (card_le_card
    (show D.filter (J.Adj v)⊆D.filter (G.Adj v) from fun _ m => mem_filter.mpr ⟨(mem_filter.mp m).1,(mem_filter.mp m).2.1⟩))
  have mono : gamma G≤gamma J := Nat.sInf_le ⟨D,inG,size⟩
  have eqb : bound J=bound G := by simp only [bound,ty]
  exact (mono.trans win).trans_eq eqb


/-- An unnormalized order-34 graph of diversity 33 with at least 33 nonleaves
is covered if all its degree-two vertices lie on triangles. -/
theorem direct34 (n : Fintype.card V=34) (t : (types G).card=33)
    (q : 33≤(nonleaves G).card) (ears : ∀ v,G.degree v=2 → 0<trianglesAt G v) :
    gamma G≤bound G := by
  classical
  by_cases full : 34≤(nonleaves G).card
  · exact Finish33.exact33 G t full
  have q33 : (nonleaves G).card=33 := by omega
  apply spanning_repair G (by omega) ears
  · intro u v du dv uz vz
    have left : (nonleaves G)ᶜ.Nonempty := card_pos.mp (by rw [card_compl,q33,n]; decide)
    obtain ⟨l,lm⟩ := left
    have out := mem_compl.mp lm
    have lu : l≠u := fun eq => out (eq ▸ mem_filter.mpr ⟨mem_univ _,du⟩)
    have lv : l≠v := fun eq => out (eq ▸ mem_filter.mpr ⟨mem_univ _,dv⟩)
    exact two_zeros G n t lu lv (Prune.outside_zero G out) uz vz
  · have ty : types (trim G)=types G := congrArg (fun f : V → ℕ => univ.image f) (funext (trim_scores G))
    exact fun _ _ ne => CrossFour34.two_ears (trim G) n ((congrArg card ty).trans t) ne

/-- At arbitrary order, uniqueness of score one dispenses with the two-ear branch. -/
theorem unique_one (q : (types G).card≤(nonleaves G).card)
    (ears : ∀ v,G.degree v=2 → 0<trianglesAt G v)
    (zero : ∀ u v,2≤G.degree u → 2≤G.degree v → trianglesAt G u=0 → trianglesAt G v=0 → u=v)
    (one : ∀ u v,trianglesAt G u=1 → trianglesAt G v=1 → u=v) : gamma G≤bound G := by
  apply spanning_repair G q ears zero
  intro u v ne du dv pu pv
  have score (x : V) (dx : (trim G).degree x=2) (px : 0<trianglesAt (trim G) x) : trianglesAt G x=1 := by
    have cap := Repair.triangles_le_choose (trim G) x
    rw [dx,Nat.choose_self] at cap
    rw [← trim_scores G]; omega
  exact (ne (one u v (score u du pu) (score v dv pv))).elim

/-- An injective failure must have a zero-score vertex of degree at most two. -/
theorem low_zero (inj : Function.Injective (trianglesAt G)) (fail : bound G<gamma G) :
    ∃ v,trianglesAt G v=0 ∧ G.degree v≤2 := by
  classical
  by_contra! highZero
  have non : nonleaves G=univ := eq_univ_of_forall (fun v => by
    by_contra out
    have h := highZero v (Prune.outside_zero G out)
    exact out (mem_filter.mpr ⟨mem_univ _,by omega⟩))
  apply (not_lt_of_ge (unique_one G (by rw [non]; exact card_image_le) ?_
    (fun u v _ _ a b => inj (a.trans b.symm)) (fun u v a b => inj (a.trans b.symm)))) fail
  intro v dv
  apply Nat.pos_of_ne_zero
  intro z
  have := highZero v z
  omega

/-- Preserve the entire set of scores when reducing a connected failure to
at most 33 vertices of the original graph. -/
theorem induced_bound (hc : G.Connected) (hn : 2<Fintype.card V) (bad : bound G<gamma G) :
    ∃ s : Finset V, 2<s.card ∧ s.card≤33 ∧ (G.induce (s : Set V)).Connected ∧
      types (G.induce (s : Set V))=types G ∧ bound (G.induce (s : Set V))<gamma (G.induce (s : Set V)) := by
  classical
  have small := Nat.lt_of_not_ge (fun b => (not_lt_of_ge (Diversity35.exact_of_at_least_34_types G hc hn b)) bad)
  by_cases t : (types G).card=33
  case neg => exact Below33.induced_bound G (by omega) hc hn bad
  let C := nonleaves G
  have cap : C.card≤33 := Below35.nonleaf_cap G (by omega) hc hn bad
  obtain ⟨s,keep,size,lo,con,same,fail⟩ := Prune.prune_failure G hc hn bad
  by_cases ls : s.card≤33
  · exact ⟨s,lo,ls,con,same,fail⟩
  change s.card≤C.card+1 at size
  have q : C.card=33 := by omega
  have sz : s.card=34 := by omega
  by_cases cz : ∃ v∈C,trianglesAt G v=0
  · obtain ⟨w,wm,wz⟩ := cz
    let J := G.induce (C : Set V)
    have sc := Prune.counts_preserved G C (Subset.rfl)
    have eq : types J=types G := by
      ext j
      constructor
      · intro m
        obtain ⟨v,_,rfl⟩ := mem_image.mp m
        exact mem_image.mpr ⟨v.val,mem_univ _,(sc v).symm⟩
      · intro m
        obtain ⟨v,_,rfl⟩ := mem_image.mp m
        by_cases vm : v∈C
        · exact mem_image.mpr ⟨⟨v,vm⟩,mem_univ _,sc ⟨v,vm⟩⟩
        · exact mem_image.mpr ⟨⟨w,wm⟩,mem_univ _,(sc ⟨w,wm⟩).trans (wz.trans (Prune.outside_zero G vm).symm)⟩
    exact ⟨C,by omega,cap,Prune.connected_core G hc Subset.rfl ⟨w,wm⟩,eq,
      Nat.lt_of_not_ge (fun sol => (not_lt_of_ge (Prune.lift_solution G C (congrArg card eq) sol)) bad)⟩
  let H := G.induce (s : Set V)
  have sc := Prune.counts_preserved G s keep
  have corepos (v : s) (vm : v.val∈C) : 0<trianglesAt H v :=
    Nat.pos_of_ne_zero (fun z => cz ⟨_,vm,(sc v).symm.trans z⟩)
  have low {v : s} (zero : trianglesAt H v=0) : v.val∉C := fun vm => (Nat.ne_of_gt (corepos v vm)) zero
  have diff : (s\C).card≤1 := by rw [card_sdiff (show C⊆s from keep),sz,q]
  have non : 33≤(nonleaves H).card := by
    have single : (nonleaves H)ᶜ.card≤1 := by
      apply card_le_one.mpr
      intro u um v vm
      apply Subtype.ext
      exact card_le_one.mp diff u.val (mem_sdiff.mpr ⟨u.property,low (Prune.outside_zero H (mem_compl.mp um))⟩)
        v.val (mem_sdiff.mpr ⟨v.property,low (Prune.outside_zero H (mem_compl.mp vm))⟩)
    rw [card_compl] at single
    change Fintype.card s - (nonleaves H).card≤1 at single
    rw [Fintype.card_coe,sz] at single
    omega
  have ep (v : s) (dv : H.degree v=2) : 0<trianglesAt H v := by
    apply corepos
    have two : 1<(H.neighborFinset v).card := by rw [card_neighborFinset_eq_degree,dv]; decide
    obtain ⟨a,am,b,bm,ne⟩ := one_lt_card.mp two
    apply mem_filter.mpr
    refine ⟨mem_univ _,deg2 G (fun e => ne (Subtype.ext e)) ?_ ?_⟩
    · exact (H.mem_neighborFinset _ _).mp am
    · exact (H.mem_neighborFinset _ _).mp bm
  exact False.elim ((not_lt_of_ge (direct34 H ((Fintype.card_coe s).trans sz) ((congrArg card same).trans t) non ep)) fail)


theorem at_most_seventeen (n : Fintype.card V=34) (t : (types G).card=33)
    (q : 33≤(nonleaves G).card) (ears : ∀ v,G.degree v=2 → 0<trianglesAt G v) :
    gamma G≤17 := by
  simpa only [bound,n,t] using direct34 G n t q ears

/-- At the top remaining diversity an induced witness has distinct triangle
counts and contains a five-clique. -/
theorem diversity33_failure (hc : G.Connected) (hn : 2<Fintype.card V) (bad : bound G<gamma G)
    (t : (types G).card=33) :
    ∃ s : Finset V, s.card=33 ∧ (G.induce (s : Set V)).Connected ∧ types (G.induce (s : Set V))=types G ∧
      Function.Injective (trianglesAt (G.induce (s : Set V))) ∧ ¬(G.induce (s : Set V)).CliqueFree 5 ∧
      (∃ v, trianglesAt (G.induce (s : Set V)) v=0 ∧ (G.induce (s : Set V)).degree v≤2) ∧
      bound (G.induce (s : Set V))<gamma (G.induce (s : Set V)) := by
  obtain ⟨s,lo,cap,conn,same,fail⟩ := induced_bound G hc hn bad
  let J := G.induce (s : Set V)
  have size : (types J).card=33 := (congrArg card same).trans t
  have num : (types J).card≤s.card := by simpa [types] using (card_image_le (s := (univ : Finset s)) (f := trianglesAt J))
  have order : s.card=33 := by omega
  have inj := card_image_iff.mp (show ((univ : Finset s).image (trianglesAt J)).card=univ.card by
    change (types J).card = _; rw [card_univ]; exact size.trans (order.symm.trans (Fintype.card_coe s).symm))
  have five : ¬J.CliqueFree 5 := fun free => (not_lt_of_ge (CliqueFrontier34.exact_of_five_clique_free J conn
    (by change 2<Fintype.card s; rw [Fintype.card_coe]; exact lo) size.ge free)) fail
  have distinct : Function.Injective (trianglesAt J) := fun _ _ eq => inj (mem_univ _) (mem_univ _) eq
  exact ⟨s,order,conn,same,distinct,five,low_zero J distinct fail,fail⟩

end Graffiti384b.OneEar
#print axioms Graffiti384b.OneEar.supported
#print axioms Graffiti384b.OneEar.exact
#print axioms Graffiti384b.OneEar.least_order
#print axioms Graffiti384b.OneEar.bounded_failure
#print axioms Graffiti384b.OneEar.direct34
#print axioms Graffiti384b.OneEar.induced_bound
#print axioms Graffiti384b.OneEar.at_most_seventeen
#print axioms Graffiti384b.OneEar.diversity33_failure
#print axioms Graffiti384b.OneEar.unique_one
#print axioms Graffiti384b.OneEar.low_zero
