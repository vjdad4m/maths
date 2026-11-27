import SharpThreeBase189
import DistanceOnly189

namespace Graffiti189LongestPath.SharpThree.Reach
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.DistanceOnly
open Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
theorem no_endpoints {x a b : V} {p : G.Walk a b}
    (hp : IsLongest p) (hx : x ∉ p.support) :
    ¬G.Adj x a ∧ ¬G.Adj x b := by
  constructor
  · intro h
    have hle := hp.2 x b (.cons h p) (hp.1.cons hx)
    simp at hle
  · intro h
    have hq : (Walk.cons h p.reverse).reverse.IsPath :=
      (hp.1.reverse.cons (by simpa using hx)).reverse
    have hle := hp.2 a x _ hq
    simp at hle

theorem dist_two {a b c : V} (hconn : G.Connected)
    (hac : a ≠ c) (hna : ¬G.Adj a c) (hab : G.Adj a b) (hbc : G.Adj b c) :
    G.dist a c = 2 := by
  have hu := hconn.one_lt_dist_of_ne_of_not_adj hac hna
  have hl := G.dist_le (Walk.cons hab (Walk.cons hbc .nil))
  simp at hl
  omega





variable [Fintype V]
theorem mem_distanceTwo {x y : V} :
    y ∈ DistanceTwo G x ↔ G.dist x y = 2 := by
  classical
  simp [DistanceTwo]





variable [DecidableEq V] [DecidableRel G.Adj]
omit [Fintype V] [DecidableEq V] in
theorem pin_data {a b : V} {p : G.Walk a b} {x : V} {i : ℕ}
    (hi : i ∈ Pins p x) : i < p.length ∧ G.Adj x (p.getVert i) :=
  ⟨Finset.mem_range.mp (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩

omit [Fintype V] [DecidableEq V] in
theorem pin_of_neighbor_mem {a b x y : V} {p : G.Walk a b}
    (hp : IsLongest p) (hx : x ∉ p.support) (hy : y ∈ p.support) (e : G.Adj x y) :
    ∃ i ∈ Pins p x, p.getVert i = y := by
  obtain ⟨i,he,hile⟩ := mem_support_iff_exists_getVert.mp hy
  have hi : i < p.length := by
    by_contra! h
    have ee : i = p.length := by omega
    rw [ee,getVert_length] at he
    exact (no_endpoints hp hx).2 (he.symm ▸ e)
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,he.symm ▸ e⟩,he⟩


private lemma mem_omittedStar {a b x z : V} {p : G.Walk a b} :
    z ∈ OmittedStar p x ↔ z ∉ p.support ∧ (z = x ∨ G.Adj x z) := by simp [OmittedStar]

private lemma mem_external {A : Finset V} {z : V} :
    z ∈ External G A ↔ z ∉ A ∧ ∃ w ∈ A, G.Adj w z := by simp [External]

omit [Fintype V] [DecidableEq V] in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private lemma short_walk_cases {x y : V} (q : G.Walk x y) (len : q.length ≤ 3) :
    x=y ∨ G.Adj x y ∨ (∃ u, G.Adj x u ∧ G.Adj u y) ∨
      (∃ u v, G.Adj x u ∧ G.Adj u v ∧ G.Adj v y) := by
  match q with
  | .nil => exact Or.inl rfl
  | .cons e .nil => exact Or.inr (Or.inl e)
  | .cons (v:=u) e (.cons f .nil) => exact Or.inr (Or.inr (Or.inl ⟨u,e,f⟩))
  | .cons (v:=u) e (.cons (v:=v) f (.cons g .nil)) =>
    exact Or.inr (Or.inr (Or.inr ⟨u,v,e,f,g⟩))
  | .cons _ (.cons _ (.cons _ (.cons _ q))) => simp only [length_cons] at len; omega



variable {a b : V} {p : G.Walk a b}

/-- All vertices on the path with at least one omitted neighbor. -/
def PathPins {a b : V} (p : G.Walk a b) : Finset V :=
  p.support.toFinset.filter fun s => ∃ x ∉ p.support, G.Adj x s

theorem mem_pathPins {s : V} :
    s ∈ PathPins p ↔ s ∈ p.support ∧ ∃ x ∉ p.support, G.Adj x s := by
  simp [PathPins]

private def AroundPins {a b : V} (p : G.Walk a b) : Finset ℕ :=
  (range p.length).filter fun j => p.getVert j ∈ PathPins p

private lemma around_data {j : ℕ} (hj : j ∈ AroundPins p) :
    j < p.length ∧ p.getVert j ∈ PathPins p :=
  ⟨mem_range.mp (mem_filter.mp hj).1,(mem_filter.mp hj).2⟩

private lemma card_around (hp : IsLongest p) : (AroundPins p).card = (PathPins p).card := by
  have eq : (AroundPins p).image p.getVert = PathPins p := by
    ext z
    constructor
    · intro hz
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
      exact (around_data hi).2
    · intro hz
      obtain ⟨zs,x,hx,e⟩ := mem_pathPins.mp hz
      obtain ⟨i,hi,ei⟩ := pin_of_neighbor_mem hp hx zs e
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨(mem_filter.mp hi).1,ei.symm ▸ hz⟩,ei⟩
  have cc : ((AroundPins p).image p.getVert).card = (AroundPins p).card := by
    apply card_image_iff.mpr
    intro i hi j hj eq
    exact hp.1.getVert_injOn (around_data hi).1.le (around_data hj).1.le eq
  rw [eq] at cc
  exact cc.symm

/-- Coverage by the pin set and both flanks for every pin. -/
private def PinPlusFlanks {a b : V} (p : G.Walk a b) : Finset V :=
  PathPins p ∪ (AroundPins p).biUnion (Flanks p)

private lemma cover_card (hp : IsLongest p) :
    (PinPlusFlanks p).card ≤ 3*(PathPins p).card := by
  have each (i : ℕ) (_h : i ∈ AroundPins p) : (Flanks p i).card ≤ 2 := by
    have c := card_insert_le (p.getVert (i-1)) ({p.getVert (i+1)} : Finset V)
    simpa [Flanks] using c
  have c₁ := card_union_le (PathPins p) ((AroundPins p).biUnion (Flanks p))
  have c₂ := card_biUnion_le_card_mul (AroundPins p) (Flanks p) 2 each
  rw [card_around hp] at c₂
  unfold PinPlusFlanks
  omega


variable (h : Hyp G)
include h

theorem chord_lifts_or_flank (hp : IsLongest p) {x z : V} (hx : x ∉ p.support) (zs : z ∈ p.support)
    {i : ℕ} (hi : i ∈ Pins p x) (edge : G.Adj (p.getVert i) z) :
    z ∈ Flanks p i ∨ ∃ y ∉ p.support, G.Adj x y ∧ G.Adj y z := by
  classical
  have nxz : ¬G.Adj x z := fun e =>
    edge.ne (unique_path_neighbor h hp hx (p.getVert_mem_support i)
      zs (pin_data hi).2 e)
  have xz : x ≠ z := fun e => hx (e.symm ▸ zs)
  have d := mem_distanceTwo.mpr (dist_two h.con xz nxz (pin_data hi).2 edge)
  let B := External G (OmittedStar p x)
  by_cases inB : z ∈ B
  · obtain ⟨_,y,hy,ey⟩ := mem_external.mp inB
    obtain ⟨yoff,eq|adj⟩ := mem_omittedStar.mp hy
    · exact (nxz (eq ▸ ey)).elim
    · exact Or.inr ⟨y,yoff,adj,ey⟩
  · have hf := h.rigid hp hx i hi
    left
    change z ∈ ({p.getVert (i-1),p.getVert (i+1)} : Finset V)
    rw [←hf]
    exact mem_sdiff.mpr ⟨d,inB⟩

private theorem chord_lifts (hp : IsLongest p) (H : OmittedComponent p) {x y : V}
    (hx : x ∈ H.vertices) (hy : y ∈ H.vertices) {i j : ℕ} (hi : i ∈ Pins p x) (hj : j ∈ Pins p y)
    (adj : G.Adj (p.getVert i) (p.getVert j)) :
    ∃ z ∉ p.support, G.Adj x z ∧ G.Adj z (p.getVert j) := by
  have ij : i ≠ j := fun e => adj.ne (congrArg p.getVert e)
  have hh := chord_lifts_or_flank h hp (H.off x hx)
    (p.getVert_mem_support j) hi adj
  exact hh.resolve_left (pin_not_other_flank h hp H hx hy hi hj ij)

/-- Starting at any active omitted vertex, every different pin can be
reached through one or two edges of the omitted graph, followed by a pin edge. -/
theorem reach_different_pin_when_near (hp : IsLongest p) (H : OmittedComponent p)
    (hH : ∀ v, v∈H.vertices ↔ v∉p.support) {x y : V} (hx : x ∉ p.support) (hy : y ∉ p.support)
    {i j : ℕ} (hi : i ∈ Pins p x) (hj : j ∈ Pins p y) (ij : i≠j) (near : G.dist x (p.getVert j)≤3) :
    (∃ u ∉ p.support, G.Adj x u ∧ G.Adj u (p.getVert j)) ∨
      (∃ u ∉ p.support, ∃ v ∉ p.support, G.Adj x u ∧ G.Adj u v ∧ G.Adj v (p.getVert j)) := by
  classical
  let s := p.getVert i
  let t := p.getVert j
  have ss : s ∈ p.support := p.getVert_mem_support _
  have ts : t ∈ p.support := p.getVert_mem_support _
  have st : s≠t := fun e => ij (hp.1.getVert_injOn (pin_data hi).1.le (pin_data hj).1.le e)
  have xs : G.Adj x s := (pin_data hi).2
  have Hy := (hH y).mpr hy
  obtain ⟨w,wl⟩ := h.con.exists_walk_length_eq_dist x t
  have le₃ : w.length≤3 := by rw [wl]; exact near
  have unique {u v r : V} (hu : u ∉ p.support) (vs : v∈p.support) (rs : r∈p.support)
      (e : G.Adj u v) (f : G.Adj u r) : v=r :=
    unique_path_neighbor h hp hu vs rs e f
  rcases short_walk_cases w le₃ with eq|e|⟨u,e,f⟩|⟨u,v,e,f,g⟩
  · exact (hx (eq.symm ▸ ts)).elim
  · exact (st (unique hx ss ts xs e)).elim
  · by_cases us : u∈p.support
    · have eq := unique hx ss us xs e
      have e' : G.Adj (p.getVert i) (p.getVert j) := by
        change G.Adj s t
        rw [eq]
        exact f
      exact Or.inl (chord_lifts h hp H ((hH x).mpr hx) Hy hi hj e')
    · exact Or.inl ⟨u,us,e,f⟩
  · by_cases us : u∈p.support <;> by_cases vs : v∈p.support
    · have eu := unique hx ss us xs e
      have sv : G.Adj (p.getVert i) v := by change G.Adj s v; rwa [eu]
      by_cases active : v ∈ PathPins p
      · obtain ⟨_,z,hz,zv⟩ := mem_pathPins.mp active
        obtain ⟨l,hl,lv⟩ := pin_of_neighbor_mem hp hz vs zv
        have first : G.Adj (p.getVert i) (p.getVert l) := by rwa [lv]
        obtain ⟨r,ro,xr,rl⟩ := chord_lifts h hp H
          ((hH x).mpr hx) ((hH z).mpr hz) hi hl first
        have second : G.Adj (p.getVert l) (p.getVert j) := by change G.Adj _ t; rwa [lv]
        have pinr : l ∈ Pins p r := mem_filter.mpr ⟨mem_range.mpr (pin_data hl).1,rl⟩
        obtain ⟨h,ho,rh,ht⟩ := chord_lifts h hp H
          ((hH r).mpr ro) Hy pinr hj second
        exact Or.inr ⟨r,ro,h,ho,xr,rh,ht⟩
      · have one : v ∈ Flanks p i := (chord_lifts_or_flank h hp hx vs hi sv).resolve_right
          (fun hv => active (mem_pathPins.mpr ⟨vs,by
            obtain ⟨w,wo,_,wv⟩ := hv
            exact ⟨w,wo,wv⟩⟩))
        have two : v ∈ Flanks p j := (chord_lifts_or_flank h hp hy vs hj g.symm).resolve_right
          (fun hv => active (mem_pathPins.mpr ⟨vs,by
            obtain ⟨w,wo,_,wv⟩ := hv
            exact ⟨w,wo,wv⟩⟩))
        exact (disjoint_left.mp (flank_sets_disjoint h hp H ((hH x).mpr hx) Hy hi hj ij) one two).elim
    · exact (st ((unique hx ss us xs e).trans (unique vs us ts f.symm g))).elim
    · obtain ⟨l,hl,lv⟩ := pin_of_neighbor_mem hp us vs f
      have vq : G.Adj (p.getVert l) (p.getVert j) := by change G.Adj _ t; rwa [lv]
      obtain ⟨z,zo,uz,zq⟩ := chord_lifts h hp H
        ((hH u).mpr us) Hy hl hj vq
      exact Or.inr ⟨u,us,z,zo,e,uz,zq⟩
    · exact Or.inr ⟨u,us,v,vs,e,f,g⟩


theorem repr_for_near_pin
    (hp : IsLongest p) (H : OmittedComponent p) (hH : ∀ y, y∈H.vertices ↔ y ∉ p.support)
    {x : V} (hx : x ∉ p.support) {i : ℕ} (hi : i∈Pins p x)
    {q : V} (hq : q∈(PathPins p).erase (p.getVert i)) (close : G.dist x q ≤ 3) :
    ∃ v ∈ DistanceTwo G x \ Flanks p i,
      (v∈p.support ∧ v=q) ∨ (v∉p.support ∧ G.Adj v q ∧
        ¬ (∃ u ∉ p.support, G.Adj x u ∧ G.Adj u q)) := by
  obtain ⟨nq,mq⟩ := mem_erase.mp hq
  obtain ⟨qs,y,hy,yq⟩ := mem_pathPins.mp mq
  obtain ⟨j,hj,jq⟩ := pin_of_neighbor_mem hp hy qs yq
  have ij : i≠j := fun e => nq ((congrArg p.getVert e).trans jq |>.symm)
  have xq : x≠q := fun e => hx (e.symm ▸ qs)
  have nxq : ¬G.Adj x q := fun e => nq (unique_path_neighbor h hp hx
    qs (p.getVert_mem_support i) e (pin_data hi).2)
  by_cases near : ∃ u ∉ p.support, G.Adj x u ∧ G.Adj u q
  · obtain ⟨u,_,xu,uq⟩ := near
    have d := dist_two h.con xq nxq xu uq
    have off : q ∉ Flanks p i := by
      have z := pin_not_other_flank h hp H ((hH x).mpr hx) ((hH y).mpr hy) hi hj ij
      rwa [jq] at z
    exact ⟨q,mem_sdiff.mpr ⟨mem_distanceTwo.mpr d,off⟩,Or.inl ⟨qs,rfl⟩⟩
  · have walks := reach_different_pin_when_near h hp H hH hx hy hi hj ij (by simpa [jq] using close)
    rw [jq] at walks
    obtain ⟨u,uo,v,vo,xu,uv,vq⟩ := walks.resolve_left near
    have xv : x≠v := fun e => nxq (e.symm ▸ vq)
    have n : ¬G.Adj x v := fun e => near ⟨v,vo,e,vq⟩
    have d := dist_two h.con xv n xu uv
    have vof : v ∉ Flanks p i := by
      intro hv
      rcases mem_insert.mp hv with e|e
      · exact vo (e.symm ▸ p.getVert_mem_support (i-1))
      · exact vo ((mem_singleton.mp e).symm ▸ p.getVert_mem_support (i+1))
    exact ⟨v,mem_sdiff.mpr ⟨mem_distanceTwo.mpr d,vof⟩,Or.inr ⟨vo,vq,near⟩⟩


#print axioms reach_different_pin_when_near
#print axioms repr_for_near_pin

theorem at_most_one_near (hp : IsLongest p) (H : OmittedComponent p)
    (hH : ∀ v, v∈H.vertices ↔ v∉p.support) {x : V} (hx : x ∉ p.support)
    {i : ℕ} (hi : i∈Pins p x) {q r : V}
    (hq : q∈(PathPins p).erase (p.getVert i)) (hr : r∈(PathPins p).erase (p.getVert i))
    (dq : G.dist x q≤3) (dr : G.dist x r≤3) : q=r := by
  obtain ⟨v, hv, vq⟩ := repr_for_near_pin h hp H hH hx hi hq dq
  obtain ⟨w, hw, wr⟩ := repr_for_near_pin h hp H hH hx hi hr dr
  obtain ⟨vd,vf⟩ := mem_sdiff.mp hv
  obtain ⟨wd,wf⟩ := mem_sdiff.mp hw
  have vw := third_unique h hp hx hi (mem_distanceTwo.mp vd) (mem_distanceTwo.mp wd) vf wf
  subst w
  rcases vq with ⟨vs,vq⟩|⟨vo,vq,_⟩ <;> rcases wr with ⟨ws,wr⟩|⟨wo,wr,_⟩
  · exact vq.symm.trans wr
  · exact (wo vs).elim
  · exact (vo ws).elim
  · exact unique_path_neighbor h hp vo (mem_pathPins.mp (mem_erase.mp hq).2).1
      (mem_pathPins.mp (mem_erase.mp hr).2).1 vq wr

theorem pin_classes_bound (hp : IsLongest p) (H : OmittedComponent p)
    (hH : ∀ v, v∈H.vertices ↔ v∉p.support) {x : V} (hx : x ∉ p.support)
    {i : ℕ} (hi : i∈Pins p x) :
    2 ≤ (PathPins p).card ∧ (PathPins p).card ≤ 3 ∧
    ((PathPins p).card = 3 → ∃ q ∈ PathPins p, 3 < G.dist x q) := by
  classical
  have eq : componentPins H = PathPins p := by
    ext q
    simp only [componentPins,PathPins,mem_filter,hH]
  have ge := componentPins_card hp H 2 h.conn
  rw [eq] at ge
  have his : p.getVert i ∈ PathPins p := mem_pathPins.mpr
    ⟨p.getVert_mem_support i,x,hx,(pin_data hi).2⟩
  let S := (PathPins p).erase (p.getVert i)
  let A := S.filter (fun q => G.dist x q≤3)
  let B := S.filter (fun q => ¬G.dist x q≤3)
  have ca : A.card≤1 := card_le_one.mpr (fun q hq r hr =>
    at_most_one_near h hp H hH hx hi (mem_filter.mp hq).1 (mem_filter.mp hr).1
      (mem_filter.mp hq).2 (mem_filter.mp hr).2)
  have cb : B.card≤1 := card_le_one.mpr (fun q hq r hr =>
    at_most_one_far h hp hx hi (mem_filter.mp hq).2 (mem_filter.mp hr).2)
  have spl : A.card+B.card=S.card := filter_card_add_filter_neg_card_eq_card _
  have cs : S.card+1 = (PathPins p).card := by simp [S,card_erase_of_mem his, Nat.sub_add_cancel (by omega : 1≤(PathPins p).card)]
  refine ⟨ge,by omega,?_⟩
  intro three
  have one : B.card=1 := by omega
  obtain ⟨q,hq⟩ := card_pos.mp (show 0<B.card by omega)
  exact ⟨q,(mem_erase.mp (mem_filter.mp hq).1).2,Nat.lt_of_not_ge (mem_filter.mp hq).2⟩

theorem no_inactive_neighbor
    (hp : IsLongest p) (ha : 4≤G.degree a) (hb : 4≤G.degree b)
    {u x s : V} (uo : u ∉ p.support) (hx : x ∉ p.support) (ss : s ∈ p.support)
    (xs : G.Adj x s) (xu : G.Adj x u)
    (inactive : ∀ {w : V}, w∈p.support → ¬G.Adj u w) : False := by
  classical
  obtain ⟨H,hH⟩ := actual_omitted_component h hp uo
  obtain ⟨i,hi,eq⟩ := pin_of_neighbor_mem hp hx ss xs
  have counts := pin_classes_bound h hp H hH hx hi
  have hs : s ∈ PathPins p := mem_pathPins.mpr ⟨ss,x,hx,xs⟩
  have ds : G.dist u s=2 := dist_two h.con (fun e => uo (e.symm ▸ ss)) (inactive ss) xu.symm xs
  let B := p.support.toFinset \ PinPlusFlanks p
  let C := B.filter (fun w => G.dist x w≤3)
  have no_cover {w : V} (hwC : w ∈ C) : G.dist u w=4 := by
    obtain ⟨hw,near⟩ := mem_filter.mp hwC
    obtain ⟨hs,hc'⟩ := mem_sdiff.mp hw
    have ws := List.mem_toFinset.mp hs
    have notpin : w ∉ PathPins p := fun h => hc' (mem_union.mpr (Or.inl h))
    have low : 4≤G.dist u w := by
      by_contra! too
      obtain ⟨q,ql⟩ := h.con.exists_walk_length_eq_dist u w
      have short : q.length≤3 := by omega
      rcases short_walk_cases q short with he|he|⟨m,he,hf⟩|⟨m,n,he,hf,hg⟩
      · exact uo (he.symm ▸ ws)
      · exact inactive ws he
      · have mo : m ∉ p.support := fun h => inactive h he
        exact notpin (mem_pathPins.mpr ⟨ws,m,mo,hf⟩)
      · have mo : m ∉ p.support := fun h => inactive h he
        by_cases ns : n ∈ p.support
        · obtain ⟨l,hl,el⟩ := pin_of_neighbor_mem hp mo ns hf
          have edge : G.Adj (p.getVert l) w := by rwa [el]
          rcases chord_lifts_or_flank h hp mo ws hl edge with fl|⟨n,no,nm,nw⟩
          · have hnp : p.getVert l∈PathPins p := mem_pathPins.mpr
              ⟨p.getVert_mem_support l,m,mo,(pin_data hl).2⟩
            have hb : l∈AroundPins p := mem_filter.mpr ⟨mem_range.mpr (pin_data hl).1,hnp⟩
            exact hc' (mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨l,hb,fl⟩)))
          · exact notpin (mem_pathPins.mpr ⟨ws,n,no,nw⟩)
        · exact notpin (mem_pathPins.mpr ⟨ws,n,ns,hg⟩)
    have plus := h.con.dist_triangle (u:=u) (v:=x) (w:=w)
    have one := dist_eq_one_iff_adj.mpr xu.symm
    omega

  have sB : s ∉ B := fun e => (mem_sdiff.mp e).2 (mem_union.mpr (Or.inl hs))
  have uB : u ∉ B := fun e => uo (List.mem_toFinset.mp (mem_sdiff.mp e).1)
  have sC : s ∉ C := fun e => sB (mem_filter.mp e).1
  have usmall : u ∉ insert s C := by
    intro e
    rcases mem_insert.mp e with h|h
    · exact uo (h.symm ▸ ss)
    · exact uB (mem_filter.mp h).1
  have capset : insert u (insert s C) ⊆ EvenFrom G u := by
    intro w hw
    rcases mem_insert.mp hw with rfl|hw
    · simp [EvenFrom,SimpleGraph.dist_self]
    · rcases mem_insert.mp hw with rfl|hw
      · simp [EvenFrom,ds,even_two]
      · simp only [EvenFrom,mem_filter,mem_univ,true_and,no_cover hw]
        decide
  have cap := card_le_card capset
  rw [card_insert_of_not_mem usmall,card_insert_of_not_mem sC] at cap
  have cardS := cover_card hp
  have cover : p.support.toFinset ⊆ (PinPlusFlanks p) ∪ B := by
    intro w hw
    by_cases hh : w∈PinPlusFlanks p
    · exact mem_union.mpr (Or.inl hh)
    · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨hw,hh⟩))
  have ca := card_le_card cover
  have cb := card_union_le (PinPlusFlanks p) B
  rw [List.toFinset_card_of_nodup hp.1.support_nodup,length_support] at ca
  have active (j : ℕ) (hj : j∈AroundPins p) : ∃ v, v∉p.support ∧ j∈Pins p v := by
    obtain ⟨rng,mark⟩ := mem_filter.mp hj
    obtain ⟨_,v,vo,vj⟩ := mem_pathPins.mp mark
    exact ⟨v,vo,mem_filter.mpr ⟨rng,vj⟩⟩
  have ine : (AroundPins p).Nonempty := by
    rw [←card_pos,card_around hp]
    omega
  have sep : ∀ j∈AroundPins p, ∀ l∈AroundPins p, j<l → j+2≤l := by
    intro j hj l hl jl
    obtain ⟨v,vo,vj⟩ := active j hj
    obtain ⟨w,wo,wl⟩ := active l hl
    have gap := pin_gap_of_component h hp H ((hH v).mpr vo) ((hH w).mpr wo) vj wl jl
    omega
  have ge := endpoint_marks_bound_of_d2 h.con 2 h.d2 h.conn
    (fun y z yz => (h.degree y z yz).imp (by omega) (by omega)) hp (AroundPins p) ine active sep
  rw [card_around hp] at ge
  let D := B.filter (fun w => ¬G.dist x w≤3)
  have Dcap : D.card ≤ 1 := card_le_one.mpr (fun v hv w hw =>
    at_most_one_far h hp hx hi (mem_filter.mp hv).2 (mem_filter.mp hw).2)
  have Db : C.card+D.card=B.card := filter_card_add_filter_neg_card_eq_card _
  have be := h.even u
  by_cases three : (PathPins p).card=3
  · obtain ⟨q,qp,qfar⟩ := counts.2.2 three
    have dz : D.card=0 := card_eq_zero.mpr (eq_empty_iff_forall_not_mem.mpr (by
      intro w hw
      have e := at_most_one_far h hp hx hi (mem_filter.mp hw).2 (by omega : ¬G.dist x q≤3)
      exact (mem_sdiff.mp (mem_filter.mp hw).1).2 (mem_union.mpr (Or.inl (e.symm ▸ qp)))))
    omega
  · omega

#print axioms at_most_one_near
#print axioms pin_classes_bound

theorem all_omitted_active (hp : IsLongest p) (ha : 4≤G.degree a) (hb : 4≤G.degree b)
    (H : OmittedComponent p) (hH : ∀ v, v ∈ H.vertices ↔ v ∉ p.support)
    {z : V} (hz : z ∉ p.support) :
    ∃ s ∈ PathPins p, G.Adj z s := by
  classical
  let Active (v : V) := ∃ s∈p.support, G.Adj v s
  obtain ⟨x,hx,y,hy,i,hi,j,hj,ij⟩ := two_porters_of_component h hp H
  obtain ⟨q,_,hsq⟩ := H.joined x hx z ((hH z).mpr hz)
  have propagate {u v : V} (q : G.Walk u v) (hq : ∀ w ∈ q.support,w ∉ p.support)
      (hu : Active u) : Active v := by
    induction q with
    | nil => exact hu
    | @cons u w v e q ih =>
      apply ih (fun z hz => hq z (by simp [hz]))
      obtain ⟨s,ss,us⟩ := hu
      by_cases act : Active w
      · exact act
      · exact (no_inactive_neighbor h hp ha hb
          (hq w (by simp)) (hq u (by simp)) ss us e (fun {t} ht wt => act ⟨t,ht,wt⟩)).elim
  obtain ⟨t,ts,zt⟩ := propagate q (fun v hv => H.off v (hsq v hv))
    ⟨p.getVert i,p.getVert_mem_support i,(pin_data hi).2⟩
  exact ⟨t,mem_pathPins.mpr ⟨ts,z,hz,zt⟩,zt⟩

#print axioms all_omitted_active
end Graffiti189LongestPath.SharpThree.Reach
