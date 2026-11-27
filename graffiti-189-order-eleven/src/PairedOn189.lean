import OneSlack189

namespace Graffiti189LongestPath.OneSlack.PairedOn
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
private theorem no_endpoints {x a b : V} {p : G.Walk a b}
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

private theorem dist_two {a b c : V} (hconn : G.Connected)
    (hac : a ≠ c) (hna : ¬G.Adj a c) (hab : G.Adj a b) (hbc : G.Adj b c) :
    G.dist a c = 2 := by
  have hu := hconn.one_lt_dist_of_ne_of_not_adj hac hna
  have hl := G.dist_le (Walk.cons hab (Walk.cons hbc .nil))
  simp at hl
  omega




variable [Fintype V]
private theorem mem_distanceTwo {x y : V} :
    y ∈ DistanceTwo G x ↔ G.dist x y = 2 := by
  classical
  simp [DistanceTwo]




variable [DecidableEq V] [DecidableRel G.Adj]
set_option maxHeartbeats 1500000 in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem splice_gap_two {x y a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (q : G.Walk x y) (hq : q.IsPath)
    (hd : ∀ w ∈ q.support, w ∉ p.support) (i : ℕ) (hi : i+1 < p.length)
    (h₀ : G.Adj (p.getVert i) x) (h₁ : G.Adj y (p.getVert (i + 2))) :
    ∃ r : G.Walk a b, r.IsPath ∧ r.length = p.length + q.length ∧
      ∀ w : V, w ∈ r.support ↔ w ∈ q.support ∨ (w ∈ p.support ∧ w ≠ p.getVert (i+1)) := by
  induction p generalizing i with
  | nil => simp at hi
  | @cons a u b hau p ih =>
    cases i with
    | zero =>
      cases p with
      | nil => simp at hi
      | @cons u v b huv p =>
        have hax : G.Adj a x := h₀
        have hyv : G.Adj y v := by simpa using h₁
        have ha : a ∉ (cons huv p).support := (cons_isPath_iff _ _).1 hp |>.2
        have hu : u ∉ p.support := (cons_isPath_iff _ _).1 hp.of_cons |>.2
        have hqapp : (q.append (.cons hyv p)).IsPath := by
          rw [isPath_def, support_append, List.nodup_append]
          refine ⟨hq.support_nodup, ?_, ?_⟩
          · simpa only [support_cons, List.tail_cons] using hp.of_cons.of_cons.support_nodup
          · intro t ht ht'
            have hx' : t ∈ p.support := by simpa only [support_cons, List.tail_cons] using ht'
            exact hd t ht (by simp [hx'])
        refine ⟨.cons hax _, hqapp.cons ?_, by simp; omega, ?_⟩
        · rw [mem_support_append_iff]
          intro hh
          rcases hh with hh | hh
          · exact hd a hh (by simp)
          · simp only [support_cons, List.mem_cons] at hh
            exact hh.elim (fun e => hd a (e.symm ▸ q.end_mem_support) (by simp))
              (fun h => ha (by simp [h]))
        · intro w
          change w ∈ (cons hax _).support ↔ w ∈ q.support ∨
            (w ∈ (cons hau (cons huv p)).support ∧ w ≠ u)
          simp only [support_cons,List.mem_cons,mem_support_append_iff]
          have e : w = y → w ∈ q.support := fun h => h.symm ▸ q.end_mem_support
          have f : w = a → w ≠ u := fun h => h.symm ▸ hau.ne
          have k : w ∈ p.support → w ≠ u := fun h e => hu (e ▸ h)
          constructor
          · rintro (ha' | h | h | h)
            · exact Or.inr ⟨Or.inl ha', f ha'⟩
            · exact Or.inl h
            · exact Or.inl (e h)
            · exact Or.inr ⟨Or.inr (Or.inr h),k h⟩
          · rintro (h | ⟨(h | h | h),hn⟩)
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
            · exact (hn h).elim
            · exact Or.inr (Or.inr (Or.inr h))
    | succ i =>
      have hi' : i+1 < p.length := by simp at hi; omega
      obtain ⟨r,hr,hlen,hsup⟩ := ih hp.of_cons
        (fun t ht hs => hd t ht (by simp [hs])) i hi' h₀ h₁
      refine ⟨.cons hau r,hr.cons ?_,by simp [hlen]; omega,?_⟩
      · rw [hsup]
        intro h
        exact h.elim (fun e => hd a e (by simp))
          (fun e => ((cons_isPath_iff _ _).1 hp |>.2) e.1)
      · intro w
        change w ∈ (cons hau r).support ↔
          w ∈ q.support ∨ (w ∈ (cons hau p).support ∧ w ≠ p.getVert (i+1))
        simp only [support_cons,List.mem_cons,hsup]
        have e : w = a → w ≠ p.getVert (i+1) := by
          intro h h'
          have ht := p.getVert_mem_support (i+1)
          rw [←h',h] at ht
          exact (cons_isPath_iff _ _).1 hp |>.2 ht
        constructor
        · rintro (h | h | ⟨h,h'⟩)
          · exact Or.inr ⟨Or.inl h,e h⟩
          · exact Or.inl h
          · exact Or.inr ⟨Or.inr h,h'⟩
        · rintro (h | ⟨(h | h),h'⟩)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr ⟨h,h'⟩)


omit [Fintype V] [DecidableEq V] in
private theorem pin_data {a b : V} {p : G.Walk a b} {x : V} {i : ℕ}
    (hi : i ∈ Pins p x) : i < p.length ∧ G.Adj x (p.getVert i) :=
  ⟨Finset.mem_range.mp (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩

omit [Fintype V] [DecidableEq V] in
private theorem pin_of_neighbor_mem {a b x y : V} {p : G.Walk a b}
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
private lemma pin_pos {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x ∉ p.support)
    {i : ℕ} (hi : i ∈ Pins p x) : 0 < i := by
  by_contra h
  have e : i=0 := Nat.eq_zero_of_not_pos h
  exact (no_endpoints hp hx).1 (by simpa only [e,getVert_zero] using (pin_data hi).2)



variable {a b : V} {p : G.Walk a b} {x : V}
private theorem card_pinVertices (hp : IsLongest p) :
    (PinVertices p x).card = (Pins p x).card := by
  apply card_image_iff.mpr
  intro i hi j hj e
  exact hp.1.getVert_injOn (pin_data hi).1.le (pin_data hj).1.le e

private theorem cardinal_flankVertices (hp : IsLongest p) :
    (FlankVertices p x).card = (FlankIndices p x).card := by
  have upper (i : ℕ) (hi : i∈FlankIndices p x) : i≤p.length := by
    rcases mem_union.mp hi with hi|hi
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      have := (pin_data hj).1
      change j-1≤p.length
      omega
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      have := (pin_data hj).1
      change j+1≤p.length
      omega
  apply card_image_iff.mpr
  intro i hi j hj e
  exact hp.1.getVert_injOn (upper i hi) (upper j hj) e

private theorem pin_vertices_subset_boundary (hx : x ∉ p.support) :
    PinVertices p x ⊆ External G (OmittedStar p x) := by
  intro z hz
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
  exact mem_external.mpr
    ⟨fun e => (mem_omittedStar.mp e).1 (p.getVert_mem_support i),x,mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩,(pin_data hi).2⟩

private theorem boundary_except_pins_two (hc : G.Connected) (hp : IsLongest p)
    (hx : x ∉ p.support) : External G (OmittedStar p x) \ PinVertices p x ⊆ DistanceTwo G x := by
  intro v hv
  obtain ⟨vb,nvp⟩ := mem_sdiff.mp hv
  obtain ⟨nva,z,za,zv⟩ := mem_external.mp vb
  have star : x∈OmittedStar p x := mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have xv : x≠v := fun e => nva (e ▸ star)
  have nxv : ¬G.Adj x v := by
    intro e
    by_cases vp : v∈p.support
    · obtain ⟨i,hi,iv⟩ := pin_of_neighbor_mem hp hx vp e
      exact nvp (mem_image.mpr ⟨i,hi,iv⟩)
    · exact nva (mem_omittedStar.mpr ⟨vp,Or.inr e⟩)
  obtain ⟨_,eq|xz⟩ := mem_omittedStar.mp za
  · exact (nxv (eq ▸ zv)).elim
  · exact mem_distanceTwo.mpr (dist_two hc xv nxv xz zv)

private theorem exclusive_gap_pin (hp : IsLongest p) (hx : x ∉ p.support)
    {y : V} (hy : y ∉ p.support) (xy : G.Adj x y) {i : ℕ} (hi : i ∈ PairedPins p x) :
    ¬G.Adj y (p.getVert i) := by
  intro ein
  have both {s t : V} (e : G.Adj s t) (hs : s ∉ p.support) (ht : t ∉ p.support) :
      ∀ w ∈ e.toWalk.support, w ∉ p.support := by simp [hs,ht]
  obtain ⟨hi,j,hj,eq|eq⟩ := mem_filter.mp hi
  · have il := (pin_data hi).1
    obtain ⟨q,qp,ql,_⟩ := splice_gap_two p hp.1 xy.toWalk (IsPath.of_adj xy) (both xy hx hy)
      j (by omega) (pin_data hj).2.symm (by rwa [eq])
    have b := hp.2 a _ q qp
    simp at ql
    omega
  · have jl := (pin_data hj).1
    obtain ⟨q,qp,ql,_⟩ := splice_gap_two p hp.1 xy.symm.toWalk (IsPath.of_adj xy.symm)
      (both xy.symm hy hx) i (by omega) ein.symm (by rw [eq]; exact (pin_data hj).2)
    have b := hp.2 a _ q qp
    simp at ql
    omega

private theorem first_pins_nonempty {x : V} (h : (Pins p x).Nonempty) :
    (FirstPins p x).Nonempty := by
  let I := Pins p x
  let m := I.min' h
  have hm : m∈I := I.min'_mem h
  refine ⟨m,mem_filter.mpr ⟨hm,?_⟩⟩
  intro j hj eq
  have le : m≤j := I.min'_le j hj
  omega

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




/-- In the d=4 one-slack range, when the third boundary vertex of a paired
double porter is itself on the path, the longest path has at most 11 vertices. -/
theorem paired_on_data (hc : G.Connected)
    (bound : ∀ v, (EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V, S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (hp : IsLongest p) (hx : x∉p.support)
    {i : ℕ} (hi : i∈Pins p x) (hj : i+2∈Pins p x)
    (size : (Pins p x).card=2)
    {u : V} (hu : u∉p.support) (xu : G.Adj x u)
    {t : V} (ts : t∈p.support) (tb : t∈External G (OmittedStar p x))
    (nt : t∉PinVertices p x) :
    p.length+1≤11 ∧ 3≤(External G (OmittedStar p x)).card ∧
    ∃ y∉p.support, G.Adj x y ∧ ∃ l∈Pins p y,
      p.getVert l=t ∧ (Pins p y).card=1 ∧ 3≤(External G (OmittedStar p y)).card := by
  classical
  let A := OmittedStar p x
  let B := External G A
  let Fx := PinVertices p x
  let SX := FlankVertices p x
  have jlt := (pin_data hj).1
  have bi : i∈PairedPins p x := mem_filter.mpr ⟨hi,i+2,hj,Or.inr rfl⟩
  have bj : i+2∈PairedPins p x := mem_filter.mpr ⟨hj,i,hi,Or.inl rfl⟩
  have ii : Pins p x = {i,i+2} := by
    have sub : ({i,i+2} : Finset ℕ) ⊆ Pins p x := by
      intro j hj'
      rcases mem_insert.mp hj' with rfl|h
      · exact hi
      · rw [mem_singleton] at h
        subst j
        exact hj
    symm
    apply eq_of_subset_of_card_le sub
    have e : i≠i+2 := by omega
    simp [size,e]
  have pin_eq : Fx={p.getVert i,p.getVert (i+2)} := by
    change (Pins p x).image p.getVert = _
    rw [ii,image_insert,image_singleton]
  have fxcard : Fx.card=2 := (card_pinVertices hp).trans size
  have fx_path {w : V} (h : w∈Fx) : w∈p.support := by
    obtain ⟨j,_,rfl⟩ := mem_image.mp h
    exact p.getVert_mem_support j
  have atw {z w : V} (zs : z∉p.support) (ws : w∈p.support) (adj : G.Adj z w) :
      w∈PinVertices p z := by
    obtain ⟨j,hj,h⟩ := pin_of_neighbor_mem hp zs ws adj
    exact mem_image.mpr ⟨j,hj,h⟩
  have sat := double_porter_saturated_one_slack hc 2 hp hx size (bound x) conn hu xu
  have bcard : B.card=3 := by
    rcases sat.2.2 with h|h
    · have e := h.1
      rw [e] at bi
      exact (not_mem_empty _ bi).elim
    · exact h.2
  have bx : B=insert t Fx := by
    symm
    apply eq_of_subset_of_card_le (insert_subset tb (pin_vertices_subset_boundary hx))
    rw [card_insert_of_not_mem nt,fxcard,bcard]
  have sf := flanks_outside_boundary hc hp hx
  have flc : SX.card=3 := by
    rw [cardinal_flankVertices hp]
    have lt := boundary_flank_count hc hp hx
    rw [bcard,sat.1,size] at lt
    have more := flank_count_exact hp hx
    have first := card_pos.mpr (first_pins_nonempty ⟨i,hi⟩)
    omega
  have tD : t∈DistanceTwo G x :=
    boundary_except_pins_two hc hp hx (mem_sdiff.mpr ⟨tb,nt⟩)
  have d_all : DistanceTwo G x = insert t SX := by
    symm
    apply eq_of_subset_of_card_le (insert_subset tD (fun v hv => (mem_sdiff.mp (sf hv)).1))
    rw [card_insert_of_not_mem (fun h => (mem_sdiff.mp (sf h)).2 tb),flc,sat.1]
  obtain ⟨_,y,yA,yt⟩ := mem_external.mp tb
  have yo : y∉p.support := (mem_omittedStar.mp yA).1
  have n : y≠x := fun e => nt (atw hx ts (e ▸ yt))
  have xy : G.Adj x y := (mem_omittedStar.mp yA).2.resolve_left n
  have xnt : ¬G.Adj x t := fun h => nt (atw hx ts h)
  have y_bound {v : V} (vs : v∈p.support) (a : G.Adj y v) : v=t := by
    have vo : v∉A := fun h => (mem_omittedStar.mp h).1 vs
    have b : v∈B := mem_external.mpr ⟨vo,y,yA,a⟩
    rw [bx,pin_eq] at b
    rcases mem_insert.mp b with h|h
    · exact h
    · rcases mem_insert.mp h with h|h
      · exact (exclusive_gap_pin hp hx yo xy bi (h ▸ a)).elim
      · exact (exclusive_gap_pin hp hx yo xy bj ((mem_singleton.mp h) ▸ a)).elim
  obtain ⟨l,hl,eqt⟩ := pin_of_neighbor_mem hp yo ts yt
  have yPins : Pins p y={l} := by
    ext j
    constructor
    · intro hj'
      apply mem_singleton.mpr
      exact hp.1.getVert_injOn (pin_data hj').1.le (pin_data hl).1.le
        ((y_bound (p.getVert_mem_support j) (pin_data hj').2).trans eqt.symm)
    · rw [mem_singleton]
      rintro rfl
      exact hl
  let SY := FlankVertices p y
  have sy_card : SY.card=2 := by
    change (FlankVertices p y).card=2
    rw [cardinal_flankVertices hp,FlankIndices,yPins,image_singleton,image_singleton]
    have lp := pin_pos hp yo hl
    have ne : l-1≠l+1 := by omega
    have dis : Disjoint ({l-1} : Finset ℕ) {l+1} := by simp [ne,Ne.symm ne]
    rw [card_union_of_disjoint dis,card_singleton,card_singleton]
  have fx_inY : Fx ⊆ External G (OmittedStar p y) := by
    intro v hv
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hv
    exact mem_external.mpr ⟨fun e => (mem_omittedStar.mp e).1 (p.getVert_mem_support j),x,
      mem_omittedStar.mpr ⟨hx,Or.inr xy.symm⟩,(pin_data hj).2⟩
  have dfx : Fx ⊆ DistanceTwo G y := by
    intro v hv
    have vp := fx_path hv
    have ynv : y≠v := fun e => yo (e.symm ▸ vp)
    have nay : ¬G.Adj y v := fun e => nt ((y_bound vp e) ▸ hv)
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hv
    exact mem_distanceTwo.mpr (dist_two hc ynv nay xy.symm (pin_data hj).2)
  have sy := flanks_outside_boundary hc hp yo
  have dis : Disjoint Fx SY := by
    rw [disjoint_left]
    exact fun w hw hh => (mem_sdiff.mp (sy hh)).2 (fx_inY hw)
  have fullY : DistanceTwo G y = Fx ∪ SY := by
    symm
    apply eq_of_subset_of_card_le (union_subset dfx (fun _ h => (mem_sdiff.mp (sy h)).1))
    rw [card_union_of_disjoint dis,fxcard,sy_card]
    exact distanceTwo_le_of_even 4 y (bound y)
  have eccY (z : V) : G.dist y z≤3 := by
    by_cases h : G.dist y z≤3
    · exact h
    · exfalso
      have dd := distanceTwo_add_two_le_even_of_far hc (show 4≤G.dist y z from Nat.lt_of_not_ge h)
      rw [fullY,card_union_of_disjoint dis,fxcard,sy_card] at dd
      have cap := bound y
      omega
  let C := (insert t Fx) ∪ (SX ∪ SY)
  have cfx : Fx⊆C := fun _ hv => mem_union.mpr (Or.inl (mem_insert.mpr (Or.inr hv)))
  have ct : t∈C := mem_union.mpr (Or.inl (mem_insert_self _ _))
  have bc : B⊆C := by rw [bx]; exact subset_union_left
  have ccard : C.card≤8 := by
    change ((insert t Fx) ∪ (SX ∪ SY)).card≤_
    have cf := card_union_le (insert t Fx) (SX ∪ SY)
    have cg := card_union_le SX SY
    have ch := card_insert_le t Fx
    omega
  have pin_chord {v w : V} (hv : v∈B) (wp : w∈p.support) (e : G.Adj v w) :
      w∈C := by
    rw [bx] at hv
    rcases mem_insert.mp hv with rfl|hv
    · have ynw : y≠w := fun e => yo (e.symm ▸ wp)
      have nay : ¬G.Adj y w := fun a => e.ne (y_bound wp a).symm
      have dw := mem_distanceTwo.mpr (dist_two hc ynw nay yt e)
      rw [fullY] at dw
      exact (mem_union.mp dw).elim (fun h => cfx h) (fun h => mem_union.mpr (Or.inr (mem_union.mpr (Or.inr h))))
    · by_cases b : w∈Fx
      · exact cfx b
      have xnw : x≠w := fun e => hx (e.symm ▸ wp)
      have nax : ¬G.Adj x w := fun e => b (atw hx wp e)
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hv
      have dw := mem_distanceTwo.mpr (dist_two hc xnw nax (pin_data hj).2 e)
      rw [d_all] at dw
      exact (mem_insert.mp dw).elim (fun e => e.symm ▸ ct)
        (fun h => mem_union.mpr (Or.inr (mem_union.mpr (Or.inl h))))
  have path_cross {v w : V} (vA : v∈A) (ws : w∈p.support) (e : G.Adj v w) : w∈B :=
    mem_external.mpr ⟨fun h => (mem_omittedStar.mp h).1 ws,v,vA,e⟩
  have off_stays {v w : V} (vA : v∈A) (wo : w∉p.support) (e : G.Adj v w) : w∈A := by
    by_cases h : w∈A
    · exact h
    · have b : w∈B := mem_external.mpr ⟨h,v,vA,e⟩
      rw [bx] at b
      exact (wo ((mem_insert.mp b).elim (fun e => e.symm ▸ ts) fx_path)).elim
  let L := p.support.toFinset \ C
  have ldist {w : V} (hw : w∈L) : w∈DistanceTwo G t := by
    obtain ⟨wp,nc⟩ := mem_sdiff.mp hw
    have ws : w∈p.support := List.mem_toFinset.mp wp
    obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist y w
    have cap := eccY w
    have le3 : q.length≤3 := by omega
    rcases short_walk_cases q le3 with e|e|⟨r,yr,rw⟩|⟨r,s,yr,rs,sw⟩
    · exact (yo (e.symm ▸ ws)).elim
    · exact (nc ((y_bound ws e).symm ▸ ct)).elim
    · by_cases rp : r∈p.support
      · have eq := y_bound rp yr
        exact (nc (pin_chord tb ws (eq ▸ rw))).elim
      · exact (nc (bc (path_cross (off_stays yA rp yr) ws rw))).elim
    · by_cases rp : r∈p.support
      · have eq := y_bound rp yr
        have tw : t≠w := fun e => nc (e ▸ ct)
        have ntw : ¬G.Adj t w := fun e => nc (pin_chord tb ws e)
        exact mem_distanceTwo.mpr (dist_two hc tw ntw (eq ▸ rs) sw)
      · have ra := off_stays yA rp yr
        by_cases sp : s∈p.support
        · exact (nc (pin_chord (path_cross ra sp rs) ws sw)).elim
        · exact (nc (bc (path_cross (off_stays ra sp rs) ws sw))).elim
  have tx : t≠x := fun e => hx (e ▸ ts)
  have xtd := mem_distanceTwo.mpr (dist_two hc tx (fun e => xnt e.symm) yt.symm xy.symm)
  have nL : x∉L := fun e => hx (List.mem_toFinset.mp (mem_sdiff.mp e).1)
  have le := card_le_card (insert_subset xtd (show L ⊆ DistanceTwo G t from fun _ hw => ldist hw))
  rw [card_insert_of_not_mem nL] at le
  have cap := distanceTwo_le_of_even 4 t (bound t)
  have cover : p.support.toFinset ⊆ C ∪ L := by
    intro v hv
    by_cases e : v∈C
    · exact mem_union.mpr (Or.inl e)
    · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨hv,e⟩))
  have cc := card_le_card cover
  rw [List.toFinset_card_of_nodup hp.1.support_nodup,length_support] at cc
  have cl := card_union_le C L
  refine ⟨by omega,bcard.ge,y,yo,xy,l,hl,eqt,by rw [yPins,card_singleton],?_⟩
  have tY := pin_vertices_subset_boundary yo (mem_image.mpr ⟨l,hl,eqt⟩)
  have c := card_le_card (insert_subset tY fx_inY)
  rw [card_insert_of_not_mem nt,fxcard] at c
  exact c

theorem path_order_le_eleven (hc : G.Connected)
    (bound : ∀ v, (EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V, S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (hp : IsLongest p) (hx : x∉p.support)
    {i : ℕ} (hi : i∈Pins p x) (hj : i+2∈Pins p x)
    (size : (Pins p x).card=2)
    {u : V} (hu : u∉p.support) (xu : G.Adj x u)
    {t : V} (ts : t∈p.support) (tb : t∈External G (OmittedStar p x))
    (nt : t∉PinVertices p x) : p.length+1≤11 :=
  (paired_on_data hc bound conn hp hx hi hj size hu xu ts tb nt).1

#print axioms paired_on_data
#print axioms path_order_le_eleven
end Graffiti189LongestPath.OneSlack.PairedOn
