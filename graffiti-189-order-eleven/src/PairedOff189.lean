import OneSlack189

namespace Graffiti189LongestPath.OneSlack.PairedOff
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



/-- In the d=4 one-slack range, a double porter with paired pins and an
off-path boundary point forces the longest path to have at most ten
vertices. The pin cap of the other boundary vertex is sufficient. -/
theorem path_order_le_ten (hc : G.Connected)
    (bound : ∀ v, (EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V, S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (hp : IsLongest p) (hx : x∉p.support)
    {i : ℕ} (hi : i∈Pins p x) (hj : i+2∈Pins p x)
    (size : (Pins p x).card=2)
    {u : V} (hu : u∉p.support) (xu : G.Adj x u)
    {t : V} (toff : t∉p.support) (tb : t∈External G (OmittedStar p x))
    (tsize : (Pins p t).card≤2) : p.length+1≤10 := by
  classical
  let A := OmittedStar p x
  let B := External G A
  let Fx := PinVertices p x
  let Ft := PinVertices p t
  let SX := FlankVertices p x
  let X := Fx ∪ SX
  have xA : x∈A := mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have uA : u∈A := mem_omittedStar.mpr ⟨hu,Or.inr xu⟩
  have tna : t∉A := (mem_external.mp tb).1
  have xtn : ¬G.Adj x t := fun e => tna (mem_omittedStar.mpr ⟨toff,Or.inr e⟩)
  have xtne : x≠t := fun e => tna (e ▸ xA)
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
  have ftcard : Ft.card≤2 := (card_pinVertices hp).le.trans tsize
  have fx_path {w : V} (h : w∈Fx) : w∈p.support := by
    obtain ⟨j,_,rfl⟩ := mem_image.mp h
    exact p.getVert_mem_support j
  have ft_path {w : V} (h : w∈Ft) : w∈p.support := by
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
    rw [card_insert_of_not_mem (fun h => toff (fx_path h)),fxcard,bcard]
  have sf := flanks_outside_boundary hc hp hx
  have flc : SX.card=3 := by
    rw [cardinal_flankVertices hp]
    have lt := boundary_flank_count hc hp hx
    rw [bcard,sat.1,size] at lt
    have more := flank_count_exact hp hx
    have first := card_pos.mpr (first_pins_nonempty ⟨i,hi⟩)
    omega
  have sx_path {w : V} (hw : w∈SX) : w∈p.support := by
    obtain ⟨j,_,rfl⟩ := mem_image.mp hw
    exact p.getVert_mem_support j
  have tD : t∈DistanceTwo G x :=
    boundary_except_pins_two hc hp hx (mem_sdiff.mpr ⟨tb,fun h => toff (fx_path h)⟩)
  have d_all : DistanceTwo G x = insert t SX := by
    symm
    apply eq_of_subset_of_card_le (insert_subset tD (fun v hv => (mem_sdiff.mp (sf hv)).1))
    rw [card_insert_of_not_mem (fun h => toff (sx_path h)),flc,sat.1]
  have pX {s w : V} (sF : s∈Fx) (ws : w∈p.support) (e : G.Adj s w) : w∈X := by
    by_cases h : w∈Fx
    · exact mem_union.mpr (Or.inl h)
    have xw : ¬G.Adj x w := fun e => h (atw hx ws e)
    obtain ⟨j,hj,rfl⟩ := mem_image.mp sF
    have xneq : x≠w := fun e => hx (e.symm ▸ ws)
    have wd := mem_distanceTwo.mpr (dist_two hc xneq xw (pin_data hj).2 e)
    rw [d_all] at wd
    exact mem_union.mpr (Or.inr ((mem_insert.mp wd).resolve_left (fun h => toff (h ▸ ws))))
  have iu {v w : V} (vA : v∈A) (vx : v≠x) (ws : w∈p.support) :
      ¬G.Adj v w := by
    intro e
    have wA : w∉A := fun h => (mem_omittedStar.mp h).1 ws
    have wb : w∈B := mem_external.mpr ⟨wA,v,vA,e⟩
    rw [bx,pin_eq] at wb
    have ⟨vout,vdis⟩ := mem_omittedStar.mp vA
    have xv := vdis.resolve_left vx
    rcases mem_insert.mp wb with h|h
    · exact toff (h ▸ ws)
    · rcases mem_insert.mp h with h|h
      · exact exclusive_gap_pin hp hx vout xv bi (h ▸ e)
      · exact exclusive_gap_pin hp hx vout xv bj ((mem_singleton.mp h) ▸ e)
  have uinact {w : V} (ws : w∈p.support) : ¬G.Adj u w :=
    iu uA xu.ne.symm ws
  have common : Disjoint Fx Ft := by
    rw [disjoint_left]
    intro s sF sT
    obtain ⟨_,v,vA,vt⟩ := mem_external.mp tb
    obtain ⟨vout,vset⟩ := mem_omittedStar.mp vA
    have xv : G.Adj x v := vset.resolve_left (fun eq => xtn (eq ▸ vt))
    let q : G.Walk x t := .cons xv vt.toWalk
    have qp : q.IsPath := (IsPath.of_adj vt).cons (by simp [xv.ne,xtne])
    have oq : ∀ w∈q.support,w∉p.support := by simp [q,hx,vout,toff]
    have ts : G.Adj t s := by
      obtain ⟨k,hk,eq⟩ := mem_image.mp sT
      exact eq ▸ (pin_data hk).2
    rw [pin_eq] at sF
    rcases mem_insert.mp sF with eq|eq
    · have e : G.Adj t (p.getVert i) := eq ▸ ts
      obtain ⟨r,rp,rl,_⟩ := splice_gap_two p hp.1 q.reverse qp.reverse
        (by simpa using oq) i (by omega) e.symm (pin_data hj).2
      have l := hp.2 a b r rp
      simp [q] at rl
      omega
    · have e : G.Adj t (p.getVert (i+2)) := (mem_singleton.mp eq) ▸ ts
      obtain ⟨r,rp,rl,_⟩ := splice_gap_two p hp.1 q qp oq i (by omega) (pin_data hi).2.symm e
      have l := hp.2 a b r rp
      simp [q] at rl
      omega
  have Cx : X.card≤5 := by
    change (Fx ∪ SX).card≤5
    have h := card_union_le Fx SX
    omega
  let DT := (DistanceTwo G t).filter (·∈p.support)
  let C := X ∪ (Ft ∪ (if G.Adj u t then DT else ∅))
  let L := p.support.toFinset \ C
  have fxc : Fx ⊆ C := fun v hv => mem_union.mpr (Or.inl (mem_union.mpr (Or.inl hv)))
  have ftc : Ft ⊆ C := fun v hv => mem_union.mpr (Or.inr (mem_union.mpr (Or.inl hv)))
  have step_in {v w : V} (vA : v∈A) (wo : w∉p.support) (e : G.Adj v w) :
      w ∈ A ∨ w=t := by
    by_cases h : w∈A
    · exact Or.inl h
    · have wb : w∈B := mem_external.mpr ⟨h,v,vA,e⟩
      rw [bx] at wb
      exact Or.inr ((mem_insert.mp wb).resolve_right (fun h => wo (fx_path h)))
  have path_from_A {v w : V} (vA : v∈A) (ws : w∈p.support) (e : G.Adj v w) : w∈Fx := by
    by_cases h : v=x
    · exact atw hx ws (h ▸ e)
    · exact (iu vA h ws e).elim
  have ldist {w : V} (hw : w∈L) : G.dist u w=4 := by
    obtain ⟨ws,nc⟩ := mem_sdiff.mp hw
    have ws' := List.mem_toFinset.mp ws
    have low : 4≤G.dist u w := by
      by_cases low : 4≤G.dist u w
      · exact low
      · exfalso
        obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist u w
        have short : q.length≤3 := by omega
        rcases short_walk_cases q short with h|h|⟨r,ur,rw⟩|⟨r,s,ur,rs,sw⟩
        · exact hu (h.symm ▸ ws')
        · exact uinact ws' h
        · have ro : r∉p.support := fun pp => uinact pp ur
          rcases step_in uA ro ur with rA|rt
          · exact nc (fxc (path_from_A rA ws' rw))
          · exact nc (ftc (atw toff ws' (rt ▸ rw)))
        · have ro : r∉p.support := fun pp => uinact pp ur
          rcases step_in uA ro ur with rA|rt
          · by_cases sp : s∈p.support
            · exact nc (mem_union.mpr (Or.inl (pX (path_from_A rA sp rs) ws' sw)))
            · rcases step_in rA sp rs with sA|st
              · exact nc (fxc (path_from_A sA ws' sw))
              · exact nc (ftc (atw toff ws' (st ▸ sw)))
          · have ut : G.Adj u t := rt ▸ ur
            have tness : t≠w := fun e => toff (e.symm ▸ ws')
            have nt : ¬G.Adj t w := fun e => nc (ftc (atw toff ws' e))
            have wd : G.dist t w=2 := dist_two hc tness nt (rt ▸ rs) sw
            have dt : w∈DT := mem_filter.mpr ⟨mem_distanceTwo.mpr wd,ws'⟩
            exact nc (mem_union.mpr (Or.inr (mem_union.mpr (Or.inr (by simpa [ut] using dt)))))
    have xx := sat.2.1 w
    have t := hc.dist_triangle (u:=u) (v:=x) (w:=w)
    have one := dist_eq_one_iff_adj.mpr xu.symm
    omega
  let P := Fx ∪ (if G.Adj u t then Ft else ∅)
  have pSub : P ⊆ C := by
    intro w hw
    rcases mem_union.mp hw with h|h
    · exact fxc h
    · by_cases ut : G.Adj u t
      · exact ftc (by simpa [ut] using h)
      · simp [ut] at h
  have pEven : P ⊆ EvenFrom G u := by
    intro w hw
    rcases mem_union.mp hw with h|h
    · have sp := fx_path h
      obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      have ne : u≠p.getVert j := fun e => hu (e.symm ▸ sp)
      have d := dist_two hc ne (uinact sp) xu.symm (pin_data hj).2
      simp [EvenFrom,d,even_two]
    · by_cases ut : G.Adj u t
      · have hh : w∈Ft := by simpa [ut] using h
        have sp := ft_path hh
        obtain ⟨j,hj,rfl⟩ := mem_image.mp hh
        have ne : u≠p.getVert j := fun e => hu (e.symm ▸ sp)
        have d := dist_two hc ne (uinact sp) ut (pin_data hj).2
        simp [EvenFrom,d,even_two]
      · simp [ut] at h
  have dPL : Disjoint P L := by
    rw [disjoint_left]
    exact fun w hp hl => (mem_sdiff.mp hl).2 (pSub hp)
  have uNot : u∉P ∪ L := by
    intro h
    rcases mem_union.mp h with hp|hl
    · rcases mem_union.mp hp with ha|hb
      · exact hu (fx_path ha)
      · by_cases ut : G.Adj u t
        · exact hu (ft_path (by simpa [ut] using hb))
        · simp [ut] at hb
    · exact hu (List.mem_toFinset.mp (mem_sdiff.mp hl).1)
  have allE : insert u (P ∪ L) ⊆ EvenFrom G u := by
    intro w hw
    rcases mem_insert.mp hw with rfl|h
    · simp [EvenFrom,SimpleGraph.dist_self]
    · rcases mem_union.mp h with h|h
      · exact pEven h
      · simp only [EvenFrom,mem_filter,mem_univ,true_and,ldist h]
        decide
  have ecard := card_le_card allE
  rw [card_insert_of_not_mem uNot,card_union_of_disjoint dPL] at ecard
  have left : p.support.toFinset ⊆ C ∪ L := by
    intro w hw
    by_cases a : w ∈ C
    · exact mem_union.mpr (Or.inl a)
    · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨hw,a⟩))
  have c_count := card_le_card left
  rw [List.toFinset_card_of_nodup hp.1.support_nodup,length_support] at c_count
  have c_union := card_union_le C L
  have e_cap := bound u
  by_cases ut : G.Adj u t
  · have p_card : P.card=2+Ft.card := by
      change (Fx ∪ (if G.Adj u t then Ft else ∅)).card = _
      rw [if_pos ut,card_union_of_disjoint common,fxcard]
    have xtD : x∈DistanceTwo G t := mem_distanceTwo.mpr (dist_two hc xtne.symm
      (fun e => xtn e.symm) ut.symm xu.symm)
    have no : x∉DT := fun h => hx (mem_filter.mp h).2
    have sub : insert x DT ⊆ DistanceTwo G t := insert_subset xtD (filter_subset _ _)
    have dtcard := card_le_card sub
    rw [card_insert_of_not_mem no] at dtcard
    have dtcap := distanceTwo_le_of_even 4 t (bound t)
    have cc : C.card ≤ X.card+(Ft.card+DT.card) := by
      change (X ∪ (Ft ∪ (if G.Adj u t then DT else ∅))).card ≤ _
      rw [if_pos ut]
      exact (card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _)
    omega
  · have p_card : P.card=2 := by
      change (Fx ∪ (if G.Adj u t then Ft else ∅)).card=2
      rw [if_neg ut,union_empty,fxcard]
    have cc : C.card ≤ X.card+Ft.card := by
      change (X ∪ (Ft ∪ (if G.Adj u t then DT else ∅))).card≤_
      rw [if_neg ut,union_empty]
      exact card_union_le _ _
    omega

#print axioms path_order_le_ten
end Graffiti189LongestPath.OneSlack.PairedOff
