import Rigidity189

namespace Graffiti189LongestPath.OneSlack
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 1800000
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
omit [Fintype V] [DecidableRel G.Adj] in
private theorem splice_walk {x y a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (q : G.Walk x y) (hq : q.IsPath)
    (hd : ∀ w ∈ q.support, w ∉ p.support) (i : ℕ) (hi : i < p.length)
    (h₀ : G.Adj (p.getVert i) x) (h₁ : G.Adj y (p.getVert (i + 1))) :
    ∃ r : G.Walk a b, r.IsPath ∧ r.length = p.length + q.length + 1 ∧
      ∀ w : V, w ∈ r.support ↔ w ∈ q.support ∨ w ∈ p.support := by
  induction p generalizing i with
  | nil => simp at hi
  | @cons v w z hvw p ih =>
    cases i with
    | zero =>
      have hvx : G.Adj v x := h₀
      have hyw : G.Adj y w := by simpa using h₁
      have hv : v ∉ p.support := (cons_isPath_iff _ _).1 hp |>.2
      have hqapp : (q.append (.cons hyw p)).IsPath := by
        rw [isPath_def, support_append, List.nodup_append]
        refine ⟨hq.support_nodup, ?_, ?_⟩
        · simpa only [support_cons, List.tail_cons] using hp.of_cons.support_nodup
        · intro t ht ht'
          have hx' : t ∈ p.support := by simpa only [support_cons, List.tail_cons] using ht'
          exact hd t ht (by simp [hx'])
      refine ⟨.cons hvx _, hqapp.cons ?_, by simp; omega, ?_⟩
      · rw [mem_support_append_iff]
        intro hh
        rcases hh with hh | hh
        · exact hd v hh (by simp)
        · simp only [support_cons, List.mem_cons] at hh
          exact hh.elim (fun e => hd v (e.symm ▸ q.end_mem_support) (by simp)) hv
      · intro t
        simp only [support_cons, List.mem_cons, mem_support_append_iff]
        have hy : t = y → t ∈ q.support := fun e => e.symm ▸ q.end_mem_support
        tauto
    | succ i =>
      have hi' : i < p.length := by simp at hi; omega
      obtain ⟨r,hr,hlen,hsup⟩ := ih hp.of_cons
        (fun t ht hs => hd t ht (by simp [hs])) i hi' h₀ h₁
      refine ⟨.cons hvw r, hr.cons ?_, by simp [hlen]; omega, ?_⟩
      · rw [hsup]
        exact not_or.mpr ⟨fun e => hd v e (by simp), (cons_isPath_iff _ _).1 hp |>.2⟩
      · intro t
        simp only [support_cons, List.mem_cons, hsup]
        tauto

omit [Fintype V] [DecidableRel G.Adj] in
private theorem walk_in_star {a b x : V} (p : G.Walk a b) (hx : x ∉ p.support)
    {y z : V} (hy : y ∉ p.support ∧ (y = x ∨ G.Adj x y))
    (hz : z ∉ p.support ∧ (z = x ∨ G.Adj x z)) :
    ∃ q : G.Walk y z, q.IsPath ∧ ∀ w ∈ q.support, w ∉ p.support := by
  by_cases e : y = z
  · subst z
    exact ⟨.nil,IsPath.nil,by simpa using hy.1⟩
  rcases hy.2 with rfl|hy'
  · rcases hz.2 with e'|hz'
    · exact (e e'.symm).elim
    · exact ⟨hz'.toWalk,IsPath.of_adj hz',by simp [hx,hz.1]⟩
  rcases hz.2 with rfl|hz'
  · exact ⟨hy'.symm.toWalk,IsPath.of_adj hy'.symm,by simp [hx,hy.1]⟩
  refine ⟨.cons hy'.symm hz'.toWalk, (IsPath.of_adj hz').cons ?_, ?_⟩
  · simp [hy'.ne.symm,e]
  · simp [hx,hy.1,hz.1]


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


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem boundary_card_of_connectivity (k : ℕ)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {x a : V} {A B : Finset V} (hxa : x ∈ A) (haa : a ∉ A) (hab : a ∉ B)
    (hdis : Disjoint A B) (hbound : ∀ y ∈ A, ∀ z ∉ A, G.Adj y z → z ∈ B) :
    k ≤ B.card := by
  by_contra! hsmall
  let W : Set V := (↑B : Set V)ᶜ
  let u : W := ⟨x,fun hb => Finset.disjoint_left.mp hdis hxa hb⟩
  let v : W := ⟨a,hab⟩
  have walk_closed {s t : W} (q : (G.induce W).Walk s t) (hs : (s : V) ∈ A) : (t : V) ∈ A := by
    induction q with
    | nil => exact hs
    | @cons a' b' c' e q ih =>
      apply ih
      by_contra h
      exact b'.prop (hbound a' hs b' h e)
  obtain ⟨q⟩ := (conn B hsmall) u v
  exact haa (walk_closed q hxa)

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

def FlankIndices {a b : V} (p : G.Walk a b) (x : V) : Finset ℕ :=
  (Pins p x).image (·-1) ∪ (Pins p x).image (·+1)

def FlankVertices {a b : V} (p : G.Walk a b) (x : V) : Finset V :=
  (FlankIndices p x).image p.getVert

def PinVertices {a b : V} (p : G.Walk a b) (x : V) : Finset V :=
  (Pins p x).image p.getVert

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

private theorem nonconsecutive_boundary (hp : IsLongest p) (hx : x ∉ p.support)
    {i : ℕ} (hi : i < p.length) (left : p.getVert i ∈ External G (OmittedStar p x)) :
    p.getVert (i+1) ∉ External G (OmittedStar p x) := by
  intro right
  obtain ⟨_,y,hy,hyl⟩ := mem_external.mp left
  obtain ⟨_,z,hz,hzr⟩ := mem_external.mp right
  obtain ⟨w,wp,ws⟩ := walk_in_star p hx (mem_omittedStar.mp hy) (mem_omittedStar.mp hz)
  obtain ⟨q,hq,ql,_⟩ := splice_walk p hp.1 w wp ws i hi hyl.symm hzr
  have m := hp.2 a b q hq
  omega

private theorem pin_vertices_subset_boundary (hx : x ∉ p.support) :
    PinVertices p x ⊆ External G (OmittedStar p x) := by
  intro z hz
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
  exact mem_external.mpr
    ⟨fun e => (mem_omittedStar.mp e).1 (p.getVert_mem_support i),x,mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩,(pin_data hi).2⟩

/-- Every path flank of every pin is at distance two from the omitted
vertex and is outside its omitted-star boundary. -/
theorem flanks_outside_boundary (hc : G.Connected) (hp : IsLongest p) (hx : x ∉ p.support) :
    FlankVertices p x ⊆ DistanceTwo G x \ External G (OmittedStar p x) := by
  intro z hz
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
  have star : x ∈ OmittedStar p x := mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have na (i : ℕ) (nb : p.getVert i ∉ External G (OmittedStar p x)) : ¬G.Adj x (p.getVert i) :=
    fun e => nb (mem_external.mpr ⟨fun h => (mem_omittedStar.mp h).1 (p.getVert_mem_support i),x,star,e⟩)
  have nei (i : ℕ) : x ≠ p.getVert i := fun e => hx (e ▸ p.getVert_mem_support i)
  rcases mem_union.mp hi with h|h
  · obtain ⟨j,hj,rfl⟩ := mem_image.mp h
    change p.getVert (j-1) ∈ _
    have pos := pin_pos hp hx hj
    have upper := (pin_data hj).1
    have jshift : j-1+1=j := by omega
    have Bj := pin_vertices_subset_boundary hx (mem_image.mpr ⟨j,hj,rfl⟩)
    have no : p.getVert (j-1) ∉ External G (OmittedStar p x) := by
      intro h
      have h' := nonconsecutive_boundary hp hx (show j-1<p.length by omega) h
      rw [jshift] at h'
      exact h' Bj
    have e := p.adj_getVert_succ (i:=j-1) (by omega)
    rw [jshift] at e
    exact mem_sdiff.mpr ⟨mem_distanceTwo.mpr
      (dist_two hc (nei _) (na _ no) (pin_data hj).2 e.symm),no⟩
  · obtain ⟨j,hj,rfl⟩ := mem_image.mp h
    change p.getVert (j+1) ∈ _
    have Bj := pin_vertices_subset_boundary hx (mem_image.mpr ⟨j,hj,rfl⟩)
    have no := nonconsecutive_boundary hp hx (pin_data hj).1 Bj
    exact mem_sdiff.mpr ⟨mem_distanceTwo.mpr
      (dist_two hc (nei _) (na _ no) (pin_data hj).2 (p.adj_getVert_succ (pin_data hj).1)),no⟩

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

/-- Exact additive slack inequality, useful below the near-connectivity range. -/
theorem boundary_flank_count (hc : G.Connected) (hp : IsLongest p) (hx : x ∉ p.support) :
    (External G (OmittedStar p x)).card + (FlankIndices p x).card ≤
      (DistanceTwo G x).card + (Pins p x).card := by
  let A := OmittedStar p x
  let B := External G A
  let F := PinVertices p x
  let S := FlankVertices p x
  have sf := flanks_outside_boundary hc hp hx
  have sb : S ⊆ DistanceTwo G x := fun _ hz => (mem_sdiff.mp (sf hz)).1
  have ds : Disjoint S (B \ F) := by
    rw [disjoint_left]
    exact fun _ h h' => (mem_sdiff.mp (sf h)).2 (mem_sdiff.mp h').1
  have cap := card_le_card (union_subset sb (boundary_except_pins_two hc hp hx))
  rw [card_union_of_disjoint ds,cardinal_flankVertices hp] at cap
  have add := card_sdiff_add_card_eq_card (pin_vertices_subset_boundary hx)
  rw [card_pinVertices hp] at add
  change (B \ F).card + (Pins p x).card = B.card at add
  change B.card + (FlankIndices p x).card ≤ (DistanceTwo G x).card + (Pins p x).card
  omega

#print axioms boundary_flank_count

/-- The first pin of each maximal run with gap two. -/
def FirstPins {a b : V} (p : G.Walk a b) (x : V) : Finset ℕ :=
  (Pins p x).filter fun i => ∀ j∈Pins p x, j+2≠i

/-- Pins belonging to at least one pair at gap two. -/
def PairedPins {a b : V} (p : G.Walk a b) (x : V) : Finset ℕ :=
  (Pins p x).filter fun i => ∃ j∈Pins p x, j+2=i ∨ i+2=j

/-- The number of flanks equals the pin count plus the gap-two run count. -/
theorem flank_count_exact (hp : IsLongest p) (hx : x ∉ p.support) :
    (FlankIndices p x).card = (Pins p x).card + (FirstPins p x).card := by
  let I := Pins p x
  let P := I.image (·-1)
  let S := I.image (·+1)
  let F := FirstPins p x
  have eq : P \ S = F.image (·-1) := by
    ext n
    constructor
    · intro hn
      obtain ⟨pred,no⟩ := mem_sdiff.mp hn
      obtain ⟨i,hi,e⟩ := mem_image.mp pred
      refine mem_image.mpr ⟨i,mem_filter.mpr ⟨hi,?_⟩,e⟩
      intro j hj eq
      apply no
      change i-1=n at e
      exact mem_image.mpr ⟨j,hj,by omega⟩
    · intro hn
      obtain ⟨i,hi,e⟩ := mem_image.mp hn
      have ⟨hiI,hif⟩ := mem_filter.mp hi
      refine mem_sdiff.mpr ⟨mem_image.mpr ⟨i,hiI,e⟩,?_⟩
      intro bad
      obtain ⟨j,hj,e'⟩ := mem_image.mp bad
      change i-1=n at e
      change j+1=n at e'
      exact hif j hj (by omega)
  have pc : (F.image (·-1)).card = F.card := by
    apply card_image_iff.mpr
    intro i hi j hj e
    have h₁ := pin_pos hp hx (mem_filter.mp hi).1
    have h₂ := pin_pos hp hx (mem_filter.mp hj).1
    change i-1=j-1 at e
    omega
  have sc : S.card=I.card := by
    apply card_image_iff.mpr
    intro i hi j hj e
    change i+1=j+1 at e
    omega
  have E : FlankIndices p x = (P \ S) ∪ S := by
    change P ∪ S = (P \ S) ∪ S
    exact Finset.sdiff_union_self_eq_union.symm
  rw [E,card_union_of_disjoint (by rw [disjoint_left]; exact fun _ h h' => (mem_sdiff.mp h).2 h'),eq,pc,sc]
  change F.card+I.card=I.card+F.card
  omega

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

private theorem boundary_lower (k : ℕ) (hp : IsLongest p) (hx : x ∉ p.support)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected) :
    k ≤ (External G (OmittedStar p x)).card := by
  let A := OmittedStar p x
  let B := External G A
  have hxA : x∈A := mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have aA : a∉A := fun e => (mem_omittedStar.mp e).1 p.start_mem_support
  have aB : a∉B := by
    intro e
    obtain ⟨_,z,hz,za⟩ := mem_external.mp e
    exact (no_endpoints hp (mem_omittedStar.mp hz).1).1 za
  have hd : Disjoint A B := by
    rw [disjoint_left]
    exact fun _ h h' => (mem_external.mp h').1 h
  exact boundary_card_of_connectivity k conn hxA aA aB hd
    (fun y hy z hz e => mem_external.mpr ⟨hz,y,hy,e⟩)

private theorem smaller_boundary_after_removing_porter (k : ℕ) (hp : IsLongest p) (hx : x ∉ p.support)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {y : V} (hy : y∉p.support) (xy : G.Adj x y) :
    k + (PairedPins p x).card ≤ (External G (OmittedStar p x)).card+1 := by
  let A := OmittedStar p x
  let B := External G A
  let A' := A.erase x
  let E := (PairedPins p x).image p.getVert
  let B' := insert x (B \ E)
  have xA : x∈A := mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have xB : x∉B := fun h => (mem_external.mp h).1 xA
  have yA : y∈A' := mem_erase.mpr ⟨xy.ne.symm,mem_omittedStar.mpr ⟨hy,Or.inr xy⟩⟩
  have aA : a∉A' := fun e => (mem_omittedStar.mp (mem_erase.mp e).2).1 p.start_mem_support
  have aB : a∉B' := by
    intro h
    rcases mem_insert.mp h with e|h
    · exact hx (e ▸ p.start_mem_support)
    · obtain ⟨_,w,hw,wa⟩ := mem_external.mp (mem_sdiff.mp h).1
      exact (no_endpoints hp (mem_omittedStar.mp hw).1).1 wa
  have hd : Disjoint A' B' := by
    rw [disjoint_left]
    intro z za zb
    obtain ⟨e,az⟩ := mem_erase.mp za
    rcases mem_insert.mp zb with ev|v
    · exact e ev
    · exact (mem_external.mp (mem_sdiff.mp v).1).1 az
  have Esub : E⊆B := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hw
    exact pin_vertices_subset_boundary hx (mem_image.mpr ⟨j,(mem_filter.mp hj).1,rfl⟩)
  have bd : ∀ z∈A', ∀ w∉A', G.Adj z w → w∈B' := by
    intro z hz w hw e
    by_cases eq : w=x
    · exact mem_insert.mpr (Or.inl eq)
    have wA : w∉A := fun h => hw (mem_erase.mpr ⟨eq,h⟩)
    have wb : w∈B := mem_external.mpr ⟨wA,z,(mem_erase.mp hz).2,e⟩
    have we : w∉E := by
      intro zz
      obtain ⟨i,hi,rfl⟩ := mem_image.mp zz
      obtain ⟨n,zA⟩ := mem_erase.mp hz
      obtain ⟨off,e'|adj⟩ := mem_omittedStar.mp zA
      · exact n e'
      · exact exclusive_gap_pin hp hx off adj hi e
    exact mem_insert.mpr (Or.inr (mem_sdiff.mpr ⟨wb,we⟩))
  have low := boundary_card_of_connectivity k conn yA aA aB hd bd
  rw [card_insert_of_not_mem (fun h => xB (mem_sdiff.mp h).1)] at low
  have es : E.card=(PairedPins p x).card := by
    apply card_image_iff.mpr
    intro i hi j hj e
    exact hp.1.getVert_injOn (pin_data (mem_filter.mp hi).1).1.le
      (pin_data (mem_filter.mp hj).1).1.le e
  have ds := card_sdiff_add_card_eq_card Esub
  change k+(PairedPins p x).card≤B.card+1
  omega

/-- With a single slot of separator slack, a vertex in a nonsingleton
omitted component has at most two pins, for every degree threshold. -/
theorem at_most_two_pins_with_omitted_neighbor (hc : G.Connected) (k : ℕ)
    (hp : IsLongest p) (hx : x ∉ p.support) (bound : (DistanceTwo G x).card≤k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {y : V} (hy : y∉p.support) (xy : G.Adj x y) :
    (Pins p x).card ≤ 2 := by
  let I := Pins p x
  let P := PairedPins p x
  let F := FirstPins p x
  let B := External G (OmittedStar p x)
  have a₁ := boundary_flank_count hc hp hx
  rw [flank_count_exact hp hx] at a₁
  have a₂ := boundary_lower k hp hx conn
  have a₃ := smaller_boundary_after_removing_porter k hp hx conn hy xy
  have sub : I \ P ⊆ F := by
    intro z hz
    obtain ⟨hi,hn⟩ := mem_sdiff.mp hz
    refine mem_filter.mpr ⟨hi,?_⟩
    intro j hj e
    exact hn (mem_filter.mpr ⟨hi,j,hj,Or.inl e⟩)
  have pI : P⊆I := filter_subset _ _
  have cc := card_sdiff_add_card_eq_card pI
  have cf := card_le_card sub
  change (I \ P).card + P.card = I.card at cc
  change B.card + (I.card+F.card) ≤ (DistanceTwo G x).card+I.card at a₁
  change k ≤ B.card at a₂
  change k+P.card ≤ B.card+1 at a₃
  change (I \ P).card ≤ F.card at cf
  change I.card≤2
  by_contra! ne
  have positive : 0<P.card := by omega
  let m := P.min' (card_pos.mp positive)
  have mP : m∈P := P.min'_mem _
  have mI : m∈I := pI mP
  have mF : m∈F := by
    refine mem_filter.mpr ⟨mI,?_⟩
    intro j hj eq
    have jp : j∈P := mem_filter.mpr ⟨hj,m,mI,Or.inr eq⟩
    have le : m≤j := P.min'_le j jp
    omega
  have mN : m∉I \ P := fun h => (mem_sdiff.mp h).2 mP
  have hh := card_le_card (insert_subset mF sub)
  rw [card_insert_of_not_mem mN] at hh
  change (I \ P).card+1≤F.card at hh
  omega

#print axioms at_most_two_pins_with_omitted_neighbor

/-- Number of ordered edges in the omitted set, used as a tie breaker
among longest paths. -/
def OmittedEdges {a b : V} (p : G.Walk a b) : Finset (V × V) :=
  (univ : Finset (V×V)).filter fun yz => yz.1 ∉ p.support ∧ yz.2 ∉ p.support ∧ G.Adj yz.1 yz.2

def EdgeOptimal {a b : V} (p : G.Walk a b) : Prop :=
  IsLongest p ∧ ∀ u v (q : G.Walk u v), IsLongest q → (OmittedEdges q).card ≤ (OmittedEdges p).card

theorem exists_edgeOptimal (hc : G.Connected) :
    ∃ (a b : V) (p : G.Walk a b), EdgeOptimal p := by
  classical
  obtain ⟨a,b,p,hp⟩ := exists_longest hc
  let C := Fintype.card (V×V)
  let M := (range (C+1)).filter fun i =>
    ∃ (u v : V) (q : G.Walk u v), IsLongest q ∧ (OmittedEdges q).card=i
  have rangeq {u v : V} (q : G.Walk u v) : (OmittedEdges q).card ∈ range (C+1) := by
    have le : (OmittedEdges q).card ≤ C := card_le_univ _
    exact mem_range.mpr (by omega)
  have mp : (OmittedEdges p).card ∈ M := mem_filter.mpr ⟨rangeq p,a,b,p,hp,rfl⟩
  let n := M.max' ⟨_,mp⟩
  obtain ⟨u,v,q,hq,eq⟩ := (mem_filter.mp (M.max'_mem ⟨_,mp⟩)).2
  refine ⟨u,v,q,hq,fun s t r hr => ?_⟩
  rw [eq]
  exact M.le_max' _ (mem_filter.mpr ⟨rangeq r,s,t,r,hr,rfl⟩)

/-- With the omitted-edge tie breaker, an isolated omitted vertex has
no pair of pins at gap two. -/
theorem singleton_has_no_gap_two_pairs (hc : G.Connected) (d : ℕ)
    (bound : ∀ z, (DistanceTwo G z).card ≤ d)
    (degree : ∀ u v : V, u≠v → d≤G.degree u ∨ d≤G.degree v)
    (hp : EdgeOptimal p) (hx : x ∉ p.support)
    (isolated : ∀ y, G.Adj x y → y∈p.support) :
    (PairedPins p x) = ∅ := by
  classical
  apply eq_empty_iff_forall_not_mem.mpr
  intro i hi
  obtain ⟨hi,j,hj,edges⟩ := mem_filter.mp hi
  obtain ⟨m,hm,hm2⟩ : ∃ m, m∈Pins p x ∧ m+2∈Pins p x := by
    rcases edges with e|e
    · exact ⟨j,hj,e.symm ▸ hi⟩
    · exact ⟨i,hi,e.symm ▸ hj⟩
  have cap := bound x
  have small := degree_lt_distanceTwo_of_omitted_isolated hc hp.1 hx isolated ⟨_,(pin_data hm).2⟩
  have low : ¬ d ≤ G.degree x := by omega
  have il := (pin_data hm2).1
  let z := p.getVert (m+1)
  have zp : z ∈ p.support := p.getVert_mem_support _
  have xz : x≠z := fun e => hx (e.symm ▸ zp)
  have qoff : ∀ w ∈ (Walk.nil : G.Walk x x).support, w ∉ p.support := by simpa using hx
  obtain ⟨q,hq,qlen,qs⟩ := splice_gap_two p hp.1.1 (Walk.nil : G.Walk x x) IsPath.nil qoff
    m (by omega) (pin_data hm).2.symm (pin_data hm2).2
  have eq : q.length=p.length := by simpa using qlen
  have hqmax : IsLongest q := ⟨hq,fun a b r hr => eq.symm ▸ hp.1.2 a b r hr⟩
  have zq : z∉q.support := by
    intro h
    rcases (qs z).mp h with h|h
    · exact xz.symm (by simpa using h)
    · exact h.2 rfl
  have xq : x∈q.support := (qs x).mpr (Or.inl (by simp))
  have high := (degree x z xz).resolve_left low
  have adj : ∃ v, G.Adj z v := ⟨p.getVert (m+2),p.adj_getVert_succ (i:=m+1) (by omega)⟩
  have nbs := omitted_has_omitted_neighbor hc hqmax zq high adj (bound z)
  obtain ⟨w,zw,wq⟩ := nbs
  have wz : w≠z := zw.ne.symm
  have wp : w∉p.support := fun h => wq ((qs w).mpr (Or.inr ⟨h,wz⟩))
  have stay {v : V} (vo : v ∉ p.support) (vn : v≠x) : v∉q.support := by
    intro vh
    rcases (qs v).mp vh with h|h
    · exact vn (by simpa using h)
    · exact vo h.1
  have sub : OmittedEdges p ⊆ OmittedEdges q := by
    intro uv huv
    obtain ⟨po,qo,e⟩ := (mem_filter.mp huv).2
    have n₁ : uv.1≠x := fun en => qo (isolated _ (en ▸ e))
    have n₂ : uv.2≠x := fun en => po (isolated _ ((en ▸ e).symm))
    exact mem_filter.mpr ⟨mem_univ _,stay po n₁,stay qo n₂,e⟩
  have new : (z,w)∈OmittedEdges q := mem_filter.mpr ⟨mem_univ _,zq,wq,zw⟩
  have notold : (z,w)∉OmittedEdges p := fun h => (mem_filter.mp h).2.1 zp
  have lt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun e => notold (e.symm ▸ new)⟩)
  have contradict := hp.2 a b q hqmax
  omega

/-- All vertices of a longest path chosen with the omitted-edge tie
breaker have at most two pins at connectivity d−2, d≥4. The argument
also excludes omitted singletons when d≥5. -/
theorem at_most_two_pins_one_slack (hc : G.Connected) (k : ℕ) (k₂ : 2≤k)
    (bound : ∀ z, (DistanceTwo G z).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (hp : EdgeOptimal p) (hx : x ∉ p.support) :
    (Pins p x).card≤2 ∧ ((∀ y, G.Adj x y → y∈p.support) → k=2) := by
  by_cases n : ∃ y∉p.support, G.Adj x y
  · obtain ⟨y,hy,xy⟩ := n
    exact ⟨at_most_two_pins_with_omitted_neighbor hc k hp.1 hx (bound x) conn hy xy,
      fun h => (hy (h y xy)).elim⟩
  have singled : ∀ y, G.Adj x y → y∈p.support := by
    intro y e
    by_contra h
    exact n ⟨y,h,e⟩
  have paired := singleton_has_no_gap_two_pairs hc (k+2) bound degree hp hx singled
  have first : FirstPins p x = Pins p x := by
    ext i
    constructor
    · exact fun h => (mem_filter.mp h).1
    · intro hi
      refine mem_filter.mpr ⟨hi,?_⟩
      intro j hj eq
      have ij : i∈PairedPins p x := mem_filter.mpr ⟨hi,j,hj,Or.inl eq⟩
      rw [paired] at ij
      exact not_mem_empty _ ij
  have ff := flanks_outside_boundary hc hp.1 hx
  have cnt := card_le_card (show FlankVertices p x ⊆ DistanceTwo G x from fun z h => (mem_sdiff.mp (ff h)).1)
  rw [cardinal_flankVertices hp.1,flank_count_exact hp.1 hx,first] at cnt
  have star : OmittedStar p x = {x} := by
    ext z
    rw [mem_omittedStar,mem_singleton]
    exact ⟨fun h => h.2.elim id (fun e => (h.1 (singled _ e)).elim),fun e => ⟨e.symm ▸ hx,Or.inl e⟩⟩
  have B : External G (OmittedStar p x) = PinVertices p x := by
    apply Subset.antisymm _ (pin_vertices_subset_boundary hx)
    intro z h
    rw [star] at h
    obtain ⟨_,y,hy,e⟩ := mem_external.mp h
    rw [mem_singleton] at hy
    subst y
    obtain ⟨i,hi,eq⟩ := pin_of_neighbor_mem hp.1 hx (singled z e) e
    exact mem_image.mpr ⟨i,hi,eq⟩
  have low := boundary_lower k hp.1 hx conn
  rw [B,card_pinVertices hp.1] at low
  have cu := bound x
  omega

#print axioms singleton_has_no_gap_two_pairs
#print axioms at_most_two_pins_one_slack

/-- Two pins three or more steps apart leave no unused distance-two
slots when the cap is four: the boundary consists only of those pins,
and the double porter is universal in its omitted component. -/
theorem two_separated_pins_cap_four (hc : G.Connected) (hp : IsLongest p)
    (hx : x ∉ p.support) (few : (Pins p x).card≤2) (cap : (DistanceTwo G x).card≤4)
    {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p x) (gap : i+3≤j) :
    (DistanceTwo G x).card=4 ∧
      External G (OmittedStar p x) = {p.getVert i,p.getVert j} ∧
      ∀ y ∉ p.support, (∃ w : G.Walk x y, ∀ z∈w.support, z∉p.support) → y=x ∨ G.Adj x y := by
  classical
  have ip := pin_pos hp hx hi
  have jp := pin_pos hp hx hj
  have f₁ : i-1≠i+1 := by omega
  have f₂ : i-1≠j-1 := by omega
  have f₃ : i-1≠j+1 := by omega
  have f₄ : i+1≠j-1 := by omega
  have f₅ : i+1≠j+1 := by omega
  have f₆ : j-1≠j+1 := by omega
  have fl : ({i-1,i+1,j-1,j+1} : Finset ℕ) ⊆ FlankIndices p x := by
    intro n hn
    simp only [mem_insert,mem_singleton] at hn
    rcases hn with rfl|rfl|rfl|rfl
    · exact mem_union.mpr (Or.inl (mem_image.mpr ⟨i,hi,rfl⟩))
    · exact mem_union.mpr (Or.inr (mem_image.mpr ⟨i,hi,rfl⟩))
    · exact mem_union.mpr (Or.inl (mem_image.mpr ⟨j,hj,rfl⟩))
    · exact mem_union.mpr (Or.inr (mem_image.mpr ⟨j,hj,rfl⟩))
  have fl₂ : 4≤(FlankIndices p x).card := by
    have e1 : i-1 ∉ ({i+1,j-1,j+1} : Finset ℕ) := by simp [f₁,f₂,f₃]
    have e2 : i+1 ∉ ({j-1,j+1} : Finset ℕ) := fun h =>
      (mem_insert.mp h).elim f₄ (fun h => f₅ (mem_singleton.mp h))
    have e3 : j-1 ∉ ({j+1} : Finset ℕ) := by simp [f₆]
    have c := card_le_card fl
    rw [card_insert_of_not_mem e1,card_insert_of_not_mem e2,card_insert_of_not_mem e3,card_singleton] at c
    exact c
  have fb := flanks_outside_boundary hc hp hx
  have cd := card_le_card (show FlankVertices p x ⊆ DistanceTwo G x from fun _ h => (mem_sdiff.mp (fb h)).1)
  rw [cardinal_flankVertices hp] at cd
  have D : (DistanceTwo G x).card=4 := by omega
  have B := boundary_flank_count hc hp hx
  have sub := pin_vertices_subset_boundary hx
  have full : External G (OmittedStar p x) = PinVertices p x := by
    symm
    apply eq_of_subset_of_card_le sub
    rw [card_pinVertices hp]
    omega
  have I : Pins p x = {i,j} := by
    have sub : ({i,j} : Finset ℕ) ⊆ Pins p x := by
      intro a h
      rcases mem_insert.mp h with rfl|h
      · exact hi
      · rw [mem_singleton] at h
        subst a
        exact hj
    symm
    apply eq_of_subset_of_card_le sub
    have inj : i≠j := by omega
    simpa [inj] using few
  have E : External G (OmittedStar p x) = {p.getVert i,p.getVert j} := by
    rw [full,PinVertices,I,image_insert,image_singleton]
  refine ⟨D,E,?_⟩
  intro y hy r
  obtain ⟨w,hw⟩ := r
  let A := OmittedStar p x
  have start : x∈A := mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have closed {s t : V} (w : G.Walk s t) (hw : ∀ z∈w.support,z∉p.support) (hs : s∈A) : t∈A := by
    induction w with
    | nil => exact hs
    | @cons u v t e w ih =>
      have ha : v∈A := by
        by_cases h : v∈A
        · exact h
        · exfalso
          have vB : v∈External G (OmittedStar p x) := mem_external.mpr ⟨h,u,hs,e⟩
          rw [E] at vB
          rcases mem_insert.mp vB with e'|e'
          · exact hw v (by simp) (e'.symm ▸ p.getVert_mem_support i)
          · exact hw v (by simp) ((mem_singleton.mp e').symm ▸ p.getVert_mem_support j)
      exact ih (fun z hz => hw z (by simp [hz])) ha
  exact (mem_omittedStar.mp (closed w hw start)).2

#print axioms two_separated_pins_cap_four

private theorem first_pins_nonempty {x : V} (h : (Pins p x).Nonempty) :
    (FirstPins p x).Nonempty := by
  let I := Pins p x
  let m := I.min' h
  have hm : m∈I := I.min'_mem h
  refine ⟨m,mem_filter.mpr ⟨hm,?_⟩⟩
  intro j hj eq
  have le : m≤j := I.min'_le j hj
  omega

private theorem first_eq_if_no_pair {x : V} (h : PairedPins p x = ∅) : FirstPins p x = Pins p x := by
  ext i
  constructor
  · exact fun e => (mem_filter.mp e).1
  · intro hi
    refine mem_filter.mpr ⟨hi,?_⟩
    intro j hj eq
    have e : i∈PairedPins p x := mem_filter.mpr ⟨hi,j,hj,Or.inl eq⟩
    rw [h] at e
    exact not_mem_empty _ e

private theorem paired_count_if_double {x : V} (h : (PairedPins p x).Nonempty)
    (size : (Pins p x).card=2) : (PairedPins p x).card=2 := by
  obtain ⟨i,hi⟩ := h
  obtain ⟨ii,j,jj,eg⟩ := mem_filter.mp hi
  have ji : j∈PairedPins p x := mem_filter.mpr ⟨jj,i,ii,eg.symm⟩
  have ne : i≠j := by rcases eg with a|a <;> omega
  have sub : ({i,j}:Finset ℕ) ⊆ PairedPins p x := by
    intro z hz
    rcases mem_insert.mp hz with rfl|hz
    · exact hi
    · rw [mem_singleton] at hz
      subst z
      exact ji
  have lower := card_le_card sub
  have upper := card_le_card (filter_subset
    (fun i => ∃ j∈Pins p x, j+2=i ∨ i+2=j) (Pins p x))
  simp only [card_insert_of_not_mem (show i ∉ ({j}:Finset ℕ) by simpa using ne),card_singleton] at lower
  change (PairedPins p x).card≤(Pins p x).card at upper
  omega

/-- At connectivity at least d−2, a double porter with any omitted
neighbor is saturated and has eccentricity at most three. Its boundary
is of size d−2 for separated pins, or d−1 for a paired pin run. -/
theorem double_porter_saturated_one_slack (hc : G.Connected) (k : ℕ)
    (hp : IsLongest p) (hx : x∉p.support) (size : (Pins p x).card=2)
    (even_cap : (EvenFrom G x).card≤k+3)
    (conn : ∀ S : Finset V, S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {y : V} (hy : y∉p.support) (xy : G.Adj x y) :
    (DistanceTwo G x).card=k+2 ∧ (∀ z, G.dist x z≤3) ∧
      (((PairedPins p x)=∅ ∧ (External G (OmittedStar p x)).card=k) ∨
       ((PairedPins p x).card=2 ∧ (External G (OmittedStar p x)).card=k+1)) := by
  have cap : (DistanceTwo G x).card≤k+2 := distanceTwo_le_of_even (k+2) x even_cap
  have f := boundary_flank_count hc hp hx
  rw [flank_count_exact hp hx,size] at f
  have low := boundary_lower k hp hx conn
  have alt : (DistanceTwo G x).card=k+2 ∧
      (((PairedPins p x)=∅ ∧ (External G (OmittedStar p x)).card=k) ∨
       ((PairedPins p x).card=2 ∧ (External G (OmittedStar p x)).card=k+1)) := by
    by_cases e : (PairedPins p x)=∅
    · rw [first_eq_if_no_pair e,size] at f
      exact ⟨by omega,Or.inl ⟨e,by omega⟩⟩
    · have ec := paired_count_if_double (nonempty_iff_ne_empty.mpr e) size
      have cs := smaller_boundary_after_removing_porter k hp hx conn hy xy
      have one := card_pos.mpr (first_pins_nonempty (card_pos.mp (by omega : 0<(Pins p x).card)))
      exact ⟨by omega,Or.inr ⟨ec,by omega⟩⟩
  refine ⟨alt.1,?_,alt.2⟩
  intro z
  by_contra! hz
  have hd := distanceTwo_add_two_le_even_of_far hc (show 4 ≤ G.dist x z by omega)
  omega

#print axioms double_porter_saturated_one_slack
end Graffiti189LongestPath.OneSlack
