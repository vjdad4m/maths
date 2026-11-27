import SmallSeparator189
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp

namespace Graffiti189LongestPath.Rigidity
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 1500000
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


/-- A ball of radius one around an outside vertex, restricted to the omitted set. -/
def OmittedStar {a b : V} (p : G.Walk a b) (x : V) : Finset V :=
  univ.filter fun z => z ∉ p.support ∧ (z = x ∨ G.Adj x z)

/-- External open neighborhood of a finite vertex set. -/
def External (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : Finset V :=
  univ.filter fun z => z ∉ A ∧ ∃ w ∈ A, G.Adj w z

private lemma mem_omittedStar {a b x z : V} {p : G.Walk a b} :
    z ∈ OmittedStar p x ↔ z ∉ p.support ∧ (z = x ∨ G.Adj x z) := by simp [OmittedStar]

private lemma mem_external {A : Finset V} {z : V} :
    z ∈ External G A ↔ z ∉ A ∧ ∃ w ∈ A, G.Adj w z := by simp [External]

/-- There are exactly two distance-two vertices outside the boundary of
the closed omitted neighborhood of an active vertex. They are the
predecessor and successor of its unique path attachment. -/
theorem rigid_flanks (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) {x : V} (hx : x ∉ p.support)
    {i : ℕ} (hi : i ∈ Pins p x) :
    DistanceTwo G x \ External G (OmittedStar p x) =
      {p.getVert (i-1), p.getVert (i+1)} := by
  classical
  let A := OmittedStar p x
  let B := External G A
  let pin := p.getVert i
  let t := p.getVert (i-1)
  let u := p.getVert (i+1)
  have hxA : x ∈ A := mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have offA {z : V} (hm : z ∈ p.support) : z ∉ A := fun zz => (mem_omittedStar.mp zz).1 hm
  have offB {z : V} (endpt : z = a ∨ z = b) : z ∉ B := by
    intro h
    obtain ⟨_,w,hw,e⟩ := mem_external.mp h
    have hn := no_endpoints hp (mem_omittedStar.mp hw).1
    rcases endpt with rfl|rfl
    · exact hn.1 e
    · exact hn.2 e
  have hdis : Disjoint A B :=
    disjoint_left.mpr (fun _ ha hb => (mem_external.mp hb).1 ha)
  have hB := boundary_card_of_connectivity k conn hxA (offA p.start_mem_support)
    (offB (Or.inl rfl)) hdis (fun y hy z hz e => mem_external.mpr ⟨hz,y,hy,e⟩)
  have noncon (j : ℕ) (hj : j < p.length) (h₁ : p.getVert j ∈ B) : p.getVert (j+1) ∉ B := by
    intro h₂
    obtain ⟨_,y,hy,hya⟩ := mem_external.mp h₁
    obtain ⟨_,z,hz,hza⟩ := mem_external.mp h₂
    obtain ⟨q,hq,hqs⟩ := walk_in_star p hx (mem_omittedStar.mp hy) (mem_omittedStar.mp hz)
    obtain ⟨r,hr,hrlen,_⟩ := splice_walk p hp.1 q hq hqs j hj hya.symm hza
    have hle := hp.2 a b r hr
    omega
  have pind := pin_data hi
  have hip : 0 < i := by
    by_contra h
    have e : i = 0 := Nat.eq_zero_of_not_pos h
    exact (no_endpoints hp hx).1 (by simpa [e] using pind.2)
  have pB : pin ∈ B := mem_external.mpr ⟨offA (p.getVert_mem_support i),x,hxA,pind.2⟩
  have isub : i-1+1=i := by omega
  have tB : t ∉ B := by
    intro h
    have h' := noncon (i-1) (by omega) h
    rw [isub] at h'
    exact h' pB
  have uB : u ∉ B := noncon i pind.1 pB
  have tAdj : G.Adj t pin := by
    have h := p.adj_getVert_succ (i:=i-1) (by omega)
    rwa [isub] at h
  have uAdj : G.Adj pin u := p.adj_getVert_succ pind.1
  have td : t ∈ DistanceTwo G x := by
    apply mem_distanceTwo.mpr
    have hn : x ≠ t := fun e => hx (e ▸ p.getVert_mem_support (i-1))
    apply dist_two hc hn ?_ pind.2 tAdj.symm
    exact fun e => tB (mem_external.mpr ⟨offA (p.getVert_mem_support _),x,hxA,e⟩)
  have ud : u ∈ DistanceTwo G x := by
    apply mem_distanceTwo.mpr
    have hn : x ≠ u := fun e => hx (e ▸ p.getVert_mem_support (i+1))
    apply dist_two hc hn ?_ pind.2 uAdj
    exact fun e => uB (mem_external.mpr ⟨offA (p.getVert_mem_support _),x,hxA,e⟩)
  have tnu : t ≠ u := by
    intro e
    have h := hp.1.getVert_injOn (show i-1 ≤ p.length by omega) (show i+1 ≤ p.length by omega) e
    omega
  have cutd : B.erase pin ⊆ DistanceTwo G x := by
    intro w hw
    obtain ⟨wnp,wb⟩ := mem_erase.mp hw
    obtain ⟨wna,z,hz,ez⟩ := mem_external.mp wb
    have wx : x ≠ w := fun e => wna (e ▸ hxA)
    have nxw : ¬G.Adj x w := by
      intro e
      by_cases h : w ∈ p.support
      · obtain ⟨j,hj,rv⟩ := pin_of_neighbor_mem hp hx h e
        have eq := unique_omitted_pin_at_near_connectivity hc k bound conn degree hp hx j hj i hi
        subst j
        exact wnp rv.symm
      · exact wna (mem_omittedStar.mpr ⟨h,Or.inr e⟩)
    rcases (mem_omittedStar.mp hz).2 with rfl|ez'
    · exact (nxw ez).elim
    · exact mem_distanceTwo.mpr (dist_two hc wx nxw ez' ez)
  change DistanceTwo G x \ B = {t,u}
  have inc : ({t,u} : Finset V) ⊆ DistanceTwo G x \ B := by
    intro z hz
    rcases mem_insert.mp hz with rfl|hz
    · exact mem_sdiff.mpr ⟨td,tB⟩
    · rw [mem_singleton] at hz
      subst z
      exact mem_sdiff.mpr ⟨ud,uB⟩
  symm
  apply eq_of_subset_of_card_le inc
  have ds : Disjoint (DistanceTwo G x \ B) (B.erase pin) :=
    disjoint_left.mpr (fun _ m n => (mem_sdiff.mp m).2 (mem_erase.mp n).2)
  have ad : (DistanceTwo G x \ B) ∪ B.erase pin ⊆ DistanceTwo G x := by
    exact union_subset (fun _ h => (mem_sdiff.mp h).1) cutd
  have cap := distanceTwo_le_of_even (k+1) x (bound x)
  have cutlen := card_erase_add_one pB
  have upto := card_le_card ad
  rw [card_union_of_disjoint ds] at upto
  simp only [card_insert_of_not_mem (show t ∉ ({u} : Finset V) by simpa using tnu),card_singleton]
  omega

#print axioms rigid_flanks

/-- Same-support reordering cannot change the unordered two flanks of a pin. -/
theorem same_support_rigid (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b c e : V} {p : G.Walk a b} {q : G.Walk c e} (hp : IsLongest p) (hq : IsLongest q)
    (same : ∀ z : V, z ∈ p.support ↔ z ∈ q.support)
    {x : V} (hx : x ∉ p.support) {i j : ℕ} (hi : i ∈ Pins p x) (hj : j ∈ Pins q x) :
    ({p.getVert (i-1),p.getVert (i+1)} : Finset V) = {q.getVert (j-1),q.getVert (j+1)} := by
  have star : OmittedStar p x = OmittedStar q x := by
    ext z
    rw [mem_omittedStar,mem_omittedStar,same z]
  have f := rigid_flanks hc k bound conn degree hp hx hi
  have g := rigid_flanks hc k bound conn degree hq (fun h => hx ((same _).mpr h)) hj
  rw [star] at f
  exact f.symm.trans g

omit [Fintype V] in
/-- Distinct path attachments in one omitted component are at least three
steps apart: joining their outside neighbors otherwise extends the path. -/
theorem gap_three_of_linked_pins {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    {i j : ℕ} (hi : i ∈ Pins p x) (hj : j ∈ Pins p y) (hij : i < j)
    (q : G.Walk x y) (hq : q.IsPath) (positive : 0 < q.length)
    (off : ∀ z ∈ q.support, z ∉ p.support) : i+3 ≤ j := by
  have di := pin_data hi
  have dj := pin_data hj
  by_contra! ht
  have eg : j=i+1 ∨ j=i+2 := by omega
  rcases eg with h|h
  · subst j
    obtain ⟨r,hr,hri,_⟩ := splice_walk p hp.1 q hq off i di.1 di.2.symm dj.2
    have lr := hp.2 a b r hr
    omega
  · subst j
    obtain ⟨r,hr,hri,_⟩ := splice_gap_two p hp.1 q hq off i (by omega) di.2.symm dj.2
    have lr := hp.2 a b r hr
    omega

#print axioms same_support_rigid
#print axioms gap_three_of_linked_pins
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private lemma lengths_take_drop {x y : V} (p : G.Walk x y) (n : ℕ) (hn : n ≤ p.length) :
    (p.take n).length = n ∧ (p.drop n).length = p.length - n := by
  induction p generalizing n with
  | nil =>
    have : n=0 := by simpa using hn
    subst n
    exact ⟨rfl,rfl⟩
  | @cons a b c h p ih =>
    cases n with
    | zero => simp [Walk.take,Walk.drop]
    | succ n =>
      have hh : n ≤ p.length := by
        simp only [length_cons] at hn
        omega
      obtain ⟨h₁,h₂⟩ := ih n hh
      simp [Walk.take,Walk.drop,h₁,h₂,Nat.add_sub_add_right]



omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private lemma split_path_edge {a b : V} (p : G.Walk a b) (j : ℕ) (hj : j < p.length) :
    (p.take j).append (.cons (p.adj_getVert_succ hj) (p.drop (j+1))) = p := by
  induction p generalizing j with
  | nil => simp at hj
  | @cons a u b edge p ih =>
    cases j with
    | zero =>
      have h : HEq (p.drop 0) p := by cases p <;> rfl
      simpa [Walk.take,Walk.drop] using h
    | succ j =>
      have hj' : j < p.length := by simpa using hj
      exact congrArg (Walk.cons edge) (ih j hj')

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Pósa rotation at the initial endpoint preserves the vertex set. -/
theorem rotate_start {a b : V} {p : G.Walk a b} (hp : IsLongest p) (j : ℕ) (hj : j < p.length)
    (jump : G.Adj a (p.getVert (j+1))) :
    ∃ q : G.Walk (p.getVert j) b, IsLongest q ∧
      (∀ z : V, z ∈ p.support ↔ z ∈ q.support) ∧
      q.length = p.length ∧ q.getVert j = a ∧ q.getVert (j+1) = p.getVert (j+1) := by
  let l := p.take j
  let r := p.drop (j+1)
  let q := l.reverse.append (.cons jump r)
  have split := split_path_edge p j hj
  have ps : p.support = l.support ++ r.support := by
    conv_lhs => rw [←split]
    simp only [support_append,support_cons,List.tail_cons,l,r]
  have qs : q.support = l.support.reverse ++ r.support := by
    simp only [q,support_append,support_reverse,support_cons,List.tail_cons]
  have qpath : q.IsPath := by
    rw [isPath_def,qs,List.nodup_append]
    have nod := hp.1.support_nodup
    rw [ps,List.nodup_append] at nod
    refine ⟨List.nodup_reverse.mpr nod.1,nod.2.1,?_⟩
    intro u hu hv
    exact nod.2.2 (List.mem_reverse.mp hu) hv
  have qsupport (z : V) : z ∈ p.support ↔ z ∈ q.support := by
    rw [ps,qs]
    simp
  have llen : l.length = j := (lengths_take_drop p j (by omega)).1
  have rlen : r.length = p.length-(j+1) := (lengths_take_drop p (j+1) (by omega)).2
  have qlen : q.length = p.length := by
    simp only [q,length_append,length_reverse,length_cons,llen,rlen]
    omega
  have qmax : IsLongest q := ⟨qpath,fun u v w hw => qlen.symm ▸ hp.2 u v w hw⟩
  refine ⟨q,qmax,qsupport,qlen,?_,?_⟩
  · simp [q,getVert_append,llen]
  · have jj : j+1-j=1 := by omega
    simp [q,getVert_append,llen,jj]

omit [Fintype V] [DecidableEq V] in
theorem start_not_adj_pin_successor {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x ∉ p.support) {i : ℕ} (hi : i ∈ Pins p x) :
    ¬G.Adj a (p.getVert (i+1)) := by
  intro h
  obtain ⟨q,hq,hs,_,_,_⟩ := rotate_start hp i (pin_data hi).1 h
  exact (no_endpoints hq (fun e => hx ((hs _).mpr e))).1 (pin_data hi).2

theorem start_not_adj_pin_of_two_le (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x ∉ p.support) {i : ℕ} (hi : i ∈ Pins p x) (h₂ : 2 ≤ i) :
    ¬G.Adj a (p.getVert i) := by
  intro h
  have hil := (pin_data hi).1
  have isub : i-1+1=i := by omega
  obtain ⟨q,hq,hs,hql,hqa,hqp⟩ := rotate_start hp (i-1) (by omega) (by simpa only [isub] using h)
  rw [isub] at hqp
  have hia : G.Adj x (q.getVert i) := by rw [hqp]; exact (pin_data hi).2
  have hj : i ∈ Pins q x := mem_filter.mpr ⟨mem_range.mpr (by omega),hia⟩
  have hf := same_support_rigid hc k bound conn degree hp hq hs hx hi hj
  have ha : a ∈ ({p.getVert (i-1),p.getVert (i+1)} : Finset V) := by
    rw [hf]
    have e := mem_insert_self (q.getVert (i-1)) ({q.getVert (i+1)} : Finset V)
    simpa only [hqa] using e
  have haa : p.getVert 0 = a := p.getVert_zero
  have clash (j : ℕ) (hj : j ≤ p.length) (pos : 0 < j) (e : p.getVert 0 = p.getVert j) : False := by
    have z := hp.1.getVert_injOn (show 0 ≤ p.length by omega) hj e
    omega
  rcases mem_insert.mp ha with h|h
  · exact clash (i-1) (by omega) (by omega) (haa.trans h)
  · exact clash (i+1) (by omega) (by omega) (haa.trans (mem_singleton.mp h))

#print axioms rotate_start
#print axioms start_not_adj_pin_of_two_le

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem reverse_longest {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    IsLongest p.reverse := ⟨hp.1.reverse,fun u v q hq => by simpa using hp.2 u v q hq⟩

omit [Fintype V] [DecidableEq V] in
private lemma pin_pos {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x ∉ p.support)
    {i : ℕ} (hi : i ∈ Pins p x) : 0 < i := by
  by_contra h
  have e : i=0 := Nat.eq_zero_of_not_pos h
  exact (no_endpoints hp hx).1 (by simpa only [e,getVert_zero] using (pin_data hi).2)

omit [Fintype V] [DecidableEq V] in
private theorem pin_reverse {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x ∉ p.support)
    {i : ℕ} (hi : i ∈ Pins p x) : p.length-i ∈ Pins p.reverse x := by
  have h := (pin_data hi).1
  have hi' := pin_pos hp hx hi
  apply mem_filter.mpr
  constructor
  · rw [mem_range,length_reverse]
    omega
  · rw [getVert_reverse]
    have eq : p.length-(p.length-i)=i := by omega
    rw [eq]
    exact (pin_data hi).2

omit [Fintype V] [DecidableEq V] in
theorem end_not_adj_pin_predecessor {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (hx : x ∉ p.support) {i : ℕ} (hi : i ∈ Pins p x) :
    ¬G.Adj b (p.getVert (i-1)) := by
  have hip := pin_pos hp hx hi
  have hil := (pin_data hi).1
  have h := start_not_adj_pin_successor (reverse_longest hp)
    (by simpa using hx) (pin_reverse hp hx hi)
  rw [getVert_reverse] at h
  have eq : p.length-(p.length-i+1)=i-1 := by omega
  rwa [eq] at h

theorem end_not_adj_pin_of_two_le (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (hx : x ∉ p.support) {i : ℕ} (hi : i ∈ Pins p x) (h₂ : i+2 ≤ p.length) :
    ¬G.Adj b (p.getVert i) := by
  have h := start_not_adj_pin_of_two_le hc k bound conn degree (reverse_longest hp)
    (by simpa using hx) (pin_reverse hp hx hi) (by omega)
  rw [getVert_reverse] at h
  have eq : p.length-(p.length-i)=i := by omega
  rwa [eq] at h

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem not_adj_both_end_marks {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x y : V} (hx : x ∉ p.support) (hy : y ∈ p.support) (attach : G.Adj x y)
    {i : ℕ} (hi : i < p.length) (ha : G.Adj a (p.getVert (i+1))) :
    ¬G.Adj b (p.getVert i) := by
  classical
  intro hb
  obtain ⟨q,hq,hs,hql,_,_⟩ := rotate_start hp i hi ha
  let c := Walk.cons hb q
  have hcy : y ∈ c.support := by
    have : y ∈ q.support := (hs y).mp hy
    simp [c,this]
  let r := c.rotate hcy
  have htail : r.support.tail ~r q.support := by
    simpa only [c,support_cons,List.tail_cons] using (support_rotate c hcy)
  have hl : r.length = q.length+1 := by
    have he := htail.perm.length_eq
    rwa [List.length_tail,length_support,length_support,Nat.add_sub_cancel] at he
  have rn : r.support.tail.Nodup := htail.nodup_iff.mpr hq.1.support_nodup
  have rx : x ∉ r.support.tail := fun h => hx ((hs x).mpr (htail.mem_iff.mp h))
  generalize hr : r = r' at hl rn rx
  cases r' with
  | nil => simp at hl
  | cons edge w =>
    have wp : w.IsPath := (isPath_def _).mpr (by simpa only [support_cons,List.tail_cons] using rn)
    have xo : x ∉ w.support := rx
    have wl : w.length = p.length := by simp only [length_cons,hql] at hl; omega
    have ex := hp.2 x _ (.cons attach w.reverse)
      (wp.reverse.cons (by simpa using xo))
    simp [wl] at ex

#print axioms end_not_adj_pin_of_two_le
#print axioms not_adj_both_end_marks

private def LeftMarks {a b : V} (p : G.Walk a b) : Finset ℕ :=
  (range p.length).filter fun i => G.Adj a (p.getVert (i+1))

private def RightMarks {a b : V} (p : G.Walk a b) : Finset ℕ :=
  (range p.length).filter fun i => G.Adj b (p.getVert i)

private theorem card_leftMarks {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    (LeftMarks p).card = G.degree a := by
  classical
  have eq : (LeftMarks p).image (fun i => p.getVert (i+1)) = G.neighborFinset a := by
    ext z
    rw [G.mem_neighborFinset,mem_image]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact (mem_filter.mp hi).2
    · intro e
      have zs : z ∈ p.support := by
        by_contra h
        exact (no_endpoints hp h).1 e.symm
      obtain ⟨i,ei,il⟩ := mem_support_iff_exists_getVert.mp zs
      have ip : 0<i := by
        by_contra h
        have he : i=0 := by omega
        rw [he,getVert_zero] at ei
        exact e.ne ei
      have iq : i-1+1=i := by omega
      exact ⟨i-1,mem_filter.mpr ⟨mem_range.mpr (by omega),by rwa [iq,ei]⟩,by rwa [iq]⟩
  have inj : ((LeftMarks p).image (fun i => p.getVert (i+1))).card = (LeftMarks p).card := by
    apply card_image_iff.mpr
    intro i hi j hj e
    have il := mem_range.mp (mem_filter.mp hi).1
    have jl := mem_range.mp (mem_filter.mp hj).1
    have h := hp.1.getVert_injOn (show i+1≤p.length by omega) (show j+1≤p.length by omega) e
    omega
  rw [eq,card_neighborFinset_eq_degree] at inj
  exact inj.symm

private theorem card_rightMarks {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    (RightMarks p).card = G.degree b := by
  classical
  have eq : (RightMarks p).image p.getVert = G.neighborFinset b := by
    ext z
    rw [G.mem_neighborFinset,mem_image]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact (mem_filter.mp hi).2
    · intro e
      have zs : z ∈ p.support := by
        by_contra h
        exact (no_endpoints hp h).2 e.symm
      obtain ⟨i,ei,il⟩ := mem_support_iff_exists_getVert.mp zs
      have ip : i < p.length := by
        by_contra h
        have he : i=p.length := by omega
        rw [he,getVert_length] at ei
        exact e.ne ei
      exact ⟨i,mem_filter.mpr ⟨mem_range.mpr ip,by rwa [ei]⟩,ei⟩
  have inj : ((RightMarks p).image p.getVert).card = (RightMarks p).card := by
    apply card_image_iff.mpr
    intro i hi j hj e
    have il := mem_range.mp (mem_filter.mp hi).1
    have jl := mem_range.mp (mem_filter.mp hj).1
    exact hp.1.getVert_injOn il.le jl.le e
  rw [eq,card_neighborFinset_eq_degree] at inj
  exact inj.symm

/-- There are two unused endpoint-indices for each separated pin, except
possibly the first and last index. -/
theorem endpoint_marks_bound (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (I : Finset ℕ) (non : I.Nonempty)
    (active : ∀ i ∈ I, ∃ x, x ∉ p.support ∧ i ∈ Pins p x)
    (sep : ∀ i ∈ I, ∀ j ∈ I, i < j → i+2 ≤ j) :
    G.degree a + G.degree b + 2*I.card ≤ p.length+2 := by
  classical
  let L := LeftMarks p
  let R := RightMarks p
  have ip (i : ℕ) (hi : i ∈ I) : 0<i ∧ i<p.length := by
    obtain ⟨x,hx,h⟩ := active i hi
    exact ⟨pin_pos hp hx h,(pin_data h).1⟩
  let J := I.image (·-1)
  have JC : J.card = I.card := by
    apply card_image_iff.mpr
    intro i hi j hj e
    have := (ip i hi).1
    change i-1=j-1 at e
    have := (ip j hj).1
    omega
  have IJ : Disjoint I J := by
    rw [disjoint_left]
    intro i hi h
    obtain ⟨j,hj,e⟩ := mem_image.mp h
    have := (ip j hj).1
    change j-1=i at e
    have ds := sep i hi j hj (by omega)
    omega
  let U := I ∪ J
  let T := (U.erase 0).erase (p.length-1)
  have UC : U.card = 2*I.card := by
    rw [card_union_of_disjoint IJ,JC]
    omega
  have TC : U.card ≤ T.card+2 := by
    have h (S : Finset ℕ) (i : ℕ) : S.card ≤ (S.erase i).card+1 := by
      by_cases hi : i ∈ S
      · rw [card_erase_add_one hi]
      · rw [erase_eq_of_not_mem hi]
        omega
    have a₁ := h U 0
    have a₂ : (U.erase 0).card ≤ T.card+1 := h (U.erase 0) (p.length-1)
    omega
  have disLR : Disjoint L R := by
    rw [disjoint_left]
    intro i h₁ h₂
    obtain ⟨j,hj⟩ := non
    obtain ⟨x,hx,ha⟩ := active j hj
    have di := mem_filter.mp h₁
    exact not_adj_both_end_marks hp hx (p.getVert_mem_support j) (pin_data ha).2
      (mem_range.mp di.1) di.2 (mem_filter.mp h₂).2
  have Tdata (i : ℕ) (hi : i ∈ T) : i ≠ 0 ∧ i ≠ p.length-1 ∧ i ∈ U := by
    obtain ⟨last,h⟩ := mem_erase.mp hi
    obtain ⟨zero,hu⟩ := mem_erase.mp h
    exact ⟨zero,last,hu⟩
  have allowed (i : ℕ) (hi : i ∈ T) : i < p.length ∧ i ∉ L ∧ i ∉ R := by
    obtain ⟨n0,nlast,hu⟩ := Tdata i hi
    rcases mem_union.mp hu with hf|hf
    · obtain ⟨x,hx,ha⟩ := active i hf
      have il := (pin_data ha).1
      refine ⟨il,?_,?_⟩
      · exact fun h => start_not_adj_pin_successor hp hx ha (mem_filter.mp h).2
      · exact fun h => end_not_adj_pin_of_two_le hc k bound conn degree hp hx ha
          (by omega) (mem_filter.mp h).2
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp hf
      obtain ⟨x,hx,ha⟩ := active j hj
      have jp := pin_pos hp hx ha
      have jl := (pin_data ha).1
      refine ⟨by omega,?_,?_⟩
      · intro h
        have e := (mem_filter.mp h).2
        have jj : j-1+1=j := by omega
        rw [jj] at e
        exact start_not_adj_pin_of_two_le hc k bound conn degree hp hx ha (by omega) e
      · exact fun h => end_not_adj_pin_predecessor hp hx ha (mem_filter.mp h).2
  have disT : Disjoint (L ∪ R) T := by
    rw [disjoint_left]
    intro x hu ht
    have wh := allowed x ht
    exact (mem_union.mp hu).elim wh.2.1 wh.2.2
  have big : (L ∪ R) ∪ T ⊆ range p.length := by
    intro i hi
    rcases mem_union.mp hi with h|h
    · rcases mem_union.mp h with h|h
      · exact (mem_filter.mp h).1
      · exact (mem_filter.mp h).1
    · exact mem_range.mpr (allowed i h).1
  have card := card_le_card big
  rw [card_union_of_disjoint disT,card_union_of_disjoint disLR,card_range,card_leftMarks hp,card_rightMarks hp] at card
  omega

#print axioms endpoint_marks_bound

/-- An omitted component forces many punctures in the endpoint-index count. -/
theorem component_and_length_bound (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (H : Finset V) (nonH : H.Nonempty)
    (off : ∀ z ∈ H, z ∉ p.support)
    (closed : ∀ z ∈ H, ∀ w ∉ H, G.Adj z w → w ∈ p.support)
    (joined : ∀ x ∈ H, ∀ y ∈ H, ∃ q : G.Walk x y, q.IsPath ∧ ∀ z ∈ q.support, z ∈ H) :
    k+1 ≤ H.card ∧ G.degree a + G.degree b + 2*k ≤ p.length+2 := by
  classical
  let I := (range p.length).filter fun i => ∃ x ∈ H, G.Adj x (p.getVert i)
  have idata (i : ℕ) (hi : i ∈ I) : ∃ x ∈ H, i ∈ Pins p x := by
    obtain ⟨il,x,hx,ha⟩ := mem_filter.mp hi
    exact ⟨x,hx,mem_filter.mpr ⟨il,ha⟩⟩
  let F := I.image p.getVert
  have covers : ∀ z ∈ H, ∀ w ∉ H, G.Adj z w → w ∈ F := by
    intro z hz w hw e
    obtain ⟨i,hi,e'⟩ := pin_of_neighbor_mem hp (off z hz) (closed z hz w hw e) e
    exact mem_image.mpr ⟨i,mem_filter.mpr ⟨(mem_filter.mp hi).1,z,hz,(pin_data hi).2⟩,e'⟩
  have hdis : Disjoint H F := by
    rw [disjoint_left]
    intro z hz hf
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hf
    exact off _ hz (p.getVert_mem_support i)
  have aH : a ∉ H := fun h => off a h p.start_mem_support
  have aF : a ∉ F := by
    intro h
    obtain ⟨i,hi,e⟩ := mem_image.mp h
    obtain ⟨z,hz,hi'⟩ := idata i hi
    have en : G.Adj z a := by rw [←e]; exact (pin_data hi').2
    exact (no_endpoints hp (off z hz)).1 en
  obtain ⟨t,ht⟩ := nonH
  have fcard := boundary_card_of_connectivity k conn ht aH aF hdis covers
  have fsmall : F.card ≤ I.card := card_image_le
  have icard : k ≤ I.card := le_trans fcard fsmall
  have iH : I.card ≤ H.card := by
    let f (i : I) : H := ⟨Classical.choose (idata i i.prop),(Classical.choose_spec (idata i i.prop)).1⟩
    have hf (i : I) : (i : ℕ) ∈ Pins p (f i : V) :=
      (Classical.choose_spec (idata i i.prop)).2
    have inj : Function.Injective f := by
      intro i j e
      have e' : (f i : V) = (f j : V) := congrArg Subtype.val e
      have m : (j : ℕ) ∈ Pins p (f i : V) := e'.symm ▸ hf j
      exact Subtype.ext (unique_omitted_pin_at_near_connectivity hc k bound conn degree hp
        (off (f i) (f i).prop) i (hf i) j m)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f inj
  have hmore : k+1 ≤ H.card := by
    by_contra! hsmall
    have many : 1 < H.card := by omega
    obtain ⟨u,hu,v,hv,uv⟩ := one_lt_card.mp many
    have each (z : V) (hz : z ∈ H) : G.degree z ≤ H.card := by
      let O := (G.neighborFinset z).filter fun w => w ∉ H
      have OS : O.card ≤ 1 := by
        apply card_le_one.mpr
        intro a ha b hb
        obtain ⟨ha₀,ha₁⟩ := mem_filter.mp ha
        obtain ⟨hb₀,hb₁⟩ := mem_filter.mp hb
        have e₁ := (G.mem_neighborFinset _ _).mp ha₀
        have e₂ := (G.mem_neighborFinset _ _).mp hb₀
        obtain ⟨i,hi,ei⟩ := pin_of_neighbor_mem hp (off z hz) (closed z hz a ha₁ e₁) e₁
        obtain ⟨j,hj,ej⟩ := pin_of_neighbor_mem hp (off z hz) (closed z hz b hb₁ e₂) e₂
        have eq := unique_omitted_pin_at_near_connectivity hc k bound conn degree hp (off z hz) i hi j hj
        subst j
        exact ei.symm.trans ej
      have N : G.neighborFinset z ⊆ H.erase z ∪ O := by
        intro w hw
        by_cases wh : w ∈ H
        · exact mem_union.mpr (Or.inl (mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp hw).ne.symm,wh⟩))
        · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hw,wh⟩))
      have c := card_le_card N
      have c' := card_union_le (H.erase z) O
      rw [G.card_neighborFinset_eq_degree] at c
      have hh := card_erase_add_one hz
      omega
    have du := each u hu
    have dv := each v hv
    rcases degree u v uv with h|h <;> omega
  have non : I.Nonempty := card_pos.mp (by omega)
  have active (i : ℕ) (hi : i ∈ I) : ∃ x, x ∉ p.support ∧ i ∈ Pins p x := by
    obtain ⟨x,hx,hd⟩ := idata i hi
    exact ⟨x,off x hx,hd⟩
  have sep (i : ℕ) (hi : i ∈ I) (j : ℕ) (hj : j ∈ I) (lt : i<j) : i+2 ≤ j := by
    obtain ⟨x,hx,hd⟩ := idata i hi
    obtain ⟨y,hy,he⟩ := idata j hj
    have dxy : x ≠ y := by
      intro e
      subst y
      exact (Nat.ne_of_lt lt)
        (unique_omitted_pin_at_near_connectivity hc k bound conn degree hp (off x hx) i hd j he)
    obtain ⟨q,hq,hqs⟩ := joined x hx y hy
    have qpos : 0<q.length := by
      cases q with
      | nil => contradiction
      | cons edge q => simp
    have g := gap_three_of_linked_pins hp hd he lt q hq qpos
      (fun z hz => off z (hqs z hz))
    omega
  have c := endpoint_marks_bound hc k bound conn degree hp I non active sep
  exact ⟨hmore,by omega⟩

#print axioms component_and_length_bound

omit [Fintype V] [DecidableRel G.Adj] in
private theorem outside_edge {a b : V} (p : G.Walk a b) (hc : G.Connected)
    (hn : ∃ x, x ∉ p.support) :
    ∃ x ∉ p.support, ∃ y ∈ p.support, G.Adj x y := by
  obtain ⟨x,hx⟩ := hn
  obtain ⟨q⟩ := hc x a
  have go {x z : V} (q : G.Walk x z) (hx : x ∉ p.support) (hz : z ∈ p.support) :
      ∃ x ∉ p.support, ∃ y ∈ p.support, G.Adj x y := by
    induction q with
    | nil => exact (hx hz).elim
    | @cons u v w e q ih =>
      by_cases hv : v ∈ p.support
      · exact ⟨u,hx,v,hv,e⟩
      · exact ih hv hz
  exact go q hx p.start_mem_support

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_longest (hc : G.Connected) :
    ∃ (a b : V) (p : G.Walk a b), IsLongest p := by
  classical
  let L := (Finset.range (Fintype.card V)).filter fun i =>
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length = i
  obtain ⟨a⟩ := hc.nonempty
  letI : Nonempty V := ⟨a⟩
  have z : 0 ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    Fintype.card_pos, a,a,.nil,IsPath.nil,rfl⟩
  let n := L.max' ⟨0,z⟩
  obtain ⟨u,v,p,hp,he⟩ := (Finset.mem_filter.mp (L.max'_mem ⟨0,z⟩)).2
  refine ⟨u,v,p,hp,fun u' v' q hq => ?_⟩
  rw [he]
  exact L.le_max' _ (Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hq.length_lt, u',v',q,hq,rfl⟩)


omit [DecidableRel G.Adj] in
theorem exists_omitted_component {a b : V} {p : G.Walk a b} {x : V} (hx : x ∉ p.support) :
    ∃ H : Finset V, x ∈ H ∧ H.Nonempty ∧ (∀ z ∈ H, z ∉ p.support) ∧
      (∀ z ∈ H, ∀ w ∉ H, G.Adj z w → w ∈ p.support) ∧
      (∀ y ∈ H, ∀ z ∈ H, ∃ q : G.Walk y z, q.IsPath ∧ ∀ w ∈ q.support, w ∈ H) := by
  classical
  let W : Set V := {x | x ∉ p.support}
  let a₀ : W := ⟨x,hx⟩
  let K := G.induce W
  let H := univ.filter fun y => ∃ h : y ∈ W, K.Reachable a₀ ⟨y,h⟩
  have hH (y : V) : y ∈ H ↔ ∃ h : y ∈ W, K.Reachable a₀ ⟨y,h⟩ := by simp [H]
  have root : x ∈ H := (hH x).mpr ⟨hx,Reachable.rfl⟩
  refine ⟨H,root,⟨x,root⟩,?_,?_,?_⟩
  · intro z hz
    exact Exists.fst ((hH z).mp hz)
  · intro z hz w hw e
    by_contra h
    obtain ⟨hz,reach⟩ := (hH z).mp hz
    have edge : K.Adj ⟨z,hz⟩ ⟨w,h⟩ := e
    exact hw ((hH w).mpr ⟨h,reach.trans edge.reachable⟩)
  · intro y hy z hz
    obtain ⟨hy,ry⟩ := (hH y).mp hy
    obtain ⟨hz,rz⟩ := (hH z).mp hz
    obtain ⟨q,hq⟩ := (ry.symm.trans rz).exists_isPath
    let f : K →g G := ⟨Subtype.val,fun h => h⟩
    refine ⟨q.map f,map_isPath_of_injective Subtype.val_injective hq,?_⟩
    intro w hw
    rw [support_map] at hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    exact (hH (f v)).mpr ⟨v.prop,ry.trans ⟨q.takeUntil v hv⟩⟩

theorem rotate_to_two_high_endpoints (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) {x : V} (hx : x ∉ p.support) :
    ∃ (u v : V) (q : G.Walk u v), IsLongest q ∧
      (∀ z : V, z ∈ p.support ↔ z ∈ q.support) ∧
      k+1 ≤ G.degree u ∧ k+1 ≤ G.degree v := by
  classical
  have alow {a b : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x ∉ p.support) :
      k ≤ G.degree a := by
    have xne : x ≠ a := fun e => hx (e.symm ▸ p.start_mem_support)
    rw [← G.card_neighborFinset_eq_degree]
    apply boundary_card_of_connectivity k conn (x:=a) (a:=x) (A:={a})
    · exact mem_singleton_self _
    · exact fun e => xne (mem_singleton.mp e)
    · exact fun e => (no_endpoints hp hx).1 ((G.mem_neighborFinset _ _).mp e).symm
    · rw [disjoint_left]
      intro z za zb
      rw [mem_singleton] at za
      subst z
      exact G.loopless _ ((G.mem_neighborFinset _ _).mp zb)
    · intro y hy z _ e
      rw [mem_singleton] at hy
      subst y
      exact (G.mem_neighborFinset _ _).mpr e
  have step {a b : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x ∉ p.support)
      (alo : ¬k+1 ≤ G.degree a) (bhi : k+1 ≤ G.degree b) :
      ∃ (u v : V) (q : G.Walk u v), IsLongest q ∧
        (∀ z : V, z ∈ p.support ↔ z ∈ q.support) ∧
        k+1 ≤ G.degree u ∧ k+1 ≤ G.degree v := by
    have lower := alow hp hx
    have mcard := card_leftMarks hp
    obtain ⟨j,hj,hne⟩ : ∃ j ∈ LeftMarks p, j ≠ 0 := by
      by_contra! h
      have sub : LeftMarks p ⊆ {0} := fun j hj => mem_singleton.mpr (h _ hj)
      have cnt := card_le_card sub
      simp only [card_singleton] at cnt
      omega
    have data := mem_filter.mp hj
    have jlt := mem_range.mp data.1
    obtain ⟨q,hq,hs,_,_,_⟩ := rotate_start hp j jlt data.2
    have nej : a ≠ p.getVert j := by
      intro eq
      have e := p.getVert_zero.trans eq
      have bad := hp.1.getVert_injOn (show 0 ≤ p.length by omega) jlt.le e
      omega
    exact ⟨_,_,q,hq,hs,(degree a _ nej).resolve_left alo,bhi⟩
  have ab : a ≠ b := by
    intro he
    subst b
    have eq := (isPath_iff_eq_nil p).mp hp.1
    obtain ⟨u,_,v,_,e⟩ := outside_edge p hc ⟨x,hx⟩
    have pos := hp.2 u v e.toWalk (IsPath.of_adj e)
    simp [eq] at pos
  by_cases al : k+1 ≤ G.degree a
  · by_cases bl : k+1 ≤ G.degree b
    · exact ⟨a,b,p,hp,fun _ => Iff.rfl,al,bl⟩
    · obtain ⟨u,v,q,hq,hs,uh,vh⟩ := step (reverse_longest hp) (by simpa using hx) bl al
      exact ⟨u,v,q,hq,fun z => by simpa only [support_reverse,List.mem_reverse] using hs z,uh,vh⟩
  · exact step hp hx al ((degree a b ab).resolve_left al)

/-- If #189 failed at connectivity at least d−1 (d≥3), it would have
at least 5d−3 vertices. Here d = k+1. -/
theorem nontraceable_order_lower_bound (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    (fail : ¬ ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ v, v ∈ p.support) :
    5*k+2 ≤ Fintype.card V := by
  classical
  obtain ⟨a,b,p,hp⟩ := exists_longest hc
  obtain ⟨x,hx⟩ : ∃ x, x ∉ p.support := not_forall.mp (fun h => fail ⟨a,b,p,hp.1,h⟩)
  obtain ⟨u,v,q,hq,qq,du,dv⟩ := rotate_to_two_high_endpoints hc k k₂ conn degree hp hx
  obtain ⟨H,_,Hne,Hoff,Hclosed,Hcon⟩ := exists_omitted_component (fun h => hx ((qq x).mpr h))
  have ⟨hH,hl⟩ := component_and_length_bound hc k k₂ bound conn degree hq H Hne Hoff Hclosed Hcon
  have dis : Disjoint H q.support.toFinset := by
    rw [disjoint_left]
    intro z hz ht
    exact Hoff z hz (List.mem_toFinset.mp ht)
  have cnt : (H ∪ q.support.toFinset).card ≤ Fintype.card V :=
    card_le_univ _
  rw [card_union_of_disjoint dis,List.toFinset_card_of_nodup hq.1.support_nodup,length_support] at cnt
  omega

#print axioms nontraceable_order_lower_bound

/-- A component of the graph induced by vertices omitted by the path. -/
structure OmittedComponent {a b : V} (p : G.Walk a b) where
  vertices : Finset V
  nonempty : vertices.Nonempty
  off : ∀ z ∈ vertices, z ∉ p.support
  closed : ∀ z ∈ vertices, ∀ w ∉ vertices, G.Adj z w → w ∈ p.support
  joined : ∀ x ∈ vertices, ∀ y ∈ vertices, ∃ q : G.Walk x y, q.IsPath ∧ ∀ z ∈ q.support, z ∈ vertices

def componentPins {a b : V} {p : G.Walk a b} (H : OmittedComponent p) : Finset V :=
  p.support.toFinset.filter fun w => ∃ x ∈ H.vertices, G.Adj x w

omit [Fintype V] in
lemma componentPins_card {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (H : OmittedComponent p) (k : ℕ)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected) :
    k ≤ (componentPins H).card := by
  obtain ⟨x,hx⟩ := H.nonempty
  apply boundary_card_of_connectivity k conn hx (fun h => H.off a h p.start_mem_support)
  · intro h
    obtain ⟨_,w,hw,e⟩ := mem_filter.mp h
    exact (no_endpoints hp (H.off w hw)).1 e
  · rw [disjoint_left]
    intro z hz hz'
    exact H.off z hz (List.mem_toFinset.mp (mem_filter.mp hz').1)
  · intro z hz w hw e
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr (H.closed z hz w hw e),z,hz,e⟩

private theorem pin_neighbors_unique (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b x s t : V} {p : G.Walk a b} (hp : IsLongest p)
    (hx : x ∉ p.support) (hs : s ∈ p.support) (ht : t ∈ p.support)
    (as : G.Adj x s) (at' : G.Adj x t) : s=t := by
  obtain ⟨i,hi,ei⟩ := pin_of_neighbor_mem hp hx hs as
  obtain ⟨j,hj,ej⟩ := pin_of_neighbor_mem hp hx ht at'
  have eq := unique_omitted_pin_at_near_connectivity hc k bound conn degree hp hx i hi j hj
  subst j
  exact ei.symm.trans ej

/-- Two disjoint omitted components cannot occur in the saturated range:
their pin sets would have to be both disjoint and joined through the same path flanks. -/
theorem no_disjoint_omitted_components (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (H K : OmittedComponent p) (disj : Disjoint H.vertices K.vertices) : False := by
  classical
  have no_cross {x y : V} (hx : x ∈ H.vertices) (hy : y ∈ K.vertices) : ¬G.Adj x y :=
    fun e => K.off y hy (H.closed x hx y (fun m => disjoint_left.mp disj m hy) e)
  have star_sub {x : V} (hx : x ∈ H.vertices) : OmittedStar p x ⊆ H.vertices := by
    intro w hw
    obtain ⟨off,eq|adj⟩ := mem_omittedStar.mp hw
    · exact eq.symm ▸ hx
    · by_contra hn
      exact off (H.closed x hx w hn adj)
  have no_shared {x y w : V} (hx : x ∈ H.vertices) (hy : y ∈ K.vertices)
      (ws : w ∈ p.support) (ex : G.Adj x w) (ey : G.Adj y w) : False := by
    obtain ⟨i,hi,ei⟩ := pin_of_neighbor_mem hp (H.off x hx) ws ex
    have dxy := dist_two hc (fun e => disjoint_left.mp disj (e ▸ hx) hy)
      (no_cross hx hy) ex ey.symm
    have outB : y ∉ External G (OmittedStar p x) := by
      intro h
      obtain ⟨_,z,hz,e⟩ := mem_external.mp h
      exact no_cross (star_sub hx hz) hy e
    have flank := rigid_flanks hc k bound conn degree hp (H.off x hx) hi
    have h := mem_sdiff.mpr ⟨mem_distanceTwo.mpr dxy,outB⟩
    rw [flank] at h
    rcases mem_insert.mp h with e|e
    · exact K.off y hy (e.symm ▸ p.getVert_mem_support (i-1))
    · exact K.off y hy ((mem_singleton.mp e).symm ▸ p.getVert_mem_support (i+1))
  have chord {x y s t : V} (hx : x ∈ H.vertices) (hy : y ∈ K.vertices)
      (ss : s ∈ p.support) (ts : t ∈ p.support) (xs : G.Adj x s) (yt : G.Adj y t) :
      G.Adj s t := by
    have span := (omitted_attachment_saturates hc k bound conn hp (H.off x hx) ss xs).2 y
    obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist x y
    have short : q.length ≤ 3 := by omega
    match q with
    | .nil => exact (disjoint_left.mp disj hx hy).elim
    | .cons xu .nil => exact (no_cross hx hy xu).elim
    | .cons (v:=u) xu (.cons uy .nil) =>
      by_cases us : u ∈ p.support
      · exact (no_shared hx hy us xu uy.symm).elim
      · have uh : u ∈ H.vertices := by
          by_contra h
          exact us (H.closed x hx u h xu)
        exact (no_cross uh hy uy).elim
    | .cons (v:=u) xu (.cons (v:=v) uv (.cons vy .nil)) =>
      by_cases us : u ∈ p.support <;> by_cases vs : v ∈ p.support
      · have es := pin_neighbors_unique hc k bound conn degree hp (H.off x hx) ss us xs xu
        have et := pin_neighbors_unique hc k bound conn degree hp (K.off y hy) ts vs yt vy.symm
        simpa only [←es,←et] using uv
      · have vk : v ∈ K.vertices := by
          by_contra h
          exact vs (K.closed y hy v h vy.symm)
        exact (no_shared hx vk us xu uv.symm).elim
      · have uh : u ∈ H.vertices := by
          by_contra h
          exact us (H.closed x hx u h xu)
        exact (no_shared uh hy vs uv vy.symm).elim
      · have uh : u ∈ H.vertices := by
          by_contra h
          exact us (H.closed x hx u h xu)
        have vk : v ∈ K.vertices := by
          by_contra h
          exact vs (K.closed y hy v h vy.symm)
        exact (no_cross uh vk uv).elim
    | .cons _ (.cons _ (.cons _ (.cons _ q))) => simp only [length_cons] at short; omega
  have bigH := componentPins_card hp H k conn
  have bigK := componentPins_card hp K k conn
  obtain ⟨s,hs,t,ht,st⟩ := one_lt_card.mp (show 1 < (componentPins H).card by omega)
  obtain ⟨u,hu⟩ := card_pos.mp (show 0 < (componentPins K).card by omega)
  obtain ⟨ss,x,hx,xs⟩ := mem_filter.mp hs
  obtain ⟨ts,y,hy,yt⟩ := mem_filter.mp ht
  obtain ⟨us,z,hz,zu⟩ := mem_filter.mp hu
  obtain ⟨i,hi,ei⟩ := pin_of_neighbor_mem hp (H.off x hx) (List.mem_toFinset.mp ss) xs
  obtain ⟨j,hj,ej⟩ := pin_of_neighbor_mem hp (H.off y hy) (List.mem_toFinset.mp ts) yt
  have ij : i ≠ j := by
    intro e
    subst j
    exact st (ei.symm.trans ej)
  have gap {i j : ℕ} {x y : V} (hx : x ∈ H.vertices) (hy : y ∈ H.vertices)
      (hi : i ∈ Pins p x) (hj : j ∈ Pins p y) (lt : i<j) : i+3≤j := by
    have xy : x ≠ y := by
      intro e
      subst y
      exact (Nat.ne_of_lt lt) (unique_omitted_pin_at_near_connectivity hc k bound conn degree hp
        (H.off x hx) i hi j hj)
    obtain ⟨q,hq,hqs⟩ := H.joined x hx y hy
    have pos : 0 < q.length := by cases q with
      | nil => contradiction
      | cons e p => simp
    exact gap_three_of_linked_pins hp hi hj lt q hq pos (fun x hx => H.off x (hqs x hx))
  have spaced : i+3≤j ∨ j+3≤i := by
    by_cases h : i<j
    · exact Or.inl (gap hx hy hi hj h)
    · exact Or.inr (gap hy hx hj hi (by omega))
  have flank_of {x w : V} {i : ℕ} (hx : x ∈ H.vertices) (hi : i ∈ Pins p x)
      (eq : p.getVert i = w) (xw : G.Adj x w) :
      u ∈ ({p.getVert (i-1),p.getVert (i+1)} : Finset V) := by
    have ha := chord hx hz (eq ▸ p.getVert_mem_support i) (List.mem_toFinset.mp us) xw zu
    have nxu : ¬G.Adj x u := fun e => no_shared hx hz (List.mem_toFinset.mp us) e zu
    have xnu : x ≠ u := fun e => H.off x hx (e.symm ▸ List.mem_toFinset.mp us)
    have du := dist_two hc xnu nxu xw ha
    have bu : u ∉ External G (OmittedStar p x) := by
      intro h
      obtain ⟨_,v,hv,e⟩ := mem_external.mp h
      exact no_shared (star_sub hx hv) hz (List.mem_toFinset.mp us) e zu
    rw [←rigid_flanks hc k bound conn degree hp (H.off x hx) hi]
    exact mem_sdiff.mpr ⟨mem_distanceTwo.mpr du,bu⟩
  have iu := flank_of hx hi ei xs
  have ju := flank_of hy hj ej yt
  have impossible (m n : ℕ) (hm : m=i-1 ∨ m=i+1) (hn : n=j-1 ∨ n=j+1)
      (e : p.getVert m = p.getVert n) : False := by
    have il := (pin_data hi).1
    have jl := (pin_data hj).1
    have eq := hp.1.getVert_injOn (show m ≤ p.length by omega) (show n ≤ p.length by omega) e
    omega
  have flanks (r : ℕ) (hr : u ∈ ({p.getVert (r-1),p.getVert (r+1)} : Finset V)) :
      ∃ m, (m=r-1 ∨ m=r+1) ∧ u=p.getVert m := by
    rcases mem_insert.mp hr with h|h
    · exact ⟨r-1,Or.inl rfl,h⟩
    · exact ⟨r+1,Or.inr rfl,mem_singleton.mp h⟩
  obtain ⟨m,hm,mu⟩ := flanks i iu
  obtain ⟨n,hn,nu⟩ := flanks j ju
  exact impossible m n hm hn (mu.symm.trans nu)

#print axioms no_disjoint_omitted_components


/-- An important rigidity consequence: the graph induced by vertices
not used by a nonspanning longest path is connected. -/
theorem omitted_complement_connected (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) {x : V} (hx : x ∉ p.support) :
    (G.induce {z | z ∉ p.support}).Connected := by
  classical
  let U : Set V := {z | z ∉ p.support}
  let L := G.induce U
  obtain ⟨H,xH,Hn,Ho,Hc,Hj⟩ := exists_omitted_component hx
  let first : OmittedComponent p := ⟨H,Hn,Ho,Hc,Hj⟩
  have all_off (z : V) (hz : z ∉ p.support) : z ∈ H := by
    by_contra h
    obtain ⟨B,zB,Bn,Bo,Bc,Bj⟩ := exists_omitted_component hz
    let second : OmittedComponent p := ⟨B,Bn,Bo,Bc,Bj⟩
    have hd : Disjoint H B := by
      rw [disjoint_left]
      intro w hw hw'
      obtain ⟨q,_,hs⟩ := Bj w hw' z zB
      have follow {s t : V} (r : G.Walk s t) (hs : ∀ w ∈ r.support, w ∈ B)
          (hh : s ∈ H) : t ∈ H := by
        induction r with
        | nil => exact hh
        | @cons u v z e r ih =>
          have vb : v ∈ B := hs v (by simp)
          have vh : v ∈ H := by
            by_contra hn
            exact Bo v vb (Hc u hh v hn e)
          exact ih (fun w hw => hs w (by simp [hw])) vh
      exact h (follow q hs hw)
    exact no_disjoint_omitted_components hc k k₂ bound conn degree hp first second hd
  letI : Nonempty U := ⟨⟨x,hx⟩⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨q,_,hs⟩ := Hj u (all_off u u.prop) v (all_off v v.prop)
  have lift {s t : V} (q : G.Walk s t) (mem : ∀ w ∈ q.support, w ∈ U) :
      L.Walk ⟨s,mem _ q.start_mem_support⟩ ⟨t,mem _ q.end_mem_support⟩ := by
    induction q with
    | nil => exact .nil
    | @cons s w t e q ih =>
      have mt : ∀ z ∈ q.support, z ∈ U := fun z hz => mem z (by simp [hz])
      exact .cons (show L.Adj ⟨s,mem _ (Walk.cons e q).start_mem_support⟩
        ⟨w,mt _ q.start_mem_support⟩ from e) (ih mt)
  exact ⟨lift q (fun w hw => Ho w (hs w hw))⟩

#print axioms omitted_complement_connected
end Graffiti189LongestPath.Rigidity
