import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Max

namespace Graffiti189LongestPath

open SimpleGraph SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}

def IsLongest {a b : V} (p : G.Walk a b) : Prop :=
  p.IsPath ∧ ∀ (u v : V) (q : G.Walk u v), q.IsPath → q.length ≤ p.length

private theorem insert_vertex {x a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∉ p.support) (i : ℕ) (hi : i < p.length)
    (h₀ : G.Adj x (p.getVert i)) (h₁ : G.Adj x (p.getVert (i + 1))) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.length = p.length + 1 ∧
      ∀ y : V, y ∈ q.support ↔ y = x ∨ y ∈ p.support := by
  induction p generalizing i with
  | nil => simp at hi
  | @cons v w z hvw p ih =>
    cases i with
    | zero =>
      have h₀' : G.Adj x v := h₀
      have h₁' : G.Adj x w := by simpa using h₁
      have hx' : x ∉ p.support := fun h => hx (by simp [h])
      have hv : v ∉ p.support := (cons_isPath_iff _ _).1 hp |>.2
      refine ⟨.cons h₀'.symm (.cons h₁' p), (hp.of_cons.cons hx').cons ?_, by simp, ?_⟩
      · simpa [h₀'.ne.symm] using hv
      · intro y
        simp only [support_cons, List.mem_cons]
        tauto
    | succ i =>
      have hi' : i < p.length := by simp at hi; omega
      have hx' : x ∉ p.support := fun h => hx (by simp [h])
      obtain ⟨q, hq, hlen, hsup⟩ := ih hp.of_cons hx' i hi' h₀ h₁
      refine ⟨.cons hvw q, hq.cons ?_, by simp [hlen], ?_⟩
      · rw [hsup]
        exact not_or.mpr ⟨fun e => hx (by simp [e]), (cons_isPath_iff _ _).1 hp |>.2⟩
      · intro y
        simp only [support_cons, List.mem_cons, hsup]
        tauto

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

private theorem no_consecutive {x a b : V} {p : G.Walk a b}
    (hp : IsLongest p) (hx : x ∉ p.support) {i : ℕ} (hi : i < p.length)
    (h₀ : G.Adj x (p.getVert i)) : ¬ G.Adj x (p.getVert (i + 1)) := by
  intro h₁
  obtain ⟨q, hq, hlen, _⟩ := insert_vertex p hp.1 hx i hi h₀ h₁
  have hle := hp.2 a b q hq
  omega

private theorem dist_two {a b c : V} (hconn : G.Connected)
    (hac : a ≠ c) (hna : ¬G.Adj a c) (hab : G.Adj a b) (hbc : G.Adj b c) :
    G.dist a c = 2 := by
  have hu := hconn.one_lt_dist_of_ne_of_not_adj hac hna
  have hl := G.dist_le (Walk.cons hab (Walk.cons hbc .nil))
  simp at hl
  omega

variable [Fintype V]

noncomputable def DistanceTwo (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter fun y => G.dist x y = 2

private theorem mem_distanceTwo {x y : V} :
    y ∈ DistanceTwo G x ↔ G.dist x y = 2 := by
  classical
  simp [DistanceTwo]

variable [DecidableEq V] [DecidableRel G.Adj]

/-- A vertex outside a longest path, all of whose neighbors lie on the path,
has strictly more vertices at distance two than neighbors. -/
theorem degree_lt_distanceTwo_of_omitted_isolated (hconn : G.Connected)
    {x a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (hx : x ∉ p.support) (hnb : ∀ y, G.Adj x y → y ∈ p.support)
    (hne : ∃ y, G.Adj x y) :
    G.degree x < (DistanceTwo G x).card := by
  classical
  let I := (Finset.range p.length).filter fun i => G.Adj x (p.getVert i)
  have data (i : ℕ) (hi : i ∈ I) : i < p.length ∧ G.Adj x (p.getVert i) :=
    ⟨Finset.mem_range.mp (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
  have no_ends := no_endpoints hp hx
  have find_index (y : V) (hy : G.Adj x y) : ∃ i ∈ I, p.getVert i = y := by
    obtain ⟨i, hiy, hil⟩ := Walk.mem_support_iff_exists_getVert.mp (hnb y hy)
    have hilt : i < p.length := by
      by_contra! h
      have eq : i = p.length := by omega
      rw [eq, Walk.getVert_length] at hiy
      exact no_ends.2 (hiy.symm ▸ hy)
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hilt, hiy.symm ▸ hy⟩, hiy⟩
  have hcard : G.degree x ≤ I.card := by
    rw [← G.card_neighborFinset_eq_degree]
    have ht : G.neighborFinset x ⊆ I.image p.getVert := by
      intro y hy
      obtain ⟨i, hi, hiy⟩ := find_index y ((G.mem_neighborFinset x y).mp hy)
      exact Finset.mem_image.mpr ⟨i, hi, hiy⟩
    exact (Finset.card_le_card ht).trans Finset.card_image_le
  obtain ⟨y, hy⟩ := hne
  obtain ⟨i, hi, _⟩ := find_index y hy
  let hI : I.Nonempty := ⟨i, hi⟩
  let m := I.min' hI
  have hm := data m (I.min'_mem hI)
  have hmpos : 0 < m := by
    by_contra h
    have heq : m = 0 := Nat.eq_zero_of_not_pos h
    exact no_ends.1 (by simpa [heq] using hm.2)
  have hnot (j : ℕ) : x ≠ p.getVert j :=
    fun e => hx (e ▸ p.getVert_mem_support j)
  let S := I.image fun j => p.getVert (j + 1)
  have hSsub : S ⊆ DistanceTwo G x := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    have hd := data j hj
    exact mem_distanceTwo.mpr (dist_two hconn (hnot _)
      (no_consecutive hp hx hd.1 hd.2) hd.2 (p.adj_getVert_succ hd.1))
  have hScard : S.card = I.card := by
    apply Finset.card_image_iff.mpr
    intro j hj k hk heq
    have hj' := (data j hj).1
    have hk' := (data k hk).1
    have hn := hp.1.getVert_injOn (show j + 1 ≤ p.length by omega)
      (show k + 1 ≤ p.length by omega) heq
    omega
  let z := p.getVert (m - 1)
  have hpr : m - 1 + 1 = m := by omega
  have hadj : G.Adj z (p.getVert m) := by
    have h := p.adj_getVert_succ (i := m - 1) (by omega)
    simpa only [hpr] using h
  have hnaz : ¬G.Adj x z := by
    intro h
    have hi' : m - 1 < p.length := by omega
    exact no_consecutive hp hx hi' h (by simpa only [hpr] using hm.2)
  have hz : z ∈ DistanceTwo G x :=
    mem_distanceTwo.mpr (dist_two hconn (hnot _) hnaz hm.2 hadj.symm)
  have hzS : z ∉ S := by
    intro hz'
    obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hz'
    have hj' := (data j hj).1
    have hmj : m ≤ j := I.min'_le j hj
    have heq := hp.1.getVert_injOn (show j + 1 ≤ p.length by omega)
      (show m - 1 ≤ p.length by omega) hje
    omega
  have hcard' := Finset.card_le_card (Finset.insert_subset hz hSsub)
  rw [Finset.card_insert_of_not_mem hzS, hScard] at hcard'
  omega

/-- The even-distance bound forces any omitted vertex of degree at least
the bound parameter to have a neighbor outside the longest path. -/
theorem omitted_has_omitted_neighbor (hconn : G.Connected)
    {d : ℕ} {x a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (hx : x ∉ p.support) (hdegree : d ≤ G.degree x) (hne : ∃ y, G.Adj x y)
    (hcap : (DistanceTwo G x).card ≤ d) :
    ∃ y, G.Adj x y ∧ y ∉ p.support := by
  by_contra! h
  have hlt := degree_lt_distanceTwo_of_omitted_isolated hconn hp hx h hne
  omega

noncomputable def EvenFrom (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter fun y => Even (G.dist x y)

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem distanceTwo_le_of_even (d : ℕ) (x : V)
    (hcap : (EvenFrom G x).card ≤ d + 1) : (DistanceTwo G x).card ≤ d := by
  classical
  have h₀ : x ∉ DistanceTwo G x := by simp [DistanceTwo, SimpleGraph.dist_self]
  have hsub : insert x (DistanceTwo G x) ⊆ EvenFrom G x := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hd
    · simp [EvenFrom, SimpleGraph.dist_self]
    · simp [EvenFrom, mem_distanceTwo.mp hd, even_two]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_not_mem h₀] at hle
  omega

/-- Under the premise of conjecture 189, a longest path whose complement is
independent can omit at most one vertex, and every omitted vertex has degree
below the second-smallest degree. -/
theorem independent_complement_of_longest (hconn : G.Connected)
    {d : ℕ} {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (hcap : ∀ v, (EvenFrom G v).card ≤ d + 1)
    (hdegree : ∀ u v, u ≠ v → d ≤ G.degree u ∨ d ≤ G.degree v)
    (hnb : ∀ u v, u ∉ p.support → v ∉ p.support → ¬G.Adj u v) :
    (∀ x, x ∉ p.support → G.degree x < d) ∧
    (∀ u v, u ∉ p.support → v ∉ p.support → u = v) := by
  have hl (x : V) (hx : x ∉ p.support) : G.degree x < d := by
    by_contra! he
    have hxa : x ≠ a := by
      intro h
      exact hx (h.symm ▸ p.start_mem_support)
    have hne : ∃ y, G.Adj x y := by
      obtain ⟨q⟩ := hconn x a
      have hqpos : 0 < q.length := by
        cases q with
        | nil => exact (hxa rfl).elim
        | cons h r => simp
      exact ⟨q.getVert 1, by simpa using q.adj_getVert_succ (i := 0) hqpos⟩
    obtain ⟨y, hy, hy'⟩ := omitted_has_omitted_neighbor hconn hp hx he hne
      (distanceTwo_le_of_even d x (hcap x))
    exact hnb x y hx hy' hy
  refine ⟨hl, ?_⟩
  intro u v hu hv
  by_cases huv : u = v
  · exact huv
  have he := hdegree u v huv
  have hu' := hl u hu
  have hv' := hl v hv
  omega

#print axioms omitted_has_omitted_neighbor
#print axioms independent_complement_of_longest


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


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem extra_predecessor (I : Finset ℕ) (hI : I.Nonempty)
    (i : ℕ) (hi : i ∈ I) (none : ∀ j ∈ I, i+2 ≠ j ∧ j+2 ≠ i)
    (many : ∃ j ∈ I, j ≠ i) :
    ∃ j ∈ I, j ≠ I.min' hI ∧ ∀ k ∈ I, k+1 ≠ j-1 := by
  let m := I.min' hI
  have hm := I.min'_mem hI
  by_cases e : i = m
  · subst i
    obtain ⟨u,hu,hne⟩ := many
    let J := I.erase m
    have ne : J.Nonempty := ⟨u,Finset.mem_erase.mpr ⟨hne,hu⟩⟩
    let j := J.min' ne
    obtain ⟨hjm,hj⟩ := Finset.mem_erase.mp (J.min'_mem ne)
    refine ⟨j,hj,hjm,?_⟩
    intro k hk h
    by_cases ekm : k = m
    · have hbad := (none j hj).1
      omega
    · have hkj := J.min'_le k (Finset.mem_erase.mpr ⟨ekm,hk⟩)
      omega
  · refine ⟨i,hi,e,?_⟩
    intro k hk h
    have hbad := (none k hk).2
    omega

/-- Indices of the neighbors of an omitted vertex along a path. -/
def Pins {a b : V} (p : G.Walk a b) (x : V) : Finset ℕ :=
  (Finset.range p.length).filter fun i => G.Adj x (p.getVert i)

/-- The closed omitted neighborhood of an attachment along a longest path
has external boundary strictly smaller than its distance-two sphere. -/
private theorem small_separator_count_pins (hc : G.Connected)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x y : V} (hx : x ∉ p.support) (hy : y ∈ p.support) (hxy : G.Adj x y) :
    ∃ (A B : Finset V), x ∈ A ∧ a ∉ A ∧ a ∉ B ∧ Disjoint A B ∧
      (∀ y ∈ A, ∀ z ∉ A, G.Adj y z → z ∈ B) ∧ B.card < (DistanceTwo G x).card ∧
      (∀ i ∈ Pins p x, (∃ j ∈ Pins p x, j ≠ i) →
          (∀ j ∈ Pins p x, i+2 ≠ j ∧ j+2 ≠ i) → B.card+2 ≤ (DistanceTwo G x).card) ∧
      (∀ z, z ∈ A ↔ z ∉ p.support ∧ (z = x ∨ G.Adj x z)) ∧
      (∀ z, z ∈ B ↔ z ∉ A ∧ ∃ w ∈ A, G.Adj w z) := by
  classical
  let A := Finset.univ.filter fun z => z ∉ p.support ∧ (z = x ∨ G.Adj x z)
  let B := Finset.univ.filter fun z => z ∉ A ∧ ∃ w ∈ A, G.Adj w z
  have memA (z : V) : z ∈ A ↔ z ∉ p.support ∧ (z = x ∨ G.Adj x z) := by simp [A]
  have memB (z : V) : z ∈ B ↔ z ∉ A ∧ ∃ w ∈ A, G.Adj w z := by simp [B]
  have hxA : x ∈ A := (memA _).mpr ⟨hx,Or.inl rfl⟩
  have notA {z : V} (h : z ∈ p.support) : z ∉ A := fun hh => ((memA _).mp hh).1 h
  have aa : a ∉ A := notA p.start_mem_support
  have noBends (z : V) (hz : z ∈ B) : z ≠ a ∧ z ≠ b := by
    obtain ⟨_,w,hw,h⟩ := (memB _).mp hz
    have he := no_endpoints hp ((memA _).mp hw).1
    exact ⟨fun q => he.1 (q ▸ h),fun q => he.2 (q ▸ h)⟩
  have noBcon (i : ℕ) (hi : i < p.length) (h₀ : p.getVert i ∈ B) :
      p.getVert (i + 1) ∉ B := by
    intro h₁
    obtain ⟨_,u,hu,hu'⟩ := (memB _).mp h₀
    obtain ⟨_,v,hv,hv'⟩ := (memB _).mp h₁
    obtain ⟨q,hq,hs⟩ := walk_in_star p hx ((memA _).mp hu) ((memA _).mp hv)
    obtain ⟨r,hr,hl,_⟩ := splice_walk p hp.1 q hq hs i hi hu'.symm hv'
    have hle := hp.2 a b r hr
    omega
  let I := Pins p x
  let F := I.image p.getVert
  have data (i : ℕ) (hi : i ∈ I) : i < p.length ∧ G.Adj x (p.getVert i) :=
    ⟨Finset.mem_range.mp (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
  have findI {z : V} (hz : z ∈ p.support) (had : G.Adj x z) : ∃ i ∈ I, p.getVert i = z := by
    obtain ⟨i,he,hile⟩ := mem_support_iff_exists_getVert.mp hz
    have hi : i < p.length := by
      by_contra! h
      have e : i = p.length := by omega
      rw [e,getVert_length] at he
      exact (no_endpoints hp hx).2 (he.symm ▸ had)
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,he.symm ▸ had⟩,he⟩
  have FB : F ⊆ B := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact (memB _).mpr ⟨notA (p.getVert_mem_support i),x,hxA,(data i hi).2⟩
  obtain ⟨i,hi,_⟩ := findI hy hxy
  let hI : I.Nonempty := ⟨i,hi⟩
  let m := I.min' hI
  have hm := data m (I.min'_mem hI)
  have hmpos : 0 < m := by
    by_contra h
    have e : m = 0 := Nat.eq_zero_of_not_pos h
    exact (no_endpoints hp hx).1 (by simpa [e] using hm.2)
  have memF (j : ℕ) (hj : j ∈ I) : p.getVert j ∈ F := Finset.mem_image.mpr ⟨j,hj,rfl⟩
  have hne (j : ℕ) : x ≠ p.getVert j := fun h => hx (h ▸ p.getVert_mem_support j)
  let S := I.image fun j => p.getVert (j+1)
  let t := p.getVert (m-1)
  have step (j : ℕ) (hj : j ∈ I) : p.getVert (j+1) ∉ B :=
    noBcon j (data j hj).1 (FB (memF j hj))
  have step2 (j : ℕ) (hj : j ∈ I) : p.getVert (j+1) ∈ DistanceTwo G x := by
    have hna : ¬G.Adj x (p.getVert (j+1)) := fun h => step j hj
      ((memB _).mpr ⟨notA (p.getVert_mem_support _),x,hxA,h⟩)
    exact mem_distanceTwo.mpr (dist_two hc (hne _) hna (data j hj).2 (p.adj_getVert_succ (data j hj).1))
  have hmshift : m-1+1 = m := by omega
  have tB : t ∉ B := by
    intro ht
    have bad := noBcon (m-1) (by omega) ht
    rw [hmshift] at bad
    exact bad (FB (memF m (I.min'_mem hI)))
  have tD : t ∈ DistanceTwo G x := by
    have hna : ¬G.Adj x t := fun h => tB ((memB _).mpr
      ⟨notA (p.getVert_mem_support _),x,hxA,h⟩)
    have h := p.adj_getVert_succ (i:=m-1) (by omega)
    rw [hmshift] at h
    exact mem_distanceTwo.mpr (dist_two hc (hne _) hna hm.2 h.symm)
  have tS : t ∉ S := by
    intro ht
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp ht
    have hj' := (data j hj).1
    have hmj : m ≤ j := I.min'_le j hj
    have e := hp.1.getVert_injOn (show j+1 ≤ p.length by omega)
      (show m-1 ≤ p.length by omega) he
    omega
  have sc : S.card = I.card := by
    apply Finset.card_image_iff.mpr
    intro j hj k hk heq
    have hj' := (data j hj).1
    have hk' := (data k hk).1
    have e := hp.1.getVert_injOn (show j+1 ≤ p.length by omega)
      (show k+1 ≤ p.length by omega) heq
    omega
  have hbsub : B \ F ⊆ DistanceTwo G x := by
    intro z hz
    obtain ⟨hb,hf⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨out,w,hw,haw⟩ := (memB _).mp hb
    have hne' : x ≠ z := fun h => out (h ▸ hxA)
    have noadj : ¬G.Adj x z := by
      intro h
      by_cases hs : z ∈ p.support
      · obtain ⟨j,hj,rfl⟩ := findI hs h
        exact hf (memF j hj)
      · exact out ((memA _).mpr ⟨hs,Or.inr h⟩)
    rcases ((memA _).mp hw).2 with rfl|hw'
    · exact (noadj haw).elim
    · exact mem_distanceTwo.mpr (dist_two hc hne' noadj hw' haw)
  have hSsub : insert t S ⊆ DistanceTwo G x := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|hz
    · exact tD
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
      exact step2 j hj
  have hd : Disjoint (insert t S) (B \ F) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    have hb := (Finset.mem_sdiff.mp hz').1
    rcases Finset.mem_insert.mp hz with rfl|hz
    · exact tB hb
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
      exact step j hj hb
  have cnt := Finset.card_le_card (Finset.union_subset hSsub hbsub)
  rw [Finset.card_union_of_disjoint hd,Finset.card_insert_of_not_mem tS,sc] at cnt
  have fc : F.card ≤ I.card := Finset.card_image_le
  have bc := Finset.card_sdiff_add_card_eq_card FB
  have hbcount : B.card < (DistanceTwo G x).card := by omega
  refine ⟨A,B,hxA,aa,fun h => (noBends a h).1 rfl,?_,?_,hbcount,?_,memA,memB⟩
  · exact Finset.disjoint_left.mpr (fun z ha hz => ((memB _).mp hz).1 ha)
  · exact fun y hy z hz e => (memB _).mpr ⟨hz,y,hy,e⟩
  · intro i hi many none
    have pos (j : ℕ) (hj : j ∈ I) : 0 < j := by
      by_contra h
      have e : j = 0 := Nat.eq_zero_of_not_pos h
      exact (no_endpoints hp hx).1 (by simpa [e] using (data j hj).2)
    obtain ⟨j,hj,hjm,noj⟩ := extra_predecessor I hI i hi none many
    have hpos := pos j hj
    let u := p.getVert (j-1)
    have ju : j-1+1=j := by omega
    have hlu := (data j hj).1
    have hbu : u ∉ B := by
      intro h
      have hn := noBcon (j-1) (by omega) h
      rw [ju] at hn
      exact hn (FB (memF j hj))
    have hdu : u ∈ DistanceTwo G x := by
      have hna : ¬G.Adj x u := fun h => hbu ((memB _).mpr
        ⟨notA (p.getVert_mem_support _),x,hxA,h⟩)
      have h := p.adj_getVert_succ (i:=j-1) (by omega)
      rw [ju] at h
      exact mem_distanceTwo.mpr (dist_two hc (hne _) hna (data j hj).2 h.symm)
    have hu : u ∉ (insert t S) ∪ (B \ F) := by
      intro h
      rcases Finset.mem_union.mp h with h|h
      · rcases Finset.mem_insert.mp h with h|h
        · have e := hp.1.getVert_injOn (show j-1 ≤ p.length by omega)
            (show m-1 ≤ p.length by omega) h
          exact hjm (by omega)
        · obtain ⟨k,hk,he⟩ := Finset.mem_image.mp h
          have hk' := (data k hk).1
          exact noj k hk (hp.1.getVert_injOn (show k+1 ≤ p.length by omega)
            (show j-1 ≤ p.length by omega) he)
      · exact hbu (Finset.mem_sdiff.mp h).1
    have big := Finset.card_le_card (Finset.insert_subset hdu (Finset.union_subset hSsub hbsub))
    rw [Finset.card_insert_of_not_mem hu,Finset.card_union_of_disjoint hd,
      Finset.card_insert_of_not_mem tS,sc] at big
    omega

theorem small_separator_of_omitted_attachment (hc : G.Connected)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x y : V} (hx : x ∉ p.support) (hy : y ∈ p.support) (hxy : G.Adj x y) :
    ∃ (A B : Finset V), x ∈ A ∧ a ∉ A ∧ a ∉ B ∧ Disjoint A B ∧
      (∀ y ∈ A, ∀ z ∉ A, G.Adj y z → z ∈ B) ∧ B.card < (DistanceTwo G x).card := by
  obtain ⟨A,B,h₁,h₂,h₃,h₄,h₅,h₆,_⟩ := small_separator_count_pins hc hp hx hy hxy
  exact ⟨A,B,h₁,h₂,h₃,h₄,h₅,h₆⟩


theorem small_separator_of_nonspanning_longest (hc : G.Connected)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (hn : ∃ x, x ∉ p.support) :
    ∃ (x : V) (A B : Finset V), x ∈ A ∧ a ∉ A ∧ a ∉ B ∧ Disjoint A B ∧
      (∀ y ∈ A, ∀ z ∉ A, G.Adj y z → z ∈ B) ∧ B.card < (DistanceTwo G x).card := by
  classical
  obtain ⟨x,hx,y,hy,hxy⟩ := outside_edge p hc hn
  exact ⟨x,small_separator_of_omitted_attachment hc hp hx hy hxy⟩

#print axioms small_separator_of_nonspanning_longest

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem exists_longest (hc : G.Connected) :
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

/-- A nontraceable finite graph has a vertex cut smaller than one of
its distance-two spheres. This uses the same deletion definition of
connectivity as the companion #199 results. -/
theorem traceable_of_distanceTwo_and_connectivity (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (DistanceTwo G x).card ≤ k)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ v, v ∈ p.support := by
  classical
  obtain ⟨a,b,p,hp⟩ := exists_longest hc
  by_cases h : ∀ v, v ∈ p.support
  · exact ⟨a,b,p,hp.1,h⟩
  have hn : ∃ x, x ∉ p.support := not_forall.mp h
  obtain ⟨x,A,B,hxa,haa,hab,hdis,hbound,hcard⟩ :=
    small_separator_of_nonspanning_longest hc hp hn
  have hsmall : B.card < k := lt_of_lt_of_le hcard (bound x)
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
  exact (haa (walk_closed q hxa)).elim

/-- Graffiti.pc #189 when vertex connectivity is at least the
second-smallest degree. The even count includes distance zero. -/
theorem traceable_of_even_and_connectivity (hc : G.Connected) (d : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ d + 1)
    (conn : ∀ S : Finset V, S.card < d → (G.induce ((↑S : Set V)ᶜ)).Connected) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ v, v ∈ p.support :=
  traceable_of_distanceTwo_and_connectivity hc d (fun x => distanceTwo_le_of_even d x (bound x)) conn

#print axioms traceable_of_distanceTwo_and_connectivity
#print axioms traceable_of_even_and_connectivity

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
private lemma distance_four_of_far (hc : G.Connected) {x y : V} (hy : 4 ≤ G.dist x y) :
    ∃ z, G.dist x z = 4 := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x y
  obtain ⟨h₁,h₂⟩ := lengths_take_drop p 4 (by omega)
  have upper := G.dist_le (p.take 4)
  have lower := hc.dist_triangle (u:=x) (v:=p.getVert 4) (w:=y)
  have suffix := G.dist_le (p.drop 4)
  exact ⟨p.getVert 4,by omega⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem distanceTwo_add_two_le_even_of_far (hc : G.Connected) {x y : V}
    (hy : 4 ≤ G.dist x y) : (DistanceTwo G x).card + 2 ≤ (EvenFrom G x).card := by
  classical
  obtain ⟨z,hz⟩ := distance_four_of_far hc hy
  have h₀ : x ∉ DistanceTwo G x := by simp [DistanceTwo,SimpleGraph.dist_self]
  have h₁ : z ∉ insert x (DistanceTwo G x) := by
    intro h
    rcases Finset.mem_insert.mp h with rfl|h
    · rw [SimpleGraph.dist_self] at hz; omega
    · rw [mem_distanceTwo.mp h] at hz
      contradiction
  have sub : insert z (insert x (DistanceTwo G x)) ⊆ EvenFrom G x := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · simp only [EvenFrom,Finset.mem_filter,Finset.mem_univ,true_and,hz]
      decide
    · rcases Finset.mem_insert.mp ha with rfl|ha
      · simp [EvenFrom,SimpleGraph.dist_self]
      · simp [EvenFrom,mem_distanceTwo.mp ha,even_two]
  have cnt := Finset.card_le_card sub
  rw [Finset.card_insert_of_not_mem h₁,Finset.card_insert_of_not_mem h₀] at cnt
  omega

/-- Graffiti.pc #189 holds at radius ≥ 4 even with vertex connectivity
one smaller than the even-count parameter. -/
theorem traceable_of_even_radius_four (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ k + 2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (radius : ∀ x, ∃ y, 4 ≤ G.dist x y) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ v, v ∈ p.support := by
  apply traceable_of_distanceTwo_and_connectivity hc k _ conn
  intro x
  obtain ⟨y,hy⟩ := radius x
  have h := distanceTwo_add_two_le_even_of_far hc hy
  have hb := bound x
  omega

#print axioms traceable_of_even_radius_four

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private lemma distance_on_geodesic (hc : G.Connected) {x y : V} (p : G.Walk x y)
    (hp : p.length = G.dist x y) (i : ℕ) (hi : i ≤ p.length) :
    G.dist x (p.getVert i) = i := by
  obtain ⟨h₁,h₂⟩ := lengths_take_drop p i hi
  have upper := G.dist_le (p.take i)
  have lower := hc.dist_triangle (u:=x) (v:=p.getVert i) (w:=y)
  have suffix := G.dist_le (p.drop i)
  omega

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem distanceTwo_add_to_even_along_geodesic (hc : G.Connected) (r : ℕ) {x y : V}
    (hy : 2*(r+1) ≤ G.dist x y) : (DistanceTwo G x).card + r + 1 ≤ (EvenFrom G x).card := by
  classical
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x y
  let E := (Finset.range r).image fun i => p.getVert (2*(i+2))
  have dis (i : ℕ) (hi : i ∈ Finset.range r) : G.dist x (p.getVert (2*(i+2))) = 2*(i+2) :=
    distance_on_geodesic hc p hp _ (by have := Finset.mem_range.mp hi; omega)
  have ec : E.card = r := by
    unfold E
    rw [Finset.card_image_iff.mpr ?_,Finset.card_range]
    intro i hi j hj eq
    have h := congrArg (G.dist x) eq
    rw [dis i hi,dis j hj] at h
    omega
  have hx : x ∉ DistanceTwo G x := by simp [DistanceTwo,SimpleGraph.dist_self]
  have dx : Disjoint (insert x (DistanceTwo G x)) E := by
    rw [Finset.disjoint_left]
    intro z hz he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    rcases Finset.mem_insert.mp hz with e|h
    · have eq := congrArg (G.dist x) e
      rw [dis i hi,SimpleGraph.dist_self] at eq
      omega
    · have eq := mem_distanceTwo.mp h
      rw [dis i hi] at eq
      omega
  have sub : (insert x (DistanceTwo G x)) ∪ E ⊆ EvenFrom G x := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · rcases Finset.mem_insert.mp hz with rfl|hz
      · simp [EvenFrom,SimpleGraph.dist_self]
      · simp [EvenFrom,mem_distanceTwo.mp hz,even_two]
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      simp only [EvenFrom,Finset.mem_filter,Finset.mem_univ,true_and,dis i hi]
      exact ⟨i+2,by omega⟩
  have cnt := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dx,Finset.card_insert_of_not_mem hx,ec] at cnt
  omega

/-- A quantitative tradeoff: each positive even distance above two along
a geodesic reduces the connectivity requirement by one. -/
theorem traceable_of_even_and_radius (hc : G.Connected) (k r : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ k + r + 1)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (radius : ∀ x, ∃ y, 2*(r+1) ≤ G.dist x y) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ v, v ∈ p.support := by
  apply traceable_of_distanceTwo_and_connectivity hc k _ conn
  intro x
  obtain ⟨y,hy⟩ := radius x
  have h := distanceTwo_add_to_even_along_geodesic hc r hy
  have hb := bound x
  omega

#print axioms traceable_of_even_and_radius

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem layer_card_of_connectivity (hc : G.Connected) (k : ℕ)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {x y : V} (i : ℕ) (hi : 0 < i) (hy : i < G.dist x y) (dec : DecidablePred (fun z => G.dist x z = i)) :
    k ≤ (Finset.univ.filter fun z => G.dist x z = i).card := by
  by_contra! hsmall
  let S := Finset.univ.filter fun z => G.dist x z = i
  have mS (z : V) : z ∈ S ↔ G.dist x z = i := by simp [S]
  let W : Set V := (↑S : Set V)ᶜ
  let a : W := ⟨x,fun hx => by
    have e := (mS _).mp hx
    rw [SimpleGraph.dist_self] at e
    omega⟩
  let b : W := ⟨y,fun hz => by
    have e := (mS _).mp hz
    omega⟩
  have propagate {u v : W} (p : (G.induce W).Walk u v)
      (hu : G.dist x (u : V) < i) : G.dist x (v : V) < i := by
    induction p with
    | nil => exact hu
    | @cons a' b' c' e p ih =>
      apply ih
      have htri := hc.dist_triangle (u:=x) (v:=(a' : V)) (w:=(b' : V))
      have hdist : G.dist (a' : V) (b' : V) = 1 := dist_eq_one_iff_adj.mpr e
      have hne : G.dist x (b' : V) ≠ i := fun he => b'.prop ((mS _).mpr he)
      omega
  obtain ⟨p⟩ := (conn S hsmall) a b
  have h := propagate p (by simpa [a,SimpleGraph.dist_self] using hi)
  exact (Nat.not_lt_of_ge (Nat.le_of_lt hy)) h

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem twoEvenLayers_of_radius_five (hc : G.Connected) (k : ℕ)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {x y : V} (hy : 5 ≤ G.dist x y) :
    (DistanceTwo G x).card + k + 1 ≤ (EvenFrom G x).card := by
  classical
  let L := Finset.univ.filter fun z => G.dist x z = 4
  have kL : k ≤ L.card := layer_card_of_connectivity hc k conn (x:=x) (y:=y) 4 (by decide) (by omega) _
  have hx : x ∉ DistanceTwo G x := by simp [DistanceTwo,SimpleGraph.dist_self]
  have dx : Disjoint (insert x (DistanceTwo G x)) L := by
    rw [Finset.disjoint_left]
    intro z hz he
    have eql := (Finset.mem_filter.mp he).2
    rcases Finset.mem_insert.mp hz with rfl|h
    · rw [SimpleGraph.dist_self] at eql
      omega
    · have eqd := mem_distanceTwo.mp h
      omega
  have sub : (insert x (DistanceTwo G x)) ∪ L ⊆ EvenFrom G x := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · rcases Finset.mem_insert.mp hz with rfl|hz
      · simp [EvenFrom,SimpleGraph.dist_self]
      · simp [EvenFrom,mem_distanceTwo.mp hz,even_two]
    · have e := (Finset.mem_filter.mp hz).2
      simp only [EvenFrom,Finset.mem_filter,Finset.mem_univ,true_and,e]
      decide
  have cnt := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dx,Finset.card_insert_of_not_mem hx] at cnt
  omega

/-- Graffiti.pc #189 at radius ≥ 5 if twice the vertex connectivity is
at least the second-smallest degree. -/
theorem traceable_of_even_radius_five (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ 2*k + 1)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (radius : ∀ x, ∃ y, 5 ≤ G.dist x y) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ v, v ∈ p.support := by
  apply traceable_of_distanceTwo_and_connectivity hc k _ conn
  intro x
  obtain ⟨y,hy⟩ := radius x
  have h := twoEvenLayers_of_radius_five hc k conn hy
  have hb := bound x
  omega

#print axioms layer_card_of_connectivity
#print axioms traceable_of_even_radius_five

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem innerEvenLayers_of_far (hc : G.Connected) (k r : ℕ)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {x y : V} (hy : 2*(r+1) + 1 ≤ G.dist x y) :
    (DistanceTwo G x).card + r*k + 1 ≤ (EvenFrom G x).card := by
  classical
  let L (i : ℕ) := Finset.univ.filter fun z => G.dist x z = 2*(i+2)
  let R := (Finset.range r).biUnion L
  have memL (i : ℕ) (z : V) : z ∈ L i ↔ G.dist x z = 2*(i+2) := by simp [L]
  have pair : (Finset.range r : Set ℕ).PairwiseDisjoint L := by
    intro i _ j _ hne
    rw [Function.onFun,Finset.disjoint_left]
    intro z hi hj
    have ei := (memL i z).mp hi
    have ej := (memL j z).mp hj
    omega
  have cardL (i : ℕ) (hi : i ∈ Finset.range r) : k ≤ (L i).card := by
    have h := Finset.mem_range.mp hi
    exact layer_card_of_connectivity hc k conn (x:=x) (y:=y) (2*(i+2)) (by omega) (by omega) _
  have cardR : r*k ≤ R.card := by
    unfold R
    rw [Finset.card_biUnion pair]
    calc
      r*k = ∑ _i ∈ Finset.range r, k := by simp
      _ ≤ _ := Finset.sum_le_sum cardL
  have hx : x ∉ DistanceTwo G x := by simp [DistanceTwo,SimpleGraph.dist_self]
  have dx : Disjoint (insert x (DistanceTwo G x)) R := by
    rw [Finset.disjoint_left]
    intro z hz he
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
    have eql := (memL i z).mp hi
    rcases Finset.mem_insert.mp hz with rfl|h
    · rw [SimpleGraph.dist_self] at eql
      omega
    · have eqd := mem_distanceTwo.mp h
      omega
  have sub : (insert x (DistanceTwo G x)) ∪ R ⊆ EvenFrom G x := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · rcases Finset.mem_insert.mp hz with rfl|hz
      · simp [EvenFrom,SimpleGraph.dist_self]
      · simp [EvenFrom,mem_distanceTwo.mp hz,even_two]
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hz
      simp only [EvenFrom,Finset.mem_filter,Finset.mem_univ,true_and,(memL i z).mp hi]
      exact ⟨i+2,by omega⟩
  have cnt := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dx,Finset.card_insert_of_not_mem hx] at cnt
  omega

/-- At radius ≥ 2r+3, the `r` interior even layers after distance two
each consume at least vertex connectivity many spots in the even count. -/
theorem traceable_of_even_many_inner_layers (hc : G.Connected) (k r : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ (r+1)*k + 1)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (radius : ∀ x, ∃ y, 2*(r+1) + 1 ≤ G.dist x y) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ v, v ∈ p.support := by
  apply traceable_of_distanceTwo_and_connectivity hc k _ conn
  intro x
  obtain ⟨y,hy⟩ := radius x
  have h := innerEvenLayers_of_far hc k r conn hy
  have hb := bound x
  rw [Nat.add_mul,one_mul] at hb
  omega

#print axioms traceable_of_even_many_inner_layers

/-- A distance shell is represented by the corresponding finite vertex set. -/
noncomputable def Shell (G : SimpleGraph V) (x : V) (i : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun y => G.dist x y = i

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma mem_shell {x y : V} {i : ℕ} : y ∈ Shell G x i ↔ G.dist x y = i := by
  classical
  simp [Shell]

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma shell_two (x : V) : Shell G x 2 = DistanceTwo G x := rfl

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma shell_card_of_far (hc : G.Connected) (k : ℕ)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {x y : V} {i : ℕ} (hi : 0 < i) (hy : i < G.dist x y) : k ≤ (Shell G x i).card := by
  classical
  exact layer_card_of_connectivity hc k conn (x:=x) (y:=y) i hi hy _

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem third_shell_le (hc : G.Connected) (d : ℕ) (bound : ∀ x, (DistanceTwo G x).card ≤ d) (x : V) :
    (Shell G x 3).card ≤ (Shell G x 2).card * d := by
  classical
  let down := Shell G x 2
  let up (z : V) := (Shell G x 3).filter (G.Adj z)
  have upbound (z : V) (hz : z ∈ down) : (up z).card ≤ d := by
    have hd := mem_shell.mp hz
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x z
    have plen : p.length = 2 := hp.trans hd
    let v := p.getVert 1
    have vd : G.dist x v = 1 := distance_on_geodesic hc p hp 1 (by omega)
    have vz : G.Adj v z := by
      have h := p.adj_getVert_succ (i:=1) (by omega : 1 < p.length)
      have eq : p.getVert 2 = z := by rw [← plen,getVert_length]
      simpa only [eq] using h
    apply le_trans (Finset.card_le_card (t:=DistanceTwo G v) ?_) (bound v)
    intro w hw
    obtain ⟨hw₁,hw₂⟩ := Finset.mem_filter.mp hw
    have wd := mem_shell.mp hw₁
    have hne : v ≠ w := by
      intro h
      rw [← h] at wd
      omega
    have hna : ¬G.Adj v w := by
      intro e
      have ed := dist_eq_one_iff_adj.mpr e
      have tri := hc.dist_triangle (u:=x) (v:=v) (w:=w)
      omega
    exact mem_distanceTwo.mpr (dist_two hc hne hna vz hw₂)
  have cover : Shell G x 3 ⊆ down.biUnion up := by
    intro w hw
    have hd := mem_shell.mp hw
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x w
    have plen : p.length = 3 := hp.trans hd
    let v := p.getVert 2
    have vd : G.dist x v = 2 := distance_on_geodesic hc p hp 2 (by omega)
    have vw : G.Adj v w := by
      have h := p.adj_getVert_succ (i:=2) (by omega : 2 < p.length)
      have eq : p.getVert 3 = w := by rw [← plen,getVert_length]
      simpa only [eq] using h
    exact Finset.mem_biUnion.mpr ⟨v,mem_shell.mpr vd,Finset.mem_filter.mpr ⟨hw,vw⟩⟩
  exact (Finset.card_le_card cover).trans (Finset.card_biUnion_le_card_mul down up d upbound)

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem diameter_at_most_four_of_even_four (hc : G.Connected)
    (bound : ∀ x, (EvenFrom G x).card ≤ 4)
    (conn : ∀ S : Finset V, S.card < 2 → (G.induce ((↑S : Set V)ᶜ)).Connected) :
    ∀ x y, G.dist x y ≤ 4 := by
  intro x y
  by_contra! h
  have ring_two : 2 ≤ (Shell G x 2).card := shell_card_of_far hc 2 conn (by decide) (by omega : 2 < G.dist x y)
  rw [shell_two] at ring_two
  have ring_four := twoEvenLayers_of_radius_five hc 2 conn (show 5 ≤ G.dist x y by omega)
  have ex := bound x
  omega

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem shell_two_four_le_of_even_four {x : V} (hb : (EvenFrom G x).card ≤ 4) :
    (Shell G x 2).card + (Shell G x 4).card ≤ 3 := by
  classical
  have h2 : x ∉ Shell G x 2 := by rw [mem_shell,SimpleGraph.dist_self]; decide
  have dh : Disjoint (insert x (Shell G x 2)) (Shell G x 4) := by
    rw [Finset.disjoint_left]
    intro y hy e
    have e' := mem_shell.mp e
    rcases Finset.mem_insert.mp hy with rfl|h
    · rw [SimpleGraph.dist_self] at e'
      omega
    · have he := mem_shell.mp h
      omega
  have sub : insert x (Shell G x 2) ∪ Shell G x 4 ⊆ EvenFrom G x := by
    intro y hy
    rcases Finset.mem_union.mp hy with h|h
    · rcases Finset.mem_insert.mp h with rfl|ht
      · simp [EvenFrom,SimpleGraph.dist_self]
      · simp [EvenFrom,mem_shell.mp ht,even_two]
    · simp only [EvenFrom,Finset.mem_filter,Finset.mem_univ,true_and,mem_shell.mp h]
      decide
  have cc := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dh,Finset.card_insert_of_not_mem h2] at cc
  omega

/-- A finite reduction for #189 with second-smallest degree three.
The stronger first bound applies when a degree-at-most-three vertex has
a vertex at distance four. -/
theorem order_le_sixteen_of_even_four (hc : G.Connected)
    (bound : ∀ x, (EvenFrom G x).card ≤ 4)
    (conn : ∀ S : Finset V, S.card < 2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (x : V) (small : G.degree x ≤ 3) :
    Fintype.card V ≤ 16 ∧ ((∃ y, G.dist x y = 4) → Fintype.card V ≤ 13) := by
  classical
  have hdiam := diameter_at_most_four_of_even_four hc bound conn
  have zero {y : V} : G.dist x y = 0 → y = x := fun h =>
    ((dist_eq_zero_iff_eq_or_not_reachable.mp h).resolve_right (not_not.mpr (hc x y))).symm
  have one : (Shell G x 1).card = G.degree x := by
    rw [← G.card_neighborFinset_eq_degree]
    congr 1
    ext z
    rw [mem_shell,G.mem_neighborFinset,dist_eq_one_iff_adj]
  have cover : (Finset.univ : Finset V) ⊆
      insert x (Shell G x 1 ∪ (Shell G x 2 ∪ (Shell G x 3 ∪ Shell G x 4))) := by
    intro y _
    have h := hdiam x y
    have e : G.dist x y = 0 ∨ G.dist x y = 1 ∨ G.dist x y = 2 ∨ G.dist x y = 3 ∨ G.dist x y = 4 := by omega
    simpa only [Finset.mem_insert,Finset.mem_union,mem_shell] using e.imp zero id
  have cu := Finset.card_le_card cover
  have cI := Finset.card_insert_le x (Shell G x 1 ∪ (Shell G x 2 ∪ (Shell G x 3 ∪ Shell G x 4)))
  have c1 := Finset.card_union_le (Shell G x 1) (Shell G x 2 ∪ (Shell G x 3 ∪ Shell G x 4))
  have c2 := Finset.card_union_le (Shell G x 2) (Shell G x 3 ∪ Shell G x 4)
  have c3 := Finset.card_union_le (Shell G x 3) (Shell G x 4)
  rw [Finset.card_univ] at cu
  have even := shell_two_four_le_of_even_four (bound x)
  have third := third_shell_le hc 3 (fun x => distanceTwo_le_of_even 3 x (bound x)) x
  constructor
  · omega
  · rintro ⟨y,hy⟩
    have four : 0 < (Shell G x 4).card := Finset.card_pos.mpr ⟨y,mem_shell.mpr hy⟩
    omega

#print axioms order_le_sixteen_of_even_four

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem diameter_bound_from_inner_even_layers (hc : G.Connected) (d k r : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ d + 1)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (hdk : d < (r+1)*k) : ∀ x y, G.dist x y ≤ 2*(r+1) := by
  intro x y
  by_contra! hfar
  have Q := innerEvenLayers_of_far hc k r conn (x:=x) (y:=y) (by omega)
  have D : k ≤ (DistanceTwo G x).card := by
    rw [← shell_two]
    exact shell_card_of_far hc k conn (x:=x) (y:=y) (by decide) (by omega)
  have E := bound x
  rw [Nat.add_mul,one_mul] at hdk
  omega

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem shell_two_four_le_of_even {x : V} {d : ℕ} (hb : (EvenFrom G x).card ≤ d+1) :
    (Shell G x 2).card + (Shell G x 4).card ≤ d := by
  classical
  have h2 : x ∉ Shell G x 2 := by rw [mem_shell,SimpleGraph.dist_self]; decide
  have dh : Disjoint (insert x (Shell G x 2)) (Shell G x 4) := by
    rw [Finset.disjoint_left]
    intro y hy e
    have e' := mem_shell.mp e
    rcases Finset.mem_insert.mp hy with rfl|h
    · rw [SimpleGraph.dist_self] at e'
      omega
    · have he := mem_shell.mp h
      omega
  have sub : insert x (Shell G x 2) ∪ Shell G x 4 ⊆ EvenFrom G x := by
    intro y hy
    rcases Finset.mem_union.mp hy with h|h
    · rcases Finset.mem_insert.mp h with rfl|ht
      · simp [EvenFrom,SimpleGraph.dist_self]
      · simp [EvenFrom,mem_shell.mp ht,even_two]
    · simp only [EvenFrom,Finset.mem_filter,Finset.mem_univ,true_and,mem_shell.mp h]
      decide
  have cc := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dh,Finset.card_insert_of_not_mem h2] at cc
  omega

/-- Uniform order bounds from the even-count premise and connectivity
greater than half the cap. -/
theorem order_bound_of_even_high_connectivity (hc : G.Connected) (d k : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ d+1)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (hdk : d < 2*k)
    (x : V) (small : G.degree x ≤ d) :
    Fintype.card V ≤ d*d+2*d+1 ∧
      ((∃ y, G.dist x y = 4) → Fintype.card V ≤ (d-1)*d+2*d+1) := by
  classical
  have hdiam := diameter_bound_from_inner_even_layers hc d k 1 bound conn hdk
  have zero {y : V} : G.dist x y = 0 → y = x := fun h =>
    ((dist_eq_zero_iff_eq_or_not_reachable.mp h).resolve_right (not_not.mpr (hc x y))).symm
  have one : (Shell G x 1).card = G.degree x := by
    rw [← G.card_neighborFinset_eq_degree]
    congr 1
    ext z
    rw [mem_shell,G.mem_neighborFinset,dist_eq_one_iff_adj]
  have cover : (Finset.univ : Finset V) ⊆
      insert x (Shell G x 1 ∪ (Shell G x 2 ∪ (Shell G x 3 ∪ Shell G x 4))) := by
    intro y _
    have h := hdiam x y
    have e : G.dist x y = 0 ∨ G.dist x y = 1 ∨ G.dist x y = 2 ∨ G.dist x y = 3 ∨ G.dist x y = 4 := by omega
    simpa only [Finset.mem_insert,Finset.mem_union,mem_shell] using e.imp zero id
  have cu := Finset.card_le_card cover
  have cI := Finset.card_insert_le x (Shell G x 1 ∪ (Shell G x 2 ∪ (Shell G x 3 ∪ Shell G x 4)))
  have c1 := Finset.card_union_le (Shell G x 1) (Shell G x 2 ∪ (Shell G x 3 ∪ Shell G x 4))
  have c2 := Finset.card_union_le (Shell G x 2) (Shell G x 3 ∪ Shell G x 4)
  have c3 := Finset.card_union_le (Shell G x 3) (Shell G x 4)
  rw [Finset.card_univ] at cu
  have even := shell_two_four_le_of_even (bound x)
  have third := third_shell_le hc d (fun x => distanceTwo_le_of_even d x (bound x)) x
  constructor
  · have m := Nat.mul_le_mul_right d (show (Shell G x 2).card ≤ d by omega)
    omega
  · rintro ⟨y,hy⟩
    have four : 0 < (Shell G x 4).card := Finset.card_pos.mpr ⟨y,mem_shell.mpr hy⟩
    have m := Nat.mul_le_mul_right d (show (Shell G x 2).card ≤ d-1 by omega)
    omega

#print axioms diameter_bound_from_inner_even_layers
#print axioms order_bound_of_even_high_connectivity

/-- At the first unproved connectivity threshold, every omitted vertex
that contacts a longest path has a full distance-two sphere and no vertex
at distance four or beyond. -/
theorem omitted_attachment_saturates (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x y : V} (hx : x ∉ p.support) (hy : y ∈ p.support) (hxy : G.Adj x y) :
    (DistanceTwo G x).card = k+1 ∧ ∀ z, G.dist x z ≤ 3 := by
  classical
  obtain ⟨A,B,hxa,haa,hab,hdis,hbound,hcard⟩ :=
    small_separator_of_omitted_attachment hc hp hx hy hxy
  have Bcard : k ≤ B.card := by
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
  have cap := distanceTwo_le_of_even (k+1) x (bound x)
  refine ⟨by omega, ?_⟩
  intro z
  by_contra! hfar
  have big := distanceTwo_add_two_le_even_of_far hc (show 4 ≤ G.dist x z by omega)
  have bnd := bound x
  omega

#print axioms omitted_attachment_saturates

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

private theorem one_pin_or_no_omitted_neighbor (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x ∉ p.support) {i j : ℕ} (hi : i ∈ Pins p x) (hj : j ∈ Pins p x) (hne : i ≠ j) :
    (∀ q ∈ Pins p x, ∃ r ∈ Pins p x, q+2=r ∨ r+2=q) ∧
    (∀ z, G.Adj x z → z ∈ p.support) := by
  classical
  obtain ⟨A,B,hxa,haa,hab,hdis,hbound,hcard,hgap,ha,hb⟩ :=
    small_separator_count_pins hc hp hx (p.getVert_mem_support i) (pin_data hi).2
  have lowB := boundary_card_of_connectivity k conn hxa haa hab hdis hbound
  have cap := distanceTwo_le_of_even (k+1) x (bound x)
  have eqB : B.card = k := by omega
  have partner (q : ℕ) (hq : q ∈ Pins p x) : ∃ r ∈ Pins p x, q+2=r ∨ r+2=q := by
    by_contra! hn
    have many : ∃ r ∈ Pins p x, r ≠ q := by
      by_cases he : i = q
      · exact ⟨j,hj,fun e => hne (he.trans e.symm)⟩
      · exact ⟨i,hi,he⟩
    have bad := hgap q hq many hn
    omega
  refine ⟨partner,?_⟩
  intro z hz
  by_contra hnot
  let A' := A.erase x
  let F := (Pins p x).image p.getVert
  let B' := insert x (B \ F)
  have zA' : z ∈ A' := Finset.mem_erase.mpr ⟨hz.ne.symm,(ha _).mpr ⟨hnot,Or.inr hz⟩⟩
  have naB' : a ∉ B' := by
    intro h
    rcases Finset.mem_insert.mp h with h|h
    · exact hx (h ▸ p.start_mem_support)
    · exact hab (Finset.mem_sdiff.mp h).1
  have naA' : a ∉ A' := fun h => haa (Finset.mem_erase.mp h).2
  have dis' : Disjoint A' B' := by
    rw [Finset.disjoint_left]
    intro u hu hv
    obtain ⟨ex,au⟩ := Finset.mem_erase.mp hu
    rcases Finset.mem_insert.mp hv with hv|hv
    · exact ex hv
    · exact Finset.disjoint_left.mp hdis au (Finset.mem_sdiff.mp hv).1
  have exclusive (q : ℕ) (hq : q ∈ Pins p x) {u : V} (hu : u ∈ A') :
      ¬G.Adj u (p.getVert q) := by
    intro huq
    obtain ⟨nx,ua⟩ := Finset.mem_erase.mp hu
    have udata := (ha _).mp ua
    have xu : G.Adj x u := udata.2.resolve_left nx
    have both {s t : V} (h : G.Adj s t) (hs : s ∉ p.support) (ht : t ∉ p.support) :
        ∀ w ∈ h.toWalk.support, w ∉ p.support := by simp [hs,ht]
    obtain ⟨r,hr,he|he⟩ := partner q hq
    · have hrlen := (pin_data hr).1
      have lead := splice_gap_two p hp.1 xu.symm.toWalk (IsPath.of_adj xu.symm)
        (both xu.symm udata.1 hx) q (by omega) huq.symm (by simpa only [he] using (pin_data hr).2)
      obtain ⟨t,ht,htl,_⟩ := lead
      have l := hp.2 a b t ht
      simp at htl
      omega
    · have hqlen := (pin_data hq).1
      have lead := splice_gap_two p hp.1 xu.toWalk (IsPath.of_adj xu)
        (both xu hx udata.1) r (by omega) (pin_data hr).2.symm (by simpa only [he] using huq)
      obtain ⟨t,ht,htl,_⟩ := lead
      have l := hp.2 a b t ht
      simp at htl
      omega
  have border : ∀ y ∈ A', ∀ t ∉ A', G.Adj y t → t ∈ B' := by
    intro u hu v hv e
    by_cases he : v = x
    · exact Finset.mem_insert.mpr (Or.inl he)
    have vna : v ∉ A := fun ht => hv (Finset.mem_erase.mpr ⟨he,ht⟩)
    have vb : v ∈ B := hbound u (Finset.mem_erase.mp hu).2 v vna e
    have vnf : v ∉ F := by
      intro hvf
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hvf
      exact exclusive t ht hu e
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨vb,vnf⟩))
  have fsub : F ⊆ B := by
    intro u hu
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hu
    have out : p.getVert l ∉ A := fun h => ((ha _).mp h).1 (p.getVert_mem_support l)
    exact hbound x hxa _ out (pin_data hl).2
  have fbig : 2 ≤ F.card := by
    have en : p.getVert i ≠ p.getVert j := fun h =>
      hne (hp.1.getVert_injOn (Nat.le_of_lt (pin_data hi).1) (Nat.le_of_lt (pin_data hj).1) h)
    have sub : ({p.getVert i, p.getVert j} : Finset V) ⊆ F := by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl|hu
      · exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
      · rw [Finset.mem_singleton] at hu
        subst u
        exact Finset.mem_image.mpr ⟨j,hj,rfl⟩
    have cc := Finset.card_le_card sub
    simp [en] at cc
    exact cc
  have xx : x ∉ B \ F := by
    intro h
    exact Finset.disjoint_left.mp hdis hxa (Finset.mem_sdiff.mp h).1
  have upper : B'.card < k := by
    have eq := Finset.card_sdiff_add_card_eq_card fsub
    rw [Finset.card_insert_of_not_mem xx]
    omega
  have lower := boundary_card_of_connectivity k conn zA' naA' naB' dis' border
  omega

#print axioms one_pin_or_no_omitted_neighbor

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

/-- At connectivity `d−1`, every vertex off a longest path has at most one
neighbor on it, provided that at most one vertex has degree below `d`. -/
theorem unique_omitted_pin_at_near_connectivity (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) {x : V} (hx : x ∉ p.support) :
    ∀ i ∈ Pins p x, ∀ j ∈ Pins p x, i = j := by
  classical
  intro i hi j hj
  by_contra ne
  obtain ⟨partner,closed⟩ :=
    one_pin_or_no_omitted_neighbor hc k bound conn hp hx hi hj ne
  obtain ⟨r,hr,he⟩ := partner i hi
  obtain ⟨m,hm,hm2⟩ : ∃ m, m ∈ Pins p x ∧ (m+2) ∈ Pins p x := by
    rcases he with h|h
    · exact ⟨i,hi,h.symm ▸ hr⟩
    · exact ⟨r,hr,h.symm ▸ hi⟩
  have ml := (pin_data hm2).1
  let z := p.getVert (m+1)
  have xz : x ≠ z := fun e => hx (e ▸ p.getVert_mem_support (m+1))
  have hq : ∀ w ∈ (Walk.nil : G.Walk x x).support, w ∉ p.support := by simpa using hx
  obtain ⟨q,hqpath,hqlen,hqsup⟩ := splice_gap_two p hp.1 (Walk.nil : G.Walk x x) IsPath.nil
    hq m (by omega) (pin_data hm).2.symm (pin_data hm2).2
  have len : q.length = p.length := by simpa using hqlen
  have hqmax : IsLongest q := ⟨hqpath,fun u v s hs => len.symm ▸ hp.2 u v s hs⟩
  have znot : z ∉ q.support := by
    intro hz
    rcases (hqsup z).mp hz with h|h
    · exact xz.symm (by simpa using h)
    · exact h.2 rfl
  have hm1le : m+1 ≤ p.length := by omega
  have qmem (t : ℕ) (ht : t ≤ p.length) (hne : t ≠ m+1) : p.getVert t ∈ q.support :=
    (hqsup _).mpr (Or.inr ⟨p.getVert_mem_support t,fun e =>
      hne (hp.1.getVert_injOn ht hm1le e)⟩)
  have hmz := p.adj_getVert_succ (i:=m) (by omega : m < p.length)
  have hzm := p.adj_getVert_succ (i:=m+1) (by omega : m+1 < p.length)
  obtain ⟨u,hu,huv⟩ := pin_of_neighbor_mem hqmax znot (qmem m (by omega) (by omega)) hmz.symm
  obtain ⟨v,hv,hvv⟩ := pin_of_neighbor_mem hqmax znot (qmem (m+2) (by omega) (by omega)) hzm
  have uv : u ≠ v := by
    intro e
    subst v
    have heq := huv.symm.trans hvv
    have bad := hp.1.getVert_injOn (show m ≤ p.length by omega) (show m+2 ≤ p.length by omega) heq
    omega
  have zclosed := (one_pin_or_no_omitted_neighbor hc k bound conn hqmax znot hu hv uv).2
  have capx := distanceTwo_le_of_even (k+1) x (bound x)
  have capz := distanceTwo_le_of_even (k+1) z (bound z)
  have smallx := degree_lt_distanceTwo_of_omitted_isolated hc hp hx closed ⟨_,(pin_data hm).2⟩
  have smallz := degree_lt_distanceTwo_of_omitted_isolated hc hqmax znot zclosed ⟨_,hmz.symm⟩
  rcases degree x z xz with h|h <;> omega

#print axioms unique_omitted_pin_at_near_connectivity
end Graffiti189LongestPath
