import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Metric reduction for Written on the Wall II #183. -/

namespace Graffiti183

open SimpleGraph Finset
noncomputable section

variable {V : Type*} [Fintype V]

def eccentricity (G : SimpleGraph V) (v : V) : ℕ := univ.sup (G.dist v)

def square (G : SimpleGraph V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ G.dist x y ≤ 2
  symm := fun x y h => ⟨h.1.symm, (G.dist_comm (u := x) (v := y)) ▸ h.2⟩
  loopless := fun _ h => h.1 rfl

def radius (G : SimpleGraph V) : ℕ := sInf (Set.range (eccentricity G))

def squareMaxDegree (G : SimpleGraph V) : ℕ := by
  classical
  exact (square G).maxDegree

def squareNeighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact (square G).neighborFinset v

def maxLeaves (G : SimpleGraph V) : ℕ := by
  classical
  exact sSup {k | ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧
    (univ.filter (fun v => T.degree v = 1)).card = k}

def bipartiteNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact (univ.powerset.filter (fun s : Finset V =>
    ∃ c : s → Bool, ∀ a b : s, G.Adj a.val b.val → c a ≠ c b)).sup Finset.card

def Claim183 (G : SimpleGraph V) : Prop :=
  squareMaxDegree G + 2 * radius (square G) ≤ maxLeaves G + bipartiteNumber G

omit [Fintype V] in
private theorem le_square (G : SimpleGraph V) : G ≤ square G :=
  fun _ _ h => ⟨h.ne, le_trans (G.dist_le h.toWalk) (by simp [Adj.toWalk])⟩

omit [Fintype V] in
private theorem square_connected {G : SimpleGraph V} (hc : G.Connected) :
    (square G).Connected := hc.mono (le_square G)

omit [Fintype V] in
private theorem dist_le_twice_square_walk {G : SimpleGraph V} (hc : G.Connected)
    {v w : V} (p : (square G).Walk v w) : G.dist v w ≤ 2 * p.length := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    have h' : G.dist a b ≤ 2 := h.2
    have htri : G.dist a c ≤ G.dist a b + G.dist b c := hc.dist_triangle
    rw [Walk.length_cons]
    omega

omit [Fintype V] in
private theorem square_dist_le_half_walk {G : SimpleGraph V} (hc : G.Connected)
    {v w : V} (p : G.Walk v w) : (square G).dist v w ≤ (p.length + 1) / 2 := by
  match p with
  | .nil => simp
  | .cons h .nil =>
    simpa [Adj.toWalk] using (square G).dist_le ((le_square G h).toWalk)
  | @Walk.cons _ _ a b c h (.cons (v := d) h' q) =>
    have htail := square_dist_le_half_walk hc q
    have hab : G.dist a b ≤ 1 := G.dist_le h.toWalk
    have hbd : G.dist b d ≤ 1 := G.dist_le h'.toWalk
    have had₀ : G.dist a d ≤ G.dist a b + G.dist b d := hc.dist_triangle
    have had : (square G).dist a d ≤ 1 := by
      by_cases heq : a = d
      · simp [heq, dist_self]
      · exact (square G).dist_le (show (square G).Adj a d from ⟨heq, by omega⟩).toWalk
    have htri : (square G).dist a c ≤ (square G).dist a d + (square G).dist d c :=
      (square_connected hc).dist_triangle
    simp only [Walk.length_cons]
    omega
termination_by p.length
decreasing_by simp only [Walk.length_cons]; omega

omit [Fintype V] in
theorem square_dist {G : SimpleGraph V} (hc : G.Connected) (v w : V) :
    (square G).dist v w = (G.dist v w + 1) / 2 := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v w
  obtain ⟨q, hq⟩ := (square_connected hc).exists_walk_length_eq_dist v w
  have hlo := dist_le_twice_square_walk hc q
  have hhi := square_dist_le_half_walk hc p
  omega

private theorem dist_le_ecc (G : SimpleGraph V) (v w : V) :
    G.dist v w ≤ eccentricity G v := le_sup (mem_univ w)

private theorem exists_dist_eq_ecc (G : SimpleGraph V) (v : V) :
    ∃ w, eccentricity G v = G.dist v w := by
  obtain ⟨w, _, hw⟩ := exists_mem_eq_sup univ ⟨v, mem_univ v⟩ (G.dist v)
  exact ⟨w, hw⟩

private theorem square_ecc {G : SimpleGraph V} (hc : G.Connected) (v : V) :
    eccentricity (square G) v = (eccentricity G v + 1) / 2 := by
  obtain ⟨w, hw⟩ := exists_dist_eq_ecc G v
  obtain ⟨z, hz⟩ := exists_dist_eq_ecc (square G) v
  have hlo := dist_le_ecc (square G) v w
  have hhi := dist_le_ecc G v z
  rw [square_dist hc] at hlo hz
  omega

omit [Fintype V] in
private theorem take_drop_lengths {G : SimpleGraph V} {v w : V}
    (p : G.Walk v w) (i : ℕ) :
    (p.take i).length = min i p.length ∧ (p.drop i).length = p.length - i := by
  induction p generalizing i with
  | nil => cases i <;> simp [Walk.take, Walk.drop]
  | cons h p ih =>
    cases i with
    | zero => simp [Walk.take, Walk.drop]
    | succ i =>
      have h := ih i
      change (p.take i).length + 1 = min (i + 1) (p.length + 1) ∧
        (p.drop i).length = p.length + 1 - (i + 1)
      omega

omit [Fintype V] in
private theorem geodesic_prefix_suffix {G : SimpleGraph V} (hc : G.Connected)
    {v w : V} {p : G.Walk v w} (hp : p.length = G.dist v w) {i : ℕ}
    (hi : i ≤ p.length) :
    G.dist v (p.getVert i) = i ∧ G.dist (p.getVert i) w = p.length - i := by
  have ht := G.dist_le (p.take i)
  have hd := G.dist_le (p.drop i)
  have hs := take_drop_lengths p i
  have htri : G.dist v w ≤ G.dist v (p.getVert i) + G.dist (p.getVert i) w :=
    hc.dist_triangle
  simp [min_eq_left hi] at hs
  omega

def farVertices (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact univ.filter (fun w => 2 < G.dist v w)

private theorem far_card_ge {G : SimpleGraph V} (hc : G.Connected)
    {v w : V} {p : G.Walk v w} (hp : p.length = G.dist v w) :
    p.length - 2 ≤ (farVertices G v).card := by
  classical
  rw [← card_range (p.length - 2)]
  refine card_le_card_of_injOn (fun i => p.getVert (i + 3)) ?_ ?_
  · intro i hi
    have hi' := mem_range.mp hi
    have h := (geodesic_prefix_suffix hc hp (i := i + 3) (by omega)).1
    simp [farVertices, h]
  · intro i hi j hj he
    have hi' := mem_range.mp (show i ∈ range (p.length - 2) from hi)
    have hj' := mem_range.mp (show j ∈ range (p.length - 2) from hj)
    have hiD := (geodesic_prefix_suffix hc hp (i := i + 3) (by omega)).1
    have hjD := (geodesic_prefix_suffix hc hp (i := j + 3) (by omega)).1
    change p.getVert (i + 3) = p.getVert (j + 3) at he
    rw [he, hjD] at hiD
    omega

private theorem radius_le_ecc (G : SimpleGraph V) (v : V) :
    radius G ≤ eccentricity G v := Nat.sInf_le ⟨v, rfl⟩

private theorem exists_ecc_eq_radius (G : SimpleGraph V) [Nonempty V] :
    ∃ v, eccentricity G v = radius G :=
  Nat.sInf_mem (Set.range_nonempty (f := eccentricity G))

theorem square_radius {G : SimpleGraph V} (hc : G.Connected) :
    radius (square G) = (radius G + 1) / 2 := by
  letI := hc.nonempty
  obtain ⟨v, hv⟩ := exists_ecc_eq_radius G
  obtain ⟨w, hw⟩ := exists_ecc_eq_radius (square G)
  have h1 := radius_le_ecc (square G) v
  have h2 := radius_le_ecc G w
  rw [square_ecc hc, hv] at h1
  rw [square_ecc hc] at hw
  omega

private theorem mem_squareNeighbors {G : SimpleGraph V} {v w : V} :
    w ∈ squareNeighbors G v ↔ v ≠ w ∧ G.dist v w ≤ 2 := by
  classical
  exact (square G).mem_neighborFinset v w

private theorem neighborhood_partition_card (G : SimpleGraph V) (v : V) :
    (farVertices G v).card + (squareNeighbors G v).card + 1 = Fintype.card V := by
  classical
  have hd : Disjoint (farVertices G v) (squareNeighbors G v) := by
    rw [disjoint_left]
    intro w hw hn
    exact (not_le_of_gt (mem_filter.mp hw).2) (mem_squareNeighbors.mp hn).2
  have hv : v ∉ farVertices G v ∪ squareNeighbors G v := by
    simp [farVertices, mem_squareNeighbors, dist_self]
  have hu : insert v (farVertices G v ∪ squareNeighbors G v) = univ := by
    apply eq_univ_of_forall
    intro w
    by_cases h : v = w
    · subst w
      exact mem_insert_self v _
    · by_cases hw : 2 < G.dist v w
      · exact mem_insert_of_mem (mem_union_left _ (by simp [farVertices, hw]))
      · exact mem_insert_of_mem (mem_union_right _ (mem_squareNeighbors.mpr ⟨h, by omega⟩))
  rw [← card_union_of_disjoint hd, ← card_insert_of_not_mem hv, hu, card_univ]

private theorem max_degree_attained {G : SimpleGraph V} (hc : G.Connected) :
    ∃ v, squareMaxDegree G = (squareNeighbors G v).card := by
  classical
  letI := hc.nonempty
  obtain ⟨v, hv⟩ := (square G).exists_maximal_degree_vertex
  exact ⟨v, hv⟩

private theorem neighbor_count_le_maxDegree (G : SimpleGraph V) (v : V) :
    (squareNeighbors G v).card ≤ squareMaxDegree G := by
  classical
  exact (square G).degree_le_maxDegree v

theorem metric_upper_bound {G : SimpleGraph V} (hc : G.Connected) :
    squareMaxDegree G + 2 * radius (square G) ≤ Fintype.card V + 2 := by
  obtain ⟨v, hv⟩ := max_degree_attained hc
  obtain ⟨w, hw⟩ := exists_dist_eq_ecc G v
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v w
  have hfar := far_card_ge hc hp
  have hpart := neighborhood_partition_card G v
  have hr := radius_le_ecc G v
  rw [square_radius hc]
  omega

/-- Equality in the metric bound occurs at radius three with a vertex
whose closed distance-two ball misses exactly one vertex. -/
theorem metric_excess_iff {G : SimpleGraph V} (hc : G.Connected) :
    Fintype.card V + 1 < squareMaxDegree G + 2 * radius (square G) ↔
      radius G = 3 ∧ ∃ v w, G.dist v w = 3 ∧ ∀ z, 2 < G.dist v z ↔ z = w := by
  classical
  constructor
  · intro hex
    obtain ⟨v, hv⟩ := max_degree_attained hc
    obtain ⟨w, hw⟩ := exists_dist_eq_ecc G v
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v w
    have hpart := neighborhood_partition_card G v
    have hfar := far_card_ge hc hp
    have hr := radius_le_ecc G v
    rw [square_radius hc, hv] at hex
    have hlen : p.length = eccentricity G v := hp.trans hw.symm
    have hsame : radius G = eccentricity G v := by omega
    have he : 3 ≤ eccentricity G v := by omega
    have hodd : eccentricity G v % 2 = 1 := by omega
    have hfar' : (farVertices G v).card = p.length - 2 := by omega
    have hc3 : eccentricity G v = 3 := by
      by_cases hthree : eccentricity G v = 3
      · exact hthree
      exfalso
      have h5 : 5 ≤ p.length := by omega
      let f (i : ℕ) := p.getVert (i + 3)
      have hdist (i : ℕ) (hi : i ∈ range (p.length - 2)) : G.dist v (f i) = i + 3 := by
        have hi' := mem_range.mp hi
        exact (geodesic_prefix_suffix hc hp (by omega : i + 3 ≤ p.length)).1
      have hsub : (range (p.length - 2)).image f ⊆ farVertices G v := by
        intro z hz
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
        simp [farVertices, hdist i hi]
      have hinj : Set.InjOn f ↑(range (p.length - 2)) := by
        intro i hi j hj heq
        have h₁ := hdist i hi
        have h₂ := hdist j hj
        rw [heq, h₂] at h₁
        omega
      have himage : (range (p.length - 2)).image f = farVertices G v := by
        apply eq_of_subset_of_card_le hsub
        rw [card_image_of_injOn hinj, card_range, hfar']
      let a := p.getVert 1
      have hda : G.dist v a = 1 := (geodesic_prefix_suffix hc hp (by omega : 1 ≤ p.length)).1
      have hra := radius_le_ecc G a
      obtain ⟨z, hz⟩ := exists_dist_eq_ecc G a
      have haz : G.dist a z ≤ p.length - 1 := by
        by_cases hzfar : z ∈ farVertices G v
        · rw [← himage] at hzfar
          obtain ⟨i, hi, rfl⟩ := mem_image.mp hzfar
          have hil := mem_range.mp hi
          have hget : (p.drop 1).getVert (i + 2) = f i := by
            change p.tail.getVert (i + 2) = p.getVert (i + 3)
            rw [Walk.getVert_tail]
          have ht := G.dist_le ((p.drop 1).take (i + 2))
          rw [(take_drop_lengths (p.drop 1) (i + 2)).1] at ht
          have hdist : G.dist a (f i) ≤ i + 2 := hget ▸ (ht.trans (min_le_left _ _))
          omega
        · have hz2 : G.dist v z ≤ 2 := by simpa [farVertices, not_lt] using hzfar
          have ht : G.dist a z ≤ G.dist a v + G.dist v z := hc.dist_triangle
          rw [G.dist_comm (u := a) (v := v), hda] at ht
          omega
      omega
    refine ⟨by omega, v, w, by omega, ?_⟩
    intro z
    have hwfar : w ∈ farVertices G v := by simp [farVertices, ← hw, hc3]
    have hsing : farVertices G v = {w} := by
      symm
      apply eq_of_subset_of_card_le (singleton_subset_iff.mpr hwfar)
      simp
      omega
    have hmem : z ∈ farVertices G v ↔ 2 < G.dist v z := by simp [farVertices]
    rw [← hmem, hsing, mem_singleton]
  · rintro ⟨hr, v, w, _, hfar⟩
    have hsing : farVertices G v = {w} := by
      ext z
      simpa [farVertices] using hfar z
    have hpart := neighborhood_partition_card G v
    rw [hsing, card_singleton] at hpart
    have hmax := neighbor_count_le_maxDegree G v
    rw [square_radius hc, hr]
    omega

/-- A graph in the metric exception has square maximum degree n-2 and
ordinary diameter at most five. -/
theorem metric_exception_parameters {G : SimpleGraph V} (hc : G.Connected)
    (hex : Fintype.card V + 1 < squareMaxDegree G + 2 * radius (square G)) :
    squareMaxDegree G + 2 = Fintype.card V ∧ ∀ a b, G.dist a b ≤ 5 := by
  obtain ⟨hr, v, w, hvw, hfar⟩ := (metric_excess_iff hc).mp hex
  have hmax := metric_upper_bound hc
  rw [square_radius hc, hr] at hex hmax
  refine ⟨by omega, ?_⟩
  intro a b
  have hab : G.dist a b ≤ G.dist a v + G.dist v b := hc.dist_triangle
  have hsymm := G.dist_comm (u := a) (v := v)
  by_cases ha : a = w <;> by_cases hb : b = w
  · simp [ha, hb, dist_self]
  · have hbd : G.dist v b ≤ 2 := by simpa [not_lt] using mt (hfar b).mp hb
    subst a
    rw [G.dist_comm (u := w) (v := v), hvw] at hab
    omega
  · have had : G.dist v a ≤ 2 := by simpa [not_lt] using mt (hfar a).mp ha
    subst b
    rw [hvw] at hab
    omega
  · have had : G.dist v a ≤ 2 := by simpa [not_lt] using mt (hfar a).mp ha
    have hbd : G.dist v b ≤ 2 := by simpa [not_lt] using mt (hfar b).mp hb
    omega

/-- A failure of the exact catalogue inequality, given the published order
bound, must attain equality in the metric bound and in the order bound. -/
theorem conjecture183_failure_iff {G : SimpleGraph V} (hc : G.Connected)
    (hbound : Fintype.card V + 1 ≤ maxLeaves G + bipartiteNumber G) :
    ¬Claim183 G ↔
      (radius G = 3 ∧ ∃ v w, G.dist v w = 3 ∧ ∀ z, 2 < G.dist v z ↔ z = w) ∧
      maxLeaves G + bipartiteNumber G = Fintype.card V + 1 := by
  unfold Claim183
  rw [Nat.not_le]
  have hmax := metric_upper_bound hc
  constructor
  · intro h
    exact ⟨(metric_excess_iff hc).mp (by omega), by omega⟩
  · rintro ⟨hex, heq⟩
    have := (metric_excess_iff hc).mpr hex
    omega

/-- Radius at least three forces an induced bipartite subgraph on five vertices.
A shortest four-vertex path can be enlarged by a vertex far from its first
interior vertex. -/
theorem five_le_bipartiteNumber_of_radius {G : SimpleGraph V} (hc : G.Connected)
    (hr : 3 ≤ radius G) : 5 ≤ bipartiteNumber G := by
  classical
  letI := hc.nonempty
  let x : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨y, hy⟩ := exists_dist_eq_ecc G x
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist x y
  have hlen : 3 ≤ p.length := by
    have h := radius_le_ecc G x
    omega
  let a := p.getVert 1
  let b := p.getVert 2
  let c := p.getVert 3
  have hxa : G.dist x a = 1 := (geodesic_prefix_suffix hc hp (by omega : 1 ≤ p.length)).1
  have hxb : G.dist x b = 2 := (geodesic_prefix_suffix hc hp (by omega : 2 ≤ p.length)).1
  have hxc : G.dist x c = 3 := (geodesic_prefix_suffix hc hp hlen).1
  have hab : G.Adj a b := p.adj_getVert_succ (by omega : 1 < p.length)
  have hbc : G.Adj b c := p.adj_getVert_succ (by omega : 2 < p.length)
  have hadb : G.dist a b ≤ 1 := G.dist_le hab.toWalk
  have hbdc : G.dist b c ≤ 1 := G.dist_le hbc.toWalk
  have hadc : G.dist a c ≤ 2 := by
    have h : G.dist a c ≤ G.dist a b + G.dist b c := hc.dist_triangle
    omega
  have hadx : G.dist a x = 1 := (G.dist_comm (u := a) (v := x)).trans hxa
  obtain ⟨w, hw⟩ := exists_dist_eq_ecc G a
  have haw : 3 ≤ G.dist a w := by
    have h := radius_le_ecc G a
    omega
  have hx_a : x ≠ a := by intro h; rw [h, dist_self] at hxa; omega
  have hx_b : x ≠ b := by intro h; rw [h, dist_self] at hxb; omega
  have hx_c : x ≠ c := by intro h; rw [h, dist_self] at hxc; omega
  have ha_c : a ≠ c := by intro h; rw [h] at hxa; omega
  have hw_x : w ≠ x := by intro h; rw [h] at haw; omega
  have hw_a : w ≠ a := by intro h; rw [h, dist_self] at haw; omega
  have hw_b : w ≠ b := by intro h; rw [h] at haw; omega
  have hw_c : w ≠ c := by intro h; rw [h] at haw; omega
  have hnxb : ¬G.Adj x b := by
    intro h
    have hdist : G.dist x b ≤ 1 := G.dist_le h.toWalk
    omega
  have hnac : ¬G.Adj a c := by
    intro h
    have hdist : G.dist a c ≤ 1 := G.dist_le h.toWalk
    have hx : G.dist x c ≤ G.dist x a + G.dist a c := hc.dist_triangle
    omega
  have hnxw : ¬G.Adj x w := by
    intro h
    have hdist : G.dist x w ≤ 1 := G.dist_le h.toWalk
    have hx : G.dist a w ≤ G.dist a x + G.dist x w := hc.dist_triangle
    omega
  have hnbw : ¬G.Adj b w := by
    intro h
    have hdist : G.dist b w ≤ 1 := G.dist_le h.toWalk
    have hx : G.dist a w ≤ G.dist a b + G.dist b w := hc.dist_triangle
    omega
  let S : Finset V := {x, a, b, c, w}
  let red : Finset V := {x, b, w}
  have hcS : S.card = 5 := by
    change ({x, a, b, c, w} : Finset V).card = 5
    rw [card_insert_of_not_mem (by simp [hx_a, hx_b, hx_c, hw_x.symm]),
      card_insert_of_not_mem (by simp [hab.ne, ha_c, hw_a.symm]),
      card_insert_of_not_mem (by simp [hbc.ne, hw_b.symm]),
      card_insert_of_not_mem (by simp [hw_c.symm]), card_singleton]
  have hred {u v : V} (hu : u ∈ red) (hv : v ∈ red) : ¬G.Adj u v := by
    simp only [red, mem_insert, mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
      first | exact G.loopless _ | assumption | exact fun h => hnxb h.symm |
        exact fun h => hnxw h.symm | exact fun h => hnbw h.symm
  have hgreen {u : V} (hu : u ∈ S) (hnot : u ∉ red) : u = a ∨ u = c := by
    simp only [S, mem_insert, mem_singleton] at hu
    simp only [red, mem_insert, mem_singleton, not_or] at hnot
    tauto
  let color (u : S) : Bool := if u.val ∈ red then false else true
  have hcolor (u v : S) (huv : G.Adj u.val v.val) : color u ≠ color v := by
    by_cases hu : u.val ∈ red <;> by_cases hv : v.val ∈ red
    · exact (hred hu hv huv).elim
    · simp [color, hu, hv]
    · simp [color, hu, hv]
    · exfalso
      obtain he | he := hgreen u.property hu <;> obtain he' | he' := hgreen v.property hv <;>
        rw [he, he'] at huv <;>
        first | exact G.loopless _ huv | exact hnac huv | exact hnac huv.symm
  have hm : S ∈ univ.powerset.filter (fun s : Finset V =>
    ∃ col : s → Bool, ∀ a b : s, G.Adj a.val b.val → col a ≠ col b) :=
    mem_filter.mpr ⟨mem_powerset.mpr (subset_univ S), color, hcolor⟩
  rw [← hcS]
  exact le_sup (f := Finset.card) hm

/-- Large leaf counts settle the radius-three case directly. -/
theorem conjecture183_of_radius_ge_three_of_leaf_bound {G : SimpleGraph V}
    (hc : G.Connected) (hr : 3 ≤ radius G)
    (hleaf : Fintype.card V ≤ maxLeaves G + 3) : Claim183 G := by
  have hb := five_le_bipartiteNumber_of_radius hc hr
  have hmetric := metric_upper_bound hc
  unfold Claim183
  omega

private theorem two_le_maxLeaves {G : SimpleGraph V} [Nontrivial V]
    (hc : G.Connected) : 2 ≤ maxLeaves G := by
  classical
  obtain ⟨T, hTG, htree⟩ := hc.exists_isTree_le
  let leaves := univ.filter (fun v => T.degree v = 1)
  have hpos (v : V) : 0 < T.degree v := by
    obtain ⟨w, hw⟩ := exists_ne v
    obtain ⟨p⟩ := htree.isConnected.preconnected v w
    exact (T.degree_pos_iff_exists_adj v).mpr ⟨_, p.adj_snd (Walk.not_nil_of_ne hw.symm)⟩
  have hpoint (v : V) : 2 ≤ T.degree v + if v ∈ leaves then 1 else 0 := by
    by_cases hd : T.degree v = 1
    · simp [leaves, hd]
    · have := hpos v
      simp [leaves, hd]
      omega
  have hsum : (∑ _v : V, 2) ≤ ∑ v : V, (T.degree v + if v ∈ leaves then 1 else 0) :=
    sum_le_sum (fun v _ => hpoint v)
  have hleaf : (∑ v : V, (if v ∈ leaves then 1 else 0 : ℕ)) = leaves.card := by simp
  have hleft : (∑ _v : V, (2 : ℕ)) = 2 * Fintype.card V := by
    simp [Nat.mul_comm]
  rw [hleft, sum_add_distrib, T.sum_degrees_eq_twice_card_edges, hleaf] at hsum
  have htree_card := htree.card_edgeFinset
  have htwo : 2 ≤ leaves.card := by omega
  refine htwo.trans (le_csSup ?_ ⟨T, hTG, htree, rfl⟩)
  refine ⟨Fintype.card V, ?_⟩
  rintro _ ⟨T, _, _, rfl⟩
  exact card_le_univ _

/-- The metric upper bound proves exact #183 on bipartite graphs of order at least two. -/
theorem conjecture183_bipartite {G : SimpleGraph V} [Nontrivial V] (hc : G.Connected)
    (hbi : ∃ c : V → Bool, ∀ a b, G.Adj a b → c a ≠ c b) : Claim183 G := by
  classical
  obtain ⟨c, hc'⟩ := hbi
  have hu : (univ : Finset V) ∈ univ.powerset.filter (fun s : Finset V =>
      ∃ k : s → Bool, ∀ a b : s, G.Adj a.val b.val → k a ≠ k b) :=
    mem_filter.mpr ⟨mem_powerset.mpr (Subset.rfl), ⟨fun v => c v.val,
      fun a b h => hc' a.val b.val h⟩⟩
  have hb : Fintype.card V ≤ bipartiteNumber G := by
    have ht := le_sup (f := Finset.card) hu
    simpa only [bipartiteNumber, card_univ] using ht
  have ht := two_le_maxLeaves hc
  have hm := metric_upper_bound hc
  unfold Claim183
  omega

#print axioms square_dist
#print axioms square_radius
#print axioms metric_upper_bound
#print axioms metric_excess_iff
#print axioms metric_exception_parameters
#print axioms conjecture183_failure_iff
#print axioms conjecture183_bipartite
#print axioms five_le_bipartiteNumber_of_radius
#print axioms conjecture183_of_radius_ge_three_of_leaf_bound

end
end Graffiti183
