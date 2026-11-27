import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Metric reduction for Written on the Wall II #182. -/

namespace Graffiti182

open SimpleGraph Finset
noncomputable section

variable {V : Type*} [Fintype V]

def eccentricity (G : SimpleGraph V) (v : V) : ℕ := univ.sup (G.dist v)
def diameter (G : SimpleGraph V) : ℕ := univ.sup (eccentricity G)

def square (G : SimpleGraph V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ G.dist x y ≤ 2
  symm := fun x y h => ⟨h.1.symm, (G.dist_comm (u := x) (v := y)) ▸ h.2⟩
  loopless := fun _ h => h.1 rfl

def periphery (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter (fun v => eccentricity G v = diameter G)

def peripheralNeighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact (periphery (square G)).filter (fun w => (square G).Adj v w)

/-- Maximum degree in the subgraph of the square induced by the square's periphery. -/
def peripheralSquareMaxDegree (G : SimpleGraph V) : ℕ :=
  (periphery (square G)).sup (fun v => (peripheralNeighbors G v).card)

def maxLeaves (G : SimpleGraph V) : ℕ := by
  classical
  exact sSup {k | ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧
    (univ.filter (fun v => T.degree v = 1)).card = k}

def bipartiteNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact (univ.powerset.filter (fun s : Finset V =>
    ∃ c : s → Bool, ∀ a b : s, G.Adj a.val b.val → c a ≠ c b)).sup Finset.card

def Claim182 (G : SimpleGraph V) : Prop :=
  peripheralSquareMaxDegree G + diameter G ≤ maxLeaves G + bipartiteNumber G

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

private theorem ecc_le_diam (G : SimpleGraph V) (v : V) :
    eccentricity G v ≤ diameter G := le_sup (mem_univ v)

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

private theorem square_diam {G : SimpleGraph V} (hc : G.Connected) :
    diameter (square G) = (diameter G + 1) / 2 := by
  letI := hc.nonempty
  obtain ⟨v, _, hv⟩ := exists_mem_eq_sup univ univ_nonempty (eccentricity G)
  obtain ⟨w, _, hw⟩ := exists_mem_eq_sup univ univ_nonempty (eccentricity (square G))
  change diameter G = eccentricity G v at hv
  change diameter (square G) = eccentricity (square G) w at hw
  have hlo := ecc_le_diam (square G) v
  have hhi := ecc_le_diam G w
  rw [square_ecc hc] at hlo hw
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

private theorem mem_peripheralNeighbors {G : SimpleGraph V} {v w : V} :
    w ∈ peripheralNeighbors G v ↔
      w ∈ periphery (square G) ∧ v ≠ w ∧ G.dist v w ≤ 2 := by
  classical
  simp only [peripheralNeighbors, mem_filter]
  rfl

private theorem not_mem_far_self (G : SimpleGraph V) (v : V) :
    v ∉ farVertices G v := by
  simp [farVertices, dist_self]

private theorem far_disjoint_neighbors (G : SimpleGraph V) (v : V) :
    Disjoint (farVertices G v) (peripheralNeighbors G v) := by
  classical
  rw [disjoint_left]
  intro w hw hn
  have h : 2 < G.dist v w := (mem_filter.mp hw).2
  exact (not_le_of_gt h) (mem_peripheralNeighbors.mp hn).2.2

private theorem max_degree_attained {G : SimpleGraph V} (hc : G.Connected) :
    ∃ v ∈ periphery (square G),
      peripheralSquareMaxDegree G = (peripheralNeighbors G v).card := by
  letI := hc.nonempty
  have hper : (periphery (square G)).Nonempty := by
    obtain ⟨a, _, ha⟩ := exists_mem_eq_sup univ univ_nonempty (eccentricity (square G))
    exact ⟨a, by simp [periphery, ← ha, diameter]⟩
  exact exists_mem_eq_sup _ hper _

private theorem peripheral_ecc {G : SimpleGraph V} (hc : G.Connected) {v : V}
    (hv : v ∈ periphery (square G)) :
    (eccentricity G v + 1) / 2 = (diameter G + 1) / 2 := by
  have hh : eccentricity (square G) v = diameter (square G) := (mem_filter.mp hv).2
  rwa [square_ecc hc, square_diam hc] at hh

private theorem neighborhood_union_card (G : SimpleGraph V) (v : V) [DecidableEq V] :
    (insert v (farVertices G v ∪ peripheralNeighbors G v)).card =
      (farVertices G v).card + (peripheralNeighbors G v).card + 1 := by
  have hvnot : v ∉ farVertices G v ∪ peripheralNeighbors G v :=
    fun h => (mem_union.mp h).elim (not_mem_far_self G v)
      (fun h => (mem_peripheralNeighbors.mp h).2.1 rfl)
  rw [card_insert_of_not_mem hvnot, card_union_of_disjoint (far_disjoint_neighbors G v)]

theorem metric_upper_bound {G : SimpleGraph V} (hc : G.Connected) :
    peripheralSquareMaxDegree G + diameter G ≤ Fintype.card V + 2 := by
  classical
  obtain ⟨v, hv, hvmax⟩ := max_degree_attained hc
  have hecc := peripheral_ecc hc hv
  obtain ⟨w, hw⟩ := exists_dist_eq_ecc G v
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v w
  have hfar := far_card_ge hc hp
  have hcard := card_le_univ (insert v (farVertices G v ∪ peripheralNeighbors G v))
  rw [neighborhood_union_card] at hcard
  omega

/-- A metric excess over n+1 can occur only in the diameter-four case
with a unique vertex at distance three and every vertex peripheral in the square. -/
theorem metric_excess_exception {G : SimpleGraph V} (hc : G.Connected)
    (hex : Fintype.card V + 1 < peripheralSquareMaxDegree G + diameter G) :
    diameter G = 4 ∧ periphery (square G) = univ ∧
      ∃ v w, G.dist v w = 3 ∧ ∀ z, 2 < G.dist v z ↔ z = w := by
  classical
  obtain ⟨v, hv, hvmax⟩ := max_degree_attained hc
  rw [hvmax] at hex
  have hecc := peripheral_ecc hc hv
  have hle := ecc_le_diam G v
  obtain ⟨w, hw⟩ := exists_dist_eq_ecc G v
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v w
  have hcard_ge := far_card_ge hc hp
  let far := farVertices G v
  let nbrs := peripheralNeighbors G v
  let used := insert v (far ∪ nbrs)
  have hused : used.card = far.card + nbrs.card + 1 := neighborhood_union_card G v
  have hused_le := card_le_univ used
  change p.length - 2 ≤ far.card at hcard_ge
  change Fintype.card V + 1 < nbrs.card + diameter G at hex
  have hlen : p.length = eccentricity G v := hp.trans hw.symm
  have hdiam : diameter G = eccentricity G v + 1 := by omega
  have he : 3 ≤ eccentricity G v := by omega
  have he_odd : eccentricity G v % 2 = 1 := by omega
  have hfar : far.card = eccentricity G v - 2 := by omega
  have hfull : used = univ := eq_univ_of_card used (by omega)
  have hfargeodesic : ∀ z ∈ far, ∃ i : ℕ, 3 ≤ i ∧ i ≤ p.length ∧ p.getVert i = z := by
    let f (i : ℕ) := p.getVert (i + 3)
    have hdist (i : ℕ) (hi : i ∈ range (p.length - 2)) : G.dist v (f i) = i + 3 := by
      have hi' := mem_range.mp hi
      exact (geodesic_prefix_suffix hc hp (by omega : i + 3 ≤ p.length)).1
    have hsub : (range (p.length - 2)).image f ⊆ far := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
      show f i ∈ farVertices G v
      simp [farVertices, hdist i hi]
    have hinj : Set.InjOn f ↑(range (p.length - 2)) := by
      intro i hi j hj he
      have h₁ := hdist i hi
      have h₂ := hdist j hj
      rw [he, h₂] at h₁
      omega
    have himage : (range (p.length - 2)).image f = far := by
      apply eq_of_subset_of_card_le hsub
      rw [card_image_of_injOn hinj, card_range]
      omega
    intro z hz
    rw [← himage] at hz
    obtain ⟨i, hi, hiEq⟩ := mem_image.mp hz
    have hi' := mem_range.mp hi
    exact ⟨i + 3, by omega, by omega, hiEq⟩
  have hspecific : eccentricity G v = 3 := by
    by_cases hthree : eccentricity G v = 3
    · exact hthree
    exfalso
    have he5 : 5 ≤ eccentricity G v := by omega
    let a := p.getVert 1
    have hda : G.dist v a = 1 := (geodesic_prefix_suffix hc hp (by omega : 1 ≤ p.length)).1
    have hanv : a ≠ v := by intro h; simp [h] at hda
    have hanfar : a ∉ far := by
      change a ∉ farVertices G v
      simp [farVertices, hda]
    have han : a ∈ nbrs := by
      have ham : a ∈ used := hfull ▸ mem_univ a
      exact (mem_union.mp ((mem_insert.mp ham).resolve_left hanv)).resolve_left hanfar
    have hape : a ∈ periphery (square G) := (mem_peripheralNeighbors.mp han).1
    have hae := peripheral_ecc hc hape
    obtain ⟨z, hz⟩ := exists_dist_eq_ecc G a
    have haz : G.dist a z ≤ eccentricity G v - 1 := by
      by_cases hzfar : z ∈ far
      · obtain ⟨i, hi3, hi, rfl⟩ := hfargeodesic z hzfar
        have hadj : G.dist a (p.getVert i) ≤ i - 1 := by
          have hget : (p.drop 1).getVert (i - 1) = p.getVert i := by
            change p.tail.getVert (i - 1) = p.getVert i
            rw [Walk.getVert_tail, show i - 1 + 1 = i by omega]
          have ht := G.dist_le ((p.drop 1).take (i - 1))
          rw [(take_drop_lengths (p.drop 1) (i - 1)).1] at ht
          exact hget ▸ (ht.trans (min_le_left _ _))
        omega
      · have hz2 : G.dist v z ≤ 2 := by simpa [far, farVertices, not_lt] using hzfar
        have ht : G.dist a z ≤ G.dist a v + G.dist v z := hc.dist_triangle
        rw [G.dist_comm (u := a) (v := v), hda] at ht
        omega
    omega
  refine ⟨by omega, ?_, v, w, by omega, ?_⟩
  · apply eq_univ_of_forall
    intro z
    have hz : z ∈ used := hfull ▸ mem_univ z
    rcases mem_insert.mp hz with rfl | hz
    · exact hv
    · rcases mem_union.mp hz with hz | hz
      · apply mem_filter.mpr
        refine ⟨mem_univ _, ?_⟩
        rw [square_ecc hc, square_diam hc]
        have hd' : 2 < G.dist v z := (mem_filter.mp hz).2
        have hlo := dist_le_ecc G z v
        rw [G.dist_comm (u := z) (v := v)] at hlo
        have hhi := ecc_le_diam G z
        omega
      · exact (mem_peripheralNeighbors.mp hz).1
  · intro z
    have hwfar : w ∈ far := by simp [far, farVertices, ← hw, hspecific]
    have hsing : far = {w} := by
      symm
      apply eq_of_subset_of_card_le (singleton_subset_iff.mpr hwfar)
      simp
      omega
    have hmem : z ∈ far ↔ 2 < G.dist v z := by simp [far, farVertices]
    rw [← hmem, hsing, mem_singleton]

/-- The metric exception is also sufficient for equality in the n+2 upper bound. -/
theorem metric_excess_iff {G : SimpleGraph V} (hc : G.Connected) :
    Fintype.card V + 1 < peripheralSquareMaxDegree G + diameter G ↔
      diameter G = 4 ∧ periphery (square G) = univ ∧
        ∃ v w, G.dist v w = 3 ∧ ∀ z, 2 < G.dist v z ↔ z = w := by
  classical
  refine ⟨metric_excess_exception hc, ?_⟩
  rintro ⟨hd, hp, v, w, hvw, hfar⟩
  have hne : v ≠ w := by
    intro h
    simp [h, dist_self] at hvw
  have hset : peripheralNeighbors G v = (univ.erase v).erase w := by
    ext z
    simp only [mem_peripheralNeighbors, hp, mem_erase, mem_univ, true_and, and_true]
    have hz : G.dist v z ≤ 2 ↔ z ≠ w := by rw [← not_lt, hfar]
    rw [hz]
    exact ⟨fun h => ⟨h.2, Ne.symm h.1⟩, fun h => ⟨Ne.symm h.2, h.1⟩⟩
  have hcard : (peripheralNeighbors G v).card + 2 = Fintype.card V := by
    rw [hset]
    have hwa : w ∈ (univ : Finset V).erase v := by simp [hne.symm]
    have h1 := card_erase_add_one hwa
    have h2 := card_erase_add_one (mem_univ v)
    rw [card_univ] at h2
    omega
  have hle : (peripheralNeighbors G v).card ≤ peripheralSquareMaxDegree G :=
    le_sup (f := fun u => (peripheralNeighbors G u).card) (hp ▸ mem_univ v)
  omega

/-- The published #173 order bound resolves #182 given either the stronger order
bound or the absence of the exceptional metric configuration. -/
theorem conjecture182_from_order_bounds {G : SimpleGraph V} (hc : G.Connected)
    (hbound : Fintype.card V + 1 ≤ maxLeaves G + bipartiteNumber G)
    (hexception : diameter G = 4 → periphery (square G) = univ →
      (∃ v w, G.dist v w = 3 ∧ ∀ z, 2 < G.dist v z ↔ z = w) →
      Fintype.card V + 2 ≤ maxLeaves G + bipartiteNumber G) : Claim182 G := by
  unfold Claim182
  by_cases h : peripheralSquareMaxDegree G + diameter G ≤ Fintype.card V + 1
  · exact h.trans hbound
  · obtain ⟨hd, hp, hfar⟩ := metric_excess_exception hc (Nat.lt_of_not_ge h)
    exact (metric_upper_bound hc).trans (hexception hd hp hfar)

/-- With the published order bound, failure is exactly the simultaneous metric
maximum and the smallest permitted value of the leaf and bipartite sum. -/
theorem conjecture182_failure_iff {G : SimpleGraph V} (hc : G.Connected)
    (hbound : Fintype.card V + 1 ≤ maxLeaves G + bipartiteNumber G) :
    ¬Claim182 G ↔
      (diameter G = 4 ∧ periphery (square G) = univ ∧
        ∃ v w, G.dist v w = 3 ∧ ∀ z, 2 < G.dist v z ↔ z = w) ∧
      maxLeaves G + bipartiteNumber G = Fintype.card V + 1 := by
  unfold Claim182
  rw [Nat.not_le]
  have hmax := metric_upper_bound hc
  constructor
  · intro h
    exact ⟨(metric_excess_iff hc).mp (by omega), by omega⟩
  · rintro ⟨hex, heq⟩
    have := (metric_excess_iff hc).mpr hex
    omega

/-- The published #173 lower bound suffices outside the exceptional case.
The bound is an explicit premise of this reduction. -/
theorem conjecture182_of_order_bound_of_diameter_ne_four {G : SimpleGraph V}
    (hc : G.Connected) (hd : diameter G ≠ 4)
    (hbound : Fintype.card V + 1 ≤ maxLeaves G + bipartiteNumber G) : Claim182 G := by
  by_contra h
  have hmetric : Fintype.card V + 1 < peripheralSquareMaxDegree G + diameter G :=
    lt_of_le_of_lt hbound (Nat.lt_of_not_ge h)
  exact hd (metric_excess_exception hc hmetric).1

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

/-- The metric upper bound proves exact #182 on bipartite graphs of order at least two. -/
theorem conjecture182_bipartite {G : SimpleGraph V} [Nontrivial V] (hc : G.Connected)
    (hbi : ∃ c : V → Bool, ∀ a b, G.Adj a b → c a ≠ c b) : Claim182 G := by
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
  unfold Claim182
  omega

#print axioms square_dist
#print axioms metric_upper_bound
#print axioms metric_excess_iff
#print axioms conjecture182_from_order_bounds
#print axioms conjecture182_failure_iff
#print axioms conjecture182_of_order_bound_of_diameter_ne_four
#print axioms conjecture182_bipartite

end
end Graffiti182
