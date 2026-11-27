import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Finset.Max

namespace Graffiti133

open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

private lemma take_length {u v : V} (p : G.Walk u v) (i : ℕ) (hi : i ≤ p.length) :
    (p.take i).length = i := by
  induction p generalizing i with
  | nil =>
    have ei : i = 0 := by simpa using hi
    subst i
    rfl
  | cons h q ih =>
    cases i with
    | zero => rfl
    | succ i =>
        change (q.take i).length + 1 = i + 1
        rw [ih i (by simp only [Walk.length_cons] at hi; omega)]

private lemma drop_length {u v : V} (p : G.Walk u v) (i : ℕ) :
    (p.drop i).length = p.length - i := by
  induction p generalizing i with
  | nil => cases i <;> simp [Walk.drop]
  | cons h q ih =>
    cases i with
    | zero => simp [Walk.drop]
    | succ i =>
        change (q.drop i).length = (q.length + 1) - (i + 1)
        rw [ih i, Nat.add_sub_add_right]

private lemma prefix_level (hc : G.Connected) {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) {i : ℕ} (hi : i ≤ p.length) :
    G.dist u (p.getVert i) = i := by
  have h₁ := G.dist_le (p.take i)
  rw [take_length p i hi] at h₁
  have h₂ := G.dist_le (p.drop i)
  rw [drop_length] at h₂
  have h₃ := hc.dist_triangle (u := u) (v := p.getVert i) (w := v)
  omega

/-- The vertices of a geodesic form an induced path, with no repetitions. -/
theorem geodesic_induced (hc : G.Connected) {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) :
    ∃ f : Fin (p.length + 1) → V, Function.Injective f ∧
      ∀ i j : Fin (p.length + 1), i < j → (G.Adj (f i) (f j) ↔ (i : ℕ) + 1 = j) := by
  let f (i : Fin (p.length + 1)) := p.getVert i
  have levels (i : Fin (p.length + 1)) : G.dist u (f i) = i :=
    prefix_level hc p hp (by omega)
  refine ⟨f, ?_, ?_⟩
  · intro i j hh
    apply Fin.ext
    rw [← levels i, ← levels j, hh]
  · intro i j hij
    constructor
    · intro h
      have h₀ := hc.dist_triangle (u := u) (v := f i) (w := f j)
      rw [levels i, levels j, dist_eq_one_iff_adj.mpr h] at h₀
      change i.val < j.val at hij
      omega
    · intro h
      have hi : i.val < p.length := by omega
      have h₀ := p.adj_getVert_succ hi
      change G.Adj (p.getVert i) (p.getVert j)
      rw [← h]
      exact h₀

/-- Absence of four-cycles, expressed as uniqueness of common neighbours. -/
def FourCycleFree (G : SimpleGraph V) : Prop :=
  ∀ a b x y, a ≠ b → G.Adj a x → G.Adj b x → G.Adj a y → G.Adj b y → x = y

/-- A geodesic can be extended by an adjacent vertex which does not complete
the terminal triangle, in a graph with no four-cycle. -/
theorem extend_geodesic (hc : G.Connected) (hc4 : FourCycleFree G)
    {u v w : V} (p : G.Walk u v) (hp : p.length = G.dist u v)
    (hlen : 0 < p.length) (hw : G.Adj v w)
    (hwpen : w ≠ p.getVert (p.length - 1))
    (hwtri : ¬ G.Adj (p.getVert (p.length - 1)) w) :
    ∃ f : Fin (p.length + 2) → V, Function.Injective f ∧
      ∀ i j : Fin (p.length + 2), i < j → (G.Adj (f i) (f j) ↔ (i : ℕ) + 1 = j) := by
  let d := p.length
  have dpos : 0 < d := hlen
  have hdp : d = G.dist u v := hp
  have last : p.getVert d = v := p.getVert_length
  have lvl (i : ℕ) (hi : i ≤ d) : G.dist u (p.getVert i) = i := prefix_level hc p hp hi
  have adj_old (i j : ℕ) (hi : i < j) (hj : j ≤ d) :
      G.Adj (p.getVert i) (p.getVert j) ↔ i + 1 = j := by
    constructor
    · intro ha
      have h := hc.dist_triangle (u := u) (v := p.getVert i) (w := p.getVert j)
      rw [lvl i (by omega), lvl j hj, dist_eq_one_iff_adj.mpr ha] at h
      omega
    · rintro rfl
      exact p.adj_getVert_succ (by omega)
  have pred_adj : G.Adj (p.getVert (d - 1)) v := by
    have e : d - 1 + 1 = d := by omega
    exact Eq.mp (congrArg (fun x => G.Adj (p.getVert (d - 1)) x) last)
      ((adj_old (d - 1) d (by omega) (by omega)).mpr e)
  have avoid (i : ℕ) (hi : i < d) : ¬ G.Adj (p.getVert i) w := by
    intro hiw
    have hdist := hc.dist_triangle (u := u) (v := w) (w := v)
    have hdist' := hc.dist_triangle (u := u) (v := p.getVert i) (w := w)
    rw [dist_eq_one_iff_adj.mpr hw.symm, ← hdp] at hdist
    rw [lvl i (by omega), dist_eq_one_iff_adj.mpr hiw] at hdist'
    by_cases hi' : i = d - 1
    · exact hwtri (hi' ▸ hiw)
    have e : i + 1 = d - 1 := by omega
    have he : p.getVert i ≠ v := by
      intro hh
      have h := lvl i (by omega)
      rw [hh, ← hdp] at h
      omega
    apply hwpen
    exact hc4 _ _ _ _ he hiw hw ((adj_old i (d - 1) (by omega) (by omega)).mpr e) pred_adj.symm
  have separate (i : ℕ) (hi : i ≤ d) : p.getVert i ≠ w := by
    intro he
    by_cases h : i = d
    · subst i
      exact hw.ne (last.symm.trans he)
    · have hp' : G.Adj (p.getVert i) (p.getVert d) := by rw [he, last]; exact hw.symm
      have eq := (adj_old i d (by omega) (by omega)).mp hp'
      have e : i = d - 1 := by omega
      exact hwpen (he.symm.trans (congrArg p.getVert e))
  let f (i : Fin (d + 2)) : V :=
    if i.val ≤ d then p.getVert i else w
  have f_old (i : Fin (d + 2)) (hi : i.val ≤ d) : f i = p.getVert i :=
    if_pos hi
  have f_new (i : Fin (d + 2)) (hi : ¬ i.val ≤ d) : f i = w := if_neg hi
  refine ⟨f, ?_, ?_⟩
  · intro i j h
    apply Fin.ext
    by_cases hi : i.val ≤ d <;> by_cases hj : j.val ≤ d
    · rw [f_old _ hi, f_old _ hj] at h
      rw [← lvl i hi, ← lvl j hj, h]
    · rw [f_old _ hi, f_new _ hj] at h
      exact (separate i hi h).elim
    · rw [f_new _ hi, f_old _ hj] at h
      exact (separate j hj h.symm).elim
    · omega
  · intro i j hij
    change i.val < j.val at hij
    by_cases hj : j.val ≤ d
    · have hi : i.val ≤ d := by omega
      rw [f_old _ hi, f_old _ hj]
      exact adj_old i j hij hj
    · have hi : i.val ≤ d := by omega
      rw [f_old _ hi, f_new _ hj]
      by_cases he : i.val = d
      · rw [he, last]
        exact iff_of_true hw (by omega)
      · exact iff_of_false (avoid i (by omega)) (by omega)

/-- Three distinct neighbours at the end of a positive-length geodesic
guarantee a one-vertex induced extension in a graph with no four-cycle. -/
theorem extend_geodesic_end_three (hc : G.Connected) (hc4 : FourCycleFree G)
    {u v : V} (p : G.Walk u v) (hp : p.length = G.dist u v)
    (hlen : 0 < p.length)
    (hthree : ∃ a b c, G.Adj v a ∧ G.Adj v b ∧ G.Adj v c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    ∃ f : Fin (p.length + 2) → V, Function.Injective f ∧
      ∀ i j : Fin (p.length + 2), i < j → (G.Adj (f i) (f j) ↔ (i : ℕ) + 1 = j) := by
  classical
  let z := p.getVert (p.length - 1)
  have zv : G.Adj z v := by
    have ht := p.adj_getVert_succ (i := p.length - 1) (by omega)
    rwa [show p.length - 1 + 1 = p.length by omega, p.getVert_length] at ht
  have exists_pair : ∃ a b, G.Adj v a ∧ G.Adj v b ∧ a ≠ z ∧ b ≠ z ∧ a ≠ b := by
    obtain ⟨a, b, c, ha, hb, hcc, hab, hac, hbc⟩ := hthree
    by_cases e : a = z
    · subst a
      exact ⟨b,c,hb,hcc,Ne.symm hab,Ne.symm hac,hbc⟩
    by_cases e₂ : b = z
    · subst b
      exact ⟨a,c,ha,hcc,e,Ne.symm hbc,hac⟩
    exact ⟨a,b,ha,hb,e,e₂,hab⟩
  obtain ⟨a,b,ha,hb,haz,hbz,hab⟩ := exists_pair
  by_cases hza : G.Adj z a
  · apply extend_geodesic hc hc4 p hp hlen hb hbz
    exact fun hzb => hab (hc4 z v a b zv.ne hza ha hzb hb)
  · exact extend_geodesic hc hc4 p hp hlen ha haz hza

#print axioms extend_geodesic_end_three

variable [Fintype V]

/-- The minimum, over all vertices, of the maximum distance to another vertex. -/
noncomputable def radius (G : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.image (fun u => Finset.univ.sup (G.dist u))).min.getD 0

/-- The radius plus one is a lower bound on the order of an induced path.
This proves the branch of WOW II #133 when the graph contains a four-cycle,
and more generally when the real-valued additive term is at most one. -/
theorem path_at_least_radius_add_one (G : SimpleGraph V) (hc : G.Connected) :
    ∃ k, radius G + 1 ≤ k ∧ ∃ f : Fin k → V, Function.Injective f ∧
      ∀ i j : Fin k, i < j → (G.Adj (f i) (f j) ↔ (i : ℕ) + 1 = j) := by
  classical
  letI := hc.nonempty
  let u : V := Classical.choice ‹Nonempty V›
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image Finset.univ (G.dist u)
    ⟨u, Finset.mem_univ _⟩
  have he : Finset.univ.sup (G.dist u) = G.dist u v :=
    le_antisymm (Finset.sup_le_iff.mpr hv) (Finset.le_sup (Finset.mem_univ v))
  have hr : radius G ≤ G.dist u v := by
    unfold radius
    have hm : G.dist u v ∈ Finset.univ.image (fun u => Finset.univ.sup (G.dist u)) :=
      Finset.mem_image.mpr ⟨u, Finset.mem_univ _, he⟩
    have hl := Finset.min_le hm
    cases hmin : (Finset.univ.image (fun u => Finset.univ.sup (G.dist u))).min with
    | top => exact Nat.zero_le _
    | coe d => simpa [hmin] using hl
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
  exact ⟨p.length + 1, Nat.add_le_add_right (hp ▸ hr) 1, geodesic_induced hc p hp⟩

private lemma radius_le_ecc (G : SimpleGraph V) (u : V) :
    radius G ≤ Finset.univ.sup (G.dist u) := by
  classical
  unfold radius
  have hm : Finset.univ.sup (G.dist u) ∈
      Finset.univ.image (fun u => Finset.univ.sup (G.dist u)) :=
    Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  have hl := Finset.min_le hm
  cases hmin : (Finset.univ.image (fun u => Finset.univ.sup (G.dist u))).min with
  | top => exact Nat.zero_le _
  | coe d => simpa [hmin] using hl

/-- The order is at least radius plus two for connected four-cycle-free
graphs that are not complete. This gives the real-average ≤ 2 band except
for the complete graphs (whose local independence is at most one). -/
theorem path_at_least_radius_add_two (G : SimpleGraph V) (hc : G.Connected)
    (hc4 : FourCycleFree G) (hnotcomplete : ∃ x y, x ≠ y ∧ ¬ G.Adj x y) :
    ∃ k, radius G + 2 ≤ k ∧ ∃ f : Fin k → V, Function.Injective f ∧
      ∀ i j : Fin k, i < j → (G.Adj (f i) (f j) ↔ (i : ℕ) + 1 = j) := by
  classical
  let r := radius G
  by_cases hfar : ∃ x y, r < G.dist x y
  · obtain ⟨x, y, hd⟩ := hfar
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist x y
    exact ⟨p.length + 1, by omega, geodesic_induced hc p hp⟩
  push_neg at hfar
  have hr : 2 ≤ r := by
    obtain ⟨x,y,hne,hnadj⟩ := hnotcomplete
    have hd := hc.one_lt_dist_of_ne_of_not_adj hne hnadj
    exact hd.trans_le (hfar x y)
  have exact_ecc (x : V) : ∃ y, G.dist x y = r := by
    obtain ⟨y, _, hy⟩ := Finset.exists_max_image Finset.univ (G.dist x)
      ⟨x, Finset.mem_univ _⟩
    have he : Finset.univ.sup (G.dist x) ≤ G.dist x y := Finset.sup_le_iff.mpr hy
    exact ⟨y, le_antisymm (hfar x y) ((radius_le_ecc G x).trans he)⟩
  by_cases hd3 : ∃ v a b c : V, G.Adj v a ∧ G.Adj v b ∧ G.Adj v c ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c
  · obtain ⟨v,a,b,c,ha,hb,hc',hab,hac,hbc⟩ := hd3
    obtain ⟨u, hu⟩ := exact_ecc v
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
    have hplen : p.length = r := by rw [hp, SimpleGraph.dist_comm, hu]
    exact ⟨p.length + 2, by omega, extend_geodesic_end_three hc hc4 p hp
      (by omega) ⟨a,b,c,ha,hb,hc',hab,hac,hbc⟩⟩
  letI : Nonempty V := hc.nonempty
  let u : V := Classical.choice ‹Nonempty V›
  obtain ⟨v, hv⟩ := exact_ecc u
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
  have hplen : p.length = r := hp.trans hv
  let z := p.getVert (p.length - 1)
  have zv : G.Adj z v := by
    have ht := p.adj_getVert_succ (i := p.length - 1) (by omega)
    rwa [show p.length - 1 + 1 = p.length by omega, p.getVert_length] at ht
  have other_neighbor : ∃ w, G.Adj v w ∧ w ≠ z := by
    by_contra! hh
    obtain ⟨a, ha⟩ := exact_ecc z
    have hne : a ≠ v := by
      intro e
      have H : G.dist z v = 1 := dist_eq_one_iff_adj.mpr zv
      rw [e, H] at ha
      omega
    obtain ⟨q,hq⟩ := hc.exists_walk_length_eq_dist v a
    have qpos : 0 < q.length := by
      cases q with
      | nil => exact (hne rfl).elim
      | cons e q => simp
    have qadj : G.Adj v (q.getVert 1) := by
      simpa using q.adj_getVert_succ (i := 0) qpos
    have eq := hh _ qadj
    have hqle := G.dist_le (q.drop 1)
    rw [drop_length, eq, ha, hq] at hqle
    have := hfar v a
    omega
  obtain ⟨w, hw, hwz⟩ := other_neighbor
  have hwtri : ¬ G.Adj z w := by
    intro hzw
    let b := p.getVert (p.length - 2)
    have bz : G.Adj b z := by
      have ht := p.adj_getVert_succ (i := p.length - 2) (by omega)
      rwa [show p.length - 2 + 1 = p.length - 1 by omega] at ht
    have hb : G.dist u b = p.length - 2 := prefix_level hc p hp (by omega)
    have hbv : b ≠ v := by
      intro e
      rw [e, ← hp] at hb
      omega
    have hbw : b ≠ w := by
      intro e
      have hd := hc.dist_triangle (u := u) (v := w) (w := v)
      rw [dist_eq_one_iff_adj.mpr hw.symm, ← hp, ← e, hb] at hd
      omega
    exact hd3 ⟨z,b,v,w,bz.symm,zv,hzw,hbv,hbw,hw.ne⟩
  exact ⟨p.length + 2, by omega,
    extend_geodesic hc hc4 p hp (by omega) hw hwz hwtri⟩

open scoped BigOperators

/-- Finite independent subsets of the open neighborhood. -/
noncomputable def localIndependentSets (G : SimpleGraph V) (v : V) : Finset (Finset V) := by
  classical
  exact ((Finset.univ.filter (G.Adj v)).powerset.filter
    (fun A => ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y))

private theorem mem_localIndependentSets {G : SimpleGraph V} {v : V} {A : Finset V} :
    A ∈ localIndependentSets G v ↔ (∀ x ∈ A, G.Adj v x) ∧
      (∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) := by
  classical
  simp only [localIndependentSets, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_iff, Finset.mem_univ, true_and]

/-- The local independence number of the open neighbourhood. -/
noncomputable def localIndependence (G : SimpleGraph V) (v : V) : ℕ :=
  (localIndependentSets G v).sup Finset.card

/-- Exact (not rounded) mean of the local independence numbers. -/
noncomputable def averageLocal (G : SimpleGraph V) : ℚ :=
  (∑ v, (localIndependence G v : ℚ)) / Fintype.card V

/-- The exact right-hand side of WOW II #133. -/
noncomputable def rhs133 (G : SimpleGraph V) : ℚ := by
  classical
  exact (radius G : ℚ) + (averageLocal G) ^ (if FourCycleFree G then (1 : ℕ) else 0)

/-- WOW II #133 for graphs with four-cycles, or with average local independence
at most two. The open band is four-cycle-free graphs with average greater than two. -/
theorem conjecture133_low_average_or_four_cycle (G : SimpleGraph V) (hc : G.Connected)
    (h : ¬ FourCycleFree G ∨ averageLocal G ≤ 2) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, Function.Injective f ∧
      ∀ i j : Fin k, i < j → (G.Adj (f i) (f j) ↔ (i : ℕ) + 1 = j) := by
  classical
  by_cases hc4 : FourCycleFree G
  · have havg := h.resolve_left (not_not.mpr hc4)
    by_cases hn : ∃ x y, x ≠ y ∧ ¬ G.Adj x y
    · obtain ⟨k, hk, p⟩ := path_at_least_radius_add_two G hc hc4 hn
      have hk' : (radius G : ℚ) + 2 ≤ (k : ℚ) := by exact_mod_cast hk
      refine ⟨k, ?_, p⟩
      simp only [rhs133, if_pos hc4, pow_one]
      exact (add_le_add_left havg _).trans hk'
    · push_neg at hn
      have hL (v : V) : localIndependence G v ≤ 1 := by
        apply Finset.sup_le_iff.mpr
        intro B hB
        apply Finset.card_le_one.mpr
        intro x hx y hy
        exact Classical.byContradiction (fun hxy => (mem_localIndependentSets.mp hB).2 x hx y hy (hn x y hxy))
      haveI : Nonempty V := hc.nonempty
      have hn' : 0 < (Fintype.card V : ℚ) := by exact_mod_cast Fintype.card_pos (α := V)
      have hmean : averageLocal G ≤ 1 := by
        apply (div_le_iff₀ hn').mpr
        simpa using (Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) =>
          show (localIndependence G v : ℚ) ≤ 1 by exact_mod_cast hL v))
      obtain ⟨k, hk, p⟩ := path_at_least_radius_add_one G hc
      have hk' : (radius G : ℚ) + 1 ≤ (k : ℚ) := by exact_mod_cast hk
      refine ⟨k, ?_, p⟩
      simp only [rhs133, if_pos hc4, pow_one]
      exact (add_le_add_left hmean _).trans hk'
  · obtain ⟨k, hk, p⟩ := path_at_least_radius_add_one G hc
    have hk' : (radius G : ℚ) + 1 ≤ (k : ℚ) := by exact_mod_cast hk
    exact ⟨k, by simpa only [rhs133, if_neg hc4, pow_zero] using hk', p⟩

/-- The original conjecture up to mean three whenever there is a geodesic of
length at least radius + 2, or one of length at least radius + 1 with a
degree-three endpoint (in particular, a non-self-centered graph of minimum
degree three). The four-cycle case is unconditional. -/
theorem conjecture133_mean_three_of_long_geodesic (G : SimpleGraph V) (hc : G.Connected)
    (hmean : averageLocal G ≤ 3)
    (hfar : (∃ u v, radius G + 2 ≤ G.dist u v) ∨
      ∃ u v a b c, radius G + 1 ≤ G.dist u v ∧
        G.Adj v a ∧ G.Adj v b ∧ G.Adj v c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, Function.Injective f ∧
      ∀ i j : Fin k, i < j → (G.Adj (f i) (f j) ↔ (i : ℕ) + 1 = j) := by
  classical
  by_cases ht : FourCycleFree G
  · have finish (k : ℕ) (hk : radius G + 3 ≤ k) : rhs133 G ≤ (k : ℚ) := by
      have hk' : (radius G : ℚ) + 3 ≤ (k : ℚ) := by exact_mod_cast hk
      simpa only [rhs133, if_pos ht, pow_one] using (add_le_add_left hmean _).trans hk'
    rcases hfar with ⟨u,v,h⟩ | ⟨u,v,a,b,c,h,ha,hb,hc',hab,hac,hbc⟩
    · obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist u v
      exact ⟨p.length + 1, finish _ (by omega), geodesic_induced hc p hp⟩
    · obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist u v
      exact ⟨p.length + 2, finish _ (by omega),
        extend_geodesic_end_three hc ht p hp (by omega) ⟨a,b,c,ha,hb,hc',hab,hac,hbc⟩⟩
  · exact conjecture133_low_average_or_four_cycle G hc (Or.inl ht)

#print axioms conjecture133_mean_three_of_long_geodesic
#print axioms conjecture133_low_average_or_four_cycle
#print axioms path_at_least_radius_add_two
#print axioms path_at_least_radius_add_one

open Finset

universe u

/-- An induced path indexed in its path order. -/
def InducedPath {W : Type*} (H : SimpleGraph W) {k : ℕ} (f : Fin k → W) : Prop :=
  Function.Injective f ∧
    ∀ i j : Fin k, i < j → (H.Adj (f i) (f j) ↔ (i : ℕ) + 1 = j)

/-- Exact catalogue reading, with the floor taken before exponentiation. -/
noncomputable def catalogueRhs133 (G : SimpleGraph V) : ℤ := by
  classical
  exact (radius G : ℤ) + (⌊averageLocal G⌋ : ℤ) ^ (if FourCycleFree G then (1 : ℕ) else 0)

omit [Fintype V] in
theorem fourCycleFree_iff (G : SimpleGraph V) :
    FourCycleFree G ↔ ¬ ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧
      b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a := by
  constructor
  · rintro h ⟨a,b,c,d,_,hac,_,_,hbd,_,hab,hbc,hcd,hda⟩
    exact hbd (h a c b d hac hab hbc.symm hda.symm hcd)
  · intro h a c b d hac hab hcb had hcd
    by_contra hbd
    exact h ⟨a,b,c,d,hab.ne,hac,had.ne,hcb.ne.symm,hbd,hcd.ne,hab,hcb.symm,hcd,had.symm⟩

private theorem radius_le_dist_exists (G : SimpleGraph V) (v : V) :
    ∃ w, radius G ≤ G.dist v w := by
  obtain ⟨w,_,hw⟩ := exists_max_image univ (G.dist v) ⟨v,mem_univ _⟩
  refine ⟨w,(radius_le_ecc G v).trans (Finset.sup_le_iff.mpr hw)⟩

private theorem exists_radius_vertex (G : SimpleGraph V) (hc : G.Connected) :
    ∃ c, ∀ v, G.dist c v ≤ radius G := by
  classical
  letI := hc.nonempty
  obtain ⟨c,_,hc⟩ := exists_min_image univ (fun v => univ.sup (G.dist v)) univ_nonempty
  have hr : (univ.image fun v => univ.sup (G.dist v)).min =
      (↑(univ.sup (G.dist c)) : WithTop ℕ) := by
    apply le_antisymm
    · exact min_le (mem_image.mpr ⟨c,mem_univ _,rfl⟩)
    · apply Finset.le_min
      intro n hn
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hn
      exact WithTop.coe_le_coe.mpr (hc w hw)
  refine ⟨c,fun v => ?_⟩
  unfold radius
  rw [hr]
  exact le_sup (mem_univ v)

omit [Fintype V] in
private theorem walk_dist_le_index (hc : G.Connected) {a b : V} (p : G.Walk a b)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) ≤ j-i := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have h₁ := ih (by omega)
    have h₂ := dist_eq_one_iff_adj.mpr (p.adj_getVert_succ (i := j) (by omega))
    have h₃ := hc.dist_triangle (u := p.getVert i) (v := p.getVert j) (w := p.getVert (j+1))
    omega

omit [Fintype V] in
private theorem walk_dist_bound (hc : G.Connected) {a b : V} (p : G.Walk a b)
    (i j : ℕ) (hi : i ≤ p.length) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) ≤ (i-j)+(j-i) := by
  by_cases h : i ≤ j
  · have h₁ := walk_dist_le_index hc p i j h hj
    omega
  · rw [SimpleGraph.dist_comm]
    have h₁ := walk_dist_le_index hc p j i (by omega) hi
    omega

omit [Fintype V] in
private theorem geod_adj_iff (hc : G.Connected) {a b : V} (p : G.Walk a b)
    (hp : p.length = G.dist a b) {i j : ℕ} (hij : i < j) (hj : j ≤ p.length) :
    G.Adj (p.getVert i) (p.getVert j) ↔ i+1=j := by
  constructor
  · intro h
    have ht := hc.dist_triangle (u := a) (v := p.getVert i) (w := p.getVert j)
    rw [prefix_level hc p hp (i := i) (by omega),prefix_level hc p hp hj,
      dist_eq_one_iff_adj.mpr h] at ht
    omega
  · rintro rfl
    exact p.adj_getVert_succ (by omega)

omit [Fintype V] in
private theorem geod_inj (hc : G.Connected) {a b : V} (p : G.Walk a b)
    (hp : p.length = G.dist a b) {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (h : p.getVert i = p.getVert j) : i = j := by
  rw [← prefix_level hc p hp hi,← prefix_level hc p hp hj,h]

omit [Fintype V] in
/-- The two geodesics used in Chung's radius bound. We join them through their
common origin, except when a chord links their first vertices. -/
private theorem chung_two_geodesics (hc : G.Connected) {c x w : V}
    (q : G.Walk c x) (p : G.Walk c w)
    (hq : q.length = G.dist c x) (hp : p.length = G.dist c w)
    (hql : 2 ≤ q.length) (hpl : p.length + 1 ≤ q.length)
    (hw : q.length ≤ G.dist (q.getVert 2) w) :
    ∃ k, 2*q.length-1 ≤ k ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  let l := p.length
  let r := q.length
  have hLow : r-2 ≤ l := by
    have ht := hc.dist_triangle (u := q.getVert 2) (v := c) (w := w)
    rw [SimpleGraph.dist_comm (u := q.getVert 2) (v := c),
      prefix_level hc q hq hql,← hp] at ht
    omega
  have hDist (i : ℕ) (hi : i ≤ l) : r + i ≤ G.dist (q.getVert 2) (p.getVert i) + l := by
    have ht := hc.dist_triangle (u := q.getVert 2) (v := p.getVert i) (w := w)
    have hi' := G.dist_le (p.drop i)
    rw [drop_length] at hi'
    omega
  have disj (i j : ℕ) (hi : 0 < i) (hil : i ≤ l) (hjr : j ≤ r) :
      p.getVert i ≠ q.getVert j := by
    intro he
    have ij : i = j := by rw [← prefix_level hc p hp hil,← prefix_level hc q hq hjr,he]
    have hi' := hDist i hil
    rw [he] at hi'
    have hmax := walk_dist_bound hc q 2 j hql hjr
    omega
  have edge (i j : ℕ) (hi : 0 < i) (hil : i ≤ l) (hjr : j ≤ r)
      (h : G.Adj (p.getVert i) (q.getVert j)) : i = 1 ∧ (j = 0 ∨ (j = 1 ∧ l+1=r)) := by
    have ht₁ := hc.dist_triangle (u := c) (v := p.getVert i) (w := q.getVert j)
    have ht₂ := hc.dist_triangle (u := c) (v := q.getVert j) (w := p.getVert i)
    rw [prefix_level hc p hp hil,prefix_level hc q hq hjr,dist_eq_one_iff_adj.mpr h] at ht₁
    rw [prefix_level hc p hp hil,prefix_level hc q hq hjr,dist_eq_one_iff_adj.mpr h.symm] at ht₂
    have ht₃ := hc.dist_triangle (u := q.getVert 2) (v := q.getVert j) (w := p.getVert i)
    rw [dist_eq_one_iff_adj.mpr h.symm] at ht₃
    have hmax := walk_dist_bound hc q 2 j hql hjr
    have hmin := hDist i hil
    by_cases hj0 : j = 0
    · exact ⟨by omega,Or.inl hj0⟩
    · exact ⟨by omega,Or.inr ⟨by omega,by omega⟩⟩
  let s : ℕ := if 0 < l ∧ G.Adj (p.getVert 1) (q.getVert 1) then 1 else 0
  have hs : s ≤ 1 := by unfold s; split <;> omega
  have hsize : 2*r-1 ≤ l+r+1-s := by
    unfold s
    split
    next h =>
      have he := (edge 1 1 (by omega) (by have := h.1; omega) (by omega) h.2).2
      omega
    next _ => omega
  let k := l+r+1-s
  let f (i : Fin k) : V := if i.val < l then p.getVert (l-i.val)
    else q.getVert (i.val-l+s)
  have pIdx (i : Fin k) (hi : i.val < l) : f i = p.getVert (l-i.val) := if_pos hi
  have qIdx (i : Fin k) (hi : ¬ i.val < l) : f i = q.getVert (i.val-l+s) := if_neg hi
  refine ⟨k,hsize,f,?_,?_⟩
  · intro i j h
    apply Fin.ext
    by_cases hi : i.val < l <;> by_cases hj : j.val < l
    · rw [pIdx _ hi,pIdx _ hj] at h
      have he := geod_inj hc p hp (i := l-i.val) (j := l-j.val) (by omega) (by omega) h
      omega
    · rw [pIdx _ hi,qIdx _ hj] at h
      exact (disj (l-i.val) (j.val-l+s) (by omega) (by omega) (by have := j.isLt; omega) h).elim
    · rw [qIdx _ hi,pIdx _ hj] at h
      exact (disj (l-j.val) (i.val-l+s) (by omega) (by omega) (by have := i.isLt; omega) h.symm).elim
    · rw [qIdx _ hi,qIdx _ hj] at h
      have he := geod_inj hc q hq (i := i.val-l+s) (j := j.val-l+s)
        (by have := i.isLt; omega) (by have := j.isLt; omega) h
      omega
  · intro i j hij
    change i.val < j.val at hij
    have hji := j.isLt
    by_cases hj : j.val < l
    · have hi : i.val < l := by omega
      rw [pIdx _ hi,pIdx _ hj, G.adj_comm,geod_adj_iff hc p hp (by omega) (by omega)]
      omega
    · by_cases hi : i.val < l
      · rw [pIdx _ hi,qIdx _ hj]
        constructor
        · intro h
          have he := edge (l-i.val) (j.val-l+s) (by omega) (by omega) (by omega) h
          obtain ⟨hi',hj' | ⟨hj',_⟩⟩ := he
          · omega
          · have hc' : G.Adj (p.getVert 1) (q.getVert 1) := by rwa [hi',hj'] at h
            have hS : s = 1 := if_pos ⟨by omega,hc'⟩
            omega
        · intro he
          have hpi : l-i.val = 1 := by omega
          have hqj : j.val-l+s = s := by omega
          rw [hpi,hqj]
          by_cases h : 0 < l ∧ G.Adj (p.getVert 1) (q.getVert 1)
          · rw [show s = 1 from if_pos h]
            exact h.2
          · rw [show s = 0 from if_neg h,q.getVert_zero]
            exact (by simpa using p.adj_getVert_succ (i := 0) (by omega : 0 < p.length) :
              G.Adj c (p.getVert 1)).symm
      · rw [qIdx _ hi,qIdx _ hj,geod_adj_iff hc q hq (by omega) (by omega)]
        omega

omit [Fintype V] in
private theorem walk_lift_reachable {S : Set V} {a b : V} (p : G.Walk a b)
    (hAll : ∀ w ∈ p.support, w ∈ S) :
    (G.induce S).Reachable ⟨a,hAll _ p.start_mem_support⟩ ⟨b,hAll _ p.end_mem_support⟩ := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons a t b h p ih =>
    have hp (w : V) (hw : w ∈ p.support) : w ∈ S :=
      hAll _ (by simp [Walk.support_cons,hw])
    have hStep : (G.induce S).Adj ⟨a,hAll _ (by simp)⟩ ⟨t,hp _ p.start_mem_support⟩ := h
    exact hStep.reachable.trans (ih hp)

omit [Fintype V] in
private theorem farthest_deletion_connected (hc : G.Connected) {u x : V} (hux : u ≠ x)
    (hmax : ∀ v, G.dist u v ≤ G.dist u x) :
    (G.induce {v | v ≠ x}).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨u,hux⟩,?_⟩
  rintro ⟨v,hv⟩
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist u v
  have hS : {w | w ∈ p.support} ⊆ {w | w ≠ x} := by
    intro w hw hEq
    subst w
    obtain ⟨i,hix,hi⟩ := Walk.mem_support_iff_exists_getVert.mp hw
    have hdist := prefix_level hc p hp hi
    rw [hix] at hdist
    have hlen := hmax v
    have he : i = p.length := by omega
    rw [he,p.getVert_length] at hix
    exact hv hix
  exact walk_lift_reachable p (fun _ h => hS h)

omit [Fintype V] in
private theorem dist_le_induce_of_connected {S : Set V}
    (h : (G.induce S).Connected) (a b : S) :
    G.dist a.val b.val ≤ (G.induce S).dist a b := by
  obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist a b
  let f := (SimpleGraph.Embedding.induce (G := G) S).toHom
  have hi := G.dist_le (p.map f)
  rwa [Walk.length_map,hp] at hi

private theorem critical_radius_arms (G : SimpleGraph V) (hc : G.Connected) {x c : V}
    (hr : 2 ≤ radius G) (hcx : G.dist c x = radius G)
    (hNear : ∀ v, v ≠ x → G.dist c v < radius G) :
    ∃ k, 2*radius G-1 ≤ k ∧ ∃ f : Fin k → V, InducedPath G f := by
  obtain ⟨q,hq⟩ := hc.exists_walk_length_eq_dist c x
  have hQ : q.length = radius G := hq.trans hcx
  obtain ⟨w,hw⟩ := radius_le_dist_exists G (q.getVert 2)
  have hne : w ≠ x := by
    intro he
    have ht := G.dist_le (q.drop 2)
    rw [drop_length] at ht
    rw [he] at hw
    omega
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist c w
  obtain ⟨k,hk,f,hf⟩ := chung_two_geodesics hc q p hq hp (by omega)
    (by have := hNear w hne; omega) (by omega)
  exact ⟨k,by omega,f,hf⟩

/-- Chung's induced path theorem, from Erdős–Saks–Sós, Theorem 2.2. -/
theorem path_at_least_twice_radius_sub_one {W : Type u} [Fintype W]
    (H : SimpleGraph W) (hc : H.Connected) :
    ∃ k, 2*radius H-1 ≤ k ∧ ∃ f : Fin k → W, InducedPath H f := by
  classical
  let Claim (n : ℕ) := ∀ (U : Type u) [Fintype U], Fintype.card U = n →
    ∀ (G : SimpleGraph U), G.Connected →
      ∃ k, 2*radius G-1 ≤ k ∧ ∃ f : Fin k → U, InducedPath G f
  have key : ∀ n, Claim n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U _ hn G hG
      by_cases hSmall : radius G ≤ 1
      · obtain ⟨k,hk,f,hf⟩ := path_at_least_radius_add_one G hG
        exact ⟨k,by omega,f,hf⟩
      let u : U := Classical.choice hG.nonempty
      obtain ⟨x,_,hx⟩ := exists_max_image univ (G.dist u) ⟨u,mem_univ _⟩
      have hMax (v : U) : G.dist u v ≤ G.dist u x := hx v (mem_univ _)
      have hFar := (radius_le_ecc G u).trans (Finset.sup_le_iff.mpr hx)
      have hux : u ≠ x := by
        intro h
        rw [← h] at hFar
        simp only [dist_self] at hFar
        omega
      let S : Set U := {v | v ≠ x}
      let J := G.induce S
      have hJ : J.Connected := farthest_deletion_connected hG hux hMax
      by_cases hRad : radius G ≤ radius J
      · have hCard : Fintype.card S < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt (p := fun v : U => v ≠ x) (x := x) (not_not.mpr rfl)
        obtain ⟨k,hk,f,hf⟩ := ih _ hCard S rfl J hJ
        exact ⟨k,by omega,fun i => (f i).val,Subtype.val_injective.comp hf.1,hf.2⟩
      obtain ⟨c,hc⟩ := exists_radius_vertex J hJ
      have hNear (v : U) (hv : v ≠ x) : G.dist c.val v < radius G :=
        ((dist_le_induce_of_connected hJ c ⟨v,hv⟩).trans (hc _)).trans_lt (by omega)
      have hLow : radius G ≤ G.dist c.val x := by
        obtain ⟨v,hv⟩ := radius_le_dist_exists G c.val
        by_cases he : v = x
        · simpa only [he] using hv
        · exact (not_lt_of_ge hv (hNear v he)).elim
      obtain ⟨p,_⟩ := hG.exists_walk_length_eq_dist x u
      have ppos : ¬ p.Nil := Walk.not_nil_of_ne hux.symm
      have hAdj := p.adj_snd ppos
      have hUpper := hG.dist_triangle (u := c.val) (v := p.snd) (w := x)
      rw [dist_eq_one_iff_adj.mpr hAdj.symm] at hUpper
      have hNearN := hNear p.snd hAdj.ne.symm
      exact critical_radius_arms G hG (by omega) (by omega) hNear
  exact key _ W rfl H hc

theorem conjecture133_high_radius (G : SimpleGraph V) (hc : G.Connected)
    (h : ⌊averageLocal G⌋ < (radius G : ℤ)) :
    ∃ k : ℕ, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases hC : FourCycleFree G
  · obtain ⟨k,hk,f,hf⟩ := path_at_least_twice_radius_sub_one G hc
    have hpos : 0 ≤ ⌊averageLocal G⌋ := Int.floor_nonneg.mpr
      (div_nonneg (sum_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _))
    refine ⟨k,?_,f,hf⟩
    simp only [catalogueRhs133,if_pos hC,pow_one]
    omega
  · obtain ⟨k,hk,f,hf⟩ := path_at_least_radius_add_one G hc
    exact ⟨k,by simp only [catalogueRhs133,if_neg hC,pow_zero]; omega,f,hf⟩

theorem conjecture133_floor_le_two_or_four_cycle (G : SimpleGraph V) (hc : G.Connected)
    (h : ¬FourCycleFree G ∨ ⌊averageLocal G⌋ ≤ 2) :
    ∃ k : ℕ, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases hC : FourCycleFree G
  · by_cases hNC : ∃ u v, u ≠ v ∧ ¬ G.Adj u v
    · obtain ⟨k,hk,f,hf⟩ := path_at_least_radius_add_two G hc hC hNC
      have ha := h.resolve_left (not_not.mpr hC)
      exact ⟨k,by simp only [catalogueRhs133,if_pos hC,pow_one]; omega,f,hf⟩
    · push_neg at hNC
      have hL (v : V) : localIndependence G v ≤ 1 := by
        apply Finset.sup_le_iff.mpr
        intro B hB
        apply Finset.card_le_one.mpr
        intro x hx y hy
        exact Classical.byContradiction fun hxy => (mem_filter.mp hB).2 x hx y hy (hNC x y hxy)
      haveI : Nonempty V := hc.nonempty
      have hN : 0 < (Fintype.card V : ℚ) := by exact_mod_cast Fintype.card_pos (α := V)
      have hAvg : averageLocal G ≤ 1 := by
        apply (div_le_iff₀ hN).mpr
        simpa using (Finset.sum_le_sum (fun v (_ : v ∈ (univ : Finset V)) =>
          show (localIndependence G v : ℚ) ≤ 1 by exact_mod_cast hL v))
      have hflo : ⌊averageLocal G⌋ ≤ 1 := by
        have hh := Int.floor_mono hAvg
        simpa using hh
      obtain ⟨k,hk,f,hf⟩ := path_at_least_radius_add_one G hc
      exact ⟨k,by simp only [catalogueRhs133,if_pos hC,pow_one]; omega,f,hf⟩
  · obtain ⟨k,hk,f,hf⟩ := path_at_least_radius_add_one G hc
    exact ⟨k,by simp only [catalogueRhs133,if_neg hC,pow_zero]; omega,f,hf⟩

#print axioms fourCycleFree_iff
#print axioms path_at_least_twice_radius_sub_one
#print axioms conjecture133_high_radius
#print axioms conjecture133_floor_le_two_or_four_cycle

section Bipartite

omit [Fintype V] in
/-- An induced path remains induced when a new vertex is joined solely
to its first vertex. -/
private theorem prepend_induced_with_positions {k : ℕ} (hk : 0 < k) {f : Fin k → V}
    (hf : InducedPath G f) (w : V) (hnew : ∀ i, w ≠ f i)
    (h₀ : G.Adj w (f ⟨0,hk⟩)) (h₁ : ∀ i : Fin k, 0 < i.val → ¬ G.Adj w (f i)) :
    ∃ ff : Fin (k+1) → V, InducedPath G ff ∧ ff ⟨0,by omega⟩ = w ∧
      ∀ i : Fin (k+1), ∀ hi : 0 < i.val, ff i = f ⟨i.val-1,by have := i.isLt; omega⟩ := by
  let F (i : Fin (k+1)) : V :=
    if h : i.val = 0 then w else f ⟨i.val-1,by omega⟩
  have head (i : Fin (k+1)) (hi : i.val = 0) : F i = w := dif_pos hi
  have tail (i : Fin (k+1)) (hi : i.val ≠ 0) :
      F i = f ⟨i.val-1,by have := i.isLt; omega⟩ := dif_neg hi
  refine ⟨F,⟨?_,?_⟩,head _ rfl, fun i hi => tail i (by omega)⟩
  · intro i j h
    apply Fin.ext
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · omega
    · rw [head _ hi,tail _ hj] at h
      exact (hnew _ h).elim
    · rw [tail _ hi,head _ hj] at h
      exact (hnew _ h.symm).elim
    · rw [tail _ hi,tail _ hj] at h
      have hh := congrArg Fin.val (hf.1 h)
      change i.val-1 = j.val-1 at hh
      omega
  · intro i j hij
    change i.val < j.val at hij
    have hji := j.isLt
    have hj : j.val ≠ 0 := by omega
    rw [tail _ hj]
    by_cases hi : i.val = 0
    · rw [head _ hi]
      by_cases h : j.val = 1
      · have hindex : (⟨j.val-1,by omega⟩ : Fin k) = ⟨0,hk⟩ :=
          Fin.ext (by change j.val-1=0; omega)
        rw [hindex]
        exact iff_of_true h₀ (by omega)
      · exact iff_of_false (h₁ _ (by change 0 < j.val-1; omega)) (by omega)
    · rw [tail _ hi,hf.2 _ _ (by change i.val-1 < j.val-1; omega)]
      change (i.val-1+1 = j.val-1) ↔ (i.val+1 = j.val)
      omega

omit [Fintype V] in
private theorem prepend_induced {k : ℕ} (hk : 0 < k) {f : Fin k → V}
    (hf : InducedPath G f) (w : V) (hnew : ∀ i, w ≠ f i)
    (h₀ : G.Adj w (f ⟨0,hk⟩)) (h₁ : ∀ i : Fin k, 0 < i.val → ¬ G.Adj w (f i)) :
    ∃ ff : Fin (k+1) → V, InducedPath G ff := by
  obtain ⟨ff,hff,_,_⟩ := prepend_induced_with_positions hk hf w hnew h₀ h₁
  exact ⟨ff,hff⟩

omit [Fintype V] in
private theorem two_colors_same {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

omit [Fintype V] in
private theorem induced_color_parity (color : V → Bool)
    (proper : ∀ ⦃x y⦄, G.Adj x y → color x ≠ color y)
    {k : ℕ} (hk : 0 < k) {f : Fin k → V} (hf : InducedPath G f) (i : Fin k) :
    color (f i) = color (f ⟨0,hk⟩) ↔ i.val % 2 = 0 := by
  have step : ∀ n : ℕ, ∀ hn : n < k,
      color (f ⟨n,hn⟩) = color (f ⟨0,hk⟩) ↔ n % 2 = 0 := by
    intro n
    induction n with
    | zero => intro hn; simp
    | succ n ih =>
      intro hn
      let a := f ⟨n,by omega⟩
      let b := f ⟨n+1,hn⟩
      let c := f ⟨0,hk⟩
      have ha : G.Adj a b := (hf.2 _ _ (by change n < n+1; omega)).mpr rfl
      have hn' := proper ha
      have hprev : color a = color c ↔ n % 2 = 0 := ih _
      have hh : color b = color c ↔ color a ≠ color c := by
        constructor
        · intro hb hc
          exact hn' (hc.trans hb.symm)
        · exact fun h => two_colors_same hn'.symm h.symm
      change color b = color c ↔ (n+1) % 2 = 0
      rw [hh,Ne,hprev]
      omega
  exact step _ i.isLt

private theorem max_induced_path_of_path (G : SimpleGraph V) {k₀ : ℕ}
    (f₀ : Fin k₀ → V) (hf₀ : InducedPath G f₀) :
    ∃ k, k₀ ≤ k ∧ ∃ f : Fin k → V, InducedPath G f ∧
        ∀ l, (∃ g : Fin l → V, InducedPath G g) → l ≤ k := by
  classical
  let S := (range (Fintype.card V + 1)).filter (fun k => ∃ f : Fin k → V, InducedPath G f)
  have hm (l : ℕ) (h : ∃ g : Fin l → V, InducedPath G g) : l ∈ S := by
    obtain ⟨g,hg⟩ := h
    have hbound := Fintype.card_le_of_injective g hg.1
    rw [Fintype.card_fin] at hbound
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),g,hg⟩
  obtain ⟨k,hS,hk⟩ := exists_max_image S id ⟨k₀,hm _ ⟨f₀,hf₀⟩⟩
  obtain ⟨f,hf⟩ := (mem_filter.mp hS).2
  exact ⟨k,hk _ (hm _ ⟨f₀,hf₀⟩),f,hf,fun l hl => hk _ (hm _ hl)⟩

/-- A bipartite four-cycle-free graph of minimum degree at least d≥2
has an induced path of order at least 2d+1. -/
theorem bipartite_path_of_min_degree [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc4 : FourCycleFree G) (color : V → Bool)
    (proper : ∀ ⦃x y⦄, G.Adj x y → color x ≠ color y)
    (d : ℕ) (hd : 2 ≤ d) (hdeg : ∀ v, d ≤ G.degree v) :
    ∃ k, 2*d+1 ≤ k ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  let v : V := Classical.choice ‹Nonempty V›
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp
    (show 1 < (G.neighborFinset v).card from lt_of_lt_of_le (by omega) (hdeg v))
  have eA := (G.mem_neighborFinset _ _).mp ha
  have eB := (G.mem_neighborFinset _ _).mp hb
  have hnab : ¬ G.Adj a b := by
    intro h
    exact proper h (two_colors_same (proper eA).symm (proper eB).symm)
  let f₀ (i : Fin 3) : V := if i.val = 0 then a else if i.val = 1 then v else b
  have hf₀ : InducedPath G f₀ := by
    refine ⟨?_,?_⟩
    · intro i j h
      fin_cases i <;> fin_cases j <;>
        norm_num [f₀, eA.ne, eA.ne.symm, eB.ne, eB.ne.symm, hab, hab.symm] at h ⊢
    · intro i j h
      change i.val < j.val at h
      fin_cases i <;> fin_cases j <;>
        norm_num [f₀, eA.symm, eB, hnab] at h ⊢
  obtain ⟨k,hk3,f,hf,hmax⟩ := max_induced_path_of_path G f₀ hf₀
  let i₀ : Fin k := ⟨0,by omega⟩
  let i₁ : Fin k := ⟨1,by omega⟩
  let i₂ : Fin k := ⟨2,by omega⟩
  have e₀₁ : G.Adj (f i₀) (f i₁) := (hf.2 _ _ (by change 0 < 1; decide)).mpr rfl
  have e₁₂ : G.Adj (f i₁) (f i₂) := (hf.2 _ _ (by change 1 < 2; decide)).mpr rfl
  let N := G.neighborFinset (f i₀)
  let R := N.erase (f i₁)
  have hAdj (w : R) : G.Adj (f i₀) w.val :=
    (G.mem_neighborFinset _ _).mp (mem_erase.mp w.property).2
  have hNe (w : R) : w.val ≠ f i₁ := (mem_erase.mp w.property).1
  have hblock (w : R) : ∃ j : Fin k, 0 < j.val ∧ G.Adj w.val (f j) := by
    by_cases hn : ∃ j : Fin k, 0 < j.val ∧ G.Adj w.val (f j)
    · exact hn
    exfalso
    push_neg at hn
    have hnew (i : Fin k) : w.val ≠ f i := by
      intro he
      have hh := hAdj w
      rw [he] at hh
      by_cases hi : i.val = 0
      · have he' : i = i₀ := Fin.ext hi
        exact G.loopless _ (he' ▸ hh)
      · have hi' : i₀ < i := by change 0 < i.val; omega
        have h := (hf.2 _ _ hi').mp hh
        have he' : i = i₁ := Fin.ext h.symm
        exact hNe w (he.trans (congrArg f he'))
    obtain ⟨ff,hff⟩ := prepend_induced (by omega) hf w.val hnew (hAdj w).symm hn
    have hle := hmax _ ⟨ff,hff⟩
    omega
  choose j hjpos hjadj using hblock
  have hjEven (w : R) : (j w).val % 2 = 0 :=
    (induced_color_parity color proper (by omega) hf (j w)).mp
      (two_colors_same (proper (hjadj w)).symm (proper (hAdj w)))
  have hjMin (w : R) : 4 ≤ (j w).val := by
    have hj := hjpos w
    have he := hjEven w
    by_cases h : 4 ≤ (j w).val
    · exact h
    exfalso
    have ht : j w = i₂ := Fin.ext (by change (j w).val = 2; omega)
    have hA := hjadj w
    rw [ht] at hA
    have hz : f i₀ ≠ f i₂ := by
      intro hz
      have h := congrArg Fin.val (hf.1 hz)
      change 0 = 2 at h
      omega
    exact hNe w (hc4 _ _ _ _ hz (hAdj w) hA.symm e₀₁ e₁₂.symm)
  let idx (w : R) : Fin ((k-1)/2-1) := ⟨(j w).val/2-2,by
    have h1 := (j w).isLt
    have h2 := hjMin w
    omega⟩
  have hi : Function.Injective idx := by
    intro w u hh
    have h := congrArg Fin.val hh
    change (j w).val/2-2 = (j u).val/2-2 at h
    have hw := hjMin w
    have hu := hjMin u
    have hew := hjEven w
    have heu := hjEven u
    have hJ : j w = j u := Fin.ext (by omega)
    have hneq : f i₀ ≠ f (j w) := by
      intro he
      have h' := congrArg Fin.val (hf.1 he)
      change 0 = (j w).val at h'
      omega
    apply Subtype.ext
    exact hc4 _ _ _ _ hneq (hAdj w) (hjadj w).symm (hAdj u) (hJ.symm ▸ (hjadj u).symm)
  have hR := Fintype.card_le_of_injective idx hi
  simp only [Fintype.card_fin, Fintype.card_coe] at hR
  have hCard : R.card + 1 = G.degree (f i₀) :=
    Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr e₀₁)
  have hlow := hdeg (f i₀)
  exact ⟨k,by omega,f,hf⟩

end Bipartite

section Density

open Classical in
private theorem edge_count_delete_vertex (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.induce {v | v ≠ x}).edgeFinset.card + G.degree x = G.edgeFinset.card := by
  classical
  let S : Set V := {v | v ≠ x}
  have heq : G.edgeFinset ∩ S.toFinset.sym2 = G.edgeFinset.filter (fun e => x ∉ e) := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [mem_inter, mk_mem_sym2_iff, Set.mem_toFinset, mem_filter, Sym2.mem_iff,
        not_or]
      simp [S, ne_comm]
  have hInc : G.incidenceFinset x = G.edgeFinset.filter (fun e => x ∈ e) := by
    ext e
    simp [SimpleGraph.incidenceFinset, SimpleGraph.incidenceSet, Set.mem_toFinset]
  have hCard := Finset.filter_card_add_filter_neg_card_eq_card
    (s := G.edgeFinset) (p := fun e => x ∈ e)
  rw [← hInc, ← heq, ← map_edgeFinset_induce, Finset.card_map, card_incidenceFinset_eq_degree] at hCard
  exact (Nat.add_comm _ _).trans hCard

/-- The endpoint bound applied after deleting low-degree vertices. -/
theorem bipartite_path_of_density {U : Type u} [Fintype U] [Nonempty U]
    (J : SimpleGraph U) [DecidableRel J.Adj] (hJ : FourCycleFree J) (color : U → Bool)
    (proper : ∀ ⦃x y⦄, J.Adj x y → color x ≠ color y)
    (d : ℕ) (hd : 1 ≤ d) (hdens : d * Fintype.card U ≤ J.edgeFinset.card) :
    ∃ k, 2*d+3 ≤ k ∧ ∃ f : Fin k → U, InducedPath J f := by
  classical
  let Claim (n : ℕ) := ∀ (W : Type u) [Fintype W] [Nonempty W], Fintype.card W = n →
    ∀ (G : SimpleGraph W) [DecidableRel G.Adj], FourCycleFree G →
    ∀ c : W → Bool, (∀ ⦃x y⦄, G.Adj x y → c x ≠ c y) → d * Fintype.card W ≤ G.edgeFinset.card →
        ∃ k, 2*d+3 ≤ k ∧ ∃ f : Fin k → W, InducedPath G f
  have hall : ∀ n, Claim n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ hn G _ hG c hc hD
      by_cases hmin : ∀ v, d+1 ≤ G.degree v
      · obtain ⟨k,hk,f,hf⟩ := bipartite_path_of_min_degree G hG c hc (d+1) (by omega) hmin
        exact ⟨k,by omega,f,hf⟩
      push_neg at hmin
      obtain ⟨v,hv⟩ := hmin
      let S : Set W := {x | x ≠ v}
      let H := G.induce S
      have hS : Fintype.card S + 1 = Fintype.card W := by
        have hpos := Fintype.card_pos (α := W)
        have hs : Fintype.card S = Fintype.card W - 1 := by
          change Fintype.card {x : W // ¬ x = v} = _
          rw [Fintype.card_subtype_compl]
          have hOne : Fintype.card {x : W // x = v} = 1 :=
            Fintype.card_unique
          rw [hOne]
        omega
      have hFree : FourCycleFree H := by
        intro a b x y hab hax hbx hay hby
        apply Subtype.ext
        exact hG _ _ _ _ (fun h => hab (Subtype.ext h)) hax hbx hay hby
      have hN : Nonempty S := by
        have hm : 0 < G.edgeFinset.card :=
          (Nat.mul_pos (by omega : 0 < d) (Fintype.card_pos (α := W))).trans_le hD
        obtain ⟨e,he⟩ := Finset.card_pos.mp hm
        have ha : ∃ a b, G.Adj a b := by
          revert he
          induction e using Sym2.ind with
          | h a b =>
            intro he
            exact ⟨a,b,(mem_edgeSet G).mp (mem_edgeFinset.mp he)⟩
        obtain ⟨a,b,hab⟩ := ha
        by_cases h : a = v
        · exact ⟨⟨b,(h ▸ hab.ne).symm⟩⟩
        · exact ⟨⟨a,h⟩⟩
      letI := hN
      have hEdges := edge_count_delete_vertex G v
      have hD' : d * Fintype.card S ≤ H.edgeFinset.card := by
        rw [← hS, Nat.mul_add, Nat.mul_one] at hD
        change H.edgeFinset.card + G.degree v = G.edgeFinset.card at hEdges
        omega
      have hC : Fintype.card S < n := by omega
      obtain ⟨k,hk,f,hf⟩ := ih _ hC S rfl H hFree (fun v => c v.val) (fun ⦃a b⦄ h => hc h) hD'
      exact ⟨k,hk,fun i => (f i).val,Subtype.val_injective.comp hf.1,hf.2⟩
  exact hall _ U rfl J hJ color proper hdens

private theorem localIndependence_bipartite (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (proper : ∀ ⦃x y⦄, G.Adj x y → color x ≠ color y) (v : V) :
    localIndependence G v = G.degree v := by
  classical
  rw [← G.card_neighborFinset_eq_degree]
  unfold localIndependence
  apply le_antisymm
  · apply Finset.sup_le_iff.mpr
    intro A hA
    apply Finset.card_le_card
    intro w hw
    exact (G.mem_neighborFinset v w).mpr ((mem_localIndependentSets.mp hA).1 w hw)
  · apply Finset.le_sup (f := card)
    apply mem_localIndependentSets.mpr
    constructor
    · intro a ha
      exact (G.mem_neighborFinset v a).mp ha
    · intro a ha b hb hab
      have h₁ := proper ((G.mem_neighborFinset v a).mp ha)
      have h₂ := proper ((G.mem_neighborFinset v b).mp hb)
      exact proper hab (two_colors_same h₁.symm h₂.symm)

theorem conjecture133_bipartite_regular (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (color : V → Bool)
    (proper : ∀ ⦃x y⦄, G.Adj x y → color x ≠ color y)
    (d : ℕ) (hreg : ∀ v, G.degree v = d) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  letI := hc.nonempty
  have hpos : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have havg : averageLocal G = d := by
    unfold averageLocal
    simp_rw [localIndependence_bipartite G color proper,hreg,sum_const,card_univ,nsmul_eq_mul]
    apply (div_eq_iff (ne_of_gt hpos)).mpr
    simp [mul_comm]
  by_cases hC : FourCycleFree G
  · by_cases hd : 2 ≤ d
    · by_cases hr : radius G ≤ d+1
      · obtain ⟨k,hk,f,hf⟩ := bipartite_path_of_min_degree G hC color proper d hd
          (fun v => (hreg v).ge)
        have hh : radius G+d ≤ k := by omega
        exact ⟨k,by simp only [rhs133,if_pos hC,pow_one,havg]; exact_mod_cast hh,f,hf⟩
      · obtain ⟨k,hk,f,hf⟩ := path_at_least_twice_radius_sub_one G hc
        have hh : radius G+d ≤ k := by omega
        exact ⟨k,by simp only [rhs133,if_pos hC,pow_one,havg]; exact_mod_cast hh,f,hf⟩
    · exact conjecture133_low_average_or_four_cycle G hc
        (Or.inr (by rw [havg]; exact_mod_cast (show d ≤ 2 by omega)))
  · exact conjecture133_low_average_or_four_cycle G hc (Or.inl hC)

theorem conjecture133_bipartite_small_radius (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (color : V → Bool)
    (proper : ∀ ⦃x y⦄, G.Adj x y → color x ≠ color y)
    (hr : radius G ≤ 2 ∨ (radius G ≤ 3 ∧ ⌊averageLocal G⌋ % 2 = 0)) :
    ∃ k : ℕ, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases hC : FourCycleFree G
  · by_cases ha : ⌊averageLocal G⌋ ≤ 2
    · exact conjecture133_floor_le_two_or_four_cycle G hc (Or.inr ha)
    letI := hc.nonempty
    let n := Fintype.card V
    let m := G.edgeFinset.card
    let d := m / n
    have hn : 0 < n := Fintype.card_pos
    have hmod := Nat.div_add_mod m n
    change n*d + m % n = m at hmod
    have hrem := Nat.mod_lt m hn
    have hD : d*n ≤ m := by rw [Nat.mul_comm d n]; omega
    have hU : m < (d+1)*n := by rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm d n]; omega
    have havg : averageLocal G = (2*(m : ℚ))/n := by
      unfold averageLocal
      simp_rw [localIndependence_bipartite G color proper]
      rw [← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges, Nat.cast_mul]
      rfl
    have hA : averageLocal G < ((2*(d+1) : ℕ) : ℚ) := by
      rw [havg]
      apply (div_lt_iff₀ (by exact_mod_cast hn)).mpr
      calc
        2 * (m : ℚ) < 2 * (((d+1)*n : ℕ) : ℚ) :=
          mul_lt_mul_of_pos_left (by exact_mod_cast hU) (by norm_num)
        _ = _ := by simp [mul_assoc]
    have hF : ⌊averageLocal G⌋ < ((2*(d+1) : ℕ) : ℤ) := by
      apply Int.floor_lt.mpr
      exact_mod_cast hA
    have hd : 1 ≤ d := by omega
    obtain ⟨k,hk,f,hf⟩ := bipartite_path_of_density G hC color proper d hd hD
    refine ⟨k,?_,f,hf⟩
    simp only [catalogueRhs133,if_pos hC,pow_one]
    rcases hr with h | ⟨h₁,h₂⟩ <;> omega
  · exact conjecture133_floor_le_two_or_four_cycle G hc (Or.inl hC)

#print axioms bipartite_path_of_min_degree
#print axioms bipartite_path_of_density
#print axioms conjecture133_bipartite_regular
#print axioms conjecture133_bipartite_small_radius

end Density


theorem average_local_le_two_of_radius_le_one (G : SimpleGraph V) (hc : G.Connected)
    (hc4 : FourCycleFree G) (hr : radius G ≤ 1) : averageLocal G ≤ 2 := by
  classical
  letI := hc.nonempty
  obtain ⟨c,hc'⟩ := exists_radius_vertex G hc
  have hstar (v : V) (hv : v ≠ c) : G.Adj c v := by
    apply dist_eq_one_iff_adj.mp
    have hz : G.dist c v ≠ 0 := fun h => hv ((hc.dist_eq_zero_iff.mp h).symm)
    have hh := (hc' v).trans hr
    omega
  have hboundC : localIndependence G c ≤ Fintype.card V := by
    apply Finset.sup_le_iff.mpr
    intro A _
    exact Finset.card_le_univ A
  have hboundV (v : V) (hv : v ≠ c) : localIndependence G v ≤ 1 := by
    apply Finset.sup_le_iff.mpr
    intro A hA
    obtain ⟨hN,hI⟩ := mem_localIndependentSets.mp hA
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_cases hxc : x = c
    · by_cases hyc : y = c
      · exact hxc.trans hyc.symm
      · exact (hI x hx y hy (hxc.symm ▸ hstar y hyc)).elim
    by_cases hyc : y = c
    · exact (hI x hx y hy (hyc.symm ▸ (hstar x hxc).symm)).elim
    exact hc4 v c x y hv (hN x hx) (hstar x hxc) (hN y hy) (hstar y hyc)
  have hSum : (∑ v : V, localIndependence G v) ≤ 2 * Fintype.card V := by
    have hrest : (∑ v ∈ (univ : Finset V).erase c, localIndependence G v) ≤
        ((univ : Finset V).erase c).card := by
      calc
        _ ≤ ∑ _v ∈ (univ : Finset V).erase c, (1 : ℕ) :=
          Finset.sum_le_sum (fun v hv => hboundV v (mem_erase.mp hv).1)
        _ = _ := by simp
    have hcard := Finset.card_erase_le (s := (univ : Finset V)) (a := c)
    have hsplit := Finset.sum_erase_add (univ : Finset V) (localIndependence G) (mem_univ c)
    simp only [card_univ] at hcard
    omega
  have hpos : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  unfold averageLocal
  apply (div_le_iff₀ hpos).mpr
  exact_mod_cast hSum

/-- Chung's bound also covers the unrounded version when the radius has
one full unit of slack over the mean. -/
theorem conjecture133_unrounded_high_radius (G : SimpleGraph V) (hc : G.Connected)
    (h : averageLocal G + 1 ≤ (radius G : ℚ)) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases hC : FourCycleFree G
  · obtain ⟨k,hk,f,hf⟩ := path_at_least_twice_radius_sub_one G hc
    have ha : 0 ≤ averageLocal G :=
      div_nonneg (sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have hr' : (1 : ℚ) ≤ radius G :=
      (le_add_of_nonneg_left ha).trans h
    have hr : 1 ≤ radius G := by exact_mod_cast hr'
    have hNat : 2*radius G ≤ k+1 := by omega
    have hh : (radius G : ℚ) + averageLocal G + 1 ≤ (k : ℚ) + 1 := calc
      _ = (radius G : ℚ) + (averageLocal G + 1) := add_assoc _ _ _
      _ ≤ (radius G : ℚ) + (radius G : ℚ) := add_le_add_left h _
      _ ≤ _ := by rw [← two_mul]; exact_mod_cast hNat
    refine ⟨k,?_,f,hf⟩
    simpa only [rhs133,if_pos hC,pow_one] using (add_le_add_iff_right _).mp hh
  · exact conjecture133_low_average_or_four_cycle G hc (Or.inl hC)

#print axioms average_local_le_two_of_radius_le_one
#print axioms conjecture133_unrounded_high_radius


/-- Necessary conditions for failure of the rounded inequality. -/
theorem catalogue_counterexample_constraints (G : SimpleGraph V) (hc : G.Connected)
    (hbad : ¬ ∃ k : ℕ, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f) :
    FourCycleFree G ∧ 3 ≤ ⌊averageLocal G⌋ ∧ 2 ≤ radius G ∧
      (radius G : ℤ) ≤ ⌊averageLocal G⌋ ∧
      ∀ u v, (G.dist u v : ℤ)+1 < (radius G : ℤ)+⌊averageLocal G⌋ := by
  classical
  have hC : FourCycleFree G := by
    by_cases h : FourCycleFree G
    · exact h
    · exact (hbad (conjecture133_floor_le_two_or_four_cycle G hc (Or.inl h))).elim
  have hLow : 3 ≤ ⌊averageLocal G⌋ := by
    by_cases h : ⌊averageLocal G⌋ ≤ 2
    · exact (hbad (conjecture133_floor_le_two_or_four_cycle G hc (Or.inr h))).elim
    · omega
  have hRad : (radius G : ℤ) ≤ ⌊averageLocal G⌋ := by
    by_cases h : ⌊averageLocal G⌋ < (radius G : ℤ)
    · exact (hbad (conjecture133_high_radius G hc h)).elim
    · omega
  have hr : 2 ≤ radius G := by
    by_cases h : radius G ≤ 1
    · have ha := Int.floor_mono (average_local_le_two_of_radius_le_one G hc hC h)
      have hf : ⌊averageLocal G⌋ ≤ 2 := by simpa using ha
      omega
    · omega
  refine ⟨hC,hLow,hr,hRad,?_⟩
  intro u v
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist u v
  by_cases h : (radius G : ℤ)+⌊averageLocal G⌋ ≤ (G.dist u v : ℤ)+1
  · apply (hbad ⟨p.length+1,?_,geodesic_induced hc p hp⟩).elim
    simpa only [catalogueRhs133,if_pos hC,pow_one,Nat.cast_add,Nat.cast_one,hp] using h
  · omega

#print axioms catalogue_counterexample_constraints

/-- There is no simple cycle of length five (whether induced or not). -/
def NoSimpleFive133 (G : SimpleGraph V) : Prop :=
  ∀ a b c d e, [a,b,c,d,e].Nodup →
    G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e → G.Adj e a → False

private theorem max_local_set (G : SimpleGraph V) (v : V) :
    ∃ A ∈ localIndependentSets G v, A.card = localIndependence G v := by
  classical
  obtain ⟨A,hA,hM⟩ := Finset.exists_max_image (localIndependentSets G v) Finset.card
    ⟨∅, mem_localIndependentSets.mpr (by simp)⟩
  exact ⟨A,hA,le_antisymm (Finset.le_sup (f := Finset.card) hA)
    (Finset.sup_le_iff.mpr hM)⟩

private theorem max_local_set_with (G : SimpleGraph V) (h4 : FourCycleFree G)
    {v y : V} (hy : G.Adj v y) :
    ∃ A ∈ localIndependentSets G v, y ∈ A ∧ A.card = localIndependence G v := by
  classical
  obtain ⟨A,hA,hAC⟩ := max_local_set G v
  obtain ⟨hN,hI⟩ := mem_localIndependentSets.mp hA
  by_cases hyA : y ∈ A
  · exact ⟨A,hA,hyA,hAC⟩
  have max_of_insert {B : Finset V} (hB : B ⊆ A)
      (hNo : ∀ z ∈ B, ¬ G.Adj y z) : insert y B ∈ localIndependentSets G v := by
    apply mem_localIndependentSets.mpr
    constructor
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hy
      · exact hN _ (hB hz)
    · intro a ha b hb
      rcases Finset.mem_insert.mp ha with e | ha'
      · subst a
        rcases Finset.mem_insert.mp hb with e | hb'
        · subst b
          exact G.loopless _
        · exact hNo _ hb'
      · rcases Finset.mem_insert.mp hb with e | hb'
        · subst b
          exact fun h => hNo _ ha' h.symm
        · exact hI _ (hB ha') _ (hB hb')
  by_cases h : ∃ z ∈ A, G.Adj y z
  · obtain ⟨z,hz,hyz⟩ := h
    have hh : insert y (A.erase z) ∈ localIndependentSets G v :=
      max_of_insert (Finset.erase_subset _ _) (fun w hw hyw =>
        (Finset.mem_erase.mp hw).1
          (h4 v y w z hy.ne (hN _ (Finset.mem_erase.mp hw).2) hyw (hN _ hz) hyz))
    refine ⟨_,hh,Finset.mem_insert_self _ _,?_⟩
    rw [Finset.card_insert_of_not_mem (fun e => hyA (Finset.erase_subset _ _ e)),
      Finset.card_erase_add_one hz, hAC]
  · push_neg at h
    have hh := Finset.le_sup (f := Finset.card) (max_of_insert (B := A) (fun _ e => e) h)
    rw [Finset.card_insert_of_not_mem hyA, hAC] at hh
    change localIndependence G v + 1 ≤ localIndependence G v at hh
    exact (by omega : False).elim

/-- Each independent neighbor of a path endpoint other than its successor
blocks extension at a distinct index. In the absence of a five-cycle,
consecutive blocking indices are also impossible. -/
private theorem path_bounds_of_min_local [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc4 : FourCycleFree G)
    (d : ℕ) (hd : 2 ≤ d) (hdeg : ∀ v, d ≤ localIndependence G v) :
    ∃ k, (d+2 ≤ k) ∧ (NoSimpleFive133 G → 2*d+1 ≤ k) ∧
      ∃ f : Fin k → V, InducedPath G f := by
  classical
  let v : V := Classical.choice ‹Nonempty V›
  obtain ⟨A,hA, hAC⟩ := max_local_set G v
  obtain ⟨haN,haI⟩ := mem_localIndependentSets.mp hA
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp
    (show 1 < A.card from lt_of_lt_of_le (by omega) (hAC ▸ hdeg v))
  have eA := haN a ha
  have eB := haN b hb
  have hnab := haI a ha b hb
  let f₀ (i : Fin 3) : V := if i.val = 0 then a else if i.val = 1 then v else b
  have hf₀ : InducedPath G f₀ := by
    refine ⟨?_,?_⟩
    · intro i j h
      fin_cases i <;> fin_cases j <;>
        norm_num [f₀, eA.ne, eA.ne.symm, eB.ne, eB.ne.symm, hab, hab.symm] at h ⊢
    · intro i j h
      change i.val < j.val at h
      fin_cases i <;> fin_cases j <;>
        norm_num [f₀, eA.symm, eB, hnab] at h ⊢
  obtain ⟨k,hk3,f,hf,hmax⟩ := max_induced_path_of_path G f₀ hf₀
  let i₀ : Fin k := ⟨0,by omega⟩
  let i₁ : Fin k := ⟨1,by omega⟩
  let i₂ : Fin k := ⟨2,by omega⟩
  have e₀₁ : G.Adj (f i₀) (f i₁) := (hf.2 _ _ (by change 0 < 1; decide)).mpr rfl
  have e₁₂ : G.Adj (f i₁) (f i₂) := (hf.2 _ _ (by change 1 < 2; decide)).mpr rfl
  obtain ⟨A,hA,hOne,hAC⟩ := max_local_set_with G hc4 e₀₁
  obtain ⟨hAN,hAI⟩ := mem_localIndependentSets.mp hA
  let R := A.erase (f i₁)
  have hAdj (w : R) : G.Adj (f i₀) w.val :=
    hAN _ (mem_erase.mp w.property).2
  have hNe (w : R) : w.val ≠ f i₁ := (mem_erase.mp w.property).1
  have hnew (w : R) (i : Fin k) : w.val ≠ f i := by
    intro he
    have hh := hAdj w
    rw [he] at hh
    by_cases hi : i.val = 0
    · have he' : i = i₀ := Fin.ext hi
      exact G.loopless _ (he' ▸ hh)
    · have hi' : i₀ < i := by change 0 < i.val; omega
      have h := (hf.2 _ _ hi').mp hh
      have he' : i = i₁ := Fin.ext h.symm
      exact hNe w (he.trans (congrArg f he'))
  have hblock (w : R) : ∃ j : Fin k, 0 < j.val ∧ G.Adj w.val (f j) := by
    by_cases hn : ∃ j : Fin k, 0 < j.val ∧ G.Adj w.val (f j)
    · exact hn
    exfalso
    push_neg at hn
    obtain ⟨ff,hff⟩ := prepend_induced (by omega) hf w.val (hnew w) (hAdj w).symm hn
    have hle := hmax _ ⟨ff,hff⟩
    omega
  choose j hjpos hjadj using hblock
  have hjMin (w : R) : 3 ≤ (j w).val := by
    have hj := hjpos w
    by_contra! h
    have hA := hjadj w
    by_cases he : (j w).val = 1
    · rw [show j w = i₁ from Fin.ext he] at hA
      exact hAI _ (mem_erase.mp w.property).2 _ hOne hA
    · rw [show j w = i₂ from Fin.ext (show (j w).val = 2 by omega)] at hA
      have hz : f i₀ ≠ f i₂ := by
        intro hz
        have h := congrArg Fin.val (hf.1 hz)
        change 0 = 2 at h
        omega
      exact hNe w (hc4 _ _ _ _ hz (hAdj w) hA.symm e₀₁ e₁₂.symm)
  have hCard : R.card + 1 = localIndependence G (f i₀) :=
    (Finset.card_erase_add_one hOne).trans hAC
  have hlow := hdeg (f i₀)
  have disj (i j : Fin k) (h : i.val ≠ j.val) : f i ≠ f j :=
    fun e => h (congrArg Fin.val (hf.1 e))
  have blocker_unique (w u : R) (hJ : j w = j u) : w = u := by
    have hneq : f i₀ ≠ f (j w) := disj _ _ (by
      have h := hjpos w
      change 0 ≠ (j w).val
      omega)
    apply Subtype.ext
    exact hc4 _ _ _ _ hneq (hAdj w) (hjadj w).symm (hAdj u) (hJ.symm ▸ (hjadj u).symm)
  have hbase : d+2 ≤ k := by
    let idx (w : R) : Fin (k-3) := ⟨(j w).val-3, by
      have h1 := (j w).isLt
      have h2 := hjMin w
      omega⟩
    have hinj : Function.Injective idx := by
      intro w u he
      have hh := congrArg Fin.val he
      change (j w).val-3 = (j u).val-3 at hh
      have hw := hjMin w
      have hu := hjMin u
      exact blocker_unique _ _ (Fin.ext (by omega))
    have hR := Fintype.card_le_of_injective idx hinj
    simp only [Fintype.card_fin,Fintype.card_coe] at hR
    omega
  refine ⟨k,hbase,?_,f,hf⟩
  intro hfive
  have hjMin4 (w : R) : 4 ≤ (j w).val := by
    have h3 := hjMin w
    by_contra! hb
    have hj3 : (j w).val = 3 := by omega
    have h01 : f i₀ ≠ f i₁ := e₀₁.ne
    have h02 : f i₀ ≠ f i₂ := disj _ _ (by change 0 ≠ 2; decide)
    have h0j : f i₀ ≠ f (j w) := disj _ _ (by change 0 ≠ (j w).val; omega)
    have h1j : f i₁ ≠ f (j w) := disj _ _ (by change 1 ≠ (j w).val; omega)
    have h2j : f i₂ ≠ f (j w) := disj _ _ (by change 2 ≠ (j w).val; omega)
    have e2j : G.Adj (f i₂) (f (j w)) := (hf.2 _ _
      (by change 2 < (j w).val; omega)).mpr (by change 2+1 = (j w).val; omega)
    exact hfive _ _ _ _ _ (by simp [h01,h02,h0j,h1j,h2j,e₁₂.ne,(hAdj w).ne,
      Ne.symm (hnew w i₁), Ne.symm (hnew w i₂), Ne.symm (hnew w (j w))])
      e₀₁ e₁₂ e2j (hjadj w).symm (hAdj w).symm
  let idx (w : R) : Fin ((k-3)/2) := ⟨((j w).val-4)/2,by
    have h1 := (j w).isLt
    have h2 := hjMin4 w
    omega⟩
  have hi : Function.Injective idx := by
    intro w u hh
    have h := congrArg Fin.val hh
    change ((j w).val-4)/2 = ((j u).val-4)/2 at h
    have hw := hjMin4 w
    have hu := hjMin4 u
    have hneq : f i₀ ≠ f (j w) := by
      intro he
      have h' := congrArg Fin.val (hf.1 he)
      change 0 = (j w).val at h'
      omega
    by_cases hs : (j w).val = (j u).val
    · have hJ : j w = j u := Fin.ext hs
      exact blocker_unique _ _ hJ
    · by_cases hwu : w.val = u.val
      · exact Subtype.ext hwu
      exfalso
      have hstep : G.Adj (f (j w)) (f (j u)) := by
        by_cases hlt : (j w).val < (j u).val
        · apply (hf.2 _ _ hlt).mpr
          omega
        · apply Adj.symm
          apply (hf.2 _ _ (show (j u).val < (j w).val by omega)).mpr
          omega
      have hx : f i₀ ≠ f (j u) := by
        intro e
        have eq := congrArg Fin.val (hf.1 e)
        change 0 = (j u).val at eq
        omega
      have hnod : [f i₀, w.val, f (j w), f (j u), u.val].Nodup := by
        simp [Ne.symm (hnew w i₀), hneq, hx, (hAdj u).ne, hnew w,
          Ne.symm (hnew u (j w)), Ne.symm (hnew u (j u)), hstep.ne, hwu]
      exact hfive _ _ _ _ _ hnod (hAdj w) (hjadj w) hstep (hjadj u).symm (hAdj u).symm
  have hR := Fintype.card_le_of_injective idx hi
  simp only [Fintype.card_fin, Fintype.card_coe] at hR
  omega

/-- The bound that does not exclude five-cycles. -/
theorem no_four_path_of_min_local [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc4 : FourCycleFree G) (d : ℕ) (hd : 2 ≤ d) (hdeg : ∀ v, d ≤ localIndependence G v) :
    ∃ k, d+2 ≤ k ∧ ∃ f : Fin k → V, InducedPath G f := by
  obtain ⟨k,hk,_,f,hf⟩ := path_bounds_of_min_local G hc4 d hd hdeg
  exact ⟨k,hk,f,hf⟩

theorem no_four_five_path_of_min_local [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc4 : FourCycleFree G) (hfive : NoSimpleFive133 G)
    (d : ℕ) (hd : 2 ≤ d) (hdeg : ∀ v, d ≤ localIndependence G v) :
    ∃ k, 2*d+1 ≤ k ∧ ∃ f : Fin k → V, InducedPath G f := by
  obtain ⟨k,_,hk,f,hf⟩ := path_bounds_of_min_local G hc4 d hd hdeg
  exact ⟨k,hk hfive,f,hf⟩

/-- At radius at most two, constant local independence suffices even if
the graph contains five-cycles. -/
theorem conjecture133_constant_local_radius_le_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hr : radius G ≤ 2)
    (d : ℕ) (hreg : ∀ v, localIndependence G v = d) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  letI := hc.nonempty
  have hpos : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have havg : averageLocal G = d := by
    unfold averageLocal
    simp_rw [hreg,sum_const,card_univ,nsmul_eq_mul]
    apply (div_eq_iff (ne_of_gt hpos)).mpr
    simp [mul_comm]
  by_cases hC : FourCycleFree G
  · by_cases hd : 2 ≤ d
    · obtain ⟨k,hk,f,hf⟩ := no_four_path_of_min_local G hC d hd (fun v => (hreg v).ge)
      have hh : radius G+d ≤ k := by omega
      exact ⟨k,by simp only [rhs133,if_pos hC,pow_one,havg]; exact_mod_cast hh,f,hf⟩
    · exact conjecture133_low_average_or_four_cycle G hc
        (Or.inr (by rw [havg]; exact_mod_cast (show d ≤ 2 by omega)))
  · exact conjecture133_low_average_or_four_cycle G hc (Or.inl hC)

#print axioms no_four_path_of_min_local
#print axioms conjecture133_constant_local_radius_le_two

/-- Graffiti #133 (unrounded) when local independence is constant and
there are no five-cycles in the four-cycle-free branch. -/
theorem conjecture133_constant_local_no_five_cycle (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hfive : NoSimpleFive133 G)
    (d : ℕ) (hreg : ∀ v, localIndependence G v = d) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  letI := hc.nonempty
  have hpos : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have havg : averageLocal G = d := by
    unfold averageLocal
    simp_rw [hreg,sum_const,card_univ,nsmul_eq_mul]
    apply (div_eq_iff (ne_of_gt hpos)).mpr
    simp [mul_comm]
  by_cases hC : FourCycleFree G
  · by_cases hd : 2 ≤ d
    · by_cases hr : radius G ≤ d
      · obtain ⟨k,hk,f,hf⟩ := no_four_five_path_of_min_local G hC hfive d hd
          (fun v => (hreg v).ge)
        have hh : radius G+d ≤ k := by omega
        exact ⟨k,by simp only [rhs133,if_pos hC,pow_one,havg]; exact_mod_cast hh,f,hf⟩
      · obtain ⟨k,hk,f,hf⟩ := path_at_least_twice_radius_sub_one G hc
        have hh : radius G+d ≤ k := by omega
        exact ⟨k,by simp only [rhs133,if_pos hC,pow_one,havg]; exact_mod_cast hh,f,hf⟩
    · exact conjecture133_low_average_or_four_cycle G hc
        (Or.inr (by rw [havg]; exact_mod_cast (show d ≤ 2 by omega)))
  · exact conjecture133_low_average_or_four_cycle G hc (Or.inl hC)

/-- The path bound also covers varying local independence numbers when the exact
average is within one of the given lower bound d and the radius is not d+1. -/
theorem conjecture133_near_constant_local_no_five_cycle
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hfive : NoSimpleFive133 G) (d : ℕ) (hd : 2 ≤ d)
    (hmin : ∀ v, d ≤ localIndependence G v) (havg : averageLocal G ≤ (d : ℚ)+1)
    (hr : radius G ≠ d+1) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  letI := hc.nonempty
  by_cases hC : FourCycleFree G
  · suffices H : ∃ k : ℕ, radius G + d + 1 ≤ k ∧ ∃ f : Fin k → V, InducedPath G f by
      obtain ⟨k,hk,f,hf⟩ := H
      refine ⟨k,?_,f,hf⟩
      simp only [rhs133,if_pos hC,pow_one]
      have hkn : (radius G : ℚ) + (d : ℚ) + 1 ≤ (k : ℚ) := by exact_mod_cast hk
      exact (add_le_add_left havg _).trans (by simpa only [← add_assoc] using hkn)
    by_cases hs : radius G ≤ d
    · obtain ⟨k,hk,f,hf⟩ := no_four_five_path_of_min_local G hC hfive d hd hmin
      exact ⟨k,by omega,f,hf⟩
    · obtain ⟨k,hk,f,hf⟩ := path_at_least_twice_radius_sub_one G hc
      exact ⟨k,by omega,f,hf⟩
  · exact conjecture133_low_average_or_four_cycle G hc (Or.inl hC)

#print axioms conjecture133_near_constant_local_no_five_cycle
#print axioms no_four_five_path_of_min_local
#print axioms conjecture133_constant_local_no_five_cycle

/-- Extend one end of a geodesic by at least floor(d/2) vertices.
Four-cycle exclusion is the only small-cycle constraint. -/
theorem one_sided_geodesic_extension_of_min_local
    (G : SimpleGraph V) (hc : G.Connected) (h4 : FourCycleFree G) (d : ℕ)
    (hdeg : ∀ v, d ≤ localIndependence G v) {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v) (hlen : 1 ≤ p.length)
    (s : ℕ) (hs : s ≤ d/2) :
    ∃ f : Fin (p.length+1+s) → V, InducedPath G f ∧
      G.dist u (f ⟨0,by omega⟩) ≤ s ∧
      (∀ i : Fin (p.length+1+s), i.val-s ≤ G.dist u (f i)) ∧
      ∀ i : Fin (p.length+1), f ⟨s+i.val,by have := i.isLt; omega⟩ = p.getVert i := by
  classical
  induction s with
  | zero =>
    refine ⟨fun i => p.getVert i,?_,by simp,?_,fun _ => by simp⟩
    · change InducedPath G (fun i : Fin (p.length+1) => p.getVert i)
      refine ⟨?_,?_⟩
      · intro i j h
        apply Fin.ext
        have hi := prefix_level hc p hp (i := i.val) (by have := i.isLt; omega)
        have hj := prefix_level hc p hp (i := j.val) (by have := j.isLt; omega)
        change p.getVert i.val = p.getVert j.val at h
        rw [h] at hi
        omega
      · intro i j hij
        constructor
        · intro hadj
          have hi := prefix_level hc p hp (i := i.val) (by have := i.isLt; omega)
          have hj := prefix_level hc p hp (i := j.val) (by have := j.isLt; omega)
          have hh := hc.dist_triangle (u := u) (v := p.getVert i) (w := p.getVert j)
          rw [hi,hj,dist_eq_one_iff_adj.mpr hadj] at hh
          change i.val < j.val at hij
          omega
        · intro he
          change i.val+1 = j.val at he
          change G.Adj (p.getVert i.val) (p.getVert j.val)
          rw [← he]
          exact p.adj_getVert_succ (by have := j.isLt; omega)
    · intro i
      rw [Nat.sub_zero,prefix_level hc p hp (by have := i.isLt; omega)]
  | succ s ih =>
    obtain ⟨f,hf,hnear,hfar,horig⟩ := ih (by omega)
    let k := p.length+1+s
    let i₀ : Fin k := ⟨0,by dsimp [k]; omega⟩
    let i₁ : Fin k := ⟨1,by dsimp [k]; omega⟩
    have h01 : G.Adj (f i₀) (f i₁) := (hf.2 _ _ (by change 0 < 1; decide)).mpr rfl
    obtain ⟨A,hA,hOne,hAC⟩ := max_local_set_with G h4 h01
    obtain ⟨hAN,hAI⟩ := mem_localIndependentSets.mp hA
    let R := A.erase (f i₁)
    have ha (w : R) : G.Adj (f i₀) w.val := hAN _ (mem_erase.mp w.property).2
    have hn (w : R) : w.val ≠ f i₁ := (mem_erase.mp w.property).1
    have hnew (w : R) (i : Fin k) : w.val ≠ f i := by
      intro he
      have hh := ha w
      rw [he] at hh
      by_cases hi : i.val = 0
      · have e : i = i₀ := Fin.ext hi
        exact G.loopless _ (e ▸ hh)
      · have hi' : i₀ < i := by change 0 < i.val; omega
        have h := (hf.2 _ _ hi').mp hh
        have e : i = i₁ := Fin.ext h.symm
        exact hn w (he.trans (congrArg f e))
    have hext : ∃ w : R, ∀ j : Fin k, 0 < j.val → ¬ G.Adj w.val (f j) := by
      apply Classical.byContradiction
      intro hbad
      push_neg at hbad
      choose j hj hjadj using hbad
      have hlo (w : R) : 3 ≤ (j w).val := by
        have hpos := hj w
        by_cases hlt : 3 ≤ (j w).val
        · exact hlt
        exfalso
        by_cases h : (j w).val = 1
        · have e : j w = i₁ := Fin.ext h
          exact hAI _ (mem_erase.mp w.property).2 _ hOne (e ▸ hjadj w)
        · have hij : i₁ < j w := by change 1 < (j w).val; omega
          have e12 : G.Adj (f i₁) (f (j w)) :=
            (hf.2 _ _ hij).mpr (by change 1+1 = (j w).val; omega)
          have hne : f i₀ ≠ f (j w) := by
            intro e
            have e' := congrArg Fin.val (hf.1 e)
            change 0 = (j w).val at e'
            omega
          exact hn w (h4 _ _ _ _ hne (ha w) (hjadj w).symm h01 e12.symm)
      have hhi (w : R) : (j w).val ≤ 2*s+2 := by
        have h₁ := hc.dist_triangle (u := f i₀) (v := w.val) (w := f (j w))
        rw [dist_eq_one_iff_adj.mpr (ha w),dist_eq_one_iff_adj.mpr (hjadj w)] at h₁
        have h₂ := hc.dist_triangle (u := u) (v := f i₀) (w := f (j w))
        have h₃ := hfar (j w)
        change G.dist u (f i₀) ≤ s at hnear
        omega
      let idx (w : R) : Fin (2*s) := ⟨(j w).val-3, by
        have := hlo w
        have := hhi w
        omega⟩
      have hinj : Function.Injective idx := by
        intro a b e
        have e' := congrArg Fin.val e
        change (j a).val-3 = (j b).val-3 at e'
        have ha3 := hlo a
        have hb3 := hlo b
        have eq : j a = j b := Fin.ext (by omega)
        have hne : f i₀ ≠ f (j a) := by
          intro h
          have hx := congrArg Fin.val (hf.1 h)
          change 0 = (j a).val at hx
          omega
        exact Subtype.ext (h4 _ _ _ _ hne (ha a) (hjadj a).symm (ha b) (eq.symm ▸ (hjadj b).symm))
      have hcount := Fintype.card_le_of_injective idx hinj
      simp only [Fintype.card_fin,Fintype.card_coe] at hcount
      have hcard : R.card + 1 = localIndependence G (f i₀) :=
        (Finset.card_erase_add_one hOne).trans hAC
      have hl := hdeg (f i₀)
      omega
    obtain ⟨w,hw⟩ := hext
    obtain ⟨ff,hff,hhead,htail⟩ :=
      prepend_induced_with_positions (by omega) hf w.val (hnew w) (ha w).symm hw
    have hheadDist : G.dist u w.val ≤ s+1 := by
      have h := hc.dist_triangle (u := u) (v := f i₀) (w := w.val)
      rw [dist_eq_one_iff_adj.mpr (ha w)] at h
      change G.dist u (f i₀) ≤ s at hnear
      omega
    refine ⟨ff,hff,by simpa only [hhead] using hheadDist,?_,?_⟩
    · intro i
      by_cases hi : 0 < i.val
      · rw [htail i hi]
        have h := hfar ⟨i.val-1,by have := i.isLt; dsimp [k] at *; omega⟩
        change i.val-1-s ≤ _ at h
        omega
      · omega
    · intro i
      have hx : 0 < s+1+i.val := by omega
      rw [htail _ hx]
      have e : (⟨s+1+i.val-1,by have := i.isLt; dsimp [k]; omega⟩ : Fin k) =
          ⟨s+i.val,by have := i.isLt; dsimp [k]; omega⟩ := Fin.ext (by change s+1+i.val-1=s+i.val; omega)
      rw [e,horig]

#print axioms one_sided_geodesic_extension_of_min_local

omit [Fintype V] in
private theorem induced_index_dist (hc : G.Connected) {k : ℕ}
    {f : Fin k → V} (hf : InducedPath G f) (i : Fin k) (t : ℕ)
    (ht : i.val+t < k) :
    G.dist (f i) (f ⟨i.val+t,ht⟩) ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    let j : Fin k := ⟨i.val+t,by omega⟩
    let j' : Fin k := ⟨i.val+(t+1),ht⟩
    have ha : G.Adj (f j) (f j') := (hf.2 _ _
      (by change i.val+t < i.val+(t+1); omega)).mpr
      (by change (i.val+t)+1 = i.val+(t+1); omega)
    have h := hc.dist_triangle (u := f i) (v := f j) (w := f j')
    rw [dist_eq_one_iff_adj.mpr ha] at h
    have hh : G.dist (f i) (f j) ≤ t := ih (by omega)
    exact le_trans h (Nat.add_le_add_right hh 1)

/-- Two independently constructed shortest-path extensions can be joined
as long as any cross edge between the new parts would shorten the geodesic. -/
theorem two_sided_geodesic_extension_of_min_local
    (G : SimpleGraph V) (hc : G.Connected) (h4 : FourCycleFree G) (d : ℕ)
    (hdeg : ∀ v, d ≤ localIndependence G v) {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v)
    (a b : ℕ) (ha : a ≤ d/2) (hb : b ≤ d/2) (hgap : a+b+2 ≤ p.length) :
    ∃ f : Fin (p.length+1+a+b) → V, InducedPath G f := by
  let D := p.length
  have dlow : 1 ≤ p.length := by omega
  have hp' : p.reverse.length = G.dist v u := by
    rw [Walk.length_reverse,hp,SimpleGraph.dist_comm]
  obtain ⟨L,hL,_,_,hLp⟩ := one_sided_geodesic_extension_of_min_local G hc h4 d hdeg
    p hp dlow a ha
  obtain ⟨R,hR,_,_,hRp⟩ := one_sided_geodesic_extension_of_min_local G hc h4 d hdeg
    p.reverse hp' (by simpa only [Walk.length_reverse] using dlow) b hb
  let l (i : ℕ) (hi : i < D+1+a) : Fin (p.length+1+a) := ⟨i,hi⟩
  have rbound (i : ℕ) (hi : a ≤ i) : D+a+b-i < p.reverse.length+1+b := by
    rw [Walk.length_reverse]
    change D+a+b-i < D+1+b
    omega
  let r (i : ℕ) (hi : a ≤ i) : Fin (p.reverse.length+1+b) := ⟨D+a+b-i,rbound i hi⟩
  let f (i : Fin (p.length+1+a+b)) : V :=
    if h : i.val < a then L (l i.val (by omega)) else R (r i.val (by omega))
  have fl (i : Fin (p.length+1+a+b)) (hi : i.val < a) :
      f i = L (l i.val (by omega)) := dif_pos hi
  have fr (i : Fin (p.length+1+a+b)) (hi : a ≤ i.val) :
      f i = R (r i.val hi) := dif_neg (by omega)
  have hoverlap (i : ℕ) (hi : a ≤ i) (hD : i ≤ a+D) :
      R (r i hi) = L (l i (by omega)) := by
    have iL : i-a < p.length+1 := by change i-a < D+1; omega
    have iR : a+D-i < p.reverse.length+1 := by
      rw [Walk.length_reverse]
      change a+D-i < D+1
      omega
    have el : l i (by omega) = ⟨a+(i-a),by dsimp [D] at *; omega⟩ :=
      Fin.ext (by change i = a+(i-a); omega)
    have er : r i hi = ⟨b+(a+D-i),by have := iR; omega⟩ :=
      Fin.ext (by change D+a+b-i = b+(a+D-i); omega)
    rw [el,er,hLp ⟨i-a,iL⟩,hRp ⟨a+D-i,iR⟩,Walk.getVert_reverse]
    congr 1
    change D-(a+D-i) = i-a
    omega
  have left_dist (i : ℕ) (hi : i < a) : G.dist u (L (l i (by omega))) ≤ a-i := by
    have h := induced_index_dist hc hL (l i (by omega)) (a-i)
      (show i+(a-i) < p.length+1+a by omega)
    have e : (⟨i+(a-i),by omega⟩ : Fin (p.length+1+a)) =
        ⟨a+(0:ℕ),by omega⟩ := Fin.ext (by change i+(a-i) = a+0; omega)
    change G.dist (L (l i (by omega))) (L ⟨i+(a-i),by omega⟩) ≤ a-i at h
    rw [e,hLp ⟨0,by omega⟩,Walk.getVert_zero,SimpleGraph.dist_comm] at h
    exact h
  have right_dist (j : ℕ) (hj : a+D < j) (hj' : j < D+1+a+b) :
      G.dist (R (r j (by omega))) v ≤ b := by
    let t := D+a+b-j
    have ht : t ≤ b := by dsimp [t]; omega
    have h := induced_index_dist hc hR (r j (by omega)) (b-t)
      (show t+(b-t) < p.reverse.length+1+b by omega)
    have e : (⟨t+(b-t),by omega⟩ : Fin (p.reverse.length+1+b)) =
        ⟨b+(0:ℕ),by omega⟩ := Fin.ext (by change t+(b-t)=b+0; omega)
    change G.dist (R (r j (by omega))) (R ⟨t+(b-t),by omega⟩) ≤ b-t at h
    rw [e,hRp ⟨0,by omega⟩,Walk.getVert_zero] at h
    omega
  have cross (i j : Fin (p.length+1+a+b)) (hi : i.val < a) (hj : a+D < j.val) :
      f i ≠ f j ∧ ¬ G.Adj (f i) (f j) := by
    rw [fl i hi,fr j (by omega)]
    have hl := left_dist i.val hi
    have hr := right_dist j.val hj (show j.val < D+1+a+b from j.isLt)
    have h₁ := hc.dist_triangle (u := u) (v := L (l i.val (by omega))) (w := v)
    have h₂ := hc.dist_triangle (u := L (l i.val (by omega)))
      (v := R (r j.val (by omega))) (w := v)
    change p.length = G.dist u v at hp
    have hD : a+b+2 ≤ D := hgap
    constructor
    · intro he
      have h₀ : G.dist (L (l i.val (by omega))) (R (r j.val (by omega))) = 0 := by rw [he,dist_self]
      change D = G.dist u v at hp
      omega
    · intro he
      have h₀ := dist_eq_one_iff_adj.mpr he
      change D = G.dist u v at hp
      omega
  have distinct (i j : Fin (p.length+1+a+b)) (hij : i.val < j.val) : f i ≠ f j := by
    by_cases hi : i.val < a
    · by_cases hj : j.val < a
      · rw [fl i hi,fl j hj]
        intro h
        have he := congrArg Fin.val (hL.1 h)
        change i.val = j.val at he
        omega
      · by_cases hjD : j.val ≤ a+D
        · rw [fl i hi,fr j (by omega),hoverlap j.val (by omega) hjD]
          intro h
          have he := congrArg Fin.val (hL.1 h)
          change i.val = j.val at he
          omega
        · exact (cross i j hi (by omega)).1
    · rw [fr i (by omega),fr j (by omega)]
      intro h
      have he := congrArg Fin.val (hR.1 h)
      change D+a+b-i.val = D+a+b-j.val at he
      have hj := j.isLt
      change j.val < D+1+a+b at hj
      omega
  refine ⟨f,⟨?_,?_⟩⟩
  · intro i j h
    apply Fin.ext
    by_cases he : i.val = j.val
    · exact he
    exfalso
    rcases lt_or_gt_of_ne he with hij | hji
    · exact distinct i j hij h
    · exact distinct j i hji h.symm
  · intro i j hij
    change i.val < j.val at hij
    by_cases hi : i.val < a
    · by_cases hj : j.val < a
      · rw [fl i hi,fl j hj]
        exact hL.2 _ _ hij
      · by_cases hjD : j.val ≤ a+D
        · rw [fl i hi,fr j (by omega),hoverlap j.val (by omega) hjD]
          exact hL.2 _ _ hij
        · exact iff_of_false (cross i j hi (by omega)).2 (by
            have hD : 2 ≤ D := by have h : a+b+2 ≤ D := hgap; omega
            omega)
    · rw [fr i (by omega),fr j (by omega)]
      have hj := j.isLt
      change j.val < D+1+a+b at hj
      rw [adj_comm, hR.2 _ _ (show (r j.val (by omega)) < (r i.val (by omega)) by
        change D+a+b-j.val < D+a+b-i.val
        omega)]
      change D+a+b-j.val+1 = D+a+b-i.val ↔ i.val+1 = j.val
      omega

#print axioms two_sided_geodesic_extension_of_min_local

/-- The diameter bound, with D supplied as a realized maximum distance. -/
theorem diameter_induced_path_bound (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G) (d D : ℕ) (hdeg : ∀ v, d ≤ localIndependence G v)
    (hD : ∃ u v, G.dist u v = D) :
    ∃ f : Fin (D+1+min (2*(d/2)) (D-2)) → V, InducedPath G f := by
  obtain ⟨u,v,hdist⟩ := hD
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist u v
  have hlen : p.length = D := hp.trans hdist
  by_cases hsmall : D < 2
  · have hz : D-2 = 0 := by omega
    rw [hz,Nat.min_zero,Nat.add_zero,← hlen]
    exact geodesic_induced hc p hp
  · let m := min (2*(d/2)) (D-2)
    let a := min (d/2) m
    let b := m-a
    have hm1 : m ≤ 2*(d/2) := min_le_left _ _
    have hm2 : m ≤ D-2 := min_le_right _ _
    have ha1 : a ≤ d/2 := min_le_left _ _
    have ha2 : a ≤ m := min_le_right _ _
    have hb : b ≤ d/2 := by
      dsimp [b,a]
      rw [Nat.min_def]
      split <;> omega
    have hsum : a+b = m := by dsimp [b]; omega
    have hgap : a+b+2 ≤ p.length := by rw [hsum,hlen]; omega
    obtain ⟨f,hf⟩ := two_sided_geodesic_extension_of_min_local G hc h4 d hdeg p hp a b ha1 hb hgap
    have he : p.length+1+a+b = D+1+m := by rw [hlen,add_assoc,hsum]
    exact he ▸ (show ∃ g : Fin (p.length+1+a+b) → V, InducedPath G g from ⟨f,hf⟩)

/-- A directly checkable sufficient condition for the unrounded #133, also
applicable when short odd cycles and heterogeneous local degrees are present. -/
theorem conjecture133_of_diameter_minimum_local (G : SimpleGraph V) (hc : G.Connected)
    (d D : ℕ) (hdeg : ∀ v, d ≤ localIndependence G v) (hD : ∃ u v, G.dist u v = D)
    (hmax : ∀ u v, G.dist u v ≤ D)
    (havg : averageLocal G ≤ ((1+min (2*(d/2)) (D-2) : ℕ) : ℚ)) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · obtain ⟨f,hf⟩ := diameter_induced_path_bound G hc h4 d D hdeg hD
    obtain ⟨u,_,_⟩ := hD
    obtain ⟨v,hv⟩ := radius_le_dist_exists G u
    have hr : radius G ≤ D := hv.trans (hmax u v)
    refine ⟨_,?_,f,hf⟩
    simp only [rhs133,if_pos h4,pow_one]
    calc
      (radius G : ℚ) + averageLocal G ≤
          (D : ℚ) + ((1+min (2*(d/2)) (D-2) : ℕ) : ℚ) :=
        add_le_add (by exact_mod_cast hr) havg
      _ = ((D+1+min (2*(d/2)) (D-2) : ℕ) : ℚ) := by
        simp only [Nat.cast_add,Nat.cast_one,add_assoc]
  · exact conjecture133_low_average_or_four_cycle G hc (Or.inl h4)

#print axioms diameter_induced_path_bound
#print axioms conjecture133_of_diameter_minimum_local

end Graffiti133
