import Small

namespace CazenaveOne
open Finset SimpleGraph
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem dart_degree_product_with_excess (k : ℕ)
    (h : ∀ u : V, (∑ v ∈ G.neighborFinset u, G.degree v) ≤ G.edgeFinset.card+k) :
    (∑ a : G.Dart, (G.degree a.fst : ℝ) * G.degree a.snd) ≤
      2 * (G.edgeFinset.card : ℝ)*((G.edgeFinset.card : ℝ)+k) := by
  classical
  have hmap (d : G.Dart) (_ : d ∈ (Finset.univ : Finset G.Dart)) : d.fst ∈ Finset.univ :=
    Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hf (v : V) : (∑ a ∈ ({d : G.Dart | d.fst = v} : Finset _),
      (G.degree a.fst : ℝ) * G.degree a.snd) =
      (G.degree v : ℝ) * (∑ w ∈ G.neighborFinset v, (G.degree w : ℝ)) := by
    rw [G.dart_fst_fiber, Finset.sum_image (fun a _ b _ hh => G.dartOfNeighborSet_injective v hh),
      Finset.mul_sum]
    rw [Finset.sum_subtype (G.neighborFinset v) (fun w => (G.mem_neighborFinset v w).trans Iff.rfl)]
    rfl
  simp_rw [hf]
  have hb (v : V) : (G.degree v : ℝ) * (∑ w ∈ G.neighborFinset v, (G.degree w : ℝ)) ≤
      (G.degree v : ℝ) * ((G.edgeFinset.card : ℝ)+k) := by
    have hs := h v
    have hcast : ((∑ w ∈ G.neighborFinset v, G.degree w : ℕ) : ℝ) ≤
        (G.edgeFinset.card : ℝ)+k := by exact_mod_cast hs
    push_cast at hcast
    exact mul_le_mul_of_nonneg_left hcast (Nat.cast_nonneg _)
  refine (Finset.sum_le_sum (fun v _ => hb v)).trans_eq ?_
  rw [← Finset.sum_mul]
  have hs : (∑ v : V, (G.degree v : ℝ)) = 2 * G.edgeFinset.card := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [hs]

theorem randic_of_neighbor_excess (k : ℕ)
    (h : ∀ u : V, (∑ v ∈ G.neighborFinset u, G.degree v) ≤ G.edgeFinset.card+k) :
    (G.edgeFinset.card : ℝ)/Real.sqrt ((G.edgeFinset.card : ℝ)+k) ≤ randic G := by
  classical
  let m : ℝ := G.edgeFinset.card
  let W (a : G.Dart) := Real.sqrt ((G.degree a.fst : ℝ) * G.degree a.snd)
  let U : ℝ := ∑ a, W a
  let S : ℝ := ∑ a, 1/W a
  have hp (a : G.Dart) : 0 < W a := by
    apply Real.sqrt_pos.2
    apply mul_pos <;> exact_mod_cast (G.degree_pos_iff_exists_adj _).2 ⟨_, by first | exact a.adj | exact a.adj.symm⟩
  have hS : 0 ≤ S := Finset.sum_nonneg fun a _ => one_div_nonneg.mpr (hp a).le
  by_cases H : 0 < G.edgeFinset.card
  · have hm : 0 < m := by dsimp [m]; exact_mod_cast H
    have hU : 0 < U := by
      apply Finset.sum_pos (fun a _ => hp a)
      rw [← Finset.card_pos,Finset.card_univ,G.dart_card_eq_twice_card_edges]
      omega
    have hNd : (Fintype.card G.Dart : ℝ)=2*m := by dsimp [m]; exact_mod_cast G.dart_card_eq_twice_card_edges
    have h1 : (2*m)^2 ≤ S*U := by
      have hh := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset G.Dart) (fun _ => (1:ℝ))
        (g := W) (fun a _ => hp a)
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, one_pow,hNd] at hh
      have hs := (div_le_iff₀ hU).mp hh
      exact hs
    have hT : (∑ a : G.Dart, W a ^ 2) ≤ 2*m*(m+k) := by
      simp_rw [W,Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
      exact dart_degree_product_with_excess G k h
    have h2 : U^2 ≤ (2*m)*(2*m*(m+k)) := by
      have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset G.Dart) W (fun _ => (1:ℝ))
      simp only [mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,one_pow,hNd] at hh
      rw [mul_comm] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left hT (by positivity))
    let root := Real.sqrt (m+k)
    have hr : 0 < root := Real.sqrt_pos.2 (by positivity)
    have hrs : root^2=m+k := Real.sq_sqrt (by positivity)
    have ub : U ≤ 2*m*root := by
      have hs : U^2≤(2*m*root)^2 := by
        calc
          _ ≤ (2*m)*(2*m*(m+k)) := h2
          _ = _ := by ring_nf; rw [hrs]; ring
      exact (sq_le_sq₀ hU.le (by positivity)).mp hs
    have hh := mul_le_mul_of_nonneg_left ub hS
    have lower : 2*(m/root) ≤ S := by
      have hthird : (2*m)^2 ≤ S*(2*m*root) := h1.trans hh
      apply le_of_mul_le_mul_right ?_ (show 0<2*m*root by positivity)
      have he : 2*(m/root)*(2*m*root) = (2*m)^2 := by
        field_simp [hr.ne'] ; ring
      rw [he]
      exact hthird
    change m/root ≤ _
    unfold randic
    have he : S = 2 * ∑ e ∈ G.edgeFinset, conventionalWeight G e := by
      have hh := Finset.sum_fiberwise_of_maps_to' (fun d : G.Dart => fun _ : d ∈ Finset.univ =>
        mem_edgeFinset.mpr d.edge_mem) (conventionalWeight G)
      rw [← show (∑ a : G.Dart, 1/W a) = ∑ a : G.Dart, conventionalWeight G a.edge from rfl]
        at hh
      change (∑ a : G.Dart, 1/W a) = 2 * ∑ e ∈ G.edgeFinset, conventionalWeight G e
      rw [← hh,Finset.mul_sum]
      apply Finset.sum_congr rfl
      exact fun e he => by rw [Finset.sum_const,G.dart_edge_fiber_card e (mem_edgeFinset.mp he)]; norm_num
    linarith only [he,lower]
  · have h0 : G.edgeFinset.card = 0 := by omega
    rw [h0,Nat.cast_zero,zero_div]
    rw [randic,Finset.card_eq_zero.mp h0,Finset.sum_empty]

#print axioms randic_of_neighbor_excess

theorem subEigen_sq_of_neighbor_excess (k : ℕ)
    (h : ∀ u : V, (∑ v ∈ G.neighborFinset u, G.degree v) ≤ G.edgeFinset.card+k) (t : ℝ) (ht : 0<t)
    (x : V → ℝ) (hex : ∃ v, 0<x v)
    (hrow : ∀ v, t*x v ≤ ∑ w ∈ G.neighborFinset v, x w) :
    t^2 ≤ (G.edgeFinset.card : ℝ)+k := by
  obtain ⟨a,ha⟩ := hex
  obtain ⟨u,_,hu⟩ := Finset.exists_max_image (Finset.univ : Finset V) x ⟨a,mem_univ _⟩
  have hu' : 0<x u := ha.trans_le (hu _ (mem_univ _))
  apply le_of_mul_le_mul_right ?_ hu'
  calc
    t^2*x u = t*(t*x u) := by ring
    _ ≤ t*(∑ v ∈ G.neighborFinset u, x v) := mul_le_mul_of_nonneg_left (hrow u) ht.le
    _ = ∑ v ∈ G.neighborFinset u, t*x v := by rw [Finset.mul_sum]
    _ ≤ ∑ v ∈ G.neighborFinset u, ∑ w ∈ G.neighborFinset v, x w :=
      Finset.sum_le_sum (fun v _ => hrow v)
    _ ≤ ∑ v ∈ G.neighborFinset u, (G.degree v : ℝ)*x u := by
      apply Finset.sum_le_sum
      intro v _
      have h' := Finset.sum_le_sum
        (fun w (_ : w ∈ G.neighborFinset v) => hu w (mem_univ w))
      simpa [Finset.sum_const,nsmul_eq_mul, G.card_neighborFinset_eq_degree] using h'
    _ = (∑ v ∈ G.neighborFinset u, (G.degree v : ℝ))*x u := by rw [Finset.sum_mul]
    _ ≤ ((G.edgeFinset.card : ℝ)+k)*x u := by
      apply mul_le_mul_of_nonneg_right _ hu'.le
      have hc : ((∑ v ∈ G.neighborFinset u, G.degree v : ℕ) : ℝ) ≤ (G.edgeFinset.card : ℝ)+k := by
        exact_mod_cast h u
      push_cast at hc
      exact hc

/-- A triangle-containing extension: a uniform neighborhood degree excess
is permitted if both sign-induced graphs are triangle free. -/
theorem sparse_triangles_nodal (hc : G.Connected) (k : ℕ) {t L : ℝ} {x y : V → ℝ}
    (ht : t≤L) (hpos : 0<t) (hk : (k:ℝ)≤t*(t-2))
    (he : AdjEigen G t x) (hE : AdjEigen G L y)
    (hx : ∃ v, x v≠0) (hy : ∃ v, y v≠0) (hort : (∑ v : V,x v*y v)=0)
    (hP : TriangleFree (restrict G (posSet x))) (hN : TriangleFree (restrict G (negSet x)))
    (hne : ∀ u : V, (∑ v ∈ G.neighborFinset u, G.degree v) ≤ G.edgeFinset.card+k) :
    t+1 ≤ randic G := by
  obtain ⟨hp,hn⟩ := orthogonal_subordinate_signs G hc ht he hE hx hy hort
  have hsp := triangleFree_subEigen_sq (restrict G (posSet x)) hP t hpos
    (fun v => max (x v) 0)
    (by obtain ⟨v,hv⟩ := hp; exact ⟨v,hv.trans_le (le_max_left _ _)⟩)
    (restrict_positive_subEigen G t x he)
  have he' : AdjEigen G t (fun v => -x v) := by
    intro v
    simp_rw [Finset.sum_neg_distrib, mul_neg, he v]
  have hset : posSet (fun v => -x v) = negSet x := by
    ext v; simp [posSet,negSet]
  have hsN := restrict_positive_subEigen G t (fun v => -x v) he'
  rw [hset] at hsN
  have hsn := triangleFree_subEigen_sq (restrict G (negSet x)) hN t hpos
    (fun v => max (-x v) 0)
    (by obtain ⟨v,hv⟩ := hn; exact ⟨v,(neg_pos.mpr hv).trans_le (le_max_left _ _)⟩)
    hsN
  have hsum := support_edge_budget G hc x hp hn
  let m : ℝ := G.edgeFinset.card
  have hbm : (2:ℝ)*t^2+1 ≤ m := by
    have hb : ((restrict G (posSet x)).edgeFinset.card:ℝ) +
        (restrict G (negSet x)).edgeFinset.card + 1 ≤ m := by dsimp [m]; exact_mod_cast hsum
    linarith only [hb,hsp,hsn]
  have hm : 0<m := by nlinarith only [hbm,sq_nonneg t]
  have hb : (t+1)^2≤m-k := by nlinarith only [hbm,hk]
  have hS : 0<Real.sqrt (m+k) := Real.sqrt_pos.2 (by positivity)
  apply le_trans ?_ (randic_of_neighbor_excess G k hne)
  change t+1≤m/Real.sqrt (m+k)
  apply (le_div_iff₀ hS).2
  have hleft : 0 ≤ (t+1)*Real.sqrt (m+k) := by positivity
  apply (sq_le_sq₀ hleft hm.le).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : 0≤m+k)]
  have hmul := mul_le_mul_of_nonneg_right hb (show 0≤m+k by positivity)
  nlinarith only [hmul,sq_nonneg (k:ℝ)]

theorem nodal_neighbor_excess (hc : G.Connected) (k kp kn : ℕ) {t L : ℝ} {x y : V → ℝ}
    (ht : t≤L) (hpos : 0<t) (hk : (k:ℝ)+kp+kn≤t*(t-2))
    (he : AdjEigen G t x) (hE : AdjEigen G L y)
    (hx : ∃ v, x v≠0) (hy : ∃ v, y v≠0) (hort : (∑ v : V,x v*y v)=0)
    (hP : ∀ u : V,
      (∑ v ∈ (restrict G (posSet x)).neighborFinset u, (restrict G (posSet x)).degree v) ≤
        (restrict G (posSet x)).edgeFinset.card+kp)
    (hN : ∀ u : V,
      (∑ v ∈ (restrict G (negSet x)).neighborFinset u, (restrict G (negSet x)).degree v) ≤
        (restrict G (negSet x)).edgeFinset.card+kn)
    (hne : ∀ u : V, (∑ v ∈ G.neighborFinset u, G.degree v) ≤ G.edgeFinset.card+k) :
    t+1 ≤ randic G := by
  obtain ⟨hp,hn⟩ := orthogonal_subordinate_signs G hc ht he hE hx hy hort
  have hsp := subEigen_sq_of_neighbor_excess (restrict G (posSet x)) kp hP t hpos
    (fun v => max (x v) 0)
    (by obtain ⟨v,hv⟩ := hp; exact ⟨v,hv.trans_le (le_max_left _ _)⟩)
    (restrict_positive_subEigen G t x he)
  have he' : AdjEigen G t (fun v => -x v) := by
    intro v
    simp_rw [Finset.sum_neg_distrib, mul_neg, he v]
  have hset : posSet (fun v => -x v) = negSet x := by
    ext v; simp [posSet,negSet]
  have hsN := restrict_positive_subEigen G t (fun v => -x v) he'
  rw [hset] at hsN
  have hsn := subEigen_sq_of_neighbor_excess (restrict G (negSet x)) kn hN t hpos
    (fun v => max (-x v) 0)
    (by obtain ⟨v,hv⟩ := hn; exact ⟨v,(neg_pos.mpr hv).trans_le (le_max_left _ _)⟩)
    hsN
  have hsum := support_edge_budget G hc x hp hn
  let m : ℝ := G.edgeFinset.card
  have hbm : (2:ℝ)*t^2+1 ≤ m+kp+kn := by
    have hb : ((restrict G (posSet x)).edgeFinset.card:ℝ) +
        (restrict G (negSet x)).edgeFinset.card + 1 ≤ m := by dsimp [m]; exact_mod_cast hsum
    linarith only [hb,hsp,hsn]
  have hm : 0<m := by nlinarith only [hbm,hk,sq_nonneg t,hpos,Nat.cast_nonneg (α:=ℝ) k]
  have hb : (t+1)^2≤m-k := by nlinarith only [hbm,hk]
  have hS : 0<Real.sqrt (m+k) := Real.sqrt_pos.2 (by positivity)
  apply le_trans ?_ (randic_of_neighbor_excess G k hne)
  change t+1≤m/Real.sqrt (m+k)
  apply (le_div_iff₀ hS).2
  have hleft : 0 ≤ (t+1)*Real.sqrt (m+k) := by positivity
  apply (sq_le_sq₀ hleft hm.le).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : 0≤m+k)]
  have hmul := mul_le_mul_of_nonneg_right hb (show 0≤m+k by positivity)
  nlinarith only [hmul,sq_nonneg (k:ℝ)]

#print axioms sparse_triangles_nodal
#print axioms nodal_neighbor_excess
end CazenaveOne
