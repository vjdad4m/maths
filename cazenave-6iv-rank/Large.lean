import RankBound

namespace CazenaveRank
set_option autoImplicit false
open scoped BigOperators

theorem am_step (B K x y : ℝ) (hb : 0 < B) (_hk : 0 ≤ K)
    (hkB : 4*K^3 ≤ 27*B) (hx : 0 < x) (hy : 0 < y) :
    K/B ≤ 1/(x*y) + x/(2*B) + y/(2*B) := by
  have ha : 0 ≤ 1/(x*y) := div_nonneg zero_le_one (mul_nonneg hx.le hy.le)
  have hb0 : 0 < 2*B := by linarith
  have hbx : 0 ≤ x/(2*B) := div_nonneg hx.le hb0.le
  have hby : 0 ≤ y/(2*B) := div_nonneg hy.le hb0.le
  have hterm : 27*(1/(x*y))*(x/(2*B))*(y/(2*B)) = 27/(4*B^2) := by
    field_simp; ring
  have hpow : (K/B)^3 ≤ 27/(4*B^2) := by
    rw [div_pow]
    apply (div_le_div_iff₀ (pow_pos hb 3) (mul_pos (by norm_num) (pow_pos hb 2))).2
    have hm := mul_le_mul_of_nonneg_right hkB (sq_nonneg B)
    nlinarith only [hm]
  have hh := cube_gap _ _ _ ha hbx hby
  rw [hterm] at hh
  by_contra! hcontra
  exact (not_lt_of_ge (hpow.trans hh)) (pow_lt_pow_left₀ hcontra (by linarith) (by decide))

/-- Graph-theoretic lift of the abstract row inequality. The remaining
    linear algebra is to extract the permutation from adjacency rank. -/
theorem graph_lower_from_perm {V ι : Type} [Fintype V] [Fintype ι] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : ι ↪ V) (π : Equiv.Perm ι)
    (B K : ℝ) (hB : 0 < B) (hK : 0 ≤ K)
    (hAM : 4*K^3 ≤ 27*B)
    (hdegree : ∀ v : V, (G.degree v : ℝ) ≤ B^2)
    (hpos : ∀ v : V, 0 < G.degree v)
    (hAdj : ∀ i : ι, G.Adj (e i) (e (π i))) :
    ((Fintype.card V : ℝ) + (K-2)*Fintype.card ι)/ (2*B) ≤ randic G := by
  classical
  let x (v : V) := Real.sqrt (G.degree v : ℝ)
  have hxn (v : V) : 0 ≤ x v := Real.sqrt_nonneg _
  have hxs (v : V) : (x v)^2 = G.degree v := Real.sq_sqrt (Nat.cast_nonneg _)
  have hxp (v w : V) (h : G.Adj v w) : 0 < x v := by
    have hm : w ∈ G.neighborFinset v := (G.mem_neighborFinset _ _).mpr h
    have hd : 0 < G.degree v := Finset.card_pos.mpr ⟨w,hm⟩
    exact Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hx1 (i : ι) : 1 ≤ x (e i) := by
    have hm : e (π i) ∈ G.neighborFinset (e i) := (G.mem_neighborFinset _ _).mpr (hAdj i)
    have hd : 0 < G.degree (e i) := Finset.card_pos.mpr ⟨_,hm⟩
    have ha : (1:ℝ) ≤ G.degree (e i) := by exact_mod_cast hd
    exact Real.le_sqrt_of_sq_le (by simpa using ha)
  have hxu (v : V) : x v ≤ B :=
    Real.sqrt_le_iff.mpr ⟨hB.le, hdegree v⟩
  let row (v : V) := ∑ w ∈ G.neighborFinset v, (1 : ℝ)/(x v*x w)
  have hx1v (v : V) : 1 ≤ x v := by
    apply Real.le_sqrt_of_sq_le
    have h : (1 : ℝ) ≤ G.degree v := by exact_mod_cast hpos v
    simpa using h
  have hmass (v : V) : 1/B ≤ row v := by
    have hv : 0 < x v := by linarith [hx1v v]
    have hpoint (w : V) (hw : w ∈ G.neighborFinset v) : 1/(B*x v) ≤ 1/(x v*x w) := by
      have hpw := hxp w v ((G.mem_neighborFinset _ _).mp hw).symm
      apply one_div_le_one_div_of_le (mul_pos hv hpw)
      rw [mul_comm B]
      exact mul_le_mul_of_nonneg_left (hxu w) hv.le
    have hh := Finset.sum_le_sum hpoint
    simp only [Finset.sum_const, nsmul_eq_mul, G.card_neighborFinset_eq_degree] at hh
    have h : (G.degree v:ℝ) * (1/(B*x v)) = x v/B := by
      rw [← hxs v]
      field_simp; ring
    rw [h] at hh
    exact ((div_le_div_iff_of_pos_right hB).mpr (hx1v v)).trans hh
  have hrow (i : ι) : 1/(x (e i)*x (e (π i))) +
      x (e i)/(2*B) + x (e i)/(2*B) - 2/(2*B) ≤ row (e i) := by
    let v := e i
    let z := e (π i)
    have haz : G.Adj v z := hAdj i
    have hmz : z ∈ G.neighborFinset v := (G.mem_neighborFinset _ _).mpr haz
    have hv : 0 < x v := hxp v z haz
    have h0 : 0 < 2*B := by linarith
    let D := (G.neighborFinset v).erase z
    have hD (w : V) (hw : w ∈ D) :
        2/(2*B*x v) ≤ 1/(x v*x w) := by
      have haw : G.Adj v w := (G.mem_neighborFinset _ _).mp (Finset.mem_of_mem_erase hw)
      have hpw := hxp w v haw.symm
      apply (div_le_div_iff₀ (mul_pos h0 hv) (mul_pos hv hpw)).mpr
      have hhh := mul_le_mul_of_nonneg_left (hxu w) hv.le
      nlinarith only [hhh]
    have hpart := Finset.sum_le_sum hD
    have hs : row v = (∑ w ∈ D, 1/(x v*x w))+1/(x v*x z) := by
      exact (Finset.sum_erase_add _ _ hmz).symm
    simp only [Finset.sum_const,nsmul_eq_mul] at hpart
    have hcar : (D.card : ℝ) = (x v)^2 - 1 := by
      have hc : D.card + 1 = G.degree v := by
        change ((G.neighborFinset v).erase z).card + 1 = (G.neighborFinset v).card
        exact Finset.card_erase_add_one hmz
      have hc' : (D.card : ℝ) + 1 = G.degree v := by exact_mod_cast hc
      linarith only [hc', hxs v]
    rw [hcar] at hpart
    have heq : (x v ^ 2 - 1) * (2/(2*B*x v)) =
        x v/(2*B) + x v/(2*B) - (1/x v)*(2/(2*B)) := by
      field_simp; ring
    rw [heq] at hpart
    have h1 : 1/x v ≤ 1 := (div_le_iff₀ hv).2 (by simpa using hx1 i)
    have h2 := mul_le_mul_of_nonneg_right h1 (div_nonneg (show (0:ℝ) ≤ 2 by norm_num) h0.le)
    change 1/(x v*x z) + x v/(2*B) + x v/(2*B) - 2/(2*B) ≤ row v
    rw [hs]
    linarith
  have hall (i : ι) : (K-2)/B ≤ 1/(x (e i)*x (e (π i))) +
      x (e i)/(2*B) + x (e (π i))/(2*B) - 2/(2*B) - 1/B := by
    have hm := am_step B K (x (e i)) (x (e (π i))) hB hK hAM
      (by linarith [hx1 i]) (by linarith [hx1 (π i)])
    have heq : (K-2)/B = K/B - 2/(2*B) - 1/B := by field_simp; ring
    rw [heq]
    linarith
  have hfull : (∑ i, (row (e i)-1/B)) ≤ ∑ v, (row v-1/B) := by
    have heq : (∑ i, (row (e i)-1/B)) = ∑ v ∈ Finset.univ.map e, (row v-1/B) := by
      rw [Finset.sum_map]
    rw [heq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun v _ _ => sub_nonneg.mpr (hmass v))
  have hu := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hall i)
  have hv := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hu hv hfull
  rw [Equiv.sum_comp π (fun i => x (e i)/(2*B))] at hu
  change _ ≤ (∑ v, row v)/2
  apply (div_le_div_iff₀ (show 0 < 2*B by linarith) (by norm_num : (0:ℝ)<2)).2
  have hz : (Fintype.card ι : ℝ)*((K-2)/B) + (Fintype.card V : ℝ)*(1/B) ≤
      ∑ v, row v := by linarith only [hu,hv,hfull]
  have hm := mul_le_mul_of_nonneg_right hz (show 0 ≤ 2*B by linarith)
  have heq : ((Fintype.card ι : ℝ)*((K-2)/B) + (Fintype.card V : ℝ)*(1/B))*(2*B) =
      ((Fintype.card V : ℝ) + (K-2)*Fintype.card ι)*2 := by field_simp; ring
  rwa [heq] at hm

#print axioms graph_lower_from_perm

/-- The complete large-order range, conditional only on the cardinality-r
    adjacent permutation, and otherwise on the genuine graph data. -/
theorem large_order_from_perm {V ι : Type} [Fintype V] [Fintype ι] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : ι ↪ V) (π : Equiv.Perm ι)
    (hn : 91 ≤ Fintype.card V) (hpos : ∀ v : V, 0 < G.degree v)
    (hAdj : ∀ i : ι, G.Adj (e i) (e (π i))) :
    1+(3/2)*(Real.sqrt (Fintype.card ι)-Real.sqrt 2) < randic G := by
  let n : ℝ := Fintype.card V
  let r : ℝ := Fintype.card ι
  let A : ℝ := Real.sqrt r
  let B : ℝ := Real.sqrt (n-1)
  have hn' : 91≤n := by dsimp [n]; exact_mod_cast hn
  have hB : 0<B := Real.sqrt_pos.2 (by linarith : 0<n-1)
  have hB2 : B^2=n-1 := Real.sq_sqrt (by linarith : 0≤n-1)
  have hA2 : A^2=r := Real.sq_sqrt (Nat.cast_nonneg _)
  have hRt : (7/6:ℝ) < Real.sqrt 2 := by
    exact (Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 7/6)).2 (by norm_num)
  have hdegree (v : V) : (G.degree v : ℝ) ≤ B^2 := by
    rw [hB2]
    have hd : G.degree v + 1 ≤ Fintype.card V := Nat.succ_le_of_lt (G.degree_lt_card_verts v)
    have h' : (G.degree v:ℝ)+1 ≤ (Fintype.card V:ℝ) := by exact_mod_cast hd
    exact (le_sub_iff_add_le).2 h'
  have h₂B : 0<2*B := by linarith
  change 1+(3/2)*(A-Real.sqrt 2) < randic G
  by_cases h : 131≤n
  · have h₀ : (4:ℝ)*(17/12)^3 ≤ B :=
      Real.le_sqrt_of_sq_le (by norm_num; linarith)
    have hK : 4*(17/4:ℝ)^3 ≤ 27*B := by norm_num at h₀ ⊢; linarith
    have hR := graph_lower_from_perm G e π B (17/4) hB (by norm_num) hK hdegree hpos hAdj
    have hh : (3/2)*A ≤ (n+(17/4-2)*r)/(2*B) := by
      apply (le_div_iff₀ h₂B).2
      nlinarith only [sq_nonneg (B-3/2*A),hB2,hA2]
    exact (show 1+(3/2)*(A-Real.sqrt 2)<(3/2)*A by linarith).trans_le (hh.trans hR)
  · have h₀ : (256/27:ℝ) ≤ B :=
      Real.le_sqrt_of_sq_le (by norm_num; linarith)
    have hK : 4*(4:ℝ)^3 ≤ 27*B := by norm_num; linarith
    have hB' : B<12 := by
      apply (Real.sqrt_lt (by linarith : 0≤n-1) (by norm_num : (0:ℝ)≤12)).2
      norm_num
      linarith
    have hR := graph_lower_from_perm G e π B 4 hB (by norm_num) hK hdegree hpos hAdj
    have hh : (3/2)*A-B/16 ≤ (n+(4-2)*r)/(2*B) := by
      apply (le_div_iff₀ h₂B).2
      nlinarith only [sq_nonneg (A-3*B/4),hB2,hA2]
    exact (show 1+(3/2)*(A-Real.sqrt 2)<(3/2)*A-B/16 by linarith).trans_le (hh.trans hR)

#print axioms large_order_from_perm
end CazenaveRank
