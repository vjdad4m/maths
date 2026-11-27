import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace CazenaveRank
set_option autoImplicit false

private theorem cube_gap_sorted (x y z : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hyz : y ≤ z) : 27 * x * y * z ≤ (x+y+z)^3 := by
  let u := y-x
  let v := z-y
  have hu : 0 ≤ u := sub_nonneg.mpr hxy
  have hv : 0 ≤ v := sub_nonneg.mpr hyz
  have h : (x+y+z)^3 - 27*x*y*z =
      8*u^3+12*u^2*v+9*u^2*x+6*u*v^2+9*u*v*x+v^3+9*v^2*x := by
    dsimp [u,v]
    ring
  have h' : 0 ≤ 8*u^3+12*u^2*v+9*u^2*x+6*u*v^2+9*u*v*x+v^3+9*v^2*x := by
    exact add_nonneg
      (add_nonneg (add_nonneg (add_nonneg (add_nonneg
        (add_nonneg (mul_nonneg (by norm_num) (pow_nonneg hu _))
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg u)) hv))
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg u)) hx))
        (mul_nonneg (mul_nonneg (by norm_num) hu) (sq_nonneg v)))
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hu) hv) hx))
        (pow_nonneg hv _))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg v)) hx)
  linarith

theorem cube_gap (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27*a*b*c ≤ (a+b+c)^3 := by
  by_cases hab : a ≤ b <;> by_cases hbc : b ≤ c <;> by_cases hac : a ≤ c
  · exact cube_gap_sorted a b c ha hab hbc
  · exact (hac (hab.trans hbc)).elim
  · nlinarith only [cube_gap_sorted a c b ha hac (le_of_not_ge hbc)]
  · nlinarith only [cube_gap_sorted c a b hc (le_of_not_ge hac) hab]
  · nlinarith only [cube_gap_sorted b a c hb (le_of_not_ge hab) hac]
  · nlinarith only [cube_gap_sorted b c a hb hbc (le_of_not_ge hac)]
  · exact (hab (hac.trans (le_of_not_ge hbc))).elim
  · nlinarith only [cube_gap_sorted c b a hc (le_of_not_ge hbc) (le_of_not_ge hab)]

/-- The edge-allocation pointwise inequality, with t = sqrt(rank A).
    The constants give the exact sufficient rank threshold floor((1331/81)^2)+1 = 271. -/
theorem rank271_pointwise (t x y : ℝ) (ht : 0 < t) (ht2 : 271 ≤ t^2)
    (hx : 0 < x) (hy : 0 < y) :
    11/(3*t) ≤ 1/(x*y) + x/(3*t) + y/(3*t) := by
  have htl : 1331/81 ≤ t := by
    by_contra! hh
    have := mul_pos (sub_pos.mpr hh) (show 0 < (1331:ℝ)/81+t by linarith)
    nlinarith
  have htpos : 0 < 3*t := by linarith
  have ha : 0 ≤ 1/(x*y) := div_nonneg zero_le_one (mul_nonneg hx.le hy.le)
  have hb : 0 ≤ x/(3*t) := div_nonneg hx.le htpos.le
  have hc : 0 ≤ y/(3*t) := div_nonneg hy.le htpos.le
  have hp : 27*(1/(x*y))*(x/(3*t))*(y/(3*t)) = 3/t^2 := by
    field_simp; ring
  have hl : (11/(3*t))^3 ≤ 3/t^2 := by
    rw [div_pow]
    apply (div_le_div_iff₀ (pow_pos htpos 3) (pow_pos ht 2)).2
    have hlin : (1331:ℝ) ≤ 81*t := by linarith
    have hm := mul_le_mul_of_nonneg_right hlin (sq_nonneg t)
    nlinarith only [hm]
  have hℓ := cube_gap _ _ _ ha hb hc
  rw [hp] at hℓ
  by_contra! hh
  have hup : (1/(x*y) + x/(3*t) + y/(3*t)) ^ 3 < (11/(3*t)) ^ 3 :=
    pow_lt_pow_left₀ hh (by linarith) (by decide)
  linarith
#print axioms rank271_pointwise

open scoped BigOperators

/-- The summed row inequality. Inputs model the support of a nonsingular principal
    adjacency submatrix and a neighbor permutation obtained from its determinant. -/
theorem rank271_from_rows {ι : Type} [Fintype ι] (π : Equiv.Perm ι)
    (t R : ℝ) (x : ι → ℝ)
    (ht : 0 < t) (ht2 : 271 ≤ t^2) (hcard : (Fintype.card ι : ℝ) = t^2)
    (hx : ∀ i, 1 ≤ x i)
    (hrows : (∑ i, (1/(x i*x (π i)) + x i/(3*t) + x i/(3*t) - 2/(3*t))) ≤ 2*R) :
    (3/2 : ℝ)*t ≤ R := by
  have h_each (i : ι) : 3/t ≤ 1/(x i*x (π i)) + x i/(3*t) + x (π i)/(3*t) - 2/(3*t) := by
    have h := rank271_pointwise t (x i) (x (π i)) ht ht2 (by linarith [hx i])
      (by linarith [hx (π i)])
    have ht' : 3*t ≠ 0 := by linarith
    have hr : 3/t = 11/(3*t) - 2/(3*t) := by field_simp; ring
    rw [hr]
    linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h_each i)
  have he := Equiv.sum_comp π (fun i => x i / (3*t))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum hrows
  rw [he] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hrows
  have ht' : t ≠ 0 := ne_of_gt ht
  have hh : t^2 * (3/t) = 3*t := by field_simp; ring
  rw [hh] at hsum
  linarith

#print axioms rank271_from_rows

/-- Randić expressed as a sum over oriented edges, divided by two. -/
noncomputable def randic {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (∑ v, ∑ w ∈ G.neighborFinset v,
    (1 : ℝ)/(Real.sqrt (G.degree v) * Real.sqrt (G.degree w))) / 2

/-- Graph-theoretic lift of the abstract row inequality. The remaining
    linear algebra is to extract the permutation from adjacency rank. -/
theorem graph_rank271_from_permutation {V ι : Type} [Fintype V] [Fintype ι] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : ι ↪ V) (π : Equiv.Perm ι)
    (t : ℝ)
    (ht : 0 < t) (ht2 : 271 ≤ t^2) (hcard : (Fintype.card ι : ℝ) = t^2)
    (hdegree : ∀ v : V, (G.degree v : ℝ) ≤ (3*t/2)^2)
    (hAdj : ∀ i : ι, G.Adj (e i) (e (π i))) :
    (3/2 : ℝ)*t ≤ randic G := by
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
  have hxu (v : V) : x v ≤ 3*t/2 :=
    Real.sqrt_le_iff.mpr ⟨by linarith, hdegree v⟩
  let row (v : V) := ∑ w ∈ G.neighborFinset v, (1 : ℝ)/(x v*x w)
  have hrow_nonneg (v : V) : 0 ≤ row v :=
    Finset.sum_nonneg fun w _ => div_nonneg zero_le_one (mul_nonneg (hxn v) (hxn w))
  have hrow (i : ι) : 1/(x (e i)*x (e (π i))) +
      x (e i)/(3*t) + x (e i)/(3*t) - 2/(3*t) ≤ row (e i) := by
    let v := e i
    let z := e (π i)
    have haz : G.Adj v z := hAdj i
    have hmz : z ∈ G.neighborFinset v := (G.mem_neighborFinset _ _).mpr haz
    have hv : 0 < x v := hxp v z haz
    have h0 : 0 < 3*t := by linarith
    let D := (G.neighborFinset v).erase z
    have hD (w : V) (hw : w ∈ D) :
        2/(3*t*x v) ≤ 1/(x v*x w) := by
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
    have heq : (x v ^ 2 - 1) * (2/(3*t*x v)) =
        x v/(3*t) + x v/(3*t) - (1/x v)*(2/(3*t)) := by
      field_simp; ring
    rw [heq] at hpart
    have h1 : 1/x v ≤ 1 := (div_le_iff₀ hv).2 (by simpa using hx1 i)
    have h2 := mul_le_mul_of_nonneg_right h1 (div_nonneg (show (0:ℝ) ≤ 2 by norm_num) h0.le)
    change 1/(x v*x z) + x v/(3*t) + x v/(3*t) - 2/(3*t) ≤ row v
    rw [hs]
    linarith
  have hfull : (∑ i, row (e i)) ≤ ∑ v, row v := by
    have heq : (∑ i, row (e i)) = ∑ v ∈ Finset.univ.map e, row v := by
      rw [Finset.sum_map]
    rw [heq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hrow_nonneg v)
  apply rank271_from_rows π t (randic G) (fun i => x (e i)) ht ht2 hcard hx1
  change (∑ i, (1 / (x (e i) * x (e (π i))) + x (e i) / (3 * t) + x (e i) / (3 * t) - 2 / (3 * t))) ≤
    2 * ((∑ v, row v)/2)
  linarith only [Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i), hfull]

#print axioms graph_rank271_from_permutation
end CazenaveRank
