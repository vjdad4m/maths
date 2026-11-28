import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Certificate

open scoped BigOperators
open Finset
namespace BadScienceSix.Formal

abbrev Input := Fin 32
abbrev Coord := Fin 6
abbrev Matrix := Coord → Coord → ℝ

def X (i : Input) (j : Coord) : ℤ :=
  if j.val = 0 then 1 else signed (i.val / 2^(j.val-1))

def doti (w : Coord → ℤ) (i : Input) : ℤ := ∑ j, w j * X i j
def normi (w : Coord → ℤ) : ℤ := ∑ j, (w j)^2
def signedSum (s : Finset Input) (b : Input → ℤ) (j : Coord) : ℤ := ∑ i ∈ s, b i * X i j
def rowEval (r : Coord → ℝ) (i : Input) : ℝ := ∑ j, r j * (X i j : ℝ)
noncomputable def maxEval (A : Matrix) (i : Input) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => |rowEval (A j) i|)
noncomputable def average (A : Matrix) : ℝ := (∑ i, maxEval A i) / 32
def UnitRows (A : Matrix) : Prop := ∀ j, ∑ k, (A j k)^2 = 1
noncomputable def chord (k : ℕ) : ℝ := 16-8*Real.sqrt 3+(2*Real.sqrt 3-2)*(k:ℝ)

theorem X_sq (i : Input) (j : Coord) : X i j ^ 2 = 1 := by
  unfold X signed
  split <;> norm_num

theorem orthog (j k : Coord) : ∑ i : Input, X i j * X i k = if j = k then 32 else 0 := by
  fin_cases j <;> fin_cases k <;> decide +kernel

theorem parseval (w : Coord → ℤ) :
    ∑ i : Input, (doti w i)^2 = 32 * normi w := by
  calc
    _ = ∑ i : Input, ∑ j : Coord, ∑ k : Coord, w j * w k * (X i j * X i k) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [doti, pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ j : Coord, ∑ k : Coord, ∑ i : Input, w j * w k * (X i j * X i k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
    _ = 32 * normi w := by
      simp only [← Finset.mul_sum, orthog, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, normi]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp [eq_comm (a := j), Finset.sum_ite_eq', pow_two, mul_comm, mul_assoc, mul_left_comm]

theorem normi_signed_identity (s : Finset Input) (b : Input → ℤ) :
    normi (signedSum s b) = ∑ i ∈ s, b i * doti (signedSum s b) i := by
  unfold normi doti
  rw [show (∑ i ∈ s, b i * ∑ j : Coord, signedSum s b j * X i j) =
    ∑ j : Coord, ∑ i ∈ s, b i * (signedSum s b j * X i j) by
      simp only [Finset.mul_sum]; rw [Finset.sum_comm]]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = signedSum s b j * ∑ i ∈ s, b i * X i j := by simp only [pow_two, signedSum]
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring

theorem norm_nonneg (w : Coord → ℤ) : 0 ≤ normi w :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem signed_dot_le (w : Coord → ℤ) (b : Input → ℤ)
    (hb : ∀ i, b i = 1 ∨ b i = -1) (i : Input) :
    b i * doti w i ≤ (doti w i).natAbs := by
  rcases hb i with h | h
  · rw [h, one_mul]; omega
  · rw [h, neg_one_mul]; omega

end BadScienceSix.Formal

namespace BadScienceSix.Formal

theorem sum_dot_le_sqrt (r : Coord → ℝ) (w : Coord → ℤ)
    (hr : ∑ j, (r j)^2 = 1) :
    ∑ j, r j * (w j : ℝ) ≤ Real.sqrt (normi w : ℝ) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ r (fun j => (w j : ℝ))
  rw [hr, one_mul] at h
  have hc : (∑ j : Coord, (w j : ℝ)^2) = (normi w : ℝ) := by simp [normi]
  rw [hc] at h
  have hz : 0 ≤ (normi w : ℝ) := by exact_mod_cast norm_nonneg w
  have hs := Real.sq_sqrt hz
  have hp := Real.sqrt_nonneg (normi w : ℝ)
  by_contra! hn
  nlinarith [sq_nonneg ((∑ j, r j * (w j : ℝ)) - Real.sqrt (normi w : ℝ))]

theorem card_square_bound (s : Finset Input) (b : Input → ℤ)
    (hb : ∀ i, b i = 1 ∨ b i = -1) :
    (normi (signedSum s b) : ℝ) ≤ 32 * (s.card : ℝ) := by
  let w := signedSum s b
  have hn : 0 ≤ (normi w : ℝ) := by exact_mod_cast norm_nonneg w
  have hi : (normi w : ℝ) ≤ ∑ i ∈ s, ((doti w i).natAbs : ℝ) := by
    have hh : normi w ≤ ∑ i ∈ s, ((doti w i).natAbs : ℤ) := (calc
      normi w = ∑ i ∈ s, b i * doti w i := normi_signed_identity s b
      _ ≤ ∑ i ∈ s, ((doti w i).natAbs : ℤ) := Finset.sum_le_sum (fun i _ => signed_dot_le w b hb i))
    have hc := (Int.cast_le (R := ℝ)).mpr hh
    simpa only [Int.cast_sum, Int.cast_natCast] using hc
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ((doti w i).natAbs : ℝ))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  have hu : ∑ i ∈ s, ((doti w i).natAbs : ℝ)^2 ≤ 32 * (normi w : ℝ) := by
    calc
      _ ≤ ∑ i : Input, ((doti w i).natAbs : ℝ)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun _ _ _ => sq_nonneg _)
      _ = _ := by
        have h0 : ∀ t : ℤ, ((t.natAbs : ℕ) : ℝ)^2 = (t : ℝ)^2 := by
          intro t
          cases t <;> simp [Int.natAbs, neg_pow, even_two]; ring
        simp_rw [h0]
        exact_mod_cast parseval w
  have h := le_trans (pow_le_pow_left₀ hn hi 2) (le_trans hc (mul_le_mul_of_nonneg_left hu (by positivity)))
  change (normi w : ℝ) ≤ _
  by_cases hcase : (normi w : ℝ) ≤ 32 * (s.card : ℝ)
  · exact hcase
  have hnot := lt_of_not_ge hcase
  have hpos : 0 < (normi w : ℝ) := lt_of_le_of_lt (by positivity) hnot
  nlinarith [mul_pos hpos (sub_pos.mpr hnot)]

theorem rational_chord_le (k : ℕ) :
    ((1464:ℝ) * k + 2143) / 1000 ≤ chord k := by
  have hlo : (1.732:ℝ) ≤ Real.sqrt 3 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hhi : Real.sqrt 3 ≤ (1.732125:ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  unfold chord
  nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (show 0 ≤ (k:ℝ) by positivity)]

theorem small_chord (k : Fin 12) : Real.sqrt (upperSq k.val : ℝ) ≤ chord k.val := by
  rcases chord_arithmetic k with h | h | h
  · rw [h]
    have hv : upperSq 4 = 64 := rfl
    rw [hv]
    unfold chord
    have : Real.sqrt 64 = 8 := by rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    norm_num only [Nat.cast_ofNat]
    rw [this]
    ring_nf
    exact le_rfl
  · rw [h]
    have hv : upperSq 8 = 192 := rfl
    rw [hv]
    simp only [chord, Nat.cast_ofNat]
    have hx : Real.sqrt 192 = 8 * Real.sqrt 3 := by
      rw [show (192:ℝ) = 64*3 by norm_num, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 64)]
      have : Real.sqrt 64 = 8 := by rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [this]
    rw [hx]
    ring_nf
    exact le_rfl
  · apply le_trans _ (rational_chord_le k.val)
    rw [Real.sqrt_le_left (by positivity)]
    have hh : (1000000 : ℝ) * upperSq k.val ≤ ((1464 : ℝ) * k.val + 2143)^2 := by
      exact_mod_cast h
    nlinarith

theorem large_chord (k : ℕ) (hk : 12 ≤ k) : Real.sqrt (32 * (k:ℝ)) ≤ chord k := by
  apply le_trans _ (rational_chord_le k)
  rw [Real.sqrt_le_left (by positivity)]
  have h0 : (12 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith [sq_nonneg ((k : ℝ) - 12)]

end BadScienceSix.Formal

namespace BadScienceSix.Formal

def cutoff (k a b c d e f : Nat) : Nat :=
  ((((List.range 32).map (fun i => (dot a b c d e f i).natAbs)).foldl
    (fun l v => (insertDesc v l).take k) []).getLast?).getD 0

def budget (k a b c d e f : Nat) : Nat :=
  let t := cutoff k a b c d e f
  k*t + ∑ i : Input, ((dot a b c d e f i.val).natAbs - t)

def checkB (k : Nat) : Bool :=
  let r := List.range (k / 2 + 1)
  r.all fun a =>
    r.all fun b => a > b ||
    (r.all fun c => b > c ||
    (r.all fun d => c > d ||
    (r.all fun e => d > e ||
    (r.all fun f => e > f ||
      let v := fun x => 2*x + k%2
      let q := norm2 (v a) (v b) (v c) (v d) (v e) (v f)
      q ≤ upperSq k || q > budget k (v a) (v b) (v c) (v d) (v e) (v f)))))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem checkB_correct (k : Fin 12) : checkB k.val = true := by
  have h : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 ∨
      k.val = 4 ∨ k.val = 5 ∨ k.val = 6 ∨ k.val = 7 ∨
      k.val = 8 ∨ k.val = 9 ∨ k.val = 10 ∨ k.val = 11 := by omega
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h <;> rw [h] <;> decide +kernel

theorem bound_of_budget (k : Fin 12) (a b c d e f : Nat)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e) (hef : e ≤ f)
    (hfk : f ≤ k.val / 2)
    (hs :
      let v := fun x => 2*x + k.val%2
      norm2 (v a) (v b) (v c) (v d) (v e) (v f) ≤
        budget k.val (v a) (v b) (v c) (v d) (v e) (v f)) :
    let v := fun x => 2*x + k.val%2
    norm2 (v a) (v b) (v c) (v d) (v e) (v f) ≤ upperSq k.val := by
  have cert := checkB_correct k
  simp only [checkB, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at cert
  have h := cert a (by omega) b (by omega)
  rcases h with h | h
  · omega
  rcases h c (by omega) with h | h
  · omega
  rcases h d (by omega) with h | h
  · omega
  rcases h e (by omega) with h | h
  · omega
  rcases h f (by omega) with h | h
  · omega
  rcases h with h | h
  · exact h
  · exact False.elim ((Nat.not_lt_of_ge hs) h)


end BadScienceSix.Formal
