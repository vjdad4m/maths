import Akbari
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace AkbariRandic
open SimpleGraph

theorem explicit_constant {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 : ℝ) ^ (-(1/3) : ℝ) * (matchingNumber G : ℝ) ^ (2/3 : ℝ) ≤ randic G := by
  let x : ℝ := matchingNumber G
  let c : ℝ := (2 : ℝ) ^ (-(1/3) : ℝ)
  have hx : 0 ≤ x := Nat.cast_nonneg _
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hr : 0 ≤ randic G := by
    unfold randic
    apply Finset.sum_nonneg
    intro e _
    induction e using Sym2.ind with
    | h a b => exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have cube (u : ℝ) (hu : 0 ≤ u) (a : ℝ) :
      (u ^ a)^3 = u ^ (a * 3 : ℝ) := by
    rw [Real.rpow_mul hu, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  have cx : (x ^ (2/3 : ℝ))^3 = x^2 := by
    rw [cube _ hx, show (2/3 : ℝ)*3 = (2 : ℕ) by norm_num, Real.rpow_natCast]
  have cc : c^3 = 1/2 := by
    dsimp [c]
    rw [cube _ (by norm_num),show (-(1/3) : ℝ)*3 = -1 by norm_num,Real.rpow_neg (by norm_num), Real.rpow_one]
    norm_num
  change c * x ^ (2/3 : ℝ) ≤ randic G
  apply (pow_le_pow_iff_left₀ (mul_nonneg hc.le (Real.rpow_nonneg hx _)) hr (by decide : (3:ℕ) ≠ 0)).mp
  rw [mul_pow, cc, cx]
  have h : x ^ 2 ≤ 2 * randic G ^ 3 := matching_number_cube_bound G
  linarith

/-- Akbari–Ghasemi Nezhad–Ghazizadeh–Haslegrave–Tohidi, Conjecture 9. -/
theorem conjecture9 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        c * (matchingNumber G : ℝ) ^ (2/3 : ℝ) ≤ randic G :=
  ⟨_,Real.rpow_pos_of_pos (by norm_num) _, fun _ _ _ G _ => explicit_constant G⟩

#print axioms explicit_constant
#print axioms conjecture9
end AkbariRandic
