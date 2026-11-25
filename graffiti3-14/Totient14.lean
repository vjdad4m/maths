/- Reproduce in a project pinned to Lean 4.19.0 / Mathlib v4.19.0 with `lake env lean Totient14.lean`. -/

import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

open scoped BigOperators
namespace GraffitiThree14
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

/-- Totient/divisor ratio for a prime power of exponent t+1. -/
private def r (p t : ℕ) : ℚ :=
  (p : ℚ)^t * ((p : ℚ)-1) / ((t : ℚ)+2)

private def f (p a : ℕ) : ℚ :=
  if a = 0 then 1 else r p (a-1)

private theorem r_mono (p : ℕ) (hp : 2 ≤ p) : Monotone (r p) := by
  apply monotone_nat_of_le_succ
  intro t
  have hp' : (2 : ℚ) ≤ p := by exact_mod_cast hp
  have hn : (0 : ℚ) ≤ t := by positivity
  have hpow : (0 : ℚ) ≤ (p:ℚ)^t * ((p:ℚ)-1) := mul_nonneg (by positivity) (by linarith)
  have hs : ((t:ℚ)+3) ≤ (p:ℚ)*((t:ℚ)+2) := by nlinarith
  unfold r
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
  convert mul_le_mul_of_nonneg_left hs hpow using 1 <;> ring

private theorem f_half (p a : ℕ) (hp : 2 ≤ p) : 1/2 ≤ f p a := by
  by_cases ha : a = 0
  · norm_num [f, ha]
  have h := r_mono p hp (Nat.zero_le (a-1))
  rw [f, if_neg ha]
  apply le_trans _ h
  have hp' : (2 : ℚ) ≤ p := by exact_mod_cast hp
  unfold r
  norm_num
  linarith

private theorem f_ge_one (p a : ℕ) (hp : 3 ≤ p) : 1 ≤ f p a := by
  by_cases ha : a = 0
  · norm_num [f, ha]
  have h := r_mono p (by omega) (Nat.zero_le (a-1))
  rw [f, if_neg ha]
  apply le_trans _ h
  have hp' : (3 : ℚ) ≤ p := by exact_mod_cast hp
  unfold r
  norm_num
  linarith

private theorem lower_r (p a b : ℕ) (hp : 2 ≤ p) (hb : b < a) : r p b ≤ f p a := by
  rw [f, if_neg (by omega)]
  exact r_mono p hp (by omega)

private theorem ratio_eq (n : ℕ) (hn : n ≠ 0) :
    (n.totient : ℚ)/(n.divisors.card : ℚ) =
      f 2 (n.factorization 2) *
        ∏ p ∈ n.primeFactors.erase 2, f p (n.factorization p) := by
  have hprod :
      (n.totient : ℚ)/(n.divisors.card : ℚ) =
        ∏ p ∈ n.primeFactors, f p (n.factorization p) := by
    rw [Nat.totient_eq_prod_factorization hn,
        Nat.prod_factorization_eq_prod_primeFactors, Nat.card_divisors hn]
    push_cast
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have ha : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hcast : ((p-1 : ℕ):ℚ) = (p:ℚ)-1 := by exact Nat.cast_sub (by omega)
    rw [f, if_neg ha, r, hcast]
    have hden : ((n.factorization p : ℕ):ℚ) + 1 =
        ((n.factorization p - 1 : ℕ):ℚ) + 2 := by
      rw [Nat.cast_sub (by omega)]
      ring
    rw [hden]
  rw [hprod]
  by_cases h : 2 ∈ n.primeFactors
  · exact (Finset.mul_prod_erase _ _ h).symm
  have hz : n.factorization 2 = 0 := Finsupp.not_mem_support_iff.mp h
  simp [hz, f, Finset.erase_eq_of_not_mem h]

private theorem prime_cases {p : ℕ} (hp : p.Prime) :
    p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ 11 ≤ p := by
  have h := hp.two_le
  by_cases hs : p < 11
  · interval_cases p <;> first | omega | (exfalso; exact (by decide : ¬Nat.Prime _) hp)
  · omega

private theorem one_le_prod_rat {s : Finset ℕ} {f : ℕ → ℚ}
    (h : ∀ x ∈ s, 1 ≤ f x) : 1 ≤ ∏ x ∈ s, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    rw [Finset.prod_insert ha]
    calc
      (1:ℚ) = 1*1 := by norm_num
      _ ≤ f a * (∏ x ∈ t, f x) := mul_le_mul h1 h2 (by norm_num) (by linarith)

private theorem cutoff_factors (p k : ℕ) (hp : p.Prime) (hd : p^k ∣ 5040) :
    k ≤ (5040:ℕ).factorization p := by
  have h := (Nat.factorization_le_iff_dvd (pow_ne_zero _ hp.ne_zero) (by decide)).mpr hd p
  simpa [hp.factorization_pow] using h

/-- Kernel-only decision on the sixty divisors of the finite cutoff. -/
private theorem finite_cutoff :
    ∀ n ∈ (5040 : ℕ).divisors, 2*n.divisors.card ≤ n.totient + 8 := by
  decide

theorem graffiti3_conj14 (n : ℕ) (hn : 1 ≤ n) :
    2 * n.divisors.card ≤ n.totient + 8 := by
  have hn0 : n ≠ 0 := by omega
  have hcard : 0 < n.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, hn0⟩⟩
  have hcard' : (0 : ℚ) < n.divisors.card := by exact_mod_cast hcard
  let a := n.factorization
  let P : ℚ := ∏ p ∈ n.primeFactors.erase 2, f p (a p)
  have hord : ∀ p ∈ n.primeFactors.erase 2, 1 ≤ f p (a p) := by
    intro p hp
    have hin := Finset.mem_erase.mp hp
    exact f_ge_one p _ (by have := (Nat.prime_of_mem_primeFactors hin.2).two_le; omega)
  have hp1 : 1 ≤ P := one_le_prod_rat hord
  have h2 : (1/2 : ℚ) ≤ f 2 (a 2) := f_half 2 _ (by decide)
  have hr : (n.totient : ℚ)/(n.divisors.card : ℚ) = f 2 (a 2) * P := ratio_eq n hn0
  by_cases hh : (2 : ℚ) ≤ (n.totient : ℚ)/(n.divisors.card : ℚ)
  · have h : (2 : ℚ) * n.divisors.card ≤ n.totient := (le_div_iff₀ hcard').mp hh
    have hN : 2*n.divisors.card ≤ n.totient := by exact_mod_cast h
    omega
  have hlt : f 2 (a 2) * P < 2 := by rw [← hr]; exact lt_of_not_ge hh
  have ha2 : a 2 ≤ 4 := by
    by_contra h
    have hbig := lower_r 2 (a 2) 4 (by decide) (by omega)
    norm_num [r] at hbig
    have hprod : f 2 (a 2) * 1 ≤ f 2 (a 2) * P :=
      mul_le_mul_of_nonneg_left hp1 (by linarith)
    linarith
  have boundOdd (p : ℕ) (hp : p∈n.primeFactors) (hne : p≠2) : f p (a p) < 4 := by
    have hmem : p ∈ n.primeFactors.erase 2 := Finset.mem_erase.mpr ⟨hne,hp⟩
    have hpnonneg : 0 ≤ f p (a p) := by linarith [hord p hmem]
    have hprod1 : 1 ≤ ∏ j ∈ (n.primeFactors.erase 2).erase p, f j (a j) :=
      one_le_prod_rat (fun j hj => hord j (Finset.mem_of_mem_erase hj))
    have hsingle : f p (a p) ≤ P := by
      dsimp [P]
      rw [← Finset.mul_prod_erase _ _ hmem]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod1 hpnonneg
    have hprod : (1/2 : ℚ)*P ≤ f 2 (a 2)*P := mul_le_mul_of_nonneg_right h2 (by linarith)
    linarith
  have hfac : n.factorization ≤ (5040 : ℕ).factorization := by
    intro p
    by_cases hp : p∈n.primeFactors
    · obtain h|h|h|h|h := prime_cases (Nat.prime_of_mem_primeFactors hp)
      · subst p
        exact Nat.le_trans ha2 (cutoff_factors 2 4 (by decide) (by decide))
      · subst p
        have hb := boundOdd 3 hp (by decide)
        have hc : a 3 ≤ 2 := by
          by_contra ht
          have hg := lower_r 3 (a 3) 2 (by decide) (by omega)
          norm_num [r] at hg
          linarith
        exact Nat.le_trans hc (cutoff_factors 3 2 (by decide) (by decide))
      · subst p
        have hb := boundOdd 5 hp (by decide)
        have hc : a 5 ≤ 1 := by
          by_contra ht
          have hg := lower_r 5 (a 5) 1 (by decide) (by omega)
          norm_num [r] at hg
          linarith
        exact Nat.le_trans hc (cutoff_factors 5 1 (by decide) (by decide))
      · subst p
        have hb := boundOdd 7 hp (by decide)
        have hc : a 7 ≤ 1 := by
          by_contra ht
          have hg := lower_r 7 (a 7) 1 (by decide) (by omega)
          norm_num [r] at hg
          linarith
        exact Nat.le_trans hc (cutoff_factors 7 1 (by decide) (by decide))
      · have hg := lower_r p (a p) 0 (by omega)
          (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp))
        have hb := boundOdd p hp (by omega)
        have hr11 : (11 : ℚ) ≤ p := by exact_mod_cast h
        norm_num [r] at hg
        linarith
    · have hz : n.factorization p = 0 := Finsupp.not_mem_support_iff.mp hp
      simp [hz]
  have hd : n ∣ 5040 := (Nat.factorization_le_iff_dvd hn0 (by decide)).mp hfac
  exact finite_cutoff n (Nat.mem_divisors.mpr ⟨hd, by decide⟩)

#print axioms graffiti3_conj14
end GraffitiThree14
