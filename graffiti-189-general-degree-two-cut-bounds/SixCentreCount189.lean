import SixCentreParity189
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Graffiti189SixCentre
open Finset
open scoped BigOperators

theorem sum_coverage_accounting {V : Type*} (s : Finset V) (w : V → ℕ)
    (lo : ∀ x ∈ s, 1 ≤ w x) (hi : ∀ x ∈ s, w x ≤ 3) :
    (∑ x ∈ s, w x) + (s.filter fun x => w x = 1).card =
      2 * s.card + (s.filter fun x => 3 ≤ w x).card := by
  classical
  have p : ∀ x ∈ s, w x + (if w x = 1 then 1 else 0) =
      2 + (if 3 ≤ w x then 1 else 0) := by
    intro x hx
    have l := lo x hx
    have h := hi x hx
    repeat' first | omega | split
  have z := Finset.sum_congr (rfl : s = s) p
  have indicator (P : V → Prop) [DecidablePred P] :
      (∑ x ∈ s, if P x then (1 : ℕ) else 0) = (s.filter P).card := by
    rw [← Finset.sum_filter]
    simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, indicator, indicator] at z
  have constant : (∑ x ∈ s, (2 : ℕ)) = 2 * s.card := by
    simp [Finset.sum_const, Nat.mul_comm]
  rw [constant] at z
  exact z

theorem order_from_six_charges (n d f g total : ℕ)
    (partition : total + f + 4 = 2 * n + g)
    (budget : 10 + total ≤ 6 * (d + 1)) :
    2 * n + g ≤ 6 * d + f := by omega

theorem order_le_three_mul_of_nonpositive_defect (n d f g : ℕ)
    (charge : 2 * n + g ≤ 6 * d + f) (hg : f ≤ g) :
    n ≤ 3 * d := by omega

#print axioms sum_coverage_accounting
#print axioms order_from_six_charges
#print axioms order_le_three_mul_of_nonpositive_defect
end Graffiti189SixCentre
