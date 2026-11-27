import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace KelmansCactus.AtomicBridge.RemoteBudgetExpectation
open Finset
open scoped BigOperators

/-- If every lost pair of shore edges is chargeable to an individual legal
two-shore exchange, the fractional expectations force an affordable exchange.
The caller supplies the fractional matching distribution and exact local split
charges; neither is hidden in the Lean theorem. -/
theorem find_affordable [Fintype ι]
    (weight : ι→ℚ) (weight_nonnegative : ∀ i,0≤weight i)
    (gap : ℕ) (gap_pos : 0<gap) (pairs : ι→ℕ)
    (charge : (i : ι) → Fin (pairs i) → ℕ)
    (gain : ι→ℕ)
    (component_budget : ∀ i, (∑ j : Fin (pairs i), charge i j)≤gain i)
    (meanGain : (∑ i : ι, weight i * (gain i : ℚ))=(gap : ℚ))
    (meanPairs : (∑ i : ι, weight i * (pairs i : ℚ))>1) :
    ∃ i, ∃ j : Fin (pairs i), charge i j < gap := by
  classical
  by_contra! expensive
  have larger (i : ι) : pairs i * gap ≤ gain i := by
    apply le_trans ?_ (component_budget i)
    have sums : (∑ j : Fin (pairs i), gap) ≤ (∑ j : Fin (pairs i), charge i j) :=
      Finset.sum_le_sum (fun j _=>expensive i j)
    simpa [Nat.mul_comm] using sums
  have means : (∑ i : ι, weight i * ((pairs i : ℚ)*(gap : ℚ))) ≤
      ∑ i : ι, weight i * (gain i : ℚ) := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (weight_nonnegative i)
    exact_mod_cast larger i
  simp_rw [←mul_assoc,←Finset.sum_mul] at means
  rw [meanGain] at means
  have positivity : 0 < (gap : ℚ) := by exact_mod_cast gap_pos
  have lt := mul_lt_mul_of_pos_right meanPairs positivity
  rw [one_mul] at lt
  exact (not_lt_of_ge means) lt

/-- The precise four-edge case: a mean lost-edge count of 8/3 forces the
mean number of pairs to be 4/3 and supplies an individual cheap exchange. -/
theorem four_edge_affordable [Fintype ι]
    (weight : ι→ℚ) (weight_nonnegative : ∀ i,0≤weight i)
    (gap : ℕ) (gap_pos : 0<gap) (pairs : ι→ℕ)
    (charge : (i : ι) → Fin (pairs i) → ℕ)
    (gain lost : ι→ℕ)
    (double : ∀ i,lost i=2*pairs i)
    (component_budget : ∀ i,(∑ j : Fin (pairs i), charge i j)≤gain i)
    (meanGain : (∑ i : ι, weight i*(gain i : ℚ))=(gap : ℚ))
    (meanLost : (∑ i : ι, weight i*(lost i : ℚ))=(8:ℚ)/3) :
    ∃ i,∃ j : Fin (pairs i),charge i j<gap := by
  apply find_affordable weight weight_nonnegative gap gap_pos pairs charge gain
    component_budget meanGain
  have he : ∀ i, weight i*(lost i : ℚ)=2*(weight i*(pairs i : ℚ)) := by
    intro i
    rw [double]
    push_cast
    ring
  simp_rw [he,←Finset.mul_sum] at meanLost
  linarith

#print axioms find_affordable
#print axioms four_edge_affordable
end KelmansCactus.AtomicBridge.RemoteBudgetExpectation
