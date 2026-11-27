import LocalDensity133
import FiveCycle133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133 Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V]

theorem nat_density_of_le_average (G : SimpleGraph V) [Nonempty V] (d : ℕ)
    (h : (d : ℚ) ≤ averageLocal G) :
    d * Fintype.card V ≤ ∑ x, localIndependence G x := by
  classical
  unfold averageLocal at h
  have hn : (0 : ℚ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos (α := V)
  have hu := (le_div_iff₀ hn).mp h
  rw [← Nat.cast_sum, ← Nat.cast_mul] at hu
  exact_mod_cast hu

private theorem exists_P5_of_local_avg_gt_two (G : SimpleGraph V)
    (hc : G.Connected) (h4 : FourCycleFree G) (hAvg : 2 < averageLocal G) :
    ∃ f : Fin 5 → V, InducedPath G f := by
  classical
  letI := hc.nonempty
  by_cases h5 : NoSimpleFive133 G
  · exact no_four_five_path_of_local_density G h4 h5 1 (by decide)
      (nat_density_of_le_average G 2 (le_of_lt hAvg))
  · rcases five_cycle_or_P5 hc h4 h5 with p | ⟨f,hf,hr⟩
    · exact p
    · have hle : averageLocal G ≤ 2 := by
        unfold averageLocal
        have hn : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α:=V)
        apply (div_le_iff₀ hn).mpr
        calc
          (∑ x, (localIndependence G x : ℚ)) ≤ ∑ _ : V, (2 : ℚ) :=
            Finset.sum_le_sum (fun v _ => by exact_mod_cast local_le_two_pent f hf.2 hr v)
          _ = 2 * (Fintype.card V : ℚ) := by simp [mul_comm]
      exact ((not_le_of_gt hAvg) hle).elim

/-- The exact floor reading holds at radius at most two whenever floor(mean)
is at most three, even with five-cycles and arbitrary variation in degrees. -/
theorem conjecture133_floor_three_radius_two (G : SimpleGraph V) (hc : G.Connected)
    (hr : radius G ≤ 2) (ha : ⌊averageLocal G⌋ ≤ 3) :
    ∃ k : ℕ, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · by_cases hSmall : ⌊averageLocal G⌋ ≤ 2
    · exact conjecture133_floor_le_two_or_four_cycle G hc (Or.inr hSmall)
    · have hA : 2 < averageLocal G := by
        have hh := Int.floor_le (averageLocal G)
        have h' : (3 : ℤ) ≤ ⌊averageLocal G⌋ := by omega
        have hr : (3 : ℚ) ≤ (⌊averageLocal G⌋ : ℚ) := by exact_mod_cast h'
        exact (show (2 : ℚ) < 3 by norm_num).trans_le (hr.trans hh)
      have h := exists_P5_of_local_avg_gt_two G hc h4 hA
      refine ⟨5,?_,h⟩
      simp only [catalogueRhs133,if_pos h4,pow_one]
      omega
  · exact conjecture133_floor_le_two_or_four_cycle G hc (Or.inl h4)

/-- The stronger unrounded inequality holds at radius at most two as long
as the local independence mean is at most three. -/
theorem conjecture133_real_three_radius_two (G : SimpleGraph V) (hc : G.Connected)
    (hr : radius G ≤ 2) (ha : averageLocal G ≤ 3) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · by_cases hSmall : averageLocal G ≤ 2
    · exact conjecture133_low_average_or_four_cycle G hc (Or.inr hSmall)
    · have h := exists_P5_of_local_avg_gt_two G hc h4 (lt_of_not_ge hSmall)
      refine ⟨5,?_,h⟩
      simp only [rhs133,if_pos h4,pow_one]
      have hr' : (radius G : ℚ) ≤ 2 := by exact_mod_cast hr
      change (radius G : ℚ) + averageLocal G ≤ 5
      linarith
  · exact conjecture133_low_average_or_four_cycle G hc (Or.inl h4)

/-- If no five-cycle exists, floor #133 holds at radius two, and also at
radius three whenever the floored average is even. No bipartiteness or
regularity is assumed. -/
theorem conjecture133_no_five_small_radius (G : SimpleGraph V) (hc : G.Connected)
    (h5 : NoSimpleFive133 G)
    (hr : radius G ≤ 2 ∨ (radius G ≤ 3 ∧ ⌊averageLocal G⌋ % 2 = 0)) :
    ∃ k : ℕ, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · by_cases ha : ⌊averageLocal G⌋ ≤ 2
    · exact conjecture133_floor_le_two_or_four_cycle G hc (Or.inr ha)
    · letI := hc.nonempty
      let d := (⌊averageLocal G⌋ / 2).toNat
      have hdn : (d : ℤ) = ⌊averageLocal G⌋ / 2 := by
        exact Int.toNat_of_nonneg (by omega)
      have hdl : 2*(d : ℤ) ≤ ⌊averageLocal G⌋ := by omega
      have hAvg : ((2*d : ℕ) : ℚ) ≤ averageLocal G := by
        have hM : ((2*d : ℕ) : ℚ) ≤ (⌊averageLocal G⌋ : ℚ) := by
          exact_mod_cast hdl
        exact hM.trans (Int.floor_le _)
      have hd : 1 ≤ d := by omega
      refine ⟨2*d+3,?_,no_four_five_path_of_local_density G h4 h5 d hd
        (nat_density_of_le_average G (2*d) hAvg)⟩
      simp only [catalogueRhs133,if_pos h4,pow_one]
      rcases hr with h | ⟨h₁,h₂⟩ <;> omega
  · exact conjecture133_floor_le_two_or_four_cycle G hc (Or.inl h4)

#print axioms conjecture133_floor_three_radius_two
#print axioms conjecture133_real_three_radius_two
#print axioms conjecture133_no_five_small_radius

end Graffiti133Revisit
