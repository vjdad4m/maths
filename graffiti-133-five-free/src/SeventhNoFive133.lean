import Remaining133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V]

/-- Four- and five-cycle-free graphs with at least four mean local
independence have an induced path of order seven, without regularity. -/
theorem P7_of_local_mean_four_without_five (G : SimpleGraph V) [Nonempty V]
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G) (ha : 4 ≤ averageLocal G) :
    ∃ f : Fin 7 → V, InducedPath G f := by
  classical
  exact no_four_five_path_of_local_density G h4 h5 2 (by decide)
    (nat_density_of_le_average G 4 ha)

/-- Radius at most two and exact local mean at most five in the whole
ordinary-five-cycle-free lane. -/
theorem conjecture133_real_five_radius_two_no_five (G : SimpleGraph V) (hc : G.Connected)
    (hr : radius G ≤ 2) (ha : averageLocal G ≤ 5) (h5 : NoSimpleFive133 G) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  letI := hc.nonempty
  by_cases h4 : FourCycleFree G
  · by_cases hSmall : averageLocal G ≤ 4
    · exact conjecture133_real_four_radius_two G hc hr hSmall
    · refine ⟨7,?_ ,P7_of_local_mean_four_without_five G h4 h5
        (le_of_lt (lt_of_not_ge hSmall))⟩
      simp only [rhs133,if_pos h4,pow_one]
      change (radius G : ℚ) + averageLocal G ≤ 7
      have hh : (radius G : ℚ) ≤ 2 := by exact_mod_cast hr
      linarith
  · exact conjecture133_low_average_or_four_cycle G hc (Or.inl h4)

#print axioms P7_of_local_mean_four_without_five
#print axioms conjecture133_real_five_radius_two_no_five

end Graffiti133Revisit
