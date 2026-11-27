import FinalEight133
import ThirdBand133
import HexFlattened133

namespace Graffiti133FinalEight
open SimpleGraph Graffiti133 Graffiti133Revisit
variable {V : Type*} [Fintype V]

theorem conjecture133_full_floor_four (G : SimpleGraph V) (hc : G.Connected)
    (ha : ⌊averageLocal G⌋ ≤ 4) :
    ∃ k : ℕ, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · by_cases small : ⌊averageLocal G⌋ ≤ 3
    · exact conjecture133_full_floor_three G hc small
    · by_cases far : ⌊averageLocal G⌋ < (radius G : ℤ)
      · exact conjecture133_high_radius G hc far
      · letI := hc.nonempty
        have low : (4 : ℚ) ≤ averageLocal G := by
          exact Int.le_floor.mp (show (4 : ℤ) ≤ ⌊averageLocal G⌋ by omega)
        have dense := nat_density_of_le_average G 3 (show (3 : ℚ) ≤ averageLocal G from (by norm_num : (3 : ℚ) ≤ 4).trans low)
        rcases induced_eight_or_radius_three G hc h4 dense with ⟨p,hp⟩|hr
        · refine ⟨8,?_,p,hp⟩
          simp only [catalogueRhs133,if_pos h4,pow_one]
          omega
        · exact conjecture133_floor_four_radius_three G hc hr ha
  · exact conjecture133_floor_le_two_or_four_cycle G hc (Or.inl h4)

theorem conjecture133_full_real_four (G : SimpleGraph V) (hc : G.Connected)
    (ha : averageLocal G ≤ 4) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · by_cases small : averageLocal G ≤ 3
    · exact conjecture133_real_full_three G hc small
    · by_cases far : 5 ≤ radius G
      · apply conjecture133_unrounded_high_radius G hc
        have hr : (5 : ℚ) ≤ radius G := by exact_mod_cast far
        linarith
      · letI := hc.nonempty
        have dense := nat_density_of_le_average G 3 (le_of_lt (lt_of_not_ge small))
        rcases induced_eight_or_radius_three G hc h4 dense with ⟨p,hp⟩|hr
        · refine ⟨8,?_,p,hp⟩
          simp only [rhs133,if_pos h4,pow_one]
          have r : (radius G : ℚ) ≤ 4 := by exact_mod_cast (show radius G ≤ 4 by omega)
          change (radius G : ℚ) + averageLocal G ≤ 8
          exact (add_le_add r ha).trans (by norm_num)
        · exact conjecture133_real_four_radius_three G hc hr ha
  · exact conjecture133_low_average_or_four_cycle G hc (Or.inl h4)

#print axioms conjecture133_full_real_four
#print axioms conjecture133_full_floor_four
end Graffiti133FinalEight
