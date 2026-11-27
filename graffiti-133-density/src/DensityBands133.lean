import SixCycle133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133 Graffiti133RevisitSix

variable {V : Type*} [Fintype V]

/-- For floor(mean) at most three, the floor reading is verified unless
the radius is exactly three and the graph contains a five-cycle. -/
theorem floor_at_most_three_except_five_radius_three (G : SimpleGraph V)
    (hc : G.Connected) (ha : ⌊averageLocal G⌋ ≤ 3)
    (h : NoSimpleFive133 G ∨ radius G ≠ 3) :
    ∃ k : ℕ, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · by_cases hs : ⌊averageLocal G⌋ ≤ 2
    · exact conjecture133_floor_le_two_or_four_cycle G hc (.inr hs)
    · by_cases hr : radius G ≤ 2
      · exact conjecture133_floor_three_radius_two G hc hr ha
      · by_cases rlarge : 4 ≤ radius G
        · exact conjecture133_high_radius G hc (by omega)
        · have eq : radius G = 3 := by omega
          have hm₀ : (3 : ℤ) ≤ ⌊averageLocal G⌋ := by omega
          have hm : (3 : ℚ) ≤ averageLocal G := by
            exact (by exact_mod_cast hm₀ : (3 : ℚ) ≤ (⌊averageLocal G⌋ : ℚ)).trans (Int.floor_le _)
          letI := hc.nonempty
          have hp := P6_of_local_mean_three G h4 (h.resolve_right (by simp [eq])) hm
          refine ⟨6,?_,hp⟩
          simp only [catalogueRhs133,if_pos h4,pow_one,eq]
          omega
  · exact conjecture133_floor_le_two_or_four_cycle G hc (.inl h4)

#print axioms floor_at_most_three_except_five_radius_three
end Graffiti133Revisit
