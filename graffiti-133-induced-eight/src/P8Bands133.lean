import P8NoFive133
import AfterSeventh133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133 Graffiti133Eighth
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V]

private theorem real_eight (G : SimpleGraph V) (hc : G.Connected)
    (h5 : NoSimpleFive133 G) (low : 4 ≤ averageLocal G)
    (high : (radius G : ℚ)+averageLocal G ≤ 8) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · letI := hc.nonempty
    exact ⟨8,by simpa only [rhs133,if_pos h4,pow_one] using high,
      P8_of_local_mean_four_without_five G h4 h5 low⟩
  · exact conjecture133_low_average_or_four_cycle G hc (Or.inl h4)

private theorem floor_eight (G : SimpleGraph V) (hc : G.Connected)
    (h5 : NoSimpleFive133 G) (low : 4 ≤ ⌊averageLocal G⌋)
    (high : (radius G : ℤ)+⌊averageLocal G⌋ ≤ 8) :
    ∃ k : ℕ, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · letI := hc.nonempty
    have a : (4:ℚ) ≤ (⌊averageLocal G⌋:ℚ) := by exact_mod_cast low
    exact ⟨8,by simpa only [catalogueRhs133,if_pos h4,pow_one] using high,
      P8_of_local_mean_four_without_five G h4 h5 (a.trans (Int.floor_le _))⟩
  · exact conjecture133_floor_le_two_or_four_cycle G hc (Or.inl h4)

/-- On the exact real interpretation, C5-free graphs now have radius-three
mean≤5 and radius-two mean≤6, as well as the radius-four mean=4 boundary. -/
theorem conjecture133_real_eight_no_five (G : SimpleGraph V) (hc : G.Connected)
    (h5 : NoSimpleFive133 G)
    (band : (radius G ≤ 3 ∧ averageLocal G ≤ 5) ∨
      (radius G ≤ 2 ∧ averageLocal G ≤ 6) ∨ (radius G ≤ 4 ∧ averageLocal G = 4)) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  rcases band with ⟨hr,ha⟩ | ⟨hr,ha⟩ | ⟨hr,ha⟩
  · by_cases small : averageLocal G ≤ 4
    · exact conjecture133_real_four_radius_three G hc hr small
    · have hR : (radius G : ℚ) ≤ 3 := by exact_mod_cast hr
      exact real_eight G hc h5 (lt_of_not_ge small).le (by linarith)
  · by_cases small : averageLocal G ≤ 5
    · exact conjecture133_real_five_radius_two G hc hr small
    · have hR : (radius G : ℚ) ≤ 2 := by exact_mod_cast hr
      exact real_eight G hc h5 (by linarith) (by linarith)
  · have hR : (radius G : ℚ) ≤ 4 := by exact_mod_cast hr
    exact real_eight G hc h5 (by linarith) (by linarith)

/-- C5-free floor-reading bands. In particular, the entire lowest unresolved
floor(mean)=4 band is settled in the absence of ordinary five-cycles. -/
theorem conjecture133_floor_eight_no_five (G : SimpleGraph V) (hc : G.Connected)
    (h5 : NoSimpleFive133 G)
    (band : (radius G ≤ 4 ∧ ⌊averageLocal G⌋ ≤ 4) ∨
      (radius G ≤ 3 ∧ ⌊averageLocal G⌋ ≤ 5) ∨ (radius G ≤ 2 ∧ ⌊averageLocal G⌋ ≤ 6)) :
    ∃ k : ℕ, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  rcases band with ⟨hr,ha⟩ | ⟨hr,ha⟩ | ⟨hr,ha⟩
  · by_cases small : ⌊averageLocal G⌋ ≤ 3
    · exact conjecture133_full_floor_three G hc small
    · exact floor_eight G hc h5 (by omega) (by omega)
  · by_cases small : ⌊averageLocal G⌋ ≤ 4
    · exact conjecture133_floor_four_radius_three G hc hr small
    · exact floor_eight G hc h5 (by omega) (by omega)
  · by_cases small : ⌊averageLocal G⌋ ≤ 5
    · exact conjecture133_floor_five_radius_two G hc hr small
    · exact floor_eight G hc h5 (by omega) (by omega)

#print axioms conjecture133_real_eight_no_five
#print axioms conjecture133_floor_eight_no_five
end Graffiti133Revisit
