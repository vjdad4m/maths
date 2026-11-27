import HexFlattened133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133
variable {V : Type*} [Fintype V]

/-- Exact first unresolved band of the real reading after the seven-path
theorem: if a counterexample has mean at most 4, it is at radius 4 and all
distances are at most 6. No hypothesis about ordinary five-cycles is used. -/
theorem after_P7_real_constraints (G : SimpleGraph V) (hc : G.Connected)
    (bad : ¬ ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f) :
    FourCycleFree G ∧ 3 < averageLocal G ∧
      7 < (radius G : ℚ)+averageLocal G ∧
      (radius G ≤ 2 → 5 < averageLocal G) ∧
      (radius G ≤ 3 → 4 < averageLocal G) ∧
      (averageLocal G ≤ 4 → radius G=4 ∧ ∀ u v, G.dist u v ≤ 6) := by
  obtain ⟨h4,hgt,_,hr,hDist⟩ := remaining_real_constraints G hc bad
  refine ⟨h4,hgt,?_,?_,?_,?_⟩
  · apply lt_of_not_ge
    intro h
    exact bad ⟨7,by simpa only [rhs133,if_pos h4,pow_one] using h,
      P7_of_strict_mean_three G hc h4 hgt⟩
  · intro r
    exact lt_of_not_ge (fun ha => bad (conjecture133_real_five_radius_two G hc r ha))
  · intro r
    exact lt_of_not_ge (fun ha => bad (conjecture133_real_four_radius_three G hc r ha))
  · intro a
    have rLo : 4 ≤ radius G := by
      by_contra! no
      exact bad (conjecture133_real_four_radius_three G hc (by omega) a)
    have rHi : radius G ≤ 4 := by
      have h : (radius G : ℚ) < 5 := by linarith
      have h' : radius G < 5 := by exact_mod_cast h
      omega
    have L := le_antisymm rHi rLo
    refine ⟨L,?_⟩
    intro u v
    have hd := hDist u v
    have e : (radius G : ℚ) = 4 := by exact_mod_cast L
    have hZ : (G.dist u v : ℚ) < 7 := by linarith
    have hN : G.dist u v < 7 := by exact_mod_cast hZ
    omega

/-- Under the floor reading, all hypothetical counterexamples with
floor(mean) = 4 are now at radius 4. -/
theorem after_P7_floor_constraints (G : SimpleGraph V) (hc : G.Connected)
    (bad : ¬ ∃ k : ℕ, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f) :
    FourCycleFree G ∧ 4 ≤ ⌊averageLocal G⌋ ∧
      (radius G ≤ 2 → 6 ≤ ⌊averageLocal G⌋) ∧
      (radius G ≤ 3 → 5 ≤ ⌊averageLocal G⌋) ∧
      ((radius G : ℤ)+⌊averageLocal G⌋ ≥ 8) ∧
      (⌊averageLocal G⌋=4 → radius G=4) := by
  obtain ⟨h4,hM,_,hR,_,_⟩ := remaining_floor_constraints G hc bad
  have ha : (3:ℚ)<averageLocal G := by
    have h : (4:ℚ) ≤ (⌊averageLocal G⌋:ℚ) := by exact_mod_cast hM
    have hh := h.trans (Int.floor_le (averageLocal G))
    linarith
  have hlow : 8 ≤ (radius G : ℤ)+⌊averageLocal G⌋ := by
    by_contra! h
    apply bad
    refine ⟨7,?_,P7_of_strict_mean_three G hc h4 ha⟩
    simp only [catalogueRhs133,if_pos h4,pow_one]
    omega
  refine ⟨h4,hM,?_,?_,hlow,?_⟩
  · intro hr
    by_contra! h
    exact bad (conjecture133_floor_five_radius_two G hc hr (by omega))
  · intro hr
    by_contra! h
    exact bad (conjecture133_floor_four_radius_three G hc hr (by omega))
  · intro h
    omega

#print axioms after_P7_real_constraints
#print axioms after_P7_floor_constraints
end Graffiti133Revisit
