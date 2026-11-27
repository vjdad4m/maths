import UnroundedBand133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133

variable {V : Type*} [Fintype V]

/-- Necessary conditions for an exact rounded counterexample after the
low-mean and small-radius closures. -/
theorem remaining_floor_constraints (G : SimpleGraph V) (hc : G.Connected)
    (bad : ¬ ∃ k : ℕ, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f) :
    FourCycleFree G ∧ 4 ≤ ⌊averageLocal G⌋ ∧
      2 ≤ radius G ∧ (radius G : ℤ) ≤ ⌊averageLocal G⌋ ∧
      (radius G ≤ 2 → 5 ≤ ⌊averageLocal G⌋) ∧
      (⌊averageLocal G⌋ = 4 →
        (radius G = 3 ∧ ¬ NoSimpleFive133 G) ∨ radius G = 4) := by
  classical
  obtain ⟨h4,_,h2,hr,_⟩ := catalogue_counterexample_constraints G hc bad
  have h := Int.lt_of_not_ge (fun h => bad (conjecture133_full_floor_three G hc h))
  have small (hr : radius G ≤ 2) : 5 ≤ ⌊averageLocal G⌋ := by
    have h := Int.lt_of_not_ge (fun h => bad (conjecture133_floor_four_radius_two G hc hr h))
    omega
  refine ⟨h4,by omega,h2,hr,small,?_⟩
  intro h4A
  have hrLo : 3 ≤ radius G := by
    by_contra! h
    have := small (by omega)
    omega
  have hrHi : radius G ≤ 4 := by omega
  by_cases hr4 : radius G = 4
  · exact Or.inr hr4
  · have hr3 : radius G = 3 := by omega
    refine Or.inl ⟨hr3,?_⟩
    intro h5
    exact bad (conjecture133_no_five_small_radius G hc h5 (Or.inr ⟨by omega,by omega⟩))

/-- Necessary conditions for an unrounded counterexample. -/
theorem remaining_real_constraints (G : SimpleGraph V) (hc : G.Connected)
    (bad : ¬ ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f) :
    FourCycleFree G ∧ 3 < averageLocal G ∧
      (radius G ≤ 2 → 4 < averageLocal G) ∧ (radius G : ℚ) < averageLocal G+1 ∧
      ∀ u v, (G.dist u v : ℚ) + 1 < (radius G : ℚ) + averageLocal G := by
  classical
  have h4 : FourCycleFree G := by
    apply Classical.byContradiction
    intro h
    exact bad (conjecture133_low_average_or_four_cycle G hc (Or.inl h))
  refine ⟨h4,lt_of_not_ge (fun h => bad (conjecture133_real_full_three G hc h)),
    fun hr => lt_of_not_ge (fun h => bad (conjecture133_real_four_radius_two G hc hr h)),
    lt_of_not_ge (fun hr => bad (conjecture133_unrounded_high_radius G hc hr)),?_⟩
  intro u v
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist u v
  apply lt_of_not_ge
  intro h
  apply bad
  refine ⟨p.length+1,?_ ,(geodesic_induced hc p hp)⟩
  simpa only [rhs133,if_pos h4,pow_one,Nat.cast_add,Nat.cast_one,hp] using h

#print axioms remaining_floor_constraints
#print axioms remaining_real_constraints

end Graffiti133Revisit
