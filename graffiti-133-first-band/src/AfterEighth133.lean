import P8Bands133
import P8AnchorRadius133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133 Graffiti133Eighth
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- In the first unresolved real band, the minimum-local-two regime is
exactly a self-centered order-four metric unless P8 is already present. -/
theorem after_P8_first_real_min_two (G : SimpleGraph V) (hc : G.Connected)
    (ha : averageLocal G ≤ 4) (hm : ∀ v, 2 ≤ localIndependence G v)
    (bad : ¬ ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f) :
    FourCycleFree G ∧ 3 < averageLocal G ∧ radius G = 4 ∧
      (∀ u v, G.dist u v ≤ 4) ∧
      (NoSimpleFive133 G → (averageLocal G < 4 ∧
        ∀ f : Fin 7 → V, InducedPath G f → localIndependence G (f 0) ≤ 2)) := by
  classical
  obtain ⟨h4,avg,_,_,_,hband⟩ := after_P7_real_constraints G hc bad
  obtain ⟨hr,_⟩ := hband ha
  have no8 : ¬∃ f : Fin 8 → V, InducedPath G f := by
    intro h
    apply bad
    refine ⟨8,?_,h⟩
    simp only [rhs133,if_pos h4,pow_one,hr,Nat.cast_ofNat]
    linarith
  refine ⟨h4,avg,hr,?_,?_⟩
  · intro u v
    by_contra! h
    obtain ⟨f,hf⟩ := diameter_induced_path_bound G hc h4 2 (G.dist u v) hm ⟨u,v,rfl⟩
    have hle : 8 ≤ G.dist u v+1+min (2*(2/2)) (G.dist u v-2) := by
      have hp : 2 ≤ G.dist u v-2 := by omega
      have hm : min (2*(2/2)) (G.dist u v-2) = 2 := by
        change min 2 (G.dist u v-2) = 2
        exact min_eq_left hp
      rw [hm]
      omega
    exact no8 (trim_path hle hf)
  · intro h5
    have low : averageLocal G < 4 := by
      by_contra! j
      exact bad (conjecture133_real_eight_no_five G hc h5
        (Or.inr (Or.inr ⟨hr.le,le_antisymm ha j⟩)))
    refine ⟨low,?_⟩
    intro f hf
    by_contra! h
    rcases P8_or_radius_three_of_high_P7_end hc h4 h5 hf (by omega) with e | e
    · exact no8 e
    · omega

#print axioms after_P8_first_real_min_two
end Graffiti133Revisit
