import FinalEight133
import FirstBandFour133
import HexFlattened133

namespace Graffiti133FiveBand
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133Camby Graffiti133NoFive
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def Full (G : SimpleGraph V) : Prop :=
  ∃ k : Nat, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f

theorem residual_real_five (hc : G.Connected) (upper : averageLocal G ≤ 5)
    (bad : ¬ Full G) :
    FourCycleFree G ∧ 4 < averageLocal G ∧
      ((radius G=3 ∧ NoPath G 8 ∧ ∀ x y,G.dist x y≤6) ∨
       (radius G=4 ∧ NoPath G 9 ∧ ∀ x y,G.dist x y≤7) ∨
       (radius G=5 ∧ NoPath G 10 ∧ ∀ x y,G.dist x y≤8)) := by
  classical
  have h4 : FourCycleFree G := by
    by_contra! no
    exact bad (conjecture133_low_average_or_four_cycle G hc (Or.inl no))
  have low : 4 < averageLocal G := by
    by_contra! no
    exact bad (Graffiti133FinalEight.conjecture133_full_real_four G hc no)
  have hr3 : 3≤radius G := by
    by_contra! no
    exact bad (conjecture133_real_five_radius_two G hc (by omega) upper)
  have hr5 : radius G≤5 := by
    by_contra! no
    have rn : (6 : ℚ)≤radius G := by exact_mod_cast (show 6≤radius G by omega)
    exact bad (conjecture133_unrounded_high_radius G hc (by linarith))
  have no (k : Nat) (bound : radius G+5≤k) : NoPath G k := by
    rintro ⟨f,hf⟩
    apply bad
    refine ⟨k,?_,f,hf⟩
    simp only [rhs133,if_pos h4,pow_one]
    have bq : (radius G : ℚ)+5≤k := by exact_mod_cast bound
    exact (add_le_add_left upper _).trans bq
  have near (k : Nat) (hn : NoPath G k) (x y : V) :
      G.dist x y + 1 < k := by
    by_contra! far
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x y
    obtain ⟨f,hf,hAdj⟩ := geodesic_induced hc p hp
    exact hn (trim_path (by omega) ⟨hf,hAdj⟩)
  refine ⟨h4,low,?_⟩
  rcases (show radius G=3 ∨ radius G=4 ∨ radius G=5 by omega) with r|r|r
  · exact Or.inl ⟨r,no 8 (by omega),fun x y => by have hh := near 8 (no 8 (by omega)) x y; omega⟩
  · exact Or.inr (Or.inl ⟨r,no 9 (by omega),fun x y => by have hh := near 9 (no 9 (by omega)) x y; omega⟩)
  · exact Or.inr (Or.inr ⟨r,no 10 (by omega),fun x y => by have hh := near 10 (no 10 (by omega)) x y; omega⟩)

theorem residual_real_five_iff (hc : G.Connected) (upper : averageLocal G ≤ 5) :
    ¬ Full G ↔ FourCycleFree G ∧ 4 < averageLocal G ∧
      ((radius G=3 ∧ NoPath G 8 ∧ ∀ x y,G.dist x y≤6) ∨
       (radius G=4 ∧ NoPath G 9 ∧ ∀ x y,G.dist x y≤7) ∨
       (radius G=5 ∧ NoPath G 10 ∧ ∀ x y,G.dist x y≤8)) := by
  classical
  refine ⟨residual_real_five hc upper,?_⟩
  rintro ⟨h4,low,hr⟩ ⟨k,hk,f,hf⟩
  have hlarge : radius G+5≤k := by
    by_contra! h
    have u : (k : ℚ) ≤ (radius G : ℚ)+4 := by
      exact_mod_cast (show k≤radius G+4 by omega)
    simp only [rhs133,if_pos h4,pow_one] at hk
    exact (not_lt_of_ge (hk.trans u)) (add_lt_add_left low _)
  rcases hr with ⟨r,no,_⟩|⟨r,no,_⟩|⟨r,no,_⟩
  · exact no (trim_path (by omega) hf)
  · exact no (trim_path (by omega) hf)
  · exact no (trim_path (by omega) hf)

#print axioms residual_real_five_iff
#print axioms residual_real_five
end Graffiti133FiveBand
