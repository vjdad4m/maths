import ThirdBand133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133 Graffiti133RevisitSix Graffiti133Pentagon Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V]

private theorem pent_card_budget {G : SimpleGraph V} (F : PentagonFrame G) :
    5 + F.allSingles.card ≤ Fintype.card V := by
  classical
  let C := (Finset.univ : Finset (Fin 5)).image F.c
  have c : C.card = 5 := by
    dsimp [C]
    rw [Finset.card_image_of_injective _ F.inj]
    simp
  have dis : Disjoint C F.allSingles := by
    rw [Finset.disjoint_left]
    intro x hx hs
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hx
    obtain ⟨j,hj⟩ : ∃ j, One G F.c x j := (Finset.mem_filter.mp hs).2
    exact hj.1 i he.symm
  have t := Finset.card_le_card (Finset.subset_univ (C ∪ F.allSingles))
  rwa [Finset.card_union_of_disjoint dis,c,Finset.card_univ] at t

/-- In a connected C4-free graph, local mean strictly above three forces P6. -/
theorem P6_of_local_mean_gt_three (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G) (ha : 3 < averageLocal G) :
    ∃ f : Fin 6 → V, InducedPath G f := by
  classical
  letI := hc.nonempty
  by_cases h5 : NoSimpleFive133 G
  · exact P6_of_local_mean_three G h4 h5 (le_of_lt ha)
  · apply Classical.byContradiction
    intro no
    obtain ⟨F⟩ := make_frame hc h4 h5 no
    have hSum := F.total_budget
    have hH := F.high_eq_five (le_of_lt ha)
    have size := pent_card_budget F
    have hb : (∑ x, localIndependence G x) ≤ 3 * Fintype.card V := by omega
    unfold averageLocal at ha
    have npos : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α:=V)
    have hBan := (lt_div_iff₀ npos).mp ha
    rw [← Nat.cast_sum] at hBan
    have hh : ((3 * Fintype.card V : ℕ) : ℚ) < ((∑ x, localIndependence G x : ℕ) : ℚ) := by
      simpa using hBan
    have : 3 * Fintype.card V < ∑ x, localIndependence G x := by exact_mod_cast hh
    omega

/-- Radius at most two, and unrounded local mean at most four. Five-cycles
are allowed, without any degree regularity or bipartiteness assumption. -/
theorem conjecture133_real_four_radius_two (G : SimpleGraph V) (hc : G.Connected)
    (hr : radius G ≤ 2) (ha : averageLocal G ≤ 4) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · by_cases hs : averageLocal G ≤ 3
    · exact conjecture133_real_three_radius_two G hc hr hs
    · have hp := P6_of_local_mean_gt_three G hc h4 (lt_of_not_ge hs)
      refine ⟨6,?_,hp⟩
      simp only [rhs133,if_pos h4,pow_one]
      have hr' : (radius G : ℚ) ≤ 2 := by exact_mod_cast hr
      change (radius G : ℚ) + averageLocal G ≤ 6
      linarith
  · exact conjecture133_low_average_or_four_cycle G hc (Or.inl h4)

/-- Radius at most two and floored local mean at most four. -/
theorem conjecture133_floor_four_radius_two (G : SimpleGraph V) (hc : G.Connected)
    (hr : radius G ≤ 2) (ha : ⌊averageLocal G⌋ ≤ 4) :
    ∃ k : ℕ, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · by_cases hs : ⌊averageLocal G⌋ ≤ 3
    · exact conjecture133_floor_three_radius_two G hc hr hs
    · have ht : (4 : ℤ) ≤ ⌊averageLocal G⌋ := by omega
      have hq : (4 : ℚ) ≤ (⌊averageLocal G⌋ : ℚ) := by exact_mod_cast ht
      have hgt := (show (3 : ℚ) < 4 by norm_num).trans_le (hq.trans (Int.floor_le _))
      refine ⟨6,?_ ,P6_of_local_mean_gt_three G hc h4 hgt⟩
      simp only [catalogueRhs133,if_pos h4,pow_one]
      omega
  · exact conjecture133_floor_le_two_or_four_cycle G hc (Or.inl h4)

#print axioms P6_of_local_mean_gt_three
#print axioms conjecture133_real_four_radius_two
#print axioms conjecture133_floor_four_radius_two

end Graffiti133Revisit
