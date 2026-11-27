import PentagonBudget133

namespace Graffiti133Revisit
open SimpleGraph Graffiti133 Graffiti133RevisitSix Graffiti133Pentagon Finset
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private lemma radius_le_ecc (G : SimpleGraph V) (u : V) :
    radius G ≤ Finset.univ.sup (G.dist u) := by
  classical
  unfold radius
  have hm : Finset.univ.sup (G.dist u) ∈
      Finset.univ.image (fun u => Finset.univ.sup (G.dist u)) :=
    Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  have hl := Finset.min_le hm
  cases hmin : (Finset.univ.image (fun u => Finset.univ.sup (G.dist u))).min with
  | top => exact Nat.zero_le _
  | coe d => simpa [hmin] using hl

private theorem short_walk {a b c : V} (h₁ : G.Adj a b) (h₂ : G.Adj b c) :
    G.dist a c ≤ 2 := by
  simpa using G.dist_le (Walk.cons h₁ (Walk.cons h₂ .nil))

private lemma near_cycle_zero : ∀ i : Fin 5,
    i = 0 ∨ pent 0 i ∨ (∃ j, pent 0 j ∧ pent j i) := by decide

private lemma near_single_zero : ∀ i : Fin 5,
    i = 0 ∨ pent 0 i ∨ i = 0+2 ∨ i = 0+3 := by decide

/-- At local independence mean at least three, the P6-free pentagon frame
is a Petersen configuration. In particular its radius is at most two. -/
theorem radius_of_dense_P6_free_pentagon (F : PentagonFrame G) (h : 3 ≤ averageLocal G) :
    radius G ≤ 2 := by
  classical
  have hi (i : Fin 5) : ∃ s, One G F.c s i ∧ 3 ≤ localIndependence G s := by
    obtain ⟨s,hs,h2⟩ := F.high_at_every_site h i
    exact ⟨s,hs,(Finset.mem_filter.mp h2).2⟩
  have unique (i : Fin 5) :
      ∃ s, One G F.c s i ∧ 3 ≤ localIndependence G s ∧
        ∀ t, One G F.c t i → t = s := by
    obtain ⟨s,hs,h3⟩ := hi i
    obtain ⟨w,hw,hw3⟩ := hi (i+3)
    obtain ⟨⟨q,hq,e,uq⟩,_⟩ := F.high_unique_opposite hw hw3
    have eq : (i+3)+2=i := (by decide : ∀ i : Fin 5, (i+3)+2=i) i
    rw [eq] at uq
    have es := uq s hs
    exact ⟨s,hs,h3,fun t ht => (uq t ht).trans es.symm⟩
  let s (i : Fin 5) := Classical.choose (unique i)
  have sig (i : Fin 5) : One G F.c (s i) i ∧ 3 ≤ localIndependence G (s i) ∧
      ∀ t, One G F.c t i → t = s i := Classical.choose_spec (unique i)
  have adj0 : G.Adj (F.c 0) (s 0) := ((sig 0).1.2 0 |>.mpr rfl).symm
  obtain ⟨a,b,ha,hb,ea,eb⟩ := F.high_opposite (sig 0).1 (sig 0).2.1
  have hA : G.Adj (s 0) (s (0+2)) := (sig (0+2)).2.2 a ha ▸ ea
  have hB : G.Adj (s 0) (s (0+3)) := (sig (0+3)).2.2 b hb ▸ eb
  apply (radius_le_ecc G (F.c 0)).trans
  apply Finset.sup_le_iff.mpr
  intro x _
  by_cases out : Outside F.c x
  · have hx := F.all_outside_singles h x out
    obtain ⟨i,ht⟩ : ∃ i, One G F.c x i := (Finset.mem_filter.mp hx).2
    have eq := (sig i).2.2 x ht
    rcases near_single_zero i with hi0 | cyc | hi2 | hi3
    · have hh : G.Adj (F.c 0) x := ((ht.2 0).mpr hi0.symm).symm
      rw [dist_eq_one_iff_adj.mpr hh]
      decide
    · exact short_walk ((F.adj _ _).mpr cyc) ((ht.2 i).mpr rfl).symm
    · rw [eq,hi2]
      exact short_walk adj0 hA
    · rw [eq,hi3]
      exact short_walk adj0 hB
  · obtain ⟨i,hi⟩ : ∃ i, x = F.c i := by
      apply Classical.byContradiction
      intro no
      exact out (fun j e => no ⟨j,e⟩)
    rw [hi]
    rcases near_cycle_zero i with eq | adj | ⟨j,e1,e2⟩
    · simp [eq,SimpleGraph.dist_self]
    · rw [dist_eq_one_iff_adj.mpr ((F.adj _ _).mpr adj)]
      decide
    · exact short_walk ((F.adj _ _).mpr e1) ((F.adj _ _).mpr e2)

/-- Mean at least three in a connected C4-free graph forces an induced
six-vertex path unless the graph has radius at most two. -/
theorem P6_or_radius_two (G : SimpleGraph V) (hc : G.Connected) (h4 : FourCycleFree G)
    (ha : 3 ≤ averageLocal G) :
    (∃ f : Fin 6 → V, InducedPath G f) ∨ radius G ≤ 2 := by
  classical
  letI := hc.nonempty
  by_cases h5 : NoSimpleFive133 G
  · exact Or.inl (P6_of_local_mean_three G h4 h5 ha)
  · by_cases hp : ∃ p : Fin 6 → V, InducedPath G p
    · exact Or.inl hp
    · obtain ⟨F⟩ := make_frame hc h4 h5 hp
      exact Or.inr (radius_of_dense_P6_free_pentagon F ha)

/-- The exact rounded catalogue conjecture when the floored local average
is at most three, with no radius, cycle or regularity restrictions. -/
theorem conjecture133_full_floor_three (G : SimpleGraph V) (hc : G.Connected)
    (ha : ⌊averageLocal G⌋ ≤ 3) :
    ∃ k : ℕ, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · by_cases hl : ⌊averageLocal G⌋ ≤ 2
    · exact conjecture133_floor_le_two_or_four_cycle G hc (Or.inr hl)
    · by_cases hr : radius G ≤ 3
      · have hAvg : 3 ≤ averageLocal G := by
          have ha' : (3 : ℤ) ≤ ⌊averageLocal G⌋ := by omega
          exact (show (3 : ℚ) ≤ (⌊averageLocal G⌋ : ℚ) by exact_mod_cast ha').trans (Int.floor_le _)
        rcases P6_or_radius_two G hc h4 hAvg with ⟨p,hp⟩ | hr2
        · refine ⟨6,?_,p,hp⟩
          simp only [catalogueRhs133,if_pos h4,pow_one]
          omega
        · exact conjecture133_floor_three_radius_two G hc hr2 ha
      · exact conjecture133_high_radius G hc (by omega)
  · exact conjecture133_floor_le_two_or_four_cycle G hc (Or.inl h4)

#print axioms P6_or_radius_two
#print axioms conjecture133_full_floor_three

end Graffiti133Revisit
