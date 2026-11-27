import NoFivePeel133

namespace Graffiti133NoFive
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133RevisitSix Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem neighbor_pair (v : V) (hv : 2 ≤ localIndependence G v) :
    ∃ x y, x ≠ y ∧ G.Adj v x ∧ G.Adj v y ∧ ¬G.Adj x y := by
  classical
  have m (s : Finset V) : s ∈ localIndependentSets G v ↔
      (∀ x ∈ s, G.Adj v x) ∧ (∀ x ∈ s, ∀ y ∈ s, ¬G.Adj x y) := by
    simp [localIndependentSets, Finset.subset_iff]
  obtain ⟨A,hA,hM⟩ := Finset.exists_max_image (localIndependentSets G v) Finset.card
    ⟨∅, m _ |>.mpr (by simp)⟩
  have hi : localIndependence G v ≤ A.card := Finset.sup_le_iff.mpr hM
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  have hA := (m _).mp hA
  exact ⟨x,y,hxy,hA.1 x hx,hA.1 y hy,hA.2 x hx y hy⟩

private theorem side_neighbor (h4 : FourCycleFree G) {v s : V} (e : G.Adj v s)
    (hv : 2 ≤ localIndependence G v) :
    ∃ w, G.Adj v w ∧ w ≠ s ∧ ¬G.Adj w s := by
  obtain ⟨x,y,hne,hx,hy,hxy⟩ := neighbor_pair v hv
  by_cases ex : x = s
  · subst x
    exact ⟨y,hy,hne.symm,fun h => hxy h.symm⟩
  by_cases ey : y = s
  · subst y
    exact ⟨x,hx,hne,hxy⟩
  by_cases es : G.Adj x s
  · have no : ¬ G.Adj y s := by
      intro hb
      exact hne (h4 v s x y e.ne hx es.symm hy hb.symm)
    exact ⟨y,hy,ey,no⟩
  · exact ⟨x,hx,ex,es⟩

private theorem short_neighbor (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) {k : ℕ} (hk : 2 ≤ k) {f : Fin k → V}
    (p : InducedPath G f) (hv : 2 ≤ localIndependence G (f ⟨0,by omega⟩)) :
    ∃ w, (∀ i, w ≠ f i) ∧ G.Adj w (f ⟨0,by omega⟩) ∧
      (∀ i : Fin k, 0 < i.val → i.val ≤ 3 → ¬G.Adj w (f i)) := by
  let a : Fin k := ⟨0,by omega⟩
  let b : Fin k := ⟨1,by omega⟩
  have e : G.Adj (f a) (f b) := (p.2 a b (by change 0<1; decide)).mpr rfl
  obtain ⟨w,ew,hw,hwB⟩ := side_neighbor h4 e hv
  have off (i : Fin k) : w ≠ f i := by
    intro eq
    by_cases h : i = a
    · rw [h] at eq
      exact ew.ne eq.symm
    · have hlt : a < i := by
        change 0 < i.val
        apply Nat.pos_of_ne_zero
        intro he
        exact h (Fin.ext he)
      have j := (p.2 a i hlt).mp (eq ▸ ew)
      have eqi : i = b := Fin.ext j.symm
      exact hw (eq.trans (congrArg f eqi))
  have no2 {i : Fin k} (hi : i.val = 2) : ¬G.Adj w (f i) := by
    intro ewi
    have ebi := (p.2 b i (by change 1 < i.val; omega)).mpr (by change 2=i.val; omega)
    have eq := h4 (f a) (f i) w (f b) (fun h => by
      have hh := congrArg Fin.val (p.1 h)
      change 0 = i.val at hh
      omega) ew ewi.symm e ebi.symm
    exact hw eq
  refine ⟨w,off,ew.symm,?_⟩
  intro i hlo hhi
  rcases (show i.val = 1 ∨ i.val = 2 ∨ i.val = 3 by omega) with h | h | h
  · have ei : i = b := Fin.ext h
    exact ei ▸ hwB
  · exact no2 h
  · intro ewi
    let j : Fin k := ⟨2,by have := i.isLt; omega⟩
    have eBj := (p.2 b j (by change 1<2; decide)).mpr rfl
    have eji := (p.2 j i (by change 2 < i.val; omega)).mpr (by change 3=i.val; omega)
    have hIndices : [a,b,j,i].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true]
      constructor
      · intro neq
        rcases neq with q | q | q <;> have uu := congrArg Fin.val q <;> dsimp [a,b,j] at uu <;> omega
      · constructor
        · intro neq
          rcases neq with q | q <;> have uu := congrArg Fin.val q <;> dsimp [a,b,j] at uu <;> omega
        · refine ⟨?_, by trivial⟩
          intro q
          have hh := congrArg Fin.val q
          dsimp [j] at hh
          omega
    have hLists : [w,f a,f b,f j,f i].Nodup := by
      apply List.nodup_cons.mpr
      refine ⟨by simp [off],?_⟩
      simpa using hIndices.map p.1
    exact h5 _ _ _ _ _ hLists ew.symm e eBj eji ewi.symm

private theorem core_P7 (hc : G.Connected) (h4 : FourCycleFree G)
    (h5 : NoSimpleFive133 G) (hl : ∀ v, 2 ≤ localIndependence G v)
    (hD : 3*Fintype.card V ≤ (∑ x, localIndependence G x)) :
    ∃ p : Fin 7 → V, InducedPath G p := by
  classical
  letI := hc.nonempty
  apply Classical.byContradiction
  intro no
  have ha : 3 ≤ averageLocal G := by
    unfold averageLocal
    have hn : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α:=V)
    apply (le_div_iff₀ hn).mpr
    rw [← Nat.cast_sum]
    exact_mod_cast hD
  obtain ⟨p,hp⟩ := P6_of_local_mean_three G h4 h5 ha
  obtain ⟨w,hw,e,hn⟩ := short_neighbor h4 h5 (by decide) hp (hl _)
  change G.Adj w (p 0) at e
  have H : Nonempty (Hole G 6) ∨ Nonempty (Hole G 7) := by
    by_cases hW4 : G.Adj w (p 4)
    · apply Or.inl
      let q := p ∘ Fin.castLE (by decide : 5 ≤ 6)
      have hq : InducedPath G q := ⟨hp.1.comp (Fin.castLE_injective (by decide)),
        fun i j ht => hp.2 _ _ ht⟩
      apply close_induced_path (by decide) hq w (fun i => hw _)
      · exact e
      · exact hW4
      · intro i h1 h2
        exact hn (Fin.castLE (by decide : 5 ≤ 6) i) h1 (by change i.val ≤ 3; omega)
    · by_cases hW5 : G.Adj w (p 5)
      · apply Or.inr
        apply close_induced_path (by decide) hp w hw e hW5
        intro i h1 h2
        by_cases hi4 : i.val = 4
        · have ee : i = 4 := Fin.ext hi4
          exact ee ▸ hW4
        · exact hn i h1 (by omega)
      · exfalso
        obtain ⟨q,hq,_,_⟩ := prepend_induced_with_positions (by decide) hp w hw e (by
          intro i hi
          by_cases h4 : i.val = 4
          · have h : i=4 := Fin.ext h4
            exact h ▸ hW4
          · by_cases h5 : i.val = 5
            · have h : i=5 := Fin.ext h5
              exact h ▸ hW5
            · exact hn i hi (by have := i.isLt; omega))
        exact no ⟨q,hq⟩
  rcases H with H6 | H7
  · obtain ⟨H⟩ := H6
    have h := hex_budget H h4 h5 (hex_dominates H hc h4 h5 no)
    omega
  · obtain ⟨H⟩ := H7
    have h := heptagon_budget H (heptagon_spans H hc h4 h5 no)
    have pos := Fintype.card_pos (α:=V)
    omega

/-- A connected ordinary-C4/C5-free graph of mean local independence
at least three contains P7. -/
theorem P7_of_mean_three_no_five (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G) (h5 : NoSimpleFive133 G) (ha : 3 ≤ averageLocal G) :
    ∃ f : Fin 7 → V, InducedPath G f := by
  letI := hc.nonempty
  apply connected_peel_for_P7 G hc h4 h5 (nat_density_of_le_average G 3 ha)
  intro W _ J c a b lo d
  exact core_P7 c a b lo d

/-- The unrounded inequality at radius at most three, mean at most four,
without ordinary five-cycles. -/
theorem conjecture133_real_four_radius_three_no_five (G : SimpleGraph V) (hc : G.Connected)
    (hr : radius G ≤ 3) (ha : averageLocal G ≤ 4) (h5 : NoSimpleFive133 G) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · by_cases low : averageLocal G ≤ 3
    · exact conjecture133_real_full_three G hc low
    · refine ⟨7,?_,P7_of_mean_three_no_five G hc h4 h5 (le_of_lt (lt_of_not_ge low))⟩
      simp only [rhs133,if_pos h4,pow_one]
      change (radius G : ℚ) + averageLocal G ≤ 7
      have hr' : (radius G : ℚ) ≤ 3 := by exact_mod_cast hr
      linarith
  · exact conjecture133_low_average_or_four_cycle G hc (Or.inl h4)

#print axioms P7_of_mean_three_no_five
#print axioms conjecture133_real_four_radius_three_no_five

end Graffiti133NoFive
