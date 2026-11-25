import Std
set_option warningAsError true
namespace Graffiti426
abbrev Set (V : Type) := V → Prop
abbrev Graph (V : Type) := V → V → Prop

def Neighborhood {V} (G : Graph V) (M : Set V) : Set V :=
  fun v => ∃ m, M m ∧ G v m

def Independent {V} (G : Graph V) (I : Set V) : Prop :=
  ∀ v w, I v → I w → ¬ G v w

def Dominates {V} (G : Graph V) (U I : Set V) : Prop :=
  ∀ v, U v → I v ∨ ∃ w, I w ∧ G v w

noncomputable def card {n} (U : Set (Fin n)) : Nat := by
  classical
  exact ((List.ofFn id : List (Fin n)).filter fun v => decide (U v)).length

theorem cover_extend {V} (G : Graph V)
    (symm : ∀ {x y}, G x y → G y x) (loopless : ∀ x, ¬ G x x)
    (xs : List V) (S : Set V) (hS : Independent G S) :
    ∃ I : Set V, Independent G I ∧ (∀ v, S v → I v)
      ∧ Dominates G (fun v => v ∈ xs) I := by
  classical
  induction xs generalizing S with
  | nil =>
    exact ⟨S, hS, fun _ h => h, fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons a xs ih =>
    by_cases hh : S a ∨ ∃ w, S w ∧ G a w
    · obtain ⟨I, hI, hSI, hDom⟩ := ih S hS
      refine ⟨I, hI, hSI, ?_⟩
      intro v h
      rcases List.mem_cons.mp h with h | h
      · subst v
        rcases hh with ha | ⟨w, hw, haw⟩
        · exact Or.inl (hSI _ ha)
        · exact Or.inr ⟨w, hSI _ hw, haw⟩
      · exact hDom _ h
    · let S' : Set V := fun v => S v ∨ v = a
      have hS' : Independent G S' := by
        intro v w hv hw h
        rcases hv with hv | rfl <;> rcases hw with hw | rfl
        · exact hS _ _ hv hw h
        · exact hh (Or.inr ⟨v, hv, symm h⟩)
        · exact hh (Or.inr ⟨w, hw, h⟩)
        · exact loopless _ h
      obtain ⟨I, hI, hSI, hDom⟩ := ih S' hS'
      refine ⟨I, hI, (fun v hv => hSI v (Or.inl hv)), ?_⟩
      intro v h
      rcases List.mem_cons.mp h with h | h
      · exact Or.inl (hSI _ (Or.inr h))
      · exact hDom _ h

private theorem filter_split {V} (U I : Set V) (xs : List V) : by
    classical
    exact (xs.filter (fun v => decide (I v))).length +
      (xs.filter (fun v => decide (U v ∧ ¬ I v))).length ≤ xs.length := by
  classical
  induction xs with
  | nil => simp
  | cons a l ih =>
    by_cases hi : I a <;> by_cases hu : U a <;>
      simp [List.filter_cons, hi, hu] at * <;> omega

theorem card_split {n} (U I : Set (Fin n)) :
    card I + card (fun v => U v ∧ ¬ I v) ≤ n := by
  classical
  have h := filter_split U I (List.ofFn id)
  simpa [card] using h

/-- Construct simultaneous independent and ordinary dominating sets with the
required sum of cardinalities. This works for arbitrary M. -/
theorem simultaneous {n} (G : Graph (Fin n))
    (symm : ∀ {x y}, G x y → G y x) (loopless : ∀ x, ¬ G x x)
    (M : Set (Fin n)) :
    ∃ I D : Set (Fin n), Independent G I ∧ Dominates G (fun _ => True) I ∧
      (∀ v, D v → Neighborhood G M v) ∧ Dominates G (Neighborhood G M) D ∧
      card I + card D ≤ n := by
  classical
  let U := Neighborhood G M
  let W : Set (Fin n) := fun v => M v ∧ ¬ U v
  have hW : Independent G W := by
    intro v w hv hw hj
    exact hv.2 ⟨w, hw.1, hj⟩
  obtain ⟨I, hi, hwi, hdi⟩ := cover_extend G @symm loopless (List.ofFn id) W hW
  let D : Set (Fin n) := fun v => U v ∧ ¬ I v
  refine ⟨I, D, hi, (fun v _ => hdi v (List.mem_ofFn.mpr ⟨v,rfl⟩)), (fun _ h => h.1), ?_, card_split U I⟩
  intro v hv
  by_cases iv : I v
  · have hn : ∃ w, U w ∧ G v w := by
      apply Classical.byContradiction
      intro hn
      obtain ⟨m, hm, hvₘ⟩ := hv
      have hwm : W m := ⟨hm, fun hum => hn ⟨m, hum, hvₘ⟩⟩
      exact hi v m iv (hwi _ hwm) (hvₘ)
    obtain ⟨w, hw, hvw⟩ := hn
    exact Or.inr ⟨w, ⟨hw, fun h => hi _ _ iv h hvw⟩, hvw⟩
  · exact Or.inl ⟨hv, iv⟩
end Graffiti426
namespace Graffiti426

theorem min_exists (P : Nat → Prop) (h : ∃ k, P k) :
    ∃ k, P k ∧ ∀ j, P j → k ≤ j := by
  classical
  obtain ⟨k, hk⟩ := h
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases he : ∃ j, j < k ∧ P j
    · obtain ⟨j, hj, hp⟩ := he
      exact ih j hj hp
    · refine ⟨k, hk, ?_⟩
      intro j hj
      by_cases hlt : j < k
      · exact False.elim (he ⟨j,hlt,hj⟩)
      · omega

def independentDomCard {n} (G : Graph (Fin n)) (k : Nat) : Prop :=
  ∃ I, Independent G I ∧ Dominates G (fun _ => True) I ∧ card I = k

def inducedDomCard {n} (G : Graph (Fin n)) (U : Set (Fin n)) (k : Nat) : Prop :=
  ∃ D, (∀ v, D v → U v) ∧ Dominates G U D ∧ card D = k

theorem indep_exists {n} (G : Graph (Fin n))
    (symm : ∀ {x y}, G x y → G y x) (loopless : ∀ x, ¬ G x x) :
    ∃ k, independentDomCard G k := by
  obtain ⟨I, _, hi, hd, _, _, _⟩ := simultaneous G @symm loopless (fun _ => False)
  exact ⟨card I, I, hi, hd, rfl⟩

theorem dom_exists {n} (G : Graph (Fin n)) (U : Set (Fin n)) :
    ∃ k, inducedDomCard G U k :=
  ⟨card U, U, (fun _ h => h), (fun _ h => Or.inl h), rfl⟩

noncomputable def independentDomination {n} (G : Graph (Fin n))
    (symm : ∀ {x y}, G x y → G y x) (loopless : ∀ x, ¬ G x x) : Nat :=
  Classical.choose (min_exists _ (indep_exists G @symm loopless))

noncomputable def inducedDomination {n} (G : Graph (Fin n)) (U : Set (Fin n)) : Nat :=
  Classical.choose (min_exists _ (dom_exists G U))

/-- Exact conjecture in the stronger version allowing arbitrary M and no
connectivity or order lower bound. -/
theorem conjecture426 {n} (G : Graph (Fin n))
    (symm : ∀ {x y}, G x y → G y x) (loopless : ∀ x, ¬ G x x)
    (M : Set (Fin n)) :
    independentDomination G @symm loopless ≤ n - inducedDomination G (Neighborhood G M) := by
  obtain ⟨I, D, hI, hdI, hD, hdD, hcard⟩ := simultaneous G @symm loopless M
  have h1 : independentDomination G @symm loopless ≤ card I :=
    (Classical.choose_spec (min_exists _ (indep_exists G @symm loopless))).2 _
      ⟨I,hI,hdI,rfl⟩
  have h2 : inducedDomination G (Neighborhood G M) ≤ card D :=
    (Classical.choose_spec (min_exists _ (dom_exists G (Neighborhood G M)))).2 _
      ⟨D,hD,hdD,rfl⟩
  omega

#print axioms conjecture426
end Graffiti426
