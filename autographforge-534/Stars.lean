import Row534

namespace Restrained534
open Finset SimpleGraph CographRadius

/-- The join of one new vertex with an independent set of size n. -/
def star (n : ℕ) : SimpleGraph (Option (Fin n)) where
  Adj x y := x ≠ y ∧ (x = none ∨ y = none)
  symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
  loopless := fun _ h => h.1 rfl

theorem star_center (n : ℕ) : Universal (star n) none :=
  fun _ h => ⟨h,Or.inl rfl⟩

theorem star_cograph (n : ℕ) : Cograph (star n) := by
  rintro ⟨f,adj⟩
  have e := ((adj 0 1).mpr (Or.inl rfl)).2
  have g := ((adj 2 3).mpr (Or.inl rfl)).2
  have distinct {i j : Fin 4} (h : i ≠ j) (a : f i = none) (b : f j = none) : False :=
    h (f.injective (a.trans b.symm))
  rcases e with h|h <;> rcases g with k|k <;> exact distinct (by decide) h k

theorem star_connected (n : ℕ) : (star n).Connected := by
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨none,?_⟩
  rintro (_|v)
  · exact Reachable.rfl
  · exact (star_center n (some v) (by simp)).reachable

theorem star_exact (n : ℕ) :
    restrainedNumber (star n) = n+1 ∧ independentDomination (star n) = 1 := by
  classical
  let emb : Fin n ↪ Option (Fin n) := ⟨some,Option.some_injective _⟩
  have leaves : leavesAt (star n) none = univ.map emb := by
    ext x
    cases x with
    | none =>
      simp only [mem_leaves,ne_self_iff_false,false_and,mem_map,mem_univ,true_and]
      simp [emb]
    | some a =>
      constructor
      · intro _
        exact mem_map.mpr ⟨a,mem_univ _,rfl⟩
      · intro _
        apply (mem_leaves _).mpr
        refine ⟨by simp,fun w h => ?_⟩
        exact h.2.resolve_left (by simp)
  refine ⟨?_,independent_universal _ (star_center n)⟩
  rw [cone_formula _ (star_center n),leaves,card_map,card_univ,Fintype.card_fin]

/-- The ordinary domination number uses the same closed-neighborhood constraint. -/
noncomputable def dominationNumber {V : Type*} (G : SimpleGraph V) :=
  sInf {n : ℕ | ∃ D : Finset V, D.card = n ∧ Dominates G D}

theorem empty_graph_domination (n : ℕ) : dominationNumber (⊥ : SimpleGraph (Fin n)) = n := by
  let H : SimpleGraph (Fin n) := ⊥
  let P := {k : ℕ | ∃ D : Finset (Fin n), D.card = k ∧ Dominates H D}
  have ex : P.Nonempty := ⟨_,univ,rfl,fun v => Or.inl (mem_univ v)⟩
  obtain ⟨D,hd,dom⟩ := Nat.sInf_mem (s := P) ex
  have full : D = univ := eq_univ_of_forall fun v =>
    (dom v).elim id fun ⟨_,_,edge⟩ => False.elim edge
  change sInf P = n
  rw [← hd, full, card_univ, Fintype.card_fin]

/-- For the join K₁ ∨ edgeless(n), n≥2, the singleton-join expression
in arXiv:1606.02340v1, Thm 7.3, gives n. The actual optimum is n+1.
Every one of the n vertices of the edgeless factor is isolated. -/
theorem singleton_join_discrepancy (n : ℕ) :
    Cograph (star n) ∧ (star n).Connected ∧
    min (1 + Fintype.card {v : Fin n // ∀ w, ¬ (⊥ : SimpleGraph (Fin n)).Adj v w})
      (dominationNumber (⊥ : SimpleGraph (Fin n))) = n ∧
    n < restrainedNumber (star n) := by
  classical
  have iso : Fintype.card {v : Fin n // ∀ w, ¬ (⊥ : SimpleGraph (Fin n)).Adj v w} = n := by
    simp
  refine ⟨star_cograph n,star_connected n,?_,?_⟩
  · rw [iso,empty_graph_domination]; omega
  · rw [(star_exact n).1]; omega

#print axioms star_exact
#print axioms singleton_join_discrepancy
end Restrained534
