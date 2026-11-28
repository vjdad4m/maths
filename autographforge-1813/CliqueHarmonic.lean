import Row595

namespace CliqueHarmonic1813
open SimpleGraph Finset RegularHarmonic595

def IsVertexCover {V : Type*} (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → u ∈ C ∨ v ∈ C

noncomputable def vertexCoverNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ C : Finset V, IsVertexCover G C ∧ C.card = k}

theorem clique_cover {n : ℕ} (hn : 0 < n) :
    vertexCoverNumber (⊤ : SimpleGraph (Fin n)) = n - 1 := by
  classical
  let G : SimpleGraph (Fin n) := ⊤
  let zero : Fin n := ⟨0,hn⟩
  let sizes : Set ℕ := {k | ∃ C : Finset (Fin n), IsVertexCover G C ∧ C.card = k}
  let D : Finset (Fin n) := univ.erase zero
  have feasible : n-1 ∈ sizes := by
    refine ⟨D,?_,by simp [D,card_erase_of_mem]⟩
    intro a b e
    by_cases h : a = zero
    · exact Or.inr (by simpa [D] using (show b ≠ zero from fun hb => e.ne (h.trans hb.symm)))
    · exact Or.inl (by simp [D,h])
  obtain ⟨C,hC,heq⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨_,feasible⟩)
  have hmiss : Cᶜ.card ≤ 1 := by
    apply Finset.card_le_one.2
    intro a ha b hb
    by_cases h : a = b
    · exact h
    · have ea : G.Adj a b := (top_adj a b).mpr h
      rcases hC ea with c|c
      · exact False.elim ((Finset.mem_compl.mp ha) c)
      · exact False.elim ((Finset.mem_compl.mp hb) c)
  rw [Finset.card_compl, Fintype.card_fin] at hmiss
  change C.card = vertexCoverNumber G at heq
  change vertexCoverNumber G = n-1
  exact le_antisymm (Nat.sInf_le feasible) (by omega)

theorem clique_harmonic {n : ℕ} (hn : 2 ≤ n) :
    harmonicIndex (⊤ : SimpleGraph (Fin n)) = (n : ℚ)/2 := by
  have h := harmonic_regular (⊤ : SimpleGraph (Fin n)) (d:=n-1) (by omega)
    (by simpa only [Fintype.card_fin] using (SimpleGraph.IsRegularOfDegree.top (V := Fin n)))
  simpa using h

theorem clique_family {n : ℕ} (hn : 37 ≤ n) :
    (35/18 : ℚ) * harmonicIndex (⊤ : SimpleGraph (Fin n)) <
      (vertexCoverNumber (⊤ : SimpleGraph (Fin n)) : ℚ) := by
  rw [clique_cover (by omega),clique_harmonic (by omega)]
  have hh : (37:ℚ) ≤ n := by exact_mod_cast hn
  rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  linarith

theorem row1813_false : ¬ (∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    2 ≤ Fintype.card V → (vertexCoverNumber G : ℚ) ≤ (35/18 : ℚ) * harmonicIndex G) := by
  intro claim
  exact (not_le_of_gt (clique_family (n:=37) le_rfl)) (claim (Fin 37) ⊤ (by decide))

#print axioms row1813_false
end CliqueHarmonic1813
