import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice

namespace Restrained534
open SimpleGraph Finset
variable {U : Type*} [Fintype U] (G : SimpleGraph U)

def Dominates {W : Type*} (H : SimpleGraph W) (S : Finset W) :=
  ∀ v, v ∈ S ∨ ∃ u ∈ S, H.Adj v u

/-- GraphCalc minimizes the size of a vertex set that is independent and
dominates every closed neighborhood. -/
noncomputable def independentDomination : ℕ := sInf {s : ℕ | ∃ S : Finset U,
  S.card = s ∧ G.IsIndepSet S ∧ Dominates G S}

/-- A maximum independent set is dominating, so the feasible sizes are nonempty. -/
theorem attained : ∃ S : Finset U, S.card = independentDomination G ∧
    G.IsIndepSet S ∧ Dominates G S := by
  classical
  obtain ⟨S,hS⟩ := maximumIndepSet_exists (G := G)
  have dom : Dominates G S := by
    intro v
    by_contra! missed
    have outside : v ∉ S := missed.1
    have nonadj (u : U) (hu : u ∈ S) : ¬G.Adj v u := missed.2 u hu
    have larger : G.IsIndepSet (↑(insert v S : Finset U) : Set U) := by
      intro a ha b hb ne ab
      rcases mem_insert.mp ha with rfl|aS <;> rcases mem_insert.mp hb with rfl|bS
      · exact ne rfl
      · exact nonadj b bS ab
      · exact nonadj a aS ab.symm
      · exact hS.isIndepSet aS bS ne ab
    have bound := hS.maximum _ larger
    rw [card_insert_of_not_mem outside] at bound
    omega
  exact Nat.sInf_mem (s := {s : ℕ | ∃ T : Finset U, T.card = s ∧ G.IsIndepSet T ∧ Dominates G T})
    ⟨S.card,S,rfl,hS.isIndepSet,dom⟩

end Restrained534
