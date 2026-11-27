import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-! Threshold forcing and its optimizer, extracted from the checked row 711 proof. -/
namespace ForcingDrop711
open Finset Function SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/- These definitions follow the published BalancedForcing module. -/
def step (k : ℕ) (S : Finset V) : Finset V :=
  S ∪ univ.filter (fun w => w ∉ S ∧ ∃ v ∈ S, G.Adj v w ∧ (G.neighborFinset v \ S).card ≤ k)

def full (k : ℕ) (S : Finset V) : Prop := (step G k)^[Fintype.card V] S = univ

noncomputable def forcing (k : ℕ) : ℕ :=
  sInf {r | ∃ S : Finset V, S.card = r ∧ full G k S}

private theorem persistent (k : ℕ) (S : Finset V) : S ⊆ step G k S :=
  subset_union_left

theorem mem_step {S : Finset V} {k : ℕ} {w : V} :
    w ∈ step G k S ↔ w ∈ S ∨ ∃ v ∈ S, G.Adj v w ∧ (G.neighborFinset v \ S).card ≤ k := by
  simp only [step, mem_union, mem_filter, mem_univ, true_and]
  by_cases h : w ∈ S <;> simp [h]

private theorem step_univ (k : ℕ) : step G k univ = univ :=
  eq_univ_of_forall (fun v => persistent G k univ (mem_univ v))

private theorem full_univ (k : ℕ) : full G k univ :=
  iterate_fixed (step_univ G k) _

theorem attained (k : ℕ) : ∃ S : Finset V, S.card = forcing G k ∧ full G k S :=
  Nat.sInf_mem (s := {r | ∃ S : Finset V, S.card = r ∧ full G k S})
    ⟨_,univ,rfl,full_univ G k⟩

theorem forcing_le {k : ℕ} {S : Finset V} (h : full G k S) : forcing G k ≤ S.card :=
  Nat.sInf_le (s := {r | ∃ T : Finset V, T.card = r ∧ full G k T}) ⟨S,rfl,h⟩

end ForcingDrop711
