import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Mathlib.Combinatorics.SimpleGraph.Finite
/-! Maximum-matching definitions and attainment, excerpted from the published matching basis. -/
namespace Graffiti326
open Finset SimpleGraph
open scoped BigOperators
noncomputable section
variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel G.Adj

def HasMatching (G : SimpleGraph V) (k : ℕ) :=
  ∃ f : Fin k × Bool ↪ V, ∀ i, G.Adj (f (i,false)) (f (i,true))

local instance (G : SimpleGraph V) : DecidablePred (HasMatching G) := Classical.decPred _

private def feasibleMatchingSizes (G : SimpleGraph V) : Finset ℕ :=
  (range (Fintype.card V / 2+1)).filter (HasMatching G)

private theorem matchingSizes_nonempty (G : SimpleGraph V) :
    (feasibleMatchingSizes G).Nonempty := by
  use 0
  simp only [feasibleMatchingSizes, mem_filter, mem_range]
  refine ⟨by omega, ⟨⟨fun p => Fin.elim0 p.1, ?_⟩, ?_⟩⟩
  · intro p; exact Fin.elim0 p.1
  · intro i; exact Fin.elim0 i

def matchingNumber (G : SimpleGraph V) : ℕ :=
  (feasibleMatchingSizes G).max' (matchingSizes_nonempty G)

theorem matchingNumber_attained (G : SimpleGraph V) : HasMatching G (matchingNumber G) := by
  exact (Finset.mem_filter.1 (Finset.max'_mem (feasibleMatchingSizes G)
    (matchingSizes_nonempty G))).2

theorem matchingNumber_upper {G : SimpleGraph V} {k : ℕ} (hk : HasMatching G k) :
    k ≤ matchingNumber G := by
  obtain ⟨f,hf⟩ := hk
  have hk' : 2*k ≤ Fintype.card V := by
    simpa [Nat.mul_comm] using Fintype.card_le_of_injective f f.injective
  apply Finset.le_max'
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ⟨f,hf⟩⟩

end
end Graffiti326
