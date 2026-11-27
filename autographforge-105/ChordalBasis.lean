import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Lattice
import Lean.Elab.Tactic.Omega

namespace TriangleChain
open SimpleGraph Finset
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

/-- Consecutive indices of a simple cycle in either direction, including its closing edge. -/
def consecutive {k : ℕ} (i j : Fin k) : Prop :=
  i.val+1 = j.val ∨ j.val+1 = i.val ∨
    (i.val=0 ∧ j.val+1=k) ∨ (j.val=0 ∧ i.val+1=k)

/-- The usual forbidden-induced-cycle definition of a chordal graph. -/
def Chordal {U : Type*} (G : SimpleGraph U) : Prop :=
  ∀ k, 4 ≤ k → ¬∃ f : Fin k ↪ U, ∀ i j, G.Adj (f i) (f j) ↔ consecutive i j

end TriangleChain
