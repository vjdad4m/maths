import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path

open Finset

namespace KelmansStarter

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Delete at most two vertices and require the surviving induced graph to be
connected. There must be at least four vertices to begin with. -/
def ThreeConnected (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card ≤ 2 → (G.induce {v : V | v ∉ S}).Connected

/-- A three-vertex path uses two edges. The endpoints may also be adjacent. -/
def IsTile (G : SimpleGraph V) (s : Finset V) : Prop :=
  s.card = 3 ∧ ∃ c ∈ s, ∀ x ∈ s, x ≠ c → G.Adj c x

/-- A partition of all vertices into three-vertex paths. -/
def HasP3Factor (G : SimpleGraph V) : Prop :=
  ∃ parts : Finset (Finset V),
    (∀ s ∈ parts, IsTile G s) ∧
    (∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t) ∧
    parts.biUnion id = univ

/-- The order-divisible-by-six form of the Kelmans conjecture.
This defines a proposition; it does not assert it. -/
def Conjecture (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∀ v, G.degree v = 3) → ThreeConnected G →
    6 ∣ Fintype.card V → HasP3Factor G

end KelmansStarter
