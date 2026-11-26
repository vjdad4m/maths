import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Nat.Lattice

/-! A kernel-checked certificate of Siddhant Dubey's witness to WOW II #398. -/

namespace Graffiti398

open Finset SimpleGraph

section Definitions
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Catalogue definition 90. Each vertex outside D needs two distinct neighbors in D. -/
def TwoDominates (D : Finset V) : Prop :=
  ∀ v, v ∈ D ∨ 2 ≤ (D.filter (G.Adj v)).card

noncomputable def twoDominationNumber : ℕ :=
  sInf {k : ℕ | ∃ D, TwoDominates G D ∧ D.card = k}

/-- Catalogue definition 123. -/
def pendants : Finset V :=
  univ.filter (fun v => G.degree v = 1)

/-- Open neighborhood of a set, as in catalogue definition 46. -/
def openNeighborhood (S : Finset V) : Finset V :=
  univ.filter (fun v => ∃ u ∈ S, G.Adj v u)

def supportVertices : Finset V := openNeighborhood G (pendants G)

def remainingEdgeCount (S : Finset V) : ℕ :=
  (G.induce ((univ \ S : Finset V) : Set V)).edgeFinset.card

def uniqueNeighborCount : ℕ :=
  (univ.filter (fun v =>
    (G.neighborFinset v ∩ (univ \ supportVertices G)).card = 1)).card

/-- An unordered edge is counted if it has an endpoint in S and one outside S. -/
def cutEdgeCount (S : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∃ u ∈ S, ∃ v ∉ S, e = s(u,v))).card

def catalogueRhs : ℕ :=
  remainingEdgeCount G (openNeighborhood G (supportVertices G)) +
    uniqueNeighborCount G + cutEdgeCount G (pendants G)

end Definitions

abbrev Vertex := Fin 5

/-- The triangle has vertices 0, 3, 4. Vertices 1 and 2 are their pendant neighbors. -/
def witnessAdj (u v : Vertex) : Prop :=
  (u ≠ v ∧ u ≠ 1 ∧ u ≠ 2 ∧ v ≠ 1 ∧ v ≠ 2) ∨
    (u = 1 ∧ v = 3) ∨ (u = 3 ∧ v = 1) ∨
    (u = 2 ∧ v = 4) ∨ (u = 4 ∧ v = 2)

instance (u v : Vertex) : Decidable (witnessAdj u v) := by
  unfold witnessAdj
  infer_instance

private theorem witness_symmetric : ∀ u v : Vertex, witnessAdj u v → witnessAdj v u := by decide

private theorem witness_loopless : ∀ v : Vertex, ¬witnessAdj v v := by decide

def witness : SimpleGraph Vertex where
  Adj := witnessAdj
  symm := witness_symmetric
  loopless := witness_loopless

instance : DecidableRel witness.Adj := fun u v =>
  inferInstanceAs (Decidable (witnessAdj u v))

theorem witness_connected : witness.Connected := by
  apply (connected_iff_exists_forall_reachable witness).mpr
  refine ⟨0,fun v => ?_⟩
  have h : ∀ w : Vertex, w = 0 ∨ witness.Adj 0 w ∨
        ∃ u : Vertex, witness.Adj 0 u ∧ witness.Adj u w := by decide
  rcases h v with rfl | he | ⟨u,hu,hev⟩
  · exact Reachable.refl _
  · exact he.reachable
  · exact hu.reachable.trans hev.reachable

theorem pendants_eq : pendants witness = {1,2} := by decide

theorem supportVertices_eq : supportVertices witness = {3,4} := by
  rw [supportVertices,pendants_eq]
  decide

theorem secondNeighborhood_eq : openNeighborhood witness (supportVertices witness) = univ := by
  rw [supportVertices_eq]
  decide

theorem induced_term_eq : remainingEdgeCount witness
    (openNeighborhood witness (supportVertices witness)) = 0 := by
  rw [secondNeighborhood_eq]
  decide

theorem unique_term_eq : uniqueNeighborCount witness = 0 := by
  unfold uniqueNeighborCount
  rw [supportVertices_eq]
  decide

theorem cut_term_eq : cutEdgeCount witness (pendants witness) = 2 := by
  rw [pendants_eq]
  decide

theorem rhs_eq : catalogueRhs witness = 2 := by
  rw [catalogueRhs, induced_term_eq, unique_term_eq, cut_term_eq]

/-- The same witness works if the old doubled typography is read as one open neighborhood. -/
theorem one_neighborhood_induced_term_eq :
    remainingEdgeCount witness (supportVertices witness) = 0 := by
  rw [supportVertices_eq]
  decide

/-- Adding the support set itself to its open neighborhood leaves the induced term zero. -/
theorem closed_second_induced_term_eq :
    remainingEdgeCount witness
      (supportVertices witness ∪ openNeighborhood witness (supportVertices witness)) = 0 := by
  rw [secondNeighborhood_eq, Finset.union_eq_right.mpr (subset_univ _)]
  decide

def selected : Finset Vertex := {0,1,2}

theorem selected_twoDominates : TwoDominates witness selected := by
  unfold TwoDominates
  decide

private theorem twoDomination_lower :
    ∀ D : Finset Vertex, TwoDominates witness D → 3 ≤ D.card := by
  unfold TwoDominates
  decide

theorem twoDomination_eq : twoDominationNumber witness = 3 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨selected,selected_twoDominates,by decide⟩
  · have hn : {k : ℕ | ∃ D, TwoDominates witness D ∧ D.card = k}.Nonempty :=
      ⟨3,selected,selected_twoDominates,by decide⟩
    obtain ⟨D,hD,hcard⟩ := Nat.sInf_mem hn
    change 3 ≤ sInf _
    rw [← hcard]
    exact twoDomination_lower D hD

theorem counterexample398 :
    witness.Connected ∧ 2 < Fintype.card Vertex ∧
      catalogueRhs witness < twoDominationNumber witness :=
  ⟨witness_connected,by decide, by rw [rhs_eq,twoDomination_eq]; decide⟩

theorem conjecture398_false :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → 2 < Fintype.card V → twoDominationNumber G ≤ catalogueRhs G := by
  intro h
  exact (not_le_of_gt counterexample398.2.2) (h Vertex witness witness_connected (by decide))

#print axioms induced_term_eq
#print axioms unique_term_eq
#print axioms cut_term_eq
#print axioms twoDomination_eq
#print axioms conjecture398_false

end Graffiti398
