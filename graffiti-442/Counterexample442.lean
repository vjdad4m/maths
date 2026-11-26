import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Written on the Wall II, conjecture 442

This formalizes AI Village's published 12-vertex witness: an 11-vertex
path and a hub adjacent to its nine internal vertices. The short set
certificate uses four disjoint path edges. Siddhant Dubey previously
published a different 12-vertex witness in his July worklog.

The high-degree induced graph contains an induced path on nine
vertices and has order ten, so its ceiling term is exactly five.
The exhibited 2-independent set has order eight, above the bound seven.
Checked on Lean 4.19.0 and Mathlib v4.19.0.
-/

namespace Graffiti442
open Finset SimpleGraph

/-- A path on n vertices, with no additional edges between its vertices. -/
def HasInducedPath {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : Fin n → V, Function.Injective f ∧ ∀ i j,
    G.Adj (f i) (f j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val

noncomputable def pathNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sSup {n | HasInducedPath G n}

def highDegree {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => 3 ≤ G.degree v

def highGraph {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph ↑(highDegree G : Set V) := G.induce (highDegree G : Set V)

def IsDissociation {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) : Prop := ∀ v ∈ D, (D.filter (G.Adj v)).card ≤ 1

noncomputable def dissociationNumber {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ := sSup {n | ∃ D : Finset V, IsDissociation G D ∧ D.card = n}

/-- Exact rational ceiling in the catalogue's integer-valued upper bound. -/
noncomputable def catalogueRhs {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℤ :=
  (Fintype.card V : ℤ) - ⌈(pathNumber (highGraph G) : ℚ) / 2⌉

abbrev Vertex := Fin 12

def witnessAdj (u v : Vertex) : Prop :=
  (u.val < 11 ∧ v.val < 11 ∧ (u.val+1 = v.val ∨ v.val+1 = u.val)) ∨
  (u = 11 ∧ 1 ≤ v.val ∧ v.val ≤ 9) ∨ (v = 11 ∧ 1 ≤ u.val ∧ u.val ≤ 9)

instance (u v : Vertex) : Decidable (witnessAdj u v) := by
  unfold witnessAdj
  infer_instance

def witness : SimpleGraph Vertex where
  Adj := witnessAdj
  symm := by intro u v h; unfold witnessAdj at *; tauto
  loopless := by change ∀ v : Vertex, ¬ witnessAdj v v; decide

instance : DecidableRel witness.Adj := fun u v => inferInstanceAs (Decidable (witnessAdj u v))

private theorem reached : ∀ v : Vertex, v = 11 ∨ witness.Adj 11 v ∨
    ∃ u, witness.Adj 11 u ∧ witness.Adj u v := by decide

theorem witness_connected : witness.Connected := by
  apply (connected_iff_exists_forall_reachable witness).mpr
  refine ⟨11,fun v => ?_⟩
  rcases reached v with rfl | h | ⟨u,hu,hv⟩
  · exact Reachable.rfl
  · exact h.reachable
  · exact hu.reachable.trans hv.reachable

private def internal (i : Fin 9) : Vertex :=
  ⟨i.val + 1,by have := i.isLt; omega⟩

private theorem internal_high : ∀ i : Fin 9, internal i ∈ highDegree witness := by decide

private def highPath (i : Fin 9) : ↑(highDegree witness : Set Vertex) :=
  ⟨internal i,internal_high i⟩

private theorem highPath_adj : ∀ i j : Fin 9,
    witness.Adj (internal i) (internal j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by decide

theorem path_bounds : 9 ≤ pathNumber (highGraph witness) ∧ pathNumber (highGraph witness) ≤ 10 := by
  have hp : HasInducedPath (highGraph witness) 9 := by
    refine ⟨highPath,?_,highPath_adj⟩
    intro x y h
    apply Fin.ext
    have he := congrArg (fun v : ↑(highDegree witness : Set Vertex) => v.val.val) h
    change x.val+1=y.val+1 at he
    omega
  have hhc : (highDegree witness).card = 10 := by decide
  have hu : ∀ k ∈ {k | HasInducedPath (highGraph witness) k}, k ≤ 10 := by
    rintro k ⟨f,hf,-⟩
    have hh := Fintype.card_le_of_injective f hf
    simpa [Fintype.card_coe,hhc] using hh
  have hm : 9 ∈ {k | HasInducedPath (highGraph witness) k} := hp
  unfold pathNumber
  exact ⟨le_csSup ⟨10,hu⟩ hm,csSup_le ⟨9,hm⟩ hu⟩

def selected : Finset Vertex := {0,1,3,4,6,7,9,10}

private theorem selected_ok : IsDissociation witness selected := by unfold IsDissociation; decide

theorem eight_le : 8 ≤ dissociationNumber witness := by
  unfold dissociationNumber
  apply le_csSup
  · refine ⟨12,?_⟩
    rintro _ ⟨D,_,rfl⟩
    exact (card_le_univ D).trans_eq (by decide)
  · exact ⟨selected,selected_ok,by decide⟩

theorem rhs_eq : catalogueRhs witness = 7 := by
  obtain ⟨hlo,hhi⟩ := path_bounds
  have he : pathNumber (highGraph witness) = 9 ∨ pathNumber (highGraph witness) = 10 := by omega
  unfold catalogueRhs
  rcases he with he | he <;> rw [he] <;> norm_num

theorem counterexample442 : witness.Connected ∧ 3 < Fintype.card Vertex ∧
    catalogueRhs witness < (dissociationNumber witness : ℤ) := by
  refine ⟨witness_connected,by decide,?_⟩
  rw [rhs_eq]
  have h : (8 : ℤ) ≤ dissociationNumber witness := by exact_mod_cast eight_le
  omega

#print axioms counterexample442
end Graffiti442
