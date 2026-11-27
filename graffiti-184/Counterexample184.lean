import Counterexample185
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! The exact peripheral-distance reading of Written on the Wall II #184. -/

namespace Graffiti184

open SimpleGraph Finset
open scoped BigOperators
noncomputable section

variable {V : Type*} [Fintype V]

def eccentricity (G : SimpleGraph V) (v : V) : ℕ := univ.sup (G.dist v)

def square (G : SimpleGraph V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ G.dist x y ≤ 2
  symm := fun x y h => ⟨h.1.symm, (G.dist_comm (u := x) (v := y)) ▸ h.2⟩
  loopless := fun _ h => h.1 rfl

def diameter (G : SimpleGraph V) : ℕ := univ.sup (eccentricity G)

def squareMaxDegree (G : SimpleGraph V) : ℕ := by
  classical
  exact (square G).maxDegree

def squareNeighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact (square G).neighborFinset v

def maxLeaves (G : SimpleGraph V) : ℕ := by
  classical
  exact sSup {k | ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧
    (univ.filter (fun v => T.degree v = 1)).card = k}

def bipartiteNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact (univ.powerset.filter (fun s : Finset V =>
    ∃ c : s → Bool, ∀ a b : s, G.Adj a.val b.val → c a ≠ c b)).sup Finset.card

def periphery (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter (fun v => eccentricity G v = diameter G)

/-- Ordered pairs, with a peripheral first coordinate and positive distance. -/
def peripheralPairs (G : SimpleGraph V) : Finset (V × V) := by
  classical
  exact ((periphery G).product univ).filter (fun p => 0 < G.dist p.1 p.2)

def peripheralMean (G : SimpleGraph V) : ℚ :=
  ((∑ p ∈ peripheralPairs G, G.dist p.1 p.2 : ℕ) : ℚ) / (peripheralPairs G).card

def Claim184 (G : SimpleGraph V) : Prop :=
  (squareMaxDegree G : ℚ) + 2 * peripheralMean (square G) ≤
    (maxLeaves G : ℚ) + (bipartiteNumber G : ℚ)

end
end Graffiti184

namespace Graffiti184.Counterexample
open Finset SimpleGraph
open Graffiti185.Counterexample (V G)
open scoped BigOperators

set_option maxHeartbeats 3200000
set_option maxRecDepth 10000

abbrev table := Graffiti185.Counterexample.numericSquareDist

theorem exact_distance (x y : V) : (square G).dist x y = table x y :=
  Graffiti185.Counterexample.distance_model x y

def tabEcc (v : V) : ℕ := univ.sup (table v)
def tabPeriphery : Finset V := univ.filter (fun v => tabEcc v = univ.sup tabEcc)
def tabPairs : Finset (V × V) :=
  (tabPeriphery.product univ).filter (fun p => 0 < table p.1 p.2)

theorem ecc_eq_table : eccentricity (square G) = tabEcc := by
  funext v
  unfold eccentricity tabEcc
  exact congrArg (univ.sup : (V → ℕ) → ℕ) (funext (exact_distance v))

theorem periphery_eq_table : periphery (square G) = tabPeriphery := by
  simp only [periphery,diameter,ecc_eq_table,tabPeriphery]

theorem pairs_eq_table : peripheralPairs (square G) = tabPairs := by
  classical
  ext p
  simp [peripheralPairs,tabPairs,periphery_eq_table,exact_distance]

theorem periphery_count : tabPeriphery.card = 21 := by decide +kernel
theorem pairs_count : tabPairs.card = 441 := by decide +kernel

theorem peripheral_sum : ∑ p ∈ tabPairs, table p.1 p.2 = 675 := by
  decide +kernel

theorem mean : peripheralMean (square G) = (75 : ℚ) / 49 := by
  unfold peripheralMean
  rw [pairs_eq_table]
  have hs : (∑ p ∈ tabPairs, (square G).dist p.1 p.2) =
      ∑ p ∈ tabPairs, table p.1 p.2 := by simp only [exact_distance]
  rw [hs,peripheral_sum,pairs_count]
  norm_num

theorem square_max : squareMaxDegree G = 21 := by
  classical
  have lo : 21 ≤ (square G).maxDegree := Graffiti185.Counterexample.degree_lower
  have hi := (square G).maxDegree_lt_card_verts
  rw [show Fintype.card V = 22 by decide] at hi
  change (square G).maxDegree = 21
  omega

theorem counterexample : G.Connected ∧ ¬ Claim184 G := by
  refine ⟨Graffiti185.Counterexample.connected_G,?_⟩
  have hL : maxLeaves G ≤ 14 := Graffiti185.Counterexample.leaves_upper
  have hB : bipartiteNumber G ≤ 10 := Graffiti185.Counterexample.bipartite_upper
  have hL' : (maxLeaves G : ℚ) ≤ 14 := by exact_mod_cast hL
  have hB' : (bipartiteNumber G : ℚ) ≤ 10 := by exact_mod_cast hB
  unfold Claim184
  rw [square_max,mean]
  norm_num; linarith

#print axioms counterexample
end Graffiti184.Counterexample
