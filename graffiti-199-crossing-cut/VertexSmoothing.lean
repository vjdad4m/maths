import TorsoMinimality

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-- Deleting a vertex and completing its open neighborhood is a smaller
three-connected graph with no increase in induced-tree order. -/
theorem traceable_after_smoothing_of_smaller {z : V}
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) :
    Traceable (cutTorso G (G.neighborFinset z) ({z} : Set V)) := by
  classical
  let D := G.neighborFinset z
  let B : Set V := {z}
  have ports (d : V) (h : d ∈ D) : d ∉ B := by
    intro hd
    have eq : d = z := hd
    exact G.loopless _ (eq ▸ (G.mem_neighborFinset z d).mp h)
  have boundary : ShoreBoundary G D B := by
    intro x xB y _ e
    have eq : x = z := xB
    exact (G.mem_neighborFinset z y).mpr (eq ▸ e)
  have minDegree := degree_of_small_deletion_preconnected (G := G)
    (by omega : 4 ≤ Fintype.card V) (fun E h => (conn.2 E h).preconnected) z
  have degree : 3 ≤ D.card := by rw [G.card_neighborFinset_eq_degree]; exact minDegree
  have size : Fintype.card {x : V // x ≠ z} = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl (fun x => x = z)]
    simp
  have keep : 3 < Fintype.card (Bᶜ : Set V) := by
    change 3 < Fintype.card {x : V // x ≠ z}
    omega
  have less : Fintype.card (Bᶜ : Set V) < Fintype.card V := by
    change Fintype.card {x : V // x ≠ z} < Fintype.card V
    omega
  have pc : (G.induce B).Preconnected :=
    fun a b => (show a = b from Subtype.ext (a.property.trans b.property.symm)) ▸ .rfl
  exact smaller _ _ less (cutTorso_connectivity conn degree keep ports boundary)
    ((cutTorso_treeNumber_le boundary pc (fun d h =>
      ⟨z,rfl,((G.mem_neighborFinset z d).mp h).symm⟩)).trans budget)

#print axioms traceable_after_smoothing_of_smaller

end Graffiti199Depleted.Catalogue
