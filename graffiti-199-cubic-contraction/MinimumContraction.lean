import ContractConnectivity
import ContractTree
import ContractPath
import CubicEdgeCuts

namespace Graffiti199Depleted

open SimpleGraph

universe u

namespace Catalogue

/-- All smaller graphs satisfying the bounds for the three-connected
case have spanning paths. This is the portion of minimum-order
minimality used by the contraction argument. -/
def SmallerAtThree (n : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] (H : SimpleGraph W), Fintype.card W < n →
    ConnectivityAtLeast H 3 → treeNumber H ≤ 5 → Traceable H

/-- The exact catalogue minimum-order premise supplies the
smaller-graph property. Here connectivity is the catalogue's finite
vertex connectivity. -/
theorem smallerAtThree_of_catalogue_minimum {n : ℕ}
    (minimum : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W), Fintype.card W < n →
      H.Connected → 2 ≤ Fintype.card W → treeNumber H ≤ vertexConnectivity H + 2 →
      Traceable H) : SmallerAtThree.{u} n := by
  classical
  intro W _ H order conn tree
  have k3 : 3 ≤ vertexConnectivity H := by
    unfold vertexConnectivity
    exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr conn.1,conn⟩)
  have nodel : ((↑(∅ : Finset W) : Set W)ᶜ) = Set.univ := by simp
  have present := conn.2 ∅ (by simp)
  rw [nodel] at present
  have hc := (H.induceUnivIso.connected_iff).mp present
  have size := conn.1
  exact minimum W H order hc (by omega) (by omega)

end Catalogue

namespace ContractedEdge

variable {V : Type u} {G : SimpleGraph V} (E : ContractedEdge G)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Minimum order guarantees a spanning path in the contraction of
any edge with no common neighbor, under the archived cut law. -/
theorem contraction_traceable_of_smaller
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card V))
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (cross : CrossingBetweenSurvivingEdges G)
    (budget : Catalogue.treeNumber G ≤ 5) (order : 5 ≤ Fintype.card V)
    (noCommon : ∀ x, ¬ (G.Adj x E.a ∧ G.Adj x E.b)) :
    Catalogue.Traceable E.graph := by
  have size := E.card_vertex
  exact smaller E.Vertex E.graph (by omega)
    (E.connectivityAtLeast_three conn cross order noCommon) ((E.treeNumber_le noCommon).trans budget)

/-- In a nontraceable minimal graph, the contracted graph has a spanning
path, and each of its spanning paths enters and exits the contracted
vertex using two neighbors of the same original endpoint. -/
theorem minimum_contraction_same_side
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card V))
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (cross : CrossingBetweenSurvivingEdges G)
    (budget : Catalogue.treeNumber G ≤ 5) (order : 5 ≤ Fintype.card V)
    (noCommon : ∀ x, ¬ (G.Adj x E.a ∧ G.Adj x E.b))
    (noTrace : ¬ Catalogue.Traceable G) :
    Nonempty (PathOn E.graph Set.univ) ∧
      ∀ (p : PathOn E.graph Set.univ), ∃ (L R : List E.Vertex) (x y : E.Other),
        p.vertices = L ++ none :: R ∧ L.getLast? = some (some x) ∧ R.head? = some (some y) ∧
        ((G.Adj E.a x.val ∧ G.Adj E.a y.val) ∨ (G.Adj E.b x.val ∧ G.Adj E.b y.val)) := by
  have t := E.contraction_traceable_of_smaller smaller conn cross budget order noCommon
  refine ⟨pathOn_univ_iff_hamiltonian_walk.mpr (Catalogue.traceable_iff_hamiltonian_walk.mp t),?_⟩
  intro p
  obtain ⟨L,R,split⟩ := List.append_of_mem ((p.covers none).mpr (Set.mem_univ _))
  obtain ⟨x,y,left,right,side⟩ := E.reduced_path_same_side noTrace p split
  exact ⟨L,R,x,y,split,left,right,side⟩

/-- In the cubic-edge case the absence of common neighbors follows
from the catalogue tree budget and the archived cut law. -/
theorem minimum_cubic_contraction_same_side
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card V))
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (cross : CrossingBetweenSurvivingEdges G)
    (budget : Catalogue.treeNumber G ≤ 5) (order : 10 ≤ Fintype.card V)
    (da : G.degree E.a = 3) (db : G.degree E.b = 3)
    (noTrace : ¬ Catalogue.Traceable G) :
    Nonempty (PathOn E.graph Set.univ) ∧
      ∀ (p : PathOn E.graph Set.univ), ∃ (L R : List E.Vertex) (x y : E.Other),
        p.vertices = L ++ none :: R ∧ L.getLast? = some (some x) ∧ R.head? = some (some y) ∧
        ((G.Adj E.a x.val ∧ G.Adj E.a y.val) ∨ (G.Adj E.b x.val ∧ G.Adj E.b y.val)) := by
  exact E.minimum_contraction_same_side smaller conn cross budget (by omega)
    (adjacent_cubic_no_common_neighbor cross conn budget order E.edge da db) noTrace

#print axioms Catalogue.smallerAtThree_of_catalogue_minimum
#print axioms minimum_cubic_contraction_same_side

end ContractedEdge
end Graffiti199Depleted
