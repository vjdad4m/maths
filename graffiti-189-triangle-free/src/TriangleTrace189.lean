import TriangleOreBridge189
import BipartiteOre189

namespace Graffiti189TriangleOre
open SimpleGraph Finset Graffiti189LongestPath

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Complete triangle-free 2-connected lane of Graffiti.pc #189 at
second-smallest degree at least three. No external small-order
Hamiltonian theorem is needed. -/
theorem triangle_free_traceable
    (hc : G.Connected)
    (conn : ∀ S : Finset V, S.card < 2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (tf : ∀ ⦃x y z : V⦄, G.Adj x y → G.Adj y z → ¬G.Adj x z)
    {d : ℕ} (hd : 3 ≤ d)
    (cap : ∀ x, (EvenFrom G x).card ≤ d + 1)
    (high : ∀ u v : V, u ≠ v → d ≤ G.degree u ∨ d ≤ G.degree v) :
    GraphPathLift.HasSpanningPath G := by
  classical
  by_cases hn : 3 ≤ Fintype.card V
  · obtain ⟨D⟩ := triangle_free_near_ore hc conn tf hd cap high hn
    letI : DecidableRel D.graph.Adj := D.dec
    have h := Graffiti189TriangleFree.bipartite_ore_path D.graph D.color D.cross
      D.large D.first D.second D.sumDeg
    exact GraphPathLift.hasSpanningPath_map D.graph G (SimpleGraph.Hom.ofLE D.sub)
      Function.bijective_id h
  · apply traceable_of_distanceTwo_and_connectivity hc 2 _ conn
    intro x
    have h := (DistanceTwo G x).card_le_univ
    omega

/-- The triangle-free, 2-connected case for every degree threshold. -/
theorem triangle_free_traceable_all_degrees
    (hc : G.Connected)
    (conn : ∀ S : Finset V, S.card < 2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (tf : ∀ ⦃x y z : V⦄, G.Adj x y → G.Adj y z → ¬G.Adj x z)
    (d : ℕ)
    (cap : ∀ x, (EvenFrom G x).card ≤ d + 1)
    (high : ∀ u v : V, u ≠ v → d ≤ G.degree u ∨ d ≤ G.degree v) :
    GraphPathLift.HasSpanningPath G := by
  by_cases hd : 3 ≤ d
  · exact triangle_free_traceable hc conn tf hd cap high
  · apply traceable_of_distanceTwo_and_connectivity hc 2 _ conn
    intro x
    have h := distanceTwo_le_of_even d x (cap x)
    omega

#print axioms triangle_free_traceable_all_degrees
#print axioms triangle_free_traceable
end Graffiti189TriangleOre
