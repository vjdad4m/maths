import OppositeClaw
import CompletePort

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
variable {A B : Set V} {D : Finset V}

/-- The verified residual profile when one of the two components of a
three-cut is a three-vertex path with a cubic endpoint. -/
theorem cubic_path_shore_residual_of_minimum
    (S : ThreeVertexShore G A)
    (smaller : SmallerAtThree.{u} (Fintype.card V))
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : 5 ≤ Fintype.card V) (no : ¬ Traceable G)
    (ind : ∀ x y, G.degree x = 3 → G.degree y = 3 → ¬ G.Adj x y)
    (size : D.card = 3) (degree : G.degree S.left = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D)
    (nonempty : B.Nonempty) :
    (∃ s ∈ D, G.Adj s S.middle ∧
      G.neighborFinset S.left = insert S.middle (D.erase s) ∧
      G.neighborFinset S.right = insert S.middle (D.erase s)) ∧
    (∃ d ∈ D, ∀ v ∈ A, G.Adj d v) ∧
    (∀ a ∈ D, ∀ b ∈ D, a ≠ b → ¬ ShoreRoute G B a b) ∧
    (¬ Nonempty (ClawShore G B)) ∧
    (∀ P : PathOn G {x | x ≠ S.left},
      ¬ ∃ L M R : List V, P.vertices = L ++ M ++ R ∧ (∀ v, v ∈ M ↔ v ∈ B)) := by
  obtain ⟨P⟩ := pathOn_of_traceable_delete
    (traceable_after_cubic_delete smaller conn budget order no ind degree)
  refine ⟨cubic_three_vertex_shore_profile S conn size offA boundA degree P no,
    exists_complete_port_of_cubic_path_shore S conn size offA boundA ind degree P no,?_,?_,?_⟩
  · intro a aD b bD ab route
    exact no (traceable_of_cubic_path_shore_and_route S conn size offA offB boundA apart
      cover degree P aD bD ab route)
  · rintro ⟨C⟩
    exact no (traceable_of_cubic_path_shore_and_claw S C conn budget size offA offB
      boundA boundB apart cover degree P)
  · intro Q
    exact no_single_interval_of_opposite_shore S conn size degree offA offB boundA boundB
      apart cover nonempty Q no

#print axioms cubic_path_shore_residual_of_minimum

end Graffiti199Depleted.Catalogue
