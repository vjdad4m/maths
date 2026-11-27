import OrderElevenGeometry

open private clique_or_path_of_three from CrossingOrder

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
variable {A B : Set V} {D : Finset V}

/-- With precisely two components and a three-vertex side, any supported
route on the other side yields traceability at any total order. -/
theorem traceable_of_three_shore_and_supported_route
    (conn : ConnectivityAtLeast G 3) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (apart : Disjoint A B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D)
    (connA : (G.induce A).Connected) (nA : Nat.card A = 3)
    {p q : V} (hp : p ∈ D) (hq : q ∈ D) (pq : p ≠ q) (route : ShoreRoute G B p q) :
    Traceable G := by
  classical
  rcases clique_or_path_of_three connA nA with cl|path
  · have retain := route
    obtain ⟨x,_,_,_,P,eq,_⟩ := route
    have xB : x ∈ B := eq ▸ (P.covers P.first).mp (List.head_mem P.nonempty)
    have swap (v : V) : v ∈ B ∨ v ∈ A ∨ v ∈ D := by have h := cover v; tauto
    exact traceable_of_routable_and_clique_shores conn size offB offA boundA (by omega)
      apart.symm ⟨x,xB⟩ swap cl hp hq pq retain
  · obtain ⟨S⟩ := path
    exact traceable_of_three_vertex_path_and_opposite_route S conn size offA offB boundA
      apart cover hp hq pq route

/-- A clique side of order at least three always suffices opposite a
connected four-vertex component, including the opposite claw. -/
theorem traceable_of_clique_and_four_shore
    (conn : ConnectivityAtLeast G 3) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D)
    (connA : (G.induce A).Connected) (connB : (G.induce B).Connected)
    (clique : A.Pairwise G.Adj) (largeA : 3 ≤ Nat.card A) (sizeB : Nat.card B = 4) :
    Traceable G := by
  classical
  obtain ⟨a⟩ := connA.nonempty
  obtain ⟨b⟩ := connB.nonempty
  have other : ∃ v : V, v ∉ B ∧ v ∉ D :=
    ⟨a.val,Set.disjoint_left.mp apart a.property,fun h => offA _ h a.property⟩
  rcases route_or_claw_of_four_shore conn size offB boundB connB sizeB other with route|claw
  · obtain ⟨p,pD,q,qD,pq,R⟩ := route
    have swap (v : V) : v ∈ B ∨ v ∈ A ∨ v ∈ D := by have h := cover v; tauto
    exact traceable_of_routable_and_clique_shores conn size offB offA boundA largeA
      apart.symm ⟨b.val,b.property⟩ swap clique pD qD pq R
  · obtain ⟨C⟩ := claw
    exact traceable_of_clique_shore_and_claw C conn size offA offB boundA boundB
      apart cover clique largeA

#print axioms traceable_of_three_shore_and_supported_route
#print axioms traceable_of_clique_and_four_shore

end Graffiti199Depleted.Catalogue
