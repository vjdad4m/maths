import ClawViaCommonPort
import CrossingOrder

open private clique_or_path_of_three from CrossingOrder

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
variable {A B : Set V} {D : Finset V}

/-- A three-cut with precisely two components of orders three and four
has a Hamiltonian path under the six-vertex induced-tree bound. -/
theorem traceable_of_three_and_four_shores
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D)
    (connA : (G.induce A).Connected) (connB : (G.induce B).Connected)
    (nA : Nat.card A = 3) (nB : Nat.card B = 4) : Traceable G := by
  classical
  obtain ⟨a⟩ := connA.nonempty
  obtain ⟨b⟩ := connB.nonempty
  have other : ∃ v : V, v ∉ B ∧ v ∉ D :=
    ⟨a.val,Set.disjoint_left.mp apart a.property,fun h => offA _ h a.property⟩
  rcases clique_or_path_of_three connA nA with clique|pathA
  · rcases route_or_claw_of_four_shore conn size offB boundB connB nB other with routeB|clawB
    · obtain ⟨p,pD,q,qD,pq,route⟩ := routeB
      have swap (v : V) : v ∈ B ∨ v ∈ A ∨ v ∈ D := by have h := cover v; tauto
      exact traceable_of_routable_and_clique_shores conn size offB offA boundA (by omega)
        apart.symm ⟨b.val,b.property⟩ swap clique pD qD pq route
    · obtain ⟨C⟩ := clawB
      exact traceable_of_clique_shore_and_claw C conn size offA offB boundA boundB apart cover clique (by omega)
  · obtain ⟨S⟩ := pathA
    rcases route_or_claw_of_four_shore conn size offB boundB connB nB other with routeB|clawB
    · obtain ⟨p,pD,q,qD,pq,route⟩ := routeB
      exact traceable_of_three_vertex_path_and_opposite_route S conn size offA offB boundA apart cover
        pD qD pq route
    · obtain ⟨C⟩ := clawB
      exact traceable_of_three_vertex_path_shore_and_claw S C conn budget size offA offB
        boundA boundB apart cover

/-- The remaining crossing failure through order ten is resolved when
the two distinguished components cover the surviving graph. -/
theorem LargeCrossingFailure.traceable_of_order_le_ten_of_cover
    (F : LargeCrossingFailure G) (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (order : Fintype.card V ≤ 10)
    (cover : ∀ v, v ∈ componentShore F.cut F.first ∨
      v ∈ componentShore F.cut F.second ∨ v ∈ F.cut) : Traceable G := by
  classical
  by_cases small : Fintype.card V ≤ 9
  · exact F.traceable_of_order_le_nine conn budget small
  let A := componentShore F.cut F.first
  let B := componentShore F.cut F.second
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  have offA := componentShore_off_cut F.cut F.first
  have offB := componentShore_off_cut F.cut F.second
  have boundA := componentShore_boundary F.cut F.first
  have boundB := componentShore_boundary F.cut F.second
  have connA := componentShore_connected F.cut F.first
  have connB := componentShore_connected F.cut F.second
  have apart := componentShore_disjoint F.different
  let U := (F.cut ∪ A.toFinset) ∪ B.toFinset
  have dA : Disjoint F.cut A.toFinset :=
    Finset.disjoint_left.mpr (fun x hx hA => offA x hx (Set.mem_toFinset.mp hA))
  have dB : Disjoint (F.cut ∪ A.toFinset) B.toFinset := by
    apply Finset.disjoint_left.mpr
    intro x hx hB
    rcases Finset.mem_union.mp hx with cut|lhs
    · exact offB x cut (Set.mem_toFinset.mp hB)
    · exact Set.disjoint_left.mp apart (Set.mem_toFinset.mp lhs) (Set.mem_toFinset.mp hB)
  have cardU : U.card = 3 + Nat.card A + Nat.card B := by
    change ((F.cut ∪ A.toFinset) ∪ B.toFinset).card = _
    rw [Finset.card_union_of_disjoint dB,Finset.card_union_of_disjoint dA,F.size,
      Set.toFinset_card,Set.toFinset_card,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  have full : U = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    change v ∈ (F.cut ∪ A.toFinset) ∪ B.toFinset
    simp only [Finset.mem_union,Set.mem_toFinset]
    have h : v ∈ A ∨ v ∈ B ∨ v ∈ F.cut := cover v
    tauto
  have ca : 3 ≤ Nat.card A := F.first_large
  have cb : 3 ≤ Nat.card B := F.second_large
  rw [full,Finset.card_univ] at cardU
  by_cases na : Nat.card A = 3
  · exact traceable_of_three_and_four_shores conn budget F.size offA offB boundA boundB apart cover
      connA connB na (show Nat.card B = 4 by omega)
  · have swap (v : V) : v ∈ B ∨ v ∈ A ∨ v ∈ F.cut := by
      have h : v ∈ A ∨ v ∈ B ∨ v ∈ F.cut := cover v
      tauto
    exact traceable_of_three_and_four_shores conn budget F.size offB offA boundB boundA apart.symm swap
      connB connA (show Nat.card B = 3 by omega) (show Nat.card A = 4 by omega)

#print axioms traceable_of_three_and_four_shores
#print axioms LargeCrossingFailure.traceable_of_order_le_ten_of_cover

end Graffiti199Depleted.Catalogue
