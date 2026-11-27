import TwoSingletons

open private ClawShore.leaf_mem ClawShore.leaf_only from OppositeClaw
open private clique_or_path_of_three from CrossingOrder
open private exists_third_port from ThreePathWithRoute

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {A B : Set V} {D : Finset V}

/-- A claw component is incompatible with two singleton components
and a second nonempty nonsingleton side. -/
theorem no_claw_shore_with_two_singletons (C : ClawShore G A)
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B) (bNon : B.Nonempty) {r s : V} (rs : r ≠ s)
    (hr : CutSingleton G D r) (hs : CutSingleton G D s)
    (rA : r ∉ A) (rB : r ∉ B) (sA : s ∉ A) (sB : s ∉ B) : False := by
  obtain ⟨x,hx⟩ : C.leaves.Nonempty := Finset.card_pos.mp (by have := C.three; omega)
  obtain ⟨y,hy,yx⟩ := Finset.exists_ne_of_one_lt_card (by have := C.three; omega : 1 < C.leaves.card) x
  have twoX := at_least_two_ports_of_shore_endpoint conn boundA
    (ClawShore.leaf_mem C hx) (ClawShore.leaf_only C hx)
  have twoY := at_least_two_ports_of_shore_endpoint conn boundA
    (ClawShore.leaf_mem C hy) (ClawShore.leaf_only C hy)
  exact C.independent x hx y hy
    (adjacent_of_two_port_contacts_and_two_singletons conn budget size offA offB boundA boundB
      apart bNon rs hr hs rA rB sA sB (ClawShore.leaf_mem C hx) (ClawShore.leaf_mem C hy)
      yx.symm twoX twoY)

/-- The order-twelve split into components of orders three, four, one,
and one has a spanning path under the same induced-tree bound. -/
theorem traceable_of_three_four_and_two_singletons
    (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundA : ShoreBoundary G D A) (boundB : ShoreBoundary G D B)
    (apart : Disjoint A B)
    {r s : V} (rs : r ≠ s) (hr : CutSingleton G D r) (hs : CutSingleton G D s)
    (rA : r ∉ A) (rB : r ∉ B) (sA : s ∉ A) (sB : s ∉ B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D ∨ v = r ∨ v = s)
    (connA : (G.induce A).Connected) (connB : (G.induce B).Connected)
    (nA : Nat.card A = 3) (nB : Nat.card B = 4) : Traceable G := by
  classical
  obtain ⟨a⟩ := connA.nonempty
  obtain ⟨b⟩ := connB.nonempty
  have clA : A.Pairwise G.Adj := by
    rcases clique_or_path_of_three connA nA with h|p
    · exact h
    · obtain ⟨P⟩ := p
      exact (no_three_vertex_path_with_two_singleton_components P conn budget size offA offB
        boundA boundB apart ⟨b.val,b.property⟩ rs hr hs rA rB sA sB).elim
  have routeB : ∃ q ∈ D, ∃ t ∈ D, q ≠ t ∧ ShoreRoute G B q t := by
    rcases route_or_claw_of_four_shore conn size offB boundB connB nB ⟨r,rB,hr.1⟩ with h|claw
    · exact h
    · obtain ⟨C⟩ := claw
      exact (no_claw_shore_with_two_singletons C conn budget size offB offA boundB boundA
        apart.symm ⟨a.val,a.property⟩ rs hr hs rB rA sB sA).elim
  obtain ⟨q,qD,t,tD,qt,R⟩ := routeB
  obtain ⟨p,qp,tp,frame⟩ := exists_third_port size qD tD qt
  have sorted : D = {p,q,t} := by
    rw [frame]
    ext v
    simp only [Finset.mem_insert,Finset.mem_singleton]
    tauto
  clear frame
  subst D
  obtain ⟨f,hf⟩ := shore_distinct_attachments conn size offA boundA (by omega) ⟨r,rA,hr.1⟩
  have L := clique_shore_route clA (p := ⟨p,by simp⟩) (q := ⟨q,by simp⟩)
    (fun e => qp (congrArg Subtype.val e).symm) f hf
  exact traceable_of_two_routes_and_two_singletons qp.symm tp.symm qt rs hr hs offA offB
    rA rB sA sB apart cover L R

#print axioms no_claw_shore_with_two_singletons
#print axioms traceable_of_three_four_and_two_singletons

end Graffiti199Depleted.Catalogue
