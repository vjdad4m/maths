import AdjacentContacts
import NonadjacentPorts

namespace Graffiti199Depleted.Catalogue.CubicMixedCut

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] [Fintype V] (F : CubicMixedCut G)

private theorem contact_pair_using (conn : ConnectivityAtLeast G 3) {v : V} (vB : v ∈ F.B)
    (touch : G.Adj F.p v ∨ G.Adj F.q v) :
    ∃ x ∈ F.B, ∃ y ∈ F.B, x ≠ y ∧ G.Adj F.p x ∧ G.Adj F.q y ∧ (x = v ∨ y = v) := by
  classical
  rcases touch with pv|qv
  · by_cases h : ∃ y ∈ F.B, y ≠ v ∧ G.Adj F.q y
    · obtain ⟨y,yB,yv,qy⟩ := h
      exact ⟨v,vB,y,yB,yv.symm,pv,qy,Or.inl rfl⟩
    · obtain ⟨x,xB,y,yB,xy,px,qy⟩ := F.distinct_contacts_to_B conn
      have eq : y = v := Classical.byContradiction (fun ne => h ⟨y,yB,ne,qy⟩)
      exact ⟨x,xB,y,yB,xy,px,qy,Or.inr eq⟩
  · by_cases h : ∃ x ∈ F.B, x ≠ v ∧ G.Adj F.p x
    · obtain ⟨x,xB,xv,px⟩ := h
      exact ⟨x,xB,v,vB,xv,px,qv,Or.inr rfl⟩
    · obtain ⟨x,xB,y,yB,xy,px,qy⟩ := F.distinct_contacts_to_B conn
      have eq : x = v := Classical.byContradiction (fun ne => h ⟨x,xB,ne,px⟩)
      exact ⟨x,xB,y,yB,xy,px,qy,Or.inl eq⟩

variable [DecidableRel G.Adj]

/-- The adjacent-neighbor case is traceable. An empty common clique
gives a bridge traversal, and a sole common vertex can be reserved by
choosing an exclusive port contact. -/
theorem traceable_of_adjacent_ports (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (bcEdge : G.Adj F.b F.c) (highB : 4 ≤ G.degree F.b) (highC : 4 ≤ G.degree F.c) : Traceable G := by
  classical
  by_cases hasHub : F.hub.Nonempty
  · by_cases two : ∃ u ∈ F.hub, ∃ v ∈ F.hub, u ≠ v
    · obtain ⟨x,xB,y,yB,xy,px,qy⟩ := F.distinct_contacts_to_B conn
      exact F.finish_of_B_path conn (F.route_with_hub budget bcEdge hasHub xB yB xy (Or.inl two)) px qy
    · obtain ⟨z,zh⟩ := hasHub
      have single : F.hub ⊆ {z} := by
        intro v vH
        exact Classical.byContradiction (fun ne => two ⟨v,vH,z,zh,ne⟩)
      have contact : ∃ v, (v ∈ F.leftOnly ∨ v ∈ F.rightOnly) ∧ (G.Adj F.p v ∨ G.Adj F.q v) := by
        rcases F.some_exclusive budget bcEdge with left|right
        · obtain ⟨v,vL,touch⟩ := F.some_port_into_leftOnly conn budget zh single left
          exact ⟨v,Or.inl vL,touch⟩
        · have zh' : z ∈ F.swap.hub := by rwa [F.swap_hub]
          have single' : F.swap.hub ⊆ {z} := by rwa [F.swap_hub]
          have right' : F.swap.leftOnly.Nonempty := by rwa [F.swap_leftOnly]
          obtain ⟨v,vR,touch⟩ := F.swap.some_port_into_leftOnly conn budget zh' single' right'
          exact ⟨v,Or.inr (F.swap_leftOnly ▸ vR),touch⟩
      obtain ⟨v,exclusive,touch⟩ := contact
      have vB : v ∈ F.B := exclusive.elim (fun h => h.1.1) (fun h => h.1.1)
      obtain ⟨x,xB,y,yB,xy,px,qy,selected⟩ := F.contact_pair_using conn vB touch
      have chosen : (x ∈ F.leftOnly ∨ x ∈ F.rightOnly) ∨
          (y ∈ F.leftOnly ∨ y ∈ F.rightOnly) := by
        rcases selected with e|e
        · exact Or.inl (e.symm ▸ exclusive)
        · exact Or.inr (e.symm ▸ exclusive)
      exact F.finish_of_B_path conn
        (F.route_with_hub budget bcEdge ⟨z,zh⟩ xB yB xy (Or.inr chosen)) px qy
  · have none (z : V) : z ∉ F.hub := fun zh => hasHub ⟨z,zh⟩
    have none' (z : V) : z ∉ F.swap.hub := by rw [F.swap_hub]; exact none z
    obtain ⟨x,xL,xfit,px⟩ := F.left_contact_without_hub conn budget none highB (Or.inl rfl)
    obtain ⟨y,yR',yfit',qy⟩ := F.swap.left_contact_without_hub conn budget none' highC (Or.inr rfl)
    have yR : y ∈ F.rightBlock := F.swap_left ▸ yR'
    have yfit : F.c ≠ y ∨ F.rightBlock = {F.c} :=
      yfit'.imp Ne.symm (fun eq => F.swap_left ▸ eq)
    have path := Traverses.along_cliques (F.left_clique budget) (F.right_clique budget)
      F.wingsApart xL (Or.inl rfl) (Or.inl rfl) yR xfit yfit bcEdge
    have empty : F.hub = ∅ := by
      ext v
      exact iff_of_false (none v) (Set.not_mem_empty v)
    have cover : F.leftBlock ∪ F.rightBlock = F.B := by
      simpa only [empty,Set.union_empty] using F.blocks_cover budget
    exact F.finish_of_B_path conn (cover ▸ path) px qy

theorem traceable_of_mixed_cut (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (highB : 4 ≤ G.degree F.b) (highC : 4 ≤ G.degree F.c) : Traceable G := by
  by_cases edge : G.Adj F.b F.c
  · exact F.traceable_of_adjacent_ports conn budget edge highB highC
  · exact F.traceable_of_nonadjacent_ports conn budget edge highB highC

#print axioms traceable_of_adjacent_ports
#print axioms traceable_of_mixed_cut

end Graffiti199Depleted.Catalogue.CubicMixedCut
