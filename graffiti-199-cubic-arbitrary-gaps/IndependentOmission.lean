import ArbitraryGaps
import NeighborOrder

namespace Graffiti199Depleted

open SimpleGraph

universe u
variable {W : Type u} {G : SimpleGraph W}
variable [DecidableEq W] [DecidableRel G.Adj] [Fintype W]

namespace WiderOmission

/-- In the archived minimum-order and cut case, a one-omission path
at a cubic vertex with three independent neighbors and a cubic
neighbor implies that the whole graph is traceable. -/
theorem traceable_of_independent_omission (budget : Catalogue.treeNumber G ≤ 5)
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card W))
    (conn : Catalogue.ConnectivityAtLeast G 3) (cross : CrossingBetweenSurvivingEdges G)
    {z w : W} (p : PathOn G {v | v ≠ z}) (dz : G.degree z = 3)
    (dw : G.degree w = 3) (zw : G.Adj z w)
    (ind : ∀ a b, G.Adj z a → G.Adj z b → ¬ G.Adj a b) :
    Catalogue.Traceable G := by
  obtain ⟨a,b,c,L,X,Y,R,split,za,zb,zc⟩ := ordered_omitted_neighbors p dz
  exact traceable_of_ordered_independent_neighbors budget smaller conn cross p L X Y R split za zb zc
    (ind _ _ za zb) (ind _ _ za zc) (ind _ _ zb zc) dz dw zw

end WiderOmission

namespace ContractedEdge

/-- For a cubic edge of an archived minimum-order counterexample, the
endpoint selected by contraction has two adjacent neighbors. This
excludes the entire independent-neighborhood branch. -/
theorem minimum_cubic_edge_omission_has_triangle (E : ContractedEdge G)
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card W))
    (conn : Catalogue.ConnectivityAtLeast G 3) (cross : CrossingBetweenSurvivingEdges G)
    (budget : Catalogue.treeNumber G ≤ 5) (order : 10 ≤ Fintype.card W)
    (da : G.degree E.a = 3) (db : G.degree E.b = 3)
    (noTrace : ¬ Catalogue.Traceable G) :
    ∃ z, (z = E.a ∨ z = E.b) ∧ (∃ p : PathOn G {v | v ≠ z}, ConstrainedOmission z p) ∧
      ∃ a b, G.Adj z a ∧ G.Adj z b ∧ G.Adj a b := by
  obtain ⟨z,whereOmitted,p,constrained⟩ :=
    E.minimum_cubic_edge_constrained_omission smaller conn cross budget order da db noTrace
  refine ⟨z,whereOmitted,⟨p,constrained⟩,?_⟩
  classical
  by_contra noTriangle
  have ind (a b : W) (za : G.Adj z a) (zb : G.Adj z b) : ¬ G.Adj a b :=
    fun e => noTriangle ⟨a,b,za,zb,e⟩
  rcases whereOmitted with h|h
  · subst z
    exact noTrace (WiderOmission.traceable_of_independent_omission budget smaller conn cross p da db E.edge ind)
  · subst z
    exact noTrace (WiderOmission.traceable_of_independent_omission budget smaller conn cross p db da E.edge.symm ind)

/-- The triangle at the selected omission uses exactly the two
neighbors other than the cubic mate. -/
theorem minimum_cubic_edge_other_neighbors_adjacent (E : ContractedEdge G)
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card W))
    (conn : Catalogue.ConnectivityAtLeast G 3) (cross : CrossingBetweenSurvivingEdges G)
    (budget : Catalogue.treeNumber G ≤ 5) (order : 10 ≤ Fintype.card W)
    (da : G.degree E.a = 3) (db : G.degree E.b = 3)
    (noTrace : ¬ Catalogue.Traceable G) :
    ∃ z w, ((z = E.a ∧ w = E.b) ∨ (z = E.b ∧ w = E.a)) ∧
      (∃ p : PathOn G {v | v ≠ z}, ConstrainedOmission z p) ∧
      ∃ a b, a ≠ w ∧ b ≠ w ∧ G.Adj a b ∧ G.neighborFinset z = {w,a,b} := by
  obtain ⟨z,endAt,path,a,b,za,zb,ab⟩ :=
    E.minimum_cubic_edge_omission_has_triangle smaller conn cross budget order da db noTrace
  have noShared := adjacent_cubic_no_common_neighbor cross conn budget order E.edge da db
  have exhaust {z w : W} (zw : G.Adj z w) (zdeg : G.degree z = 3)
      (no : ∀ x, ¬ (G.Adj x z ∧ G.Adj x w))
      (za : G.Adj z a) (zb : G.Adj z b) :
      a ≠ w ∧ b ≠ w ∧ G.Adj a b ∧ G.neighborFinset z = {w,a,b} := by
    have aw : a ≠ w := fun e => no b ⟨zb.symm,(e ▸ ab).symm⟩
    have bw : b ≠ w := fun e => no a ⟨za.symm,e ▸ ab⟩
    let S : Finset W := {w,a,b}
    have sub : S ⊆ G.neighborFinset z := by
      intro x mem
      rcases (show x = w ∨ x = a ∨ x = b by simpa [S] using mem) with rfl|rfl|rfl
      · exact (G.mem_neighborFinset _ _).mpr zw
      · exact (G.mem_neighborFinset _ _).mpr za
      · exact (G.mem_neighborFinset _ _).mpr zb
    have count : S.card = 3 := by
      change (insert w ({a,b} : Finset W)).card = 3
      rw [Finset.card_insert_of_not_mem (by simp [aw.symm,bw.symm]),Finset.card_pair ab.ne]
    refine ⟨aw,bw,ab,(Finset.eq_of_subset_of_card_le sub ?_).symm⟩
    rw [G.card_neighborFinset_eq_degree,zdeg,count]
  rcases endAt with h|h
  · subst z
    exact ⟨E.a,E.b,Or.inl ⟨rfl,rfl⟩,path,a,b,exhaust E.edge da noShared za zb⟩
  · subst z
    exact ⟨E.b,E.a,Or.inr ⟨rfl,rfl⟩,path,a,b,
      exhaust E.edge.symm db (fun x h => noShared x ⟨h.2,h.1⟩) za zb⟩

end ContractedEdge

#print axioms WiderOmission.traceable_of_independent_omission
#print axioms ContractedEdge.minimum_cubic_edge_omission_has_triangle
#print axioms ContractedEdge.minimum_cubic_edge_other_neighbors_adjacent

end Graffiti199Depleted
