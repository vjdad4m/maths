import TrianglePathForms
import IndependentOmission

open private positive_gaps from GapBounds
open private first_last from ArbitraryGaps

namespace Graffiti199Depleted

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

namespace WiderOmission

/-- A spanning path missing one end of a cubic edge extends to a
spanning path of the graph if the other two neighbors of the omitted
vertex are adjacent. The two gaps and both exterior portions may have
arbitrary length. -/
theorem traceable_of_triangle_omission (budget : Catalogue.treeNumber G ≤ 5)
    (conn : Catalogue.ConnectivityAtLeast G 3)
    {z w : V} (p : PathOn G {v | v ≠ z}) (dz : G.degree z = 3) (dw : G.degree w = 3)
    (zw : G.Adj z w)
    (tri : ∀ x y, x ≠ y → x ≠ w → y ≠ w → G.Adj z x → G.Adj z y → G.Adj x y) :
    Catalogue.Traceable G := by
  classical
  by_contra noTrace
  obtain ⟨a,b,c,L,X,Y,R,split,za,zb,zc⟩ := ordered_omitted_neighbors p dz
  have ⟨px,py⟩ := positive_gaps noTrace p L X Y R split za zb zc
  by_cases hx : X.length = 1
  · obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp hx
    by_cases hy : Y.length = 1
    · obtain ⟨y,rfl⟩ := List.length_eq_one_iff.mp hy
      exact noTrace (traceable_triangle_compact_fragments budget conn p L R
        (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
        za zb zc dz dw zw tri)
    · obtain ⟨y,U,r,rfl⟩ := first_last (show 2 ≤ Y.length by omega)
      exact noTrace (traceable_triangle_short_fragments budget conn p L U R
        (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
        za zb zc dz dw zw tri)
  · by_cases hy : Y.length = 1
    · have backwards : p.rev.vertices =
          R.reverse ++ (c :: Y.reverse) ++ (b :: X.reverse) ++ a :: L.reverse := by
        change p.vertices.reverse = _
        rw [split]
        simp [List.reverse_append,List.reverse_cons,List.append_assoc,List.cons_append]
      obtain ⟨x,hx'⟩ := List.length_eq_one_iff.mp (show Y.reverse.length = 1 by simpa using hy)
      obtain ⟨y,U,r,hU⟩ := first_last (show 2 ≤ X.reverse.length by
        simpa only [List.length_reverse] using (show 2 ≤ X.length by omega))
      rw [hx',hU] at backwards
      exact noTrace (traceable_triangle_short_fragments budget conn p.rev R.reverse U L.reverse
        (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using backwards)
        zc zb za dz dw zw tri)
    · obtain ⟨x,U,q,he⟩ := first_last (show 2 ≤ X.length by omega)
      obtain ⟨y,S,r,hf⟩ := first_last (show 2 ≤ Y.length by omega)
      rw [he,hf] at split
      exact noTrace (traceable_triangle_separated_fragments budget p L U S R
        (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
        za zb zc dz dw zw tri)

end WiderOmission

namespace ContractedEdge

/-- An edge joining two cubic vertices cannot occur in the archived
minimum-order connectivity-three counterexample with the surviving-edge
cut property and at least ten vertices. -/
theorem traceable_of_minimum_cubic_edge (E : ContractedEdge G)
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card V))
    (conn : Catalogue.ConnectivityAtLeast G 3) (cross : CrossingBetweenSurvivingEdges G)
    (budget : Catalogue.treeNumber G ≤ 5) (order : 10 ≤ Fintype.card V)
    (da : G.degree E.a = 3) (db : G.degree E.b = 3) : Catalogue.Traceable G := by
  classical
  by_contra noTrace
  obtain ⟨z,w,which,⟨p,_⟩,a,b,_,_,ab,neighborhood⟩ :=
    E.minimum_cubic_edge_other_neighbors_adjacent smaller conn cross budget order da db noTrace
  have triangle (x y : V) (xy : x ≠ y) (xw : x ≠ w) (yw : y ≠ w)
      (zx : G.Adj z x) (zy : G.Adj z y) : G.Adj x y := by
    have mx := (G.mem_neighborFinset _ _).mpr zx
    have my := (G.mem_neighborFinset _ _).mpr zy
    rw [neighborhood] at mx my
    have hx : x = a ∨ x = b := by simpa [xw] using mx
    have hy : y = a ∨ y = b := by simpa [yw] using my
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
    · exact (xy rfl).elim
    · exact ab
    · exact ab.symm
    · exact (xy rfl).elim
  rcases which with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact noTrace (WiderOmission.traceable_of_triangle_omission budget conn p da db E.edge triangle)
  · exact noTrace (WiderOmission.traceable_of_triangle_omission budget conn p db da E.edge.symm triangle)

end ContractedEdge

/-- The cubic vertices form an independent set in the same minimum-order
case. In particular, the earlier single-edge and matching residuals are
excluded together. -/
theorem cubic_vertices_independent_of_minimum
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card V))
    (conn : Catalogue.ConnectivityAtLeast G 3) (cross : CrossingBetweenSurvivingEdges G)
    (budget : Catalogue.treeNumber G ≤ 5) (order : 10 ≤ Fintype.card V)
    (noTrace : ¬ Catalogue.Traceable G) {a b : V}
    (da : G.degree a = 3) (db : G.degree b = 3) : ¬ G.Adj a b :=
  fun edge => noTrace (ContractedEdge.traceable_of_minimum_cubic_edge
    ⟨a,b,edge⟩ smaller conn cross budget order da db)

#print axioms WiderOmission.traceable_of_triangle_omission
#print axioms ContractedEdge.traceable_of_minimum_cubic_edge
#print axioms cubic_vertices_independent_of_minimum

end Graffiti199Depleted
