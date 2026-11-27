import Placement23
import Placement24
import Placement33
import OmissionGap

namespace Graffiti199Depleted

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

namespace WiderOmission

omit [DecidableRel G.Adj] [Fintype V] in
private theorem positive_gaps (noTrace : ¬ Catalogue.Traceable G)
    {z a b c : V} (p : PathOn G {v | v ≠ z}) (L X Y R : List V)
    (split : p.vertices = L ++ (a :: X) ++ (b :: Y) ++ c :: R)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c) :
    0 < X.length ∧ 0 < Y.length := by
  have h := omission_constraints noTrace p
  constructor
  · cases X with
    | nil =>
      exact (h.transitionOff L (Y ++ c :: R) a b
        (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split) ⟨za,zb⟩).elim
    | cons => simp
  · cases Y with
    | nil =>
      exact (h.transitionOff (L ++ (a :: X)) R b c
        (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split) ⟨zb,zc⟩).elim
    | cons => simp

/-- The two gaps between successive visits to the independent neighbors
of a cubic omission have total length at least seven edges. The
quantities X.length and Y.length count only intervening vertices. -/
theorem sum_intervening_at_least_five (budget : Catalogue.treeNumber G ≤ 5)
    (noTrace : ¬ Catalogue.Traceable G) {z w a b c : V}
    (dz : G.degree z = 3) (dw : G.degree w = 3) (zw : G.Adj z w)
    (p : PathOn G {v | v ≠ z}) (L X Y R : List V)
    (split : p.vertices = L ++ (a :: X) ++ (b :: Y) ++ c :: R)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c)
    (ab : ¬ G.Adj a b) (ac : ¬ G.Adj a c) (bc : ¬ G.Adj b c) :
    5 ≤ X.length + Y.length := by
  have ⟨pX,pY⟩ := positive_gaps noTrace p L X Y R split za zb zc
  have noncompact := CompactOmission.two_intervening_vertices budget noTrace dz dw zw
    p L X Y R split za zb zc ab ac bc
  by_contra! small
  by_cases x1 : X.length = 1
  · have y : Y.length = 2 ∨ Y.length = 3 := by omega
    obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp x1
    rcases y with y2|y3
    · obtain ⟨v,t,rfl⟩ := List.length_eq_two.mp y2
      exact noTrace (traceable_of_gaps_two_three budget p L R (by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
        za zb zc ab ac bc dz dw zw)
    · obtain ⟨v,s,t,rfl⟩ := List.length_eq_three.mp y3
      exact noTrace (traceable_of_gaps_two_four budget p L R (by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
        za zb zc ab ac bc dz dw zw)
  · by_cases y1 : Y.length = 1
    · have x : X.length = 2 ∨ X.length = 3 := by omega
      obtain ⟨s,rfl⟩ := List.length_eq_one_iff.mp y1
      rcases x with x2|x3
      · obtain ⟨v,t,rfl⟩ := List.length_eq_two.mp x2
        exact noTrace (traceable_of_gaps_three_two budget p L R (by
          simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
          zc zb za (fun e => bc e.symm) (fun e => ac e.symm) (fun e => ab e.symm) dz dw zw)
      · obtain ⟨v,u,t,rfl⟩ := List.length_eq_three.mp x3
        exact noTrace (traceable_of_gaps_four_two budget p L R (by
          simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
          zc zb za (fun e => bc e.symm) (fun e => ac e.symm) (fun e => ab e.symm) dz dw zw)
    · have x2 : X.length = 2 := by omega
      have y2 : Y.length = 2 := by omega
      obtain ⟨x,v,rfl⟩ := List.length_eq_two.mp x2
      obtain ⟨y,t,rfl⟩ := List.length_eq_two.mp y2
      exact noTrace (traceable_of_gaps_three_three budget p L R (by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
        za zb zc ab ac bc dz dw zw)

end WiderOmission

namespace ContractedEdge

/-- The selected endpoint omission in the cubic-edge contraction obeys
the gap bound on every path through the vertex deletion. -/
theorem minimum_cubic_edge_wider_gaps (E : ContractedEdge G)
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card V))
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (cross : CrossingBetweenSurvivingEdges G) (budget : Catalogue.treeNumber G ≤ 5)
    (order : 10 ≤ Fintype.card V) (da : G.degree E.a = 3) (db : G.degree E.b = 3)
    (noTrace : ¬ Catalogue.Traceable G) :
    ∃ z, (z = E.a ∨ z = E.b) ∧ (∃ p : PathOn G {v | v ≠ z}, ConstrainedOmission z p) ∧
      ∀ {a b c : V} (q : PathOn G {v | v ≠ z}) (L X Y R : List V),
        q.vertices = L ++ (a :: X) ++ (b :: Y) ++ c :: R →
        G.Adj z a → G.Adj z b → G.Adj z c →
        ¬ G.Adj a b → ¬ G.Adj a c → ¬ G.Adj b c → 5 ≤ X.length + Y.length := by
  obtain ⟨z,atEnd,p,constrained⟩ :=
    E.minimum_cubic_edge_constrained_omission smaller conn cross budget order da db noTrace
  refine ⟨z,atEnd,⟨p,constrained⟩,?_⟩
  rcases atEnd with ha|hb
  · subst z
    intro a b c q L X Y R
    exact WiderOmission.sum_intervening_at_least_five budget noTrace da db E.edge q L X Y R
  · subst z
    intro a b c q L X Y R
    exact WiderOmission.sum_intervening_at_least_five budget noTrace db da E.edge.symm q L X Y R

end ContractedEdge

#print axioms WiderOmission.sum_intervening_at_least_five
#print axioms ContractedEdge.minimum_cubic_edge_wider_gaps

end Graffiti199Depleted
