import Placement25
import Placement34
import GapBounds

open private positive_gaps from GapBounds

namespace Graffiti199Depleted

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

namespace WiderOmission

omit [DecidableEq V] [Fintype V] in
private theorem length_eq_four {L : List V} (h : L.length = 4) :
    ∃ a b c d, L = [a,b,c,d] := by
  cases L with
  | nil => simp at h
  | cons a T =>
    have len : T.length = 3 := by simpa using h
    obtain ⟨b,c,d,rfl⟩ := List.length_eq_three.mp len
    exact ⟨a,b,c,d,rfl⟩

/-- In the nontraceable case, the two gaps between consecutive visits
to the three independent neighbors have at least eight edges total. -/
theorem sum_intervening_at_least_six (budget : Catalogue.treeNumber G ≤ 5)
    (noTrace : ¬ Catalogue.Traceable G) {z w a b c : V}
    (dz : G.degree z = 3) (dw : G.degree w = 3) (zw : G.Adj z w)
    (p : PathOn G {v | v ≠ z}) (L X Y R : List V)
    (split : p.vertices = L ++ (a :: X) ++ (b :: Y) ++ c :: R)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c)
    (ab : ¬ G.Adj a b) (ac : ¬ G.Adj a c) (bc : ¬ G.Adj b c) :
    6 ≤ X.length + Y.length := by
  have ⟨pX,pY⟩ := positive_gaps noTrace p L X Y R split za zb zc
  have large := sum_intervening_at_least_five budget noTrace dz dw zw p L X Y R
    split za zb zc ab ac bc
  by_contra! small
  have cases : X.length = 1 ∨ X.length = 2 ∨ X.length = 3 ∨ X.length = 4 := by omega
  rcases cases with hx|hx|hx|hx
  · have hy : Y.length = 4 := by omega
    obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp hx
    obtain ⟨v,s,t,u,rfl⟩ := length_eq_four hy
    exact noTrace (traceable_of_gaps_two_five budget p L R (by
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
      za zb zc ab ac bc dz dw zw)
  · have hy : Y.length = 3 := by omega
    obtain ⟨x,y,rfl⟩ := List.length_eq_two.mp hx
    obtain ⟨v,t,u,rfl⟩ := List.length_eq_three.mp hy
    exact noTrace (traceable_of_gaps_three_four budget p L R (by
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
      za zb zc ab ac bc dz dw zw)
  · have hy : Y.length = 2 := by omega
    obtain ⟨v,t,u,rfl⟩ := List.length_eq_three.mp hx
    obtain ⟨x,y,rfl⟩ := List.length_eq_two.mp hy
    exact noTrace (traceable_of_gaps_four_three budget p L R (by
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
      zc zb za (fun e => bc e.symm) (fun e => ac e.symm) (fun e => ab e.symm) dz dw zw)
  · have hy : Y.length = 1 := by omega
    obtain ⟨v,s,t,u,rfl⟩ := length_eq_four hx
    obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp hy
    exact noTrace (traceable_of_gaps_five_two budget p L R (by
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
      zc zb za (fun e => bc e.symm) (fun e => ac e.symm) (fun e => ab e.symm) dz dw zw)

end WiderOmission

namespace ContractedEdge

theorem minimum_cubic_edge_total_gap_eight (E : ContractedEdge G)
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card V))
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (cross : CrossingBetweenSurvivingEdges G) (budget : Catalogue.treeNumber G ≤ 5)
    (order : 10 ≤ Fintype.card V) (da : G.degree E.a = 3) (db : G.degree E.b = 3)
    (noTrace : ¬ Catalogue.Traceable G) :
    ∃ z, (z = E.a ∨ z = E.b) ∧ (∃ p : PathOn G {v | v ≠ z}, ConstrainedOmission z p) ∧
      ∀ {a b c : V} (q : PathOn G {v | v ≠ z}) (L X Y R : List V),
        q.vertices = L ++ (a :: X) ++ (b :: Y) ++ c :: R →
        G.Adj z a → G.Adj z b → G.Adj z c →
        ¬ G.Adj a b → ¬ G.Adj a c → ¬ G.Adj b c → 6 ≤ X.length + Y.length := by
  obtain ⟨z,atEnd,p,constrained⟩ :=
    E.minimum_cubic_edge_constrained_omission smaller conn cross budget order da db noTrace
  refine ⟨z,atEnd,⟨p,constrained⟩,?_⟩
  rcases atEnd with ha|hb
  · subst z
    intro a b c q L X Y R
    exact WiderOmission.sum_intervening_at_least_six budget noTrace da db E.edge q L X Y R
  · subst z
    intro a b c q L X Y R
    exact WiderOmission.sum_intervening_at_least_six budget noTrace db da E.edge.symm q L X Y R

end ContractedEdge

#print axioms WiderOmission.sum_intervening_at_least_six
#print axioms ContractedEdge.minimum_cubic_edge_total_gap_eight

end Graffiti199Depleted
