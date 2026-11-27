import PathForms
import GapSevenBound

open private positive_gaps from GapBounds

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

universe u
variable {W : Type u} {G : SimpleGraph W}
variable [DecidableEq W] [DecidableRel G.Adj] [Fintype W]

omit [DecidableEq W] [Fintype W] in
private theorem first_last {X : List W} (h : 2 ≤ X.length) :
    ∃ a U b, X = a :: (U ++ [b]) := by
  cases X with
  | nil => simp at h
  | cons a S =>
    have ne : S ≠ [] := by rintro rfl; simp at h
    exact ⟨a,S.dropLast,S.getLast ne,congrArg (List.cons a) (List.dropLast_append_getLast ne).symm⟩

omit [DecidableEq W] [Fintype W] in
private theorem first_two_last {X : List W} (h : 3 ≤ X.length) :
    ∃ a b U c, X = a :: b :: (U ++ [c]) := by
  cases X with
  | nil => simp at h
  | cons a S =>
    have lt : 2 ≤ S.length := by simp only [List.length_cons] at h; omega
    obtain ⟨b,U,c,rfl⟩ := first_last lt
    exact ⟨a,b,U,c,rfl⟩

/-- Two gaps of at least three edges force a spanning path, with no
bound on either gap length. -/
theorem traceable_of_separated_gaps (budget : Catalogue.treeNumber G ≤ 5)
    {z w a b c : W} (p : PathOn G {v | v ≠ z}) (L X Y R : List W)
    (split : p.vertices = L ++ (a :: X) ++ (b :: Y) ++ c :: R)
    (longX : 2 ≤ X.length) (longY : 2 ≤ Y.length)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c)
    (ab : ¬ G.Adj a b) (ac : ¬ G.Adj a c) (bc : ¬ G.Adj b c)
    (dz : G.degree z = 3) (dw : G.degree w = 3) (zw : G.Adj z w) :
    Catalogue.Traceable G := by
  obtain ⟨x,U,q,rfl⟩ := first_last longX
  obtain ⟨y,V,r,rfl⟩ := first_last longY
  exact traceable_of_separated_fragments budget p L U V R
    (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
    za zb zc ab ac bc dz dw zw

/-- One gap of two edges and one gap of at least four edges force a
spanning path under the archived minimum-order and cut hypotheses. -/
theorem traceable_of_short_long_gaps (budget : Catalogue.treeNumber G ≤ 5)
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card W))
    (conn : Catalogue.ConnectivityAtLeast G 3) (cross : CrossingBetweenSurvivingEdges G)
    {z w a b c : W} (p : PathOn G {v | v ≠ z}) (L X Y R : List W)
    (split : p.vertices = L ++ (a :: X) ++ (b :: Y) ++ c :: R)
    (shortX : X.length = 1) (longY : 3 ≤ Y.length)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c)
    (ab : ¬ G.Adj a b) (ac : ¬ G.Adj a c) (bc : ¬ G.Adj b c)
    (dz : G.degree z = 3) (dw : G.degree w = 3) (zw : G.Adj z w) :
    Catalogue.Traceable G := by
  obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp shortX
  obtain ⟨u,v,U,r,rfl⟩ := first_two_last longY
  exact traceable_of_short_fragments budget smaller conn cross p L U R
    (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
    za zb zc ab ac bc dz dw zw

/-- The independent-neighborhood one-omission placement is excluded
at arbitrary gap lengths in the archived minimum-order case. -/
theorem traceable_of_ordered_independent_neighbors (budget : Catalogue.treeNumber G ≤ 5)
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card W))
    (conn : Catalogue.ConnectivityAtLeast G 3) (cross : CrossingBetweenSurvivingEdges G)
    {z w a b c : W} (p : PathOn G {v | v ≠ z}) (L X Y R : List W)
    (split : p.vertices = L ++ (a :: X) ++ (b :: Y) ++ c :: R)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c)
    (ab : ¬ G.Adj a b) (ac : ¬ G.Adj a c) (bc : ¬ G.Adj b c)
    (dz : G.degree z = 3) (dw : G.degree w = 3) (zw : G.Adj z w) :
    Catalogue.Traceable G := by
  classical
  by_contra noTrace
  have ⟨px,py⟩ := positive_gaps noTrace p L X Y R split za zb zc
  have total := sum_intervening_at_least_six budget noTrace dz dw zw p L X Y R
    split za zb zc ab ac bc
  by_cases hx : X.length = 1
  · exact noTrace (traceable_of_short_long_gaps budget smaller conn cross p L X Y R split hx
      (by omega) za zb zc ab ac bc dz dw zw)
  · by_cases hy : Y.length = 1
    · have backwards : p.rev.vertices =
          R.reverse ++ (c :: Y.reverse) ++ (b :: X.reverse) ++ a :: L.reverse := by
        change p.vertices.reverse = _
        rw [split]
        simp [List.reverse_append,List.reverse_cons,List.append_assoc,List.cons_append]
      exact noTrace (traceable_of_short_long_gaps budget smaller conn cross p.rev
        R.reverse Y.reverse X.reverse L.reverse backwards (by simpa using hy)
        (by simpa only [List.length_reverse] using (show 3 ≤ X.length by omega))
        zc zb za (fun e => bc e.symm) (fun e => ac e.symm) (fun e => ab e.symm) dz dw zw)
    · exact noTrace (traceable_of_separated_gaps budget p L X Y R split (by omega) (by omega)
        za zb zc ab ac bc dz dw zw)

#print axioms traceable_of_separated_gaps
#print axioms traceable_of_ordered_independent_neighbors

end Graffiti199Depleted.WiderOmission
