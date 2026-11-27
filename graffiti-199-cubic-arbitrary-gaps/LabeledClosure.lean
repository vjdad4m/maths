import SparseTransfer
import RowsSeparated
import RowsShort
import ChartMinimum

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

universe u
variable {W : Type u} {G : SimpleGraph W}
variable [DecidableEq W] [DecidableRel G.Adj] [Fintype W]

set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
private def originSeparated : List (SegmentToken 9 2) :=
  [.vertex 0,.vertex 1,.across 0 false,.vertex 4,.across 1 false,.vertex 7,.vertex 8]

/-- Traceability with the designated internal fragments of arbitrary length. -/
theorem traceable_separated_labeled (budget : Catalogue.treeNumber G ≤ 5) (f : Fin 10 ↪ W)
    (p : PathOn G {v | v ≠ f (Fin.last 9)}) {L U V R : List W}
    (split : p.vertices = L ++ ([f 0,f 1,f 2] ++ U ++ [f 3,f 4,f 5] ++ V ++ [f 6,f 7,f 8]) ++ R)
    (ports : ∀ i, G.Adj (f (Fin.last 9)) (f (layoutSeparated.port i)))
    (ind : ∀ i j, ¬ G.Adj (f (layoutSeparated.port i)) (f (layoutSeparated.port j)))
    (dz : G.degree (f (Fin.last 9)) = 3)
    (cubic : ∃ i, G.degree (f (layoutSeparated.port i)) = 3) : Catalogue.Traceable G := by
  obtain ⟨m,dm⟩ := cubic
  let I : Fin 2 → List W := ![U,V]
  have origin : p.vertices = L ++ originSeparated.flatMap (SegmentToken.expand seamsSeparated I f) ++ R := by
    simpa [originSeparated,SegmentToken.expand,seamsSeparated,I,List.append_assoc] using split
  have inside (i : Fin 2) :
      (f (seamsSeparated i).1 :: I i ++ [f (seamsSeparated i).2]).Chain' G.Adj := by
    fin_cases i
    · change (f 2 :: U ++ [f 3]).Chain' G.Adj
      exact path_subchain (L := L ++ [f 0,f 1])
        (R := [f 4,f 5] ++ V ++ [f 6,f 7,f 8] ++ R) p
        (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
    · change (f 5 :: V ++ [f 6]).Chain' G.Adj
      exact path_subchain (L := L ++ [f 0,f 1,f 2] ++ U ++ [f 3,f 4])
        (R := [f 7,f 8] ++ R) p
        (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have around (i : Fin 3) : ∃ A B : List W,
      p.vertices = A ++ f (layoutSeparated.prev i) :: f (layoutSeparated.port i) :: f (layoutSeparated.next i) :: B := by
    fin_cases i
    · refine ⟨L,
        U ++ [f 3,f 4,f 5] ++ V ++ [f 6,f 7,f 8] ++ R,?_⟩
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
    · refine ⟨L ++ [f 0,f 1,f 2] ++ U,
        V ++ [f 6,f 7,f 8] ++ R,?_⟩
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
    · refine ⟨L ++ [f 0,f 1,f 2] ++ U ++ [f 3,f 4,f 5] ++ V,
        R,?_⟩
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
  have adj0 : G.Adj (f 0) (f 1) :=
    adjacent_on_path (L := L)
      (R := [f 2] ++ U ++ [f 3,f 4,f 5] ++ V ++ [f 6,f 7,f 8] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj1 : G.Adj (f 1) (f 2) :=
    adjacent_on_path (L := L ++ [f 0])
      (R := U ++ [f 3,f 4,f 5] ++ V ++ [f 6,f 7,f 8] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj3 : G.Adj (f 3) (f 4) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2] ++ U)
      (R := [f 5] ++ V ++ [f 6,f 7,f 8] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj4 : G.Adj (f 4) (f 5) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2] ++ U ++ [f 3])
      (R := V ++ [f 6,f 7,f 8] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj6 : G.Adj (f 6) (f 7) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2] ++ U ++ [f 3,f 4,f 5] ++ V)
      (R := [f 8] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj7 : G.Adj (f 7) (f 8) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2] ++ U ++ [f 3,f 4,f 5] ++ V ++ [f 6])
      (R := R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have positions : ∀ i j : Fin 10, i.val+1=j.val → j.val<9 → i.val∉([2,5] : List ℕ) →
      (i=0 ∧ j=1) ∨ (i=1 ∧ j=2) ∨ (i=3 ∧ j=4) ∨ (i=4 ∧ j=5) ∨ (i=6 ∧ j=7) ∨ (i=7 ∧ j=8) := by decide
  have real (i j : Fin 10) (e : i.val+1=j.val) (lt : j.val<9) (off : i.val∉([2,5] : List ℕ)) :
      G.Adj (f i) (f j) := by
    rcases positions i j e lt off with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact adj0
    · exact adj1
    · exact adj3
    · exact adj4
    · exact adj6
    · exact adj7
  apply resolve_sparse layoutSeparated m (familySeparated m) (familySeparated_consistent m)
    (residuesSeparated m) (classificationSeparated m) budget p real around ports ind dz dm
  intro tag ok chart
  exact splice_from_origin p originSeparated origin (by decide) (by decide) (by decide) (by decide)
    chart inside (certifiedRouteSeparated m ok)

#print axioms traceable_separated_labeled

private def shortFirstEmbed : Fin 9 ↪ Fin 10 :=
  ⟨![0,1,2,3,4,5,7,8,9],by
    change ∀ i j : Fin 9, (![0,1,2,3,4,5,7,8,9] : Fin 9 → Fin 10) i = ![0,1,2,3,4,5,7,8,9] j → i = j
    decide⟩

private theorem shortFirst_eq : ∀ i j, edgeShort 0 16345 (shortFirstEmbed i) (shortFirstEmbed j) =
    edge23 0 253 i j := by decide

private theorem shortSecond_eq : ∀ i j, edgeShort 1 16124 i j = edge24 1 7932 i j := by decide

private def originShort : List (SegmentToken 9 1) :=
  [.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 4,.across 0 false,.vertex 7,.vertex 8]

/-- Traceability with the designated internal fragments of arbitrary length. -/
theorem traceable_short_labeled (budget : Catalogue.treeNumber G ≤ 5) (f : Fin 10 ↪ W)
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card W))
    (conn : Catalogue.ConnectivityAtLeast G 3) (cross : CrossingBetweenSurvivingEdges G)
    (p : PathOn G {v | v ≠ f (Fin.last 9)}) {L U R : List W}
    (split : p.vertices = L ++ ([f 0,f 1,f 2,f 3,f 4,f 5] ++ U ++ [f 6,f 7,f 8]) ++ R)
    (ports : ∀ i, G.Adj (f (Fin.last 9)) (f (layoutShort.port i)))
    (ind : ∀ i j, ¬ G.Adj (f (layoutShort.port i)) (f (layoutShort.port j)))
    (dz : G.degree (f (Fin.last 9)) = 3)
    (cubic : ∃ i, G.degree (f (layoutShort.port i)) = 3) : Catalogue.Traceable G := by
  obtain ⟨m,dm⟩ := cubic
  let I : Fin 1 → List W := ![U]
  have origin : p.vertices = L ++ originShort.flatMap (SegmentToken.expand seamsShort I f) ++ R := by
    simpa [originShort,SegmentToken.expand,seamsShort,I,List.append_assoc] using split
  have inside (i : Fin 1) :
      (f (seamsShort i).1 :: I i ++ [f (seamsShort i).2]).Chain' G.Adj := by
    fin_cases i
    · change (f 5 :: U ++ [f 6]).Chain' G.Adj
      exact path_subchain (L := L ++ [f 0,f 1,f 2,f 3,f 4])
        (R := [f 7,f 8] ++ R) p
        (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have around (i : Fin 3) : ∃ A B : List W,
      p.vertices = A ++ f (layoutShort.prev i) :: f (layoutShort.port i) :: f (layoutShort.next i) :: B := by
    fin_cases i
    · refine ⟨L,
        [f 3,f 4,f 5] ++ U ++ [f 6,f 7,f 8] ++ R,?_⟩
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
    · refine ⟨L ++ [f 0,f 1],
        [f 5] ++ U ++ [f 6,f 7,f 8] ++ R,?_⟩
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
    · refine ⟨L ++ [f 0,f 1,f 2,f 3,f 4,f 5] ++ U,
        R,?_⟩
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
  have adj0 : G.Adj (f 0) (f 1) :=
    adjacent_on_path (L := L)
      (R := [f 2,f 3,f 4,f 5] ++ U ++ [f 6,f 7,f 8] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj1 : G.Adj (f 1) (f 2) :=
    adjacent_on_path (L := L ++ [f 0])
      (R := [f 3,f 4,f 5] ++ U ++ [f 6,f 7,f 8] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj2 : G.Adj (f 2) (f 3) :=
    adjacent_on_path (L := L ++ [f 0,f 1])
      (R := [f 4,f 5] ++ U ++ [f 6,f 7,f 8] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj3 : G.Adj (f 3) (f 4) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2])
      (R := [f 5] ++ U ++ [f 6,f 7,f 8] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj4 : G.Adj (f 4) (f 5) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2,f 3])
      (R := U ++ [f 6,f 7,f 8] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj6 : G.Adj (f 6) (f 7) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2,f 3,f 4,f 5] ++ U)
      (R := [f 8] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj7 : G.Adj (f 7) (f 8) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2,f 3,f 4,f 5] ++ U ++ [f 6])
      (R := R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have positions : ∀ i j : Fin 10, i.val+1=j.val → j.val<9 → i.val∉([5] : List ℕ) →
      (i=0 ∧ j=1) ∨ (i=1 ∧ j=2) ∨ (i=2 ∧ j=3) ∨ (i=3 ∧ j=4) ∨ (i=4 ∧ j=5) ∨ (i=6 ∧ j=7) ∨ (i=7 ∧ j=8) := by decide
  have real (i j : Fin 10) (e : i.val+1=j.val) (lt : j.val<9) (off : i.val∉([5] : List ℕ)) :
      G.Adj (f i) (f j) := by
    rcases positions i j e lt off with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact adj0
    · exact adj1
    · exact adj2
    · exact adj3
    · exact adj4
    · exact adj6
    · exact adj7
  apply resolve_sparse layoutShort m (familyShort m) (familyShort_consistent m)
    (residuesShort m) (classificationShort m) budget p real around ports ind dz dm
  intro tag ok chart
  rcases certifiedRouteShort m ok with res|route
  · rcases res with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact traceable_of_minimum_23_chart (shortFirstEmbed.trans f)
        (fun i j => (chart _ _).trans (by
          change edgeShort 0 16345 (shortFirstEmbed i) (shortFirstEmbed j) = true ↔ _
          rw [shortFirst_eq])) dz dm smaller conn cross budget
    · exact traceable_of_minimum_24_chart f
        (fun i j => (chart _ _).trans (by
          change edgeShort 1 16124 i j = true ↔ _
          rw [shortSecond_eq])) dz dm smaller conn cross budget
  · exact splice_from_origin p originShort origin (by decide) (by decide) (by decide) (by decide) chart inside route

#print axioms traceable_short_labeled

end Graffiti199Depleted.WiderOmission
