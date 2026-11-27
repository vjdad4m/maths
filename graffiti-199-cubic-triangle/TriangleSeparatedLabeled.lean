import OriginFrame
import TriSeparatedRows
import TriangleSeparatedFlank0_53579
import TriangleSeparatedFlank0_66049
import TriangleSeparatedFlank1_67585
import TriangleSeparatedFlank1_39100
import TriangleSeparatedFlank2_91088
import TriangleSeparatedFlank2_67585

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

variable {W : Type*} {G : SimpleGraph W} [DecidableEq W] [DecidableRel G.Adj] [Fintype W]
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

private def origin : List (SegmentToken 9 2) :=
  [.vertex 0,.vertex 1,.across 0 false,.vertex 4,.across 1 false,.vertex 7,.vertex 8]

theorem traceable_triangle_separated_labeled (budget : Catalogue.treeNumber G ≤ 5)
    (f : Fin 10 ↪ W) (p : PathOn G {v | v ≠ f (Fin.last 9)}) {L U V R : List W}
    (split : p.vertices = L ++ ([f 0,f 1,f 2] ++ U ++ [f 3,f 4,f 5] ++ V ++ [f 6,f 7,f 8]) ++ R)
    (ports : ∀ i, G.Adj (f (Fin.last 9)) (f (layoutTriSeparated.port i)))
    (dz : G.degree (f (Fin.last 9)) = 3) (m : Fin 3)
    (dm : G.degree (f (layoutTriSeparated.port m)) = 3)
    (tri : ∀ i j, i ≠ j → i ≠ m → j ≠ m → G.Adj (f (layoutTriSeparated.port i)) (f (layoutTriSeparated.port j))) :
    Catalogue.Traceable G := by
  let I : Fin 2 → List W := ![U,V]
  have originEq : p.vertices = L ++ origin.flatMap (SegmentToken.expand seamsTriSeparated I f) ++ R := by
    simpa [origin,SegmentToken.expand,seamsTriSeparated,I,List.append_assoc] using split
  have inside (i : Fin 2) :
      (f (seamsTriSeparated i).1 :: I i ++ [f (seamsTriSeparated i).2]).Chain' G.Adj := by
    fin_cases i
    · change (f 2 :: U ++ [f 3]).Chain' G.Adj
      exact path_subchain (L := L ++ [f 0,f 1]) (R := [f 4,f 5] ++ V ++ [f 6,f 7,f 8] ++ R) p
        (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
    · change (f 5 :: V ++ [f 6]).Chain' G.Adj
      exact path_subchain (L := L ++ [f 0,f 1,f 2] ++ U ++ [f 3,f 4]) (R := [f 7,f 8] ++ R) p
        (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have around (i : Fin 3) : ∃ A B : List W,
      p.vertices = A ++ f (layoutTriSeparated.prev i) :: f (layoutTriSeparated.port i) :: f (layoutTriSeparated.next i) :: B := by
    fin_cases i
    · exact ⟨L, U ++ [f 3,f 4,f 5] ++ V ++ [f 6,f 7,f 8] ++ R, by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using split⟩
    · exact ⟨L ++ [f 0,f 1,f 2] ++ U, V ++ [f 6,f 7,f 8] ++ R, by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using split⟩
    · exact ⟨L ++ [f 0,f 1,f 2] ++ U ++ [f 3,f 4,f 5] ++ V, R, by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using split⟩
  have adj0 : G.Adj (f 0) (f 1) :=
    adjacent_on_path (L := L) (R := [f 2] ++ U ++ [f 3,f 4,f 5] ++ V ++ [f 6,f 7,f 8] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj1 : G.Adj (f 1) (f 2) :=
    adjacent_on_path (L := L ++ [f 0]) (R := U ++ [f 3,f 4,f 5] ++ V ++ [f 6,f 7,f 8] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj3 : G.Adj (f 3) (f 4) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2] ++ U) (R := [f 5] ++ V ++ [f 6,f 7,f 8] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj4 : G.Adj (f 4) (f 5) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2] ++ U ++ [f 3]) (R := V ++ [f 6,f 7,f 8] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj6 : G.Adj (f 6) (f 7) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2] ++ U ++ [f 3,f 4,f 5] ++ V) (R := [f 8] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj7 : G.Adj (f 7) (f 8) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2] ++ U ++ [f 3,f 4,f 5] ++ V ++ [f 6]) (R := R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have pos : ∀ i j : Fin 10, i.val+1=j.val → j.val<9 → i.val∉([2,5] : List ℕ) →
      (i=0 ∧ j=1) ∨ (i=1 ∧ j=2) ∨ (i=3 ∧ j=4) ∨ (i=4 ∧ j=5) ∨ (i=6 ∧ j=7) ∨ (i=7 ∧ j=8) := by decide
  have real (i j : Fin 10) (e : i.val+1=j.val) (lt : j.val<9) (off : i.val∉([2,5] : List ℕ)) :
      G.Adj (f i) (f j) := by
    rcases pos i j e lt off with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact adj0
    · exact adj1
    · exact adj3
    · exact adj4
    · exact adj6
    · exact adj7
  apply resolve_triangle_routed layoutTriSeparated m (familyTriSeparated m) (consistentTriSeparated m)
    (exceptionalSeparated m) (classifyTriSeparated m) budget p real around ports tri dz dm
  · intro _ _ chart route
    exact splice_from_origin p origin originEq (by decide) (by decide) (by decide) (by decide)
      chart inside route
  · intro tag exception chart
    obtain ⟨off,pre,suc⟩ := triangle_frame_facts layoutTriSeparated m p around ports dz dm
    let F := frame_of_origin p origin (by decide) (by decide) (by decide) (by decide)
      chart inside off pre suc
    change tag ∈ _ at exception
    fin_cases m
    · have cases : tag = 53579 ∨ tag = 66049 := by
        change tag ∈ [53579,66049] at exception
        simpa only [List.mem_cons,List.not_mem_nil,or_false] using exception
      rcases cases with rfl|rfl
      · exact traceable_of_fragment_flanks F budget TriangleSeparatedFlank0_53579.rule L R
          (by simpa only [F,frame_of_origin,List.append_assoc] using originEq)
      · exact traceable_of_fragment_flanks F budget TriangleSeparatedFlank0_66049.rule L R
          (by simpa only [F,frame_of_origin,List.append_assoc] using originEq)
    · have cases : tag = 67585 ∨ tag = 39100 := by
        change tag ∈ [67585,39100] at exception
        simpa only [List.mem_cons,List.not_mem_nil,or_false] using exception
      rcases cases with rfl|rfl
      · exact traceable_of_fragment_flanks F budget TriangleSeparatedFlank1_67585.rule L R
          (by simpa only [F,frame_of_origin,List.append_assoc] using originEq)
      · exact traceable_of_fragment_flanks F budget TriangleSeparatedFlank1_39100.rule L R
          (by simpa only [F,frame_of_origin,List.append_assoc] using originEq)
    · have cases : tag = 91088 ∨ tag = 67585 := by
        change tag ∈ [91088,67585] at exception
        simpa only [List.mem_cons,List.not_mem_nil,or_false] using exception
      rcases cases with rfl|rfl
      · exact traceable_of_fragment_flanks F budget TriangleSeparatedFlank2_91088.rule L R
          (by simpa only [F,frame_of_origin,List.append_assoc] using originEq)
      · exact traceable_of_fragment_flanks F budget TriangleSeparatedFlank2_67585.rule L R
          (by simpa only [F,frame_of_origin,List.append_assoc] using originEq)

#print axioms traceable_triangle_separated_labeled

end Graffiti199Depleted.WiderOmission
