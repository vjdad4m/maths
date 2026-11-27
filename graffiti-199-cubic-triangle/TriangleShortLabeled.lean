import OriginFrame
import TriShortRows
import TriangleShortFlank0_93
import TriangleShortFlank0_509
import TriangleShortFlank1_472
import TriangleShortFlank1_510
import TriangleShortFlank2_752

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

variable {W : Type*} {G : SimpleGraph W} [DecidableEq W] [DecidableRel G.Adj] [Fintype W]
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

private def origin : List (SegmentToken 8 1) :=
  [.vertex 0,.vertex 1,.vertex 2,.vertex 3,.across 0 false,.vertex 6,.vertex 7]

theorem traceable_triangle_short_labeled (budget : Catalogue.treeNumber G ≤ 5)
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (f : Fin 9 ↪ W) (p : PathOn G {v | v ≠ f (Fin.last 8)}) {L U R : List W}
    (split : p.vertices = L ++ ([f 0,f 1,f 2,f 3,f 4] ++ U ++ [f 5,f 6,f 7]) ++ R)
    (ports : ∀ i, G.Adj (f (Fin.last 8)) (f (layoutTriShort.port i)))
    (dz : G.degree (f (Fin.last 8)) = 3) (m : Fin 3)
    (dm : G.degree (f (layoutTriShort.port m)) = 3)
    (tri : ∀ i j, i ≠ j → i ≠ m → j ≠ m → G.Adj (f (layoutTriShort.port i)) (f (layoutTriShort.port j))) :
    Catalogue.Traceable G := by
  let I : Fin 1 → List W := ![U]
  have originEq : p.vertices = L ++ origin.flatMap (SegmentToken.expand seamsTriShort I f) ++ R := by
    simpa [origin,SegmentToken.expand,seamsTriShort,I,List.append_assoc] using split
  have inside (i : Fin 1) :
      (f (seamsTriShort i).1 :: I i ++ [f (seamsTriShort i).2]).Chain' G.Adj := by
    have eq : i = 0 := Subsingleton.elim _ _
    subst i
    change (f 4 :: U ++ [f 5]).Chain' G.Adj
    exact path_subchain (L := L ++ [f 0,f 1,f 2,f 3]) (R := [f 6,f 7] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have around (i : Fin 3) : ∃ A B : List W,
      p.vertices = A ++ f (layoutTriShort.prev i) :: f (layoutTriShort.port i) :: f (layoutTriShort.next i) :: B := by
    fin_cases i
    · exact ⟨L, [f 3,f 4] ++ U ++ [f 5,f 6,f 7] ++ R, by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using split⟩
    · exact ⟨L ++ [f 0,f 1], U ++ [f 5,f 6,f 7] ++ R, by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using split⟩
    · exact ⟨L ++ [f 0,f 1,f 2,f 3,f 4] ++ U, R, by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using split⟩
  have adj0 : G.Adj (f 0) (f 1) :=
    adjacent_on_path (L := L) (R := [f 2,f 3,f 4] ++ U ++ [f 5,f 6,f 7] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj1 : G.Adj (f 1) (f 2) :=
    adjacent_on_path (L := L ++ [f 0]) (R := [f 3,f 4] ++ U ++ [f 5,f 6,f 7] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj2 : G.Adj (f 2) (f 3) :=
    adjacent_on_path (L := L ++ [f 0,f 1]) (R := [f 4] ++ U ++ [f 5,f 6,f 7] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj3 : G.Adj (f 3) (f 4) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2]) (R := U ++ [f 5,f 6,f 7] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj5 : G.Adj (f 5) (f 6) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2,f 3,f 4] ++ U) (R := [f 7] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj6 : G.Adj (f 6) (f 7) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2,f 3,f 4] ++ U ++ [f 5]) (R := R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have pos : ∀ i j : Fin 9, i.val+1=j.val → j.val<8 → i.val∉([4] : List ℕ) →
      (i=0 ∧ j=1) ∨ (i=1 ∧ j=2) ∨ (i=2 ∧ j=3) ∨ (i=3 ∧ j=4) ∨ (i=5 ∧ j=6) ∨ (i=6 ∧ j=7) := by decide
  have real (i j : Fin 9) (e : i.val+1=j.val) (lt : j.val<8) (off : i.val∉([4] : List ℕ)) :
      G.Adj (f i) (f j) := by
    rcases pos i j e lt off with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact adj0
    · exact adj1
    · exact adj2
    · exact adj3
    · exact adj5
    · exact adj6
  apply resolve_triangle layoutTriShort m (familyTriShort m) (consistentTriShort m)
    (residuesTriShort m) (classifyTriShort m) budget p real around ports tri dz dm
  intro tag valid chart
  rcases routedTriShort m valid with route|exception
  · exact splice_from_origin p origin originEq (by decide) (by decide) (by decide) (by decide)
      chart inside route
  · obtain ⟨off,pre,suc⟩ := triangle_frame_facts layoutTriShort m p around ports dz dm
    let F := frame_of_origin p origin (by decide) (by decide) (by decide) (by decide)
      chart inside off pre suc
    change tag ∈ _ at exception
    fin_cases m
    · have cases : tag = 93 ∨ tag = 509 := by
        change tag ∈ [93,509] at exception
        simpa only [List.mem_cons,List.not_mem_nil,or_false] using exception
      rcases cases with rfl|rfl
      · exact traceable_of_fragment_flanks F budget TriangleShortFlank0_93.rule L R
          (by simpa only [F,frame_of_origin,List.append_assoc] using originEq)
      · exact traceable_of_fragment_flanks F budget TriangleShortFlank0_509.rule L R
          (by simpa only [F,frame_of_origin,List.append_assoc] using originEq)
    · have cases : tag = 472 ∨ tag = 510 := by
        change tag ∈ [472,510] at exception
        simpa only [List.mem_cons,List.not_mem_nil,or_false] using exception
      rcases cases with rfl|rfl
      · exfalso
        apply contradiction_of_triangle_cut TriangleShortFlank1_472.rule budget
          (fun D h => (conn.2 D h).preconnected) chart off (by decide) (by decide) (by decide)
        decide +kernel
      · exact traceable_of_fragment_flanks F budget TriangleShortFlank1_510.rule L R
          (by simpa only [F,frame_of_origin,List.append_assoc] using originEq)
    · have cases : tag = 752 := by
        change tag ∈ [752] at exception
        simpa only [List.mem_cons,List.not_mem_nil,or_false] using exception
      subst tag
      exact traceable_of_fragment_flanks F budget TriangleShortFlank2_752.rule L R
        (by simpa only [F,frame_of_origin,List.append_assoc] using originEq)

#print axioms traceable_triangle_short_labeled

end Graffiti199Depleted.WiderOmission
