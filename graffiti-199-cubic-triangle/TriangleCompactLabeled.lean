import OriginFrame
import TriCompactRows
import TriangleCompactFlank0_31
import TriangleCompactFlank1_20
import TriangleCompactFlank1_11
import TriangleCompactFlank1_27
import TriangleCompactFlank1_15
import TriangleCompactFlank1_31
import TriangleCompactFlank2_31

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

variable {W : Type*} {G : SimpleGraph W} [DecidableEq W] [DecidableRel G.Adj] [Fintype W]
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

private def origin : List (SegmentToken 7 0) :=
  [.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 4,.vertex 5,.vertex 6]

theorem traceable_triangle_compact_labeled (budget : Catalogue.treeNumber G ≤ 5)
    (conn : Catalogue.ConnectivityAtLeast G 3)
    (f : Fin 8 ↪ W) (p : PathOn G {v | v ≠ f (Fin.last 7)}) {L R : List W}
    (split : p.vertices = L ++ ([f 0,f 1,f 2,f 3,f 4,f 5,f 6]) ++ R)
    (ports : ∀ i, G.Adj (f (Fin.last 7)) (f (layoutTriCompact.port i)))
    (dz : G.degree (f (Fin.last 7)) = 3) (m : Fin 3)
    (dm : G.degree (f (layoutTriCompact.port m)) = 3)
    (tri : ∀ i j, i ≠ j → i ≠ m → j ≠ m → G.Adj (f (layoutTriCompact.port i)) (f (layoutTriCompact.port j))) :
    Catalogue.Traceable G := by
  let I : Fin 0 → List W := Fin.elim0
  have originEq : p.vertices = L ++ origin.flatMap (SegmentToken.expand seamsTriCompact I f) ++ R := by
    simpa [origin,SegmentToken.expand,seamsTriCompact,List.append_assoc] using split
  have inside (i : Fin 0) :
      (f (seamsTriCompact i).1 :: I i ++ [f (seamsTriCompact i).2]).Chain' G.Adj := by
    exact Fin.elim0 i
  have around (i : Fin 3) : ∃ A B : List W,
      p.vertices = A ++ f (layoutTriCompact.prev i) :: f (layoutTriCompact.port i) :: f (layoutTriCompact.next i) :: B := by
    fin_cases i
    · exact ⟨L, [f 3,f 4,f 5,f 6] ++ R, by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using split⟩
    · exact ⟨L ++ [f 0,f 1], [f 5,f 6] ++ R, by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using split⟩
    · exact ⟨L ++ [f 0,f 1,f 2,f 3], R, by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using split⟩
  have adj0 : G.Adj (f 0) (f 1) :=
    adjacent_on_path (L := L) (R := [f 2,f 3,f 4,f 5,f 6] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj1 : G.Adj (f 1) (f 2) :=
    adjacent_on_path (L := L ++ [f 0]) (R := [f 3,f 4,f 5,f 6] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj2 : G.Adj (f 2) (f 3) :=
    adjacent_on_path (L := L ++ [f 0,f 1]) (R := [f 4,f 5,f 6] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj3 : G.Adj (f 3) (f 4) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2]) (R := [f 5,f 6] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj4 : G.Adj (f 4) (f 5) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2,f 3]) (R := [f 6] ++ R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have adj5 : G.Adj (f 5) (f 6) :=
    adjacent_on_path (L := L ++ [f 0,f 1,f 2,f 3,f 4]) (R := R) p
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split)
  have pos : ∀ i j : Fin 8, i.val+1=j.val → j.val<7 → i.val∉([] : List ℕ) →
      (i=0 ∧ j=1) ∨ (i=1 ∧ j=2) ∨ (i=2 ∧ j=3) ∨ (i=3 ∧ j=4) ∨ (i=4 ∧ j=5) ∨ (i=5 ∧ j=6) := by decide
  have real (i j : Fin 8) (e : i.val+1=j.val) (lt : j.val<7) (off : i.val∉([] : List ℕ)) :
      G.Adj (f i) (f j) := by
    rcases pos i j e lt off with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact adj0
    · exact adj1
    · exact adj2
    · exact adj3
    · exact adj4
    · exact adj5
  apply resolve_triangle layoutTriCompact m (familyTriCompact m) (consistentTriCompact m)
    (residuesTriCompact m) (classifyTriCompact m) budget p real around ports tri dz dm
  intro tag valid chart
  rcases routedTriCompact m valid with route|exception
  · exact splice_from_origin p origin originEq (by decide) (by decide) (by decide) (by decide)
      chart inside route
  · obtain ⟨off,pre,suc⟩ := triangle_frame_facts layoutTriCompact m p around ports dz dm
    let F := frame_of_origin p origin (by decide) (by decide) (by decide) (by decide)
      chart inside off pre suc
    change tag ∈ _ at exception
    fin_cases m
    · have cases : tag = 31 := by
        change tag ∈ [31] at exception
        simpa only [List.mem_cons,List.not_mem_nil,or_false] using exception
      subst tag
      exact traceable_of_fragment_flanks F budget TriangleCompactFlank0_31.rule L R
        (by simpa only [F,frame_of_origin,List.append_assoc] using originEq)
    · have cases : tag = 20 ∨ tag = 11 ∨ tag = 27 ∨ tag = 15 ∨ tag = 31 := by
        change tag ∈ [20,11,27,15,31] at exception
        simpa only [List.mem_cons,List.not_mem_nil,or_false] using exception
      rcases cases with rfl|rfl|rfl|rfl|rfl
      · exfalso
        apply contradiction_of_triangle_cut TriangleCompactFlank1_20.rule budget
          (fun D h => (conn.2 D h).preconnected) chart off (by decide) (by decide) (by decide)
        decide +kernel
      · exact traceable_of_fragment_flanks F budget TriangleCompactFlank1_11.rule L R
          (by simpa only [F,frame_of_origin,List.append_assoc] using originEq)
      · exact traceable_of_fragment_flanks F budget TriangleCompactFlank1_27.rule L R
          (by simpa only [F,frame_of_origin,List.append_assoc] using originEq)
      · exact traceable_of_fragment_flanks F budget TriangleCompactFlank1_15.rule L R
          (by simpa only [F,frame_of_origin,List.append_assoc] using originEq)
      · exact traceable_of_fragment_flanks F budget TriangleCompactFlank1_31.rule L R
          (by simpa only [F,frame_of_origin,List.append_assoc] using originEq)
    · have cases : tag = 31 := by
        change tag ∈ [31] at exception
        simpa only [List.mem_cons,List.not_mem_nil,or_false] using exception
      subst tag
      exact traceable_of_fragment_flanks F budget TriangleCompactFlank2_31.rule L R
        (by simpa only [F,frame_of_origin,List.append_assoc] using originEq)

#print axioms traceable_triangle_compact_labeled

end Graffiti199Depleted.WiderOmission
