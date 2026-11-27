import InducedBudget
import UniformProfiles
import Rows25
import Conclusion24

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private def smallA25 : Fin 9 ↪ Fin 11 :=
  ⟨![0,1,2,3,6,7,8,9,10],by
    change ∀ i j : Fin 9,
      (![0,1,2,3,6,7,8,9,10] : Fin 9 → Fin 11) i = ![0,1,2,3,6,7,8,9,10] j → i = j
    decide⟩

private def smallB25 : Fin 10 ↪ Fin 11 :=
  ⟨![0,1,2,3,4,6,7,8,9,10],by
    change ∀ i j : Fin 10,
      (![0,1,2,3,4,6,7,8,9,10] : Fin 10 → Fin 11) i = ![0,1,2,3,4,6,7,8,9,10] j → i = j
    decide⟩

private theorem smallA25_edge : ∀ i j, edge25 0 786225 (smallA25 i) (smallA25 j) = edge23 0 253 i j := by
  decide

private theorem smallB25_edge : ∀ i j, edge25 1 783352 (smallB25 i) (smallB25 j) = edge24 1 7932 i j := by
  decide

theorem twins_of_first25 (f : Fin 11 ↪ V) (budget : Catalogue.treeNumber G ≤ 5)
    (chart : ∀ i j, G.Adj (f i) (f j) ↔ edge25 0 786225 i j = true)
    (dz : G.degree (f 10) = 3) (dm : G.degree (f 1) = 3) :
    AdjacentTwins G (f 6) (f 7) :=
  twins_from_23_chart (smallA25.trans f) budget
    (fun i j => (chart _ _).trans (by rw [smallA25_edge i j])) dz dm

theorem twins_of_second25 (f : Fin 11 ↪ V) (budget : Catalogue.treeNumber G ≤ 5)
    (chart : ∀ i j, G.Adj (f i) (f j) ↔ edge25 1 783352 i j = true)
    (dz : G.degree (f 10) = 3) (dm : G.degree (f 3) = 3) :
    AdjacentTwins G (f 6) (f 7) :=
  twins_from_24_chart (smallB25.trans f) budget
    (fun i j => (chart _ _).trans (by rw [smallB25_edge i j])) dz dm

private def retain25 : Fin 10 ↪ Fin 11 :=
  ⟨![0,1,2,3,4,5,7,8,9,10],by
    change ∀ i j : Fin 10,
      (![0,1,2,3,4,5,7,8,9,10] : Fin 10 → Fin 11) i = ![0,1,2,3,4,5,7,8,9,10] j → i = j
    decide⟩

private theorem retain25_off : ∀ i, retain25 i ≠ 6 := by decide

/-- Deleting a twin on the long flank of the placement preserves both
cubic degrees and reduces this shape to the checked 2-and-4 case. -/
theorem traceable_of_twins25
    (budget : Catalogue.treeNumber G ≤ 5) (f : Fin 11 ↪ V) (m : Fin 3)
    (p : PathOn G {v | v ≠ f (Fin.last 10)}) {L R : List V}
    (split : p.vertices = L ++ block f ++ R)
    (tw : AdjacentTwins G (f 6) (f 7))
    (ports : ∀ i, G.Adj (f (Fin.last 10)) (f (layout25.port i)))
    (ind : ∀ i j, ¬ G.Adj (f (layout25.port i)) (f (layout25.port j)))
    (dz : G.degree (f (Fin.last 10)) = 3) (dm : G.degree (f (layout25.port m)) = 3)
    (offZ : ¬ G.Adj (f (Fin.last 10)) (f 6))
    (offM : ¬ G.Adj (f (layout25.port m)) (f 6)) : Catalogue.Traceable G := by
  classical
  let S : Set V := {x | x ≠ f 6}
  let H := G.induce S
  let g : Fin 10 ↪ S :=
    ⟨fun i => ⟨f (retain25 i), f.injective.ne (retain25_off i)⟩,
      fun _ _ eq => retain25.injective (f.injective (congrArg (fun x : S => x.val) eq))⟩
  have old : p.vertices = (L ++ [f 0,f 1,f 2,f 3,f 4,f 5]) ++ f 6 :: f 7 :: ([f 8,f 9] ++ R) := by
    have h : block f = [f 0,f 1,f 2,f 3,f 4,f 5,f 6,f 7,f 8,f 9] := rfl
    simpa only [h,List.append_assoc,List.cons_append,List.nil_append] using split
  obtain ⟨q,qs⟩ := p.delete_before_twin tw old
  have coreMap : (block g).map (fun x : S => x.val) =
      [f 0,f 1,f 2,f 3,f 4,f 5,f 7,f 8,f 9] := rfl
  have qs' : q.vertices = L ++ (block g).map (fun x : S => x.val) ++ R := by
    simpa only [coreMap,List.append_assoc,List.cons_append,List.nil_append] using qs
  have memberLeft (x : V) (hx : x ∈ L) : x ∈ S := by
    apply ((q.covers x).mp ?_).2
    rw [qs']
    simp [hx]
  have memberRight (x : V) (hx : x ∈ R) : x ∈ S := by
    apply ((q.covers x).mp ?_).2
    rw [qs']
    simp [hx]
  let l : List S := L.attachWith (· ∈ S) memberLeft
  let r : List S := R.attachWith (· ∈ S) memberRight
  obtain ⟨s,sm⟩ := q.induce_restrict (T := S) (fun _ h => h.2)
  have sv : s.vertices = l ++ block g ++ r := by
    apply Subtype.val_injective.list_map
    rw [sm,List.map_append,List.map_append,List.attachWith_map_subtype_val memberLeft,
      List.attachWith_map_subtype_val memberRight,qs']
  have cover (x : S) : x ∈ s.vertices ↔ x ≠ g (Fin.last 9) := by
    rw [s.covers]
    change (x.val ≠ f (Fin.last 10) ∧ x.val ≠ f 6) ↔ x ≠ g (Fin.last 9)
    exact ⟨fun h e => h.1 (congrArg (fun x : S => x.val) e),
      fun h => ⟨fun eq => h (Subtype.ext eq),x.property⟩⟩
  let hpath : PathOn H {x | x ≠ g (Fin.last 9)} :=
    ⟨s.vertices,s.nonempty,s.chain,s.nodup,cover⟩
  have redBudget : Catalogue.treeNumber H ≤ 5 := (Catalogue.treeNumber_induce_le (G := G) S).trans budget
  have portEq (i : Fin 3) : (g (layout24.port i)).val = f (layout25.port i) := by
    fin_cases i <;> rfl
  have zH : H.degree (g (Fin.last 9)) = 3 := by
    have keep := Catalogue.degree_delete_nonneighbor (G := G) (g (Fin.last 9)).property offZ
    exact keep.trans dz
  have mateH : H.degree (g (layout24.port m)) = 3 := by
    have keep := Catalogue.degree_delete_nonneighbor (G := G) (g (layout24.port m)).property
      (by simpa only [portEq m] using offM)
    refine keep.trans ?_
    rw [portEq m,dm]
  apply tw.traceable_of_delete
  apply traceable_of_layout24 redBudget g hpath sv
  · intro i
    change G.Adj (f (Fin.last 10)) (g (layout24.port i)).val
    rw [portEq]
    exact ports i
  · intro i j
    change ¬ G.Adj (g (layout24.port i)).val (g (layout24.port j)).val
    rw [portEq,portEq]
    exact ind i j
  · exact zH
  · exact ⟨m,mateH⟩

#print axioms twins_of_first25
#print axioms twins_of_second25
#print axioms traceable_of_twins25

end Graffiti199Depleted.WiderOmission
