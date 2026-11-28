import SixSingletonQ1Slots189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair PortCertificates
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

def Q1EdgeList : List (Fin 6×Fin 6) :=
  [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

def Q1Pairs (f : Fin 6→V) (i : ℕ) : Bool :=
  match Q1EdgeList[i]? with
  | some (a,b) => decide (G.Adj (f a) (f b))
  | none => false

private theorem score_list (u : V) (l : List V) (nodup : l.Nodup) :
    (inside G l.toFinset u).card=(l.map (fun t=>marks (decide (G.Adj u t)))).sum := by
  induction l with
  | nil => simp [inside]
  | cons v l ih =>
    have nn := List.nodup_cons.mp nodup
    rw [List.toFinset_cons,inside_insert_score (G:=G) (by simpa using nn.1),ih nn.2]
    simp [Nat.add_comm]

private theorem mark_symm (u v : V) :
    marks (decide (G.Adj u v))=marks (decide (G.Adj v u)) := by
  have d : decide (G.Adj u v)=decide (G.Adj v u) := by
    congr 1
    exact propext ⟨Adj.symm,Adj.symm⟩
  exact congrArg marks d

theorem q1_port_scores (f : Fin 6→V) (inj : Function.Injective f) (P : Finset V)
    (image : univ.image f=P) :
    let B := Q1Pairs (G:=G) f
    (inside G P (f 0)).card=marks (B 0)+marks (B 1)+marks (B 2)+marks (B 3)+marks (B 4) ∧
    (inside G P (f 1)).card=marks (B 0)+marks (B 5)+marks (B 6)+marks (B 7)+marks (B 8) ∧
    (inside G P (f 2)).card=marks (B 1)+marks (B 5)+marks (B 9)+marks (B 10)+marks (B 11) ∧
    (inside G P (f 3)).card=marks (B 2)+marks (B 6)+marks (B 9)+marks (B 12)+marks (B 13) ∧
    (inside G P (f 4)).card=marks (B 3)+marks (B 7)+marks (B 10)+marks (B 12)+marks (B 14) ∧
    (inside G P (f 5)).card=marks (B 4)+marks (B 8)+marks (B 11)+marks (B 13)+marks (B 14) := by
  let L : List (Fin 6) := [0,1,2,3,4,5]
  have disp : (L.map f).toFinset=P := by
    rw [←image]
    ext x
    rw [List.mem_toFinset,List.mem_map,mem_image]
    have hall : ∀ j : Fin 6,j∈L := by decide
    exact ⟨fun ⟨j,_,e⟩=>⟨j,mem_univ _,e⟩,fun ⟨j,_,e⟩=>⟨j,hall j,e⟩⟩
  have nodup : (L.map f).Nodup := (show L.Nodup by decide).map inj
  have e := fun u=>score_list (G:=G) u _ nodup
  rw [disp] at e
  simp only [L,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at e
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals simp only [Q1Pairs,Q1EdgeList,List.getElem?_cons_zero,List.getElem?_cons_succ]
  · simpa [marks, G.loopless, Nat.add_assoc] using e (f 0)
  · rw [mark_symm (G:=G) (f 0) (f 1)]
    simpa [marks, G.loopless, Nat.add_assoc] using e (f 1)
  · rw [mark_symm (G:=G) (f 0) (f 2),mark_symm (G:=G) (f 1) (f 2)]
    simpa [marks, G.loopless, Nat.add_assoc] using e (f 2)
  · rw [mark_symm (G:=G) (f 0) (f 3),mark_symm (G:=G) (f 1) (f 3),mark_symm (G:=G) (f 2) (f 3)]
    simpa [marks, G.loopless, Nat.add_assoc] using e (f 3)
  · rw [mark_symm (G:=G) (f 0) (f 4),mark_symm (G:=G) (f 1) (f 4),mark_symm (G:=G) (f 2) (f 4),
      mark_symm (G:=G) (f 3) (f 4)]
    simpa [marks, G.loopless, Nat.add_assoc] using e (f 4)
  · rw [mark_symm (G:=G) (f 0) (f 5),mark_symm (G:=G) (f 1) (f 5),mark_symm (G:=G) (f 2) (f 5),
      mark_symm (G:=G) (f 3) (f 5),mark_symm (G:=G) (f 4) (f 5)]
    simpa [marks, G.loopless, Nat.add_assoc] using e (f 5)

theorem q1_z_score (f : Fin 6→V) (inj : Function.Injective f) (P : Finset V)
    (image : univ.image f=P) (z : V) :
    (inside G P z).card = marks (decide (G.Adj (f 0) z)) + marks (decide (G.Adj (f 1) z)) +
       marks (decide (G.Adj (f 2) z)) + marks (decide (G.Adj (f 3) z)) +
       marks (decide (G.Adj (f 4) z)) + marks (decide (G.Adj (f 5) z)) := by
  let L : List (Fin 6) := [0,1,2,3,4,5]
  have disp : (L.map f).toFinset=P := by
    rw [←image]
    ext x
    rw [List.mem_toFinset,List.mem_map,mem_image]
    have hall : ∀ j : Fin 6,j∈L := by decide
    exact ⟨fun ⟨j,_,e⟩=>⟨j,mem_univ _,e⟩,fun ⟨j,_,e⟩=>⟨j,hall j,e⟩⟩
  have nodup : (L.map f).Nodup := (show L.Nodup by decide).map inj
  have e := score_list (G:=G) z _ nodup
  rw [disp] at e
  simp only [L,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at e
  rw [mark_symm (G:=G) (f 0) z,mark_symm (G:=G) (f 1) z,mark_symm (G:=G) (f 2) z,
      mark_symm (G:=G) (f 3) z,mark_symm (G:=G) (f 4) z,mark_symm (G:=G) (f 5) z]
  simpa only [Nat.add_assoc] using e

#print axioms q1_port_scores
#print axioms q1_z_score

end Graffiti189LongestPath.CrossSaturation.ThresholdSix
