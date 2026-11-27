import ExampleBase180
import LeafPatterns180
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option warningAsError true
set_option compiler.extract_closed false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Minimal180.Case12
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180
private noncomputable def pat0 : LeafPattern V := ⟨{10,11},6,1,{0,4,5,6,9}⟩
private noncomputable def pat1 : LeafPattern V := ⟨{1,11},6,3,{0,2,4,5,6,7,9,10}⟩
private noncomputable def pat2 : LeafPattern V := ⟨{1,3},6,8,{0,2,4,5,6,7,9,10,11}⟩
private noncomputable def pat3 : LeafPattern V := ⟨{7,8},6,1,{0,2,3,4,5,6,9,10,11}⟩
private noncomputable def pat4 : LeafPattern V := ⟨{2,8},6,7,{0,3,4,5,6,9,10,11}⟩
private noncomputable def pat5 : LeafPattern V := ⟨{1,7,8},1,1,∅⟩
private noncomputable def pat6 : LeafPattern V := ⟨{3,7},6,1,{0,2,4,5,6,9,10,11}⟩
private noncomputable def pat7 : LeafPattern V := ⟨{0,4,5},6,9,{1,2,3,6,7,8,10,11}⟩
private noncomputable def pat8 : LeafPattern V := ⟨{1,3,8},8,8,∅⟩
private noncomputable def pat9 : LeafPattern V := ⟨{2,7,10},2,2,∅⟩
private noncomputable def pat10 : LeafPattern V := ⟨{2,11},6,1,{0,4,5,6,9,10}⟩
private noncomputable def pat11 : LeafPattern V := ⟨{8,10},6,2,{0,3,4,5,6,9,11}⟩
private noncomputable def pat12 : LeafPattern V := ⟨{3,8,11},3,3,∅⟩
private noncomputable def pat13 : LeafPattern V := ⟨{1,2,7},7,7,∅⟩
private noncomputable def pat14 : LeafPattern V := ⟨{1,7,10},3,2,{0,3,4,5,6,8,9,11}⟩
private noncomputable def pat15 : LeafPattern V := ⟨{2,3,10},6,1,{0,4,5,6,9,11}⟩
private noncomputable def pat16 : LeafPattern V := ⟨{1,2,10},3,7,{0,3,4,5,6,8,9,11}⟩
private noncomputable def patterns : List (LeafPattern V) := [pat0,pat1,pat2,pat3,pat4,pat5,pat6,pat7,pat8,pat9,pat10,pat11,pat12,pat13,pat14,pat15,pat16]

private theorem valid0 : pat0.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid1 : pat1.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid2 : pat2.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid3 : pat3.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid4 : pat4.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid5 : pat5.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid6 : pat6.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid7 : pat7.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid8 : pat8.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid9 : pat9.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid10 : pat10.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid11 : pat11.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid12 : pat12.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid13 : pat13.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid14 : pat14.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid15 : pat15.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid16 : pat16.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid_patterns (p:LeafPattern V) (hp:p∈patterns) : p.valid oldEdges := by
  simp only [patterns,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact valid0
  · exact valid1
  · exact valid2
  · exact valid3
  · exact valid4
  · exact valid5
  · exact valid6
  · exact valid7
  · exact valid8
  · exact valid9
  · exact valid10
  · exact valid11
  · exact valid12
  · exact valid13
  · exact valid14
  · exact valid15
  · exact valid16

private noncomputable def tally (v0 v1 v2 v3 v4 v5 v7 v8 v10 v11:Bool) : ℕ := (if v0 then 1 else 0)+((if v1 then 1 else 0)+((if v2 then 1 else 0)+((if v3 then 1 else 0)+((if v4 then 1 else 0)+((if v5 then 1 else 0)+((if v7 then 1 else 0)+((if v8 then 1 else 0)+((if v10 then 1 else 0)+(if v11 then 1 else 0)))))))))
private noncomputable def options (v0 v1 v2 v3 v4 v5 v7 v8 v10 v11:Bool) : Prop :=
  ((v10=true ∧ v11=true) ∧ (True ∧ v1=false)) ∨
  ((v1=true ∧ v11=true) ∧ (True ∧ v3=false)) ∨
  ((v1=true ∧ v3=true) ∧ (True ∧ v8=false)) ∨
  ((v7=true ∧ v8=true) ∧ (True ∧ v1=false)) ∨
  ((v2=true ∧ v8=true) ∧ (True ∧ v7=false)) ∨
  ((v1=true ∧ v7=true ∧ v8=true) ∧ (True)) ∨
  ((v3=true ∧ v7=true) ∧ (True ∧ v1=false)) ∨
  ((v0=true ∧ v4=true ∧ v5=true) ∧ (True ∧ True)) ∨
  ((v1=true ∧ v3=true ∧ v8=true) ∧ (True)) ∨
  ((v2=true ∧ v7=true ∧ v10=true) ∧ (True)) ∨
  ((v2=true ∧ v11=true) ∧ (True ∧ v1=false)) ∨
  ((v8=true ∧ v10=true) ∧ (True ∧ v2=false)) ∨
  ((v3=true ∧ v8=true ∧ v11=true) ∧ (True)) ∨
  ((v1=true ∧ v2=true ∧ v7=true) ∧ (True)) ∨
  ((v1=true ∧ v7=true ∧ v10=true) ∧ (v3=false ∧ v2=false)) ∨
  ((v2=true ∧ v3=true ∧ v10=true) ∧ (True ∧ v1=false)) ∨
  ((v1=true ∧ v2=true ∧ v10=true) ∧ (v3=false ∧ v7=false))
private theorem logical_cover (v0 v1 v2:Bool) : ∀ v3 v4 v5 v7 v8 v10 v11,tally v0 v1 v2 v3 v4 v5 v7 v8 v10 v11=5 → options v0 v1 v2 v3 v4 v5 v7 v8 v10 v11 := by
  cases v0 <;> cases v1 <;> cases v2 <;> unfold tally options <;> decide +kernel

private theorem coverage {K:Finset V} (h:K∈U.powersetCard 5) : ∃ p∈patterns,p.hits K := by
  obtain ⟨sub,number⟩ := mem_powersetCard.mp h
  have outside6 : (6:V)∉K := fun a => (show (6:V)∉U by decide) (sub a)
  have outside9 : (9:V)∉K := fun a => (show (9:V)∉U by decide) (sub a)
  have filt : U.filter (fun i=>i∈K)=K := by ext i; simp only [mem_filter]; exact ⟨And.right,fun hi => ⟨sub hi,hi⟩⟩
  have count : (∑ i∈U,if i∈K then (1:ℕ) else 0)=5 := by
    calc
      _ = (U.filter (fun i=>i∈K)).card := Finset.sum_boole _ _
      _ = 5 := (congrArg Finset.card filt).trans number
  simp only [U,sum_insert (by decide : (0:V)∉({1,2,3,4,5,7,8,10,11}:Finset V)),sum_insert (by decide : (1:V)∉({2,3,4,5,7,8,10,11}:Finset V)),sum_insert (by decide : (2:V)∉({3,4,5,7,8,10,11}:Finset V)),sum_insert (by decide : (3:V)∉({4,5,7,8,10,11}:Finset V)),sum_insert (by decide : (4:V)∉({5,7,8,10,11}:Finset V)),sum_insert (by decide : (5:V)∉({7,8,10,11}:Finset V)),sum_insert (by decide : (7:V)∉({8,10,11}:Finset V)),sum_insert (by decide : (8:V)∉({10,11}:Finset V)),sum_insert (by decide : (10:V)∉({11}:Finset V)),sum_singleton] at count
  have possible := logical_cover (decide ((0:V)∈K)) (decide ((1:V)∈K)) (decide ((2:V)∈K)) (decide ((3:V)∈K)) (decide ((4:V)∈K)) (decide ((5:V)∈K)) (decide ((7:V)∈K)) (decide ((8:V)∈K)) (decide ((10:V)∈K)) (decide ((11:V)∈K)) (by simpa only [tally,decide_eq_true_eq] using count)
  unfold options at possible
  simp only [decide_eq_true_eq,decide_eq_false_iff_not] at possible
  rcases possible with e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e
  · refine ⟨pat0,by simp [patterns],?_,?_⟩
    · simpa only [pat0,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside6,e.2.2⟩
  · refine ⟨pat1,by simp [patterns],?_,?_⟩
    · simpa only [pat1,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside6,e.2.2⟩
  · refine ⟨pat2,by simp [patterns],?_,?_⟩
    · simpa only [pat2,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside6,e.2.2⟩
  · refine ⟨pat3,by simp [patterns],?_,?_⟩
    · simpa only [pat3,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside6,e.2.2⟩
  · refine ⟨pat4,by simp [patterns],?_,?_⟩
    · simpa only [pat4,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside6,e.2.2⟩
  · refine ⟨pat5,by simp [patterns],?_,?_⟩
    · simpa only [pat5,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inl rfl
  · refine ⟨pat6,by simp [patterns],?_,?_⟩
    · simpa only [pat6,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside6,e.2.2⟩
  · refine ⟨pat7,by simp [patterns],?_,?_⟩
    · simpa only [pat7,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside6,outside9⟩
  · refine ⟨pat8,by simp [patterns],?_,?_⟩
    · simpa only [pat8,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inl rfl
  · refine ⟨pat9,by simp [patterns],?_,?_⟩
    · simpa only [pat9,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inl rfl
  · refine ⟨pat10,by simp [patterns],?_,?_⟩
    · simpa only [pat10,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside6,e.2.2⟩
  · refine ⟨pat11,by simp [patterns],?_,?_⟩
    · simpa only [pat11,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside6,e.2.2⟩
  · refine ⟨pat12,by simp [patterns],?_,?_⟩
    · simpa only [pat12,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inl rfl
  · refine ⟨pat13,by simp [patterns],?_,?_⟩
    · simpa only [pat13,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inl rfl
  · refine ⟨pat14,by simp [patterns],?_,?_⟩
    · simpa only [pat14,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat15,by simp [patterns],?_,?_⟩
    · simpa only [pat15,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside6,e.2.2⟩
  · refine ⟨pat16,by simp [patterns],?_,?_⟩
    · simpa only [pat16,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩

theorem old_score : weightedLeaves J U=4 := by
  have lower : 4≤weightedLeaves J U := by
    apply (score_iff_core J jc (by decide) U 4).mpr
    refine ⟨{0,2,5,7},by decide,by decide,con 3 (fun i => [88,2,88,0,3,88,2,88,1,4,2,1][i.val]!) (by decide) (by decide),?_⟩
    unfold Dominates; decide
  apply le_antisymm _ lower
  apply weighted_le_of_patterns J jc (by decide) U 4 oldEdges patterns (fun e => e.2)
  · exact valid_patterns
  · exact fun _ h => coverage h

#print axioms old_score
end Minimal180.Case12
