import AllTipsBase180
import LeafPatterns180
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option warningAsError true
set_option compiler.extract_closed false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace Minimal180.Case14
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180
private noncomputable def pat0 : LeafPattern V := ⟨{0,1},2,8,{2}⟩
private noncomputable def pat1 : LeafPattern V := ⟨{3,7},2,8,{0,1,2,9,10,11,12,13}⟩
private noncomputable def pat2 : LeafPattern V := ⟨{4,9},2,8,{0,1,2,3,5,10,11,13}⟩
private noncomputable def pat3 : LeafPattern V := ⟨{5,10},2,8,{0,1,2,3,13}⟩
private noncomputable def pat4 : LeafPattern V := ⟨{6,12},2,8,{0,1,2,3,4,5,9,10,11,13}⟩
private noncomputable def pat5 : LeafPattern V := ⟨{1,13},0,8,{0,2}⟩
private noncomputable def pat6 : LeafPattern V := ⟨{0,3},1,7,{1,2}⟩
private noncomputable def pat7 : LeafPattern V := ⟨{0,7},1,11,{1,2,3,4,5,6,8}⟩
private noncomputable def pat8 : LeafPattern V := ⟨{4,10},2,8,{0,1,2,3,5,13}⟩
private noncomputable def pat9 : LeafPattern V := ⟨{5,9},2,4,{0,1,2,3,10,11,13}⟩
private noncomputable def pat10 : LeafPattern V := ⟨{6,13},1,8,{0,1,2,3,4,5}⟩
private noncomputable def pat11 : LeafPattern V := ⟨{9,10},2,11,{0,1,2,3,4,5,6,7,8,12,13}⟩
private noncomputable def pat12 : LeafPattern V := ⟨{12,13},1,11,{0,1,2,3,4,5,6,7,8}⟩
private noncomputable def pat13 : LeafPattern V := ⟨{1,7},0,3,{0,2,9,10,11,12,13}⟩
private noncomputable def pat14 : LeafPattern V := ⟨{1,12},0,6,{0,2,9,10,11,13}⟩
private noncomputable def pat15 : LeafPattern V := ⟨{0,4},1,7,{1,2,3,5}⟩
private noncomputable def pat16 : LeafPattern V := ⟨{1,6},0,3,{0,2,7,8,9,10,11,12,13}⟩
private noncomputable def pat17 : LeafPattern V := ⟨{3,4},0,5,{0,1,2,6,7,8,9,10,11,12,13}⟩
private noncomputable def pat18 : LeafPattern V := ⟨{3,6},0,4,{0,1,2,7,8,9,10,11,12,13}⟩
private noncomputable def pat19 : LeafPattern V := ⟨{4,7},0,8,{0,1,2,3,5,9,10,11,12,13}⟩
private noncomputable def pat20 : LeafPattern V := ⟨{5,12},1,8,{0,1,2,3,9,10,11,13}⟩
private noncomputable def pat21 : LeafPattern V := ⟨{5,13},1,6,{0,1,2,3}⟩
private noncomputable def pat22 : LeafPattern V := ⟨{0,6},1,7,{1,2,3,4,5}⟩
private noncomputable def pat23 : LeafPattern V := ⟨{3,9},0,4,{0,1,2,10,11,13}⟩
private noncomputable def pat24 : LeafPattern V := ⟨{3,10},0,4,{0,1,2,13}⟩
private noncomputable def pat25 : LeafPattern V := ⟨{6,7},0,8,{0,1,2,3,4,5,9,10,11,12,13}⟩
private noncomputable def pat26 : LeafPattern V := ⟨{0,9},1,10,{1,2,3,4,5,6,7,8,12}⟩
private noncomputable def pat27 : LeafPattern V := ⟨{7,10},0,9,{0,1,2,3,4,5,6,8,13}⟩
private noncomputable def pat28 : LeafPattern V := ⟨{0,10},1,13,{1,2,3,4,5,6,7,8,9,11,12}⟩
private noncomputable def pat29 : LeafPattern V := ⟨{1,4},0,3,{0,2,6,7,8,9,10,11,12,13}⟩
private noncomputable def pat30 : LeafPattern V := ⟨{7,9},0,12,{0,1,2,3,4,5,6,8,10,11,13}⟩
private noncomputable def pat31 : LeafPattern V := ⟨{0,10,13},13,13,∅⟩
private noncomputable def pat32 : LeafPattern V := ⟨{1,3,5},3,3,∅⟩
private noncomputable def pat33 : LeafPattern V := ⟨{3,4,5},5,5,∅⟩
private noncomputable def pat34 : LeafPattern V := ⟨{4,5,6},4,4,∅⟩
private noncomputable def pat35 : LeafPattern V := ⟨{7,9,12},12,12,∅⟩
private noncomputable def patterns : List (LeafPattern V) := [pat0,pat1,pat2,pat3,pat4,pat5,pat6,pat7,pat8,pat9,pat10,pat11,pat12,pat13,pat14,pat15,pat16,pat17,pat18,pat19,pat20,pat21,pat22,pat23,pat24,pat25,pat26,pat27,pat28,pat29,pat30,pat31,pat32,pat33,pat34,pat35]

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
private theorem valid17 : pat17.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid18 : pat18.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid19 : pat19.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid20 : pat20.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid21 : pat21.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid22 : pat22.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid23 : pat23.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid24 : pat24.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid25 : pat25.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid26 : pat26.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid27 : pat27.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid28 : pat28.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid29 : pat29.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid30 : pat30.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid31 : pat31.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid32 : pat32.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid33 : pat33.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid34 : pat34.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid35 : pat35.valid oldEdges := by unfold LeafPattern.valid; decide +kernel
private theorem valid_patterns (p:LeafPattern V) (hp:p∈patterns) : p.valid oldEdges := by
  simp only [patterns,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
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
  · exact valid17
  · exact valid18
  · exact valid19
  · exact valid20
  · exact valid21
  · exact valid22
  · exact valid23
  · exact valid24
  · exact valid25
  · exact valid26
  · exact valid27
  · exact valid28
  · exact valid29
  · exact valid30
  · exact valid31
  · exact valid32
  · exact valid33
  · exact valid34
  · exact valid35

private noncomputable def tally (v0 v1 v3 v4 v5 v6 v7 v9 v10 v12 v13:Bool) : ℕ := (if v0 then 1 else 0)+((if v1 then 1 else 0)+((if v3 then 1 else 0)+((if v4 then 1 else 0)+((if v5 then 1 else 0)+((if v6 then 1 else 0)+((if v7 then 1 else 0)+((if v9 then 1 else 0)+((if v10 then 1 else 0)+((if v12 then 1 else 0)+(if v13 then 1 else 0))))))))))
private noncomputable def options (v0 v1 v3 v4 v5 v6 v7 v9 v10 v12 v13:Bool) : Prop :=
  ((v0=true ∧ v1=true) ∧ (True ∧ True)) ∨
  ((v3=true ∧ v7=true) ∧ (True ∧ True)) ∨
  ((v4=true ∧ v9=true) ∧ (True ∧ True)) ∨
  ((v5=true ∧ v10=true) ∧ (True ∧ True)) ∨
  ((v6=true ∧ v12=true) ∧ (True ∧ True)) ∨
  ((v1=true ∧ v13=true) ∧ (v0=false ∧ True)) ∨
  ((v0=true ∧ v3=true) ∧ (v1=false ∧ v7=false)) ∨
  ((v0=true ∧ v7=true) ∧ (v1=false ∧ True)) ∨
  ((v4=true ∧ v10=true) ∧ (True ∧ True)) ∨
  ((v5=true ∧ v9=true) ∧ (True ∧ v4=false)) ∨
  ((v6=true ∧ v13=true) ∧ (v1=false ∧ True)) ∨
  ((v9=true ∧ v10=true) ∧ (True ∧ True)) ∨
  ((v12=true ∧ v13=true) ∧ (v1=false ∧ True)) ∨
  ((v1=true ∧ v7=true) ∧ (v0=false ∧ v3=false)) ∨
  ((v1=true ∧ v12=true) ∧ (v0=false ∧ v6=false)) ∨
  ((v0=true ∧ v4=true) ∧ (v1=false ∧ v7=false)) ∨
  ((v1=true ∧ v6=true) ∧ (v0=false ∧ v3=false)) ∨
  ((v3=true ∧ v4=true) ∧ (v0=false ∧ v5=false)) ∨
  ((v3=true ∧ v6=true) ∧ (v0=false ∧ v4=false)) ∨
  ((v4=true ∧ v7=true) ∧ (v0=false ∧ True)) ∨
  ((v5=true ∧ v12=true) ∧ (v1=false ∧ True)) ∨
  ((v5=true ∧ v13=true) ∧ (v1=false ∧ v6=false)) ∨
  ((v0=true ∧ v6=true) ∧ (v1=false ∧ v7=false)) ∨
  ((v3=true ∧ v9=true) ∧ (v0=false ∧ v4=false)) ∨
  ((v3=true ∧ v10=true) ∧ (v0=false ∧ v4=false)) ∨
  ((v6=true ∧ v7=true) ∧ (v0=false ∧ True)) ∨
  ((v0=true ∧ v9=true) ∧ (v1=false ∧ v10=false)) ∨
  ((v7=true ∧ v10=true) ∧ (v0=false ∧ v9=false)) ∨
  ((v0=true ∧ v10=true) ∧ (v1=false ∧ v13=false)) ∨
  ((v1=true ∧ v4=true) ∧ (v0=false ∧ v3=false)) ∨
  ((v7=true ∧ v9=true) ∧ (v0=false ∧ v12=false)) ∨
  ((v0=true ∧ v10=true ∧ v13=true) ∧ (True)) ∨
  ((v1=true ∧ v3=true ∧ v5=true) ∧ (True)) ∨
  ((v3=true ∧ v4=true ∧ v5=true) ∧ (True)) ∨
  ((v4=true ∧ v5=true ∧ v6=true) ∧ (True)) ∨
  ((v7=true ∧ v9=true ∧ v12=true) ∧ (True))
private theorem logical_cover (v0 v1 v3:Bool) : ∀ v4 v5 v6 v7 v9 v10 v12 v13,tally v0 v1 v3 v4 v5 v6 v7 v9 v10 v12 v13=3 → options v0 v1 v3 v4 v5 v6 v7 v9 v10 v12 v13 := by
  cases v0 <;> cases v1 <;> cases v3 <;> unfold tally options <;> decide +kernel

private theorem coverage {K:Finset V} (h:K∈U.powersetCard 3) : ∃ p∈patterns,p.hits K := by
  obtain ⟨sub,number⟩ := mem_powersetCard.mp h
  have outside2 : (2:V)∉K := fun a => (show (2:V)∉U by decide) (sub a)
  have outside8 : (8:V)∉K := fun a => (show (8:V)∉U by decide) (sub a)
  have outside11 : (11:V)∉K := fun a => (show (11:V)∉U by decide) (sub a)
  have filt : U.filter (fun i=>i∈K)=K := by ext i; simp only [mem_filter]; exact ⟨And.right,fun hi => ⟨sub hi,hi⟩⟩
  have count : (∑ i∈U,if i∈K then (1:ℕ) else 0)=3 := by
    calc
      _ = (U.filter (fun i=>i∈K)).card := Finset.sum_boole _ _
      _ = 3 := (congrArg Finset.card filt).trans number
  simp only [U,sum_insert (by decide : (0:V)∉({1,3,4,5,6,7,9,10,12,13}:Finset V)),sum_insert (by decide : (1:V)∉({3,4,5,6,7,9,10,12,13}:Finset V)),sum_insert (by decide : (3:V)∉({4,5,6,7,9,10,12,13}:Finset V)),sum_insert (by decide : (4:V)∉({5,6,7,9,10,12,13}:Finset V)),sum_insert (by decide : (5:V)∉({6,7,9,10,12,13}:Finset V)),sum_insert (by decide : (6:V)∉({7,9,10,12,13}:Finset V)),sum_insert (by decide : (7:V)∉({9,10,12,13}:Finset V)),sum_insert (by decide : (9:V)∉({10,12,13}:Finset V)),sum_insert (by decide : (10:V)∉({12,13}:Finset V)),sum_insert (by decide : (12:V)∉({13}:Finset V)),sum_singleton] at count
  have possible := logical_cover (decide ((0:V)∈K)) (decide ((1:V)∈K)) (decide ((3:V)∈K)) (decide ((4:V)∈K)) (decide ((5:V)∈K)) (decide ((6:V)∈K)) (decide ((7:V)∈K)) (decide ((9:V)∈K)) (decide ((10:V)∈K)) (decide ((12:V)∈K)) (decide ((13:V)∈K)) (by simpa only [tally,decide_eq_true_eq] using count)
  unfold options at possible
  simp only [decide_eq_true_eq,decide_eq_false_iff_not] at possible
  rcases possible with e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e
  · refine ⟨pat0,by simp [patterns],?_,?_⟩
    · simpa only [pat0,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside2,outside8⟩
  · refine ⟨pat1,by simp [patterns],?_,?_⟩
    · simpa only [pat1,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside2,outside8⟩
  · refine ⟨pat2,by simp [patterns],?_,?_⟩
    · simpa only [pat2,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside2,outside8⟩
  · refine ⟨pat3,by simp [patterns],?_,?_⟩
    · simpa only [pat3,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside2,outside8⟩
  · refine ⟨pat4,by simp [patterns],?_,?_⟩
    · simpa only [pat4,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside2,outside8⟩
  · refine ⟨pat5,by simp [patterns],?_,?_⟩
    · simpa only [pat5,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,outside8⟩
  · refine ⟨pat6,by simp [patterns],?_,?_⟩
    · simpa only [pat6,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat7,by simp [patterns],?_,?_⟩
    · simpa only [pat7,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,outside11⟩
  · refine ⟨pat8,by simp [patterns],?_,?_⟩
    · simpa only [pat8,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside2,outside8⟩
  · refine ⟨pat9,by simp [patterns],?_,?_⟩
    · simpa only [pat9,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside2,e.2.2⟩
  · refine ⟨pat10,by simp [patterns],?_,?_⟩
    · simpa only [pat10,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,outside8⟩
  · refine ⟨pat11,by simp [patterns],?_,?_⟩
    · simpa only [pat11,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨outside2,outside11⟩
  · refine ⟨pat12,by simp [patterns],?_,?_⟩
    · simpa only [pat12,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,outside11⟩
  · refine ⟨pat13,by simp [patterns],?_,?_⟩
    · simpa only [pat13,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat14,by simp [patterns],?_,?_⟩
    · simpa only [pat14,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat15,by simp [patterns],?_,?_⟩
    · simpa only [pat15,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat16,by simp [patterns],?_,?_⟩
    · simpa only [pat16,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat17,by simp [patterns],?_,?_⟩
    · simpa only [pat17,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat18,by simp [patterns],?_,?_⟩
    · simpa only [pat18,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat19,by simp [patterns],?_,?_⟩
    · simpa only [pat19,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,outside8⟩
  · refine ⟨pat20,by simp [patterns],?_,?_⟩
    · simpa only [pat20,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,outside8⟩
  · refine ⟨pat21,by simp [patterns],?_,?_⟩
    · simpa only [pat21,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat22,by simp [patterns],?_,?_⟩
    · simpa only [pat22,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat23,by simp [patterns],?_,?_⟩
    · simpa only [pat23,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat24,by simp [patterns],?_,?_⟩
    · simpa only [pat24,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat25,by simp [patterns],?_,?_⟩
    · simpa only [pat25,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,outside8⟩
  · refine ⟨pat26,by simp [patterns],?_,?_⟩
    · simpa only [pat26,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat27,by simp [patterns],?_,?_⟩
    · simpa only [pat27,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat28,by simp [patterns],?_,?_⟩
    · simpa only [pat28,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat29,by simp [patterns],?_,?_⟩
    · simpa only [pat29,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat30,by simp [patterns],?_,?_⟩
    · simpa only [pat30,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩
  · refine ⟨pat31,by simp [patterns],?_,?_⟩
    · simpa only [pat31,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inl rfl
  · refine ⟨pat32,by simp [patterns],?_,?_⟩
    · simpa only [pat32,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inl rfl
  · refine ⟨pat33,by simp [patterns],?_,?_⟩
    · simpa only [pat33,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inl rfl
  · refine ⟨pat34,by simp [patterns],?_,?_⟩
    · simpa only [pat34,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inl rfl
  · refine ⟨pat35,by simp [patterns],?_,?_⟩
    · simpa only [pat35,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inl rfl


theorem old_score : weightedLeaves J U=2 := by
  have lower : 2≤weightedLeaves J U := by
    apply (score_iff_core J jc (by decide) U 2).mpr
    refine ⟨{0,13},by decide,by decide,con 1 (fun i => [88,0,1,1,3,2,4,5,5,7,8,8,6,88][i.val]!) (by decide) (by decide),?_⟩
    unfold Dominates; decide
  apply le_antisymm _ lower
  apply weighted_le_of_patterns J jc (by decide) U 2 oldEdges patterns (fun e => e.2)
  · exact valid_patterns
  · exact fun _ h => coverage h

#print axioms old_score
end Minimal180.Case14
