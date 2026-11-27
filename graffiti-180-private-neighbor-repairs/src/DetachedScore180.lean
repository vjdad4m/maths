import DetachedGraph180

set_option warningAsError true
set_option compiler.extract_closed false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
namespace Minimal180.DetachedExample
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 PrivateCore

private noncomputable def pat0 : LeafPattern V := ⟨{0,1,12},12,12,∅⟩
private noncomputable def pat1 : LeafPattern V := ⟨{2,6,8},8,8,∅⟩
private noncomputable def pat2 : LeafPattern V := ⟨{0,3,13},13,13,∅⟩
private noncomputable def pat3 : LeafPattern V := ⟨{1,6,7},7,7,∅⟩
private noncomputable def pat4 : LeafPattern V := ⟨{3,4,5,13},3,3,∅⟩
private noncomputable def pat5 : LeafPattern V := ⟨{4,5,13},9,3,{0,1,2,6,7,8,9,10,11,12}⟩
private noncomputable def pat6 : LeafPattern V := ⟨{0,3},9,13,{1,2,4,5,6,7,8,9,10,11,12}⟩
private noncomputable def pat7 : LeafPattern V := ⟨{1,2,3,5},5,5,∅⟩
private noncomputable def pat8 : LeafPattern V := ⟨{1,2,3},0,5,{0,4,6,7,8,9,10,11,12,13}⟩
private noncomputable def patterns := [pat0,pat1,pat2,pat3,pat4,pat5,pat6,pat7,pat8]
private theorem valid0 : pat0.valid E := by unfold LeafPattern.valid; decide +kernel
private theorem valid1 : pat1.valid E := by unfold LeafPattern.valid; decide +kernel
private theorem valid2 : pat2.valid E := by unfold LeafPattern.valid; decide +kernel
private theorem valid3 : pat3.valid E := by unfold LeafPattern.valid; decide +kernel
private theorem valid4 : pat4.valid E := by unfold LeafPattern.valid; decide +kernel
private theorem valid5 : pat5.valid E := by unfold LeafPattern.valid; decide +kernel
private theorem valid6 : pat6.valid E := by unfold LeafPattern.valid; decide +kernel
private theorem valid7 : pat7.valid E := by unfold LeafPattern.valid; decide +kernel
private theorem valid8 : pat8.valid E := by unfold LeafPattern.valid; decide +kernel
private theorem valid (p : LeafPattern V) (h : p∈patterns) : p.valid E := by
  simp only [patterns,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact valid0
  · exact valid1
  · exact valid2
  · exact valid3
  · exact valid4
  · exact valid5
  · exact valid6
  · exact valid7
  · exact valid8
private noncomputable def tally (v0 v1 v2 v3 v4 v5 v6 v7 v8 v12 v13 : Bool) : ℕ := (if v0 then 1 else 0) + ((if v1 then 1 else 0) + ((if v2 then 1 else 0) + ((if v3 then 1 else 0) + ((if v4 then 1 else 0) + ((if v5 then 1 else 0) + ((if v6 then 1 else 0) + ((if v7 then 1 else 0) + ((if v8 then 1 else 0) + ((if v12 then 1 else 0) + ((if v13 then 1 else 0)))))))))))
private noncomputable def options (v0 v1 v2 v3 v4 v5 v6 v7 v8 v12 v13 : Bool) : Prop :=
  ((v0=true ∧ v1=true ∧ v12=true) ∧ (True)) ∨
  ((v2=true ∧ v6=true ∧ v8=true) ∧ (True)) ∨
  ((v0=true ∧ v3=true ∧ v13=true) ∧ (True)) ∨
  ((v1=true ∧ v6=true ∧ v7=true) ∧ (True)) ∨
  ((v3=true ∧ v4=true ∧ v5=true ∧ v13=true) ∧ (True)) ∨
  ((v4=true ∧ v5=true ∧ v13=true) ∧ (True ∧ v3=false)) ∨
  ((v0=true ∧ v3=true) ∧ (True ∧ v13=false)) ∨
  ((v1=true ∧ v2=true ∧ v3=true ∧ v5=true) ∧ (True)) ∨
  ((v1=true ∧ v2=true ∧ v3=true) ∧ (v0=false ∧ v5=false))
private theorem logical_cover (v0 v1 v2 v3 : Bool) : ∀ v4 v5 v6 v7 v8 v12 v13,tally v0 v1 v2 v3 v4 v5 v6 v7 v8 v12 v13=8 → options v0 v1 v2 v3 v4 v5 v6 v7 v8 v12 v13 := by
  cases v0 <;> cases v1 <;> cases v2 <;> cases v3 <;> unfold tally options <;> decide +kernel
private theorem covered {K : Finset V} (hk : K∈U.powersetCard 8) : ∃ p∈patterns,p.hits K := by
  obtain ⟨sub,num⟩ := mem_powersetCard.mp hk
  have out9 : (9:V)∉K := fun h => (show (9:V)∉U by decide) (sub h)
  have filt : U.filter (fun i=>i∈K)=K := by ext i; simp only [mem_filter]; exact ⟨And.right,fun h => ⟨sub h,h⟩⟩
  have count : (∑ i∈U,if i∈K then (1:ℕ) else 0)=8 := by
    calc
      _ = (U.filter (fun i=>i∈K)).card := Finset.sum_boole _ _
      _ = 8 := (congrArg Finset.card filt).trans num
  simp only [U,sum_insert (by decide : (0:V)∉({1,2,3,4,5,6,7,8,12,13}:Finset V)),sum_insert (by decide : (1:V)∉({2,3,4,5,6,7,8,12,13}:Finset V)),sum_insert (by decide : (2:V)∉({3,4,5,6,7,8,12,13}:Finset V)),sum_insert (by decide : (3:V)∉({4,5,6,7,8,12,13}:Finset V)),sum_insert (by decide : (4:V)∉({5,6,7,8,12,13}:Finset V)),sum_insert (by decide : (5:V)∉({6,7,8,12,13}:Finset V)),sum_insert (by decide : (6:V)∉({7,8,12,13}:Finset V)),sum_insert (by decide : (7:V)∉({8,12,13}:Finset V)),sum_insert (by decide : (8:V)∉({12,13}:Finset V)),sum_insert (by decide : (12:V)∉({13}:Finset V)),sum_singleton] at count
  have co := logical_cover (decide ((0:V)∈K)) (decide ((1:V)∈K)) (decide ((2:V)∈K)) (decide ((3:V)∈K)) (decide ((4:V)∈K)) (decide ((5:V)∈K)) (decide ((6:V)∈K)) (decide ((7:V)∈K)) (decide ((8:V)∈K)) (decide ((12:V)∈K)) (decide ((13:V)∈K)) (by simpa only [tally,decide_eq_true_eq] using count)
  unfold options at co
  simp only [decide_eq_true_eq,decide_eq_false_iff_not] at co
  rcases co with e|e|e|e|e|e|e|e|e
  · refine ⟨pat0,by simp [patterns],?_,?_⟩
    · simpa only [pat0,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inl rfl
  · refine ⟨pat1,by simp [patterns],?_,?_⟩
    · simpa only [pat1,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inl rfl
  · refine ⟨pat2,by simp [patterns],?_,?_⟩
    · simpa only [pat2,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inl rfl
  · refine ⟨pat3,by simp [patterns],?_,?_⟩
    · simpa only [pat3,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inl rfl
  · refine ⟨pat4,by simp [patterns],?_,?_⟩
    · simpa only [pat4,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inl rfl
  · refine ⟨pat5,by simp [patterns],?_,?_⟩
    · simpa only [pat5,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨out9,e.2.2⟩
  · refine ⟨pat6,by simp [patterns],?_,?_⟩
    · simpa only [pat6,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨out9,e.2.2⟩
  · refine ⟨pat7,by simp [patterns],?_,?_⟩
    · simpa only [pat7,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inl rfl
  · refine ⟨pat8,by simp [patterns],?_,?_⟩
    · simpa only [pat8,insert_subset_iff,singleton_subset_iff] using e.1
    · exact Or.inr ⟨e.2.1,e.2.2⟩

theorem old_score : weightedLeaves J U=7 := by
  have low : 7≤weightedLeaves J U := by
    apply (score_iff_core J root_data.1.1 (by decide) U 7).mpr
    refine ⟨C.erase 4,by decide,by decide,Case14.con 0 (fun i => ([0, 2, 2, 88, 1, 88, 88, 88, 88, 1, 1, 2, 88, 88]:List ℕ)[i.val]!) (by decide) (by decide),?_⟩
    unfold Dominates; decide
  apply le_antisymm _ low
  exact weighted_le_of_patterns J root_data.1.1 (by decide) U 7 E patterns (fun e => e.2) valid (fun _ hk => covered hk)

#print axioms old_score
end Minimal180.DetachedExample
