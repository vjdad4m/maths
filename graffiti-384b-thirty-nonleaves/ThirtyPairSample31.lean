import ThirtyBoth31

namespace Graffiti384b.ThirtyCore
open Finset SimpleGraph JointRank
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]

private def need (i : ℕ) := if i=0 then 1 else i+3

private def cost (i : ℕ) := if i≤0 then 2042975 else if i≤2 then 1107890 else if i≤3 then 817190 else if i≤5 then 797810 else if i≤9 then 545870 else if i≤13 then 354926 else if i≤18 then 218790 else if i≤24 then 127270 else 92378

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem table : (∀ i : Fin 26,∀ d : Fin 11,
    ((need i≤RankTable.cap d 3 ∨ d.val=10) → FiniteRange.badCount 26 9 d≤cost i) ∧
    ((need i≤(d.val+1).choose 2 ∨ d.val=10) → (26-d.val).choose 9≤cost i)) ∧
    (∑ i∈range 26,cost i)=12224697 ∧ 12224697<4*(26:ℕ).choose 9 := by
  unfold need RankTable.cap cost FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide

private theorem fiber {W : Finset V} (ws : W.card=26) {v : V} (vm : v∈W) {j i : ℕ}
    (lt : i<26) (score : need i≤j)
    (plain : (∀ w,w∉W → ¬J.Adj v w) → j≤(turanGraph (J.degree v) 3).edgeFinset.card)
    (single : ∀ w,w∉W → J.Adj v w → J.neighborFinset v⊆insert w W → j≤(J.degree v+1).choose 2) :
    ((W.powersetCard 9).filter (fun k => v∈FiniteRange.bad J W k)).card≤cost i := by
  classical
  let d := min (J.degree v) 10
  have lo : d≤J.degree v := min_le_left ..
  have hi : d≤10 := min_le_right ..
  have same (ne : d≠10) : d=J.degree v := by dsimp [d] at *; omega
  obtain ⟨p,c⟩ := table.1 ⟨i,lt⟩ ⟨d,by omega⟩
  change (need i≤RankTable.cap d 3 ∨ d=10 → FiniteRange.badCount 26 9 d≤cost i) at p
  change (need i≤(d+1).choose 2 ∨ d=10 → (26-d).choose 9≤cost i) at c
  by_cases credit : ∃ w,w∉W ∧ J.Adj v w
  · obtain ⟨w,wm,edge⟩ := credit
    by_cases sub : J.neighborFinset v⊆insert w W
    · have bound := EarPalette.credited_count J vm edge wm sub 9
      rw [ws] at bound
      apply bound.trans; apply (Nat.choose_le_choose 9 (by omega : 26-J.degree v≤26-d)).trans
      apply c; by_cases eq : d=10
      · exact Or.inr eq
      · apply Or.inl; rw [same eq]; exact score.trans (single w wm edge sub)
    · obtain ⟨z,zn,off⟩ := not_subset.mp sub
      have ⟨zw,zm⟩ := (show z≠w ∧ z∉W by simpa [not_or] using off)
      have empty : ((W.powersetCard 9).filter (fun k => v∈FiniteRange.bad J W k))=∅ := eq_empty_of_forall_not_mem (by
        intro k km
        have low := (mem_filter.mp (mem_filter.mp km).2).2
        have two := PinnedColor34.two J zw ((J.mem_neighborFinset ..).mp zn) edge
          (mem_union_left k (mem_compl.mpr zm)) (mem_union_left k (mem_compl.mpr wm))
        omega)
      rw [empty,card_empty]; exact Nat.zero_le _
  · have h := FiniteRange.count_bad J W 9 d v vm lo (by rw [ws]; omega)
    rw [ws] at h
    apply h.trans; apply p; by_cases eq : d=10
    · exact Or.inr eq
    · have h := plain (fun w wm ed => credit ⟨w,wm,ed⟩)
      have ar := RankTable.cap_table ⟨d,by omega⟩ ⟨3,by decide⟩ (by decide)
      change (turanGraph d 3).edgeFinset.card=RankTable.cap d 3 at ar
      rw [←same eq] at h
      exact Or.inl (score.trans (h.trans_eq ar))

/-- In the 26-vertex sample pool the 26 distinct positive scores skip
two and three. The explicit upper bound on trial failures is 12,224,697. -/
theorem sample {W : Finset V} (ws : W.card=26) (f : V → ℕ) (inj : Function.Injective f)
    (range' : ∀ v∈W,f v=1 ∨ 4≤f v)
    (plain : ∀ v∈W,(∀ w,w∉W → ¬J.Adj v w) → f v≤(turanGraph (J.degree v) 3).edgeFinset.card)
    (single : ∀ v∈W,∀ w,w∉W → J.Adj v w → J.neighborFinset v⊆insert w W → f v≤(J.degree v+1).choose 2) :
    ∃ k∈W.powersetCard 9,(FiniteRange.bad J W k).card≤3 := by
  classical
  let g (v : V) := if f v=1 then 1 else f v-2
  have fi : Set.InjOn g (W : Set V) := by
    intro v vm w wm eq
    have := range' v vm; have := range' w wm
    apply inj; unfold g at eq; split_ifs at eq <;> omega
  have low (v : V) (vm : v∈W) : 1≤g v := by have := range' v vm; unfold g; split_ifs <;> omega
  let opts := W.powersetCard 9
  let fail := fun k => FiniteRange.bad J W k
  let hit := fun v => (opts.filter (fun k => v∈fail k)).card
  have per (v : V) (vm : v∈W) : hit v≤cost (rank W g v) := by
    have valid := mem_image_of_mem (rank W g) vm
    rw [rank_range W g fi,ws] at valid
    have h := rank_lower W g fi 1 low vm
    have vals := range' v vm
    change 1+rank W g v≤(if f v=1 then 1 else f v-2) at h
    have val : need (rank W g v)≤f v := by unfold need; split_ifs at * <;> omega
    exact fiber J ws vm (mem_range.mp valid) val (plain v vm) (single v vm)
  have total : (∑ k∈opts,(fail k).card)=∑ v∈W,hit v := by
    have sub (k : Finset V) : fail k⊆W := (filter_subset ..).trans sdiff_subset
    calc _ = ∑ k∈opts,∑ v∈W,if v∈fail k then 1 else 0 := by
           apply sum_congr rfl; intro k _; simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (sub k)]
         _ = _ := by rw [sum_comm]; simp [hit,sum_boole]
  have lim := sum_le_sum per
  rw [sum_by_rank W g fi cost,ws,table.2.1] at lim
  apply Classical.byContradiction; intro noSample
  have none (k : Finset V) (km : k∈opts) : 4≤(fail k).card := Nat.le_of_not_gt (fun h => noSample ⟨k,km,by change (fail k).card≤3; omega⟩)
  have lots : (∑ _k∈opts,4)≤∑ k∈opts,(fail k).card := sum_le_sum (fun k km => none k km)
  have os : opts.card=(26:ℕ).choose 9 := by rw [show opts=W.powersetCard 9 from rfl,card_powersetCard,ws]
  rw [total] at lots
  simp only [sum_const,nsmul_eq_mul,os,Nat.cast_id] at lots
  have := table.2.2
  omega

end Graffiti384b.ThirtyCore
#print axioms Graffiti384b.ThirtyCore.sample

