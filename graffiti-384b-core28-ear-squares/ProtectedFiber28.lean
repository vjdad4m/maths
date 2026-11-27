import ThirtyBoth31

namespace Graffiti384b.CorePair28
open Finset SimpleGraph JointRank
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]

private def need (i : ℕ) := if i=0 then 1 else i+3

private def cost (i : ℕ) := if i=0 then 817190 else if i≤2 then 394706 else if i≤3 then 293930 else if i≤5 then 267410 else if i≤9 then 170170 else if i≤13 then 101530 else if i≤18 then 56485 else 29029

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem table : (∀ i : Fin 24,∀ d : Fin 11,
    ((need i≤RankTable.cap d 3 ∨ d.val=10) → FiniteRange.badCount 24 9 d≤cost i) ∧
    ((need i≤(d.val+1).choose 2 ∨ d.val=10) → (24-d.val).choose 9≤cost i)) ∧
    (∑ i∈range 24,cost i)=3949722 ∧ 3949722<3*(24:ℕ).choose 9+29029 := by
  unfold need RankTable.cap cost FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide

private theorem fiber {W : Finset V} (ws : W.card=24) {v : V} (vm : v∈W) {j i : ℕ}
    (lt : i<24) (score : need i≤j)
    (plain : (∀ w,w∉W → ¬J.Adj v w) → j≤(turanGraph (J.degree v) 3).edgeFinset.card)
    (single : ∀ w,w∉W → J.Adj v w → J.neighborFinset v⊆insert w W → j≤(J.degree v+1).choose 2) :
    ((W.powersetCard 9).filter (fun k => v∈FiniteRange.bad J W k)).card≤cost i := by
  classical
  let d := min (J.degree v) 10
  have lo : d≤J.degree v := min_le_left ..
  have hi : d≤10 := min_le_right ..
  have same (ne : d≠10) : d=J.degree v := by dsimp [d] at *; omega
  obtain ⟨p,c⟩ := table.1 ⟨i,lt⟩ ⟨d,by omega⟩
  change (need i≤RankTable.cap d 3 ∨ d=10 → FiniteRange.badCount 24 9 d≤cost i) at p
  change (need i≤(d+1).choose 2 ∨ d=10 → (24-d).choose 9≤cost i) at c
  by_cases credit : ∃ w,w∉W ∧ J.Adj v w
  · obtain ⟨w,wm,edge⟩ := credit
    by_cases sub : J.neighborFinset v⊆insert w W
    · have bound := EarPalette.credited_count J vm edge wm sub 9
      rw [ws] at bound
      apply bound.trans; apply (Nat.choose_le_choose 9 (by omega : 24-J.degree v≤24-d)).trans
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

/-- A protected pool vertex never needs repair, saving at least the smallest of the 24 rank costs. -/
theorem sample {W : Finset V} (ws : W.card=24) (f : V → ℕ) (inj : Function.Injective f)
    (range' : ∀ v∈W,f v=1 ∨ 4≤f v)
    (plain : ∀ v∈W,(∀ w,w∉W → ¬J.Adj v w) → f v≤(turanGraph (J.degree v) 3).edgeFinset.card)
    (single : ∀ v∈W,∀ w,w∉W → J.Adj v w → J.neighborFinset v⊆insert w W → f v≤(J.degree v+1).choose 2)
    {z : V} (zw : z∈W) (safe : ∀ k,z∉FiniteRange.bad J W k) :
    ∃ k∈W.powersetCard 9,(FiniteRange.bad J W k).card≤2 := by
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
  have zero : hit z=0 := by
    have eq : opts.filter (fun k => z∈fail k)=∅ := filter_eq_empty_iff.mpr (fun k _ => safe k)
    change (opts.filter (fun k => z∈fail k)).card=0
    rw [eq,card_empty]
  have improved (v : V) (vm : v∈W) : hit v+(if v=z then 29029 else 0)≤cost (rank W g v) := by
    by_cases eq : v=z
    · subst v; simp only [zero,if_true,zero_add]; unfold cost; split_ifs <;> decide
    · simpa [eq] using per v vm
  have lim := sum_le_sum improved
  rw [sum_add_distrib] at lim
  have refund : (∑ v∈W,if v=z then 29029 else 0)=29029 := by simp [zw]
  rw [refund] at lim
  rw [sum_by_rank W g fi cost,ws,table.2.1] at lim
  apply Classical.byContradiction; intro noSample
  have none (k : Finset V) (km : k∈opts) : 3≤(fail k).card := Nat.le_of_not_gt (fun h => noSample ⟨k,km,by change (fail k).card≤2; omega⟩)
  have lots : (∑ _k∈opts,3)≤∑ k∈opts,(fail k).card := sum_le_sum (fun k km => none k km)
  have os : opts.card=(24:ℕ).choose 9 := by rw [show opts=W.powersetCard 9 from rfl,card_powersetCard,ws]
  rw [total] at lots
  simp only [sum_const,nsmul_eq_mul,os,Nat.cast_id] at lots
  have := table.2.2
  omega

end Graffiti384b.CorePair28
#print axioms Graffiti384b.CorePair28.sample


