import CreditGeometry31
import CreditTable31

namespace Graffiti384b.EarCredit.Pair
open SimpleGraph Finset JointRank
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private EarCredit.credited from CreditRanks31
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- For a retained pair outside W, zero, one and two guaranteed neighbors
give the three kernel-checked costs. -/
theorem pair_fiber {W A : Finset V} (ws : W.card=27) (aw : Disjoint A W)
    {v : V} (vm : v∈W) :
    ((W.powersetCard 9).filter (fun k => v∈FiniteRange.bad H W k)).card≤
    loss (min (H.degree v) 10) (nbr H v A) := by
  classical
  let d := min (H.degree v) 10
  have dr : d≤H.degree v := min_le_left ..
  have ds : d≤10 := min_le_right ..
  have asub : A⊆Wᶜ := fun z zm => mem_compl.mpr (fun wm => disjoint_left.mp aw zm wm)
  by_cases none : nbr H v A=0
  · have cap := FiniteRange.count_bad H W 9 d v vm dr (by rw [ws]; omega)
    rw [ws] at cap; simpa [loss,none,d] using cap
  by_cases one : nbr H v A=1
  · obtain ⟨z,zm⟩ := card_pos.mp (show 0<nbr H v A by omega)
    obtain ⟨za,vz⟩ := mem_filter.mp zm
    have cap := EarCredit.credited H vm (mem_compl.mp (asub za)) vz 9
    rw [ws] at cap
    simpa [loss,one,d] using cap.trans (Nat.choose_le_choose 9 (Nat.sub_le_sub_left dr 27))
  have empty : ((W.powersetCard 9).filter (fun k => v∈FiniteRange.bad H W k))=∅ := eq_empty_of_forall_not_mem (by
    intro k km
    have low := (mem_filter.mp (mem_filter.mp km).2).2
    have up := Repair.nbr_mono H v (asub.trans (subset_union_left (s₂:=k)))
    omega)
  simp [loss,empty,none,one]

/-- Ranking all exterior scores, with a reserved pivot in the two contact
cases, makes the three finite bounds apply to every exterior graph. -/
theorem estimate {W : Finset V} {x : V} (ws : W.card=27) (xm : x∈W)
    (sx : trianglesAt H x=5) (dx : H.degree x=4) (fi : Function.Injective (trianglesAt H))
    (scores : ∀ v∈W,2≤trianglesAt H v) (free : H.CliqueFree 5)
    (mode : Fin 3) (j bill : V→ℕ) (jbound : ∀ v∈W,j v≤2)
    (low : ∀ v∈W,3≤trianglesAt H v → j v=0 → 4≤H.degree v)
    (fiber : ∀ v∈W,bill v≤loss (min (H.degree v) 10) (j v))
    (single : mode.val=0 → ∀ v∈W,j v≠2)
    (touch : mode.val=1 → 1≤j x) (both : mode.val=2 → j x=2)
    (over : (∑ v∈W,rebate mode (j v))≤penalty mode)
    (inc : 12≤∑ v∈W,j v) : (∑ v∈W,bill v)<4*(27:ℕ).choose 9 := by
  classical
  let U := if mode.val=0 then W else W.erase x
  have sub : U⊆W := by dsimp [U]; split_ifs; exacts [Subset.rfl,erase_subset ..]
  have size : U.card=quota mode := by by_cases h : mode.val=0 <;> simp [U,quota,h,card_erase_of_mem xm,ws]
  have reserve (v : V) (vm : v∈U) (non : mode.val≠0) : trianglesAt H v≠5 := by
    have away : v≠x := (mem_erase.mp (show v∈W.erase x by simpa [U,non] using vm)).1
    exact fun eq => away (fi (eq.trans sx.symm))
  let f (v : V) := if mode.val≠0 ∧ 5<trianglesAt H v then trianglesAt H v-1 else trianglesAt H v
  have inj : Set.InjOn f (U:Set V) := by
    intro v vm w wm eq; have a := reserve v vm; have b := reserve w wm
    unfold f at eq; apply fi; split_ifs at eq <;> omega
  have floor' (v : V) (vm : v∈U) : 2≤f v := by have := scores v (sub vm); unfold f; split_ifs <;> omega
  let r := rank U f
  have line (v : V) (vm : v∈U) : bill v+price mode*j v≤budget mode (r v)+rebate mode (j v) := by
    have valid := mem_image_of_mem (rank U f) vm
    rw [rank_range U f inj,size,mem_range] at valid
    change r v<quota mode at valid
    have lt : r v<27 := by unfold quota at valid; split_ifs at valid <;> omega
    have lo := rank_lower U f inj 2 floor' vm
    change 2+r v≤f v at lo
    have sc : minimumScore mode (r v)≤trianglesAt H v := by
      have z := reserve v vm; dsimp [f] at lo; unfold minimumScore; split_ifs at * <;> omega
    let d := min (H.degree v) 10
    have ds : d≤10 := min_le_right ..
    have cap : minimumScore mode (r v)≤RankTable.cap d 3 ∨ d=10 := by
      by_cases h : H.degree v≤10
      · rw [show d=H.degree v from min_eq_left h]
        exact Or.inl (sc.trans ((RankTuran.local_turan H 3 (by decide) free v).trans_eq
          (RankTable.cap_table ⟨H.degree v,by omega⟩ ⟨3,by decide⟩ (by decide))))
      · exact Or.inr (min_eq_right (by omega))
    have bv := jbound v (sub vm)
    have lim := (rows mode).1 ⟨r v,lt⟩ ⟨d,by omega⟩ ⟨j v,by omega⟩ cap
      (fun h z => le_min (low v (sub vm) (h.trans sc) z) (by decide))
      (fun h => single h v (sub vm))
    exact (Nat.add_le_add_right (fiber v (sub vm)) _).trans lim
  let g (v : V) := bill v+price mode*j v
  let h (v : V) := rebate mode (j v)
  have whole : (∑ v∈W,g v)≤(∑ i∈range (quota mode),budget mode i)+pivotBill mode+∑ v∈W,h v := by
    have upper := sum_le_sum line
    rw [sum_add_distrib (f:=fun v => budget mode (r v)),sum_by_rank U f inj (budget mode),size] at upper
    change (∑ v∈U,g v)≤(∑ i∈range (quota mode),budget mode i)+∑ v∈U,h v at upper
    by_cases plain : mode.val=0
    · simpa [U,plain,pivotBill] using upper
    have bx := jbound x xm
    have z := (rows mode).2.1 ⟨j x,by omega⟩ plain touch both
    have fb := fiber x xm
    rw [dx] at fb; change bill x≤loss 4 (j x) at fb
    have add : g x≤pivotBill mode+h x := (Nat.add_le_add_right fb _).trans z
    have parts (F : V→ℕ) : (∑ v∈U,F v)+F x=∑ v∈W,F v := by
      rw [show U=W.erase x from if_neg plain]; exact sum_erase_add _ _ xm
    have a := parts g; have b := parts h; omega
  dsimp [g,h] at whole
  rw [sum_add_distrib,←mul_sum] at whole
  have total := (rows mode).2.2
  have d := Nat.mul_le_mul_left (price mode) inc
  rw [Nat.mul_comm (price mode) 12] at d
  omega

end Graffiti384b.EarCredit.Pair
#print axioms Graffiti384b.EarCredit.Pair.pair_fiber
#print axioms Graffiti384b.EarCredit.Pair.estimate
