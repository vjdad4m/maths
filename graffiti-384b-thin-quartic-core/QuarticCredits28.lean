import FourFrontier28

namespace Graffiti384b.Four28
open Finset SimpleGraph JointRank
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private Four28.square_rows from FourSquareSample28
variable {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]

set_option maxRecDepth 32768 in
private theorem refund_rows : ∀ i : Fin 24, ∀ d : Fin 11,
    29029≤squareCost 4 i ∧ ((required 4 i≤RankTable.cap d 3 ∨ d.val=10) →
      (24-d.val).choose 9+24024≤squareCost 4 i) := by
  unfold required squareCost RankTable.cap
  simp only [Nat.choose_eq_fast_choose]
  decide

set_option maxHeartbeats 800000 in
theorem quartic_refund {W L : Finset V} (ws : W.card=24) {y t : V} (ym : y∈W) (tm : t∈W) (yt : y≠t)
    (safe : fibers J W 9 y=0) (touchT : ∃ p,p∉W ∧ J.Adj t p)
    (f : V → ℕ) (fi : Function.Injective f)
    (scores : ∀ w∈W,2≤f w ∧ f w≠4)
    (full : ∀ w∈W,f w≤(turanGraph (J.degree w+1) 3).edgeFinset.card ∨ 10≤J.degree w)
    (plain : ∀ w∈W,w∉L → (∀ z,z∉W → ¬J.Adj w z) →
      f w≤(turanGraph (J.degree w) 3).edgeFinset.card ∨ 10≤J.degree w)
    (capT : f t≤(turanGraph (J.degree t) 3).edgeFinset.card ∨ 10≤J.degree t) :
    (∑ k∈W.powersetCard 9,(FiniteRange.bad J W k).card)+29029+24024 ≤
      (∑ i∈range 24,squareCost 4 i)+∑ w∈W,(if w∈L then surcharge (J.degree w) else 0) := by
  classical
  let s : ℕ := 4
  have small : s∈Icc 2 5 := by decide
  let g (v : V) := f v-(if s<f v then 1 else 0)
  have inj : Set.InjOn g (W:Set V) := by
    intro x xm y ym eq
    have sx := scores x xm; have sy := scores y ym
    change 2≤f x ∧ f x≠s at sx; change 2≤f y ∧ f y≠s at sy
    apply fi; unfold g at eq; split_ifs at eq <;> omega
  have base (v : V) (vm : v∈W) : 2≤g v := by
    have := scores v vm; have := mem_Icc.mp small
    unfold g; split_ifs <;> omega
  let rk := rank W g
  have costs (v : V) (vm : v∈W) : fibers J W 9 v + (if v=y then 29029 else 0) + (if v=t then 24024 else 0) ≤squareCost s (rk v)+(if v∈L then surcharge (J.degree v) else 0) := by
    have range' := mem_image_of_mem (rank W g) vm
    rw [rank_range W g inj,ws,mem_range] at range'
    have low := rank_lower W g inj 2 base vm
    change 2+rk v≤f v-(if s<f v then 1 else 0) at low
    have sc := scores v vm
    change 2≤f v ∧ f v≠s at sc
    have lb : required s (rk v)≤f v := by unfold required; split_ifs at * <;> omega
    let d := min (J.degree v) 10
    have dh : d≤10 := min_le_right ..
    have dl : d≤J.degree v := min_le_left ..
    have eq (ne : d≠10) : J.degree v=d := by dsimp [d] at *; omega
    have asCap (d' : ℕ) (dsmall : d'<12) :
        (turanGraph d' 3).edgeFinset.card=RankTable.cap d' 3 :=
      RankTable.cap_table ⟨d',dsmall⟩ ⟨3,by decide⟩ (by decide)
    have rows := Four28.square_rows s small ⟨rk v,range'⟩ ⟨d,by omega⟩
    dsimp only at rows
    have one : required s (rk v)≤RankTable.cap (d+1) 3 ∨ d=10 := by
      by_cases hi : d=10
      · exact Or.inr hi
      · rcases full v vm with le|big
        · rw [eq hi,asCap _ (by omega)] at le
          exact Or.inl (lb.trans le)
        · have := eq hi; omega
    by_cases vy : v=y
    · subst v
      have b := (refund_rows ⟨rk y,range'⟩ ⟨d,by omega⟩).1
      simp only [safe,if_pos rfl,if_neg yt,Nat.zero_add,Nat.add_zero]
      exact b.trans (Nat.le_add_right ..)
    rw [if_neg vy,Nat.add_zero]
    by_cases vt : v=t
    · subst v
      rw [if_pos rfl]
      obtain ⟨p,pm,tp⟩ := touchT
      have dg : 0<J.degree t := by
        rw [←card_neighborFinset_eq_degree]; exact card_pos.mpr ⟨p,(J.mem_neighborFinset ..).mpr tp⟩
      have h := BoundaryFiber.count J W 9 d vm pm tp dl (by dsimp [d]; omega)
      rw [ws] at h
      have cap : required 4 (rk t)≤RankTable.cap d 3 ∨ d=10 := by
        by_cases hi : d=10
        · exact Or.inr hi
        · rcases capT with le|big
          · rw [eq hi,asCap _ (by omega)] at le
            exact Or.inl (lb.trans le)
          · have := eq hi; omega
      have disc := (refund_rows ⟨rk t,range'⟩ ⟨d,by omega⟩).2 cap
      exact ((Nat.add_le_add_right h 24024).trans disc).trans (Nat.le_add_right ..)
    rw [if_neg vt,Nat.add_zero]
    by_cases touch : ∃ w,w∉W ∧ J.Adj v w
    · obtain ⟨w,wm,ed⟩ := touch
      have dg : 0<J.degree v := by
        rw [←card_neighborFinset_eq_degree]; exact card_pos.mpr ⟨w,(J.mem_neighborFinset ..).mpr ed⟩
      have h := BoundaryFiber.count J W 9 d vm wm ed dl (by dsimp [d]; omega)
      rw [ws] at h
      exact (h.trans (rows.1 one).1).trans (Nat.le_add_right ..)
    · have h := FiniteRange.count_bad J W 9 d v vm dl (by rw [ws]; omega)
      rw [ws] at h
      by_cases mark : v∈L
      · rw [if_pos mark]
        have same : surcharge (J.degree v)=surcharge d := by simp [surcharge,d]
        rw [same]; exact h.trans (rows.1 one).2
      · rw [if_neg mark,Nat.add_zero]
        apply h.trans; apply rows.2
        by_cases hi : d=10
        · exact Or.inr hi
        · rcases plain v vm mark (fun z zm ed => touch ⟨z,zm,ed⟩) with le|big
          · rw [eq hi,asCap _ (by omega)] at le
            exact Or.inl (lb.trans le)
          · have := eq hi; omega
  have total : (∑ k∈W.powersetCard 9,(FiniteRange.bad J W k).card)=∑ w∈W,fibers J W 9 w := by
    have sub (k : Finset V) : FiniteRange.bad J W k⊆W := (filter_subset ..).trans sdiff_subset
    calc _ = ∑ k∈W.powersetCard 9,∑ w∈W,if w∈FiniteRange.bad J W k then 1 else 0 := by
           apply sum_congr rfl; intro k _; simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (sub k)]
         _ = _ := by rw [sum_comm]; simp [fibers,sum_boole]
  have lim := sum_le_sum costs
  simp only [sum_add_distrib] at lim
  rw [sum_by_rank W g inj,ws] at lim
  simp [ym,tm] at lim
  rw [total]
  simpa [s] using lim

/-- Even if no adjacent failures share a repair, the two pinned-neighbor discounts
already cover the one exceptional surcharge. -/
theorem quartic_sample {W L : Finset V} (ws : W.card=24) (ls : L.card≤1)
    {y t : V} (ym : y∈W) (tm : t∈W) (yt : y≠t)
    (safe : fibers J W 9 y=0) (touch : ∃ p,p∉W ∧ J.Adj t p)
    (f : V → ℕ) (fi : Function.Injective f)
    (scores : ∀ w∈W,2≤f w ∧ f w≠4)
    (full : ∀ w∈W,f w≤(turanGraph (J.degree w+1) 3).edgeFinset.card ∨ 10≤J.degree w)
    (plain : ∀ w∈W,w∉L → (∀ z,z∉W → ¬J.Adj w z) →
      f w≤(turanGraph (J.degree w) 3).edgeFinset.card ∨ 10≤J.degree w)
    (capT : f t≤(turanGraph (J.degree t) 3).edgeFinset.card ∨ 10≤J.degree t) :
    ∃ T,Wᶜ⊆T ∧ TwoDominates J T ∧ T.card≤Wᶜ.card+11 := by
  classical
  have mass := quartic_refund J ws ym tm yt safe touch f fi scores full plain capT
  have sc (w : V) (_ : w∈W) : (if w∈L then surcharge (J.degree w) else 0)≤(if w∈L then 155040 else 0) := by
    unfold surcharge; split_ifs <;> decide
  have amount : (∑ w∈W,if w∈L then 155040 else 0)≤1*155040 := by
    rw [←sum_filter,filter_mem_eq_inter,sum_const,nsmul_eq_mul]
    exact Nat.mul_le_mul_right _ ((card_le_card inter_subset_right).trans ls)
  have bd := (sum_le_sum sc).trans amount
  have value : (∑ i∈range 24,squareCost 4 i)=3803046 := by decide
  rw [value] at mass
  by_contra! no
  have each (k : Finset V) (km : k∈W.powersetCard 9) :
      3+(if pairReady J W k then 1 else 0)≤(FiniteRange.bad J W k).card := by
    obtain ⟨T,ct,dom,up⟩ := trial_repair J W k
    have low := no T ct dom
    have sz := (mem_powersetCard.mp km).2
    omega
  have all := sum_le_sum each
  rw [sum_add_distrib,sum_boole,sum_const,card_powersetCard,ws] at all
  simp only [Nat.cast_id] at all
  change 3922512+_≤_ at all
  omega

end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.quartic_refund
#print axioms Graffiti384b.Four28.quartic_sample
