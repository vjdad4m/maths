import FourPool28
namespace Graffiti384b.Four28
open Finset SimpleGraph JointRank
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]

def required (s i : ℕ) := 2+i+(if s≤2+i then 1 else 0)
def squareCost (s i : ℕ) : ℕ :=
  let row : List ℕ := if s≤3 then [545870,394706,394706,267410,267410,267410,170170,170170,170170,170170,101530,101530,101530,101530,56485,56485,56485,56485,56485,29029,29029,29029,29029,29029]
    else [545870,545870,394706,267410,267410,267410,170170,170170,170170,170170,101530,101530,101530,101530,56485,56485,56485,56485,56485,29029,29029,29029,29029,29029]
  row[i]?.getD 0
def surcharge (d : ℕ) := if d≤4 then 155040 else 97240

def allowance (s : ℕ) := if s≤3 then 1 else 0

set_option maxRecDepth 32768 in
private theorem square_rows : ∀ s∈Icc 2 5,∀ i : Fin 24,∀ d : Fin 11,
    ((required s i≤RankTable.cap (d.val+1) 3 ∨ d.val=10) →
      (24-d.val).choose 9≤squareCost s i ∧
      FiniteRange.badCount 24 9 d≤squareCost s i+surcharge d) ∧
    ((required s i≤RankTable.cap d 3 ∨ d.val=10) →
      FiniteRange.badCount 24 9 d≤squareCost s i) := by
  unfold squareCost surcharge required RankTable.cap FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide

private theorem squares_total : ∀ s∈Icc 2 5,
    (∑ i∈range 24,squareCost s i)+allowance s*155040<3*(24:ℕ).choose 9 := by
  unfold squareCost allowance
  simp only [Nat.choose_eq_fast_choose]
  decide

set_option maxHeartbeats 800000 in
/-- The pool excludes scores one and s. An uncredited exterior neighbor
of the second omitted vertex incurs an explicit extra repair charge. -/
theorem square_mass {W L : Finset V} (ws : W.card=24) {s : ℕ} (small : s∈Icc 2 5)
    (f : V → ℕ) (fi : Function.Injective f)
    (scores : ∀ w∈W,2≤f w ∧ f w≠s)
    (full : ∀ w∈W,f w≤(turanGraph (J.degree w+1) 3).edgeFinset.card ∨ 10≤J.degree w)
    (plain : ∀ w∈W,w∉L → (∀ z,z∉W → ¬J.Adj w z) →
      f w≤(turanGraph (J.degree w) 3).edgeFinset.card ∨ 10≤J.degree w) :
    (∑ k∈W.powersetCard 9,(FiniteRange.bad J W k).card) ≤
      (∑ i∈range 24,squareCost s i)+∑ w∈W,(if w∈L then surcharge (J.degree w) else 0) := by
  classical
  let g (v : V) := f v-(if s<f v then 1 else 0)
  have inj : Set.InjOn g (W:Set V) := by
    intro x xm y ym eq
    have := scores x xm; have := scores y ym
    apply fi; unfold g at eq; split_ifs at eq <;> omega
  have base (v : V) (vm : v∈W) : 2≤g v := by
    have := scores v vm; have := mem_Icc.mp small
    unfold g; split_ifs <;> omega
  let rk := rank W g
  have costs (v : V) (vm : v∈W) : fibers J W 9 v≤squareCost s (rk v)+(if v∈L then surcharge (J.degree v) else 0) := by
    have range' := mem_image_of_mem (rank W g) vm
    rw [rank_range W g inj,ws,mem_range] at range'
    have low := rank_lower W g inj 2 base vm
    change 2+rk v≤f v-(if s<f v then 1 else 0) at low
    have sc := scores v vm
    have lb : required s (rk v)≤f v := by unfold required; split_ifs at * <;> omega
    let d := min (J.degree v) 10
    have dh : d≤10 := min_le_right ..
    have dl : d≤J.degree v := min_le_left ..
    have eq (ne : d≠10) : J.degree v=d := by dsimp [d] at *; omega
    have asCap (d' : ℕ) (dsmall : d'<12) :
        (turanGraph d' 3).edgeFinset.card=RankTable.cap d' 3 :=
      RankTable.cap_table ⟨d',dsmall⟩ ⟨3,by decide⟩ (by decide)
    have rows := square_rows s small ⟨rk v,range'⟩ ⟨d,by omega⟩
    dsimp only at rows
    have one : required s (rk v)≤RankTable.cap (d+1) 3 ∨ d=10 := by
      by_cases hi : d=10
      · exact Or.inr hi
      · rcases full v vm with le|big
        · rw [eq hi,asCap _ (by omega)] at le
          exact Or.inl (lb.trans le)
        · have := eq hi; omega
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
  rw [sum_add_distrib,sum_by_rank W g inj,ws] at lim
  rw [total]
  exact lim

theorem square_sample {W L : Finset V} (ws : W.card=24) {s : ℕ} (small : s∈Icc 2 5)
    (size : L.card≤allowance s) (f : V → ℕ) (fi : Function.Injective f)
    (scores : ∀ w∈W,2≤f w ∧ f w≠s)
    (full : ∀ w∈W,f w≤(turanGraph (J.degree w+1) 3).edgeFinset.card ∨ 10≤J.degree w)
    (plain : ∀ w∈W,w∉L → (∀ z,z∉W → ¬J.Adj w z) →
      f w≤(turanGraph (J.degree w) 3).edgeFinset.card ∨ 10≤J.degree w) :
    ∃ k∈W.powersetCard 9,(FiniteRange.bad J W k).card≤2 := by
  classical
  have lim := square_mass J ws small f fi scores full plain (L:=L)
  have sc (w : V) (_ : w∈W) : (if w∈L then surcharge (J.degree w) else 0)≤(if w∈L then 155040 else 0) := by
    unfold surcharge; split_ifs <;> decide
  have amount : (∑ w∈W,if w∈L then 155040 else 0)≤allowance s*155040 := by
    rw [←sum_filter,filter_mem_eq_inter,sum_const,nsmul_eq_mul]
    exact Nat.mul_le_mul_right _ ((card_le_card inter_subset_right).trans size)
  by_contra! none
  have many := sum_le_sum (s:=W.powersetCard 9) (f:=fun _ => 3) (g:=fun k => (FiniteRange.bad J W k).card)
    (fun k km => show 3≤_ from none k km)
  simp only [sum_const,nsmul_eq_mul,card_powersetCard,ws,Nat.cast_id] at many
  have bd := (sum_le_sum sc).trans amount
  have win := squares_total s small
  omega
end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.square_mass
#print axioms Graffiti384b.Four28.square_sample
