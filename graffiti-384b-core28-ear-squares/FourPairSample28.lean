import FourPairRebate28
import FourSquareSample28
namespace Graffiti384b.Four28
open Finset SimpleGraph
open private FiniteRange.bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]

/-- Two adjacent uncredited neighbors may replace the single allowed exception
at scores two and three. The repair choice depends on the sample. -/
theorem repaired_sample {W : Finset V} (ws : W.card=24) {s : ℕ} (small : s=2 ∨ s=3)
    {x y : V} (xy : J.Adj x y) (xn : J.neighborFinset x⊆W) (yn : J.neighborFinset y⊆W)
    (f : V → ℕ) (fi : Function.Injective f)
    (scores : ∀ w∈W,2≤f w ∧ f w≠s)
    (full : ∀ w∈W,f w≤(turanGraph (J.degree w+1) 3).edgeFinset.card ∨ 10≤J.degree w)
    (plain : ∀ w∈W,w∉({x,y}:Finset V) → (∀ z,z∉W → ¬J.Adj w z) →
      f w≤(turanGraph (J.degree w) 3).edgeFinset.card ∨ 10≤J.degree w) :
    ∃ T,Wᶜ⊆T ∧ TwoDominates J T ∧ T.card≤Wᶜ.card+11 := by
  classical
  have sm : s∈Icc 2 5 := mem_Icc.mpr (by omega)
  have mass := square_mass J ws sm f fi scores full plain
  have xw := yn ((J.mem_neighborFinset ..).mpr xy.symm)
  have yw := xn ((J.mem_neighborFinset ..).mpr xy)
  have sub : ({x,y}:Finset V)⊆W := insert_subset xw (singleton_subset_iff.mpr yw)
  have two : (∑ w∈W,if w∈({x,y}:Finset V) then surcharge (J.degree w) else 0)=
      surcharge (J.degree x)+surcharge (J.degree y) := by
    rw [←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr sub,sum_pair xy.ne]
  have value : (∑ i∈range 24,squareCost s i)=3651882 := by
    rcases small with rfl|rfl <;> decide
  rw [value,two] at mass
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
  change 3922512+((W.powersetCard 9).filter (pairReady J W)).card≤_ at all
  by_cases xd : J.degree x≤4
  · by_cases yd : J.degree y≤4
    · have low : 2≤J.degree x := by
        by_contra! less
        have lo := (scores x xw).1
        rcases full x xw with cap|big
        · have t := RankTable.cap_table ⟨J.degree x+1,by omega⟩ ⟨3,by decide⟩ (by decide)
          change (turanGraph (J.degree x+1) 3).edgeFinset.card=RankTable.cap (J.degree x+1) 3 at t
          rw [t] at cap
          have dg : J.degree x=0 ∨ J.degree x=1 := by omega
          rcases dg with z|z <;> rw [z] at cap <;> norm_num [RankTable.cap,Nat.choose] at cap <;> omega
        · omega
      have plus := pair_frequency J ws xy xn yn low xd yd
      simp only [surcharge,if_pos xd,if_pos yd] at mass
      omega
    · simp only [surcharge,if_pos xd,if_neg yd] at mass; omega
  · unfold surcharge at mass; rw [if_neg xd] at mass; split_ifs at mass <;> omega
end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.repaired_sample
