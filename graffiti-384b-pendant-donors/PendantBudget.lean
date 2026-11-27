import Remaining29
import BoundaryFiber384b
import JointRank384b

namespace Graffiti384b.Donor
open Finset SimpleGraph JointRank
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def exposed (X : Finset V) := X.filter (fun v => ∃w∉X,G.Adj v w)

private def rankDegree (i : ℕ) :=
  if i<2 then 3 else if i<5 then 4 else if i<9 then 5 else if i<14 then 6 else if i<20 then 7 else 8

private def cost (b floor price i : ℕ) :=
  let d := max floor (rankDegree i)
  max (FiniteRange.badCount 26 b d) ((26-d).choose b+price)

/-- A fixed exterior contact gives the exact zero-hit upper bound. The
same price is transferred at every exposed vertex before summing by rank. -/
private theorem budget26 (X : Finset V) (sz : X.card=26)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (pos : ∀v∈X,2≤trianglesAt G v)
    (floor b price : ℕ) (small : floor≤8) (degrees : ∀v∈X,floor≤G.degree v) :
    (∑ k∈X.powersetCard b,(FiniteRange.bad G X k).card) + (exposed G X).card*price ≤
      ∑ i∈range 26,cost b floor price i := by
  classical
  let r := rank X (trianglesAt G)
  let count (v : V) := ((X.powersetCard b).filter (fun k => v∈FiniteRange.bad G X k)).card
  let credit (v : V) := if v∈exposed G X then price else 0
  have each (v : V) (vm : v∈X) : count v+credit v≤cost b floor price (r v) := by
    have ri : r v<26 := mem_range.mp (by rw [←sz,←rank_range X (trianglesAt G) inj]; exact mem_image_of_mem _ vm)
    have lo := rank_lower X (trianglesAt G) inj 2 pos vm
    change 2+r v≤trianglesAt G v at lo
    have cap := Repair.triangles_le_choose G v
    have dsmall : rankDegree (r v)≤8 := by unfold rankDegree; split_ifs <;> decide
    have required : rankDegree (r v)≤G.degree v := by
      by_cases big : 8≤G.degree v
      · exact dsmall.trans big
      have table : ∀ d : Fin 8,∀ i : Fin 26,2+i.val≤d.val.choose 2 → rankDegree i≤d := by decide
      exact table ⟨G.degree v,Nat.lt_of_not_ge big⟩ ⟨r v,ri⟩ (lo.trans cap)
    let d := max floor (rankDegree (r v))
    have den : d≤G.degree v := max_le (degrees v vm) required
    have up : d≤8 := max_le small dsmall
    have one : 1≤d := by dsimp [d]; unfold rankDegree; split_ifs <;> omega
    by_cases ex : v∈exposed G X
    · obtain ⟨w,wx,vw⟩ := (mem_filter.mp ex).2
      have lim := BoundaryFiber.count G X b d vm wx vw den one
      rw [sz] at lim
      change count v+credit v ≤ max (FiniteRange.badCount 26 b d) ((26-d).choose b+price)
      simp only [credit,if_pos ex]
      exact (Nat.add_le_add_right lim price).trans (le_max_right ..)
    · have lim := FiniteRange.count_bad G X b d v vm den (by omega)
      rw [sz] at lim
      simp only [credit,if_neg ex,Nat.add_zero]
      exact lim.trans (le_max_left ..)
  have total := sum_le_sum each
  rw [sum_add_distrib,sum_by_rank X (trianglesAt G) inj,sz] at total
  have c : (∑v∈X,credit v)=(exposed G X).card*price := by
    simp only [credit,←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr (show exposed G X⊆X from filter_subset ..),sum_const,nsmul_eq_mul,Nat.cast_id]
  have swap : (∑ k∈X.powersetCard b,(FiniteRange.bad G X k).card)=∑v∈X,count v := by
    calc
      _ = ∑k∈X.powersetCard b,∑v∈X,if v∈FiniteRange.bad G X k then 1 else 0 := by
        apply sum_congr rfl; intro k _
        simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (show FiniteRange.bad G X k⊆X from (filter_subset ..).trans sdiff_subset)]
      _ = _ := by rw [sum_comm]; simp [count]
  rwa [swap,←c]

/-- The alternatives use the same rank certificate. The count of exterior
contacts may include retained vertices besides the pendant triangle's root. -/
theorem sample26 (X : Finset V) (sz : X.card=26)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (pos : ∀v∈X,2≤trianglesAt G v)
    (degree3 : ∀v∈X,3≤G.degree v)
    (regime : 14≤(exposed G X).card ∨
      (12≤(exposed G X).card ∧ ∀v∈X,4≤G.degree v) ∨
      (1≤(exposed G X).card ∧ ∀v∈X,5≤G.degree v)) :
    ∃k⊆X,k.card+(FiniteRange.bad G X k).card≤12 := by
  classical
  have win (b floor price n : ℕ) (bsmall : b≤12) (fs : floor≤8)
      (degrees : ∀v∈X,floor≤G.degree v) (hits : n≤(exposed G X).card)
      (table : (∑ i∈range 26,cost b floor price i)<(13-b)*(26:ℕ).choose b+n*price) :
      ∃k⊆X,k.card+(FiniteRange.bad G X k).card≤12 := by
    by_contra! none
    have total := budget26 G X sz inj pos floor b price fs degrees
    have lo := sum_le_sum (s:=X.powersetCard b) (fun k km => show 13-b≤(FiniteRange.bad G X k).card by
      obtain ⟨sub,eq⟩ := mem_powersetCard.mp km; have := none k sub; omega)
    simp only [sum_const,smul_eq_mul,card_powersetCard,sz] at lo
    rw [Nat.mul_comm] at lo
    have credit := Nat.mul_le_mul_right price hits
    omega
  rcases regime with h|⟨h,d⟩|⟨h,d⟩
  · exact win 9 3 377910 14 (by decide) (by decide) degree3 h (by unfold cost rankDegree FiniteRange.badCount; simp only [Nat.choose_eq_fast_choose]; decide)
  · exact win 9 4 262548 12 (by decide) (by decide) d h (by unfold cost rankDegree FiniteRange.badCount; simp only [Nat.choose_eq_fast_choose]; decide)
  · exact win 10 5 170170 1 (by decide) (by decide) d h (by unfold cost rankDegree FiniteRange.badCount; simp only [Nat.choose_eq_fast_choose]; decide)

end Graffiti384b.Donor
#print axioms Graffiti384b.Donor.sample26
