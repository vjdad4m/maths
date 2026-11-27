import Energy

namespace CazenaveOne
open Finset SimpleGraph
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def IsCliqueSet (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u≠v → G.Adj u v

theorem block_partition (S : Finset V) (z : V→ℝ) :
    energy G z = block G S S z + block G (univ \ S) (univ \ S) z
      + 2*block G (univ \ S) S z := by
  let T := (univ : Finset V) \ S
  have hpart (f : V→ℝ) : (∑ v : V, f v) = (∑ v ∈ T,f v) + ∑ v ∈ S,f v :=
    (Finset.sum_sdiff (Finset.subset_univ S)).symm
  have hsymm : block G S T z = block G T S z := by
    unfold block
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [coeff_symm G v u]
    ring
  calc
    _ = (∑ u ∈ T, ∑ v, coeff G u v*z u*z v) +
          ∑ u ∈ S, ∑ v, coeff G u v*z u*z v := hpart _
    _ = block G T T z + block G T S z + (block G S T z + block G S S z) := by
      simp_rw [hpart (fun v => coeff G _ v*z _*z v)]
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
      rfl
    _ = _ := by rw [hsymm]; ring

theorem length_partition (S : Finset V) (z : V→ℝ) :
    lengthSq univ z = lengthSq (univ \ S) z + lengthSq S z :=
  (Finset.sum_sdiff (Finset.subset_univ S)).symm

theorem clique_block (S : Finset V) (hs : IsCliqueSet G S)
    (z : V→ℝ) (hz : (∑ u ∈ S, z u) = 0) :
    block G S S z = -lengthSq S z := by
  unfold block lengthSq
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hfilter (v : V) (hv : v ∈ S) :
      coeff G u v*z u*z v = z u*z v-(if v=u then z u^2 else 0) := by
    by_cases h : v=u
    · subst v
      simp [coeff,G.loopless,pow_two]
    · have ha : G.Adj u v := hs u hu v hv (Ne.symm h)
      simp [coeff,ha,h]
  rw [Finset.sum_congr rfl hfilter,Finset.sum_sub_distrib,← Finset.mul_sum,hz,mul_zero]
  rw [Finset.sum_eq_single u (fun v _ hv => by simp [hv]) (fun h => (h hu).elim)]
  simp

private theorem sq_sum_abs (S : Finset V) (z : V→ℝ) :
    (∑ u ∈ S, |z u|)^2 ≤ (S.card:ℝ)*lengthSq S z := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun u => |z u|) (fun _ => (1:ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,sq_abs] at h
  rw [mul_comm] at h
  exact h

theorem arbitrary_block_bound (S : Finset V) (z : V→ℝ) :
    block G S S z ≤ ((S.card:ℝ)-1)*lengthSq S z := by
  have hh : block G S S z ≤ ∑ u ∈ S, ∑ v ∈ S,
      (|z u| *|z v|-(if v=u then z u^2 else 0)) := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    by_cases eq : v=u
    · subst v
      simp [coeff,G.loopless,← abs_mul,pow_two]
    · by_cases ha : G.Adj u v
      · simpa [coeff,ha,eq,← abs_mul] using le_abs_self (z u*z v)
      · simp [coeff,ha,eq]
        positivity
  have hEq : (∑ u ∈ S, ∑ v ∈ S,
      (|z u| *|z v|-(if v=u then z u^2 else 0))) =
      (∑ u ∈ S, |z u|)^2 - lengthSq S z := by
    simp_rw [Finset.sum_sub_distrib,← Finset.mul_sum]
    rw [← Finset.sum_mul,pow_two]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.sum_eq_single u (fun v _ hv => by simp [hv]) (fun e => (e hu).elim)]
    simp
  rw [hEq] at hh
  linarith only [hh,sq_sum_abs S z]

theorem cross_block_sq (S T : Finset V) (z : V→ℝ)
    (hz : (∑ u ∈ S,z u)=0) :
    (2*block G T S z)^2 ≤
      (S.card:ℝ)*(T.card:ℝ)*lengthSq S z*lengthSq T z := by
  have hcenter :
      block G T S z = ∑ u ∈ T, ∑ v ∈ S, (coeff G u v-1/2)*z u*z v := by
    unfold block
    apply Finset.sum_congr rfl
    intro u _
    have e (v : V) : (coeff G u v-1/2)*z u*z v =
        coeff G u v*z u*z v - (z u/2)*z v := by ring
    simp_rw [e,Finset.sum_sub_distrib,← Finset.mul_sum,hz,mul_zero,sub_zero]
  have hAbs : |block G T S z| ≤ ((∑ u ∈ T,|z u|)*(∑ v ∈ S,|z v|))/2 := by
    rw [hcenter]
    calc
      _ ≤ ∑ u ∈ T, |∑ v ∈ S, (coeff G u v-1/2)*z u*z v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u ∈ T, ∑ v ∈ S, |(coeff G u v-1/2)*z u*z v| :=
        Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        have h (u v : V) : |(coeff G u v-1/2)*z u*z v| = (1/2)*|z u| *|z v| := by
          rw [abs_mul,abs_mul]
          congr 2
          by_cases e : G.Adj u v <;> norm_num [coeff,e]
        simp_rw [h,← Finset.mul_sum,← Finset.sum_mul]
        rw [← Finset.mul_sum]
        ring
  have hh0 := abs_nonneg (block G T S z)
  have hprod : 0 ≤ (∑ u ∈ T,|z u|)*(∑ v ∈ S,|z v|) := by positivity
  have hh := (sq_le_sq₀ hh0 (show 0 ≤ _/2 from div_nonneg hprod (by norm_num))).2 hAbs
  rw [sq_abs,div_pow,mul_pow] at hh
  have hprodSq := mul_le_mul (sq_sum_abs T z) (sq_sum_abs S z)
    (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (lengthSq_nonneg T z))
  calc
    _ = 4*(block G T S z)^2 := by ring
    _ ≤ (∑ u ∈ T,|z u|)^2*(∑ v ∈ S,|z v|)^2 := by linarith only [hh]
    _ ≤ _ := by convert hprodSq using 1; ring

#print axioms clique_block
#print axioms arbitrary_block_bound
#print axioms cross_block_sq
end CazenaveOne
