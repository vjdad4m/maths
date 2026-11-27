import Perron

namespace CazenaveOne
open Finset SimpleGraph
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def coeff (u v : V) : ℝ := if G.Adj u v then 1 else 0
noncomputable def dot (x y : V → ℝ) : ℝ := ∑ u, x u*y u
noncomputable def block (S T : Finset V) (x : V → ℝ) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ T, coeff G u v * x u * x v
noncomputable def lengthSq (S : Finset V) (x : V → ℝ) : ℝ :=
  ∑ u ∈ S, x u^2
noncomputable def energy (x : V → ℝ) : ℝ :=
  ∑ u, ∑ v, coeff G u v * x u * x v

theorem coeff_symm (u v : V) : coeff G u v = coeff G v u := by
  by_cases h : G.Adj u v
  · simp [coeff,h,h.symm]
  · simp [coeff,h,show ¬ G.Adj v u from fun e => h e.symm]

theorem sum_coeff (u : V) (x : V→ℝ) :
    (∑ v : V, coeff G u v * x v) = ∑ v ∈ G.neighborFinset u, x v := by
  have h : (univ.filter (fun v => G.Adj u v) : Finset V) = G.neighborFinset u := by
    ext v
    simp [G.mem_neighborFinset]
  rw [← h,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases ha : G.Adj u v <;> simp [coeff,ha]

theorem energy_eq (x : V→ℝ) :
    energy G x = ∑ u, x u * (∑ v ∈ G.neighborFinset u, x v) := by
  unfold energy
  apply Finset.sum_congr rfl
  intro u _
  rw [← sum_coeff G,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem lengthSq_nonneg (S : Finset V) (x : V → ℝ) :
    0 ≤ lengthSq S x := Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem lengthSq_pos {x : V → ℝ} (hx : ∃ u, x u ≠ 0) :
    0 < lengthSq (univ : Finset V) x := by
  obtain ⟨u,hu⟩ := hx
  have h := Finset.single_le_sum (fun w (_ : w ∈ (univ : Finset V)) => sq_nonneg (x w))
    (mem_univ u)
  exact (sq_pos_of_ne_zero hu).trans_le h

theorem rayleigh_zero_sum (S : Finset V) {t L : ℝ} {x y : V → ℝ}
    (ht : t ≤ L) (he : AdjEigen G t x) (hE : AdjEigen G L y)
    (hx : ∃ v, x v ≠ 0) (hy : ∃ v, y v ≠ 0) (hort : dot x y = 0) :
    ∃ z : V → ℝ, (∑ v ∈ S, z v) = 0 ∧ 0 < lengthSq univ z ∧
      t * lengthSq univ z ≤ energy G z := by
  let a := ∑ v ∈ S, x v
  let b := ∑ v ∈ S, y v
  by_cases ha : a = 0
  · refine ⟨x,ha,lengthSq_pos hx,?_⟩
    rw [energy_eq]
    apply le_of_eq
    unfold lengthSq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [← he u]
    ring
  · let z (u : V) := b*x u-a*y u
    have hzsum : (∑ v ∈ S,z v)=0 := by
      dsimp [z]
      rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum]
      change b*a-a*b=0
      ring
    have hortr : dot y x = 0 := by
      rw [← hort]
      apply Finset.sum_congr rfl
      intro v _
      ring
    have hdot : (∑ u, y u*z u) = -a*lengthSq univ y := by
      calc
        _ = (∑ u, (b*(y u*x u) - a*(y u)^2)) := by
          apply Finset.sum_congr rfl
          intro u _
          dsimp [z]
          ring
        _ = _ := by
          rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum]
          change b*dot y x-a*lengthSq univ y = _
          rw [hortr]
          ring
    have hposy := lengthSq_pos hy
    have hnz : ∃ u, z u≠0 := by
      by_contra! h
      have hzero : (∑ u, y u*z u)=0 := by simp [h]
      rw [hzero] at hdot
      rcases mul_eq_zero.mp hdot.symm with e | e
      · exact ha (neg_eq_zero.mp e)
      · exact hposy.ne' e
    refine ⟨z,hzsum,lengthSq_pos hnz,?_⟩
    rw [energy_eq]
    have hr (u : V) : (∑ v ∈ G.neighborFinset u,z v) = t*z u+(t-L)*a*y u := by
      dsimp [z]
      rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,← he,← hE]
      ring
    simp_rw [hr]
    have hh : (∑ u, z u*(t*z u+(t-L)*a*y u)) =
        t*lengthSq univ z + (t-L)*a*(-a*lengthSq univ y) := by
      calc
        _ = ∑ u, (t*(z u)^2+(t-L)*a*(y u*z u)) := by
          apply Finset.sum_congr rfl
          intro u _
          ring
        _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,hdot]; rfl
    rw [hh]
    have hp := mul_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg a)) hposy.le
    nlinarith only [hp]

#print axioms rayleigh_zero_sum
end CazenaveOne
