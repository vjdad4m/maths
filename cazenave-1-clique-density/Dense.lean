import NearClique

namespace CazenaveOne
open Finset SimpleGraph
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem energy_lower_of_degree (z : V→ℝ) (δ : ℝ)
    (hd : ∀ u : V, (G.degree u:ℝ)≤δ) :
    -(δ*lengthSq univ z) ≤ energy G z := by
  unfold energy
  have hnon (u v : V) : 0≤coeff G u v := by
    by_cases h : G.Adj u v <;> simp [coeff,h]
  have hmain : (∑ u : V, ∑ v : V, -(coeff G u v * ((z u)^2+(z v)^2))) ≤
      ∑ u : V, ∑ v : V, 2*(coeff G u v*z u*z v) := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    nlinarith only [mul_nonneg (hnon u v) (sq_nonneg (z u+z v))]
  have hE (u : V) : (∑ v : V, coeff G u v) = (G.degree u:ℝ) := by
    simpa only [mul_one,Finset.sum_const,nsmul_eq_mul,
      G.card_neighborFinset_eq_degree] using sum_coeff G u (fun _ => 1)
  have hF : (∑ u : V, ∑ v : V, coeff G u v*(z u)^2) = ∑ u : V, (G.degree u:ℝ)*(z u)^2 := by
    apply Finset.sum_congr rfl
    intro u _
    rw [← Finset.sum_mul,hE]
  have hF' : (∑ u : V, ∑ v : V, coeff G u v*(z v)^2) = ∑ u : V, (G.degree u:ℝ)*(z u)^2 := by
    rw [Finset.sum_comm,← hF]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [coeff_symm G v u]
  simp_rw [mul_add, Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hmain
  rw [hF,hF'] at hmain
  have hh : (∑ u : V, (G.degree u:ℝ)*(z u)^2) ≤ δ*lengthSq univ z := by
    unfold lengthSq
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_right (hd u) (sq_nonneg _))
  linarith only [hmain,hh]

theorem energy_complement_zero (z : V→ℝ)
    (hzero : (∑ u : V,z u)=0) :
    energy G z + energy Gᶜ z = -lengthSq univ z := by
  unfold energy
  simp_rw [← Finset.sum_add_distrib]
  have hsum : (∑ u : V, ∑ v : V,
      (coeff G u v*z u*z v+coeff Gᶜ u v*z u*z v)) =
      block (⊤ : SimpleGraph V) univ univ z := by
    unfold block
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases huv : u=v
    · subst v
      simp [coeff,G.loopless]
    · by_cases he : G.Adj u v <;> simp [coeff,he,huv,SimpleGraph.compl_adj]
  rw [hsum]
  exact clique_block (⊤ : SimpleGraph V) univ (fun _ _ _ _ hn => hn) z hzero

/-- Any real upper bound on complement degrees bounds t+1. -/
theorem complement_degree_spectral (δ : ℝ) (hd : ∀ u : V, (Gᶜ.degree u:ℝ)≤δ)
    {t L : ℝ} {x y : V→ℝ} (ht : t≤L)
    (he : AdjEigen G t x) (hE : AdjEigen G L y)
    (hx : ∃ v, x v≠0) (hy : ∃ v, y v≠0) (ho : dot x y=0) :
    t+1≤δ := by
  obtain ⟨z,hz,hp,hEn⟩ := rayleigh_zero_sum G univ ht he hE hx hy ho
  have hLower := energy_lower_of_degree Gᶜ z δ hd
  have hComp := energy_complement_zero G z hz
  have hb : energy G z ≤ (δ-1)*lengthSq univ z := by linarith only [hLower,hComp]
  have hh := le_of_mul_le_mul_right (hEn.trans hb) hp
  linarith only [hh]

theorem very_dense_randic (hn : 1<Fintype.card V) (d : ℝ)
    (hd : ∀ u : V, d ≤ (G.degree u:ℝ))
    (hcond : ((Fintype.card V:ℝ)-1-d) * 2*((Fintype.card V:ℝ)-1) ≤
      (Fintype.card V:ℝ)*d)
    {t L : ℝ} {x y : V→ℝ} (ht : t≤L)
    (he : AdjEigen G t x) (hE : AdjEigen G L y)
    (hx : ∃ v, x v≠0) (hy : ∃ v, y v≠0) (ho : dot x y=0) :
    t+1≤randic G := by
  let N : ℝ := Fintype.card V
  have hN : 1<N := by dsimp [N]; exact_mod_cast hn
  have hnd (u : V) : (Gᶜ.degree u:ℝ)≤N-1-d := by
    have hNat : Gᶜ.degree u + G.degree u + 1 = Fintype.card V := by
      have h := G.degree_compl u
      have h' := G.degree_lt_card_verts u
      omega
    have hReal : (Gᶜ.degree u:ℝ) + (G.degree u:ℝ) + 1 = N := by
      dsimp [N]
      exact_mod_cast hNat
    linarith only [hReal,hd u]
  apply (complement_degree_spectral G (N-1-d) hnd ht he hE hx hy ho).trans
  apply le_trans ?_ (randic_edge_card_lower G hn)
  apply (le_div_iff₀ (sub_pos.mpr hN)).2
  have hh := Finset.sum_le_sum (s:=univ) (fun u _ => hd u)
  rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ] at hh
  have hsum : (∑ u : V,(G.degree u:ℝ)) = 2*(G.edgeFinset.card:ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  change N*d ≤ _ at hh
  rw [hsum] at hh
  nlinarith only [hcond,hh]

#print axioms complement_degree_spectral
#print axioms very_dense_randic
end CazenaveOne
