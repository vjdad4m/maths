import Cross

namespace CazenaveOne
open Finset SimpleGraph
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- If at least four fifths of the vertices are in one clique, the
Randić index bounds the subordinate eigenvalue plus one. -/
theorem four_fifths_clique_randic (S : Finset V) (hcl : IsCliqueSet G S)
    {t L : ℝ} {x y : V→ℝ} (ht : t≤L)
    (he : AdjEigen G t x) (hE : AdjEigen G L y)
    (hx : ∃ v, x v≠0) (hy : ∃ v, y v≠0) (ho : dot x y=0)
    (hsmall : 4*((univ : Finset V) \ S).card ≤ S.card) :
    t+1 ≤ randic G := by
  let T := (univ : Finset V) \ S
  let r : ℝ := T.card
  let k : ℝ := S.card
  let e : ℝ := (crossPairs G S T).card
  let n : ℝ := Fintype.card V
  let m : ℝ := G.edgeFinset.card
  have hr : 0≤r := Nat.cast_nonneg _
  have hk : 0≤k := Nat.cast_nonneg _
  have hs : 4*r≤k := by
    dsimp [r,k,T]
    exact_mod_cast hsmall
  by_cases hzero : T.card=0
  · apply near_clique_randic G S hcl ht he hE hx hy ho
    change 5*T.card≤S.card
    omega
  have hr1 : 1≤r := by
    dsimp [r]
    exact_mod_cast (show 1≤T.card by omega)
  have hk4 : 4≤k := by linarith only [hs,hr1]
  have nc : T.card + S.card = Fintype.card V := by
    rw [show T = univ \ S from rfl,Finset.card_sdiff (Finset.subset_univ S),Finset.card_univ]
    have := Finset.card_le_card (Finset.subset_univ S)
    simpa using Nat.sub_add_cancel this
  have ncr : r+k=n := by dsimp [r,k,n]; exact_mod_cast nc
  have hnR : (1:ℝ)<n := by linarith only [hr1,hk4,ncr]
  have hn : 1<Fintype.card V := by dsimp [n] at hnR; exact_mod_cast hnR
  by_cases h : e≤k^2/24
  · have hq : r≤3*k/8 := by linarith only [hs,hk4]
    have hq' : e≤(3*k/8)*(3*k/8-r) := by
      have hp := mul_nonneg hk (show 0≤k-4*r by linarith only [hs])
      nlinarith only [hp,h,sq_nonneg k]
    have htq : t+1≤3*k/8 := clique_cross_spectral G S hcl ht he hE hx hy ho _ hq hq'
    apply htq.trans (le_trans ?_ (randic_edge_card_lower G hn))
    apply (le_div_iff₀ (sub_pos.mpr hnR)).2
    have hh : k*(k-1)≤2*m := clique_edge_card_lower G S hcl
    have h₁ := mul_nonneg hk (show 0≤k-4*r by linarith only [hs])
    have h₂ := mul_nonneg hk (show 0≤k-4 by linarith only [hk4])
    change (3*k/8)*(n-1)≤m
    rw [← ncr]
    nlinarith only [hh,h₁,h₂]
  · have hq : r≤5*k/12 := by linarith only [hs,hk4]
    have hq' : k*r≤4*(5*k/12)*(5*k/12-r) := by
      have hprod := mul_nonneg hk (show 0≤k-4*r by linarith only [hs])
      nlinarith only [hprod,sq_nonneg k]
    have hm : (5*k/12)*(n-1)≤m := by
      have hh : k*(k-1)+2*e≤2*m := clique_plus_cross G S hcl
      have h₁ := mul_nonneg hk (show 0≤k-4*r by linarith only [hs])
      have h₂ := mul_nonneg hk (show 0≤k-4 by linarith only [hk4])
      rw [← ncr]
      nlinarith only [hh,h₁,h₂,h]
    exact clique_density_randic G S hcl hn ht he hE hx hy ho _ hq hq' hm

#print axioms four_fifths_clique_randic
end CazenaveOne
