import CliqueEdges

namespace CazenaveOne
open Finset SimpleGraph
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A large clique limits the subordinate adjacency eigenvalue through the
centered cross-block bound. This interface requires an ordered orthogonal pair. -/
theorem clique_complement_spectral (S : Finset V) (hcl : IsCliqueSet G S)
    {t L : ℝ} {x y : V→ℝ} (ht : t≤L)
    (he : AdjEigen G t x) (hE : AdjEigen G L y)
    (hx : ∃ v, x v≠0) (hy : ∃ v, y v≠0) (ho : dot x y=0)
    (q : ℝ) (hqr : (((univ : Finset V) \ S).card:ℝ) ≤ q)
    (hq : (S.card:ℝ)*(((univ : Finset V) \ S).card:ℝ) ≤
      4*q*(q-(((univ : Finset V) \ S).card:ℝ))) :
    t+1≤q := by
  obtain ⟨z,hz,hp,heq⟩ := rayleigh_zero_sum G S ht he hE hx hy ho
  let T := (univ : Finset V) \ S
  let a := lengthSq S z
  let b := lengthSq T z
  let c := 2*block G T S z
  let r : ℝ := T.card
  have ha : 0≤a := lengthSq_nonneg S z
  have hb : 0≤b := lengthSq_nonneg T z
  have hqpos : 0≤q := (Nat.cast_nonneg T.card).trans hqr
  have hcomp : 0≤q-r := sub_nonneg.mpr hqr
  have hlen : lengthSq univ z=b+a := length_partition S z
  have hsq : c^2 ≤ (S.card:ℝ)*r*a*b := cross_block_sq G S T z hz
  have hsq' : c^2≤4*q*(q-r)*a*b :=
    hsq.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq ha) hb)
  have hcross : c≤q*a+(q-r)*b := by
    have hright := add_nonneg (mul_nonneg hqpos ha) (mul_nonneg hcomp hb)
    by_contra! hn
    have hpos : 0≤c := hright.trans hn.le
    have hpow := (sq_lt_sq₀ hright hpos).2 hn
    nlinarith only [sq_nonneg (q*a-(q-r)*b),hsq',hpow]
  have hBB : block G T T z ≤ (r-1)*b := arbitrary_block_bound G T z
  have hEn : energy G z ≤ (q-1)*(b+a) := by
    rw [block_partition G S z,clique_block G S hcl z hz]
    change -a+block G T T z+c ≤ _
    nlinarith only [hBB,hcross]
  have hlenpos : 0<b+a := hlen ▸ hp
  rw [hlen] at heq
  have ht' : t ≤ q-1 := le_of_mul_le_mul_right (heq.trans hEn) hlenpos
  linarith only [ht']

theorem near_clique_randic (S : Finset V) (hcl : IsCliqueSet G S)
    {t L : ℝ} {x y : V→ℝ} (ht : t≤L)
    (he : AdjEigen G t x) (hE : AdjEigen G L y)
    (hx : ∃ v, x v≠0) (hy : ∃ v, y v≠0) (ho : dot x y=0)
    (hsmall : 5*((univ : Finset V) \ S).card ≤ S.card) :
    t+1 ≤ randic G := by
  let T := (univ : Finset V) \ S
  let r : ℝ := T.card
  let k : ℝ := S.card
  have hr : 0≤r := Nat.cast_nonneg _
  have hk : 0≤k := Nat.cast_nonneg _
  have hs : 5*r≤k := by
    dsimp [r,k,T]
    exact_mod_cast hsmall
  by_cases hzero : T.card=0
  · have hzero' : r=0 := by dsimp [r]; exact_mod_cast hzero
    apply le_trans ?_ (randic_nonneg G)
    apply clique_complement_spectral G S hcl ht he hE hx hy ho 0
    · change r≤0
      exact hzero'.le
    · change k*r≤4*0*(0-r)
      simp [hzero']
  · have hr1 : 1≤r := by
      dsimp [r]
      exact_mod_cast (show 1≤T.card by omega)
    have hq : r≤2*k/5 := by linarith only [hr,hs]
    have hq' : k*r ≤ 4*(2*k/5)*(2*k/5-r) := by
      have hprod := mul_nonneg hk (show 0≤k-5*r by linarith only [hs])
      nlinarith only [hprod,sq_nonneg k]
    have ht' : t+1≤2*k/5 := clique_complement_spectral G S hcl ht he hE hx hy ho _ hq hq'
    have nc : T.card + S.card = Fintype.card V := by
      rw [show T = univ \ S from rfl,Finset.card_sdiff (Finset.subset_univ S),Finset.card_univ]
      have := Finset.card_le_card (Finset.subset_univ S)
      simpa using Nat.sub_add_cancel this
    have ncr : r+k=(Fintype.card V:ℝ) := by dsimp [r,k]; exact_mod_cast nc
    have hnR : (1:ℝ)<Fintype.card V := by linarith only [hr1,hs,ncr]
    have hn : 1<Fintype.card V := by exact_mod_cast hnR
    apply ht'.trans (le_trans ?_ (randic_edge_card_lower G hn))
    apply (le_div_iff₀ (sub_pos.mpr hnR)).2
    have hE' : k*(k-1)≤2*(G.edgeFinset.card:ℝ) := clique_edge_card_lower G S hcl
    have hK := mul_nonneg hk (show 0≤k-4*r-1 by linarith only [hs,hr1])
    rw [← ncr]
    nlinarith only [hE',hK]

#print axioms clique_complement_spectral
#print axioms near_clique_randic

/-- An edge-density and clique-size criterion stated entirely in graph
statistics (besides the ordered orthogonal eigenpair interface). -/
theorem clique_density_randic (S : Finset V) (hcl : IsCliqueSet G S)
    (hn : 1<Fintype.card V)
    {t L : ℝ} {x y : V→ℝ} (ht : t≤L)
    (he : AdjEigen G t x) (hE : AdjEigen G L y)
    (hx : ∃ v, x v≠0) (hy : ∃ v, y v≠0) (ho : dot x y=0)
    (q : ℝ) (hqr : (((univ : Finset V) \ S).card:ℝ) ≤ q)
    (hq : (S.card:ℝ)*(((univ : Finset V) \ S).card:ℝ) ≤
      4*q*(q-(((univ : Finset V) \ S).card:ℝ)))
    (hm : q*((Fintype.card V:ℝ)-1)≤G.edgeFinset.card) :
    t+1≤randic G :=
  (clique_complement_spectral G S hcl ht he hE hx hy ho q hqr hq).trans <|
    ((le_div_iff₀ (sub_pos.mpr (by exact_mod_cast hn))).2 hm).trans
      (randic_edge_card_lower G hn)

#print axioms clique_density_randic
end CazenaveOne
