import Perron

namespace CazenaveOne
open Finset SimpleGraph
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- For a sign-changing adjacency eigenvector, all triangle-free graphs with
at least eight edges satisfy the Cazenave inequality. -/
theorem triangleFree_sign_change_ge8 (hf : TriangleFree G) (hc : G.Connected)
    (hm : 8 ≤ G.edgeFinset.card) {t : ℝ} {x : V → ℝ}
    (he : AdjEigen G t x) (hp : ∃ v, 0<x v) (hn : ∃ v, x v<0) :
    t+1 ≤ randic G := by
  have hR := triangleFree_randic G hf
  have hm8 : (8:ℝ) ≤ G.edgeFinset.card := by exact_mod_cast hm
  apply le_trans ?_ hR
  by_cases ht : 0<t
  · let p := (restrict G (posSet x)).edgeFinset.card
    let n := (restrict G (negSet x)).edgeFinset.card
    let m := G.edgeFinset.card
    have hsp : t^2≤(p:ℝ) := positive_support_edges G hf t ht x he hp
    have hsn : t^2≤(n:ℝ) := negative_support_edges G hf t ht x he hn
    have hsum : p+n+1≤m := support_edge_budget G hc x hp hn
    by_cases ht2 : 2≤t
    · apply Real.le_sqrt_of_sq_le
      have hb : (p:ℝ)+n+1≤(m:ℝ) := by exact_mod_cast hsum
      have hmul := mul_nonneg ht.le (sub_nonneg.mpr ht2)
      nlinarith only [hsp,hsn,hb,hmul]
    · by_cases hm9 : 9≤m
      · apply Real.le_sqrt_of_sq_le
        have hh : (9:ℝ)≤m := by exact_mod_cast hm9
        have hb : t^2≤4 := by
          have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_ge ht2))
            (show 0≤2+t by linarith)
          nlinarith only [hprod]
        nlinarith only [hh,hb,(le_of_not_ge ht2 : t ≤ 2)]
      · have hm' : 8≤m := hm
        have hmin : p≤3 ∨ n≤3 := by omega
        have ht3 : t^2≤3 := by
          rcases hmin with h | h
          · exact hsp.trans (by exact_mod_cast h)
          · exact hsn.trans (by exact_mod_cast h)
        have ht4 : t≤7/4 := by
          have htSqrt := Real.le_sqrt_of_sq_le ht3
          have hSqrt : Real.sqrt 3≤(7/4:ℝ) := Real.sqrt_le_iff.2 ⟨by norm_num,by norm_num⟩
          exact htSqrt.trans hSqrt
        have hSqrt : (11/4:ℝ)≤Real.sqrt (G.edgeFinset.card : ℝ) :=
          Real.le_sqrt_of_sq_le ((show (11/4 : ℝ)^2 ≤ 8 by norm_num).trans hm8)
        linarith only [ht4,hSqrt]
  · have hSqrt : (1:ℝ)≤Real.sqrt (G.edgeFinset.card : ℝ) :=
      Real.le_sqrt_of_sq_le ((show (1:ℝ)^2 ≤ 8 by norm_num).trans hm8)
    linarith only [ht,hSqrt]

/-- The same range from an ordered top-two orthogonal adjacency eigenpair.
No sign assumption, spectral radius bound, or Perron theorem is supplied. -/
theorem triangleFree_orthogonal_ge8 (hf : TriangleFree G) (hc : G.Connected)
    (hm : 8 ≤ G.edgeFinset.card) {t L : ℝ} {x y : V → ℝ}
    (ht : t≤L) (he : AdjEigen G t x) (hE : AdjEigen G L y)
    (hx : ∃ v, x v≠0) (hy : ∃ v, y v≠0)
    (hort : (∑ v : V,x v*y v)=0) :
    t+1 ≤ randic G := by
  obtain ⟨hp,hn⟩ := orthogonal_subordinate_signs G hc ht he hE hx hy hort
  exact triangleFree_sign_change_ge8 G hf hc hm he hp hn

#print axioms triangleFree_sign_change_ge8
#print axioms triangleFree_orthogonal_ge8
end CazenaveOne
