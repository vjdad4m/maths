import Core

namespace CazenaveOne

/-- Numerical consequence of the externally proved Bollobás–Nikiforov
inequality and the Randić lower bound by edge count divided by spectral radius.
This lemma does not itself prove either input bound for graphs. -/
theorem clique_high (m L t k R : ℝ) (hL : 0 < L) (hk : 1 < k)
    (hBN : L^2+t^2 ≤ 2*(1-k⁻¹)*m) (hR : m ≤ L*R)
    (ht : k-1 ≤ t) : t+1 ≤ R := by
  have hk0 : 0<k := by linarith
  have hki : 1-k⁻¹ > 0 := by
    rw [inv_eq_one_div]
    have hh : (1:ℝ)/k < 1 := (div_lt_iff₀ hk0).2 (by simpa only [one_mul] using hk)
    linarith only [hh]
  have hki' : k*k⁻¹=1 := mul_inv_cancel₀ hk0.ne'
  have hr : 2*(1-k⁻¹)*m ≤ 2*(1-k⁻¹)*(L*R) :=
    mul_le_mul_of_nonneg_left hR (by positivity)
  have ht' : 0≤(t+1-k)*k⁻¹ := mul_nonneg (by linarith only [ht]) (inv_nonneg.mpr hk0.le)
  have haux := mul_nonneg hL.le ht'
  have hx := sq_nonneg (L-t)
  have hn : 2*(1-k⁻¹)*(L*(t+1)) ≤ L^2+t^2 := by
    have haux' : 0≤L*((t+1)*k⁻¹-1) := by
      calc
        0 ≤ L*((t+1-k)*k⁻¹) := haux
        _ = L*((t+1)*k⁻¹-1) := by
          congr 1
          rw [sub_mul,hki']
    nlinarith only [hx,haux']
  exact le_of_mul_le_mul_left
    (le_of_mul_le_mul_left (hn.trans (hBN.trans hr)) (by positivity : 0 < 2*(1-k⁻¹))) hL

theorem clique_order (m L t k R order : ℝ) (hL : 0 < L) (hk : 1 < k)
    (hBN : L^2+t^2 ≤ 2*(1-k⁻¹)*m) (hR : m ≤ L*R)
    (hRb : Real.sqrt (order-1) ≤ R) (horder : k^2+1 ≤ order) : t+1 ≤ R := by
  by_cases h : k - 1 ≤ t
  · exact clique_high m L t k R hL hk hBN hR h
  · have hsq : k^2≤order-1 := by linarith
    have := (Real.le_sqrt_of_sq_le hsq).trans hRb
    linarith only [h,this]

#print axioms clique_high
#print axioms clique_order
end CazenaveOne
