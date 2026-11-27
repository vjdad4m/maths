import Nodal

namespace CazenaveOne
open Finset SimpleGraph
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem nonneg_zero_neighbor {t : ℝ} {x : V → ℝ} (he : AdjEigen G t x)
    (hn : ∀ v, 0≤x v) {u v : V} (hu : x u=0) (ha : G.Adj u v) : x v=0 := by
  have hsum : (∑ w ∈ G.neighborFinset u,x w)=0 := by rw [← he u,hu,mul_zero]
  have h := Finset.single_le_sum (fun w (_ : w ∈ G.neighborFinset u) => hn w)
    ((G.mem_neighborFinset u v).mpr ha)
  linarith only [hsum,h,hn v]

theorem nonneg_zero_propagates (hc : G.Connected) {t : ℝ} {x : V → ℝ}
    (he : AdjEigen G t x) (hn : ∀ v, 0≤x v) {u : V} (hu : x u=0) :
    ∀ v, x v=0 := by
  intro v
  obtain ⟨p⟩ := hc.preconnected u v
  induction p with
  | nil => exact hu
  | cons ha _ ih => exact ih (nonneg_zero_neighbor G he hn hu ha)

private theorem no_ordered_orthogonal_nonnegative
    (hc : G.Connected) {t L : ℝ} {x y : V→ℝ}
    (htL : t≤L) (he : AdjEigen G t x) (hE : AdjEigen G L y)
    (hn : ∀ v, 0≤x v) (hx : ∃ v, x v≠0) (hy : ∃ v, y v≠0)
    (hort : (∑ v : V,x v*y v)=0) : False := by
  have xpos (v : V) : 0<x v := by
    have h := hn v
    by_contra! hv
    obtain ⟨w,hw⟩ := hx
    exact hw (nonneg_zero_propagates G hc he hn (le_antisymm hv h) w)
  have ypos : ∃ v, 0<y v := by
    by_contra! hz
    have hm (v : V) : 0≤x v*(-y v) := mul_nonneg (xpos v).le (neg_nonneg.mpr (hz v))
    obtain ⟨w,hw⟩ := hy
    have hwp : 0 < x w*(-y w) := mul_pos (xpos w) (neg_pos.mpr (lt_of_le_of_ne (hz w) hw))
    have hsum : (∑ v : V, x v*(-y v))=0 := by
      simp_rw [mul_neg,Finset.sum_neg_distrib,hort,neg_zero]
    have h := Finset.single_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hm v)
      (Finset.mem_univ w)
    linarith only [h,hsum,hwp]
  obtain ⟨w,hw⟩ := ypos
  obtain ⟨u,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset V)
    (fun v => y v/x v) ⟨w,Finset.mem_univ _⟩
  let c := y u/x u
  have cp : 0<c := (div_pos hw (xpos w)).trans_le (hmax w (Finset.mem_univ _))
  have heq : y u=c*x u := by dsimp [c]; field_simp [(xpos u).ne']
  have yup : 0<y u := by rw [heq]; exact mul_pos cp (xpos u)
  have major (v : V) : y v≤c*x v :=
    (div_le_iff₀ (xpos v)).mp (hmax v (Finset.mem_univ _))
  have Ltu : L*y u≤t*y u := by
    calc
      _ = ∑ v ∈ G.neighborFinset u, y v := hE u
      _ ≤ ∑ v ∈ G.neighborFinset u, c*x v := Finset.sum_le_sum (fun v _ => major v)
      _ = c*(∑ v ∈ G.neighborFinset u,x v) := (Finset.mul_sum ..).symm
      _ = t*y u := by rw [← he u,heq]; ring
  have Lt : L=t := le_antisymm (le_of_mul_le_mul_right Ltu yup) htL
  let z (v : V) := c*x v-y v
  have hze : AdjEigen G t z := by
    intro v
    dsimp [z]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,← he v,← hE v,Lt]
    ring
  have hzn (v : V) : 0≤z v := sub_nonneg.mpr (major v)
  have hzu : z u=0 := sub_eq_zero.mpr heq.symm
  have hall := nonneg_zero_propagates G hc hze hzn hzu
  have heq' : y w=c*x w := (sub_eq_zero.mp (hall w)).symm
  have hp : 0<x w*y w := mul_pos (xpos w) hw
  have hn' (v : V) : 0≤x v*y v := by
    have e : y v=c*x v := (sub_eq_zero.mp (hall v)).symm
    rw [e]
    exact mul_nonneg (xpos v).le (mul_nonneg cp.le (xpos v).le)
  have hb := Finset.single_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hn' v)
    (Finset.mem_univ w)
  linarith only [hp,hb,hort]

/-- The subordinate eigenvector of an ordered nonzero orthogonal eigenpair
changes sign. This includes the top-two eigenvectors of a real symmetric
adjacency matrix. No Perron theorem is assumed in this lemma. -/
theorem orthogonal_subordinate_signs (hc : G.Connected) {t L : ℝ} {x y : V→ℝ}
    (htL : t≤L) (he : AdjEigen G t x) (hE : AdjEigen G L y)
    (hx : ∃ v, x v≠0) (hy : ∃ v, y v≠0)
    (hort : (∑ v : V,x v*y v)=0) :
    (∃ v, 0<x v) ∧ (∃ v, x v<0) := by
  constructor
  · by_contra! h
    have he' : AdjEigen G t (fun v => -x v) := by
      intro v; simp_rw [Finset.sum_neg_distrib,mul_neg,he v]
    have hn' : ∀ v, 0≤ -x v := fun v => neg_nonneg.mpr (h v)
    have hx' : ∃ v, -x v≠0 := by
      obtain ⟨w,hw⟩ := hx; exact ⟨w,neg_ne_zero.mpr hw⟩
    apply no_ordered_orthogonal_nonnegative G hc htL he' hE hn' hx' hy
    simp_rw [neg_mul,Finset.sum_neg_distrib,hort,neg_zero]
  · by_contra! h
    exact no_ordered_orthogonal_nonnegative G hc htL he hE h hx hy hort

#print axioms orthogonal_subordinate_signs
end CazenaveOne
